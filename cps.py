import os
import re
import sys
import math
import tempfile
import threading
import multiprocessing as mp
from datetime import datetime
from time import perf_counter
from queue import Empty, Queue
from concurrent.futures import ProcessPoolExecutor, as_completed
import socket
import subprocess
import time
import shutil
from pathlib import Path
from selenium.common.exceptions import WebDriverException
import traceback
from selenium.common.exceptions import ElementClickInterceptedException, TimeoutException

try:
    import pymupdf as fitz
except Exception:
    fitz = None

from pypdf import PdfReader
import tkinter as tk
from tkinter import ttk, filedialog
from tkinterdnd2 import DND_FILES, TkinterDnD

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager


# === ESTADO GLOBAL ===
ruta_salida_global = None
ruta_archivo_seleccionado = None
cola = None
procesando = False
preview_cache = {}
preview_window = None
chromedriver_path_cache = None

app = None
etiqueta = None
barra = None
boton_abrir = None
boton_copiar = None
boton_subir = None


# === REGEX / CONSTANTES ===
RE_CP = re.compile(r"\b\d{5}\b")
RE_DIGITO = re.compile(r"\d")
TOKEN_SPAIN = "SPAIN"
SUFIJO_CP = " 001"
EMPTY_PREVIEW = ("", "", "", "")
EMPTY_CODES = ()
PREVIEW_UPDATE_STEP = 16
WORKER_UPDATE_STEP = 16
UI_POLL_MS = 80
FAST_BACKEND_NAME = "PyMuPDF" if fitz is not None else "pypdf"

MIN_PARALLEL_PAGES = 40
TARGET_CHUNKS_PER_WORKER = 4
MIN_CHUNK_SIZE = 8
MAX_SCAN_WORKERS = max(1, min(os.cpu_count() or 1, 6))


# === COLORES ===
BG_COLOR = "#1e1e1e"
FG_COLOR = "#ffffff"
TEXT_SECONDARY = "#cccccc"
BUTTON_COLOR = "#2d2d2d"
INFO_BG = "#252526"


# === UTILIDADES ===
def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS  # PyInstaller
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


def obtener_nombre_unico(ruta):
    if not os.path.exists(ruta):
        return ruta

    base, ext = os.path.splitext(ruta)
    i = 1
    while True:
        nueva = f"{base}({i}){ext}"
        if not os.path.exists(nueva):
            return nueva
        i += 1


def guardar_codigos_txt(codigos_finales):
    documentos = os.path.join(os.path.expanduser("~"), "Documents")
    fecha = datetime.now().strftime("%d_%m_%Y")
    carpeta = os.path.join(documentos, "Pedidos_CP", fecha)
    os.makedirs(carpeta, exist_ok=True)

    ruta = obtener_nombre_unico(os.path.join(carpeta, "cps.txt"))
    with open(ruta, "w", encoding="utf-8") as f:
        f.write("\n".join(codigos_finales))
    return ruta


def construir_rangos(total_paginas, workers):
    if total_paginas <= 0:
        return []

    chunk = max(MIN_CHUNK_SIZE, math.ceil(total_paginas / max(1, workers * TARGET_CHUNKS_PER_WORKER)))
    rangos = []
    start = 0
    while start < total_paginas:
        stop = min(start + chunk, total_paginas)
        rangos.append((start, stop))
        start = stop
    return rangos


# === BACKEND PDF ===
def obtener_total_paginas_pymupdf(ruta):
    with fitz.open(ruta) as doc:
        return doc.page_count


def obtener_total_paginas_pypdf(ruta):
    return len(PdfReader(ruta).pages)


def obtener_total_paginas(ruta):
    if fitz is not None:
        return obtener_total_paginas_pymupdf(ruta)
    return obtener_total_paginas_pypdf(ruta)


def extraer_texto_pagina_pymupdf(page):
    return page.get_text("text") or ""


def extraer_texto_pagina_pymupdf_fast(page):
    textpage = page.get_textpage()
    if not textpage.search(TOKEN_SPAIN):
        return ""
    return textpage.extractText(sort=False) or ""


def extraer_texto_pagina_pypdf(page):
    return page.extract_text() or ""


# === ANALISIS DE TEXTO ===
def analizar_pagina_spain(texto):
    search_cp = RE_CP.search
    search_digit = RE_DIGITO.search
    token = TOKEN_SPAIN
    sufijo = SUFIJO_CP

    nombre_partes = []
    codigos = []
    append_nombre = nombre_partes.append
    append_codigo = codigos.append

    direccion = ""
    cp = ""
    ciudad = ""
    lineas_limpias = 0
    esperando_ciudad = False

    prev1 = ""
    prev2 = ""
    prev3 = ""

    for raw_line in texto.splitlines():
        stripped = raw_line.strip()
        if stripped:
            lineas_limpias += 1
            if not direccion:
                if search_digit(stripped):
                    direccion = stripped
                    esperando_ciudad = True
                else:
                    append_nombre(stripped)
            elif esperando_ciudad:
                match = search_cp(stripped)
                if match:
                    cp = match.group(0)
                    ciudad = stripped.replace(cp, "", 1).strip()
                esperando_ciudad = False

        if token in raw_line.upper():
            match = search_cp(prev1) or search_cp(prev2) or search_cp(prev3)
            if match:
                append_codigo(match.group(0) + sufijo)

        prev3, prev2, prev1 = prev2, prev1, raw_line

    if lineas_limpias < 3 or not direccion:
        return EMPTY_PREVIEW, EMPTY_CODES

    return (cp, " ".join(nombre_partes), direccion, ciudad), tuple(codigos)


def formatear_linea(idx, cp, nombre, direccion, ciudad):
    return (
        f"{str(idx + 1).rjust(3)} | {cp.ljust(6)} | {nombre[:20].ljust(20)} | "
        f"{direccion[:38].ljust(38)} | {ciudad[:15].ljust(15)}"
    )


# === ESCANEO POR RANGOS ===
def escanear_rango_pymupdf(args):
    ruta, start, stop = args
    paginas_preview = []
    cache_local = {}
    append_preview = paginas_preview.append

    with fitz.open(ruta) as doc:
        for i in range(start, stop):
            texto = extraer_texto_pagina_pymupdf_fast(doc.load_page(i))
            if not texto:
                continue

            preview_data, codigos = analizar_pagina_spain(texto)
            linea = formatear_linea(i, *preview_data)
            append_preview((i, linea))
            cache_local[i] = (linea, codigos)

    return start, stop, paginas_preview, cache_local


def escanear_rango_pypdf(args):
    ruta, start, stop = args
    paginas_preview = []
    cache_local = {}
    append_preview = paginas_preview.append

    reader = PdfReader(ruta)
    pages = reader.pages

    for i in range(start, stop):
        texto = extraer_texto_pagina_pypdf(pages[i])
        if TOKEN_SPAIN not in texto.upper():
            continue

        preview_data, codigos = analizar_pagina_spain(texto)
        linea = formatear_linea(i, *preview_data)
        append_preview((i, linea))
        cache_local[i] = (linea, codigos)

    return start, stop, paginas_preview, cache_local


# === SUBIR A CORREOS ===
from pathlib import Path
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC

CHROME_USER_DATA_DIR = Path.home() / "AppData" / "Local" / "CPSCorreosChrome"
CHROME_PROFILE_NAME = "Default"

driver_correos = None

def esperar_pagina_cargada(driver, timeout=20):
    WebDriverWait(driver, timeout).until(
        lambda d: d.execute_script("return document.readyState") == "complete"
    )


def click_robusto(driver, locator, timeout=20):
    wait = WebDriverWait(driver, timeout)

    elem = wait.until(EC.presence_of_element_located(locator))
    driver.execute_script(
        "arguments[0].scrollIntoView({block: 'center', inline: 'center'});", elem
    )

    time.sleep(0.3)

    try:
        wait.until(EC.element_to_be_clickable(locator)).click()
        return
    except ElementClickInterceptedException:
        pass

    elem = wait.until(EC.presence_of_element_located(locator))
    driver.execute_script("arguments[0].click();", elem)
    
def crear_driver_con_perfil_persistente():
    CHROME_USER_DATA_DIR.mkdir(parents=True, exist_ok=True)

    options = webdriver.ChromeOptions()
    options.add_argument(f"--user-data-dir={CHROME_USER_DATA_DIR}")
    options.add_argument(f"--profile-directory={CHROME_PROFILE_NAME}")
    options.add_argument("--no-first-run")
    options.add_argument("--no-default-browser-check")
    options.add_argument("--start-maximized")

    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_experimental_option("excludeSwitches", ["enable-automation"])
    options.add_experimental_option("useAutomationExtension", False)

    driver = webdriver.Chrome(options=options)

    try:
        driver.execute_script(
            "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
        )
    except Exception:
        pass

    return driver


def obtener_driver_correos():
    global driver_correos

    try:
        if driver_correos is not None:
            handles = driver_correos.window_handles
            if handles:
                _ = driver_correos.current_url
                return driver_correos
    except Exception:
        pass

    try:
        if driver_correos is not None:
            driver_correos.quit()
    except Exception:
        pass

    driver_correos = crear_driver_con_perfil_persistente()
    return driver_correos

def subir_a_correos():
    if not ruta_archivo_seleccionado:
        etiqueta.config(text="❌ No hay archivo seleccionado")
        return

    try:
        etiqueta.config(text="🟡 Abriendo Chrome con sesión guardada...")
        app.update_idletasks()

        driver = obtener_driver_correos()

        driver.get(
            "https://epostal.correos.es/OV2PREENVWEB/jsp/mioficinavirtual/_rlvid.jsp.faces?_rap=mov_generadorEtiquetasORHandler.mostrarVista&_rvip=/jsp/mioficinavirtual/miCuenta.jsp"
        )

        esperar_pagina_cargada(driver)

        click_robusto(driver, (By.ID, "myform:tipocarga:1"), timeout=20)

        input_file = WebDriverWait(driver, 20).until(
            EC.presence_of_element_located((By.ID, "myform:fileUpload"))
        )
        driver.execute_script(
            "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
            input_file
        )
        input_file.send_keys(ruta_archivo_seleccionado)

        etiqueta.config(
            text=(
                f"🚀 Archivo cargado:\n{os.path.basename(ruta_archivo_seleccionado)}\n"
                f"Perfil Chrome: {CHROME_USER_DATA_DIR.name}"
            )
        )

    except Exception as e:
        print(traceback.format_exc())
        etiqueta.config(text=f"❌ Error al abrir/subir en Correos: {e}")
# === PREVIEW ===
def actualizar_progreso_preview(porcentaje, actual, total, restante):
    barra["mode"] = "determinate"
    barra["value"] = porcentaje
    etiqueta.config(
        text=f"🔄 Analizando... {porcentaje}% ({actual}/{total}) | ETA: {restante}s"
    )


def cargar_preview_secuencial_pymupdf(ruta):
    global preview_cache

    total = obtener_total_paginas_pymupdf(ruta)
    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    ultimo_porcentaje = -1

    with fitz.open(ruta) as doc:
        for i in range(total):
            texto = extraer_texto_pagina_pymupdf_fast(doc.load_page(i))
            if texto:
                preview_data, codigos = analizar_pagina_spain(texto)
                linea = formatear_linea(i, *preview_data)
                paginas_preview.append((i, linea))
                cache_local[i] = (linea, codigos)

            actual = i + 1
            porcentaje = int(actual * 100 / total) if total else 100
            if porcentaje != ultimo_porcentaje and (
                porcentaje == 100 or actual == 1 or actual % PREVIEW_UPDATE_STEP == 0
            ):
                ultimo_porcentaje = porcentaje
                transcurrido = perf_counter() - inicio
                restante = int((transcurrido / actual) * (total - actual)) if actual else 0
                app.after(0, actualizar_progreso_preview, porcentaje, actual, total, restante)

    preview_cache = cache_local
    app.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview_secuencial_pypdf(ruta):
    global preview_cache

    reader = PdfReader(ruta)
    pages = reader.pages
    total = len(pages)
    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    ultimo_porcentaje = -1

    for i, pagina in enumerate(pages):
        texto = extraer_texto_pagina_pypdf(pagina)
        if TOKEN_SPAIN in texto.upper():
            preview_data, codigos = analizar_pagina_spain(texto)
            linea = formatear_linea(i, *preview_data)
            paginas_preview.append((i, linea))
            cache_local[i] = (linea, codigos)

        actual = i + 1
        porcentaje = int(actual * 100 / total) if total else 100
        if porcentaje != ultimo_porcentaje and (
            porcentaje == 100 or actual == 1 or actual % PREVIEW_UPDATE_STEP == 0
        ):
            ultimo_porcentaje = porcentaje
            transcurrido = perf_counter() - inicio
            restante = int((transcurrido / actual) * (total - actual)) if actual else 0
            app.after(0, actualizar_progreso_preview, porcentaje, actual, total, restante)

    preview_cache = cache_local
    app.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview_paralelo(ruta):
    global preview_cache

    total = obtener_total_paginas(ruta)
    workers = min(MAX_SCAN_WORKERS, total)
    if total < MIN_PARALLEL_PAGES or workers <= 1:
        if fitz is not None:
            return cargar_preview_secuencial_pymupdf(ruta)
        return cargar_preview_secuencial_pypdf(ruta)

    worker_fn = escanear_rango_pymupdf if fitz is not None else escanear_rango_pypdf
    rangos = construir_rangos(total, workers)

    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    procesadas = 0
    ultimo_porcentaje = -1

    try:
        with ProcessPoolExecutor(
            max_workers=workers,
            mp_context=mp.get_context("spawn"),
        ) as executor:
            futures = [executor.submit(worker_fn, (ruta, start, stop)) for start, stop in rangos]

            for future in as_completed(futures):
                start, stop, chunk_preview, chunk_cache = future.result()
                paginas_preview.extend(chunk_preview)
                cache_local.update(chunk_cache)

                procesadas += stop - start
                porcentaje = int(procesadas * 100 / total) if total else 100
                if porcentaje != ultimo_porcentaje:
                    ultimo_porcentaje = porcentaje
                    transcurrido = perf_counter() - inicio
                    restante = int((transcurrido / procesadas) * (total - procesadas)) if procesadas else 0
                    app.after(0, actualizar_progreso_preview, porcentaje, procesadas, total, restante)

    except Exception:
        if fitz is not None:
            return cargar_preview_secuencial_pymupdf(ruta)
        return cargar_preview_secuencial_pypdf(ruta)

    paginas_preview.sort(key=lambda x: x[0])
    preview_cache = cache_local
    app.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview(ruta):
    cargar_preview_paralelo(ruta)


def cerrar_preview(ventana):
    global preview_window
    if ventana.winfo_exists():
        ventana.destroy()
    preview_window = None
    etiqueta.config(text="Arrastra aquí tu PDF")


def mostrar_preview(pdf_path, paginas):
    global preview_window

    barra.stop()
    barra.pack_forget()

    if not paginas:
        etiqueta.config(text="❌ No se encontraron páginas de SPAIN")
        return

    etiqueta.config(text="Selecciona las páginas a procesar")

    ventana = tk.Toplevel(app)
    preview_window = ventana
    ventana.title("Seleccionar páginas")
    ventana.geometry("820x720")
    ventana.configure(bg=INFO_BG)
    ventana.protocol("WM_DELETE_WINDOW", lambda v=ventana: cerrar_preview(v))

    canvas = tk.Canvas(ventana, bg=INFO_BG)
    scrollbar = tk.Scrollbar(ventana, command=canvas.yview)
    frame = tk.Frame(canvas, bg=INFO_BG)

    canvas.create_window((0, 0), window=frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

    checks = []

    tk.Label(
        frame,
        text="Nº     | CP     | Nombre               | Dirección                              | Ciudad",
        font=("Consolas", 10, "bold"),
        bg=INFO_BG,
        fg="#aaaaaa",
    ).pack(anchor="w", padx=10, pady=5)

    for i, linea in paginas:
        var = tk.BooleanVar(value=True)
        checks.append((i, var))
        tk.Checkbutton(
            frame,
            text=linea,
            variable=var,
            bg=INFO_BG,
            fg=FG_COLOR,
            selectcolor="#333",
            font=("Consolas", 10),
        ).pack(anchor="w", padx=10, pady=3)

    def confirmar():
        seleccionadas = [i for i, var in checks if var.get()]
        codigos_por_pagina = {i: preview_cache[i][1] for i in seleccionadas if i in preview_cache}
        ventana.destroy()
        etiqueta.config(text="Procesando selección...")
        iniciar_proceso_filtrado(seleccionadas, codigos_por_pagina)

    tk.Button(
        ventana,
        text="Procesar selección",
        command=confirmar,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
    ).pack(pady=10)


# === PROCESADO FINAL DESDE CACHE ===
def proceso_cache_worker(paginas_seleccionadas, cola_local, codigos_por_pagina):
    total = len(paginas_seleccionadas)
    codigos_finales = []
    extend_codigos = codigos_finales.extend
    inicio = perf_counter()
    ultimo_porcentaje = -1

    for i, idx_pagina in enumerate(paginas_seleccionadas):
        extend_codigos(codigos_por_pagina.get(idx_pagina, EMPTY_CODES))

        actual = i + 1
        porcentaje = int(actual * 100 / total) if total else 100
        if porcentaje != ultimo_porcentaje and (
            porcentaje == 100 or actual == 1 or actual % WORKER_UPDATE_STEP == 0
        ):
            ultimo_porcentaje = porcentaje
            transcurrido = perf_counter() - inicio
            restante = int((transcurrido / actual) * (total - actual)) if actual else 0
            cola_local.put(("progreso", porcentaje, actual, total, restante))

    cola_local.put(("fin", guardar_codigos_txt(codigos_finales)))


def iniciar_proceso_filtrado(paginas, codigos_por_pagina):
    global cola, procesando

    procesando = True
    barra.pack(pady=10)
    barra["mode"] = "determinate"
    barra["value"] = 0

    cola = Queue()
    threading.Thread(
        target=proceso_cache_worker,
        args=(paginas, cola, codigos_por_pagina),
        daemon=True,
    ).start()

    actualizar_ui()


def actualizar_ui():
    global procesando, ruta_salida_global, ruta_archivo_seleccionado

    try:
        while True:
            msg = cola.get_nowait()
            tipo = msg[0]

            if tipo == "progreso":
                _, porcentaje, actual, total, restante = msg
                barra["mode"] = "determinate"
                barra["value"] = porcentaje
                etiqueta.config(
                    text=f"⚙️ Procesando... {porcentaje}% ({actual}/{total}) | ETA: {restante}s"
                )
                continue

            if tipo == "fin":
                ruta_salida_global = msg[1]
                ruta_archivo_seleccionado = ruta_salida_global
                actualizar_botones()
                procesando = False
                barra.stop()
                barra.pack_forget()
                etiqueta.config(text=f"✅ {os.path.basename(ruta_salida_global)} generado")

    except Empty:
        pass

    if procesando:
        app.after(UI_POLL_MS, actualizar_ui)


# === FUNCIONES VARIAS ===
def seleccionar_archivo():
    global ruta_archivo_seleccionado

    ruta = filedialog.askopenfilename(filetypes=[("TXT", "*.txt")])
    if not ruta:
        return

    ruta_archivo_seleccionado = ruta
    etiqueta.config(text=f"📄 {os.path.basename(ruta)} seleccionado")
    actualizar_botones()


def copiar_ruta():
    if not ruta_archivo_seleccionado:
        return

    app.clipboard_clear()
    app.clipboard_append(os.path.dirname(ruta_archivo_seleccionado))
    etiqueta.config(text="📋 Ruta copiada")


def abrir_carpeta():
    if ruta_archivo_seleccionado:
        os.startfile(os.path.dirname(ruta_archivo_seleccionado))


# === EVENTOS ===
def drop(event):
    ruta = event.data.strip("{}")

    barra.pack(pady=10)
    barra["mode"] = "determinate"
    barra["value"] = 0
    etiqueta.config(text=f"🔄 Analizando PDF [{FAST_BACKEND_NAME}]...")

    threading.Thread(target=cargar_preview, args=(ruta,), daemon=True).start()


def actualizar_botones():
    estado = "normal" if ruta_archivo_seleccionado else "disabled"
    boton_abrir.config(state=estado)
    boton_copiar.config(state=estado)
    boton_subir.config(state=estado)


# === INFORMACION LEGAL ===
def mostrar_info():
    ventana = tk.Toplevel(app)
    ventana.title("Información")
    ventana.geometry("500x450")
    ventana.configure(bg=INFO_BG)
    ventana.resizable(False, False)

    container = tk.Frame(ventana, bg=INFO_BG)
    container.pack(fill="both", expand=True, padx=10, pady=10)

    canvas = tk.Canvas(container, bg=INFO_BG, highlightthickness=0)
    scrollbar = tk.Scrollbar(container, command=canvas.yview)
    scroll_frame = tk.Frame(canvas, bg=INFO_BG)

    canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

    tk.Label(
        scroll_frame,
        text="Extractor de Códigos Postales",
        font=("Segoe UI", 12, "bold"),
        fg=FG_COLOR,
        bg=INFO_BG,
    ).pack(pady=(5, 10))

    tk.Label(
        scroll_frame,
        text="Desarrollado por: Chema\nVersión 1.1.1",
        font=("Segoe UI", 10),
        fg="#cccccc",
        bg=INFO_BG,
        justify="center",
    ).pack(pady=(0, 10))

    licencia = """LICENCIA DE USO

Copyright (c) 2026 José María Ibáñez Martínez

Todos los derechos reservados.

Este software y la documentación asociada están protegidos por derechos de autor.
No se permite su copia, modificación, distribución, sublicencia, uso comercial
ni cualquier otro uso sin autorización expresa y por escrito del autor.

Este software está destinado únicamente a uso personal o interno.

EL SOFTWARE SE PROPORCIONA \"TAL CUAL\", SIN GARANTÍA DE NINGÚN TIPO,
EXPRESA O IMPLÍCITA, INCLUYENDO, PERO NO LIMITADO A, GARANTÍAS DE
COMERCIABILIDAD, IDONEIDAD PARA UN PROPÓSITO PARTICULAR Y NO INFRACCIÓN.

EN NINGÚN CASO EL AUTOR SERÁ RESPONSABLE DE NINGÚN DAÑO, RECLAMACIÓN
O RESPONSABILIDAD, YA SEA EN UNA ACCIÓN CONTRACTUAL, AGRAVIO O DE OTRO TIPO,
DERIVADO DE, O EN CONEXIÓN CON EL SOFTWARE O EL USO DEL MISMO.
"""

    texto = tk.Text(
        scroll_frame,
        wrap="word",
        bg=INFO_BG,
        fg="#cccccc",
        font=("Segoe UI", 9),
        relief="flat",
        height=20,
    )
    texto.insert("1.0", licencia)
    texto.config(state="disabled")
    texto.pack(fill="both", expand=True, padx=5, pady=5)


# === UI PRINCIPAL ===
def main():
    global app, etiqueta, barra, boton_abrir, boton_copiar, boton_subir

    app = TkinterDnD.Tk()
    app.title("Extractor de Códigos Postales")
    app.geometry("560x300")
    app.configure(bg=BG_COLOR)
    app.resizable(False, False)

    icon_path = resource_path("icono.ico")
    if os.path.exists(icon_path):
        try:
            app.iconbitmap(icon_path)
        except Exception:
            pass

    style = ttk.Style()
    style.theme_use("default")
    style.configure(
        "TProgressbar",
        thickness=20,
        troughcolor="#333333",
        background="#4caf50",
        bordercolor="#333333",
        lightcolor="#4caf50",
        darkcolor="#4caf50",
    )

    frame = tk.Frame(app, bg=BG_COLOR)
    frame.pack(expand=True)

    tk.Label(
        frame,
        text="Extractor de Códigos Postales",
        font=("Segoe UI", 16, "bold"),
        fg=FG_COLOR,
        bg=BG_COLOR,
    ).pack(pady=20)

    etiqueta = tk.Label(frame, text="Arrastra aquí tu PDF", fg=TEXT_SECONDARY, bg=BG_COLOR)
    etiqueta.pack(pady=10)

    barra = ttk.Progressbar(frame, length=300)

    frame_botones = tk.Frame(app, bg=BG_COLOR)
    frame_botones.pack(side="bottom", fill="x", pady=15)

    frame_izq = tk.Frame(frame_botones, bg=BG_COLOR)
    frame_izq.pack(side="left", expand=True)

    boton_abrir = tk.Button(
        frame_izq,
        text="📂 Abrir carpeta",
        command=abrir_carpeta,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        state="disabled",
    )
    boton_abrir.pack(pady=5)

    boton_copiar = tk.Button(
        frame_izq,
        text="📋 Copiar ruta",
        command=copiar_ruta,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        state="disabled",
    )
    boton_copiar.pack(pady=5)

    frame_der = tk.Frame(frame_botones, bg=BG_COLOR)
    frame_der.pack(side="right", expand=True)

    tk.Button(
        frame_der,
        text="📂 Seleccionar archivo",
        command=seleccionar_archivo,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
    ).pack(pady=5)

    boton_subir = tk.Button(
        frame_der,
        text="🚀 Subir a Correos",
        command=subir_a_correos,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        state="disabled",
    )
    boton_subir.pack(pady=5)

    boton_info = tk.Button(
        app,
        text="ℹ",
        command=mostrar_info,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        relief="flat",
        font=("Segoe UI", 10),
    )

    boton_info.place(relx=1.0, rely=1.0, anchor="se", x=-5, y=-5)
    app.drop_target_register(DND_FILES)
    app.dnd_bind("<<Drop>>", drop)
    app.mainloop()


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()
    main()
