"""Aplicación de escritorio para extraer códigos postales desde PDFs, generar un TXT
para Correos y automatizar el ciclo de descarga e impresión de etiquetas Brother.
"""

import os
import re
import sys
import math
import tempfile
import threading
import multiprocessing as mp
from datetime import datetime
import hashlib
import io
import zipfile
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
from selenium.common.exceptions import ElementClickInterceptedException, TimeoutException, StaleElementReferenceException, InvalidSessionIdException
try:
    import keyring
except Exception:
    keyring = None

from tkinter import simpledialog
try:
    import winreg
except Exception:
    winreg = None
    
try:
    import pymupdf as fitz
except Exception:
    fitz = None

from pypdf import PdfReader
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinterdnd2 import DND_FILES, TkinterDnD

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager

try:
    from PIL import Image, ImageTk, ImageChops, ImageStat
except Exception:
    Image = ImageTk = ImageChops = ImageStat = None


try:
    import win32api
    import win32print
except Exception:
    win32api = None
    win32print = None


# === ESTADO GLOBAL DE LA APLICACIÓN ===
ruta_archivo_salida = None
ruta_archivo_actual = None
cola_ui = None
proceso_en_curso = False
cache_preview_paginas = {}
ventana_preview = None
cache_ruta_chromedriver = None

ventana_principal = None
etiqueta_estado = None
barra_progreso = None
boton_abrir_carpeta = None
boton_copiar_ruta = None
boton_subir_correos = None
boton_postlibri = None
etiqueta_estado_impresora = None
boton_actualizar_impresora = None

postlibri_directorio_salida = None
postlibri_ventana_preview = None
postlibri_cache_etiquetas = []


# === EXPRESIONES REGULARES Y CONSTANTES ===
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
RE_CP = re.compile(r"\b\d{5}\b")
RE_DIGITO = re.compile(r"\d")
RE_DNI_NIE = re.compile(r"^(?:DNI|NIE|CIF)\b", re.IGNORECASE)

PALABRAS_DIRECCION = (
    "CALLE", "C/", "AV.", "AVDA", "AVENIDA", "PLAZA", "PASEO", "CAMINO",
    "RONDA", "TRAVESIA", "TRAVESÍA", "CARRETERA", "BARRIO", "URB",
    "URBANIZACION", "URBANIZACIÓN", "EDIF", "EDIFICIO", "PORTAL",
    "PISO", "PUERTA", "AP.", "APARTADO"
)
CORREOS_LOGIN_URL = "https://mioficina.correos.es/es/es/login"
CORREOS_HOME_URL = "https://mioficina.correos.es/es/es/home"
CORREOS_KEYRING_SERVICE = "cps_correos"
CORREOS_KEYRING_USER_KEY = "__username__"

def es_linea_documento(linea):
    linea = linea.strip()
    return bool(RE_DNI_NIE.match(linea))


def parece_linea_direccion(linea):
    linea = linea.strip()
    upper = linea.upper()

    if not linea or es_linea_documento(linea):
        return False

    return bool(RE_DIGITO.search(linea)) or any(p in upper for p in PALABRAS_DIRECCION)


# === PARÁMETROS DE POSTLIBRI ===
POSTLIBRI_DPI = 300
POSTLIBRI_LABELS_PER_PAGE = 10
POSTLIBRI_LBL_WIDTH = 1134
POSTLIBRI_LBL_HEIGHT = 585
POSTLIBRI_LBL_LOCX = 87
POSTLIBRI_LBL_LOCY = 103
POSTLIBRI_LBL_SEPX = 45
POSTLIBRI_LBL_SEPY = 91
POSTLIBRI_THUMB_SIZE = (200, 80)
POSTLIBRI_DEFAULT_PRINTER = "Brother QL-700"
POSTLIBRI_BLANK_THRESHOLD = 0.001
POSTLIBRI_TEMPLATE_NAMES = ("PostLibri.zip", "Postlibri.zip", "PostLibri.lbx", "Postlibri.lbx")
POSTLIBRI_STATUS_CHECK_MS = 10000


# === PALETA DE COLORES ===
BG_COLOR = "#1e1e1e"
FG_COLOR = "#ffffff"
TEXT_SECONDARY = "#cccccc"
BUTTON_COLOR = "#2d2d2d"
INFO_BG = "#252526"
# --- CREDENCIALES ---
def pedir_credenciales_correos_grande(parent=None, usuario_inicial=""):
    """Muestra una ventana más grande para introducir correo y contraseña de Correos."""
    resultado = {"usuario": None, "password": None}

    win = tk.Toplevel(parent or ventana_principal)
    win.title("Credenciales de Correos")
    win.geometry("460x220")
    win.configure(bg=INFO_BG)
    win.resizable(False, False)
    win.transient(parent or ventana_principal)
    win.grab_set()

    # Centrar ventana
    win.update_idletasks()
    ancho = 460
    alto = 220
    x = (win.winfo_screenwidth() // 2) - (ancho // 2)
    y = (win.winfo_screenheight() // 2) - (alto // 2)
    win.geometry(f"{ancho}x{alto}+{x}+{y}")

    frame = tk.Frame(win, bg=INFO_BG)
    frame.pack(fill="both", expand=True, padx=18, pady=16)

    tk.Label(
        frame,
        text="Introduce tus credenciales de Correos",
        bg=INFO_BG,
        fg=FG_COLOR,
        font=("Segoe UI", 12, "bold"),
    ).pack(anchor="w", pady=(0, 14))

    tk.Label(
        frame,
        text="Correo de Correos",
        bg=INFO_BG,
        fg=FG_COLOR,
        font=("Segoe UI", 10),
    ).pack(anchor="w")

    entry_usuario = tk.Entry(
        frame,
        font=("Segoe UI", 12),
        width=36,
        bg="#ffffff",
        fg="#000000",
        relief="flat",
    )
    entry_usuario.pack(fill="x", pady=(4, 12), ipady=6)
    entry_usuario.insert(0, usuario_inicial or "")

    tk.Label(
        frame,
        text="Contraseña",
        bg=INFO_BG,
        fg=FG_COLOR,
        font=("Segoe UI", 10),
    ).pack(anchor="w")

    entry_password = tk.Entry(
        frame,
        font=("Segoe UI", 12),
        width=36,
        show="*",
        bg="#ffffff",
        fg="#000000",
        relief="flat",
    )
    entry_password.pack(fill="x", pady=(4, 16), ipady=6)

    botones = tk.Frame(frame, bg=INFO_BG)
    botones.pack(fill="x")

    def aceptar(event=None):
        usuario = entry_usuario.get().strip()
        password = entry_password.get()
        if not usuario or not password:
            messagebox.showwarning(
                "Correos",
                "Debes introducir correo y contraseña.",
                parent=win,
            )
            return
        resultado["usuario"] = usuario
        resultado["password"] = password
        win.destroy()

    def cancelar(event=None):
        win.destroy()

    tk.Button(
        botones,
        text="Cancelar",
        command=cancelar,
        bg="#4a4f59",
        fg=FG_COLOR,
        relief="flat",
        font=("Segoe UI", 10, "bold"),
        padx=14,
        pady=8,
        cursor="hand2",
    ).pack(side="left")

    tk.Button(
        botones,
        text="Guardar",
        command=aceptar,
        bg="#2f8f4e",
        fg=FG_COLOR,
        relief="flat",
        font=("Segoe UI", 10, "bold"),
        padx=14,
        pady=8,
        cursor="hand2",
    ).pack(side="right")

    win.bind("<Return>", aceptar)
    win.bind("<Escape>", cancelar)

    entry_usuario.focus_set()
    win.wait_window()

    return resultado["usuario"], resultado["password"]

def guardar_credenciales_correos(usuario, password):
    if keyring is None:
        raise RuntimeError("Falta instalar keyring: pip install keyring")

    usuario = (usuario or "").strip()
    if not usuario or not password:
        raise RuntimeError("Usuario o contraseña vacíos.")

    keyring.set_password(CORREOS_KEYRING_SERVICE, CORREOS_KEYRING_USER_KEY, usuario)
    keyring.set_password(CORREOS_KEYRING_SERVICE, usuario, password)


def cargar_credenciales_correos():
    if keyring is None:
        return None, None

    usuario = keyring.get_password(CORREOS_KEYRING_SERVICE, CORREOS_KEYRING_USER_KEY)
    if not usuario:
        return None, None

    password = keyring.get_password(CORREOS_KEYRING_SERVICE, usuario)
    return usuario, password


def borrar_credenciales_correos():
    if keyring is None:
        return

    usuario = keyring.get_password(CORREOS_KEYRING_SERVICE, CORREOS_KEYRING_USER_KEY)
    if usuario:
        try:
            keyring.delete_password(CORREOS_KEYRING_SERVICE, usuario)
        except Exception:
            pass
        try:
            keyring.delete_password(CORREOS_KEYRING_SERVICE, CORREOS_KEYRING_USER_KEY)
        except Exception:
            pass

def asegurar_credenciales_correos():
    usuario, password = cargar_credenciales_correos()
    if usuario and password:
        return usuario, password

    usuario, password = pedir_credenciales_correos_grande(
        parent=ventana_principal
    )

    if not usuario:
        raise RuntimeError("No se indicó el correo de Correos.")
    if not password:
        raise RuntimeError("No se indicó la contraseña de Correos.")

    guardar_credenciales_correos(usuario, password)
    return usuario, password

def _abrir_generador_si_hay_sesion(driver, timeout=18):
    """Desde una sesión ya iniciada, abre el generador y espera a que quede usable."""
    fin = time.time() + timeout
    ultimo_error = None

    while time.time() < fin:
        try:
            enfocar_pestana_correos(driver)
            driver.get(CORREOS_URL)
            esperar_carga_completa_pagina(driver, timeout=min(12, timeout))

            if _pagina_parece_login_correos(driver):
                return False

            if driver.find_elements(By.ID, "myform:tipocarga:1"):
                return True
            if driver.find_elements(By.ID, "myform:fileUpload"):
                return True

            url = (driver.current_url or "").lower()
            if "epostal.correos.es" in url and "/login" not in url:
                time.sleep(1)
                if driver.find_elements(By.ID, "myform:tipocarga:1"):
                    return True
                if driver.find_elements(By.ID, "myform:fileUpload"):
                    return True

        except Exception as e:
            ultimo_error = e

        time.sleep(0.35)

    raise RuntimeError(
        f"Hay sesión iniciada, pero no se pudo abrir el generador de Correos. Último error: {ultimo_error}"
    )


def cerrar_sesion_correos_ui():
    def _worker():
        try:
            ui_set_estado("🔓 Forzando cierre de sesión de Correos...")

            driver = obtener_driver_correos(
                headless=False,
                forzar_nuevo=False,
            )

            ok = cerrar_sesion_correos(driver, timeout=15)

            cerrar_driver_correos(sincronizar_perfil=True)

            if ok:
                ui_set_estado("✅ Sesión de Correos cerrada correctamente.")
            else:
                ui_set_estado("⚠️ No se pudo cerrar la sesión de Correos.")
        except Exception as e:
            print(traceback.format_exc())
            try:
                cerrar_driver_correos()
            except Exception:
                pass
            ui_show_error("Correos", f"No se pudo cerrar la sesión:\n{e}")
            ui_set_estado(f"❌ Error al cerrar sesión de Correos: {e}")

    threading.Thread(target=_worker, daemon=True).start()
    
def login_automatico_correos(driver, timeout=18):
    """Hace login automático en Correos usando credenciales guardadas en keyring."""
    usuario, password = cargar_credenciales_correos()
    if not usuario or not password:
        raise RuntimeError(
            "No hay credenciales guardadas de Correos. Usa 'Configurar credenciales' antes de continuar."
        )

    ui_set_estado("🔐 Iniciando sesión automática en Correos...")

    driver.get(CORREOS_LOGIN_URL)
    esperar_carga_completa_pagina(driver, timeout=12)
    wait = WebDriverWait(driver, timeout)

    # Si ya hay sesión y la web redirige a /home, abrimos el generador directamente
    if "/home" in (driver.current_url or "").lower():
        _abrir_generador_si_hay_sesion(driver, timeout=timeout)
        return

    email = wait.until(EC.element_to_be_clickable((By.ID, "_ul_email")))
    pwd = wait.until(EC.element_to_be_clickable((By.ID, "_ul_password_email")))

    driver.execute_script("""
        const el = arguments[0];
        el.focus();
        el.value = '';
        el.dispatchEvent(new Event('input', {bubbles:true}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
    """, email)
    email.clear()
    email.send_keys(usuario)
    driver.execute_script("""
        const el = arguments[0];
        el.dispatchEvent(new Event('input', {bubbles:true}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
        el.dispatchEvent(new Event('blur', {bubbles:true}));
    """, email)

    driver.execute_script("""
        const el = arguments[0];
        el.focus();
        el.value = '';
        el.dispatchEvent(new Event('input', {bubbles:true}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
    """, pwd)
    pwd.clear()
    pwd.send_keys(password)
    driver.execute_script("""
        const el = arguments[0];
        el.dispatchEvent(new Event('input', {bubbles:true}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
        el.dispatchEvent(new Event('blur', {bubbles:true}));
    """, pwd)

    try:
        chk = driver.find_element(By.ID, "_ul_remember_checbox")
        if not chk.is_selected():
            driver.execute_script("arguments[0].click();", chk)
            driver.execute_script(
                "arguments[0].dispatchEvent(new Event('change', {bubbles:true}));",
                chk
            )
    except Exception:
        pass

    boton = wait.until(
        EC.presence_of_element_located(
            (By.CSS_SELECTOR, "correos-ui-button button[type='submit']")
        )
    )

    WebDriverWait(driver, 10).until(
        lambda d: boton.is_enabled() and not boton.get_attribute("disabled")
    )

    driver.execute_script("arguments[0].scrollIntoView({block:'center'});", boton)
    time.sleep(0.15)
    handles_antes = list(driver.window_handles)

    try:
        boton.click()
    except Exception:
        driver.execute_script("arguments[0].click();", boton)

    def _esperar_fin_login(d):
        try:
            handles = d.window_handles
            if len(handles) > len(handles_antes):
                d.switch_to.window(handles[-1])

            enfocar_pestana_correos(d)
            url = (d.current_url or "").lower()

            if "/home" in url:
                return True
            if "epostal.correos.es" in url and "/login" not in url:
                return True
            if not _pagina_parece_login_correos(d):
                return True
            return False
        except Exception:
            return False

    WebDriverWait(driver, timeout).until(_esperar_fin_login)

    enfocar_pestana_correos(driver)
    try:
        esperar_carga_completa_pagina(driver, timeout=30)
    except Exception:
        pass

    time.sleep(0.6)

    # Tras el login, no basta con /home: abrimos el generador sí o sí
    if _abrir_generador_si_hay_sesion(driver, timeout=timeout):
        return

    texto = (driver.page_source or "").lower()
    if (
        "contraseña incorrect" in texto
        or "contrasena incorrect" in texto
        or "correo incorrect" in texto
        or "usuario o contraseña incorrect" in texto
        or "usuario o contrasena incorrect" in texto
        or "email o contraseña incorrect" in texto
        or "email o contrasena incorrect" in texto
    ):
        raise RuntimeError("Correos rechazó las credenciales. Revisa usuario y contraseña.")

    raise RuntimeError(
        f"No se pudo confirmar la sesión de Correos tras el login. URL final: {(driver.current_url or '').lower()}"
    )

def _pagina_parece_login_correos(driver):
    """Detecta el login real de Correos evitando falsos positivos."""
    try:
        url = (driver.current_url or "").lower()

        # Si la URL ya apunta al login, es login.
        if "/login" in url:
            return True

        # Comprobamos los campos reales del formulario de acceso.
        emails = driver.find_elements(By.ID, "_ul_email")
        pwds = driver.find_elements(By.ID, "_ul_password_email")

        if emails and pwds:
            try:
                return emails[0].is_displayed() and pwds[0].is_displayed()
            except Exception:
                return True

        return False
    except Exception:
        return False

def cerrar_sesion_correos(driver, timeout=15):
    """Intenta cerrar sesión en Correos antes de cerrar Chrome para dejar el perfil limpio."""
    try:
        ui_set_estado("🔓 Cerrando sesión de Correos...")

        # Intentamos primero en la página actual
        enfocar_pestana_correos(driver)
        try:
            esperar_carga_completa_pagina(driver, timeout=10)
        except Exception:
            pass

        elems = driver.find_elements(By.ID, "cerrarsesion")

        # Si no está el enlace en la página actual, vamos a home
        if not elems:
            driver.get(CORREOS_HOME_URL)
            esperar_carga_completa_pagina(driver, timeout=timeout)
            enfocar_pestana_correos(driver)
            elems = driver.find_elements(By.ID, "cerrarsesion")

        if not elems:
            raise RuntimeError("No se encontró el enlace de cerrar sesión en Correos.")

        enlace = elems[0]
        driver.execute_script("arguments[0].scrollIntoView({block:'center'});", enlace)
        time.sleep(0.5)

        try:
            enlace.click()
        except Exception:
            driver.execute_script("arguments[0].click();", enlace)

        def _esperar_logout(d):
            try:
                url = (d.current_url or "").lower()
                if "/login" in url:
                    return True
                if _pagina_parece_login_correos(d):
                    return True
                return False
            except Exception:
                return False

        WebDriverWait(driver, timeout).until(_esperar_logout)
        ui_set_estado("🔓 Sesión de Correos cerrada correctamente.")
        return True

    except Exception as e:
        # No bloqueamos el flujo principal si el logout falla,
        # pero dejamos constancia en estado para depuración.
        ui_set_estado(f"⚠️ No se pudo cerrar sesión en Correos: {e}")
        return False
def _sesion_correos_valida(driver, timeout=30, navegar=True):
    """Comprueba la sesión de Correos. Puede validar en la página actual o navegando al generador."""
    if navegar:
        driver.get(CORREOS_URL)
        esperar_carga_completa_pagina(driver, timeout=timeout)

    if _pagina_parece_login_correos(driver):
        return False

    # Señales de zona autenticada válida
    if driver.find_elements(By.ID, "myform:tipocarga:1"):
        return True
    if driver.find_elements(By.ID, "myform:fileUpload"):
        return True

    url = (driver.current_url or "").lower()
    if "/home" in url:
        return True

    return "epostal.correos.es" in url and "/login" not in url


def asegurar_sesion_correos(driver, timeout=30):
    """Garantiza que haya una sesión válida en Correos antes de continuar."""
    ui_set_estado("🔐 Verificando sesión de Correos...")

    # SIEMPRE abrimos primero la URL de login:
    # - si no hay sesión, se verá el formulario
    # - si ya hay sesión, Correos redirige a /home y eso es éxito
    driver.get(CORREOS_LOGIN_URL)
    esperar_carga_completa_pagina(driver, timeout=timeout)
    enfocar_pestana_correos(driver)

    url_actual = (driver.current_url or "").lower()

    # Caso clave: si la propia web redirige a /home, ya hay sesión iniciada
    if "/home" in url_actual:
        time.sleep(1.5)
        return

    # Si seguimos en login, hacemos login automático
    if _pagina_parece_login_correos(driver):
        login_automatico_correos(driver, timeout=timeout)

    # Tras el login, volvemos a comprobar
    enfocar_pestana_correos(driver)
    try:
        esperar_carga_completa_pagina(driver, timeout=timeout)
    except Exception:
        pass

    url_post_login = (driver.current_url or "").lower()

    # Segundo caso clave: si tras el login estamos en /home, también es éxito
    if "/home" in url_post_login:
        time.sleep(1.5)
        return

    # Última validación: probamos la zona autenticada real
    deadline = time.time() + timeout
    ultimo_error = None

    while time.time() < deadline:
        try:
            enfocar_pestana_correos(driver)

            url = (driver.current_url or "").lower()
            if "/home" in url:
                return

            if _sesion_correos_valida(driver, timeout=10, navegar=False):
                return

            if _sesion_correos_valida(driver, timeout=10, navegar=True):
                return
        except Exception as e:
            ultimo_error = e

        time.sleep(1.0)

    raise RuntimeError(
        f"No se pudo confirmar una sesión válida en Correos tras el login. Último error: {ultimo_error}"
    )
def configurar_credenciales_correos():
    try:
        usuario_actual, _ = cargar_credenciales_correos()

        usuario, password = pedir_credenciales_correos_grande(
            parent=ventana_principal,
            usuario_inicial=usuario_actual or "",
        )

        if not usuario or not password:
            return

        guardar_credenciales_correos(usuario, password)
        ui_set_estado("✅ Credenciales de Correos guardadas de forma segura.")
    except Exception as e:
        ui_show_error("Correos", f"No se pudieron guardar las credenciales:\n{e}")

def eliminar_credenciales_correos_ui():
    try:
        borrar_credenciales_correos()
        ui_set_estado("🗑️ Credenciales de Correos eliminadas.")
    except Exception as e:
        ui_show_error("Correos", f"No se pudieron borrar las credenciales:\n{e}")

def credenciales_correos_configuradas():
    usuario, password = cargar_credenciales_correos()
    return bool(usuario and password)

def asegurar_credenciales_correos_desde_ui():
    if credenciales_correos_configuradas():
        return True

    try:
        configurar_credenciales_correos()
        return credenciales_correos_configuradas()
    except Exception:
        return False

    

# === UTILIDADES GENERALES ===
def resolver_ruta_recurso(relative_path):
    """Devuelve la ruta absoluta de un recurso"""
    try:
        base_path = sys._MEIPASS  # PyInstaller
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


def generar_ruta_unica(ruta):
    """Genera una ruta de archivo no existente añadiendo un sufijo numérico cuando el nombre base ya está ocupado."""
    if not os.path.exists(ruta):
        return ruta

    base, ext = os.path.splitext(ruta)
    i = 1
    while True:
        nueva = f"{base}({i}){ext}"
        if not os.path.exists(nueva):
            return nueva
        i += 1


def guardar_codigos_postales_txt(codigos_finales):
    """Guarda la colección final de códigos postales en un archivo TXT dentro del directorio de trabajo del usuario."""
    documentos = os.path.join(os.path.expanduser("~"), "Documents")
    fecha = datetime.now().strftime("%d_%m_%Y")
    carpeta = os.path.join(documentos, "Pedidos_CP", fecha)
    os.makedirs(carpeta, exist_ok=True)

    ruta = generar_ruta_unica(os.path.join(carpeta, "cps.txt"))
    with open(ruta, "w", encoding="utf-8") as f:
        f.write("\n".join(codigos_finales))
    return ruta


def construir_rangos_paginas(total_paginas, workers):
    """Divide el total de páginas en rangos de trabajo equilibrados para el escaneo secuencial o paralelo."""
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


# === BACKENDS DE LECTURA PDF ===
def obtener_total_paginas_con_pymupdf(ruta):
    """Cuenta el número total de páginas del PDF utilizando PyMuPDF."""
    with fitz.open(ruta) as doc:
        return doc.page_count


def obtener_total_paginas_con_pypdf(ruta):
    """Cuenta el número total de páginas del PDF utilizando pypdf."""
    return len(PdfReader(ruta).pages)


def obtener_total_paginas_pdf(ruta):
    """Selecciona automáticamente el backend disponible y devuelve el número total de páginas del PDF."""
    if fitz is not None:
        return obtener_total_paginas_con_pymupdf(ruta)
    return obtener_total_paginas_con_pypdf(ruta)


def extraer_texto_pagina_con_pymupdf(page):
    """Extrae el texto completo de una página usando PyMuPDF."""
    return page.get_text("text") or ""


def extraer_texto_pagina_con_pymupdf_rapido(page):
    """Extrae texto con una ruta rápida: primero busca el token SPAIN y solo entonces recupera el contenido completo."""
    textpage = page.get_textpage()
    if not textpage.search(TOKEN_SPAIN):
        return ""
    return textpage.extractText(sort=False) or ""


def extraer_texto_pagina_con_pypdf(page):
    """Extrae el texto completo de una página usando pypdf."""
    return page.extract_text() or ""


# === ANÁLISIS DE TEXTO ===
def analizar_pagina_destino_espana(texto):
    """Analiza una página SPAIN contemplando DNI en línea aparte y direcciones en varias líneas."""
    search_cp = RE_CP.search
    token = TOKEN_SPAIN
    sufijo = SUFIJO_CP

    codigos = []

    lineas = [linea.strip() for linea in texto.splitlines() if linea.strip()]
    if not lineas:
        return EMPTY_PREVIEW, EMPTY_CODES

    # Buscar la línea del país
    idx_spain = None
    for i, linea in enumerate(lineas):
        if token in linea.upper():
            idx_spain = i
            break

    if idx_spain is None:
        return EMPTY_PREVIEW, EMPTY_CODES

    # Obtener CP final para exportación buscando hasta 3 líneas antes de SPAIN
    for i, linea in enumerate(lineas):
        if token in linea.upper():
            for j in range(i - 1, max(-1, i - 4), -1):
                match = search_cp(lineas[j])
                if match:
                    codigos.append(match.group(0) + sufijo)
                    break

    bloque = lineas[:idx_spain]
    if not bloque:
        return EMPTY_PREVIEW, tuple(codigos)

    # La ciudad/CP suele ser la última línea antes de SPAIN que contiene CP
    idx_ciudad = None
    cp = ""
    ciudad = ""

    for i in range(len(bloque) - 1, -1, -1):
        match = search_cp(bloque[i])
        if match:
            idx_ciudad = i
            cp = match.group(0)
            ciudad = bloque[i].replace(cp, "", 1).strip(" ,")
            break

    if idx_ciudad is None:
        return EMPTY_PREVIEW, tuple(codigos)

    antes_ciudad = bloque[:idx_ciudad]
    if not antes_ciudad:
        return (cp, "", "", ciudad), tuple(codigos)

    # El nombre será la primera línea útil
    nombre = antes_ciudad[0]
    resto = antes_ciudad[1:]

    extras = []
    direccion_partes = []

    for linea in resto:
        if es_linea_documento(linea):
            continue

        if direccion_partes:
            direccion_partes.append(linea)
            continue

        if parece_linea_direccion(linea):
            direccion_partes.append(linea)
        else:
            extras.append(linea)

    direccion = " ".join(extras + direccion_partes).strip()

    return (cp, nombre, direccion, ciudad), tuple(codigos)

def formatear_linea_preview(idx, cp, nombre, direccion, ciudad):
    """Construye la línea del preview en el orden: Nº Pedido | Nombre | Código postal."""
    return (
        f"{str(idx + 1):^10} | "
        f"{nombre[:32].ljust(32)} | "
        f"{cp:^13}"
    )


# === ESCANEO POR RANGOS DE PÁGINAS ===
def escanear_rango_con_pymupdf(args):
    """Procesa un rango de páginas con PyMuPDF y devuelve tanto las líneas de preview como la caché de códigos detectados."""
    ruta, start, stop = args
    paginas_preview = []
    cache_local = {}
    append_preview = paginas_preview.append

    with fitz.open(ruta) as doc:
        for i in range(start, stop):
            texto = extraer_texto_pagina_con_pymupdf_rapido(doc.load_page(i))
            if not texto:
                continue

            preview_data, codigos = analizar_pagina_destino_espana(texto)
            linea = formatear_linea_preview(i, *preview_data)
            append_preview((i, linea))
            cache_local[i] = (linea, codigos)

    return start, stop, paginas_preview, cache_local


def escanear_rango_con_pypdf(args):
    """Procesa un rango de páginas con pypdf y devuelve tanto las líneas de preview como la caché de códigos detectados."""
    ruta, start, stop = args
    paginas_preview = []
    cache_local = {}
    append_preview = paginas_preview.append

    reader = PdfReader(ruta)
    pages = reader.pages

    for i in range(start, stop):
        texto = extraer_texto_pagina_con_pypdf(pages[i])
        if TOKEN_SPAIN not in texto.upper():
            continue

        preview_data, codigos = analizar_pagina_destino_espana(texto)
        linea = formatear_linea_preview(i, *preview_data)
        append_preview((i, linea))
        cache_local[i] = (linea, codigos)

    return start, stop, paginas_preview, cache_local



# === FLUJO POSTLIBRI (PORTADO DESDE VB/.NET) ===
def postlibri_obtener_posicion_etiqueta(ctr_equ):
    """Calcula la posición X/Y de una etiqueta dentro de la plantilla PostLibri."""
    i_ctr = ((ctr_equ - 1) % POSTLIBRI_LABELS_PER_PAGE) + 1
    fila = ((i_ctr + 1) // 2) - 1
    co_y = (fila * POSTLIBRI_LBL_HEIGHT) + (fila * POSTLIBRI_LBL_SEPY) + POSTLIBRI_LBL_LOCY - fila
    co_x = POSTLIBRI_LBL_LOCX + (POSTLIBRI_LBL_WIDTH + POSTLIBRI_LBL_SEPX if i_ctr % 2 == 0 else 0)
    return co_x, co_y


def postlibri_renderizar_pagina_a_imagen(page, dpi=POSTLIBRI_DPI):
    """Renderiza una página PDF a una imagen Pillow con la resolución solicitada."""
    if fitz is None:
        raise RuntimeError("PyMuPDF es obligatorio para renderizar páginas en el modo PostLibri")
    if Image is None:
        raise RuntimeError("Pillow es obligatorio para el modo PostLibri")

    zoom = dpi / 72.0
    pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), alpha=False)
    mode = "RGB"
    return Image.frombytes(mode, (pix.width, pix.height), pix.samples)


def postlibri_recorte_esta_vacio(img):
    """Determina si un recorte de etiqueta está en blanco o prácticamente vacío."""
    if ImageChops is None or ImageStat is None:
        return False

    gray = img.convert("L")
    white = Image.new("L", gray.size, 255)
    diff = ImageChops.difference(gray, white)
    mask = diff.point(lambda p: 255 if p > 8 else 0)
    bbox = mask.getbbox()
    if bbox is None:
        return True

    hist = mask.histogram()
    non_white = hist[255] if len(hist) > 255 else 0
    total = gray.width * gray.height
    ratio = non_white / total if total else 0.0
    mean = ImageStat.Stat(gray).mean[0]
    return ratio < POSTLIBRI_BLANK_THRESHOLD and mean > 245


def postlibri_obtener_directorio_salida(pdf_path):
    """Crea y devuelve el directorio de salida donde se almacenarán los BMP generados por PostLibri."""
    base = Path.home() / "Documents" / "PostLibri" / datetime.now().strftime("%d_%m_%Y")
    base.mkdir(parents=True, exist_ok=True)
    stem = Path(pdf_path).stem
    out_dir = base / stem
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir


def postlibri_limpiar_bmps_salida(out_dir):
    """Elimina BMP temporales previos para evitar mezclar resultados de distintas ejecuciones."""
    for p in Path(out_dir).glob("Object*.bmp"):
        try:
            p.unlink()
        except Exception:
            pass


def postlibri_extraer_etiquetas_pdf(pdf_path, progress_cb=None):
    """Recorre el PDF, recorta las posiciones de etiquetas configuradas y guarda únicamente las que contienen contenido útil."""
    out_dir = postlibri_obtener_directorio_salida(pdf_path)
    postlibri_limpiar_bmps_salida(out_dir)
    labels = []

    with fitz.open(pdf_path) as doc:
        total_slots = doc.page_count * POSTLIBRI_LABELS_PER_PAGE
        procesadas = 0
        for page_idx in range(doc.page_count):
            pil_page = postlibri_renderizar_pagina_a_imagen(doc.load_page(page_idx), dpi=POSTLIBRI_DPI)

            for slot in range(1, POSTLIBRI_LABELS_PER_PAGE + 1):
                label_idx = page_idx * POSTLIBRI_LABELS_PER_PAGE + slot
                x, y = postlibri_obtener_posicion_etiqueta(label_idx)
                x2 = x + POSTLIBRI_LBL_WIDTH
                y2 = y + POSTLIBRI_LBL_HEIGHT

                if x < 0 or y < 0 or x2 > pil_page.width or y2 > pil_page.height:
                    procesadas += 1
                    if progress_cb:
                        progress_cb(procesadas, total_slots, label_idx, None)
                    continue

                crop = pil_page.crop((x, y, x2, y2))
                if postlibri_recorte_esta_vacio(crop):
                    procesadas += 1
                    if progress_cb:
                        progress_cb(procesadas, total_slots, label_idx, None)
                    continue

                bmp_path = out_dir / f"Object{label_idx:02d}.bmp"
                crop.save(bmp_path, format="BMP")
                labels.append({
                    "idx": label_idx,
                    "path": str(bmp_path),
                })

                procesadas += 1
                if progress_cb:
                    progress_cb(procesadas, total_slots, label_idx, str(bmp_path))

    return out_dir, labels


def postlibri_crear_miniatura(path_bmp):
    """Crea una miniatura centrada y lista para mostrarse en Tkinter a partir de un BMP de etiqueta."""
    if Image is None or ImageTk is None:
        raise RuntimeError("Pillow es obligatorio para mostrar miniaturas")
    img = Image.open(path_bmp)
    thumb = img.copy()
    thumb.thumbnail(POSTLIBRI_THUMB_SIZE)
    canvas = Image.new("RGB", POSTLIBRI_THUMB_SIZE, "white")
    pos = ((canvas.width - thumb.width) // 2, (canvas.height - thumb.height) // 2)
    canvas.paste(thumb, pos)
    return ImageTk.PhotoImage(canvas)


def postlibri_actualizar_progreso_ui(porcentaje, actual, total, texto):
    """Actualiza la barra de progreso y el texto de estado durante el procesamiento PostLibri."""
    barra_progreso["mode"] = "determinate"
    barra_progreso["value"] = porcentaje
    etiqueta_estado.config(text=f"🏷️ {texto} {porcentaje}% ({actual}/{total})")


def postlibri_procesar_pdf(pdf_path):
    """Orquesta el flujo completo de PostLibri: extrae etiquetas, valida impresora, genera LBX temporales y envía el trabajo a impresión."""
    global postlibri_directorio_salida, postlibri_cache_etiquetas

    if fitz is None:
        messagebox.showerror("PostLibri", "Este modo necesita PyMuPDF instalado.")
        return
    if Image is None:
        messagebox.showerror("PostLibri", "Este modo necesita Pillow instalado.")
        return

    temp_dir = None
    try:
        barra_progreso.pack(pady=10)
        barra_progreso["mode"] = "determinate"
        barra_progreso["value"] = 0
        etiqueta_estado.config(text="🏷️ Procesando PDF PostLibri...")
        ventana_principal.update_idletasks()

        progreso_estado = {"ultimo": -1}

        def progress_cb(actual, total, label_idx, path_generado):
            porcentaje = int(actual * 100 / total) if total else 100
            if porcentaje != progreso_estado["ultimo"]:
                progreso_estado["ultimo"] = porcentaje
                ventana_principal.after(0, postlibri_actualizar_progreso_ui, porcentaje, actual, total, "Extrayendo etiquetas...")

        out_dir, labels = postlibri_extraer_etiquetas_pdf(pdf_path, progress_cb=progress_cb)
        postlibri_directorio_salida = str(out_dir)
        postlibri_cache_etiquetas = labels

        if not labels:
            ventana_principal.after(0, lambda: etiqueta_estado.config(text="❌ No se detectaron etiquetas útiles en el PDF"))
            return

        ventana_principal.after(0, postlibri_actualizar_progreso_ui, 100, len(labels), len(labels), "Preparando impresión...")

        template = postlibri_resolver_plantilla_predeterminada()
        lbxs = postlibri_generar_lbxs(labels, template, out_dir, usar_directorio_temporal=True)
        if lbxs:
            temp_dir = str(Path(lbxs[0]).resolve().parent)

        estado_impresora = postlibri_obtener_estado_impresora(POSTLIBRI_DEFAULT_PRINTER)
        if not estado_impresora["ok"]:
            raise RuntimeError(estado_impresora["text"])

        ventana_principal.after(0, lambda total=len(lbxs): etiqueta_estado.config(text=f"🖨️ Enviando {total} etiquetas a {POSTLIBRI_DEFAULT_PRINTER}..."))
        postlibri_imprimir_lbxs(lbxs, printer_name=POSTLIBRI_DEFAULT_PRINTER)
        ventana_principal.after(0, lambda total=len(lbxs), carpeta=str(out_dir): etiqueta_estado.config(
            text=f"✅ {total} etiquetas enviadas a {POSTLIBRI_DEFAULT_PRINTER} | Salida: {carpeta}"
        ))
    except Exception as e:
        print(traceback.format_exc())
        ventana_principal.after(0, lambda msg=f"❌ Error PostLibri: {e}": etiqueta_estado.config(text=msg))
        ventana_principal.after(0, lambda err=e: messagebox.showerror("PostLibri", f"No se pudo imprimir automáticamente:\n{err}"))
    finally:
        ventana_principal.after(0, barra_progreso.pack_forget)
        if temp_dir:
            shutil.rmtree(temp_dir, ignore_errors=True)


def postlibri_seleccionar_pdf():
    """Permite seleccionar manualmente un PDF y lanza su procesamiento PostLibri en segundo plano."""
    ruta = filedialog.askopenfilename(filetypes=[("PDF", "*.pdf")])
    if not ruta:
        return
    threading.Thread(target=postlibri_procesar_pdf, args=(ruta,), daemon=True).start()


def postlibri_cerrar_preview(ventana):
    """Cierra la ventana de preview de etiquetas PostLibri y restablece el estado visual principal."""
    global postlibri_ventana_preview
    if ventana.winfo_exists():
        ventana.destroy()
    postlibri_ventana_preview = None
    etiqueta_estado.config(text="Listo")


def postlibri_resolver_plantilla_predeterminada():
    """Localiza la plantilla PostLibri por defecto buscando en las rutas conocidas de distribución y desarrollo."""
    candidatos = []

    base_dirs = []
    try:
        base_dirs.append(Path(resolver_ruta_recurso(".")))
    except Exception:
        pass

    try:
        base_dirs.append(Path(__file__).resolve().parent)
    except Exception:
        pass

    for base_dir in base_dirs:
        for name in POSTLIBRI_TEMPLATE_NAMES:
            candidatos.append(base_dir / name)

    vistos = set()
    for candidato in candidatos:
        c = str(candidato)
        if c in vistos:
            continue
        vistos.add(c)
        if candidato.exists():
            return str(candidato)

    nombres = ", ".join(POSTLIBRI_TEMPLATE_NAMES)
    raise FileNotFoundError(
        f"No se encontró la plantilla PostLibri. Copia uno de estos archivos junto al .exe o al .py: {nombres}"
    )


def postlibri_crear_lbx_desde_plantilla(template_path, bmp_path, salida_lbx):
    """Genera un archivo LBX sustituyendo la imagen Object0.bmp de la plantilla por la etiqueta indicada."""
    template_path = Path(template_path)
    salida_lbx = Path(salida_lbx)

    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_dir = Path(tmp_dir)
        with zipfile.ZipFile(template_path, "r") as zf:
            zf.extractall(tmp_dir)

        object0 = tmp_dir / "Object0.bmp"
        shutil.copy2(bmp_path, object0)

        tmp_zip = tmp_dir / "out.zip"
        with zipfile.ZipFile(tmp_zip, "w", compression=zipfile.ZIP_DEFLATED) as zf:
            for p in tmp_dir.rglob("*"):
                if p == tmp_zip or p.is_dir():
                    continue
                zf.write(p, p.relative_to(tmp_dir))

        salida_lbx.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(tmp_zip, salida_lbx)


def postlibri_generar_lbxs(labels_seleccionadas, template_path, out_dir, usar_directorio_temporal=False):
    """Genera un archivo LBX por cada etiqueta seleccionada, ya sea en un directorio definitivo o temporal."""
    if usar_directorio_temporal:
        lbx_dir = Path(tempfile.mkdtemp(prefix="postlibri_print_"))
    else:
        lbx_dir = Path(out_dir) / "LBX"
        lbx_dir.mkdir(parents=True, exist_ok=True)

    generados = []
    for label in labels_seleccionadas:
        salida = lbx_dir / f"PostLibri_{label['idx']:02d}.lbx"
        postlibri_crear_lbx_desde_plantilla(template_path, label["path"], salida)
        generados.append(str(salida))
    return generados


def _postlibri_bpac_invocar(obj, nombre_metodo, *args, obligatorio=True):
    """Invoca de forma segura un método COM de b-PAC y evita reintentos sobre atributos que en algunos entornos llegan como booleanos."""
    miembro = getattr(obj, nombre_metodo, None)
    if miembro is None:
        if obligatorio:
            raise RuntimeError(f"b-PAC no expone '{nombre_metodo}'")
        return None
    if callable(miembro):
        return miembro(*args)
    if obligatorio and args:
        raise RuntimeError(
            f"b-PAC devolvió un valor no invocable para '{nombre_metodo}': {type(miembro).__name__}"
        )
    return miembro


def postlibri_imprimir_lbxs(lbx_paths, printer_name=POSTLIBRI_DEFAULT_PRINTER):
    """Envía una secuencia de archivos LBX a la impresora Brother mediante la automatización b-PAC de Windows."""
    if os.name != "nt":
        raise RuntimeError("La impresión b-PAC solo está disponible en Windows")

    try:
        import pythoncom
        import win32com.client
    except Exception as e:
        raise RuntimeError("No se encontró pywin32/win32com. Instala pywin32 para imprimir con Brother.") from e

    pythoncom.CoInitialize()
    try:
        total = len(lbx_paths)
        for idx, lbx_path in enumerate(lbx_paths, start=1):
            obj_doc = None
            try:
                obj_doc = win32com.client.Dispatch("bpac.Document")
                opened = _postlibri_bpac_invocar(obj_doc, "Open", str(lbx_path))
                if not opened:
                    raise RuntimeError(f"No se pudo abrir la plantilla LBX: {lbx_path}")

                _postlibri_bpac_invocar(obj_doc, "SetPrinter", printer_name, True)
                _postlibri_bpac_invocar(obj_doc, "StartPrint", "", 0)
                _postlibri_bpac_invocar(obj_doc, "PrintOut", 1, 0)

                end_print = getattr(obj_doc, "EndPrint", None)
                if callable(end_print):
                    end_print()

                close_doc = getattr(obj_doc, "Close", None)
                if callable(close_doc):
                    close_doc()

                if idx < total:
                    time.sleep(0.35)
            except Exception as e:
                raise RuntimeError(
                    f"Error al imprimir la etiqueta {idx}/{total} en Brother QL-700: {e}"
                ) from e
            finally:
                obj_doc = None
    finally:
        pythoncom.CoUninitialize()


def postlibri_obtener_estado_impresora(printer_name=POSTLIBRI_DEFAULT_PRINTER):
    """Consulta por WMI el estado operativo de la impresora configurada y devuelve un resumen apto para UI."""
    try:
        import win32com.client
    except Exception:
        return {
            "ok": False,
            "state": "sin_pywin32",
            "text": f"Impresora: {printer_name} sin pywin32",
            "color": "#ff6b6b",
            "detail": "No se encontró pywin32/win32com.",
        }

    try:
        locator = win32com.client.Dispatch("WbemScripting.SWbemLocator")
        svc = locator.ConnectServer(".", r"root\cimv2")
        safe_name = printer_name.replace(chr(92), chr(92) * 2).replace("'", chr(92) + "'")
        query = (
            "SELECT Name, WorkOffline, Availability, PrinterStatus, ExtendedPrinterStatus, Status, "
            "DetectedErrorState FROM Win32_Printer WHERE Name = '%s'" % safe_name
        )
        printers = list(svc.ExecQuery(query))
    except Exception as e:
        return {
            "ok": False,
            "state": "wmi_error",
            "text": f"Impresora: error consultando {printer_name}",
            "color": "#ff6b6b",
            "detail": str(e),
        }

    if not printers:
        return {
            "ok": False,
            "state": "not_found",
            "text": f"Impresora: {printer_name} no encontrada",
            "color": "#ff6b6b",
            "detail": "La cola no existe en Windows.",
        }

    p = printers[0]
    work_offline = bool(getattr(p, "WorkOffline", False))
    availability = int(getattr(p, "Availability", 0) or 0)
    printer_status = int(getattr(p, "PrinterStatus", 0) or 0)
    extended_status = int(getattr(p, "ExtendedPrinterStatus", 0) or 0)
    detected_error = int(getattr(p, "DetectedErrorState", 0) or 0)
    status_text = str(getattr(p, "Status", "") or "").strip()

    detail = (
        f"WorkOffline={work_offline}, Availability={availability}, PrinterStatus={printer_status}, "
        f"ExtendedPrinterStatus={extended_status}, DetectedErrorState={detected_error}, Status='{status_text}'"
    )

    if work_offline or availability == 8 or printer_status == 7 or status_text.lower() == "offline":
        return {
            "ok": False,
            "state": "offline",
            "text": f"Impresora: {printer_name} offline",
            "color": "#ff6b6b",
            "detail": detail,
        }

    if printer_status == 8:
        return {
            "ok": False,
            "state": "paper_jam",
            "text": f"Impresora: {printer_name} atasco de papel",
            "color": "#ff6b6b",
            "detail": detail,
        }

    if printer_status == 5 or extended_status == 7:
        return {
            "ok": False,
            "state": "warming_up",
            "text": f"Impresora: {printer_name} calentando",
            "color": "#f0ad4e",
            "detail": detail,
        }

    if printer_status == 9:
        return {
            "ok": False,
            "state": "out_of_paper",
            "text": f"Impresora: {printer_name} sin etiquetas/papel",
            "color": "#f0ad4e",
            "detail": detail,
        }

    if printer_status == 1:
        return {
            "ok": False,
            "state": "paused",
            "text": f"Impresora: {printer_name} pausada",
            "color": "#f0ad4e",
            "detail": detail,
        }

    if printer_status in (2, 3, 4, 6, 10) or status_text.lower() in ("ok", "idle", "degraded", "unknown"):
        return {
            "ok": True,
            "state": "online",
            "text": f"Impresora: {printer_name} online",
            "color": "#4caf50",
            "detail": detail,
        }

    return {
        "ok": True,
        "state": "available",
        "text": f"Impresora: {printer_name} disponible",
        "color": "#4caf50",
        "detail": detail,
    }


def postlibri_aplicar_estado_impresora_ui(estado):
    """Pinta en la interfaz el estado actual de la impresora Brother."""
    if etiqueta_estado_impresora is None:
        return
    try:
        etiqueta_estado_impresora.config(
            text=estado.get("text", "Impresora: estado desconocido"),
            fg=estado.get("color", FG_COLOR),
        )
    except Exception:
        pass


def postlibri_refrescar_estado_impresora(programar_siguiente=True):
    """Actualiza el estado de la impresora y, si procede, programa una nueva comprobación periódica."""
    estado = postlibri_obtener_estado_impresora(POSTLIBRI_DEFAULT_PRINTER)
    postlibri_aplicar_estado_impresora_ui(estado)
    if ventana_principal is not None and programar_siguiente:
        ventana_principal.after(POSTLIBRI_STATUS_CHECK_MS, postlibri_refrescar_estado_impresora)

def postlibri_mostrar_preview(pdf_path, labels, out_dir):
    """Muestra un visor con las etiquetas extraídas para permitir su revisión, generación de LBX o impresión manual."""
    global postlibri_ventana_preview

    barra_progreso.stop()
    barra_progreso.pack_forget()

    if not labels:
        etiqueta_estado.config(text="❌ No se detectaron etiquetas útiles en el PDF")
        return

    etiqueta_estado.config(text=f"✅ {len(labels)} etiquetas extraídas")

    ventana = tk.Toplevel(ventana_principal)
    postlibri_ventana_preview = ventana
    ventana.title("Selector de etiquetas PostLibri")
    ventana.geometry("760x720")
    ventana.configure(bg=INFO_BG)
    ventana.protocol("WM_DELETE_WINDOW", lambda v=ventana: postlibri_cerrar_preview(v))

    top_info = tk.Label(
        ventana,
        text=f"PDF: {os.path.basename(pdf_path)}\nCarpeta de salida: {out_dir}",
        bg=INFO_BG,
        fg=FG_COLOR,
        justify="left",
        anchor="w",
    )
    top_info.pack(fill="x", padx=10, pady=(10, 5))

    canvas = tk.Canvas(ventana, bg=INFO_BG, highlightthickness=0)
    scrollbar = tk.Scrollbar(ventana, command=canvas.yview)
    frame = tk.Frame(canvas, bg=INFO_BG)
    frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.create_window((0, 0), window=frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    checks = []
    imagenes = []

    for label in labels:
        row = tk.Frame(frame, bg=INFO_BG)
        row.pack(fill="x", padx=10, pady=4)

        var = tk.BooleanVar(value=True)
        checks.append((label, var))

        thumb = postlibri_crear_miniatura(label["path"])
        imagenes.append(thumb)

        cb = tk.Checkbutton(
            row,
            text=f"Etiqueta {label['idx']:02d}",
            variable=var,
            bg=INFO_BG,
            fg=FG_COLOR,
            selectcolor="#333",
            width=14,
            anchor="w",
        )
        cb.pack(side="left")

        img_lbl = tk.Label(row, image=thumb, bg=INFO_BG)
        img_lbl.pack(side="left", padx=8)

        path_lbl = tk.Label(
            row,
            text=os.path.basename(label["path"]),
            bg=INFO_BG,
            fg=TEXT_SECONDARY,
            anchor="w",
        )
        path_lbl.pack(side="left", padx=8)

    ventana._postlibri_images = imagenes

    bottom = tk.Frame(ventana, bg=INFO_BG)
    bottom.pack(fill="x", padx=10, pady=10)

    def seleccionadas():
        return [label for label, var in checks if var.get()]

    def abrir_salida():
        destino = out_dir
        try:
            os.startfile(destino)
        except Exception:
            messagebox.showinfo("PostLibri", f"Carpeta de salida:\n{destino}")

    def generar_lbx():
        elegidas = seleccionadas()
        if not elegidas:
            messagebox.showwarning("PostLibri", "No hay etiquetas seleccionadas.")
            return
        try:
            template = postlibri_resolver_plantilla_predeterminada()
            lbxs = postlibri_generar_lbxs(elegidas, template, out_dir)
            messagebox.showinfo("PostLibri", f"Se han generado {len(lbxs)} archivos LBX en:\n{Path(out_dir) / 'LBX'}")
        except Exception as e:
            messagebox.showerror("PostLibri", f"No se pudieron generar los LBX:\n{e}")

    def imprimir_brother():
        elegidas = seleccionadas()
        if not elegidas:
            messagebox.showwarning("PostLibri", "No hay etiquetas seleccionadas.")
            return

        temp_dir = None
        try:
            template = postlibri_resolver_plantilla_predeterminada()
            lbxs = postlibri_generar_lbxs(elegidas, template, out_dir, usar_directorio_temporal=True)
            if lbxs:
                temp_dir = str(Path(lbxs[0]).resolve().parent)
            postlibri_imprimir_lbxs(lbxs, printer_name=POSTLIBRI_DEFAULT_PRINTER)
            messagebox.showinfo(
                "PostLibri",
                f"Se han enviado {len(lbxs)} etiquetas a impresión en {POSTLIBRI_DEFAULT_PRINTER}."
            )
        except Exception as e:
            messagebox.showerror("PostLibri", f"No se pudo imprimir:\n{e}")
        finally:
            if temp_dir:
                shutil.rmtree(temp_dir, ignore_errors=True)

    tk.Button(bottom, text="🧩 Generar LBX", command=generar_lbx, bg=BUTTON_COLOR, fg=FG_COLOR).pack(side="left", padx=5)
    tk.Button(bottom, text="🖨️ Imprimir Brother", command=imprimir_brother, bg=BUTTON_COLOR, fg=FG_COLOR).pack(side="left", padx=5)

# === AUTOMATIZACIÓN DE CORREOS ===
CHROME_USER_DATA_DIR = Path.home() / "AppData" / "Local" / "CPSCorreosChrome"
CHROME_FALLBACK_USER_DATA_DIR = Path.home() / "AppData" / "Local" / "CPSCorreosChromeSelenium"
CHROME_ACTIVE_USER_DATA_DIR = CHROME_USER_DATA_DIR
CHROME_DOWNLOAD_DIR = Path.home() / 'Documents' / 'Pedidos_CP' / 'Correos_PDF'
CORREOS_AUTOMATION_HEADLESS = True
CORREOS_URL = (
    "https://epostal.correos.es/OV2PREENVWEB/jsp/mioficinavirtual/"
    "_rlvid.jsp.faces?_rap=mov_generadorEtiquetasORHandler.mostrarVista"
    "&_rvip=/jsp/mioficinavirtual/miCuenta.jsp"
)

driver_correos = None
driver_correos_visible = False
chrome_login_process = None
chrome_runtime_profile_dir = None
CHROME_DEBUG_HOST = "127.0.0.1"
CHROME_DEBUG_PORT = 9222


def esperar_carga_completa_pagina(driver, timeout=20):
    """Espera hasta que el navegador indique que el documento HTML ha terminado de cargarse."""
    WebDriverWait(driver, timeout).until(
        lambda d: d.execute_script("return document.readyState") == "complete"
    )


def hacer_click_robusto(driver, locator, timeout=20, intentos=5):
    """Intenta hacer clic de forma tolerante a overlays, staleness e interceptaciones frecuentes en Selenium."""
    ultimo_error = None
    for _ in range(intentos):
        wait = WebDriverWait(driver, timeout)
        try:
            elem = wait.until(EC.presence_of_element_located(locator))
            driver.execute_script(
                "arguments[0].scrollIntoView({block: 'center', inline: 'center'});", elem
            )
            time.sleep(0.15)

            elem = wait.until(EC.element_to_be_clickable(locator))
            try:
                elem.click()
            except (ElementClickInterceptedException, StaleElementReferenceException):
                elem = wait.until(EC.presence_of_element_located(locator))
                driver.execute_script("arguments[0].click();", elem)
            return
        except (StaleElementReferenceException, ElementClickInterceptedException, TimeoutException) as e:
            ultimo_error = e
            time.sleep(0.2)
            continue

    if ultimo_error:
        raise ultimo_error


def obtener_directorio_descargas_correos():
    """Garantiza la existencia y devuelve la carpeta usada para las descargas del flujo de Correos."""
    CHROME_DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
    return CHROME_DOWNLOAD_DIR


def listar_pdfs_descargados(download_dir: Path):
    """Devuelve el conjunto de PDFs presentes actualmente en el directorio de descargas."""
    return {p.resolve() for p in download_dir.glob("*.pdf")}


def limpiar_descargas_parciales(download_dir: Path):
    """Elimina archivos temporales de descarga incompleta antes de iniciar una nueva automatización."""
    for patron in ("*.crdownload", "*.tmp", "*.part"):
        for p in download_dir.glob(patron):
            try:
                p.unlink()
            except Exception:
                pass


def esperar_pdf_descargado(download_dir: Path, existentes=None, timeout=180):
    """Espera hasta detectar un nuevo PDF descargado y completamente cerrado por Chrome."""
    if existentes is None:
        existentes = set()

    deadline = time.time() + timeout
    ultimo_candidato = None

    while time.time() < deadline:
        actuales = listar_pdfs_descargados(download_dir)
        nuevos = [p for p in actuales if p not in existentes]

        if nuevos:
            nuevos.sort(key=lambda p: p.stat().st_mtime, reverse=True)
            candidato = nuevos[0]
            ultimo_candidato = candidato
            temporal = candidato.with_suffix(candidato.suffix + ".crdownload")
            if candidato.exists() and not temporal.exists():
                return candidato

        parciales = list(download_dir.glob("*.crdownload"))
        if not parciales and ultimo_candidato and ultimo_candidato.exists():
            return ultimo_candidato

        time.sleep(1)

    raise TimeoutException(
        f"No se descargó ningún PDF en {download_dir} dentro de {timeout} segundos."
    )

def esperar_pdf_descargado_o_login(driver, download_dir: Path, existentes=None, timeout=45):
    """Espera un PDF nuevo, pero aborta antes si la sesión de Correos ha caducado o vuelve al login."""
    if existentes is None:
        existentes = set()

    deadline = time.time() + timeout
    ultimo_candidato = None
    ultimo_url = ""

    while time.time() < deadline:
        # 1) Si Correos vuelve al login, abortamos enseguida
        try:
            ultimo_url = (driver.current_url or "").lower()
            if _pagina_parece_login_correos(driver):
                raise RuntimeError(
                    "La sesión de Correos no está iniciada o ha caducado mientras se intentaba generar/descargar el PDF. "
                    "Pulsa '🔐 Iniciar sesión Correos' y vuelve a intentarlo."
                )
            if "login" in ultimo_url or "autentic" in ultimo_url:
                raise RuntimeError(
                    "Correos ha redirigido al inicio de sesión antes de descargar el PDF. "
                    "Pulsa '🔐 Iniciar sesión Correos' y vuelve a intentarlo."
                )
        except RuntimeError:
            raise
        except Exception:
            pass

        # 2) Comprobamos si ya apareció el PDF
        actuales = listar_pdfs_descargados(download_dir)
        nuevos = [p for p in actuales if p not in existentes]

        if nuevos:
            nuevos.sort(key=lambda p: p.stat().st_mtime, reverse=True)
            candidato = nuevos[0]
            ultimo_candidato = candidato
            temporal = candidato.with_suffix(candidato.suffix + ".crdownload")
            if candidato.exists() and not temporal.exists():
                return candidato

        # 3) Si no hay .crdownload y había candidato, damos por terminada la descarga
        parciales = list(download_dir.glob("*.crdownload"))
        if not parciales and ultimo_candidato and ultimo_candidato.exists():
            return ultimo_candidato

        time.sleep(1)

    raise TimeoutException(
        f"Correos no descargó ningún PDF en {timeout} segundos. "
        "Puede que no haya sesión iniciada, que la sesión haya caducado o que la web se haya quedado bloqueada."
    )


def _configurar_opciones_chrome(headless=False, user_data_dir=None):
    """Construye las opciones de Chrome necesarias para reutilizar perfil, descargas automáticas y modo headless si aplica."""
    options = webdriver.ChromeOptions()
    options.add_argument(f"--user-data-dir={user_data_dir}")
    options.add_argument("--no-first-run")
    options.add_argument("--no-default-browser-check")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_experimental_option("excludeSwitches", ["enable-automation"])
    options.add_experimental_option("useAutomationExtension", False)

    if headless:
        options.add_argument("--headless=new")
        options.add_argument("--window-size=1920,1080")
        options.add_argument("--disable-gpu")
        options.add_argument("--no-sandbox")
    else:
        options.add_argument("--start-maximized")

    CHROME_DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
    prefs = {
        "download.default_directory": str(CHROME_DOWNLOAD_DIR),
        "download.prompt_for_download": False,
        "download.directory_upgrade": True,
        "plugins.always_open_pdf_externally": True,
        "download.open_pdf_in_system_reader": False,
        "safebrowsing.enabled": True,
    }
    options.add_experimental_option("prefs", prefs)
    return options


def _localizar_ejecutable_chrome():
    """Busca Google Chrome en rutas habituales, PATH y registro de Windows."""
    candidatos = [
        Path(os.environ.get("PROGRAMFILES", r"C:\Program Files")) / "Google/Chrome/Application/chrome.exe",
        Path(os.environ.get("PROGRAMFILES(X86)", r"C:\Program Files (x86)")) / "Google/Chrome/Application/chrome.exe",
        Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData/Local"))) / "Google/Chrome/Application/chrome.exe",
    ]
    for candidato in candidatos:
        if candidato.exists():
            return str(candidato)

    for nombre in ("chrome.exe", "chrome"):
        ruta = shutil.which(nombre)
        if ruta:
            return ruta

    if winreg is not None:
        claves = [
            r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\chrome.exe",
            r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\App Paths\chrome.exe",
        ]
        for raiz in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
            for clave in claves:
                try:
                    with winreg.OpenKey(raiz, clave) as k:
                        valor, _ = winreg.QueryValueEx(k, "")
                    if valor and os.path.exists(valor):
                        return valor
                except OSError:
                    pass

    return None

def _hay_login_chrome_abierto():
    """Indica si el proceso manual de Chrome para login sigue abierto."""
    global chrome_login_process
    try:
        return chrome_login_process is not None and chrome_login_process.poll() is None
    except Exception:
        return False


def _depurador_chrome_activo(host=CHROME_DEBUG_HOST, port=CHROME_DEBUG_PORT, timeout=0.5):
    """Comprueba si hay una instancia de Chrome exponiendo depuración remota en el host y puerto indicados."""
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def _limpiar_referencia_login_chrome():
    """Limpia la referencia al proceso de login manual cuando este ya ha terminado."""
    global chrome_login_process
    try:
        if chrome_login_process is not None and chrome_login_process.poll() is not None:
            chrome_login_process = None
    except Exception:
        chrome_login_process = None


def crear_driver_adjuntado_a_chrome_existente():
    """Crea un driver Selenium conectado a una instancia de Chrome ya abierta con depuración remota."""
    options = webdriver.ChromeOptions()
    options.add_experimental_option(
        "debuggerAddress", f"{CHROME_DEBUG_HOST}:{CHROME_DEBUG_PORT}"
    )
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=options)
    driver.set_page_load_timeout(60)
    return driver


def crear_driver_correos(headless=False, user_data_dir=None):
    """Construye un driver de Chrome listo para automatizar el portal de Correos con el perfil indicado."""
    global CHROME_ACTIVE_USER_DATA_DIR

    user_data_dir = Path(user_data_dir or CHROME_ACTIVE_USER_DATA_DIR)
    user_data_dir.mkdir(parents=True, exist_ok=True)
    CHROME_ACTIVE_USER_DATA_DIR = user_data_dir

    options = _configurar_opciones_chrome(headless=headless, user_data_dir=user_data_dir)
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=options)
    driver.set_page_load_timeout(60)

    try:
        driver.execute_script(
            "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
        )
    except Exception:
        pass

    return driver


def _driver_esta_vivo(driver):
    """Comprueba si el driver Selenium actual sigue respondiendo y conserva ventanas activas."""
    if driver is None:
        return False
    try:
        return bool(driver.window_handles) and driver.current_url is not None
    except Exception:
        return False


def _limpiar_perfil_runtime():
    """Elimina el perfil runtime solo si es realmente temporal."""
    global chrome_runtime_profile_dir
    try:
        if chrome_runtime_profile_dir:
            ruta = Path(chrome_runtime_profile_dir)
            ruta_persistente = Path(CHROME_FALLBACK_USER_DATA_DIR)
            if ruta.resolve() != ruta_persistente.resolve():
                shutil.rmtree(ruta, ignore_errors=True)
    except Exception:
        pass
    chrome_runtime_profile_dir = None


def _sincronizar_runtime_a_perfil_base():
    """Copia de vuelta al perfil persistente los cambios válidos realizados durante la sesión automatizada."""
    global CHROME_ACTIVE_USER_DATA_DIR, chrome_runtime_profile_dir
    try:
        if not chrome_runtime_profile_dir:
            return

        origen = Path(chrome_runtime_profile_dir)
        destino = Path(CHROME_USER_DATA_DIR)
        if not origen.exists():
            return

        destino.mkdir(parents=True, exist_ok=True)

        def _ignorar(_, nombres):
            ignorar = {
                "SingletonLock", "SingletonCookie", "SingletonSocket",
                "lockfile", "lockfile.lock", "LOCK", "lock",
                "Crashpad", "CrashpadMetrics-active.pma",
                "BrowserMetrics", "OptimizationHints",
                "ShaderCache", "GrShaderCache", "Code Cache",
                "GPUCache", "DawnCache", "Safe Browsing",
                "component_crx_cache", "pnacl", "CertificateRevocation",
            }
            return [n for n in nombres if n in ignorar or n.endswith('.lock')]

        shutil.copytree(origen, destino, dirs_exist_ok=True, ignore=_ignorar)
        CHROME_ACTIVE_USER_DATA_DIR = CHROME_USER_DATA_DIR
    except Exception:
        pass


def cerrar_driver_correos(sincronizar_perfil=False):
    """Cierra el driver activo de Correos y, opcionalmente, sincroniza la copia temporal del perfil."""
    global driver_correos, driver_correos_visible, CHROME_ACTIVE_USER_DATA_DIR

    try:
        if driver_correos is not None:
            driver_correos.quit()
    except Exception:
        pass

    driver_correos = None
    driver_correos_visible = False

    if sincronizar_perfil:
        _sincronizar_runtime_a_perfil_base()

    _limpiar_perfil_runtime()

    # IMPORTANTE: tras cerrar, volvemos siempre al perfil persistente
    CHROME_ACTIVE_USER_DATA_DIR = CHROME_USER_DATA_DIR


def _crear_copia_perfil_correos(origen: Path) -> Path:
    """Clona el perfil persistente de Chrome de Correos a una carpeta temporal para trabajar con seguridad."""
    origen = Path(origen)
    if not origen.exists():
        raise RuntimeError(
            f"No existe el perfil de Chrome de Correos en: {origen}\n"
            "Pulsa '🔐 Iniciar sesión Correos' primero para crear e iniciar sesión en ese perfil."
        )

    temp_root = Path(tempfile.mkdtemp(prefix="cps_correos_profile_"))
    destino = temp_root / "profile"

    def _ignorar(_, nombres):
        ignorar = {
            "SingletonLock", "SingletonCookie", "SingletonSocket",
            "lockfile", "lockfile.lock", "LOCK", "lock",
            "Crashpad", "CrashpadMetrics-active.pma",
            "BrowserMetrics", "OptimizationHints",
            "ShaderCache", "GrShaderCache", "Code Cache",
            "GPUCache", "DawnCache", "Safe Browsing",
            "component_crx_cache", "pnacl", "CertificateRevocation",
        }
        return [n for n in nombres if n in ignorar or n.endswith(".lock")]

    shutil.copytree(origen, destino, ignore=_ignorar, dirs_exist_ok=True)
    return destino


def obtener_driver_correos(headless=True, forzar_nuevo=False):
    """Devuelve un driver listo para usar usando un perfil persistente dedicado para Selenium."""
    global driver_correos, driver_correos_visible, CHROME_ACTIVE_USER_DATA_DIR, chrome_runtime_profile_dir

    _limpiar_referencia_login_chrome()

    if _hay_login_chrome_abierto():
        raise RuntimeError(
            "El Chrome de inicio de sesión sigue abierto.\n"
            "Ciérralo después de iniciar sesión y vuelve a lanzar el proceso automático."
        )

    if not forzar_nuevo and _driver_esta_vivo(driver_correos):
        return driver_correos

    cerrar_driver_correos()

    # PERFIL PERSISTENTE PARA LA AUTOMATIZACIÓN
    chrome_runtime_profile_dir = Path(CHROME_FALLBACK_USER_DATA_DIR)
    chrome_runtime_profile_dir.mkdir(parents=True, exist_ok=True)

    CHROME_ACTIVE_USER_DATA_DIR = chrome_runtime_profile_dir

    driver_correos = crear_driver_correos(
        headless=headless,
        user_data_dir=chrome_runtime_profile_dir,
    )
    driver_correos_visible = not headless
    return driver_correos


def abrir_login_correos():
    """Abre una ventana de Chrome real con el mismo perfil que usa la automatización de Correos."""
    global CHROME_ACTIVE_USER_DATA_DIR, chrome_login_process
    try:
        cerrar_driver_correos()
        _limpiar_referencia_login_chrome()

        user_data_dir = Path(CHROME_FALLBACK_USER_DATA_DIR)
        user_data_dir.mkdir(parents=True, exist_ok=True)
        CHROME_ACTIVE_USER_DATA_DIR = user_data_dir

        chrome_exe = _localizar_ejecutable_chrome()
        if not chrome_exe:
            raise RuntimeError(
                "No se ha encontrado Google Chrome en este equipo. "
                "Instálalo o ajusta manualmente la ruta de chrome.exe en el código."
            )

        cmd = [
            chrome_exe,
            f"--user-data-dir={user_data_dir}",
            "--profile-directory=Default",
            "--new-window",
            CORREOS_LOGIN_URL,
        ]
        chrome_login_process = subprocess.Popen(cmd)

        etiqueta_estado.config(
            text=(
                "🔐 Chrome abierto para Correos con el perfil de automatización.\n"
                "Comprueba la sesión y, cuando termines, cierra esa ventana."
            )
        )
    except Exception as e:
        print(traceback.format_exc())
        messagebox.showerror(
            "Correos",
            "No se pudo abrir Chrome para iniciar sesión.\n\n"
            f"Detalle: {e}"
        )
        etiqueta_estado.config(text=f"❌ Error al abrir Chrome de Correos: {e}")

def esperar_clickable_robusto(driver, locator, timeout=30):
    """Espera a que un elemento exista, se centre en pantalla y quede realmente clickable."""
    wait = WebDriverWait(driver, timeout)
    elem = wait.until(EC.presence_of_element_located(locator))
    driver.execute_script(
        "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
        elem
    )
    time.sleep(0.3)
    return wait.until(EC.element_to_be_clickable(locator))


def esperar_elemento_estable(driver, locator, timeout=30):
    """Espera a que un elemento deje de volverse stale y pueda usarse con cierta estabilidad."""
    wait = WebDriverWait(driver, timeout)
    # Forzamos a que el elemento exista y aguante dos lecturas seguidas sin quedar stale.
    fin = time.time() + timeout
    ultimo = None
    while time.time() < fin:
        try:
            elem = wait.until(EC.presence_of_element_located(locator))
            driver.execute_script(
                "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
                elem
            )
            _ = elem.is_displayed()
            time.sleep(0.4)
            elem = driver.find_element(*locator)
            _ = elem.is_enabled()
            return elem
        except (StaleElementReferenceException, TimeoutException) as e:
            ultimo = e
            time.sleep(0.4)
    if ultimo:
        raise ultimo
    raise TimeoutException(f'No se pudo estabilizar el elemento: {locator}')

def esperar_generador_correos(driver, timeout=20):
    """Espera hasta que aparezca el generador de etiquetas de Correos o detecta que falta autenticación."""
    def _condicion(d):
        if d.find_elements(By.ID, "myform:tipocarga:1"):
            return "generador"
        if d.find_elements(By.ID, "myform:fileUpload"):
            return "generador"
        if _pagina_parece_login_correos(d):
            return "login"
        return False

    try:
        estado = WebDriverWait(driver, timeout).until(_condicion)
    except TimeoutException as e:
        raise RuntimeError(
            f"Correos no mostró el generador de etiquetas en {timeout}s. "
            "Seguramente no hay sesión iniciada o la web no respondió correctamente. "
            "Pulsa '🔐 Iniciar sesión Correos' y vuelve a intentarlo."
        ) from e

    if estado == "login":
        raise RuntimeError(
            "No hay sesión iniciada en Correos. Pulsa '🔐 Iniciar sesión Correos', entra manualmente y vuelve a intentarlo."
        )


def enfocar_pestana_correos(driver):
    """Intenta activar la pestaña del navegador que contiene el portal de Correos."""
    try:
        handles = list(driver.window_handles)
    except Exception:
        return False

    for handle in handles:
        try:
            driver.switch_to.window(handle)
            url = (driver.current_url or "").lower()
            title = (driver.title or "").lower()
            if "correos" in url or "correos" in title:
                return True
        except Exception:
            continue

    try:
        if handles:
            driver.switch_to.window(handles[-1])
            return True
    except Exception:
        pass
    return False


def postlibri_imprimir_pdf_descargado(pdf_path):
    """Procesa un PDF descargado desde Correos, genera sus etiquetas y las envía a la impresora Brother."""
    pdf_path = str(Path(pdf_path).resolve())
    if not os.path.exists(pdf_path):
        raise RuntimeError(f"No existe el PDF descargado: {pdf_path}")

    if fitz is None:
        raise RuntimeError("PyMuPDF es obligatorio para procesar el PDF descargado de Correos.")
    if Image is None:
        raise RuntimeError("Pillow es obligatorio para procesar el PDF descargado de Correos.")

    estado_impresora = postlibri_obtener_estado_impresora(POSTLIBRI_DEFAULT_PRINTER)
    if not estado_impresora["ok"]:
        raise RuntimeError(estado_impresora["text"])

    out_dir = None
    temp_dir = None
    try:
        out_dir, labels = postlibri_extraer_etiquetas_pdf(pdf_path)
        if not labels:
            raise RuntimeError(
                "No se detectaron etiquetas útiles en el PDF descargado de Correos. "
                "Revisa el PDF o ajusta las coordenadas PostLibri si el diseño ha cambiado."
            )

        template = postlibri_resolver_plantilla_predeterminada()
        lbxs = postlibri_generar_lbxs(labels, template, out_dir, usar_directorio_temporal=True)
        if not lbxs:
            raise RuntimeError("No se pudieron generar archivos LBX para la impresión Brother.")

        temp_dir = str(Path(lbxs[0]).resolve().parent)
        postlibri_imprimir_lbxs(lbxs, printer_name=POSTLIBRI_DEFAULT_PRINTER)

        return {
            "pdf": pdf_path,
            "out_dir": str(out_dir),
            "count": len(labels),
            "printer": POSTLIBRI_DEFAULT_PRINTER,
            "template": template,
        }
    finally:
        if temp_dir:
            shutil.rmtree(temp_dir, ignore_errors=True)




def postlibri_procesar_pdf_descargado_manual(pdf_path):
    """Lanza desde la UI el procesado e impresión de un PDF ya descargado previamente."""
    ventana_principal.after(0, lambda: barra_progreso.pack(pady=10))
    ventana_principal.after(0, lambda: barra_progreso.configure(mode="indeterminate"))
    ventana_principal.after(0, lambda: barra_progreso.start(12))
    ventana_principal.after(
        0,
        lambda: etiqueta_estado.config(
            text=(
                f"🟡 Procesando PDF descargado para Brother...\n"
                f"{os.path.basename(pdf_path)}"
            )
        ),
    )

    try:
        resultado = postlibri_imprimir_pdf_descargado(pdf_path)
        ventana_principal.after(
            0,
            lambda r=resultado: etiqueta_estado.config(
                text=(
                    f"✅ PDF procesado e impreso en Brother\n"
                    f"{os.path.basename(r['pdf'])}\n"
                    f"{r['count']} etiquetas → {r['printer']}"
                )
            ),
        )
    except Exception as e:
        print(traceback.format_exc())
        ventana_principal.after(0, lambda err=e: etiqueta_estado.config(text=f"❌ Error al imprimir PDF descargado: {err}"))
        ventana_principal.after(
            0,
            lambda err=e: messagebox.showerror(
                "Brother / PDF descargado",
                f"No se pudo procesar e imprimir el PDF descargado:\n{err}",
            ),
        )
    finally:
        ventana_principal.after(0, barra_progreso.stop)
        ventana_principal.after(0, barra_progreso.pack_forget)


def postlibri_seleccionar_pdf_descargado():
    """Permite seleccionar manualmente un PDF descargado desde Correos para imprimirlo con Brother."""
    initial_dir = CHROME_DOWNLOAD_DIR if CHROME_DOWNLOAD_DIR.exists() else Path.home()
    ruta = filedialog.askopenfilename(
        title="Seleccionar PDF descargado de Correos",
        initialdir=str(initial_dir),
        filetypes=[("PDF", "*.pdf")],
    )
    if not ruta:
        return
    threading.Thread(target=postlibri_procesar_pdf_descargado_manual, args=(ruta,), daemon=True).start()

def ui_set_estado(texto):
    if ventana_principal is not None:
        ventana_principal.after(0, lambda t=texto: etiqueta_estado.config(text=t))

def ui_show_error(titulo, mensaje):
    if ventana_principal is not None:
        ventana_principal.after(0, lambda: messagebox.showerror(titulo, mensaje))

def ui_barra_mostrar(modo="determinate", valor=0):
    if ventana_principal is not None:
        def _accion():
            barra_progreso.pack(pady=10)
            barra_progreso["mode"] = modo
            barra_progreso["value"] = valor
            if modo == "indeterminate":
                barra_progreso.start(12)
        ventana_principal.after(0, _accion)

def ui_barra_ocultar():
    if ventana_principal is not None:
        ventana_principal.after(0, barra_progreso.stop)
        ventana_principal.after(0, barra_progreso.pack_forget)
        
def subir_archivo_a_correos():
    """Ejecuta de extremo a extremo la subida del TXT a Correos, descarga el PDF generado y lo manda a impresión Brother."""
    if not ruta_archivo_actual:
        etiqueta_estado.config(text="❌ No hay archivo seleccionado")
        return

    ruta_abs = os.path.abspath(ruta_archivo_actual)
    if not os.path.exists(ruta_abs):
        etiqueta_estado.config(text="❌ El archivo seleccionado no existe")
        return

    ultimo_error = None

    for intento in range(2):
        try:
            ui_set_estado(
                "🟡 Conectando con Correos..."
                if not CORREOS_AUTOMATION_HEADLESS
                else "🟡 Conectando con Correos en segundo plano..."
            )

            # 1) Abrimos o reutilizamos una sesión válida de Chrome con el perfil persistente.
            driver = obtener_driver_correos(
                headless=CORREOS_AUTOMATION_HEADLESS,
                forzar_nuevo=(intento > 0),
            )

            download_dir = obtener_directorio_descargas_correos()
            limpiar_descargas_parciales(download_dir)
            pdfs_antes = listar_pdfs_descargados(download_dir)

            ui_set_estado("🟡 Abriendo Correos con la sesión guardada...")
            # 2) Navegamos al generador de etiquetas y comprobamos que la sesión siga autenticada.
            driver = obtener_driver_correos(
                headless=CORREOS_AUTOMATION_HEADLESS,
                forzar_nuevo=(intento > 0),
            )

            download_dir = obtener_directorio_descargas_correos()
            limpiar_descargas_parciales(download_dir)
            pdfs_antes = listar_pdfs_descargados(download_dir)

            # 2) ANTES de entrar al generador, obligamos a tener sesión válida
            asegurar_sesion_correos(driver, timeout=18)

            ui_set_estado("🟡 Verificando generador de Correos...")
            esperar_generador_correos(driver, timeout=12)

            ui_set_estado("🟡 Seleccionando tipo de carga...")
            hacer_click_robusto(driver, (By.ID, "myform:tipocarga:1"), timeout=30)

            ui_set_estado("🟡 Cargando TXT...")

            # 3) Subimos el TXT generado a la plataforma de Correos.
            input_file = WebDriverWait(driver, 30).until(
                EC.presence_of_element_located((By.ID, "myform:fileUpload"))
            )
            driver.execute_script(
                "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
                input_file,
            )
            input_file.send_keys(ruta_abs)

            WebDriverWait(driver, 30).until(
                lambda d: d.find_element(By.ID, "myform:fileUpload").get_attribute("value")
            )

            etiqueta_estado.config(text="🟡 Añadiendo elementos...")
            ventana_principal.update_idletasks()
            hacer_click_robusto(driver, (By.ID, "myform:btnAniadirFichTemp"), timeout=30)

            esperar_elemento_estable(
                driver,
                (By.ID, "myform:j_id_jsp_253607634_70"),
                timeout=60,
            )

            etiqueta_estado.config(text="🟡 Confirmando...")
            ventana_principal.update_idletasks()
            hacer_click_robusto(driver, (By.ID, "myform:j_id_jsp_253607634_70"), timeout=30, intentos=6)

            etiqueta_estado.config(text="🟡 Abriendo impresión...")
            ventana_principal.update_idletasks()
            esperar_clickable_robusto(
                driver,
                (By.XPATH, "//input[@type='submit' and @value='Imprimir' and @title='Imprimir']"),
                timeout=60,
            )
            hacer_click_robusto(
                driver,
                (By.XPATH, "//input[@type='submit' and @value='Imprimir' and @title='Imprimir']"),
                timeout=30,
            )

            etiqueta_estado.config(text="🟡 Solicitando PDF de etiqueta...")
            ventana_principal.update_idletasks()
            esperar_clickable_robusto(
                driver,
                (By.XPATH, "//input[@type='submit' and @value='Imprimir Etiqueta' and @title='Imprimir Etiqueta']"),
                timeout=60,
            )
            hacer_click_robusto(
                driver,
                (By.XPATH, "//input[@type='submit' and @value='Imprimir Etiqueta' and @title='Imprimir Etiqueta']"),
                timeout=30,
            )

            # 4) Esperamos a que Correos genere y descargue el PDF final de etiquetas.
            etiqueta_estado.config(text="🟡 Esperando descarga del PDF de Correos...")
            pdf_descargado = esperar_pdf_descargado_o_login(
                driver,
                download_dir,
                existentes=pdfs_antes,
                timeout=45,
            )
            etiqueta_estado.config(text="🟡 PDF descargado. Cerrando sesión de Correos...")
            ventana_principal.update_idletasks()

            cerrar_sesion_correos(driver, timeout=15)

            cerrar_driver_correos(sincronizar_perfil=True)

            etiqueta_estado.config(text="🟡 Generando etiquetas Brother desde el PDF descargado...")
            ventana_principal.update_idletasks()
            # 5) Convertimos el PDF descargado al formato de impresión Brother y lanzamos la cola.
            resultado_impresion = postlibri_imprimir_pdf_descargado(pdf_descargado)

            etiqueta_estado.config(
                text=(
                    f"✅ PDF de Correos procesado e impreso en Brother\n"
                    f"{os.path.basename(pdf_descargado)}\n"
                    f"Etiquetas: {resultado_impresion['count']}\n"
                    f"Carpeta BMP: {resultado_impresion['out_dir']}\n"
                    f"Impresora: {resultado_impresion['printer']}\n"
                    f"Sesión de Correos guardada"
                )
            )
            return


        except (InvalidSessionIdException, WebDriverException) as e:
            ultimo_error = e
            print(traceback.format_exc())
            cerrar_driver_correos()
            if intento == 0:
                etiqueta_estado.config(
                    text=(
                        "🟡 La sesión de Chrome se ha cerrado o ha fallado. "
                        "Reintentando con una copia limpia del perfil de Correos..."
                    )
                )
                ventana_principal.update_idletasks()
                time.sleep(1)
                continue
            break
        except Exception as e:
            ultimo_error = e
            print(traceback.format_exc())
            break

    etiqueta_estado.config(text=f"❌ Error en flujo Correos: {ultimo_error}")


# === GENERACIÓN DEL PREVIEW ===
def actualizar_progreso_preview(porcentaje, actual, total, restante):
    """Actualiza la barra y el texto de estado mientras se analiza el PDF para construir el preview."""
    barra_progreso["mode"] = "determinate"
    barra_progreso["value"] = porcentaje
    etiqueta_estado.config(
        text=f"🔄 Analizando... {porcentaje}% ({actual}/{total}) | ETA: {restante}s"
    )


def cargar_preview_secuencial_con_pymupdf(ruta):
    """Analiza el PDF secuencialmente con PyMuPDF y prepara la información necesaria para el preview."""
    global cache_preview_paginas

    total = obtener_total_paginas_con_pymupdf(ruta)
    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    ultimo_porcentaje = -1

    with fitz.open(ruta) as doc:
        for i in range(total):
            texto = extraer_texto_pagina_con_pymupdf_rapido(doc.load_page(i))
            if texto:
                preview_data, codigos = analizar_pagina_destino_espana(texto)
                linea = formatear_linea_preview(i, *preview_data)
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
                ventana_principal.after(0, actualizar_progreso_preview, porcentaje, actual, total, restante)

    cache_preview_paginas = cache_local
    ventana_principal.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview_secuencial_con_pypdf(ruta):
    """Analiza el PDF secuencialmente con pypdf y prepara la información necesaria para el preview."""
    global cache_preview_paginas

    reader = PdfReader(ruta)
    pages = reader.pages
    total = len(pages)
    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    ultimo_porcentaje = -1

    for i, pagina in enumerate(pages):
        texto = extraer_texto_pagina_con_pypdf(pagina)
        if TOKEN_SPAIN in texto.upper():
            preview_data, codigos = analizar_pagina_destino_espana(texto)
            linea = formatear_linea_preview(i, *preview_data)
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
            ventana_principal.after(0, actualizar_progreso_preview, porcentaje, actual, total, restante)

    cache_preview_paginas = cache_local
    ventana_principal.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview_en_paralelo(ruta):
    """Analiza el PDF en paralelo por rangos y degrada automáticamente a modo secuencial si algo falla."""
    global cache_preview_paginas

    total = obtener_total_paginas_pdf(ruta)
    workers = min(MAX_SCAN_WORKERS, total)
    if total < MIN_PARALLEL_PAGES or workers <= 1:
        if fitz is not None:
            return cargar_preview_secuencial_con_pymupdf(ruta)
        return cargar_preview_secuencial_con_pypdf(ruta)

    worker_fn = escanear_rango_con_pymupdf if fitz is not None else escanear_rango_con_pypdf
    rangos = construir_rangos_paginas(total, workers)

    paginas_preview = []
    cache_local = {}
    inicio = perf_counter()
    procesadas = 0
    ultimo_porcentaje = -1

    try:
        # Repartimos el documento en bloques y procesamos cada bloque en paralelo.
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
                    ventana_principal.after(0, actualizar_progreso_preview, porcentaje, procesadas, total, restante)

    except Exception:
        if fitz is not None:
            return cargar_preview_secuencial_con_pymupdf(ruta)
        return cargar_preview_secuencial_con_pypdf(ruta)

    paginas_preview.sort(key=lambda x: x[0])
    cache_preview_paginas = cache_local
    ventana_principal.after(0, mostrar_preview, ruta, paginas_preview)


def cargar_preview_pdf(ruta):
    """Punto de entrada del análisis previo del PDF; actualmente delega en la ruta paralela."""
    cargar_preview_en_paralelo(ruta)


def cerrar_preview(ventana):
    """Cierra el visor de páginas detectadas y restablece el mensaje principal de la aplicación."""
    global ventana_preview
    if ventana.winfo_exists():
        ventana.destroy()
    ventana_preview = None
    etiqueta_estado.config(text="Arrastra aquí tu PDF")


def mostrar_preview(pdf_path, paginas):
    """Muestra la lista de páginas detectadas para que el usuario elija cuáles desea procesar."""
    global ventana_preview

    barra_progreso.stop()
    barra_progreso.pack_forget()

    if not paginas:
        etiqueta_estado.config(text="❌ No se encontraron páginas de SPAIN")
        return

    etiqueta_estado.config(text="Selecciona las páginas a procesar")

    ventana = tk.Toplevel(ventana_principal)
    ventana_preview = ventana
    ventana.title("Seleccionar páginas")
    ventana.geometry("600x720")
    ventana.configure(bg=INFO_BG)
    ventana.protocol("WM_DELETE_WINDOW", lambda v=ventana: cerrar_preview(v))

    # ===== Helpers visuales =====
    def crear_boton(master, texto, comando, bg="#2d2d2d", fg="#ffffff", ancho=18, activebg=None):
        return tk.Button(
            master,
            text=texto,
            command=comando,
            bg=bg,
            fg=fg,
            activebackground=activebg or bg,
            activeforeground=fg,
            relief="flat",
            bd=0,
            font=("Segoe UI", 10, "bold"),
            padx=12,
            pady=8,
            cursor="hand2",
            width=ancho,
    )
    # ===== Cabecera =====
    topbar = tk.Frame(ventana, bg=INFO_BG)
    topbar.pack(fill="x", padx=12, pady=(12, 8))

    tk.Label(
        topbar,
        text="Selecciona los pedidos a procesar",
        font=("Segoe UI", 12, "bold"),
        bg=INFO_BG,
        fg=FG_COLOR,
    ).pack(side="left")

    acciones_top = tk.Frame(topbar, bg=INFO_BG)
    acciones_top.pack(side="right")

    # ===== Zona scroll =====

    contenedor = tk.Frame(ventana, bg=INFO_BG)
    contenedor.pack(fill="both", expand=True, padx=12, pady=(0, 10))

    canvas = tk.Canvas(
        contenedor,
        bg=INFO_BG,
        highlightthickness=0,
        bd=0,
    )
    scrollbar = tk.Scrollbar(contenedor, command=canvas.yview)
    frame = tk.Frame(canvas, bg=INFO_BG)

    canvas.create_window((0, 0), window=frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

    def _on_mousewheel(event):
        canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

    def _on_mousewheel_linux_up(event):
        canvas.yview_scroll(-1, "units")

    def _on_mousewheel_linux_down(event):
        canvas.yview_scroll(1, "units")

    def _activar_scroll_rueda(_event=None):
        canvas.bind_all("<MouseWheel>", _on_mousewheel)          # Windows / macOS
        canvas.bind_all("<Button-4>", _on_mousewheel_linux_up)   # Linux
        canvas.bind_all("<Button-5>", _on_mousewheel_linux_down) # Linux

    def _desactivar_scroll_rueda(_event=None):
        canvas.unbind_all("<MouseWheel>")
        canvas.unbind_all("<Button-4>")
        canvas.unbind_all("<Button-5>")

    canvas.bind("<Enter>", _activar_scroll_rueda)
    canvas.bind("<Leave>", _desactivar_scroll_rueda)
    frame.bind("<Enter>", _activar_scroll_rueda)
    frame.bind("<Leave>", _desactivar_scroll_rueda)

    checks = []

    tk.Label(
        frame,
        text=f"{'Nº Pedido':^10}    | {'Nombre':^32} | {'Código postal':^13}",
        font=("Consolas", 10, "bold"),
        bg=INFO_BG,
        fg="#aaaaaa",
    ).pack(anchor="w", padx=10, pady=(6, 8))

    filas_frame = tk.Frame(frame, bg=INFO_BG)
    filas_frame.pack(fill="both", expand=True)

    for idx, (i, linea) in enumerate(paginas):
        var = tk.BooleanVar(value=True)
        checks.append((i, var))

        fila_bg = INFO_BG if idx % 2 == 0 else "#2b2b2b"

        fila = tk.Frame(filas_frame, bg=fila_bg)
        fila.pack(fill="x", padx=6, pady=2)

        tk.Checkbutton(
            fila,
            text=linea,
            variable=var,
            bg=fila_bg,
            fg=FG_COLOR,
            activebackground=fila_bg,
            activeforeground=FG_COLOR,
            selectcolor="#333333",
            relief="flat",
            bd=0,
            font=("Consolas", 10),
            anchor="w",
            padx=8,
            pady=6,
        ).pack(anchor="w", fill="x")

    def seleccionar_todo():
        for _, var in checks:
            var.set(True)

    def deseleccionar_todo():
        for _, var in checks:
            var.set(False)

    def confirmar():
        seleccionadas = [i for i, var in checks if var.get()]
        if not seleccionadas:
            messagebox.showwarning("Selección vacía", "Debes seleccionar al menos un pedido.")
            return

        codigos_por_pagina = {
            i: cache_preview_paginas[i][1]
            for i in seleccionadas
            if i in cache_preview_paginas
        }

        ventana.destroy()
        etiqueta_estado.config(text="Procesando selección...")
        iniciar_proceso_filtrado(seleccionadas, codigos_por_pagina)

    def cancelar():
        cerrar_preview(ventana)

    crear_boton(
        acciones_top,
        "✓ Seleccionar todo",
        seleccionar_todo,
        bg="#3b5875",
        activebg="#49698a",
        ancho=16,
    ).pack(side="left", padx=4)

    crear_boton(
        acciones_top,
        "✕ Deseleccionar",
        deseleccionar_todo,
        bg="#5a5f6b",
        activebg="#6a7080",
        ancho=16,
    ).pack(side="left", padx=4)


    # ===== Botonera inferior =====
    bottom = tk.Frame(ventana, bg=INFO_BG)
    bottom.pack(fill="x", padx=12, pady=(0, 14))

    crear_boton(
        bottom,
        "Cancelar",
        cancelar,
        bg="#4a4f59",
        activebg="#5a6070",
        ancho=14,
    ).pack(side="left")

    crear_boton(
        bottom,
        "Procesar selección",
        confirmar,
        bg="#2f8f4e",
        activebg="#3aa95b",
        ancho=18,
    ).pack(side="right")

# === GENERACIÓN FINAL DESDE CACHÉ ===
def worker_generacion_desde_cache(paginas_seleccionadas, cola_local, codigos_por_pagina):
    """Genera la lista final de códigos a partir de la selección hecha por el usuario y reporta progreso por cola."""
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

    cola_local.put(("fin", guardar_codigos_postales_txt(codigos_finales)))


def iniciar_proceso_filtrado(paginas, codigos_por_pagina):
    """Inicializa el hilo que genera el TXT final y activa el sondeo de mensajes hacia la interfaz."""
    global cola_ui, proceso_en_curso

    proceso_en_curso = True
    barra_progreso.pack(pady=10)
    barra_progreso["mode"] = "determinate"
    barra_progreso["value"] = 0

    cola_ui = Queue()
    threading.Thread(
        target=worker_generacion_desde_cache,
        args=(paginas, cola_ui, codigos_por_pagina),
        daemon=True,
    ).start()

    actualizar_interfaz_desde_cola()


def actualizar_interfaz_desde_cola():
    """Consume los mensajes de progreso y fin emitidos por el worker para mantener la UI sincronizada."""
    global proceso_en_curso, ruta_archivo_salida, ruta_archivo_actual

    try:
        # Consumimos todos los mensajes pendientes emitidos por el hilo de trabajo.
        while True:
            msg = cola_ui.get_nowait()
            tipo = msg[0]

            if tipo == "progreso":
                _, porcentaje, actual, total, restante = msg
                barra_progreso["mode"] = "determinate"
                barra_progreso["value"] = porcentaje
                etiqueta_estado.config(
                    text=f"⚙️ Procesando... {porcentaje}% ({actual}/{total}) | ETA: {restante}s"
                )
                continue

            if tipo == "fin":
                ruta_archivo_salida = msg[1]
                ruta_archivo_actual = ruta_archivo_salida
                actualizar_estado_botones()
                proceso_en_curso = False
                barra_progreso.stop()
                barra_progreso.pack_forget()
                etiqueta_estado.config(
                    text=(
                        f"✅ {os.path.basename(ruta_archivo_salida)} generado\n"
                        "🟡 Lanzando subida automática a Correos..."
                    )
                )
                ventana_principal.after(
                    300,
                    lambda: threading.Thread(target=subir_archivo_a_correos, daemon=True).start()
                )

    except Empty:
        pass

    if proceso_en_curso:
        ventana_principal.after(UI_POLL_MS, actualizar_interfaz_desde_cola)


# === ACCIONES AUXILIARES DE INTERFAZ ===
def seleccionar_archivo():
    """Permite seleccionar manualmente un TXT ya existente para reutilizarlo dentro de la aplicación."""
    global ruta_archivo_actual

    ruta = filedialog.askopenfilename(filetypes=[("TXT", "*.txt")])
    if not ruta:
        return

    ruta_archivo_actual = ruta
    etiqueta_estado.config(text=f"📄 {os.path.basename(ruta)} seleccionado")
    actualizar_estado_botones()


def copiar_ruta():
    """Copia al portapapeles el directorio del archivo actualmente seleccionado."""
    if not ruta_archivo_actual:
        return

    ventana_principal.clipboard_clear()
    ventana_principal.clipboard_append(os.path.dirname(ruta_archivo_actual))
    etiqueta_estado.config(text="📋 Ruta copiada")


def abrir_carpeta():
    """Abre en el explorador la carpeta que contiene el archivo actualmente seleccionado."""
    if ruta_archivo_actual:
        os.startfile(os.path.dirname(ruta_archivo_actual))

def cambiar_modo_headless_ui(headless_var):
    global CORREOS_AUTOMATION_HEADLESS

    nuevo_valor = bool(headless_var.get())
    if CORREOS_AUTOMATION_HEADLESS == nuevo_valor:
        return

    CORREOS_AUTOMATION_HEADLESS = nuevo_valor

    try:
        cerrar_driver_correos(sincronizar_perfil=True)
    except Exception:
        pass

    ui_set_estado(
        "⚙️ Modo headless activado. Se aplicará en la próxima conexión a Correos."
        if CORREOS_AUTOMATION_HEADLESS
        else "🖥️ Modo visible activado. Se aplicará en la próxima conexión a Correos."
    )
    
def mostrar_menu_opciones(menu, boton):
    try:
        x = boton.winfo_rootx()
        y = boton.winfo_rooty() + boton.winfo_height()
        menu.tk_popup(x, y)
    finally:
        menu.grab_release()

# === EVENTOS DE INTERFAZ ===
def manejar_drop_pdf(event):
    """Gestiona el evento de arrastrar y soltar un PDF sobre la ventana principal."""
    ruta = event.data.strip("{}")

    barra_progreso.pack(pady=10)
    barra_progreso["mode"] = "determinate"
    barra_progreso["value"] = 0
    etiqueta_estado.config(text=f"🔄 Analizando PDF [{FAST_BACKEND_NAME}]...")

    threading.Thread(target=cargar_preview_pdf, args=(ruta,), daemon=True).start()


def actualizar_estado_botones():
    """Habilita o deshabilita los botones dependientes de la existencia de un archivo seleccionado."""
    estado = "normal" if ruta_archivo_actual else "disabled"
    if boton_abrir_carpeta is not None:
        boton_abrir_carpeta.config(state=estado)
    if boton_copiar_ruta is not None:
        boton_copiar_ruta.config(state=estado)
    if boton_subir_correos is not None:
        boton_subir_correos.config(state=estado)


# === INFORMACIÓN LEGAL ===
def mostrar_info_aplicacion():
    """Abre la ventana informativa con los datos de versión, autoría y licencia del programa."""
    ventana = tk.Toplevel(ventana_principal)
    ventana.title("Información")
    ventana.geometry("550x450")
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
        text="Desarrollado por: Chema\nVersión 1.3",
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


# === INTERFAZ PRINCIPAL ===
def main():
    """Construye la interfaz principal, registra eventos y arranca el bucle de la aplicación."""
    global ventana_principal, etiqueta_estado, barra_progreso, boton_abrir_carpeta, boton_copiar_ruta, boton_subir_correos, boton_postlibri, etiqueta_estado_impresora, boton_actualizar_impresora
    
    ventana_principal = TkinterDnD.Tk()
    ventana_principal.title("Extractor de Códigos Postales")
    ventana_principal.geometry("720x400")
    ventana_principal.configure(bg=BG_COLOR)
    ventana_principal.resizable(False, False)

    icon_path = resolver_ruta_recurso("icono.ico")
    if os.path.exists(icon_path):
        try:
            ventana_principal.iconbitmap(icon_path)
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

    frame = tk.Frame(ventana_principal, bg=BG_COLOR)
    frame.pack(expand=True)

    tk.Label(
        frame,
        text="Extractor de Códigos Postales",
        font=("Segoe UI", 16, "bold"),
        fg=FG_COLOR,
        bg=BG_COLOR,
    ).pack(pady=20)
    
    etiqueta_estado = tk.Label(frame, text="Arrastra aquí tu PDF", fg=TEXT_SECONDARY, bg=BG_COLOR)
    etiqueta_estado.pack(pady=10)

    estado_frame = tk.Frame(frame, bg=BG_COLOR)
    estado_frame.pack(pady=(0, 8))
    headless_var = tk.BooleanVar(value=CORREOS_AUTOMATION_HEADLESS)
    etiqueta_estado_impresora = tk.Label(
        estado_frame,
        text=f"Impresora: comprobando {POSTLIBRI_DEFAULT_PRINTER}...",
        fg="#f0ad4e",
        bg=BG_COLOR,
        font=("Segoe UI", 9, "bold"),
    )
    etiqueta_estado_impresora.pack(side="left", padx=(0, 8))

    boton_actualizar_impresora = tk.Button(
        estado_frame,
        text="🔄",
        command=lambda: postlibri_refrescar_estado_impresora(programar_siguiente=False),
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        relief="flat",
        width=3,
    )
    boton_actualizar_impresora.pack(side="left")

    barra_progreso = ttk.Progressbar(frame, length=300)

    frame_botones = tk.Frame(ventana_principal, bg=BG_COLOR)
    frame_botones.pack(side="bottom", fill="x", pady=15)

    frame_login = tk.Frame(frame_botones, bg=BG_COLOR)
    frame_login.pack(side="bottom", expand=True)
    menu_opciones = tk.Menu(
        ventana_principal,
        tearoff=0,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        activebackground="#3a3a3a",
        activeforeground=FG_COLOR,
        relief="flat",
        bd=0,
        font=("Segoe UI", 11, "bold"),
    )
    menu_opciones.add_command(
        label="🔑 Configurar credenciales",
        command=configurar_credenciales_correos,
    )
    menu_opciones.add_command(
        label="🗑️ Borrar credenciales",
        command=eliminar_credenciales_correos_ui,
    )
    menu_opciones.add_command(
        label="🔓 Cerrar sesión Correos",
        command=cerrar_sesion_correos_ui,
    )
    menu_opciones.add_separator()
    menu_opciones.add_checkbutton(
        label="👻 Ver ventanas de Chrome",
        variable=headless_var,
        onvalue=True,
        offvalue=False,
        command=lambda: cambiar_modo_headless_ui(headless_var),
    )
   
    boton_menu = tk.Button(
        ventana_principal,
        text="⋮",
        command=lambda: mostrar_menu_opciones(menu_opciones, boton_menu),
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        relief="flat",
        font=("Segoe UI", 12, "bold"),
        width=3,
        cursor="hand2",
    )
    boton_menu.place(relx=1.0, rely=0.0, anchor="ne", x=-8, y=8)
    tk.Button(
        frame_login,
        text="🖨️ Abrir PDF descargado e imprimir",
        command=postlibri_seleccionar_pdf_descargado,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
    ).pack(pady=5)

    boton_info = tk.Button(
        ventana_principal,
        text="ℹ",
        command=mostrar_info_aplicacion,
        bg=BUTTON_COLOR,
        fg=FG_COLOR,
        relief="flat",
        font=("Segoe UI", 10),
    )

    boton_info.place(relx=1.0, rely=1.0, anchor="se", x=-5, y=-5)
    ventana_principal.drop_target_register(DND_FILES)
    ventana_principal.dnd_bind("<<Drop>>", manejar_drop_pdf)
    postlibri_refrescar_estado_impresora()
    ventana_principal.mainloop()


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()
    main()
