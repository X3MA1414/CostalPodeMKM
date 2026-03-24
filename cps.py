import re
import os
import webbrowser
import multiprocessing as mp
from datetime import datetime
from time import time
from pypdf import PdfReader
import tkinter as tk
from tkinter import ttk
from tkinterdnd2 import DND_FILES, TkinterDnD

ruta_salida_global = None
cola = None
procesando = False
inicio_tiempo = None

# === COLORES ===
BG_COLOR = "#1e1e1e"
FG_COLOR = "#ffffff"
BUTTON_COLOR = "#2d2d2d"
BUTTON_HOVER = "#3a3a3a"

# === REGEX EUROPA ===
PATRON_CP = re.compile(
    r"(?<!\w)(\d{5}|\d{4}-\d{3}|\d{4}\s?[A-Z]{2}|[A-Z]{1,2}\d[A-Z\d]?\s?\d[A-Z]{2})(?!\w)"
)

# === NOMBRE ÚNICO ===
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

# === FUNCIÓN PARALELA ===
def extraer_texto_pagina(args):
    pdf_path, i = args
    reader = PdfReader(pdf_path)
    pagina = reader.pages[i]

    texto = pagina.extract_text()
    if texto:
        return i, PATRON_CP.findall(texto)
    return i, []

# === PROCESO ===
def proceso_worker(pdf_path, cola):
    reader = PdfReader(pdf_path)
    total = len(reader.pages)

    pool = mp.Pool(mp.cpu_count())
    resultados = []

    for i, resultado in enumerate(pool.imap_unordered(
        extraer_texto_pagina,
        [(pdf_path, idx) for idx in range(total)]
    )):
        resultados.append(resultado)

        progreso = int((i + 1) / total * 100)
        cola.put(("progreso", progreso, i + 1, total))

    pool.close()
    pool.join()

    resultados.sort(key=lambda x: x[0])

    codigos = []
    for _, lista in resultados:
        codigos.extend([cp.upper().strip() for cp in lista])

    escritorio = os.path.join(os.path.expanduser("~"), "Desktop")
    fecha = datetime.now().strftime("%d_%m_%Y")
    carpeta = os.path.join(escritorio, "Pedidos_CP", fecha)
    os.makedirs(carpeta, exist_ok=True)

    ruta_base = os.path.join(carpeta, "cps.txt")
    ruta_final = obtener_nombre_unico(ruta_base)

    with open(ruta_final, "w", encoding="utf-8") as f:
        f.write("\n".join(codigos))

    cola.put(("fin", ruta_final))

# === INICIAR ===
def iniciar_proceso(ruta):
    global cola, procesando, inicio_tiempo

    cola = mp.Queue()
    procesando = True
    inicio_tiempo = time()

    barra.pack(pady=10)
    barra["value"] = 0

    boton_abrir.config(state="disabled")
    boton_correo.config(state="disabled")

    proceso = mp.Process(target=proceso_worker, args=(ruta, cola))
    proceso.start()

    actualizar_ui()

# === UI UPDATE ===
def actualizar_ui():
    global procesando, ruta_salida_global

    try:
        while True:
            msg = cola.get_nowait()

            if msg[0] == "progreso":
                _, valor, actual, total = msg
                barra["value"] = valor

                tiempo = time() - inicio_tiempo
                velocidad = tiempo / actual
                restante = velocidad * (total - actual)

                etiqueta.config(
                    text=f"Procesando... {valor}%\n{actual}/{total} páginas\nETA: {int(restante)}s"
                )

            elif msg[0] == "fin":
                ruta_salida_global = msg[1]
                procesando = False

                barra.pack_forget()

                etiqueta.config(text=f"✅ Guardado en:\n{ruta_salida_global}")
                boton_abrir.config(state="normal")
                boton_correo.config(state="normal")

    except:
        pass

    if procesando:
        app.after(100, actualizar_ui)

# === EVENTOS ===
def drop(event):
    ruta = event.data.strip("{}")
    iniciar_proceso(ruta)

def abrir_carpeta():
    if ruta_salida_global:
        os.startfile(os.path.dirname(ruta_salida_global))

def abrir_correos():
    webbrowser.open("https://epostal.correos.es/OV2PREENVWEB/jsp/mioficinavirtual/_rlvid.jsp.faces?_rap=mov_generadorEtiquetasORHandler.mostrarVista&_rvip=/jsp/mioficinavirtual/miCuenta.jsp")

def on_enter(e):
    e.widget["background"] = BUTTON_HOVER

def on_leave(e):
    e.widget["background"] = BUTTON_COLOR

# === INFO ===
def mostrar_info():
    ventana = tk.Toplevel(app)
    ventana.title("Información")
    ventana.geometry("420x350")
    ventana.configure(bg=BG_COLOR)
    ventana.resizable(False, False)

    # === TÍTULO ===
    tk.Label(
        ventana,
        text="Extractor de Códigos Postales",
        font=("Segoe UI", 12, "bold"),
        fg=FG_COLOR,
        bg=BG_COLOR
    ).pack(pady=(10, 5))

    # === AUTOR / VERSION ===
    tk.Label(
        ventana,
        text="Desarrollado por: Chema\nVersión: 1.0",
        font=("Segoe UI", 10),
        fg="#cccccc",
        bg=BG_COLOR,
        justify="center"
    ).pack(pady=(0, 10))

    # === CONTENEDOR SCROLL ===
    frame_texto = tk.Frame(ventana, bg=BG_COLOR)
    frame_texto.pack(fill="both", expand=True, padx=10, pady=5)

    scrollbar = tk.Scrollbar(frame_texto)
    scrollbar.pack(side="right", fill="y")

    texto = tk.Text(
        frame_texto,
        wrap="word",
        yscrollcommand=scrollbar.set,
        bg="#2a2a2a",
        fg=FG_COLOR,
        font=("Segoe UI", 9),
        relief="flat"
    )
    texto.pack(fill="both", expand=True)

    scrollbar.config(command=texto.yview)

    # === LICENCIA ===
    licencia = """Copyright (c) 2026 José María Ibáñez Martínez

Todos los derechos reservados.

Este software y la documentación asociada están protegidos por derechos de autor.
No se permite su copia, modificación, distribución, sublicencia, uso comercial
ni cualquier otro uso sin autorización expresa y por escrito del autor.

Este software está destinado únicamente a uso personal o interno.

EL SOFTWARE SE PROPORCIONA "TAL CUAL", SIN GARANTÍA DE NINGÚN TIPO,
EXPRESA O IMPLÍCITA, INCLUYENDO, PERO NO LIMITADO A, GARANTÍAS DE
COMERCIABILIDAD, IDONEIDAD PARA UN PROPÓSITO PARTICULAR Y NO INFRACCIÓN.

EN NINGÚN CASO EL AUTOR SERÁ RESPONSABLE DE NINGÚN DAÑO, RECLAMACIÓN
O RESPONSABILIDAD, YA SEA EN UNA ACCIÓN CONTRACTUAL, AGRAVIO O DE OTRO TIPO,
DERIVADO DE, O EN CONEXIÓN CON EL SOFTWARE O EL USO DEL MISMO.
"""

    texto.insert("1.0", licencia)
    texto.config(state="disabled")  # solo lectura
# === UI ===
app = TkinterDnD.Tk()
app.title("Extractor de Códigos Postales")
app.geometry("520x400")
app.configure(bg=BG_COLOR)

frame = tk.Frame(app, bg=BG_COLOR)
frame.pack(expand=True)

tk.Label(frame, text="Extractor de Códigos Postales",
         font=("Segoe UI", 16, "bold"),
         fg=FG_COLOR, bg=BG_COLOR).pack(pady=15)

etiqueta = tk.Label(frame, text="Arrastra aquí tu PDF",
                    font=("Segoe UI", 12),
                    fg="#cccccc", bg=BG_COLOR)
etiqueta.pack(pady=10)

barra = ttk.Progressbar(frame, orient="horizontal", length=300)

# === BOTONES ===
frame_botones = tk.Frame(app, bg=BG_COLOR)
frame_botones.pack(side="bottom", fill="x", pady=15)

boton_abrir = tk.Button(frame_botones, text="📂 Abrir carpeta",
                        state="disabled", command=abrir_carpeta,
                        bg=BUTTON_COLOR, fg=FG_COLOR, relief="flat")
boton_abrir.pack(side="left", expand=True, padx=20)
boton_abrir.bind("<Enter>", on_enter)
boton_abrir.bind("<Leave>", on_leave)

boton_correo = tk.Button(frame_botones, text="🌐 Abrir correos",
                         state="disabled", command=abrir_correos,
                         bg=BUTTON_COLOR, fg=FG_COLOR, relief="flat")
boton_correo.pack(side="left", expand=True, padx=20)
boton_correo.bind("<Enter>", on_enter)
boton_correo.bind("<Leave>", on_leave)

# === BOTÓN INFO ===
boton_info = tk.Button(app, text="ℹ️", command=mostrar_info,
                       bg=BUTTON_COLOR, fg=FG_COLOR,
                       relief="flat", font=("Segoe UI", 10))

boton_info.place(relx=1.0, rely=1.0, anchor="se", x=-10, y=-10)
boton_info.bind("<Enter>", on_enter)
boton_info.bind("<Leave>", on_leave)

# === DRAG & DROP ===
app.drop_target_register(DND_FILES)
app.dnd_bind("<<Drop>>", drop)

if __name__ == "__main__":
    mp.freeze_support()
    app.mainloop()
