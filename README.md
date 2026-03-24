# 📦 Extractor de Códigos Postales (Europa)

Aplicación de escritorio desarrollada en Python que permite extraer automáticamente códigos postales de documentos PDF, manteniendo el orden original y soportando múltiples formatos europeos.

---

## 🚀 Características

- 📄 Extracción automática de códigos postales desde PDF
- 🌍 Soporte para formatos europeos:
  - España, Francia, Alemania, Italia (5 dígitos)
  - Portugal (`1234-567`)
  - Países Bajos (`1234 AB`)
  - Reino Unido (`SW1A 1AA`)
- ⚡ Procesamiento paralelo (multiprocessing)
- 🧊 Interfaz fluida (sin bloqueos)
- 📊 Barra de progreso + estimación de tiempo (ETA)
- 🖱️ Drag & Drop (arrastrar y soltar PDF)
- 🌙 Interfaz moderna en modo oscuro
- 📁 Guardado automático en:

Escritorio/Pedidos_CP/Día_Mes_Año/

- 🧾 Generación de archivos sin sobrescribir
- 📂 Acceso rápido a la carpeta generada
- 🌐 Botón para abrir URL personalizada
- ℹ️ Ventana de información integrada

---

## 🖥️ Vista general

Aplicación ligera con interfaz gráfica basada en Tkinter, diseñada para uso rápido y eficiente sin necesidad de configuración compleja.

---

## 📦 Requisitos

- Python 3.10 o superior
- Windows (para versión ejecutable `.exe`)

---

📁 Estructura de salida
Escritorio/
└── Pedidos_CP/
    └── 24_03_2026/
        ├── cps.txt
        ├── cps(1).txt
        └── cps(2).txt
        
⚙️ Tecnologías utilizadas
Python
Tkinter (interfaz gráfica)
multiprocessing (paralelización)
pypdf (lectura de PDFs)
tkinterdnd2 (drag & drop)
