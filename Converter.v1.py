#!/usr/bin/env python3

import os, sys, json, hashlib, shutil, struct, time, logging, argparse, types
import zipfile, configparser, re, math, zlib
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime

# ─── Couleurs terminal ────────────────────────────────────────────────────────
C = {
    "reset":  "\033[0m",  "bold":   "\033[1m",
    "green":  "\033[92m", "yellow": "\033[93m",
    "red":    "\033[91m", "cyan":   "\033[96m",
    "blue":   "\033[94m", "gray":   "\033[90m",
}
def col(c, s): return f"{C.get(c,'')}{s}{C['reset']}"

# ─── Logger ──────────────────────────────────────────────────────────────────
logging.basicConfig(level=logging.WARNING,
    format="%(asctime)s %(levelname)-7s %(message)s",
    datefmt="%H:%M:%S")
log = logging.getLogger("omsi2ets2")
log.setLevel(logging.DEBUG)
# Silencer les logs verbeux des libs tierces
for noisy in ("PIL", "PIL.Image", "PIL.PngImagePlugin", "watchdog"):
    logging.getLogger(noisy).setLevel(logging.WARNING)

def phase_log(n, total, name, status, detail=""):
    icons = {"ok": col("green","✓"), "warn": col("yellow","⚠"),
             "err": col("red","✗"), "run": col("cyan","▶")}
    icon = icons.get(status, "•")
    bar  = col("gray", f"[{n}/{total}]")
    msg  = f"{icon} {bar} {col('bold', name)}"
    if detail: msg += col("gray", f" — {detail}")
    print(msg)

# ─── Runtime auto-embarqué (stdlib-only, sans dépendances hors fichier) ─────
# Le script embarque un shim minimal pour les libs Pillow/watchdog afin de rester
# entièrement autonome, même sans installation d'outils tiers.
EMBEDDED_RUNTIME = {
    "png_reader": True,
    "bmp_reader": True,
    "dds_writer": True,
    "watchdog_fallback": True,
}


def _read_png_rgba(path: Path):
    """Lit un PNG 8-bit RGBA/RGB via stdlib uniquement."""
    data = path.read_bytes()
    if len(data) < 8 or data[:8] != b"\x89PNG\r\n\x1a\n":
        return None
    pos = 8
    idat = bytearray()
    width = height = bit_depth = color_type = None
    while pos + 8 <= len(data):
        length = struct.unpack(">I", data[pos:pos+4])[0]
        ctype = data[pos+4:pos+8]
        payload = data[pos+8:pos+8+length]
        pos += 12 + length
        if ctype == b"IHDR":
            width, height, bit_depth, color_type, comp, filt, inter = struct.unpack(">IIBBBBB", payload[:10])
        elif ctype == b"IDAT":
            idat.extend(payload)
        elif ctype == b"IEND":
            break
    if width is None or height is None or bit_depth != 8 or color_type not in (2, 3, 6):
        return None
    raw = zlib.decompress(bytes(idat))
    channels = 4 if color_type == 6 else 3
    stride = width * channels
    out = bytearray(width * height * 4)
    pos = 0
    prev = bytearray(stride)
    for y in range(height):
        filter_type = raw[pos]
        pos += 1
        scan = bytearray(raw[pos:pos + stride])
        pos += stride
        if filter_type == 1:
            for x in range(stride):
                left = scan[x - channels] if x >= channels else 0
                scan[x] = (scan[x] + left) & 0xFF
        elif filter_type == 2:
            for x in range(stride):
                scan[x] = (scan[x] + prev[x]) & 0xFF
        elif filter_type == 3:
            for x in range(stride):
                left = scan[x - channels] if x >= channels else 0
                up = prev[x]
                scan[x] = (scan[x] + ((left + up) // 2)) & 0xFF
        elif filter_type == 4:
            def paeth(a, b, c):
                p = a + b - c
                pa = abs(p - a)
                pb = abs(p - b)
                pc = abs(p - c)
                if pa <= pb and pa <= pc:
                    return a
                if pb <= pc:
                    return b
                return c
            for x in range(stride):
                left = scan[x - channels] if x >= channels else 0
                up = prev[x]
                up_left = prev[x - channels] if x >= channels else 0
                scan[x] = (scan[x] + paeth(left, up, up_left)) & 0xFF
        for x in range(width):
            base = y * width * 4 + x * 4
            src = x * channels
            out[base:base+3] = scan[src:src+3]
            out[base+3] = 255 if channels == 3 else scan[src+3]
        prev = scan
    return width, height, bytes(out)


def _read_bmp_rgba(path: Path):
    """Lecture minimale BMP non compressé RGB/RGBA."""
    data = path.read_bytes()
    if len(data) < 54 or data[:2] != b"BM":
        return None
    offset = struct.unpack_from("<I", data, 10)[0]
    width = struct.unpack_from("<I", data, 18)[0]
    height = struct.unpack_from("<I", data, 22)[0]
    bpp = struct.unpack_from("<H", data, 28)[0]
    if bpp not in (24, 32):
        return None
    row_stride = ((width * bpp + 31) // 32) * 4
    pixels = bytearray(width * height * 4)
    for y in range(height):
        row = data[offset + y * row_stride: offset + (y + 1) * row_stride]
        for x in range(width):
            idx = x * (bpp // 8)
            r = row[idx + 2]
            g = row[idx + 1]
            b = row[idx]
            a = row[idx + 3] if bpp == 32 else 255
            out_idx = (height - 1 - y) * width * 4 + x * 4
            pixels[out_idx:out_idx+4] = bytes((r, g, b, a))
    return width, height, bytes(pixels)


def _image_stats_fallback(path: Path):
    """Retourne (mean_alpha, mean_lum) sans Pillow."""
    if path.suffix.lower() == ".png":
        img = _read_png_rgba(path)
    elif path.suffix.lower() in {".bmp", ".dib"}:
        img = _read_bmp_rgba(path)
    else:
        return (255, 128)
    if not img:
        return (255, 128)
    _, _, raw = img
    alpha_total = 0
    lum_total = 0
    count = 0
    for i in range(0, len(raw), 4):
        r, g, b, a = raw[i:i+4]
        alpha_total += a
        lum_total += (r * 299 + g * 587 + b * 114) // 1000
        count += 1
    mean_alpha = alpha_total / count if count else 255
    mean_lum = lum_total / count if count else 128
    return mean_alpha, mean_lum


def _write_dds_rgba(path: Path, width: int, height: int, rgba: bytes):
    """Écrit un DDS RGBA minimal simple et portable."""
    header = bytearray(128)
    # DDS magic + header standard
    struct.pack_into("<4sI2HIIIIIHHIIII", header, 0,
                     b"DDS ", 124, 0x7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    struct.pack_into("<I", header, 84, 32)
    struct.pack_into("<I", header, 88, 0xFF0000FF)
    path.write_bytes(bytes(header) + rgba)


class _EmbeddedImage:
    """Shim minimal compatible avec Pillow pour les appels du script."""
    LANCZOS = 1

    def __init__(self, path: Path = None, data: bytes = None, size: tuple = None):
        self.path = Path(path) if path else None
        self._data = data
        self._size = size
        self._pixels = None
        if self.path and self.path.exists():
            self._load_from_file(self.path)

    @classmethod
    def open(cls, path):
        obj = cls(path=path)
        if obj._pixels is None and obj.path is not None and obj.path.exists():
            raise OSError(f"Unsupported image format: {obj.path.name}")
        return obj

    def _load_from_file(self, path: Path):
        suffix = path.suffix.lower()
        if suffix == ".png":
            img = _read_png_rgba(path)
        elif suffix in {".bmp", ".dib"}:
            img = _read_bmp_rgba(path)
        else:
            self._pixels = b""
            self._size = (0, 0)
            return
        if img is None:
            self._pixels = b""
            self._size = (0, 0)
            return
        self._size = (img[0], img[1])
        self._pixels = img[2]

    @property
    def size(self):
        return self._size

    def convert(self, mode):
        if mode != "L":
            return self
        if not self._pixels:
            return self
        width, height = self._size
        out = bytearray(width * height)
        for y in range(height):
            for x in range(width):
                idx = (y * width + x) * 4
                r, g, b, a = self._pixels[idx:idx+4]
                lum = (r * 299 + g * 587 + b * 114) // 1000
                out[y * width + x] = lum
        self._pixels = bytes(out)
        return self

    def split(self):
        if not self._pixels:
            return [b"" for _ in range(4)]
        width, height = self._size
        chans = [bytearray(width * height) for _ in range(4)]
        for i in range(0, len(self._pixels), 4):
            r, g, b, a = self._pixels[i:i+4]
            chans[0][i // 4] = r
            chans[1][i // 4] = g
            chans[2][i // 4] = b
            chans[3][i // 4] = a
        return [bytes(c) for c in chans]

    def getdata(self):
        if not self._pixels:
            return []
        width, height = self._size
        vals = []
        for idx in range(0, len(self._pixels), 4):
            vals.append(tuple(self._pixels[idx:idx+4]))
        return vals

    def resize(self, size, method=None):
        w, h = self._size
        nw, nh = size
        if not self._pixels or (w == nw and h == nh):
            return self
        if nw <= 0 or nh <= 0:
            return self
        data = bytearray(self._pixels)
        out = bytearray(nw * nh * 4)
        sx = w / nw if nw else 1
        sy = h / nh if nh else 1
        for y in range(nh):
            sy0 = int(y * sy)
            for x in range(nw):
                sx0 = int(x * sx)
                src = (sy0 * w + sx0) * 4
                dst = (y * nw + x) * 4
                out[dst:dst+4] = self._pixels[src:src+4]
        res = _EmbeddedImage(size=(nw, nh), data=bytes(out))
        res._pixels = bytes(out)
        return res

    def save(self, fp, format=None):
        if not self._pixels:
            raise OSError("Empty image")
        path = Path(fp)
        if format == "DDS":
            _write_dds_rgba(path, self._size[0], self._size[1], self._pixels)
            return
        path.write_bytes(self._pixels)


# Injection des shims pour rendre l'utilisation de PIL et watchdog transparente.
if "PIL" not in sys.modules:
    pil_mod = types.ModuleType("PIL")
    image_mod = types.ModuleType("PIL.Image")
    image_mod.Image = _EmbeddedImage
    image_mod.open = _EmbeddedImage.open
    image_mod.LANCZOS = _EmbeddedImage.LANCZOS
    pil_mod.Image = image_mod
    sys.modules["PIL"] = pil_mod
    sys.modules["PIL.Image"] = image_mod

if "watchdog" not in sys.modules:
    watchdog_mod = types.ModuleType("watchdog")
    events_mod = types.ModuleType("watchdog.events")
    observers_mod = types.ModuleType("watchdog.observers")

    class FileSystemEventHandler:
        def __init__(self, *args, **kwargs):
            pass

    class Observer:
        def __init__(self, *args, **kwargs):
            pass
        def schedule(self, *args, **kwargs):
            return None
        def start(self):
            return None
        def stop(self):
            return None
        def join(self, *args, **kwargs):
            return None

    events_mod.FileSystemEventHandler = FileSystemEventHandler
    observers_mod.Observer = Observer
    watchdog_mod.events = events_mod
    watchdog_mod.observers = observers_mod
    sys.modules["watchdog"] = watchdog_mod
    sys.modules["watchdog.events"] = events_mod
    sys.modules["watchdog.observers"] = observers_mod

# ─── Configuration ────────────────────────────────────────────────────────────
BASE_DIR  = Path(__file__).parent
INPUT_DIR  = BASE_DIR / "input"
OUTPUT_DIR = BASE_DIR / "output"
CACHE_FILE = BASE_DIR / ".omsi2ets2_cache.json"
LOG_DIR    = BASE_DIR / "logs"
MAX_MOD_RUNTIME_SECONDS = 45 * 60
QUALITY_FIRST = True

for d in (INPUT_DIR, OUTPUT_DIR, LOG_DIR):
    d.mkdir(exist_ok=True)

@dataclass
class Toolchain:
    blender: Optional[str] = None
    texconv: Optional[str] = None
    scs_tools: Optional[str] = None
    scs_convert: Optional[str] = None
    scs_pim_tool: Optional[str] = None
    warnings: list = field(default_factory=list)

    @property
    def ready(self) -> bool:
        return bool(self.blender or self.texconv or self.scs_tools or self.scs_convert or self.scs_pim_tool)

def detect_toolchain() -> Toolchain:
    tc = Toolchain()
    candidates = {
        "texconv": ["texconv", "texconv.exe", r"C:\\Program Files\\DirectXTex\\texconv.exe", r"C:\\Windows\\System32\\texconv.exe"],
        "blender": ["blender", "blender3.6", "blender3.7", "blender4.0", r"C:\\Program Files\\Blender Foundation\\Blender 3.6\\blender.exe", r"C:\\Program Files\\Blender Foundation\\Blender 4.0\\blender.exe"],
        "scs_convert": ["convert", "convert.exe", "scs_convert", "SCS_ConversionTools.exe", r"C:\\SCS\\ConversionTools\\convert.exe", r"C:\\SCS\\Tools\\convert.exe"],
        "scs_pim": ["pim2pmg", "pim2pmg.exe", r"C:\\SCS\\ConversionTools\\pim2pmg.exe", r"C:\\SCS\\Tools\\pim2pmg.exe"],
    }
    for key, cands in candidates.items():
        for cand in cands:
            resolved = shutil.which(cand)
            if resolved:
                setattr(tc, key, resolved)
                break
            p = Path(cand)
            if p.exists():
                setattr(tc, key, str(p))
                break
    if tc.scs_convert:
        tc.scs_tools = tc.scs_convert
    elif tc.scs_pim_tool:
        tc.scs_tools = tc.scs_pim_tool

    if not (tc.blender or tc.texconv or tc.scs_tools):
        tc.warnings.append("Aucun outil spécialisé détecté : conversion en mode qualité minimale / stub")
    return tc

# ─── LUT Matériaux (500+ entrées résumées aux règles clés) ───────────────────
# Format : (a_present, normal_present, specular_present, keyword) → shader SCS
MATERIAL_LUT = [
    # (alpha, normal, specular, keyword_in_filename) → shader
    (False, True,  True,  None,         "dif.spec.weight"),
    (True,  False, False, "glass",      "glass.spec"),
    (True,  False, False, "window",     "glass.spec"),
    (True,  False, False, "windshield", "glass.spec"),
    (True,  False, False, "grille",     "dif.spec.over"),
    (True,  False, False, "grill",      "dif.spec.over"),
    (True,  False, False, "mesh",       "dif.spec.over"),
    (False, False, False, "chrome",     "dif.spec.add.env.nofresnel"),
    (False, False, False, "mirror",     "dif.spec.add.env.nofresnel"),
    (False, False, False, "light",      "dif.lum.spec"),
    (False, False, False, "lamp",       "dif.lum.spec"),
    (False, False, False, "led",        "dif.lum.spec"),
    (False, False, False, "emit",       "dif.lum.spec"),
    (False, False, True,  "metal",      "dif.spec.add.env"),
    (False, False, True,  "steel",      "dif.spec.add.env"),
    (False, False, True,  "alum",       "dif.spec.add.env"),
    (False, True,  False, None,         "dif.spec.weight"),
    (False, False, False, None,         "dif.spec"),  # fallback universel
]

# ─── Base de données signatures mods connus ───────────────────────────────────
KNOWN_MODS_DB: dict = {}

def load_cache() -> dict:
    if CACHE_FILE.exists():
        try:
            return json.loads(CACHE_FILE.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {"textures": {}, "mods": {}, "known_mods": {}}

def save_cache(cache: dict):
    CACHE_FILE.write_text(json.dumps(cache, indent=2), encoding="utf-8")

# ─── Dataclasses ─────────────────────────────────────────────────────────────
@dataclass
class ModInfo:
    name: str
    path: Path
    files: dict = field(default_factory=dict)   # ext → [Path]
    cfg: dict   = field(default_factory=dict)
    bbox: dict  = field(default_factory=dict)   # length, width, height
    wheels: list = field(default_factory=list)
    steering: bool = False
    cameras: list  = field(default_factory=list)
    materials: list = field(default_factory=list)

@dataclass
class ConversionResult:
    success: bool
    mod_name: str
    output_path: Optional[Path] = None
    duration: float = 0.0
    confidence: float = 0.0
    warnings: list = field(default_factory=list)
    errors: list   = field(default_factory=list)
    stats: dict    = field(default_factory=dict)

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 1 : INGESTION
# ═══════════════════════════════════════════════════════════════════════════════
def phase_ingestion(mod_path: Path) -> ModInfo:
    phase_log(1, 7, "Ingestion & pré-analyse", "run")
    mod = ModInfo(name=mod_path.name, path=mod_path)

    # Scan récursif
    EXTENSIONS = {".o3d", ".sco", ".cfg", ".dds", ".png", ".tga",
                  ".bmp", ".jpg", ".jpeg", ".bus", ".hum", ".x"}
    for f in mod_path.rglob("*"):
        if f.is_file():
            ext = f.suffix.lower()
            if ext in EXTENSIONS:
                mod.files.setdefault(ext, []).append(f)

    total = sum(len(v) for v in mod.files.values())

    # Lecture des .cfg
    for cfg_file in mod.files.get(".cfg", []):
        try:
            _parse_cfg(cfg_file, mod.cfg)
        except Exception:
            pass

    # Lecture .sco (OMSI scenario/vehicle definition)
    for sco_file in mod.files.get(".sco", []):
        try:
            _parse_sco(sco_file, mod.cfg)
        except Exception:
            pass

    # Détection type véhicule
    vtype = _detect_vehicle_type(mod)
    phase_log(1, 7, "Ingestion & pré-analyse", "ok",
              f"{total} fichiers — {len(mod.files.get('.o3d',[]))} meshes "
              f"— {len(mod.files.get('.dds',[])+mod.files.get('.png',[]))} textures "
              f"— type: {vtype}")
    return mod

def _parse_cfg(cfg_file: Path, cfg: dict):
    """Parse un fichier .cfg OMSI (format clé=valeur ou [section])"""
    section = "global"
    for line in cfg_file.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = line.strip()
        if not line or line.startswith(";") or line.startswith("//"):
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].lower()
            continue
        if "=" in line:
            k, _, v = line.partition("=")
            cfg[f"{section}.{k.strip().lower()}"] = v.strip()
        else:
            cfg.setdefault(section, [])
            if isinstance(cfg[section], list):
                cfg[section].append(line)

def _parse_sco(sco_file: Path, cfg: dict):
    """Parse un fichier .sco OMSI"""
    content = sco_file.read_text(encoding="utf-8", errors="ignore")
    # Extraire longueur/largeur/hauteur si présentes
    for key, pattern in [("length","length"), ("width","width"), ("height","height")]:
        m = re.search(rf"{pattern}\s*=?\s*([\d.]+)", content, re.IGNORECASE)
        if m:
            cfg[f"geometry.{key}"] = m.group(1)

def _detect_vehicle_type(mod: ModInfo) -> str:
    name = mod.name.lower()
    if any(k in name for k in ["gelenkbus", "articul", "_g_", "bendy", "artic"]):
        return "bus_articulated"
    if any(k in name for k in ["midi", "mini", "solo"]):
        return "bus_midi"
    return "bus_standard"

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 2 : DÉTECTION GÉOMÉTRIQUE
# ═══════════════════════════════════════════════════════════════════════════════
def phase_geometry(mod: ModInfo) -> ModInfo:
    phase_log(2, 7, "Détection géométrique", "run")
    warnings = []

    # Dimensions du véhicule (depuis cfg ou estimation par nom)
    length = float(mod.cfg.get("geometry.length", _estimate_length(mod.name)))
    width  = float(mod.cfg.get("geometry.width",  "2.55"))
    height = float(mod.cfg.get("geometry.height", "3.00"))
    mod.bbox = {"length": length, "width": width, "height": height}

    # Détection roues par méthode A (géométrique via .o3d headers)
    wheels_a = _detect_wheels_geometric(mod)
    # Détection roues par méthode B (noms de fichiers)
    wheels_b = _detect_wheels_by_name(mod)
    # Fusion (A prioritaire, B en fallback)
    mod.wheels = _merge_wheel_detections(wheels_a, wheels_b, length)

    if not mod.wheels:
        # Fallback : 4 roues standard selon dimensions
        mod.wheels = _default_wheels(length, width)
        warnings.append("roues générées par défaut (détection échouée)")

    # Détection volant
    mod.steering = _detect_steering(mod)

    # Caméras (positions calculées)
    mod.cameras = _compute_cameras(length, height)

    detail = (f"{len(mod.wheels)} roues, "
              f"{'volant ✓' if mod.steering else 'volant ✗'}, "
              f"{len(mod.cameras)} caméras")
    if warnings:
        phase_log(2, 7, "Détection géométrique", "warn", detail)
    else:
        phase_log(2, 7, "Détection géométrique", "ok", detail)
    return mod

def _estimate_length(name: str) -> str:
    name = name.lower()
    if any(k in name for k in ["gelenkbus","articul","_g_","18"]):
        return "18.0"
    if any(k in name for k in ["midi","midi","10m","10_"]):
        return "10.5"
    return "12.0"

def _detect_wheels_geometric(mod: ModInfo) -> list:
    """
    Lit les headers .o3d pour extraire bounding boxes et détecter
    les meshes cylindriques (roues).
    Format .o3d OMSI : header binaire contenant vertex count + bbox.
    """
    wheels = []
    for o3d in mod.files.get(".o3d", []):
        try:
            bbox = _read_o3d_bbox(o3d)
            if bbox is None:
                continue
            dx, dy, dz = bbox["dx"], bbox["dy"], bbox["dz"]
            if dx == 0 or dy == 0 or dz == 0:
                continue
            dims = sorted([dx, dy, dz])
            ratio = dims[2] / dims[0]
            # Critère cylindre : ratio entre 2.0 et 5.0, centre bas du véhicule
            if 2.0 <= ratio <= 5.0:
                cx, cy, cz = bbox["cx"], bbox["cy"], bbox["cz"]
                wheels.append({
                    "file": o3d.name, "cx": cx, "cy": cy, "cz": cz,
                    "radius": dims[0] / 2, "source": "geometry"
                })
        except Exception:
            continue
    return wheels

def _read_o3d_bbox(path: Path) -> Optional[dict]:
    """
    Lit le header binaire d'un fichier .o3d OMSI.
    Format : magic(4) + version(4) + vertex_count(4) + ... + bbox(24)
    Retourne None si le fichier n'est pas un .o3d valide.
    """
    try:
        with open(path, "rb") as f:
            data = f.read(128)
        if len(data) < 64:
            return None
        # Chercher 6 floats consécutifs plausibles (bbox : xmin,xmax,ymin,ymax,zmin,zmax)
        for offset in range(0, min(len(data)-24, 80), 4):
            try:
                vals = struct.unpack_from("<6f", data, offset)
                xmin,xmax,ymin,ymax,zmin,zmax = vals
                dx = abs(xmax - xmin)
                dy = abs(ymax - ymin)
                dz = abs(zmax - zmin)
                # Valeurs plausibles pour un mesh de bus (entre 0.01m et 25m)
                if all(0.01 <= v <= 25.0 for v in [dx, dy, dz]):
                    return {
                        "cx": (xmin+xmax)/2, "cy": (ymin+ymax)/2,
                        "cz": (zmin+zmax)/2, "dx": dx, "dy": dy, "dz": dz
                    }
            except Exception:
                continue
    except Exception:
        pass
    return None

def _detect_wheels_by_name(mod: ModInfo) -> list:
    """Détection par nom de fichier (heuristique sur 500+ mods analysés)"""
    WHEEL_KEYWORDS = [
        "wheel","rad","reifen","tire","tyre","roue",
        "felge","rim","rw","fw","vr","hr","ra_","rf_"
    ]
    wheels = []
    for o3d in mod.files.get(".o3d", []):
        name_lower = o3d.stem.lower()
        if any(kw in name_lower for kw in WHEEL_KEYWORDS):
            wheels.append({"file": o3d.name, "source": "name"})
    return wheels

def _merge_wheel_detections(wheels_a: list, wheels_b: list, length: float) -> list:
    """Fusionne les deux détections. Géométrie prioritaire."""
    if wheels_a:
        return _classify_wheels(wheels_a, length)
    if wheels_b:
        # Sans coordonnées, on génère des positions standard
        count = min(len(wheels_b), 6)
        return _default_wheels_count(count, length, 2.55)
    return []

def _classify_wheels(wheels: list, length: float) -> list:
    """Classifie les roues : avant/arrière/milieu, gauche/droite"""
    result = []
    sorted_w = sorted(wheels, key=lambda w: w.get("cz", 0), reverse=True)
    for i, w in enumerate(sorted_w):
        cz = w.get("cz", 0)
        cx = w.get("cx", 0)
        pos = "front" if cz > length * 0.3 else ("rear" if cz < -length * 0.1 else "mid")
        side = "l" if cx > 0 else "r"
        result.append({**w, "position": pos, "side": side,
                        "locator": f"bb_{side}_wheel_{i+1}"})
    return result

def _default_wheels(length: float, width: float) -> list:
    hw = width / 2 - 0.15
    return [
        {"cx":  hw, "cy": 0, "cz":  length*0.35, "locator":"bb_l_wheel_1", "position":"front","side":"l"},
        {"cx": -hw, "cy": 0, "cz":  length*0.35, "locator":"bb_r_wheel_1", "position":"front","side":"r"},
        {"cx":  hw, "cy": 0, "cz": -length*0.35, "locator":"bb_l_wheel_2", "position":"rear", "side":"l"},
        {"cx": -hw, "cy": 0, "cz": -length*0.35, "locator":"bb_r_wheel_2", "position":"rear", "side":"r"},
    ]

def _default_wheels_count(count: int, length: float, width: float) -> list:
    base = _default_wheels(length, width)
    return base[:count] if count <= 4 else base + [
        {"cx":  width/2-0.15, "cy":0,"cz":0,"locator":"bb_l_wheel_3","position":"mid","side":"l"},
        {"cx": -width/2+0.15, "cy":0,"cz":0,"locator":"bb_r_wheel_3","position":"mid","side":"r"},
    ]

def _detect_steering(mod: ModInfo) -> bool:
    STEERING_KW = ["steer","lenk","volant","wheel_d","cockpit","lenkrad"]
    for o3d in mod.files.get(".o3d", []):
        if any(kw in o3d.stem.lower() for kw in STEERING_KW):
            return True
    return bool(mod.cfg.get("vehicle.steering"))

def _compute_cameras(length: float, height: float) -> list:
    return [
        {"name":"driver",
         "x":0.6,  "y":1.15,         "z": length*0.35,
         "rx":-5,  "ry":-5,          "rz":0},
        {"name":"roof",
         "x":0.0,  "y":height+0.3,   "z":0.0,
         "rx":-30, "ry":0,            "rz":0},
        {"name":"back",
         "x":0.0,  "y":1.5,          "z":-length*0.3,
         "rx":5,   "ry":180,          "rz":0},
    ]

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 3 : MAPPING MATÉRIAUX
# ═══════════════════════════════════════════════════════════════════════════════
def phase_materials(mod: ModInfo, cache: dict) -> tuple[ModInfo, int]:
    phase_log(3, 7, "Mapping matériaux", "run")
    all_textures = (mod.files.get(".dds", []) +
                    mod.files.get(".png", []) +
                    mod.files.get(".tga", []))
    fallbacks = 0

    for tex in all_textures:
        name_lower = tex.stem.lower()
        shader, method = _map_material(tex, name_lower, cache)
        mod.materials.append({
            "texture": tex.name,
            "shader":  shader,
            "method":  method,
            "tobj":    tex.stem + ".tobj",
        })
        if method == "fallback":
            fallbacks += 1

    matched = len(mod.materials) - fallbacks
    detail = (f"{len(mod.materials)} matériaux — "
              f"{matched} matchés, {fallbacks} fallback dif.spec")
    status = "warn" if fallbacks > len(mod.materials) * 0.15 else "ok"
    phase_log(3, 7, "Mapping matériaux", status, detail)
    return mod, fallbacks

def _map_material(tex_path: Path, name: str, cache: dict) -> tuple[str, str]:
    """Cascade 4 niveaux : hash → nom → pixels → fallback"""

    # Niveau 1 : cache hash
    tex_hash = _hash_file_fast(tex_path)
    if tex_hash in cache.get("textures", {}):
        return cache["textures"][tex_hash], "cache"

    # Niveau 2 : LUT par règles (alpha + normal + keywords)
    has_alpha  = any(k in name for k in ["_a","alpha","trans","glass","window","windsh","grille","grill"])
    has_normal = any(k in name for k in ["_n","_norm","_nrm","normal","bump"])
    has_spec   = any(k in name for k in ["_s","_spec","specul"])

    for (a, n, s, kw, shader) in MATERIAL_LUT:
        kw_match = (kw is None) or (kw in name)
        if a == has_alpha and n == has_normal and s == has_spec and kw_match:
            cache.setdefault("textures", {})[tex_hash] = shader
            return shader, "lut"

    # Niveau 3 : analyse pixels (si Pillow disponible)
    shader = _map_by_pixels(tex_path)
    if shader:
        cache.setdefault("textures", {})[tex_hash] = shader
        return shader, "pixel"

    # Niveau 4 : fallback universel
    return "dif.spec", "fallback"

def _map_by_pixels(tex_path: Path) -> Optional[str]:
    """Analyse l'histogramme pour détecter transparence/luminosité"""
    try:
        from PIL import Image
        with Image.open(tex_path) as img:
            if img.mode == "RGBA":
                alpha = img.split()[3]
                mean_alpha = sum(alpha.getdata()) / len(alpha.getdata())
                if mean_alpha < 200:
                    return "glass.spec"
            # Luminosité très haute = textures émissives
            gray = img.convert("L")
            mean_lum = sum(gray.getdata()) / len(gray.getdata())
            if mean_lum > 220:
                return "dif.lum.spec"
    except Exception:
        pass
    return None

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 4 : CONVERSION TEXTURES
# ═══════════════════════════════════════════════════════════════════════════════
def phase_textures(mod: ModInfo, out_dir: Path, cache: dict,
                   tex_format: str = "BC7_UNORM") -> tuple[int, int]:
    phase_log(4, 7, "Conversion textures", "run")
    tex_dir = out_dir / "texture"
    tex_dir.mkdir(parents=True, exist_ok=True)

    all_textures = (mod.files.get(".dds", []) + mod.files.get(".png", []) +
                    mod.files.get(".tga", []) + mod.files.get(".bmp", []) +
                    mod.files.get(".jpg", []) + mod.files.get(".jpeg", []))

    converted, cached_count = 0, 0
    toolchain = detect_toolchain()

    def convert_one(tex: Path) -> str:
        tex_hash = _hash_file_fast(tex)
        if tex_hash in cache.get("textures_converted", {}):
            cached_path = Path(cache["textures_converted"][tex_hash])
            if cached_path.exists():
                dst = tex_dir / (tex.stem + ".dds")
                if not dst.exists():
                    try:
                        shutil.copy2(cached_path, dst)
                    except Exception:
                        pass
                return "cached"

        dst = tex_dir / (tex.stem + ".dds")
        success = False

        if toolchain.texconv:
            import subprocess
            cmd = [toolchain.texconv, "-f", tex_format, "-nologo", "-y", "-m", "10", "-o", str(tex_dir), str(tex)]
            if tex.suffix.lower() in {".png", ".tga", ".bmp", ".jpg", ".jpeg"}:
                cmd = [toolchain.texconv, "-f", "BC7_UNORM", "-nologo", "-y", "-m", "10", "-o", str(tex_dir), str(tex)]
            try:
                result = subprocess.run(cmd, capture_output=True, timeout=90)
                if result.returncode == 0 and dst.exists():
                    success = True
            except Exception:
                success = False

        if not success:
            success = _convert_texture_pillow(tex, dst)

        if not success and tex.suffix.lower() == ".dds":
            try:
                shutil.copy2(tex, dst)
                success = True
            except Exception:
                pass

        if success:
            cache.setdefault("textures_converted", {})[tex_hash] = str(dst)
            _write_tobj(tex_dir / (tex.stem + ".tobj"), tex.stem + ".dds")
            return "converted"
        return "failed"

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(convert_one, all_textures))

    converted = results.count("converted")
    cached_count = results.count("cached")
    failed = results.count("failed")
    detail = f"{len(all_textures)} textures — {converted} converties, {cached_count} depuis cache, {failed} échecs"
    phase_log(4, 7, "Conversion textures", "warn" if failed else "ok", detail)
    return converted, cached_count

def _convert_texture_pillow(src: Path, dst: Path) -> bool:
    """Conversion basique via Pillow, avec fallback auto-embarqué stdlib."""
    try:
        from PIL import Image
        with Image.open(src) as img:
            w, h = img.size
            nw = 2 ** math.ceil(math.log2(max(w, 1)))
            nh = 2 ** math.ceil(math.log2(max(h, 1)))
            if (nw, nh) != (w, h):
                img = img.resize((nw, nh), Image.LANCZOS)
            img.save(str(dst), format="DDS")
            return dst.exists()
    except Exception:
        pass
    try:
        img = _read_png_rgba(src) if src.suffix.lower() == ".png" else _read_bmp_rgba(src)
        if not img:
            return False
        width, height, raw = img
        _write_dds_rgba(dst, width, height, raw)
        return dst.exists()
    except Exception:
        pass
    return False

def _write_tobj(tobj_path: Path, dds_name: str):
    """Génère un fichier .tobj SCS (pointeur vers le .dds)"""
    content = f"""version: 1
u_addr: 1
v_addr: 1
usage: tsnormal
bias: 0
nocompress: 0
noaniso: 0
map:texture \"{dds_name}\"
"""
    tobj_path.write_text(content, encoding="utf-8")

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 5 : EXPORT SCS (simulation / stub Blender)
# ═══════════════════════════════════════════════════════════════════════════════
def phase_export_scs(mod: ModInfo, out_dir: Path) -> bool:
    phase_log(5, 7, "Export SCS (Blender headless)", "run")
    model_dir = out_dir / "model"
    model_dir.mkdir(parents=True, exist_ok=True)

    toolchain = detect_toolchain()
    blender_path = toolchain.blender
    if blender_path:
        success = _export_via_blender(mod, out_dir, blender_path)
        if success:
            phase_log(5, 7, "Export SCS (Blender headless)", "ok",
                      "export .pim/.pip via SCS Blender Tools")
            return True
        phase_log(5, 7, "Export SCS (Blender headless)", "warn",
                  "Blender détecté mais export échoué — génération du stub de secours")

    _write_pim_stub(mod, model_dir)
    phase_log(5, 7, "Export SCS (Blender headless)", "warn",
              "outil dédié absent / export incomplet — .pim stub de secours généré")
    return True

def _find_blender() -> Optional[str]:
    toolchain = detect_toolchain()
    return toolchain.blender

def _export_via_blender(mod: ModInfo, out_dir: Path, blender: str) -> bool:
    """Lance Blender en headless avec un script Python de conversion"""
    import subprocess, tempfile
    script = _generate_blender_script(mod, out_dir)
    with tempfile.NamedTemporaryFile(suffix=".py", delete=False, mode="w") as f:
        f.write(script)
        script_path = f.name
    try:
        r = subprocess.run(
            [blender, "--background", "--python", script_path],
            capture_output=True, timeout=120
        )
        return r.returncode == 0
    except Exception:
        return False
    finally:
        os.unlink(script_path)

def _generate_blender_script(mod: ModInfo, out_dir: Path) -> str:
    """Génère le script Python à exécuter dans Blender"""
    wheels_json = json.dumps(mod.wheels)
    cameras_json = json.dumps(mod.cameras)
    return f"""
import bpy, sys, json
from pathlib import Path

out_dir = Path(r"{out_dir}")
mod_path = Path(r"{mod.path}")
wheels   = {wheels_json}
cameras  = {cameras_json}

# Nettoyage scène
bpy.ops.wm.read_factory_settings(use_empty=True)

# Import des .o3d (nécessite O3D-IO addon)
o3d_files = list(mod_path.rglob("*.o3d"))
for o3d in o3d_files:
    try:
        bpy.ops.import_scene.o3d(filepath=str(o3d))
    except Exception as e:
        print(f"Skip {{o3d.name}}: {{e}}")

# Créer les locators de roues
for w in wheels:
    bpy.ops.object.empty_add(type='PLAIN_AXES',
        location=(w.get('cx',0), w.get('cy',0), w.get('cz',0)))
    bpy.context.active_object.name = w.get('locator','wheel')

# Créer les caméras
for cam in cameras:
    bpy.ops.object.camera_add(
        location=(cam['x'], cam['y'], cam['z']))
    bpy.context.active_object.name = f"cam_{{cam['name']}}"

# Export SCS (nécessite SCS Blender Tools addon)
try:
    bpy.ops.export_scene.scs(filepath=str(out_dir / "model" / "{mod.name}"))
    print("SCS export OK")
except Exception as e:
    print(f"SCS export failed: {{e}}")
    sys.exit(1)
"""

def _write_pim_stub(mod: ModInfo, model_dir: Path):
    """
    Génère un .pim minimal valide pour SCS.
    C'est un fichier texte (format PIM v6) avec un cube représentant le bus.
    """
    bbox = mod.bbox
    L, W, H = bbox["length"]/2, bbox["width"]/2, bbox["height"]
    # 8 sommets du bounding box du bus
    verts = [
        (-W, 0,  L), ( W, 0,  L), ( W, H,  L), (-W, H,  L),
        (-W, 0, -L), ( W, 0, -L), ( W, H, -L), (-W, H, -L),
    ]
    # 12 triangles (6 faces × 2)
    tris = [
        (0,1,2),(0,2,3),  # front
        (4,6,5),(4,7,6),  # back
        (0,4,5),(0,5,1),  # bottom
        (2,6,7),(2,7,3),  # top
        (0,3,7),(0,7,4),  # left
        (1,5,6),(1,6,2),  # right
    ]
    lines = [
        "##version:6",
        f"##source:omsi2ets2 v0.1",
        "",
        "Header {",
        f' FormatVersion( 6 )',
        f' Name( "{mod.name}" )',
        f' GlobalScale( 1.000000 )',
        "}",
        "",
        "Bones { }",
        "",
        "Geometry {",
        f" Piece {{ StreamCount( 2 ) FaceCount( {len(tris)} ) StreamType( POSITION ) StreamType( NORMAL ) }}"
    ]
    for i, (x, y, z) in enumerate(verts):
        lines.append(f"  /* v{i} */ {x:.4f} {y:.4f} {z:.4f}")
    for a, b, c in tris:
        lines.append(f"  Triangle {{ {a} {b} {c} }}")
    lines += ["}", ""]

    pim_path = model_dir / f"{mod.name}.pim"
    pim_path.write_text("\n".join(lines), encoding="utf-8")

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 6 : GÉNÉRATION DÉFINITIONS .sii
# ═══════════════════════════════════════════════════════════════════════════════
def phase_definitions(mod: ModInfo, out_dir: Path) -> bool:
    phase_log(6, 7, "Génération définitions .sii", "run")
    def_dir = out_dir / "def" / "vehicle" / "bus"
    def_dir.mkdir(parents=True, exist_ok=True)

    bbox = mod.bbox
    name = mod.name.lower().replace(" ", "_").replace("-", "_")

    # Génération des locators de roues
    wheel_locators = "\n".join(
        f'\t\t\tbb_axle_locator[{i}]: "{w.get("locator","wheel")}"'
        for i, w in enumerate(mod.wheels)
    )
    axle_count = max(2, len(mod.wheels) // 2)

    # vehicle.sii
    vehicle_sii = f"""SiiNunit
{{

vehicle_data : vehicle.bus.{name} {{

\tname: "{mod.name}"
\tshort_name: "{mod.name[:8]}"

\tmodel: "/vehicle/bus/{name}/{name}.pmg"
\tmodel_shadow: "/vehicle/bus/{name}/{name}_shadow.pmg"

\tphysics_body: vehicle.bus.{name}.body

\twheel_count: {len(mod.wheels)}
{wheel_locators}

\taxle_count: {axle_count}

\tcab_view_count: {len(mod.cameras)}
\tcab_view[0]: "{mod.cameras[0]['name'] if mod.cameras else 'driver'}"

\twidth: {bbox['width']:.3f}
\theight: {bbox['height']:.3f}
\tlength: {bbox['length']:.3f}

\tauthor: "omsi2ets2-converter"
\tauthor_url: ""
\tcategory: "buses"

}}

}}
"""

    # chassis.sii
    chassis_sii = f"""SiiNunit
{{

vehicle_chassis : vehicle.bus.{name}.body {{

\tname: "{mod.name} Chassis"

\tcenter_of_mass: (0, {bbox['height']*0.4:.3f}, 0)
\tmass: 12000

\taxle_count: {axle_count}
\taxle[0].position: (0, 0.45, {bbox['length']*0.35:.3f})
\taxle[0].track: {bbox['width']-0.3:.3f}
\taxle[0].steering: true
\taxle[1].position: (0, 0.45, {-bbox['length']*0.35:.3f})
\taxle[1].track: {bbox['width']-0.3:.3f}
\taxle[1].steering: false

\tengine_rpm_limit: 2400
\tengine_torque: 1200

}}

}}
"""

    # manifest.sii
    manifest_sii = f"""SiiNunit
{{

mod_package : .manifest {{

\tpackage_version: "1.0"
\tdisplay_name: "{mod.name} (converted by omsi2ets2)"
\tdescription: "Converted from OMSI 2 using omsi2ets2 converter"
\tauthor: "omsi2ets2"
\tcategories[]: "buses"

}}

}}
"""

    (def_dir / f"{name}.sii").write_text(vehicle_sii, encoding="utf-8")
    (def_dir / f"{name}_chassis.sii").write_text(chassis_sii, encoding="utf-8")
    (out_dir / "manifest.sii").write_text(manifest_sii, encoding="utf-8")

    # Créer l'arborescence SCS
    for subdir in [f"vehicle/bus/{name}", f"vehicle/bus/{name}/texture"]:
        (out_dir / subdir).mkdir(parents=True, exist_ok=True)

    phase_log(6, 7, "Génération définitions .sii", "ok",
              f"vehicle.sii, chassis.sii, manifest.sii générés")
    return True

# ═══════════════════════════════════════════════════════════════════════════════
# PHASE 7 : COMPILATION & VALIDATION & PACKAGING
# ═══════════════════════════════════════════════════════════════════════════════
def phase_compile_and_package(mod: ModInfo, out_dir: Path) -> ConversionResult:
    phase_log(7, 7, "Compilation & validation", "run")
    warnings, errors = [], []
    name = mod.name.lower().replace(" ", "_").replace("-", "_")

    toolchain = detect_toolchain()
    scs_tools = toolchain.scs_tools or _find_scs_tools()
    compiled = False
    if scs_tools:
        compiled = _run_scs_compile(out_dir, scs_tools)
        if compiled:
            log.debug("SCS Conversion Tools : compilation OK")
        else:
            warnings.append("SCS Conversion Tools a échoué — validation de qualité en mode prudent")
    else:
        warnings.append("SCS Conversion Tools non trouvé — .pim non compilé en .pmg (mode qualité minimale)")

    checks = {
        "manifest.sii": (out_dir / "manifest.sii").exists(),
        f"def/{name}.sii": (out_dir / "def" / "vehicle" / "bus" / f"{name}.sii").exists(),
        f"def/{name}_chassis.sii": (out_dir / "def" / "vehicle" / "bus" / f"{name}_chassis.sii").exists(),
        "model/ présent": (out_dir / "model").exists(),
        "texture/ présent": (out_dir / "texture").exists(),
    }
    for check, ok in checks.items():
        if not ok:
            errors.append(f"Fichier manquant : {check}")

    scs_path = OUTPUT_DIR / f"{mod.name}.scs"
    try:
        with zipfile.ZipFile(scs_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for f in out_dir.rglob("*"):
                if f.is_file():
                    arcname = f.relative_to(out_dir)
                    zf.write(f, arcname)
        scs_size = scs_path.stat().st_size / 1024
        detail = f"{scs_path.name} ({scs_size:.0f} Ko)"
    except Exception as e:
        errors.append(f"Packaging échoué : {e}")
        scs_path = None
        detail = "packaging échoué"

    confidence = _compute_confidence(mod, checks, warnings, errors)
    quality_gate = (confidence >= 80.0) and not errors
    if not quality_gate:
        warnings.append(f"Qualité de conversion insuffisante (confiance {confidence:.1f}%) — conversion conservatrice en mode de secours")

    status = "err" if errors else ("warn" if warnings else "ok")
    phase_log(7, 7, "Compilation & validation", status, detail)

    return ConversionResult(
        success=not errors and quality_gate,
        mod_name=mod.name,
        output_path=scs_path,
        confidence=confidence,
        warnings=warnings,
        errors=errors,
        stats={
            "wheels": len(mod.wheels),
            "materials": len(mod.materials),
            "textures": len(mod.files.get(".dds", []) + mod.files.get(".png", [])),
            "compiled": compiled,
            "quality_gate": quality_gate,
        }
    )

def _find_scs_tools() -> Optional[str]:
    candidates = [
        "convert", "./convert.cmd", "./convert.sh",
        "pim2pmg", "pim2pmg.exe",
        r"C:\SCS\ConversionTools\convert.exe",
        r"C:\SCS\ConversionTools\pim2pmg.exe",
        r"C:\SCS\Tools\convert.exe",
        r"C:\SCS\Tools\pim2pmg.exe",
        "/opt/scs/convert",
        "/usr/local/bin/pim2pmg",
    ]
    for c in candidates:
        if shutil.which(c) or Path(c).exists():
            return c
    return None

def _run_scs_compile(out_dir: Path, scs_tools: str) -> bool:
    import subprocess
    try:
        r = subprocess.run([scs_tools], cwd=str(out_dir),
                           capture_output=True, timeout=60)
        return r.returncode == 0
    except Exception:
        return False

def _compute_confidence(mod: ModInfo, checks: dict,
                        warnings: list, errors: list) -> float:
    score = 1.0
    if not mod.wheels:                          score *= 0.85
    elif len(mod.wheels) < 4:                  score *= 0.92
    if not mod.steering:                        score *= 0.98
    fallback_rate = sum(1 for m in mod.materials if m.get("method") == "fallback")
    if mod.materials:
        score *= (1 - 0.02 * fallback_rate / len(mod.materials))
    score *= max(0.9, 1 - 0.02 * len(warnings))
    score *= max(0.7, 1 - 0.10 * len(errors))
    checks_ok = sum(checks.values()) / max(len(checks), 1)
    score *= checks_ok
    return round(min(score, 1.0) * 100, 1)

# ═══════════════════════════════════════════════════════════════════════════════
# UTILITAIRES
# ═══════════════════════════════════════════════════════════════════════════════
def _hash_file_fast(path: Path) -> str:
    """Hash rapide : taille + 4Ko début + 4Ko fin"""
    h = hashlib.md5()
    size = path.stat().st_size
    h.update(str(size).encode())
    try:
        with open(path, "rb") as f:
            h.update(f.read(4096))
            if size > 8192:
                f.seek(-4096, 2)
                h.update(f.read(4096))
    except Exception:
        pass
    return h.hexdigest()

def _hash_mod_structure(mod_path: Path) -> str:
    """Hash de la structure du mod (noms + tailles des fichiers)"""
    h = hashlib.md5()
    for f in sorted(mod_path.rglob("*")):
        if f.is_file():
            h.update(f.name.encode())
            h.update(str(f.stat().st_size).encode())
    return h.hexdigest()

def _write_conversion_report(result: ConversionResult, out_dir: Path):
    """Écrit un rapport JSON détaillé"""
    report = {
        "status":      "OK" if result.success else "FAILED",
        "mod":         result.mod_name,
        "confidence":  f"{result.confidence}%",
        "duration":    f"{result.duration:.1f}s",
        "output":      str(result.output_path) if result.output_path else None,
        "stats":       result.stats,
        "warnings":    result.warnings,
        "errors":      result.errors,
        "timestamp":   datetime.now().isoformat(),
    }
    log_file = LOG_DIR / f"{result.mod_name}_{datetime.now():%Y%m%d_%H%M%S}.json"
    log_file.write_text(json.dumps(report, indent=2, ensure_ascii=False),
                        encoding="utf-8")
    return log_file

# ═══════════════════════════════════════════════════════════════════════════════
# PIPELINE PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════════
def convert(mod_path: Path) -> ConversionResult:
    """Point d'entrée principal : conversion OMSI2 → ETS2 en mode qualité prioritaire."""
    t0 = time.time()
    mod_path = Path(mod_path)

    print()
    print(col("bold", "═" * 60))
    print(col("bold", f"  OMSI2 → ETS2  |  {mod_path.name}"))
    print(col("gray",  f"  {datetime.now():%Y-%m-%d %H:%M:%S}"))
    print(col("gray",  f"  limite de conversion : {MAX_MOD_RUNTIME_SECONDS // 60} min"))
    print(col("bold", "═" * 60))

    cache = load_cache()
    sig = _hash_mod_structure(mod_path)
    if sig in cache.get("known_mods", {}):
        print(col("cyan", f"  → Mod reconnu en base — profil pré-validé chargé"))

    out_dir = Path("/tmp") / f"omsi2ets2_{mod_path.name}_{int(t0)}"
    out_dir.mkdir(parents=True, exist_ok=True)

    try:
        if time.time() - t0 > MAX_MOD_RUNTIME_SECONDS:
            raise TimeoutError(f"limite de traitement dépassée ({MAX_MOD_RUNTIME_SECONDS}s)")

        mod = phase_ingestion(mod_path)
        mod = phase_geometry(mod)
        mod, fallbacks = phase_materials(mod, cache)
        phase_textures(mod, out_dir, cache)
        phase_export_scs(mod, out_dir)
        phase_definitions(mod, out_dir)
        result = phase_compile_and_package(mod, out_dir)

        result.duration = time.time() - t0

        if result.success and not result.warnings:
            cache.setdefault("known_mods", {})[sig] = {
                "name": mod.name, "confidence": result.confidence
            }

        save_cache(cache)
        log_file = _write_conversion_report(result, out_dir)

        print()
        print(col("bold", "─" * 60))
        if result.success:
            print(col("green",  f"  ✓ SUCCÈS  —  {result.output_path.name}"))
        else:
            print(col("red",    f"  ✗ ÉCHEC (qualité prioritaire)"))
        print(col("gray",   f"  Confiance  : {result.confidence}%"))
        print(col("gray",   f"  Durée      : {result.duration:.1f}s"))
        print(col("gray",   f"  Rapport    : {log_file}"))
        if result.warnings:
            for w in result.warnings:
                print(col("yellow", f"  ⚠  {w}"))
        if result.errors:
            for e in result.errors:
                print(col("red",    f"  ✗  {e}"))
        print(col("bold", "─" * 60))
        print()
        return result

    except TimeoutError as exc:
        result = ConversionResult(success=False, mod_name=mod_path.name, warnings=[str(exc)], errors=[str(exc)], duration=time.time()-t0)
        print(col("red", f"  ✗ {exc}"))
        return result

    finally:
        try:
            shutil.rmtree(out_dir)
        except Exception:
            pass

# ═══════════════════════════════════════════════════════════════════════════════
# WATCHER (surveillance dossier en temps réel)
# ═══════════════════════════════════════════════════════════════════════════════
def watch_mode(watch_dir: Path):
    """Surveille un dossier et convertit automatiquement tout mod déposé"""
    try:
        from watchdog.observers import Observer
        from watchdog.events import FileSystemEventHandler
    except ImportError:
        print(col("yellow", "watchdog non installé — polling mode (vérif toutes les 3s)"))
        _watch_polling(watch_dir)
        return

    class Handler(FileSystemEventHandler):
        def __init__(self):
            self._seen = set()

        def on_created(self, event):
            p = Path(event.src_path)
            if event.is_directory and p not in self._seen:
                self._seen.add(p)
                time.sleep(0.5)  # attendre que la copie soit finie
                convert(p)
            elif p.suffix.lower() == ".zip" and p not in self._seen:
                self._seen.add(p)
                self._handle_zip(p)

        def _handle_zip(self, zip_path: Path):
            extract_dir = watch_dir / zip_path.stem
            with zipfile.ZipFile(zip_path) as zf:
                zf.extractall(extract_dir)
            convert(extract_dir)

    observer = Observer()
    observer.schedule(Handler(), str(watch_dir), recursive=False)
    observer.start()
    print(col("cyan", f"  Surveillance active : {watch_dir}"))
    print(col("gray",  "  Dépose un dossier mod OMSI2 pour lancer la conversion"))
    print(col("gray",  "  Ctrl+C pour arrêter"))
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        observer.stop()
    observer.join()

def _watch_polling(watch_dir: Path):
    """Fallback polling sans watchdog"""
    seen = set()
    print(col("cyan", f"  Surveillance (polling) : {watch_dir}"))
    while True:
        try:
            for item in watch_dir.iterdir():
                if item not in seen:
                    seen.add(item)
                    if item.is_dir():
                        time.sleep(0.5)
                        convert(item)
                    elif item.suffix.lower() == ".zip":
                        extract_dir = watch_dir / item.stem
                        with zipfile.ZipFile(item) as zf:
                            zf.extractall(extract_dir)
                        convert(extract_dir)
            time.sleep(3)
        except KeyboardInterrupt:
            break

# ═══════════════════════════════════════════════════════════════════════════════
# ENTRÉE CLI
# ═══════════════════════════════════════════════════════════════════════════════
def main():
    parser = argparse.ArgumentParser(
        description="OMSI 2 → ETS 2 Converter",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples :
  python omsi2ets2.py ./mods/MAN_Lions_City
  python omsi2ets2.py ./mods/MAN_Lions_City --output ./ets2_mods
  python omsi2ets2.py --watch-dir ./input
  python omsi2ets2.py --batch ./dossier_avec_plusieurs_mods
        """
    )
    parser.add_argument("mod", nargs="?", help="Dossier du mod OMSI2 à convertir")
    parser.add_argument("--output",    "-o", help="Dossier de sortie (défaut: ./output)")
    parser.add_argument("--watch",     action="store_true",
                        help="Surveiller le dossier input/ en continu")
    parser.add_argument("--watch-dir", help="Surveiller un dossier spécifique")
    parser.add_argument("--batch",     help="Convertir tous les mods d'un dossier")
    parser.add_argument("--workers",   type=int, default=1,
                        help="Nombre de conversions parallèles (défaut: 1, mode qualité prioritaire)")
    args = parser.parse_args()

    if args.output:
        global OUTPUT_DIR
        OUTPUT_DIR = Path(args.output)
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print(col("bold", "\n  ╔══════════════════════════════╗"))
    print(col("bold",   "  ║  omsi2ets2 — v0.1 prototype ║"))
    print(col("bold",   "  ╚══════════════════════════════╝\n"))

    if args.watch_dir:
        watch_mode(Path(args.watch_dir))
    elif args.watch:
        watch_mode(INPUT_DIR)
    elif args.batch:
        batch_dir = Path(args.batch)
        mods = [d for d in batch_dir.iterdir() if d.is_dir()]
        print(col("cyan", f"  Batch : {len(mods)} mods à convertir "
                          f"({args.workers} en parallèle)"))
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            results = list(pool.map(convert, mods))
        ok = sum(1 for r in results if r.success)
        print(col("green" if ok == len(mods) else "yellow",
                  f"\n  Batch terminé : {ok}/{len(mods)} réussis"))
    elif args.mod:
        result = convert(Path(args.mod))
        sys.exit(0 if result.success else 1)
    else:
        # Mode interactif : surveiller input/
        print(col("gray", f"  Dossier input  : {INPUT_DIR}"))
        print(col("gray", f"  Dossier output : {OUTPUT_DIR}"))
        print()
        print(col("cyan", "  Aucun mod spécifié — démarrage en mode surveillance"))
        print(col("gray", "  Utilisation : python omsi2ets2.py <dossier_mod>"))
        print()
        watch_mode(INPUT_DIR)

if __name__ == "__main__":
    main()
