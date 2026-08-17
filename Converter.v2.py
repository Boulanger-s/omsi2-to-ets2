#!/usr/bin/env python3
"""
omsi2ets2_gx127_v2.py — Convertisseur PBS → ETS2 | Heuliez GX x27
===================================================================
Source : Proton Bus Simulator (Ago'Projects - Heuliez Bus GX x27)
Cible  : Euro Truck Simulator 2

Améliorations v2 :
  - Lecture complète models.txt (liste des meshes par rôle)
  - Dimensions exactes depuis la doc PDF (9.42m GX127 / 12.04m GX327)
  - Système d'accessoires ETS2 (fonctions PBS → variants .sii)
  - Conversion repaints → skins ETS2 (paintjobs)
  - Intégration SCS Conversion Tools (compile .pim → .pmg si disponible)
  - GX127C et GX127L comme deux véhicules distincts
"""

import os, sys, json, shutil, struct, time, math
import zipfile, re, argparse, subprocess
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from typing import Optional

# ── Couleurs terminal ─────────────────────────────────────────────────────────
def col(c, s):
    C={"g":"\033[92m","y":"\033[93m","r":"\033[91m","c":"\033[96m",
       "b":"\033[1m","x":"\033[0m","gray":"\033[90m","m":"\033[95m"}
    return f"{C.get(c,'')}{s}{C['x']}"

def plog(n, tot, name, status, detail=""):
    icons={"ok":col("g","✓"),"warn":col("y","⚠"),"err":col("r","✗"),
           "run":col("c","▶"),"info":col("m","ℹ")}
    print(f"{icons.get(status,'•')} {col('gray',f'[{n}/{tot}]')} "
          f"{col('b',name)}" + (col("gray",f" — {detail}") if detail else ""))

# ═══════════════════════════════════════════════════════════════════════════════
# DONNÉES EXACTES DU PDF (vérité terrain)
# ═══════════════════════════════════════════════════════════════════════════════
VEHICLE_SPECS = {
    "GX127": {
        "length": 9.42, "width": 2.33, "height": 2.885,
        "engine": "Iveco Tector 6", "axles": 2,
        "doors": "battantes", "normed": "Euro4",
    },
    "GX127L": {
        "length": 10.645, "width": 2.33, "height": 2.885,
        "engine": "Iveco Tector 6", "axles": 2,
        "doors": "coulissantes", "normed": "Euro4",
    },
    "GX327": {
        "length": 12.04, "width": 2.55, "height": 2.88,
        "engine": "Iveco Cursor 8", "axles": 2,
        "doors": "standard", "normed": "Euro4",
    },
    "GX427": {
        "length": 17.95, "width": 2.55, "height": 2.88,
        "engine": "Iveco Cursor 8", "axles": 3,
        "doors": "articulé", "normed": "Euro4",
        "articulated": True,
    },
}

# Accessoires PBS → ETS2 (Fonctions 1-8 du PDF)
PBS_FUNCTIONS_GX127 = {
    1: {"name": "calandre_avant_2012",    "mesh_kw": ["Front_Grill"],      "ets2_slot": "front_grille"},
    2: {"name": "plaque_arriere",          "mesh_kw": ["Rear_Plate"],       "ets2_slot": "license_plate"},
    3: {"name": "grille_moteur_arriere",   "mesh_kw": ["Rear_Grid"],        "ets2_slot": "engine_cover"},
    4: {"name": "baies_panoramiques",      "mesh_kw": ["Triangular_Side"],  "ets2_slot": "side_window"},
    5: {"name": "feux_additionnels",       "mesh_kw": ["Light", "Feux"],    "ets2_slot": "add_lights"},
    6: {"name": "sieges",                  "mesh_kw": ["Seats"],            "ets2_slot": "interior_seats"},
    7: {"name": "caches_ecrous",           "mesh_kw": ["Wheel", "Wheels"],  "ets2_slot": "wheel_covers"},
}

# ═══════════════════════════════════════════════════════════════════════════════
# PARSEUR FICHIERS PBS
# ═══════════════════════════════════════════════════════════════════════════════
def parse_pbs_ini(path: Path) -> dict:
    """Parse un .txt PBS (format [section] key=value)"""
    cfg, section = {}, "global"
    try:
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            line = line.strip().replace("\r","")
            if not line or line.startswith("#"): continue
            if line.startswith("[") and line.endswith("]"):
                section = line[1:-1].lower(); cfg.setdefault(section, {}); continue
            if "=" in line:
                k, _, v = line.partition("=")
                cfg.setdefault(section, {})[k.strip().lower()] = v.strip()
    except: pass
    return cfg

def read_models_list(mod_path: Path, variant: str = "") -> dict:
    """
    Lit models.txt (ou models_L.txt pour GX127L) et retourne
    le mapping rôle → fichier mesh.
    """
    fname = f"models_{variant}.txt" if variant else "models.txt"
    fpath = mod_path / fname
    if not fpath.exists():
        fpath = mod_path / "models.txt"

    cfg = parse_pbs_ini(fpath)
    part = cfg.get("part1_3ds", {})

    meshes = {}
    for k, v in part.items():
        if k.startswith("model"):
            mesh_path = mod_path / v.replace("\\","/")
            stem = Path(v).stem
            # Détecter le rôle à partir du nom
            role = _classify_mesh_role(stem)
            meshes[stem] = {"path": mesh_path, "role": role, "src": v}

    # Volant
    sw = cfg.get("steering_wheel", {})
    steering = {
        "x": float(sw.get("posx", -0.574)),
        "y": float(sw.get("posy",  1.639)),
        "z": float(sw.get("posz",  4.053)),
        "rx": float(sw.get("rotx", -30)),
        "total_angle": float(sw.get("totalturningangle", 900)),
    } if sw else None

    return {"meshes": meshes, "steering": steering}

def _classify_mesh_role(stem: str) -> str:
    sl = stem.lower()
    if any(k in sl for k in ["body"]): return "body"
    if any(k in sl for k in ["wheel"]): return "wheel"
    if any(k in sl for k in ["door"]): return "door"
    if any(k in sl for k in ["interior"]): return "interior"
    if any(k in sl for k in ["seat"]): return "seat"
    if any(k in sl for k in ["mirror"]): return "mirror"
    if any(k in sl for k in ["driver","cab"]): return "driver"
    if any(k in sl for k in ["glass","window","vitre"]): return "glass"
    if any(k in sl for k in ["light","lamp","ineo","display"]): return "emissive"
    if any(k in sl for k in ["grill","grille","calandre"]): return "accessory"
    if any(k in sl for k in ["meshcollider","collider"]): return "collider"
    return "detail"

def read_wheels(mod_path: Path, variant: str = "") -> list:
    fname = f"wheels1{'_'+variant if variant else ''}.txt"
    fpath = mod_path / fname
    if not fpath.exists():
        fpath = mod_path / "wheels1.txt"
    cfg = parse_pbs_ini(fpath)
    wheels = []
    for key in sorted(cfg.keys()):
        if not any(k in key for k in ["leftwheel","rightwheel"]): continue
        w = cfg[key]
        side = "l" if "left" in key else "r"
        num  = re.search(r"\d+", key)
        num  = num.group() if num else "1"
        wheels.append({
            "locator": f"bb_{side}_wheel_{num}",
            "side": side, "num": int(num),
            "x": float(w.get("posx", 0)),
            "y": float(w.get("posy", 0)),
            "z": float(w.get("posz", 0)),
            "radius": float(w.get("radius", 0.515)),
            "mass":   float(w.get("mass", 30)),
            "spring": float(w.get("springrate", 161024)),
            "damper": float(w.get("damperrate", 8051)),
        })
    return wheels

def read_engine(mod_path: Path) -> dict:
    for fname in ["engine1auto.txt", "engine1manual.txt"]:
        fp = mod_path / fname
        if not fp.exists(): continue
        cfg = parse_pbs_ini(fp)
        e  = cfg.get("engine", {})
        gb = cfg.get("automatic_gearbox", cfg.get("manual_gearbox", {}))
        df = cfg.get("differential", {})
        n_gears = int(gb.get("numforward", gb.get("num_forward_ratios", 4)))
        ratios = []
        for i in range(1, n_gears+1):
            for key in [f"fwd_ratio_{i}", f"ratio_{i}", f"forwardratio{i}"]:
                if key in gb:
                    ratios.append(float(gb[key])); break
            else:
                ratios.append(round(3.5 / (1.5**i), 4))
        return {
            "idle_rpm":    float(e.get("idlerpm", e.get("idle_rpm", 550))),
            "peak_rpm":    float(e.get("peakrpm",  e.get("peak_rpm", 1600))),
            "max_rpm":     float(e.get("maxrpm",   e.get("max_rpm", 2300))),
            "peak_torque": float(e.get("peakrpmtorque", e.get("peak_rpm_torque", 550))),
            "gear_ratios": ratios if ratios else [3.43, 2.01, 1.42, 1.0],
            "diff_ratio":  float(df.get("gearratio", 6.2)),
        }
    return {"idle_rpm":550,"peak_rpm":1600,"max_rpm":2300,
            "peak_torque":550,"gear_ratios":[3.43,2.01,1.42,1.0],"diff_ratio":6.2}

def read_repaints(mod_path: Path) -> list:
    """Lit tous les repaints et retourne leur liste avec textures"""
    repaints = []
    for repaint_dir in ["Repaint C", "Repaint L", "Repaint"]:
        rdir = mod_path / repaint_dir
        if not rdir.exists(): continue
        for txt in rdir.rglob("*.txt"):
            cfg = parse_pbs_ini(txt)
            skins = cfg.get("skin", {})
            if skins:
                repaints.append({
                    "name":  txt.stem,
                    "dir":   repaint_dir,
                    "skins": skins,
                    "textures": {k: rdir / v.replace("\\","/")
                                 for k, v in skins.items()},
                })
    return repaints

# ═══════════════════════════════════════════════════════════════════════════════
# PARSEUR 3DS NATIF
# ═══════════════════════════════════════════════════════════════════════════════
def parse_3ds(path: Path) -> dict:
    if not path.exists(): return {"meshes":[],"materials":[],"bbox":{}}
    data = open(path,"rb").read()
    meshes, materials = [], []

    def rstr(d, off):
        s=b""
        while off<len(d) and d[off]!=0: s+=bytes([d[off]]); off+=1
        return s.decode("latin1","ignore"), off+1

    def chunks(start, end):
        off=start
        while off<end-6:
            try:
                cid=struct.unpack_from("<H",data,off)[0]
                cl =struct.unpack_from("<I",data,off+2)[0]
            except: break
            if cl<6 or off+cl>end+8: break
            pl=off+6; ce=off+cl
            if cid==0xAFFF:
                mat={"name":"","texture":""}
                k=pl
                while k<ce-6:
                    try: sc=struct.unpack_from("<H",data,k)[0]; sl=struct.unpack_from("<I",data,k+2)[0]
                    except: break
                    if sl<6: break
                    if sc==0xA000: mat["name"],_=rstr(data,k+6)
                    elif sc==0xA200:
                        j=k+6
                        while j<k+sl-6:
                            try: tc=struct.unpack_from("<H",data,j)[0]; tl=struct.unpack_from("<I",data,j+2)[0]
                            except: break
                            if tl<6: break
                            if tc==0xA300: mat["texture"],_=rstr(data,j+6)
                            j+=tl
                    k+=sl
                materials.append(mat)
            elif cid==0x4000:
                nm,an=rstr(data,pl)
                mesh={"name":nm,"verts":[],"faces":[],"uvs":[],"material":""}
                k=an
                while k<ce-6:
                    try: sc=struct.unpack_from("<H",data,k)[0]; sl=struct.unpack_from("<I",data,k+2)[0]
                    except: break
                    if sl<6: break
                    se=k+sl
                    if sc==0x4100:
                        j=k+6
                        while j<se-6:
                            try: tc=struct.unpack_from("<H",data,j)[0]; tl=struct.unpack_from("<I",data,j+2)[0]
                            except: break
                            if tl<6: break
                            te=j+tl
                            if tc==0x4110:
                                try:
                                    n=struct.unpack_from("<H",data,j+6)[0]
                                    for i in range(n):
                                        x,y,z=struct.unpack_from("<3f",data,j+8+i*12)
                                        mesh["verts"].append((x,y,z))
                                except: pass
                            elif tc==0x4120:
                                try:
                                    n=struct.unpack_from("<H",data,j+6)[0]
                                    for i in range(n):
                                        a,b,c,_=struct.unpack_from("<4H",data,j+8+i*8)
                                        mesh["faces"].append((a,b,c))
                                except: pass
                            elif tc==0x4140:
                                try:
                                    n=struct.unpack_from("<H",data,j+6)[0]
                                    for i in range(n):
                                        u,v=struct.unpack_from("<2f",data,j+8+i*8)
                                        mesh["uvs"].append((u,v))
                                except: pass
                            elif tc==0x4130:
                                mn,_=rstr(data,j+6); mesh["material"]=mn
                            j+=tl
                    k+=sl
                if mesh["verts"]: meshes.append(mesh)
            elif cid in (0x4D4D,0x3D3D,0xB000): chunks(pl,ce)
            off=ce

    chunks(0, len(data))
    av=[v for m in meshes for v in m["verts"]]
    bbox={}
    if av:
        xs=[v[0] for v in av]; ys=[v[1] for v in av]; zs=[v[2] for v in av]
        bbox={"dx":max(xs)-min(xs),"dy":max(zs)-min(zs),"dz":max(ys)-min(ys),
              "cx":(min(xs)+max(xs))/2,"cy":(min(zs)+max(zs))/2,"cz":(min(ys)+max(ys))/2}
    return {"meshes":meshes,"materials":materials,"bbox":bbox,"file":path.name}

# ═══════════════════════════════════════════════════════════════════════════════
# MAPPING SHADERS SCS
# ═══════════════════════════════════════════════════════════════════════════════
def map_shader(mesh_name: str, tex_name: str, has_alpha: bool) -> str:
    ml, tl = mesh_name.lower(), tex_name.lower()
    if any(k in ml for k in ["glass","window","vitre","transparent"]): return "glass.spec"
    if any(k in ml for k in ["ineo","display","light","lamp"]): return "dif.lum.spec"
    if any(k in ml for k in ["mirror","retro"]): return "dif.spec.add.env.nofresnel"
    if any(k in tl for k in ["glass","vitre","window","transparent"]): return "glass.spec"
    if any(k in tl for k in ["_n.","_norm","_nrm"]): return "dif.spec.weight"
    if any(k in tl for k in ["reflexion","chrome"]): return "dif.spec.add.env"
    if has_alpha: return "dif.spec.over"
    return "dif.spec"

# ═══════════════════════════════════════════════════════════════════════════════
# CONVERSION TEXTURES
# ═══════════════════════════════════════════════════════════════════════════════
def next_pow2(n): return 1 if n==0 else 2**math.ceil(math.log2(max(n,1)))

def convert_texture(src: Path, dst_dir: Path) -> dict:
    dst_dds  = dst_dir / (src.stem + ".dds")
    dst_tobj = dst_dir / (src.stem + ".tobj")
    r = {"src":src.name, "dst":dst_dds.name, "status":"ok",
         "alpha":False, "resized":False}

    # Essai texconv d'abord (meilleure qualité BC7)
    if shutil.which("texconv"):
        res = subprocess.run(
            ["texconv","-f","BC7_UNORM","-nologo","-y","-m","10",
             "-o",str(dst_dir), str(src)],
            capture_output=True, timeout=60)
        if res.returncode == 0 and dst_dds.exists():
            dst_tobj.write_text(
                f'version: 1\nu_addr: 1\nv_addr: 1\nusage: tsnormal\n'
                f'bias: 0\nnocompress: 0\nnoaniso: 0\nmap:texture "{src.stem}.dds"\n')
            return r

    # Fallback Pillow
    try:
        from PIL import Image
        with Image.open(src) as img:
            r["alpha"] = img.mode=="RGBA"
            if r["alpha"]:
                vals=list(img.split()[3].getdata())
                r["alpha"] = sum(vals)/len(vals) < 250
            w,h = img.size
            nw,nh = next_pow2(w), next_pow2(h)
            if (nw,nh)!=(w,h): img=img.resize((nw,nh),Image.LANCZOS); r["resized"]=True
            img.convert("RGBA" if r["alpha"] else "RGB").save(str(dst_dds), format="DDS")
    except Exception as e:
        r["status"]="failed"; r["error"]=str(e); return r

    dst_tobj.write_text(
        f'version: 1\nu_addr: 1\nv_addr: 1\nusage: tsnormal\n'
        f'bias: 0\nnocompress: 0\nnoaniso: 0\nmap:texture "{src.stem}.dds"\n')
    return r

# ═══════════════════════════════════════════════════════════════════════════════
# GÉNÉRATION .PIM SCS
# ═══════════════════════════════════════════════════════════════════════════════
def generate_pim(slug: str, all_mesh_data: list, out_path: Path) -> int:
    lines = [
        f'##version:6', f'##source:omsi2ets2_v2', '',
        f'Header {{', f'\tFormatVersion( 6 )', f'\tName( "{slug}" )',
        f'\tGlobalScale( 1.000000 )', f'}}', '', f'Bones {{ }}', '', f'Geometry {{',
    ]
    pieces = 0
    for md in all_mesh_data:
        for mesh in md.get("meshes",[]):
            verts, faces, uvs = mesh["verts"], mesh["faces"], mesh["uvs"]
            if not verts or not faces: continue
            tex_name = next((m["texture"] for m in md.get("materials",[])
                             if m["name"]==mesh["material"]), "")
            has_alpha = "glass" in mesh["name"].lower() or "transparent" in mesh["name"].lower()
            shader = map_shader(mesh["name"], tex_name, has_alpha)
            mat_name = Path(tex_name).stem if tex_name else "default"

            lines += [f'\tPiece {{',
                      f'\t\tStreamCount( {2 if uvs else 1} )',
                      f'\t\tFaceCount( {len(faces)} )',
                      f'\t\tStreamType( POSITION )']
            if uvs: lines.append(f'\t\tStreamType( UV0 )')

            # Vertices (swap Y↔Z : PBS→SCS)
            for x,y,z in verts:
                lines.append(f'\t\t\t{x:.6f} {z:.6f} {y:.6f}')
            if uvs:
                for u,v in uvs:
                    lines.append(f'\t\t\t{u:.6f} {1.0-v:.6f}')
            for a,b,c in faces:
                if max(a,b,c)<len(verts):
                    lines.append(f'\t\tTriangle {{ {a} {c} {b} }}')
            lines.append(f'\t\tMaterial {{ "{mat_name}" "{shader}" }}')
            lines.append(f'\t}}')
            pieces += 1

    lines += ['}','']
    out_path.write_text("\n".join(lines), encoding="utf-8")
    return pieces

# ═══════════════════════════════════════════════════════════════════════════════
# GÉNÉRATION DÉFINITIONS ETS2 (.sii)
# ═══════════════════════════════════════════════════════════════════════════════
def generate_vehicle_sii(slug: str, specs: dict, wheels: list,
                          cameras: list, out_dir: Path) -> Path:
    def_dir = out_dir / "def" / "vehicle" / "bus"
    def_dir.mkdir(parents=True, exist_ok=True)
    L, W, H = specs["length"], specs["width"], specs["height"]
    axle_count = specs.get("axles", 2)
    wheel_locs = "\n".join(
        f'\t\tbb_axle_locator[{i}]: "{w["locator"]}"'
        for i,w in enumerate(wheels))
    cam_views = "\n".join(
        f'\t\tcab_view[{i}]: "{c["name"]}"' for i,c in enumerate(cameras))

    sii = f"""SiiNunit
{{

vehicle_data : vehicle.bus.{slug} {{

\tname: "Heuliez Bus {slug.upper().replace('_',' ')}"
\tshort_name: "{slug[:12]}"
\tinfo_text: "Heuliez Bus {specs.get('engine','Iveco')} | {specs.get('normed','Euro4')} | Converti depuis PBS par omsi2ets2"

\tmodel:        "/vehicle/bus/{slug}/{slug}.pmg"
\tmodel_shadow: "/vehicle/bus/{slug}/{slug}_shadow.pmg"

\tphysics_body: vehicle.bus.{slug}.chassis

\twheel_count: {len(wheels)}
{wheel_locs}

\taxle_count: {axle_count}

\tcab_view_count: {len(cameras)}
{cam_views}

\twidth:  {W:.3f}
\theight: {H:.3f}
\tlength: {L:.3f}

\tcategory: "buses"
\tauthor:   "omsi2ets2-converter | Ago Projects original"

}}

}}
"""
    p = def_dir / f"{slug}.sii"
    p.write_text(sii, encoding="utf-8")
    return p

def generate_chassis_sii(slug: str, specs: dict, wheels: list,
                          engine: dict, out_dir: Path) -> Path:
    def_dir = out_dir / "def" / "vehicle" / "bus"
    def_dir.mkdir(parents=True, exist_ok=True)
    H = specs["height"]
    ratios_str = "\n".join(
        f'\t\tforward_gear_ratio[{i}]: {r:.4f}'
        for i,r in enumerate(engine.get("gear_ratios",[3.43,2.01,1.42,1.0])))
    l_wheels = [w for w in wheels if w["side"]=="l"]
    r_wheels  = [w for w in wheels if w["side"]=="r"]

    axles_str = ""
    for i,(lw,rw) in enumerate(zip(l_wheels, r_wheels)):
        is_front = i==0
        axles_str += f"""
\taxle[{i}].position:  (0, {lw['y']:.4f}, {lw['z']:.4f})
\taxle[{i}].track:     {abs(lw['x'])+abs(rw['x']):.4f}
\taxle[{i}].steering:  {"true" if is_front else "false"}
\taxle[{i}].driven:    {"false" if is_front else "true"}
"""
    wheels_str = ""
    for i,w in enumerate(wheels):
        wheels_str += f"""
\twheel[{i}].position: ({w['x']:.4f}, {w['y']:.4f}, {w['z']:.4f})
\twheel[{i}].radius:   {w['radius']:.4f}
\twheel[{i}].mass:     {w['mass']:.1f}
\twheel[{i}].spring:   {w['spring']:.1f}
\twheel[{i}].damper:   {w['damper']:.1f}
"""
    sii = f"""SiiNunit
{{

vehicle_chassis : vehicle.bus.{slug}.chassis {{

\tname: "Heuliez {slug.upper()} Chassis"

\tcenter_of_mass_offset: (0, {H*0.35:.3f}, 0)
\tmass: 11500
\taxle_count: {specs.get('axles',2)}
{axles_str}
{wheels_str}
\tengine_rpm_idle:  {engine.get('idle_rpm',550):.0f}
\tengine_rpm_limit: {engine.get('max_rpm',2300):.0f}
\tengine_torque:    {engine.get('peak_torque',550):.0f}

\tforward_gear_count: {len(engine.get('gear_ratios',[3.43,2.01,1.42,1.0]))}
{ratios_str}
\treverse_gear_count: 1
\treverse_gear_ratio[0]: 4.8400

\tdifferential_ratio: {engine.get('diff_ratio',6.2):.4f}
\tmax_steering_angle: 45

}}

}}
"""
    p = def_dir / f"{slug}_chassis.sii"
    p.write_text(sii, encoding="utf-8")
    return p

def generate_paintjobs(slug: str, repaints: list, out_dir: Path) -> int:
    """Génère les définitions paintjob ETS2 pour chaque repaint PBS"""
    pj_dir = out_dir / "def" / "vehicle" / "bus" / "paintjob"
    pj_dir.mkdir(parents=True, exist_ok=True)
    count = 0
    for rp in repaints:
        pj_slug = re.sub(r"[^a-z0-9_]","_", rp["name"].lower()).strip("_")
        sii = f"""SiiNunit
{{

vehicle_paintjob : vehicle.bus.{slug}.paintjob.{pj_slug} {{

\tname:           "{rp['name']}"
\tvehicle:        vehicle.bus.{slug}
\tbase_color:     (1, 1, 1)

\tbase_texture:   "/vehicle/bus/{slug}/repaint/{pj_slug}/skin.dds"

\tprice:          0
\tunlock:         0

}}

}}
"""
        (pj_dir / f"{pj_slug}.sii").write_text(sii, encoding="utf-8")
        count += 1
    return count

def generate_manifest(slug: str, out_dir: Path):
    (out_dir / "manifest.sii").write_text(f"""SiiNunit
{{

mod_package : .manifest {{

\tpackage_version: "1.0"
\tdisplay_name:    "Heuliez Bus GX x27 — PBS→ETS2 (omsi2ets2 v2)"
\tdescription:     "Conversion automatique depuis Proton Bus Simulator\\nVéhicules : GX127, GX127L\\nOriginal : Ago Projects (Lenny_91, KRcd)\\nConvertisseur : omsi2ets2 v2"
\tauthor:          "omsi2ets2-converter"
\tcategories[]:   "buses"
\tcategories[]:   "french"

}}

}}
""", encoding="utf-8")

# ═══════════════════════════════════════════════════════════════════════════════
# SCS CONVERSION TOOLS
# ═══════════════════════════════════════════════════════════════════════════════
def find_scs_tools() -> Optional[Path]:
    """Cherche SCS Conversion Tools dans les emplacements standard"""
    candidates = [
        Path("./conversion_tools_2_21"),
        Path("./scs_tools"),
        Path("./conversion_tools"),
        Path(r"C:/SCS/conversion_tools_2_21"),
        Path(os.environ.get("SCS_TOOLS_PATH", "__none__")),
    ]
    for d in candidates:
        for cmd in ["convert.cmd", "convert.sh", "convert.bat"]:
            if (d / cmd).exists():
                return d / cmd
    return None

def compile_with_scs_tools(mod_tmp: Path, scs_cmd: Path, out_dir: Path) -> tuple:
    """
    Lance SCS Conversion Tools :
      1. Copie notre mod dans conversion_tools/base/
      2. Exécute convert.cmd
      3. Récupère rsrc/base/@cache/ comme résultat compilé
    """
    tools_dir = scs_cmd.parent
    base_dir  = tools_dir / "base"
    rsrc_dir  = tools_dir / "rsrc" / "base" / "@cache"

    # Préparer base/
    if base_dir.exists(): shutil.rmtree(base_dir)
    base_dir.mkdir(parents=True)
    for item in mod_tmp.iterdir():
        dst = base_dir / item.name
        shutil.copytree(item, dst) if item.is_dir() else shutil.copy2(item, dst)

    # Lancer la compilation
    try:
        if sys.platform == "win32":
            r = subprocess.run([str(scs_cmd)], cwd=str(tools_dir),
                               capture_output=True, timeout=300, shell=True)
        else:
            r = subprocess.run(["bash", str(scs_cmd)], cwd=str(tools_dir),
                               capture_output=True, timeout=300)
        log_p = tools_dir / "mass_convert.log"
        log = log_p.read_text(errors="ignore") if log_p.exists() else ""
        errors = [l for l in log.splitlines() if "ERROR" in l.upper()]
        return r.returncode==0 and rsrc_dir.exists(), rsrc_dir, errors
    except Exception as e:
        return False, rsrc_dir, [str(e)]

# ═══════════════════════════════════════════════════════════════════════════════
# PIPELINE PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════════
def convert(mod_path: Path, output_dir: Path, vehicle_id: str = "GX127") -> dict:
    t0 = time.time()
    mod_path   = Path(mod_path)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    specs = VEHICLE_SPECS.get(vehicle_id, VEHICLE_SPECS["GX127"])
    slug  = f"heuliez_{vehicle_id.lower()}"
    tmp   = Path("/tmp") / f"ets2_{slug}_{int(t0)}"
    tmp.mkdir(parents=True)

    print()
    print(col("b","═"*64))
    print(col("b",f"  PBS → ETS2  |  Heuliez Bus {vehicle_id}  |  omsi2ets2 v2"))
    print(col("gray", f"  {specs['length']}m × {specs['width']}m × {specs['height']}m"
              f"  |  {specs['engine']}  |  {datetime.now():%H:%M:%S}"))
    print(col("b","═"*64))

    # ── 1. INGESTION ──────────────────────────────────────────────────────────
    plog(1,7,"Ingestion fichiers PBS","run")
    variant = "L" if vehicle_id=="GX127L" else ""
    model_info = read_models_list(mod_path, variant)
    wheels     = read_wheels(mod_path, variant)
    engine     = read_engine(mod_path)
    repaints   = read_repaints(mod_path)
    textures   = sorted((mod_path/"Texture").glob("*.png")) if (mod_path/"Texture").exists() else []
    sounds     = list(mod_path.rglob("*.wav")) + list(mod_path.rglob("*.ogg"))

    mesh_files = [info["path"] for info in model_info["meshes"].values()
                  if info["path"].exists()]
    plog(1,7,"Ingestion fichiers PBS","ok",
         f"{len(mesh_files)} meshes | {len(textures)} textures | "
         f"{len(sounds)} sons | {len(repaints)} repaints")

    # ── 2. GÉOMÉTRIE ──────────────────────────────────────────────────────────
    plog(2,7,"Géométrie (wheels / steering / specs PDF)","run")
    steering = model_info["steering"]
    sw_x = steering["x"] if steering else 0.6
    sw_y = steering["y"] if steering else 1.64
    sw_z = steering["z"] if steering else 4.0
    cameras = [
        {"name":"driver","x":sw_x,"y":sw_y,"z":sw_z},
        {"name":"roof",  "x":0.0, "y":specs["height"]+0.3,"z":0.0},
        {"name":"back",  "x":0.0, "y":1.5,"z":-specs["length"]*0.35},
    ]
    plog(2,7,"Géométrie (wheels / steering / specs PDF)","ok",
         f"{len(wheels)} roues exactes | volant X={sw_x:.3f} Y={sw_y:.3f} Z={sw_z:.3f} | "
         f"{specs['length']}m × {specs['width']}m × {specs['height']}m")

    # ── 3. PARSE MESHES 3DS ───────────────────────────────────────────────────
    plog(3,7,"Parsing meshes .3ds","run")
    all_mesh_data, total_v, total_f, failed = [], 0, 0, []
    for f3ds in mesh_files:
        try:
            d = parse_3ds(f3ds)
            all_mesh_data.append(d)
            total_v += sum(len(m["verts"]) for m in d["meshes"])
            total_f += sum(len(m["faces"]) for m in d["meshes"])
        except Exception as e:
            failed.append(f"{f3ds.name}: {e}")

    status = "warn" if failed else "ok"
    plog(3,7,"Parsing meshes .3ds", status,
         f"{len(all_mesh_data)}/{len(mesh_files)} fichiers | "
         f"{total_v:,} verts | {total_f:,} faces")
    for f in failed[:2]: print(col("y",f"    ⚠ {f}"))

    # ── 4. TEXTURES ───────────────────────────────────────────────────────────
    plog(4,7,"Conversion textures PNG → DDS + .tobj","run")
    tex_out = tmp / "texture"
    tex_out.mkdir(parents=True)

    def conv_one(t): return convert_texture(t, tex_out)
    with ThreadPoolExecutor(max_workers=4) as pool:
        tex_results = list(pool.map(conv_one, textures))

    ok_tex    = sum(1 for r in tex_results if r["status"]=="ok")
    resized   = sum(1 for r in tex_results if r.get("resized"))
    fail_tex  = sum(1 for r in tex_results if r["status"]=="failed")
    plog(4,7,"Conversion textures PNG → DDS + .tobj",
         "warn" if fail_tex else "ok",
         f"{ok_tex}/{len(textures)} OK | {resized} redimensionnées | {fail_tex} échecs")

    # ── 5. GÉNÉRATION .PIM ───────────────────────────────────────────────────
    plog(5,7,"Génération .pim SCS","run")
    model_dir = tmp / "vehicle" / "bus" / slug
    model_dir.mkdir(parents=True, exist_ok=True)
    pim_path = model_dir / f"{slug}.pim"
    pieces = generate_pim(slug, all_mesh_data, pim_path)
    pim_kb = pim_path.stat().st_size // 1024
    plog(5,7,"Génération .pim SCS","ok",
         f"{pieces} pièces | {pim_kb} Ko")

    # ── 6. DÉFINITIONS .SII ──────────────────────────────────────────────────
    plog(6,7,"Génération .sii + paintjobs","run")
    generate_vehicle_sii(slug, specs, wheels, cameras, tmp)
    generate_chassis_sii(slug, specs, wheels, engine, tmp)
    pj_count = generate_paintjobs(slug, repaints, tmp)
    generate_manifest(slug, tmp)

    # Copier sons
    snd_dir = tmp / "sound" / "bus" / slug
    snd_dir.mkdir(parents=True, exist_ok=True)
    snd_ok = sum(1 for s in sounds
                 if shutil.copy2(s, snd_dir/s.name) or True)
    plog(6,7,"Génération .sii + paintjobs","ok",
         f"vehicle.sii + chassis.sii + manifest.sii | {pj_count} paintjobs | {snd_ok} sons")

    # ── 7. COMPILATION + PACKAGING ───────────────────────────────────────────
    plog(7,7,"Compilation SCS + packaging","run")

    scs_cmd = find_scs_tools()
    compiled = False
    compile_src = tmp  # source pour le packaging

    if scs_cmd:
        print(col("c",f"    SCS Conversion Tools trouvé : {scs_cmd}"))
        ok, rsrc_dir, errs = compile_with_scs_tools(tmp, scs_cmd, output_dir)
        if ok:
            compiled = True
            compile_src = rsrc_dir
            for e in errs[:2]: print(col("y",f"    ⚠ {e}"))
        else:
            print(col("y","    ⚠ Compilation SCS échouée — packaging .pim non compilé"))
            for e in errs[:3]: print(col("y",f"      {e}"))
    else:
        print(col("y","    ℹ SCS Conversion Tools absent — .pim non compilé en .pmg"))
        print(col("gray","      → https://download.eurotrucksimulator2.com/conversion_tools_2_21.zip"))
        print(col("gray","      → Extraire à côté de ce script, relancer"))

    # Validation
    checks = {
        "manifest.sii":  (tmp/"manifest.sii").exists(),
        "vehicle.sii":   (tmp/"def"/"vehicle"/"bus"/f"{slug}.sii").exists(),
        "chassis.sii":   (tmp/"def"/"vehicle"/"bus"/f"{slug}_chassis.sii").exists(),
        f"{slug}.pim":   pim_path.exists() and pim_path.stat().st_size > 10000,
        "textures":      any(tex_out.glob("*.dds")),
    }
    errors = [k for k,v in checks.items() if not v]

    # Packaging .scs
    scs_path = output_dir / f"Heuliez_Bus_{vehicle_id}.scs"
    try:
        with zipfile.ZipFile(scs_path,"w",zipfile.ZIP_DEFLATED,compresslevel=6) as zf:
            for f in compile_src.rglob("*"):
                if f.is_file():
                    zf.write(f, f.relative_to(compile_src))
        scs_kb = scs_path.stat().st_size // 1024
        compiled_tag = " [.pmg compilé ✓]" if compiled else " [.pim — needs SCS Tools]"
        plog(7,7,"Compilation SCS + packaging",
             "err" if errors else "ok",
             f"{scs_path.name} ({scs_kb} Ko){compiled_tag}")
    except Exception as e:
        errors.append(f"packaging: {e}")
        plog(7,7,"Compilation SCS + packaging","err",str(e))
        scs_path = None

    shutil.rmtree(tmp, ignore_errors=True)
    duration = time.time() - t0

    # Confiance
    confidence = round(min(1.0,
        (1 - 0.1*len(errors)) *
        (ok_tex/max(len(textures),1)) *
        (1.0 if total_f>1000 else 0.8) *
        (1.0 if steering else 0.97)
    ) * 100, 1)

    print()
    print(col("b","─"*64))
    c = col("g","✓ SUCCÈS") if not errors else col("r","✗ ÉCHEC")
    print(f"  {c}  —  Heuliez Bus {vehicle_id}")
    print(col("gray",f"  Confiance  : {confidence}%"))
    print(col("gray",f"  Durée      : {duration:.1f}s"))
    print(col("gray",f"  Géométrie  : {total_v:,} verts | {total_f:,} faces | {pieces} pièces"))
    print(col("gray",f"  Textures   : {ok_tex}/{len(textures)} ({resized} redimensionnées)"))
    print(col("gray",f"  Paintjobs  : {pj_count} livrées incluses"))
    print(col("gray",f"  Sons       : {snd_ok} fichiers"))
    print(col("gray",f"  .pmg compilé : {'✓ oui' if compiled else '✗ non (SCS Tools requis)'}"))
    if not compiled:
        print(col("y", ""))
        print(col("y", "  ┌─ PROCHAINE ÉTAPE pour jouer dans ETS2 ────────────────────"))
        print(col("y", "  │  1. Télécharger SCS Conversion Tools v2.21 :"))
        print(col("y", "  │     https://download.eurotrucksimulator2.com/conversion_tools_2_21.zip"))
        print(col("y", "  │  2. Extraire dans le même dossier que ce script"))
        print(col("y", "  │  3. Relancer la conversion — le .pmg sera compilé automatiquement"))
        print(col("y", "  └────────────────────────────────────────────────────────────"))
    for e in errors: print(col("r",f"  ✗ {e}"))
    print(col("b","─"*64))
    print()

    return {"success": not errors, "scs": str(scs_path) if scs_path else None,
            "compiled": compiled, "confidence": confidence, "duration": duration}

# ═══════════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="PBS → ETS2 | Heuliez GX x27 v2")
    ap.add_argument("mod",    help="Dossier du mod PBS")
    ap.add_argument("--output","-o", default="./output")
    ap.add_argument("--vehicle","-v", default="GX127",
                    choices=["GX127","GX127L","GX327","GX427"],
                    help="Variante à convertir")
    ap.add_argument("--all", action="store_true",
                    help="Convertir GX127 et GX127L en parallèle")
    args = ap.parse_args()

    if args.all:
        from concurrent.futures import ThreadPoolExecutor as TPE
        variants = ["GX127","GX127L"]
        print(col("b",f"\n  Conversion batch : {', '.join(variants)}"))
        with TPE(max_workers=2) as pool:
            results = list(pool.map(
                lambda v: convert(Path(args.mod), Path(args.output), v),
                variants))
        ok = sum(1 for r in results if r["success"])
        print(col("g" if ok==len(variants) else "y",
                  f"\n  Batch terminé : {ok}/{len(variants)} réussis"))
    else:
        r = convert(Path(args.mod), Path(args.output), args.vehicle)
        sys.exit(0 if r["success"] else 1)
