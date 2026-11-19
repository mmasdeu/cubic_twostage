# SPDX-License-Identifier: GPL-3.0-or-later
"""TikZ figures of the regions V(q) for the write-up (in the style of the figures of
Guitart-Masdeu, paper/continued-fractions.tex).  Run from the project root:
    /usr/bin/python3 writeup/gen_regions.py
Writes writeup/fig-horn.tex, writeup/fig-slices.tex, writeup/fig-zoom3.tex.
Data: the certificate of d = -327 (t^3 - t^2 - 2t - 3), and a covering attempt with N = 1."""
import os, sys, json, math, pickle
os.environ.setdefault("OMP_NUM_THREADS", "1")
sys.path.insert(0, ".")
import numpy as np
import contourpy
import sage.all
from sage.all import QQ, latex
from cubic_twostage import TwoStage

OUT = "writeup"
R = {json.loads(l)["disc"]: json.loads(l) for l in open("data/results_final_v2.jsonl")}
REC = R[-327]
CERT_FILE = REC["cert"]
if not os.path.exists(CERT_FILE):          # full certificate set not present: use the bundled sample
    CERT_FILE = os.path.join("samples", "certificates", os.path.basename(CERT_FILE))
POLY, CERT = pickle.load(open(CERT_FILE, "rb"))
S = TwoStage(POLY)
SLICE = 15 / 33                      # third lattice coordinate of the witness (2, 20, 15)/33
WIT = (2 / 33, 20 / 33)


def f(x):
    return f"{x:.4f}".rstrip("0").rstrip(".") if abs(x) > 1e-12 else "0"


def P(x, y):
    return f"({f(x)},{f(y)})"


# ------------------------------------------------------------------ 3D picture of V(0)
def fig_horn(Rmax=2.2, Umax=3.4, az=28.0, el=20.0, nth=60):
    """Shaded 3D rendering of the boundary of V(0) = {|u||w|^2 < 1}, truncated to
    |w| <= Rmax and |u| <= Umax.  World coordinates (x, y, z) = (u, Im w, Re w).
    Orthographic view from azimuth az / elevation el, Lambert shading, painter's algorithm."""
    base = np.array([31, 119, 180]) / 255          # regA
    cut = np.array([150, 190, 225]) / 255          # truncation faces (lighter)
    ar, er = math.radians(az), math.radians(el)
    d = np.array([math.sin(ar) * math.cos(er), -math.cos(ar) * math.cos(er), math.sin(er)])  # towards viewer
    up = np.array([0.0, 0.0, 1.0])
    rgt = np.cross(up, d); rgt /= np.linalg.norm(rgt)
    scr_up = np.cross(d, rgt)
    light = np.array([0.35, -0.75, 0.75]); light /= np.linalg.norm(light)

    def proj(p):
        return (float(p @ rgt), float(p @ scr_up))

    def colour(rgb, n, ambient=0.38):
        lam = max(0.0, float(n @ light))
        spec = max(0.0, float(n @ ((light + d) / np.linalg.norm(light + d)))) ** 24
        c = rgb * (ambient + (1 - ambient) * lam) + 0.35 * spec
        c = np.clip(c * 1.08, 0, 1)
        return "{rgb,255:red,%d;green,%d;blue,%d}" % tuple(int(round(255 * t)) for t in c)

    faces = []                                      # (depth, points, colour)
    u0 = 1 / Rmax ** 2
    th = np.linspace(0, 2 * math.pi, nth + 1)

    def add_quad(pts, n, rgb, ambient=0.38):
        n = n / np.linalg.norm(n)
        if n @ d <= 0:                              # back face: hidden by the solid
            return
        faces.append((float(np.mean([p @ d for p in pts])), [proj(p) for p in pts], colour(rgb, n, ambient)))

    # boundary surface |w| = |u|^(-1/2), both sides, rows spaced geometrically from u0 to Umax
    us = [u0 * (Umax / u0) ** (i / 30) for i in range(31)]
    for sgn in (1, -1):
        for i in range(len(us) - 1):
            ua, ub = us[i], us[i + 1]
            ra, rb = ua ** -0.5, ub ** -0.5
            um = (ua + ub) / 2; rp = 0.5 * um ** -1.5          # |dr/du| at the middle
            for j in range(nth):
                t0, t1 = th[j], th[j + 1]; tm = (t0 + t1) / 2
                pts = [np.array([sgn * ua, ra * math.sin(t0), ra * math.cos(t0)]),
                       np.array([sgn * ub, rb * math.sin(t0), rb * math.cos(t0)]),
                       np.array([sgn * ub, rb * math.sin(t1), rb * math.cos(t1)]),
                       np.array([sgn * ua, ra * math.sin(t1), ra * math.cos(t1)])]
                n = np.array([sgn * rp, math.sin(tm), math.cos(tm)])  # outward normal (-r', sin, cos)
                add_quad(pts, n, base)
    # truncation: cylinder |w| = Rmax for |u| <= u0, and the end discs |u| = Umax
    for j in range(nth):
        t0, t1 = th[j], th[j + 1]; tm = (t0 + t1) / 2
        pts = [np.array([-u0, Rmax * math.sin(t0), Rmax * math.cos(t0)]), np.array([u0, Rmax * math.sin(t0), Rmax * math.cos(t0)]),
               np.array([u0, Rmax * math.sin(t1), Rmax * math.cos(t1)]), np.array([-u0, Rmax * math.sin(t1), Rmax * math.cos(t1)])]
        add_quad(pts, np.array([0, math.sin(tm), math.cos(tm)]), cut, 0.6)
    re = Umax ** -0.5
    for sgn in (1, -1):
        disc = [np.array([sgn * Umax, re * math.sin(t), re * math.cos(t)]) for t in th[:-1]]
        n = np.array([sgn, 0.0, 0.0])
        if n @ d > 0:
            faces.append((float(np.mean([p @ d for p in disc])), [proj(p) for p in disc], colour(cut, n, 0.75)))

    def path(pts):
        return " -- ".join(P(*p) for p in pts) + " -- cycle"

    L = [r"\begin{tikzpicture}[scale=0.95]"]
    # asymptotic sets, part behind the solid: the left end of the u-axis and the far half of the circle
    ring = [np.array([0.0, (Rmax + .45) * math.sin(t), (Rmax + .45) * math.cos(t)]) for t in np.linspace(0, 2 * math.pi, 121)]
    back = [p for p in ring if p @ d < 0]; front_idx = [i for i, p in enumerate(ring) if p @ d >= 0]
    def arc(sel):
        return " -- ".join(P(*proj(p)) for p in sel)
    # split the circle into its back and front arcs (contiguous index runs)
    runs, cur = [], [ring[0]]
    for p_prev, p in zip(ring, ring[1:]):
        if (p_prev @ d >= 0) == (p @ d >= 0):
            cur.append(p)
        else:
            runs.append(cur); cur = [p_prev, p]
    runs.append(cur)
    for r_ in runs:
        if r_[len(r_) // 2] @ d < 0:
            L.append(rf"\draw[regA!80!black, densely dotted] {arc(r_)};")
    L.append(rf"\draw[regA!80!black, densely dotted, thick] {P(*proj(np.array([-Umax - 1.0, 0, 0])))} -- {P(*proj(np.array([-Umax, 0, 0])))};")
    for dep, pts, col in sorted(faces, key=lambda t: t[0]):
        L.append(rf"\filldraw[fill={col}, draw={col}, line width=0.15pt] {path(pts)};")
    # silhouette-like outline of the end discs and of the truncation band
    for sgn in (1, -1):
        disc = [np.array([sgn * Umax, re * math.sin(t), re * math.cos(t)]) for t in th]
        if np.array([sgn, 0, 0]) @ d > 0:
            L.append(rf"\draw[regA!60!black, line width=0.4pt] {' -- '.join(P(*proj(p)) for p in disc)};")
    for r_ in runs:
        if r_[len(r_) // 2] @ d >= 0:
            L.append(rf"\draw[regA!80!black, densely dotted] {arc(r_)};")
    L.append(rf"\draw[regA!80!black, densely dotted, thick] {P(*proj(np.array([Umax, 0, 0])))} -- {P(*proj(np.array([Umax + 1.0, 0, 0])))};")
    # labels
    L.append(rf"\node[font=\scriptsize, regA!80!black, anchor=west] at {P(*proj(np.array([Umax + 1.05, 0, 0])))} {{$w=0$}};")
    L.append(rf"\node[font=\scriptsize, regA!80!black, anchor=south] at {P(*proj(np.array([0, 0, Rmax + .5])))} {{$u=0$}};")
    L.append(rf"\node[font=\small, regA!85!black] at {P(*proj(np.array([2.4, 0, 1.75])))} {{$V(0)$}};")
    # axes triad
    o = np.array([-Umax - 0.6, -0.5, -Rmax - 0.4])
    for vec, lab in ((np.array([0.9, 0, 0]), r"$u$"), (np.array([0, 0.9, 0]), r"$\operatorname{Im}w$"), (np.array([0, 0, 0.9]), r"$\operatorname{Re}w$")):
        L.append(rf"\draw[->, gray] {P(*proj(o))} -- {P(*proj(o + vec))} node[font=\scriptsize, anchor=west] {{{lab}}};")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L)


# ------------------------------------------------------------------ slices of D
def in_slice(lo3, w):
    return lo3 <= SLICE < lo3 + w


def cert_boxes_in_slice():
    out = []
    for m, d, ci, g in CERT:
        w = 2.0 ** -d
        if in_slice(m[2] * w, w):
            out.append((m[0] * w, m[1] * w, w, d, ci, tuple(g)))
    return out


def rect(x0, y0, w, style):
    return rf"\fill[{style}] {P(x0, y0)} rectangle {P(x0 + w, y0 + w)};"


def outline(x0, y0, w, style):
    return rf"\draw[{style}] {P(x0, y0)} rectangle {P(x0 + w, y0 + w)};"


def fig_slices(sc=4.6):
    panels = []
    # left: N = 1 attempt
    certs, failed = S.cover(1, T=3, maxdepth=6, verbose=False, max_failed=None, K=2, L=300, W=20)
    cs = [(lo[0], lo[1], w, d) for lo, w, d, k in certs if in_slice(lo[2], w)]
    fs = [(lo[0], lo[1], w, d) for lo, w, d in failed if in_slice(lo[2], w)]
    L = [rf"\begin{{tikzpicture}}[scale={sc}]"]
    L += [rect(x, y, w, "regA!18") for x, y, w, d in cs]
    L += [rect(x, y, w, "bad") for x, y, w, d in fs]
    L += [outline(x, y, w, "black!45, line width=0.15pt") for x, y, w, d in cs if d <= 5]
    L.append(r"\draw[black!80] (0,0) rectangle (1,1);")
    L.append(rf"\node[star, star points=5, fill=black, inner sep=1.1pt] at {P(*WIT)} {{}};")
    L.append(r"\node[font=\scriptsize, below] at (0.5,0) {$N=1$: %d boxes, %d undecided at depth 6};" % (len(cs), len(fs)))
    L.append(r"\end{tikzpicture}")
    panels.append("\n".join(L))
    # right: the certificate (N = 3)
    sl = cert_boxes_in_slice()
    L = [rf"\begin{{tikzpicture}}[scale={sc}]"]
    for x, y, w, d, ci, g in sl:
        L.append(rect(x, y, w, ("regA" if ci[1] == 1 else "regB") + "!30"))
    L += [outline(x, y, w, "black!55, line width=0.2pt") for x, y, w, d, ci, g in sl]
    L.append(r"\draw[black!80] (0,0) rectangle (1,1);")
    L.append(rf"\node[star, star points=5, fill=black, inner sep=1.1pt] at {P(*WIT)} {{}};")
    n1 = sum(1 for b in sl if b[4][1] == 1)
    L.append(r"\node[font=\scriptsize, below] at (0.5,0) {$N=3$: %d boxes (%d with $|\mathrm{Nm}(q_2)|=1$, %d with $3$)};" % (len(sl), n1, len(sl) - n1))
    L.append(r"\end{tikzpicture}")
    panels.append("\n".join(L))
    meta = dict(n1_cert=len(cs), n1_fail=len(fs), cert=len(sl), cert_n1=n1)
    return panels[0] + "\n\\hfill\n" + panels[1], meta


# ------------------------------------------------------------------ zoom with region boundaries
def centre_coords(ci, g):
    return np.array([float(c) + gi for c, gi in zip(ci[0], g)])


def region_contours(c, n, x0, y0, w, k=500):
    xs = np.linspace(x0, x0 + w, k); ys = np.linspace(y0, y0 + w, k)
    X, Y = np.meshgrid(xs, ys)
    A = np.stack([X - c[0], Y - c[1], np.full_like(X, SLICE - c[2])], axis=-1)
    Z = A @ S.M.T
    F = n * np.abs(Z[..., 0]) * (Z[..., 1] ** 2 + Z[..., 2] ** 2)
    lines = contourpy.contour_generator(xs, ys, F).lines(1.0)
    out = []
    for ln in lines:
        if len(ln) < 2:
            continue
        step = max(1, len(ln) // 160)
        pts = ln[::step].tolist() + ([ln[-1].tolist()] if (len(ln) - 1) % step else [])
        out.append(" -- ".join(P(px, py) for px, py in pts))
    return out


def fig_zoom(sc=22.0):
    sl = cert_boxes_in_slice()
    # window: chosen by searching squares of side 1/4, 3/16, 1/8 (half-step grid) for the one in
    # which the boundaries of the most certifying regions are visible (4 of 5 here)
    w, x0, y0 = 0.25, 0.75, 0.75
    inside = [b for b in sl if b[0] < x0 + w and b[0] + b[2] > x0 and b[1] < y0 + w and b[1] + b[2] > y0]
    keys = {(tuple(b[4][0]), b[4][1], b[5]) for b in inside}
    order = sorted(keys, key=lambda k: (k[1], k))
    n1 = [k for k in order if k[1] == 1]; n3 = [k for k in order if k[1] != 1]
    colour = {**{k: ["zA", "zB", "zC"][i] for i, k in enumerate(n1)}, **{k: ["zD", "zE", "zF"][i] for i, k in enumerate(n3)}}
    L = [rf"\begin{{tikzpicture}}[scale={sc}]", rf"\begin{{scope}}\clip {P(x0, y0)} rectangle {P(x0 + w, y0 + w)};"]
    for b in inside:
        k = (tuple(b[4][0]), b[4][1], b[5])
        L.append(rect(b[0], b[1], b[2], f"{colour[k]}!28"))
    for k in order:
        ci = next(b[4] for b in inside if (tuple(b[4][0]), b[4][1], b[5]) == k)
        c = centre_coords(ci, k[2])
        for path in region_contours(c, k[1], x0, y0, w):
            L.append(rf"\draw[{colour[k]}!85!black, thick] {path};")
    for b in inside:
        L.append(outline(b[0], b[1], b[2], "black!70, line width=0.3pt"))
    L.append(r"\end{scope}")
    L.append(rf"\draw[black!80] {P(x0, y0)} rectangle {P(x0 + w, y0 + w)};")
    if x0 <= WIT[0] <= x0 + w and y0 <= WIT[1] <= y0 + w:
        L.append(rf"\node[star, star points=5, fill=black, inner sep=1.1pt] at {P(*WIT)} {{}};")
    leg = []
    for k in order:
        q = S.elt([QQ(c) + gi for c, gi in zip(k[0], k[2])])
        leg.append(rf"\textcolor{{{colour[k]}!85!black}}{{\rule{{6pt}}{{6pt}}}}\ $q={latex(q)}$, $|\mathrm{{Nm}}(q_2)|={k[1]}$")
    L.append(rf"\node[anchor=north west, font=\scriptsize, align=left] at {P(x0 + w + 0.012, y0 + w)} {{" + r"\\ ".join(leg) + "};")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L), dict(x0=x0, y0=y0, w=w, boxes=len(inside), centres=len(keys), legend=[(str(S.elt([QQ(c) + gi for c, gi in zip(k[0], k[2])])), k[1]) for k in order])


if __name__ == "__main__":
    hdr = "% generated by writeup/gen_regions.py; do not edit by hand\n"
    open(f"{OUT}/fig-horn.tex", "w").write(hdr + fig_horn() + "\n")
    if sys.argv[1:] == ["horn"]:
        sys.exit(0)
    s, m1 = fig_slices(); open(f"{OUT}/fig-slices.tex", "w").write(hdr + s + "\n")
    z, m2 = fig_zoom(); open(f"{OUT}/fig-zoom3.tex", "w").write(hdr + z + "\n")
    print("slices:", m1); print("zoom:", m2)
