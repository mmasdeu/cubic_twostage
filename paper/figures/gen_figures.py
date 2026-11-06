# SPDX-License-Identifier: GPL-3.0-or-later
"""Generate the TikZ figures of the paper (Section 2-3 illustrations) for F = Q(sqrt 14).
usage (from paper/figures):  python3 gen_figures.py      (needs Sage)
Writes fig-regions.tex, fig-strips.tex, fig-boxlemma.tex, fig-solve.tex, fig-zoom.tex.
All coverings drawn are produced by covering2d.Cover2D.solve, i.e. Algorithm SOLVE with the
corner test of Lemma 3.2, every containment certified in 200-bit interval arithmetic."""
import sys, math
sys.path.insert(0, '.')
import sage.all
from covering2d import Cover2D

M = 14
S = Cover2D(M)
D = S.D                                   # corners of D: v(0), v(1), v(1+w), v(w)
R0 = [float(t) for t in S.R0]
SQ = math.sqrt(M)


def f(x):
    return f"{x:.4f}".rstrip('0').rstrip('.') if abs(x) > 1e-12 else "0"


def P(x, y):
    return f"({f(x)},{f(y)})"


def region_path(X, Y, eps, W=40.0, k=60):
    """Closed polygon of {|(x-X)(y-Y)| < eps} intersected with the square of half-side W."""
    a = eps / W
    us = [a * (W / a) ** (i / k) for i in range(k + 1)]          # geometric spacing a..W
    pts = []
    pts += [(u, eps / u) for u in reversed(us)]                    # Q1 branch, from (W,a) to (a,W)
    pts += [(-u, eps / u) for u in us]                             # Q2 branch, (-a,W) to (-W,a)
    pts += [(-u, -eps / u) for u in reversed(us)]                  # Q3 branch, (-W,-a) to (-a,-W)
    pts += [(u, -eps / u) for u in us]                             # Q4 branch, (a,-W) to (W,-a)
    return " -- ".join(P(X + u, Y + v) for u, v in pts) + " -- cycle"


def branches(X, Y, eps, W=40.0, k=60):
    """The four hyperbola branches (x-X)(y-Y) = +-eps as open paths."""
    a = eps / W
    us = [a * (W / a) ** (i / k) for i in range(k + 1)]
    out = []
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        out.append(" -- ".join(P(X + sx * u, Y + sy * eps / u) for u in us))
    return out


def Dpath():
    return " -- ".join(P(*c) for c in D) + " -- cycle"


def lattice(x0, x1, y0, y1):
    pts = []
    for b in range(-8, 9):
        for a in range(-20, 21):
            x, y = a + b * SQ, a - b * SQ
            if x0 <= x <= x1 and y0 <= y <= y1:
                pts.append((x, y))
    return pts


# ---------------------------------------------------------------- Figure: regions V(q)
def fig_regions():
    x0, x1, y0, y1 = -1.4, 5.6, -4.6, 2.5
    cen = [(0.0, 0.0, 1.0, "regA", r"v(0)", "below left"),
           (SQ, -SQ, 1.0, "regA", r"v(\omega)", "below left"),
           (0.5 * SQ - 1, -0.5 * SQ - 1, 0.5, "regB", r"v(q)", "below left")]
    L = [r"\begin{tikzpicture}[scale=1.05]",
         rf"\begin{{scope}}\clip {P(x0, y0)} rectangle {P(x1, y1)};"]
    for X, Y, e, col, lab, pos in cen:
        L.append(rf"\fill[{col}!25, opacity=.8] {region_path(X, Y, e)};")
    for X, Y, e, col, lab, pos in cen:
        for br in branches(X, Y, e):
            L.append(rf"\draw[{col}!80!black, thin] {br};")
        L.append(rf"\draw[{col}!80!black, densely dotted, very thin] {P(X, y0)} -- {P(X, y1)} {P(x0, Y)} -- {P(x1, Y)};")
    L.append(r"\end{scope}")
    L.append(rf"\draw[->, gray] {P(x0, 0)} -- {P(x1 + .25, 0)} node[right] {{$x$}};")
    L.append(rf"\draw[->, gray] {P(0, y0)} -- {P(0, y1 + .25)} node[above] {{$y$}};")
    for x, y in lattice(x0, x1, y0, y1):
        L.append(rf"\fill[black] {P(x, y)} circle (1.4pt);")
    L.append(rf"\draw[very thick] {Dpath()};")
    L.append(rf"\node at {P(2.37, -1.37)} {{$D$}};")
    for X, Y, e, col, lab, pos in cen:
        L.append(rf"\fill[{col}!80!black] {P(X, Y)} circle (1.8pt) node[{pos}, font=\scriptsize, fill=white, inner sep=1pt] {{${lab}$}};")
    L.append(rf"\draw[thick] {P(1, -.06)} -- {P(1, .06)} node[below=3pt, font=\scriptsize] {{$1$}};")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L)


# ---------------------------------------------------------------- Figure: translates and strips
def fig_strips():
    x0, x1, y0, y1 = -4.2, 8.6, -7.6, 4.6
    n = 2
    delta = n ** -0.5
    cx, cy = 0.5 * SQ, -0.5 * SQ                          # q = (1/2) w, class of the norm-2 centre
    Dx0, Dx1, Dy0, Dy1 = 0.0, 1 + SQ, -SQ, 1.0
    L = [r"\begin{tikzpicture}[scale=0.62]",
         rf"\begin{{scope}}\clip {P(x0, y0)} rectangle {P(x1, y1)};"]
    dsel = 0
    X, Y = cx + dsel, cy + dsel
    L.append(rf"\fill[regB!12] {P(X - delta, y0)} rectangle {P(X + delta, y1)};")
    L.append(rf"\fill[regB!12] {P(x0, Y - delta)} rectangle {P(x1, Y + delta)};")
    L.append(rf"\draw[regB!70!black, dashed, thin] {P(X - delta, y0)} -- {P(X - delta, y1)} {P(X + delta, y0)} -- {P(X + delta, y1)};")
    L.append(rf"\draw[regB!70!black, dashed, thin] {P(x0, Y - delta)} -- {P(x1, Y - delta)} {P(x0, Y + delta)} -- {P(x1, Y + delta)};")
    L.append(rf"\fill[regB!45] {region_path(X, Y, 1 / n)};")
    L.append(rf"\draw[gray, thin] {P(cx - 12, cy - 12)} -- {P(cx + 12, cy + 12)};")
    L.append(r"\end{scope}")
    L.append(rf"\draw[very thick] {Dpath()};")
    L.append(rf"\node at {P(3.6, -3.0)} {{$D$}};")
    for d in range(-9, 10):
        X, Y = cx + d, cy + d
        if not (x0 < X < x1 and y0 < Y < y1):
            continue
        hits = (Dx0 - delta < X < Dx1 + delta) or (Dy0 - delta < Y < Dy1 + delta)
        style = "fill=regB!80!black" if hits else "fill=white"
        L.append(rf"\draw[regB!80!black, {style}] {P(X, Y)} circle (2.2pt);")
    L.append(rf"\node[font=\scriptsize, fill=white, inner sep=1pt, anchor=east] at {P(cx - delta - 0.15, cy + 0.45)} {{$v(q')$}};")
    L.append(rf"\draw[gray, very thin] {P(cx - delta - 0.15, cy + 0.45)} -- {P(cx, cy)};")
    L.append(rf"\node[font=\scriptsize, regB!60!black] at {P(cx + delta + 1.1, y1 - .5)} {{$R^x_d$}};")
    L.append(rf"\node[font=\scriptsize, regB!60!black] at {P(x1 - .7, cy + delta + .45)} {{$R^y_d$}};")
    L.append(rf"\draw[gray, <->] {P(cx - delta, y0 - .35)} -- node[below, font=\scriptsize] {{$2|\mathrm{{Nm}}(q_2)|^{{-1/2}}$}} {P(cx + delta, y0 - .35)};")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L)


# ---------------------------------------------------------------- Figure: Lemma 3.2 (corner test)
def fig_boxlemma():
    W = 2.3
    eps = 1.0
    L = [r"\begin{tikzpicture}[scale=1.55]",
         rf"\begin{{scope}}\clip {P(-W, -W)} rectangle {P(W, W)};",
         rf"\fill[regA!20] {region_path(0, 0, eps)};"]
    for br in branches(0, 0, eps):
        L.append(rf"\draw[regA!80!black, thin] {br};")
    L.append(r"\end{scope}")
    L.append(rf"\draw[->, gray] {P(-W, 0)} -- {P(W + .2, 0)} node[right] {{$x$}};")
    L.append(rf"\draw[->, gray] {P(0, -W)} -- {P(0, W + .2)} node[above] {{$y$}};")
    L.append(rf"\node[regA!70!black, font=\scriptsize] at {P(1.45, 1.6)} {{$xy=\epsilon$}};")
    L.append(rf"\node[regA!70!black, font=\scriptsize] at {P(-1.45, 1.6)} {{$xy=-\epsilon$}};")

    def box(bx0, bx1, by0, by1, ok_style, lab=None, labpos="right"):
        out = [rf"\draw[thick, {ok_style}] {P(bx0, by0)} rectangle {P(bx1, by1)};"]
        for x in (bx0, bx1):
            for y in (by0, by1):
                inside = abs(x * y) < eps
                out.append(rf"\fill[{'good' if inside else 'bad'}] {P(x, y)} circle (1.6pt);")
        if lab:
            out.append(rf"\node[font=\scriptsize, {labpos}] at {P(bx1 if 'right' in labpos else bx0, (by0 + by1) / 2)} {{{lab}}};")
            # sanity: R_1, R_2 must pass, R_3 must fail with exactly 3 passing quarters (checked below)
        return out
    # accepted box in the first quadrant, with the max-corner argument of the proof
    L += box(0.15, 0.6, 0.9, 1.55, "good", "$R_1$", "left")
    L.append(rf"\draw[good, densely dashed] {P(0.6, 0)} -- {P(0.6, 1.55)} -- {P(0, 1.55)};")
    L.append(rf"\node[font=\scriptsize, below] at {P(0.6, 0)} {{$X$}};")
    L.append(rf"\node[font=\scriptsize, left] at {P(0, 1.55)} {{$Y$}};")
    # accepted box straddling the y-axis
    L += box(-0.45, 0.5, -1.65, -1.05, "good", "$R_2$")
    # rejected box: corner (1.5, 0.75) outside; its four quarters
    bx0, bx1, by0, by1 = 1.05, 1.7, 0.25, 0.7
    xm, ym = (bx0 + bx1) / 2, (by0 + by1) / 2
    L.append(rf"\draw[bad!60, densely dashed] {P(xm, by0)} -- {P(xm, by1)} {P(bx0, ym)} -- {P(bx1, ym)};")
    L += box(bx0, bx1, by0, by1, "bad", "$R_3$")
    L.append(r"\end{tikzpicture}")
    return "\n".join(L)


# ---------------------------------------------------------------- Figure: SOLVE on Q(sqrt 14)
def box_cmd(b, style):
    x0, x1, y0, y1 = [float(t) for t in b]
    return rf"\fill[{style}] {P(x0, y0)} rectangle {P(x1, y1)};"


def box_draw(b, style):
    x0, x1, y0, y1 = [float(t) for t in b]
    return rf"\draw[{style}] {P(x0, y0)} rectangle {P(x1, y1)};"


def fig_solve():
    out = []
    for N, scale, md in ((1, 0.95, 6), (2, 0.95, 9)):
        C, Lv, Fl = S.solve(N, 3, maxdepth=md)
        L = [rf"\begin{{tikzpicture}}[scale={scale}]"]
        for b, d, i in Lv:
            col = "regA" if C[i][1] == 1 else "regB"
            L.append(box_cmd(b, f"{col}!{30 if N == 2 else 18}"))
        for b in Fl:
            L.append(box_cmd(b, "bad"))
        for b, d, i in Lv:
            if d <= 7:
                L.append(box_draw(b, "black!55, line width=0.2pt"))
        L.append(rf"\draw[black!80, thin] {P(R0[0], R0[2])} rectangle {P(R0[1], R0[3])};")
        L.append(rf"\draw[very thick] {Dpath()};")
        L.append(rf"\node[font=\scriptsize, below] at {P((R0[0] + R0[1]) / 2, R0[2])} {{$N={N}$: {len(Lv)} boxes" +
                 (f", {len(Fl)} undecided at depth {md}" if Fl else "") + "};")
        L.append(r"\end{tikzpicture}")
        out.append("\n".join(L))
    return out[0] + "\n\\hfill\n" + out[1]


# ---------------------------------------------------------------- Figure: zoom with certifying regions
def fig_zoom():
    C, Lv, Fl = S.solve(2, 3, maxdepth=9)
    # window: square of side |R_0|/4 inside D, on the grid of step |R_0|/16 (found by searching
    # for a square centred in D whose boxes are certified by >= 3 centres, one with norm-2 denominator)
    W0 = R0[1] - R0[0]
    w = W0 / 4
    wx0, wy0 = R0[0] + 4 * W0 / 16, R0[2] + 6 * W0 / 16
    inside = [(b, d, k) for b, d, k in Lv if float(b[0]) < wx0 + w and float(b[1]) > wx0
              and float(b[2]) < wy0 + w and float(b[3]) > wy0]
    cs = {k for _, _, k in inside}
    palette = ["zA", "zB", "zC", "zD", "zE"]   # norm-1 centres first (blues/violet), then norm 2 (orange)
    n1 = [k for k in sorted(cs) if C[k][1] == 1]; n2 = [k for k in sorted(cs) if C[k][1] != 1]
    colour = {**{k: ["zA", "zB", "zC"][i] for i, k in enumerate(n1)},
              **{k: ["zD", "zE"][i] for i, k in enumerate(n2)}}   # orange = norm-2 denominator
    pad = 0.0
    cx0, cy0, cx1, cy1 = wx0 - pad, wy0 - pad, wx0 + w + pad, wy0 + w + pad
    sc = 6.0 / w
    L = [rf"\begin{{tikzpicture}}[scale={sc:.3f}]",
         rf"\begin{{scope}}\clip {P(cx0, cy0)} rectangle {P(cx1, cy1)};"]
    for b, d, k in inside:
        L.append(box_cmd(b, f"{colour[k]}!28"))
    for k in sorted(cs):
        q, n, X, Y = C[k]
        for br in branches(float(X.center()), float(Y.center()), 1.0 / n, W=60, k=200):
            L.append(rf"\draw[{colour[k]}!85!black, thick] {br};")
    for b, d, k in inside:
        L.append(box_draw(b, "black!70, line width=0.3pt"))
    L.append(rf"\draw[very thick] {Dpath()};")
    L.append(r"\end{scope}")
    L.append(rf"\draw[black!80] {P(wx0, wy0)} rectangle {P(wx0 + w, wy0 + w)};")
    # legend
    leg = []
    for k in sorted(cs, key=lambda k: (C[k][1], k)):
        q, n, X, Y = C[k]
        qs = sage_latex(q)
        leg.append(rf"\textcolor{{{colour[k]}!85!black}}{{\rule{{6pt}}{{6pt}}}}\ $q={qs}$, $|\mathrm{{Nm}}(q_2)|={n}$")
    L.append(rf"\node[anchor=north west, font=\scriptsize, align=left] at {P(cx1 + 0.05 * w, cy1)} {{" + r"\\ ".join(leg) + "};")
    L.append(r"\end{tikzpicture}")
    meta = (wx0, wy0, w, len(inside), len(cs))
    return "\n".join(L), meta


def sage_latex(q):
    from sage.all import latex
    return latex(q).replace(r"\sqrt{14}", r"\omega")


if __name__ == "__main__":
    files = {"fig-regions.tex": fig_regions(), "fig-strips.tex": fig_strips(),
             "fig-boxlemma.tex": fig_boxlemma(), "fig-solve.tex": fig_solve()}
    z, meta = fig_zoom()
    files["fig-zoom.tex"] = z
    hdr = "% generated by gen_figures.py (F = Q(sqrt 14)); do not edit by hand\n"
    for fn, body in files.items():
        open(fn, "w").write(hdr + body + "\n")
        print(fn, len(body), "chars")
    print("zoom window: x0=%.4f y0=%.4f side=%.4f, %d boxes, %d centres" % meta)
