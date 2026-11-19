# cubic_twostage

A Python/SageMath package that proves number fields to be **2-stage Euclidean** and computes
**continued fractions** in them. It covers real quadratic fields, complex cubic fields and
totally real cubic fields (and the norm-Euclidean imaginary quadratic fields).

A ring of integers O_K is 2-stage Euclidean if every pair α, β (β ≠ 0) has a decreasing
division chain of length at most two. Then every element of K has a finite continued fraction
with partial quotients in O_K. The package finds a finite covering of a fundamental domain of
O_K by the regions |Nm(x − [q₁, q₂])| < 1/|Nm(q₂)|, checks every piece with interval arithmetic
(so the covering is a proof), and uses it to expand elements as continued fractions. This
generalizes the algorithm of Guitart–Masdeu for real quadratic fields
([arXiv:1106.0856](https://arxiv.org/abs/1106.0856)) to arbitrary signature.

It is also the companion code of the paper *Two-stage Euclidean algorithms and continued
fractions in complex cubic fields* (draft, [`writeup/cubic2stage.pdf`](writeup/cubic2stage.pdf)):

* All **550** complex cubic fields of class number one with |d| < 5000 are 2-stage Euclidean,
  each with a certificate.
* A number field with infinite unit group is 2-stage Euclidean **iff** finitely many regions
  V(q) cover a fundamental domain (proved in the paper, using a theorem of Berend; a Lean
  formalization of this part is in [`CubicTwoStage/`](CubicTwoStage) and
  [`blueprint/`](blueprint)).
* For complex cubic fields: an exact, finite test (via the unit action) for points showing that
  a field is not norm-Euclidean, and lower bounds for the *smooth level* N_min (the largest
  norm of the denominators q₂ needed).

## Installation

You need SageMath (≥ 10). Into an existing Sage installation (use Sage's Python):

    git clone https://github.com/mmasdeu/cubic_twostage
    cd cubic_twostage
    sage -pip install .            # or: python3 -m pip install .   (the Python that has Sage)

Without a Sage installation, `pip` can bring Sage in as a Python package
([passagemath](https://github.com/passagemath/passagemath)):

    pip install ".[passagemath]"

Use `pip install -e .` for a development install. The extra `figures` installs `contourpy`
(only needed to regenerate the paper's figures). The package was developed with Sage 10.9 and
passagemath 10.8 on Python 3.13–3.14.

## Usage

```python
sage: from cubic_twostage import TwoStage, evaluate_cf
sage: S = TwoStage("x^3 - x^2 - 2*x - 3")   # complex cubic field, d = -327
sage: S.find_covering()                      # search + certification; returns the level N
3
sage: t = S.K.gen()
sage: x = (2 + 3*t + 5*t^2) / (7 - t)
sage: qs = S.continued_fraction(x); qs
[t^2 + t, 1, t^2 - 3*t, 1, -t^2 + t, t]
sage: evaluate_cf(qs) == x
True
```

`TwoStage` accepts a defining polynomial (the generator is then called `t`) or a number field.
`continued_fraction` works directly on field elements and caches the covering of each field:

```python
sage: from cubic_twostage import continued_fraction
sage: K.<a> = QuadraticField(14)
sage: continued_fraction((1 + a) / 7)
[0, 1, 1, 1, -a - 8, a + 4, -11*a + 40, 1]
sage: K.<b> = NumberField(x^3 - x^2 - 2*x + 1)      # totally real cubic, d = 49
sage: continued_fraction((1 + 2*b - b^2) / (5 + b^2))
[-1, 1, b^2 - 3*b - 5, 1, 2*b^2 - 3*b - 2, 1]
```

The partial quotients depend on the covering found; the value never does.

Certificates can be stored and verified independently of the search:

```python
sage: S.save_certificate("cert_327.pkl")
sage: S = TwoStage.from_certificate("cert_327.pkl")     # ready for continued fractions
sage: from cubic_twostage import verify_certificate
sage: verify_certificate(S, S.cert)
{'N': 3, 'boxes': 484, 'classes': 5}
```

`verify_certificate` checks that the boxes tile [0,1]ⁿ (distinct, non-nested, total volume
exactly 1); that every centre r/α has |Nm α| = n and r ≡ unit (mod α); that every
(box, centre) inequality holds in interval arithmetic; and it checks random continued
fractions exactly.

### Command line

    cubic-twostage cover "x^2 - 14" -o cert_14.pkl            # find, certify and save a covering
    cubic-twostage cf "x^2 - 14" "(3 + 5*t)/(2 - 7*t)"         # continued fraction
    cubic-twostage cf "x^2 - 14" "(3 + 5*t)/(2 - 7*t)" -c cert_14.pkl
    cubic-twostage verify samples/certificates                # verify every cert_*.pkl

(`python3 -m cubic_twostage …` does the same without the installed command.)

### Which fields

| Signature | Fields | Coverings and continued fractions | Witnesses, smooth-level bounds |
|---|---|---|---|
| (2, 0) | real quadratic | yes | — |
| (1, 1) | complex cubic | yes (the paper) | yes (`witness_orbit`, `certify_lower`) |
| (3, 0) | totally real cubic | yes (unit rank 2) | — |
| (0, 1) | imaginary quadratic | only the norm-Euclidean ones (d = −3, −4, −7, −8, −11) | — |

The field must have class number one: a 2-stage Euclidean ring is a principal ideal domain.
Under GRH every such field with infinite unit group is 2-stage Euclidean (Cooke–Weinberger),
so `find_covering` is expected to succeed. The code is written for any degree, but it is only
tested in degrees 2 and 3.

The covering search (`TwoStage.cover`) is in floating point. Its parameters `T, K, L, W,
maxdepth` say which centres are used (translates, unit images, slabs along the places) and how
deep boxes are subdivided. `find_covering` tries the levels N = 1, 2, … (ideal norms) with the
defaults of the paper's pipeline. A failure at a level does not prove anything; a covering at
level N proves N_min ≤ N. For hard fields see `cover_adaptive` and the pipeline in `scripts/`.

## Documentation and tests

The documentation is in `doc/` (Sphinx): `cd doc && make html`. The examples in the docstrings
are doctests:

    sage -t cubic_twostage            # or: python3 -m sage.doctest cubic_twostage

The GitHub workflows run the doctests and verify the sample certificates (`test.yml`), check
the formatting with black and isort (`lint.yml`), and build the manual (`doc.yml`; GitHub
Pages of this repository serve the Lean blueprint).

## Reproducing the paper

The scripts of the paper's computation are in `scripts/`. Run them **from the repository root**
(paths such as `data/` are relative), with the package installed.

**1. Check the sample certificates.** `samples/certificates/` has coverings for seven complex
cubic fields (d = −23, −199, −327, −351, −419, −436, −815):

    cubic-twostage verify samples/certificates

**2. Examples.** `examples/continued_fraction.py` expands (2+3t+5t²)/(7−t) in the field of
d = −327 with the stored certificate; `examples/witness.py` checks the exact
non-Euclideanity witness x₀ = 2/33 + 20/33 t + 5/11 t² (norm distance 101/99 > 1 from O_K);
`examples/fields.py` computes coverings for a real quadratic, a complex cubic and a totally
real cubic field.

**3. The pipeline on a short list of fields.** `samples/fields.txt` has six defining polynomials:

    mkdir -p work data/certificates_k
    python3 scripts/batch4.py samples/fields.txt work/results.jsonl 3     # search + certify, 3 workers
    cubic-twostage verify data/certificates_k                           # independent check
    python3 scripts/make_csv.py work/results.csv work/results.jsonl       # table, with literature status
    python3 scripts/compare_lit.py work/results.jsonl                     # agreement with Cavallar–Lemmermeyer
    python3 scripts/smooth_level.py work/smooth.jsonl work/results.jsonl --mmax 12 --workers 3
    python3 scripts/analyze_smooth.py work/results.jsonl work/smooth.jsonl work/summary.csv

For each field `batch4.py` tries a covering with N = 1 (norm-Euclidean), searches an exact
witness that N = 1 is impossible, and then raises N = 2, 3, … until a covering is found. Its
output record has the covering level `N` (an upper bound for N_min), the witness if any, and
the path of the certificate (`data/certificates_k/cert_<|d|>_<a2>_<a1>_<a0>.pkl`).

### The full computation (550 fields, |d| < 5000)

The covering certificates take **3.4 GB** and are not stored in this repository. The per-field
results (`data/results_final_v3.jsonl`, `data/results_k_5000.csv`) are. To regenerate:

    python3 scripts/enum_fields.py 5000                  # data/h1_5000.txt (550 fields)
    python3 scripts/certify_h.py 5000 8                  # certified class numbers
    CUBIC_MEM_GB=12 python3 scripts/batch4.py data/h1_5000.txt data/results_k_5000.jsonl 8   # resumes
    python3 scripts/resolve_hard.py data/results_k_5000.jsonl data/updates_k_5000.jsonl 4
    python3 scripts/smooth_level.py data/smooth.jsonl data/results_k_5000.jsonl data/updates_k_5000.jsonl --workers 8
    python3 scripts/tighten.py <merged results> data/smooth.jsonl <updates out> 8
    cubic-twostage verify data/certificates_k --shard 0/8      # and shards 1/8 … 7/8
    python3 scripts/certify_lower.py data/lower_bounds_certified.jsonl 6

The main `batch4.py` run took about 55 CPU-hours (timings in the records come from machines
with different loads and are only indicative). Environment variables: `CUBIC_MEM_GB`
(address-space cap per worker; very large unit groups need several GB), `CUBIC_TIMEOUT`
(seconds per field), `CUBIC_MAX_D` (largest translate set in `certify_lower`). Each runner sets
one BLAS thread per worker; without that, parallel runs oversubscribe the CPUs. For long runs,
launch detached (`setsid nohup …` or tmux).

`results_final_v3.jsonl` is the current record file. `results_final_v2.jsonl` still contains
two witnesses (d = −4872, −4952) that `certify_lower.py` refutes; they came from an earlier
search with an incomplete translate set. `scripts/certify_lower.py` reads v2 on purpose.

### Bagger–Booker–Trudgian certificates

`scripts/verify_bbt.py` needs the certificate file of
[arbooker/complex-cubic](https://github.com/arbooker/complex-cubic) (not redistributed here):

    git clone https://github.com/arbooker/complex-cubic
    mkdir -p data/bbt && cp complex-cubic/results/certificates.txt data/bbt/
    sha256sum data/bbt/certificates.txt   # 67e9f2cc4c9c83bff7bc66f97770fc11b5c2a0b878f70bb820a6c64a679a328d
    python3 scripts/verify_bbt.py data/bbt_verified.jsonl 6

### Regenerating the paper's figures

    python3 writeup/gen_regions.py          # fig-horn.tex, fig-slices.tex, fig-zoom3.tex (needs contourpy)
    cd writeup && pdflatex cubic2stage.tex && pdflatex cubic2stage.tex

`gen_regions.py` uses the d = −327 certificate from `samples/` if the full set is absent.
The quadratic-case figures (`writeup/figures-quad/`) come from `paper/figures/gen_figures.py`.

## Certificate format

A certificate is a pickle `(poly, [(m, depth, class, g), …])` for a field of degree n. The box
is 2^−depth·(m + [0,1]ⁿ) in lattice coordinates (basis = Sage's `integral_basis()`); the centre
is `class[0] + g` (lattice coordinates of r/α modulo 1, plus an integer translate) with
`class = (coords, n_c, α, r)`, where `n_c = |Nm α|` is the norm of the denominator and the
region has radius 1/n_c. Unpickle with `import sage.all` first (or use
`TwoStage.from_certificate`).

## Repository layout

| Path | Contents |
|---|---|
| `cubic_twostage/` | The package. `twostage.py`: `TwoStage` (Minkowski embedding, centres, covering search, interval certification, continued fractions); `verify.py`: certificate verification; `witness_orbit.py`: exact witness and level-witness tests via unit invariance (complex cubic); `certify_lower.py`: rigorous re-check of witnesses with a provably complete translate set (complex cubic); `witness_fast.py`: witnesses via ideal generators (independent check); `__main__.py`: command line |
| `scripts/` | The paper's pipeline: `batch4.py` (search + certify), `resolve_hard.py`, `tighten.py` (lower N), `smooth_level.py`, `analyze_smooth.py`, `merge_results.py`, `make_csv.py`, `compare_lit.py`, `enum_fields.py`, `certify_h.py` (certified class numbers), `certify_lower.py`, `verify_bbt.py`, `diag_cover.py`, `check_unit_residues.py` |
| `examples/` | Small scripts (see above) |
| `samples/` | Sample certificates and field list |
| `data/` | Field lists, per-field results, smooth-level tables, re-check outputs (see `data/README.md`) |
| `doc/` | Sphinx documentation, change log fragments (`doc/news/`), roadmap (`doc/strategy_outline.md`) |
| `writeup/` | LaTeX source of the paper, plot data, figure generator `gen_regions.py` |
| `paper/figures/` | Generator of the TikZ figures for the quadratic case (Q(√14)) |
| `CubicTwoStage/`, `CubicTwoStage.lean`, `blueprint/`, `BEREND_BLUEPRINT.md` | Lean formalization and blueprint of the Berend argument |
| `legacy/` | First-generation pipeline and earlier exploratory scripts (not maintained; they import the old module layout) |

Releases follow darmonpoints: version in `pyproject.toml`, `doc/conf.py` and
`cubic_twostage/__init__.py`, change log in `ChangeLog` with fragments in `doc/news/`,
released with `rever` (`rever.xsh`).

## Status and caveats

* The paper is a draft; the full certificate set needs a permanent archive (e.g. Zenodo).
* Covering certificates are proofs (given the correctness of Sage/PARI for integral bases, ideal
  enumeration and unit groups, and of the interval enclosures of the embeddings). The
  floating-point search is not part of the proof. A certificate needs only that the r are unit
  residues, not that the units are fundamental.
* `certify_h.py` certifies class numbers and fundamental units with PARI's `bnfcertify`
  (`certify_lower.py` checks the unit against the certified regulator); `TwoStage` itself uses
  `proof=False` for the class number check.

## Literature

Cooke, *A weakening of the Euclidean property…* (1976); Cooke–Weinberger (1975); Guitart–Masdeu,
*Continued fractions in 2-stage Euclidean quadratic fields*; Cavallar–Lemmermeyer, *The Euclidean
algorithm in cubic number fields* (arXiv:1202.6019); Bagger–Booker–Trudgian, *Determining
norm-Euclidean complex cubic fields* (arXiv:2610.38073); Berend, *Multi-invariant sets on tori*.
Full references are in the paper.

## Licence

| What | Licence | File |
|---|---|---|
| **Code**: every `.py` file, including the figure generators `writeup/gen_regions.py` and `paper/figures/*.py` | [GNU GPL v3 or later](https://www.gnu.org/licenses/gpl-3.0.html) (`GPL-3.0-or-later`) | `LICENSE` |
| **Paper**: text, figures and plot data in `writeup/` (the `.tex`, `.pdf`, `.csv` files) | [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) | `writeup/LICENSE` |
| **Figures** for the quadratic case: the generated TikZ files `paper/figures/fig-*.tex` | [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) | `paper/figures/LICENSE-figures` |
| **Data**: everything in `data/` and `samples/` | [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/) | `data/LICENSE`, `samples/LICENSE` |

The remaining documentation (`README.md`, `doc/`) is covered by the GPL like the code.
