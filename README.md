# cubic_twostage

Certified computation of **2-stage Euclideanity and continued fractions in complex cubic fields**
(signature (1,1), class number one), generalizing the algorithm of Guitart–Masdeu for real
quadratic fields ([arXiv:1106.0856](https://arxiv.org/abs/1106.0856)).

Companion code and data of the paper *Two-stage Euclidean algorithms and continued fractions in
complex cubic fields* (draft, `writeup/cubic2stage.pdf`). Main results:

* All **550** complex cubic fields of class number one with |d| < 5000 are 2-stage Euclidean.
  Each is proved by a certificate: a finite list of (dyadic box, centre) pairs covering a
  fundamental domain, checked with 128-bit interval arithmetic.
* A number field with infinite unit group is 2-stage Euclidean **iff** finitely many regions
  V(q) cover a fundamental domain (proved in the paper, using a theorem of Berend).
* An exact, finite test (via the unit action) for points that show a field is not
  norm-Euclidean, and for lower bounds of the *smooth level* N_min (the largest norm of the
  denominators needed). N_min is determined exactly for 166 fields by our own computations.
* Given a certificate, every element of the field is expanded as a continued fraction with
  integral partial quotients.

## Installation

You need Python with SageMath (≥ 10) and NumPy. Either a Sage installation or

    pip install -r requirements.txt        # passagemath-standard, numpy, contourpy

The code was developed with Sage 10.9. Use the Python interpreter that provides Sage, and **run
every script from the repository root** (paths such as `data/` are relative).

## Quick start (about a minute in total)

**1. Check the sample certificates.** `samples/certificates/` has coverings for seven fields
(d = −23, −199, −327, −351, −419, −436, −815):

    python3 verify_all.py samples/certificates

This re-checks, independently of the search: (i) the boxes lie in [0,1)³, are distinct,
non-nested and have total volume exactly 1; (ii) every centre r/α has |Nm α| = n and r ≡ ±ε^k
(mod α); (iii) every (box, centre) inequality holds in interval arithmetic; and it computes
continued fractions of random elements with the certificate and checks them exactly.

**2. Continued fractions** for d = −327 (K = Q(t), t³ − t² − 2t − 3 = 0):

    python3 examples/continued_fraction.py

expands (2+3t+5t²)/(7−t) as [t²+t, 1, t²−3t, 1, −t²+t, t].

**3. Exact non-Euclideanity witness** for d = −327 (the point x₀ = 2/33 + 20/33 t + 5/11 t²
is at norm distance 101/99 > 1 from the ring of integers):

    python3 examples/witness.py

**4. Run the whole pipeline on a short list of fields.** `samples/fields.txt` has six
defining polynomials (one per line):

    mkdir -p work data/certificates_k
    python3 batch4.py samples/fields.txt work/results.jsonl 3     # search + certify, 3 workers
    python3 verify_all.py data/certificates_k                     # independent check
    python3 make_csv.py work/results.csv work/results.jsonl       # table, with literature status
    python3 compare_lit.py work/results.jsonl                     # agreement with Cavallar–Lemmermeyer
    python3 smooth_level.py work/smooth.jsonl work/results.jsonl --mmax 12 --workers 3
    python3 analyze_smooth.py work/results.jsonl work/smooth.jsonl work/summary.csv

For each field `batch4.py` tries a covering with N = 1 (norm-Euclidean), searches an exact
witness that N = 1 is impossible, and then raises N = 2, 3, … until a covering is found. Its
output record has the covering level `N` (an upper bound for N_min), the witness if any, and
the path of the certificate (`data/certificates_k/cert_<|d|>_<a2>_<a1>_<a0>.pkl`).

## What is in the repository

| Path | Contents |
|---|---|
| `twostage.py` | Core: `TwoStage(poly)`, Minkowski embedding, centres, floating-point covering search, 128-bit interval certification, continued fractions |
| `witness_orbit.py` | Exact witness and level-witness tests via unit invariance (fast search; its translate set is computed in floating point) |
| `certify_lower.py` | **Rigorous** re-check of every witness / level witness with a provably complete translate set, interval arithmetic, and a second exact method for small denominators |
| `verify_all.py`, `check_unit_residues.py` | Independent verification of covering certificates |
| `batch4.py`, `resolve_hard.py`, `tighten.py` | Pipeline: search, harder N = 1 attempts, lowering N |
| `smooth_level.py`, `analyze_smooth.py` | Lower bounds for N_min and the table of exact values vs splitting of small primes |
| `merge_results.py`, `make_csv.py`, `compare_lit.py` | Merge runs, tables, comparison with the literature |
| `enum_fields.py`, `certify_h.py` | Field lists (PARI `nflist`) and certified class numbers (`bnfcertify`) |
| `verify_bbt.py` | Re-check, with our test, the non-norm-Euclideanity certificates of Bagger–Booker–Trudgian |
| `diag_cover.py` | Diagnose where and why a covering fails |
| `batch3.py`, `witness_fast.py`, `witness2.py`, `witness_search.py`, `rewit2.py`, `crosscheck.py`, `resolve_open.py` | First-generation pipeline; `witness_fast.py` (enumerates ideal generators) is an independent cross-check of `witness_orbit.py` |
| `legacy/` | Earlier exploratory scripts (not maintained) |
| `data/` | Field lists, per-field results, smooth-level tables, re-check outputs (see `data/README.md`) |
| `samples/` | Sample certificates and field list for the quick start |
| `examples/` | Small scripts used above |
| `writeup/` | LaTeX source of the paper, plot data, figure generator `gen_regions.py` |
| `paper/figures/` | Generator of the TikZ figures for the quadratic case (Q(√14)) |
| `docs/strategy_outline.md` | Roadmap |

## Certificate format

A certificate is a pickle `(poly, [(m, depth, class, g), …])`. The box is
2^−depth·(m + [0,1]³) in lattice coordinates (basis = Sage's `integral_basis()`); the centre is
`class[0] + g` (lattice coordinates of r/α modulo 1, plus an integer translate) with
`class = (coords, n, α, r)`, where `n = |Nm α|` is the norm of the denominator and the region
has radius 1/n. Unpickle with `import sage.all` first.

## The full computation (550 fields, |d| < 5000)

The covering certificates take **3.4 GB** and are not stored in this repository. The per-field
results (`data/results_final_v3.jsonl`, `data/results_k_5000.csv`) are. To regenerate:

    python3 enum_fields.py 5000                  # data/h1_5000.txt (550 fields)
    python3 certify_h.py 5000 8                  # certified class numbers
    CUBIC_MEM_GB=12 python3 batch4.py data/h1_5000.txt data/results_k_5000.jsonl 8   # resumes
    python3 resolve_hard.py data/results_k_5000.jsonl data/updates_k_5000.jsonl 4
    python3 smooth_level.py data/smooth.jsonl data/results_k_5000.jsonl data/updates_k_5000.jsonl --workers 8
    python3 tighten.py <merged results> data/smooth.jsonl <updates out> 8
    python3 verify_all.py data/certificates_k --shard 0/8      # and shards 1/8 … 7/8
    python3 certify_lower.py data/lower_bounds_certified.jsonl 6

The main `batch4.py` run took about 55 CPU-hours (timings in the records come from machines
with different loads and are only indicative). Environment variables: `CUBIC_MEM_GB`
(address-space cap per worker; very large unit groups need several GB), `CUBIC_TIMEOUT`
(seconds per field). Each runner sets one BLAS thread per worker; without that, parallel runs
oversubscribe the CPUs. For long runs, launch detached (`setsid nohup …` or tmux).

`results_final_v3.jsonl` is the current record file. `results_final_v2.jsonl` still contains
two witnesses (d = −4872, −4952) that `certify_lower.py` refutes; they came from an earlier
search with an incomplete translate set. `certify_lower.py` reads v2 on purpose.

### Bagger–Booker–Trudgian certificates

`verify_bbt.py` needs the certificate file of
[arbooker/complex-cubic](https://github.com/arbooker/complex-cubic) (not redistributed here):

    git clone https://github.com/arbooker/complex-cubic
    mkdir -p data/bbt && cp complex-cubic/results/certificates.txt data/bbt/
    sha256sum data/bbt/certificates.txt   # 67e9f2cc4c9c83bff7bc66f97770fc11b5c2a0b878f70bb820a6c64a679a328d
    python3 verify_bbt.py data/bbt_verified.jsonl 6

## Regenerating the paper's figures

    python3 writeup/gen_regions.py          # fig-horn.tex, fig-slices.tex, fig-zoom3.tex (needs contourpy)
    cd writeup && pdflatex cubic2stage.tex && pdflatex cubic2stage.tex

`gen_regions.py` uses the d = −327 certificate from `samples/` if the full set is absent.
The quadratic-case figures (`writeup/figures-quad/`) come from `paper/figures/gen_figures.py`.

## Status and caveats

* The paper is a draft. The repository link in it still needs to point here, and the full
  certificate set needs a permanent archive (e.g. Zenodo).
* Covering certificates are proofs (given the correctness of Sage/PARI for integral bases, and
  of the interval enclosures of the embeddings). The floating-point search itself is not part of
  the proof.
* Unit groups: `bnfcertify` certifies class numbers and fundamental units
  (`certify_lower.py` checks the unit against the certified regulator).
* Licences: see the last section.

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

The remaining documentation (`README.md`, `docs/`) is covered by the GPL like the code.
