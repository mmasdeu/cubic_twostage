# Data

Licence: CC0 1.0 (`LICENSE`), as for `samples/`. `literature_cavallar_lemmermeyer.csv` only transcribes
the numerical results of Cavallar–Lemmermeyer's published table.

Everything here is small. The 550 covering certificates (3.4 GB) are **not** in the repository;
`samples/certificates/` has seven of them. See the top-level README for how to regenerate them.

## Field lists
| File | Contents |
|---|---|
| `h1_5000.txt` | defining polynomials of the 550 complex cubic fields of class number one with \|d\| < 5000 (`scripts/enum_fields.py 5000`); `h1_1500.txt`, `h1.txt`, `h1_1500_5000.txt` are subsets |
| `h_certified_5000.jsonl` | `bnfcertify` class numbers (`scripts/certify_h.py`): all 729 fields with \|d\| < 5000 certified, 550 with h = 1 |

## Results (one JSON record per field)
| File | Contents |
|---|---|
| `results_final_v3.jsonl` | **current** final record per field. Keys: `poly`, `disc`, `N` (covering level, an upper bound for N_min), `norm_euclid_cover` (N = 1 certificate), `witness`/`wit_m` (point x with min_g \|Nm(x−g)\| ≥ 1 and its denominator, or the bound searched; `wit_m = 0`: search skipped, unit too large), `n1_level`/`n1_note`, `K, L, W` (far-centre parameters of the certificate), `boxes`, `maxdepth`, `cert` (path of the certificate pickle), `t_*` (timings, mixed machines) |
| `results_final_v2.jsonl` | the same before two false witnesses (d = −4872, −4952) were removed. Kept because `scripts/certify_lower.py` reads it and reproduces the refutation |
| `results_final_5000.jsonl` | before the tightening pass (`scripts/tighten.py`) |
| `results_k_5000.jsonl`, `updates_k_5000.jsonl`, `antz9/*.jsonl` | raw batch / update / tightening outputs of the runs that were merged by `scripts/merge_results.py` |
| `results_k_5000.csv` | `results_final_v3.jsonl` as a table (`scripts/make_csv.py`), with the Cavallar–Lemmermeyer status and Euclidean minimum |
| `results_1500.*`, `results_1500_5000.jsonl`, `wit_*.jsonl` | first-generation pipeline (`legacy/batch3.py`), centres restricted to [−3,3]³: only 39 of the 58 norm-Euclidean fields get an N = 1 covering |

## Smooth level
| File | Contents |
|---|---|
| `antz9/smooth_level_v2.jsonl` | `scripts/smooth_level.py` output: level-(N−1) witnesses (lower bounds) and the consistency check at level N |
| `smooth_level_summary.csv` | `scripts/analyze_smooth.py`: per field N, whether N = N_min is proved and why, splitting of 2, 3, 5, 7, smallest ideal norms |
| `smooth_level_local.jsonl` | experiments with local centres |

## Rigorous re-checks
| File | Contents |
|---|---|
| `lower_bounds_certified.jsonl` | `scripts/certify_lower.py`: interval-arithmetic re-check of every witness and level witness: 271 ordinary witnesses and 99 level witnesses confirmed (`ok: true`), 2 refuted (`ok: false`, d = −4872, −4952) |
| `bbt_verified.jsonl`, `bbt_verified_retry.jsonl` | `scripts/verify_bbt.py`: our test applied to the non-norm-Euclideanity certificates of Bagger–Booker–Trudgian; `ok: null` means the unit is too large for our translate set |

## Literature
`literature_cavallar_lemmermeyer.csv`: table of Cavallar–Lemmermeyer (arXiv:1202.6019) for
\|d\| ≤ 1219 (status E/N/H and Euclidean minimum), parsed from the paper.

## Not included
`data/bbt/certificates.txt` (certificates of Bagger–Booker–Trudgian): download it, see README.
