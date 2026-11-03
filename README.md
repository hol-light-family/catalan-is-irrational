# HOL Light Formalization of Irrationality of Catalan's Constant

A formalization in [HOL Light](https://github.com/jrh13/hol-light), autoformalized and
translated into HOL Light with Claude Code using Claude Opus 5.5, of the main result of

> OpenAI, *Catalan's constant is irrational*, 2026-09-24
> ([Valency Hub](https://hub.valency.io/works/W_czyy5f3a);
> a copy of the paper is in [`ref/paper.pdf`](ref/paper.pdf)).

Catalan's constant is G = 1 − 1/3² + 1/5² − 1/7² + ⋯ = Σ_{j≥0} (−1)^j / (2j+1)².

## Main theorem

[`src/catalan_main.ml`](src/catalan_main.ml) proves:

```
CATALAN_CONSTANT_IRRATIONAL_HEADLINE :
 |- (exists G. ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)) /\
    (forall G. ((\j. --(&1) pow j / &(2 * j + 1) pow 2) real_sums G) (from 0)
               ==> ~(exists m n. integer m /\ integer n /\ ~(n = &0) /\ G = m / n))
```

That is, the series converges, and its sum is not a quotient of two integers. The statement
uses only HOL Light's own notions: `real_sums` (convergence of partial sums, from
`Multivariate/realanalysis.ml`), `integer` (core HOL Light) and `&k` (a natural number as a
real).

| theorem | statement |
|---|---|
| `CATALAN_CONSTANT_IRRATIONAL_HEADLINE` | as above, with everything unfolded |
| `CATALAN_CONSTANT_IRRATIONAL` | `\|- ~(rational catalan_constant)` |
| `CATALAN_IRRATIONAL` | `\|- CATALAN_IRRATIONAL_STATEMENT` |

## What has to be trusted

- **HOL Light's kernel and its three standard axioms** (`ETA_AX`, `SELECT_AX`,
  `INFINITY_AX`). `make.ml` ends with HOL Light's `check_axioms ()`, which fails if any
  other axiom is present. No file uses `CHEAT_TAC` or `new_axiom`.
- **The statement.** It is fully visible in `src/catalan_main.ml` (above).

## How the proof is organized

The proof follows the paper. For each N it builds a determinant Δ_N of size 48N whose
entries are double integrals of explicit polynomial rows. Assuming G is rational, it bounds
the normalized logarithm L_N = log|Δ_N| / (48N)² − (log 2)/2 from both sides, and the two
bounds are incompatible. [`src/catalan_components.ml`](src/catalan_components.ml) states four
components and proves `CATALAN_FROM_COMPONENTS`: the four together imply the main theorem.

| component | paper | content | files | size |
|---|---|---|---|---|
| `CAT_RATIONALITY` | Prop. 2.1 | with z = G, an explicit rational formula equals the integral determinant; moment evaluations, the starting values 4G and π²/4, the ζ(2) cancellation | `src/catalan_rat_*.ml` | 6 files, 2.8k lines |
| `CAT_FINITE_PLACE` | Props. 2.2, 3.4 | for every rational z, L_N > −2.29084 whenever the rational determinant is nonzero: 2-adic and odd-prime valuation bounds, combined through the prime number theorem | `src/catalan_fin_*.ml` | 22 files, 8.2k lines |
| `CAT_NONVANISHING` | Prop. 4.1 | for every rational z, the rational determinant is nonzero at every large prime N = p: reduction mod p (Frobenius, palindromic bases, block determinant) and a fixed mod-101 certificate | `src/catalan_nv_*.ml` | 24 files, 8.4k lines |
| `CAT_REAL_PLACE` | Props. 5.2–7.1 | L_N < −2.2909 for large N with Δ_N ≠ 0: integral representation, interpolation and Hadamard estimates, energy bound, exact certificates for two one-variable suprema | `src/catalan_rp_*.ml` | 57 files, 14.2k lines |

Since −2.2909 < −2.29084, a large prime p with Δ_p ≠ 0 gives the contradiction.

[`PROOF_STRUCTURE.md`](PROOF_STRUCTURE.md) describes the structure of the proof in more detail,
and how it differs from the paper and from the Lean formalization.

All numerical constants are proved inside HOL Light by exact rational arithmetic. External
programs only propose certificate data that HOL then checks: Python scripts found the root
brackets used in the real-place certificate, and OCaml computes the mod-101 inverse matrices
of the nonvanishing certificate at load time.

## Directory structure

```
make.ml                  loads the development, prints the headline theorems, checks axioms
README.md                this file
PROOF_STRUCTURE.md       structure of the proof and comparison with the paper and Lean
ref/                     the paper (paper.pdf)
src/
  catalan_statement.ml   the statement: Catalan's constant and CATALAN_IRRATIONAL_STATEMENT
  catalan_defs.ml        definitions used inside the proof (rows, moments, determinants)
  catalan_components.ml  the four components and their assembly, CATALAN_FROM_COMPONENTS
  catalan_main.ml        the headline theorems
  catalan_rat_*.ml       component CAT_RATIONALITY
  catalan_fin_*.ml       component CAT_FINITE_PLACE
  catalan_nv_*.ml        component CAT_NONVANISHING
  catalan_rp_*.ml        component CAT_REAL_PLACE
tools/
  check_defs.py          independent check of the definitions against the paper's Table 1
  rp_cert/               scripts that generated the real-place certificate data
```

Each component has a final file `src/catalan_<prefix>_final.ml` that proves the component
theorem, for example `CAT_NONVANISHING_THM : |- CAT_NONVANISHING` in
`src/catalan_nv_final.ml`. All files of a component share its prefix, so the components can be
loaded together without name clashes.

- `src/catalan_defs.ml` follows the paper's notation for the Chebyshev rows, the moments, the
  determinant and its rational formula.
- `tools/check_defs.py` confirms that these definitions reproduce the paper's Table 1, the
  mod-101 Gaussian pivots, exactly.
- `tools/rp_cert/` holds the Python scripts that generated `src/catalan_rp_cert_data.ml` and
  `src/catalan_rp_cert_certdata.ml`. They are needed only to regenerate that data, not to check
  the proof.

## Building

The development uses [HOL Light](https://github.com/jrh13/hol-light), and was tested at commit
`31fe213`. It needs `100/pnt.ml` (and hence `Multivariate/cauchy.ml`) and
`Library/ring_det.ml` from HOL Light; `make.ml` loads them. Start HOL Light with its `hol.sh` in
the root of this repository (HOL Light's load path is the current directory first, then the HOL
Light directory), then:

```
loadt "make.ml";;
```

This loads the development, prints the headline theorems and runs `check_axioms ()`. To run it
non-interactively from the shell, in the root of this repository:

```
echo 'loadt "make.ml";;' | LINE_EDITOR=env /path/to/hol-light/hol.sh
```

On one core, the whole run takes about an hour (62 minutes in our test), including HOL Light's
prerequisites. Most of the development's own time goes to the exact arithmetic of the
real-place certificate (about 22 minutes) and to `Library/ring_det.ml`.

## Acknowledgements

The mathematics is from the paper above. Its Lean 4 formalization
(https://github.com/openai/math, `lean/OAI/NumberTheory/Catalan`) served as a guide to the
structure of the argument; this HOL Light development is independent of it.
