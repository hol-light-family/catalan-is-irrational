# Structure of the proof

> **Disclaimer.** This document was written by Claude Code (Claude Opus 5.5). It may contain
> errors or incorrect explanations. The HOL Light sources are the authoritative description of
> what is proved and how.

This note describes how the HOL Light proof is organized, and where it departs from the paper
(*Catalan's constant is irrational*, OpenAI, 2026-09-24, [`ref/paper.pdf`](ref/paper.pdf)) and
from its Lean 4 formalization (https://github.com/openai/math,
`lean/OAI/NumberTheory/Catalan`). Section and equation numbers refer to the paper.

## The argument in one paragraph

For each N ≥ 1 the paper defines a determinant Δ_N of size n = 48N (Equation (7)). Its entries
combine two double integrals of explicit polynomial rows built from Chebyshev polynomials. Each
entry is a rational combination of 1, G and ζ(2). The rows are chosen so that ζ(2) cancels, so
if G is rational then Δ_N is rational. Write L_N = log|Δ_N| / n² − (log 2)/2. Bounds on the
prime-power denominators of Δ_N give L_N > −2.29084 whenever Δ_N ≠ 0. A Frobenius argument shows
Δ_p ≠ 0 for every large prime p. An analytic estimate of the integrals gives L_N < −2.2909 for
all large N. These cannot all hold, so G is irrational.

## Top level

The HOL Light proof has the same top level as the Lean one. Both separate a rational formula for
the determinant from the integral determinant.

- `src/catalan_statement.ml` defines `catalan_constant` as the sum of the series and states
  `CATALAN_IRRATIONAL_STATEMENT`.
- `src/catalan_defs.ml` defines the rows, the integral determinant `cat_det N`, and the rational
  formula `cat_detq z N`, in which an arbitrary real z stands in for G. These definitions match
  the Lean ones one for one. `tools/check_defs.py` confirms them against the paper's Table 1.
- `src/catalan_components.ml` states four components and proves `CATALAN_FROM_COMPONENTS`, which
  is the paper's Section 8:

| component | statement, informally | paper |
|---|---|---|
| `CAT_RATIONALITY` | `cat_detq G N = cat_det N` for N ≥ 1 | Prop. 2.1 |
| `CAT_FINITE_PLACE` | z rational, `cat_detq z N ≠ 0`, N large ⟹ L_N > −2.29084 | Props. 2.2, 3.4 |
| `CAT_NONVANISHING` | z rational, p a large prime ⟹ `cat_detq z p ≠ 0` | Prop. 4.1 |
| `CAT_REAL_PLACE` | `cat_det N ≠ 0`, N large ⟹ L_N < −2.2909 | Props. 5.2–7.1 |

The two arithmetic components hold for every rational z and involve no integrals. Only
rationality and the real-place bound involve analysis, and only rationality mentions G.

- `src/catalan_main.ml` combines the four components. It proves the headline theorem
  `CATALAN_CONSTANT_IRRATIONAL_HEADLINE`, which is stated with every definition unfolded.

## The components

### Rationality (`src/catalan_rat_*.ml`, Proposition 2.1)

This component expands both moment functionals over the polynomial rows and filtered columns. It
proves Equation (17) for the monomial moments, then the ζ(2) cancellation (Equation (5)), and
then entrywise equality of the two matrices.

- **No ζ(2) and no π.** The proof never evaluates ζ(2) as π²/6, and HOL Light's library has no
  Basel identity. Instead it names the value Z(0,0) of the second double integral. It only uses
  the relation K₁⁺ = M(0,1) = (3/2)·Z(0,0), which it proves by the substitutions x = 2w/(1+w²)
  and v = w². The paper evaluates K₁⁺ = π²/4 through the arcsin² series or a Fourier series.
- **The start K₀ = 4G.** This uses the substitution x = (1−y²)/(1+y²) and a dominated-convergence
  expansion against −log y / (1+y²). The same expansion proves that the series for G converges.
  The headline theorem uses that fact.
- **Integrability.** The monomial moments are expanded as series by dominated and monotone
  convergence, which also gives the integrability needed for linearity.
- **The ζ(2) cancellation.** This is proved with formal power series, that is coefficient
  sequences and Cauchy products, following the identities for reversed Chebyshev rows. The paper
  argues through w = t/(1+f) and the Taylor branch of f.

### Finite-place lower bound (`src/catalan_fin_*.ml`, Propositions 2.2 and 3.4)

This component bounds the 2-adic valuation and the valuations at odd primes of the rational
determinant. It combines them through a lower bound for log|x| by its prime valuations, and sums
the losses with the prime number theorem.

- **One atom lemma instead of Cauchy–Binet and Z_p linear algebra.** The paper changes columns
  over Z_(p), uses Cauchy–Binet to pass to all full minors, and bounds ranks over F_p. The HOL
  proof uses a single lemma instead. Suppose every column of a determinant is a p-integral
  combination of fixed atom vectors with known valuations. Repeated atoms give zero terms, so
  the valuation is bounded by the best injective choice of atoms. This lemma is applied directly
  to the filtered determinant, so neither Cauchy–Binet nor linear algebra over F_p is needed.
- **No 2-adic series.** The paper's series M_s in Q₂ (Equation (22)) is replaced by a finite
  truncation whose tail has very high 2-adic valuation.
- **The prime-number-theorem sum.** HOL Light's `100/pnt.ml` proves the prime number theorem in
  counting form. The proof derives θ(n) ≤ (1+ε)n + C from it. The weighted limit (Equation (45))
  is needed only as an upper bound, and Abel summation against the nonincreasing loss function
  gives it. The paper uses step functions and uniform continuity.
- **log 2.** The bound log 2 ≤ 693149/10⁶ in the final numerical check is proved from the Taylor
  series of exp. The paper uses the series for log 2.

### Nonvanishing (`src/catalan_nv_*.ml`, Proposition 4.1)

This component shows that p² times the filtered matrix at N = p is congruent mod p to an explicit
block matrix. Its determinant is a p-unit for large p, so the determinant is nonzero.

- **Real numbers and congruences instead of F_p.** p-integrality and congruence mod p are
  predicates on real numbers. Matrices that are entrywise congruent have congruent determinants.
  The palindromic identities of Equations (51)–(55) are proved for lifts to the integers rather
  than for polynomials over F_p.
- **Lifted basis change.** The paper's change-of-basis matrix a is lifted to integers through
  Chebyshev U coefficients, which agree with a up to the unit 2^(p−1). The determinant of the
  lifted block matrix is then computed exactly over the reals. It equals
  (∏ 2^(p−1−i))⁴⁸ · det B₀ · det(B₀+B₁)^((p−1)/2) · det(B₀−B₁)^((p−1)/2), which is Equation (60)
  without an eigenvector basis for Π over F_p.
- **The fixed certificate.** The paper and the Lean proof certify the three fixed 48×48
  matrices by Gaussian elimination mod 101, using the pivots of Table 1. In Lean this takes
  three times 48 step files plus inverse-row files, the bulk of the 395,000 lines in
  `FiniteMatrices/`. In HOL Light, OCaml computes an inverse mod 101 of each reduced matrix at
  load time, and HOL proves that the matrix times that inverse is the identity mod 101. This
  implies the determinant is nonzero.
- **Digit reductions.** Lemma 3.1 and Equations (32)–(36) are also proved here, independently
  of the finite-place files, so the two components do not depend on each other.

### Real-place upper bound (`src/catalan_rp_*.ml`, Sections 5–7)

This component bounds |Δ_N| by integrands with Vandermonde factors, in two cases. It bounds those
integrands by an energy functional and certifies the resulting one-variable suprema with exact
arithmetic. Its own interfaces are in `src/catalan_rp_defs.ml`, and `src/catalan_rp_asm.ml`
assembles them.

- **Riemann sums instead of n-fold integrals.** HOL Light types cannot depend on N, so the proof
  never forms integrals over (−1,1)ⁿ × (0,1)ⁿ. The paper applies the Andréief identity twice to
  get Equation (62). The HOL proof instead changes variables to x with t = 2x/(1+x²) in each
  entry. It then approximates the entries by midpoint Riemann sums, using that the determinant is
  continuous in its entries. For the discrete matrices, Cauchy–Binet expresses the determinant
  as a weighted sum of the paper's integrand over increasing node tuples. This gives
  |Δ_N| ≤ 2ⁿ · sup |integrand| directly.
- **Cauchy double alternant and row factorization.** Equations (63) and (65) are proved as in
  the paper.
- **The interpolation estimate without Hardy spaces.** The paper's Proposition 5.2 uses a
  projection onto a finite-dimensional subspace of H² and the operator L = I + JR. The HOL proof
  is finite-dimensional algebra:
  - The Gram matrix G_ij = 1/(1 − x_i x_j) is positive definite.
  - An explicit reversal matrix R satisfies R² = I and is an isometry for G.
  - The determinant identity |det[x_i^(n−1−r) + h_i x_i^r]| = |det(I + RD)| · |V(x)| holds.
  - Combined with a determinant bound for positive definite forms, these give the
    (1 + K₀n)ⁿ factor.
- **Lemma 5.1 without the maximum modulus principle.** The interpolating function h* is glued
  from Cauchy integrals over two explicit polygonal contours, using Cauchy's theorem and the
  identity theorem. Only the bound |h*| ≤ K₀n on the unit circle is needed, together with the
  Cauchy integral formula on the circle, so the maximum modulus step is not used.
- **The Hadamard estimate (Proposition 5.3).** This is proved through a real positive
  semidefinite Hadamard inequality and a "projective" Vandermonde matrix on the unit circle.
- **The energy bound (Proposition 6.1).** This follows Section 6: the Chebyshev expansion of
  the logarithmic kernel, the damping, and completing the squares with the trial sequences.
- **The certificates (Section 7).**
  - **Trial sequences:** the same as the paper's (Section 7.1).
  - **Root isolation:** the derivative of each one-variable function is A/(s·Q), with integer
    polynomials A, Q of degree up to 36. Instead of the paper's root brackets, the domain is cut
    into pieces on which a Möbius transform of A has at most one sign variation, which implies
    at most one root.
  - **Brackets:** each root is enclosed in a bracket of width about 10⁻¹² where A changes sign.
    Function values are bounded using proved rational bounds for log, arctan and π.
  - **Who computes what:** the Python scripts in `tools/rp_cert/` chose the cut points and
    brackets, and HOL checks all of them. The certified suprema give about −2.29110 for the
    case κ = 2, against the paper's stated −2.290939875 and the target −2.2909.

## Comparison with the Lean formalization

- **Shared skeleton.** The four components, the rational formula with a variable z, and the
  final assembly are the same as in Lean (`Results/Catalan.lean`).
- **Different routes inside the components:**
  - the ζ(2)-free treatment of the starting values
  - the atom lemma in place of Cauchy–Binet over Z_(p)
  - Riemann sums in place of n-fold integrals
  - finite-dimensional algebra in place of Hardy spaces
  - an inverse-matrix check in place of step-by-step Gaussian elimination
  - a sign-variation root isolation in place of the paper's brackets
- **Certificate data.** Most of the Lean development's size is stored certificate data:
  - Gaussian elimination steps for the fixed matrices
  - per-point rounding and logarithm-precision files that follow the manuscript's numerics
  The HOL development recomputes and checks such data when it loads, so it is much smaller,
  about 34,000 lines against about 574,000, but takes longer to check.
- **Independence.** The HOL proof was written independently. The Lean development served only
  as a guide to the structure and to the intermediate statements.
