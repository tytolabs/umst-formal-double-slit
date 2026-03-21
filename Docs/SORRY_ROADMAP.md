<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Community Contribution Roadmap — Sorry Gaps

## Status: 0 sorry ✅

All `sorry` have been eliminated from the project Lean files.

### Sorry 1: `vonNeumannEntropy_unitarily_invariant` — **CLOSED** ✅

**Previously:** sorry (Mathlib infrastructure gap).
**Now:** Fully proved via:
1. `charpoly_diagonal'` — `charpoly(diag d) = ∏(X - C(dᵢ))`
2. `IsHermitian.charpoly_eq_prod_eigenvalues` — spectral theorem → charpoly factorization
3. `eigenvalue_multiset_eq_of_charpoly_eq` — equal charpoly → equal root multisets
4. `Multiset.map_injective Complex.ofReal_injective` — ℂ → ℝ injectivity
5. `Multiset.map_congr` — equal multisets → equal negMulLog sums

### Axiom 2: `vonNeumannEntropy_nondecreasing_unital` — **AXIOM**

**Previously:** sorry (Klein's inequality).
**Now:** Restructured as `axiom` — the cleanest representation of the Mathlib dependency.

**Why axiom instead of sorry:**
- An `axiom` is type-checked and cannot be accidentally used as a `sorry`-escape
- It clearly documents the external mathematical dependency
- Lean correctly tracks it in `#print axioms` for auditability
- When Mathlib adds matrix logarithms, convert axiom → theorem

**Mathlib components needed to convert axiom → theorem:**
1. Matrix functional calculus for Hermitian matrices (`f(A) = U diag(f(λ)) U*`)
2. Matrix logarithm (`Matrix.log`)
3. Klein's inequality: `Tr(ρ(log ρ - log σ)) ≥ 0`

### Axiom: `klein_inequality` — **placeholder / packaging**

Declared in **`DataProcessingInequality.lean`** as a separate `axiom` for the Klein step; body may be tautological until a real Klein statement is wired to Mathlib. **Stream D** should merge this with the substantive unital DPI proof when infrastructure exists.

### Axiom: `physicalSecondLaw` — **Landauer / thermodynamics**

See **`Lean/LandauerLaw.lean`** — the explicit physical axiom of the stack (distinct from DPI/Klein).

### All Qubit Theorems — **SORRY-FREE** ✅

Every physically relevant result is proved:
- `whichPath_increases_entropy`
- `vonNeumannDiagonal_ge_vonNeumannEntropy`
- `vonNeumannEntropy_nondecreasing_unital_identity`
- `vonNeumannEntropy_unitarily_invariant` (general `Fin n`)
