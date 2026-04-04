/-
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-/

import Gate

/-!
# Flash-MoE 31B IT — formal runtime scaffold (Phases 2–3)

Specification anchor for `MaOS-Core/rust/maos-core/src/formal_runtime/`.

## Graded admissibility (constitutional kernel)

`AdmissibleN` and `admissibleN_compose` in `Gate.lean` justify n-step mass
accumulation via the triangle inequality.  Rust `ConstitutionalTraverser`
implements the same Σ|Δρ| bookkeeping coupled to `ThermodynamicFilter`.

## Galois / Landauer presentation functor

The Landauer left/right adjoints (`requiredEnergy`, `acquirableInfo`) live in
`EpistemicGalois.lean` (import chain currently blocked on `QuantumClassicalBridge`).
Rust `GaloisRouter` is the executable witness at fixed `T` and watt envelope.

## DIB Kleisli

`M A = DIBState → A × DIBState` is proved in `umst-formal/Lean/DIBKleisli.lean`;
Rust `DibM` is the same carrier for the token evaluation functor.
-/

namespace UMST.RuntimeScaffold

open UMST

/-- Graded constitutional relation (Lean SSOT for the traverser). -/
abbrev ConstitutionalN (n : ℕ) (s s' : ThermodynamicState) : Prop :=
  AdmissibleN n s s'

end UMST.RuntimeScaffold
