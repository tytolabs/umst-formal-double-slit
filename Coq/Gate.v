(* SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar *)
(* SPDX-License-Identifier: MIT *)
(* SPDX-License-Identifier: MIT *)

(* ================================================================== *)
(*  UMST-Formal: Gate.v                                                *)
(*                                                                      *)
(*  Core admissible-state predicate and safety theorems for the         *)
(*  thermodynamic gate of the Unified Material-State Tensor.            *)
(*                                                                      *)
(*  This module formalises the thermodynamic gate from the Rust kernel   *)
(*  (umst-prototype-2a) as a decidable predicate over rational-valued   *)
(*  material states.  We use QArith (Coq's rational arithmetic)         *)
(*  throughout — no floating-point anywhere in this file.               *)
(*                                                                      *)
(*  The gate accepts a proposed state transition (old → new) iff four   *)
(*  physical invariants hold simultaneously:                            *)
(*                                                                      *)
(*    1. Mass conservation        |ρ_new − ρ_old| < δ                  *)
(*    2. Clausius-Duhem           D_int = −ρ · ψ̇ ≥ 0                   *)
(*    3. Hydration irreversibility    α_new ≥ α_old                    *)
(*    4. Strength monotonicity    fc_new ≥ fc_old                      *)
(*                                                                      *)
(*  Empirical basis:                                                    *)
(*    Each invariant was identified inductively from field observation   *)
(*    of material failure modes across variable earth, lime, masonry,   *)
(*    and recycled-aggregate concrete (RAC) systems.  The constraints   *)
(*    are consistent with the cement science literature and are         *)
(*    documented with their derivation in                               *)
(*    Docs/Architecture-Invariants.md.                                  *)
(*                                                                      *)
(*  Correspondence to Rust kernel:                                      *)
(*    ThermodynamicState  ↔  ThermodynamicState in                      *)
(*                           thermodynamic_filter.rs                    *)
(*    admissible          ↔  check_transition returning accepted=true   *)
(*    gate_check          ↔  ThermodynamicFilter::check_transition      *)
(*                                                                      *)
(*  Mirror:                                                             *)
(*    This file mirrors Gate.agda in the Agda layer.  The Agda version  *)
(*    uses a Dec type (decision procedure); here we separate the        *)
(*    propositional predicate (admissible) from the boolean decision    *)
(*    function (gate_check) and prove their equivalence.                *)
(* ================================================================== *)

From Coq Require Import QArith.
From Coq Require Import Qfield.
From Coq Require Import Qring.
From Coq Require Import Bool.
From Coq Require Import Lia.

Open Scope Q_scope.

(* ================================================================== *)
(*  SECTION 1: Thermodynamic State                                      *)
(* ================================================================== *)

(** A [ThermodynamicState] captures the minimal set of fields needed
    to evaluate the four physical invariants.  We use rationals [Q]
    throughout for exact, decidable arithmetic.  The Rust kernel uses
    f64 with tolerance ε = 10⁻⁶; here we prove properties exactly.

    Physical meaning of each field:
      density      ρ   (kg/m³)   bulk density of the paste / concrete
      free_energy  ψ   (J/kg)    Helmholtz free energy per unit mass
                                  In Rust: ψ(α) = −Q_hyd · α
      hydration    α   (0–1)     degree of cement hydration
      strength     fc  (MPa)     compressive strength (Powers model:
                                  fc = S · x³ where x = gel-space ratio) *)

Record ThermodynamicState : Set := mkState {
  density     : Q;
  free_energy : Q;
  hydration   : Q;
  strength    : Q
}.

(* ================================================================== *)
(*  SECTION 2: Physical Constants                                       *)
(* ================================================================== *)

(** Tolerance for the mass conservation check.
    In the Rust kernel this is 100.0 kg/m³ — a generous bound that
    catches gross density jumps (e.g., accidentally swapping concrete
    with timber) while allowing normal hydration-induced changes
    (cement paste densifies by ~5–8% during full hydration). *)

Definition delta_mass : Q := 100 # 1.

(** Heat of hydration constant.
    Q_hyd ≈ 450 J/g for typical Portland cement (CEM I).
    The Helmholtz free energy model is ψ(α) = −Q_hyd · α.
    Since Q_hyd > 0, advancing hydration (α ↑) decreases ψ (ψ ↓),
    encoding the irreversible exothermic nature of the reaction.

    This value is consistent with standard Portland cement calorimetry
    data (Mindess, Young & Darwin, 2003) and the UMST Rust kernel. *)

Definition Q_hyd : Q := 450 # 1.

(* ================================================================== *)
(*  SECTION 3: Helmholtz Free Energy Model                              *)
(* ================================================================== *)

(** The specific constitutive law from cement chemistry.

        ψ(α) = −Q_hyd · α

    This is a simplification of the full thermodynamic potential
    (which would include elastic strain energy, thermal terms, etc.)
    but captures the dominant effect: hydration releases stored
    chemical energy monotonically.

    Physical intuition: think of unhydrated cement grains as tiny
    batteries.  Each grain that reacts (increasing α) discharges
    energy (decreasing ψ).  You cannot un-react a grain, so α only
    goes up and ψ only goes down. *)

Definition helmholtz (alpha : Q) : Q := (-Q_hyd) * alpha.

(* ================================================================== *)
(*  SECTION 4: Admissibility Predicate                                  *)
(* ================================================================== *)

(** The four invariants bundled as a single proposition.
    [admissible old new_] holds iff the transition old → new_
    satisfies all four physical laws simultaneously.

    Categorically, this defines the admissible morphisms in the
    category of material states — only transitions satisfying all
    four constraints are physically realisable.  The gate is the
    characteristic function of this predicate.

    Note on dt:  The time step appears in the Rust kernel's
    computation of ψ̇ = (ψ_new − ψ_old) / dt, but cancels in the
    sign check:
        D_int ≥ 0  ⟺  −ρ · ψ̇ ≥ 0  ⟺  ψ̇ ≤ 0  (since ρ > 0)
    We therefore omit dt without loss of generality. *)

Definition admissible (old new_ : ThermodynamicState) : Prop :=
  (density new_ - density old <= delta_mass)     /\
  (density old - density new_ <= delta_mass)     /\
  (free_energy new_ <= free_energy old)          /\
  (hydration old <= hydration new_)              /\
  (strength old <= strength new_).

(** Dissipation non-negativity — an equivalent restatement of
    Invariant 2 (Clausius-Duhem) that makes the physics explicit.

    D_int = −ρ · ψ̇ ≥ 0
    In discrete time:  D_int · dt = −ρ · (ψ_new − ψ_old)
                                   = ρ · (ψ_old − ψ_new)
    Since ρ > 0 and dt > 0, this reduces to ψ_new ≤ ψ_old. *)

Definition dissipation_nonneg (old new_ : ThermodynamicState) : Prop :=
  free_energy new_ <= free_energy old.

(* ================================================================== *)
(*  SECTION 5: Gate Decision Procedure (Boolean)                        *)
(* ================================================================== *)

(** [gate_check] is the computable boolean decision function that
    mirrors [ThermodynamicFilter::check_transition] in the Rust kernel.

    It returns [true] iff all four invariants hold.  Each individual
    check uses [Qle_bool] — the decidable ≤ on rationals — and the
    conjunction is computed with [andb] (&&).

    In category-theoretic terms, this is a morphism in the arrow
    category of Set:  gate_check : State × State → Bool.
    Theorem [gate_check_correct] below proves it is the characteristic
    function of [admissible]. *)

Definition gate_check (old new_ : ThermodynamicState) : bool :=
  Qle_bool (density new_ - density old) delta_mass     &&
  Qle_bool (density old - density new_) delta_mass     &&
  Qle_bool (free_energy new_) (free_energy old)        &&
  Qle_bool (hydration old) (hydration new_)            &&
  Qle_bool (strength old) (strength new_).

(* ================================================================== *)
(*  SECTION 6: Boolean Reflection Helpers                               *)
(* ================================================================== *)

(** These helper lemmas bridge between the left-associated boolean
    conjunction in [gate_check] and the right-associated propositional
    conjunction in [admissible].

    The standard library provides [Qle_bool_iff : Qle_bool x y = true
    <-> x <= y] and [andb_true_iff : a && b = true <-> a = true /\
    b = true].  We compose them into a 5-way version for readability. *)

Local Lemma andb5_true (a b c d e : bool) :
  a && b && c && d && e = true ->
  a = true /\ b = true /\ c = true /\ d = true /\ e = true.
Proof.
  destruct a, b, c, d, e; simpl; intro H; try discriminate H; auto 10.
Qed.

Local Lemma andb5_intro (a b c d e : bool) :
  a = true -> b = true -> c = true -> d = true -> e = true ->
  a && b && c && d && e = true.
Proof.
  intros -> -> -> -> ->. reflexivity.
Qed.

(* SECTION 7: constitutive laws — MirrorScope.GatePhysicalModel.PhysicalLaws *)

(* ================================================================== *)
(*  SECTION 8: Helmholtz Antitone Lemma (Concrete Model)                *)
(* ================================================================== *)

(** This lemma shows that the specific Helmholtz model ψ(α) = −Q·α
    satisfies the antitone property, providing a concrete witness
    for the [psi_antitone] axiom.

    Proof obligation: if a₁ ≤ a₂ and Q > 0, then −Q·a₂ ≤ −Q·a₁.
    This is a standard ordered-field property: multiplying both sides
    of an inequality by a negative number (−Q < 0) reverses the
    direction. *)

Lemma helmholtz_antitone : forall a1 a2 : Q,
  a1 <= a2 -> helmholtz a2 <= helmholtz a1.
Proof.
  intros a1 a2 H.
  unfold helmholtz, Q_hyd.
  assert (e2 : (- (450 # 1)) * a2 == - ((450 # 1) * a2)) by field.
  assert (e1 : (- (450 # 1)) * a1 == - ((450 # 1) * a1)) by field.
  assert (Hmul : (450 # 1) * a1 <= (450 # 1) * a2).
  { rewrite (Qmult_comm (450 # 1) a1), (Qmult_comm (450 # 1) a2).
    apply Qmult_le_compat_r with (z := (450 # 1)).
    - exact H.
    - unfold Qle. simpl. lia. }
  assert (Hopp : - ((450 # 1) * a2) <= - ((450 # 1) * a1)).
  { now apply Qopp_le_compat. }
  rewrite e2, e1.
  exact Hopp.
Qed.

(* ================================================================== *)
(*  SECTION 8b: Helmholtz Gradient — SDF Interpretation                *)
(* ================================================================== *)

(** Lemma (Helmholtz Gradient):
    The discrete gradient of the Helmholtz function is constant:

        ψ(α + ε) − ψ(α) = −Q_hyd · ε

    This is the formal counterpart of the SDF "Eikonal" condition:
    the gradient of ψ has constant magnitude Q_hyd = 450 J/kg
    everywhere on [0, 1].  Specifically:

        ψ(α) = −Q_hyd · α
        ψ(α + ε) = −Q_hyd · (α + ε) = −Q_hyd · α − Q_hyd · ε
        ψ(α + ε) − ψ(α) = −Q_hyd · ε

    This, together with helmholtz_antitone, gives the complete SDF
    characterisation of ψ:
      • Gradient direction: −Q_hyd < 0 (antitone in α, §8)
      • Gradient magnitude: Q_hyd = 450 (constant, Eikonal, §8b)
      • Admissible side: ψ_new ≤ ψ_old, i.e., moving along −∇ψ

    In the gate's Clausius-Duhem check, the condition D_int ≥ 0 is
    exactly the condition that the state transition moves along the
    negative-gradient direction of ψ.

    Proof: immediate by ring — the goal reduces to linear arithmetic
    over Q after unfolding the definitions. *)

Lemma helmholtz_gradient : forall alpha eps : Q,
  helmholtz (alpha + eps) - helmholtz alpha == - (Q_hyd * eps).
Proof.
  intros alpha eps.
  unfold helmholtz, Q_hyd.
  ring.
Qed.

(** Corollary: ψ is additive (linear).
    ψ(α₁ + α₂) = ψ(α₁) + ψ(α₂).
    This is the formal statement that ψ is a group homomorphism from
    (Q, +) to (Q, +), i.e., a linear SDF. *)

Lemma helmholtz_additive : forall a1 a2 : Q,
  helmholtz (a1 + a2) == helmholtz a1 + helmholtz a2.
Proof.
  intros a1 a2.
  unfold helmholtz, Q_hyd.
  ring.
Qed.

(* SECTIONS 9–11 + gate_accepts_forward_hydration: MirrorScope.GatePhysicalModel *)

(* ================================================================== *)
(*  SECTION 12: Gate Correctness — Soundness + Completeness             *)
(* ================================================================== *)

(** Theorem (Gate Correctness):
    [gate_check] returns [true] if and only if [admissible] holds.

    This is a SOUNDNESS + COMPLETENESS result:

    Soundness (→):    gate_check = true  →  admissible
      "If the gate says yes, the transition truly is admissible."
      This ensures the gate never accepts unphysical transitions.

    Completeness (←):  admissible  →  gate_check = true
      "If a transition is admissible, the gate says yes."
      This ensures the gate never rejects valid transitions.

    Together, [gate_check] is the faithful decision procedure for
    [admissible].  The extracted OCaml code inherits this guarantee:
    the boolean function computed by OCaml agrees exactly with the
    mathematical predicate proved correct in Coq.

    Proof strategy:
      We decompose the 5-way boolean conjunction into individual
      [Qle_bool] checks and use [Qle_bool_iff] (from the standard
      library) to bridge between boolean and propositional ≤. *)

Theorem gate_check_correct :
  forall old new_ : ThermodynamicState,
  gate_check old new_ = true <-> admissible old new_.
Proof.
  intros old new_.
  unfold gate_check, admissible.
  split.

  - (* Soundness: gate_check = true → admissible *)
    intro H.
    apply andb5_true in H.
    destruct H as (H1 & H2 & H3 & H4 & H5).
    refine (conj _ (conj _ (conj _ (conj _ _))));
      apply (proj1 (Qle_bool_iff _ _)); assumption.

  - (* Completeness: admissible → gate_check = true *)
    intros (H1 & H2 & H3 & H4 & H5).
    apply andb5_intro;
      apply (proj2 (Qle_bool_iff _ _)); assumption.
Qed.

(** Corollary: gate_check is sound. *)

Corollary gate_check_sound :
  forall old new_ : ThermodynamicState,
  gate_check old new_ = true -> admissible old new_.
Proof.
  intros old new_.
  apply (proj1 (gate_check_correct old new_)).
Qed.

(** Corollary: gate_check is complete. *)

Corollary gate_check_complete :
  forall old new_ : ThermodynamicState,
  admissible old new_ -> gate_check old new_ = true.
Proof.
  intros old new_.
  apply (proj2 (gate_check_correct old new_)).
Qed.

(* ================================================================== *)
(*  SECTION 13: Graded Admissibility (N-Step Accumulated Tolerance)    *)
(*                                                                      *)
(*  Mirrors Gate.lean §10.  The single-step admissible predicate is    *)
(*  NOT transitive for the mass condition (see Constitutional.v for    *)
(*  the counterexample and admissible_N_compose).                      *)
(*                                                                      *)
(*  admissible_N n old new_ holds iff:                                  *)
(*    1. |ρ_new - ρ_old| ≤ n * delta_mass  (accumulated mass bound)   *)
(*    2-4. same as admissible (order conditions)                        *)
(* ================================================================== *)

Definition admissible_N (n : nat) (old new_ : ThermodynamicState) : Prop :=
  (density new_ - density old <= inject_Z (Z.of_nat n) * delta_mass) /\
  (density old - density new_ <= inject_Z (Z.of_nat n) * delta_mass) /\
  (free_energy new_ <= free_energy old) /\
  (hydration old <= hydration new_) /\
  (strength old <= strength new_).

Lemma admissible_N_refl : forall (n : nat) (s : ThermodynamicState),
  admissible_N n s s.
Proof.
  intros n s.
  unfold admissible_N.
  repeat split.
  - ring_simplify (density s - density s).
    apply Qmult_le_0_compat.
    + destruct n; simpl; unfold inject_Z; simpl; try apply Qle_refl.
      unfold Qle. simpl. lia.
    + unfold delta_mass. unfold Qle. simpl. lia.
  - ring_simplify (density s - density s).
    apply Qmult_le_0_compat.
    + destruct n; simpl; unfold inject_Z; simpl; try apply Qle_refl.
      unfold Qle. simpl. lia.
    + unfold delta_mass. unfold Qle. simpl. lia.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qle_refl.
Qed.

Lemma admissible_implies_admissible_N1 : forall old new_ : ThermodynamicState,
  admissible old new_ -> admissible_N 1 old new_.
Proof.
  intros old new_ (Hmc1 & Hmc2 & Hdiss & Hhyd & Hstr).
  unfold admissible_N.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
    rewrite <- Hq.
    exact Hmc1.
  - assert (Hq : inject_Z (Z.of_nat 1) * delta_mass == delta_mass) by (simpl; ring).
    rewrite <- Hq.
    exact Hmc2.
  - exact Hdiss.
  - exact Hhyd.
  - exact Hstr.
Qed.

(* ================================================================== *)
(*  END OF FILE                                                         *)
(*                                                                      *)
(*  Summary of results:                                                 *)
(*    • ThermodynamicState : record with ρ, ψ, α, fc                   *)
(*    • admissible : Prop requiring 4 invariants                        *)
(*    • gate_check : bool decision function                             *)
(*    • clausius_duhem_forward : α advances ⟹ dissipation ≥ 0          *)
(*    • strength_monotone_powers : α advances ⟹ fc non-decreasing      *)
(*    • forward_hydration_admissible : main safety theorem              *)
(*    • gate_check_correct : gate_check ↔ admissible (sound+complete)  *)
(*    • gate_accepts_forward_hydration : physical ⟹ gate says true     *)
(*                                                                      *)
(*  Axioms used:                                                        *)
(*    • psi_antitone (Helmholtz model: ψ antitone in α)                *)
(*    • fc_monotone  (Powers model: fc monotone in α)                  *)
(*                                                                      *)
(*  All lemmas fully proved (no Admitted obligations remain):           *)
(*    • helmholtz_antitone:  proved via unfold Qle / destruct / nia    *)
(*    • helmholtz_gradient:  proved via ring                           *)
(*    • helmholtz_additive:  proved via ring                           *)
(* ================================================================== *)
