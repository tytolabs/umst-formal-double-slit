-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
------------------------------------------------------------------------
-- UMST-Formal-Double-Slit: KnowingFibreLaw.agda
--
-- Twin of Lean/KnowingFibreInstance.lean and Lean/KnowingFibreLaw.lean: the knowing fibre's processes as instances
-- of the erase and measure-feedback cases of umst-formal's one predicate SecondLaw (umst-formal Agda/Process.agda).
-- The two cases are stated below clause for clause on the records of Process.agda (ErasureProcess by its dissipated
-- entropy, FeedbackProcess by its work, free-energy change and k_B T); this tree cannot import Process.agda while
-- both trees name a module Constants.SI (cell FORMAL-KNOWING-TWIN-LAW-IMPORT).
--
-- Over ℚ: the standard library has no real logarithm, so the logarithm is a parameter (PathLog) carrying the
-- properties of the real logarithm the statements use: ln 1 = 0, ln x ≤ x − 1 for x > 0, and the binary entropy at
-- most ln 2 (Lean Real.binEntropy_le_log_two, Coq shannon_binary_le_ln2). With the real logarithm each theorem
-- below is the Lean statement; the record is a parameter of each statement, never a postulate. Energies in joules
-- are k_B T times an entropy in nats (k_B T ln 2 times bits), so no division by ln 2 or T appears.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module KnowingFibreLaw where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _-_; -_; _≤_; _<_; nonNegative)
open import Data.Rational.Properties
  using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; *-monoˡ-≤-nonNeg; neg-antimono-≤; <-cmp;
         <-irrefl; ≤-<-trans; nonNegative⁻¹; nonNeg*nonNeg⇒nonNeg;
         +-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ; neg-distrib-+;
         *-assoc; *-comm; *-identityˡ; *-zeroˡ; *-distribˡ-+; *-distribʳ-+; neg-distribʳ-*)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import DensityStateSpec
open import ComplementaritySpec

open DensityMatrix2

two : ℚ
two = 1ℚ + 1ℚ

-- Identities of the field ℚ used below, each from the ring laws of Data.Rational.Properties (the reflective ring
-- solver over ℚ normalises its coefficients by gcd during type checking, which this file avoids).
private
  zero-neg-add : ∀ x → (- 0ℚ) + x ≡ x
  zero-neg-add x = +-identityˡ x

  sub-zero : ∀ a → a - 0ℚ ≡ a
  sub-zero a = +-identityʳ a

  add-sub-cancelʳ : ∀ a b → (a + b) - b ≡ a
  add-sub-cancelʳ a b = trans (+-assoc a b (- b)) (trans (cong (a +_) (+-inverseʳ b)) (+-identityʳ a))

  add-sub-cancelˡ : ∀ a b → (a + b) - a ≡ b
  add-sub-cancelˡ a b = trans (cong (_- a) (+-comm a b)) (add-sub-cancelʳ b a)

  four-split : ∀ x → four * x ≡ two * (x + x)
  four-split x = trans (*-distribʳ-+ x two two) (sym (*-distribˡ-+ two x x))

  half-two : ∀ k s → ½ * (k * (two * s)) ≡ k * s
  half-two k s =
    trans (cong (½ *_) (trans (sym (*-assoc k two s)) (trans (cong (_* s) (*-comm k two)) (*-assoc two k s))))
          (trans (sym (*-assoc ½ two (k * s))) (*-identityˡ (k * s)))

------------------------------------------------------------------------
-- The two cases of SecondLaw (umst-formal Agda/Process.agda)
------------------------------------------------------------------------

record ErasureProcess : Set where
  constructor mkErasure
  field
    dissipatedEntropy : ℚ

-- A measurement with feedback: external work, free-energy change, and k_B T of its bath.
record FeedbackProcess : Set where
  constructor mkFeedback
  field
    extWork         : ℚ
    deltaFreeEnergy : ℚ
    kBT             : ℚ

open ErasureProcess
open FeedbackProcess

-- SecondLaw (erase e) (erasure ΔS): the entropy removed is at most the entropy dissipated.
eraseCase : ErasureProcess → ℚ → Set
eraseCase e ΔS = ΔS ≤ dissipatedEntropy e

-- SecondLaw (measureFeedback f) (feedback I): W_ext ≤ −ΔF + k_B T I.
measureFeedbackCase : FeedbackProcess → ℚ → Set
measureFeedbackCase f I = extWork f ≤ (- deltaFreeEnergy f) + kBT f * I

------------------------------------------------------------------------
-- The logarithm and the entropies of the path qubit
------------------------------------------------------------------------

-- Shannon entropy (nats) of the binary distribution (p, 1 − p).
binaryEntropy : (ℚ → ℚ) → ℚ → ℚ
binaryEntropy ln p = - (p * ln p + (1ℚ - p) * ln (1ℚ - p))

record PathLog : Set where
  field
    ln             : ℚ → ℚ
    ln-one         : ln 1ℚ ≡ 0ℚ
    ln-le-sub-one  : ∀ x → 0ℚ < x → ln x ≤ x - 1ℚ
    entropy-le-ln2 : ∀ p → 0ℚ ≤ p → p ≤ 1ℚ → binaryEntropy ln p ≤ ln two

open PathLog

-- Diagonal (path) entropy in nats.
vonNeumannDiagonal : PathLog → DensityMatrix2 → ℚ
vonNeumannDiagonal L ρ = binaryEntropy (ln L) (p₀ ρ)

-- The Born prior of the path, by its first weight.
pathBornDist : DensityMatrix2 → ℚ
pathBornDist ρ = p₀ ρ

-- The entropy erasing the path prior to the Dirac state removes: S(prior) − S(Dirac).
entropyDrop : PathLog → DensityMatrix2 → ℚ
entropyDrop L ρ = binaryEntropy (ln L) (pathBornDist ρ) - binaryEntropy (ln L) 1ℚ

private
  binaryEntropy-one : ∀ L → binaryEntropy (ln L) 1ℚ ≡ 0ℚ
  binaryEntropy-one L =
    trans (cong -_ (trans (cong₂ _+_ (*-identityˡ (ln L 1ℚ)) (*-zeroˡ (ln L (1ℚ - 1ℚ)))) (+-identityʳ (ln L 1ℚ))))
          (cong -_ (ln-one L))

  p₁≡ : ∀ ρ → p₁ ρ ≡ 1ℚ - p₀ ρ
  p₁≡ ρ = trans (sym (add-sub-cancelˡ (p₀ ρ) (p₁ ρ))) (cong (_- p₀ ρ) (trace-one ρ))

  p₀≡ : ∀ ρ → p₀ ρ ≡ 1ℚ - p₁ ρ
  p₀≡ ρ = trans (sym (add-sub-cancelʳ (p₀ ρ) (p₁ ρ))) (cong (_- p₁ ρ) (trace-one ρ))

  p₀≤1 : ∀ ρ → p₀ ρ ≤ 1ℚ
  p₀≤1 ρ = ≤-trans (≤-reflexive (sym (+-identityʳ (p₀ ρ))))
                   (≤-trans (+-monoʳ-≤ (p₀ ρ) (p₁-nonneg ρ)) (≤-reflexive (trace-one ρ)))

  ln2-nonneg : ∀ L → 0ℚ ≤ ln L two
  ln2-nonneg L = subst (_≤ ln L two) (binaryEntropy-one L) (entropy-le-ln2 L 1ℚ (nonNegative⁻¹ 1ℚ) ≤-refl)

-- The drop equals the path entropy (twin of KnowingFibreInstance.shannonEntropy_pathBornDist).
shannonEntropy-pathBornDist : ∀ L ρ → entropyDrop L ρ ≡ vonNeumannDiagonal L ρ
shannonEntropy-pathBornDist L ρ =
  trans (cong (λ z → binaryEntropy (ln L) (p₀ ρ) - z) (binaryEntropy-one L))
        (sub-zero (vonNeumannDiagonal L ρ))

------------------------------------------------------------------------
-- Twins of Lean/KnowingFibreInstance.lean
------------------------------------------------------------------------

-- The erasure of the path prior at work T · S: it dissipates S.
pathBornEraseProcess : PathLog → DensityMatrix2 → ErasureProcess
pathBornEraseProcess L ρ = mkErasure (vonNeumannDiagonal L ρ)

pathBornErase-secondLaw : ∀ L ρ → eraseCase (pathBornEraseProcess L ρ) (entropyDrop L ρ)
pathBornErase-secondLaw L ρ = ≤-reflexive (shannonEntropy-pathBornDist L ρ)

-- The same instance as a member of the process family, against the path entropy itself.
pathBornErase-processFamily : ∀ L ρ → eraseCase (pathBornEraseProcess L ρ) (vonNeumannDiagonal L ρ)
pathBornErase-processFamily L ρ = ≤-refl

-- Energies in joules at k_B T: one bit k_B T ln 2; the diagonal Landauer cost k_B T ln 2 · (S / ln 2) = k_B T S.
landauerBitEnergy : PathLog → ℚ → ℚ
landauerBitEnergy L kT = kT * ln L two

landauerCostDiagonal : PathLog → ℚ → DensityMatrix2 → ℚ
landauerCostDiagonal L kT ρ = kT * vonNeumannDiagonal L ρ

landauerCostDiagonal-eq-kB-eraseWork : ∀ L kT ρ →
  landauerCostDiagonal L kT ρ ≡ kT * dissipatedEntropy (pathBornEraseProcess L ρ)
landauerCostDiagonal-eq-kB-eraseWork L kT ρ = refl

-- The erase hypothesis of a path qubit: the qubit, the logarithm, and admissibility of its erasure.
record PathEraseHypothesis : Set where
  field
    log        : PathLog
    state      : DensityMatrix2
    admissible : eraseCase (pathBornEraseProcess log state) (entropyDrop log state)

pathEraseHypothesis-default : PathLog → DensityMatrix2 → PathEraseHypothesis
pathEraseHypothesis-default L ρ = record { log = L ; state = ρ ; admissible = pathBornErase-secondLaw L ρ }

data PathProbe : Set where
  nullProbe whichPathProbe : PathProbe

EpistemicMI : PathLog → PathProbe → DensityMatrix2 → ℚ
EpistemicMI L nullProbe      ρ = 0ℚ
EpistemicMI L whichPathProbe ρ = vonNeumannDiagonal L ρ

EpistemicMI-le-ln2 : ∀ L p ρ → EpistemicMI L p ρ ≤ ln L two
EpistemicMI-le-ln2 L nullProbe      ρ = ln2-nonneg L
EpistemicMI-le-ln2 L whichPathProbe ρ = entropy-le-ln2 L (p₀ ρ) (p₀-nonneg ρ) (p₀≤1 ρ)

-- The probe's readout cost: k_B T ln 2 per bit of its information.
measurementCost : PathLog → PathProbe → DensityMatrix2 → ℚ → ℚ
measurementCost L p ρ kT = kT * EpistemicMI L p ρ

epistemicMeasureFeedback : PathLog → PathProbe → DensityMatrix2 → ℚ → FeedbackProcess
epistemicMeasureFeedback L p ρ kT = mkFeedback (measurementCost L p ρ kT) 0ℚ kT

measurementCost-eq-kBT-epistemicMI : ∀ L p ρ kT → measurementCost L p ρ kT ≡ kT * EpistemicMI L p ρ
measurementCost-eq-kBT-epistemicMI L p ρ kT = refl

-- The measure-feedback hypothesis: a probe on a qubit at k_B T, a record information equal to the probe's, and the
-- measure-feedback case.
record MeasureFeedbackHypothesis : Set where
  field
    log        : PathLog
    probe      : PathProbe
    state      : DensityMatrix2
    kT         : ℚ
    mi         : ℚ
    miAlign    : mi ≡ EpistemicMI log probe state
    admissible : measureFeedbackCase (epistemicMeasureFeedback log probe state kT) mi

measureFeedback-admissible-iff : ∀ L p ρ kT mi → mi ≡ EpistemicMI L p ρ →
  (measureFeedbackCase (epistemicMeasureFeedback L p ρ kT) mi → measurementCost L p ρ kT ≤ kT * EpistemicMI L p ρ) ×
  (measurementCost L p ρ kT ≤ kT * EpistemicMI L p ρ → measureFeedbackCase (epistemicMeasureFeedback L p ρ kT) mi)
measureFeedback-admissible-iff L p ρ kT mi hmi = (λ h → ≤-trans h (≤-reflexive e)) , (λ h → ≤-trans h (≤-reflexive (sym e)))
  where
  e : (- 0ℚ) + kT * mi ≡ kT * EpistemicMI L p ρ
  e = trans (zero-neg-add (kT * mi)) (cong (kT *_) hmi)

measureFeedback-null-instance : ∀ L ρ kT → measureFeedbackCase (epistemicMeasureFeedback L nullProbe ρ kT) 0ℚ
measureFeedback-null-instance L ρ kT = ≤-reflexive (sym (zero-neg-add (kT * 0ℚ)))

------------------------------------------------------------------------
-- Twins of Lean/KnowingFibreLaw.lean
------------------------------------------------------------------------

-- A joint law of two binary variables, by its four masses.
record JointDist2 : Set where
  constructor mkJoint
  field
    j00 j01 j10 j11 : ℚ

open JointDist2

jointEntropy : (ℚ → ℚ) → JointDist2 → ℚ
jointEntropy ln J = - (j00 J * ln (j00 J) + j01 J * ln (j01 J) + j10 J * ln (j10 J) + j11 J * ln (j11 J))

marginalX marginalY : JointDist2 → ℚ
marginalX J = j00 J + j01 J
marginalY J = j00 J + j10 J

mutualInformation : (ℚ → ℚ) → JointDist2 → ℚ
mutualInformation ln J = binaryEntropy ln (marginalX J) + binaryEntropy ln (marginalY J) - jointEntropy ln J

-- The record of a Lüders which-path measurement: the record equals the path.
pathRecordJoint : DensityMatrix2 → JointDist2
pathRecordJoint ρ = mkJoint (p₀ ρ) 0ℚ 0ℚ (p₁ ρ)

pathRecordJoint-marginalX : ∀ ρ → marginalX (pathRecordJoint ρ) ≡ pathBornDist ρ
pathRecordJoint-marginalX ρ = +-identityʳ (p₀ ρ)

pathRecordJoint-marginalY : ∀ ρ → marginalY (pathRecordJoint ρ) ≡ pathBornDist ρ
pathRecordJoint-marginalY ρ = +-identityʳ (p₀ ρ)

pathRecordJoint-jointEntropy : ∀ L ρ → jointEntropy (ln L) (pathRecordJoint ρ) ≡ binaryEntropy (ln L) (pathBornDist ρ)
pathRecordJoint-jointEntropy L ρ =
  trans (cong (λ t → - (t + p₁ ρ * ln L (p₁ ρ))) drop-zeros)
        (cong (λ x → - (p₀ ρ * ln L (p₀ ρ) + x * ln L x)) (p₁≡ ρ))
  where
  al = p₀ ρ * ln L (p₀ ρ)
  drop-zeros : (al + 0ℚ * ln L 0ℚ) + 0ℚ * ln L 0ℚ ≡ al
  drop-zeros = trans (cong₂ _+_ (trans (cong (al +_) (*-zeroˡ (ln L 0ℚ))) (+-identityʳ al)) (*-zeroˡ (ln L 0ℚ)))
                     (+-identityʳ al)

pathRecordJoint-mutualInformation : ∀ L ρ → mutualInformation (ln L) (pathRecordJoint ρ) ≡ EpistemicMI L whichPathProbe ρ
pathRecordJoint-mutualInformation L ρ =
  trans (cong (λ x → binaryEntropy (ln L) x + binaryEntropy (ln L) x - jointEntropy (ln L) (pathRecordJoint ρ))
              (pathRecordJoint-marginalX ρ))
        (trans (cong (λ y → binaryEntropy (ln L) (p₀ ρ) + binaryEntropy (ln L) (p₀ ρ) - y) (pathRecordJoint-jointEntropy L ρ))
               (add-sub-cancelʳ (binaryEntropy (ln L) (p₀ ρ)) (binaryEntropy (ln L) (p₀ ρ))))

-- The which-path readout at its cost k_B T I is a measure-feedback instance, with equality.
whichPath-measureFeedback-secondLaw : ∀ L ρ kT →
  measureFeedbackCase (epistemicMeasureFeedback L whichPathProbe ρ kT) (mutualInformation (ln L) (pathRecordJoint ρ))
whichPath-measureFeedback-secondLaw L ρ kT
  with measureFeedback-admissible-iff L whichPathProbe ρ kT _ (pathRecordJoint-mutualInformation L ρ)
... | _ , bwd = bwd ≤-refl

landauerBitEnergy-eq-kB : ∀ L kT → landauerBitEnergy L kT ≡ kT * ln L two
landauerBitEnergy-eq-kB L kT = refl

private
  mono-kT : ∀ kT → 0ℚ ≤ kT → ∀ {a b} → a ≤ b → kT * a ≤ kT * b
  mono-kT kT hk = *-monoˡ-≤-nonNeg kT {{nonNegative hk}}

-- Information is worth at most one bit: an admissible feedback on a record whose information is a path probe's
-- extracts at most −ΔF + k_B T ln 2.
measureFeedback-extWork-le-landauerBitEnergy : ∀ L f p ρ mi → 0ℚ ≤ kBT f → mi ≡ EpistemicMI L p ρ →
  measureFeedbackCase f mi → extWork f ≤ (- deltaFreeEnergy f) + landauerBitEnergy L (kBT f)
measureFeedback-extWork-le-landauerBitEnergy L f p ρ mi hk hmi h =
  ≤-trans h (+-monoʳ-≤ (- deltaFreeEnergy f)
    (mono-kT (kBT f) hk (subst (_≤ ln L two) (sym hmi) (EpistemicMI-le-ln2 L p ρ))))

-- The readout costs at most one bit, through the law: a probe's readout admissible under the measure-feedback case
-- against a record carrying its information costs at most k_B T ln 2.
readoutCost-le-landauerBitEnergy-of-secondLaw : ∀ L p ρ kT mi → 0ℚ ≤ kT → mi ≡ EpistemicMI L p ρ →
  measureFeedbackCase (epistemicMeasureFeedback L p ρ kT) mi → measurementCost L p ρ kT ≤ landauerBitEnergy L kT
readoutCost-le-landauerBitEnergy-of-secondLaw L p ρ kT mi hk hmi h =
  ≤-trans (measureFeedback-extWork-le-landauerBitEnergy L (epistemicMeasureFeedback L p ρ kT) p ρ mi hk hmi h)
          (≤-reflexive (zero-neg-add (landauerBitEnergy L kT)))

-- The erase case on the path record, unfolded: the path entropy is at most the dissipated entropy.
erase-pathRecord-work : ∀ L e ρ → eraseCase e (entropyDrop L ρ) → vonNeumannDiagonal L ρ ≤ dissipatedEntropy e
erase-pathRecord-work L e ρ h = subst (_≤ dissipatedEntropy e) (shannonEntropy-pathBornDist L ρ) h

-- Each bit costs k_B T ln 2: erasing the path record costs at least the diagonal Landauer cost.
erase-pathRecord-cost-ge-bits : ∀ L e ρ kT → 0ℚ ≤ kT → eraseCase e (entropyDrop L ρ) →
  landauerCostDiagonal L kT ρ ≤ kT * dissipatedEntropy e
erase-pathRecord-cost-ge-bits L e ρ kT hk h = mono-kT kT hk (erase-pathRecord-work L e ρ h)

-- −x ln x ≥ x (1 − x) for x ≥ 0, from ln x ≤ x − 1.
negMulLog-ge-mul-one-sub : ∀ L x → 0ℚ ≤ x → x * (1ℚ - x) ≤ - (x * ln L x)
negMulLog-ge-mul-one-sub L x hx with <-cmp 0ℚ x
... | tri< 0<x _ _ =
  ≤-trans (≤-reflexive (sym (trans (neg-distribʳ-* x (x - 1ℚ))
                                    (cong (x *_) (trans (neg-distrib-+ x (- 1ℚ)) (+-comm (- x) 1ℚ))))))
          (neg-antimono-≤ (mono-kT x hx (ln-le-sub-one L x 0<x)))
... | tri≈ _ 0≡x _ =
  subst (λ y → y * (1ℚ - y) ≤ - (y * ln L y)) 0≡x
        (≤-reflexive (sym (cong -_ (*-zeroˡ (ln L 0ℚ)))))
... | tri> _ _ x<0 = ⊥-elim (<-irrefl refl (≤-<-trans hx x<0))

-- The Englert partner bounds the path entropy: 1 − D² ≤ 2 S.
one-sub-distinguishability-sq-le-two-mul-entropy : ∀ L ρ → 1ℚ - distinguishability² ρ ≤ two * vonNeumannDiagonal L ρ
one-sub-distinguishability-sq-le-two-mul-entropy L ρ =
  ≤-trans (≤-reflexive lhs)
          (≤-trans (*-monoˡ-≤-nonNeg two (+-mono-≤ h₀ h₁)) (≤-reflexive rhs))
  where
  a = p₀ ρ
  b = p₁ ρ
  h₀ : a * (1ℚ - a) ≤ - (a * ln L a)
  h₀ = negMulLog-ge-mul-one-sub L a (p₀-nonneg ρ)
  h₁ : b * (1ℚ - b) ≤ - (b * ln L b)
  h₁ = negMulLog-ge-mul-one-sub L b (p₁-nonneg ρ)
  -- Englert's square identity at trace one: 4 a b + D² = (a + b)² = 1.
  four-ab : four * (a * b) + distinguishability² ρ ≡ 1ℚ
  four-ab = trans (square-identity a b) (cong (λ t → t * t) (trace-one ρ))
  ab≡ : a * b ≡ a * (1ℚ - a)
  ab≡ = cong (a *_) (p₁≡ ρ)
  ba≡ : a * b ≡ b * (1ℚ - b)
  ba≡ = trans (*-comm a b) (cong (b *_) (p₀≡ ρ))
  lhs : 1ℚ - distinguishability² ρ ≡ two * (a * (1ℚ - a) + b * (1ℚ - b))
  lhs = trans (cong (_- distinguishability² ρ) (sym four-ab))
              (trans (add-sub-cancelʳ (four * (a * b)) (distinguishability² ρ))
                     (trans (four-split (a * b)) (cong (two *_) (cong₂ _+_ ab≡ ba≡))))
  rhs : two * (- (a * ln L a) + - (b * ln L b)) ≡ two * vonNeumannDiagonal L ρ
  rhs = trans (cong (two *_) (sym (neg-distrib-+ (a * ln L a) (b * ln L b))))
              (cong (λ t → two * - (a * ln L a + t * ln L t)) (p₁≡ ρ))

-- Erasing the path record costs at least k_B T (1 − D²) / 2.
erase-pathRecord-cost-ge-complementarity : ∀ L e ρ kT → 0ℚ ≤ kT → eraseCase e (entropyDrop L ρ) →
  ½ * (kT * (1ℚ - distinguishability² ρ)) ≤ kT * dissipatedEntropy e
erase-pathRecord-cost-ge-complementarity L e ρ kT hk h =
  ≤-trans (*-monoˡ-≤-nonNeg ½ (mono-kT kT hk (one-sub-distinguishability-sq-le-two-mul-entropy L ρ)))
          (≤-trans (≤-reflexive (half-two kT (vonNeumannDiagonal L ρ)))
                   (erase-pathRecord-cost-ge-bits L e ρ kT hk h))

-- Fringes cost to forget: through Englert's V² + D² ≤ 1, erasing the record costs at least k_B T V² / 2.
erase-pathRecord-cost-ge-visibility-sq : ∀ L e ρ kT → 0ℚ ≤ kT → eraseCase e (entropyDrop L ρ) →
  ½ * (kT * visibility² ρ) ≤ kT * dissipatedEntropy e
erase-pathRecord-cost-ge-visibility-sq L e ρ kT hk h =
  ≤-trans (*-monoˡ-≤-nonNeg ½ (mono-kT kT hk v≤))
          (erase-pathRecord-cost-ge-complementarity L e ρ kT hk h)
  where
  v≤ : visibility² ρ ≤ 1ℚ - distinguishability² ρ
  v≤ = ≤-trans (≤-reflexive (sym (add-sub-cancelʳ (visibility² ρ) (distinguishability² ρ))))
               (+-monoˡ-≤ (- distinguishability² ρ) (englert ρ))

-- The Szilard balance on the path qubit: measure the path with feedback at no free-energy change, then erase the
-- record at the same bath; the extracted work is at most the erasure work.
measure-then-erase-no-net-work : ∀ L ρ f e → 0ℚ ≤ kBT f → deltaFreeEnergy f ≡ 0ℚ →
  measureFeedbackCase f (mutualInformation (ln L) (pathRecordJoint ρ)) → eraseCase e (entropyDrop L ρ) →
  extWork f ≤ kBT f * dissipatedEntropy e
measure-then-erase-no-net-work L ρ f e hk hF hm he =
  ≤-trans hm (≤-trans (≤-reflexive eq) (erase-pathRecord-cost-ge-bits L e ρ (kBT f) hk he))
  where
  eq : (- deltaFreeEnergy f) + kBT f * mutualInformation (ln L) (pathRecordJoint ρ) ≡ kBT f * vonNeumannDiagonal L ρ
  eq = trans (cong (λ d → (- d) + kBT f * mutualInformation (ln L) (pathRecordJoint ρ)) hF)
             (trans (cong (λ m → (- 0ℚ) + kBT f * m) (pathRecordJoint-mutualInformation L ρ))
                    (zero-neg-add (kBT f * vonNeumannDiagonal L ρ)))

-- The reset of LandauerBound: an initial state, a dissipated heat, and its Landauer bound.
record ResetProcess (L : PathLog) (kT : ℚ) : Set where
  field
    initial        : DensityMatrix2
    dissipatedHeat : ℚ
    resetBound     : landauerCostDiagonal L kT initial ≤ dissipatedHeat

-- The reset whose heat is the erasure work in joules takes its bound from the erase case.
resetProcess-of-secondLaw : ∀ L e ρ kT → 0ℚ ≤ kT → eraseCase e (entropyDrop L ρ) → ResetProcess L kT
resetProcess-of-secondLaw L e ρ kT hk h = record
  { initial = ρ ; dissipatedHeat = kT * dissipatedEntropy e ; resetBound = erase-pathRecord-cost-ge-bits L e ρ kT hk h }

------------------------------------------------------------------------
-- The measurement channel: the Lüders which-path map
------------------------------------------------------------------------

-- The Lüders which-path channel keeps the Born weights and removes the coherence.
whichPathApply : DensityMatrix2 → DensityMatrix2
whichPathApply ρ = mkDensityMatrix2 (p₀ ρ) (p₁ ρ) 0ℚ (p₀-nonneg ρ) (p₁-nonneg ρ) (trace-one ρ) ≤-refl
  (nonNegative⁻¹ (p₀ ρ * p₁ ρ) {{nonNeg*nonNeg⇒nonNeg (p₀ ρ) {{nonNegative (p₀-nonneg ρ)}} (p₁ ρ) {{nonNegative (p₁-nonneg ρ)}}}})

fringeVisibility-whichPath-apply : ∀ ρ → visibility² (whichPathApply ρ) ≡ 0ℚ
fringeVisibility-whichPath-apply ρ = refl

measurementCost-le-landauerBitEnergy : ∀ L p ρ kT → 0ℚ ≤ kT → measurementCost L p ρ kT ≤ landauerBitEnergy L kT
measurementCost-le-landauerBitEnergy L p ρ kT hk = mono-kT kT hk (EpistemicMI-le-ln2 L p ρ)
