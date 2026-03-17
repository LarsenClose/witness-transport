/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/ProjectionObstruction.lean — Why nontrivial
idempotent canonicalizers cannot be realized as full-carrier selfApp.

The three Group B chains (2, 3, 5) each identify a canonicalization operation
(multilinearReduce, protocol flattening, NNF conversion) that is:
  (a) idempotent
  (b) grade-non-increasing
  (c) nontrivial (not the identity)

If any such operation WERE the selfApp of a full GradedReflModel, then
selfApp would be grade-non-increasing, which directly contradicts
SelfAppUnbounded. This is the projection obstruction: you cannot have
a nontrivial idempotent grade-non-increasing selfApp in a model that
supports separation.

More precisely: the obstruction is not that the canonicalizer exists,
but that realizing it as selfApp = unfold . fold on the FULL carrier
forces the model into the PEqNP regime. The fixed-point set of the
canonicalizer IS the only viable carrier for a separation model, but
on that restricted set the canonicalizer is the identity -- which is
Group C, not Group B.

This file proves the obstruction in full generality, subsuming the
three chain-specific instances.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Tower.ForcingPredicates
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Idempotent normalizer — the common abstraction
-- ════════════════════════════════════════════════════════════

/-- An idempotent normalizer on a graded type: the common structure
    shared by multilinearReduce (Chain 5), protocol flattening (Chain 2),
    and NNF conversion (Chain 3).

    The four fields correspond exactly to the four ModelData fields
    in each chain's PartialLambek file. -/
structure IdempotentNormalizer (α : Type) where
  /-- The normalization map. -/
  normalize : α → α
  /-- The grade function. -/
  grade : α → Nat
  /-- Normalization is idempotent: normalizing twice = normalizing once. -/
  idempotent : ∀ x, normalize (normalize x) = normalize x
  /-- Normalization is grade-non-increasing. -/
  grade_le : ∀ x, grade (normalize x) ≤ grade x

/-- An element is canonical (in the image of normalize) iff it is a
    fixed point of normalize. -/
def IdempotentNormalizer.isCanonical {α : Type}
    (N : IdempotentNormalizer α) (x : α) : Prop :=
  N.normalize x = x

-- ════════════════════════════════════════════════════════════
-- Section 2: Fixed points characterize the canonical subdomain
-- ════════════════════════════════════════════════════════════

/-- Every output of normalize is canonical: normalize(x) is a fixed
    point of normalize, by idempotence. -/
theorem IdempotentNormalizer.normalize_is_canonical {α : Type}
    (N : IdempotentNormalizer α) (x : α) :
    N.isCanonical (N.normalize x) :=
  N.idempotent x

/-- Canonical elements are exactly the fixed points. An element is
    canonical iff normalize fixes it. (This is definitional, but
    stated as a theorem for the record.) -/
theorem IdempotentNormalizer.canonical_iff_fixed {α : Type}
    (N : IdempotentNormalizer α) (x : α) :
    N.isCanonical x ↔ N.normalize x = x :=
  Iff.rfl

/-- On canonical elements, normalize is the identity. -/
theorem IdempotentNormalizer.normalize_on_canonical {α : Type}
    (N : IdempotentNormalizer α) (x : α) (hx : N.isCanonical x) :
    N.normalize x = x :=
  hx

-- ════════════════════════════════════════════════════════════
-- Section 3: Nontriviality — the normalizer is not the identity
-- ════════════════════════════════════════════════════════════

/-- A normalizer is nontrivial when there exists an element that is
    NOT canonical (not a fixed point of normalize). -/
def IdempotentNormalizer.Nontrivial {α : Type}
    (N : IdempotentNormalizer α) : Prop :=
  ∃ x, ¬N.isCanonical x

/-- If normalize is nontrivial, then normalize ≠ id pointwise:
    there exists x with normalize(x) ≠ x. -/
theorem IdempotentNormalizer.nontrivial_ne_id {α : Type}
    (N : IdempotentNormalizer α) (h : N.Nontrivial) :
    ∃ x, N.normalize x ≠ x :=
  h

-- ════════════════════════════════════════════════════════════
-- Section 4: The projection obstruction — grade-non-increasing
--            selfApp forces PEqNP
-- ════════════════════════════════════════════════════════════

/-- THE PROJECTION OBSTRUCTION.

    If a GradedReflModel's selfApp equals some grade-non-increasing
    function, then PEqNP holds. In particular, if selfApp = normalize
    for any IdempotentNormalizer, the model is in the collapse regime.

    This is the unified statement behind chain5_direct_bridge,
    chain2_direct_bridge, and chain3_direct_bridge. It shows that
    realizing a canonicalizer as full-carrier selfApp is incompatible
    with separation.

    Proof: selfApp is grade-non-increasing, so it factors through every
    grade level. FactorsThrough at d = 0 gives PEqNP. -/
theorem projection_forces_PEqNP (M : GradedReflModel)
    (f : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = f x)
    (h_le : ∀ x, M.grade (f x) ≤ M.grade x) :
    PEqNP M :=
  ⟨0, fun x hx => by rw [h_eq]; exact Nat.le_trans (h_le x) hx⟩

/-- Corollary: projection + SelfAppUnbounded is a contradiction.

    If selfApp = f for a grade-non-increasing f, and selfApp is also
    unbounded, we have a direct contradiction. This is the pattern
    used by all three Group B direct bridges. -/
theorem projection_contradicts_unbounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (f : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = f x)
    (h_le : ∀ x, M.grade (f x) ≤ M.grade x) :
    False := by
  obtain ⟨x, hxd, hxsa⟩ := hub.overflows 0
  have : M.grade (M.selfApp x) ≤ M.grade x := by rw [h_eq]; exact h_le x
  omega

/-- The obstruction specialized to IdempotentNormalizer:
    if selfApp = N.normalize for a grade-non-increasing normalizer,
    then PEqNP. -/
theorem normalizer_forces_PEqNP (M : GradedReflModel)
    (N : IdempotentNormalizer M.carrier)
    (h_grade : N.grade = M.grade)
    (h_eq : ∀ x, M.selfApp x = N.normalize x) :
    PEqNP M :=
  projection_forces_PEqNP M N.normalize h_eq
    (fun x => by have := N.grade_le x; rw [h_grade] at this; exact this)

/-- The obstruction + unboundedness: SelfAppUnbounded contradicts
    selfApp being any IdempotentNormalizer. -/
theorem normalizer_contradicts_unbounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (N : IdempotentNormalizer M.carrier)
    (h_grade : N.grade = M.grade)
    (h_eq : ∀ x, M.selfApp x = N.normalize x) :
    False :=
  projection_contradicts_unbounded M hub N.normalize h_eq
    (fun x => by have := N.grade_le x; rw [h_grade] at this; exact this)

-- ════════════════════════════════════════════════════════════
-- Section 5: The restriction dilemma
-- ════════════════════════════════════════════════════════════

/-- On the fixed-point set of a normalizer, the normalizer IS the identity.
    So restricting the carrier to Fix(normalize) eliminates the nontriviality
    that Group B requires. This is the dilemma:

    - Full carrier: selfApp = normalize forces PEqNP (no separation)
    - Restricted carrier: selfApp = id (Group C, not Group B)

    There is no middle ground within the standard GRM structure. -/
theorem restriction_collapses_to_identity
    {α : Type}
    (N : IdempotentNormalizer α)
    (x : α) (hx : N.isCanonical x) :
    N.normalize x = x :=
  hx

/-- The full dilemma: for a nontrivial normalizer, EITHER
    (a) realize it as selfApp on the full carrier (forces PEqNP), OR
    (b) restrict to the canonical subdomain (selfApp = id, Group C).

    No GRM with nontrivial selfApp and SelfAppUnbounded can have
    selfApp = normalize for a grade-non-increasing normalizer. -/
theorem carrier_engineering_dilemma (M : GradedReflModel)
    (N : IdempotentNormalizer M.carrier)
    (h_grade : N.grade = M.grade)
    (h_eq : ∀ x, M.selfApp x = N.normalize x) :
    -- Either selfApp is the identity on the canonical subdomain...
    (∀ x, N.isCanonical x → M.selfApp x = x) ∧
    -- ...and if the normalizer is nontrivial, PEqNP holds on the full carrier
    (N.Nontrivial → PEqNP M) :=
  ⟨fun x hx => by rw [h_eq]; exact hx,
   fun _ => normalizer_forces_PEqNP M N h_grade h_eq⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Concrete witnesses of the obstruction
-- ════════════════════════════════════════════════════════════

/-- The retractionModel (fold = /2, unfold = 2x) witnesses the
    obstruction concretely: selfApp(x) = 2*(x/2) is grade-non-increasing,
    nontrivial, and the model is PEqNP. -/
theorem retractionModel_witnesses_obstruction :
    -- selfApp is grade-non-increasing
    (∀ x, retractionModel.grade (retractionModel.selfApp x) ≤
          retractionModel.grade x) ∧
    -- selfApp is nontrivial (not identity)
    (∃ x, retractionModel.selfApp x ≠ x) ∧
    -- PEqNP holds
    PEqNP retractionModel :=
  ⟨retractionModel_selfApp_grade_le,
   retractionModel_selfApp_ne_id,
   retractionModel_PEqNP⟩

/-- The standardModel witnesses the OTHER side: selfApp is unbounded,
    so no grade-non-increasing function can equal selfApp. -/
theorem standardModel_no_normalizer :
    ∀ (f : Nat → Nat),
      (∀ x, standardModel.selfApp x = f x) →
      (∀ x, standardModel.grade (f x) ≤ standardModel.grade x) →
      False :=
  fun f h_eq h_le =>
    projection_contradicts_unbounded standardModel
      standardModel_selfAppUnbounded f h_eq h_le

-- ════════════════════════════════════════════════════════════
-- Section 7: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms IdempotentNormalizer.normalize_is_canonical
#print axioms IdempotentNormalizer.canonical_iff_fixed
#print axioms projection_forces_PEqNP
#print axioms projection_contradicts_unbounded
#print axioms normalizer_forces_PEqNP
#print axioms normalizer_contradicts_unbounded
#print axioms carrier_engineering_dilemma
#print axioms retractionModel_witnesses_obstruction
#print axioms standardModel_no_normalizer

end WTS
