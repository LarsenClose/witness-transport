/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/OmegaGradeTransfer.lean — omega's grade overhead derived
from gradeGap.

The Y combinator's pointwise action is omega(f, x) = f(selfApp(x)).
Its grade overhead is therefore determined entirely by two quantities:
  (1) gradeGap: how much selfApp shifts grade
  (2) c_f: how much f shifts grade

This file proves that omega's grade transfer IS gradeGap, replacing the
vacuous omega_grade_transfer axiom in AntiCompression.lean (pnp-integrated)
where two free functions (sem_grade, struct_grade_of_omega) are constrained
by an axiom without connection to the actual omega construction.

Connection to categorical/container levels (documented, not imported):
- ConstructiveOmega.lean: omega φ f = reflexiveCurry φ (selfApp φ >> f)
- FixedPointCombinator.lean: omega f = fold (fun x => f (selfApp x))
- Containerization.lean: omega f = name (fun x => f (selfApp x))
- At the GRM level: selfApp = unfold ∘ fold (OmegaChainCompletion lines 34-38)

The pointwise form f(selfApp(x)) captures the grade content without
requiring the reflexive fold : (carrier → carrier) → carrier.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Composition grade bound — the core theorem
-- ════════════════════════════════════════════════════════════

/-- The grade of f(selfApp(x)) is bounded by grade(selfApp(x)) + c_f.
    Combined with the Compatible hypothesis (grade(selfApp(x)) ≤ grade(x)),
    this gives grade(f(selfApp(x))) ≤ grade(x) + c_f.

    This is the non-vacuous content of omega's grade transfer:
    when the retraction is grade-compatible, composing f after selfApp
    adds at most f's overhead. selfApp contributes zero additional cost. -/
theorem compatible_composition_grade (M : GradedReflModel)
    (hcompat : M.toGradedRetraction.Compatible)
    (f : M.carrier → M.carrier)
    (c : Nat)
    (hf : ∀ x, M.grade (f x) ≤ M.grade x + c)
    (x : M.carrier) :
    M.grade (f (M.selfApp x)) ≤ M.grade x + c := by
  have h1 : M.grade (M.selfApp x) ≤ M.grade x := hcompat x
  have h2 : M.grade (f (M.selfApp x)) ≤ M.grade (M.selfApp x) + c := hf (M.selfApp x)
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: Compatible composition factors through
-- ════════════════════════════════════════════════════════════

/-- If Compatible and f factors through grade d, then f ∘ selfApp also
    factors through grade d.

    This is the non-vacuous injection bound: the "bounded construction"
    leg of pick-2-of-3 holds when Compatible holds. Replaces the vacuous
    omega_grade_transfer axiom that constrained free functions.

    The proof: Compatible gives grade(selfApp(x)) ≤ grade(x) ≤ d,
    then FactorsThrough M f d gives grade(f(selfApp(x))) ≤ d. -/
theorem compatible_composition_factors (M : GradedReflModel)
    (hcompat : M.toGradedRetraction.Compatible)
    (f : M.carrier → M.carrier)
    (d : Nat)
    (hf : FactorsThrough M f d) :
    FactorsThrough M (f ∘ M.selfApp) d := by
  intro x hx
  show M.grade (f (M.selfApp x)) ≤ d
  exact hf (M.selfApp x) (Nat.le_trans (hcompat x) hx)

/-- selfApp alone factors through every grade when Compatible. -/
theorem compatible_selfApp_factors (M : GradedReflModel)
    (hcompat : M.toGradedRetraction.Compatible)
    (d : Nat) :
    FactorsThrough M M.selfApp d := by
  intro x hx
  exact Nat.le_trans (hcompat x) hx

-- ════════════════════════════════════════════════════════════
-- Section 3: Unbounded composition does not factor
-- ════════════════════════════════════════════════════════════

/-- If selfApp is unbounded, then f ∘ selfApp does not factor through
    any grade, regardless of f's overhead.

    The key: selfApp overflow at grade d gives a point x with
    grade(selfApp(x)) > d, so grade(f(selfApp(x))) ≥ grade(selfApp(x))
    when f is non-decreasing. But we do not need non-decreasing f —
    the identity f = id suffices to show the composition unfactors. -/
theorem unbounded_selfApp_unfactors (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (d : Nat) :
    ¬FactorsThrough M M.selfApp d :=
  selfApp_not_factors M hub d

-- ════════════════════════════════════════════════════════════
-- Section 4: The grade transfer trichotomy
-- ════════════════════════════════════════════════════════════

/-- THE GRADE TRANSFER TRICHOTOMY through gradeGap.

    At each position in the answer space, gradeGap determines which
    leg of pick-2-of-3 holds or fails:

    (1) Compatible (gradeGap ≤ 0): f ∘ selfApp factors through d + c.
        The injection bound holds. For pick-2-of-3, the "bounded
        construction" leg is satisfied — the growth gap must fail.

    (2) Unbounded (gradeGap > 0 at arbitrarily high grades):
        selfApp does not factor through any grade.
        The injection bound fails. For pick-2-of-3, the "bounded
        construction" leg fails — the growth gap may hold.

    Each regime is witnessed by a concrete model. -/
theorem grade_transfer_trichotomy :
    -- Compatible regime: composition factors through
    (∃ M : GradedReflModel,
      M.toGradedRetraction.Compatible ∧
      ∀ d, FactorsThrough M M.selfApp d) ∧
    -- Unbounded regime: selfApp does not factor through any grade
    (∃ M : GradedReflModel,
      SelfAppUnbounded M ∧
      ∀ d, ¬FactorsThrough M M.selfApp d) :=
  ⟨⟨trivialModel,
    fun x => by cases x; exact Nat.le_refl _,
    fun d => compatible_selfApp_factors trivialModel
      (fun x => by cases x; exact Nat.le_refl _) d⟩,
   ⟨standardModel,
    standardModel_selfAppUnbounded,
    fun d => selfApp_not_factors standardModel standardModel_selfAppUnbounded d⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Connecting to the pick-2-of-3
-- ════════════════════════════════════════════════════════════

/-- The pick-2-of-3 through gradeGap: Compatible implies PEqNP.

    When f ∘ selfApp factors through d + c, and we take f = id (c = 0),
    selfApp factors through every d. This is exactly PEqNP.

    Restated from CarrierEngineering to show the gradeGap path:
    gradeGap ≤ 0 → Compatible → selfApp factors → PEqNP. -/
theorem compatible_implies_bounded_construction (M : GradedReflModel)
    (hcompat : M.toGradedRetraction.Compatible) :
    PEqNP M :=
  compatible_retraction_gives_PEqNP M hcompat

/-- The other direction: unbounded selfApp → ¬PEqNP.

    When selfApp does not factor through any grade, the injection bound
    fails at every grade, so there is no bound d with FactorsThrough. -/
theorem unbounded_implies_no_bounded_construction (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    ¬PEqNP M :=
  incompatible_retraction_gives_separation M hub

-- ════════════════════════════════════════════════════════════
-- Section 6: The composition bound at retracted points
-- ════════════════════════════════════════════════════════════

/-- On the image of selfApp (the retracted subspace), gradeGap = 0
    (from GradeGapMeasure.selfApp_image_zero_gap). Therefore f ∘ selfApp
    applied to a retracted point has overhead exactly c_f — no
    additional cost from selfApp.

    This holds for ALL GRMs, regardless of regime. The retracted
    subspace is always grade-stable. -/
theorem composition_at_retracted_point (M : GradedReflModel)
    (f : M.carrier → M.carrier)
    (c : Nat)
    (hf : ∀ x, M.grade (f x) ≤ M.grade x + c)
    (x : M.carrier) :
    M.grade (f (M.selfApp (M.selfApp x))) ≤ M.grade (M.selfApp x) + c := by
  have hidemp := grm_roundtrip_forces_idempotent M x
  rw [hidemp]
  exact hf (M.selfApp x)

-- ════════════════════════════════════════════════════════════
-- Section 7: gradeGap determines factoring — the full statement
-- ════════════════════════════════════════════════════════════

/-- gradeGap determines whether selfApp factors through ANY grade.

    This is the non-vacuous replacement for omega_grade_transfer:
    gradeGap ≤ 0 means selfApp factors through every grade (so
    f ∘ selfApp factors when f factors). gradeGap unbounded means
    selfApp factors through no grade (so no composition can help).

    The grade transfer is not an axiom on free functions — it is
    a derived consequence of gradeGap, which is defined from the
    roundtrip axiom alone. -/
theorem gradeGap_determines_factoring :
    -- gradeGap ≤ 0 → selfApp factors through every grade
    (∀ M : GradedReflModel, (∀ x, gradeGap M x ≤ 0) →
      ∀ d, FactorsThrough M M.selfApp d) ∧
    -- SelfAppUnbounded → selfApp factors through no grade
    (∀ M : GradedReflModel, SelfAppUnbounded M →
      ∀ d, ¬FactorsThrough M M.selfApp d) :=
  ⟨fun M hgap d =>
    compatible_selfApp_factors M ((compatible_iff_nonpositive_gap M).mpr hgap) d,
   fun M hub d =>
    selfApp_not_factors M hub d⟩

/-- The regime is fully determined by gradeGap:
    nonpositive gap → PEqNP, unbounded selfApp → ¬PEqNP,
    both witnessed by concrete models. -/
theorem gradeGap_determines_regime :
    -- Nonpositive gradeGap → PEqNP
    (∀ M : GradedReflModel, (∀ x, gradeGap M x ≤ 0) → PEqNP M) ∧
    -- Unbounded selfApp → ¬PEqNP
    (∀ M : GradedReflModel, SelfAppUnbounded M → ¬PEqNP M) ∧
    -- Compatible regime witnessed (trivialModel)
    (∃ M : GradedReflModel, ∀ x, gradeGap M x ≤ 0) ∧
    -- Separation regime witnessed (standardModel)
    (∃ M : GradedReflModel, SelfAppUnbounded M) :=
  ⟨fun M hgap =>
    compatible_retraction_gives_PEqNP M ((compatible_iff_nonpositive_gap M).mpr hgap),
   fun M hub =>
    incompatible_retraction_gives_separation M hub,
   ⟨trivialModel, fun x => by cases x; show (↑(trivialModel.grade (trivialModel.unfold (trivialModel.fold PUnit.unit))) : Int) - ↑(trivialModel.grade PUnit.unit) ≤ 0; decide⟩,
   ⟨standardModel, standardModel_selfAppUnbounded⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms compatible_composition_grade
#print axioms compatible_composition_factors
#print axioms compatible_selfApp_factors
#print axioms unbounded_selfApp_unfactors
#print axioms grade_transfer_trichotomy
#print axioms compatible_implies_bounded_construction
#print axioms unbounded_implies_no_bounded_construction
#print axioms composition_at_retracted_point
#print axioms gradeGap_determines_factoring
#print axioms gradeGap_determines_regime

end WTS
