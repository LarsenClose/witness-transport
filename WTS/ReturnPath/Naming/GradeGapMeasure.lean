/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/GradeGapMeasure.lean — gradeGap as the quantitative measure
of distance from identity in the answer space.

gradeGap(M, x) measures how much selfApp shifts grade at each point.
This is the ruler for the return path characterization:
- gradeGap = 0 everywhere: full iso, selfApp = id (Group C)
- gradeGap ≤ 0 everywhere: bounded retraction, Compatible (Group B/C)
- gradeGap > 0 unbounded: separation regime

The key theorem: GradedRetraction.Compatible (CarrierEngineering) is
equivalent to gradeGap ≤ 0 everywhere. This connects the three-group
classification to the quantitative grade dynamics.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Tower.ForcingPredicates
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The grade gap measure
-- ════════════════════════════════════════════════════════════

/-- The grade gap at a point: how much selfApp shifts grade.

    gradeGap(M, x) = grade(selfApp(x)) - grade(x), computed in Int
    to allow negative values (when selfApp decreases grade).

    - Full iso (selfApp = id): gradeGap = 0 everywhere
    - Bounded retraction (selfApp ≠ id, Compatible): gradeGap ≤ 0
    - Separation (SelfAppUnbounded): gradeGap > 0 at arbitrarily high grades

    This is the formal ruler for the return path characterization.
    Adapted from PNP/Foundations/ReflexiveToGraded.lean (pnp-integrated). -/
def gradeGap (M : GradedReflModel) (x : M.carrier) : Int :=
  (M.grade (M.selfApp x) : Int) - (M.grade x : Int)

-- ════════════════════════════════════════════════════════════
-- Section 2: Compatible ↔ nonpositive gap
-- ════════════════════════════════════════════════════════════

/-- Compatible retraction iff gradeGap ≤ 0 everywhere.

    This is the bridge between CarrierEngineering's predicate
    classification and the quantitative grade dynamics. Compatible
    says "the retraction doesn't increase grade." gradeGap ≤ 0 says
    "selfApp shifts grade downward or not at all." These are the
    same condition, restated. -/
theorem compatible_iff_nonpositive_gap (M : GradedReflModel) :
    M.toGradedRetraction.Compatible ↔ ∀ x, gradeGap M x ≤ 0 := by
  constructor
  · intro h x
    have hle := h x
    simp only [gradeGap, GradedReflModel.toGradedRetraction] at *
    omega
  · intro h x
    have hx := h x
    simp only [gradeGap, GradedReflModel.toGradedRetraction] at *
    omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Group C — zero gap
-- ════════════════════════════════════════════════════════════

/-- selfApp = id implies gradeGap = 0 everywhere. -/
theorem selfApp_eq_id_zero_gap (M : GradedReflModel)
    (h : ∀ x, M.selfApp x = x) (x : M.carrier) :
    gradeGap M x = 0 := by
  simp only [gradeGap, h x]; omega

/-- gradeGap = 0 everywhere implies selfApp preserves grade exactly. -/
theorem zero_gap_preserves_grade (M : GradedReflModel)
    (h : ∀ x, gradeGap M x = 0) (x : M.carrier) :
    M.grade (M.selfApp x) = M.grade x := by
  have := h x
  simp only [gradeGap] at this
  omega

/-- Group C witness: trivialModel has zero gap everywhere. -/
theorem trivialModel_zero_gap :
    ∀ x, gradeGap trivialModel x = 0 :=
  selfApp_eq_id_zero_gap trivialModel trivial_selfApp_eq_id

-- ════════════════════════════════════════════════════════════
-- Section 4: Group B — nonpositive gap, not always zero
-- ════════════════════════════════════════════════════════════

/-- retractionModel has nonpositive gap everywhere. -/
theorem retractionModel_nonpositive_gap :
    ∀ x, gradeGap retractionModel x ≤ 0 := by
  intro x
  have := retractionModel_selfApp_grade_le x
  simp only [gradeGap, GradedReflModel.selfApp] at *
  omega

/-- retractionModel has strictly negative gap at x = 1.
    selfApp(1) = 2*(1/2) = 0, grade(0) = 0, grade(1) = 1.
    gradeGap = 0 - 1 = -1 < 0. -/
theorem retractionModel_negative_gap_at_one :
    gradeGap retractionModel (1 : Nat) < 0 := by
  simp only [gradeGap, GradedReflModel.selfApp, retractionModel, id]
  decide

/-- retractionModel is Compatible (immediate from nonpositive gap). -/
theorem retractionModel_compatible :
    retractionModel.toGradedRetraction.Compatible :=
  (compatible_iff_nonpositive_gap retractionModel).mpr
    retractionModel_nonpositive_gap

-- ════════════════════════════════════════════════════════════
-- Section 5: Separation — unbounded positive gap
-- ════════════════════════════════════════════════════════════

/-- SelfAppUnbounded implies gradeGap > 0 at arbitrarily high grades. -/
theorem unbounded_implies_unbounded_gap (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ∀ d, ∃ x, M.grade x ≤ d ∧ gradeGap M x > 0 := by
  intro d
  obtain ⟨x, hle, hgt⟩ := h.overflows d
  exact ⟨x, hle, by simp only [gradeGap]; omega⟩

/-- Unbounded positive gap implies not Compatible. -/
theorem unbounded_gap_not_compatible (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ¬M.toGradedRetraction.Compatible := by
  rw [compatible_iff_nonpositive_gap]
  intro hall
  obtain ⟨x, _, hgap⟩ := unbounded_implies_unbounded_gap M h 0
  have := hall x; omega

/-- standardModel has unbounded positive gap. -/
theorem standardModel_unbounded_gap :
    ∀ d, ∃ x, standardModel.grade x ≤ d ∧ gradeGap standardModel x > 0 :=
  unbounded_implies_unbounded_gap standardModel standardModel_selfAppUnbounded

-- ════════════════════════════════════════════════════════════
-- Section 6: The gap trichotomy
-- ════════════════════════════════════════════════════════════

/-- THE GAP TRICHOTOMY: three regimes witnessed by concrete models.

    (1) Zero gap: selfApp = id, gradeGap = 0 everywhere (trivialModel)
    (2) Nonpositive gap with negative points: selfApp ≠ id but Compatible,
        gradeGap ≤ 0 with gradeGap < 0 at some points (retractionModel)
    (3) Unbounded positive gap: selfApp overflows every grade bound,
        gradeGap > 0 at arbitrarily high grades (standardModel)

    These correspond to the three positions in the answer space:
    Group C (identity), Group B (bounded retraction), separation. -/
theorem gap_trichotomy :
    -- Zero gap (Group C)
    (∃ M : GradedReflModel, ∀ x, gradeGap M x = 0) ∧
    -- Nonpositive with negative points (Group B)
    (∃ M : GradedReflModel,
      (∀ x, gradeGap M x ≤ 0) ∧ (∃ x, gradeGap M x < 0)) ∧
    -- Unbounded positive (separation)
    (∃ M : GradedReflModel,
      ∀ d, ∃ x, M.grade x ≤ d ∧ gradeGap M x > 0) :=
  ⟨⟨trivialModel, trivialModel_zero_gap⟩,
   ⟨retractionModel, retractionModel_nonpositive_gap,
    ⟨(1 : Nat), retractionModel_negative_gap_at_one⟩⟩,
   ⟨standardModel, standardModel_unbounded_gap⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Gap and idempotence
-- ════════════════════════════════════════════════════════════

/-- selfApp is idempotent (from roundtrip), so applying it twice
    gives the same gap as applying it once.
    gradeGap(M, selfApp(x)) + gradeGap(M, x) = gradeGap(M, x)
    since selfApp(selfApp(x)) = selfApp(x). -/
theorem gap_at_retracted_point (M : GradedReflModel) (x : M.carrier) :
    gradeGap M (M.selfApp x) = 0 := by
  simp only [gradeGap]
  have := grm_roundtrip_forces_idempotent M x
  rw [this]; omega

/-- The image of selfApp is always in the zero-gap region.
    selfApp is a projection onto the grade-stable subspace. -/
theorem selfApp_image_zero_gap (M : GradedReflModel) :
    ∀ x, gradeGap M (M.selfApp x) = 0 :=
  gap_at_retracted_point M

-- ════════════════════════════════════════════════════════════
-- Section 8: Connecting to CarrierEngineering groups
-- ════════════════════════════════════════════════════════════

/-- Compatible implies PEqNP (via CarrierEngineering). Restated here
    to show the gradeGap path: nonpositive gap → Compatible → PEqNP. -/
theorem nonpositive_gap_implies_PEqNP (M : GradedReflModel)
    (h : ∀ x, gradeGap M x ≤ 0) :
    PEqNP M :=
  compatible_retraction_gives_PEqNP M
    ((compatible_iff_nonpositive_gap M).mpr h)

/-- Unbounded gap implies ¬PEqNP (separation). -/
theorem unbounded_gap_implies_separation (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ¬PEqNP M :=
  incompatible_retraction_gives_separation M h

-- ════════════════════════════════════════════════════════════
-- Section 9: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms compatible_iff_nonpositive_gap
#print axioms gap_trichotomy
#print axioms selfApp_image_zero_gap
#print axioms nonpositive_gap_implies_PEqNP

end WTS
