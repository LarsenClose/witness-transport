/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/DeficitEquivalence.lean — Contraction deficit as Nat decomposition
of gradeGap, connecting to carrier engineering compatibility.

gradeGap (Int) decomposes into two Nat quantities:
  - gradeDeficit: grade(selfApp(x)) - grade(x), saturating at 0
    (the upward cost — how much selfApp increases grade)
  - gradeShortfall: grade(x) - grade(selfApp(x)), saturating at 0
    (the downward shift — how much selfApp decreases grade)

The deficit is the Nat-resolution view of the same data gradeGap measures
in Int. Compatible (CarrierEngineering) is equivalent to gradeDeficit = 0
everywhere: the retraction never increases grade.

Connection to BLL contraction deficit (Level 2 observation, not formal import):
  PNP/BLL/BLLBridge.lean defines contractionDeficit measuring resource
  duplication cost in linear logic terms. gradeDeficit measures the same
  phenomenon — distance from identity — at the GRM level. The BLL deficit
  counts contraction rule applications; gradeDeficit counts grade shift.
  Both are zero iff the operation preserves resources/grade exactly.
  The correspondence is structural, not imported across projects.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Tower.CarrierEngineering

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Nat decomposition of gradeGap
-- ════════════════════════════════════════════════════════════

/-- The grade deficit at a point: how much selfApp increases grade.
    Nat saturating subtraction: 0 when selfApp does not increase grade.

    gradeDeficit(M, x) = grade(selfApp(x)) - grade(x)  (in Nat, saturating)

    This is the positive part of gradeGap. -/
def gradeDeficit (M : GradedReflModel) (x : M.carrier) : Nat :=
  M.grade (M.selfApp x) - M.grade x

/-- The grade shortfall at a point: how much selfApp decreases grade.
    Nat saturating subtraction: 0 when selfApp does not decrease grade.

    gradeShortfall(M, x) = grade(x) - grade(selfApp(x))  (in Nat, saturating)

    This is the negative part of gradeGap (negated to Nat). -/
def gradeShortfall (M : GradedReflModel) (x : M.carrier) : Nat :=
  M.grade x - M.grade (M.selfApp x)

-- ════════════════════════════════════════════════════════════
-- Section 2: Relationship between deficit, shortfall, and gradeGap
-- ════════════════════════════════════════════════════════════

/-- gradeGap = deficit - shortfall (as Int). The two Nat quantities
    reconstruct the Int-valued gradeGap exactly. -/
theorem gradeGap_eq_deficit_sub_shortfall (M : GradedReflModel) (x : M.carrier) :
    gradeGap M x = (gradeDeficit M x : Int) - (gradeShortfall M x : Int) := by
  simp only [gradeGap, gradeDeficit, gradeShortfall]
  omega

/-- Deficit and shortfall cannot both be positive: at least one is 0.
    This is immediate from Nat subtraction: if a ≥ b then b - a = 0,
    and if a < b then a - b = 0. -/
theorem deficit_shortfall_exclusive (M : GradedReflModel) (x : M.carrier) :
    gradeDeficit M x = 0 ∨ gradeShortfall M x = 0 := by
  simp only [gradeDeficit, gradeShortfall]
  omega

/-- When gradeGap ≤ 0, the deficit is 0. -/
theorem nonpositive_gap_zero_deficit (M : GradedReflModel) (x : M.carrier)
    (h : gradeGap M x ≤ 0) : gradeDeficit M x = 0 := by
  simp only [gradeGap, gradeDeficit] at *; omega

/-- When gradeGap ≥ 0, the shortfall is 0. -/
theorem nonnegative_gap_zero_shortfall (M : GradedReflModel) (x : M.carrier)
    (h : gradeGap M x ≥ 0) : gradeShortfall M x = 0 := by
  simp only [gradeGap, gradeShortfall] at *; omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Deficit = 0 iff selfApp does not increase grade
-- ════════════════════════════════════════════════════════════

/-- Deficit = 0 iff grade(selfApp(x)) ≤ grade(x).
    Note: this is ≤, not =. Deficit = 0 means "no upward cost",
    which allows selfApp to decrease grade. -/
theorem deficit_zero_iff_le (M : GradedReflModel) (x : M.carrier) :
    gradeDeficit M x = 0 ↔ M.grade (M.selfApp x) ≤ M.grade x := by
  simp only [gradeDeficit]; omega

/-- Shortfall = 0 iff grade(selfApp(x)) ≥ grade(x). -/
theorem shortfall_zero_iff_ge (M : GradedReflModel) (x : M.carrier) :
    gradeShortfall M x = 0 ↔ M.grade (M.selfApp x) ≥ M.grade x := by
  simp only [gradeShortfall]; omega

/-- Both deficit and shortfall = 0 iff selfApp preserves grade exactly. -/
theorem deficit_and_shortfall_zero_iff_eq (M : GradedReflModel) (x : M.carrier) :
    gradeDeficit M x = 0 ∧ gradeShortfall M x = 0 ↔
    M.grade (M.selfApp x) = M.grade x := by
  simp only [gradeDeficit, gradeShortfall]; omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Compatible iff deficit = 0 everywhere
-- ════════════════════════════════════════════════════════════

/-- Compatible iff gradeDeficit = 0 at every point.

    Compatible says grade(selfApp(x)) ≤ grade(x) for all x.
    Deficit = 0 says the same thing pointwise.
    This is the Nat-resolution restatement of compatible_iff_nonpositive_gap. -/
theorem compatible_iff_zero_deficit (M : GradedReflModel) :
    M.toGradedRetraction.Compatible ↔ ∀ x, gradeDeficit M x = 0 := by
  constructor
  · intro hcompat x
    exact (deficit_zero_iff_le M x).mpr (hcompat x)
  · intro hdef x
    exact (deficit_zero_iff_le M x).mp (hdef x)

/-- Connecting the two characterizations: nonpositive gap ↔ zero deficit.
    The Int and Nat views agree. -/
theorem nonpositive_gap_iff_zero_deficit (M : GradedReflModel) :
    (∀ x, gradeGap M x ≤ 0) ↔ (∀ x, gradeDeficit M x = 0) := by
  constructor
  · intro h x; exact nonpositive_gap_zero_deficit M x (h x)
  · intro h x
    have := (deficit_zero_iff_le M x).mp (h x)
    simp only [gradeGap]; omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Group B — nonzero shortfall characterization
-- ════════════════════════════════════════════════════════════

/-- Group B has zero deficit (Compatible) but nonzero shortfall at some point.
    The shortfall measures how much grade selfApp actually removes —
    the "work" the retraction does. Group C has shortfall = 0 everywhere
    (selfApp = id preserves grade exactly). -/
theorem groupB_zero_deficit_nonzero_shortfall :
    ∃ M : GradedReflModel,
      (∀ x, gradeDeficit M x = 0) ∧
      (∃ x, gradeShortfall M x ≠ 0) := by
  refine ⟨retractionModel, ?_, ?_⟩
  · intro x
    exact (deficit_zero_iff_le retractionModel x).mpr
      (retractionModel_selfApp_grade_le x)
  · refine ⟨(1 : Nat), ?_⟩
    simp only [gradeShortfall, GradedReflModel.selfApp, retractionModel, id]
    decide

/-- Group C has zero deficit AND zero shortfall everywhere.
    selfApp = id means grade is exactly preserved. -/
theorem groupC_zero_deficit_zero_shortfall :
    ∀ x, gradeDeficit trivialModel x = 0 ∧ gradeShortfall trivialModel x = 0 := by
  intro x
  exact (deficit_and_shortfall_zero_iff_eq trivialModel x).mpr
    (by rw [trivial_selfApp_eq_id])

-- ════════════════════════════════════════════════════════════
-- Section 6: Unbounded deficit — the separation regime
-- ════════════════════════════════════════════════════════════

/-- Unbounded selfApp implies nonzero deficit at arbitrarily high grades. -/
theorem unbounded_implies_nonzero_deficit (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ∀ d, ∃ x, M.grade x ≤ d ∧ gradeDeficit M x > 0 := by
  intro d
  obtain ⟨x, hle, hgt⟩ := h.overflows d
  exact ⟨x, hle, by simp only [gradeDeficit]; omega⟩

/-- Nonzero deficit at any point implies not Compatible. -/
theorem nonzero_deficit_not_compatible (M : GradedReflModel)
    (x : M.carrier) (h : gradeDeficit M x > 0) :
    ¬M.toGradedRetraction.Compatible := by
  rw [compatible_iff_zero_deficit]
  intro hall
  have := hall x; omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Deficit at retracted points
-- ════════════════════════════════════════════════════════════

/-- On the image of selfApp, both deficit and shortfall are 0.
    selfApp is idempotent, so grade(selfApp(selfApp(x))) = grade(selfApp(x)).
    The retracted subspace is always deficit-free, regardless of regime. -/
theorem retracted_point_zero_deficit (M : GradedReflModel) (x : M.carrier) :
    gradeDeficit M (M.selfApp x) = 0 ∧ gradeShortfall M (M.selfApp x) = 0 :=
  (deficit_and_shortfall_zero_iff_eq M (M.selfApp x)).mpr
    (by have := grm_roundtrip_forces_idempotent M x
        show M.grade (M.selfApp (M.selfApp x)) = M.grade (M.selfApp x)
        rw [this])

-- ════════════════════════════════════════════════════════════
-- Section 8: The deficit trichotomy
-- ════════════════════════════════════════════════════════════

/-- THE DEFICIT TRICHOTOMY: three regimes via Nat-valued deficit.

    (1) Zero deficit, zero shortfall: selfApp preserves grade exactly (Group C)
    (2) Zero deficit, nonzero shortfall: selfApp decreases grade (Group B)
    (3) Nonzero deficit at unbounded grades: selfApp increases grade (separation)

    This is the Nat-resolution restatement of the gap trichotomy. -/
theorem deficit_trichotomy :
    -- Zero deficit + zero shortfall (Group C)
    (∃ M : GradedReflModel,
      (∀ x, gradeDeficit M x = 0) ∧ (∀ x, gradeShortfall M x = 0)) ∧
    -- Zero deficit + nonzero shortfall (Group B)
    (∃ M : GradedReflModel,
      (∀ x, gradeDeficit M x = 0) ∧ (∃ x, gradeShortfall M x ≠ 0)) ∧
    -- Nonzero deficit at unbounded grades (separation)
    (∃ M : GradedReflModel,
      ∀ d, ∃ x, M.grade x ≤ d ∧ gradeDeficit M x > 0) :=
  ⟨⟨trivialModel, fun x => (groupC_zero_deficit_zero_shortfall x).1,
                   fun x => (groupC_zero_deficit_zero_shortfall x).2⟩,
   groupB_zero_deficit_nonzero_shortfall,
   ⟨standardModel,
    unbounded_implies_nonzero_deficit standardModel standardModel_selfAppUnbounded⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: Deficit and PEqNP
-- ════════════════════════════════════════════════════════════

/-- Zero deficit everywhere implies PEqNP (via Compatible). -/
theorem zero_deficit_implies_PEqNP (M : GradedReflModel)
    (h : ∀ x, gradeDeficit M x = 0) :
    PEqNP M :=
  compatible_retraction_gives_PEqNP M
    ((compatible_iff_zero_deficit M).mpr h)

/-- Unbounded deficit implies not PEqNP (via separation). -/
theorem unbounded_deficit_implies_separation (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ¬PEqNP M :=
  incompatible_retraction_gives_separation M h

-- ════════════════════════════════════════════════════════════
-- Section 10: GroupBData and deficit
-- ════════════════════════════════════════════════════════════

/-- GroupBData's red_grade_le is exactly zero deficit for the retraction.
    The "red" function in Group B chains has zero deficit by construction.
    This is what it means for ModelData to have been identified:
    a concrete retraction with zero deficit is known.

    Stated at the GradedRetraction level: Compatible (which GroupBData
    provides via red_grade_le) is equivalent to zero deficit. -/
theorem groupBData_compatible_iff_zero_deficit {α : Type} (gb : GroupBData α) :
    gb.toGradedRetraction.Compatible ↔
    ∀ x, gb.grade (gb.retract x) - gb.grade x = 0 := by
  constructor
  · intro hcompat x; have := hcompat x; omega
  · intro h x; have := h x; omega

/-- GroupBData always has zero deficit (from red_grade_le). -/
theorem groupBData_has_zero_deficit {α : Type} (gb : GroupBData α) :
    ∀ x, gb.grade (gb.retract x) - gb.grade x = 0 :=
  (groupBData_compatible_iff_zero_deficit gb).mp gb.red_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 11: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms gradeGap_eq_deficit_sub_shortfall
#print axioms deficit_shortfall_exclusive
#print axioms compatible_iff_zero_deficit
#print axioms nonpositive_gap_iff_zero_deficit
#print axioms deficit_trichotomy
#print axioms zero_deficit_implies_PEqNP
#print axioms retracted_point_zero_deficit
#print axioms groupBData_compatible_iff_zero_deficit
#print axioms groupBData_has_zero_deficit

end WTS
