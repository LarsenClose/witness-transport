/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/CarrierEngineering.lean — Grade-retraction compatibility and the three groups.

What does it mean formally for a grade to be "compatible" with a retraction?
The three groups (A/B/C) are distinguished by which predicates hold:
  - Group C (Chain 7): selfApp = id, always compatible, PEqNP trivially
  - Group B (Chains 5/2/3): ModelData identified (red, red_grade_le),
    both lock and direct bridge available
  - Group A (Chains 1/4/6): lock theorems exist (conditional), Path 1
    applies, no ModelData identified, no direct bridge available

STATUS: 0 sorry.
-/

import WTS.Core
import WTS.Tower.ForcingPredicates

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Grade-retraction compatibility
-- ════════════════════════════════════════════════════════════

/-- An idempotent retraction on a graded type.
    This is the structural data at the ULC level: selfApp is always
    idempotent (from roundtrip), and grade is always present. -/
structure GradedRetraction (α : Type) where
  retract : α → α
  grade : α → Nat
  idempotent : ∀ x, retract (retract x) = retract x

/-- A grade is compatible with a retraction when the retraction
    is grade-non-increasing: grade(r(x)) ≤ grade(x) for all x. -/
def GradedRetraction.Compatible {α : Type} (gr : GradedRetraction α) : Prop :=
  ∀ x, gr.grade (gr.retract x) ≤ gr.grade x

/-- Compatible implies FactorsThrough every grade level (transitivity). -/
theorem GradedRetraction.compatible_factors {α : Type} (gr : GradedRetraction α)
    (h : gr.Compatible) :
    ∀ d x, gr.grade x ≤ d → gr.grade (gr.retract x) ≤ d :=
  fun _ x hx => Nat.le_trans (h x) hx

-- ════════════════════════════════════════════════════════════
-- Section 2: Group C — retraction = id
-- ════════════════════════════════════════════════════════════

/-- Group C retraction: identity. The degenerate point where the
    regime question is vacuous. Chain 7 lives here. -/
def groupC (α : Type) (grade : α → Nat) : GradedRetraction α where
  retract := id
  grade := grade
  idempotent _ := rfl

/-- Group C is always compatible with any grade.
    grade(id(x)) = grade(x) ≤ grade(x). -/
theorem groupC_always_compatible (α : Type) (grade : α → Nat) :
    (groupC α grade).Compatible :=
  fun _ => Nat.le_refl _

-- ════════════════════════════════════════════════════════════
-- Section 3: Group B — known retraction from ModelData
-- ════════════════════════════════════════════════════════════

/-- Group B data: a known retraction with grade-non-increasing property.
    This is the content of ModelData's red + red_grade_le fields.
    Chains 5, 2, 3 each provide this via their specific red function. -/
structure GroupBData (α : Type) extends GradedRetraction α where
  red_grade_le : ∀ x, grade (retract x) ≤ grade x

/-- Group B is compatible by construction: red_grade_le IS compatibility. -/
theorem groupB_compatible {α : Type} (gb : GroupBData α) :
    gb.toGradedRetraction.Compatible :=
  gb.red_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 4: Group A — unknown retraction
-- ════════════════════════════════════════════════════════════

-- Group A IS just GradedRetraction with no extra data.
-- Chains 1, 4, 6: lock theorems exist (conditional on faithfulness
-- + transfer), Path 1 applies, no ModelData identified, no direct
-- bridge available. Compatibility is not stated because no red
-- function has been identified.

-- ════════════════════════════════════════════════════════════
-- Section 5: From GRM to GradedRetraction
-- ════════════════════════════════════════════════════════════

/-- Every GRM yields a GradedRetraction via selfApp.
    Idempotence comes from roundtrip (proved in ForcingPredicates). -/
def GradedReflModel.toGradedRetraction (M : GradedReflModel) :
    GradedRetraction M.carrier where
  retract := M.selfApp
  grade := M.grade
  idempotent := grm_roundtrip_forces_idempotent M

-- ════════════════════════════════════════════════════════════
-- Section 6: Carrier engineering as the regime question
-- ════════════════════════════════════════════════════════════

/-- Compatible retraction → PEqNP.
    If a chain's grade is compatible with its selfApp retraction,
    the chain witnesses P = NP. -/
theorem compatible_retraction_gives_PEqNP (M : GradedReflModel)
    (h_compat : M.toGradedRetraction.Compatible) :
    PEqNP M :=
  ⟨0, M.toGradedRetraction.compatible_factors h_compat 0⟩

/-- Incompatible retraction (selfApp unbounded) → ¬PEqNP. -/
theorem incompatible_retraction_gives_separation (M : GradedReflModel)
    (h : SelfAppUnbounded M) : ¬PEqNP M :=
  fun ⟨d, hd⟩ => by
    obtain ⟨x, hle, hgt⟩ := h.overflows d
    have := hd x hle; omega

/-- The regime trichotomy witnessed by concrete models.
    Each group contributes a different point in the answer space. -/
theorem carrier_engineering_trichotomy :
    -- Group C: identity retraction, always compatible
    (∃ M : GradedReflModel, M.toGradedRetraction.Compatible ∧
      (∀ x, M.selfApp x = x)) ∧
    -- Group B: nontrivial compatible retraction
    (∃ M : GradedReflModel, M.toGradedRetraction.Compatible ∧
      (∃ x, M.selfApp x ≠ x)) ∧
    -- Incompatible: unbounded selfApp
    (∃ M : GradedReflModel, ¬M.toGradedRetraction.Compatible ∧
      SelfAppUnbounded M) :=
  ⟨⟨trivialModel,
    fun x => by cases x; exact Nat.le_refl _,
    trivial_selfApp_eq_id⟩,
   ⟨retractionModel,
    retractionModel_selfApp_grade_le,
    retractionModel_selfApp_ne_id⟩,
   ⟨standardModel,
    fun h => by
      obtain ⟨x, hle, hgt⟩ := standardModel_selfAppUnbounded.overflows 0
      have h1 : standardModel.grade (standardModel.selfApp x) ≤
                standardModel.grade x := h x
      have h2 : standardModel.grade (standardModel.selfApp x) ≤ 0 :=
        Nat.le_trans h1 hle
      omega,
    standardModel_selfAppUnbounded⟩⟩

end WTS
