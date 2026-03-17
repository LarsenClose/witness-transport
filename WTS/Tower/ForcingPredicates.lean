/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ForcingPredicates.lean — The forcing gap: bounded-idempotent, not identity.

The forcing argument pushes selfApp into the bounded-idempotent region,
NOT all the way to selfApp = id. Forcing identity would be proving P=NP,
which contradicts conservativity (both regimes are consistent).

The gap between bounded-idempotent and identity IS the answer space.
Different retractions correspond to different possible resolutions.

STATUS: 0 sorry.
-/

import WTS.Core
import WTS.Tower.ClassicalModels

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The retraction model — bounded-idempotent, not identity
-- ════════════════════════════════════════════════════════════

/-- Retraction model: Nat carrier, fold = ÷2, unfold = 2×.
    selfApp rounds down to even: selfApp(x) = 2⌊x/2⌋.
    Bounded (grade-non-increasing) and idempotent, but ≠ id.
    Witnesses the gap between bounded-idempotent and identity. -/
def retractionModel : GradedReflModel where
  carrier := Nat
  fold x := x / 2
  unfold x := 2 * x
  roundtrip x := by show (2 * x) / 2 = x; omega
  grade := id

/-- selfApp is idempotent in retractionModel. -/
theorem retractionModel_selfApp_idempotent :
    ∀ x, retractionModel.selfApp (retractionModel.selfApp x) =
         retractionModel.selfApp x := by
  intro x
  simp only [GradedReflModel.selfApp, retractionModel]
  omega

/-- selfApp is grade-non-increasing: grade(selfApp(x)) ≤ grade(x). -/
theorem retractionModel_selfApp_grade_le :
    ∀ x, retractionModel.grade (retractionModel.selfApp x) ≤
         retractionModel.grade x := by
  intro x
  simp only [GradedReflModel.selfApp, retractionModel, id]
  omega

/-- selfApp factors through every grade level in retractionModel. -/
theorem retractionModel_selfApp_bounded (d : Nat) :
    FactorsThrough retractionModel retractionModel.selfApp d := by
  intro x hx
  exact Nat.le_trans (retractionModel_selfApp_grade_le x) hx

/-- PEqNP holds in retractionModel. -/
theorem retractionModel_PEqNP : PEqNP retractionModel :=
  ⟨0, retractionModel_selfApp_bounded 0⟩

/-- selfApp ≠ id in retractionModel: selfApp(1) = 0 ≠ 1. -/
theorem retractionModel_selfApp_ne_id :
    ∃ x, retractionModel.selfApp x ≠ x := by
  refine ⟨(1 : Nat), ?_⟩
  simp only [GradedReflModel.selfApp, retractionModel]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: The gap theorem
-- ════════════════════════════════════════════════════════════

/-- THE GAP THEOREM: bounded-idempotent does not force identity.

    There exists a GradedReflModel where:
    (1) selfApp is idempotent (structural, from roundtrip)
    (2) selfApp is bounded (PEqNP holds)
    (3) selfApp ≠ id (nontrivial retraction)

    The gap between (1)+(2) and selfApp=id IS the answer space.
    Different retractions in this gap correspond to different
    possible resolutions of P vs NP. -/
theorem bounded_idempotent_not_forces_identity :
    ∃ (M : GradedReflModel),
      (∀ x, M.selfApp (M.selfApp x) = M.selfApp x) ∧
      PEqNP M ∧
      (∃ x, M.selfApp x ≠ x) :=
  ⟨retractionModel,
   retractionModel_selfApp_idempotent,
   retractionModel_PEqNP,
   retractionModel_selfApp_ne_id⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Three-regime conservativity
-- ════════════════════════════════════════════════════════════

/-- Three regimes coexist, witnessed by concrete models:

    (1) Identity retraction: selfApp = id, PEqNP trivially (trivialModel)
    (2) Nontrivial bounded retraction: selfApp ≠ id but PEqNP (retractionModel)
    (3) Unbounded selfApp: SelfAppUnbounded, ¬PEqNP (standardModel)

    The forcing argument constrains valid resolutions to regime (1) or (2).
    Regime (3) is the separation case. The gap between (1) and (2) is
    the formal content — not a deficiency. -/
theorem three_regime_conservativity :
    -- Regime 1: identity retraction
    (∃ M : GradedReflModel, (∀ x, M.selfApp x = x) ∧ PEqNP M) ∧
    -- Regime 2: nontrivial bounded retraction
    (∃ M : GradedReflModel, (∃ x, M.selfApp x ≠ x) ∧ PEqNP M) ∧
    -- Regime 3: unbounded (separation)
    (∃ M : GradedReflModel, SelfAppUnbounded M) :=
  ⟨⟨trivialModel, trivial_selfApp_eq_id,
    ⟨0, fun x hx => by rw [trivial_selfApp_eq_id]; exact hx⟩⟩,
   ⟨retractionModel, retractionModel_selfApp_ne_id, retractionModel_PEqNP⟩,
   ⟨standardModel, standardModel_selfAppUnbounded⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Forcing predicates — what roundtrip gives you
-- ════════════════════════════════════════════════════════════

/-- Roundtrip forces idempotence at the GRM level.
    This is the structural content: fold ∘ unfold = id implies
    selfApp ∘ selfApp = selfApp. No grade needed. -/
theorem grm_roundtrip_forces_idempotent (M : GradedReflModel) :
    ∀ x, M.selfApp (M.selfApp x) = M.selfApp x := by
  intro x
  show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
  rw [M.roundtrip]

/-- The regime question is NOT forced by roundtrip alone.
    Both bounded and unbounded selfApp are consistent with roundtrip.
    The grade function is what makes the regime distinction askable. -/
theorem regime_not_forced_by_roundtrip :
    (∃ M : GradedReflModel, PEqNP M) ∧
    (∃ M : GradedReflModel, ¬PEqNP M) :=
  ⟨⟨trivialModel, ⟨0, fun x hx => by rw [trivial_selfApp_eq_id]; exact hx⟩⟩,
   ⟨standardModel, fun ⟨d, hd⟩ => by
     obtain ⟨x, hle, hgt⟩ := standardModel_selfAppUnbounded.overflows d
     have := hd x hle; omega⟩⟩

end WTS
