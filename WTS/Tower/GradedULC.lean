/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/GradedULC.lean — Graded refinement of UniversalLanguageComputer.

Adds a grade function to ULC. Defines regime predicates (bounded/unbounded
selfApp) at the ULC level. Shows GRM = ULC + HasRoundtrip + grade with
shared carrier. The regime question is statable only at this level — bare
ULC sees structural properties (idempotence) but not quantitative ones
(boundedness).

STATUS: 0 sorry.
-/

import WTS.Tower.UniversalLanguageComputer
import WTS.Core
import WTS.Tower.ClassicalModels

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Grade on ULC
-- ════════════════════════════════════════════════════════════

/-- A grade function on a ULC's language type. -/
structure ULCGrade (P : UniversalLanguageComputer) where
  grade : P.Lang → Nat

/-- selfApp is bounded: some grade level contains selfApp outputs
    for inputs at that level. This is PEqNP at the ULC level. -/
def ULCSelfAppBounded (P : UniversalLanguageComputer) (g : ULCGrade P) : Prop :=
  ∃ d, ∀ x, g.grade x ≤ d → g.grade (P.selfApp x) ≤ d

/-- selfApp is unbounded: at every grade level, some input overflows. -/
def ULCSelfAppUnbounded (P : UniversalLanguageComputer) (g : ULCGrade P) : Prop :=
  ∀ d, ∃ x, g.grade x ≤ d ∧ g.grade (P.selfApp x) > d

-- ════════════════════════════════════════════════════════════
-- Section 2: GRM → graded ULC
-- ════════════════════════════════════════════════════════════

/-- Every GRM has a natural grade on its ULC projection. -/
def GradedReflModel.toULCGrade (M : GradedReflModel) : ULCGrade M.toULC where
  grade := M.grade

/-- PEqNP on GRM = ULCSelfAppBounded on its graded ULC. -/
theorem grm_bounded_iff (M : GradedReflModel) :
    PEqNP M ↔ ULCSelfAppBounded M.toULC M.toULCGrade :=
  Iff.rfl

/-- SelfAppUnbounded on GRM ↔ ULCSelfAppUnbounded on its graded ULC. -/
theorem grm_unbounded_iff (M : GradedReflModel) :
    SelfAppUnbounded M ↔ ULCSelfAppUnbounded M.toULC M.toULCGrade :=
  ⟨fun h => h.overflows, fun h => ⟨h⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Regime dichotomy
-- ════════════════════════════════════════════════════════════

/-- Bounded and unbounded are contradictory at the graded ULC level. -/
theorem ulc_regime_contradiction (P : UniversalLanguageComputer) (g : ULCGrade P)
    (hb : ULCSelfAppBounded P g) (hu : ULCSelfAppUnbounded P g) : False := by
  obtain ⟨d, hf⟩ := hb
  obtain ⟨x, hle, hgt⟩ := hu d
  have := hf x hle; omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Conservativity
-- ════════════════════════════════════════════════════════════

/-- Both regimes exist as graded ULC instances with roundtrip.
    The structural type admits both — the regime is not forced. -/
theorem graded_ulc_conservativity :
    (∃ (P : UniversalLanguageComputer) (g : ULCGrade P),
      P.HasRoundtrip ∧ ULCSelfAppBounded P g) ∧
    (∃ (P : UniversalLanguageComputer) (g : ULCGrade P),
      P.HasRoundtrip ∧ ULCSelfAppUnbounded P g) :=
  ⟨⟨trivialModel.toULC, trivialModel.toULCGrade,
    trivialModel.toULC_hasRoundtrip,
    (grm_bounded_iff trivialModel).mp ⟨0, fun x _ => by cases x; exact Nat.zero_le 0⟩⟩,
   ⟨standardModel.toULC, standardModel.toULCGrade,
    standardModel.toULC_hasRoundtrip,
    (grm_unbounded_iff standardModel).mp standardModel_selfAppUnbounded⟩⟩

end WTS
