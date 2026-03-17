/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ClassicalModels.lean — GradedReflModel as UniversalLanguageComputer.

Every GRM is a ULC: Lang = CompModel = carrier, encode = fold, decode = unfold.
The GRM roundtrip axiom IS the ULC HasRoundtrip condition.

The two concrete models in Core.lean become ULC instances:

  trivialModel — carrier = Unit, fold = unfold = id.
    A machine that halts immediately. selfApp = id. No self-interpretation.

  standardModel — carrier = Nat, fold = (÷2), unfold = (2·+1).
    Programs are even numbers (grade 0), execution traces are odd (grade k+1).
    Self-interpretation: selfApp(2k) = 2k+1 — running program k produces
    trace k+1. Unbounded: for any grade d, running program 2d overflows to
    grade d+1. This is the formal content of "universal computation overflows."

Both have roundtrip. Both have idempotent selfApp (structural). The phase
difference is quantitative: one has selfApp = id, the other has selfApp
unbounded. The grade is what makes the regime question askable.

STATUS: 0 sorry.
-/

import WTS.Tower.UniversalLanguageComputer
import WTS.Core

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: GRM → ULC embedding
-- ════════════════════════════════════════════════════════════

/-- Every GradedReflModel is a UniversalLanguageComputer.
    Lang = CompModel = carrier, encode = fold, decode = unfold.
    The grade is forgotten — this is the structural projection. -/
def GradedReflModel.toULC (M : GradedReflModel) : UniversalLanguageComputer where
  Lang := M.carrier
  CompModel := M.carrier
  encode := M.fold
  decode := M.unfold

/-- The GRM roundtrip axiom IS the ULC HasRoundtrip condition. -/
theorem GradedReflModel.toULC_hasRoundtrip (M : GradedReflModel) :
    M.toULC.HasRoundtrip :=
  M.roundtrip

/-- selfApp in ULC agrees with selfApp in GRM. -/
theorem GradedReflModel.toULC_selfApp_eq (M : GradedReflModel) (x : M.carrier) :
    M.toULC.selfApp x = M.selfApp x :=
  rfl

/-- Idempotence carries over: every GRM has idempotent selfApp as a ULC. -/
theorem GradedReflModel.toULC_idempotent (M : GradedReflModel) :
    ∀ x, M.toULC.selfApp (M.toULC.selfApp x) = M.toULC.selfApp x :=
  UniversalLanguageComputer.roundtrip_selfApp_idempotent _ M.toULC_hasRoundtrip

-- ════════════════════════════════════════════════════════════
-- Section 2: trivialModel — the halting machine
-- ════════════════════════════════════════════════════════════

/-- trivialModel as ULC: selfApp = id. No self-interpretation. -/
theorem trivialModel_ULC_selfApp_id :
    ∀ x, trivialModel.toULC.selfApp x = x := by
  intro x; cases x; rfl

-- ════════════════════════════════════════════════════════════
-- Section 3: standardModel — the universal evaluator
-- ════════════════════════════════════════════════════════════

/-- standardModel as ULC: selfApp overflows every grade bound.
    Running program 2d produces trace 2d+1 at grade d+1 > d. -/
theorem standardModel_ULC_selfApp_unbounded :
    ∀ d, ∃ x, standardModel.grade x ≤ d ∧
      standardModel.grade (standardModel.toULC.selfApp x) > d := by
  intro d
  obtain ⟨x, hle, hgt⟩ := standardModel_selfAppUnbounded.overflows d
  exact ⟨x, hle, by rwa [GradedReflModel.toULC_selfApp_eq]⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Phase structure at the ULC level
-- ════════════════════════════════════════════════════════════

/-- The phase structure: both models have roundtrip (structural),
    both have idempotent selfApp (structural), but they differ
    quantitatively — one has selfApp = id, the other has selfApp
    unbounded. The grade is what creates the regime distinction. -/
theorem phase_structure :
    -- Both have roundtrip
    (trivialModel.toULC.HasRoundtrip ∧ standardModel.toULC.HasRoundtrip) ∧
    -- trivialModel: selfApp = id
    (∀ x, trivialModel.toULC.selfApp x = x) ∧
    -- standardModel: selfApp unbounded
    (∀ d, ∃ x, standardModel.grade x ≤ d ∧
      standardModel.grade (standardModel.toULC.selfApp x) > d) :=
  ⟨⟨trivialModel.toULC_hasRoundtrip, standardModel.toULC_hasRoundtrip⟩,
   trivialModel_ULC_selfApp_id,
   standardModel_ULC_selfApp_unbounded⟩

/-- Conservativity at the ULC level: both regimes exist as ULC instances.
    The structural type (UniversalLanguageComputer) admits both selfApp = id
    and selfApp unbounded. The regime is not forced by the structure. -/
theorem ULC_conservativity :
    (∃ P : UniversalLanguageComputer, P.HasRoundtrip ∧ ∀ x, P.selfApp x = x) ∧
    (∃ M : GradedReflModel, M.toULC.HasRoundtrip ∧ SelfAppUnbounded M) :=
  ⟨⟨trivialModel.toULC, trivialModel.toULC_hasRoundtrip, trivialModel_ULC_selfApp_id⟩,
   ⟨standardModel, standardModel.toULC_hasRoundtrip, standardModel_selfAppUnbounded⟩⟩

end WTS
