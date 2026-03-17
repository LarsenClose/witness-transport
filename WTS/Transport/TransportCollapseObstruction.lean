/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/TransportCollapseObstruction.lean — Growth gap obstructs
transport collapse. The shortcut barrier theorem.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore
import WTS.Transport.ConsequenceClosureCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Bounded transport
-- ════════════════════════════════════════════════════════════

/-- A bounded transport: overhead bounded by a function of input grade. -/
structure BoundedTransport (M : GradedReflModel) extends Transport M where
  poly_bound : Nat → Nat
  h_poly : ∀ x, overhead ≤ poly_bound (M.grade x)

/-- A transport shortcut: zero overhead with realizability preservation at same grade. -/
structure TransportShortcut (M : GradedReflModel) where
  shortcut : Transport M
  h_zero : shortcut.overhead = 0
  /-- Preserves realizability at the same grade (overhead = 0 so d + 0 = d). -/
  h_preserves : ∀ x d, Realizable M x d → Realizable M (shortcut.move x) d

-- ════════════════════════════════════════════════════════════
-- Section 2: The core abstract impossibility
-- ════════════════════════════════════════════════════════════

/-- THE CORE RESULT: selfApp cannot be computed by a uniformly grade-bounded function.
    This follows directly from selfApp_not_factors (which follows from SelfAppUnbounded).
    No growth gap needed — just SelfAppUnbounded. -/
theorem no_uniform_bounded_selfApp (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ¬∃ f : M.carrier → M.carrier,
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade (f x) ≤ d) := by
  intro ⟨f, h_agree, h_bound⟩
  exact selfApp_not_factors M hub d (fun x hx => h_agree x hx ▸ h_bound x)

/-- selfApp cannot be computed by any grade-d-bounded function. -/
theorem selfApp_not_grade_bounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat)
    (f : M.carrier → M.carrier)
    (h_grade : ∀ x, M.grade (f x) ≤ d)
    (h_agree : ∀ x, M.grade x ≤ d → f x = M.selfApp x) :
    False :=
  selfApp_not_factors M hub d (fun x hx => h_agree x hx ▸ h_grade x)

/-- Exact interface theorem for WTS/Shared/SideAMirror.lean.
    This has the identical type signature as the axiom
    `sideA_bounded_selector_impossible_mirror` in WTS/Shared/SideAMirror.lean,
    enabling character-level verification that the axiom mirrors a proved theorem.

    The local output bound (grade x ≤ d → grade (f x) ≤ d) is strictly
    weaker as a precondition on f than the global bound in
    `no_uniform_bounded_selfApp`, making this negation strictly stronger.
    Derived from `selfApp_not_factors` in one step. -/
theorem sideA_bounded_selector_impossible (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) := by
  intro ⟨f, hagree, hbound⟩
  exact selfApp_not_factors M hub d (fun x hx => hagree x hx ▸ hbound x hx)

-- ════════════════════════════════════════════════════════════
-- Section 3: Transport collapse connection
-- ════════════════════════════════════════════════════════════

/-- Transport collapse implies a grade-preserving map exists.
    Useful for connecting to the abstract impossibility. -/
theorem transport_collapse_grade_preserved (M : GradedReflModel)
    (h : TransportCollapse M) :
    ∃ f : M.carrier → M.carrier,
      ∀ x d, M.grade x ≤ d → M.grade (f x) ≤ d := by
  obtain ⟨t, hzero, _⟩ := h
  exact ⟨t.move, fun x d hx => by
    have := t.h_grade_bound x; rw [hzero, Nat.add_zero] at this
    exact Nat.le_trans this hx⟩

/-- Transport collapse connection to core impossibility: transport collapse gives
    a grade-preserving map, but NOT necessarily selfApp agreement.
    The full connection requires a faithfulness bridge (provided by K7). -/
theorem transport_collapse_implies_core_collapse (M : GradedReflModel)
    (h : TransportCollapse M) :
    ∃ f : M.carrier → M.carrier, ∀ x d, M.grade x ≤ d → M.grade (f x) ≤ d :=
  transport_collapse_grade_preserved M h

-- ════════════════════════════════════════════════════════════
-- Section 4: Conditional obstruction (with faithfulness)
-- ════════════════════════════════════════════════════════════

/-- A faithfulness condition: the zero-overhead transport acts as a
    grade-bounded evaluator for selfApp. This bridges transport collapse
    to the abstract selfApp impossibility. -/
def TransportFaithful (M : GradedReflModel) (t : Transport M) (d : Nat) : Prop :=
  ∀ x, M.grade x ≤ d → t.move x = M.selfApp x

/-- If t is a faithful evaluator for selfApp at grade d
    and selfApp is unbounded, then no such t can exist.
    (No zero-overhead assumption needed: faithfulness + boundedness suffice.) -/
theorem faithful_transport_impossible (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (t : Transport M) (d : Nat)
    (hfaith : TransportFaithful M t d)
    (h_bound : ∀ x, M.grade (t.move x) ≤ d) :
    False :=
  selfApp_not_grade_bounded M hub d t.move h_bound hfaith

/-- Zero overhead + faithfulness → contradiction with SelfAppUnbounded.
    Zero overhead gives grade(move x) ≤ grade(x) from h_grade_bound,
    so the local bound (grade x ≤ d → grade(move x) ≤ d) is free.
    Combined with faithfulness, this is exactly sideA_bounded_selector_impossible. -/
theorem faithful_zero_overhead_impossible (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (t : Transport M) (d : Nat)
    (hzero : t.overhead = 0)
    (hfaith : TransportFaithful M t d) :
    False := by
  have h_local : ∀ x, M.grade x ≤ d → M.grade (t.move x) ≤ d := fun x hx =>
    Nat.le_trans (by rw [← Nat.add_zero (M.grade x)]; rw [← hzero]; exact t.h_grade_bound x) hx
  exact selfApp_not_factors M hub d (fun x hx => hfaith x hx ▸ h_local x hx)

/-- CONDITIONAL OBSTRUCTION (strengthened): if SelfAppUnbounded holds and
    transport collapse produces a faithful evaluator, then no transport
    collapse can occur. The global boundedness assumption is unnecessary —
    zero overhead provides the local bound via h_grade_bound.
    The faithfulness is the sole open bridge condition. -/
theorem selfAppUnbounded_obstructs_transport_collapse (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (h_faith : ∀ t : Transport M, t.overhead = 0 → ∃ d, TransportFaithful M t d) :
    ¬TransportCollapse M := by
  intro ⟨t, hzero, _⟩
  obtain ⟨d, hf⟩ := h_faith t hzero
  exact faithful_zero_overhead_impossible M hub t d hzero hf

/-- FAITHFULNESS IS DISPROVABLE IN THE SEPARATION REGIME.
    For any zero-overhead transport, at any grade, TransportFaithful fails
    when SelfAppUnbounded holds. This is the explicit negation of
    faithfulness — not an open condition, but a proved impossibility. -/
theorem zero_overhead_not_faithful (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (t : Transport M) (d : Nat)
    (hzero : t.overhead = 0) :
    ¬TransportFaithful M t d :=
  fun hf => faithful_zero_overhead_impossible M hub t d hzero hf

-- ════════════════════════════════════════════════════════════
-- Section 5: TransportShortcut impossibility
-- ════════════════════════════════════════════════════════════

/-- TransportShortcut implies TransportCollapse (same data, forward direction). -/
theorem shortcut_to_collapse (M : GradedReflModel) (s : TransportShortcut M) :
    TransportCollapse M :=
  ⟨s.shortcut, s.h_zero, s.h_preserves⟩

/-- Transport shortcut impossibility (conditional, strengthened). -/
theorem selfAppUnbounded_no_shortcut (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (h_faith : ∀ t : Transport M, t.overhead = 0 → ∃ d, TransportFaithful M t d) :
    ¬TransportCollapse M :=
  selfAppUnbounded_obstructs_transport_collapse M hub h_faith

-- ════════════════════════════════════════════════════════════
-- Section 6: Conservativity
-- ════════════════════════════════════════════════════════════

/-- trivialModel has transport collapse (not obstructed). -/
theorem trivialModel_not_obstructed :
    TransportCollapse trivialModel :=
  trivialModel_transport_collapse

/-- CONSERVATIVITY: trivialModel's identity transport IS faithful at every grade.
    move = id, selfApp = id, so move = selfApp pointwise.
    TransportFaithful sorts by regime: true at identity, false at separation. -/
theorem trivialModel_faithful (d : Nat) :
    TransportFaithful trivialModel (Transport.identity trivialModel) d :=
  fun x _ => by simp [Transport.identity, GradedReflModel.selfApp, trivialModel]

end WTS
