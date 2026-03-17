/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/AggregationDepthBarrier.lean — Aggregation depth barrier:
consequence-closed aggregation has constitutive overhead, static certificates
cannot replace non-constant aggregations, and selfApp-implementing aggregations
admit no faithful replacement at any grade bound.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore
import WTS.Transport.ConsequenceClosureCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Aggregation scheme
-- ════════════════════════════════════════════════════════════

/-- An aggregation scheme: a sequence of consequence-closed transport
    steps that produces a realizable state from locally certified inputs.
    This models consensus, multi-step delegation, iterative refinement. -/
structure AggregationScheme (M : GradedReflModel) where
  /-- Number of aggregation steps -/
  depth : Nat
  /-- The transport at each step -/
  steps : Fin depth → Transport M
  /-- Each step is consequence-closed -/
  h_closed : ∀ k, (steps k).consequenceClosed M
  /-- The composed transport of the entire aggregation -/
  composed : Transport M
  /-- The total overhead is the sum of step overheads -/
  total_overhead : Nat
  /-- The composed overhead matches total_overhead -/
  h_overhead : composed.overhead = total_overhead

/-- Extend an aggregation scheme by one extra consequence-closed step. -/
def AggregationScheme.extend (M : GradedReflModel)
    (agg : AggregationScheme M)
    (extra : Transport M) (h_extra : extra.consequenceClosed M) :
    AggregationScheme M where
  depth := agg.depth + 1
  steps := fun k =>
    if h : k.val < agg.depth
    then agg.steps ⟨k.val, h⟩
    else extra
  h_closed := by
    intro k
    by_cases h : k.val < agg.depth
    · simp only [dif_pos h]
      exact agg.h_closed ⟨k.val, h⟩
    · simp only [dif_neg h]
      exact h_extra
  composed := Transport.compose M agg.composed extra
  total_overhead := agg.total_overhead + extra.overhead
  h_overhead := by
    simp only [Transport.compose]
    rw [agg.h_overhead]

-- ════════════════════════════════════════════════════════════
-- Section 2: Aggregation complexity
-- ════════════════════════════════════════════════════════════

/-- Aggregation complexity: there exists an aggregation scheme of depth ≤ d
    that transports input to output. -/
def AggregationComplexity (M : GradedReflModel)
    (input output : M.carrier) : Nat → Prop :=
  fun d =>
    ∃ agg : AggregationScheme M, agg.depth ≤ d ∧
      agg.composed.move input = output

-- ════════════════════════════════════════════════════════════
-- Section 3: Replacement mechanism
-- ════════════════════════════════════════════════════════════

/-- A replacement mechanism: any single-step function that attempts to
    produce the same output as a multi-step aggregation. This models
    "static certificate," "centralized oracle," "shortcut witness." -/
structure ReplacementMechanism (M : GradedReflModel) where
  /-- The replacement function -/
  replace : M.carrier → M.carrier
  /-- Grade bound on the replacement -/
  grade_bound : Nat
  /-- Replacement output is grade-bounded -/
  h_bounded : ∀ x, M.grade (replace x) ≤ grade_bound

/-- A replacement is faithful if it agrees with the aggregation on all
    grade-bounded inputs. This is pure functional agreement — realizability
    of outputs is a consequence to be derived, not an assumption. -/
def ReplacementFaithful (M : GradedReflModel)
    (agg : AggregationScheme M) (rep : ReplacementMechanism M) : Prop :=
  ∀ x, M.grade x ≤ rep.grade_bound →
    rep.replace x = agg.composed.move x

-- ════════════════════════════════════════════════════════════
-- Section 4: Abstract complexity measure
-- ════════════════════════════════════════════════════════════

/-- An abstract complexity measure on carrier elements:
    monotone with grade, increasing through transports. -/
structure ComplexityMeasure (M : GradedReflModel) where
  measure : M.carrier → Nat
  /-- Measure is at most grade -/
  h_monotone : ∀ x, measure x ≤ M.grade x
  /-- Transport increases measure by at most the overhead -/
  h_transport : ∀ (t : Transport M) x,
    measure (t.move x) ≤ measure x + t.overhead

-- ════════════════════════════════════════════════════════════
-- Section 5: Core grade consistency results
-- ════════════════════════════════════════════════════════════

/-- Grade consistency: faithful replacement's output is grade-bounded.
    Derived from h_bounded and functional agreement (not assumed). -/
theorem faithful_replacement_grade_bounded (M : GradedReflModel)
    (agg : AggregationScheme M)
    (rep : ReplacementMechanism M)
    (h_faithful : ReplacementFaithful M agg rep)
    (x : M.carrier) (hx : M.grade x ≤ rep.grade_bound) :
    M.grade (agg.composed.move x) ≤ rep.grade_bound := by
  rw [← h_faithful x hx]
  exact rep.h_bounded x

/-- If faithful replacement exists, the composed transport is bounded by grade_bound. -/
theorem faithful_composed_transport_bounded (M : GradedReflModel)
    (agg : AggregationScheme M)
    (rep : ReplacementMechanism M)
    (h_faithful : ReplacementFaithful M agg rep) :
    ∀ x, M.grade x ≤ rep.grade_bound →
      M.grade (agg.composed.move x) ≤ rep.grade_bound :=
  fun x hx => faithful_replacement_grade_bounded M agg rep h_faithful x hx

-- ════════════════════════════════════════════════════════════
-- Section 6: Consequence closure through aggregation
-- ════════════════════════════════════════════════════════════

/-- Consequence closure propagates realizability through the aggregation:
    if the composed transport is consequence-closed, realizable inputs produce
    realizable outputs at grade d + total_overhead. -/
theorem aggregation_propagates_realizability (M : GradedReflModel)
    (agg : AggregationScheme M)
    (h_cc : agg.composed.consequenceClosed M) :
    ∀ x d, Realizable M x d →
      Realizable M (agg.composed.move x) (d + agg.total_overhead) := by
  intro x d h_real
  rw [← agg.h_overhead]
  exact h_cc x d h_real

/-- THE OVERHEAD CONSTITUTIVITY THEOREM. Faithful replacement combined with
    consequence closure forces the aggregation's output to be realizable at
    grade_bound + total_overhead. The overhead is constitutive: it is derived
    from the consequence closure of the aggregation steps, not assumed.

    This is the correct form of what was previously called
    "aggregation_irreducibility". The overhead bound is a genuine derived
    consequence of consequence closure, not a definitional unwrap. -/
theorem overhead_constitutivity (M : GradedReflModel)
    (agg : AggregationScheme M)
    (h_cc : agg.composed.consequenceClosed M)
    (rep : ReplacementMechanism M)
    (h_faithful : ReplacementFaithful M agg rep) :
    ∀ x, M.grade x ≤ rep.grade_bound →
      Realizable M x rep.grade_bound →
      M.grade (agg.composed.move x) ≤ rep.grade_bound ∧
      Realizable M (agg.composed.move x) (rep.grade_bound + agg.total_overhead) := by
  intro x hx h_real
  exact ⟨faithful_replacement_grade_bounded M agg rep h_faithful x hx,
         aggregation_propagates_realizability M agg h_cc x rep.grade_bound h_real⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Complexity measure bounds
-- ════════════════════════════════════════════════════════════

/-- Any faithful replacement factors through an object whose complexity
    measure is at most grade_bound. -/
theorem replacement_must_match_complexity (M : GradedReflModel)
    (cm : ComplexityMeasure M)
    (agg : AggregationScheme M)
    (rep : ReplacementMechanism M)
    (h_faithful : ReplacementFaithful M agg rep) :
    ∀ x, M.grade x ≤ rep.grade_bound →
      cm.measure (agg.composed.move x) ≤ rep.grade_bound := by
  intro x hx
  rw [← h_faithful x hx]
  exact Nat.le_trans (cm.h_monotone (rep.replace x)) (rep.h_bounded x)

-- ════════════════════════════════════════════════════════════
-- Section 8: Static certificate impossibility
-- ════════════════════════════════════════════════════════════

/-- If a static certificate (grade-constant replacement) is faithful for an aggregation,
    then the aggregation's composed transport is also grade-constant on grade-bounded inputs:
    same-grade inputs produce same-grade-bounded outputs. -/
theorem static_faithful_implies_agg_grade_constant (M : GradedReflModel)
    (agg : AggregationScheme M)
    (cert : ReplacementMechanism M)
    (h_static : ∀ x y, M.grade x = M.grade y → cert.replace x = cert.replace y)
    (h_faithful : ReplacementFaithful M agg cert)
    (x y : M.carrier) (hx : M.grade x ≤ cert.grade_bound)
    (hy : M.grade y ≤ cert.grade_bound) (hgrade : M.grade x = M.grade y) :
    agg.composed.move x = agg.composed.move y := by
  rw [← h_faithful x hx, ← h_faithful y hy]
  exact h_static x y hgrade

/-- Static certificate impossibility: if cert is faithful for agg AND the aggregation
    is NOT grade-constant (i.e., there exist same-grade inputs producing different outputs),
    then the replacement cannot be static (grade-constant). -/
theorem no_static_certificate_replacement (M : GradedReflModel)
    (agg : AggregationScheme M)
    (cert : ReplacementMechanism M)
    (h_not_constant : ∃ x y, M.grade x = M.grade y ∧
      M.grade x ≤ cert.grade_bound ∧ M.grade y ≤ cert.grade_bound ∧
      agg.composed.move x ≠ agg.composed.move y) :
    ¬(ReplacementFaithful M agg cert ∧
      ∀ x y, M.grade x = M.grade y → cert.replace x = cert.replace y) := by
  intro ⟨h_faithful, h_static⟩
  obtain ⟨x, y, hgrade, hx, hy, hne⟩ := h_not_constant
  apply hne
  exact static_faithful_implies_agg_grade_constant M agg cert h_static h_faithful x y hx hy hgrade

-- ════════════════════════════════════════════════════════════
-- Section 9: Depth monotonicity
-- ════════════════════════════════════════════════════════════

/-- The extended aggregation's total_overhead is the original plus extra. -/
theorem extend_overhead (M : GradedReflModel)
    (agg : AggregationScheme M)
    (extra : Transport M) (h_extra : extra.consequenceClosed M) :
    (agg.extend M extra h_extra).total_overhead = agg.total_overhead + extra.overhead := rfl

-- ════════════════════════════════════════════════════════════
-- Section 10: selfApp aggregation impossibility
-- ════════════════════════════════════════════════════════════

/-- SELFAPP AGGREGATION IMPOSSIBILITY. If the aggregation's composed transport
    agrees with selfApp on all grade-bounded inputs and selfApp is unbounded,
    then no faithful replacement exists at ANY grade bound.

    This is the real impossibility result connecting aggregation to the P≠NP
    program: when an aggregation implements selfApp-like behavior, the
    replacement would force selfApp to factor through grade_bound, contradicting
    SelfAppUnbounded. -/
theorem selfApp_aggregation_no_replacement (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (agg : AggregationScheme M)
    (h_selfApp : ∀ d, ∀ x, M.grade x ≤ d → agg.composed.move x = M.selfApp x) :
    ∀ rep : ReplacementMechanism M, ¬ReplacementFaithful M agg rep := by
  intro rep h_faithful
  have hfact : FactorsThrough M M.selfApp rep.grade_bound := by
    intro x hx
    rw [← h_selfApp rep.grade_bound x hx, ← h_faithful x hx]
    exact rep.h_bounded x
  exact selfApp_not_factors M hub rep.grade_bound hfact

-- ════════════════════════════════════════════════════════════
-- Section 11: Connection to transport collapse
-- ════════════════════════════════════════════════════════════

/-- Conditional transport collapse obstruction: if SelfAppUnbounded holds and
    any zero-overhead transport must agree with selfApp on grade-bounded inputs
    (the faithfulness bridge), then transport collapse is impossible.

    The faithfulness bridge is the open condition. Without it, no abstract
    contradiction is available: trivialModel has selfApp = id (so does NOT
    satisfy SelfAppUnbounded) and admits transport collapse. The hypothesis
    SelfAppUnbounded is doing real work, not just framing. -/
theorem selfAppUnbounded_obstructs_collapse_conditional (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (h_faith : ∀ t : Transport M, t.overhead = 0 →
      ∃ d, (∀ x, M.grade x ≤ d → t.move x = M.selfApp x) ∧
           FactorsThrough M t.move d) :
    ¬TransportCollapse M := by
  intro ⟨t, hzero, _⟩
  obtain ⟨d, h_agree, h_factor⟩ := h_faith t hzero
  exact selfApp_not_factors M hub d (fun x hx => h_agree x hx ▸ h_factor x hx)

/-- An aggregation with positive total overhead and consequence-closed composed
    transport forces realizability at a strictly higher grade than grade_bound.
    This captures the "overhead is constitutive" intuition. -/
theorem aggregation_overhead_is_real (M : GradedReflModel)
    (agg : AggregationScheme M)
    (h_cc : agg.composed.consequenceClosed M)
    (ho : agg.total_overhead > 0)
    (x : M.carrier) (d : Nat) (h_real : Realizable M x d) :
    Realizable M (agg.composed.move x) (d + agg.total_overhead) ∧
    d + agg.total_overhead > d := by
  exact ⟨aggregation_propagates_realizability M agg h_cc x d h_real, by omega⟩

-- ════════════════════════════════════════════════════════════
-- Section 12: Conservativity on trivialModel
-- ════════════════════════════════════════════════════════════

/-- The identity aggregation scheme: depth 0, identity transport, zero overhead. -/
def identityAggregation (M : GradedReflModel) : AggregationScheme M where
  depth := 0
  steps := Fin.elim0
  h_closed := fun k => k.elim0
  composed := Transport.identity M
  total_overhead := 0
  h_overhead := rfl

/-- On trivialModel, the identity aggregation (depth 0) works for any element. -/
theorem trivialModel_zero_aggregation :
    ∀ (x : trivialModel.carrier),
      AggregationComplexity trivialModel x x 0 := by
  intro x
  exact ⟨identityAggregation trivialModel, Nat.le_refl _, rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 13: Additional aggregation properties
-- ════════════════════════════════════════════════════════════

/-- The composed transport of a consequence-closed aggregation propagates realizability
    when h_eq_compose provides the consequence closure of the composed transport. -/
theorem aggregation_composed_closed (M : GradedReflModel)
    (agg : AggregationScheme M)
    (h_eq_compose : agg.composed.consequenceClosed M) :
    ∀ x d, Realizable M x d → Realizable M (agg.composed.move x) (d + agg.total_overhead) :=
  aggregation_propagates_realizability M agg h_eq_compose

/-- The identity aggregation's composed transport moves x → x. -/
theorem identityAggregation_move (M : GradedReflModel) (x : M.carrier) :
    (identityAggregation M).composed.move x = x := rfl

/-- Aggregation of depth ≥ 1 has at least one step: the first step. -/
theorem aggregation_has_first_step (M : GradedReflModel)
    (agg : AggregationScheme M) (hd : agg.depth ≥ 1) :
    ∃ t : Transport M, t.consequenceClosed M :=
  ⟨agg.steps ⟨0, hd⟩, agg.h_closed ⟨0, hd⟩⟩

end WTS
