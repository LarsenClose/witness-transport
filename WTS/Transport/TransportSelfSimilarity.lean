/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/TransportSelfSimilarity.lean — Consequence-closed transports
form a graded reflexive structure: the self-similarity theorem.

The key result: applying "what are the consequence-preserving maps between
grade-d witness configurations?" to the Transport structure returns the
Transport structure. The consequence-closed transports at grade d, with their
composition and identity, satisfy the GradedReflModel axioms with overhead
as grade. This is the M-closure property — Chain 7's operations reproduce
under the meta-rule.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore
import WTS.Transport.ConsequenceClosureCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Pointwise operations on transports
-- ════════════════════════════════════════════════════════════

/-- Pointwise fold on a transport: wrap the output with M.fold.
    The overhead is preserved because fold∘unfold = id means
    fold does not increase grade beyond what unfold introduced. -/
def Transport.foldWrap (M : GradedReflModel) (t : Transport M)
    (h_fold_bound : ∀ x, M.grade (M.fold x) ≤ M.grade x) :
    Transport M where
  move := fun x => M.fold (t.move x)
  overhead := t.overhead
  h_grade_bound := fun x => by
    have h1 := h_fold_bound (t.move x)
    have h2 := t.h_grade_bound x
    exact Nat.le_trans h1 h2

/-- Pointwise unfold on a transport: wrap the output with M.unfold.
    Requires a grade bound on unfold to produce a valid transport. -/
def Transport.unfoldWrap (M : GradedReflModel) (t : Transport M)
    (unfold_overhead : Nat)
    (h_unfold_bound : ∀ x, M.grade (M.unfold x) ≤ M.grade x + unfold_overhead) :
    Transport M where
  move := fun x => M.unfold (t.move x)
  overhead := t.overhead + unfold_overhead
  h_grade_bound := fun x => by
    have h1 := t.h_grade_bound x
    have h2 := h_unfold_bound (t.move x)
    omega

-- ════════════════════════════════════════════════════════════
-- Section 2: The roundtrip transport
-- ════════════════════════════════════════════════════════════

/-- The roundtrip transport: fold∘unfold applied pointwise.
    By the roundtrip axiom, this is the identity on elements.
    It has zero overhead. This is the "verification" at the transport level. -/
def Transport.roundtrip (M : GradedReflModel) : Transport M where
  move := fun x => M.fold (M.unfold x)
  overhead := 0
  h_grade_bound := fun x => by
    rw [M.roundtrip x]; exact Nat.le_refl _

/-- The roundtrip transport's move is pointwise identity. -/
theorem roundtrip_move_eq_id (M : GradedReflModel) :
    (Transport.roundtrip M).move = id := by
  funext x; exact M.roundtrip x

/-- The roundtrip transport is consequence-closed. -/
theorem roundtrip_consequence_closed (M : GradedReflModel) :
    (Transport.roundtrip M).consequenceClosed M := by
  intro x d hreal
  simp only [Transport.roundtrip, Nat.add_zero]
  constructor
  · rw [M.roundtrip]; exact hreal.1
  · rw [M.roundtrip]; exact hreal.2

-- ════════════════════════════════════════════════════════════
-- Section 3: The selfApp transport
-- ════════════════════════════════════════════════════════════

/-- The selfApp transport (unfold∘fold) is NOT a valid Transport in general
    because selfApp can increase grade unboundedly. This theorem witnesses
    the obstruction: for any proposed overhead k, there exists an input
    whose selfApp exceeds grade k. -/
theorem selfApp_no_bounded_transport (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    ∀ k, ∃ x, M.grade x ≤ k ∧ M.grade (M.selfApp x) > k := by
  intro k
  exact hub.overflows k

-- ════════════════════════════════════════════════════════════
-- Section 4: Transport composition is associative
-- ════════════════════════════════════════════════════════════

/-- Transport composition is associative on the `move` function. -/
theorem transport_compose_assoc_move (M : GradedReflModel)
    (t₁ t₂ t₃ : Transport M) :
    (Transport.compose M (Transport.compose M t₁ t₂) t₃).move =
    (Transport.compose M t₁ (Transport.compose M t₂ t₃)).move := by
  rfl

/-- Transport composition is associative on overhead. -/
theorem transport_compose_assoc_overhead (M : GradedReflModel)
    (t₁ t₂ t₃ : Transport M) :
    (Transport.compose M (Transport.compose M t₁ t₂) t₃).overhead =
    (Transport.compose M t₁ (Transport.compose M t₂ t₃)).overhead := by
  simp [Transport.compose]; omega

/-- Left identity: composing identity with t gives same move as t. -/
theorem transport_identity_left (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M (Transport.identity M) t).move = t.move := by
  rfl

/-- Right identity: composing t with identity gives same move as t. -/
theorem transport_identity_right (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M t (Transport.identity M)).move = t.move := by
  rfl

/-- Left identity overhead: 0 + t.overhead = t.overhead. -/
theorem transport_identity_left_overhead (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M (Transport.identity M) t).overhead = t.overhead := by
  simp [Transport.compose, Transport.identity]

/-- Right identity overhead: t.overhead + 0 = t.overhead. -/
theorem transport_identity_right_overhead (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M t (Transport.identity M)).overhead = t.overhead := by
  simp [Transport.compose, Transport.identity]

-- ════════════════════════════════════════════════════════════
-- Section 5: The meta-roundtrip property
-- ════════════════════════════════════════════════════════════

/-- Composing with the roundtrip transport (from either side) preserves
    the transport's move function. This is the transport-level analog of
    fold∘unfold = id: the roundtrip transport acts as identity. -/
theorem roundtrip_compose_left (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M (Transport.roundtrip M) t).move = t.move := by
  funext x
  simp [Transport.compose, Transport.roundtrip]
  exact congrArg t.move (M.roundtrip x)

theorem roundtrip_compose_right (M : GradedReflModel) (t : Transport M) :
    (Transport.compose M t (Transport.roundtrip M)).move = t.move := by
  funext x
  simp [Transport.compose, Transport.roundtrip]
  exact M.roundtrip (t.move x)

-- ════════════════════════════════════════════════════════════
-- Section 6: The Transport GradedReflModel
-- ════════════════════════════════════════════════════════════

/-- The consequence-closed transports on M form a GradedReflModel.

    - carrier: Transport M (all transports, not just consequence-closed)
    - fold: wrapping output with fold∘unfold (= id by roundtrip)
    - unfold: the identity on transports (trivially)
    - grade: the transport's overhead
    - roundtrip: fold(unfold(t)) = t because fold is roundtrip-wrapping = id

    The critical observation: fold at the transport level is the roundtrip
    wrapping, which is the identity on moves (by M.roundtrip). So
    fold∘unfold = id holds definitionally after funext.

    The "selfApp" of this model is unfold∘fold = roundtrip-wrapping, which
    is also id on moves. This means selfApp = id at the transport level,
    which means the transport model is in the P = NP regime (trivial model).

    This is NOT a defect — it is the precise content of self-similarity:
    the transport structure is self-similar because it is a FIXED POINT.
    The meta-rule applied to it returns a trivial (self-identical) structure.
    M(Transport) ≅ Transport is exactly what a fixed point means: applying
    the operation doesn't change the structure. The non-trivial separation
    lives in the BASE model M, not in the meta-model of transports over M.

    Compare: trivialModel has selfApp = id and P = NP. The transport model
    over a Turing-complete M reproduces the trivialModel shape at the
    meta-level. This is the M-closure property: transports are already
    at the fixed point of the meta-rule. -/
def transportGradedReflModel (M : GradedReflModel) : GradedReflModel where
  carrier := Transport M
  fold := fun t => {
    move := fun x => M.fold (M.unfold (t.move x))
    overhead := t.overhead
    h_grade_bound := fun x => by
      rw [M.roundtrip]; exact t.h_grade_bound x
  }
  unfold := id
  roundtrip := fun t => by
    simp only [id]
    -- Need: fold(unfold(t)) = t, i.e., the roundtrip-wrapped transport = t
    -- fold(t) has move = fun x => fold(unfold(t.move x)) = fun x => t.move x (by roundtrip)
    -- So fold(t).move = t.move, fold(t).overhead = t.overhead
    -- Transport extensionality: two transports with same move and overhead
    -- and compatible grade bounds are equal... but h_grade_bound is a proof,
    -- so we need proof irrelevance (propext gives us this for Prop fields).
    have h_move : (fun x => M.fold (M.unfold (t.move x))) = t.move := by
      funext x; exact M.roundtrip (t.move x)
    -- Use the fact that Transport is a structure with one Prop field
    -- after move and overhead are fixed, h_grade_bound is determined.
    cases t with
    | mk move overhead h_grade_bound =>
      simp only at h_move ⊢
      congr 1
  grade := fun t => t.overhead

/-- The transportGradedReflModel has selfApp = id (the identity on transports).
    This means the transport model is at the fixed point: applying the meta-rule
    returns the same structure. -/
theorem transport_model_selfApp_eq_id (M : GradedReflModel) :
    ∀ t : (transportGradedReflModel M).carrier,
      (transportGradedReflModel M).selfApp t = t := by
  intro t
  simp only [GradedReflModel.selfApp, transportGradedReflModel, id]
  cases t with
  | mk move overhead h_grade_bound =>
    simp only
    congr 1
    funext x; exact M.roundtrip (move x)

/-- The transport model satisfies P = NP (selfApp factors through every grade). -/
theorem transport_model_PEqNP (M : GradedReflModel) :
    PEqNP (transportGradedReflModel M) := by
  refine ⟨0, fun t ht => ?_⟩
  -- selfApp(t) has the same overhead as t (by the roundtrip construction)
  -- so grade(selfApp(t)) = t.overhead ≤ 0 = ht
  simp only [GradedReflModel.selfApp, transportGradedReflModel, id]
  exact ht

/-- The roundtrip transport has grade 0 in the transport model. -/
theorem roundtrip_grade_zero (M : GradedReflModel) :
    (transportGradedReflModel M).grade (Transport.roundtrip M) = 0 := rfl

/-- The identity transport has grade 0 in the transport model. -/
theorem identity_grade_zero (M : GradedReflModel) :
    (transportGradedReflModel M).grade (Transport.identity M) = 0 := rfl

-- ════════════════════════════════════════════════════════════
-- Section 7: Self-similarity as fixed-point property
-- ════════════════════════════════════════════════════════════

/-- THE SELF-SIMILARITY THEOREM: the transport model's selfApp is the identity.
    In a GradedReflModel, the key structural tension is between fold∘unfold = id
    (verification is trivial) and unfold∘fold = selfApp (extraction may overflow).
    For the transport model, BOTH are the identity. The meta-rule applied to the
    transport structure returns a trivial (self-identical) model.

    This is the M-closure property: consequence-closed transports are already
    at the fixed point. The structure reproduces under the meta-rule because
    the meta-rule has nothing to do — the transport structure is self-similar.

    Formally: transportGradedReflModel M satisfies selfApp = id and therefore
    also satisfies PEqNP (verification = extraction at the meta-level).

    The non-trivial content is not that the meta-level is hard, but that the
    meta-level is trivial PRECISELY BECAUSE the base level carries the full
    separation. The transport operations (compose, project, realize) constitute
    the consequence structure rather than describing it, so there is no gap
    between "what the meta-rule sees" and "what the structure is." -/
theorem transport_self_similarity (M : GradedReflModel) :
    (∀ t, (transportGradedReflModel M).selfApp t = t) ∧
    PEqNP (transportGradedReflModel M) :=
  ⟨transport_model_selfApp_eq_id M, transport_model_PEqNP M⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Consequence closure lifts to the transport model
-- ════════════════════════════════════════════════════════════

/-- If t is consequence-closed on M, then the constant function returning t
    factors through every grade in the transport model. This shows that
    consequence-closed transports are "low-grade" in the meta-model. -/
theorem consequence_closed_factors (M : GradedReflModel) (t : Transport M)
    (_hcc : t.consequenceClosed M) (d : Nat) (hd : t.overhead ≤ d) :
    (transportGradedReflModel M).grade t ≤ d :=
  hd

/-- Composition preserves consequence closure (already proved, restated
    for the self-similarity context). -/
theorem compose_preserves_consequence_closure (M : GradedReflModel)
    (t₁ t₂ : Transport M)
    (h₁ : t₁.consequenceClosed M) (h₂ : t₂.consequenceClosed M) :
    (Transport.compose M t₁ t₂).consequenceClosed M :=
  consequence_closed_compose M t₁ t₂ h₁ h₂

-- ════════════════════════════════════════════════════════════
-- Section 9: The contrast with other chains
-- ════════════════════════════════════════════════════════════

/-- Applying the meta-rule to the BASE model M gives a model where
    selfApp may be unbounded (the original model's separation).
    Applying the meta-rule to the TRANSPORT model gives a model
    where selfApp = id (the fixed-point property).

    This contrast is the formal content of "Chain 7 is not another language":
    - Other chains work within M where separation may hold
    - Chain 7's operations form a structure where the meta-rule is trivial
    - The non-trivial content is carried by the base model, not repeated
      at the meta-level -/
theorem base_vs_transport_contrast (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    -- Base model: selfApp is unbounded (separation may hold)
    (¬PEqNP M) ∧
    -- Transport model: selfApp = id (fixed point)
    PEqNP (transportGradedReflModel M) := by
  constructor
  · -- ¬PEqNP M follows from selfApp unbounded
    intro ⟨d, hf⟩
    exact selfApp_not_factors M hub d hf
  · exact transport_model_PEqNP M

-- ════════════════════════════════════════════════════════════
-- Section 10: Conservativity
-- ════════════════════════════════════════════════════════════

/-- Conservativity: the transport model of trivialModel is itself trivial.
    Both the base and transport models have selfApp = id. -/
theorem trivial_transport_conservativity :
    (∀ t, (transportGradedReflModel trivialModel).selfApp t = t) ∧
    (∀ x, trivialModel.selfApp x = x) :=
  ⟨transport_model_selfApp_eq_id trivialModel, trivial_selfApp_eq_id⟩

/-- Conservativity: the transport model of standardModel is trivial at the meta-level
    while standardModel itself is non-trivial (selfApp unbounded). -/
theorem standard_transport_nontrivial_base :
    (∀ t, (transportGradedReflModel standardModel).selfApp t = t) ∧
    SelfAppUnbounded standardModel :=
  ⟨transport_model_selfApp_eq_id standardModel, standardModel_selfAppUnbounded⟩

-- ════════════════════════════════════════════════════════════
-- Section 11: Transport idempotence (nested self-similarity)
-- ════════════════════════════════════════════════════════════

/-- Transport idempotence: applying transportGradedReflModel twice gives the
    same structural properties as applying it once. The double-transport model
    TTM = transportGradedReflModel (transportGradedReflModel M) still has
    selfApp = id and PEqNP.

    The proof is NOT a trivial reuse of transport_self_similarity — it must
    unfold the nested structure. TTM.selfApp t has move =
    fun x => TM.fold (TM.unfold (t.move x)). Since TM.unfold = id, this
    reduces to fun x => TM.fold (t.move x). And TM.fold applied to
    (t.move x : Transport M) wraps with M.fold ∘ M.unfold, which is id
    by M.roundtrip. So the nested roundtrip collapses at each level. -/
theorem transport_model_idempotent (M : GradedReflModel) :
    let TM := transportGradedReflModel M
    let TTM := transportGradedReflModel TM
    (∀ t, TTM.selfApp t = t) ∧
    PEqNP TTM := by
  constructor
  · -- Part 1: selfApp = id at the double-transport level
    intro t
    -- Unfold selfApp and the outer transportGradedReflModel
    simp only [GradedReflModel.selfApp, transportGradedReflModel, id]
    -- t : Transport TM where TM = transportGradedReflModel M
    -- Need to show the outer transport (with move wrapped by TM.fold∘TM.unfold) = t
    cases t with
    | mk move overhead h_grade_bound =>
      simp only
      congr 1
      -- Need: (fun x => TM.fold (TM.unfold (move x))) = move
      -- where TM.unfold = id, so this is (fun x => TM.fold (move x)) = move
      funext x
      -- Now need: TM.fold (move x) = move x
      -- TM.fold wraps a Transport M with M.fold∘M.unfold on its move field
      -- move x : Transport M, so we case-split on its components
      -- Unfolding TM.fold: it produces {move := fun y => M.fold (M.unfold ((move x).move y)),
      --                                  overhead := (move x).overhead, ...}
      -- The goal is: {move := fun y => M.fold (M.unfold ((move x).move y)),
      --               overhead := (move x).overhead, h_grade_bound := ...} = move x
      -- This is exactly (transportGradedReflModel M).fold (move x) = move x
      -- which follows from (transportGradedReflModel M).roundtrip (move x)
      -- since (transportGradedReflModel M).unfold = id.
      -- We convert the goal to use TM.roundtrip.
      change (transportGradedReflModel M).fold (move x) = move x
      have := (transportGradedReflModel M).roundtrip (move x)
      simp only [transportGradedReflModel, id] at this
      exact this
  · -- Part 2: PEqNP at the double-transport level
    refine ⟨0, fun t ht => ?_⟩
    -- TTM.grade (TTM.selfApp t) = overhead of selfApp(t) = overhead of t = TTM.grade t
    simp only [GradedReflModel.selfApp, transportGradedReflModel, id]
    exact ht

-- ════════════════════════════════════════════════════════════
-- Section 12: Universal consequence closure on T(M)
-- ════════════════════════════════════════════════════════════

/-- Realizability in the transport model reduces to an overhead bound.
    Both components of Realizable (grade and fold-grade) equal s.overhead
    in transportGradedReflModel, because fold preserves overhead exactly. -/
theorem realizable_transportModel_iff (M : GradedReflModel) (s : Transport M) (d : Nat) :
    Realizable (transportGradedReflModel M) s d ↔ s.overhead ≤ d := by
  constructor
  · exact fun ⟨h, _⟩ => h
  · exact fun h => ⟨h, h⟩

/-- UNIVERSAL CLOSURE THEOREM: every transport on T(M) is consequence-closed.

    The transport meta-level has no consequence gaps. This is because
    realizability on T(M) reduces to an overhead bound
    (realizable_transportModel_iff), and the grade bound on any transport
    provides the needed arithmetic.

    Contrast with the base model M, where consequence closure is a
    nontrivial property that distinguishes well-behaved transports from
    degrading ones. At the meta-level, the distinction collapses: ALL
    transports are well-behaved. This is the formal content of
    "the meta-rule has nothing to do." -/
theorem transport_model_universally_closed (M : GradedReflModel) :
    ∀ t : Transport (transportGradedReflModel M),
      t.consequenceClosed (transportGradedReflModel M) := by
  intro t s d hreal
  rw [realizable_transportModel_iff] at hreal ⊢
  have := t.h_grade_bound s
  simp only [transportGradedReflModel] at this
  omega

-- ════════════════════════════════════════════════════════════
-- Section 13: Grade-preserving retraction T(T(M)) ↪ T(M)
-- ════════════════════════════════════════════════════════════

/-- Evaluation at the identity: maps a transport-of-transports to a
    transport by applying it to the identity transport.
    Grade: non-increasing ((eval tt).overhead ≤ tt.overhead). -/
def transport_eval_at_id (M : GradedReflModel)
    (tt : Transport (transportGradedReflModel M)) : Transport M :=
  tt.move (Transport.identity M)

/-- Lifting by post-composition: embeds a transport into the
    transport-of-transports level.

    Given t : Transport M, lift(t) maps any transport s to the
    composition t;s (apply t first, then s). Grade is exactly preserved:
    lift(t).overhead = t.overhead. -/
def transport_lift (M : GradedReflModel) (t : Transport M) :
    Transport (transportGradedReflModel M) where
  move := fun s => Transport.compose M t s
  overhead := t.overhead
  h_grade_bound := fun s => by
    simp only [transportGradedReflModel, Transport.compose]
    omega

/-- RETRACTION THEOREM: eval_at_id ∘ lift = id on Transport M.

    T(M) is a retract of T(T(M)): the lift embeds it, and evaluation
    at the identity recovers it. This is stronger than saying both models
    are in the same regime — it says the structures are related by a
    section-retraction pair.

    Proof: lift(t) applied to the identity transport gives compose(t, id),
    which has move = id ∘ t.move = t.move and overhead = t.overhead + 0
    = t.overhead. Both are definitional equalities. -/
theorem transport_section_retraction (M : GradedReflModel)
    (t : Transport M) :
    transport_eval_at_id M (transport_lift M t) = t := by
  simp only [transport_eval_at_id, transport_lift, Transport.compose, Transport.identity]
  cases t with
  | mk move overhead h_grade_bound =>
    simp only
    congr 1

/-- Lift preserves grade exactly: the overhead at the TT-level equals
    the overhead at the T-level. -/
theorem transport_lift_grade_preserving (M : GradedReflModel)
    (t : Transport M) :
    (transportGradedReflModel (transportGradedReflModel M)).grade
      (transport_lift M t) =
    (transportGradedReflModel M).grade t :=
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 14: The transport fixed-point theorem
-- ════════════════════════════════════════════════════════════

/-- THE TRANSPORT FIXED-POINT THEOREM.

    T(M) is a fixed point of the transport construction in four precise
    senses:
    (1) selfApp = id at the meta-level (collapse regime)
    (2) PEqNP at the meta-level (verification = solving)
    (3) Every transport on T(M) is consequence-closed (no gaps at meta-level)
    (4) T(M) is a grade-preserving retract of T(T(M)) (structure preserved)

    Together these formalize "the operations reproduce under their own
    meta-rule." The transport construction, applied to its own output,
    produces a maximally trivial structure that embeds back as a retract.
    There is no new obstruction at the meta-level; the separation lives
    entirely in the base model M.

    Compare: for an arbitrary model M, (3) can fail — some transports
    degrade. For T(M), it cannot. The meta-level is structurally closed.

    This is stronger than transport_model_idempotent (Section 11), which
    only proves the regime match. The fixed-point theorem adds universal
    closure and the structural retraction. -/
theorem transport_fixed_point (M : GradedReflModel) :
    -- (1) selfApp = id
    (∀ t, (transportGradedReflModel M).selfApp t = t) ∧
    -- (2) PEqNP
    PEqNP (transportGradedReflModel M) ∧
    -- (3) Universal consequence closure
    (∀ t : Transport (transportGradedReflModel M),
      t.consequenceClosed (transportGradedReflModel M)) ∧
    -- (4) Grade-preserving retract
    (∀ t : Transport M,
      transport_eval_at_id M (transport_lift M t) = t ∧
      (transportGradedReflModel (transportGradedReflModel M)).grade
        (transport_lift M t) =
      (transportGradedReflModel M).grade t) :=
  ⟨transport_model_selfApp_eq_id M,
   transport_model_PEqNP M,
   transport_model_universally_closed M,
   fun t => ⟨transport_section_retraction M t, transport_lift_grade_preserving M t⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 15: GRM morphisms and structural retraction
-- ════════════════════════════════════════════════════════════

/-- A strict morphism of graded reflexive models: commutes with fold
    and unfold, preserves grade exactly. -/
structure GRMorphism (M₁ M₂ : GradedReflModel) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  map_grade : ∀ x, M₂.grade (map x) = M₁.grade x

/-- A grade-compatible retraction of graded reflexive models: commutes
    with fold and unfold, grade non-increasing. -/
structure GRRetraction (M₁ M₂ : GradedReflModel) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  map_grade_le : ∀ x, M₂.grade (map x) ≤ M₁.grade x

/-- Every strict morphism is a retraction. -/
def GRMorphism.toRetraction {M₁ M₂ : GradedReflModel} (φ : GRMorphism M₁ M₂) :
    GRRetraction M₁ M₂ where
  map := φ.map
  map_fold := φ.map_fold
  map_unfold := φ.map_unfold
  map_grade_le := fun x => by have := φ.map_grade x; omega

/-- Fold in the transport model is the identity (since unfold = id
    and fold ∘ unfold = id by roundtrip). -/
theorem transportModel_fold_eq_id (M : GradedReflModel) :
    ∀ t : Transport M, (transportGradedReflModel M).fold t = t :=
  fun t => (transportGradedReflModel M).roundtrip t

/-- The lift embedding T(M) → T(T(M)) is a strict GRM morphism.

    - fold commutation: both TM.fold and TTM.fold act as identity
      (by roundtrip), so the diagram commutes trivially.
    - unfold commutation: both unfolds are literally id.
    - grade: overhead at both levels equals t.overhead. -/
def transport_lift_morphism (M : GradedReflModel) :
    GRMorphism (transportGradedReflModel M)
               (transportGradedReflModel (transportGradedReflModel M)) where
  map := transport_lift M
  map_fold := fun t => by
    rw [transportModel_fold_eq_id M t,
        transportModel_fold_eq_id (transportGradedReflModel M) (transport_lift M t)]
  map_unfold := fun _ => rfl
  map_grade := fun _ => rfl

/-- The evaluation map T(T(M)) → T(M) commutes with fold. -/
theorem transport_eval_map_fold (M : GradedReflModel)
    (tt : Transport (transportGradedReflModel M)) :
    transport_eval_at_id M
      ((transportGradedReflModel (transportGradedReflModel M)).fold tt) =
    (transportGradedReflModel M).fold (transport_eval_at_id M tt) := by
  rw [transportModel_fold_eq_id (transportGradedReflModel M) tt,
      transportModel_fold_eq_id M (transport_eval_at_id M tt)]

/-- The evaluation map T(T(M)) → T(M) is grade non-increasing:
    eval(tt).overhead ≤ tt.overhead, because evaluating at the zero-grade
    identity transport can only reduce overhead. -/
theorem transport_eval_grade_le (M : GradedReflModel)
    (tt : Transport (transportGradedReflModel M)) :
    (transportGradedReflModel M).grade (transport_eval_at_id M tt) ≤
    (transportGradedReflModel (transportGradedReflModel M)).grade tt := by
  have h := tt.h_grade_bound (Transport.identity M)
  simp only [transport_eval_at_id, transportGradedReflModel, Transport.identity] at h ⊢
  omega

/-- The evaluation at identity T(T(M)) → T(M) is a GR retraction:
    commutes with fold/unfold, grade non-increasing. -/
def transport_eval_retraction (M : GradedReflModel) :
    GRRetraction (transportGradedReflModel (transportGradedReflModel M))
                 (transportGradedReflModel M) where
  map := transport_eval_at_id M
  map_fold := transport_eval_map_fold M
  map_unfold := fun _ => rfl
  map_grade_le := transport_eval_grade_le M

/-- STRUCTURAL RETRACTION THEOREM.

    T(M) is a structure-preserving retract of T(T(M)): the lift is a
    strict GRM morphism (section) and evaluation at the identity is a
    GR retraction, with eval ∘ lift = id.

    This upgrades the transport fixed-point theorem (Section 14) from
    regime matching to structural preservation. The section-retraction
    pair respects fold, unfold, and grade — the maps do not merely
    land in the same regime, they preserve the GRM structure. -/
theorem structural_retraction (M : GradedReflModel) :
    (∃ φ : GRMorphism (transportGradedReflModel M)
                      (transportGradedReflModel (transportGradedReflModel M)),
      ∃ ψ : GRRetraction (transportGradedReflModel (transportGradedReflModel M))
                         (transportGradedReflModel M),
        ∀ t, ψ.map (φ.map t) = t) :=
  ⟨transport_lift_morphism M,
   transport_eval_retraction M,
   transport_section_retraction M⟩

-- ════════════════════════════════════════════════════════════
-- Section 16: Regime functoriality
-- ════════════════════════════════════════════════════════════

/-- GRM morphisms preserve selfApp: φ(selfApp(x)) = selfApp(φ(x)).

    Proof: selfApp = unfold ∘ fold, and φ commutes with both.
    This is the formal content of "regime is functorial": a morphism
    cannot map a model with selfApp = id to one with selfApp unbounded,
    or vice versa. The separation/collapse distinction is an invariant
    of the GRM category. -/
theorem GRMorphism.map_selfApp {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) (x : M₁.carrier) :
    φ.map (M₁.selfApp x) = M₂.selfApp (φ.map x) := by
  simp only [GradedReflModel.selfApp]
  rw [φ.map_unfold, φ.map_fold]

/-- GR retractions also preserve selfApp (same proof). -/
theorem GRRetraction.map_selfApp {M₁ M₂ : GradedReflModel}
    (ψ : GRRetraction M₁ M₂) (x : M₁.carrier) :
    ψ.map (M₁.selfApp x) = M₂.selfApp (ψ.map x) := by
  simp only [GradedReflModel.selfApp]
  rw [ψ.map_unfold, ψ.map_fold]

/-- Strict morphisms reflect FactorsThrough: if selfApp factors through
    grade d in M₂, then it factors through grade d in M₁.

    Proof: given x in M₁ with grade(x) ≤ d, map it to M₂ where
    grade(φ(x)) = grade(x) ≤ d (exact grade preservation). Then
    grade(selfApp(φ(x))) ≤ d (by hypothesis on M₂). But
    selfApp(φ(x)) = φ(selfApp(x)) (by map_selfApp), so
    grade(φ(selfApp(x))) ≤ d, hence grade(selfApp(x)) ≤ d
    (by exact grade preservation again).

    Contrapositive: if M₁ has ¬FactorsThrough at grade d, then so
    does M₂. Separation propagates forward along strict morphisms. -/
theorem GRMorphism.reflects_factorsThrough {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) (d : Nat)
    (hf : FactorsThrough M₂ M₂.selfApp d) :
    FactorsThrough M₁ M₁.selfApp d := by
  intro x hx
  have h1 : M₂.grade (φ.map x) ≤ d := by rw [φ.map_grade]; exact hx
  have h2 : M₂.grade (M₂.selfApp (φ.map x)) ≤ d := hf _ h1
  rw [← φ.map_selfApp] at h2
  rw [φ.map_grade] at h2
  exact h2

/-- Strict morphisms reflect PEqNP: if M₂ has PEqNP and there exists
    a strict morphism M₁ → M₂, then M₁ has PEqNP. -/
theorem GRMorphism.reflects_PEqNP {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) (h : PEqNP M₂) :
    PEqNP M₁ := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, φ.reflects_factorsThrough d hd⟩

/-- Separation propagates forward along strict morphisms: if M₁ has
    unbounded selfApp, then no target of a strict morphism from M₁
    can have PEqNP.

    This is the formal version of "you cannot bridge across the
    separation with a structure-preserving map." -/
theorem strict_morphism_propagates_separation {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) (hub : SelfAppUnbounded M₁) :
    ¬PEqNP M₂ := by
  intro ⟨d, hd⟩
  exact selfApp_not_factors M₁ hub d (φ.reflects_factorsThrough d hd)

/-- GRM morphisms preserve realizability with zero overhead.

    A GRM morphism is the inter-model analogue of a zero-overhead
    consequence-closed transport: it maps realizable elements to
    realizable elements without grade shift.

    Note: the CONVERSE does not hold. Consequence closure is weaker
    than GRM morphism — it gives grade bounds but not fold/unfold
    commutation. The gap is exactly fold/unfold commutation: a
    consequence-closed map that also commutes with fold and unfold
    is a GR retraction. -/
theorem GRMorphism.preserves_realizable {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable M₁ x d) :
    Realizable M₂ (φ.map x) d := by
  unfold Realizable at hr ⊢
  obtain ⟨hg, hfg⟩ := hr
  constructor
  · rw [φ.map_grade]; exact hg
  · rw [← φ.map_fold, φ.map_grade]; exact hfg

/-- GR retractions also preserve realizability (grade non-increasing
    suffices since realizability is a ≤ condition). -/
theorem GRRetraction.preserves_realizable {M₁ M₂ : GradedReflModel}
    (ψ : GRRetraction M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable M₁ x d) :
    Realizable M₂ (ψ.map x) d := by
  unfold Realizable at hr ⊢
  obtain ⟨hg, hfg⟩ := hr
  constructor
  · exact Nat.le_trans (ψ.map_grade_le x) hg
  · rw [← ψ.map_fold]; exact Nat.le_trans (ψ.map_grade_le _) hfg

/-- REGIME FUNCTORIALITY FOR THE TRANSPORT RETRACTION.

    The structural retraction (Section 15) necessarily preserves regime.
    Since transport_lift is a strict GRM morphism T(M) → T(T(M)),
    it reflects PEqNP: T(T(M)) having PEqNP forces T(M) to have PEqNP.
    This is not a coincidence — it is forced by the morphism structure.

    More precisely: the same proof gives that ANY model admitting a
    strict morphism into T(T(M)) must be in the P=NP regime. The
    transport construction is a regime sink — everything that maps
    strictly into it collapses. -/
theorem transport_retraction_regime_forced (M : GradedReflModel) :
    PEqNP (transportGradedReflModel M) :=
  (transport_lift_morphism M).reflects_PEqNP (transport_model_PEqNP (transportGradedReflModel M))

-- ════════════════════════════════════════════════════════════
-- Section 17: PolyGRRetraction — polynomial-slack retractions
-- ════════════════════════════════════════════════════════════

/-- A polynomial-slack retraction of graded reflexive models: commutes
    with fold and unfold, grade bounded by a polynomial of the source grade.

    This captures the common pattern across all seven chains: the bridge
    condition is "GRRetraction with polynomial grade distortion."

    Hierarchy: GRMorphism (exact) ⊂ GRRetraction (non-increasing) ⊂
    PolyGRRetraction (polynomial slack). -/
structure PolyGRRetraction (M₁ M₂ : GradedReflModel) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  bound : PolyBound
  map_grade_poly : ∀ x, M₂.grade (map x) ≤ bound.eval (M₁.grade x)

/-- Every GRRetraction is a PolyGRRetraction with bound n^1 + 0 = n. -/
def GRRetraction.toPolyGRRetraction {M₁ M₂ : GradedReflModel}
    (ψ : GRRetraction M₁ M₂) : PolyGRRetraction M₁ M₂ where
  map := ψ.map
  map_fold := ψ.map_fold
  map_unfold := ψ.map_unfold
  bound := ⟨1, 0⟩
  map_grade_poly := fun x => by
    simp [PolyBound.eval]
    exact ψ.map_grade_le x

/-- Every GRMorphism is a PolyGRRetraction with bound n^1 + 0 = n. -/
def GRMorphism.toPolyGRRetraction {M₁ M₂ : GradedReflModel}
    (φ : GRMorphism M₁ M₂) : PolyGRRetraction M₁ M₂ :=
  φ.toRetraction.toPolyGRRetraction

/-- PolyGRRetractions preserve selfApp: φ(selfApp(x)) = selfApp(φ(x)). -/
theorem PolyGRRetraction.map_selfApp {M₁ M₂ : GradedReflModel}
    (φ : PolyGRRetraction M₁ M₂) (x : M₁.carrier) :
    φ.map (M₁.selfApp x) = M₂.selfApp (φ.map x) := by
  simp only [GradedReflModel.selfApp]
  rw [φ.map_unfold, φ.map_fold]

/-- Auxiliary: PolyBound.eval is monotone in its argument. -/
theorem PolyBound.eval_mono (p : PolyBound) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  unfold PolyBound.eval
  exact Nat.add_le_add_right (Nat.pow_le_pow_left h p.degree) p.constant

/-- PolyGRRetractions preserve realizability with polynomial overhead:
    if x is realizable at grade d in M₁, then φ(x) is realizable at
    grade bound.eval(d) in M₂. -/
theorem PolyGRRetraction.preserves_realizable {M₁ M₂ : GradedReflModel}
    (φ : PolyGRRetraction M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable M₁ x d) :
    Realizable M₂ (φ.map x) (φ.bound.eval d) := by
  obtain ⟨hg, hfg⟩ := hr
  constructor
  · exact Nat.le_trans (φ.map_grade_poly x) (φ.bound.eval_mono hg)
  · rw [← φ.map_fold]
    exact Nat.le_trans (φ.map_grade_poly _) (φ.bound.eval_mono hfg)

/-- PolyGRRetractions transport FactorsThrough on the image: if selfApp
    factors through grade d in M₁, then for every x in M₁ with grade ≤ d,
    grade(selfApp(φ(x))) ≤ bound.eval(d) in M₂.

    This is the polynomial analogue of regime functoriality: a map with
    polynomial grade slack carries the FactorsThrough property forward
    (on its image) with a polynomial shift. Unlike GRMorphism which
    reflects FactorsThrough exactly, PolyGRRetraction transports it
    forward with polynomial distortion — precisely the bridge condition
    that all seven chains satisfy. -/
theorem PolyGRRetraction.image_factorsThrough {M₁ M₂ : GradedReflModel}
    (φ : PolyGRRetraction M₁ M₂) (d : Nat)
    (hf : FactorsThrough M₁ M₁.selfApp d)
    (x : M₁.carrier) (hx : M₁.grade x ≤ d) :
    M₂.grade (M₂.selfApp (φ.map x)) ≤ φ.bound.eval d := by
  rw [← φ.map_selfApp]
  exact Nat.le_trans (φ.map_grade_poly _) (φ.bound.eval_mono (hf x hx))

/-- PolyGRRetraction consequence closure: a PolyGRRetraction induces a
    consequence-closed transport on M₂ (restricted to the image of φ).
    The overhead is the polynomial bound's contribution at a given grade.

    Concretely: φ maps realizable elements to realizable elements with
    polynomial grade shift, which is exactly what consequence closure
    requires when the transport is φ.map itself. -/
theorem PolyGRRetraction.consequence_closure {M₁ M₂ : GradedReflModel}
    (φ : PolyGRRetraction M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable M₁ x d) :
    Realizable M₂ (φ.map x) (φ.bound.eval d) :=
  φ.preserves_realizable x d hr

/-- The structural retraction (Section 15) yields a PolyGRRetraction
    T(M) → T(T(M)) via the lift morphism. Since the lift is already a
    strict GRM morphism, this is immediate through the hierarchy
    GRMorphism → GRRetraction → PolyGRRetraction. -/
def transport_lift_polyRetraction (M : GradedReflModel) :
    PolyGRRetraction (transportGradedReflModel M)
                     (transportGradedReflModel (transportGradedReflModel M)) :=
  (transport_lift_morphism M).toPolyGRRetraction

/-- Composition of PolyBound evaluations: the nested application
    q.eval(p.eval(n)) is bounded by a single PolyBound with
    degree (d₁+1)*d₂ and constant (2*(c₁+1))^d₂ + c₂. -/
def PolyBound.comp (p q : PolyBound) : PolyBound :=
  ⟨(p.degree + 1) * q.degree,
   (2 * (p.constant + 1)) ^ q.degree + q.constant⟩

/-- Auxiliary: when n^(d+1) < n^d + c, we have n^d + c ≤ 2*(c+1).
    This holds because n must be small (≤ 1 or n^d < c). -/
private theorem bound_when_pow_small {n d c : Nat}
    (h : n ^ (d + 1) < n ^ d + c) :
    n ^ d + c ≤ 2 * (c + 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- n ≤ 1: n^d ≤ 1
    have hnd : n ^ d ≤ 1 := by
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hn) with rfl | h
      · simp
      · have : n = 0 := by omega
        subst this; cases d <;> simp
    omega
  · -- n ≥ 2: from n^(d+1) = n * n^d < n^d + c, get n^d < c
    rw [Nat.pow_succ'] at h
    have : n ^ d < c := by
      have h2 : 2 * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hn
      omega
    omega

private theorem PolyBound.comp_eval_le (p q : PolyBound) (n : Nat) :
    q.eval (p.eval n) ≤ (PolyBound.comp p q).eval n := by
  simp only [PolyBound.eval, PolyBound.comp]
  suffices h : (n ^ p.degree + p.constant) ^ q.degree ≤
      n ^ ((p.degree + 1) * q.degree) + (2 * (p.constant + 1)) ^ q.degree by
    omega
  rcases Nat.lt_or_ge (n ^ (p.degree + 1)) (n ^ p.degree + p.constant) with h | h
  · -- n^(d₁+1) < n^d₁ + c₁: constant term dominates
    have hb := bound_when_pow_small h
    calc (n ^ p.degree + p.constant) ^ q.degree
        ≤ (2 * (p.constant + 1)) ^ q.degree := Nat.pow_le_pow_left hb _
      _ ≤ n ^ ((p.degree + 1) * q.degree) + (2 * (p.constant + 1)) ^ q.degree :=
          Nat.le_add_left _ _
  · -- n^(d₁+1) ≥ n^d₁ + c₁: degree term dominates
    calc (n ^ p.degree + p.constant) ^ q.degree
        ≤ (n ^ (p.degree + 1)) ^ q.degree := Nat.pow_le_pow_left h _
      _ = n ^ ((p.degree + 1) * q.degree) := by rw [← Nat.pow_mul]
      _ ≤ n ^ ((p.degree + 1) * q.degree) + (2 * (p.constant + 1)) ^ q.degree :=
          Nat.le_add_right _ _

/-- Composing two PolyGRRetractions yields a PolyGRRetraction.
    The composed map ψ ∘ φ commutes with fold/unfold, with grade bounded
    by ψ.bound.eval(φ.bound.eval(grade(x))). -/
theorem PolyGRRetraction.compose {M₁ M₂ M₃ : GradedReflModel}
    (φ : PolyGRRetraction M₁ M₂) (ψ : PolyGRRetraction M₂ M₃) :
    ∃ (r : PolyGRRetraction M₁ M₃),
      r.map = ψ.map ∘ φ.map ∧
      ∀ x, M₃.grade (r.map x) ≤ ψ.bound.eval (φ.bound.eval (M₁.grade x)) := by
  refine ⟨⟨ψ.map ∘ φ.map, ?_, ?_, PolyBound.comp φ.bound ψ.bound, ?_⟩, rfl, ?_⟩
  · intro x; simp [Function.comp, φ.map_fold, ψ.map_fold]
  · intro x; simp [Function.comp, φ.map_unfold, ψ.map_unfold]
  · intro x
    calc M₃.grade (ψ.map (φ.map x))
        ≤ ψ.bound.eval (M₂.grade (φ.map x)) := ψ.map_grade_poly _
      _ ≤ ψ.bound.eval (φ.bound.eval (M₁.grade x)) :=
            ψ.bound.eval_mono (φ.map_grade_poly x)
      _ ≤ (PolyBound.comp φ.bound ψ.bound).eval (M₁.grade x) :=
            PolyBound.comp_eval_le φ.bound ψ.bound _
  · intro x
    calc M₃.grade (ψ.map (φ.map x))
        ≤ ψ.bound.eval (M₂.grade (φ.map x)) := ψ.map_grade_poly _
      _ ≤ ψ.bound.eval (φ.bound.eval (M₁.grade x)) :=
            ψ.bound.eval_mono (φ.map_grade_poly x)

end WTS
