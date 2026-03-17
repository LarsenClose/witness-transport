/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/WitnessTransportCore.lean — Transport, Projection, Realization
on graded reflexive models. Abstract foundation for the cryptoeconomy chain.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Transport
-- ════════════════════════════════════════════════════════════

/-- A transport relation on a graded reflexive model: a way to move
    carrier elements while tracking grade change.
    Transport is a morphism in the grade-indexed category. -/
structure Transport (M : GradedReflModel) where
  /-- The transport map -/
  move : M.carrier → M.carrier
  /-- Transport has bounded overhead: grade increases by at most `overhead` -/
  overhead : Nat
  /-- Grade bound: transported element's grade is bounded -/
  h_grade_bound : ∀ x, M.grade (move x) ≤ M.grade x + overhead

-- ════════════════════════════════════════════════════════════
-- Section 2: Projection
-- ════════════════════════════════════════════════════════════

/-- A projection on a graded reflexive model: reduces grade, discarding
    structure. The key property: fold still works on projected data
    (certify survives), but selfApp may not (extract may fail). -/
structure Projection (M : GradedReflModel) where
  /-- The projection map -/
  project : M.carrier → M.carrier
  /-- Target grade bound -/
  target_grade : Nat
  /-- Projection reduces grade to at most target_grade -/
  h_reduces : ∀ x, M.grade (project x) ≤ target_grade
  /-- Projection is idempotent -/
  h_idempotent : ∀ x, project (project x) = project x

/-- Certify-preservation: fold commutes with projection.
    This captures the non-trivial property that the verification operation
    (fold) respects the projection structure. Parallel to blocksExtract,
    which checks whether selfApp commutes with projection. -/
def Projection.preservesCertify (M : GradedReflModel) (p : Projection M) : Prop :=
  ∀ x, M.fold (p.project x) = p.project (M.fold x)

/-- Extract-blocking: selfApp does NOT factor through the projection.
    There exist inputs where selfApp(project(x)) ≠ project(selfApp(x)). -/
def Projection.blocksExtract (M : GradedReflModel) (p : Projection M) : Prop :=
  ∃ x, M.selfApp (p.project x) ≠ p.project (M.selfApp x)

-- ════════════════════════════════════════════════════════════
-- Section 3: Realization
-- ════════════════════════════════════════════════════════════

/-- Realization: the condition under which a transported/projected element
    can drive action. An element is realizable at grade d if applying fold
    to it produces a result that still has grade ≤ d. -/
def Realizable (M : GradedReflModel) (x : M.carrier) (d : Nat) : Prop :=
  M.grade x ≤ d ∧ M.grade (M.fold x) ≤ d

-- ════════════════════════════════════════════════════════════
-- Section 4: Transport operations
-- ════════════════════════════════════════════════════════════

/-- Transport composition: two transports compose into one with summed overhead. -/
def Transport.compose (M : GradedReflModel) (t₁ t₂ : Transport M) : Transport M where
  move := t₂.move ∘ t₁.move
  overhead := t₁.overhead + t₂.overhead
  h_grade_bound := fun x => by
    have h1 : M.grade (t₁.move x) ≤ M.grade x + t₁.overhead := t₁.h_grade_bound x
    have h2 : M.grade (t₂.move (t₁.move x)) ≤ M.grade (t₁.move x) + t₂.overhead :=
      t₂.h_grade_bound (t₁.move x)
    show M.grade (t₂.move (t₁.move x)) ≤ M.grade x + (t₁.overhead + t₂.overhead)
    omega

/-- Consequence closure: a transport is consequence-closed if realizability
    is preserved. If x is realizable at grade d before transport, then
    move(x) is realizable at grade d + overhead after transport. -/
def Transport.consequenceClosed (M : GradedReflModel) (t : Transport M) : Prop :=
  ∀ x d, Realizable M x d → Realizable M (t.move x) (d + t.overhead)

/-- Transport collapse: a transported element can be realized at the SAME
    grade as the original (zero overhead). This is the distributed analogue
    of certify/extract collapse. -/
def TransportCollapse (M : GradedReflModel) : Prop :=
  ∃ t : Transport M, t.overhead = 0 ∧
    ∀ x d, Realizable M x d → Realizable M (t.move x) d

/-- Projection collapse: projection preserves certify AND does not block
    extract. This means the projection is trivial (doesn't actually
    discard anything relevant). -/
def ProjectionCollapse (M : GradedReflModel) : Prop :=
  ∃ p : Projection M,
    p.preservesCertify M ∧ ¬p.blocksExtract M

-- ════════════════════════════════════════════════════════════
-- Section 5: The identity transport
-- ════════════════════════════════════════════════════════════

/-- The identity transport: moves nothing, zero overhead. -/
def Transport.identity (M : GradedReflModel) : Transport M where
  move := id
  overhead := 0
  h_grade_bound := fun _ => Nat.le_refl _

-- ════════════════════════════════════════════════════════════
-- Section 6: Core theorems
-- ════════════════════════════════════════════════════════════

/-- Transport composes: the composition overhead is the sum of the two overheads. -/
theorem transport_compose (M : GradedReflModel) (t₁ t₂ : Transport M) :
    (Transport.compose M t₁ t₂).overhead = t₁.overhead + t₂.overhead := rfl

/-- Consequence-closed transports compose. -/
theorem consequence_closed_compose_pair (M : GradedReflModel)
    (t₁ t₂ : Transport M)
    (h₁ : t₁.consequenceClosed M) (h₂ : t₂.consequenceClosed M) :
    (Transport.compose M t₁ t₂).consequenceClosed M := by
  intro x d hreal
  have hr1 : Realizable M (t₁.move x) (d + t₁.overhead) := h₁ x d hreal
  have hr2 : Realizable M (t₂.move (t₁.move x)) (d + t₁.overhead + t₂.overhead) :=
    h₂ (t₁.move x) (d + t₁.overhead) hr1
  show Realizable M ((Transport.compose M t₁ t₂).move x)
    (d + (Transport.compose M t₁ t₂).overhead)
  simp only [Transport.compose]
  show Realizable M (t₂.move (t₁.move x)) (d + (t₁.overhead + t₂.overhead))
  have heq : d + t₁.overhead + t₂.overhead = d + (t₁.overhead + t₂.overhead) := by omega
  rw [← heq]; exact hr2

/-- The identity transport is consequence-closed. -/
theorem identity_consequence_closed (M : GradedReflModel) :
    (Transport.identity M).consequenceClosed M := by
  intro x d hreal
  simp only [Transport.identity, Nat.add_zero]
  exact hreal

/-- Projection preserves certify when fold commutes with project.
    This is a genuine property: not all projections satisfy it.
    Compare with blocksExtract, which checks selfApp non-commutativity. -/
theorem projection_certify_from_fold_compat (M : GradedReflModel)
    (p : Projection M)
    (h_fold_compat : ∀ x, M.fold (p.project x) = p.project (M.fold x)) :
    p.preservesCertify M :=
  h_fold_compat

/-- Projection idempotent: projecting twice = projecting once. -/
theorem projection_idempotent (M : GradedReflModel) (p : Projection M) :
    ∀ x, p.project (p.project x) = p.project x := p.h_idempotent

/-- Projection reduces grade to at most target_grade. -/
theorem projection_grade_bounded (M : GradedReflModel) (p : Projection M) :
    ∀ x, M.grade (p.project x) ≤ p.target_grade := p.h_reduces

-- ════════════════════════════════════════════════════════════
-- Section 7: Projection blocking extract
-- ════════════════════════════════════════════════════════════

/-- When projection is a retraction on grade-bounded elements (project(x) = x
    whenever grade(x) ≤ target_grade) and selfApp is unbounded, projection
    blocks extract.

    Proof: hub gives x with grade(x) ≤ target_grade and grade(selfApp(x)) > target_grade.
    Since project(x) = x (by h_retract), if selfApp(project(x)) = project(selfApp(x))
    then selfApp(x) = project(selfApp(x)), so grade(selfApp(x)) ≤ target_grade. Contradiction. -/
theorem projection_blocks_extract_when_retraction (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (p : Projection M)
    (h_retract : ∀ x, M.grade x ≤ p.target_grade → p.project x = x) :
    p.blocksExtract M := by
  obtain ⟨x, hle, hgt⟩ := hub.overflows p.target_grade
  -- show ∃ z, selfApp(project(z)) ≠ project(selfApp(z))
  refine ⟨x, ?_⟩
  intro heq
  -- heq : selfApp(project(x)) = project(selfApp(x))
  rw [h_retract x hle] at heq
  -- heq : selfApp(x) = project(selfApp(x))
  have hred : M.grade (p.project (M.selfApp x)) ≤ p.target_grade := p.h_reduces _
  rw [← heq] at hred
  -- hred : grade(selfApp(x)) ≤ target_grade, contradicts hgt
  omega

/-- Projection blocks extract when selfApp is unbounded and projection is
    a retraction on grade-bounded elements (h_retract condition). The nontriviality
    (existence of high-grade elements) follows automatically from hub. -/
theorem projection_blocks_extract_when_unbounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (p : Projection M)
    (h_retract : ∀ x, M.grade x ≤ p.target_grade → p.project x = x) :
    p.blocksExtract M :=
  projection_blocks_extract_when_retraction M hub p h_retract

-- ════════════════════════════════════════════════════════════
-- Section 8: Transport collapse consequences
-- ════════════════════════════════════════════════════════════

/-- Transport collapse implies grade-preserving map exists:
    t.move maps grade-d inputs to grade-d outputs (zero overhead). -/
theorem transport_collapse_implies_grade_preserved (M : GradedReflModel)
    (h : TransportCollapse M) :
    ∃ (f : M.carrier → M.carrier),
      (∀ x d, M.grade x ≤ d → M.grade (f x) ≤ d) := by
  obtain ⟨t, hzero, _hpres⟩ := h
  exact ⟨t.move, fun x d hx => by
    have hb := t.h_grade_bound x
    rw [hzero, Nat.add_zero] at hb
    exact Nat.le_trans hb hx⟩

/-- Transport collapse with realizability preservation. -/
theorem transport_collapse_preserves_realizable (M : GradedReflModel)
    (h : TransportCollapse M) :
    ∃ (f : M.carrier → M.carrier),
      ∀ x d, Realizable M x d → Realizable M (f x) d := by
  obtain ⟨t, _hzero, hpres⟩ := h
  exact ⟨t.move, hpres⟩

/-- Conservativity: trivialModel has transport collapse. -/
theorem trivialModel_transport_collapse :
    TransportCollapse trivialModel :=
  ⟨Transport.identity trivialModel, rfl, fun _ _ hr => hr⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: Projection collapse and bounded selfApp
-- ════════════════════════════════════════════════════════════

/-- Projection collapse with retraction implies selfApp is grade-bounded.

    If projection commutes with selfApp AND projection is a retraction on
    grade-bounded elements, then for x with grade(x) ≤ target_grade:
    project(x) = x, selfApp(project(x)) = project(selfApp(x)),
    so selfApp(x) = project(selfApp(x)), so grade(selfApp(x)) ≤ target_grade. -/
theorem projection_collapse_implies_bounded (M : GradedReflModel)
    (p : Projection M)
    (h_commutes : ∀ x, M.selfApp (p.project x) = p.project (M.selfApp x))
    (h_retract : ∀ x, M.grade x ≤ p.target_grade → p.project x = x) :
    ∀ x, M.grade x ≤ p.target_grade → M.grade (M.selfApp x) ≤ p.target_grade := by
  intro x hx
  have heq := h_commutes x
  rw [h_retract x hx] at heq
  -- heq : selfApp(x) = project(selfApp(x))
  rw [heq]
  exact p.h_reduces _

end WTS
