/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/ConsequenceClosureCore.lean — Transport chain composition
and consequence-closure propagation.

STATUS: 0 sorry, 0 Classical.choice. All theorems: propext + Quot.sound only.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Transport chains
-- ════════════════════════════════════════════════════════════

/-- A transport chain: a finite sequence of transport steps. -/
structure TransportChain (M : GradedReflModel) where
  length : Nat
  steps : Fin length → Transport M

/-- A chain is fully consequence-closed if every step is. -/
def TransportChain.fullyConsequenceClosed {M : GradedReflModel}
    (c : TransportChain M) : Prop :=
  ∀ k : Fin c.length, (c.steps k).consequenceClosed M

/-- Prefix truncation: first k steps of a chain. -/
def TransportChain.truncate {M : GradedReflModel} (c : TransportChain M)
    (k : Nat) (hk : k ≤ c.length) : TransportChain M where
  length := k
  steps := fun i => c.steps ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Pair-level composition (the core compositional result)
-- ════════════════════════════════════════════════════════════

/-- THE COMPOSITION THEOREM (pair form): if t₁ and t₂ are each consequence-closed,
    applying t₁ then t₂ preserves realizability with total overhead t₁.overhead + t₂.overhead.
    This is the fundamental building block for chain composition. -/
theorem consequence_closed_compose (M : GradedReflModel)
    (t₁ t₂ : Transport M)
    (h₁ : t₁.consequenceClosed M) (h₂ : t₂.consequenceClosed M) :
    (Transport.compose M t₁ t₂).consequenceClosed M :=
  consequence_closed_compose_pair M t₁ t₂ h₁ h₂

/-- Consequence-closed transport composes (explicit two-step form): if x is
    realizable at d and t₁, t₂ are consequence-closed, then t₂(t₁(x)) is
    realizable at d + t₁.overhead + t₂.overhead. -/
theorem two_step_consequence_closed (M : GradedReflModel)
    (t₁ t₂ : Transport M)
    (h₁ : t₁.consequenceClosed M) (h₂ : t₂.consequenceClosed M)
    (x : M.carrier) (d : Nat) (hr : Realizable M x d) :
    Realizable M (t₂.move (t₁.move x)) (d + t₁.overhead + t₂.overhead) :=
  h₂ (t₁.move x) (d + t₁.overhead) (h₁ x d hr)

-- ════════════════════════════════════════════════════════════
-- Section 3: Inductive chain composition
-- ════════════════════════════════════════════════════════════

/-- A fully consequence-closed 2-chain: t₁ then t₂, each consequence-closed,
    gives a consequence-closed composed transport. -/
theorem chain_two_consequence_closed {M : GradedReflModel}
    (c : TransportChain M) (h2 : c.length = 2)
    (hc : c.fullyConsequenceClosed) :
    ∀ x d, Realizable M x d →
      Realizable M ((c.steps ⟨1, h2 ▸ Nat.lt_of_sub_eq_succ rfl⟩).move
        ((c.steps ⟨0, h2 ▸ Nat.zero_lt_two⟩).move x))
        (d + (c.steps ⟨0, h2 ▸ Nat.zero_lt_two⟩).overhead +
             (c.steps ⟨1, h2 ▸ Nat.lt_of_sub_eq_succ rfl⟩).overhead) := by
  intro x d hr
  exact two_step_consequence_closed M
    (c.steps ⟨0, h2 ▸ Nat.zero_lt_two⟩)
    (c.steps ⟨1, h2 ▸ Nat.lt_of_sub_eq_succ rfl⟩)
    (hc ⟨0, h2 ▸ Nat.zero_lt_two⟩)
    (hc ⟨1, h2 ▸ Nat.lt_of_sub_eq_succ rfl⟩)
    x d hr

-- ════════════════════════════════════════════════════════════
-- Section 4: Degradation and incoherence
-- ════════════════════════════════════════════════════════════

/-- A chain has degradation at step k if that step is not consequence-closed
    and some realizable input becomes unrealizable after transport. -/
def TransportChain.hasDegradationAt {M : GradedReflModel} (c : TransportChain M)
    (k : Fin c.length) : Prop :=
  ¬(c.steps k).consequenceClosed M ∧
  ∃ x d, Realizable M x d ∧ ¬Realizable M ((c.steps k).move x) (d + (c.steps k).overhead)

/-- A degradation witness implies the transport step is not consequence-closed.
    Constructive direction: given a concrete input that loses realizability,
    conclude non-closure. -/
theorem degradation_witness_implies_incoherent (M : GradedReflModel) (t : Transport M)
    (x : M.carrier) (d : Nat)
    (hr : Realizable M x d) (hnr : ¬Realizable M (t.move x) (d + t.overhead)) :
    ¬t.consequenceClosed M :=
  fun hcc => hnr (hcc x d hr)

/-- If a step has degradation, there exists a witness input that is realizable
    before the step but unrealizable after. -/
theorem degradation_implies_witness {M : GradedReflModel} (c : TransportChain M)
    (k : Fin c.length) (hd : c.hasDegradationAt k) :
    ∃ x d, Realizable M x d ∧ ¬Realizable M ((c.steps k).move x) (d + (c.steps k).overhead) :=
  hd.2

-- ════════════════════════════════════════════════════════════
-- Section 5: Prefix consequence closure
-- ════════════════════════════════════════════════════════════

/-- A prefix of a fully-closed chain is fully-closed. -/
theorem prefix_fullyConsequenceClosed {M : GradedReflModel}
    (c : TransportChain M) (h : c.fullyConsequenceClosed)
    (k : Nat) (hk : k ≤ c.length) :
    (c.truncate k hk).fullyConsequenceClosed :=
  fun i => h ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Zero-degradation characterization
-- ════════════════════════════════════════════════════════════

/-- Consequence closure implies no degradation at any step.
    Constructive direction: if every step is consequence-closed,
    no step can exhibit degradation (the witness would contradict closure). -/
theorem closed_implies_no_degradation {M : GradedReflModel} (c : TransportChain M)
    (h : c.fullyConsequenceClosed) :
    ∀ k : Fin c.length, ¬c.hasDegradationAt k :=
  fun k ⟨hnc, _⟩ => hnc (h k)

-- ════════════════════════════════════════════════════════════
-- Section 7: Conservativity on trivialModel
-- ════════════════════════════════════════════════════════════

/-- On trivialModel, every element is realizable at any grade. -/
private theorem trivialModel_realizable (x : trivialModel.carrier) (d : Nat) :
    Realizable trivialModel x d := by
  cases x
  constructor
  · -- grade(()) = 0 ≤ d
    show trivialModel.grade () ≤ d
    simp [trivialModel]
  · -- grade(fold(())) = grade(()) = 0 ≤ d
    show trivialModel.grade (trivialModel.fold ()) ≤ d
    simp [trivialModel]

/-- On trivialModel, every transport step is consequence-closed. -/
theorem trivialModel_step_closed (t : Transport trivialModel) :
    t.consequenceClosed trivialModel := by
  intro x d _
  exact trivialModel_realizable (t.move x) (d + t.overhead)

/-- On trivialModel, every chain is fully consequence-closed. -/
theorem trivialModel_all_closed (c : TransportChain trivialModel) :
    c.fullyConsequenceClosed :=
  fun k => trivialModel_step_closed (c.steps k)

end WTS
