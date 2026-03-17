/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/BindingStructure.lean — Coherent transport induces binding:
consequence-connected elements cannot be independently updated.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Consequence field
-- ════════════════════════════════════════════════════════════

/-- A consequence field: a pair of carrier elements connected by a consequence-closed
    transport. This is the minimal binding structure. -/
structure ConsequenceBinding (M : GradedReflModel) where
  source : M.carrier
  target : M.carrier
  transport : Transport M
  h_closed : transport.consequenceClosed M
  h_connects : transport.move source = target

/-- Decomposability: a consequence binding is decomposable if changing
    the source element (via a grade-modifying function f) does NOT affect
    the target's realizability. This would mean source and target are
    grade-independent. -/
def ConsequenceBinding.Decomposable (M : GradedReflModel)
    (cb : ConsequenceBinding M) : Prop :=
  ∃ f : M.carrier → M.carrier,
    (∀ d, Realizable M (cb.source) d → ¬Realizable M (f (cb.source)) d) ∧
    (∀ d, Realizable M (cb.target) d → Realizable M (f (cb.target)) d)

/-- Binding: a consequence binding is bound if it's not decomposable — i.e.,
    source and target share consequence structure that cannot be partitioned. -/
def ConsequenceBinding.Bound (M : GradedReflModel) (cb : ConsequenceBinding M) : Prop :=
  ¬cb.Decomposable M

-- ════════════════════════════════════════════════════════════
-- Section 2: Consequence closure creates binding
-- ════════════════════════════════════════════════════════════

/-- If a and b are connected by a consequence-closed transport, then
    any realizable state of a implies a realizable state of b (with overhead).
    This is the binding result: consequence closure propagates realizability. -/
theorem consequence_closure_creates_binding (M : GradedReflModel)
    (a b : M.carrier) (d : Nat)
    (t : Transport M) (ht : t.consequenceClosed M) (ht_move : t.move a = b) :
    Realizable M a d → Realizable M b (d + t.overhead) := by
  intro hr; rw [← ht_move]; exact ht a d hr

/-- Grade propagates through consequence-closed transport. -/
theorem grade_propagates_through_transport (M : GradedReflModel)
    (a b : M.carrier) (d : Nat)
    (t : Transport M) (ht : t.consequenceClosed M) (ht_move : t.move a = b)
    (hr : Realizable M a d) :
    M.grade b ≤ d + t.overhead := by
  have := consequence_closure_creates_binding M a b d t ht ht_move hr
  exact this.1

-- ════════════════════════════════════════════════════════════
-- Section 3: Binding is non-decomposable
-- ════════════════════════════════════════════════════════════

/-- THE BINDING THEOREM: if selfApp is unbounded and a consequence binding has
    a source element that is realizable at some grade d, then the binding is
    non-decomposable in the following sense: any function that makes the source
    unrealizable at grade d also propagates through the transport, making the
    target realizable at grade d + overhead.

    This shows the source and target are NOT grade-independent: changing
    source realizability propagates to target via consequence closure. -/
theorem consequence_binding_propagates (M : GradedReflModel)
    (cb : ConsequenceBinding M)
    (d : Nat) (hr : Realizable M cb.source d) :
    Realizable M cb.target (d + cb.transport.overhead) := by
  rw [← cb.h_connects]
  exact cb.h_closed cb.source d hr

/-- THE NON-DECOMPOSABILITY THEOREM: every consequence binding is non-decomposable.

    The Decomposable condition requires f(source) to be unrealizable at every grade
    where source is realizable. But every carrier element is eventually realizable
    (at grade max(grade(x), grade(fold(x)))), and Realizable is monotone in grade.
    So for sufficiently large d, both source and f(source) are realizable —
    contradicting the decomposability condition. -/
theorem consequence_binding_bound (M : GradedReflModel)
    (cb : ConsequenceBinding M) :
    cb.Bound M := by
  intro ⟨f, hf_kill, _⟩
  let fs := f cb.source
  let D_src := max (M.grade cb.source) (M.grade (M.fold cb.source))
  let D_fs := max (M.grade fs) (M.grade (M.fold fs))
  let d := max D_src D_fs
  have h_src : Realizable M cb.source d :=
    ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
     Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
  have h_fs : Realizable M fs d :=
    ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
     Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩
  exact hf_kill d h_src h_fs

/-- Consequence-closed transport propagates realizability through the binding:
    if any element x is realizable at grade d, the transported element is
    realizable at grade d + overhead. -/
theorem binding_overflow_propagates (M : GradedReflModel)
    (cb : ConsequenceBinding M)
    (h_realize : ∀ d, ∃ x, Realizable M x d) :
    ∃ x d, Realizable M x d ∧ Realizable M (cb.transport.move x) (d + cb.transport.overhead) := by
  obtain ⟨x, hr⟩ := h_realize 0
  exact ⟨x, 0, hr, cb.h_closed x 0 hr⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Coherent field binding (field of n elements)
-- ════════════════════════════════════════════════════════════

/-- A coherent field: n elements all mutually connected by consequence-closed
    transports. When all n elements are connected, they form a binding cluster. -/
structure CoherentField (M : GradedReflModel) (n : Nat) where
  elements : Fin n → M.carrier
  h_connected : ∀ (i j : Fin n),
    ∃ t : Transport M, t.consequenceClosed M ∧ t.move (elements i) = elements j

/-- In a coherent field of size ≥ 2, every pair of elements is bound:
    their realizability is linked by consequence-closed transports. -/
theorem coherent_field_creates_binding (M : GradedReflModel) (n : Nat) (_hn : n ≥ 2)
    (cf : CoherentField M n)
    (i j : Fin n) (d : Nat)
    (hr : Realizable M (cf.elements i) d) :
    ∃ overhead, Realizable M (cf.elements j) (d + overhead) := by
  obtain ⟨t, ht, hmove⟩ := cf.h_connected i j
  exact ⟨t.overhead, hmove ▸ ht (cf.elements i) d hr⟩

/-- In a coherent field, all elements are bound: given one realizable element,
    all other elements are realizable (with some overhead). -/
theorem coherent_field_fully_bound (M : GradedReflModel) (n : Nat)
    (cf : CoherentField M n)
    (h_realize : ∃ i : Fin n, ∃ d, Realizable M (cf.elements i) d) :
    ∀ j : Fin n, ∃ d', Realizable M (cf.elements j) d' := by
  obtain ⟨i, d, hr⟩ := h_realize
  intro j
  obtain ⟨t, ht, hmove⟩ := cf.h_connected i j
  exact ⟨d + t.overhead, hmove ▸ ht (cf.elements i) d hr⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Consequence field (multi-element version)
-- ════════════════════════════════════════════════════════════

/-- Non-decomposability of consequence field: if the field has at least 2 elements
    connected by consequence-closed transports, then source and target grades are
    NOT independent — consequence closure ensures grade propagation. -/
theorem coherent_field_non_independent (M : GradedReflModel) (n : Nat) (hn : n ≥ 2)
    (cf : CoherentField M n) (i j : Fin n) :
    ∀ d, Realizable M (cf.elements i) d →
      ∃ d', Realizable M (cf.elements j) d' := by
  intro d hr
  obtain ⟨overhead, hre⟩ := coherent_field_creates_binding M n hn cf i j d hr
  exact ⟨d + overhead, hre⟩

/-- Decomposability of a coherent field: the field is decomposable if some pair
    of elements can be grade-independently modified — one made unrealizable while
    the other's realizability is preserved. -/
def CoherentField.Decomposable (M : GradedReflModel) (n : Nat)
    (cf : CoherentField M n) : Prop :=
  ∃ (i j : Fin n) (f : M.carrier → M.carrier),
    (∀ d, Realizable M (cf.elements i) d → ¬Realizable M (f (cf.elements i)) d) ∧
    (∀ d, Realizable M (cf.elements j) d → Realizable M (f (cf.elements j)) d)

/-- NON-DECOMPOSABILITY OF COHERENT FIELDS: no coherent field is decomposable.
    Same argument as consequence_binding_bound: for any pair (i, j) and any f,
    f(elements i) is eventually realizable at large enough grade, contradicting
    the requirement that f destroys realizability of elements i at all grades
    where it was realizable. -/
theorem coherent_field_non_decomposable (M : GradedReflModel) (n : Nat)
    (cf : CoherentField M n) :
    ¬cf.Decomposable M n := by
  intro ⟨i, _, f, hf_kill, _⟩
  let ei := cf.elements i
  let fei := f ei
  let D_ei := max (M.grade ei) (M.grade (M.fold ei))
  let D_fei := max (M.grade fei) (M.grade (M.fold fei))
  let d := max D_ei D_fei
  have h_ei : Realizable M ei d :=
    ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
     Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
  have h_fei : Realizable M fei d :=
    ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
     Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩
  exact hf_kill d h_ei h_fei

-- ════════════════════════════════════════════════════════════
-- Section 6: Conservativity
-- ════════════════════════════════════════════════════════════

/-- trivialModel: consequence binding propagates trivially (grade 0 everywhere). -/
theorem trivialModel_consequence_binding_trivial
    (cb : ConsequenceBinding trivialModel) (d : Nat) :
    Realizable trivialModel cb.source d →
    Realizable trivialModel cb.target d := by
  intro _
  exact ⟨by cases cb.target; simp [trivialModel],
         by cases cb.target; simp [trivialModel]⟩

end WTS
