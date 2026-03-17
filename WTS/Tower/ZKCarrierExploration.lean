/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/ZKCarrierExploration.lean — Carrier engineering: obstruction, escape, witnesses.

The naive approach to the carrier engineering gap (setting fold = red) fails:
an idempotent fold forces selfApp to be grade-non-increasing whenever the grade
function factors through fold. The factorization theorem shows the escape:
fold = e' ∘ r where e embeds into Fix(r) and e' retracts. This fold is NOT
idempotent, escaping the obstruction. The divisorModel family demonstrates
the construction concretely for all k ≥ 2.

STATUS: 0 sorry.
-/

import WTS.Core
import WTS.Tower.ForcingPredicates

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The idempotent-fold obstruction
-- ════════════════════════════════════════════════════════════

/-- If fold is idempotent, fold absorbs selfApp:
    fold(selfApp(x)) = fold(x) for all x.
    Proof: selfApp(x) = unfold(fold(x)), so
    fold(selfApp(x)) = fold(unfold(fold(x))) = fold(x) by roundtrip.
    Note: h_idem is not used -- the absorption follows from roundtrip alone.
    The hypothesis is retained because the theorem is about the setting
    where fold IS idempotent; the proof shows the constraint is structural. -/
theorem idempotent_fold_absorbs_selfApp (M : GradedReflModel)
    (_h_idem : ∀ x, M.fold (M.fold x) = M.fold x) :
    ∀ x, M.fold (M.selfApp x) = M.fold x := by
  intro x; show M.fold (M.unfold (M.fold x)) = M.fold x; rw [M.roundtrip]

/-- When fold is idempotent and grade-non-increasing,
    grade(fold(selfApp(x))) ≤ grade(x). The grade of fold's output
    after selfApp is bounded by the original grade. -/
theorem bounded_fold_constrains_carrier (M : GradedReflModel)
    (h_idem : ∀ x, M.fold (M.fold x) = M.fold x)
    (h_le : ∀ x, M.grade (M.fold x) ≤ M.grade x) :
    ∀ x, M.grade (M.fold (M.selfApp x)) ≤ M.grade x := by
  intro x
  rw [idempotent_fold_absorbs_selfApp M h_idem x]
  exact h_le x

/-- Stronger: if fold is idempotent AND grade = grade ∘ fold
    (the grade function sees only fold's image), then selfApp
    is grade-non-increasing. An idempotent fold with grade
    factoring through it forces PEqNP -- it cannot produce separation. -/
theorem capExp_fold_constrains_carrier (M : GradedReflModel)
    (h_idem : ∀ x, M.fold (M.fold x) = M.fold x)
    (h_grade_fold : ∀ x, M.grade x = M.grade (M.fold x)) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x := by
  intro x
  have h1 : M.grade (M.selfApp x) = M.grade (M.fold x) := by
    rw [h_grade_fold (M.selfApp x),
        idempotent_fold_absorbs_selfApp M h_idem x]
  have h2 : M.grade (M.fold x) = M.grade x := (h_grade_fold x).symm
  omega

-- ════════════════════════════════════════════════════════════
-- Section 2: The factorization escape
-- ════════════════════════════════════════════════════════════

/-- Data for the factorization theorem: a grade-non-increasing
    retraction r on a carrier C, with an embedding e into Fix(r)
    and a retraction e' (left inverse of e). -/
structure RetractionData where
  C : Type
  r : C → C
  grade : C → Nat
  r_idempotent : ∀ x, r (r x) = r x
  r_grade_le : ∀ x, grade (r x) ≤ grade x
  e : C → C          -- embedding into Fix(r)
  e' : C → C         -- retraction from Fix(r)
  e_into_fix : ∀ x, r (e x) = e x   -- e maps into fixed points of r
  sect : ∀ x, e' (e x) = x          -- e' is left inverse of e

/-- The factorization theorem: any grade-non-increasing retraction
    with an embedding into its fixed points yields a GRM.
    The key construction: fold = e' ∘ r, unfold = e.
    This fold is NOT idempotent in general, escaping the obstruction. -/
def retraction_to_grm (rd : RetractionData) : GradedReflModel where
  carrier := rd.C
  fold x := rd.e' (rd.r x)
  unfold := rd.e
  roundtrip x := by
    show rd.e' (rd.r (rd.e x)) = x
    rw [rd.e_into_fix]; exact rd.sect x
  grade := rd.grade

/-- selfApp of the factorized GRM: e ∘ e' ∘ r. -/
theorem retraction_to_grm_selfApp (rd : RetractionData) (x : rd.C) :
    (retraction_to_grm rd).selfApp x = rd.e (rd.e' (rd.r x)) := rfl

-- ════════════════════════════════════════════════════════════
-- Section 3: The divisorModel family
-- ════════════════════════════════════════════════════════════

/-- Parametrized Group B witnesses: fold = x/k, unfold = k*x.
    selfApp rounds down to the nearest multiple of k.
    For k ≥ 2: selfApp ≠ id but PEqNP holds. fold is not idempotent. -/
def divisorModel (k : Nat) (hk : k ≥ 2) : GradedReflModel where
  carrier := Nat
  fold x := x / k
  unfold x := k * x
  roundtrip x := Nat.mul_div_cancel_left x (by omega : 0 < k)
  grade := id

/-- selfApp is grade-non-increasing in divisorModel:
    k * (x/k) ≤ x (integer division rounds down). -/
theorem divisorModel_selfApp_le (k : Nat) (hk : k ≥ 2) (x : Nat) :
    (divisorModel k hk).grade ((divisorModel k hk).selfApp x) ≤
    (divisorModel k hk).grade x := by
  simp only [GradedReflModel.selfApp, divisorModel, id]
  exact Nat.mul_div_le x k

/-- selfApp ≠ id: selfApp(1) = k*(1/k) = k*0 = 0 ≠ 1 for k ≥ 2. -/
theorem divisorModel_selfApp_ne_id (k : Nat) (hk : k ≥ 2) :
    ∃ x : Nat, (divisorModel k hk).selfApp x ≠ x := by
  refine ⟨(1 : Nat), ?_⟩
  show k * (1 / k) ≠ 1
  rw [Nat.div_eq_of_lt (by omega : 1 < k)]; omega

/-- PEqNP holds: selfApp is grade-non-increasing, so FactorsThrough at d = 0. -/
theorem divisorModel_PEqNP (k : Nat) (hk : k ≥ 2) :
    PEqNP (divisorModel k hk) :=
  ⟨0, fun x hx => Nat.le_trans (divisorModel_selfApp_le k hk x) hx⟩

/-- fold = x/k is NOT idempotent: fold(fold(k²)) = 1 ≠ k = fold(k²).
    This confirms the factorization escape -- the fold is not the
    red operation itself. -/
theorem divisorModel_fold_not_idempotent (k : Nat) (hk : k ≥ 2) :
    ∃ x : Nat, (divisorModel k hk).fold ((divisorModel k hk).fold x) ≠
         (divisorModel k hk).fold x := by
  refine ⟨k * k, ?_⟩
  show (k * k / k) / k ≠ k * k / k
  rw [Nat.mul_div_cancel_left k (by omega : 0 < k),
      Nat.div_self (by omega : 0 < k)]
  omega

-- ════════════════════════════════════════════════════════════
-- Section 4: divisorModel IS the factorization
-- ════════════════════════════════════════════════════════════

/-- The retraction data for divisorModel: r(x) = k*(x/k),
    e(x) = k*x (embeds into multiples of k = Fix(r)),
    e'(x) = x/k (retracts back). -/
def divisorRetractionData (k : Nat) (hk : k ≥ 2) : RetractionData where
  C := Nat
  r x := k * (x / k)
  grade := id
  r_idempotent x := by
    show k * (k * (x / k) / k) = k * (x / k)
    rw [Nat.mul_div_cancel_left (x / k) (by omega : 0 < k)]
  r_grade_le x := by simp [id]; exact Nat.mul_div_le x k
  e x := k * x
  e' x := x / k
  e_into_fix x := by
    show k * (k * x / k) = k * x
    rw [Nat.mul_div_cancel_left x (by omega : 0 < k)]
  sect x := Nat.mul_div_cancel_left x (by omega : 0 < k)

-- ════════════════════════════════════════════════════════════
-- Section 5: General embedding from enumeration
-- ════════════════════════════════════════════════════════════

/-- Given any idempotent retraction r on a type C with an enumeration
    of Fix(r) (a bijection enum : C ≃ Fix(r) as witnessed by enum/decode),
    construct the RetractionData. This is the general pattern that
    divisorModel instantiates arithmetically.

    The construction: e = enum, e' = decode.
    - e_into_fix: r(enum(x)) = enum(x) because enum maps into Fix(r)
    - sect: decode(enum(x)) = x because decode is left inverse of enum -/
def retractionData_from_enumeration
    (C : Type)
    (r : C → C)
    (grade : C → Nat)
    (r_idempotent : ∀ x, r (r x) = r x)
    (r_grade_le : ∀ x, grade (r x) ≤ grade x)
    (enum : C → C)           -- maps into Fix(r)
    (decode : C → C)         -- left inverse of enum
    (enum_into_fix : ∀ x, r (enum x) = enum x)
    (decode_enum : ∀ x, decode (enum x) = x) :
    RetractionData where
  C := C
  r := r
  grade := grade
  r_idempotent := r_idempotent
  r_grade_le := r_grade_le
  e := enum
  e' := decode
  e_into_fix := enum_into_fix
  sect := decode_enum

/-- For Nat with an idempotent retraction: if the fixed-point set
    contains all multiples of some k ≥ 2, the divisor embedding works.
    This generalizes divisorModel to any retraction whose fixed points
    include the multiples. -/
def nat_retraction_via_multiples
    (r : Nat → Nat) (k : Nat) (hk : k ≥ 2)
    (r_idempotent : ∀ x, r (r x) = r x)
    (r_grade_le : ∀ x, r x ≤ x)
    (r_fixes_multiples : ∀ x, r (k * x) = k * x) :
    RetractionData :=
  retractionData_from_enumeration Nat r id
    r_idempotent (fun x => by simp [id]; exact r_grade_le x)
    (fun x => k * x) (fun x => x / k)
    r_fixes_multiples
    (fun x => Nat.mul_div_cancel_left x (by omega : 0 < k))

-- ════════════════════════════════════════════════════════════
-- Section 6: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms idempotent_fold_absorbs_selfApp
#print axioms bounded_fold_constrains_carrier
#print axioms capExp_fold_constrains_carrier
#print axioms retraction_to_grm
#print axioms retraction_to_grm_selfApp
#print axioms divisorModel
#print axioms divisorModel_selfApp_le
#print axioms divisorModel_selfApp_ne_id
#print axioms divisorModel_PEqNP
#print axioms divisorModel_fold_not_idempotent
#print axioms divisorRetractionData
#print axioms retractionData_from_enumeration
#print axioms nat_retraction_via_multiples

end WTS
