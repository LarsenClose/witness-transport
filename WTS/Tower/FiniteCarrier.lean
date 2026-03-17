/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/FiniteCarrier.lean — On finite types, roundtrip forces selfApp = id.

If fold, unfold : Fin n → Fin n with fold ∘ unfold = id (roundtrip),
then unfold ∘ fold = id (selfApp = id). Pigeonhole forces fold bijective.

This means phase transition (nontrivial selfApp, SelfAppUnbounded)
requires infinite carriers. On finite types, P = NP is the only
consistent regime.

The proof uses fin_injective_le (pigeonhole on finite ordinals).

STATUS: 0 sorry.
-/

import WTS.Core

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Pigeonhole infrastructure
-- ════════════════════════════════════════════════════════════

/-- If there exists an injection Fin n → Fin m, then n ≤ m. -/
theorem fin_injective_le : ∀ (n m : Nat),
    (∃ (f : Fin n → Fin m), Function.Injective f) → n ≤ m := by
  intro n
  induction n with
  | zero => intro _ _; exact Nat.zero_le _
  | succ k ih =>
    intro m ⟨f, hf⟩
    match m with
    | 0 => exact absurd (f ⟨0, Nat.zero_lt_succ k⟩).isLt (Nat.not_lt_zero _)
    | Nat.succ m' =>
      suffices k ≤ m' by omega
      let t := f ⟨k, Nat.lt_succ_of_le (Nat.le_refl k)⟩
      let g : Fin k → Fin m' := fun i =>
        let vi := f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        have h_ne_t : vi ≠ t := by
          intro h_eq
          have := hf h_eq
          simp [Fin.ext_iff] at this
          exact absurd this (Nat.ne_of_lt i.isLt)
        if h_lt : vi.val < t.val then
          ⟨vi.val, by omega⟩
        else
          ⟨vi.val - 1, by
            have : vi.val ≠ t.val := fun h => h_ne_t (Fin.ext h)
            have : vi.val > t.val := by omega
            have : vi.val ≤ m' := by omega
            omega⟩
      apply ih m' ⟨g, ?_⟩
      intro a b h_eq_g
      have h_a_ne_val : (f ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩).val ≠ t.val := by
        intro h_eq
        have : (⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ : Fin (k + 1)) =
               ⟨k, Nat.lt_succ_of_le (Nat.le_refl k)⟩ := hf (Fin.ext h_eq)
        exact absurd (Fin.val_eq_of_eq this) (Nat.ne_of_lt a.isLt)
      have h_b_ne_val : (f ⟨b.val, Nat.lt_succ_of_lt b.isLt⟩).val ≠ t.val := by
        intro h_eq
        have : (⟨b.val, Nat.lt_succ_of_lt b.isLt⟩ : Fin (k + 1)) =
               ⟨k, Nat.lt_succ_of_le (Nat.le_refl k)⟩ := hf (Fin.ext h_eq)
        exact absurd (Fin.val_eq_of_eq this) (Nat.ne_of_lt b.isLt)
      have h_vals_eq : (f ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩).val =
          (f ⟨b.val, Nat.lt_succ_of_lt b.isLt⟩).val := by
        have h_v := Fin.val_eq_of_eq h_eq_g
        dsimp only [g] at h_v
        split at h_v <;> rename_i h1 <;> split at h_v <;> rename_i h2 <;>
          simp at h_v <;> omega
      exact Fin.ext (by
        have := Fin.val_eq_of_eq (hf (Fin.ext h_vals_eq))
        simpa [Fin.val] using this)

-- ════════════════════════════════════════════════════════════
-- Section 2: Decidable existence on Fin n
-- ════════════════════════════════════════════════════════════

/-- Decidable existence on Fin n: constructively search all elements. -/
private def finDecideExists : (n : Nat) → (p : Fin n → Prop) →
    (∀ i, Decidable (p i)) → Decidable (∃ i, p i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => absurd i.isLt (Nat.not_lt_zero _))
  | n + 1, p, inst =>
    let last : Fin (n + 1) := ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩
    match inst last with
    | isTrue h => isTrue ⟨last, h⟩
    | isFalse h_last =>
      match finDecideExists n
        (fun i : Fin n => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => inst ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) with
      | isTrue h => isTrue (by
          obtain ⟨i, hi⟩ := h
          exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩)
      | isFalse h_rest => isFalse (fun ⟨i, hi⟩ => by
          if h : i.val < n then
            exact h_rest ⟨⟨i.val, h⟩, by
              have : (⟨i.val, Nat.lt_succ_of_lt h⟩ : Fin (n + 1)) = i :=
                Fin.ext rfl
              rw [this]; exact hi⟩
          else
            have : i = last := by ext; show i.val = n; omega
            exact h_last (this ▸ hi))

-- ════════════════════════════════════════════════════════════
-- Section 3: Compression helper for pigeonhole
-- ════════════════════════════════════════════════════════════

/-- Compress Fin (n+1) into Fin n by skipping element y.
    Elements below y keep their value; elements above y shift down. -/
private def compressAway (n : Nat) (y : Fin (n + 1))
    (x : Fin (n + 1)) (hne : x ≠ y) : Fin n :=
  if h : x.val < y.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val - 1, by
      have : x.val ≠ y.val := fun h => hne (Fin.ext h)
      have : x.val < n + 1 := x.isLt
      omega⟩

/-- compressAway is injective on elements ≠ y. -/
private theorem compressAway_injective (n : Nat) (y : Fin (n + 1))
    (a b : Fin (n + 1)) (ha : a ≠ y) (hb : b ≠ y)
    (heq : compressAway n y a ha = compressAway n y b hb) : a = b := by
  apply Fin.ext
  have ha' : a.val ≠ y.val := fun h => ha (Fin.ext h)
  have hb' : b.val ≠ y.val := fun h => hb (Fin.ext h)
  have hv := Fin.val_eq_of_eq heq
  unfold compressAway at hv
  split at hv <;> rename_i h1 <;> split at hv <;> rename_i h2 <;>
    simp only [] at hv <;> omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Injective endofunction on Fin n is surjective
-- ════════════════════════════════════════════════════════════

/-- On Fin n, an injective endofunction is surjective.
    Proof by pigeonhole: if f misses some y, compress the codomain
    to Fin (n-1), giving an injection Fin n → Fin (n-1).
    By fin_injective_le, n ≤ n-1, contradicting n ≥ 1. -/
theorem fin_injective_surjective : ∀ (n : Nat) (f : Fin n → Fin n),
    Function.Injective f → Function.Surjective f
  | 0, _, _, y => absurd y.isLt (Nat.not_lt_zero _)
  | n + 1, f, hf, y => by
    -- Constructively decide whether y has a preimage
    match finDecideExists (n + 1) (fun x => f x = y) (fun x => decEq (f x) y) with
    | isTrue h => exact h
    | isFalse h_miss =>
      exfalso
      have h_ne : ∀ x, f x ≠ y := fun x heq => h_miss ⟨x, heq⟩
      -- Compress f through compressAway, giving injection Fin (n+1) → Fin n
      have : n + 1 ≤ n := by
        apply fin_injective_le (n + 1) n
        refine ⟨fun x => compressAway n y (f x) (h_ne x), ?_⟩
        intro a b heq_c
        exact hf (compressAway_injective n y (f a) (f b) (h_ne a) (h_ne b) heq_c)
      omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Left inverse is right inverse on Fin n
-- ════════════════════════════════════════════════════════════

/-- On Fin n, a left inverse is also a right inverse.
    If f ∘ g = id, then g ∘ f = id.

    Proof: g is injective (from f ∘ g = id), hence surjective
    (pigeonhole on Fin n). For any x, let z be such that g(z) = x.
    Then f(x) = f(g(z)) = z, so g(f(x)) = g(z) = x. -/
theorem fin_left_inverse_right_inverse (n : Nat) (f g : Fin n → Fin n)
    (h : ∀ x, f (g x) = x) : ∀ x, g (f x) = x := by
  have g_inj : Function.Injective g := by
    intro a b hab
    have : f (g a) = f (g b) := by rw [hab]
    rw [h, h] at this; exact this
  have g_surj := fin_injective_surjective n g g_inj
  intro x
  obtain ⟨z, hz⟩ := g_surj x
  have : f x = z := by rw [← hz, h]
  rw [this, hz]

-- ════════════════════════════════════════════════════════════
-- Section 6: Finite-carrier theorem
-- ════════════════════════════════════════════════════════════

/-- THE FINITE-CARRIER THEOREM.
    On Fin n, roundtrip (fold ∘ unfold = id) forces selfApp = id
    (unfold ∘ fold = id).

    Pigeonhole forces fold bijective: roundtrip makes unfold injective,
    which on Fin n makes unfold surjective. Then fold = unfold⁻¹,
    so fold is also a right inverse of unfold. -/
theorem fin_selfApp_eq_id (n : Nat)
    (fold unfold : Fin n → Fin n)
    (roundtrip : ∀ x, fold (unfold x) = x) :
    ∀ x, unfold (fold x) = x :=
  fin_left_inverse_right_inverse n fold unfold roundtrip

/-- Corollary: any GRM with carrier Fin n has selfApp = id.
    Phase transition requires infinite carriers. -/
theorem finite_grm_selfApp_eq_id (n : Nat)
    (fold unfold : Fin n → Fin n)
    (roundtrip : ∀ x, fold (unfold x) = x)
    (grade : Fin n → Nat) :
    ∀ x, (⟨Fin n, fold, unfold, roundtrip, grade⟩ : GradedReflModel).selfApp x = x :=
  fin_selfApp_eq_id n fold unfold roundtrip

/-- Phase transition requires infinite carriers.
    On Fin n, SelfAppUnbounded is impossible. -/
theorem finite_carrier_no_separation (n : Nat)
    (fold unfold : Fin n → Fin n)
    (roundtrip : ∀ x, fold (unfold x) = x)
    (grade : Fin n → Nat) :
    ¬SelfAppUnbounded (⟨Fin n, fold, unfold, roundtrip, grade⟩ : GradedReflModel) := by
  intro ⟨hov⟩
  obtain ⟨x, hle, hgt⟩ := hov 0
  have heq := fin_selfApp_eq_id n fold unfold roundtrip x
  -- Reduce structure projections so omega can see the arithmetic
  change grade (unfold (fold x)) > 0 at hgt
  rw [heq] at hgt
  exact absurd (Nat.lt_of_lt_of_le hgt hle) (Nat.lt_irrefl _)

/-- Nontrivial selfApp (and hence SelfAppUnbounded) requires
    an infinite carrier. Witnessed by standardModel (carrier = Nat). -/
theorem nontrivial_selfApp_requires_infinite_carrier :
    -- Finite: selfApp = id always
    (∀ (n : Nat) (fold unfold : Fin n → Fin n),
      (∀ x, fold (unfold x) = x) → ∀ x, unfold (fold x) = x) ∧
    -- Infinite (Nat): nontrivial selfApp exists
    (∃ M : GradedReflModel, ∃ x, M.selfApp x ≠ x) :=
  ⟨fun n fold unfold rt => fin_selfApp_eq_id n fold unfold rt,
   ⟨standardModel, (0 : Nat), by
     simp only [GradedReflModel.selfApp, standardModel]
     omega⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Finite carrier → gradeGap = 0
-- ════════════════════════════════════════════════════════════

/-- On finite carriers, selfApp = id implies gradeGap = 0 everywhere.
    Combined with fin_selfApp_eq_id, this means finite carriers are
    always at zero gradeGap — phase transition requires infinite carriers
    not just for SelfAppUnbounded but for any nonzero gradeGap. -/
theorem finite_carrier_zero_gap (n : Nat)
    (fold unfold : Fin n → Fin n)
    (roundtrip : ∀ x, fold (unfold x) = x)
    (grade : Fin n → Nat) :
    ∀ x, (grade (unfold (fold x)) : Int) - (grade x : Int) = 0 := by
  intro x
  have heq := fin_selfApp_eq_id n fold unfold roundtrip x
  rw [heq]; omega

/-- Finite carrier models are Group C: selfApp = id, gradeGap = 0, PEqNP. -/
theorem finite_carrier_groupC (n : Nat)
    (fold unfold : Fin n → Fin n)
    (roundtrip : ∀ x, fold (unfold x) = x)
    (grade : Fin n → Nat) :
    let M : GradedReflModel := ⟨Fin n, fold, unfold, roundtrip, grade⟩
    (∀ x, M.selfApp x = x) ∧
    (∀ x, (M.grade (M.selfApp x) : Int) - (M.grade x : Int) = 0) ∧
    PEqNP M :=
  let M : GradedReflModel := ⟨Fin n, fold, unfold, roundtrip, grade⟩
  ⟨fin_selfApp_eq_id n fold unfold roundtrip,
   fun x => by
    have := fin_selfApp_eq_id n fold unfold roundtrip x
    show (grade (unfold (fold x)) : Int) - (grade x : Int) = 0
    rw [this]; omega,
   ⟨0, fun x hx => by
    have := fin_selfApp_eq_id n fold unfold roundtrip x
    show grade (unfold (fold x)) ≤ 0
    rw [this]; exact hx⟩⟩

end WTS
