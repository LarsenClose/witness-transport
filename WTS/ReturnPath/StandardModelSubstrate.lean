/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

StandardModelSubstrate: the invariant substrate made concrete.

In standardModel (carrier = Nat, fold = /2, unfold = 2x+1):
  selfApp(x) = 2 * (x / 2) + 1

For odd x: selfApp(x) = x (fixed point).
For even x: selfApp(x) = x + 1 (shifted to odd).

Therefore Im(selfApp) = odd naturals. The invariant substrate — where
the full iso holds, gradeGap = 0, and P = NP pointwise — is exactly
the odd numbers. The even numbers lie outside Im(selfApp): they are the
carrier engineering gap of standardModel, the part of the carrier where
naming cannot reach the computation substrate.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: selfApp in standardModel computes 2*(x/2)+1
-- ════════════════════════════════════════════════════════════

/-- selfApp in standardModel: unfold(fold(x)) = 2 * (x / 2) + 1. -/
theorem standardModel_selfApp_eq (x : Nat) :
    standardModel.selfApp x = 2 * (x / 2) + 1 := by
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 2: selfApp fixes odd numbers
-- ════════════════════════════════════════════════════════════

/-- For odd x, selfApp(x) = x. The odd numbers are fixed points. -/
theorem standardModel_selfApp_fixes_odd (x : Nat) (hodd : x % 2 = 1) :
    standardModel.selfApp x = x := by
  show 2 * (x / 2) + 1 = x; omega

-- ════════════════════════════════════════════════════════════
-- Section 3: selfApp shifts even numbers
-- ════════════════════════════════════════════════════════════

/-- For even x, selfApp(x) = x + 1. Even numbers are shifted to odd. -/
theorem standardModel_selfApp_shifts_even (x : Nat) (heven : x % 2 = 0) :
    standardModel.selfApp x = x + 1 := by
  show 2 * (x / 2) + 1 = x + 1; omega

-- ════════════════════════════════════════════════════════════
-- Section 4: selfApp always produces odd numbers
-- ════════════════════════════════════════════════════════════

/-- selfApp maps every element to an odd number.
    selfApp(x) = 2*(x/2)+1, which is always odd. -/
theorem standardModel_selfApp_odd (x : Nat) :
    ∃ k, standardModel.selfApp x = 2 * k + 1 := by
  exact ⟨x / 2, rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Im(selfApp) = odd naturals
-- ════════════════════════════════════════════════════════════

/-- Every odd number is in Im(selfApp): it is its own preimage. -/
theorem standardModel_odd_in_image (y : Nat) (hodd : y % 2 = 1) :
    ∃ x, standardModel.selfApp x = y :=
  ⟨y, standardModel_selfApp_fixes_odd y hodd⟩

/-- No even number is in Im(selfApp): selfApp always produces odds. -/
theorem standardModel_even_not_in_image (y : Nat) (heven : y % 2 = 0) :
    ¬∃ x : Nat, standardModel.selfApp x = y := by
  intro ⟨x, hx⟩
  have : standardModel.selfApp x = 2 * (x / 2) + 1 := rfl
  rw [this] at hx; subst hx; omega

/-- Characterization: y ∈ Im(selfApp) iff y is odd. -/
theorem standardModel_image_iff_odd (y : Nat) :
    (∃ x, standardModel.selfApp x = y) ↔ y % 2 = 1 := by
  constructor
  · intro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := standardModel_selfApp_odd x
    rw [hk] at hx; subst hx; omega
  · exact standardModel_odd_in_image y

-- ════════════════════════════════════════════════════════════
-- Section 6: P = NP on the substrate (odd naturals)
-- ════════════════════════════════════════════════════════════

/-- On the substrate (odd numbers), selfApp is the identity,
    so grade(selfApp(x)) = grade(x). P = NP pointwise. -/
theorem standardModel_substrate_PEqNP (x : Nat) (hodd : x % 2 = 1) :
    standardModel.grade (standardModel.selfApp x) = standardModel.grade x := by
  rw [standardModel_selfApp_fixes_odd x hodd]

/-- On the substrate, selfApp factors through every grade level. -/
theorem standardModel_substrate_factors (d : Nat) (x : Nat) (hodd : x % 2 = 1)
    (hle : standardModel.grade x ≤ d) :
    standardModel.grade (standardModel.selfApp x) ≤ d := by
  rw [standardModel_selfApp_fixes_odd x hodd]; exact hle

-- ════════════════════════════════════════════════════════════
-- Section 7: The naming gap — even naturals are outside
-- ════════════════════════════════════════════════════════════

/-- The even naturals are precisely the carrier engineering gap:
    elements outside Im(selfApp). For any even x, selfApp(x) ≠ x. -/
theorem standardModel_naming_gap (x : Nat) (heven : x % 2 = 0) :
    standardModel.selfApp x ≠ x := by
  show 2 * (x / 2) + 1 ≠ x; omega

/-- The grade shift on evens: selfApp increases grade.
    This is the concrete content of the carrier engineering gap:
    naming (selfApp) costs grade on elements outside the substrate. -/
theorem standardModel_grade_shift_even (k : Nat) :
    standardModel.grade (standardModel.selfApp (2 * k)) > standardModel.grade (2 * k) := by
  have h := standardModel_overflow k
  omega

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms standardModel_selfApp_eq
#print axioms standardModel_selfApp_fixes_odd
#print axioms standardModel_selfApp_shifts_even
#print axioms standardModel_selfApp_odd
#print axioms standardModel_odd_in_image
#print axioms standardModel_even_not_in_image
#print axioms standardModel_image_iff_odd
#print axioms standardModel_substrate_PEqNP
#print axioms standardModel_substrate_factors
#print axioms standardModel_naming_gap
#print axioms standardModel_grade_shift_even

end WTS
