/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

RedIsSubstrate: connecting chain-specific red functions to InvariantSubstrate.

For Group B chains, the chain's computational content is captured by a
function red : carrier → carrier with selfApp = red (pointwise). Since
selfApp is idempotent (from roundtrip), red is idempotent. On Im(red),
red = id — this is exactly the invariant substrate.

The carrier engineering gap at each Group B chain is: how much of the
carrier lies outside Im(red)?

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.ReturnPath.InvariantSubstrate
import WTS.Tower.ForcingPredicates

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Red inherits idempotence from selfApp
-- ════════════════════════════════════════════════════════════

/-- If selfApp = red pointwise, then red is idempotent.
    Proof: selfApp is idempotent (from roundtrip), and selfApp = red. -/
theorem red_idempotent (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x) :
    ∀ x, red (red x) = red x := by
  intro x
  rw [← h_eq x, ← h_eq (M.selfApp x)]
  exact grm_roundtrip_forces_idempotent M x

-- ════════════════════════════════════════════════════════════
-- Section 2: Im(red) = Im(selfApp)
-- ════════════════════════════════════════════════════════════

/-- Fixed points of red are exactly fixed points of selfApp.
    If selfApp = red, then red(x) = x iff selfApp(x) = x. -/
theorem red_fixed_iff_selfApp_fixed (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    red x = x ↔ M.selfApp x = x := by
  constructor
  · intro h; rw [h_eq]; exact h
  · intro h; rw [← h_eq]; exact h

/-- Im(red) = Im(selfApp): y is in the image of red iff it is in
    the image of selfApp. Since selfApp = red, their images coincide. -/
theorem red_image_is_substrate (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x) :
    (∀ x, ∃ y, red y = red x ∧ M.selfApp y = red x) ∧
    (∀ x, ∃ y, M.selfApp y = M.selfApp x ∧ red y = M.selfApp x) := by
  constructor
  · intro x; exact ⟨x, rfl, by rw [h_eq]⟩
  · intro x; exact ⟨x, rfl, by rw [← h_eq]⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Red = id on its image
-- ════════════════════════════════════════════════════════════

/-- On Im(red), red = id. For any x, red(red(x)) = red(x),
    so red(x) is a fixed point of red. -/
theorem red_identity_on_image (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    red (red x) = red x :=
  red_idempotent M red h_eq x

/-- On Im(red), selfApp = id. Since selfApp = red and red is idempotent,
    selfApp fixes every element of Im(red). -/
theorem selfApp_identity_on_red_image (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    M.selfApp (red x) = red x := by
  rw [h_eq]; exact red_idempotent M red h_eq x

-- ════════════════════════════════════════════════════════════
-- Section 4: Every red image point is an InvariantSubstrate point
-- ════════════════════════════════════════════════════════════

/-- Every image point of red gives an InvariantSubstrate.
    Since red = selfApp, red(x) = selfApp(x), which is already
    an invariant substrate point by InvariantSubstrate.ofSelfApp. -/
def invariantSubstrate_of_red (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    InvariantSubstrate M := by
  have : M.selfApp x = red x := h_eq x
  exact InvariantSubstrate.ofSelfApp M x

-- ════════════════════════════════════════════════════════════
-- Section 5: Full iso on Im(red)
-- ════════════════════════════════════════════════════════════

/-- On Im(red), the full iso holds: both fold(unfold(y)) = y and
    unfold(fold(y)) = y, where y = red(x).

    The first is roundtrip (global). The second follows from
    selfApp(red(x)) = red(x), since selfApp = unfold ∘ fold. -/
theorem red_image_full_iso (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    M.fold (M.unfold (red x)) = red x ∧
    M.unfold (M.fold (red x)) = red x := by
  constructor
  · exact M.roundtrip (red x)
  · exact selfApp_identity_on_red_image M red h_eq x

/-- On Im(red), gradeGap = 0. Since red(x) is a fixed point
    of selfApp, its grade gap is zero. -/
theorem red_image_zero_gap (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (x : M.carrier) :
    gradeGap M (red x) = 0 := by
  have : red x = M.selfApp x := (h_eq x).symm
  rw [this]
  exact selfApp_image_zero_gap M x

-- ════════════════════════════════════════════════════════════
-- Section 6: Grade-non-increasing red implies PEqNP
-- ════════════════════════════════════════════════════════════

/-- If selfApp = red and red is grade-non-increasing, then PEqNP.
    This is the direct bridge for Group B chains. -/
theorem red_nonincreasing_gives_PEqNP (M : GradedReflModel)
    (red : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = red x)
    (h_le : ∀ x, M.grade (red x) ≤ M.grade x) :
    PEqNP M := by
  refine ⟨0, fun x hx => ?_⟩
  rw [h_eq]
  exact Nat.le_trans (h_le x) hx

-- ════════════════════════════════════════════════════════════
-- Section 7: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms red_idempotent
#print axioms red_fixed_iff_selfApp_fixed
#print axioms red_image_is_substrate
#print axioms red_identity_on_image
#print axioms selfApp_identity_on_red_image
#print axioms invariantSubstrate_of_red
#print axioms red_image_full_iso
#print axioms red_image_zero_gap
#print axioms red_nonincreasing_gives_PEqNP

end WTS
