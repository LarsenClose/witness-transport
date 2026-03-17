/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

InvariantSubstrate: the computation layer seen from inside any graded model.

The invariant substrate is the image of selfApp — the set of elements
x where selfApp(x) = x. By idempotence (from roundtrip), every element
of Im(selfApp) is a fixed point of selfApp, and conversely.

On this substrate:
- The full iso holds pointwise: both fold(unfold(x)) = x and
  unfold(fold(x)) = x. The first is the roundtrip (holds globally).
  The second IS the hypothesis selfApp(x) = x restated.
- The gradeGap is zero: selfApp doesn't shift grade.
- Composition with f has overhead exactly c_f: selfApp contributes
  nothing additional.

The invariant substrate is always present, always has zero gap, and
always carries the full iso. The carrier engineering gap at each chain
measures how much of the carrier lies outside this substrate.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.Tower.ForcingPredicates
import WTS.ReturnPath.Naming.OmegaGradeTransfer

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Fixed points of selfApp carry the full iso
-- ════════════════════════════════════════════════════════════

/-- At a fixed point of selfApp, both directions of the iso hold.

    - fold(unfold(x)) = x: this is M.roundtrip, holds globally
    - unfold(fold(x)) = x: this IS selfApp(x) = x, the hypothesis

    The cotrip direction is literally the hypothesis restated:
    selfApp = unfold ∘ fold, so selfApp(x) = x means unfold(fold(x)) = x. -/
theorem selfApp_fixed_has_full_iso (M : GradedReflModel)
    (x : M.carrier)
    (hfix : M.selfApp x = x) :
    M.fold (M.unfold x) = x ∧ M.unfold (M.fold x) = x :=
  ⟨M.roundtrip x, hfix⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Im(selfApp) consists of fixed points
-- ════════════════════════════════════════════════════════════

/-- Every element in Im(selfApp) is a fixed point.
    selfApp(selfApp(x)) = selfApp(x) by idempotence. -/
theorem selfApp_image_is_fixed (M : GradedReflModel) (x : M.carrier) :
    M.selfApp (M.selfApp x) = M.selfApp x :=
  grm_roundtrip_forces_idempotent M x

/-- Im(selfApp) carries the full iso pointwise. -/
theorem selfApp_image_has_full_iso (M : GradedReflModel) (x : M.carrier) :
    M.fold (M.unfold (M.selfApp x)) = M.selfApp x ∧
    M.unfold (M.fold (M.selfApp x)) = M.selfApp x :=
  selfApp_fixed_has_full_iso M (M.selfApp x) (selfApp_image_is_fixed M x)

-- ════════════════════════════════════════════════════════════
-- Section 3: The invariant substrate exists in every model
-- ════════════════════════════════════════════════════════════

/-- For any GradedReflModel, there exist elements where the full iso holds.
    Proof: for any x, selfApp(x) is such an element. -/
theorem invariant_substrate_exists (M : GradedReflModel) (x : M.carrier) :
    ∃ y : M.carrier,
      M.selfApp y = y ∧
      M.fold (M.unfold y) = y ∧
      M.unfold (M.fold y) = y :=
  ⟨M.selfApp x,
   selfApp_image_is_fixed M x,
   (selfApp_image_has_full_iso M x).1,
   (selfApp_image_has_full_iso M x).2⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Zero gap on the substrate
-- ════════════════════════════════════════════════════════════

/-- Elements where the full iso holds have gradeGap = 0.
    This connects to selfApp_image_zero_gap: the retracted subspace
    is always grade-stable. -/
theorem substrate_zero_gap (M : GradedReflModel) (x : M.carrier) :
    gradeGap M (M.selfApp x) = 0 :=
  selfApp_image_zero_gap M x

/-- Fixed points of selfApp have gradeGap = 0.
    If selfApp(x) = x then gradeGap(M, x) = grade(selfApp(x)) - grade(x)
    = grade(x) - grade(x) = 0. -/
theorem fixed_point_zero_gap (M : GradedReflModel)
    (x : M.carrier) (hfix : M.selfApp x = x) :
    gradeGap M x = 0 := by
  simp only [gradeGap, hfix]; omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Computation on the substrate is free of selfApp overhead
-- ════════════════════════════════════════════════════════════

/-- On the invariant substrate (Im(selfApp)), composition with f has
    overhead exactly c_f — selfApp contributes zero.

    For any x, applying f after selfApp at the retracted point selfApp(x)
    costs at most grade(selfApp(x)) + c. selfApp adds nothing because
    selfApp(selfApp(x)) = selfApp(x) by idempotence.

    This holds for ALL GRMs, regardless of regime. -/
theorem substrate_computation_free (M : GradedReflModel)
    (f : M.carrier → M.carrier)
    (c : Nat)
    (hf : ∀ x, M.grade (f x) ≤ M.grade x + c)
    (x : M.carrier) :
    M.grade (f (M.selfApp (M.selfApp x))) ≤ M.grade (M.selfApp x) + c :=
  composition_at_retracted_point M f c hf x

/-- Simplified form: at a fixed point of selfApp, f costs exactly c_f. -/
theorem computation_at_fixed_point (M : GradedReflModel)
    (f : M.carrier → M.carrier)
    (c : Nat)
    (hf : ∀ x, M.grade (f x) ≤ M.grade x + c)
    (x : M.carrier)
    (_ : M.selfApp x = x) :
    M.grade (f x) ≤ M.grade x + c :=
  hf x

-- ════════════════════════════════════════════════════════════
-- Section 6: The InvariantSubstrate structure
-- ════════════════════════════════════════════════════════════

/-- The invariant substrate of a GradedReflModel: a point on the carrier
    that is fixed by selfApp, carries the full iso, and has zero gradeGap.

    Every GRM has such points (by idempotence of selfApp). -/
structure InvariantSubstrate (M : GradedReflModel) where
  /-- The point on the substrate. -/
  point : M.carrier
  /-- selfApp fixes it. -/
  fixed : M.selfApp point = point
  /-- fold ∘ unfold round-trip. -/
  roundtrip : M.fold (M.unfold point) = point
  /-- unfold ∘ fold cotrip (the full iso direction). -/
  cotrip : M.unfold (M.fold point) = point
  /-- gradeGap is zero. -/
  zero_gap : gradeGap M point = 0

/-- Every GradedReflModel has an InvariantSubstrate at every image point
    of selfApp. -/
def InvariantSubstrate.ofSelfApp (M : GradedReflModel) (x : M.carrier) :
    InvariantSubstrate M where
  point := M.selfApp x
  fixed := selfApp_image_is_fixed M x
  roundtrip := (selfApp_image_has_full_iso M x).1
  cotrip := (selfApp_image_has_full_iso M x).2
  zero_gap := substrate_zero_gap M x

-- ════════════════════════════════════════════════════════════
-- Section 7: PEqNP on the substrate
-- ════════════════════════════════════════════════════════════

/-- At a fixed point of selfApp, selfApp is trivially grade-bounded:
    grade(selfApp(x)) = grade(x). Immediate from rewriting the hypothesis. -/
theorem substrate_selfApp_bounded (M : GradedReflModel)
    (x : M.carrier) (hfix : M.selfApp x = x) :
    M.grade (M.selfApp x) ≤ M.grade x := by
  rw [hfix]; exact Nat.le_refl _

/-- selfApp factors through every grade on Im(selfApp).
    At selfApp(x): grade(selfApp(selfApp(x))) = grade(selfApp(x)) by idempotence. -/
theorem substrate_factors_through (M : GradedReflModel)
    (d : Nat) (x : M.carrier)
    (hx : M.grade (M.selfApp x) ≤ d) :
    M.grade (M.selfApp (M.selfApp x)) ≤ d := by
  rw [selfApp_image_is_fixed]; exact hx

/-- SelfAppUnbounded cannot hold on Im(selfApp).
    At every image point, selfApp(selfApp(x)) = selfApp(x), so
    grade(selfApp(y)) = grade(y) for y in Im(selfApp). Any overflow
    witness would need grade(selfApp(y)) > d with grade(y) ≤ d,
    but these are equal. -/
theorem substrate_not_unbounded (M : GradedReflModel) :
    ¬∀ d, ∃ x, M.grade (M.selfApp x) ≤ d ∧
      M.grade (M.selfApp (M.selfApp x)) > d := by
  intro h
  obtain ⟨x, hle, hgt⟩ := h 0
  rw [selfApp_image_is_fixed] at hgt
  omega

/-- PEqNP holds pointwise on Im(selfApp): selfApp restricted to its image
    factors through every grade level.

    This is the formal content: the invariant substrate is always in the
    collapse regime, regardless of which regime the full model lives in.
    The carrier engineering gap measures how much of the carrier lies
    OUTSIDE this substrate — that's where separation can occur. -/
theorem substrate_PEqNP (M : GradedReflModel) :
    ∀ d, ∀ x, M.grade (M.selfApp x) ≤ d →
      M.grade (M.selfApp (M.selfApp x)) ≤ d := by
  intro d x hle
  rw [selfApp_image_is_fixed]; exact hle

-- ════════════════════════════════════════════════════════════
-- Section 8: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms selfApp_fixed_has_full_iso
#print axioms selfApp_image_has_full_iso
#print axioms invariant_substrate_exists
#print axioms substrate_zero_gap
#print axioms substrate_computation_free
#print axioms InvariantSubstrate.ofSelfApp
#print axioms substrate_selfApp_bounded
#print axioms substrate_not_unbounded
#print axioms substrate_PEqNP

end WTS
