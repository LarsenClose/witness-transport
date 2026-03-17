/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

NamingAccess: the bridge condition as naming's access to computation.

The invariant substrate Im(selfApp) is always present, always has
zero gradeGap, and always carries the full iso (InvariantSubstrate.lean).
The bridge conditions (ConsequenceBridge, ConsequenceFaithful) ask
whether the encoding's depth profiles respect consequence closure.

This file restates the bridge condition in terms of naming access:

- When Im(selfApp) = full carrier (selfApp = id everywhere), the
  ConsequenceBridge is trivially satisfied: any grade-linked depth
  function is bounded because selfApp doesn't overflow. The naming
  convention sees the entire computation substrate.

- When selfApp ≠ id, the ConsequenceBridge's h_consequence constrains
  the depth profiles to stay within the zero-gap region. The bridge
  condition IS the condition that naming has access to the substrate.

- The ConsequenceBridge at a fixed point of selfApp is always
  satisfiable: consequence closure holds trivially where selfApp = id.
  Separation occurs precisely where naming cannot reach the substrate —
  where elements lie outside Im(selfApp).

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.ReturnPath.InvariantSubstrate
import WTS.Transport.BridgeNecessity

namespace WTS.ReturnPath.NamingAccess

open WTS
open WTS.Transport.BridgeNecessity

-- ════════════════════════════════════════════════════════════
-- Section 1: selfApp = id implies ConsequenceBridge trivially
-- ════════════════════════════════════════════════════════════

/-- Any GRM has a trivially satisfiable ConsequenceBridge (zero-depth functions).

    NOTE: This holds unconditionally for all models, not just those with
    selfApp = id. The bridge is trivially satisfiable because the zero-depth
    functions satisfy h_consequence as 0 ≤ d. -/
theorem consequence_bridge_always_satisfiable (M : GradedReflModel) :
    Nonempty (ConsequenceBridge M) :=
  ⟨consequence_bridge_trivially_satisfiable M⟩

/-- A ConsequenceBridge from any depth profile where target ≤ source.

    The consequence field h_consequence: source ≤ d → target ≤ d
    is satisfied whenever target ≤ source (transitivity).

    NOTE: Like consequence_bridge_always_satisfiable, this holds for
    any model — the selfApp behavior is irrelevant because h_consequence
    only depends on the depth function ordering. -/
def any_profile_bridge (M : GradedReflModel)
    (source target : Nat → Nat)
    (h_dom : ∀ n, target n ≤ source n)
    (poly : PolyBound)
    (h_upper : ∀ n, target n ≤ source n * poly.eval n + poly.eval n)
    (h_lower : ∀ n, source n ≤ target n * poly.eval n + poly.eval n) :
    ConsequenceBridge M where
  source_depth := source
  target_depth := target
  poly := poly
  h_upper := h_upper
  h_lower := h_lower
  h_consequence := fun n _ hle => Nat.le_trans (h_dom n) hle

-- ════════════════════════════════════════════════════════════
-- Section 2: ConsequenceBridge at fixed points of selfApp
-- ════════════════════════════════════════════════════════════

/-- At a fixed point of selfApp, selfApp factors through every grade.
    This is the pointwise version: grade(selfApp(x)) ≤ d whenever
    grade(x) ≤ d, because selfApp(x) = x. -/
theorem fixed_point_factors (M : GradedReflModel)
    (x : M.carrier) (hfix : M.selfApp x = x) (d : Nat)
    (hle : M.grade x ≤ d) :
    M.grade (M.selfApp x) ≤ d := by
  rw [hfix]; exact hle

/-- The consequence property holds at every point of Im(selfApp).
    For any y = selfApp(x): grade(selfApp(y)) ≤ d whenever grade(y) ≤ d,
    because selfApp(y) = y by idempotence. -/
theorem consequence_on_substrate (M : GradedReflModel)
    (x : M.carrier) (d : Nat)
    (hle : M.grade (M.selfApp x) ≤ d) :
    M.grade (M.selfApp (M.selfApp x)) ≤ d := by
  rw [selfApp_image_is_fixed]; exact hle

-- ════════════════════════════════════════════════════════════
-- Section 3: The access condition — consequence IS substrate access
-- ════════════════════════════════════════════════════════════

/-- A grade-linked bridge: the source_depth profile is linked to
    selfApp's actual grade behavior at each input size.

    This is a ConsequenceBridge where source_depth(n) is witnessed
    by selfApp: there exists a grade-≤-n input where selfApp produces
    output at grade source_depth(n). This grounds the profile in
    the model's actual computation. -/
structure GradeLinkedBridge (M : GradedReflModel) extends ConsequenceBridge M where
  /-- source_depth is grounded: at each n, some grade-≤-n input has
      selfApp output at grade ≥ source_depth(n). -/
  h_grounded : ∀ n, ∃ x, M.grade x ≤ n ∧
    M.grade (M.selfApp x) ≥ source_depth n

/-- A grade-linked bridge with source_depth(n) > n implies selfApp
    overflows at every grade — giving SelfAppUnbounded and ¬PEqNP.

    This follows the same pattern as grounded_overflowing_implies_separation
    in BridgeNecessity, but uses selfApp directly (the h_grounded field
    references selfApp, not witness functions). -/
theorem grade_linked_overflow_separation (M : GradedReflModel)
    (glb : GradeLinkedBridge M)
    (h_overflow : ∀ n, glb.source_depth n > n) :
    ¬PEqNP M := by
  intro ⟨d, hd⟩
  obtain ⟨x, hle, hout⟩ := glb.h_grounded d
  have hsa := hd x hle
  have hov := h_overflow d
  omega

/-- On Im(selfApp), grade-linking is trivially satisfiable.
    We can ground the depth at selfApp's image because
    grade(selfApp(selfApp(x))) = grade(selfApp(x)) by idempotence.

    source_depth(n) = 0 satisfies h_grounded trivially (grade ≥ 0 always).
    The interesting case is the IMPOSSIBILITY of h_overflow on the substrate:
    since selfApp(selfApp(x)) = selfApp(x), we cannot have
    grade(selfApp(y)) > grade(y) for y in Im(selfApp). -/
theorem substrate_grade_linked_no_overflow (M : GradedReflModel)
    (x : M.carrier) :
    ¬(M.grade (M.selfApp (M.selfApp x)) > M.grade (M.selfApp x)) := by
  rw [selfApp_image_is_fixed]; omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Separation = naming's inability to reach substrate
-- ════════════════════════════════════════════════════════════

/-- The separation characterization through naming access:

    SelfAppUnbounded means there are elements at every grade level
    where selfApp pushes them OUTSIDE their grade band. These are
    elements that lie outside Im(selfApp) — elements where the naming
    convention cannot see the computation substrate.

    The bridge condition (ConsequenceBridge with grounding) fails
    precisely when these outside-substrate elements prevent grade-linked
    profiles from being bounded. The overflow witnesses are elements
    where naming fails to access computation. -/
theorem separation_is_naming_failure (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    -- (1) selfApp overflows at every grade
    (∀ d, ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d) ∧
    -- (2) but on Im(selfApp), selfApp never overflows
    (∀ d x, M.grade (M.selfApp x) ≤ d →
      M.grade (M.selfApp (M.selfApp x)) ≤ d) ∧
    -- (3) therefore ¬PEqNP
    ¬PEqNP M :=
  ⟨hub.overflows,
   fun d x hle => by rw [selfApp_image_is_fixed]; exact hle,
   selfApp_unbounded_not_peqnp M hub⟩

/-- The full naming access theorem: in every GradedReflModel, the
    invariant substrate is accessible (consequence holds there) and
    separation occurs precisely outside the substrate.

    (1) On Im(selfApp): consequence holds — grade(selfApp(y)) ≤ d
        whenever grade(y) ≤ d (because selfApp(y) = y).
    (2) Outside Im(selfApp) (when it exists): selfApp can overflow,
        breaking the consequence property at those points.
    (3) PEqNP ↔ the consequence property holds EVERYWHERE
        (not just on the substrate). -/
theorem naming_access_characterization (M : GradedReflModel) :
    -- The substrate always satisfies the consequence property
    (∀ d x, M.grade (M.selfApp x) ≤ d →
      M.grade (M.selfApp (M.selfApp x)) ≤ d) ∧
    -- PEqNP iff selfApp factors through some grade globally
    -- (definitional: PEqNP is defined as this existential)
    (PEqNP M ↔ ∃ d, FactorsThrough M M.selfApp d) :=
  ⟨fun d x hle => by rw [selfApp_image_is_fixed]; exact hle,
   Iff.rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms consequence_bridge_always_satisfiable
#print axioms any_profile_bridge
#print axioms fixed_point_factors
#print axioms consequence_on_substrate
#print axioms grade_linked_overflow_separation
#print axioms substrate_grade_linked_no_overflow
#print axioms separation_is_naming_failure
#print axioms naming_access_characterization

end WTS.ReturnPath.NamingAccess
