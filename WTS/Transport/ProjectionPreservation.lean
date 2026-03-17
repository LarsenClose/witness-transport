/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/ProjectionPreservation.lean — Projection preserves certify,
blocks extract when selfApp is unbounded.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Transport.WitnessTransportCore

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Compatible projections
-- ════════════════════════════════════════════════════════════

/-- A grade-compatible projection: fold commutes with project. -/
structure CompatibleProjection (M : GradedReflModel) extends Projection M where
  /-- fold commutes with project -/
  h_fold_compat : ∀ x, M.fold (project x) = project (M.fold x)

/-- The certify/extract asymmetry: a projection that preserves certify
    but blocks extract. -/
structure ProjectionAsymmetry (M : GradedReflModel) where
  proj : Projection M
  h_certify : proj.preservesCertify M
  h_extract : proj.blocksExtract M

-- ════════════════════════════════════════════════════════════
-- Section 2: Certify preservation
-- ════════════════════════════════════════════════════════════

/-- Compatible projections preserve certify: fold commutes with project
    by the h_fold_compat field. This is genuinely non-trivial — it does
    NOT follow from roundtrip alone. -/
theorem compatible_preserves_certify (M : GradedReflModel)
    (p : CompatibleProjection M) :
    p.toProjection.preservesCertify M :=
  p.h_fold_compat

-- ════════════════════════════════════════════════════════════
-- Section 3: Extract blocking
-- ════════════════════════════════════════════════════════════

/-- A non-trivial projection (one that is a retraction on grade-bounded elements)
    blocks extract when selfApp is unbounded.

    Non-trivial means: project(x) = x for all x with grade(x) ≤ target_grade.
    This is the "retraction" condition.

    Proof: hub gives x with grade(x) ≤ target_grade and grade(selfApp(x)) > target_grade.
    If selfApp(project(x)) = project(selfApp(x)), substituting project(x) = x:
      selfApp(x) = project(selfApp(x))
    But grade(project(selfApp(x))) ≤ target_grade < grade(selfApp(x)). Contradiction. -/
theorem projection_blocks_extract_nontrivial (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (p : Projection M)
    (h_retract : ∀ x, M.grade x ≤ p.target_grade → p.project x = x) :
    p.blocksExtract M :=
  projection_blocks_extract_when_retraction M hub p h_retract

/-- h_nontrivial follows from hub: selfApp(x) has grade > target_grade. -/
theorem hub_gives_nontrivial (M : GradedReflModel) (hub : SelfAppUnbounded M)
    (d : Nat) : ∃ y, M.grade y > d := by
  obtain ⟨x, _, hgt⟩ := hub.overflows d
  exact ⟨M.selfApp x, hgt⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Projection asymmetry existence
-- ════════════════════════════════════════════════════════════

/-- In a model with SelfAppUnbounded, a fold-compatible retraction projection
    gives projection asymmetry: certify preserved (fold commutes) but extract
    blocked (selfApp does not commute). -/
def projection_asymmetry_exists (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (p : CompatibleProjection M)
    (h_retract : ∀ x, M.grade x ≤ p.target_grade → p.project x = x) :
    ProjectionAsymmetry M :=
  ⟨p.toProjection,
    compatible_preserves_certify M p,
    projection_blocks_extract_when_retraction M hub p.toProjection h_retract⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Projection properties
-- ════════════════════════════════════════════════════════════

/-- Projection idempotent. -/
theorem projection_idempotent_pp (M : GradedReflModel) (p : Projection M) :
    ∀ x, p.project (p.project x) = p.project x := p.h_idempotent

/-- Projection reduces grade to at most target_grade. -/
theorem projection_grade_monotone (M : GradedReflModel) (p : Projection M) :
    ∀ x, M.grade (p.project x) ≤ p.target_grade := p.h_reduces

/-- Transport then project: grade bounded by target_grade (projection absorbs overhead). -/
theorem transport_then_project_overhead (M : GradedReflModel)
    (t : Transport M) (p : Projection M) :
    ∀ x, M.grade (p.project (t.move x)) ≤ p.target_grade :=
  fun _ => p.h_reduces _

/-- Applying projection twice has the same grade as applying it once. -/
theorem projection_grade_stable (M : GradedReflModel) (p : Projection M) :
    ∀ x, M.grade (p.project (p.project x)) = M.grade (p.project x) := by
  intro x
  rw [p.h_idempotent x]

-- ════════════════════════════════════════════════════════════
-- Section 6: Conservativity: trivialModel has no asymmetry
-- ════════════════════════════════════════════════════════════

/-- trivialModel has no projection asymmetry: selfApp = id, so
    selfApp(project(x)) = project(x) = project(selfApp(x)) always. -/
theorem trivialModel_no_asymmetry (pa : ProjectionAsymmetry trivialModel) :
    False := by
  obtain ⟨x, hne⟩ := pa.h_extract
  -- x : trivialModel.carrier = Unit
  -- selfApp(project(x)) ≠ project(selfApp(x)) — but trivialModel is Unit, everything is ()
  cases x
  apply hne
  -- selfApp(project()) = project(selfApp())
  -- trivialModel.selfApp () = (), trivialModel is Unit so project = const ()
  show trivialModel.selfApp (pa.proj.project ()) =
       pa.proj.project (trivialModel.selfApp ())
  -- Both sides: trivialModel carrier is Unit, everything equals ()
  -- trivialModel.selfApp () = trivialModel.unfold (trivialModel.fold ()) = unfold(fold(())) = ()
  -- since fold and unfold on Unit are id
  -- pa.proj.project () : Unit, so it must be ()
  cases (trivialModel.selfApp (pa.proj.project ()))
  cases (pa.proj.project (trivialModel.selfApp ()))
  rfl

end WTS
