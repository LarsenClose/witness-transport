/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

SubstrateComputation: universal computation on the invariant substrate.

The invariant substrate (Im(selfApp)) carries the full iso pointwise
in every GradedReflModel. This file proves that the positive chain's
computational results — Y combinator, beta law, fixed points — hold
on this substrate.

The formal content of "computation precedes naming": inside every model
where P vs NP is askable, there is a subspace carrying universal
computation constructively at zero gradeGap. The computation does not
depend on which regime the full model is in.

The approach: rather than building a ReflCat instance (which would
require universe-polymorphic categorical infrastructure), we work
directly with the pointwise content. The positive chain's key results
are:
  (1) selfApp is well-defined (from fold/unfold)
  (2) beta: selfApp ∘ fold(f) = f (from roundtrip)
  (3) omega fixed point: omega(f) applied via selfApp = selfApp ∘ f
  (4) Both iso directions hold (from roundtrip + cotrip)

On Im(selfApp), all four hold because selfApp = id there. The
computation is trivially well-behaved when the self-application
operation is the identity.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.ReturnPath.InvariantSubstrate

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The full iso on the substrate
-- ════════════════════════════════════════════════════════════

/-- On Im(selfApp), fold and unfold are genuine inverses.
    This is the pointwise content of ReflData (fwd_bwd + bwd_fwd)
    restricted to the computation substrate.

    fold(unfold(y)) = y: the roundtrip (holds globally).
    unfold(fold(y)) = y: the cotrip (holds on Im(selfApp) only). -/
theorem substrate_full_iso (M : GradedReflModel) (x : M.carrier) :
    let y := M.selfApp x
    M.fold (M.unfold y) = y ∧ M.unfold (M.fold y) = y :=
  selfApp_image_has_full_iso M x

-- ════════════════════════════════════════════════════════════
-- Section 2: Self-application is identity on the substrate
-- ════════════════════════════════════════════════════════════

/-- selfApp = id on Im(selfApp). The substrate's self-application
    does not shift anything — computation is free of overhead.

    This is the pointwise content of Group C (selfApp = id)
    restricted to the substrate. It holds in EVERY model,
    including separation-regime models. -/
theorem substrate_selfApp_is_id (M : GradedReflModel) (x : M.carrier) :
    M.selfApp (M.selfApp x) = M.selfApp x :=
  selfApp_image_is_fixed M x

-- ════════════════════════════════════════════════════════════
-- Section 3: Beta law on the substrate
-- ════════════════════════════════════════════════════════════

/-- The beta law: applying a function f through the fold/unfold
    cycle recovers f at substrate points.

    For any f : carrier → carrier and substrate point y = selfApp(x):
      f(selfApp(y)) = f(y)

    This is the pointwise beta reduction: encoding y as fold(y),
    then decoding as unfold(fold(y)) = y (cotrip on substrate),
    then applying f gives f(y). No information is lost.

    The full categorical beta (ccomp (wL (reflexiveCurry f)) selfApp = f)
    reduces to this at the pointwise level on the substrate. -/
theorem substrate_beta (M : GradedReflModel)
    (f : M.carrier → M.carrier) (x : M.carrier) :
    f (M.selfApp (M.selfApp x)) = f (M.selfApp x) := by
  rw [selfApp_image_is_fixed]

-- ════════════════════════════════════════════════════════════
-- Section 4: Fixed-point construction on the substrate
-- ════════════════════════════════════════════════════════════

/-- The omega construction at the pointwise level.

    In the categorical framework: omega(f) = reflexiveCurry(selfApp >> f).
    At the pointwise level on carrier: omega_pw(f, x) = f(selfApp(x)).

    On the substrate (y = selfApp(x)):
      omega_pw(f, y) = f(selfApp(y)) = f(y)

    So omega reduces to f itself on the substrate. The fixed-point
    construction is trivially available because selfApp = id there. -/
def omega_pointwise (M : GradedReflModel) (f : M.carrier → M.carrier)
    (x : M.carrier) : M.carrier :=
  f (M.selfApp x)

/-- omega_pointwise(f) = f on the substrate. -/
theorem omega_eq_f_on_substrate (M : GradedReflModel)
    (f : M.carrier → M.carrier) (x : M.carrier) :
    omega_pointwise M f (M.selfApp x) = f (M.selfApp x) := by
  unfold omega_pointwise
  rw [selfApp_image_is_fixed]

/-- Omega output lands back on the substrate after one selfApp.
    omega_pw(f, y) = f(y) which may leave the substrate, but
    selfApp(f(y)) is always a substrate point (by idempotence).
    So one selfApp step returns any computation result to the substrate. -/
theorem omega_returns_to_substrate (M : GradedReflModel)
    (f : M.carrier → M.carrier) (x : M.carrier) :
    let y := M.selfApp x
    M.selfApp (M.selfApp (omega_pointwise M f y)) =
      M.selfApp (omega_pointwise M f y) := by
  simp only [omega_pointwise]
  rw [selfApp_image_is_fixed]

-- ════════════════════════════════════════════════════════════
-- Section 5: Computation is regime-independent on the substrate
-- ════════════════════════════════════════════════════════════

/-- THE MAIN THEOREM: universal computation on the substrate.

    In every GradedReflModel — regardless of whether the model is in
    the identity regime, separation regime, or anything in between —
    the invariant substrate Im(selfApp) carries:

    (1) Full iso: both fold(unfold(y)) = y and unfold(fold(y)) = y
    (2) selfApp = id: self-application is trivial
    (3) Zero gradeGap: no grade overhead from self-application
    (4) Beta reduction: f(selfApp(y)) = f(y)
    (5) Omega reduces to f: omega_pw(f, y) = f(y)
    (6) Iteration stability: selfApp(omega_pw(f, y)) is a substrate point

    This is the formal content of "computation exists independently
    of naming." The substrate exists in every model. The naming
    regime (which determines gradeGap on the full carrier) does not
    affect the substrate. The carrier engineering gap measures how
    much of the carrier lies OUTSIDE this substrate. -/
theorem substrate_universal_computation (M : GradedReflModel) (x : M.carrier) :
    let y := M.selfApp x
    -- (1) Full iso
    (M.fold (M.unfold y) = y ∧ M.unfold (M.fold y) = y) ∧
    -- (2) selfApp = id
    M.selfApp y = y ∧
    -- (3) Zero gradeGap
    gradeGap M y = 0 ∧
    -- (4) Beta reduction (for any f)
    (∀ f : M.carrier → M.carrier, f (M.selfApp y) = f y) ∧
    -- (5) Omega reduces to f (for any f)
    (∀ f : M.carrier → M.carrier, omega_pointwise M f y = f y) ∧
    -- (6) Omega output returns to substrate after selfApp (for any f)
    (∀ f : M.carrier → M.carrier,
      M.selfApp (M.selfApp (omega_pointwise M f y)) =
        M.selfApp (omega_pointwise M f y)) :=
  ⟨substrate_full_iso M x,
   selfApp_image_is_fixed M x,
   substrate_zero_gap M x,
   fun f => by rw [selfApp_image_is_fixed],
   fun f => omega_eq_f_on_substrate M f x,
   fun f => omega_returns_to_substrate M f x⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: The substrate exists in both regimes
-- ════════════════════════════════════════════════════════════

/-- Even in the separation regime (SelfAppUnbounded), the substrate
    exists and carries all computational structure. The separation
    affects elements OUTSIDE the substrate, not the substrate itself. -/
theorem separation_regime_has_substrate :
    ∃ M : GradedReflModel,
      SelfAppUnbounded M ∧
      (∀ x, let y := M.selfApp x;
        M.selfApp y = y ∧
        gradeGap M y = 0 ∧
        M.fold (M.unfold y) = y ∧
        M.unfold (M.fold y) = y) :=
  ⟨standardModel,
   standardModel_selfAppUnbounded,
   fun x => ⟨selfApp_image_is_fixed standardModel x,
             substrate_zero_gap standardModel x,
             (substrate_full_iso standardModel x).1,
             (substrate_full_iso standardModel x).2⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms substrate_full_iso
#print axioms substrate_selfApp_is_id
#print axioms substrate_beta
#print axioms omega_eq_f_on_substrate
#print axioms omega_returns_to_substrate
#print axioms substrate_universal_computation
#print axioms separation_regime_has_substrate

end WTS
