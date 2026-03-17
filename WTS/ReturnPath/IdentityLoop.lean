/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

IdentityLoop: the identity modulation core at axiom level ∅.

This file packages the identity equations from ReflData — the equations
that emerge when the Y combinator is specialized to the identity morphism.
When f = cid, the omega construction collapses to pure self-recognition:
the morphism omega(cid) is the quine, the self-referencing fixed point.

The four equations of the IdentityLoop capture what happens when the
naming layer (ReflData) meets the identity endomorphism:

1. selfApp decomposes as wL(bwd) >> unc(cid) — definition
2. omega(cid) = reflexiveCurry(selfApp) — omega at identity
3. wL(quine) >> selfApp = selfApp — quine self-recognition
4. bwd >> fwd = cid — the iso round-trip

The quine omega(cid) is the categorical analogue of (λx.xx)(λx.xx):
self-application applied to itself. quine_self_recognition shows that
whiskering the quine into selfApp gives back selfApp — the quine
recognizes itself.

Only import: ConstructiveOmega.lean. Axiom profile: ∅.

STATUS: Tier 1 (0 sorry, 0 axioms).
-/

import WTS.ReturnPath.ConstructiveOmega

namespace WTS.ReturnPath.IdentityLoop

open WTS.ReturnPath.ConstructiveOmega
open ReflCat

universe v u

variable {C : Type u} [ReflCat.{v} C]
variable {A L : C} (φ : ReflData A L)

/-! ## Section 1: The Quine -/

/-- The quine: omega specialized to the identity morphism.
    This is the categorical (λx.xx)(λx.xx) — self-application applied to itself.
    Construction: reflexiveCurry(selfApp >> cid) = reflexiveCurry(selfApp). -/
def quine : ReflCat.Hom L L := omega φ (cid L)

/-- The quine unfolds to omega(cid). -/
theorem quine_unfold : quine φ = omega φ (cid L) := rfl

/-! ## Section 2: Core Identity Equations -/

/-- selfApp is definitionally wL(bwd) >> unc(cid). This is its construction. -/
theorem selfApp_def :
    selfApp φ = ccomp (wL A φ.bwd) (unc (cid (ihom A L))) := rfl

/-- omega(f) is definitionally reflexiveCurry(selfApp >> f). -/
theorem omega_def (f : ReflCat.Hom L L) :
    omega φ f = reflexiveCurry φ (ccomp (selfApp φ) f) := rfl

/-- computation_from_identity: omega(f) = reflexiveCurry(selfApp >> f).
    This IS the definition of omega, so it holds by rfl. -/
theorem computation_from_identity (f : ReflCat.Hom L L) :
    omega φ f = reflexiveCurry φ (ccomp (selfApp φ) f) := rfl

/-- omega at identity simplifies: omega(cid) = reflexiveCurry(selfApp).
    Since selfApp >> cid = selfApp by comp_id. -/
theorem omega_at_identity :
    omega φ (cid L) = reflexiveCurry φ (selfApp φ) := by
  unfold omega
  rw [comp_id]

/-- The quine equals reflexiveCurry(selfApp). -/
theorem quine_eq : quine φ = reflexiveCurry φ (selfApp φ) :=
  omega_at_identity φ

/-! ## Section 3: Quine Self-Recognition -/

/-- **Quine self-recognition.** wL(quine) >> selfApp = selfApp.

    The quine is a fixed point of self-application: whiskering it into
    the self-application morphism gives back self-application unchanged.

    This follows from omega_fixed_point with f = cid:
      wL(omega(cid)) >> selfApp = selfApp >> cid = selfApp.

    Axiom profile: ∅. -/
theorem quine_self_recognition :
    ccomp (wL A (quine φ)) (selfApp φ) = selfApp φ := by
  unfold quine
  rw [omega_fixed_point, comp_id]

/-! ## Section 4: Round-Trip Equations -/

/-- Forward round-trip: cur(selfApp) >> fwd >> bwd = cur(selfApp).
    The iso fwd >> bwd is the identity on ihom A L. -/
theorem cur_selfApp_fwd_bwd :
    ccomp (ccomp (cur (selfApp φ)) φ.fwd) φ.bwd = cur (selfApp φ) := by
  rw [assoc, φ.fwd_bwd, comp_id]

/-- Reverse round-trip: bwd >> fwd = cid L. This is just the ReflData axiom. -/
theorem bwd_fwd_roundtrip : ccomp φ.bwd φ.fwd = cid L := φ.bwd_fwd

/-! ## Section 5: The IdentityLoop Structure -/

/-- The identity loop: four equations capturing the identity modulation core.

    These four equations record what happens when omega is specialized to
    the identity morphism. Together they show that the quine (omega at cid)
    is a self-recognizing fixed point of self-application.

    1. selfApp decomposes as wL(bwd) >> unc(cid) — by definition
    2. quine = reflexiveCurry(selfApp) — omega at identity
    3. wL(quine) >> selfApp = selfApp — quine self-recognition
    4. bwd >> fwd = cid — the iso round-trip -/
structure IdentityLoop' where
  /-- selfApp is wL(bwd) >> unc(cid). -/
  eq_selfApp : selfApp φ = ccomp (wL A φ.bwd) (unc (cid (ihom A L)))
  /-- The quine equals reflexiveCurry(selfApp). -/
  eq_quine : quine φ = reflexiveCurry φ (selfApp φ)
  /-- Quine self-recognition: wL(quine) >> selfApp = selfApp. -/
  eq_self_recognition : ccomp (wL A (quine φ)) (selfApp φ) = selfApp φ
  /-- The iso round-trip: bwd >> fwd = cid. -/
  eq_roundtrip : ccomp φ.bwd φ.fwd = cid L

/-- Every ReflData gives rise to an IdentityLoop. All four equations
    are proved from the axioms of ReflCat and ReflData alone.

    Axiom profile: ∅. -/
def identityLoop : IdentityLoop' φ where
  eq_selfApp := selfApp_def φ
  eq_quine := quine_eq φ
  eq_self_recognition := quine_self_recognition φ
  eq_roundtrip := bwd_fwd_roundtrip φ

/-! ## Axiom audit -/

#print axioms quine_self_recognition
#print axioms omega_at_identity
#print axioms computation_from_identity
#print axioms identityLoop

end WTS.ReturnPath.IdentityLoop
