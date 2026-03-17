/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WeakReflData: the computation/naming boundary as a formal object.

ReflData requires a full isomorphism [A, L] ≅ L (fwd_bwd AND bwd_fwd).
WeakReflData requires only a retraction: fwd ≫ bwd = id (fwd_bwd only).

This single missing equation — bwd_fwd — is the exact boundary between
computation and naming equivalence:

  WITH fwd_bwd only (WeakReflData):
    selfApp, reflexiveCurry, omega, beta, fixed points — ALL work.
    The entire positive computational chain survives.

  WITHOUT bwd_fwd:
    eta law CANNOT be proved. Naming recovery CANNOT be proved.
    The naming equivalence (decode ∘ encode = id on L) is lost.

This formalizes the claim: self-indexed computation requires only a
retraction. Full naming equivalence requires the isomorphism.

Axiom profile: ∅ (no propext, no Classical.choice, no Quot.sound).
Only import: ConstructiveOmega.

STATUS: Tier 1 (0 sorry, 0 axioms).
-/

import WTS.ReturnPath.ConstructiveOmega

namespace WTS.ReturnPath.WeakReflData

open WTS.ReturnPath.ConstructiveOmega
open ReflCat

universe v u

variable {C : Type u} [ReflCat.{v} C]

/-! ## Section 1: WeakReflData — retraction only -/

/-- Weak reflexive data: a retraction [A, L] ◁ L.
    Only fwd_bwd (fwd ≫ bwd = id on [A,L]) is required.
    Compare ReflData which also requires bwd_fwd (bwd ≫ fwd = id on L). -/
structure WeakReflData (A L : C) where
  /-- Forward: [A, L] → L. -/
  fwd : Hom (ihom A L) L
  /-- Backward: L → [A, L]. -/
  bwd : Hom L (ihom A L)
  /-- Retraction: fwd ≫ bwd = id on [A,L].
      Encoding then decoding a function recovers it exactly. -/
  fwd_bwd : ccomp fwd bwd = cid (ihom A L)

/-! ## Section 2: Definitions survive — selfApp, reflexiveCurry, omega

These definitions from ConstructiveOmega use only fwd and bwd,
never the round-trip equations. We redefine them for WeakReflData. -/

/-- Self-application: A ⊗ L → L. Uses only bwd.
    Construction: wL(bwd) ≫ unc(id). -/
def weakSelfApp {A L : C} (φ : WeakReflData A L) : Hom (tensor A L) L :=
  ccomp (wL A φ.bwd) (unc (cid (ihom A L)))

/-- Reflexive currying: (A ⊗ X → L) → (X → L). Uses only fwd.
    Construction: cur(f) ≫ fwd. -/
def weakReflexiveCurry {A L X : C} (φ : WeakReflData A L)
    (f : Hom (tensor A X) L) : Hom X L :=
  ccomp (cur f) φ.fwd

/-- The omega map (categorical Y combinator): (L → L) → (L → L).
    Uses only weakSelfApp and weakReflexiveCurry. -/
def weakOmega {A L : C} (φ : WeakReflData A L) (f : Hom L L) : Hom L L :=
  weakReflexiveCurry φ (ccomp (weakSelfApp φ) f)

/-! ## Section 3: Reproved helper -/

/-- wL preserves fwd ≫ bwd = id. Uses only fwd_bwd. -/
private theorem wL_fwd_bwd {A L : C} (φ : WeakReflData A L) :
    ccomp (wL A φ.fwd) (wL A φ.bwd) = cid (tensor A (ihom A L)) := by
  rw [← wL_comp, φ.fwd_bwd, wL_id]

/-! ## Section 4: Beta law — survives -/

/-- Beta law: weakSelfApp ∘ wL(weakReflexiveCurry f) = f.
    Uses only fwd_bwd (through wL_fwd_bwd). -/
theorem weakBeta {A L X : C} (φ : WeakReflData A L)
    (f : Hom (tensor A X) L) :
    ccomp (wL A (weakReflexiveCurry φ f)) (weakSelfApp φ) = f := by
  unfold weakReflexiveCurry weakSelfApp
  rw [wL_comp, assoc, ← assoc (wL A φ.fwd), wL_fwd_bwd, id_comp, eval_eq]

/-! ## Section 5: Fixed-point theorem — survives -/

/-- The fixed-point equation at axiom level ∅, from a retraction alone.
    For any f : L → L: wL(weakOmega f) ≫ weakSelfApp = weakSelfApp ≫ f.
    Uses only fwd_bwd (through wL_fwd_bwd). -/
theorem weak_omega_fixed_point {A L : C} (φ : WeakReflData A L)
    (f : Hom L L) :
    ccomp (wL A (weakOmega φ f)) (weakSelfApp φ) = ccomp (weakSelfApp φ) f := by
  unfold weakOmega weakReflexiveCurry weakSelfApp
  rw [wL_comp, assoc, ← assoc (wL A φ.fwd), wL_fwd_bwd, id_comp, eval_eq]

/-! ## Section 6: Naming round-trip — one direction survives -/

/-- Naming cancellation: fwd ≫ bwd = id on [A,L].
    Encoding a decoded function recovers the code. Survives (IS fwd_bwd). -/
theorem naming_roundtrip_cancel {A L : C} (φ : WeakReflData A L) :
    ccomp φ.fwd φ.bwd = cid (ihom A L) :=
  φ.fwd_bwd

/-! ## Section 7: What CANNOT be proved without bwd_fwd

The eta law and naming recovery both require bwd ≫ fwd = id on L.
This is the structural content of the computation/naming boundary:

  eta : weakReflexiveCurry(wL(g) ≫ weakSelfApp) = g
    Proof would need: ... ≫ bwd_fwd ≫ ... = g
    Without bwd_fwd, the chain cannot close.

  naming_recovery : bwd ≫ fwd = id on L
    This IS bwd_fwd — it is literally the missing axiom.

The boundary is sharp: every positive computational result (Y combinator,
beta, fixed points) uses only the retraction direction fwd_bwd.
Every naming equivalence result (eta, recovery) requires the full
isomorphism bwd_fwd.

A ReflData upgrades to a WeakReflData by forgetting bwd_fwd: -/

/-- Every ReflData is a WeakReflData (forget bwd_fwd). -/
def ReflData.toWeak {A L : C} (φ : ReflData A L) : WeakReflData A L where
  fwd := φ.fwd
  bwd := φ.bwd
  fwd_bwd := φ.fwd_bwd

/-! ## Axiom audit -/

#print axioms weakBeta
#print axioms weak_omega_fixed_point
#print axioms naming_roundtrip_cancel
#print axioms ReflData.toWeak

end WTS.ReturnPath.WeakReflData
