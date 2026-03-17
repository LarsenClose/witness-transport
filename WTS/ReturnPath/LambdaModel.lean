/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

LambdaModel: deriving a lambda model from reflexive data.

Given ReflData (an isomorphism [A, L] ≅ L), selfApp is application and
reflexiveCurry is abstraction. The beta law is eval_eq; the eta law
comes from the round-trip equations. Every endomorphism has a fixed
point via omega_fixed_point.

This file imports only ConstructiveOmega.lean. No Mathlib.
Axiom profile: ∅ (no propext, no Classical.choice, no Quot.sound).

STATUS: Tier 1 (0 sorry, 0 axioms).
-/

import WTS.ReturnPath.ConstructiveOmega

namespace WTS.ReturnPath.LambdaModel

open WTS.ReturnPath.ConstructiveOmega
open ReflCat

universe v u

variable {C : Type u} [ReflCat.{v} C]

/-! ## Section 1: The Lambda Model Structure -/

/-- A lambda model over a monoidal closed category: a carrier object L
    with application and abstraction satisfying beta and eta laws. -/
structure LambdaModel (A L : C) where
  /-- Application: A ⊗ L → L. -/
  app : Hom (tensor A L) L
  /-- Abstraction: for any X, a morphism (A ⊗ X → L) yields (X → L). -/
  lam : ∀ {X : C}, Hom (tensor A X) L → Hom X L
  /-- Beta law: app ∘ wL(lam f) = f. Applying the abstraction of f is f. -/
  beta : ∀ {X : C} (f : Hom (tensor A X) L),
    ccomp (wL A (lam f)) app = f
  /-- Eta law: lam(app ∘ wL(g)) = g. Abstracting an application recovers g. -/
  eta : ∀ {X : C} (g : Hom X L),
    lam (ccomp (wL A g) app) = g

/-! ## Section 2: Beta law for ReflData -/

/-- Beta law: selfApp ∘ wL(reflexiveCurry f) = f.
    selfApp applied after whiskering by the abstraction of f gives f. -/
theorem reflData_beta {A L X : C} (φ : ReflData A L)
    (f : Hom (tensor A X) L) :
    ccomp (wL A (reflexiveCurry φ f)) (selfApp φ) = f := by
  unfold reflexiveCurry selfApp
  rw [wL_comp, assoc, ← assoc (wL A φ.fwd), wL_fwd_bwd, id_comp, eval_eq]

/-! ## Section 4: Eta law for ReflData -/

/-- Eta law: reflexiveCurry(selfApp ∘ wL(g)) = g.
    Abstracting a self-application recovers the original morphism.

    Proof sketch:
    1. Expand selfApp and use wL_comp + assoc to get wL(g ≫ bwd) ≫ unc(id)
    2. By ← unc_nat + comp_id, this is unc(g ≫ bwd)
    3. cur(unc(g ≫ bwd)) = g ≫ bwd by cur_unc
    4. (g ≫ bwd) ≫ fwd = g ≫ (bwd ≫ fwd) = g ≫ id = g -/
theorem reflData_eta {A L X : C} (φ : ReflData A L)
    (g : Hom X L) :
    reflexiveCurry φ (ccomp (wL A g) (selfApp φ)) = g := by
  unfold reflexiveCurry selfApp
  rw [← assoc, ← wL_comp, ← unc_nat, comp_id, cur_unc, assoc, φ.bwd_fwd, comp_id]

/-! ## Section 5: The Lambda Model from ReflData -/

/-- Every reflexive object gives a lambda model.
    Application is selfApp, abstraction is reflexiveCurry. -/
def reflData_to_lambda_model {A L : C} (φ : ReflData A L) :
    LambdaModel A L where
  app := selfApp φ
  lam := reflexiveCurry φ
  beta := reflData_beta φ
  eta := reflData_eta φ

/-! ## Section 6: Fixed-Point Theorem -/

/-- Every endomorphism on a reflexive object has a fixed point
    (in the sense of the categorical Y combinator equation). -/
theorem lambda_model_fixed_point {A L : C} (φ : ReflData A L)
    (f : Hom L L) :
    ccomp (wL A (omega φ f)) (selfApp φ) = ccomp (selfApp φ) f :=
  omega_fixed_point φ f

/-! ## Axiom audit -/

#print axioms reflData_beta
#print axioms reflData_eta
#print axioms reflData_to_lambda_model
#print axioms lambda_model_fixed_point

end WTS.ReturnPath.LambdaModel
