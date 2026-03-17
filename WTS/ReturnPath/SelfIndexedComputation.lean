/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

SelfIndexedComputation: ReflData as computation vocabulary.

This file repackages the constructions from ConstructiveOmega in
computational terms. The reflexive object (ReflData) gives a self-indexed
computation model: a type L that names its own operations A ⊗ X → L
via morphisms X → L, with an evaluator (selfApp) that recovers the
named operation, and a fixed-point combinator (omega) that gives every
endomorphism a fixed point.

The naming equivalence is an isomorphism:
  Hom(A ⊗ X, L) ≅ Hom(X, L)

Forward: reflexiveCurry (= cur >> fwd)
Backward: reflexiveUncurry (= (- >> bwd) >> unc)
Round-trips: from cur_unc/unc_cur composed with fwd_bwd/bwd_fwd.

## Axiom tracking

- naming_roundtrip_cancel uses fwd_bwd (retraction direction)
- naming_roundtrip_recover uses bwd_fwd (section direction)
- Both directions of the ReflData iso are needed.

STATUS: 0 sorry, 0 axioms.
-/

import WTS.ReturnPath.ConstructiveOmega

namespace WTS.ReturnPath.SelfIndexedComputation

open WTS.ReturnPath.ConstructiveOmega
open ReflCat

universe v u

variable {C : Type u} [ReflCat.{v} C]

/-! ## Section 1: Naming Equivalence

The reflexive structure gives an equivalence between "operations"
(morphisms A ⊗ X → L) and "names" (morphisms X → L). -/

/-- Reflexive uncurrying: the inverse of reflexiveCurry.
    Given a name g : X → L, recover the operation A ⊗ X → L.
    Construction: (g >> φ.bwd) >> unc. -/
def reflexiveUncurry {A L X : C} (φ : ReflData A L)
    (g : ReflCat.Hom X L) : ReflCat.Hom (tensor A X) L :=
  unc (ccomp g φ.bwd)

/-- Round-trip: curry then uncurry recovers the original operation.
    reflexiveUncurry(reflexiveCurry(f)) = f.
    Uses: unc_cur, fwd_bwd. -/
theorem naming_roundtrip_cancel {A L X : C} (φ : ReflData A L)
    (f : ReflCat.Hom (tensor A X) L) :
    reflexiveUncurry φ (reflexiveCurry φ f) = f := by
  unfold reflexiveUncurry reflexiveCurry
  rw [assoc, φ.fwd_bwd, comp_id, unc_cur]

/-- Round-trip: uncurry then curry recovers the original name.
    reflexiveCurry(reflexiveUncurry(g)) = g.
    Uses: cur_unc, bwd_fwd. -/
theorem naming_roundtrip_recover {A L X : C} (φ : ReflData A L)
    (g : ReflCat.Hom X L) :
    reflexiveCurry φ (reflexiveUncurry φ g) = g := by
  unfold reflexiveCurry reflexiveUncurry
  rw [cur_unc, assoc, φ.bwd_fwd, comp_id]

/-! ## Section 2: Naming Properties

Every morphism A ⊗ X → L has a name, and every name denotes an operation. -/

/-- Naming surjectivity: every operation A ⊗ X → L is named by some X → L.
    Witness: reflexiveCurry(f). Recovery: naming_roundtrip_cancel. -/
theorem naming_surjective {A L X : C} (φ : ReflData A L)
    (f : ReflCat.Hom (tensor A X) L) :
    ∃ g : ReflCat.Hom X L, reflexiveUncurry φ g = f :=
  ⟨reflexiveCurry φ f, naming_roundtrip_cancel φ f⟩

/-- Naming representability: every X → L names some A ⊗ X → L.
    Witness: reflexiveUncurry(g). Recovery: naming_roundtrip_recover. -/
theorem naming_representable {A L X : C} (φ : ReflData A L)
    (g : ReflCat.Hom X L) :
    ∃ f : ReflCat.Hom (tensor A X) L, reflexiveCurry φ f = g :=
  ⟨reflexiveUncurry φ g, naming_roundtrip_recover φ g⟩

/-! ## Section 3: The Evaluator

selfApp is the evaluation map: given a name (element of L),
decode it and apply. The key property is that evaluation recovers
the named operation. -/

/-- The evaluator recovers named operations.
    Given f : A ⊗ X → L, naming it (via reflexiveCurry) and then
    evaluating (via selfApp after whiskering) gives back f.

    wL(reflexiveCurry(f)) >> selfApp = f

    This says selfApp is a left inverse to "name then whisker". -/
theorem selfApp_recovers_named {A L X : C} (φ : ReflData A L)
    (f : ReflCat.Hom (tensor A X) L) :
    ccomp (wL A (reflexiveCurry φ f)) (selfApp φ) = f := by
  unfold reflexiveCurry selfApp
  rw [wL_comp, assoc, ← assoc (wL A φ.fwd), wL_fwd_bwd, id_comp, eval_eq]

/-! ## Section 4: The Fixed-Point Combinator in Computation Vocabulary

omega_fixed_point rephrased: the evaluator intertwines with omega. -/

/-- **Self-indexed Kleene fixed-point theorem.**

    For any endomorphism f : L → L on a self-indexed computation model:

      wL(omega(f)) >> selfApp = selfApp >> f

    The omega map produces a name whose evaluation under selfApp
    equals selfApp post-composed with f. This is the Y combinator
    equation in computation vocabulary.

    Axiom profile: ∅. -/
theorem self_indexed_kleene {A L : C} (φ : ReflData A L)
    (f : ReflCat.Hom L L) :
    ccomp (wL A (omega φ f)) (selfApp φ) = ccomp (selfApp φ) f :=
  omega_fixed_point φ f

/-! ## Section 5: The Computation Structure

Package everything into a single structure witnessing that L
is a self-indexed computation model over A. -/

/-- A self-indexed computation model: a type L that names its own
    operations over A, with evaluation and fixed points. -/
structure SelfIndexedModel (A L : C) extends ReflData A L where
  /-- The evaluator: decode and apply. -/
  eval : ReflCat.Hom (tensor A L) L := selfApp toReflData
  /-- The naming map: operation → name. -/
  name : ∀ {X}, ReflCat.Hom (tensor A X) L → ReflCat.Hom X L :=
    fun f => reflexiveCurry toReflData f
  /-- The interpretation map: name → operation. -/
  interpret : ∀ {X}, ReflCat.Hom X L → ReflCat.Hom (tensor A X) L :=
    fun g => reflexiveUncurry toReflData g

/-- Every ReflData gives a SelfIndexedModel. -/
def SelfIndexedModel.ofReflData {A L : C} (φ : ReflData A L) :
    SelfIndexedModel A L where
  toReflData := φ

/-! ## Axiom audit -/

#print axioms naming_roundtrip_cancel
#print axioms naming_roundtrip_recover
#print axioms naming_surjective
#print axioms naming_representable
#print axioms selfApp_recovers_named
#print axioms self_indexed_kleene
#print axioms SelfIndexedModel.ofReflData

end WTS.ReturnPath.SelfIndexedComputation
