/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

Constructive Omega: the Y combinator at axiom level ∅.

This file proves the categorical fixed-point theorem (omega_fixed_point)
using ZERO axioms — not propext, not Quot.sound, not Classical.choice.
The entire construction lives in the equational theory of categories
with curry/uncurry (monoidal closed categories).

## Why this matters

The main project proves omega_fixed_point using Mathlib's MonoidalClosed
infrastructure, which transitively depends on {propext, Classical.choice,
Quot.sound} — the full classical stack. But this is an artifact of
Mathlib's implementation, not of the mathematics.

This file demonstrates that the Y combinator is PURELY CONSTRUCTIVE
by axiomatizing the categorical vocabulary (composition, whiskerLeft,
curry, uncurry) without importing Mathlib, and proving the fixed-point
equation from these axioms alone. The axiom profile ∅ is the theorem
statement: structural self-reference requires no classical reasoning.

## Connection to the incompleteness stratification

The Y combinator (structural self-reference, Level 2) and Rice's theorem
(limitative, Level 3) are two faces of the same identity equations,
differentiated by the naming layer. This file provides the machine-checked
evidence for the axiom split:

- **Level 2** (Y combinator): axiom profile ∅. Constructive. Total.
- **Level 3** (Rice, Kleene): axiom profile {propext, Classical.choice,
  Quot.sound}. Classical. Limitative.

The axiom boundary IS the Level 2/3 boundary. Classical.choice enters
through the naming layer (extensional equality over infinite domains
requires excluded middle). The Y combinator never needs it because it
constructs the fixed point — it hands you the witness.

## The axiomatization

We axiomatize only what's needed:
- Category: Hom, id, comp, associativity, identity laws
- Tensor: tensor, whiskerLeft, functoriality of whiskerLeft
- Curry/uncurry: cur, unc, cur∘unc = id, unc∘cur = id, naturality of unc

No universe polymorphism, no functor API, no limits, no colimits, no
adjunctions. The Y combinator needs only the closed monoidal structure.

STATUS: Tier 1 (0 sorry, 0 axioms).
-/

-- NO IMPORTS. This file is entirely self-contained.

namespace WTS.ReturnPath.ConstructiveOmega

universe v u

/-- Minimal categorical vocabulary: a category with tensor product,
    internal hom, and curry/uncurry adjunction. No Mathlib dependency.

    This axiomatizes exactly the equational theory of monoidal closed
    categories, with no universe polymorphism or categorical infrastructure
    beyond what the Y combinator needs. -/
class ReflCat (C : Type u) where
  /-- Morphisms. -/
  Hom : C → C → Type v
  /-- Identity morphism. -/
  cid : ∀ X, Hom X X
  /-- Composition. -/
  ccomp : ∀ {X Y Z}, Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity. -/
  id_comp : ∀ {X Y} (f : Hom X Y), ccomp (cid X) f = f
  /-- Right identity. -/
  comp_id : ∀ {X Y} (f : Hom X Y), ccomp f (cid Y) = f
  /-- Associativity. -/
  assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    ccomp (ccomp f g) h = ccomp f (ccomp g h)
  /-- Tensor product on objects. -/
  tensor : C → C → C
  /-- Left whiskering: A ⊗ f for f : X → Y. -/
  wL : ∀ (A : C) {X Y}, Hom X Y → Hom (tensor A X) (tensor A Y)
  /-- whiskerLeft preserves identity. -/
  wL_id : ∀ (A X : C), wL A (cid X) = cid (tensor A X)
  /-- whiskerLeft preserves composition. -/
  wL_comp : ∀ (A : C) {X Y Z} (f : Hom X Y) (g : Hom Y Z),
    wL A (ccomp f g) = ccomp (wL A f) (wL A g)
  /-- Internal hom on objects. -/
  ihom : C → C → C
  /-- Currying: (A ⊗ X → Y) → (X → [A, Y]). -/
  cur : ∀ {A X Y}, Hom (tensor A X) Y → Hom X (ihom A Y)
  /-- Uncurrying: (X → [A, Y]) → (A ⊗ X → Y). -/
  unc : ∀ {A X Y}, Hom X (ihom A Y) → Hom (tensor A X) Y
  /-- cur ∘ unc = id. -/
  cur_unc : ∀ {A X Y} (g : Hom X (ihom A Y)), cur (unc g) = g
  /-- unc ∘ cur = id. -/
  unc_cur : ∀ {A X Y} (f : Hom (tensor A X) Y), unc (cur f) = f
  /-- Naturality of unc in the first argument:
      unc(g ≫ h) = wL(g) ≫ unc(h). -/
  unc_nat : ∀ {A X Y Z} (g : Hom X Y) (h : Hom Y (ihom A Z)),
    unc (ccomp g h) = ccomp (wL A g) (unc h)

variable {C : Type u} [ReflCat.{v} C]
open ReflCat

/-- Reflexive data: an isomorphism [A, L] ≅ L. -/
structure ReflData (A L : C) where
  /-- Forward: [A, L] → L. -/
  fwd : ReflCat.Hom (ihom A L) L
  /-- Backward: L → [A, L]. -/
  bwd : ReflCat.Hom L (ihom A L)
  /-- fwd ≫ bwd = id_{[A,L]}. -/
  fwd_bwd : ccomp fwd bwd = cid (ihom A L)
  /-- bwd ≫ fwd = id_L. -/
  bwd_fwd : ccomp bwd fwd = cid L

/-- Self-application: A ⊗ L → L.
    Decode an element of L as a function A → L via φ⁻¹, then evaluate.
    Construction: wL(φ.bwd) ≫ unc(id_{[A,L]}). -/
def selfApp {A L : C} (φ : ReflData A L) : ReflCat.Hom (tensor A L) L :=
  ccomp (wL A φ.bwd) (unc (cid (ihom A L)))

/-- Reflexive currying: (A ⊗ X → L) → (X → L).
    Curry then compose with the iso forward direction.
    Construction: cur(f) ≫ φ.fwd. -/
def reflexiveCurry {A L X : C} (φ : ReflData A L)
    (f : ReflCat.Hom (tensor A X) L) : ReflCat.Hom X L :=
  ccomp (cur f) φ.fwd

/-- The omega map (categorical Y combinator): L → L.
    Given f : L → L, produce the categorical analogue of λx. f(x x).
    Construction: reflexiveCurry(selfApp ≫ f). -/
def omega {A L : C} (φ : ReflData A L) (f : ReflCat.Hom L L) :
    ReflCat.Hom L L :=
  reflexiveCurry φ (ccomp (selfApp φ) f)

/-- Evaluation equation: wL(cur(f)) ≫ unc(id) = f.
    This is the computational content of the adjunction. -/
theorem eval_eq {A X Y : C} (f : ReflCat.Hom (tensor A X) Y) :
    ccomp (wL A (cur f)) (unc (cid (ihom A Y))) = f := by
  rw [← unc_nat, comp_id, unc_cur]

/-- Helper: φ.fwd ≫ φ.bwd cancels inside wL. -/
theorem wL_fwd_bwd {A L : C} (φ : ReflData A L) :
    ccomp (wL A φ.fwd) (wL A φ.bwd) = cid (tensor A (ihom A L)) := by
  rw [← wL_comp, φ.fwd_bwd, wL_id]

/-- **The fixed-point equation at axiom level ∅.**

    For any endomorphism f : L → L on a reflexive object:

      wL(omega(f)) ≫ selfApp = selfApp ≫ f

    This is the categorical Y combinator equation. It says omega(f)
    acts as a fixed point of "post-compose with f" on self-application.

    **Axiom profile: ∅.** No propext, no Quot.sound, no Classical.choice.
    The Y combinator is purely constructive — it constructs the fixed
    point witness from the equational theory of monoidal closed categories.
    This is the formal proof that structural self-reference lives below
    Classical.choice in the axiom hierarchy. -/
theorem omega_fixed_point {A L : C} (φ : ReflData A L)
    (f : ReflCat.Hom L L) :
    ccomp (wL A (omega φ f)) (selfApp φ) = ccomp (selfApp φ) f := by
  unfold omega reflexiveCurry selfApp
  rw [wL_comp, assoc, ← assoc (wL A φ.fwd), wL_fwd_bwd, id_comp, eval_eq]

end WTS.ReturnPath.ConstructiveOmega
