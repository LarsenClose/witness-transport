/-
  ReflexiveObject.lean

  Defines a reflexive object: a type D equipped with an isomorphism D ≅ (D → D),
  known as the Lambek isomorphism. This is the type-theoretic distillation of the
  categorical reflexive domain equation [A, L] ≅ L.

  The isomorphism witnesses that D "contains its own function space": every element
  of D can be interpreted as an endomorphism D → D (via `unfold`), and every
  endomorphism can be reified as an element of D (via `fold`).

  From this single structure we derive:
  - `selfApp : D → D` — interpret an element as a function and apply it to itself
  - `curry` / `uncurry` — collapse and expand the function-space isomorphism

  Pure Lean 4, no imports, no sorry, no axioms beyond propext and Quot.sound.
-/

namespace WTS.ReturnPath

/-- A reflexive object: a type `D` with an isomorphism `D ≅ (D → D)`.

    `fold` reifies an endomorphism as a datum; `unfold` interprets a datum as
    an endomorphism. The two round-trip laws witness that these are inverse. -/
structure ReflexiveObject where
  /-- The carrier type. -/
  D : Type
  /-- Reify: embed an endomorphism into the carrier. -/
  fold : (D → D) → D
  /-- Reflect: interpret a carrier element as an endomorphism. -/
  unfold : D → (D → D)
  /-- Round-trip: reflecting a reified function recovers it. -/
  unfold_fold : ∀ f : D → D, unfold (fold f) = f
  /-- Round-trip: reifying a reflected element recovers it. -/
  fold_unfold : ∀ d : D, fold (unfold d) = d

namespace ReflexiveObject

variable (r : ReflexiveObject)

/-! ### Self-application

The fundamental operation on a reflexive object: interpret an element
as a function (via `unfold`) and apply it to itself. This is the
type-theoretic analogue of `selfApp : A ⊗ L ⟶ L` in the categorical setting. -/

/-- Self-application: interpret `d` as a function and apply it to itself.
    `selfApp d = (unfold d) d` -/
def selfApp (d : r.D) : r.D :=
  r.unfold d d

/-- Self-application of a reified function applies the function to its own reification. -/
theorem selfApp_fold (f : r.D → r.D) :
    r.selfApp (r.fold f) = f (r.fold f) := by
  unfold selfApp
  have h := r.unfold_fold f
  exact congrFun h (r.fold f)

/-- `selfApp` is `unfold` applied diagonally. -/
theorem selfApp_def (d : r.D) :
    r.selfApp d = r.unfold d d :=
  rfl

/-! ### Reflexive currying

Currying collapses the two-argument structure `D → D → D` into `D → D`
by passing through the isomorphism. Uncurrying goes the other way. -/

/-- Reflexive curry: given `f : D → D → D`, produce `D → D` by
    reifying the inner function at each point.

    `curry f d = fold (f d)` — apply f to get an endomorphism, then reify. -/
def curry (f : r.D → r.D → r.D) (d : r.D) : r.D :=
  r.fold (f d)

/-- Reflexive uncurry: given `g : D → D`, produce `D → D → D` by
    reflecting each output.

    `uncurry g d₁ d₂ = unfold (g d₁) d₂` — apply g to get an element,
    reflect it as a function, then apply. -/
def uncurry (g : r.D → r.D) (d₁ d₂ : r.D) : r.D :=
  r.unfold (g d₁) d₂

/-- Curry then uncurry recovers the original two-argument function. -/
theorem uncurry_curry (f : r.D → r.D → r.D) :
    r.uncurry (r.curry f) = f := by
  funext d₁ d₂
  show r.unfold (r.fold (f d₁)) d₂ = f d₁ d₂
  rw [r.unfold_fold]

/-- Uncurry then curry recovers the original one-argument function. -/
theorem curry_uncurry (g : r.D → r.D) :
    r.curry (r.uncurry g) = g := by
  funext d
  show r.fold (r.unfold (g d)) = g d
  rw [r.fold_unfold]

/-! ### Identity properties -/

/-- Folding the identity function and then unfolding recovers the identity. -/
theorem unfold_fold_id :
    r.unfold (r.fold id) = id :=
  r.unfold_fold id

/-- Self-application of `fold id` is `fold id` itself: the identity is a
    fixed point of self-application. -/
theorem selfApp_fold_id :
    r.selfApp (r.fold id) = r.fold id := by
  rw [selfApp_fold]; rfl

/-! ### Axiom audit -/

#print axioms ReflexiveObject.selfApp_fold
#print axioms ReflexiveObject.uncurry_curry
#print axioms ReflexiveObject.curry_uncurry
#print axioms ReflexiveObject.selfApp_fold_id

end ReflexiveObject

end WTS.ReturnPath
