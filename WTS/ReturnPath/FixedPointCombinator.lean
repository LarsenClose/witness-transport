/-
  FixedPointCombinator.lean

  Constructs the fixed-point combinator (Y combinator) from a reflexive object
  and proves the fixed-point property.

  Given a reflexive object with isomorphism D ≅ (D → D), the Y combinator is:
    Y f = (fun x => f (unfold x x)) (fold (fun x => f (unfold x x)))

  which simplifies to: Y f = f (Y f).

  This is the type-theoretic distillation of the categorical construction
  in which `omega f = reflexiveCurry (selfApp >> f)` and the double application
  `omega f (omega f)` yields the fixed point.

  Pure Lean 4, no sorry, no axioms beyond propext and Quot.sound.
-/

import WTS.ReturnPath.ReflexiveObject

namespace WTS.ReturnPath

-- ReflexiveObject imported from ReflexiveObject.lean.

namespace ReflexiveObject

variable (r : ReflexiveObject)

-- selfApp and selfApp_fold imported from ReflexiveObject.lean.

/-! ### The omega construction

`omega f` is the type-theoretic analogue of `lambda x. f(x x)` — it reifies
the operation "unfold, self-apply, then post-compose with f". -/

/-- The omega map: given `f : D → D`, produce the element of D that represents
    `lambda x. f (unfold x x)`.

    This is `fold (fun x => f (selfApp x))`. -/
def omega (f : r.D → r.D) : r.D :=
  r.fold (fun x => f (r.selfApp x))

/-- Unfolding omega recovers the self-apply-then-f operation:
    `unfold (omega f) = fun x => f (selfApp x)`. -/
theorem unfold_omega (f : r.D → r.D) :
    r.unfold (r.omega f) = fun x => f (r.selfApp x) := by
  unfold omega selfApp
  exact r.unfold_fold _

/-- Self-applying omega: `selfApp (omega f) = f (selfApp (omega f))`.

    This is the key step: omega f applied to itself yields f applied to the
    result. In lambda notation: `(lambda x. f(x x))(lambda x. f(x x)) = f(...)`. -/
theorem selfApp_omega (f : r.D → r.D) :
    r.selfApp (r.omega f) = f (r.selfApp (r.omega f)) := by
  unfold selfApp omega
  have h := r.unfold_fold (fun x => f (r.unfold x x))
  exact congrFun h (r.fold fun x => f (r.unfold x x))

/-! ### The Y combinator

The Y combinator is `omega f` self-applied: `Y f = selfApp (omega f)`.
This is the type-theoretic version of `Y f = (lambda x. f(x x))(lambda x. f(x x))`. -/

/-- The Y combinator: `Y f = selfApp (omega f)`.

    Equivalently, `Y f = unfold (omega f) (omega f)`, which is
    `(lambda x. f(x x))` applied to `(lambda x. f(x x))`. -/
def Y (f : r.D → r.D) : r.D :=
  r.selfApp (r.omega f)

/-- **The fixed-point theorem.** For any `f : D → D`:

      `Y f = f (Y f)`

    Every endomorphism of a reflexive object has a fixed point.
    This is the fundamental theorem of reflexive computation. -/
theorem Y_fixed_point (f : r.D → r.D) :
    r.Y f = f (r.Y f) :=
  r.selfApp_omega f

/-- Y is definitionally `selfApp ∘ omega`. -/
theorem Y_def (f : r.D → r.D) :
    r.Y f = r.selfApp (r.omega f) :=
  rfl

/-- Y of the identity is a fixed point of the identity, hence equal to itself. -/
theorem Y_id :
    r.Y id = id (r.Y id) :=
  r.Y_fixed_point id

/-! ### Omega properties -/

/-- Omega of the identity reifies `selfApp` itself. -/
theorem omega_id :
    r.omega id = r.fold (fun x => r.selfApp x) :=
  rfl

/-- Omega respects post-composition: `selfApp (omega (g ∘ f))` equals
    `g (f (selfApp (omega (g ∘ f))))`. -/
theorem selfApp_omega_comp (f g : r.D → r.D) :
    r.selfApp (r.omega (g ∘ f)) = g (f (r.selfApp (r.omega (g ∘ f)))) :=
  r.selfApp_omega (g ∘ f)

/-! ### Double application -/

/-- Double omega: `omega f` composed with itself at the element level.
    This is the morphism-level analogue of `omega_f(omega_f)`. -/
def omegaSq (f : r.D → r.D) : r.D :=
  r.unfold (r.omega f) (r.omega f)

/-- `omegaSq` equals `Y` (they are the same computation). -/
theorem omegaSq_eq_Y (f : r.D → r.D) :
    r.omegaSq f = r.Y f :=
  rfl

/-- The fixed-point equation restated for `omegaSq`. -/
theorem omegaSq_fixed_point (f : r.D → r.D) :
    r.omegaSq f = f (r.omegaSq f) := by
  show r.Y f = f (r.Y f)
  exact r.Y_fixed_point f

/-! ### Axiom audit -/

#print axioms ReflexiveObject.Y_fixed_point
#print axioms ReflexiveObject.selfApp_omega
#print axioms ReflexiveObject.omegaSq_fixed_point

end ReflexiveObject

end WTS.ReturnPath
