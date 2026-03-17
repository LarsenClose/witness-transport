/-
  Containerization.lean

  Defines a closed container: a type equipped with eval/name operations
  satisfying beta and eta laws. A closed container is the organizational
  structure that enables self-reference and computation.

  The key operations:
  - `eval : D → D → D` — interpret an element as a function and apply it
  - `name : (D → D) → D` — reify a function as an element

  The laws:
  - Beta: `eval (name f) = f` — evaluating a named function recovers it
  - Eta: `name (eval d) = d` — naming an element's evaluation recovers it

  Every reflexive object (D ≅ (D → D)) gives rise to a closed container
  where eval = unfold and name = fold. The container perspective highlights
  that the Lambek isomorphism IS the container boundary.

  Pure Lean 4, no sorry, no axioms beyond propext and Quot.sound.
-/

import WTS.ReturnPath.ReflexiveObject

namespace WTS.ReturnPath

-- ReflexiveObject imported from ReflexiveObject.lean.

/-! ### Closed container structure -/

/-- A closed container: a type with eval/name operations satisfying beta and eta.

    `eval` opens the container: it interprets an element as a function.
    `name` closes the container: it reifies a function as an element.

    The beta law says that opening a closed thing recovers the content.
    The eta law says that closing the opened thing recovers the element.

    Together, these witness that the container boundary is an isomorphism:
    the type is closed under its own function space. -/
structure ClosedContainer where
  /-- The carrier type: what is inside the container. -/
  D : Type
  /-- Evaluation: interpret an element as a function (open the container). -/
  eval : D → D → D
  /-- Naming: reify a function as an element (close the container). -/
  name : (D → D) → D
  /-- Beta law: evaluating a named function recovers the function. -/
  beta : ∀ f : D → D, eval (name f) = f
  /-- Eta law: naming the evaluation of an element recovers the element. -/
  eta : ∀ d : D, name (eval d) = d

/-! ### Every reflexive object is a closed container -/

namespace ReflexiveObject

/-- Construct a closed container from a reflexive object.

    The Lambek isomorphism IS the container boundary:
    - `eval = unfold` (interpret as function = open the container)
    - `name = fold` (reify as element = close the container)
    - beta = `unfold_fold` (reflecting a reified function recovers it)
    - eta = `fold_unfold` (reifying a reflected element recovers it) -/
def toClosedContainer (r : ReflexiveObject) : ClosedContainer where
  D := r.D
  eval := r.unfold
  name := r.fold
  beta := r.unfold_fold
  eta := r.fold_unfold

/-- The container built from a reflexive object has eval = unfold. -/
theorem toClosedContainer_eval (r : ReflexiveObject) :
    r.toClosedContainer.eval = r.unfold :=
  rfl

/-- The container built from a reflexive object has name = fold. -/
theorem toClosedContainer_name (r : ReflexiveObject) :
    r.toClosedContainer.name = r.fold :=
  rfl

end ReflexiveObject

/-! ### Derived operations on closed containers -/

namespace ClosedContainer

variable (c : ClosedContainer)

/-- Self-application in a closed container: `eval d d`. -/
def selfApp (d : c.D) : c.D :=
  c.eval d d

/-- Self-reference: the element that, when evaluated, performs self-application.
    This is `name (fun d => eval d d)` — the quine. -/
def selfReference : c.D :=
  c.name c.selfApp

/-- Evaluating the self-reference element recovers self-application. -/
theorem eval_selfReference :
    c.eval c.selfReference = c.selfApp := by
  show c.eval (c.name c.selfApp) = c.selfApp
  rw [c.beta]

/-! ### Fixed-point combinator from containers

The Y combinator expressed purely in terms of eval/name.
`omega f = name (fun x => f (eval x x))`
`Y f = eval (omega f) (omega f)` -/

/-- The omega map in container form: `name (fun x => f (eval x x))`. -/
def omega (f : c.D → c.D) : c.D :=
  c.name (fun x => f (c.selfApp x))

/-- The Y combinator in container form: `selfApp (omega f)`. -/
def Y (f : c.D → c.D) : c.D :=
  c.selfApp (c.omega f)

/-- **The fixed-point equation for closed containers.**

      `Y f = f (Y f)`

    This is the Y combinator equation expressed purely in terms
    of the container's eval/name interface. -/
theorem Y_fixed_point (f : c.D → c.D) :
    c.Y f = f (c.Y f) := by
  unfold Y selfApp omega
  exact congrFun (c.beta (fun x => f (c.eval x x)))
    (c.name fun x => f (c.eval x x))

/-- Self-reference equals omega of the identity:
    `name(selfApp) = name(fun x => id(selfApp x)) = omega(id)`.
    The quine is omega applied to doing nothing. -/
theorem selfReference_eq_omega_id :
    c.selfReference = c.omega id :=
  rfl

/-! ### The eval-name bijection

The beta and eta laws together witness that `eval` and `name` form
a bijection `D ↔ (D → D)`. We package this as a pair of inverse functions. -/

/-- `name` is a left inverse of `eval`. -/
theorem name_eval (d : c.D) :
    c.name (c.eval d) = d :=
  c.eta d

/-- `eval` is a left inverse of `name`. -/
theorem eval_name (f : c.D → c.D) :
    c.eval (c.name f) = f :=
  c.beta f

/-- `name` is injective. -/
theorem name_injective (f g : c.D → c.D) (h : c.name f = c.name g) :
    f = g := by
  have hf := c.beta f
  have hg := c.beta g
  rw [← hf, ← hg, h]

/-- `eval` is injective. -/
theorem eval_injective (a b : c.D) (h : c.eval a = c.eval b) :
    a = b := by
  have ha := c.eta a
  have hb := c.eta b
  rw [← ha, ← hb, h]

/-! ### Composition in a closed container

A closed container supports composition of named functions. -/

/-- Compose two elements as functions: `comp a b = name (eval a ∘ eval b)`. -/
def comp (a b : c.D) : c.D :=
  c.name (c.eval a ∘ c.eval b)

/-- Evaluating a composition yields function composition. -/
theorem eval_comp (a b : c.D) :
    c.eval (c.comp a b) = c.eval a ∘ c.eval b := by
  show c.eval (c.name (c.eval a ∘ c.eval b)) = c.eval a ∘ c.eval b
  exact c.beta _

/-- The identity element: `name id`. -/
def idElem : c.D :=
  c.name id

/-- Evaluating the identity element yields the identity function. -/
theorem eval_idElem :
    c.eval c.idElem = id := by
  show c.eval (c.name id) = id
  exact c.beta id

/-- Right identity for composition. -/
theorem comp_idElem (a : c.D) :
    c.comp a c.idElem = a := by
  show c.name (c.eval a ∘ c.eval (c.name id)) = a
  rw [c.beta]
  show c.name (c.eval a ∘ id) = a
  rw [Function.comp_id]
  exact c.eta a

/-- Left identity for composition. -/
theorem idElem_comp (a : c.D) :
    c.comp c.idElem a = a := by
  show c.name (c.eval (c.name id) ∘ c.eval a) = a
  rw [c.beta]
  show c.name (id ∘ c.eval a) = a
  rw [Function.id_comp]
  exact c.eta a

/-- Composition is associative. -/
theorem comp_assoc (a b d : c.D) :
    c.comp (c.comp a b) d = c.comp a (c.comp b d) := by
  show c.name (c.eval (c.name (c.eval a ∘ c.eval b)) ∘ c.eval d)
     = c.name (c.eval a ∘ c.eval (c.name (c.eval b ∘ c.eval d)))
  simp only [c.beta]
  rfl

/-! ### Axiom audit -/

#print axioms ClosedContainer.Y_fixed_point
#print axioms ClosedContainer.selfReference_eq_omega_id
#print axioms ClosedContainer.eval_selfReference
#print axioms ClosedContainer.comp_assoc
#print axioms ClosedContainer.comp_idElem
#print axioms ClosedContainer.idElem_comp

end ClosedContainer

end WTS.ReturnPath
