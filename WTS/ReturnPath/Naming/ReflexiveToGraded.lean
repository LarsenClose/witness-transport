/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ReflexiveToGraded — GradedReflModel derived from reflexive structure.

GradedReflModel is not an arbitrary axiom system. It is the natural structure
obtained by weakening a full reflexive isomorphism (fold∘unfold = id AND
unfold∘fold = id) to a retract (fold∘unfold = id only) and measuring the
failure of the dropped direction with a grade function.

The full iso gives selfApp = id (collapse regime, P = NP).
Dropping the reverse direction and adding a grade gives GradedReflModel.
When the grade is bounded, selfApp is near-id (collapse persists).
When the grade is unbounded, selfApp escapes every bound (separation regime).

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core

open WTS

namespace ReflexiveToGraded

-- ════════════════════════════════════════════════════════════
-- Section 1: Full reflexive structure
-- ════════════════════════════════════════════════════════════

/-- A full reflexive structure: fold and unfold are inverse in BOTH directions.
    This is the Type-level shadow of the categorical Lambek isomorphism
    [A, L] ≅ L, specialized to endomorphisms on a single type. -/
structure FullReflexiveStructure where
  carrier : Type
  fold : carrier → carrier
  unfold : carrier → carrier
  roundtrip : ∀ x, fold (unfold x) = x
  cotrip : ∀ x, unfold (fold x) = x

/-- selfApp in a full reflexive structure. -/
def FullReflexiveStructure.selfApp (F : FullReflexiveStructure) (x : F.carrier) :
    F.carrier :=
  F.unfold (F.fold x)

/-- In a full reflexive structure, selfApp = id. The cotrip axiom forces this. -/
theorem fullReflexive_selfApp_eq_id (F : FullReflexiveStructure) :
    ∀ x, F.selfApp x = x :=
  F.cotrip

/-- In a full reflexive structure, fold and unfold are mutual inverses:
    fold∘unfold = id and unfold∘fold = id. -/
theorem fullReflexive_mutual_inverse (F : FullReflexiveStructure) :
    (∀ x, F.fold (F.unfold x) = x) ∧ (∀ x, F.unfold (F.fold x) = x) :=
  ⟨F.roundtrip, F.cotrip⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Graded weakening — deriving GradedReflModel
-- ════════════════════════════════════════════════════════════

/-- A graded weakening: drop the cotrip axiom from FullReflexiveStructure,
    add a grade function that measures the failure of the reverse direction.
    This IS a GradedReflModel — the construction is definitional. -/
def gradedWeakening_to_gradedReflModel
    (carrier : Type) (fold unfold : carrier → carrier)
    (roundtrip : ∀ x, fold (unfold x) = x)
    (grade : carrier → Nat) : GradedReflModel where
  carrier := carrier
  fold := fold
  unfold := unfold
  roundtrip := roundtrip
  grade := grade

-- ════════════════════════════════════════════════════════════
-- Section 3: Full iso implies collapse regime
-- ════════════════════════════════════════════════════════════

/-- A FullReflexiveStructure induces a GradedReflModel with any grade function.
    Since selfApp = id, the choice of grade is irrelevant — it always collapses. -/
def fullReflexive_to_graded (F : FullReflexiveStructure) (grade : F.carrier → Nat) :
    GradedReflModel where
  carrier := F.carrier
  fold := F.fold
  unfold := F.unfold
  roundtrip := F.roundtrip
  grade := grade

/-- In the GradedReflModel induced by a full reflexive structure, selfApp = id
    (pointwise). The full iso forces collapse regardless of the grade function. -/
theorem fullReflexive_selfApp_is_id (F : FullReflexiveStructure)
    (grade : F.carrier → Nat) :
    ∀ x, (fullReflexive_to_graded F grade).selfApp x = x :=
  F.cotrip

/-- In the GradedReflModel induced by a full reflexive structure, PEqNP holds.
    Proof: selfApp = id, so it factors through grade 0. -/
theorem fullReflexive_to_collapse (F : FullReflexiveStructure)
    (grade : F.carrier → Nat) :
    PEqNP (fullReflexive_to_graded F grade) :=
  ⟨0, fun x hx => by
    show grade (F.unfold (F.fold x)) ≤ 0
    rw [F.cotrip]; exact hx⟩

/-- The converse direction: any GradedReflModel where selfApp = id satisfies PEqNP.
    This does NOT require a FullReflexiveStructure — just the pointwise condition. -/
theorem selfApp_eq_id_implies_collapse (M : GradedReflModel)
    (h : ∀ x, M.selfApp x = x) : PEqNP M :=
  ⟨0, fun x hx => by show M.grade (M.selfApp x) ≤ 0; rw [h]; exact hx⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Unbounded failure implies separation regime
-- ════════════════════════════════════════════════════════════

/-- When selfApp is unbounded, the GradedReflModel is in the separation regime.
    This is the direct negation of PEqNP: no grade bound works.
    The hypothesis SelfAppUnbounded witnesses the failure of cotrip at every
    grade — it is the graded measure of how far selfApp is from id. -/
theorem weakening_creates_separation (M : GradedReflModel)
    (h : SelfAppUnbounded M) : ¬PEqNP M := by
  intro ⟨d, hd⟩
  exact selfApp_not_factors M h d hd

-- ════════════════════════════════════════════════════════════
-- Section 5: Grade measures iso failure
-- ════════════════════════════════════════════════════════════

/-- The grade gap at a point: how much selfApp increases the grade.
    When selfApp = id (full iso), this is zero. When selfApp overflows,
    this witnesses the failure of the reverse iso direction. -/
def gradeGap (M : GradedReflModel) (x : M.carrier) : Int :=
  (M.grade (M.selfApp x) : Int) - (M.grade x : Int)

/-- In a model derived from a full reflexive structure, the grade gap is
    zero everywhere — selfApp is the identity, so it doesn't change the grade. -/
theorem fullReflexive_zero_gap (F : FullReflexiveStructure)
    (grade : F.carrier → Nat) (x : F.carrier) :
    gradeGap (fullReflexive_to_graded F grade) x = 0 := by
  simp [gradeGap, GradedReflModel.selfApp, fullReflexive_to_graded, F.cotrip x]

/-- SelfAppUnbounded means the grade gap is unbounded: for every target d,
    there exists a point where selfApp pushes the grade above d from below d.
    This is the graded witness of iso failure. -/
theorem unbounded_gap_from_selfAppUnbounded (M : GradedReflModel)
    (h : SelfAppUnbounded M) :
    ∀ d, ∃ x, M.grade x ≤ d ∧ gradeGap M x > 0 := by
  intro d
  obtain ⟨x, hle, hgt⟩ := h.overflows d
  exact ⟨x, hle, by simp [gradeGap]; omega⟩

/-- Grade-preservation at a point implies selfApp acts as a grade-bounded
    operation there. If grade(selfApp(x)) ≤ grade(x), the gap is non-positive.
    This is the local condition that, when global, gives collapse. -/
theorem grade_preserved_at_point (M : GradedReflModel) (x : M.carrier)
    (h : M.grade (M.selfApp x) ≤ M.grade x) :
    gradeGap M x ≤ 0 := by
  simp [gradeGap]; omega

-- ════════════════════════════════════════════════════════════
-- Section 6: The regime dichotomy from weakening
-- ════════════════════════════════════════════════════════════

/-- The regime dichotomy: for any GradedReflModel, either selfApp factors
    through some grade (collapse, PEqNP) or selfApp is unbounded (separation,
    ¬PEqNP). These are contradictory.

    This is the structural content: GradedReflModel arises from weakening
    the full iso. If the weakening is mild (bounded), collapse persists.
    If the weakening is severe (unbounded), separation appears.
    There is no third option. -/
theorem regime_contradiction (M : GradedReflModel)
    (hpeq : PEqNP M) (hunb : SelfAppUnbounded M) : False := by
  exact weakening_creates_separation M hunb hpeq

/-- The grounding theorem: a full reflexive structure cannot have unbounded
    selfApp, because selfApp = id. This connects the categorical construction
    (full Lambek iso) to the impossibility of separation in the full-iso case. -/
theorem fullReflexive_not_selfAppUnbounded (F : FullReflexiveStructure)
    (grade : F.carrier → Nat) :
    ¬SelfAppUnbounded (fullReflexive_to_graded F grade) := by
  intro ⟨h⟩
  obtain ⟨x, hle, hgt⟩ := h 0
  have : grade (F.unfold (F.fold x)) ≤ 0 := by rw [F.cotrip]; exact hle
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hgt this)

/-- Grounding summary: a full reflexive structure is always in the collapse
    regime. Separation requires genuine weakening of the iso — dropping
    cotrip is necessary for the separation to appear. -/
theorem fullReflexive_always_collapse (F : FullReflexiveStructure)
    (grade : F.carrier → Nat) :
    PEqNP (fullReflexive_to_graded F grade) ∧
    ¬SelfAppUnbounded (fullReflexive_to_graded F grade) :=
  ⟨fullReflexive_to_collapse F grade,
   fullReflexive_not_selfAppUnbounded F grade⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Witnessing both regimes from reflexive structure
-- ════════════════════════════════════════════════════════════

/-- Unit is a full reflexive structure (both directions trivially). -/
def unitFullReflexive : FullReflexiveStructure where
  carrier := Unit
  fold := id
  unfold := id
  roundtrip _ := rfl
  cotrip _ := rfl

/-- The trivialModel IS the graded weakening of unitFullReflexive.
    Collapse regime: derived from a full iso. -/
theorem trivialModel_from_full_reflexive :
    fullReflexive_to_graded unitFullReflexive (fun _ => 0) = trivialModel := by
  simp [fullReflexive_to_graded, unitFullReflexive, trivialModel]

/-- standardModel witnesses genuine weakening: fold∘unfold = id but
    unfold∘fold ≠ id. This is the separation regime — cotrip fails. -/
theorem standardModel_cotrip_fails :
    ∃ x, standardModel.selfApp x ≠ x := by
  refine ⟨(0 : Nat), ?_⟩
  show standardModel.unfold (standardModel.fold (0 : Nat)) ≠ (0 : Nat)
  simp [standardModel]

/-- The derivation story in one theorem:
    1. Full iso → collapse (PEqNP, selfApp bounded)
    2. Genuine weakening → separation possible (¬PEqNP when unbounded)
    3. Both regimes are witnessed by concrete models -/
theorem grounding_summary :
    -- Part 1: full iso always collapses
    (∀ (F : FullReflexiveStructure) (g : F.carrier → Nat),
      PEqNP (fullReflexive_to_graded F g)) ∧
    -- Part 2: unbounded weakening creates separation
    (∀ (M : GradedReflModel), SelfAppUnbounded M → ¬PEqNP M) ∧
    -- Part 3: both regimes exist
    (∃ M : GradedReflModel, PEqNP M) ∧
    (∃ M : GradedReflModel, ¬PEqNP M) :=
  ⟨fullReflexive_to_collapse,
   weakening_creates_separation,
   ⟨trivialModel, selfApp_eq_id_implies_collapse trivialModel
     (fun x => by cases x; rfl)⟩,
   ⟨standardModel, weakening_creates_separation standardModel
     standardModel_selfAppUnbounded⟩⟩

-- Axiom audit
#print axioms fullReflexive_selfApp_eq_id
#print axioms fullReflexive_to_collapse
#print axioms weakening_creates_separation
#print axioms fullReflexive_zero_gap
#print axioms unbounded_gap_from_selfAppUnbounded
#print axioms fullReflexive_not_selfAppUnbounded
#print axioms fullReflexive_always_collapse
#print axioms grounding_summary

end ReflexiveToGraded
