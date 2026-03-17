/-
The Omega Tower, parameterized by a grade cutoff.

The tower is fixed: it's the positive chain (axiom empty).
The cutoff moves: it's the grade function (the naming convention).
The hierarchy has always and only existed within naming.
-/

import WTS.ReturnPath.ConstructiveOmega
import WTS.ReturnPath.ReflexiveObject
import WTS.ReturnPath.FixedPointCombinator
import WTS.Core

namespace WTS.Generator

open WTS.ReturnPath.ConstructiveOmega
open WTS.ReturnPath
open WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The tower (fixed, axiom empty)
-- ════════════════════════════════════════════════════════════

inductive TowerLevel where
  | grammar
  | fixedPoint
  | selfReference
  | abstraction
  | selfIndexing
  deriving BEq

def TowerLevel.rank : TowerLevel → Nat
  | .grammar => 0
  | .fixedPoint => 1
  | .selfReference => 2
  | .abstraction => 3
  | .selfIndexing => 4

-- ════════════════════════════════════════════════════════════
-- Section 2: Enriched level answers
-- ════════════════════════════════════════════════════════════

/-- Level 1 answer: what does the fixed-point construction cost?
    At axiom empty: free (no grade). With grade: gradeGap. -/
structure FixedPointCost (M : GradedReflModel) where
  /-- selfApp is idempotent (always true, from roundtrip) -/
  idempotent : ∀ x, M.selfApp (M.selfApp x) = M.selfApp x
  /-- Is selfApp grade-bounded? -/
  bounded : Prop
  /-- Does selfApp overflow every grade? -/
  unbounded : Prop
  /-- These are exclusive -/
  exclusive : bounded → ¬unbounded

/-- Level 2 answer: what is the self-referential nucleus?
    The substrate Im(selfApp) where selfApp = id pointwise. -/
structure SubstrateShape (M : GradedReflModel) where
  /-- Every image point is fixed -/
  image_fixed : ∀ x, M.selfApp (M.selfApp x) = M.selfApp x
  /-- Roundtrip holds on image -/
  image_roundtrip : ∀ x, M.fold (M.unfold (M.selfApp x)) = M.selfApp x
  /-- Cotrip holds on image -/
  image_cotrip : ∀ x, M.unfold (M.fold (M.selfApp x)) = M.selfApp x

/-- Level 3 answer: how does eta fail?
    Beta always holds (roundtrip). Eta (cotrip) may fail.
    When it fails, selfApp is the residual. -/
structure EtaStatus (M : GradedReflModel) where
  /-- Beta always holds -/
  beta : ∀ x, M.fold (M.unfold x) = x
  /-- Does eta hold? (selfApp = id) -/
  eta_holds : Prop
  /-- If eta fails, selfApp is the residual projection -/
  residual_idempotent : ∀ x, M.selfApp (M.selfApp x) = M.selfApp x

/-- Level 4 answer: the naming equivalence.
    At axiom empty: full equivalence (every operation has a name,
    every name denotes an operation).
    With grade: may decouple. -/
structure NamingEquivalence (M : GradedReflModel) where
  /-- The naming direction: does fold ∘ unfold = id? (always, roundtrip) -/
  naming_recovers : ∀ x, M.fold (M.unfold x) = x
  /-- The interpretation direction: does unfold ∘ fold = id? (eta) -/
  interp_recovers : Prop
  /-- On Im(selfApp), interpretation always recovers -/
  interp_on_substrate : ∀ x, M.unfold (M.fold (M.selfApp x)) = M.selfApp x

-- ════════════════════════════════════════════════════════════
-- Section 3: The full profile at a GRM
-- ════════════════════════════════════════════════════════════

/-- The full enriched profile: what the tower looks like through
    a specific naming convention (grade function). -/
structure TowerProfile (M : GradedReflModel) where
  fixedPointCost : FixedPointCost M
  substrate : SubstrateShape M
  eta : EtaStatus M
  naming : NamingEquivalence M

/-- Every GRM has a canonical enriched profile. -/
def canonical (M : GradedReflModel) : TowerProfile M where
  fixedPointCost := {
    idempotent := fun x => by
      show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
      rw [M.roundtrip]
    bounded := PEqNP M
    unbounded := ∃ _ : SelfAppUnbounded M, True
    exclusive := fun hb ⟨hu, _⟩ => by
      obtain ⟨d, hd⟩ := hb
      obtain ⟨x, hle, hgt⟩ := hu.overflows d
      exact absurd (hd x hle) (by omega)
  }
  substrate := {
    image_fixed := fun x => by
      show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
      rw [M.roundtrip]
    image_roundtrip := fun x => M.roundtrip (M.selfApp x)
    image_cotrip := fun x => by
      show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
      rw [M.roundtrip]
  }
  eta := {
    beta := M.roundtrip
    eta_holds := ∀ x, M.selfApp x = x
    residual_idempotent := fun x => by
      show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
      rw [M.roundtrip]
  }
  naming := {
    naming_recovers := M.roundtrip
    interp_recovers := ∀ x, M.selfApp x = x
    interp_on_substrate := fun x => by
      show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
      rw [M.roundtrip]
  }

-- ════════════════════════════════════════════════════════════
-- Section 4: What's derivable? What carries independent content?
-- ════════════════════════════════════════════════════════════

/-- substrate.image_fixed = fixedPointCost.idempotent.
    Same proof. No independent content. -/
theorem substrate_eq_idempotent (M : GradedReflModel) :
    (canonical M).substrate.image_fixed = (canonical M).fixedPointCost.idempotent :=
  rfl

/-- eta.beta = naming.naming_recovers = M.roundtrip.
    Same proof three times. No independent content. -/
theorem beta_eq_naming (M : GradedReflModel) :
    (canonical M).eta.beta = (canonical M).naming.naming_recovers :=
  rfl

/-- eta.eta_holds = naming.interp_recovers = (∀ x, selfApp x = x).
    Same Prop. No independent content. -/
theorem eta_eq_interp (M : GradedReflModel) :
    (canonical M).eta.eta_holds = (canonical M).naming.interp_recovers :=
  rfl

/-- substrate.image_cotrip = substrate.image_fixed.
    Same proof. No independent content. -/
theorem cotrip_eq_fixed (M : GradedReflModel) :
    (canonical M).substrate.image_cotrip = (canonical M).substrate.image_fixed :=
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 5: What's NOT derivable — the independent content
-- ════════════════════════════════════════════════════════════

/-- fixedPointCost.bounded (PEqNP) is NOT derivable from eta_holds.
    retractionModel: PEqNP but selfApp ≠ id. -/
@[reducible] def retractionModel : GradedReflModel where
  carrier := Nat
  fold x := x / 2
  unfold x := 2 * x
  roundtrip x := by show 2 * x / 2 = x; omega
  grade := id

theorem bounded_not_from_eta :
    (∃ M : GradedReflModel,
      (canonical M).fixedPointCost.bounded ∧
      ¬(canonical M).eta.eta_holds) :=
  ⟨retractionModel,
   ⟨0, fun x hx => by
     change 2 * (x / 2) ≤ 0
     have : x = 0 := Nat.le_zero.mp hx; subst this; decide⟩,
   fun h => by have := h 1; simp [GradedReflModel.selfApp, retractionModel] at this⟩

/-- eta_holds implies bounded. The reverse fails (above). -/
theorem eta_implies_bounded (M : GradedReflModel)
    (h : (canonical M).eta.eta_holds) :
    (canonical M).fixedPointCost.bounded :=
  ⟨0, fun x hx => by show M.grade (M.selfApp x) ≤ 0; rw [h]; exact hx⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: The collapse — how much is independent?
-- ════════════════════════════════════════════════════════════

/-- The profile collapses. After removing derivable content:

    ALWAYS TRUE (from roundtrip, carries no information):
    - idempotent, image_fixed, image_roundtrip, image_cotrip,
      residual_idempotent, interp_on_substrate
    - beta, naming_recovers

    SAME PROP (one degree of freedom, not two):
    - eta_holds = interp_recovers = (∀ x, selfApp x = x)

    RELATED BUT NOT IDENTICAL (the independent content):
    - bounded (PEqNP): ∃ d, selfApp factors through d
    - eta_holds: selfApp = id everywhere
    - unbounded: selfApp overflows every grade

    The profile has exactly TWO independent propositions:
    1. Is selfApp bounded? (PEqNP)
    2. Is selfApp identity? (eta_holds / cotrip)

    These give three regimes:
    - selfApp = id → bounded (full regime)
    - bounded but selfApp ≠ id (answer space)
    - unbounded → ¬bounded (separation)

    The hierarchy IS these two propositions. -/
theorem profile_has_two_degrees_of_freedom :
    -- eta → bounded (one direction)
    (∀ (M : GradedReflModel), (∀ x, M.selfApp x = x) → PEqNP M) ∧
    -- bounded ↛ eta (strict)
    (∃ M : GradedReflModel, PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∧
    -- ¬bounded → ¬eta (trivial)
    (∀ (M : GradedReflModel), ¬PEqNP M → ¬(∀ x, M.selfApp x = x)) :=
  ⟨fun M h => eta_implies_bounded M h,
   bounded_not_from_eta,
   fun M hnb heta => hnb (eta_implies_bounded M heta)⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: The tower is always complete (computation side)
-- ════════════════════════════════════════════════════════════

/-- The tower exists at axiom empty. -/
theorem tower_complete (r : ReflexiveObject) :
    (∀ f : r.D → r.D, ∃ d : r.D, r.unfold d = f) ∧
    (∀ f : r.D → r.D, r.Y f = f (r.Y f)) ∧
    (∃ q : r.D, r.unfold q q = r.unfold q q) ∧
    (∀ f : r.D → r.D, r.unfold (r.fold f) = f) ∧
    (∀ d : r.D, r.fold (r.unfold d) = d) :=
  ⟨fun f => ⟨r.fold f, r.unfold_fold f⟩,
   fun f => r.Y_fixed_point f,
   ⟨r.fold (fun x => r.unfold x x), rfl⟩,
   r.unfold_fold,
   r.fold_unfold⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Three regimes exist
-- ════════════════════════════════════════════════════════════

theorem group_C_exists :
    ∃ M : GradedReflModel, ∀ x, M.selfApp x = x :=
  ⟨trivialModel, fun x => by cases x; rfl⟩

theorem separation_exists :
    ∃ M : GradedReflModel, SelfAppUnbounded M :=
  ⟨standardModel, standardModel_selfAppUnbounded⟩

theorem answer_space_exists :
    ∃ M : GradedReflModel, PEqNP M ∧ ¬(∀ x, M.selfApp x = x) :=
  bounded_not_from_eta

-- ════════════════════════════════════════════════════════════
-- Section 9: Double negation — what does classical add?
-- ════════════════════════════════════════════════════════════

/-- The regime question is ¬¬-stable: constructively, we know it's
    not the case that the regime question has no answer.
    This is provable at ∅ — no classical axioms. -/
theorem regime_dn (M : GradedReflModel) :
    ¬¬(PEqNP M ∨ ¬PEqNP M) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

/-- The eta question is ¬¬-stable too. -/
theorem eta_dn (M : GradedReflModel) :
    ¬¬((∀ x, M.selfApp x = x) ∨ ¬(∀ x, M.selfApp x = x)) :=
  fun h => h (Or.inr (fun heta => h (Or.inl heta)))

/-- The full 2-bit classification is ¬¬-stable. -/
theorem classification_dn (M : GradedReflModel) :
    ¬¬((∀ x, M.selfApp x = x) ∨
        (PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∨
        ¬PEqNP M) := by
  intro h
  apply h
  right; right
  intro hp
  apply h
  right; left
  constructor
  · exact hp
  · intro heta
    apply h
    left
    exact heta

/-- With Classical.em, the classification becomes decidable.
    This is what Classical.choice adds: not a new regime,
    but the ability to determine which regime applies. -/
theorem classification_classical (M : GradedReflModel) :
    (∀ x, M.selfApp x = x) ∨
    (PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∨
    ¬PEqNP M := by
  by_cases heta : (∀ x, M.selfApp x = x)
  · left; exact heta
  · by_cases hb : PEqNP M
    · right; left; exact ⟨hb, heta⟩
    · right; right; exact hb

/-- The substrate is always constructive. -/
theorem substrate_constructive (M : GradedReflModel) (x : M.carrier) :
    M.selfApp (M.selfApp x) = M.selfApp x := by
  show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
  rw [M.roundtrip]

/-- Bounded → substrate accessible. Constructive (no classical).
    Note: PEqNP is not used — idempotence is free from roundtrip.
    The hypothesis is retained to show the substrate is available
    even when the caller only knows the bounded regime. -/
theorem bounded_substrate (M : GradedReflModel) (_h : PEqNP M) :
    ∀ x, M.selfApp (M.selfApp x) = M.selfApp x :=
  fun x => substrate_constructive M x

/-- ¬¬-bounded → ¬¬-substrate accessible. Lifts through ¬¬.
    Note: the ¬¬PEqNP hypothesis is not used — the conclusion
    is constructively true regardless. Retained to show the
    substrate lives below the ¬¬/classical split. -/
theorem dn_bounded_substrate (M : GradedReflModel)
    (_h : ¬¬PEqNP M) :
    ¬¬(∀ x, M.selfApp (M.selfApp x) = M.selfApp x) :=
  fun hn => hn (substrate_constructive M)

/-- But the substrate is actually STRONGER than ¬¬:
    it's constructively true regardless of regime.
    The ¬¬ wrapper was unnecessary. This shows the substrate
    lives below the ¬¬/classical split — it's pure computation. -/
theorem substrate_below_dn (M : GradedReflModel) :
    (∀ x, M.selfApp (M.selfApp x) = M.selfApp x) ∧
    ¬¬(PEqNP M ∨ ¬PEqNP M) :=
  ⟨substrate_constructive M, regime_dn M⟩

-- ════════════════════════════════════════════════════════════
-- Section 10: The three axiom levels of naming
-- ════════════════════════════════════════════════════════════

/-- The tower decomposes into three axiom strata:

    Stratum 0 (∅ axioms): the tower itself, substrate, idempotence,
    beta/roundtrip, and the ¬¬-stability of the regime question.
    This is computation + the irrefutability of naming.

    Stratum 1 (propext + Quot.sound): concrete witnesses for all
    three regimes. trivialModel, standardModel, retractionModel.
    This is naming demonstrated.

    Stratum 2 (Classical.choice): regime classification for an
    ARBITRARY GradedReflModel. This is naming naming itself —
    the naming convention that determines which naming regime
    a given naming convention falls in.

    Classical.choice is the naming axiom that lets naming
    talk about itself. The tower (computation) never needs it.
    The witnesses (naming demonstrated) need propext + Quot.sound.
    The self-classification (naming naming) needs choice. -/
theorem three_strata :
    -- Stratum 0: tower + ¬¬-stability (∅)
    (∀ (r : ReflexiveObject) (f : r.D → r.D), r.Y f = f (r.Y f)) ∧
    (∀ (M : GradedReflModel), ¬¬(PEqNP M ∨ ¬PEqNP M)) ∧
    -- Stratum 1: witnesses (propext + Quot.sound)
    (∃ M : GradedReflModel, ∀ x, M.selfApp x = x) ∧
    (∃ M : GradedReflModel, SelfAppUnbounded M) :=
  ⟨fun r f => r.Y_fixed_point f,
   regime_dn,
   group_C_exists,
   separation_exists⟩

-- ════════════════════════════════════════════════════════════
-- Section 11: ¬PEqNP vs SelfAppUnbounded — classical equivalence?
-- ════════════════════════════════════════════════════════════

/-- ¬PEqNP unfolds to: no grade bound works for selfApp. -/
theorem not_peqnp_unfold (M : GradedReflModel) :
    ¬PEqNP M ↔ ∀ d, ¬FactorsThrough M M.selfApp d :=
  ⟨fun h d hf => h ⟨d, hf⟩, fun h ⟨d, hf⟩ => h d hf⟩

/-- SelfAppUnbounded → ¬PEqNP. Constructive (∅ direction). -/
theorem unbounded_implies_not_peqnp (M : GradedReflModel)
    (h : SelfAppUnbounded M) : ¬PEqNP M := by
  intro ⟨d, hd⟩
  obtain ⟨x, hle, hgt⟩ := h.overflows d
  have := hd x hle; omega

/-- ¬FactorsThrough gives an explicit overflow at that grade.
    Uses classical reasoning (by_contra) to extract the witness. -/
theorem not_factors_gives_overflow (M : GradedReflModel) (d : Nat)
    (h : ¬FactorsThrough M M.selfApp d) :
    ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d :=
  Classical.byContradiction fun hc => h fun x hle =>
    Classical.byContradiction fun hgt =>
      hc ⟨x, hle, by omega⟩

/-- ¬PEqNP → SelfAppUnbounded. Extracts overflow witnesses. -/
theorem not_peqnp_implies_unbounded (M : GradedReflModel)
    (h : ¬PEqNP M) : SelfAppUnbounded M where
  overflows d := by
    have hnd := (not_peqnp_unfold M).mp h d
    exact not_factors_gives_overflow M d hnd

/-- The full equivalence: PEqNP ↔ ¬SelfAppUnbounded. -/
theorem peqnp_iff_not_unbounded (M : GradedReflModel) :
    PEqNP M ↔ ¬SelfAppUnbounded M :=
  ⟨fun hp hu => unbounded_implies_not_peqnp M hu hp,
   fun hnu => by
    -- Need to show PEqNP from ¬SelfAppUnbounded
    -- ¬SelfAppUnbounded = ¬(∀ d, ∃ x, ...) -- this is hard constructively
    -- Use classical: ¬¬PEqNP → PEqNP
    exact Classical.byContradiction fun hnp =>
      hnu (not_peqnp_implies_unbounded M hnp)⟩

-- ════════════════════════════════════════════════════════════
-- Section 12: PolyMarkov — the middle stratum
-- ════════════════════════════════════════════════════════════

/-- PolyMarkov: for decidable predicates over Nat,
    double-negation of existence implies existence.
    Strictly between ∅ and Classical.choice. -/
def PolyMarkov : Prop :=
  ∀ (P : Nat → Prop), (∀ n, Decidable (P n)) → ¬¬(∃ n, P n) → ∃ n, P n

/-- PolyMarkov follows from Classical.choice (EM → PolyMarkov). -/
theorem polymarkov_from_em
    (em : ∀ P : Prop, P ∨ ¬P) : PolyMarkov :=
  fun P _ hnn => by
    rcases em (∃ n, P n) with h | h
    · exact h
    · exact absurd h hnn

/-- PolyMarkov gives ¬¬PEqNP → PEqNP when FactorsThrough is
    decidable at each grade. This is the middle stratum:
    stronger than ¬¬-stability (∅), weaker than full
    classification (Classical.choice). -/
theorem polymarkov_peqnp (M : GradedReflModel)
    (hdec : ∀ d, Decidable (FactorsThrough M M.selfApp d))
    (hpm : PolyMarkov) (hnn : ¬¬PEqNP M) : PEqNP M := by
  -- PEqNP M = ∃ d, FactorsThrough M M.selfApp d
  -- FactorsThrough is decidable at each d (hypothesis)
  -- PolyMarkov extracts the witness
  exact hpm (fun d => FactorsThrough M M.selfApp d)
    hdec (by intro h; exact hnn (fun ⟨d, hf⟩ => h ⟨d, hf⟩))

-- Note: for standardModel, FactorsThrough IS decidable at each grade
-- (the grade-bounded set is finite). A full proof would require Fintype
-- on {x | grade x ≤ d}. The decidability is genuine but we leave the
-- instance to the chain-specific instantiation.

-- ════════════════════════════════════════════════════════════
-- Section 13: The four strata — complete decomposition
-- ════════════════════════════════════════════════════════════

/-- THE FOUR AXIOM STRATA OF NAMING.

    Stratum 0 (∅): The tower exists. The regime question is
    irrefutable. The substrate is constructive. Computation.

    Stratum 1 (propext + Quot.sound): Concrete witnesses for
    all three regimes. Naming demonstrated.

    Stratum 2 (PolyMarkov): For decidable predicates,
    ¬¬PEqNP → PEqNP. The Markov bridge. Naming extracts
    witnesses from irrefutability when search is available.

    Stratum 3 (Classical.choice): Classification of arbitrary
    models. PEqNP M ∨ ¬PEqNP M for all M. Naming names itself.

    The two Classical.byContradiction uses in Section 11
    (not_factors_gives_overflow, peqnp_iff_not_unbounded) are
    Stratum 3 demonstrations: they show that extracting overflow
    witnesses from ¬FactorsThrough, and proving the full PEqNP ↔
    ¬SelfAppUnbounded equivalence, both require Classical.choice.
    This is by design — the axiom profile IS the content. -/
theorem four_strata :
    -- Stratum 0 (∅): tower + irrefutability
    (∀ (r : ReflexiveObject) (f : r.D → r.D), r.Y f = f (r.Y f)) ∧
    (∀ (M : GradedReflModel), ¬¬(PEqNP M ∨ ¬PEqNP M)) ∧
    -- Stratum 1 (propext + Quot.sound): witnesses
    (∃ M : GradedReflModel, ∀ x, M.selfApp x = x) ∧
    (∃ M : GradedReflModel, SelfAppUnbounded M) ∧
    -- Stratum 2 (PolyMarkov): EM → PolyMarkov
    ((∀ P : Prop, P ∨ ¬P) → PolyMarkov) :=
  ⟨fun r f => r.Y_fixed_point f,
   regime_dn,
   group_C_exists,
   separation_exists,
   polymarkov_from_em⟩

-- ════════════════════════════════════════════════════════════
-- Section 14: Computation Precedes Naming
-- ════════════════════════════════════════════════════════════

/-- Computation Precedes Naming.

    ONE field: the ¬¬ regime classification.

    M.roundtrip provides everything about computation — substrate,
    idempotence, full iso on image, directional implications, the
    entire return path. All derivable from the single GRM axiom.

    The ¬¬ is the single point where Classical.choice acts.
    Classical.byContradiction applied to `regime` gives the
    decided classification. Nothing else changes.

    Axiom profile of construction: ∅.
    Axiom profile of classical collapse: propext, Classical.choice,
    Quot.sound — and all three enter through one operation on one field. -/
structure ComputationPrecedesNaming (M : GradedReflModel) where
  /-- The regime is irrefutably one of three positions. -/
  regime : ¬¬((∀ x, M.selfApp x = x) ∨
              (PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∨
              ¬PEqNP M)

/-- Every GRM satisfies Computation Precedes Naming. Axiom: ∅. -/
def ComputationPrecedesNaming.of (M : GradedReflModel) :
    ComputationPrecedesNaming M :=
  ⟨classification_dn M⟩

-- Computation consequences (from M.roundtrip alone, no ¬¬ needed)

/-- selfApp is a retraction. From M.roundtrip in one rewrite. -/
theorem ComputationPrecedesNaming.substrate (M : GradedReflModel) :
    ∀ x, M.selfApp (M.selfApp x) = M.selfApp x :=
  fun x => by
    show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
    rw [M.roundtrip]

/-- Roundtrip holds on Im(selfApp): syntax recovers. -/
theorem ComputationPrecedesNaming.substrate_fwd (M : GradedReflModel) :
    ∀ x, M.fold (M.unfold (M.selfApp x)) = M.selfApp x :=
  fun x => M.roundtrip (M.selfApp x)

/-- Cotrip holds on Im(selfApp): semantics recovers.
    Full iso pointwise on the substrate. -/
theorem ComputationPrecedesNaming.substrate_bwd (M : GradedReflModel) :
    ∀ x, M.unfold (M.fold (M.selfApp x)) = M.selfApp x :=
  fun x => by
    show M.unfold (M.fold (M.unfold (M.fold x))) = M.unfold (M.fold x)
    rw [M.roundtrip]

-- Naming consequences (from definitions, unconditional)

/-- Identity implies bounded. -/
theorem ComputationPrecedesNaming.eta_bounded (M : GradedReflModel) :
    (∀ x, M.selfApp x = x) → PEqNP M :=
  fun h => ⟨0, fun x hx => by rw [h x]; exact hx⟩

/-- Unbounded implies not identity. -/
theorem ComputationPrecedesNaming.unbounded_not_eta (M : GradedReflModel) :
    ¬PEqNP M → ¬(∀ x, M.selfApp x = x) :=
  fun hnp heta => hnp ⟨0, fun x hx => by rw [heta x]; exact hx⟩

-- The ¬¬ monad

/-- Lift any consequence of the regime into ¬¬.
    This is the monadic map on the single ¬¬ field:
    if you can derive P from knowing the regime,
    you can derive ¬¬P from irrefutability alone. -/
theorem ComputationPrecedesNaming.lift {M : GradedReflModel}
    (h : ComputationPrecedesNaming M) {P : Prop}
    (f : ((∀ x, M.selfApp x = x) ∨
          (PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∨
          ¬PEqNP M) → P) :
    ¬¬P :=
  fun hp => h.regime (fun hc => hp (f hc))

/-- Classical collapse: Classical.byContradiction on the single ¬¬.
    This IS the formal content of what the classical formulation adds.
    One operation. One field. ¬¬ becomes decidable.
    Intentional Classical.byContradiction demonstration. -/
theorem ComputationPrecedesNaming.classical {M : GradedReflModel}
    (h : ComputationPrecedesNaming M) :
    (∀ x, M.selfApp x = x) ∨
    (PEqNP M ∧ ¬(∀ x, M.selfApp x = x)) ∨
    ¬PEqNP M :=
  Classical.byContradiction h.regime

-- ════════════════════════════════════════════════════════════
-- Section 15: Axiom audit
-- ════════════════════════════════════════════════════════════

-- Stratum 0 (∅)
#print axioms tower_complete
#print axioms regime_dn
#print axioms classification_dn
#print axioms substrate_constructive
#print axioms ComputationPrecedesNaming.of
#print axioms ComputationPrecedesNaming.substrate
#print axioms ComputationPrecedesNaming.substrate_fwd
#print axioms ComputationPrecedesNaming.substrate_bwd
#print axioms ComputationPrecedesNaming.eta_bounded
#print axioms ComputationPrecedesNaming.unbounded_not_eta
#print axioms ComputationPrecedesNaming.lift
-- Stratum 1 (propext + Quot.sound)
#print axioms unbounded_implies_not_peqnp
-- Stratum 2 (PolyMarkov)
#print axioms polymarkov_peqnp
-- Stratum 3 (Classical.choice) — BY DESIGN
#print axioms classification_classical
#print axioms not_factors_gives_overflow
#print axioms not_peqnp_implies_unbounded
#print axioms peqnp_iff_not_unbounded
#print axioms ComputationPrecedesNaming.classical
-- Full decomposition
#print axioms four_strata

end WTS.Generator
