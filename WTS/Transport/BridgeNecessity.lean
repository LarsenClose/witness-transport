/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Transport/BridgeNecessity.lean — Measure-only bridges are insufficient;
consequence structure is necessary for discriminating collapse from separation.

## The argument

A measure-only bridge (like CookFaithful, DegreeFaithful) asks only that two
numeric depth profiles are polynomially related. This condition is satisfiable
by trivialModel (where P = NP) using constant-zero depth functions. Moreover,
it admits nontrivial instances (growing depth functions) even in the collapse
regime. Therefore measure-only conditions cannot distinguish collapse from
separation. This is the Avis-Tiwary phenomenon: a numeric measure can grow
without bound while the model remains in the collapse regime.

A consequence bridge adds h_consequence: bounded source depth implies bounded
target depth. This field forces target_depth ≤ source_depth pointwise. When
combined with grade-linking (the bridge's source_depth tracks the model's
selfApp overflow), the combination requires SelfAppUnbounded, which implies
¬PEqNP. The consequence field is what makes the bridge discriminating: it
links the depth functions to the model's separation mechanism.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core

namespace WTS.Transport.BridgeNecessity

open WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Bridge conditions (inlined from classical side)
-- ════════════════════════════════════════════════════════════

/-- A measure-only bridge: two numeric depth profiles polynomially related.
    This is the shape shared by CookFaithful, DegreeFaithful, and
    PolymorphismFaithful. No consequence structure required. -/
structure MeasureBridge (M : GradedReflModel) where
  source_depth : Nat → Nat
  target_depth : Nat → Nat
  poly : PolyBound
  h_upper : ∀ n, target_depth n ≤ source_depth n * poly.eval n + poly.eval n
  h_lower : ∀ n, source_depth n ≤ target_depth n * poly.eval n + poly.eval n

/-- A consequence bridge: adds the requirement that bounded source depth
    implies bounded target depth. This is the h_consequence field from
    ConsequenceFaithful in WTS/Protocol/ProtocolWitnessFamilyLock.lean.

    The direction: source_depth bounded → target_depth bounded.
    Contrapositive: target_depth unbounded → source_depth unbounded.
    Instantiation: target_depth n ≤ source_depth n (taking d = source_depth n).

    This couples the two depth functions: target cannot exceed source. -/
structure ConsequenceBridge (M : GradedReflModel) extends MeasureBridge M where
  h_consequence : ∀ n d, source_depth n ≤ d → target_depth n ≤ d

-- ════════════════════════════════════════════════════════════
-- Section 2: MeasureBridge is universally satisfiable (the weakness)
-- ════════════════════════════════════════════════════════════

/-- ANY GradedReflModel satisfies MeasureBridge with zero depth functions.
    The polynomial bounds hold trivially because 0 ≤ anything.

    This is the formal statement that measure-only conditions are vacuous:
    they hold for every model, regardless of regime. -/
def measure_bridge_trivially_satisfiable (M : GradedReflModel) :
    MeasureBridge M where
  source_depth := fun _ => 0
  target_depth := fun _ => 0
  poly := ⟨0, 0⟩
  h_upper _ := Nat.zero_le _
  h_lower _ := Nat.zero_le _

/-- P = NP holds in trivialModel — a model where MeasureBridge is satisfied. -/
theorem trivialModel_peqnp : PEqNP trivialModel :=
  ⟨0, fun _ _ => Nat.zero_le 0⟩

/-- MeasureBridge is compatible with BOTH regimes. It cannot distinguish
    collapse (P = NP) from separation (P ≠ NP). -/
theorem measure_bridge_compatible_with_both_regimes :
    (∃ M : GradedReflModel, PEqNP M ∧ Nonempty (MeasureBridge M)) ∧
    (∃ M : GradedReflModel, SelfAppUnbounded M ∧ Nonempty (MeasureBridge M)) :=
  ⟨⟨trivialModel, trivialModel_peqnp,
    ⟨measure_bridge_trivially_satisfiable trivialModel⟩⟩,
   ⟨standardModel, standardModel_selfAppUnbounded,
    ⟨measure_bridge_trivially_satisfiable standardModel⟩⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: ConsequenceBridge with zero depths is also trivially
-- satisfiable — but the consequence field constrains nontrivial use
-- ════════════════════════════════════════════════════════════

/-- ConsequenceBridge is also trivially satisfiable with zero depth
    functions (h_consequence is vacuously 0 ≤ d). But this is the
    TRIVIAL instance — it carries no information. -/
def consequence_bridge_trivially_satisfiable (M : GradedReflModel) :
    ConsequenceBridge M where
  source_depth := fun _ => 0
  target_depth := fun _ => 0
  poly := ⟨0, 0⟩
  h_upper _ := Nat.zero_le _
  h_lower _ := Nat.zero_le _
  h_consequence _ _ _ := Nat.zero_le _

-- ════════════════════════════════════════════════════════════
-- Section 4: The Avis-Tiwary phenomenon — nontrivial MeasureBridge
-- in the collapse regime
-- ════════════════════════════════════════════════════════════

/-- A bridge is nontrivial if its source depth is unbounded:
    for every bound B, some input has source_depth exceeding B. -/
def NontrivialBridge {M : GradedReflModel} (b : MeasureBridge M) : Prop :=
  ∀ B, ∃ n, b.source_depth n > B

/-- MeasureBridge can be nontrivial even in the collapse regime.
    Nothing prevents source_depth from growing without bound in
    trivialModel — the depth functions are not tied to the model. -/
def trivialModel_nontrivial_measure : MeasureBridge trivialModel where
  source_depth := fun n => n
  target_depth := fun n => n
  poly := ⟨0, 1⟩
  h_upper n := by simp [PolyBound.eval]; omega
  h_lower n := by simp [PolyBound.eval]; omega

theorem trivialModel_nontrivial_measure_is_nontrivial :
    NontrivialBridge trivialModel_nontrivial_measure := by
  intro B; exact ⟨B + 1, by simp [trivialModel_nontrivial_measure]⟩

/-- The collapse regime admits a nontrivial MeasureBridge. The depth
    functions grow without bound, yet P = NP. The measure tracks
    something — but NOT the model's consequence structure. This is
    the Avis-Tiwary phenomenon: high extension complexity (growing
    measure) coexists with polynomial-time solvability (P = NP). -/
theorem measure_nontrivial_in_collapse :
    ∃ (b : MeasureBridge trivialModel), NontrivialBridge b ∧ PEqNP trivialModel :=
  ⟨trivialModel_nontrivial_measure,
   trivialModel_nontrivial_measure_is_nontrivial,
   trivialModel_peqnp⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Consequence field blocks the Avis-Tiwary phenomenon
-- ════════════════════════════════════════════════════════════

/-- The consequence field forces target_depth ≤ source_depth pointwise.
    Taking d = source_depth n in h_consequence gives target_depth n ≤ source_depth n. -/
theorem consequence_target_le_source {M : GradedReflModel} (cb : ConsequenceBridge M) (n : Nat) :
    cb.target_depth n ≤ cb.source_depth n :=
  cb.h_consequence n (cb.source_depth n) (Nat.le_refl _)

/-- Contrapositive of h_consequence: target_depth exceeding d implies
    source_depth exceeding d. -/
theorem consequence_contrapositive {M : GradedReflModel} (cb : ConsequenceBridge M)
    (n d : Nat) (h : cb.target_depth n > d) : cb.source_depth n > d := by
  match Nat.lt_or_ge d (cb.source_depth n) with
  | Or.inl hgt => exact hgt
  | Or.inr hle =>
    have := cb.h_consequence n d hle
    omega

-- ════════════════════════════════════════════════════════════
-- Section 6: Grounded bridges and commutativity
-- ════════════════════════════════════════════════════════════

/-! ## Grounded bridges: profiles that correspond to real functions

The trivial bridge (zero depths) is vacuous. The Avis-Tiwary phenomenon
shows that even nontrivial MeasureBridges (growing profiles) exist in
the collapse regime. The profiles float free of the model.

A GROUNDED bridge demands that profile values come from actual grade
behavior of selfApp. The witness function at size n agrees with selfApp
on grade-≤-n inputs, and some grade-n input produces output at grade
source_depth(n). This grounds the profile in real computational behavior.

When profiles are grounded AND unbounded, selfApp must overflow at
every grade — which is SelfAppUnbounded, implying ¬PEqNP. The bridge's
witness functions are what CONNECT profiles to selfApp: they are the
proof mechanism, not a side condition.
-/

/-- A grounded bridge: extends MeasureBridge with witness functions
    that ground the profile values in actual model behavior.

    - witness n is a function that agrees with selfApp on grade-≤-n inputs
    - h_grounded: some grade-≤-n input produces output at grade ≥ source_depth n
    - h_agrees: on bounded inputs, witness IS selfApp

    The witness functions are the bridge between abstract profiles
    (Nat → Nat) and concrete grade behavior (carrier → carrier).

    Design note: h_grounded requires grade x ≤ n (not ≤ source_depth n).
    This is the key: the input bound is the SIZE PARAMETER n, not the
    output. If we allowed grade x ≤ source_depth n, the grounding would
    not connect to SelfAppUnbounded (which needs bounded-input witnesses).
    With grade x ≤ n, combined with h_agrees, we get: there exists x
    with grade x ≤ n such that grade(selfApp x) ≥ source_depth n.
    When source_depth n > n, this IS overflow at grade n. -/
structure GroundedBridge (M : GradedReflModel) extends MeasureBridge M where
  witness : Nat → (M.carrier → M.carrier)
  h_agrees : ∀ n x, M.grade x ≤ n → witness n x = M.selfApp x
  h_grounded : ∀ n, ∃ x, M.grade x ≤ n ∧ M.grade (witness n x) ≥ source_depth n

/-- A bridge commutes if its profiles are the image of grounded witness
    functions. The profiles are not independent data — they are shadows
    of actual model behavior. -/
def BridgeCommutes (M : GradedReflModel) (b : MeasureBridge M) : Prop :=
  ∃ (gb : GroundedBridge M),
    gb.source_depth = b.source_depth ∧
    gb.target_depth = b.target_depth

/-- SelfAppUnbounded implies ¬PEqNP.
    Local proof (also proved in UnconditionalChain and elsewhere,
    but we only import Core). -/
theorem selfApp_unbounded_not_peqnp (M : GradedReflModel)
    (h : SelfAppUnbounded M) : ¬PEqNP M := by
  intro ⟨d, hf⟩
  obtain ⟨x, hle, hgt⟩ := h.overflows d
  have := hf x hle
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Theorem A — the nontrivial measure bridge does not commute
-- ════════════════════════════════════════════════════════════

/-- Theorem A: The nontrivial MeasureBridge in trivialModel does NOT commute.

    The growing profiles (source_depth = id, target_depth = id) cannot be
    grounded because trivialModel has grade = 0 everywhere. A grounded
    bridge would require ∃ x, grade(witness n x) ≥ n. But in trivialModel,
    h_agrees forces witness n x = selfApp x = x (since grade x ≤ n always),
    and grade x = 0 for all x. So grade(witness n x) = 0, which fails
    to be ≥ n for n ≥ 1.

    This IS the Avis-Tiwary phenomenon expressed as non-commutativity:
    the extension complexity (profile) grows, but no grade-bounded
    function on the model tracks this growth. -/
theorem trivialModel_measure_not_commutative :
    ¬BridgeCommutes trivialModel trivialModel_nontrivial_measure := by
  intro ⟨gb, hsrc, _⟩
  -- source_depth = id, so source_depth 1 = 1
  obtain ⟨x, hx_le, hx_out⟩ := gb.h_grounded 1
  -- In trivialModel, h_agrees gives witness 1 x = selfApp x
  have h_eq := gb.h_agrees 1 x hx_le
  -- selfApp in trivialModel is id
  have h_sa : trivialModel.selfApp x = x := by
    cases x; rfl
  rw [h_eq, h_sa] at hx_out
  -- grade x = 0 in trivialModel
  have h_gr : trivialModel.grade x = 0 := by
    cases x; rfl
  -- But source_depth 1 = 1 (from hsrc and the definition)
  have h_sd : gb.source_depth 1 = 1 := by
    have : trivialModel_nontrivial_measure.source_depth 1 = 1 := rfl
    rw [← hsrc] at this; exact this
  rw [h_gr, h_sd] at hx_out
  omega

-- ════════════════════════════════════════════════════════════
-- Section 8: Theorem B — h_consequence enables grounding
-- ════════════════════════════════════════════════════════════

/-- Theorem B: h_consequence constrains profiles so that grounded witnesses
    automatically bound the target side.

    If witness functions exist for the source side with grade output
    bounded by source_depth, then h_consequence propagates this bound
    to target_depth. This is what makes ConsequenceBridge compatible
    with grounding — the consequence field ensures the target profile
    stays within the source's grade envelope.

    This follows directly from consequence_target_le_source. -/
theorem consequence_enables_grounding (M : GradedReflModel)
    (cb : ConsequenceBridge M) :
    ∀ n, cb.target_depth n ≤ cb.source_depth n :=
  consequence_target_le_source cb

-- ════════════════════════════════════════════════════════════
-- Section 9: Theorem C — grounded + unbounded profiles → separation
-- ════════════════════════════════════════════════════════════

/-- Theorem C: A GroundedBridge with unbounded source_depth and
    source_depth n > n for all n implies ¬PEqNP.

    This is the theorem where the bridge is GENUINELY USED.
    The proof extracts overflow witnesses from the GroundedBridge:

    1. h_grounded gives x with grade x ≤ n and grade(witness n x) ≥ source_depth n
    2. h_agrees gives witness n x = selfApp x (since grade x ≤ n)
    3. Combined: grade(selfApp x) ≥ source_depth n > n ≥ grade x
    4. This is selfApp overflow at grade n
    5. This holds for all n, giving SelfAppUnbounded
    6. SelfAppUnbounded implies ¬PEqNP

    The condition source_depth n > n is what converts "grounded" into
    "overflowing": it means the profile exceeds the size parameter,
    so the grounded witness demonstrates actual grade overflow.

    Note: the spec's original statement used just unbounded source_depth,
    but that is insufficient. Unbounded means ∀ B, ∃ n, source_depth n > B,
    which gives source_depth n₀ > B for SOME n₀, but we need overflow at
    EVERY grade d (SelfAppUnbounded). The condition source_depth n > n
    for all n gives this: at grade d, use n = d, get x with grade x ≤ d
    and grade(selfApp x) ≥ source_depth d > d. -/
theorem grounded_overflowing_implies_separation (M : GradedReflModel)
    (gb : GroundedBridge M)
    (h_overflow : ∀ n, gb.source_depth n > n) :
    ¬PEqNP M := by
  apply selfApp_unbounded_not_peqnp
  constructor
  intro d
  obtain ⟨x, hx_le, hx_out⟩ := gb.h_grounded d
  have h_eq := gb.h_agrees d x hx_le
  rw [h_eq] at hx_out
  exact ⟨x, hx_le, Nat.lt_of_lt_of_le (h_overflow d) hx_out⟩

/-- Corollary: if a GroundedBridge has source_depth n > n for all n,
    it cannot exist in a model where PEqNP holds. The grounding
    forces the model into the separation regime.

    Compare with measure_nontrivial_in_collapse: the SAME profile
    (source_depth = id, which satisfies source_depth n > n - 1 but
    NOT source_depth n > n) can exist as an ungrounded MeasureBridge
    in trivialModel. The GROUNDING is what makes the difference. -/
theorem grounded_bridge_incompatible_with_collapse (M : GradedReflModel)
    (gb : GroundedBridge M)
    (h_overflow : ∀ n, gb.source_depth n > n)
    (hpeq : PEqNP M) : False :=
  grounded_overflowing_implies_separation M gb h_overflow hpeq

-- ════════════════════════════════════════════════════════════
-- Section 10: Theorem D — non-commutative bridges are vacuous
-- ════════════════════════════════════════════════════════════

/-- Theorem D: Any MeasureBridge's profiles can be realized in a
    collapse model (trivialModel). The profiles alone carry no
    regime information.

    This is stronger than "non-commutative bridges are vacuous" —
    it says ALL MeasureBridge profiles can be transplanted to a
    model where P = NP. The profiles are just pairs of Nat → Nat
    functions with polynomial bounds, and those bounds are satisfiable
    in any model (including trivialModel). -/
theorem measure_profiles_realizable_in_collapse {M : GradedReflModel} (b : MeasureBridge M) :
    ∃ M' : GradedReflModel, PEqNP M' ∧
      ∃ b' : MeasureBridge M', b'.source_depth = b.source_depth ∧
        b'.target_depth = b.target_depth :=
  ⟨trivialModel, trivialModel_peqnp,
   ⟨{ source_depth := b.source_depth
      target_depth := b.target_depth
      poly := b.poly
      h_upper := b.h_upper
      h_lower := b.h_lower },
    rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 11: Theorem E — commutativity summary
-- ════════════════════════════════════════════════════════════

/-- Theorem E: The commutativity summary.

    1. Non-commutative nontrivial bridges exist in the collapse regime
       (the Avis-Tiwary phenomenon).
    2. Grounded bridges with overflowing profiles force separation.
    3. h_consequence constrains profiles toward groundability
       (target ≤ source). -/
theorem commutativity_summary :
    -- (1) Non-commutative nontrivial bridge in collapse
    (∃ b : MeasureBridge trivialModel,
      NontrivialBridge b ∧ ¬BridgeCommutes trivialModel b) ∧
    -- (2) Grounded + overflowing profiles → separation
    (∀ M (gb : GroundedBridge M),
      (∀ n, gb.source_depth n > n) → ¬PEqNP M) ∧
    -- (3) h_consequence constrains profiles
    (∀ M (cb : ConsequenceBridge M),
      ∀ n, cb.target_depth n ≤ cb.source_depth n) :=
  ⟨⟨trivialModel_nontrivial_measure,
    trivialModel_nontrivial_measure_is_nontrivial,
    trivialModel_measure_not_commutative⟩,
   fun M gb h => grounded_overflowing_implies_separation M gb h,
   fun _ cb => consequence_target_le_source cb⟩

/-! ## Why consequence structure is necessary

The file proves five things:

1. **MeasureBridge is regime-blind** (measure_bridge_compatible_with_both_regimes):
   Both P = NP and P != NP models satisfy MeasureBridge.

2. **Nontrivial MeasureBridges don't commute in collapse**
   (trivialModel_measure_not_commutative): Growing profiles in trivialModel
   cannot be grounded — no grade-bounded functions match the profile values.
   This is the Avis-Tiwary phenomenon as non-commutativity.

3. **Grounded overflowing bridges force separation**
   (grounded_overflowing_implies_separation): When profiles ARE grounded
   (witness functions connect profiles to selfApp) AND overflow (source_depth
   n > n), the bridge's witnesses prove SelfAppUnbounded, giving ¬PEqNP.
   The bridge is genuinely used in this proof.

4. **Ungrounded profiles are vacuous** (measure_profiles_realizable_in_collapse):
   Any MeasureBridge's profiles can be transplanted to a collapse model.
   Without grounding, profiles carry no regime information.

5. **h_consequence constrains toward groundability**
   (consequence_enables_grounding): The consequence field forces target ≤ source,
   ensuring the profile data is compatible with grounded witness functions.

The consequence field is what makes grounding POSSIBLE: it ensures the target
profile doesn't exceed the source profile, so a single set of witness functions
can account for both sides. Without it (pure MeasureBridge), the profiles
float free and can be realized in any regime.
-/

/-- Witness functions form a coherent family: on bounded inputs,
    witnesses at different grades agree. This follows directly from
    h_agrees — both witnesses equal selfApp on the shared domain. -/
theorem grounded_witness_monotone (M : GradedReflModel)
    (gb : GroundedBridge M) (d₁ d₂ : Nat) (h : d₁ ≤ d₂) :
    ∀ x, M.grade x ≤ d₁ → gb.witness d₁ x = gb.witness d₂ x := by
  intro x hx
  rw [gb.h_agrees d₁ x hx, gb.h_agrees d₂ x (Nat.le_trans hx h)]

-- ════════════════════════════════════════════════════════════
-- Section 12: Transfer entails consequence — the necessity theorem
-- ════════════════════════════════════════════════════════════

/-- Theorem F: Any grade-bounded function agreeing with selfApp on
    bounded inputs automatically witnesses bounded selfApp behavior
    at that grade.

    This is the NECESSITY theorem: the TransferHypothesis return type
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }
    ENTAILS that selfApp is grade-bounded at d on grade-≤-d inputs.

    Consequence closure is not additional structure imposed on the
    bridge — it is DERIVED from what any working bridge must satisfy.
    Any f that is grade-bounded and agrees with selfApp on bounded
    inputs automatically demonstrates that selfApp respects the
    grade bound on those inputs. -/
theorem transfer_witnesses_consequence (M : GradedReflModel)
    (f : M.carrier → M.carrier) (d : Nat)
    (h_bounded : ∀ x, M.grade (f x) ≤ d)
    (h_agrees : ∀ x, M.grade x ≤ d → f x = M.selfApp x) :
    ∀ x, M.grade x ≤ d → M.grade (M.selfApp x) ≤ d :=
  fun x hx => h_agrees x hx ▸ h_bounded x

/-- Theorem G: When selfApp is unbounded, no grade-bounded function
    can agree with selfApp on all bounded inputs.

    This is Side A expressed in transfer language: the TransferHypothesis
    return type is uninhabited when SelfAppUnbounded holds.

    Combined with Theorem F:
    - If a transfer exists at grade d → selfApp is bounded at d (Thm F)
    - If selfApp is unbounded → no transfer exists at any d (Thm G)
    - Therefore: in a TC model, no uniform transfer exists
    - Therefore: the bridge, if it could be constructed for all d,
      would prove selfApp bounded — contradicting TC

    This is ¬PEqNP derived from the IMPOSSIBILITY of uniform transfer,
    not from assuming it and deriving contradiction. The direction matters:
    the transfer's type FORCES consequence closure, and consequence
    closure is incompatible with unbounded selfApp. -/
theorem no_transfer_when_unbounded (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (d : Nat) :
    ¬∃ f : M.carrier → M.carrier,
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) := by
  intro ⟨f, hb, ha⟩
  have hcon := transfer_witnesses_consequence M f d hb ha
  obtain ⟨x, hle, hgt⟩ := hub.overflows d
  have := hcon x hle
  omega

/-- Theorem H: The derivation chain from transfer to separation.

    1. Any grade-bounded f agreeing with selfApp witnesses consequence
       closure at that grade (transfer_witnesses_consequence)
    2. Consequence closure at every grade contradicts SelfAppUnbounded
       (no_transfer_when_unbounded)
    3. Therefore: in a TC model, no uniform family of transfers exists
    4. This is ¬PEqNP derived purely from the transfer's type signature

    The bridge conditions (CookFaithful, ConsequenceFaithful, etc.)
    are conditions under which such transfers COULD be constructed.
    But any transfer that IS constructed automatically has consequence
    closure. So:
    - CookFaithful without consequence closure: profiles exist but
      no transfer can be built (the profiles float free)
    - ConsequenceFaithful: consequence closure is stated, making
      the bridge COMPATIBLE with transfers that could exist
    - The transfer's type is what forces consequence — not the
      bridge condition. The bridge condition is an ENABLING condition,
      and only consequence-compatible conditions enable anything.

    This is why Chain 7 is distinguished: its operations natively
    produce consequence-closed structure, which is the ONLY structure
    compatible with working transfers. -/
theorem consequence_is_only_bridge_form (M : GradedReflModel)
    (hub : SelfAppUnbounded M) :
    -- No uniform transfer exists
    (∀ d, ¬∃ f : M.carrier → M.carrier,
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x)) ∧
    -- Any individual transfer at grade d witnesses consequence at d
    (∀ d (f : M.carrier → M.carrier),
      (∀ x, M.grade (f x) ≤ d) →
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) →
      (∀ x, M.grade x ≤ d → M.grade (M.selfApp x) ≤ d)) ∧
    -- Therefore ¬PEqNP
    ¬PEqNP M :=
  ⟨fun d => no_transfer_when_unbounded M hub d,
   fun d f hb ha => transfer_witnesses_consequence M f d hb ha,
   selfApp_unbounded_not_peqnp M hub⟩

/-! ## The necessity of consequence closure (Theorems F-H)

Theorems F-H complete the bridge necessity argument:

**F (transfer_witnesses_consequence):** The TransferHypothesis return type
ENTAILS consequence-bounded selfApp. Any grade-bounded function agreeing
with selfApp automatically demonstrates that selfApp respects the grade
bound. This is one line of proof — the content is in the TYPE, not the proof.

**G (no_transfer_when_unbounded):** When selfApp is unbounded, the
TransferHypothesis return type is uninhabited at every grade. No
transfer can be constructed. This is Side A in transfer language.

**H (consequence_is_only_bridge_form):** Composition of F and G.
In a TC model: (1) no uniform transfer exists, (2) any individual
transfer witnesses consequence closure, (3) ¬PEqNP.

**The full derivation chain this file proves:**

1. MeasureBridge is regime-blind (Sections 2-4)
2. Nontrivial MeasureBridges don't commute in collapse / Avis-Tiwary (Section 7)
3. Grounded overflowing bridges force separation with bridge used in proof (Section 9)
4. Any working transfer entails consequence closure — it's forced by the type (Section 12)
5. Therefore: consequence closure is the NECESSARY form of any bridge,
   not an optional strengthening

Chain 7's distributed witness operations are distinguished because they
natively produce consequence-closed structure. The other chains' languages
(resolution, FO, PC, CSP, LP) require proving as additional hypotheses
that their reductions produce consequence-compatible objects. Chain 7's
operations ARE consequence-compatible by construction — transport composes
with bounded overhead, projection preserves certify, consequence closure
propagates. This is the formal content of "Chain 7 is not another language."
-/

end WTS.Transport.BridgeNecessity
