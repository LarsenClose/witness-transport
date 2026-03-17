/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/ChainInstantiation.lean — Group B chain
instantiations of the CanonicalMirror interface.

Each Group B chain (2, 3, 5) has already proved four concrete fields:
  - red : A -> A (the canonicalization operation)
  - red_idempotent : red . red = red
  - red_grade_le : grade(red(x)) <= grade(x)
  - selfApp_eq_red : selfApp = red (when M exists)

These four fields are exactly the input to canonicalMirror_of_modelData
(PartialMirrorAdequacy.lean), which produces a CanonicalMirror from which
all bridge properties follow.

This file demonstrates the instantiation pattern with concrete Nat-based
witnesses that mirror the structure of each chain. The actual chain
instantiations would use the domain-specific types (MvPolynomial,
ProtocolTree, FOFormula), but those live in classical-constraints.
Here we provide the PATTERN using Nat operations that capture the
essential structure, plus the abstract instantiation theorem.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Tower.CarrierEngineering.PartialMirrorAdequacy

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Abstract instantiation — any ModelData yields a
--            CanonicalMirror with all bridge properties
-- ════════════════════════════════════════════════════════════

/-- The universal instantiation theorem: ANY idempotent grade-non-increasing
    endomorphism on any type yields a CanonicalMirror, and that CanonicalMirror
    provides the complete bridge package.

    This is the theorem each chain cites. The chain provides:
    - A type (its carrier)
    - A red operation (its canonicalization)
    - A grade function
    - Proofs of idempotence and grade-non-increasing

    The theorem returns the full bridge package: idempotence, grade bounds,
    identity on the canonical subdomain, FactorsThrough at every grade,
    and GroupBData on the ambient carrier. -/
theorem universal_chain_instantiation
    (A : Type) (red : A → A) (grade : A → Nat)
    (h_idem : ∀ x, red (red x) = red x)
    (h_grade_le : ∀ x, grade (red x) ≤ grade x) :
    let CM := canonicalMirror_of_modelData A red grade h_idem h_grade_le
    -- (1) Canonicalizer = red
    (∀ a, CM.canonicalize a = red a) ∧
    -- (2) Idempotent
    (∀ a, red (red a) = red a) ∧
    -- (3) Grade-non-increasing
    (∀ a, grade (red a) ≤ grade a) ∧
    -- (4) FactorsThrough every grade
    (∀ d a, grade a ≤ d → grade (red a) ≤ d) ∧
    -- (5) Grade stability on the image: red preserves grade on canonical elements.
    --     Chain 3 has grade equality on ALL elements; universally we get it on the image.
    (∀ a, grade (red (red a)) = grade (red a)) ∧
    -- (6) No overflow possible
    ((∀ d, ∃ a, grade a ≤ d ∧ grade (red a) > d) → False) :=
  ⟨fun _ => rfl,
   h_idem,
   h_grade_le,
   fun d a hle => Nat.le_trans (h_grade_le a) hle,
   fun a => congrArg grade (h_idem a),
   fun h_overflows => by
     obtain ⟨a, hle, hgt⟩ := h_overflows 0
     have := h_grade_le a; omega⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Chain 5 pattern — multilinear reduction
-- ════════════════════════════════════════════════════════════

/-- Chain 5 pattern: exponent capping as a Nat endomorphism.
    The concrete operation: cap(x) = min(x, 1). This mirrors
    multilinearReduce's capExp at the single-variable level. -/
def chain5_red_pattern (x : Nat) : Nat := min x 1

theorem chain5_red_idempotent : ∀ x, chain5_red_pattern (chain5_red_pattern x) = chain5_red_pattern x := by
  intro x; simp [chain5_red_pattern]

theorem chain5_red_grade_le : ∀ x, chain5_red_pattern x ≤ x := by
  intro x; simp [chain5_red_pattern]; exact Nat.min_le_left x 1

/-- Chain 5 CanonicalMirror instantiation. -/
def chain5_canonical_mirror : CanonicalMirror :=
  canonicalMirror_of_modelData Nat chain5_red_pattern id
    chain5_red_idempotent chain5_red_grade_le

/-- The Chain 5 bridge: all properties hold. -/
theorem chain5_bridge_properties :
    let CM := chain5_canonical_mirror
    (∀ a, CM.canonicalize a = chain5_red_pattern a) ∧
    (∀ d a, a ≤ d → chain5_red_pattern a ≤ d) ∧
    ((∀ d, ∃ a, a ≤ d ∧ chain5_red_pattern a > d) → False) :=
  ⟨fun _ => rfl,
   fun d a hle => Nat.le_trans (chain5_red_grade_le a) hle,
   fun h => by obtain ⟨a, hle, hgt⟩ := h 0; have := chain5_red_grade_le a; omega⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Chain 2 pattern — protocol flattening
-- ════════════════════════════════════════════════════════════

/-- Chain 2 pattern: round down to even as a Nat endomorphism.
    The concrete operation: flatten(x) = 2 * (x / 2). This mirrors
    proto_to_dt . dt_to_proto: a two-player protocol is flattened
    to a single-player protocol (decision tree) and re-embedded. -/
def chain2_red_pattern (x : Nat) : Nat := 2 * (x / 2)

theorem chain2_red_idempotent : ∀ x, chain2_red_pattern (chain2_red_pattern x) = chain2_red_pattern x := by
  intro x; unfold chain2_red_pattern; omega

theorem chain2_red_grade_le : ∀ x, chain2_red_pattern x ≤ x := by
  intro x; simp [chain2_red_pattern]; omega

/-- Chain 2 CanonicalMirror instantiation. -/
def chain2_canonical_mirror : CanonicalMirror :=
  canonicalMirror_of_modelData Nat chain2_red_pattern id
    chain2_red_idempotent chain2_red_grade_le

/-- The Chain 2 bridge: all properties hold. -/
theorem chain2_bridge_properties :
    let CM := chain2_canonical_mirror
    (∀ a, CM.canonicalize a = chain2_red_pattern a) ∧
    (∀ d a, a ≤ d → chain2_red_pattern a ≤ d) ∧
    ((∀ d, ∃ a, a ≤ d ∧ chain2_red_pattern a > d) → False) :=
  ⟨fun _ => rfl,
   fun d a hle => Nat.le_trans (chain2_red_grade_le a) hle,
   fun h => by obtain ⟨a, hle, hgt⟩ := h 0; have := chain2_red_grade_le a; omega⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Chain 3 pattern — depth-preserving canonicalization
-- ════════════════════════════════════════════════════════════

/-- Chain 3 grade function: x / 2.

    WHY x / 2: Chain 3 (foCanonical, NNF conversion on first-order formulas)
    has a distinctive property among Group B chains: it preserves grade
    EXACTLY. Quantifier depth is unchanged by NNF conversion, even though
    the formula's structure changes (negations pushed to atoms, De Morgan
    applied, etc.).

    On (Nat, grade = id), no nontrivial idempotent can preserve grade:
    if grade(red(x)) = red(x) = x for all x, then red = id. The fix
    is to use a non-injective grade function — multiple carrier elements
    at the same grade level — modeling the fact that multiple formulas
    can share the same quantifier depth.

    With grade = x / 2, consecutive pairs (2k, 2k+1) share grade k.
    The reduction red(x) = 2*(x/2) maps each pair to its even member,
    changing structure while preserving grade: (2*(x/2))/2 = x/2.

    Note: this is the same REDUCTION as Chain 2, but with a different
    grade function. Chain 2 uses grade = id, so red strictly decreases
    grade on odd inputs (flattening reduces depth). Chain 3 uses
    grade = x/2, so red preserves grade (NNF preserves depth). The
    grade function determines the chain's character, not the reduction
    alone. -/
def chain3_grade (x : Nat) : Nat := x / 2

/-- Chain 3 pattern: round to even as a Nat endomorphism.
    red(x) = 2 * (x / 2). This mirrors foCanonical: a nontrivial
    idempotent that changes structure while preserving grade exactly.

    The carrier elements are natural numbers. The "canonical" elements
    are the even numbers (analogous to NNF formulas). The odd numbers
    are the "non-canonical" elements (analogous to formulas with
    non-atomic negation). The reduction maps each number to the
    nearest even number below it (analogous to pushing negation inward).

    Key properties capturing Chain 3's character:
    - Idempotent: red(red(x)) = red(x)                    [NNF of NNF is NNF]
    - Grade-preserving: grade(red(x)) = grade(x)          [depth unchanged]
    - Nontrivial: red(1) = 0 ≠ 1                          [non-NNF formulas exist]
    - Grade-non-increasing: red(x) ≤ x                    [for CanonicalMirror] -/
def chain3_red_pattern (x : Nat) : Nat := 2 * (x / 2)

theorem chain3_red_idempotent : ∀ x, chain3_red_pattern (chain3_red_pattern x) = chain3_red_pattern x := by
  intro x; unfold chain3_red_pattern; omega

theorem chain3_red_grade_le : ∀ x, chain3_grade (chain3_red_pattern x) ≤ chain3_grade x := by
  intro x; simp [chain3_grade, chain3_red_pattern]

/-- Chain 3 carrier-level non-increasing: red(x) ≤ x. This holds because
    2*(x/2) ≤ x for all Nat. Used by ProjectionalAtlas where grade = id. -/
theorem chain3_red_carrier_le : ∀ x, chain3_red_pattern x ≤ x := by
  intro x; simp [chain3_red_pattern]; omega

/-- Chain 3 grade EQUALITY: the defining property that distinguishes
    Chain 3 from Chains 2 and 5. NNF preserves quantifier depth exactly. -/
theorem chain3_red_grade_eq : ∀ x, chain3_grade (chain3_red_pattern x) = chain3_grade x := by
  intro x; simp [chain3_grade, chain3_red_pattern]

/-- Chain 3 is nontrivial: odd inputs are not fixed points. -/
theorem chain3_nontrivial : ∃ x, chain3_red_pattern x ≠ x := by
  exact ⟨1, by simp [chain3_red_pattern]⟩

/-- Chain 3 CanonicalMirror instantiation. Uses chain3_grade (= x/2)
    rather than id, modeling the non-injective depth function. -/
def chain3_canonical_mirror : CanonicalMirror :=
  canonicalMirror_of_modelData Nat chain3_red_pattern chain3_grade
    chain3_red_idempotent chain3_red_grade_le

/-- The Chain 3 bridge: all properties hold, including grade preservation. -/
theorem chain3_bridge_properties :
    let CM := chain3_canonical_mirror
    -- Canonicalize = red
    (∀ a, CM.canonicalize a = chain3_red_pattern a) ∧
    -- FactorsThrough every grade
    (∀ d a, chain3_grade a ≤ d → chain3_grade (chain3_red_pattern a) ≤ d) ∧
    -- No overflow possible
    ((∀ d, ∃ a, chain3_grade a ≤ d ∧ chain3_grade (chain3_red_pattern a) > d) → False) ∧
    -- Grade EQUALITY (the Chain 3 distinguishing property)
    (∀ a, chain3_grade (chain3_red_pattern a) = chain3_grade a) ∧
    -- Nontriviality
    (∃ a, chain3_red_pattern a ≠ a) :=
  ⟨fun _ => rfl,
   fun d a hle => Nat.le_trans (chain3_red_grade_le a) hle,
   fun h => by obtain ⟨a, hle, hgt⟩ := h 0; have := chain3_red_grade_le a; omega,
   chain3_red_grade_eq,
   chain3_nontrivial⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: The pattern — all three are one theorem
-- ════════════════════════════════════════════════════════════

/-- All three Group B chains instantiate the same pattern: an idempotent
    grade-non-increasing endomorphism yields a CanonicalMirror that
    provides the full bridge package. The chain-specific content is
    ONLY in defining the endomorphism and proving the two properties.

    Cross-chain table:
    | Chain | red                         | grade        | A              |
    |-------|----------------------------|--------------|----------------|
    | 5     | multilinearReduce          | totalDegree  | MvPolynomial   |
    | 2     | dt_to_proto . proto_to_dt  | depth        | ProtocolTree   |
    | 3     | foCanonical                | quant. rank  | FOFormula      |

    Each row provides (red, grade, A, h_idem, h_grade_le) to
    universal_chain_instantiation and gets the full bridge for free. -/
theorem three_chains_one_pattern :
    -- Chain 5 pattern: canonicalize = min(x, 1)
    (∀ a : Nat, chain5_canonical_mirror.canonicalize a = chain5_red_pattern a) ∧
    -- Chain 2 pattern: canonicalize = 2*(x/2)
    (∀ a : Nat, chain2_canonical_mirror.canonicalize a = chain2_red_pattern a) ∧
    -- Chain 3 pattern: canonicalize = 2*(x/2), grade = x/2
    (∀ a : Nat, chain3_canonical_mirror.canonicalize a = chain3_red_pattern a) :=
  ⟨fun _ => rfl,
   fun _ => rfl,
   fun _ => rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms universal_chain_instantiation
#print axioms chain5_red_idempotent
#print axioms chain5_red_grade_le
#print axioms chain5_canonical_mirror
#print axioms chain5_bridge_properties
#print axioms chain2_red_idempotent
#print axioms chain2_red_grade_le
#print axioms chain2_canonical_mirror
#print axioms chain2_bridge_properties
#print axioms chain3_red_idempotent
#print axioms chain3_red_grade_le
#print axioms chain3_red_carrier_le
#print axioms chain3_red_grade_eq
#print axioms chain3_nontrivial
#print axioms chain3_canonical_mirror
#print axioms chain3_bridge_properties
#print axioms three_chains_one_pattern

end WTS
