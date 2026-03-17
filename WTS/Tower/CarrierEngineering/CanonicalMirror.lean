/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/CanonicalMirror.lean — The weaker mirror
structure for Group B carrier engineering.

ProjectionObstruction.lean proves that a nontrivial idempotent
grade-non-increasing canonicalizer cannot be the selfApp of a
full GradedReflModel without forcing PEqNP. The CanonicalMirror
structure is the RIGHT weakening: instead of demanding a full GRM
on the ambient carrier, it exposes the canonicalizer's reflector
structure directly.

The key design choice: the codomain of the reduction is the
canonical subdomain C, not the ambient carrier A. This makes the
reflective structure explicit rather than disguising it as an
endomorphism.

Components:
  - A : Type (ambient carrier -- all objects, including non-canonical)
  - C : Type (canonical subdomain -- fixed points of the normalizer)
  - incl : C -> A (inclusion: canonical objects embed into the ambient)
  - normalize : A -> C (reduction: projects ambient objects to canonical form)
  - sect : normalize . incl = id on C (section: normalizing a canonical
    object recovers it)
  - grade_A : A -> Nat (ambient grade)
  - grade_C : C -> Nat (canonical grade)
  - grade_compat : grade_A (incl c) = grade_C c (inclusion preserves grade)
  - normalize_grade_le : grade_C (normalize a) <= grade_A a (normalization
    is grade-non-increasing)

The induced endomorphism on A is: incl . normalize : A -> A.
This is the canonicalizer. It is idempotent (by sect) and
grade-non-increasing (by normalize_grade_le + grade_compat).

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.Core
import WTS.Tower.CarrierEngineering.ProjectionObstruction

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The CanonicalMirror structure
-- ════════════════════════════════════════════════════════════

/-- A canonical mirror: the reflective structure underlying every
    Group B chain's carrier engineering.

    Instead of a full GradedReflModel (which requires a roundtrip
    on the full carrier and forces the projection obstruction), this
    structure exposes the section-retraction pair between the ambient
    carrier A and the canonical subdomain C.

    The incl/normalize pair forms a retraction: normalize is left
    inverse of incl. The induced endomorphism incl . normalize on A
    is the canonicalizer (idempotent, grade-non-increasing).

    Chains 2/3/5 each instantiate this with:
    - Chain 5: A = MvPolynomial, C = multilinear polynomials,
      normalize = multilinearReduce, incl = subtype inclusion
    - Chain 2: A = ProtocolTree, C = DecisionTree (single-player protocols),
      normalize = proto_to_dt, incl = dt_to_proto
    - Chain 3: A = FOFormula, C = NNF formulas,
      normalize = foCanonical, incl = subtype inclusion -/
structure CanonicalMirror where
  /-- The ambient carrier (all objects). -/
  A : Type
  /-- The canonical subdomain (fixed points of canonicalization). -/
  C : Type
  /-- Inclusion: canonical objects embed into the ambient carrier. -/
  incl : C → A
  /-- Normalization: projects ambient objects to canonical form. -/
  normalize : A → C
  /-- Section: normalizing an included canonical object recovers it.
      This makes (incl, normalize) a section-retraction pair. -/
  sect : ∀ c, normalize (incl c) = c
  /-- Grade on the ambient carrier. -/
  grade_A : A → Nat
  /-- Grade on the canonical subdomain. -/
  grade_C : C → Nat
  /-- Inclusion preserves grade. -/
  grade_compat : ∀ c, grade_A (incl c) = grade_C c
  /-- Normalization is grade-non-increasing. -/
  normalize_grade_le : ∀ a, grade_C (normalize a) ≤ grade_A a

-- ════════════════════════════════════════════════════════════
-- Section 2: Derived properties
-- ════════════════════════════════════════════════════════════

/-- The induced endomorphism on A: the canonicalizer.
    This is incl . normalize : A -> A. -/
def CanonicalMirror.canonicalize (CM : CanonicalMirror) (a : CM.A) : CM.A :=
  CM.incl (CM.normalize a)

/-- The canonicalizer is idempotent.
    canonicalize(canonicalize(a)) = incl(normalize(incl(normalize(a))))
    = incl(normalize(a)) by sect. -/
theorem CanonicalMirror.canonicalize_idempotent (CM : CanonicalMirror) :
    ∀ a, CM.canonicalize (CM.canonicalize a) = CM.canonicalize a := by
  intro a
  show CM.incl (CM.normalize (CM.incl (CM.normalize a))) =
       CM.incl (CM.normalize a)
  rw [CM.sect]

/-- The canonicalizer is grade-non-increasing on A.
    grade_A(canonicalize(a)) = grade_A(incl(normalize(a)))
    = grade_C(normalize(a)) <= grade_A(a). -/
theorem CanonicalMirror.canonicalize_grade_le (CM : CanonicalMirror) :
    ∀ a, CM.grade_A (CM.canonicalize a) ≤ CM.grade_A a := by
  intro a
  show CM.grade_A (CM.incl (CM.normalize a)) ≤ CM.grade_A a
  rw [CM.grade_compat]
  exact CM.normalize_grade_le a

/-- The canonicalizer applied to an included element is the element itself.
    canonicalize(incl(c)) = incl(normalize(incl(c))) = incl(c) by sect. -/
theorem CanonicalMirror.canonicalize_incl (CM : CanonicalMirror) :
    ∀ c, CM.canonicalize (CM.incl c) = CM.incl c := by
  intro c
  show CM.incl (CM.normalize (CM.incl c)) = CM.incl c
  rw [CM.sect]

/-- incl is injective when normalize is a retraction (left inverse).
    If incl(c1) = incl(c2), then c1 = normalize(incl(c1)) = normalize(incl(c2)) = c2. -/
theorem CanonicalMirror.incl_injective (CM : CanonicalMirror) :
    Function.Injective CM.incl := by
  intro c1 c2 h
  have h1 := CM.sect c1
  have h2 := CM.sect c2
  rw [h] at h1
  rw [← h1, h2]

-- ════════════════════════════════════════════════════════════
-- Section 3: The canonicalizer as an IdempotentNormalizer
-- ════════════════════════════════════════════════════════════

/-- Every CanonicalMirror yields an IdempotentNormalizer on the
    ambient carrier. This connects to ProjectionObstruction.lean. -/
def CanonicalMirror.toNormalizer (CM : CanonicalMirror) :
    IdempotentNormalizer CM.A where
  normalize := CM.canonicalize
  grade := CM.grade_A
  idempotent := CM.canonicalize_idempotent
  grade_le := CM.canonicalize_grade_le

/-- The canonical elements (fixed points of canonicalize) are exactly
    the image of incl. -/
theorem CanonicalMirror.canonical_iff_in_image (CM : CanonicalMirror) (a : CM.A) :
    CM.toNormalizer.isCanonical a ↔ ∃ c, CM.incl c = a := by
  constructor
  · -- If a is canonical (canonicalize(a) = a), then a = incl(normalize(a))
    intro h
    exact ⟨CM.normalize a, h⟩
  · -- If a = incl(c), then canonicalize(a) = canonicalize(incl(c)) = incl(c) = a
    intro ⟨c, hc⟩
    show CM.canonicalize a = a
    rw [← hc, CM.canonicalize_incl]

-- ════════════════════════════════════════════════════════════
-- Section 4: Nontriviality
-- ════════════════════════════════════════════════════════════

/-- A CanonicalMirror is nontrivial when there exists an ambient element
    that is NOT in the image of incl (not canonical). -/
def CanonicalMirror.Nontrivial (CM : CanonicalMirror) : Prop :=
  ∃ a, CM.canonicalize a ≠ a

/-- Nontriviality of the CanonicalMirror implies nontriviality of the
    induced IdempotentNormalizer. -/
theorem CanonicalMirror.nontrivial_normalizer (CM : CanonicalMirror)
    (h : CM.Nontrivial) : CM.toNormalizer.Nontrivial :=
  h

-- ════════════════════════════════════════════════════════════
-- Section 5: Cofinality — overflow witnesses can be normalized
-- ════════════════════════════════════════════════════════════

/-- Cofinality data for a CanonicalMirror: for any overflow witness
    on the ambient carrier, there exists an overflow witness in the
    canonical subdomain.

    This is the key property that connects the ambient overflow
    (selfApp is unbounded on A) to the canonical subdomain (the
    normalized witnesses still overflow). The normalization is
    grade-non-increasing and preserves the selfApp value (when
    selfApp = canonicalize), so normalizing an overflow witness
    produces another overflow witness in C.

    In the CanonicalMirror framework this is AUTOMATIC: if selfApp
    = canonicalize and canonicalize is grade-non-increasing, then
    for any x with grade(x) <= d and grade(selfApp(x)) > d, we have
    grade(canonicalize(x)) <= grade(x) <= d and selfApp(canonicalize(x))
    = canonicalize(canonicalize(x)) = canonicalize(x), so
    grade(selfApp(canonicalize(x))) = grade(canonicalize(x)) <= d.
    Wait -- that means the CANONICAL overflow witness does NOT overflow.

    This is precisely the projection obstruction from a different angle:
    you cannot have selfApp = canonicalize and SelfAppUnbounded, because
    canonical elements are fixed points where selfApp = id, so grade
    cannot overflow. The obstruction is real; the bridge must work
    without demanding selfApp = canonicalize on the full carrier.

    Instead, cofinality for the bridge argument requires:
    for overflow witnesses x (grade(selfApp(x)) > d), we can find
    x' in C with grade_C(x') <= d and the SAME selfApp behavior
    on the chain's bridge argument. This is what PartialMirrorAdequacy
    establishes. -/
theorem CanonicalMirror.normalize_grade_le_of_input
    (CM : CanonicalMirror) (a : CM.A) (d : Nat)
    (hle : CM.grade_A a ≤ d) :
    CM.grade_C (CM.normalize a) ≤ d :=
  Nat.le_trans (CM.normalize_grade_le a) hle

-- ════════════════════════════════════════════════════════════
-- Section 6: Connection to GroupBData
-- ════════════════════════════════════════════════════════════

/-- Every CanonicalMirror yields GroupBData on its ambient carrier:
    the canonicalizer is an idempotent retraction that is grade-non-increasing. -/
def CanonicalMirror.toGroupBData (CM : CanonicalMirror) :
    GroupBData CM.A where
  retract := CM.canonicalize
  grade := CM.grade_A
  idempotent := CM.canonicalize_idempotent
  red_grade_le := CM.canonicalize_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 7: Constructing a CanonicalMirror from subtype data
-- ════════════════════════════════════════════════════════════

/-- Build a CanonicalMirror when the canonical subdomain is given as
    a subtype { x : A // P x } with a normalization map landing in it. -/
def CanonicalMirror.ofSubtype
    (A : Type) (P : A → Prop)
    (norm : A → { x : A // P x })
    (grade : A → Nat)
    (norm_sect : ∀ (x : { x : A // P x }), norm x.val = x)
    (norm_grade_le : ∀ a, grade (norm a).val ≤ grade a) :
    CanonicalMirror where
  A := A
  C := { x : A // P x }
  incl := Subtype.val
  normalize := norm
  sect := norm_sect
  grade_A := grade
  grade_C := fun c => grade c.val
  grade_compat := fun _ => rfl
  normalize_grade_le := norm_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 8: Constructing a CanonicalMirror from an endomorphism
-- ════════════════════════════════════════════════════════════

/-- Build a CanonicalMirror from an idempotent grade-non-increasing
    endomorphism on A, using its fixed-point set as C.

    This is the canonical construction: given red : A -> A with
    red . red = red and grade(red(x)) <= grade(x), let C = Fix(red),
    incl = subtype inclusion, normalize(a) = (red(a), proof).

    NOTE: This requires decidable equality or proof irrelevance to
    construct the subtype. We use the fact that red(red(a)) = red(a)
    to get the proof that red(a) is a fixed point. -/
def CanonicalMirror.ofIdempotentEndo
    (A : Type)
    (red : A → A)
    (grade : A → Nat)
    (h_idem : ∀ x, red (red x) = red x)
    (h_grade_le : ∀ x, grade (red x) ≤ grade x) :
    CanonicalMirror where
  A := A
  C := { x : A // red x = x }
  incl := Subtype.val
  normalize a := ⟨red a, h_idem a⟩
  sect c := by
    ext
    show red c.val = c.val
    exact c.property
  grade_A := grade
  grade_C := fun c => grade c.val
  grade_compat _ := rfl
  normalize_grade_le := h_grade_le

/-- The canonicalizer of ofIdempotentEndo IS the original red. -/
theorem CanonicalMirror.ofIdempotentEndo_canonicalize
    (A : Type) (red : A → A) (grade : A → Nat)
    (h_idem : ∀ x, red (red x) = red x)
    (h_grade_le : ∀ x, grade (red x) ≤ grade x) :
    ∀ a, (CanonicalMirror.ofIdempotentEndo A red grade h_idem h_grade_le).canonicalize a = red a :=
  fun _ => rfl

-- ════════════════════════════════════════════════════════════
-- Section 9: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms CanonicalMirror.canonicalize_idempotent
#print axioms CanonicalMirror.canonicalize_grade_le
#print axioms CanonicalMirror.canonicalize_incl
#print axioms CanonicalMirror.incl_injective
#print axioms CanonicalMirror.toNormalizer
#print axioms CanonicalMirror.canonical_iff_in_image
#print axioms CanonicalMirror.toGroupBData
#print axioms CanonicalMirror.ofIdempotentEndo
#print axioms CanonicalMirror.ofIdempotentEndo_canonicalize

end WTS
