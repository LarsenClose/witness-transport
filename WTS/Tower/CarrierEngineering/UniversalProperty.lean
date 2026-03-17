/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/UniversalProperty.lean — The universal
property of the canonical splitting of an idempotent endomorphism.

Categorical significance: the splitting of an idempotent is unique up
to unique isomorphism. Given an idempotent e : A → A, ANY section-
retraction pair (C', incl', norm') satisfying incl' ∘ norm' = e is
canonically isomorphic to the fixed-point splitting (Fix(e), val, ⟨e·, idem⟩).
Moreover, the comparison map is the ONLY isomorphism compatible with
the embeddings.

Strategic significance: this makes AdmissibleEncoding the only
possible bridge. If a classical semantics induces an idempotent
residual (which any fold/unfold pair does), then the carrier
architecture it lands in is uniquely determined — not chosen.
The adequacy question reduces to: "does the classical semantics
satisfy the admissibility conditions?" If so, the induced
architecture is forced by the idempotent.

The file establishes:
  1. CompatibleSplitting: a section-retraction pair whose induced
     canonicalizer equals a given idempotent.
  2. Comparison maps toFixed / fromFixed between any compatible
     splitting and the canonical fixed-point splitting.
  3. These maps are mutually inverse (the universal property).
  4. The comparison is the unique isomorphism compatible with the
     embeddings into A.
  5. Normalization intertwining: normalizing in any compatible
     splitting agrees with canonical normalization, up to comparison.
  6. GRM and AdmissibleEncoding corollaries.

STATUS: 0 sorry.
-/

import WTS.Tower.CarrierEngineering.SplitIdempotent
import WTS.Tower.CarrierEngineering.AdmissibleBridge

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: CompatibleSplitting — a splitting compatible with
-- a given idempotent
-- ════════════════════════════════════════════════════════════

/-- A compatible splitting of an idempotent e on A: a section-retraction
    pair (C', incl', norm') such that incl' ∘ norm' = e. The key
    compatibility condition `compat` says the induced canonicalizer
    equals the original idempotent — this is what makes the splitting
    "of" the idempotent e, not just any retraction. -/
structure CompatibleSplitting (S : SplitIdempotent) where
  /-- The splitting's carrier type. -/
  C' : Type
  /-- Inclusion: C' embeds into A. -/
  incl' : C' → S.A
  /-- Normalization: A projects to C'. -/
  norm' : S.A → C'
  /-- Section: norm' is left inverse of incl'. -/
  sect' : ∀ c, norm' (incl' c) = c
  /-- Compatibility: incl' ∘ norm' = e. This is the essential condition. -/
  compat : ∀ a, incl' (norm' a) = S.e a

-- ════════════════════════════════════════════════════════════
-- Section 2: The canonical splitting IS a CompatibleSplitting
-- ════════════════════════════════════════════════════════════

/-- The canonical fixed-point splitting is a CompatibleSplitting.
    C' = Fix(e), incl' = Subtype.val, norm' a = ⟨e a, idem a⟩.
    Compatibility: val(⟨e a, _⟩) = e a, which is definitional. -/
def SplitIdempotent.canonicalSplitting (S : SplitIdempotent) :
    CompatibleSplitting S where
  C' := S.FixedPoints
  incl' := Subtype.val
  norm' a := ⟨S.e a, S.idem a⟩
  sect' c := by
    apply Subtype.ext
    show S.e c.val = c.val
    exact c.property
  compat _ := rfl

-- ════════════════════════════════════════════════════════════
-- Section 3: Comparison maps
-- ════════════════════════════════════════════════════════════

/-- Forward comparison: C' → Fix(e).
    Send c' to incl'(c'), which is a fixed point of e because:
      e(incl'(c')) = incl'(norm'(incl'(c'))) = incl'(c')
    by compat and sect'. -/
def CompatibleSplitting.toFixed {S : SplitIdempotent} (CS : CompatibleSplitting S)
    (c' : CS.C') : S.FixedPoints :=
  ⟨CS.incl' c', by
    -- Need: S.e (CS.incl' c') = CS.incl' c'
    -- By compat at (incl' c'): incl'(norm'(incl' c')) = e(incl' c')
    -- By sect': norm'(incl' c') = c'
    -- So: incl'(c') = e(incl' c'), i.e., e(incl' c') = incl'(c')
    have h1 : CS.incl' (CS.norm' (CS.incl' c')) = S.e (CS.incl' c') :=
      CS.compat (CS.incl' c')
    rw [CS.sect'] at h1
    exact h1.symm⟩

/-- Backward comparison: Fix(e) → C'.
    Send ⟨a, ha⟩ to norm'(a). -/
def CompatibleSplitting.fromFixed {S : SplitIdempotent} (CS : CompatibleSplitting S)
    (fp : S.FixedPoints) : CS.C' :=
  CS.norm' fp.val

-- ════════════════════════════════════════════════════════════
-- Section 4: The universal property — comparison maps are inverse
-- ════════════════════════════════════════════════════════════

/-- toFixed ∘ fromFixed = id on Fix(e).

    Proof: fromFixed(⟨a, ha⟩) = norm'(a), so
    toFixed(norm'(a)) = ⟨incl'(norm'(a)), ...⟩ = ⟨e(a), ...⟩ = ⟨a, ...⟩
    by compat and ha : e(a) = a. -/
theorem CompatibleSplitting.toFixed_fromFixed {S : SplitIdempotent}
    (CS : CompatibleSplitting S) (fp : S.FixedPoints) :
    CS.toFixed (CS.fromFixed fp) = fp := by
  apply Subtype.ext
  show CS.incl' (CS.norm' fp.val) = fp.val
  rw [CS.compat]
  exact fp.property

/-- fromFixed ∘ toFixed = id on C'.

    Proof: toFixed(c') = ⟨incl'(c'), ...⟩, so
    fromFixed(⟨incl'(c'), ...⟩) = norm'(incl'(c')) = c' by sect'. -/
theorem CompatibleSplitting.fromFixed_toFixed {S : SplitIdempotent}
    (CS : CompatibleSplitting S) (c' : CS.C') :
    CS.fromFixed (CS.toFixed c') = c' := by
  show CS.norm' (CS.incl' c') = c'
  exact CS.sect' c'

/-- The comparison is a bijection: toFixed is injective. -/
theorem CompatibleSplitting.toFixed_injective {S : SplitIdempotent}
    (CS : CompatibleSplitting S) : Function.Injective CS.toFixed := by
  intro c1 c2 h
  have := congrArg CS.fromFixed h
  rwa [CS.fromFixed_toFixed, CS.fromFixed_toFixed] at this

/-- The comparison is a bijection: toFixed is surjective. -/
theorem CompatibleSplitting.toFixed_surjective {S : SplitIdempotent}
    (CS : CompatibleSplitting S) : Function.Surjective CS.toFixed := by
  intro fp
  exact ⟨CS.fromFixed fp, CS.toFixed_fromFixed fp⟩

/-- The comparison is a bijection: fromFixed is injective. -/
theorem CompatibleSplitting.fromFixed_injective {S : SplitIdempotent}
    (CS : CompatibleSplitting S) : Function.Injective CS.fromFixed := by
  intro fp1 fp2 h
  have := congrArg CS.toFixed h
  rwa [CS.toFixed_fromFixed, CS.toFixed_fromFixed] at this

/-- The comparison is a bijection: fromFixed is surjective. -/
theorem CompatibleSplitting.fromFixed_surjective {S : SplitIdempotent}
    (CS : CompatibleSplitting S) : Function.Surjective CS.fromFixed := by
  intro c'
  exact ⟨CS.toFixed c', CS.fromFixed_toFixed c'⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Uniqueness — the comparison is the ONLY compatible
-- isomorphism
-- ════════════════════════════════════════════════════════════

/-- Any map φ : C' → Fix(e) satisfying (φ c').val = incl'(c') must
    equal toFixed. The comparison map is not just an isomorphism —
    it is the unique one compatible with the embeddings into A.

    Proof: if (φ c').val = incl'(c'), then φ c' and toFixed c' have
    the same .val, hence are equal by Subtype.ext. -/
theorem CompatibleSplitting.toFixed_unique {S : SplitIdempotent}
    (CS : CompatibleSplitting S)
    (φ : CS.C' → S.FixedPoints)
    (h : ∀ c', (φ c').val = CS.incl' c') :
    ∀ c', φ c' = CS.toFixed c' := by
  intro c'
  apply Subtype.ext
  exact h c'

/-- Dually: any map ψ : Fix(e) → C' satisfying incl'(ψ fp) = fp.val
    must equal fromFixed.

    Proof: ψ fp = norm'(fp.val) because:
    incl'(ψ fp) = fp.val and incl'(norm'(fp.val)) = e(fp.val) = fp.val
    by compat and fp.property. Applying norm' ∘ incl' being id (sect')
    and the fact that incl' is injective-like through norm'. -/
theorem CompatibleSplitting.fromFixed_unique {S : SplitIdempotent}
    (CS : CompatibleSplitting S)
    (ψ : S.FixedPoints → CS.C')
    (h : ∀ fp, CS.incl' (ψ fp) = fp.val) :
    ∀ fp, ψ fp = CS.fromFixed fp := by
  intro fp
  -- ψ fp and fromFixed fp both map to the same thing under incl':
  -- incl'(ψ fp) = fp.val  (hypothesis h)
  -- incl'(fromFixed fp) = incl'(norm'(fp.val)) = e(fp.val) = fp.val
  --   (by compat and fp.property)
  -- So norm'(incl'(ψ fp)) = norm'(incl'(fromFixed fp))
  -- By sect': ψ fp = fromFixed fp
  have h1 : CS.incl' (ψ fp) = CS.incl' (CS.fromFixed fp) := by
    rw [h]
    show fp.val = CS.incl' (CS.norm' fp.val)
    rw [CS.compat]
    exact fp.property.symm
  have h2 : CS.norm' (CS.incl' (ψ fp)) = CS.norm' (CS.incl' (CS.fromFixed fp)) :=
    congrArg CS.norm' h1
  rwa [CS.sect', CS.sect'] at h2

-- ════════════════════════════════════════════════════════════
-- Section 6: Normalization intertwining
-- ════════════════════════════════════════════════════════════

/-- The comparison maps intertwine the normalization maps:
    toFixed ∘ norm' = canonical norm.

    This says normalization in ANY compatible splitting, followed by
    comparison to Fix(e), gives the SAME result as normalizing
    directly in the canonical splitting. The two normalizations agree.

    Proof: both sides have .val = e(a):
      (toFixed(norm'(a))).val = incl'(norm'(a)) = e(a) by compat
      (canonical norm a).val  = e(a) definitionally. -/
theorem CompatibleSplitting.norm_intertwines {S : SplitIdempotent}
    (CS : CompatibleSplitting S) (a : S.A) :
    CS.toFixed (CS.norm' a) = S.toReflectiveCarrierData.norm a := by
  apply Subtype.ext
  show CS.incl' (CS.norm' a) = S.e a
  exact CS.compat a

/-- The inclusion maps intertwine with fromFixed:
    incl' ∘ fromFixed = Subtype.val.

    This says: mapping a fixed point to C' via fromFixed and then
    including back into A recovers the original value.

    Proof: incl'(fromFixed ⟨a, ha⟩) = incl'(norm'(a)) = e(a) = a
    by compat and ha. -/
theorem CompatibleSplitting.incl_intertwines {S : SplitIdempotent}
    (CS : CompatibleSplitting S) (fp : S.FixedPoints) :
    CS.incl' (CS.fromFixed fp) = fp.val := by
  show CS.incl' (CS.norm' fp.val) = fp.val
  rw [CS.compat]
  exact fp.property

-- ════════════════════════════════════════════════════════════
-- Section 7: Any two compatible splittings are isomorphic
-- ════════════════════════════════════════════════════════════

/-- Given two compatible splittings of the same idempotent, there is
    a canonical bijection between their carrier types, obtained by
    composing through Fix(e). -/
def CompatibleSplitting.compare {S : SplitIdempotent}
    (CS₁ CS₂ : CompatibleSplitting S) (c₁ : CS₁.C') : CS₂.C' :=
  CS₂.fromFixed (CS₁.toFixed c₁)

/-- The comparison between two compatible splittings is an isomorphism:
    compare CS₁ CS₂ ∘ compare CS₂ CS₁ = id. -/
theorem CompatibleSplitting.compare_inverse {S : SplitIdempotent}
    (CS₁ CS₂ : CompatibleSplitting S) (c₂ : CS₂.C') :
    CS₁.compare CS₂ (CS₂.compare CS₁ c₂) = c₂ := by
  show CS₂.fromFixed (CS₁.toFixed (CS₁.fromFixed (CS₂.toFixed c₂))) = c₂
  rw [CS₁.toFixed_fromFixed]
  exact CS₂.fromFixed_toFixed c₂

/-- The comparison preserves the embedding into A:
    incl₂(compare(c₁)) = incl₁(c₁).

    Two compatible splittings embed the "same" elements into A. -/
theorem CompatibleSplitting.compare_preserves_incl {S : SplitIdempotent}
    (CS₁ CS₂ : CompatibleSplitting S) (c₁ : CS₁.C') :
    CS₂.incl' (CS₁.compare CS₂ c₁) = CS₁.incl' c₁ := by
  show CS₂.incl' (CS₂.fromFixed (CS₁.toFixed c₁)) = CS₁.incl' c₁
  exact CS₂.incl_intertwines (CS₁.toFixed c₁)

-- ════════════════════════════════════════════════════════════
-- Section 8: GRM connection
-- ════════════════════════════════════════════════════════════

/-- Any section-retraction pair on a GRM's carrier compatible with
    selfApp is a CompatibleSplitting of the GRM's SplitIdempotent. -/
structure GRMCompatibleSplitting (M : GradedReflModel) where
  /-- The splitting's carrier type. -/
  C' : Type
  /-- Inclusion: C' embeds into M.carrier. -/
  incl' : C' → M.carrier
  /-- Normalization: M.carrier projects to C'. -/
  norm' : M.carrier → C'
  /-- Section: norm' is left inverse of incl'. -/
  sect' : ∀ c, norm' (incl' c) = c
  /-- Compatibility: incl' ∘ norm' = selfApp. -/
  compat : ∀ x, incl' (norm' x) = M.selfApp x

/-- A GRMCompatibleSplitting is a CompatibleSplitting of the GRM's
    induced SplitIdempotent. The e of the SplitIdempotent is
    definitionally selfApp. -/
def GRMCompatibleSplitting.toCompatibleSplitting {M : GradedReflModel}
    (CS : GRMCompatibleSplitting M) :
    CompatibleSplitting (M.toReflectiveCarrierData.toSplitIdempotent) where
  C' := CS.C'
  incl' := CS.incl'
  norm' := CS.norm'
  sect' := CS.sect'
  compat a := by
    show CS.incl' (CS.norm' a) = M.toReflectiveCarrierData.canonicalize a
    rw [GradedReflModel.reflectiveCarrierData_canonicalize]
    exact CS.compat a

/-- The canonical ReflectiveCarrierData of a GRM IS a GRMCompatibleSplitting. -/
def GradedReflModel.canonicalGRMSplitting (M : GradedReflModel) :
    GRMCompatibleSplitting M where
  C' := { x : M.carrier // M.selfApp x = x }
  incl' := Subtype.val
  norm' x := ⟨M.selfApp x, grm_roundtrip_forces_idempotent M x⟩
  sect' c := by
    ext
    show M.selfApp c.val = c.val
    exact c.property
  compat _ := rfl

/-- The universal property for GRMs: any GRMCompatibleSplitting has its
    carrier C' in bijection with Fix(selfApp), and this bijection is
    canonical. -/
theorem GRMCompatibleSplitting.universal_property {M : GradedReflModel}
    (CS : GRMCompatibleSplitting M) :
    let CS' := CS.toCompatibleSplitting
    (∀ c', CS'.toFixed (CS'.fromFixed c') = c') ∧
    (∀ fp, CS'.fromFixed (CS'.toFixed fp) = fp) :=
  ⟨CS.toCompatibleSplitting.toFixed_fromFixed,
   CS.toCompatibleSplitting.fromFixed_toFixed⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: AdmissibleEncoding connection
-- ════════════════════════════════════════════════════════════

/-- Every AdmissibleEncoding induces a SplitIdempotent via
    selfApp = unfold ∘ fold. -/
def AdmissibleEncoding.toSplitIdempotent (E : AdmissibleEncoding) :
    SplitIdempotent where
  A := E.Names
  e x := E.unfold (E.fold x)
  idem := grm_roundtrip_forces_idempotent E.toGRM

/-- The AdmissibleEncoding's SplitIdempotent agrees with the one
    obtained through the GRM path. -/
theorem AdmissibleEncoding.splitIdempotent_eq_grm (E : AdmissibleEncoding) :
    ∀ x, E.toSplitIdempotent.e x =
         (E.toGRM.toReflectiveCarrierData.toSplitIdempotent).e x := by
  intro x; rfl

/-- Any section-retraction pair on an AdmissibleEncoding's carrier
    compatible with selfApp induces a uniquely determined carrier
    architecture.

    Combined with the invariance theorems from AdmissibleBridge.lean
    and ReencodingInvariance.lean, this says: if your classical
    semantics satisfies admissibility, the carrier architecture is
    forced — there is no alternative. -/
theorem AdmissibleEncoding.carrier_architecture_unique
    (E : AdmissibleEncoding) (CS : CompatibleSplitting E.toSplitIdempotent) :
    -- The comparison maps are mutually inverse
    (∀ fp, CS.toFixed (CS.fromFixed fp) = fp) ∧
    (∀ c', CS.fromFixed (CS.toFixed c') = c') ∧
    -- And the comparison is the UNIQUE such map
    (∀ (φ : CS.C' → E.toSplitIdempotent.FixedPoints),
      (∀ c', (φ c').val = CS.incl' c') → ∀ c', φ c' = CS.toFixed c') :=
  ⟨CS.toFixed_fromFixed, CS.fromFixed_toFixed, CS.toFixed_unique⟩

-- ════════════════════════════════════════════════════════════
-- Section 10: The factorization theorem
-- ════════════════════════════════════════════════════════════

/-- FACTORIZATION: any compatible splitting of a SplitIdempotent
    factors uniquely through the canonical fixed-point splitting.

    This is the formal statement that the architecture is forced:
    if your semantics induces an idempotent (which any fold/unfold
    pair does), and you have ANY section-retraction pair compatible
    with it, then your carrier type is canonically isomorphic to
    Fix(e), your inclusion is determined, and your normalization is
    determined — up to the unique comparison isomorphism.

    The four components:
    1. Bijection: toFixed and fromFixed are mutually inverse.
    2. Inclusion compatibility: incl_canonical ∘ toFixed = incl'.
    3. Normalization compatibility: toFixed ∘ norm' = norm_canonical.
    4. Uniqueness: toFixed is the only map with property (2). -/
theorem CompatibleSplitting.factorization {S : SplitIdempotent}
    (CS : CompatibleSplitting S) :
    -- (1) Bijection
    (∀ fp, CS.toFixed (CS.fromFixed fp) = fp) ∧
    (∀ c', CS.fromFixed (CS.toFixed c') = c') ∧
    -- (2) Inclusion compatibility: val ∘ toFixed = incl'
    (∀ c', (CS.toFixed c').val = CS.incl' c') ∧
    -- (3) Normalization compatibility
    (∀ a, CS.toFixed (CS.norm' a) = S.toReflectiveCarrierData.norm a) ∧
    -- (4) Uniqueness
    (∀ (φ : CS.C' → S.FixedPoints),
      (∀ c', (φ c').val = CS.incl' c') → ∀ c', φ c' = CS.toFixed c') :=
  ⟨CS.toFixed_fromFixed,
   CS.fromFixed_toFixed,
   fun _ => rfl,
   CS.norm_intertwines,
   CS.toFixed_unique⟩

-- ════════════════════════════════════════════════════════════
-- Section 11: The canonical splitting is self-comparing
-- ════════════════════════════════════════════════════════════

/-- The canonical splitting compared with itself is the identity:
    toFixed on the canonical splitting is the identity on Fix(e). -/
theorem SplitIdempotent.canonicalSplitting_toFixed_eq_id (S : SplitIdempotent)
    (c : S.FixedPoints) :
    S.canonicalSplitting.toFixed c = c := by
  apply Subtype.ext
  -- toFixed c = ⟨incl'(c), ...⟩ = ⟨c.val, ...⟩ since incl' = Subtype.val
  rfl

/-- The canonical splitting compared with itself: fromFixed is the identity. -/
theorem SplitIdempotent.canonicalSplitting_fromFixed_eq_id (S : SplitIdempotent)
    (fp : S.FixedPoints) :
    S.canonicalSplitting.fromFixed fp = fp := by
  -- fromFixed fp = norm'(fp.val) = ⟨e(fp.val), _⟩ = ⟨fp.val, _⟩
  apply Subtype.ext
  show S.e fp.val = fp.val
  exact fp.property

-- ════════════════════════════════════════════════════════════
-- Section 12: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms SplitIdempotent.canonicalSplitting
#print axioms CompatibleSplitting.toFixed
#print axioms CompatibleSplitting.fromFixed
#print axioms CompatibleSplitting.toFixed_fromFixed
#print axioms CompatibleSplitting.fromFixed_toFixed
#print axioms CompatibleSplitting.toFixed_injective
#print axioms CompatibleSplitting.toFixed_surjective
#print axioms CompatibleSplitting.fromFixed_injective
#print axioms CompatibleSplitting.fromFixed_surjective
#print axioms CompatibleSplitting.toFixed_unique
#print axioms CompatibleSplitting.fromFixed_unique
#print axioms CompatibleSplitting.norm_intertwines
#print axioms CompatibleSplitting.incl_intertwines
#print axioms CompatibleSplitting.compare
#print axioms CompatibleSplitting.compare_inverse
#print axioms CompatibleSplitting.compare_preserves_incl
#print axioms GRMCompatibleSplitting.toCompatibleSplitting
#print axioms GradedReflModel.canonicalGRMSplitting
#print axioms GRMCompatibleSplitting.universal_property
#print axioms AdmissibleEncoding.toSplitIdempotent
#print axioms AdmissibleEncoding.splitIdempotent_eq_grm
#print axioms AdmissibleEncoding.carrier_architecture_unique
#print axioms CompatibleSplitting.factorization
#print axioms SplitIdempotent.canonicalSplitting_toFixed_eq_id
#print axioms SplitIdempotent.canonicalSplitting_fromFixed_eq_id

end WTS
