/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/DefectSpectrum.lean — The defect spectrum
of a GRM: a coarse geometric invariant under bounded reencoding.

The defect function captures the worst-case additive grade increase of
selfApp at each grade level. This replaces scattered qualitative predicates
(FiniteDrift? UnboundedGap? SelfAppUnbounded?) with one geometric object.

Key results:
  - DefectBounded k ↔ AdmitsDrift k (links to existing drift API)
  - FiniteDrift ↔ ∃ k, DefectBounded k
  - UnboundedGap ↔ ∀ k, ∃ d, DefectExceeds d k
  - Defect transport: BoundedGRMEquiv shifts defect by at most 2 * overhead
  - DefectEquivalent: coarse defect class is encoding-invariant
  - Concrete witnesses: standardModel unbounded, trivialModel zero

STATUS: 0 sorry.
-/

import WTS.Tower.CarrierEngineering.ReencodingInvariance

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Pointwise gap and defect predicates
-- ════════════════════════════════════════════════════════════

/-- The additive grade increase of selfApp at a specific carrier element.
    Uses truncated subtraction: if selfApp decreases grade, gap is 0. -/
def GradedReflModel.gap (M : GradedReflModel) (x : M.carrier) : Nat :=
  M.grade (M.selfApp x) - M.grade x

/-- The defect at grade level d is bounded by k: every input at grade ≤ d
    has gap at most k. -/
def GradedReflModel.DefectBoundedAt (M : GradedReflModel) (d k : Nat) : Prop :=
  ∀ x, M.grade x ≤ d → M.grade (M.selfApp x) ≤ M.grade x + k

/-- The defect is globally bounded by k: selfApp increases grade by at most k
    everywhere. -/
def GradedReflModel.DefectBounded (M : GradedReflModel) (k : Nat) : Prop :=
  ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k

/-- The defect exceeds k at grade level d: there exists an input at grade ≤ d
    whose gap exceeds k. -/
def GradedReflModel.DefectExceeds (M : GradedReflModel) (d k : Nat) : Prop :=
  ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > M.grade x + k

-- ════════════════════════════════════════════════════════════
-- Section 2: Equivalences linking to existing predicates
-- ════════════════════════════════════════════════════════════

/-- Global defect bounded by k ↔ drift-k extension exists.
    This bridges the defect language to the existing drift API. -/
theorem GradedReflModel.defectBounded_iff_drift (M : GradedReflModel) (k : Nat) :
    M.DefectBounded k ↔ M.AdmitsDrift k := by
  unfold DefectBounded AdmitsDrift
  exact (M.drift_extension_iff k).symm

/-- Defect bounded at every level iff globally bounded.
    The quantifier over d is redundant since DefectBounded already
    quantifies over all x. -/
theorem GradedReflModel.defectBoundedAt_all_iff_defectBounded (M : GradedReflModel) (k : Nat) :
    (∀ d, M.DefectBoundedAt d k) ↔ M.DefectBounded k := by
  unfold DefectBoundedAt DefectBounded
  constructor
  · intro h x
    exact h (M.grade x) x (Nat.le_refl _)
  · intro h d x _
    exact h x

/-- FiniteDrift ↔ defect is globally bounded by some k. -/
theorem GradedReflModel.finiteDrift_iff_defect_bounded (M : GradedReflModel) :
    M.FiniteDrift ↔ ∃ k, M.DefectBounded k := by
  unfold FiniteDrift DefectBounded AdmitsDrift
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, (M.drift_extension_iff k).mp hk⟩
  · intro ⟨k, hk⟩
    exact ⟨k, (M.drift_extension_iff k).mpr hk⟩

/-- UnboundedGap ↔ defect exceeds every bound at some level.
    The defect function grows without bound. -/
theorem GradedReflModel.unboundedGap_iff_defect_unbounded (M : GradedReflModel) :
    M.UnboundedGap ↔ ∀ k, ∃ d, M.DefectExceeds d k := by
  unfold UnboundedGap DefectExceeds
  constructor
  · intro h k
    obtain ⟨x, hgap⟩ := h k
    exact ⟨M.grade x, x, Nat.le_refl _, hgap⟩
  · intro h k
    obtain ⟨d, x, _, hgap⟩ := h k
    exact ⟨x, hgap⟩

/-- DefectBounded 0 ↔ strict naming (grade-non-increasing selfApp). -/
theorem GradedReflModel.defectBounded_zero_iff_strict (M : GradedReflModel) :
    M.DefectBounded 0 ↔ Nonempty M.GradeCompatibleExtension := by
  unfold DefectBounded
  rw [M.grade_compatible_extension_iff]
  constructor
  · intro h x; have := h x; omega
  · intro h x; have := h x; omega

-- ════════════════════════════════════════════════════════════
-- Section 3: Monotonicity
-- ════════════════════════════════════════════════════════════

/-- DefectBoundedAt is monotone in d (larger grade level, same bound):
    restricting to a smaller grade level preserves the bound. -/
theorem GradedReflModel.defectBoundedAt_mono_d (M : GradedReflModel) {d₁ d₂ k : Nat}
    (h : d₁ ≤ d₂) : M.DefectBoundedAt d₂ k → M.DefectBoundedAt d₁ k := by
  intro hbd x hx
  exact hbd x (Nat.le_trans hx h)

/-- DefectBounded is monotone in k (larger bound). -/
theorem GradedReflModel.defectBounded_mono (M : GradedReflModel) {k₁ k₂ : Nat}
    (h : k₁ ≤ k₂) : M.DefectBounded k₁ → M.DefectBounded k₂ := by
  intro hb x
  have := hb x; omega

/-- DefectExceeds is anti-monotone in k: exceeding a larger bound implies
    exceeding a smaller one. -/
theorem GradedReflModel.defectExceeds_anti_k (M : GradedReflModel) {d k₁ k₂ : Nat}
    (h : k₂ ≤ k₁) : M.DefectExceeds d k₁ → M.DefectExceeds d k₂ := by
  intro ⟨x, hle, hgt⟩
  exact ⟨x, hle, by omega⟩

/-- DefectExceeds is monotone in d: enlarging the grade level preserves
    the witness. -/
theorem GradedReflModel.defectExceeds_mono_d (M : GradedReflModel) {d₁ d₂ k : Nat}
    (h : d₁ ≤ d₂) : M.DefectExceeds d₁ k → M.DefectExceeds d₂ k := by
  intro ⟨x, hle, hgt⟩
  exact ⟨x, Nat.le_trans hle h, hgt⟩

/-- DefectBoundedAt is anti-monotone in k: a tighter bound implies a looser one. -/
theorem GradedReflModel.defectBoundedAt_mono_k (M : GradedReflModel) {d k₁ k₂ : Nat}
    (h : k₁ ≤ k₂) : M.DefectBoundedAt d k₁ → M.DefectBoundedAt d k₂ := by
  intro hbd x hx
  have := hbd x hx; omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Complementarity
-- ════════════════════════════════════════════════════════════

/-- DefectBounded k and DefectExceeds d k are contradictory. -/
theorem GradedReflModel.defectBounded_not_exceeds (M : GradedReflModel) {d k : Nat}
    (hb : M.DefectBounded k) : ¬M.DefectExceeds d k := by
  intro ⟨x, _, hgt⟩
  have := hb x; omega

/-- DefectBoundedAt d k and DefectExceeds d k are contradictory. -/
theorem GradedReflModel.defectBoundedAt_not_exceeds (M : GradedReflModel) {d k : Nat}
    (hb : M.DefectBoundedAt d k) : ¬M.DefectExceeds d k := by
  intro ⟨x, hle, hgt⟩
  have := hb x hle; omega

-- ════════════════════════════════════════════════════════════
-- Section 5: The defect transport theorem
-- ════════════════════════════════════════════════════════════

/-- DEFECT TRANSPORT (M → M'): if M has defect bounded by k, then M' has
    defect bounded by k + 2 * overhead. The defect envelope shifts by at
    most 2 * overhead under bounded reencoding.

    Reuses drift_transport from ReencodingInvariance.lean. -/
theorem BoundedGRMEquiv.defectBounded_transport {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) :
    M.DefectBounded k → M'.DefectBounded (k + 2 * E.overhead) :=
  E.drift_transport k

/-- DEFECT TRANSPORT (M' → M): symmetric direction. -/
theorem BoundedGRMEquiv.defectBounded_transport_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) :
    M'.DefectBounded k → M.DefectBounded (k + 2 * E.overhead) :=
  E.drift_transport_g k

/-- DEFECT FINITENESS IS ENCODING-INVARIANT: M has some finite defect bound
    iff M' does. This is finite_drift_iff restated in defect language. -/
theorem BoundedGRMEquiv.defect_finiteness_iff {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    (∃ k, M.DefectBounded k) ↔ (∃ k, M'.DefectBounded k) := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k + 2 * E.overhead, E.defectBounded_transport k hk⟩
  · intro ⟨k, hk⟩
    exact ⟨k + 2 * E.overhead, E.defectBounded_transport_g k hk⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: DefectExceeds transport
-- ════════════════════════════════════════════════════════════

/-- If defect exceeds k + 2c at some level in M, defect exceeds k at some
    level in M'. The witness is transported via f and the grade level shifts
    by at most overhead. -/
theorem BoundedGRMEquiv.defectExceeds_transport {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) (d : Nat) :
    M.DefectExceeds d (k + 2 * E.overhead) →
    M'.DefectExceeds (d + E.overhead) k := by
  intro ⟨x, hle, hgap⟩
  refine ⟨E.f x, ?_, ?_⟩
  · -- grade'(f(x)) ≤ grade(x) + overhead ≤ d + overhead
    have := E.f_bounded x; omega
  · -- gap_distortion: gap > k + 2c in M → gap > k in M'
    exact E.gap_distortion x k hgap

/-- Symmetric DefectExceeds transport via g. -/
theorem BoundedGRMEquiv.defectExceeds_transport_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) (d : Nat) :
    M'.DefectExceeds d (k + 2 * E.overhead) →
    M.DefectExceeds (d + E.overhead) k := by
  intro ⟨x', hle, hgap⟩
  refine ⟨E.g x', ?_, ?_⟩
  · have := E.g_bounded x'; omega
  · exact E.gap_distortion_g x' k hgap

-- ════════════════════════════════════════════════════════════
-- Section 7: The coarse defect class
-- ════════════════════════════════════════════════════════════

/-- Two models have equivalent defect class when their defect bounds differ
    by at most an additive constant c. -/
def DefectEquivalent (M M' : GradedReflModel) (c : Nat) : Prop :=
  (∀ k, M.DefectBounded k → M'.DefectBounded (k + c)) ∧
  (∀ k, M'.DefectBounded k → M.DefectBounded (k + c))

/-- BoundedGRMEquiv implies defect equivalence with constant 2 * overhead. -/
theorem BoundedGRMEquiv.toDefectEquivalent {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    DefectEquivalent M M' (2 * E.overhead) :=
  ⟨fun k => E.defectBounded_transport k, fun k => E.defectBounded_transport_g k⟩

/-- DefectEquivalent is reflexive with constant 0. -/
theorem defectEquivalent_refl (M : GradedReflModel) :
    DefectEquivalent M M 0 := by
  constructor <;> intro k hk <;> simpa using hk

/-- DefectEquivalent is symmetric. -/
theorem defectEquivalent_symm {M M' : GradedReflModel} {c : Nat} :
    DefectEquivalent M M' c → DefectEquivalent M' M c := by
  intro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- DefectEquivalent is transitive (with additive constants). -/
theorem defectEquivalent_trans {M M' M'' : GradedReflModel} {c₁ c₂ : Nat} :
    DefectEquivalent M M' c₁ → DefectEquivalent M' M'' c₂ →
    DefectEquivalent M M'' (c₁ + c₂) := by
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  constructor
  · intro k hk
    have h := h3 (k + c₁) (h1 k hk)
    have : k + c₁ + c₂ = k + (c₁ + c₂) := by omega
    rw [this] at h; exact h
  · intro k hk
    have h := h2 (k + c₂) (h4 k hk)
    have : k + c₂ + c₁ = k + (c₁ + c₂) := by omega
    rw [this] at h; exact h

/-- DefectEquivalent is monotone in the constant. -/
theorem defectEquivalent_mono {M M' : GradedReflModel} {c₁ c₂ : Nat}
    (h : c₁ ≤ c₂) : DefectEquivalent M M' c₁ → DefectEquivalent M M' c₂ := by
  intro ⟨h1, h2⟩
  constructor
  · intro k hk
    exact M'.defectBounded_mono (by omega) (h1 k hk)
  · intro k hk
    exact M.defectBounded_mono (by omega) (h2 k hk)

-- ════════════════════════════════════════════════════════════
-- Section 8: Concrete witnesses
-- ════════════════════════════════════════════════════════════

/-- standardModel has unbounded defect: defect exceeds every bound.
    Uses standardModel_unboundedGap from ReflectiveCarrierData.lean. -/
theorem standardModel_defect_unbounded :
    ∀ k, ∃ d, standardModel.DefectExceeds d k := by
  exact standardModel.unboundedGap_iff_defect_unbounded.mp standardModel_unboundedGap

/-- trivialModel has defect 0. -/
theorem trivialModel_defect_zero :
    trivialModel.DefectBounded 0 := by
  intro x
  have : trivialModel.selfApp x = x := trivial_selfApp_eq_id x
  rw [this]; omega

/-- trivialModel has zero defect at every level. -/
theorem trivialModel_defectBoundedAt_zero :
    ∀ d, trivialModel.DefectBoundedAt d 0 := by
  rw [trivialModel.defectBoundedAt_all_iff_defectBounded]
  exact trivialModel_defect_zero

-- ════════════════════════════════════════════════════════════
-- Section 9: Gap properties
-- ════════════════════════════════════════════════════════════

/-- Fixed points have zero gap. -/
theorem GradedReflModel.gap_eq_zero_of_fixed (M : GradedReflModel) (x : M.carrier)
    (hfix : M.selfApp x = x) : M.gap x = 0 := by
  unfold gap; rw [hfix]; omega

/-- DefectBounded k implies gap ≤ k everywhere. -/
theorem GradedReflModel.gap_le_of_defectBounded (M : GradedReflModel) {k : Nat}
    (hb : M.DefectBounded k) (x : M.carrier) : M.gap x ≤ k := by
  unfold gap
  have := hb x; omega

/-- Gap > k implies DefectExceeds at the grade of the witness. -/
theorem GradedReflModel.defectExceeds_of_gap_gt (M : GradedReflModel) (x : M.carrier) (k : Nat)
    (h : M.grade (M.selfApp x) > M.grade x + k) :
    M.DefectExceeds (M.grade x) k :=
  ⟨x, Nat.le_refl _, h⟩

-- ════════════════════════════════════════════════════════════
-- Section 10: Protocol GRM defect bound
-- ════════════════════════════════════════════════════════════

/-- Protocol GRMs have defect bounded by 2 * overhead.
    Reuses selfApp_constant_overhead from ReflectiveCarrierData.lean. -/
theorem ProtocolGRM.defect_bounded (P : ProtocolGRM) :
    P.toGRM.DefectBounded (2 * P.sys.transportOverhead) :=
  P.selfApp_constant_overhead

/-- Protocol GRMs are defect-equivalent under bounded reencoding. -/
theorem ProtocolGRM.admits_drift_from_defect (P : ProtocolGRM) :
    P.toGRM.AdmitsDrift (2 * P.sys.transportOverhead) :=
  (P.toGRM.defectBounded_iff_drift (2 * P.sys.transportOverhead)).mp P.defect_bounded

-- ════════════════════════════════════════════════════════════
-- Section 11: DefectBounded and negation relationships
-- ════════════════════════════════════════════════════════════

/-- ¬DefectBounded k ↔ ∃ x, gap > k (classically). -/
theorem GradedReflModel.not_defectBounded_iff (M : GradedReflModel) (k : Nat) :
    ¬M.DefectBounded k ↔ ∃ x, M.grade (M.selfApp x) > M.grade x + k := by
  unfold DefectBounded
  push_neg
  rfl

/-- ¬DefectBoundedAt d k ↔ DefectExceeds d k (classically). -/
theorem GradedReflModel.not_defectBoundedAt_iff (M : GradedReflModel) (d k : Nat) :
    ¬M.DefectBoundedAt d k ↔ M.DefectExceeds d k := by
  unfold DefectBoundedAt DefectExceeds
  push_neg
  rfl

-- ════════════════════════════════════════════════════════════
-- Section 12: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms GradedReflModel.gap
#print axioms GradedReflModel.DefectBoundedAt
#print axioms GradedReflModel.DefectBounded
#print axioms GradedReflModel.DefectExceeds
#print axioms GradedReflModel.defectBounded_iff_drift
#print axioms GradedReflModel.defectBoundedAt_all_iff_defectBounded
#print axioms GradedReflModel.finiteDrift_iff_defect_bounded
#print axioms GradedReflModel.unboundedGap_iff_defect_unbounded
#print axioms GradedReflModel.defectBounded_zero_iff_strict
#print axioms GradedReflModel.defectBoundedAt_mono_d
#print axioms GradedReflModel.defectBounded_mono
#print axioms GradedReflModel.defectExceeds_anti_k
#print axioms GradedReflModel.defectExceeds_mono_d
#print axioms GradedReflModel.defectBoundedAt_mono_k
#print axioms GradedReflModel.defectBounded_not_exceeds
#print axioms GradedReflModel.defectBoundedAt_not_exceeds
#print axioms BoundedGRMEquiv.defectBounded_transport
#print axioms BoundedGRMEquiv.defectBounded_transport_g
#print axioms BoundedGRMEquiv.defect_finiteness_iff
#print axioms BoundedGRMEquiv.defectExceeds_transport
#print axioms BoundedGRMEquiv.defectExceeds_transport_g
#print axioms BoundedGRMEquiv.toDefectEquivalent
#print axioms defectEquivalent_refl
#print axioms defectEquivalent_symm
#print axioms defectEquivalent_trans
#print axioms defectEquivalent_mono
#print axioms standardModel_defect_unbounded
#print axioms trivialModel_defect_zero
#print axioms trivialModel_defectBoundedAt_zero
#print axioms GradedReflModel.gap_eq_zero_of_fixed
#print axioms GradedReflModel.gap_le_of_defectBounded
#print axioms GradedReflModel.defectExceeds_of_gap_gt
#print axioms ProtocolGRM.defect_bounded
#print axioms ProtocolGRM.admits_drift_from_defect
#print axioms GradedReflModel.not_defectBounded_iff
#print axioms GradedReflModel.not_defectBoundedAt_iff

end WTS
