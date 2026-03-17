/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/LeastDrift.lean — The least admissible
drift as a quantitative invariant, stable under bounded reencoding.

The admissible drift set { k | AdmitsDrift M k } is upward-closed and
its emptiness is encoding-invariant (ReencodingInvariance.lean). But
the qualitative question "does finite drift exist?" leaves open the
quantitative one: "how much naming loss does this model minimally
require?" This file extracts that number and proves it is stable up
to additive constants under BoundedGRMEquiv.

Key results:
  - IsLeastDrift k: predicate for the minimal admissible drift
  - exists_least_drift: FiniteDrift → ∃ k, IsLeastDrift k (well-ordering)
  - isLeastDrift_unique: the least drift is unique
  - leastDrift_upper_bound: THE STABILITY THEOREM —
      |minDrift(M) - minDrift(M')| ≤ 2 * overhead under BoundedGRMEquiv
  - Concrete witnesses: trivialModel has least drift 0,
      standardModel has no least drift
  - Protocol bound: ProtocolGRM least drift ≤ 2 * transportOverhead
  - Connection to DefectBounded: IsLeastDrift via defect language

STATUS: 0 sorry.
-/

import WTS.Tower.CarrierEngineering.DefectSpectrum

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The IsLeastDrift predicate
-- ════════════════════════════════════════════════════════════

/-- k is the least drift admitted by M: M admits drift k but does not
    admit any drift j < k. Equivalently: selfApp increases grade by
    at most k everywhere, and for every j < k there exists some x
    where selfApp increases grade by more than j. -/
def GradedReflModel.IsLeastDrift (M : GradedReflModel) (k : Nat) : Prop :=
  M.AdmitsDrift k ∧ ∀ j, j < k → ¬M.AdmitsDrift j

-- ════════════════════════════════════════════════════════════
-- Section 2: Existence and uniqueness of least drift
-- ════════════════════════════════════════════════════════════

/-- If M has finite drift, it has a least drift.
    By well-ordering of Nat: among all k with AdmitsDrift k,
    there is a smallest. Uses classical logic (already present
    in the reverse direction of finiteDrift_iff_not_unboundedGap). -/
theorem GradedReflModel.exists_least_drift (M : GradedReflModel)
    (h : M.FiniteDrift) : ∃ k, M.IsLeastDrift k := by
  -- h : ∃ k, M.AdmitsDrift k
  -- We prove: ∃ k, AdmitsDrift k ∧ ∀ j < k, ¬AdmitsDrift j
  -- by strong induction on the witness
  obtain ⟨n, hn⟩ := h
  -- Strong induction: for each n, if AdmitsDrift n then ∃ k ≤ n, IsLeastDrift k
  suffices ∀ m, M.AdmitsDrift m → ∃ k, M.IsLeastDrift k from this n hn
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h0 : ∀ j, j < m → ¬M.AdmitsDrift j
    · -- m itself is the least
      exact ⟨m, hm, h0⟩
    · -- Some j < m also admits drift; recurse
      push_neg at h0
      obtain ⟨j, hjm, hj⟩ := h0
      exact ih j hjm hj

/-- The least drift is unique: if k₁ and k₂ are both least drifts of M,
    then k₁ = k₂. -/
theorem GradedReflModel.isLeastDrift_unique (M : GradedReflModel) {k₁ k₂ : Nat}
    (h₁ : M.IsLeastDrift k₁) (h₂ : M.IsLeastDrift k₂) : k₁ = k₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- k₁ < k₂: but h₂ says ¬AdmitsDrift k₁, contradicting h₁
    exact h₂.2 k₁ hlt h₁.1
  · -- k₂ < k₁: symmetric
    exact h₁.2 k₂ hgt h₂.1

/-- FiniteDrift ↔ ∃ least drift. The forward direction is exists_least_drift;
    the reverse is immediate since IsLeastDrift implies AdmitsDrift. -/
theorem GradedReflModel.finiteDrift_iff_exists_leastDrift (M : GradedReflModel) :
    M.FiniteDrift ↔ ∃ k, M.IsLeastDrift k := by
  constructor
  · exact M.exists_least_drift
  · intro ⟨k, hk, _⟩; exact ⟨k, hk⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: Noncomputable extraction via Nat.find
-- ════════════════════════════════════════════════════════════

/-- Extract the least drift as a natural number. Uses classical
    decidability to apply Nat.find. -/
noncomputable def GradedReflModel.minDrift (M : GradedReflModel) (h : M.FiniteDrift) : Nat :=
  @Nat.find (fun k => M.AdmitsDrift k) (fun _ => Classical.propDecidable _) h

/-- minDrift satisfies the AdmitsDrift predicate. -/
theorem GradedReflModel.minDrift_admitsDrift (M : GradedReflModel) (h : M.FiniteDrift) :
    M.AdmitsDrift (M.minDrift h) :=
  @Nat.find_spec (fun k => M.AdmitsDrift k) (fun _ => Classical.propDecidable _) h

/-- No drift below minDrift is admissible. -/
theorem GradedReflModel.minDrift_minimal (M : GradedReflModel) (h : M.FiniteDrift)
    {j : Nat} (hj : j < M.minDrift h) : ¬M.AdmitsDrift j :=
  @Nat.find_min (fun k => M.AdmitsDrift k) (fun _ => Classical.propDecidable _) h j hj

/-- minDrift is the least drift. -/
theorem GradedReflModel.minDrift_isLeastDrift (M : GradedReflModel) (h : M.FiniteDrift) :
    M.IsLeastDrift (M.minDrift h) :=
  ⟨M.minDrift_admitsDrift h, fun _ hj => M.minDrift_minimal h hj⟩

/-- IsLeastDrift k implies k = minDrift. -/
theorem GradedReflModel.isLeastDrift_eq_minDrift (M : GradedReflModel) (h : M.FiniteDrift)
    {k : Nat} (hk : M.IsLeastDrift k) : k = M.minDrift h :=
  M.isLeastDrift_unique hk (M.minDrift_isLeastDrift h)

-- ════════════════════════════════════════════════════════════
-- Section 4: Basic characterizations
-- ════════════════════════════════════════════════════════════

/-- Least drift 0 ↔ strict naming (grade-non-increasing selfApp).
    If the least drift is 0, nothing below 0 needs to be excluded. -/
theorem GradedReflModel.isLeastDrift_zero_iff (M : GradedReflModel) :
    M.IsLeastDrift 0 ↔ Nonempty M.GradeCompatibleExtension := by
  constructor
  · intro ⟨h, _⟩; exact M.admitsDrift_zero_iff.mp h
  · intro h; exact ⟨M.admitsDrift_zero_iff.mpr h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- IsLeastDrift k implies FiniteDrift. -/
theorem GradedReflModel.isLeastDrift_finiteDrift (M : GradedReflModel) {k : Nat}
    (hk : M.IsLeastDrift k) : M.FiniteDrift :=
  ⟨k, hk.1⟩

/-- IsLeastDrift k implies ¬UnboundedGap. -/
theorem GradedReflModel.isLeastDrift_not_unboundedGap (M : GradedReflModel) {k : Nat}
    (hk : M.IsLeastDrift k) : ¬M.UnboundedGap :=
  M.finiteDrift_iff_not_unboundedGap.mp (M.isLeastDrift_finiteDrift hk)

/-- UnboundedGap implies no least drift exists. -/
theorem GradedReflModel.unboundedGap_no_leastDrift (M : GradedReflModel)
    (h : M.UnboundedGap) : ¬∃ k, M.IsLeastDrift k := by
  intro ⟨k, hk⟩
  exact M.isLeastDrift_not_unboundedGap hk h

-- ════════════════════════════════════════════════════════════
-- Section 5: Connection to DefectBounded
-- ════════════════════════════════════════════════════════════

/-- IsLeastDrift k ↔ DefectBounded k ∧ ¬DefectBounded (k-1) (for k > 0),
    restated: DefectBounded k and for all j < k, ¬DefectBounded j. -/
theorem GradedReflModel.isLeastDrift_iff_defect (M : GradedReflModel) (k : Nat) :
    M.IsLeastDrift k ↔ M.DefectBounded k ∧ ∀ j, j < k → ¬M.DefectBounded j := by
  unfold IsLeastDrift
  constructor
  · intro ⟨hk, hmin⟩
    exact ⟨(M.defectBounded_iff_drift k).mpr hk,
           fun j hj => fun hd => hmin j hj ((M.defectBounded_iff_drift j).mp hd)⟩
  · intro ⟨hk, hmin⟩
    exact ⟨(M.defectBounded_iff_drift k).mp hk,
           fun j hj => fun hd => hmin j hj ((M.defectBounded_iff_drift j).mpr hd)⟩

/-- If the least drift is k > 0, there exists a witness where selfApp
    increases grade by more than k - 1. -/
theorem GradedReflModel.isLeastDrift_witness (M : GradedReflModel) {k : Nat}
    (hk : M.IsLeastDrift k) (hpos : 0 < k) :
    ∃ x, M.grade (M.selfApp x) > M.grade x + (k - 1) := by
  have hnotk : ¬M.AdmitsDrift (k - 1) := hk.2 (k - 1) (by omega)
  unfold AdmitsDrift at hnotk
  rw [M.drift_extension_iff] at hnotk
  push_neg at hnotk
  obtain ⟨x, hx⟩ := hnotk
  exact ⟨x, hx⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: THE STABILITY THEOREM
-- ════════════════════════════════════════════════════════════

/-- LEAST DRIFT UPPER BOUND UNDER REENCODING.

    If M has least drift k and M' has least drift k', then k' ≤ k + 2c
    where c is the overhead of the bounded equivalence.

    Proof: M admits drift k (by IsLeastDrift). By drift_extension_transport,
    M' admits drift k + 2c. Since k' is the least drift of M', k' ≤ k + 2c.

    This is one direction of the stability inequality. The other direction
    follows by symmetry (using the reverse transport). -/
theorem BoundedGRMEquiv.leastDrift_upper_bound {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k : Nat} (hk : M.IsLeastDrift k)
    {k' : Nat} (hk' : M'.IsLeastDrift k') :
    k' ≤ k + 2 * E.overhead := by
  -- M admits drift k
  have hadmit : M.AdmitsDrift k := hk.1
  -- Therefore M' admits drift k + 2c
  have hadmit' : M'.AdmitsDrift (k + 2 * E.overhead) :=
    E.drift_extension_transport k hadmit
  -- k' is the least drift of M', so k' ≤ k + 2c
  -- (upward closure: M' admits drift k + 2c, and AdmitsDrift is upward-closed,
  --  so if k' > k + 2c, M' would not admit drift k + 2c by minimality — contradiction)
  by_contra h
  push_neg at h
  -- h : k + 2 * E.overhead < k'
  -- So ¬AdmitsDrift M' (k + 2 * E.overhead) by minimality
  exact hk'.2 (k + 2 * E.overhead) h hadmit'

/-- LEAST DRIFT UPPER BOUND (REVERSE DIRECTION).

    The symmetric bound: k ≤ k' + 2c. Uses transport in the g direction. -/
theorem BoundedGRMEquiv.leastDrift_upper_bound_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k : Nat} (hk : M.IsLeastDrift k)
    {k' : Nat} (hk' : M'.IsLeastDrift k') :
    k ≤ k' + 2 * E.overhead := by
  have hadmit' : M'.AdmitsDrift k' := hk'.1
  have hadmit : M.AdmitsDrift (k' + 2 * E.overhead) :=
    E.drift_extension_transport_g k' hadmit'
  by_contra h
  push_neg at h
  exact hk.2 (k' + 2 * E.overhead) h hadmit

/-- THE STABILITY THEOREM FOR LEAST DRIFT.

    Under a bounded GRM equivalence with overhead c, the least drifts
    of M and M' differ by at most 2c in each direction:
      k' ≤ k + 2c  and  k ≤ k' + 2c

    Equivalently: |minDrift(M) - minDrift(M')| ≤ 2c (in truncated
    subtraction on Nat, both directions hold).

    This gives a quantitative invariant: the least drift is not just
    "exists or not" (encoding-invariant by finite_drift_iff) but a
    specific number stable up to additive 2c. -/
theorem BoundedGRMEquiv.leastDrift_stability {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k : Nat} (hk : M.IsLeastDrift k)
    {k' : Nat} (hk' : M'.IsLeastDrift k') :
    k' ≤ k + 2 * E.overhead ∧ k ≤ k' + 2 * E.overhead :=
  ⟨E.leastDrift_upper_bound hk hk', E.leastDrift_upper_bound_g hk hk'⟩

/-- Stability via minDrift: the extracted minimum drifts satisfy the
    stability bound. -/
theorem BoundedGRMEquiv.minDrift_stability {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (hM : M.FiniteDrift) (hM' : M'.FiniteDrift) :
    M'.minDrift hM' ≤ M.minDrift hM + 2 * E.overhead ∧
    M.minDrift hM ≤ M'.minDrift hM' + 2 * E.overhead :=
  E.leastDrift_stability (M.minDrift_isLeastDrift hM) (M'.minDrift_isLeastDrift hM')

-- ════════════════════════════════════════════════════════════
-- Section 7: Stability under composition
-- ════════════════════════════════════════════════════════════

/-- Stability through a chain: if M ≃ M' ≃ M'' with overheads c₁, c₂,
    then least drifts of M and M'' differ by at most 2(c₁ + c₂). -/
theorem BoundedGRMEquiv.leastDrift_stability_chain
    {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'')
    {k : Nat} (hk : M.IsLeastDrift k)
    {k'' : Nat} (hk'' : M''.IsLeastDrift k'') :
    k'' ≤ k + 2 * (E₁.overhead + E₂.overhead) ∧
    k ≤ k'' + 2 * (E₁.overhead + E₂.overhead) :=
  (E₁.trans E₂).leastDrift_stability hk hk''

-- ════════════════════════════════════════════════════════════
-- Section 8: Stability under identity and symmetry
-- ════════════════════════════════════════════════════════════

/-- Under the identity equivalence, least drifts are equal. -/
theorem BoundedGRMEquiv.leastDrift_refl {M : GradedReflModel}
    {k₁ k₂ : Nat} (hk₁ : M.IsLeastDrift k₁) (hk₂ : M.IsLeastDrift k₂) :
    k₁ = k₂ :=
  M.isLeastDrift_unique hk₁ hk₂

/-- Under a symmetric equivalence, the stability bound is the same. -/
theorem BoundedGRMEquiv.leastDrift_stability_symm {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k : Nat} (hk : M.IsLeastDrift k)
    {k' : Nat} (hk' : M'.IsLeastDrift k') :
    k ≤ k' + 2 * E.overhead ∧ k' ≤ k + 2 * E.overhead :=
  E.symm.leastDrift_stability hk' hk

-- ════════════════════════════════════════════════════════════
-- Section 9: Concrete witnesses
-- ════════════════════════════════════════════════════════════

/-- trivialModel has least drift 0: selfApp = id is grade-non-increasing,
    and nothing below 0 needs to be excluded. -/
theorem trivialModel_isLeastDrift_zero : trivialModel.IsLeastDrift 0 := by
  constructor
  · -- AdmitsDrift 0 via DefectBounded 0
    exact (trivialModel.defectBounded_iff_drift 0).mp trivialModel_defect_zero
  · -- No j < 0
    intro j hj; exact absurd hj (Nat.not_lt_zero j)

/-- standardModel has no least drift: it has UnboundedGap, so no
    finite drift exists. -/
theorem standardModel_no_least_drift : ¬∃ k, standardModel.IsLeastDrift k :=
  standardModel.unboundedGap_no_leastDrift standardModel_unboundedGap

-- ════════════════════════════════════════════════════════════
-- Section 10: Protocol GRM least drift bound
-- ════════════════════════════════════════════════════════════

/-- Every ProtocolGRM has finite drift (from selfApp_constant_overhead). -/
theorem ProtocolGRM.finiteDrift (P : ProtocolGRM) : P.toGRM.FiniteDrift :=
  ⟨2 * P.sys.transportOverhead, P.admits_drift_from_defect⟩

/-- If a ProtocolGRM has a least drift, it is at most 2 * transportOverhead.
    The protocol overhead bounds the least drift from above. -/
theorem ProtocolGRM.leastDrift_le (P : ProtocolGRM) {k : Nat}
    (hk : P.toGRM.IsLeastDrift k) : k ≤ 2 * P.sys.transportOverhead := by
  -- P.toGRM admits drift 2 * overhead
  have hadmit : P.toGRM.AdmitsDrift (2 * P.sys.transportOverhead) :=
    P.admits_drift_from_defect
  -- k is the least drift, so k ≤ 2 * overhead
  by_contra h
  push_neg at h
  exact hk.2 (2 * P.sys.transportOverhead) h hadmit

/-- Combined: every ProtocolGRM has a least drift bounded by 2 * overhead. -/
theorem ProtocolGRM.exists_leastDrift_bounded (P : ProtocolGRM) :
    ∃ k, P.toGRM.IsLeastDrift k ∧ k ≤ 2 * P.sys.transportOverhead := by
  obtain ⟨k, hk⟩ := P.toGRM.exists_least_drift P.finiteDrift
  exact ⟨k, hk, P.leastDrift_le hk⟩

-- ════════════════════════════════════════════════════════════
-- Section 11: Least drift monotonicity under stronger equivalences
-- ════════════════════════════════════════════════════════════

/-- Zero-overhead equivalence preserves least drift exactly.
    If the overhead is 0, then M and M' have the same least drift. -/
theorem BoundedGRMEquiv.leastDrift_eq_of_zero_overhead {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (h0 : E.overhead = 0)
    {k : Nat} (hk : M.IsLeastDrift k) {k' : Nat} (hk' : M'.IsLeastDrift k') :
    k = k' := by
  have ⟨h1, h2⟩ := E.leastDrift_stability hk hk'
  rw [h0] at h1 h2; omega

/-- If M has least drift k and E has overhead c, then M' admits drift k + 2c. -/
theorem BoundedGRMEquiv.leastDrift_gives_admitsDrift {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') {k : Nat} (hk : M.IsLeastDrift k) :
    M'.AdmitsDrift (k + 2 * E.overhead) :=
  E.drift_extension_transport k hk.1

-- ════════════════════════════════════════════════════════════
-- Section 12: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms GradedReflModel.IsLeastDrift
#print axioms GradedReflModel.exists_least_drift
#print axioms GradedReflModel.isLeastDrift_unique
#print axioms GradedReflModel.finiteDrift_iff_exists_leastDrift
#print axioms GradedReflModel.minDrift
#print axioms GradedReflModel.minDrift_admitsDrift
#print axioms GradedReflModel.minDrift_minimal
#print axioms GradedReflModel.minDrift_isLeastDrift
#print axioms GradedReflModel.isLeastDrift_eq_minDrift
#print axioms GradedReflModel.isLeastDrift_zero_iff
#print axioms GradedReflModel.isLeastDrift_finiteDrift
#print axioms GradedReflModel.isLeastDrift_not_unboundedGap
#print axioms GradedReflModel.unboundedGap_no_leastDrift
#print axioms GradedReflModel.isLeastDrift_iff_defect
#print axioms GradedReflModel.isLeastDrift_witness
#print axioms BoundedGRMEquiv.leastDrift_upper_bound
#print axioms BoundedGRMEquiv.leastDrift_upper_bound_g
#print axioms BoundedGRMEquiv.leastDrift_stability
#print axioms BoundedGRMEquiv.minDrift_stability
#print axioms BoundedGRMEquiv.leastDrift_stability_chain
#print axioms BoundedGRMEquiv.leastDrift_refl
#print axioms BoundedGRMEquiv.leastDrift_stability_symm
#print axioms trivialModel_isLeastDrift_zero
#print axioms standardModel_no_least_drift
#print axioms ProtocolGRM.finiteDrift
#print axioms ProtocolGRM.leastDrift_le
#print axioms ProtocolGRM.exists_leastDrift_bounded
#print axioms BoundedGRMEquiv.leastDrift_eq_of_zero_overhead
#print axioms BoundedGRMEquiv.leastDrift_gives_admitsDrift

end WTS
