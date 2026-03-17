/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/ReencodingInvariance.lean — Encoding
invariance for the carrier engineering obstruction.

A BoundedGRMEquiv is a bijection between two GRMs with bounded additive
grade distortion and selfApp compatibility. Under such an equivalence:

  - The additive gap shifts by at most 2 * overhead (core distortion lemma)
  - Drift-compatible extensions transport: drift k in M gives drift
    k + 2*overhead in M' (and vice versa)
  - Finite drift existence is invariant (the admissible drift set shifts
    but its emptiness/non-emptiness is stable)
  - UnboundedGap is invariant: no admissible re-encoding can collapse
    an infinite naming obstruction into a finite one
  - The canonical fixed-point subdomain transfers: Fix(selfApp_M) ≃ Fix(selfApp_M')
  - BoundedGRMEquiv forms a groupoid-like structure: refl (overhead 0),
    symm (same overhead), trans (additive overhead c₁ + c₂)
  - Overhead accumulates additively under composition
  - All invariance results lift to chains via trans

What does NOT transfer cleanly under positive overhead:
  - Exact SelfAppUnbounded (threshold overflow can be absorbed by overhead)
  - Exact PEqNP threshold (only shifted versions transfer)
  - Strict extension (drift 0 can become drift 2*overhead)

The encoding-invariant separation claim is therefore:
  "Changing admissible encoding can shift thresholds by a bounded amount,
   but cannot collapse an infinite naming obstruction into a finite one."

STATUS: 0 sorry.
-/

import WTS.Tower.CarrierEngineering.ReflectiveCarrierData

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: The bounded equivalence structure
-- ════════════════════════════════════════════════════════════

/-- A bounded grade-distorted equivalence between two GRMs.
    The carrier bijection (f/g) commutes with selfApp and distorts
    grade by at most `overhead` in each direction.

    This captures "admissible re-encoding": the same objects measured
    by a different but commensurable resource grade.

    From gf/fg + f_bounded/g_bounded, grade sandwiches are derivable:
      M.grade x - overhead ≤ M'.grade (f x) ≤ M.grade x + overhead
      M'.grade x' - overhead ≤ M.grade (g x') ≤ M'.grade x' + overhead

    From f_compat + gf + fg, g_compat is derivable. -/
structure BoundedGRMEquiv (M M' : GradedReflModel) where
  /-- Forward translation. -/
  f : M.carrier → M'.carrier
  /-- Backward translation. -/
  g : M'.carrier → M.carrier
  /-- g is left inverse of f. -/
  gf : ∀ x, g (f x) = x
  /-- f is left inverse of g (full bijection). -/
  fg : ∀ x', f (g x') = x'
  /-- Maximum additive grade distortion. -/
  overhead : Nat
  /-- f has bounded additive overhead on grade. -/
  f_bounded : ∀ x, M'.grade (f x) ≤ M.grade x + overhead
  /-- g has bounded additive overhead on grade. -/
  g_bounded : ∀ x', M.grade (g x') ≤ M'.grade x' + overhead
  /-- f commutes with selfApp. -/
  f_compat : ∀ x, M'.selfApp (f x) = f (M.selfApp x)

-- ════════════════════════════════════════════════════════════
-- Section 2: Derived properties
-- ════════════════════════════════════════════════════════════

/-- g commutes with selfApp (derived from f_compat + gf + fg). -/
theorem BoundedGRMEquiv.g_compat {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    ∀ x', M.selfApp (E.g x') = E.g (M'.selfApp x') := by
  intro x'
  -- From f_compat at g(x'): M'.selfApp (f (g x')) = f (M.selfApp (g x'))
  -- By fg: M'.selfApp x' = f (M.selfApp (g x'))
  -- Apply g: g (M'.selfApp x') = g (f (M.selfApp (g x'))) = M.selfApp (g x')
  have h := E.f_compat (E.g x')
  rw [E.fg] at h
  -- h : M'.selfApp x' = f (M.selfApp (g x'))
  calc M.selfApp (E.g x')
      = E.g (E.f (M.selfApp (E.g x'))) := (E.gf _).symm
    _ = E.g (M'.selfApp x') := by rw [← h]

/-- Grade lower bound for f: grade doesn't compress too much.
    Derived from g_bounded + gf. -/
theorem BoundedGRMEquiv.f_lower {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    ∀ x, M.grade x ≤ M'.grade (E.f x) + E.overhead := by
  intro x
  have h := E.g_bounded (E.f x)
  rw [E.gf] at h
  exact h

/-- Grade lower bound for g: grade doesn't compress too much.
    Derived from f_bounded + fg. -/
theorem BoundedGRMEquiv.g_lower {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    ∀ x', M'.grade x' ≤ M.grade (E.g x') + E.overhead := by
  intro x'
  have h := E.f_bounded (E.g x')
  rw [E.fg] at h
  exact h

-- ════════════════════════════════════════════════════════════
-- Section 3: The core gap-distortion lemma
-- ════════════════════════════════════════════════════════════

/-- THE GAP-DISTORTION LEMMA.

    Under a bounded equivalence with overhead c, the additive gap
    between grade(selfApp(x)) and grade(x) shifts by at most 2c
    when transported through f.

    Concretely: if the gap at x in M exceeds k + 2c, then the gap
    at f(x) in M' exceeds k. This is the engine for all invariance
    theorems — drift transport and UnboundedGap are direct corollaries. -/
theorem BoundedGRMEquiv.gap_distortion {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (x : M.carrier) (k : Nat)
    (h : M.grade (M.selfApp x) > M.grade x + (k + 2 * E.overhead)) :
    M'.grade (M'.selfApp (E.f x)) > M'.grade (E.f x) + k := by
  rw [E.f_compat]
  have h_upper := E.f_bounded x
  have h_lower := E.f_lower (M.selfApp x)
  omega

/-- Symmetric gap-distortion: transporting through g. -/
theorem BoundedGRMEquiv.gap_distortion_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (x' : M'.carrier) (k : Nat)
    (h : M'.grade (M'.selfApp x') > M'.grade x' + (k + 2 * E.overhead)) :
    M.grade (M.selfApp (E.g x')) > M.grade (E.g x') + k := by
  rw [E.g_compat]
  have h_upper := E.g_bounded x'
  have h_lower := E.g_lower (M'.selfApp x')
  omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Drift transport
-- ════════════════════════════════════════════════════════════

/-- Drift transport (M → M'): if selfApp in M has drift at most k,
    then selfApp in M' has drift at most k + 2 * overhead. -/
theorem BoundedGRMEquiv.drift_transport {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M')
    (k : Nat) (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    ∀ x', M'.grade (M'.selfApp x') ≤ M'.grade x' + (k + 2 * E.overhead) := by
  intro x'
  -- selfApp'(x') = f(selfApp(g(x'))) by f_compat + fg
  have hcompat : M'.selfApp x' = E.f (M.selfApp (E.g x')) := by
    rw [← E.f_compat, E.fg]
  rw [hcompat]
  -- h1: grade'(f(selfApp(g(x')))) ≤ grade(selfApp(g(x'))) + c
  -- h2: grade(g(x')) ≤ grade'(x') + c
  -- h3: grade(selfApp(g(x'))) ≤ grade(g(x')) + k
  -- Chain: c ≤ (d+k) + c ≤ ((e+c)+k) + c = e + k + 2c ✓
  have h1 := E.f_bounded (M.selfApp (E.g x'))
  have h2 := E.g_bounded x'
  have h3 := h (E.g x')
  omega

/-- Drift transport (M' → M): symmetric direction. -/
theorem BoundedGRMEquiv.drift_transport_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M')
    (k : Nat) (h : ∀ x', M'.grade (M'.selfApp x') ≤ M'.grade x' + k) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x + (k + 2 * E.overhead) := by
  intro x
  have hcompat : M.selfApp x = E.g (M'.selfApp (E.f x)) := by
    rw [← E.g_compat, E.gf]
  rw [hcompat]
  have h1 := E.g_bounded (M'.selfApp (E.f x))
  have h2 := E.f_bounded x
  have h3 := h (E.f x)
  omega

/-- Drift extension transport (M → M'): a drift-k extension of M
    gives a drift-(k + 2c) extension of M'. -/
theorem BoundedGRMEquiv.drift_extension_transport {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) :
    Nonempty (M.DriftCompatibleExtension k) →
    Nonempty (M'.DriftCompatibleExtension (k + 2 * E.overhead)) := by
  rw [GradedReflModel.drift_extension_iff, GradedReflModel.drift_extension_iff]
  exact E.drift_transport k

/-- Drift extension transport (M' → M): symmetric direction. -/
theorem BoundedGRMEquiv.drift_extension_transport_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat) :
    Nonempty (M'.DriftCompatibleExtension k) →
    Nonempty (M.DriftCompatibleExtension (k + 2 * E.overhead)) := by
  rw [GradedReflModel.drift_extension_iff, GradedReflModel.drift_extension_iff]
  exact E.drift_transport_g k

-- ════════════════════════════════════════════════════════════
-- Section 5: UnboundedGap invariance
-- ════════════════════════════════════════════════════════════

/-- UnboundedGap is encoding-invariant (M → M').
    If M has arbitrarily large additive gap, so does M'.
    The 2c deficit from re-encoding is absorbed by choosing a
    larger gap witness in M. -/
theorem BoundedGRMEquiv.unboundedGap_transfer {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    M.UnboundedGap → M'.UnboundedGap := by
  intro h k'
  -- Choose k = k' + 2c in M to absorb the distortion
  obtain ⟨x, hgap⟩ := h (k' + 2 * E.overhead)
  exact ⟨E.f x, E.gap_distortion x k' hgap⟩

/-- UnboundedGap is encoding-invariant (M' → M): symmetric direction. -/
theorem BoundedGRMEquiv.unboundedGap_transfer_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    M'.UnboundedGap → M.UnboundedGap := by
  intro h k
  obtain ⟨x', hgap⟩ := h (k + 2 * E.overhead)
  exact ⟨E.g x', E.gap_distortion_g x' k hgap⟩

/-- THE ENCODING-INVARIANCE THEOREM FOR UNBOUNDED GAP.

    UnboundedGap is equivalent across any bounded GRM equivalence.
    No admissible re-encoding can collapse an infinite naming
    obstruction into a finite one. -/
theorem BoundedGRMEquiv.unboundedGap_iff {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    M.UnboundedGap ↔ M'.UnboundedGap :=
  ⟨E.unboundedGap_transfer, E.unboundedGap_transfer_g⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Finite drift existence invariance
-- ════════════════════════════════════════════════════════════

/-- Finite drift existence is encoding-invariant (M → M').
    If M admits some finite drift, so does M'. -/
theorem BoundedGRMEquiv.finite_drift_transfer {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    (∃ k, Nonempty (M.DriftCompatibleExtension k)) →
    (∃ k, Nonempty (M'.DriftCompatibleExtension k)) :=
  fun ⟨k, hk⟩ => ⟨k + 2 * E.overhead, E.drift_extension_transport k hk⟩

/-- Finite drift existence is encoding-invariant (M' → M). -/
theorem BoundedGRMEquiv.finite_drift_transfer_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    (∃ k, Nonempty (M'.DriftCompatibleExtension k)) →
    (∃ k, Nonempty (M.DriftCompatibleExtension k)) :=
  fun ⟨k, hk⟩ => ⟨k + 2 * E.overhead, E.drift_extension_transport_g k hk⟩

/-- THE ENCODING-INVARIANCE THEOREM FOR FINITE DRIFT EXISTENCE.

    Whether any finite-drift naming layer exists is invariant across
    bounded GRM equivalence. Combined with unboundedGap_iff, this gives:
    "changing admissible encoding can shift thresholds by a bounded amount,
    but cannot collapse an infinite naming obstruction into a finite one." -/
theorem BoundedGRMEquiv.finite_drift_iff {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') :
    (∃ k, Nonempty (M.DriftCompatibleExtension k)) ↔
    (∃ k, Nonempty (M'.DriftCompatibleExtension k)) :=
  ⟨E.finite_drift_transfer, E.finite_drift_transfer_g⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Fixed-point subdomain equivalence
-- ════════════════════════════════════════════════════════════

/-- f maps fixed points of selfApp_M to fixed points of selfApp_M'. -/
theorem BoundedGRMEquiv.f_preserves_fixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (x : M.carrier)
    (hfix : M.selfApp x = x) :
    M'.selfApp (E.f x) = E.f x := by
  rw [E.f_compat, hfix]

/-- g maps fixed points of selfApp_M' to fixed points of selfApp_M. -/
theorem BoundedGRMEquiv.g_preserves_fixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (x' : M'.carrier)
    (hfix : M'.selfApp x' = x') :
    M.selfApp (E.g x') = E.g x' := by
  rw [E.g_compat, hfix]

/-- f restricts to fixed-point subtypes. -/
def BoundedGRMEquiv.fFixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (c : { x : M.carrier // M.selfApp x = x }) :
    { x : M'.carrier // M'.selfApp x = x } :=
  ⟨E.f c.val, E.f_preserves_fixed c.val c.property⟩

/-- g restricts to fixed-point subtypes. -/
def BoundedGRMEquiv.gFixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (c' : { x : M'.carrier // M'.selfApp x = x }) :
    { x : M.carrier // M.selfApp x = x } :=
  ⟨E.g c'.val, E.g_preserves_fixed c'.val c'.property⟩

/-- The fixed-point restrictions are inverse: g(f(c)) = c on subtypes. -/
theorem BoundedGRMEquiv.gFixed_fFixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (c : { x : M.carrier // M.selfApp x = x }) :
    E.gFixed (E.fFixed c) = c := by
  exact Subtype.ext (E.gf c.val)

/-- The fixed-point restrictions are inverse: f(g(c')) = c' on subtypes. -/
theorem BoundedGRMEquiv.fFixed_gFixed {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (c' : { x : M'.carrier // M'.selfApp x = x }) :
    E.fFixed (E.gFixed c') = c' := by
  exact Subtype.ext (E.fg c'.val)

/-- f intertwines the canonicalizers of M and M'. -/
theorem BoundedGRMEquiv.f_intertwines_canonicalize {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (x : M.carrier) :
    E.f (M.selfApp x) = M'.selfApp (E.f x) :=
  (E.f_compat x).symm

-- ════════════════════════════════════════════════════════════
-- Section 8: Composition / functoriality
-- ════════════════════════════════════════════════════════════

/-- Identity equivalence: every GRM is boundedly equivalent to itself with overhead 0. -/
def BoundedGRMEquiv.refl (M : GradedReflModel) : BoundedGRMEquiv M M where
  f := id
  g := id
  gf _ := rfl
  fg _ := rfl
  overhead := 0
  f_bounded x := by simp
  g_bounded x := by simp
  f_compat _ := rfl

/-- Symmetric equivalence: swap f and g, same overhead. -/
def BoundedGRMEquiv.symm {M M' : GradedReflModel} (E : BoundedGRMEquiv M M') :
    BoundedGRMEquiv M' M where
  f := E.g
  g := E.f
  gf := E.fg
  fg := E.gf
  overhead := E.overhead
  f_bounded := E.g_bounded
  g_bounded := E.f_bounded
  f_compat := E.g_compat

/-- Composition: overheads add. If M ≃ M' with overhead c₁ and M' ≃ M''
    with overhead c₂, then M ≃ M'' with overhead c₁ + c₂. -/
def BoundedGRMEquiv.trans {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'') :
    BoundedGRMEquiv M M'' where
  f x := E₂.f (E₁.f x)
  g x := E₁.g (E₂.g x)
  gf x := by rw [E₂.gf, E₁.gf]
  fg x := by rw [E₁.fg, E₂.fg]
  overhead := E₁.overhead + E₂.overhead
  f_bounded x := by
    -- grade''(f₂(f₁(x))) ≤ grade'(f₁(x)) + c₂ ≤ (grade(x) + c₁) + c₂
    have h1 := E₁.f_bounded x
    have h2 := E₂.f_bounded (E₁.f x)
    omega
  g_bounded x := by
    have h1 := E₂.g_bounded x
    have h2 := E₁.g_bounded (E₂.g x)
    omega
  f_compat x := by
    -- M''.selfApp (f₂(f₁(x))) = f₂(M'.selfApp(f₁(x))) = f₂(f₁(M.selfApp(x)))
    rw [E₂.f_compat, E₁.f_compat]

/-- Overhead accumulates additively under composition. -/
theorem BoundedGRMEquiv.trans_overhead {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'') :
    (E₁.trans E₂).overhead = E₁.overhead + E₂.overhead := rfl

/-- Drift transport through a chain: drift k in M gives drift k + 2(c₁+c₂) in M''. -/
theorem BoundedGRMEquiv.trans_drift_transport {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'') (k : Nat) :
    Nonempty (M.DriftCompatibleExtension k) →
    Nonempty (M''.DriftCompatibleExtension (k + 2 * (E₁.overhead + E₂.overhead))) :=
  (E₁.trans E₂).drift_extension_transport k

/-- Composed fixed-point map: f₂ ∘ f₁ on fixed-point subtypes. -/
def BoundedGRMEquiv.trans_fFixed {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'')
    (c : { x : M.carrier // M.selfApp x = x }) :
    { x : M''.carrier // M''.selfApp x = x } :=
  E₂.fFixed (E₁.fFixed c)

/-- The composed fixed-point map agrees with the transitive equivalence's fFixed. -/
theorem BoundedGRMEquiv.trans_fFixed_eq {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'')
    (c : { x : M.carrier // M.selfApp x = x }) :
    (E₁.trans E₂).fFixed c = E₁.trans_fFixed E₂ c := by
  exact Subtype.ext rfl

/-- UnboundedGap is invariant across any finite chain of bounded equivalences.
    (Follows from transitivity + unboundedGap_iff, stated for convenience.) -/
theorem BoundedGRMEquiv.unboundedGap_chain {M M' M'' : GradedReflModel}
    (E₁ : BoundedGRMEquiv M M') (E₂ : BoundedGRMEquiv M' M'') :
    M.UnboundedGap ↔ M''.UnboundedGap :=
  (E₁.trans E₂).unboundedGap_iff

-- ════════════════════════════════════════════════════════════
-- Section 9: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms BoundedGRMEquiv.g_compat
#print axioms BoundedGRMEquiv.f_lower
#print axioms BoundedGRMEquiv.g_lower
#print axioms BoundedGRMEquiv.gap_distortion
#print axioms BoundedGRMEquiv.gap_distortion_g
#print axioms BoundedGRMEquiv.drift_transport
#print axioms BoundedGRMEquiv.drift_transport_g
#print axioms BoundedGRMEquiv.drift_extension_transport
#print axioms BoundedGRMEquiv.drift_extension_transport_g
#print axioms BoundedGRMEquiv.unboundedGap_transfer
#print axioms BoundedGRMEquiv.unboundedGap_transfer_g
#print axioms BoundedGRMEquiv.unboundedGap_iff
#print axioms BoundedGRMEquiv.finite_drift_transfer
#print axioms BoundedGRMEquiv.finite_drift_transfer_g
#print axioms BoundedGRMEquiv.finite_drift_iff
#print axioms BoundedGRMEquiv.f_preserves_fixed
#print axioms BoundedGRMEquiv.g_preserves_fixed
#print axioms BoundedGRMEquiv.fFixed
#print axioms BoundedGRMEquiv.gFixed
#print axioms BoundedGRMEquiv.gFixed_fFixed
#print axioms BoundedGRMEquiv.fFixed_gFixed
#print axioms BoundedGRMEquiv.f_intertwines_canonicalize
#print axioms BoundedGRMEquiv.refl
#print axioms BoundedGRMEquiv.symm
#print axioms BoundedGRMEquiv.trans
#print axioms BoundedGRMEquiv.trans_overhead
#print axioms BoundedGRMEquiv.trans_drift_transport
#print axioms BoundedGRMEquiv.trans_fFixed
#print axioms BoundedGRMEquiv.trans_fFixed_eq
#print axioms BoundedGRMEquiv.unboundedGap_chain

end WTS
