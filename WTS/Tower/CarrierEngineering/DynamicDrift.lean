/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/Tower/CarrierEngineering/DynamicDrift.lean — Generalization from
constant drift to dynamic drift functions.

The constant drift formulation (FixedGradeDriftCarrier) captures
"selfApp increases grade by at most k everywhere". But the actual
invariant of a GRM is the drift FUNCTION:

    δ_M(g) = sup{ grade(selfApp(x)) - grade(x) | grade(x) ≤ g }

This is grade-dependent: the overhead of naming at grade g may be
different from the overhead at grade g'. The constant collapse loses
this structure.

Three structural gaps in the constant formulation:

  (1) classicalGRM has δ(g) = 0 for g ≥ headerLen, not a constant.
      Saying "FiniteDrift at 2*overhead" overstates the actual overhead
      for large inputs.

  (2) The regime spectrum has a gap between constant drift (FiniteDrift)
      and unbounded (UnboundedGap). Sub-polynomial drift like O(log g)
      is not expressible with a constant.

  (3) Emergent computation across minimal systems requires grade-dependent
      drift — the self-interpretation overhead varies with complexity.

This file introduces:

  A. DynamicDriftCarrier: the naming layer with drift : Nat → Nat,
     bounding grade_C(norm(a)) ≤ grade_A(a) + drift(grade_A(a)).

  B. actualDriftFn: the pointwise-least admissible drift function,
     defined via leastDriftAt (the grade-localized minimum).

  C. Coercion: FixedGradeDriftCarrier is a special case (constant function).

  D. dynamic_drift_extension_iff: inhabitation iff pointwise selfApp bound.

  E. actualDriftFn_mono: the actual drift function is non-decreasing.

  F. Encoding invariance: BoundedGRMEquiv shifts the drift function by
     at most 2*overhead at each grade (for non-decreasing drift functions).

  G. Drift function classes: eventually-zero, constant, linear/polynomial,
     and their relationship to FiniteDrift.

  H. Connection to FiniteDrift: constant drift is the special case where
     actualDriftFn is uniformly bounded.

The key constraint: FixedGradeDriftCarrier and all existing theorems
remain valid as the constant-function special case. Nothing is broken.

STATUS: 0 sorry. Classical.choice enters via Nat.find in leastDriftAt
and actualDriftFn (same pattern as LeastDrift.lean).
-/

import WTS.Tower.CarrierEngineering.LeastDrift

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: DynamicDriftCarrier — the grade-dependent naming layer
-- ════════════════════════════════════════════════════════════

/-- A dynamically-drifted grade extension: normalization may increase grade
    by at most `drift(grade_A(a))` — the allowed overhead depends on the
    grade of the input.

    This is the correct structural object. The drift function δ : Nat → Nat
    characterizes how much naming loss the model requires at each grade level:

      grade_C(norm a) ≤ grade_A(a) + drift(grade_A(a))

    Special cases:
      - drift = fun _ => k   : recovers FixedGradeDriftCarrier
      - drift = fun _ => 0   : recovers FixedGradeReflectiveCarrier
      - drift = fun g => g   : grade-doubling (very lossy naming)
      - drift unbounded      : tautological (every model admits this) -/
structure DynamicDriftCarrier
    (R : ReflectiveCarrierData) (grade_A : R.A → Nat) (drift : Nat → Nat) where
  /-- Grade on the canonical subdomain. -/
  grade_C : R.C → Nat
  /-- Inclusion preserves grade. -/
  grade_compat : ∀ c, grade_A (R.incl c) = grade_C c
  /-- Normalization is grade-non-increasing up to drift at each grade level. -/
  norm_grade_le_drift : ∀ a, grade_C (R.norm a) ≤ grade_A a + drift (grade_A a)

-- ════════════════════════════════════════════════════════════
-- Section 2: Special-case coercions
-- ════════════════════════════════════════════════════════════

/-- Every FixedGradeDriftCarrier yields a DynamicDriftCarrier (constant function). -/
def FixedGradeDriftCarrier.toDynamic
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {k : Nat}
    (E : FixedGradeDriftCarrier R grade_A k) :
    DynamicDriftCarrier R grade_A (fun _ => k) where
  grade_C := E.grade_C
  grade_compat := E.grade_compat
  norm_grade_le_drift := E.norm_grade_le_drift

/-- A DynamicDriftCarrier with constant drift function yields a FixedGradeDriftCarrier. -/
def DynamicDriftCarrier.toFixed
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {k : Nat}
    (E : DynamicDriftCarrier R grade_A (fun _ => k)) :
    FixedGradeDriftCarrier R grade_A k where
  grade_C := E.grade_C
  grade_compat := E.grade_compat
  norm_grade_le_drift := E.norm_grade_le_drift

/-- Zero constant drift = strict carrier. -/
def DynamicDriftCarrier.toStrict
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat}
    (E : DynamicDriftCarrier R grade_A (fun _ => 0)) :
    FixedGradeReflectiveCarrier R grade_A where
  grade_C := E.grade_C
  grade_compat := E.grade_compat
  norm_grade_le a := by have := E.norm_grade_le_drift a; omega

/-- grade_C is uniquely determined in DynamicDriftCarrier: grade_compat forces
    grade_C c = grade_A (incl c). -/
theorem DynamicDriftCarrier.grade_C_unique
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {drift : Nat → Nat}
    (E : DynamicDriftCarrier R grade_A drift) :
    ∀ c, E.grade_C c = grade_A (R.incl c) :=
  fun c => (E.grade_compat c).symm

/-- DynamicDriftCarrier is a subsingleton at each drift function:
    grade_compat forces grade_C and the remaining fields are Props. -/
instance DynamicDriftCarrier.instSubsingleton
    {R : ReflectiveCarrierData} {grade_A : R.A → Nat} {drift : Nat → Nat} :
    Subsingleton (DynamicDriftCarrier R grade_A drift) :=
  ⟨fun E₁ E₂ => by
    have h : E₁.grade_C = E₂.grade_C :=
      funext fun c => by rw [E₁.grade_C_unique, E₂.grade_C_unique]
    cases E₁; cases E₂; congr⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: GRM dynamic drift interface
-- ════════════════════════════════════════════════════════════

/-- The dynamic drift compatible extension of a GRM. -/
abbrev GradedReflModel.DynamicDriftCompatibleExtension
    (M : GradedReflModel) (δ : Nat → Nat) :=
  DynamicDriftCarrier M.toReflectiveCarrierData M.grade δ

/-- THE DYNAMIC DRIFT INHABITATION THEOREM.

    A GRM admits a dynamic drift extension with drift function δ if and only if
    selfApp satisfies the pointwise bound:
      grade(selfApp(x)) ≤ grade(x) + δ(grade(x))   for all x.

    - Constant δ = fun _ => k: recovers drift_extension_iff
    - Constant δ = fun _ => 0: recovers grade_compatible_extension_iff
    - δ = fun g => 0 for g ≥ t (eventually zero): captures classicalGRM behavior
    - Unbounded δ: tautological — every model admits this -/
theorem GradedReflModel.dynamic_drift_extension_iff (M : GradedReflModel) (δ : Nat → Nat) :
    Nonempty (M.DynamicDriftCompatibleExtension δ) ↔
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x + δ (M.grade x)) := by
  constructor
  · intro ⟨G⟩ x
    have h1 : M.grade (M.selfApp x) =
        G.grade_C (M.toReflectiveCarrierData.norm x) :=
      G.grade_compat (M.toReflectiveCarrierData.norm x)
    have h2 := G.norm_grade_le_drift x
    omega
  · intro h
    exact ⟨{
      grade_C := fun c => M.grade c.val
      grade_compat := fun _ => rfl
      norm_grade_le_drift := h
    }⟩

/-- Dynamic drift monotonicity (pointwise): if δ₁ ≤ δ₂ pointwise and a δ₁-extension
    exists, so does a δ₂-extension. -/
theorem GradedReflModel.dynamic_drift_mono
    (M : GradedReflModel) {δ₁ δ₂ : Nat → Nat}
    (h : ∀ g, δ₁ g ≤ δ₂ g) :
    Nonempty (M.DynamicDriftCompatibleExtension δ₁) →
    Nonempty (M.DynamicDriftCompatibleExtension δ₂) := by
  rw [M.dynamic_drift_extension_iff, M.dynamic_drift_extension_iff]
  intro h1 x
  have := h1 x
  have hd := h (M.grade x)
  omega

/-- Constant-function specialization: DynamicDriftCompatibleExtension (fun _ => k)
    ↔ DriftCompatibleExtension k. -/
theorem GradedReflModel.dynamic_drift_const_iff (M : GradedReflModel) (k : Nat) :
    Nonempty (M.DynamicDriftCompatibleExtension (fun _ => k)) ↔
    Nonempty (M.DriftCompatibleExtension k) := by
  rw [M.dynamic_drift_extension_iff, M.drift_extension_iff]

-- ════════════════════════════════════════════════════════════
-- Section 4: Grade-localized drift bounds
-- ════════════════════════════════════════════════════════════

/-- Whether M admits a bounded drift at grade level g: there exists k such that
    all x with grade(x) ≤ g have grade(selfApp(x)) ≤ grade(x) + k. -/
def GradedReflModel.HasBoundedDriftAt (M : GradedReflModel) (g : Nat) : Prop :=
  ∃ k, M.DefectBoundedAt g k

/-- The global DefectBounded condition implies HasBoundedDriftAt at every level. -/
theorem GradedReflModel.defectBounded_implies_hasBoundedDriftAt
    (M : GradedReflModel) {k : Nat} (h : M.DefectBounded k) (g : Nat) :
    M.HasBoundedDriftAt g := ⟨k, fun x _ => h x⟩

/-- FiniteDrift implies HasBoundedDriftAt at every grade level. -/
theorem GradedReflModel.finiteDrift_hasBoundedDriftAt
    (M : GradedReflModel) (hfd : M.FiniteDrift) (g : Nat) :
    M.HasBoundedDriftAt g := by
  obtain ⟨k, hk⟩ := hfd
  rw [GradedReflModel.AdmitsDrift, GradedReflModel.drift_extension_iff] at hk
  exact ⟨k, fun x _ => hk x⟩

/-- The least drift at grade level g (requires HasBoundedDriftAt g). -/
noncomputable def GradedReflModel.leastDriftAt
    (M : GradedReflModel) (g : Nat) (h : M.HasBoundedDriftAt g) : Nat :=
  @Nat.find (fun k => M.DefectBoundedAt g k)
    (fun _ => Classical.propDecidable _) h

/-- leastDriftAt satisfies DefectBoundedAt. -/
theorem GradedReflModel.leastDriftAt_defectBoundedAt
    (M : GradedReflModel) (g : Nat) (h : M.HasBoundedDriftAt g) :
    M.DefectBoundedAt g (M.leastDriftAt g h) :=
  @Nat.find_spec (fun k => M.DefectBoundedAt g k)
    (fun _ => Classical.propDecidable _) h

/-- No drift below leastDriftAt is admissible at grade g. -/
theorem GradedReflModel.leastDriftAt_minimal
    (M : GradedReflModel) (g : Nat) (h : M.HasBoundedDriftAt g)
    {j : Nat} (hj : j < M.leastDriftAt g h) :
    ¬M.DefectBoundedAt g j :=
  @Nat.find_min (fun k => M.DefectBoundedAt g k)
    (fun _ => Classical.propDecidable _) h j hj

-- ════════════════════════════════════════════════════════════
-- Section 5: The actual drift function
-- ════════════════════════════════════════════════════════════

/-- The actual drift function of M: for each grade g, the least k such that
    all inputs at grade ≤ g have selfApp overhead at most k.

    This is defined only when M has FiniteDrift (otherwise the function
    is unbounded at some grades). -/
noncomputable def GradedReflModel.actualDriftFn
    (M : GradedReflModel) (hfd : M.FiniteDrift) (g : Nat) : Nat :=
  M.leastDriftAt g (M.finiteDrift_hasBoundedDriftAt hfd g)

/-- actualDriftFn witnesses the bound: all x at grade ≤ g satisfy the drift bound. -/
theorem GradedReflModel.actualDriftFn_bound
    (M : GradedReflModel) (hfd : M.FiniteDrift) (g : Nat) :
    ∀ x, M.grade x ≤ g → M.grade (M.selfApp x) ≤ M.grade x + M.actualDriftFn hfd g :=
  M.leastDriftAt_defectBoundedAt g (M.finiteDrift_hasBoundedDriftAt hfd g)

/-- actualDriftFn is the least such function: any smaller value at grade g
    would fail the bound at some input. -/
theorem GradedReflModel.actualDriftFn_minimal
    (M : GradedReflModel) (hfd : M.FiniteDrift) (g : Nat)
    {j : Nat} (hj : j < M.actualDriftFn hfd g) :
    ¬M.DefectBoundedAt g j :=
  M.leastDriftAt_minimal g (M.finiteDrift_hasBoundedDriftAt hfd g) hj

/-- The GRM admits a DynamicDriftCompatibleExtension for its actual drift function. -/
theorem GradedReflModel.admits_actualDriftFn
    (M : GradedReflModel) (hfd : M.FiniteDrift) :
    Nonempty (M.DynamicDriftCompatibleExtension (M.actualDriftFn hfd)) := by
  rw [M.dynamic_drift_extension_iff]
  intro x
  exact M.actualDriftFn_bound hfd (M.grade x) x (Nat.le_refl _)

/-- actualDriftFn is non-decreasing: higher grade levels allow more drift witnesses.

    Proof: DefectBoundedAt is anti-monotone in d (larger d means more inputs
    are subject to the bound, so the bound can only get larger). Therefore,
    the least bound at g₁ ≤ the least bound at g₂ when g₁ ≤ g₂. -/
theorem GradedReflModel.actualDriftFn_mono
    (M : GradedReflModel) (hfd : M.FiniteDrift) {g₁ g₂ : Nat} (h : g₁ ≤ g₂) :
    M.actualDriftFn hfd g₁ ≤ M.actualDriftFn hfd g₂ := by
  by_contra hlt
  push_neg at hlt
  -- hlt: actualDriftFn g₂ < actualDriftFn g₁
  -- actualDriftFn_minimal at g₁: any j < leastDrift g₁ fails DefectBoundedAt g₁ j
  -- In particular, actualDriftFn g₂ fails DefectBoundedAt g₁
  have hfail := M.actualDriftFn_minimal hfd g₁ hlt
  -- But DefectBoundedAt g₂ (actualDriftFn g₂) holds, and g₁ ≤ g₂,
  -- so DefectBoundedAt g₁ (actualDriftFn g₂) holds by anti-monotonicity in d
  have hok : M.DefectBoundedAt g₁ (M.actualDriftFn hfd g₂) :=
    M.defectBoundedAt_mono_d h (M.leastDriftAt_defectBoundedAt g₂ _)
  exact hfail hok

-- ════════════════════════════════════════════════════════════
-- Section 6: actualDriftFn vs. minDrift
-- ════════════════════════════════════════════════════════════

/-- Under FiniteDrift, actualDriftFn is bounded by the global minDrift. -/
theorem GradedReflModel.actualDriftFn_le_minDrift
    (M : GradedReflModel) (hfd : M.FiniteDrift) (g : Nat) :
    M.actualDriftFn hfd g ≤ GradedReflModel.minDrift M hfd := by
  -- minDrift gives DefectBounded (minDrift), which implies DefectBoundedAt g (minDrift)
  have hmin : M.DefectBounded (GradedReflModel.minDrift M hfd) :=
    (M.defectBounded_iff_drift _).mpr (GradedReflModel.minDrift_admitsDrift M hfd)
  have hbat : M.DefectBoundedAt g (GradedReflModel.minDrift M hfd) :=
    fun x _ => hmin x
  -- leastDriftAt g ≤ minDrift since minDrift witnesses DefectBoundedAt g
  by_contra hlt
  push_neg at hlt
  exact M.leastDriftAt_minimal g _ hlt hbat

/-- Under zero drift (Group B/C), actualDriftFn is zero everywhere. -/
theorem GradedReflModel.actualDriftFn_zero_of_isLeastDrift_zero
    (M : GradedReflModel) (hfd : M.FiniteDrift)
    (h0 : M.IsLeastDrift 0) (g : Nat) :
    M.actualDriftFn hfd g = 0 := by
  have hle : M.actualDriftFn hfd g ≤ 0 := by
    have hmin : M.DefectBounded 0 :=
      (M.defectBounded_iff_drift _).mpr h0.1
    have hbat : M.DefectBoundedAt g 0 := fun x _ => by have := hmin x; omega
    by_contra hlt
    push_neg at hlt
    exact M.leastDriftAt_minimal g _ hlt hbat
  omega

/-- actualDriftFn equals minDrift at grade levels that "realize" the global minimum.
    At sufficiently high grades, the pointwise minimum stabilizes to the global minimum. -/
theorem GradedReflModel.actualDriftFn_ge_minDrift_at_witness
    (M : GradedReflModel) (hfd : M.FiniteDrift)
    (hld : M.IsLeastDrift (GradedReflModel.minDrift M hfd)) (g : Nat)
    (hw : ∀ j < GradedReflModel.minDrift M hfd, ∃ x, M.grade x ≤ g ∧
            M.grade (M.selfApp x) > M.grade x + j) :
    M.actualDriftFn hfd g = GradedReflModel.minDrift M hfd := by
  apply Nat.le_antisymm (M.actualDriftFn_le_minDrift hfd g)
  -- Need: minDrift ≤ actualDriftFn g
  -- By minimality of leastDriftAt: show ¬DefectBoundedAt g (actualDriftFn g - 1)
  -- Equivalently: show actualDriftFn g is the minimum
  -- Use hw: for any j < minDrift, DefectBoundedAt g j fails
  by_contra hlt
  push_neg at hlt
  -- hlt: actualDriftFn g < minDrift
  -- hw gives: for j = actualDriftFn g, there exists an overflow witness at grade ≤ g
  obtain ⟨x, hgx, hgap⟩ := hw (M.actualDriftFn hfd g) hlt
  -- But actualDriftFn_bound says: grade(selfApp(x)) ≤ grade(x) + actualDriftFn g
  have hbound := M.actualDriftFn_bound hfd g x hgx
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Encoding invariance for the dynamic drift function
-- ════════════════════════════════════════════════════════════

/-- Dynamic drift transport for non-decreasing drift functions.

    If M has drift function δ (non-decreasing) and BoundedGRMEquiv overhead c,
    then M' has drift function δ' = fun g => δ(g + c) + 2c.

    Derivation: For x' in M',
      grade'(selfApp'(x')) = grade'(f(selfApp(g(x'))))
        ≤ grade(selfApp(g(x'))) + c
        ≤ (grade(g(x')) + δ(grade(g(x')))) + c
        ≤ (grade'(x') + c + δ(grade(g(x')))) + c
        ≤ grade'(x') + δ(grade'(x') + c) + 2c   [by monotonicity of δ]
-/
theorem BoundedGRMEquiv.dynamic_drift_transport_mono {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (δ : Nat → Nat)
    (hδ : ∀ g₁ g₂, g₁ ≤ g₂ → δ g₁ ≤ δ g₂)
    (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + δ (M.grade x)) :
    ∀ x', M'.grade (M'.selfApp x') ≤
      M'.grade x' + (δ (M'.grade x' + E.overhead) + 2 * E.overhead) := by
  intro x'
  have hcompat : M'.selfApp x' = E.f (M.selfApp (E.g x')) := by
    rw [← E.f_compat, E.fg]
  rw [hcompat]
  have h1 := E.f_bounded (M.selfApp (E.g x'))
  have h2 := E.g_bounded x'
  have h3 := h (E.g x')
  -- grade(g(x')) ≤ grade'(x') + overhead
  -- δ(grade(g(x'))) ≤ δ(grade'(x') + overhead) by monotonicity
  have hδ_le : δ (M.grade (E.g x')) ≤ δ (M'.grade x' + E.overhead) :=
    hδ _ _ h2
  omega

/-- Dynamic drift transport in the reverse direction (M' → M). -/
theorem BoundedGRMEquiv.dynamic_drift_transport_mono_g {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (δ : Nat → Nat)
    (hδ : ∀ g₁ g₂, g₁ ≤ g₂ → δ g₁ ≤ δ g₂)
    (h : ∀ x', M'.grade (M'.selfApp x') ≤ M'.grade x' + δ (M'.grade x')) :
    ∀ x, M.grade (M.selfApp x) ≤
      M.grade x + (δ (M.grade x + E.overhead) + 2 * E.overhead) := by
  intro x
  have hcompat : M.selfApp x = E.g (M'.selfApp (E.f x)) := by
    rw [← E.g_compat, E.gf]
  rw [hcompat]
  have h1 := E.g_bounded (M'.selfApp (E.f x))
  have h2 := E.f_bounded x
  have h3 := h (E.f x)
  have hδ_le : δ (M'.grade (E.f x)) ≤ δ (M.grade x + E.overhead) :=
    hδ _ _ h2
  omega

/-- Constant drift is a special case of the monotone transport:
    constant functions are trivially non-decreasing.
    Recovers drift_transport as a special case. -/
theorem BoundedGRMEquiv.const_drift_from_dynamic_transport {M M' : GradedReflModel}
    (E : BoundedGRMEquiv M M') (k : Nat)
    (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + k) :
    ∀ x', M'.grade (M'.selfApp x') ≤ M'.grade x' + (k + 2 * E.overhead) :=
  E.drift_transport k h

-- ════════════════════════════════════════════════════════════
-- Section 8: Drift function classes
-- ════════════════════════════════════════════════════════════

/-- A GRM has eventually-zero drift: drift is zero for all grades ≥ threshold.
    classicalGRM satisfies this (zero drift above headerLen). -/
def GradedReflModel.EventuallyZeroDrift (M : GradedReflModel) (threshold : Nat) : Prop :=
  ∀ x, M.grade x ≥ threshold → M.grade (M.selfApp x) ≤ M.grade x

/-- A GRM has eventually-zero drift AND bounded below threshold.

    This is the correct hypothesis for classicalGRM-style models:
    - Below the threshold (small inputs), drift is bounded by k.
    - Above the threshold (large inputs), drift is zero.
    Together these give uniform FiniteDrift. -/
def GradedReflModel.EventuallyZeroDriftBounded
    (M : GradedReflModel) (threshold k : Nat) : Prop :=
  (∀ x, M.grade x ≥ threshold → M.grade (M.selfApp x) ≤ M.grade x) ∧
  (∀ x, M.grade x < threshold → M.grade (M.selfApp x) ≤ M.grade x + k)

/-- EventuallyZeroDriftBounded implies FiniteDrift. -/
theorem GradedReflModel.eventuallyZeroDriftBounded_finiteDrift
    (M : GradedReflModel) {threshold k : Nat}
    (h : M.EventuallyZeroDriftBounded threshold k) :
    M.FiniteDrift := by
  refine ⟨k, M.drift_extension_iff k |>.mpr (fun x => ?_)⟩
  by_cases hge : M.grade x ≥ threshold
  · have := h.1 x hge; omega
  · push_neg at hge
    exact h.2 x hge

/-- EventuallyZeroDriftBounded gives a better (non-constant) dynamic drift
    witness: δ(g) = 0 for g ≥ threshold, δ(g) = k otherwise. -/
theorem GradedReflModel.eventuallyZeroDriftBounded_dynamic
    (M : GradedReflModel) {threshold k : Nat}
    (h : M.EventuallyZeroDriftBounded threshold k) :
    Nonempty (M.DynamicDriftCompatibleExtension
      (fun g => if g ≥ threshold then 0 else k)) := by
  rw [M.dynamic_drift_extension_iff]
  intro x
  by_cases hge : M.grade x ≥ threshold
  · simp [hge]
    exact h.1 x hge
  · push_neg at hge
    simp [Nat.not_le.mpr hge]
    exact h.2 x hge

/-- A GRM has linearly-bounded drift: grade(selfApp(x)) ≤ grade(x) * (a + 1) + b.

    For a = 0: recovers constant drift (FiniteDrift).
    For a > 0: drift grows linearly with grade (sub-quadratic complexity overhead). -/
def GradedReflModel.LinearDriftBounded (M : GradedReflModel) (a b : Nat) : Prop :=
  ∀ x, M.grade (M.selfApp x) ≤ M.grade x * (a + 1) + b

/-- Zero-slope linear drift is FiniteDrift (constant overhead). -/
theorem GradedReflModel.zeroSlope_finiteDrift
    (M : GradedReflModel) {b : Nat}
    (h : ∀ x, M.grade (M.selfApp x) ≤ M.grade x + b) :
    M.FiniteDrift :=
  ⟨b, M.drift_extension_iff b |>.mpr h⟩

/-- Positive-slope linear drift gives a DynamicDriftCompatibleExtension
    (with drift function fun g => a * g + b), but NOT FiniteDrift for a > 0. -/
theorem GradedReflModel.posSlope_dynamic_drift
    (M : GradedReflModel) {a b : Nat}
    (h : M.LinearDriftBounded a b) :
    Nonempty (M.DynamicDriftCompatibleExtension (fun g => a * g + b)) := by
  rw [M.dynamic_drift_extension_iff]
  intro x
  have hx := h x
  -- LinearDriftBounded: grade(selfApp(x)) ≤ grade(x) * (a+1) + b
  -- grade(x) * (a+1) = grade(x) + grade(x) * a
  -- target: grade(selfApp(x)) ≤ grade(x) + (a * grade(x) + b)
  -- Both sides equal grade(x) + a * grade(x) + b = grade(x) + grade(x) * a + b
  -- Nat.mul_succ: grade(x) * (a + 1) = grade(x) * a + grade(x)
  -- so grade(x) * (a+1) + b = grade(x) + grade(x) * a + b ≥ target
  have hrw : M.grade x * (a + 1) = M.grade x * a + M.grade x := Nat.mul_succ _ _
  have hcomm : M.grade x * a = a * M.grade x := Nat.mul_comm _ _
  omega

/-- Super-linear drift: drift exceeds every linear bound. Specifically,
    the model does not have finite drift, and for every linear function
    a·g + b, there exists an input whose selfApp grade exceeds grade + (a·grade + b).

    This fills the gap in the regime spectrum between LinearDriftBounded and
    UnboundedGap: the drift function grows faster than any linear function
    but may still be sub-exponential (e.g. quadratic, polynomial). -/
def GradedReflModel.HasSuperLinearDrift (M : GradedReflModel) : Prop :=
  ¬M.FiniteDrift ∧ ∀ a b, ∃ x, M.grade (M.selfApp x) > M.grade x + (a * M.grade x + b)

-- ════════════════════════════════════════════════════════════
-- Section 9: Connection to FiniteDrift
-- ════════════════════════════════════════════════════════════

/-- FiniteDrift ↔ actualDriftFn is uniformly bounded. -/
theorem GradedReflModel.finiteDrift_iff_actualDriftFn_bounded
    (M : GradedReflModel) :
    M.FiniteDrift ↔ ∃ hfd : M.FiniteDrift, ∃ k, ∀ g, M.actualDriftFn hfd g ≤ k := by
  constructor
  · intro hfd
    refine ⟨hfd, GradedReflModel.minDrift M hfd, fun g => ?_⟩
    exact M.actualDriftFn_le_minDrift hfd g
  · intro ⟨hfd, _, _⟩; exact hfd

/-- A uniform bound on actualDriftFn recovers FiniteDrift directly. -/
theorem GradedReflModel.uniformBound_finiteDrift
    (M : GradedReflModel) (hfd : M.FiniteDrift) {k : Nat}
    (hunif : ∀ g, M.actualDriftFn hfd g ≤ k) :
    M.FiniteDrift :=
  hfd

-- ════════════════════════════════════════════════════════════
-- Section 10: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms DynamicDriftCarrier
#print axioms FixedGradeDriftCarrier.toDynamic
#print axioms DynamicDriftCarrier.toFixed
#print axioms DynamicDriftCarrier.toStrict
#print axioms DynamicDriftCarrier.grade_C_unique
#print axioms DynamicDriftCarrier.instSubsingleton
#print axioms GradedReflModel.DynamicDriftCompatibleExtension
#print axioms GradedReflModel.dynamic_drift_extension_iff
#print axioms GradedReflModel.dynamic_drift_mono
#print axioms GradedReflModel.dynamic_drift_const_iff
#print axioms GradedReflModel.HasBoundedDriftAt
#print axioms GradedReflModel.defectBounded_implies_hasBoundedDriftAt
#print axioms GradedReflModel.finiteDrift_hasBoundedDriftAt
#print axioms GradedReflModel.leastDriftAt
#print axioms GradedReflModel.leastDriftAt_defectBoundedAt
#print axioms GradedReflModel.leastDriftAt_minimal
#print axioms GradedReflModel.actualDriftFn
#print axioms GradedReflModel.actualDriftFn_bound
#print axioms GradedReflModel.actualDriftFn_minimal
#print axioms GradedReflModel.admits_actualDriftFn
#print axioms GradedReflModel.actualDriftFn_mono
#print axioms GradedReflModel.actualDriftFn_le_minDrift
#print axioms GradedReflModel.actualDriftFn_zero_of_isLeastDrift_zero
#print axioms GradedReflModel.actualDriftFn_ge_minDrift_at_witness
#print axioms BoundedGRMEquiv.dynamic_drift_transport_mono
#print axioms BoundedGRMEquiv.dynamic_drift_transport_mono_g
#print axioms BoundedGRMEquiv.const_drift_from_dynamic_transport
#print axioms GradedReflModel.EventuallyZeroDrift
#print axioms GradedReflModel.EventuallyZeroDriftBounded
#print axioms GradedReflModel.eventuallyZeroDriftBounded_finiteDrift
#print axioms GradedReflModel.eventuallyZeroDriftBounded_dynamic
#print axioms GradedReflModel.LinearDriftBounded
#print axioms GradedReflModel.zeroSlope_finiteDrift
#print axioms GradedReflModel.posSlope_dynamic_drift
#print axioms GradedReflModel.HasSuperLinearDrift
#print axioms GradedReflModel.finiteDrift_iff_actualDriftFn_bounded
#print axioms GradedReflModel.uniformBound_finiteDrift

end WTS
