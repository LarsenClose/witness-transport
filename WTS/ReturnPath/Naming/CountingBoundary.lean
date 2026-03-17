/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

WTS/ReturnPath/CountingBoundary.lean — Growth gap counting arguments
connected to gradeGap regimes.

The growth gap (N_End(g) > N_L(g + c) for some g, all overhead c) is
the counting-theoretic obstruction: there are more endomorphisms at
grade g than carrier elements at grade g + c. This file establishes:

  (1) Binary growth gap: N_End(g) = N_Val(g)^N_Val(g) grows strictly
      faster than N_Val(g + c) = 2^(g+c+1) for any fixed overhead c.

  (2) The connection to gradeGap regimes: Compatible (gradeGap ≤ 0)
      implies selfApp factors through every grade. If additionally
      the grade structure has growth gap AND an injection bound linking
      the two levels, we get a contradiction. The injection bound
      hypothesis is stated explicitly — it bridges the counting level
      (N_End, N_L) to the carrier level (selfApp, FactorsThrough).

  (3) At unbounded gap (SelfAppUnbounded), the growth gap is consistent
      — selfApp already fails to factor, so no injection bound applies.

The two levels (counting functions vs carrier elements) do not directly
connect in the current formalization without an explicit bridging
hypothesis. This file documents that gap honestly.

STATUS: 0 sorry, 0 Classical.choice.
-/

import WTS.ReturnPath.Naming.GradeGapMeasure
import WTS.ReturnPath.Naming.OmegaGradeTransfer
import WTS.Core

namespace WTS

-- ════════════════════════════════════════════════════════════
-- Section 1: Binary growth gap — N_End grows faster than N_Val
-- ════════════════════════════════════════════════════════════

/-- For a ≥ 2, a^a > a. Core of the tower domination. -/
theorem pow_self_gt_self (a : Nat) (ha : a ≥ 2) : a ^ a > a := by
  have h1 : a ^ a ≥ a ^ 2 := Nat.pow_le_pow_right (by omega : a > 0) ha
  have h2 : a ^ 2 = a * a := by rw [Nat.pow_succ, Nat.pow_one]
  have h3 : a * a ≥ 2 * a := Nat.mul_le_mul_right a ha
  omega

/-- N_End(g) > N_Val(g) for all g.
    Since N_Val(g) ≥ 2, we have N_Val(g)^N_Val(g) > N_Val(g). -/
theorem N_End_gt_N_Val (g : Nat) : N_End g > N_Val g := by
  unfold N_End
  exact pow_self_gt_self (N_Val g) (N_Val_ge_2 g)

/-- HasGrowthGap instantiated for the binary model at overhead 0. -/
theorem binary_has_growth_gap_zero : HasGrowthGap N_End N_Val 0 := by
  unfold HasGrowthGap
  exact ⟨0, by simp; exact N_End_gt_N_Val 0⟩

/-- 2*c + 3 < 8 * 2^c for all c. Helper for the growth gap witness. -/
private theorem two_c_plus_3_lt_8_mul_2_pow (c : Nat) : 2 * c + 3 < 8 * 2 ^ c := by
  induction c with
  | zero => decide
  | succ k ih =>
    have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [Nat.pow_succ]; omega
    omega

/-- 2^(c+3) = 8 * 2^c -/
private theorem two_pow_add_3 (c : Nat) : 2 ^ (c + 3) = 8 * 2 ^ c := by
  induction c with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 from by omega]
    rw [Nat.pow_succ, ih]
    rw [Nat.pow_succ]; omega

/-- N_End(g) > N_Val(g + c) witnessed at g = c + 2.
    The tower N_Val(g)^N_Val(g) = 2^((g+1)*2^(g+1)) dominates 2^(g+c+1). -/
theorem binary_growth_gap_witness (c : Nat) :
    N_End (c + 2) > N_Val (c + 2 + c) := by
  unfold N_End N_Val
  -- Goal: 2^(c+2+1) ^ 2^(c+2+1) > 2^(c+2+c+1)
  -- Normalize: c+2+1 = c+3 and c+2+c+1 = 2*c+3
  have heq1 : c + 2 + 1 = c + 3 := by omega
  have heq2 : c + 2 + c + 1 = 2 * c + 3 := by omega
  rw [heq1, heq2]
  -- Goal: 2^(c+3) ^ 2^(c+3) > 2^(2*c+3)
  have hge2 : 2 ^ (c + 3) ≥ 2 := two_pow_ge_2 (c + 2)
  have htower := pow_self_ge_two_pow (2 ^ (c + 3)) hge2
  -- htower : (2^(c+3))^(2^(c+3)) ≥ 2^(2^(c+3))
  have hexp : 2 ^ (c + 3) > 2 * c + 3 := by
    have h8 := two_c_plus_3_lt_8_mul_2_pow c
    rw [two_pow_add_3]
    exact h8
  have hmono := two_pow_strict_mono hexp
  -- hmono : 2^(2*c+3) < 2^(2^(c+3))
  exact Nat.lt_of_lt_of_le hmono htower

/-- HasGrowthGap holds at every overhead for the binary model. -/
theorem binary_has_growth_gap (c : Nat) : HasGrowthGap N_End N_Val c :=
  ⟨c + 2, binary_growth_gap_witness c⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: GradeStructure and the injection bound hypothesis
-- ════════════════════════════════════════════════════════════

/-- N_End is monotone: N_Val(g) ≤ N_Val(g+1) implies
    N_Val(g)^N_Val(g) ≤ N_Val(g+1)^N_Val(g+1). -/
private theorem N_End_mono_succ (g : Nat) : N_End g ≤ N_End (g + 1) := by
  unfold N_End
  have hmono := N_Val_mono_succ g
  -- N_Val(g) ≤ N_Val(g+1), both positive
  -- N_Val(g)^N_Val(g) ≤ N_Val(g+1)^N_Val(g) ≤ N_Val(g+1)^N_Val(g+1)
  calc N_Val g ^ N_Val g
      ≤ N_Val (g + 1) ^ N_Val g := Nat.pow_le_pow_left hmono (N_Val g)
    _ ≤ N_Val (g + 1) ^ N_Val (g + 1) :=
        Nat.pow_le_pow_right (N_Val_pos (g + 1)) hmono

/-- The binary grade structure: endomorphisms and carrier elements
    counted by N_End and N_Val respectively. -/
def binaryGradeStructure : GradeStructure where
  N_End := N_End
  N_L := N_Val
  N_End_mono := N_End_mono_succ
  N_L_mono := fun g => N_Val_mono_succ g

/-- An injection bound connects counting (N_End, N_L) to selfApp factoring.
    If selfApp factors through grade d, then the number of distinct
    endomorphisms reachable within grade d is at most the number of
    carrier elements at grade d + overhead.

    This is a HYPOTHESIS, not a theorem: it requires that the grade
    structure faithfully counts what the GRM's grade function measures.
    The connection between GradeStructure.N_End/N_L (abstract counting
    functions) and GradedReflModel.grade (carrier → Nat) is not
    established by either structure alone. -/
def HasInjectionBound (M : GradedReflModel) (gs : GradeStructure)
    (overhead : Nat) : Prop :=
  FactorsThrough M M.selfApp overhead →
    ∀ g, gs.N_End g ≤ gs.N_L (g + overhead)

-- ════════════════════════════════════════════════════════════
-- Section 3: Compatible + growth gap + injection bound → contradiction
-- ════════════════════════════════════════════════════════════

/-- If a model is Compatible (gradeGap ≤ 0), has an injection bound
    linking its grade structure to selfApp factoring, and the grade
    structure has a growth gap, then we have a contradiction.

    The argument:
    (1) Compatible → selfApp factors through every grade
    (2) In particular, selfApp factors through grade `overhead`
    (3) Injection bound: factoring implies N_End(g) ≤ N_L(g + overhead)
    (4) Growth gap: ∃ g, N_End(g) > N_L(g + overhead)
    (3) and (4) contradict at the witnessed g. -/
theorem compatible_growth_gap_injection_absurd
    (M : GradedReflModel)
    (gs : GradeStructure)
    (overhead : Nat)
    (hcompat : M.toGradedRetraction.Compatible)
    (hinj : HasInjectionBound M gs overhead)
    (hgap : HasGrowthGap gs.N_End gs.N_L overhead) :
    False := by
  have hfactors : FactorsThrough M M.selfApp overhead :=
    compatible_selfApp_factors M hcompat overhead
  have hbound := hinj hfactors
  obtain ⟨g, hgt⟩ := hgap
  have hle := hbound g
  omega

/-- Corollary via gradeGap: nonpositive gap + injection bound + growth gap
    is contradictory. -/
theorem nonpositive_gap_growth_injection_absurd
    (M : GradedReflModel)
    (gs : GradeStructure)
    (overhead : Nat)
    (hgap_le : ∀ x, gradeGap M x ≤ 0)
    (hinj : HasInjectionBound M gs overhead)
    (hgrowth : HasGrowthGap gs.N_End gs.N_L overhead) :
    False :=
  compatible_growth_gap_injection_absurd M gs overhead
    ((compatible_iff_nonpositive_gap M).mpr hgap_le) hinj hgrowth

-- ════════════════════════════════════════════════════════════
-- Section 4: Unbounded regime — growth gap is consistent
-- ════════════════════════════════════════════════════════════

/-- When selfApp is unbounded, the injection bound hypothesis FAILS
    because selfApp does not factor through any grade. Therefore the
    growth gap is consistent with unbounded selfApp. -/
theorem unbounded_no_injection_bound
    (M : GradedReflModel)
    (hub : SelfAppUnbounded M)
    (overhead : Nat) :
    ¬(FactorsThrough M M.selfApp overhead) :=
  selfApp_not_factors M hub overhead

/-- standardModel is unbounded AND binaryGradeStructure has growth gap.
    These coexist without contradiction. -/
theorem standard_model_consistent_growth_gap :
    SelfAppUnbounded standardModel ∧
    (∀ c, HasGrowthGap binaryGradeStructure.N_End binaryGradeStructure.N_L c) :=
  ⟨standardModel_selfAppUnbounded,
   fun c => binary_has_growth_gap c⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: The counting boundary pick-two
-- ════════════════════════════════════════════════════════════

/-- THE COUNTING BOUNDARY: how growth gap interacts with gradeGap regimes.

    (1) Compatible + injection bound: growth gap is IMPOSSIBLE.
    (2) Unbounded (SelfAppUnbounded): growth gap is CONSISTENT.

    The injection bound hypothesis bridges the counting level
    (N_End, N_L) to the carrier level (selfApp, grade). Without
    it, Compatible and growth gap live on different levels and do not
    interact. With it, Compatible forces the growth gap closed.

    This captures the pick-2-of-3 at the counting level:
    you cannot have all three of (Compatible, injection bound, growth gap). -/
theorem counting_boundary_pick_two :
    -- (1) Compatible + injection bound → no growth gap
    (∀ (M : GradedReflModel) (gs : GradeStructure) (c : Nat),
      M.toGradedRetraction.Compatible →
      HasInjectionBound M gs c →
      ¬HasGrowthGap gs.N_End gs.N_L c) ∧
    -- (2) Unbounded + growth gap is consistent (witnessed)
    (∃ (M : GradedReflModel) (gs : GradeStructure),
      SelfAppUnbounded M ∧
      ∀ c, HasGrowthGap gs.N_End gs.N_L c) :=
  ⟨fun M gs c hcompat hinj hgap =>
    compatible_growth_gap_injection_absurd M gs c hcompat hinj hgap,
   ⟨standardModel, binaryGradeStructure, standard_model_consistent_growth_gap⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Injection bound vacuity for unbounded models
-- ════════════════════════════════════════════════════════════

/-- On SelfAppUnbounded models, HasInjectionBound holds vacuously.
    The premise (selfApp factors through some grade) is always false,
    so the implication is trivially true.

    This is the formal content of "the bounded construction leg fails"
    in the separation regime: the injection bound doesn't constrain
    anything because selfApp never factors. -/
theorem unbounded_injection_bound_vacuous (M : GradedReflModel)
    (hub : SelfAppUnbounded M) (gs : GradeStructure) (overhead : Nat) :
    HasInjectionBound M gs overhead :=
  fun hfac => absurd hfac (selfApp_not_factors M hub overhead)

-- ════════════════════════════════════════════════════════════
-- Section 7: Complete picture for concrete models
-- ════════════════════════════════════════════════════════════

/-- standardModel: the complete separation-regime picture.

    All four properties coexist:
    (1) SelfAppUnbounded — selfApp overflows every grade
    (2) ¬PEqNP — selfApp does not factor
    (3) Growth gap at every overhead — N_End dominates N_Val
    (4) Injection bound vacuously satisfied — no contradiction

    This is the formal witness that growth gap + separation regime
    is consistent. The injection bound holds vacuously because selfApp
    never factors, so the counting contradiction (pick-2-of-3) does
    not fire. -/
theorem standardModel_separation_complete :
    SelfAppUnbounded standardModel ∧
    ¬PEqNP standardModel ∧
    (∀ c, HasGrowthGap binaryGradeStructure.N_End binaryGradeStructure.N_L c) ∧
    (∀ c, HasInjectionBound standardModel binaryGradeStructure c) :=
  ⟨standardModel_selfAppUnbounded,
   incompatible_retraction_gives_separation standardModel standardModel_selfAppUnbounded,
   fun c => binary_has_growth_gap c,
   fun c => unbounded_injection_bound_vacuous standardModel
     standardModel_selfAppUnbounded binaryGradeStructure c⟩

/-- trivialModel: the complete compatible-regime picture.

    (1) Compatible (gradeGap ≤ 0) — selfApp = id
    (2) PEqNP — selfApp factors through every grade
    (3) No growth gap possible IF injection bound holds — counting
        boundary forces growth gap closed

    The injection bound for trivialModel is trivially satisfiable
    because the carrier is Unit (one element at every grade). -/
theorem trivialModel_compatible_complete :
    (∀ x, gradeGap trivialModel x ≤ 0) ∧
    PEqNP trivialModel ∧
    (∀ d, FactorsThrough trivialModel trivialModel.selfApp d) :=
  ⟨fun x => by cases x; show (↑(trivialModel.grade (trivialModel.unfold (trivialModel.fold PUnit.unit))) : Int) - ↑(trivialModel.grade PUnit.unit) ≤ 0; decide,
   compatible_retraction_gives_PEqNP trivialModel
     (fun x => by cases x; exact Nat.le_refl _),
   fun d => compatible_selfApp_factors trivialModel
     (fun x => by cases x; exact Nat.le_refl _) d⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: The full gradeGap anti-compression assembly
-- ════════════════════════════════════════════════════════════

/-- THE FULL ANTI-COMPRESSION THROUGH GRADEGAP.

    Combines all pieces into a single result:

    (1) Compatible + injection bound → growth gap impossible.
        This is the non-vacuous content: gradeGap ≤ 0 forces
        selfApp to factor, the injection bound then constrains
        counting, and growth gap contradicts.

    (2) Unbounded → injection bound vacuous → growth gap consistent.
        This is the consistency witness: gradeGap unbounded means
        selfApp never factors, so the injection bound's premise
        is false, and growth gap lives without contradiction.

    (3) Both regimes concretely witnessed.

    This replaces the vacuous omega_grade_transfer axiom in
    AntiCompression.lean (pnp-integrated) with a derived result
    where every ingredient traces to gradeGap. -/
theorem gradeGap_anti_compression_assembly :
    -- (1) Compatible + injection bound → no growth gap
    (∀ (M : GradedReflModel) (gs : GradeStructure) (c : Nat),
      (∀ x, gradeGap M x ≤ 0) →
      HasInjectionBound M gs c →
      ¬HasGrowthGap gs.N_End gs.N_L c) ∧
    -- (2) Unbounded → injection bound vacuous
    (∀ (M : GradedReflModel) (gs : GradeStructure) (c : Nat),
      SelfAppUnbounded M →
      HasInjectionBound M gs c) ∧
    -- (3) Separation regime witnessed with growth gap
    (∃ (M : GradedReflModel) (gs : GradeStructure),
      SelfAppUnbounded M ∧
      (∀ c, HasGrowthGap gs.N_End gs.N_L c) ∧
      (∀ c, HasInjectionBound M gs c)) :=
  ⟨fun M gs c hgap hinj hgrowth =>
    nonpositive_gap_growth_injection_absurd M gs c hgap hinj hgrowth,
   fun M gs c hub =>
    unbounded_injection_bound_vacuous M hub gs c,
   ⟨standardModel, binaryGradeStructure,
    standardModel_selfAppUnbounded,
    fun c => binary_has_growth_gap c,
    fun c => unbounded_injection_bound_vacuous standardModel
      standardModel_selfAppUnbounded binaryGradeStructure c⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: Axiom audit
-- ════════════════════════════════════════════════════════════

#print axioms pow_self_gt_self
#print axioms N_End_gt_N_Val
#print axioms binary_has_growth_gap
#print axioms compatible_growth_gap_injection_absurd
#print axioms nonpositive_gap_growth_injection_absurd
#print axioms counting_boundary_pick_two
#print axioms unbounded_injection_bound_vacuous
#print axioms standardModel_separation_complete
#print axioms trivialModel_compatible_complete
#print axioms gradeGap_anti_compression_assembly

end WTS
