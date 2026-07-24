import Submission.NU.LCFT.Basic.LocalField

/-!
# The Lubin--Tate formal module

We use `f(X)=πX+X^q` and Mathlib's `FormalGroup`.  Composition of one-variable series is written
with `PowerSeries.subst`; bivariate formal addition uses `MvPowerSeries.subst`.
-/

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel
open MvPowerSeries

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A uniformizer has an integral representative. -/
theorem uniformizer_integer_exists (π : Uniformizer K) :
    ∃ x : RingOfIntegers K, (x : K) = (π.val : K) := by
  apply (exists_normalizedValuationHom K).choose_spec.2 π.val |>.1
  change 0 ≤ normalizedValuation K π.val
  rw [π.valuation_eq_one]
  omega

/-- The chosen integral representative of a uniformizer. -/
noncomputable def uniformizerInteger (π : Uniformizer K) : RingOfIntegers K :=
  (uniformizer_integer_exists K π).choose

private theorem normalizedValuation_inv
    (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem isUnit_of_normalizedValuation_eq_zero
    (a : RingOfIntegers K) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [normalizedValuation_inv K, hval, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers K) :=
    { val := a
      inv := b
      val_inv := by
        apply Subtype.ext
        change (a : K) * (b : K) = 1
        rw [hb]
        exact mul_inv_cancel₀ ha
      inv_val := by
        apply Subtype.ext
        change (b : K) * (a : K) = 1
        rw [hb]
        exact inv_mul_cancel₀ ha }
  exact ⟨u, rfl⟩

private theorem uniformizerInteger_irreducible (π : Uniformizer K) :
    Irreducible (uniformizerInteger K π) := by
  let ϖ := uniformizerInteger K π
  have hϖ : (ϖ : K) = (π.val : K) := (uniformizer_integer_exists K π).choose_spec
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation K
        (Units.map (algebraMap (RingOfIntegers K) K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
      rw [normalizedValuation_inv K] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers K) K) u = π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
      rw [hu, hϖ]
    rw [heq, π.valuation_eq_one] at huval
    omega
  · intro a b hab
    have ha0 : (a : K) ≠ 0 := by
      intro ha
      have : (ϖ : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [ha]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    have hb0 : (b : K) ≠ 0 := by
      intro hb
      have : (ϖ : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [hb]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    let ua : Units K := Units.mk0 (a : K) ha0
    let ub : Units K := Units.mk0 (b : K) hb0
    have hva : 0 ≤ normalizedValuation K ua :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨a, rfl⟩
    have hvb : 0 ≤ normalizedValuation K ub :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨b, rfl⟩
    have huv : ua * ub = π.val := by
      apply Units.ext
      simpa [ua, ub, ← hϖ] using congr_arg Subtype.val hab.symm
    have hvsum : normalizedValuation K ua + normalizedValuation K ub = 1 := by
      rw [← normalizedValuation_mul, huv, π.valuation_eq_one]
    rcases (show normalizedValuation K ua = 0 ∨ normalizedValuation K ub = 0 by omega) with ha | hb
    · exact Or.inl (isUnit_of_normalizedValuation_eq_zero K a ha0 ha)
    · exact Or.inr (isUnit_of_normalizedValuation_eq_zero K b hb0 hb)

private theorem uniformizerInteger_maximalIdeal (π : Uniformizer K) :
    Ideal.span ({uniformizerInteger K π} : Set (RingOfIntegers K)) =
      LocalMaximalIdeal K :=
  (uniformizerInteger_irreducible K π).maximalIdeal_eq.symm

/-- The Lubin--Tate polynomial `πX+X^q`. -/
def lubinTatePolynomial (π : Uniformizer K) : Polynomial (RingOfIntegers K) :=
  Polynomial.C (uniformizerInteger K π) * Polynomial.X +
    Polynomial.X ^ residueCard K

/-- The Lubin--Tate polynomial as a power series. -/
def lubinTateSeries (π : Uniformizer K) : PowerSeries (RingOfIntegers K) :=
  (lubinTatePolynomial K π : PowerSeries (RingOfIntegers K))

private theorem mvPowerSeries_expand_card_fintype
    {σ k : Type*} [Field k] [Fintype k] (f : MvPowerSeries σ k) :
    f.expand (Fintype.card k) Fintype.card_ne_zero = f ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases FiniteField.card k p with ⟨⟨n, _⟩, ⟨hp, hn⟩⟩
  letI : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  have h := MvPowerSeries.map_iterateFrobenius_expand p hp.ne_zero f n
  rw [iterateFrobenius_eq_pow, FiniteField.frobenius_pow hn] at h
  rw [show (1 : k →+* k) = RingHom.id k from rfl, map_id] at h
  change f.expand (p ^ n) (pow_ne_zero n hp.ne_zero) = f ^ p ^ n at h
  simpa only [hn] using h

private theorem mvPowerSeries_expand_card
    {σ k : Type*} [Field k] [Finite k] (f : MvPowerSeries σ k) :
    f.expand (Nat.card k) (Nat.card_pos.ne') = f ^ Nat.card k := by
  letI := Fintype.ofFinite k
  simpa only [Nat.card_eq_fintype_card] using mvPowerSeries_expand_card_fintype f

private theorem one_lt_residueCard : 1 < residueCard K := by
  letI := Fintype.ofFinite (LocalResidueField K)
  change 1 < Nat.card (LocalResidueField K)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

private def lubinTateVariable {σ : Type*} (π : Uniformizer K) (i : σ) :
    MvPowerSeries σ (RingOfIntegers K) :=
  C (uniformizerInteger K π) * X i + X i ^ residueCard K

private def lubinTateDiscrepancy {σ : Type*} (π : Uniformizer K)
    (A : MvPowerSeries σ (RingOfIntegers K)) :
    MvPowerSeries σ (RingOfIntegers K) :=
  A.subst (lubinTateVariable K π) -
    (C (uniformizerInteger K π) * A + A ^ residueCard K)

private theorem lubinTateDiscrepancy_dvd {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K)) (d : σ →₀ ℕ) :
    uniformizerInteger K π ∣ coeff d (lubinTateDiscrepancy K π A) := by
  rw [← Ideal.mem_span_singleton, uniformizerInteger_maximalIdeal K π,
    ← Ideal.Quotient.eq_zero_iff_mem]
  let r := IsLocalRing.residue (RingOfIntegers K)
  have hp : r (uniformizerInteger K π) = 0 := by
    change Ideal.Quotient.mk (LocalMaximalIdeal K) (uniformizerInteger K π) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← uniformizerInteger_maximalIdeal K π]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hq : residueCard K = Nat.card (LocalResidueField K) := rfl
  have hq0 : residueCard K ≠ 0 :=
    (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'
  have he := mvPowerSeries_expand_card (A.map r)
  have H : (lubinTateDiscrepancy K π A).map r = 0 := by
    rw [lubinTateDiscrepancy, map_sub, map_add, map_mul, map_pow,
      map_subst (hasSubst_of_constantCoeff_zero (by
        simp [lubinTateVariable, hq0])), map_C, hp]
    simp only [map_zero, zero_mul, zero_add]
    rw [hq, ← he, sub_eq_zero]
    congr! 2 with i
    simp [lubinTateVariable, hp, hq, MvPowerSeries.expand]
  exact congrArg (MvPowerSeries.coeff d) H

private theorem uniformizerInteger_mem_maximalIdeal (π : Uniformizer K) :
    uniformizerInteger K π ∈ LocalMaximalIdeal K := by
  rw [← uniformizerInteger_maximalIdeal K π]
  exact Ideal.mem_span_singleton.mpr (dvd_refl _)

private theorem one_sub_uniformizer_pow_isUnit (π : Uniformizer K)
    {n : ℕ} (hn : 0 < n) :
    IsUnit (1 - uniformizerInteger K π ^ n) := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [← IsLocalRing.mem_maximalIdeal]
  exact (LocalMaximalIdeal K).pow_mem_of_mem
    (uniformizerInteger_mem_maximalIdeal K π) n hn

private noncomputable def lubinTateCorrectionCoeff {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K))
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) : RingOfIntegers K :=
  let z := (lubinTateDiscrepancy_dvd K π A d).choose
  let u := (one_sub_uniformizer_pow_isUnit K π (Nat.sub_pos_of_lt hd)).unit
  z * (u⁻¹ : Units (RingOfIntegers K))

private theorem lubinTateCorrectionCoeff_spec {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K))
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    (uniformizerInteger K π - uniformizerInteger K π ^ d.degree) *
        lubinTateCorrectionCoeff K π A d hd =
      coeff d (lubinTateDiscrepancy K π A) := by
  let p := uniformizerInteger K π
  let z := (lubinTateDiscrepancy_dvd K π A d).choose
  have hz : p * z = coeff d (lubinTateDiscrepancy K π A) :=
    (lubinTateDiscrepancy_dvd K π A d).choose_spec.symm
  let hu := one_sub_uniformizer_pow_isUnit K π (Nat.sub_pos_of_lt hd)
  let u := hu.unit
  have huv : (u : RingOfIntegers K) = 1 - p ^ (d.degree - 1) := hu.unit_spec
  have huinv : (u : RingOfIntegers K) * (↑u⁻¹ : RingOfIntegers K) = 1 := by simp
  have hdeg : d.degree - 1 + 1 = d.degree := Nat.sub_add_cancel (by omega)
  have hfactor : p - p ^ d.degree = p * (1 - p ^ (d.degree - 1)) := by
    rw [mul_sub, mul_one, ← pow_succ', hdeg]
  change (p - p ^ d.degree) * (z * (↑u⁻¹ : RingOfIntegers K)) = _
  rw [hfactor, ← huv]
  calc
    p * (u : RingOfIntegers K) * (z * (↑u⁻¹ : RingOfIntegers K)) =
        p * z * ((u : RingOfIntegers K) * (↑u⁻¹ : RingOfIntegers K)) := by ring
    _ = p * z := by rw [huinv, mul_one]
    _ = _ := hz

private noncomputable def lubinTateCorrection {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K)) (n : ℕ) :
    MvPowerSeries σ (RingOfIntegers K) := fun d =>
  if hd : 2 ≤ d.degree ∧ d.degree = n then
    lubinTateCorrectionCoeff K π A d hd.1
  else 0

private theorem lubinTateCorrection_coeff {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K))
    (n : ℕ) (hn : 2 ≤ n) (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d (lubinTateCorrection K π A n) =
      lubinTateCorrectionCoeff K π A d (hd ▸ hn) := by
  rw [coeff_apply, lubinTateCorrection, dif_pos ⟨hd ▸ hn, hd⟩]

private theorem lubinTateCorrection_coeff_of_degree_ne {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K))
    (n : ℕ) (d : σ →₀ ℕ) (hd : d.degree ≠ n) :
    coeff d (lubinTateCorrection K π A n) = 0 := by
  rw [coeff_apply, lubinTateCorrection, dif_neg]
  exact fun h => hd h.2

private theorem lubinTateCorrection_isHomogeneous {σ : Type*} [Finite σ]
    (π : Uniformizer K) (A : MvPowerSeries σ (RingOfIntegers K)) (n : ℕ) :
    (lubinTateCorrection K π A n).IsHomogeneous n := by
  intro d hd
  by_contra hdegree
  have hw : d.degree = d.weight (fun _ : σ => 1) :=
    DFunLike.congr_fun (Finsupp.degree_eq_weight_one (R := ℕ)) d
  have hw' : d.weight (1 : σ → ℕ) = d.degree := by
    rw [show (1 : σ → ℕ) = fun _ => 1 by funext i; simp, ← hw]
  have hdegree' : d.degree ≠ n := fun h => hdegree (hw'.trans h)
  exact hd (lubinTateCorrection_coeff_of_degree_ne K π A n d hdegree')

private theorem homogeneousComponent_pow_of_one_le_order
    {σ R : Type*} [CommRing R] (f : MvPowerSeries σ R)
    (hf : 1 ≤ f.order) (m : ℕ) :
    (f ^ m).homogeneousComponent m = (f.homogeneousComponent 1) ^ m := by
  classical
  induction m with
  | zero =>
      ext d
      rw [coeff_homogeneousComponent]
      by_cases hd : d.degree = 0
      · rw [if_pos hd, (Finsupp.degree_eq_zero_iff d).mp hd]
        simp
      · have hd0 : d ≠ 0 := fun h => hd (by rw [h]; simp)
        rw [if_neg hd, pow_zero, coeff_one, if_neg hd0]
  | succ m ih =>
      rw [pow_succ, pow_succ, ← ih]
      apply homogeneousComponent_mul_of_le_order
      · calc
          (m : ℕ∞) = m • (1 : ℕ∞) := by simp
          _ ≤ m • f.order := nsmul_le_nsmul_right hf m
          _ ≤ (f ^ m).order := le_order_pow m
      · exact hf

private theorem homogeneousComponent_finsuppProd
    {σ R : Type*} [CommRing R] (g : σ → MvPowerSeries σ R) (e : σ →₀ ℕ)
    (hg : ∀ i, 1 ≤ (g i).order) (s : Finset σ) :
    (∏ i ∈ s, g i ^ e i).homogeneousComponent (∑ i ∈ s, e i) =
      ∏ i ∈ s, (g i).homogeneousComponent 1 ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext d
      simp only [Finset.sum_empty, Finset.prod_empty, coeff_homogeneousComponent]
      by_cases hd : d.degree = 0
      · rw [if_pos hd, (Finsupp.degree_eq_zero_iff d).mp hd]
      · have hd0 : d ≠ 0 := fun h => hd (by rw [h]; simp)
        rw [if_neg hd, coeff_one, if_neg hd0]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ← ih,
        ← homogeneousComponent_pow_of_one_le_order (g a) (hg a) (e a)]
      apply homogeneousComponent_mul_of_le_order
      · calc
          (e a : ℕ∞) = e a • (1 : ℕ∞) := by simp
          _ ≤ e a • (g a).order := nsmul_le_nsmul_right (hg a) _
          _ ≤ (g a ^ e a).order := le_order_pow _
      · calc
          ((∑ i ∈ s, e i : ℕ) : ℕ∞) = ∑ i ∈ s, (e i : ℕ∞) := by simp
          _ ≤ ∑ i ∈ s, (g i ^ e i).order := Finset.sum_le_sum fun i _ => by
            calc
              (e i : ℕ∞) = e i • (1 : ℕ∞) := by simp
              _ ≤ e i • (g i).order := nsmul_le_nsmul_right (hg i) _
              _ ≤ (g i ^ e i).order := le_order_pow _
          _ ≤ (∏ i ∈ s, g i ^ e i).order := le_order_prod _ _

private theorem coeff_finsuppProd_of_linear_part
    {σ R : Type*} [CommRing R] [DecidableEq σ]
    (p : R) (g : σ → MvPowerSeries σ R) (e : σ →₀ ℕ)
    (hg : ∀ i, 1 ≤ (g i).order)
    (hlin : ∀ i, (g i).homogeneousComponent 1 = p • X i)
    (d : σ →₀ ℕ) (he : e.degree = d.degree) :
    coeff d (e.prod fun i m => g i ^ m) =
      if d = e then p ^ d.degree else 0 := by
  have H := homogeneousComponent_finsuppProd g e hg e.support
  change (e.prod fun i m => g i ^ m).homogeneousComponent e.degree =
    e.prod fun i m => (g i).homogeneousComponent 1 ^ m at H
  have hd : coeff d (e.prod fun i m => g i ^ m) =
      coeff d ((e.prod fun i m => g i ^ m).homogeneousComponent d.degree) := by
    rw [coeff_homogeneousComponent, if_pos rfl]
  rw [hd, ← he, H]
  simp_rw [hlin]
  rw [← MvPowerSeries.monomial_smul_const e p, coeff_monomial]
  have hdeg : e.sum (fun _ n => n) = e.degree := rfl
  rw [hdeg, he]

private theorem lubinTateVariable_one_le_order {σ : Type*}
    (π : Uniformizer K) (i : σ) :
    1 ≤ (lubinTateVariable K π i).order := by
  rw [one_le_order_iff_constCoeff_eq_zero]
  simp [lubinTateVariable, (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']

private theorem lubinTateVariable_linearComponent {σ : Type*}
    (π : Uniformizer K) (i : σ) :
    (lubinTateVariable K π i).homogeneousComponent 1 =
      uniformizerInteger K π • X i := by
  classical
  let p := uniformizerInteger K π
  let q := residueCard K
  have hq : 2 ≤ q := one_lt_residueCard K
  ext d
  rw [lubinTateVariable, coeff_homogeneousComponent]
  by_cases hd : d.degree = 1
  · rw [if_pos hd]
    simp only [map_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_smul]
    split_ifs with hdi hdi'
    · have heq := DFunLike.congr_fun (hdi.symm.trans hdi') i
      simp only [Finsupp.single_eq_same] at heq
      omega
    · simp
    · subst d
      rw [Finsupp.degree_single] at hd
      omega
    · simp
  · rw [if_neg hd]
    simp only [coeff_smul, coeff_X]
    split_ifs with hdi
    · subst d
      simp at hd
    · simp

private theorem coeff_subst_lubinTateVariable_of_isHomogeneous
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (P : MvPowerSeries σ (RingOfIntegers K)) {n : ℕ} (hP : P.IsHomogeneous n)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d (P.subst (lubinTateVariable K π)) =
      uniformizerInteger K π ^ n * coeff d P := by
  classical
  let g : σ → MvPowerSeries σ (RingOfIntegers K) := lubinTateVariable K π
  have hg : ∀ i, 1 ≤ (g i).order := lubinTateVariable_one_le_order K π
  have hlin : ∀ i, (g i).homogeneousComponent 1 =
      uniformizerInteger K π • X i := lubinTateVariable_linearComponent K π
  rw [coeff_subst (hasSubst_of_constantCoeff_zero (by
    simp [g, lubinTateVariable,
      (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']))]
  rw [finsum_eq_single _ d]
  · have hprod := coeff_finsuppProd_of_linear_part
      (uniformizerInteger K π) g d hg hlin d rfl
    rw [if_pos rfl] at hprod
    change coeff d P * coeff d (d.prod fun i m => g i ^ m) = _
    rw [hprod, hd]
    ring
  · intro e hed
    by_cases he : e.degree = n
    · have hprod := coeff_finsuppProd_of_linear_part
        (uniformizerInteger K π) g e hg hlin d (he.trans hd.symm)
      rw [if_neg hed.symm] at hprod
      change coeff e P * coeff d (e.prod fun i m => g i ^ m) = 0
      rw [hprod, mul_zero]
    · rw [hP.coeff_eq_zero he, zero_smul]

private theorem isHomogeneous_le_order {σ R : Type*} [Semiring R]
    {P : MvPowerSeries σ R} {n : ℕ} (hP : P.IsHomogeneous n) :
    n ≤ P.order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  apply hP.coeff_eq_zero
  omega

private theorem coeff_subst_lubinTateVariable_of_lt_degree
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (P : MvPowerSeries σ (RingOfIntegers K)) {n : ℕ} (hP : P.IsHomogeneous n)
    (d : σ →₀ ℕ) (hd : d.degree < n) :
    coeff d (P.subst (lubinTateVariable K π)) = 0 := by
  apply coeff_of_lt_order
  apply lt_of_lt_of_le (show (d.degree : ℕ∞) < n by exact_mod_cast hd)
  calc
    (n : ℕ∞) = 1 * (n : ℕ∞) := by simp
    _ ≤ (⨅ i, (lubinTateVariable K π i).order) * P.order := by
      gcongr
      · exact le_iInf fun i => lubinTateVariable_one_le_order K π i
      · exact isHomogeneous_le_order hP
    _ ≤ _ := le_order_subst
      (hasSubst_of_constantCoeff_zero (by
        simp [lubinTateVariable,
          (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])) P

private theorem coeff_add_pow_sub_pow_eq_zero
    {σ R : Type*} [CommRing R] (A P : MvPowerSeries σ R) (q n : ℕ)
    (hA : A.constantCoeff = 0) (hP : n ≤ P.order)
    (hq : 2 ≤ q) (hn : 2 ≤ n) (d : σ →₀ ℕ) (hd : d.degree ≤ n) :
    coeff d ((A + P) ^ q - A ^ q) = 0 := by
  rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
  rw [map_sum, Finset.sum_eq_zero]
  intro m hm
  rw [Finset.mem_range] at hm
  apply coeff_of_lt_order
  have hAo : 1 ≤ A.order := one_le_order_iff_constCoeff_eq_zero.mpr hA
  have hterm : (m : ℕ∞) + ((q - m) * n : ℕ) ≤
      (A ^ m * P ^ (q - m) * (q.choose m : MvPowerSeries σ R)).order := by
    calc
      (m : ℕ∞) + ((q - m) * n : ℕ) =
          m • (1 : ℕ∞) + (q - m) • (n : ℕ∞) := by
            simp [nsmul_eq_mul, Nat.cast_mul]
      _ ≤ m • A.order + (q - m) • P.order :=
        add_le_add (nsmul_le_nsmul_right hAo _) (nsmul_le_nsmul_right hP _)
      _ ≤ (A ^ m).order + (P ^ (q - m)).order :=
        add_le_add (le_order_pow _) (le_order_pow _)
      _ ≤ (A ^ m * P ^ (q - m)).order := le_order_mul
      _ ≤ (A ^ m * P ^ (q - m)).order +
          ((q.choose m : MvPowerSeries σ R)).order := le_add_right le_rfl
      _ ≤ _ := le_order_mul
  apply lt_of_lt_of_le _ hterm
  have hsub : 1 ≤ q - m := by omega
  have hnlt : n < m + (q - m) * n := by
    by_cases hm0 : m = 0
    · subst m
      simp only [Nat.zero_add, Nat.sub_zero]
      nlinarith
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmul : n ≤ (q - m) * n := by nlinarith
      omega
  exact_mod_cast hd.trans_lt hnlt

private theorem lubinTateDiscrepancy_add_correction_coeff
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A : MvPowerSeries σ (RingOfIntegers K)) (hA : A.constantCoeff = 0)
    (n : ℕ) (hn : 2 ≤ n) (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d (lubinTateDiscrepancy K π
      (A + lubinTateCorrection K π A n)) = 0 := by
  let P := lubinTateCorrection K π A n
  have hP : (lubinTateCorrection K π A n).IsHomogeneous n :=
    lubinTateCorrection_isHomogeneous K π A n
  change P.IsHomogeneous n at hP
  have hnonlinear : coeff d ((A + P) ^ residueCard K - A ^ residueCard K) = 0 :=
    coeff_add_pow_sub_pow_eq_zero A P (residueCard K) n hA
      (isHomogeneous_le_order hP) (one_lt_residueCard K) hn d hd.le
  have hpowequal : coeff d ((A + P) ^ residueCard K) =
      coeff d (A ^ residueCard K) := by
    simpa only [map_sub, sub_eq_zero] using hnonlinear
  have hsubst := coeff_subst_lubinTateVariable_of_isHomogeneous K π P hP d hd
  have hcorr := lubinTateCorrectionCoeff_spec K π A d (hd ▸ hn)
  have hPcorr : coeff d P = lubinTateCorrectionCoeff K π A d (hd ▸ hn) :=
    lubinTateCorrection_coeff K π A n hn d hd
  rw [lubinTateDiscrepancy,
    subst_add (hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']))]
  simp only [map_sub, map_add, coeff_C_mul]
  rw [hsubst, hpowequal, hPcorr]
  change coeff d (A.subst (lubinTateVariable K π)) +
      uniformizerInteger K π ^ n * lubinTateCorrectionCoeff K π A d (hd ▸ hn) -
    (uniformizerInteger K π *
        (coeff d A + lubinTateCorrectionCoeff K π A d (hd ▸ hn)) +
      coeff d (A ^ residueCard K)) = 0
  have hdisc : coeff d (lubinTateDiscrepancy K π A) =
      coeff d (A.subst (lubinTateVariable K π)) -
        (uniformizerInteger K π * coeff d A + coeff d (A ^ residueCard K)) := by
    rw [lubinTateDiscrepancy]
    simp only [map_sub, map_add, coeff_C_mul]
  have hcorrn :
      (uniformizerInteger K π - uniformizerInteger K π ^ n) *
          lubinTateCorrectionCoeff K π A d (hd ▸ hn) =
        coeff d (lubinTateDiscrepancy K π A) := by
    simpa only [hd] using hcorr
  calc
    coeff d (A.subst (lubinTateVariable K π)) +
        uniformizerInteger K π ^ n * lubinTateCorrectionCoeff K π A d (hd ▸ hn) -
      (uniformizerInteger K π *
          (coeff d A + lubinTateCorrectionCoeff K π A d (hd ▸ hn)) +
        coeff d (A ^ residueCard K)) =
      coeff d (lubinTateDiscrepancy K π A) -
        (uniformizerInteger K π - uniformizerInteger K π ^ n) *
          lubinTateCorrectionCoeff K π A d (hd ▸ hn) := by rw [hdisc]; ring
    _ = 0 := by rw [hcorrn, sub_self]

private theorem lubinTateDiscrepancy_add_correction_coeff_of_lt
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A : MvPowerSeries σ (RingOfIntegers K)) (hA : A.constantCoeff = 0)
    (n : ℕ) (hn : 2 ≤ n) (d : σ →₀ ℕ) (hd : d.degree < n) :
    coeff d (lubinTateDiscrepancy K π
      (A + lubinTateCorrection K π A n)) =
        coeff d (lubinTateDiscrepancy K π A) := by
  let P := lubinTateCorrection K π A n
  have hP : (lubinTateCorrection K π A n).IsHomogeneous n :=
    lubinTateCorrection_isHomogeneous K π A n
  change P.IsHomogeneous n at hP
  have hPcoeff : coeff d P = 0 := hP.coeff_eq_zero (by omega)
  have hsubst : coeff d (P.subst (lubinTateVariable K π)) = 0 :=
    coeff_subst_lubinTateVariable_of_lt_degree K π P hP d hd
  have hnonlinear : coeff d ((A + P) ^ residueCard K - A ^ residueCard K) = 0 :=
    coeff_add_pow_sub_pow_eq_zero A P (residueCard K) n hA
      (isHomogeneous_le_order hP) (one_lt_residueCard K) hn d hd.le
  have hpowequal : coeff d ((A + P) ^ residueCard K) =
      coeff d (A ^ residueCard K) := by
    simpa only [map_sub, sub_eq_zero] using hnonlinear
  rw [lubinTateDiscrepancy,
    subst_add (hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']))]
  simp only [map_sub, map_add, coeff_C_mul]
  rw [hsubst, hPcoeff, hpowequal]
  rw [lubinTateDiscrepancy]
  simp only [map_sub, map_add, coeff_C_mul]
  ring

private theorem lubinTateCorrection_constantCoeff
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A : MvPowerSeries σ (RingOfIntegers K)) (n : ℕ) :
    (lubinTateCorrection K π A n).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_apply, lubinTateCorrection, dif_neg]
  simp

private def lubinTateLinearSeries {σ : Type*} [Fintype σ]
    (c : σ → RingOfIntegers K) : MvPowerSeries σ (RingOfIntegers K) :=
  ∑ i, C (c i) * X i

private theorem lubinTateLinearSeries_constantCoeff {σ : Type*} [Fintype σ]
    (c : σ → RingOfIntegers K) :
    (lubinTateLinearSeries K c).constantCoeff = 0 := by
  simp [lubinTateLinearSeries]

private theorem lubinTateLinearSeries_isHomogeneous {σ : Type*}
    [Fintype σ] [DecidableEq σ] (c : σ → RingOfIntegers K) :
    (lubinTateLinearSeries K c).IsHomogeneous 1 := by
  intro d hd
  by_contra hdegree
  apply hd
  rw [lubinTateLinearSeries, map_sum, Finset.sum_eq_zero]
  intro i _
  rw [coeff_C_mul, coeff_X]
  split_ifs with hdi
  · subst d
    exfalso
    apply hdegree
    simp [Finsupp.weight_single]
  · simp

private theorem lubinTateLinearSeries_coeff_single {σ : Type*}
    [Fintype σ] [DecidableEq σ] (c : σ → RingOfIntegers K) (i : σ) :
    coeff (Finsupp.single i 1) (lubinTateLinearSeries K c) = c i := by
  rw [lubinTateLinearSeries, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [coeff_C_mul, coeff_index_single_X, if_neg (Ne.symm hji)]
    simp
  · simp

private theorem lubinTateLinearSeries_discrepancy_coeff_of_degree_lt_two
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (π : Uniformizer K) (c : σ → RingOfIntegers K) (d : σ →₀ ℕ)
    (hd : d.degree < 2) :
    coeff d (lubinTateDiscrepancy K π (lubinTateLinearSeries K c)) = 0 := by
  let A := lubinTateLinearSeries K c
  have hA0 : A.constantCoeff = 0 := lubinTateLinearSeries_constantCoeff K c
  rcases (show d.degree = 0 ∨ d.degree = 1 by omega) with hzero | hone
  · have hd0 : d = 0 := Finsupp.degree_eq_zero_iff d |>.mp hzero
    subst d
    rw [coeff_zero_eq_constantCoeff, lubinTateDiscrepancy]
    have hg : HasSubst (lubinTateVariable K π :
        σ → MvPowerSeries σ (RingOfIntegers K)) :=
      hasSubst_of_constantCoeff_zero (fun i => by
        simp [lubinTateVariable,
          (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])
    rw [map_sub, map_add, constantCoeff_subst_eq_zero hg (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']) hA0]
    simp only [map_mul, map_pow, constantCoeff_C,
      lubinTateLinearSeries_constantCoeff, mul_zero]
    rw [zero_pow (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']
    simp
  · have hhom : A.IsHomogeneous 1 := by
      change (lubinTateLinearSeries K c).IsHomogeneous 1
      exact lubinTateLinearSeries_isHomogeneous K c
    have hsubst := coeff_subst_lubinTateVariable_of_isHomogeneous K π A hhom d hone
    have hpow : coeff d (A ^ residueCard K) = 0 := by
      apply coeff_of_lt_order
      apply lt_of_lt_of_le (show (d.degree : ℕ∞) < residueCard K by
        exact_mod_cast hone.trans_lt (one_lt_residueCard K))
      exact le_order_pow_of_constantCoeff_eq_zero _ hA0
    rw [lubinTateDiscrepancy]
    simp only [map_sub, map_add, coeff_C_mul]
    rw [hsubst, hpow]
    change uniformizerInteger K π ^ 1 * coeff d A -
      (uniformizerInteger K π * coeff d A + 0) = 0
    rw [pow_one]
    ring

private noncomputable def lubinTateApproximation {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) : ℕ → MvPowerSeries σ (RingOfIntegers K)
  | 0 => lubinTateLinearSeries K c
  | n + 1 => lubinTateApproximation π c n +
      lubinTateCorrection K π (lubinTateApproximation π c n) (n + 2)

private theorem lubinTateApproximation_constantCoeff {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (n : ℕ) :
    (lubinTateApproximation K π c n).constantCoeff = 0 := by
  induction n with
  | zero => exact lubinTateLinearSeries_constantCoeff K c
  | succ n ih =>
      rw [lubinTateApproximation, map_add, ih,
        lubinTateCorrection_constantCoeff, add_zero]

private theorem lubinTateApproximation_discrepancy {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (n : ℕ) (d : σ →₀ ℕ)
    (hd : d.degree < n + 2) :
    coeff d (lubinTateDiscrepancy K π (lubinTateApproximation K π c n)) = 0 := by
  induction n with
  | zero =>
      exact lubinTateLinearSeries_discrepancy_coeff_of_degree_lt_two K π c d (by simpa using hd)
  | succ n ih =>
      rw [lubinTateApproximation]
      by_cases heq : d.degree = n + 2
      · exact lubinTateDiscrepancy_add_correction_coeff K π
          (lubinTateApproximation K π c n)
          (lubinTateApproximation_constantCoeff K π c n) (n + 2) (by omega) d heq
      · rw [lubinTateDiscrepancy_add_correction_coeff_of_lt K π
          (lubinTateApproximation K π c n)
          (lubinTateApproximation_constantCoeff K π c n) (n + 2) (by omega) d (by omega)]
        exact ih (by omega)

private theorem lubinTateApproximation_coeff_succ_of_degree_ne {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (n : ℕ) (d : σ →₀ ℕ)
    (hd : d.degree ≠ n + 2) :
    coeff d (lubinTateApproximation K π c (n + 1)) =
      coeff d (lubinTateApproximation K π c n) := by
  rw [lubinTateApproximation, map_add,
    lubinTateCorrection_coeff_of_degree_ne K π _ _ d hd, add_zero]

private theorem lubinTateApproximation_coeff_stable {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) {m n : ℕ} (hmn : m ≤ n)
    (d : σ →₀ ℕ) (hd : d.degree < m + 2) :
    coeff d (lubinTateApproximation K π c n) =
      coeff d (lubinTateApproximation K π c m) := by
  induction hmn with
  | refl => rfl
  | @step n hmn ih =>
      rw [lubinTateApproximation_coeff_succ_of_degree_ne K π c n d
        (ne_of_lt (hd.trans_le (Nat.add_le_add_right hmn 2))), ih]

private noncomputable def lubinTateFunctionalSeries {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) : MvPowerSeries σ (RingOfIntegers K) := fun d =>
  coeff d (lubinTateApproximation K π c d.degree)

private theorem lubinTateFunctionalSeries_coeff_eq_approximation {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (n : ℕ) (d : σ →₀ ℕ)
    (hd : d.degree < n + 2) :
    coeff d (lubinTateFunctionalSeries K π c) =
      coeff d (lubinTateApproximation K π c n) := by
  rw [coeff_apply, lubinTateFunctionalSeries]
  by_cases hle : d.degree ≤ n
  · exact (lubinTateApproximation_coeff_stable K π c hle d (by omega)).symm
  · have hnle : n ≤ d.degree := by omega
    exact lubinTateApproximation_coeff_stable K π c hnle d (by omega)

private theorem lubinTateFunctionalSeries_constantCoeff {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) :
    (lubinTateFunctionalSeries K π c).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff,
    lubinTateFunctionalSeries_coeff_eq_approximation K π c 0 0 (by simp)]
  exact lubinTateLinearSeries_constantCoeff K c

private theorem lubinTateFunctionalSeries_coeff_single {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (i : σ) :
    coeff (Finsupp.single i 1) (lubinTateFunctionalSeries K π c) = c i := by
  rw [lubinTateFunctionalSeries_coeff_eq_approximation K π c 0 _ (by simp),
    lubinTateApproximation]
  exact lubinTateLinearSeries_coeff_single K c i

private theorem lubinTateFunctionalSeries_sub_approximation_order {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) (n : ℕ) :
    (n + 2 : ℕ) ≤ (lubinTateFunctionalSeries K π c -
      lubinTateApproximation K π c n).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [map_sub, lubinTateFunctionalSeries_coeff_eq_approximation K π c n d hd,
    sub_self]

private theorem lubinTateFunctionalSeries_discrepancy {σ : Type*}
    [Fintype σ] [DecidableEq σ] (π : Uniformizer K)
    (c : σ → RingOfIntegers K) :
    lubinTateDiscrepancy K π (lubinTateFunctionalSeries K π c) = 0 := by
  apply MvPowerSeries.ext
  intro d
  rw [coeff_zero]
  let n := d.degree
  let A := lubinTateApproximation K π c n
  let H := lubinTateFunctionalSeries K π c
  let Q := H - A
  have hA0 : A.constantCoeff = 0 := lubinTateApproximation_constantCoeff K π c n
  have hQorder : (n + 2 : ℕ) ≤ Q.order := by
    exact lubinTateFunctionalSeries_sub_approximation_order K π c n
  have hQcoeff : coeff d Q = 0 := by
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (show (d.degree : ℕ∞) < n + 2 by
      exact_mod_cast (show d.degree < n + 2 by omega)) hQorder
  have hQ0 : Q.constantCoeff = 0 := one_le_order_iff_constCoeff_eq_zero.mp
    ((show (1 : ℕ∞) ≤ n + 2 by exact_mod_cast (show 1 ≤ n + 2 by omega)).trans hQorder)
  have hsubstQ : coeff d (Q.subst (lubinTateVariable K π)) = 0 := by
    apply coeff_of_lt_order
    apply lt_of_lt_of_le (show (d.degree : ℕ∞) < Q.order by
      exact (show (d.degree : ℕ∞) < n + 2 by
        exact_mod_cast (show d.degree < n + 2 by omega)).trans_le hQorder)
    calc
      Q.order = 1 * Q.order := by simp
      _ ≤ (⨅ i, (lubinTateVariable K π i).order) * Q.order := by
        gcongr
        exact le_iInf fun i => lubinTateVariable_one_le_order K π i
      _ ≤ _ := le_order_subst
        (hasSubst_of_constantCoeff_zero (by
          simp [lubinTateVariable,
            (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])) Q
  have hnonlinear : coeff d ((A + Q) ^ residueCard K - A ^ residueCard K) = 0 :=
    coeff_add_pow_sub_pow_eq_zero A Q (residueCard K) (n + 2) hA0 hQorder
      (one_lt_residueCard K) (by omega) d (by omega)
  have hpowequal : coeff d ((A + Q) ^ residueCard K) = coeff d (A ^ residueCard K) := by
    simpa only [map_sub, sub_eq_zero] using hnonlinear
  have hHA : H = A + Q := by simp [Q]
  rw [show lubinTateFunctionalSeries K π c = H from rfl, hHA,
    lubinTateDiscrepancy,
    subst_add (hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']))]
  simp only [map_sub, map_add, coeff_C_mul]
  rw [hsubstQ, hQcoeff, hpowequal]
  have hdisc := lubinTateApproximation_discrepancy K π c n d (by omega)
  rw [lubinTateDiscrepancy] at hdisc
  simp only [map_sub, map_add, coeff_C_mul] at hdisc
  simpa only [add_zero] using hdisc

private theorem coeff_subst_lubinTateVariable_of_le_order
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (P : MvPowerSeries σ (RingOfIntegers K)) (n : ℕ) (hP : n ≤ P.order)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d (P.subst (lubinTateVariable K π)) =
      uniformizerInteger K π ^ n * coeff d P := by
  let Pn := P.homogeneousComponent n
  let Q := P - Pn
  have hPn : Pn.IsHomogeneous n := isHomogeneous_homogeneousComponent P n
  have hQorder : (n + 1 : ℕ) ≤ Q.order := by
    apply MvPowerSeries.nat_le_order
    intro e he
    rw [map_sub, coeff_homogeneousComponent]
    by_cases hen : e.degree = n
    · rw [if_pos hen, sub_self]
    · rw [if_neg hen]
      have helt : e.degree < n := by omega
      rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast helt) hP), sub_zero]
  have hQcoeff : coeff d (Q.subst (lubinTateVariable K π)) = 0 := by
    apply coeff_of_lt_order
    apply lt_of_lt_of_le (show (d.degree : ℕ∞) < n + 1 by
      exact_mod_cast (show d.degree < n + 1 by omega))
    calc
      (n + 1 : ℕ∞) = 1 * (n + 1 : ℕ∞) := by simp
      _ ≤ (⨅ i, (lubinTateVariable K π i).order) * Q.order := by
        gcongr
        · exact le_iInf fun i => lubinTateVariable_one_le_order K π i
        · exact hQorder
      _ ≤ _ := le_order_subst
        (hasSubst_of_constantCoeff_zero (by
          simp [lubinTateVariable,
            (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])) Q
  have hdecomp : P = Pn + Q := by simp [Q, Pn]
  rw [hdecomp, subst_add (hasSubst_of_constantCoeff_zero (by
    simp [lubinTateVariable,
      (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])), map_add,
    coeff_subst_lubinTateVariable_of_isHomogeneous K π Pn hPn d hd, hQcoeff,
    add_zero]
  rw [coeff_homogeneousComponent, if_pos hd]
  rw [← hdecomp]

private theorem lubinTateDiscrepancy_sub
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A B : MvPowerSeries σ (RingOfIntegers K))
    (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (n : ℕ) (hn : 2 ≤ n) (horder : n ≤ (B - A).order)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d (lubinTateDiscrepancy K π B) =
      coeff d (lubinTateDiscrepancy K π A) +
        (uniformizerInteger K π ^ n - uniformizerInteger K π) *
          (coeff d B - coeff d A) := by
  let P := B - A
  have hP0 : P.constantCoeff = 0 := by rw [map_sub, hB0, hA0, sub_zero]
  have hBA : B = A + P := by simp [P]
  have hsubst := coeff_subst_lubinTateVariable_of_le_order K π P n horder d hd
  have hnonlinear : coeff d ((A + P) ^ residueCard K - A ^ residueCard K) = 0 :=
    coeff_add_pow_sub_pow_eq_zero A P (residueCard K) n hA0 horder
      (one_lt_residueCard K) hn d hd.le
  have hpowequal : coeff d ((A + P) ^ residueCard K) = coeff d (A ^ residueCard K) := by
    simpa only [map_sub, sub_eq_zero] using hnonlinear
  rw [hBA, lubinTateDiscrepancy,
    subst_add (hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']))]
  simp only [map_sub, map_add, coeff_C_mul]
  rw [hsubst, hpowequal]
  rw [lubinTateDiscrepancy]
  simp only [map_sub, map_add, coeff_C_mul]
  change coeff d (A.subst (lubinTateVariable K π)) +
      uniformizerInteger K π ^ n * (coeff d B - coeff d A) -
        (uniformizerInteger K π * (coeff d A + (coeff d B - coeff d A)) +
          coeff d (A ^ residueCard K)) = _
  simp only [P, map_sub]
  ring

private theorem lubinTateFunctional_unique
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A B : MvPowerSeries σ (RingOfIntegers K))
    (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hA : lubinTateDiscrepancy K π A = 0)
    (hB : lubinTateDiscrepancy K π B = 0)
    (hlinear : ∀ d : σ →₀ ℕ, d.degree = 1 → coeff d A = coeff d B) :
    A = B := by
  apply MvPowerSeries.ext
  intro d
  generalize hdn : d.degree = n
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
      by_cases hn0 : n = 0
      · have hd0 : d = 0 := Finsupp.degree_eq_zero_iff d |>.mp (hdn.trans hn0)
        subst d
        rw [coeff_zero_eq_constantCoeff, hA0, hB0]
      by_cases hn1 : n = 1
      · exact hlinear d (hdn.trans hn1)
      have hn : 2 ≤ n := by omega
      have horder : (n : ℕ) ≤ (B - A).order := by
        apply MvPowerSeries.nat_le_order
        intro e he
        rw [map_sub, ih e.degree he e rfl, sub_self]
      have hdiff := lubinTateDiscrepancy_sub K π A B hA0 hB0 n hn horder d hdn
      rw [hA, hB] at hdiff
      simp only [coeff_zero, zero_add] at hdiff
      have hp : uniformizerInteger K π ≠ 0 := (uniformizerInteger_irreducible K π).ne_zero
      have hu : 1 - uniformizerInteger K π ^ (n - 1) ≠ 0 :=
        (one_sub_uniformizer_pow_isUnit K π (by omega)).ne_zero
      have hfactor : uniformizerInteger K π - uniformizerInteger K π ^ n ≠ 0 := by
        rw [show uniformizerInteger K π - uniformizerInteger K π ^ n =
          uniformizerInteger K π * (1 - uniformizerInteger K π ^ (n - 1)) by
            rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega)]]
        exact mul_ne_zero hp hu
      have hfactor' : uniformizerInteger K π ^ n - uniformizerInteger K π ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hfactor))
      have hz : coeff d B - coeff d A = 0 :=
        (mul_eq_zero.mp hdiff.symm).resolve_left hfactor'
      exact (sub_eq_zero.mp hz).symm

private theorem lubinTateDiscrepancy_eq_zero_iff {σ : Type*} [Finite σ]
    (π : Uniformizer K) (H : MvPowerSeries σ (RingOfIntegers K)) :
    lubinTateDiscrepancy K π H = 0 ↔
      H.subst (lubinTateVariable K π) =
        C (uniformizerInteger K π) * H + H ^ residueCard K := by
  rw [lubinTateDiscrepancy, sub_eq_zero]

private theorem lubinTateDiscrepancy_subst
    {σ τ : Type*} [Finite σ] [Finite τ] (π : Uniformizer K)
    (H : MvPowerSeries σ (RingOfIntegers K))
    (a : σ → MvPowerSeries τ (RingOfIntegers K))
    (hH : lubinTateDiscrepancy K π H = 0)
    (ha0 : ∀ i, (a i).constantCoeff = 0)
    (ha : ∀ i, lubinTateDiscrepancy K π (a i) = 0) :
    lubinTateDiscrepancy K π (H.subst a) = 0 := by
  let gσ : σ → MvPowerSeries σ (RingOfIntegers K) := lubinTateVariable K π
  let gτ : τ → MvPowerSeries τ (RingOfIntegers K) := lubinTateVariable K π
  have hgaσ : HasSubst gσ := hasSubst_of_constantCoeff_zero (by
    simp [gσ, lubinTateVariable,
      (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])
  have hgaτ : HasSubst gτ := hasSubst_of_constantCoeff_zero (by
    simp [gτ, lubinTateVariable,
      (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])
  have has : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [lubinTateDiscrepancy_eq_zero_iff]
  calc
    (H.subst a).subst gτ = H.subst (fun i => (a i).subst gτ) :=
      subst_comp_subst_apply has hgaτ H
    _ = H.subst (fun i => C (uniformizerInteger K π) * a i +
        (a i) ^ residueCard K) := by
      congr 1
      funext i
      exact (lubinTateDiscrepancy_eq_zero_iff K π (a i)).mp (ha i)
    _ = H.subst (fun i => (gσ i).subst a) := by
      congr 1
      funext i
      simp [gσ, lubinTateVariable, subst_add has, subst_mul has,
        subst_pow has, subst_C, subst_X has]
    _ = (H.subst gσ).subst a := (subst_comp_subst_apply hgaσ has H).symm
    _ = (C (uniformizerInteger K π) * H + H ^ residueCard K).subst a := by
      rw [(lubinTateDiscrepancy_eq_zero_iff K π H).mp hH]
    _ = C (uniformizerInteger K π) * H.subst a +
        (H.subst a) ^ residueCard K := by
      rw [subst_add has, subst_mul has, subst_pow has, subst_C]

private theorem finsupp_eq_single_of_degree_eq_one
    {σ : Type*} (d : σ →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  exact Finsupp.sum_eq_one_iff d |>.mp hd

private theorem coeff_finsuppProd_eq_zero_of_degree_lt
    {σ τ R : Type*} [CommRing R] (a : σ → MvPowerSeries τ R)
    (ha0 : ∀ i, (a i).constantCoeff = 0)
    (e : σ →₀ ℕ) (d : τ →₀ ℕ) (hde : d.degree < e.degree) :
    coeff d (e.prod fun i m => a i ^ m) = 0 := by
  apply coeff_of_lt_order
  apply lt_of_lt_of_le (show (d.degree : ℕ∞) < e.degree by exact_mod_cast hde)
  change (e.degree : ℕ∞) ≤ (∏ i ∈ e.support, a i ^ e i).order
  calc
    (e.degree : ℕ∞) = ∑ i ∈ e.support, (e i : ℕ∞) := by
      change (↑(∑ i ∈ e.support, e i) : ℕ∞) = _
      simp
    _ ≤ ∑ i ∈ e.support, (a i ^ e i).order := Finset.sum_le_sum fun i _ => by
      calc
        (e i : ℕ∞) = e i • (1 : ℕ∞) := by simp
        _ ≤ e i • (a i).order := nsmul_le_nsmul_right
          (one_le_order_iff_constCoeff_eq_zero.mpr (ha0 i)) _
        _ ≤ _ := le_order_pow _
    _ ≤ _ := le_order_prod _ _

private theorem coeff_subst_eq_of_linear
    {σ τ : Type*} [Finite σ] (H J : MvPowerSeries σ (RingOfIntegers K))
    (a b : σ → MvPowerSeries τ (RingOfIntegers K))
    (hH0 : H.constantCoeff = 0) (hJ0 : J.constantCoeff = 0)
    (ha0 : ∀ i, (a i).constantCoeff = 0) (hb0 : ∀ i, (b i).constantCoeff = 0)
    (hHJ : ∀ i, coeff (Finsupp.single i 1) H = coeff (Finsupp.single i 1) J)
    (hab : ∀ i d, d.degree = 1 → coeff d (a i) = coeff d (b i))
    (d : τ →₀ ℕ) (hd : d.degree = 1) :
    coeff d (H.subst a) = coeff d (J.subst b) := by
  have has : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hbs : HasSubst b := hasSubst_of_constantCoeff_zero hb0
  rw [coeff_subst has, coeff_subst hbs]
  apply finsum_congr
  intro e
  rcases lt_trichotomy e.degree 1 with he | he | he
  · have he0 : e = 0 := Finsupp.degree_eq_zero_iff e |>.mp (by omega)
    subst e
    simp [hH0, hJ0]
  · obtain ⟨i, rfl⟩ := finsupp_eq_single_of_degree_eq_one e he
    simp [hHJ i, hab i d hd]
  · have ha := coeff_finsuppProd_eq_zero_of_degree_lt a ha0 e d (hd.trans_lt he)
    have hb := coeff_finsuppProd_eq_zero_of_degree_lt b hb0 e d (hd.trans_lt he)
    rw [ha, hb, smul_zero, smul_zero]

private theorem lubinTateSeries_eq (π : Uniformizer K) :
    lubinTateSeries K π =
      PowerSeries.C (uniformizerInteger K π) * PowerSeries.X +
        PowerSeries.X ^ residueCard K := by
  rw [lubinTateSeries, lubinTatePolynomial]
  simp

private theorem subst_lubinTateSeries {σ : Type*} [Finite σ]
    (π : Uniformizer K) (H : MvPowerSeries σ (RingOfIntegers K))
    (hH0 : H.constantCoeff = 0) :
    MvPowerSeries.subst (fun _ : Unit => H) (lubinTateSeries K π) =
      C (uniformizerInteger K π) * H + H ^ residueCard K := by
  have hH : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH0
  change PowerSeries.subst H (lubinTateSeries K π) = _
  rw [lubinTateSeries_eq K π, PowerSeries.subst_add hH,
    PowerSeries.subst_mul hH, PowerSeries.subst_pow hH,
    PowerSeries.subst_C, PowerSeries.subst_X hH]

private theorem subst_X_lubinTateSeries {σ : Type*} [Finite σ]
    (π : Uniformizer K) (i : σ) :
    MvPowerSeries.subst (fun _ : Unit => X i) (lubinTateSeries K π) =
      lubinTateVariable K π i := by
  rw [subst_lubinTateSeries K π (X i) (by simp), lubinTateVariable]

private theorem lubinTateFunctional_unique_of_coeff_single
    {σ : Type*} [Finite σ] (π : Uniformizer K)
    (A B : MvPowerSeries σ (RingOfIntegers K))
    (hA0 : A.constantCoeff = 0) (hB0 : B.constantCoeff = 0)
    (hA : lubinTateDiscrepancy K π A = 0)
    (hB : lubinTateDiscrepancy K π B = 0)
    (hsingle : ∀ i, coeff (Finsupp.single i 1) A =
      coeff (Finsupp.single i 1) B) : A = B := by
  apply lubinTateFunctional_unique K π A B hA0 hB0 hA hB
  intro d hd
  obtain ⟨i, rfl⟩ := finsupp_eq_single_of_degree_eq_one d hd
  exact hsingle i

private theorem lubinTateVariable_discrepancy {σ : Type*} [Finite σ]
    (π : Uniformizer K) (i : σ) :
    lubinTateDiscrepancy K π (X i) = 0 := by
  rw [lubinTateDiscrepancy_eq_zero_iff]
  have hg : HasSubst (lubinTateVariable K π :
      σ → MvPowerSeries σ (RingOfIntegers K)) :=
    hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])
  rw [subst_X hg]
  rfl

private theorem lubinTateZero_discrepancy {σ : Type*} [Finite σ]
    (π : Uniformizer K) :
    lubinTateDiscrepancy K π (0 : MvPowerSeries σ (RingOfIntegers K)) = 0 := by
  rw [lubinTateDiscrepancy_eq_zero_iff]
  have hg : HasSubst (lubinTateVariable K π :
      σ → MvPowerSeries σ (RingOfIntegers K)) :=
    hasSubst_of_constantCoeff_zero (by
      simp [lubinTateVariable,
        (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne'])
  rw [← substAlgHom_apply hg, map_zero]
  simp [zero_pow (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']

private noncomputable def lubinTateFormalGroupSeries (π : Uniformizer K) :
    MvPowerSeries (Fin 2) (RingOfIntegers K) :=
  lubinTateFunctionalSeries K π (fun _ => 1)

private noncomputable def lubinTateEndomorphismSeries (π : Uniformizer K)
    (a : RingOfIntegers K) : PowerSeries (RingOfIntegers K) :=
  lubinTateFunctionalSeries K π (fun _ : Unit => a)

private theorem lubinTateFormalGroupSeries_constantCoeff (π : Uniformizer K) :
    (lubinTateFormalGroupSeries K π).constantCoeff = 0 :=
  lubinTateFunctionalSeries_constantCoeff K π _

private theorem lubinTateFormalGroupSeries_coeff (π : Uniformizer K) (i : Fin 2) :
    coeff (Finsupp.single i 1) (lubinTateFormalGroupSeries K π) = 1 :=
  lubinTateFunctionalSeries_coeff_single K π _ i

private theorem lubinTateFormalGroupSeries_discrepancy (π : Uniformizer K) :
    lubinTateDiscrepancy K π (lubinTateFormalGroupSeries K π) = 0 :=
  lubinTateFunctionalSeries_discrepancy K π _

private theorem lubinTateEndomorphismSeries_constantCoeff (π : Uniformizer K)
    (a : RingOfIntegers K) :
    (lubinTateEndomorphismSeries K π a).constantCoeff = 0 :=
  lubinTateFunctionalSeries_constantCoeff K π _

private theorem lubinTateEndomorphismSeries_coeff_one (π : Uniformizer K)
    (a : RingOfIntegers K) :
    PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π a) = a :=
  lubinTateFunctionalSeries_coeff_single K π _ ()

private theorem lubinTateEndomorphismSeries_discrepancy (π : Uniformizer K)
    (a : RingOfIntegers K) :
    lubinTateDiscrepancy K π (lubinTateEndomorphismSeries K π a) = 0 :=
  lubinTateFunctionalSeries_discrepancy K π _

private theorem lubinTateEndomorphismSeries_zero (π : Uniformizer K) :
    lubinTateEndomorphismSeries K π 0 = 0 := by
  apply lubinTateFunctional_unique_of_coeff_single K π
  · exact lubinTateEndomorphismSeries_constantCoeff K π 0
  · rfl
  · exact lubinTateEndomorphismSeries_discrepancy K π 0
  · exact lubinTateZero_discrepancy K π
  · intro i
    rcases i with ⟨⟩
    change PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π 0) =
      PowerSeries.coeff 1 0
    rw [lubinTateEndomorphismSeries_coeff_one]
    simp

private theorem lubinTateEndomorphismSeries_one (π : Uniformizer K) :
    lubinTateEndomorphismSeries K π 1 = PowerSeries.X := by
  apply lubinTateFunctional_unique_of_coeff_single K π
  · exact lubinTateEndomorphismSeries_constantCoeff K π 1
  · simp [PowerSeries.constantCoeff, PowerSeries.X]
  · exact lubinTateEndomorphismSeries_discrepancy K π 1
  · exact lubinTateVariable_discrepancy K π ()
  · intro i
    rcases i with ⟨⟩
    change PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π 1) =
      PowerSeries.coeff 1 PowerSeries.X
    rw [lubinTateEndomorphismSeries_coeff_one]
    simp [PowerSeries.coeff_X]

private theorem lubinTateSeries_constantCoeff (π : Uniformizer K) :
    PowerSeries.constantCoeff (lubinTateSeries K π) = 0 := by
  rw [lubinTateSeries_eq]
  simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, mul_zero]
  rw [zero_pow (Nat.zero_lt_one.trans (one_lt_residueCard K)).ne']
  simp

private theorem lubinTateSeries_coeff_one (π : Uniformizer K) :
    PowerSeries.coeff 1 (lubinTateSeries K π) = uniformizerInteger K π := by
  rw [lubinTateSeries_eq]
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
    if_pos rfl, mul_one, PowerSeries.coeff_X_pow,
    if_neg (one_lt_residueCard K).ne]
  simp

private theorem lubinTateSeries_discrepancy (π : Uniformizer K) :
    lubinTateDiscrepancy K π (lubinTateSeries K π) = 0 := by
  rw [lubinTateDiscrepancy_eq_zero_iff]
  have hs0 := lubinTateSeries_constantCoeff K π
  have hg : (lubinTateVariable K π : Unit →
      PowerSeries (RingOfIntegers K)) = fun _ => lubinTateSeries K π := by
    funext i
    rcases i with ⟨⟩
    rw [lubinTateVariable, lubinTateSeries_eq]
    rfl
  rw [hg, subst_lubinTateSeries K π (lubinTateSeries K π) hs0]

private theorem lubinTateEndomorphismSeries_uniformizer (π : Uniformizer K) :
    lubinTateEndomorphismSeries K π (uniformizerInteger K π) = lubinTateSeries K π := by
  apply lubinTateFunctional_unique_of_coeff_single K π
  · exact lubinTateEndomorphismSeries_constantCoeff K π _
  · exact lubinTateSeries_constantCoeff K π
  · exact lubinTateEndomorphismSeries_discrepancy K π _
  · exact lubinTateSeries_discrepancy K π
  · intro i
    rcases i with ⟨⟩
    change PowerSeries.coeff 1
      (lubinTateEndomorphismSeries K π (uniformizerInteger K π)) =
        PowerSeries.coeff 1 (lubinTateSeries K π)
    rw [lubinTateEndomorphismSeries_coeff_one, lubinTateSeries_coeff_one]

private theorem lubinTateEndomorphismSeries_mul (π : Uniformizer K)
    (a b : RingOfIntegers K) :
    lubinTateEndomorphismSeries K π (a * b) =
      PowerSeries.subst (lubinTateEndomorphismSeries K π b)
        (lubinTateEndomorphismSeries K π a) := by
  let Ea := lubinTateEndomorphismSeries K π a
  let Eb := lubinTateEndomorphismSeries K π b
  let C : PowerSeries (RingOfIntegers K) := PowerSeries.subst Eb Ea
  have hC0 : C.constantCoeff = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero
      (lubinTateEndomorphismSeries_constantCoeff K π b) Ea
      (lubinTateEndomorphismSeries_constantCoeff K π a)
  have hC : lubinTateDiscrepancy K π C = 0 := by
    apply lubinTateDiscrepancy_subst K π Ea (fun _ : Unit => Eb)
    · exact lubinTateEndomorphismSeries_discrepancy K π a
    · intro i
      change Eb.constantCoeff = 0
      exact lubinTateEndomorphismSeries_constantCoeff K π b
    · intro i
      exact lubinTateEndomorphismSeries_discrepancy K π b
  apply lubinTateFunctional_unique_of_coeff_single K π
  · exact lubinTateEndomorphismSeries_constantCoeff K π (a * b)
  · exact hC0
  · exact lubinTateEndomorphismSeries_discrepancy K π (a * b)
  · exact hC
  · intro i
    rcases i with ⟨⟩
    change PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π (a * b)) =
      PowerSeries.coeff 1 C
    rw [lubinTateEndomorphismSeries_coeff_one]
    have hlin := coeff_subst_eq_of_linear K Ea
      (lubinTateLinearSeries K (fun _ : Unit => a))
      (fun _ : Unit => Eb)
      (fun _ : Unit => lubinTateLinearSeries K (fun _ : Unit => b))
      (lubinTateEndomorphismSeries_constantCoeff K π a)
      (lubinTateLinearSeries_constantCoeff K _)
      (by
        intro i
        change Eb.constantCoeff = 0
        exact lubinTateEndomorphismSeries_constantCoeff K π b)
      (by
        intro i
        exact lubinTateLinearSeries_constantCoeff K _)
      (fun j => by
        rcases j with ⟨⟩
        change PowerSeries.coeff 1 Ea = PowerSeries.coeff 1
          (lubinTateLinearSeries K (fun _ : Unit => a))
        rw [lubinTateEndomorphismSeries_coeff_one]
        symm
        change coeff (Finsupp.single () 1)
          (lubinTateLinearSeries K (fun _ : Unit => a)) = a
        exact lubinTateLinearSeries_coeff_single K _ ())
      (fun j d hd => by
        rcases j with ⟨⟩
        obtain ⟨k, rfl⟩ := finsupp_eq_single_of_degree_eq_one d hd
        rcases k with ⟨⟩
        change PowerSeries.coeff 1 Eb = PowerSeries.coeff 1
          (lubinTateLinearSeries K (fun _ : Unit => b))
        rw [lubinTateEndomorphismSeries_coeff_one]
        symm
        change coeff (Finsupp.single () 1)
          (lubinTateLinearSeries K (fun _ : Unit => b)) = b
        exact lubinTateLinearSeries_coeff_single K _ ())
      (Finsupp.single () 1) (by simp)
    change PowerSeries.coeff 1 C = _ at hlin
    rw [hlin]
    change a * b = coeff (Finsupp.single () 1)
      ((lubinTateLinearSeries K (fun _ : Unit => a)).subst
        (fun _ : Unit => lubinTateLinearSeries K (fun _ : Unit => b)))
    have hLa : lubinTateLinearSeries K (fun _ : Unit => a) =
        MvPowerSeries.C a * X () := by simp [lubinTateLinearSeries]
    have hLb : lubinTateLinearSeries K (fun _ : Unit => b) =
        MvPowerSeries.C b * X () := by simp [lubinTateLinearSeries]
    rw [hLa, hLb]
    have hbsubst : HasSubst (fun _ : Unit => (MvPowerSeries.C b * X () :
        PowerSeries (RingOfIntegers K))) :=
      hasSubst_of_constantCoeff_zero (by simp)
    rw [subst_mul hbsubst, subst_C, subst_X hbsubst,
      coeff_C_mul, coeff_C_mul, coeff_X]
    simp

private theorem coeff_subst_binary {τ : Type*}
    (F : MvPowerSeries (Fin 2) (RingOfIntegers K))
    (f g : MvPowerSeries τ (RingOfIntegers K))
    (hF0 : F.constantCoeff = 0) (hf0 : f.constantCoeff = 0)
    (hg0 : g.constantCoeff = 0) (d : τ →₀ ℕ) (hd : d.degree = 1) :
    coeff d (F.subst ![f, g]) =
      coeff (Finsupp.single 0 1) F * coeff d f +
        coeff (Finsupp.single 1 1) F * coeff d g := by
  let v : Fin 2 → MvPowerSeries τ (RingOfIntegers K) := ![f, g]
  have hv0 : ∀ i, (v i).constantCoeff = 0 := by
    intro i
    fin_cases i <;> assumption
  have hv : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  rw [coeff_subst hv]
  let e0 : Fin 2 →₀ ℕ := Finsupp.single 0 1
  let e1 : Fin 2 →₀ ℕ := Finsupp.single 1 1
  rw [finsum_eq_finsetSum_of_support_subset _ (s := {e0, e1})]
  · have he01 : e0 ≠ e1 := by
      intro h
      have h0 := DFunLike.congr_fun h (0 : Fin 2)
      simp [e0, e1] at h0
    have hp0 : e0.prod (fun i m => v i ^ m) = f := by
      simp [e0, v, Finsupp.prod]
    have hp1 : e1.prod (fun i m => v i ^ m) = g := by
      simp [e1, v, Finsupp.prod]
    rw [Finset.sum_insert (by simp [he01]), Finset.sum_singleton, hp0, hp1]
    simp only [smul_eq_mul, e0, e1]
  · intro e he
    change coeff e F • coeff d (e.prod fun i m => v i ^ m) ≠ 0 at he
    by_cases he0 : e.degree = 0
    · have : e = 0 := Finsupp.degree_eq_zero_iff e |>.mp he0
      subst e
      simp [hF0] at he
    by_cases he1 : e.degree = 1
    · obtain ⟨i, rfl⟩ := finsupp_eq_single_of_degree_eq_one e he1
      fin_cases i <;> simp [e0, e1]
    · have hgt : 1 < e.degree := by omega
      have hp := coeff_finsuppProd_eq_zero_of_degree_lt v hv0 e d (hd.trans_lt hgt)
      exact (he (by rw [hp, smul_zero])).elim

set_option maxHeartbeats 800000 in
-- Degree-one coefficient reduction through nested substitutions is elaboration-intensive.
private theorem lubinTateEndomorphismSeries_add (π : Uniformizer K)
    (a b : RingOfIntegers K) :
    lubinTateEndomorphismSeries K π (a + b) =
      (lubinTateFormalGroupSeries K π).subst ![
        lubinTateEndomorphismSeries K π a,
        lubinTateEndomorphismSeries K π b] := by
  let F := lubinTateFormalGroupSeries K π
  let Ea := lubinTateEndomorphismSeries K π a
  let Eb := lubinTateEndomorphismSeries K π b
  let v : Fin 2 → PowerSeries (RingOfIntegers K) := ![Ea, Eb]
  let C := F.subst v
  have hv0 : ∀ i, (v i).constantCoeff = 0 := by
    intro i
    fin_cases i
    · exact lubinTateEndomorphismSeries_constantCoeff K π a
    · exact lubinTateEndomorphismSeries_constantCoeff K π b
  have hv : HasSubst v := hasSubst_of_constantCoeff_zero hv0
  have hC0 : C.constantCoeff = 0 :=
    constantCoeff_subst_eq_zero hv hv0 (lubinTateFormalGroupSeries_constantCoeff K π)
  have hC : lubinTateDiscrepancy K π C = 0 := by
    apply lubinTateDiscrepancy_subst K π F v
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · exact hv0
    · intro i
      fin_cases i
      · exact lubinTateEndomorphismSeries_discrepancy K π a
      · exact lubinTateEndomorphismSeries_discrepancy K π b
  apply lubinTateFunctional_unique_of_coeff_single K π
  · exact lubinTateEndomorphismSeries_constantCoeff K π (a + b)
  · exact hC0
  · exact lubinTateEndomorphismSeries_discrepancy K π (a + b)
  · exact hC
  · intro i
    rcases i with ⟨⟩
    change PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π (a + b)) =
      PowerSeries.coeff 1 C
    rw [lubinTateEndomorphismSeries_coeff_one]
    change a + b = PowerSeries.coeff 1 (F.subst ![Ea, Eb])
    rw [show PowerSeries.coeff 1 (F.subst ![Ea, Eb]) =
        coeff (Finsupp.single () 1) (F.subst ![Ea, Eb]) from rfl,
      coeff_subst_binary K F Ea Eb
      (lubinTateFormalGroupSeries_constantCoeff K π)
      (lubinTateEndomorphismSeries_constantCoeff K π a)
      (lubinTateEndomorphismSeries_constantCoeff K π b)
      (Finsupp.single () 1) (by simp),
      lubinTateFormalGroupSeries_coeff, lubinTateFormalGroupSeries_coeff]
    change a + b = 1 * PowerSeries.coeff 1 Ea + 1 * PowerSeries.coeff 1 Eb
    rw [lubinTateEndomorphismSeries_coeff_one,
      lubinTateEndomorphismSeries_coeff_one]
    ring

private theorem lubinTateFormalGroupSeries_comm (π : Uniformizer K) :
    lubinTateFormalGroupSeries K π =
      (lubinTateFormalGroupSeries K π).subst ![X (1 : Fin 2), X (0 : Fin 2)] := by
  let F := lubinTateFormalGroupSeries K π
  let v : Fin 2 → MvPowerSeries (Fin 2) (RingOfIntegers K) := ![X 1, X 0]
  let C := F.subst v
  have hv0 : ∀ i, (v i).constantCoeff = 0 := by intro i; fin_cases i <;> simp [v]
  have hC0 : C.constantCoeff = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hv0) hv0
      (lubinTateFormalGroupSeries_constantCoeff K π)
  have hC : lubinTateDiscrepancy K π C = 0 := by
    apply lubinTateDiscrepancy_subst K π F v
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · exact hv0
    · intro i
      fin_cases i
      · exact lubinTateVariable_discrepancy K π 1
      · exact lubinTateVariable_discrepancy K π 0
  apply lubinTateFunctional_unique_of_coeff_single K π F C
  · exact lubinTateFormalGroupSeries_constantCoeff K π
  · exact hC0
  · exact lubinTateFormalGroupSeries_discrepancy K π
  · exact hC
  · intro i
    rw [lubinTateFormalGroupSeries_coeff]
    change 1 = coeff (Finsupp.single i 1) (F.subst ![X 1, X 0])
    rw [coeff_subst_binary K F (X 1) (X 0)
      (lubinTateFormalGroupSeries_constantCoeff K π) (by simp) (by simp)
      (Finsupp.single i 1) (by simp),
      lubinTateFormalGroupSeries_coeff, lubinTateFormalGroupSeries_coeff]
    fin_cases i <;> simp [coeff_X, Finsupp.single_left_inj]

private theorem lubinTateFormalGroupSeries_assoc (π : Uniformizer K) :
    (lubinTateFormalGroupSeries K π).subst ![
        (lubinTateFormalGroupSeries K π).subst ![
          X (R := RingOfIntegers K) (0 : Fin 3), X (1 : Fin 3)], X (2 : Fin 3)] =
      (lubinTateFormalGroupSeries K π).subst ![
        X (R := RingOfIntegers K) (0 : Fin 3),
        (lubinTateFormalGroupSeries K π).subst ![X (1 : Fin 3), X (2 : Fin 3)]] := by
  let F := lubinTateFormalGroupSeries K π
  let A : MvPowerSeries (Fin 3) (RingOfIntegers K) := F.subst ![X 0, X 1]
  let B : MvPowerSeries (Fin 3) (RingOfIntegers K) := F.subst ![X 1, X 2]
  let L : MvPowerSeries (Fin 3) (RingOfIntegers K) := F.subst ![A, X 2]
  let R : MvPowerSeries (Fin 3) (RingOfIntegers K) := F.subst ![X 0, B]
  have hA0 : A.constantCoeff = 0 := constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
    (by intro i; fin_cases i <;> simp) (lubinTateFormalGroupSeries_constantCoeff K π)
  have hB0 : B.constantCoeff = 0 := constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
    (by intro i; fin_cases i <;> simp) (lubinTateFormalGroupSeries_constantCoeff K π)
  have hA : lubinTateDiscrepancy K π A = 0 := by
    apply lubinTateDiscrepancy_subst K π F ![X 0, X 1]
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i
      · exact lubinTateVariable_discrepancy K π 0
      · exact lubinTateVariable_discrepancy K π 1
  have hB : lubinTateDiscrepancy K π B = 0 := by
    apply lubinTateDiscrepancy_subst K π F ![X 1, X 2]
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · intro i; fin_cases i <;> simp
    · intro i; fin_cases i
      · exact lubinTateVariable_discrepancy K π 1
      · exact lubinTateVariable_discrepancy K π 2
  have hL0 : L.constantCoeff = 0 := constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hA0]))
    (by intro i; fin_cases i <;> simp [hA0]) (lubinTateFormalGroupSeries_constantCoeff K π)
  have hR0 : R.constantCoeff = 0 := constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hB0]))
    (by intro i; fin_cases i <;> simp [hB0]) (lubinTateFormalGroupSeries_constantCoeff K π)
  have hL : lubinTateDiscrepancy K π L = 0 := by
    apply lubinTateDiscrepancy_subst K π F ![A, X 2]
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · intro i; fin_cases i <;> simp [hA0]
    · intro i; fin_cases i
      · exact hA
      · exact lubinTateVariable_discrepancy K π 2
  have hR : lubinTateDiscrepancy K π R = 0 := by
    apply lubinTateDiscrepancy_subst K π F ![X 0, B]
    · exact lubinTateFormalGroupSeries_discrepancy K π
    · intro i; fin_cases i <;> simp [hB0]
    · intro i; fin_cases i
      · exact lubinTateVariable_discrepancy K π 0
      · exact hB
  apply lubinTateFunctional_unique_of_coeff_single K π L R hL0 hR0 hL hR
  intro i
  have hAi : coeff (Finsupp.single i 1) A =
      coeff (Finsupp.single i 1) (X 0) + coeff (Finsupp.single i 1) (X 1) := by
    rw [coeff_subst_binary K F (X 0) (X 1)
      (lubinTateFormalGroupSeries_constantCoeff K π) (by simp) (by simp)
      (Finsupp.single i 1) (by simp),
      lubinTateFormalGroupSeries_coeff, lubinTateFormalGroupSeries_coeff]
    ring
  have hBi : coeff (Finsupp.single i 1) B =
      coeff (Finsupp.single i 1) (X 1) + coeff (Finsupp.single i 1) (X 2) := by
    rw [coeff_subst_binary K F (X 1) (X 2)
      (lubinTateFormalGroupSeries_constantCoeff K π) (by simp) (by simp)
      (Finsupp.single i 1) (by simp),
      lubinTateFormalGroupSeries_coeff, lubinTateFormalGroupSeries_coeff]
    ring
  change coeff (Finsupp.single i 1) (F.subst ![A, X 2]) =
    coeff (Finsupp.single i 1) (F.subst ![X 0, B])
  rw [coeff_subst_binary K F A (X 2)
      (lubinTateFormalGroupSeries_constantCoeff K π) hA0 (by simp)
      (Finsupp.single i 1) (by simp),
    coeff_subst_binary K F (X 0) B
      (lubinTateFormalGroupSeries_constantCoeff K π) (by simp) hB0
      (Finsupp.single i 1) (by simp),
    lubinTateFormalGroupSeries_coeff, lubinTateFormalGroupSeries_coeff,
    hAi, hBi]
  fin_cases i <;> simp [coeff_X] <;> ring

private noncomputable def lubinTateFormalGroup (π : Uniformizer K) :
    FormalGroup (RingOfIntegers K) where
  toPowerSeries := lubinTateFormalGroupSeries K π
  zero_constantCoeff := lubinTateFormalGroupSeries_constantCoeff K π
  lin_coeff_X := lubinTateFormalGroupSeries_coeff K π 0
  lin_coeff_Y := lubinTateFormalGroupSeries_coeff K π 1
  assoc := lubinTateFormalGroupSeries_assoc K π

private theorem lubinTateFormalGroup_isComm (π : Uniformizer K) :
    (lubinTateFormalGroup K π).IsComm := by
  constructor
  exact lubinTateFormalGroupSeries_comm K π

set_option maxHeartbeats 800000 in
-- Unfolding the two-variable substitution identity is elaboration-intensive.
private theorem lubinTateFormalGroup_functional (π : Uniformizer K) :
    MvPowerSeries.subst (fun _ : Unit => (lubinTateFormalGroup K π).toPowerSeries)
        (lubinTateSeries K π) =
      (lubinTateFormalGroup K π).toPowerSeries.subst ![
        MvPowerSeries.subst (fun _ : Unit => X (0 : Fin 2)) (lubinTateSeries K π),
        MvPowerSeries.subst (fun _ : Unit => X (1 : Fin 2)) (lubinTateSeries K π)] := by
  change MvPowerSeries.subst (fun _ : Unit => lubinTateFormalGroupSeries K π)
      (lubinTateSeries K π) =
    (lubinTateFormalGroupSeries K π).subst ![
      MvPowerSeries.subst (fun _ : Unit => X (0 : Fin 2)) (lubinTateSeries K π),
      MvPowerSeries.subst (fun _ : Unit => X (1 : Fin 2)) (lubinTateSeries K π)]
  rw [subst_lubinTateSeries K π _ (lubinTateFormalGroupSeries_constantCoeff K π),
    subst_X_lubinTateSeries K π 0, subst_X_lubinTateSeries K π 1]
  have hv : (![lubinTateVariable K π 0, lubinTateVariable K π 1] :
      Fin 2 → MvPowerSeries (Fin 2) (RingOfIntegers K)) = lubinTateVariable K π := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact (lubinTateDiscrepancy_eq_zero_iff K π _).mp
    (lubinTateFormalGroupSeries_discrepancy K π) |>.symm

private theorem lubinTateEndomorphismSeries_functional (π : Uniformizer K)
    (a : RingOfIntegers K) :
    PowerSeries.subst (lubinTateEndomorphismSeries K π a) (lubinTateSeries K π) =
      PowerSeries.subst (lubinTateSeries K π) (lubinTateEndomorphismSeries K π a) := by
  have hE0 := lubinTateEndomorphismSeries_constantCoeff K π a
  change MvPowerSeries.subst (fun _ : Unit => lubinTateEndomorphismSeries K π a)
      (lubinTateSeries K π) =
    MvPowerSeries.subst (fun _ : Unit => lubinTateSeries K π)
      (lubinTateEndomorphismSeries K π a)
  rw [subst_lubinTateSeries K π _ hE0]
  have hg : (fun _ : Unit => lubinTateSeries K π) =
      (lubinTateVariable K π : Unit → PowerSeries (RingOfIntegers K)) := by
    funext i
    rcases i with ⟨⟩
    rw [lubinTateSeries_eq, lubinTateVariable]
    rfl
  rw [hg]
  exact (lubinTateDiscrepancy_eq_zero_iff K π _).mp
    (lubinTateEndomorphismSeries_discrepancy K π a) |>.symm

/-- A formal `𝒪_K`-module satisfying the Lubin--Tate functional equations. -/
structure LubinTateFormalModule (π : Uniformizer K) where
  /-- The commutative one-dimensional formal group. -/
  formalGroup : FormalGroup (RingOfIntegers K)
  /-- Commutativity of the formal group. -/
  isComm : formalGroup.IsComm
  /-- The endomorphism `[a](X)`. -/
  endomorphism : RingOfIntegers K → PowerSeries (RingOfIntegers K)
  /-- Linear coefficient of `[a]`. -/
  linearCoeff : ∀ a, PowerSeries.coeff 1 (endomorphism a) = a
  /-- Constant coefficient of `[a]`. -/
  constantCoeff : ∀ a, PowerSeries.constantCoeff (endomorphism a) = 0
  /-- The defining equation `f(F(X,Y)) = F(f(X),f(Y))`. -/
  formalGroup_functional :
    MvPowerSeries.subst (fun _ : Unit => formalGroup.toPowerSeries)
        (lubinTateSeries K π) =
      formalGroup.toPowerSeries.subst ![
        MvPowerSeries.subst (fun _ : Unit => MvPowerSeries.X (0 : Fin 2))
          (lubinTateSeries K π),
        MvPowerSeries.subst (fun _ : Unit => MvPowerSeries.X (1 : Fin 2))
          (lubinTateSeries K π)]
  /-- The defining equation `f([a](X)) = [a](f(X))`. -/
  functional : ∀ a,
    PowerSeries.subst (endomorphism a) (lubinTateSeries K π) =
      PowerSeries.subst (lubinTateSeries K π) (endomorphism a)
  /-- `[0](X)=0`. -/
  zero_action : endomorphism 0 = 0
  /-- `[1](X)=X`. -/
  one_action : endomorphism 1 = PowerSeries.X
  /-- `[a+b]=[a]+_F[b]`. -/
  map_add : ∀ a b,
    endomorphism (a + b) = formalGroup.toPowerSeries.subst ![endomorphism a, endomorphism b]
  /-- `[ab]=[a]∘[b]`; `subst h g` means `g(h)`. -/
  map_mul : ∀ a b,
    endomorphism (a * b) = PowerSeries.subst (endomorphism b) (endomorphism a)
  /-- `[π]=f`. -/
  uniformizer_action : endomorphism (uniformizerInteger K π) = lubinTateSeries K π

private noncomputable def canonicalLubinTateFormalModule (π : Uniformizer K) :
    LubinTateFormalModule K π where
  formalGroup := lubinTateFormalGroup K π
  isComm := lubinTateFormalGroup_isComm K π
  endomorphism := lubinTateEndomorphismSeries K π
  linearCoeff := lubinTateEndomorphismSeries_coeff_one K π
  constantCoeff := lubinTateEndomorphismSeries_constantCoeff K π
  formalGroup_functional := lubinTateFormalGroup_functional K π
  functional := lubinTateEndomorphismSeries_functional K π
  zero_action := lubinTateEndomorphismSeries_zero K π
  one_action := lubinTateEndomorphismSeries_one K π
  map_add := lubinTateEndomorphismSeries_add K π
  map_mul := lubinTateEndomorphismSeries_mul K π
  uniformizer_action := lubinTateEndomorphismSeries_uniformizer K π

variable (π : Uniformizer K)

private theorem LubinTateFormalModule.formalGroup_discrepancy
    (G : LubinTateFormalModule K π) :
    lubinTateDiscrepancy K π G.formalGroup.toPowerSeries = 0 := by
  have h := G.formalGroup_functional
  rw [subst_lubinTateSeries K π _ G.formalGroup.zero_constantCoeff,
    subst_X_lubinTateSeries K π 0, subst_X_lubinTateSeries K π 1] at h
  have hv : (![lubinTateVariable K π 0, lubinTateVariable K π 1] :
      Fin 2 → MvPowerSeries (Fin 2) (RingOfIntegers K)) = lubinTateVariable K π := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact (lubinTateDiscrepancy_eq_zero_iff K π _).mpr h.symm

private theorem LubinTateFormalModule.endomorphism_discrepancy
    (G : LubinTateFormalModule K π) (a : RingOfIntegers K) :
    lubinTateDiscrepancy K π (G.endomorphism a) = 0 := by
  have h := G.functional a
  change MvPowerSeries.subst (fun _ : Unit => G.endomorphism a) (lubinTateSeries K π) =
    MvPowerSeries.subst (fun _ : Unit => lubinTateSeries K π) (G.endomorphism a) at h
  rw [subst_lubinTateSeries K π _ (G.constantCoeff a)] at h
  have hg : (fun _ : Unit => lubinTateSeries K π) =
      (lubinTateVariable K π : Unit → PowerSeries (RingOfIntegers K)) := by
    funext i
    rcases i with ⟨⟩
    rw [lubinTateSeries_eq, lubinTateVariable]
    rfl
  rw [hg] at h
  exact (lubinTateDiscrepancy_eq_zero_iff K π _).mpr h.symm

private theorem LubinTateFormalModule.ext_of_fields
    {G H : LubinTateFormalModule K π} (hF : G.formalGroup = H.formalGroup)
    (hE : G.endomorphism = H.endomorphism) : G = H := by
  cases G
  cases H
  cases hF
  cases hE
  rfl

/--
**L01**, Lemma `lem:lt-functional`: coefficientwise solution of the functional equation,
uniqueness, additivity, composition, and `[π]=f`.
-/
theorem lubinTateFormalModule_existsUnique (π : Uniformizer K) :
    ∃ F : LubinTateFormalModule K π,
      ∀ G : LubinTateFormalModule K π, G = F := by
  let C := canonicalLubinTateFormalModule K π
  refine ⟨C, ?_⟩
  intro G
  have hseries : G.formalGroup.toPowerSeries = C.formalGroup.toPowerSeries := by
    apply lubinTateFunctional_unique_of_coeff_single K π
    · exact G.formalGroup.zero_constantCoeff
    · exact C.formalGroup.zero_constantCoeff
    · exact G.formalGroup_discrepancy
    · exact C.formalGroup_discrepancy
    · intro i
      change coeff (Finsupp.single i 1) G.formalGroup.toPowerSeries =
        coeff (Finsupp.single i 1) (lubinTateFormalGroupSeries K π)
      fin_cases i
      · change coeff (Finsupp.single (0 : Fin 2) 1) G.formalGroup.toPowerSeries =
          coeff (Finsupp.single (0 : Fin 2) 1) (lubinTateFormalGroupSeries K π)
        rw [G.formalGroup.lin_coeff_X, lubinTateFormalGroupSeries_coeff]
      · change coeff (Finsupp.single (1 : Fin 2) 1) G.formalGroup.toPowerSeries =
          coeff (Finsupp.single (1 : Fin 2) 1) (lubinTateFormalGroupSeries K π)
        rw [G.formalGroup.lin_coeff_Y, lubinTateFormalGroupSeries_coeff]
  have hF : G.formalGroup = C.formalGroup := FormalGroup.ext hseries
  have hE : G.endomorphism = C.endomorphism := by
    funext a
    apply lubinTateFunctional_unique_of_coeff_single K π
    · exact G.constantCoeff a
    · exact C.constantCoeff a
    · exact LubinTateFormalModule.endomorphism_discrepancy (K := K) (π := π) G a
    · exact LubinTateFormalModule.endomorphism_discrepancy (K := K) (π := π) C a
    · intro i
      rcases i with ⟨⟩
      change PowerSeries.coeff 1 (G.endomorphism a) =
        PowerSeries.coeff 1 (lubinTateEndomorphismSeries K π a)
      rw [G.linearCoeff, lubinTateEndomorphismSeries_coeff_one]
  exact LubinTateFormalModule.ext_of_fields (K := K) (π := π) hF hE

/-- The chosen Lubin--Tate formal module. -/
noncomputable def lubinTateFormalModule (π : Uniformizer K) :
    LubinTateFormalModule K π :=
  (lubinTateFormalModule_existsUnique K π).choose

end

end NU.LCFT
