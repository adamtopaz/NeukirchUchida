import Submission.NU.Chebotarev.RayClass
import Submission.NU.Chebotarev.Discrepancy

/-!
# M5. Counting ideals in ray classes

Blueprint §5.2, especially Theorem 5.2 and equations (3)--(6). The common
leading term is exposed separately from the quantitative remainder, following
the milestone order in §10.4(M5).
-/

open Bornology Filter MeasureTheory Metric Module Pointwise Set Topology
open scoped ENNReal NNReal nonZeroDivisors Pointwise Real

namespace NU.Chebotarev

variable {K : Type*} [Field K] [NumberField K]

/-- The counting function `A_c(x)` of nonzero integral ideals prime to `m₀`
in ray class `c` (blueprint equation (3)). -/
noncomputable def rayIdealCounting (m : RayModulus K) (c : RayClassGroup m)
    (x : ℝ) : ℕ :=
  Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
    a ≠ 0 ∧ IsCoprime a m.finite ∧
    RayClassGroup.IsClassOfIdeal m a c ∧ (Ideal.absNorm a : ℝ) ≤ x}

local notation "O" => NumberField.RingOfIntegers K

private theorem count_coe_eq_multiplicity (p : PrimeIdeal K)
    {a : Ideal O} (ha : a ≠ 0) :
    FractionalIdeal.count K p (a : FractionalIdeal O⁰ K) =
      (multiplicity p.asIdeal a : ℤ) := by
  rw [FractionalIdeal.count_coe K p ha,
    Ideal.count_associates_factors_eq ha p.isPrime p.ne_bot,
    IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity ha]

private theorem count_inf_one_of_count_eq_zero
    (I : FractionalIdeal O⁰ K) (hI : I ≠ 0) (p : PrimeIdeal K)
    (hp : FractionalIdeal.count K p I = 0) :
    FractionalIdeal.count K p (I ⊓ 1) = 0 := by
  obtain ⟨a, A, ha, hIA⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let D : Ideal O := Ideal.span {a}
  have hA : A ≠ 0 := FractionalIdeal.ideal_factor_ne_zero hI hIA
  have hD : D ≠ 0 := FractionalIdeal.constant_factor_ne_zero hI hIA
  have hD' : (D : FractionalIdeal O⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hD
  have hA' : (A : FractionalIdeal O⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hA
  have hDI : (D : FractionalIdeal O⁰ K) * I =
      (A : FractionalIdeal O⁰ K) := by
    rw [hIA, ← FractionalIdeal.spanSingleton_inv,
      ← FractionalIdeal.coeIdeal_span_singleton]
    change (D : FractionalIdeal O⁰ K) *
      ((D : FractionalIdeal O⁰ K)⁻¹ * (A : FractionalIdeal O⁰ K)) = _
    rw [← mul_assoc, mul_inv_cancel₀ hD', one_mul]
  have hcountAD : FractionalIdeal.count K p (A : FractionalIdeal O⁰ K) =
      FractionalIdeal.count K p (D : FractionalIdeal O⁰ K) := by
    rw [hIA, ← FractionalIdeal.spanSingleton_inv,
      ← FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.count_mul K p (inv_ne_zero hD') hA',
      FractionalIdeal.count_inv] at hp
    omega
  have hmultAD : multiplicity p.asIdeal A = multiplicity p.asIdeal D := by
    rw [count_coe_eq_multiplicity p hA, count_coe_eq_multiplicity p hD] at hcountAD
    exact_mod_cast hcountAD
  have hS : A ⊔ D ≠ 0 := by
    intro h
    apply hA
    exact le_bot_iff.mp (le_sup_left.trans_eq h)
  have hF : A ⊓ D ≠ 0 := by
    intro h
    have hprod := Ideal.sup_mul_inf A D
    rw [h, mul_zero] at hprod
    exact mul_ne_zero hA hD hprod.symm
  have hcountS : FractionalIdeal.count K p
      ((A ⊔ D : Ideal O) : FractionalIdeal O⁰ K) =
      FractionalIdeal.count K p (D : FractionalIdeal O⁰ K) := by
    rw [count_coe_eq_multiplicity p hS, count_coe_eq_multiplicity p hD,
      IsDedekindDomain.HeightOneSpectrum.multiplicity_sup p hA hD, hmultAD,
      min_self]
  have hcountF : FractionalIdeal.count K p
      ((A ⊓ D : Ideal O) : FractionalIdeal O⁰ K) =
      FractionalIdeal.count K p (D : FractionalIdeal O⁰ K) := by
    have hprod := congr_arg (FractionalIdeal.count K p)
      (show ((A ⊔ D : Ideal O) : FractionalIdeal O⁰ K) *
          ((A ⊓ D : Ideal O) : FractionalIdeal O⁰ K) =
        (A : FractionalIdeal O⁰ K) * (D : FractionalIdeal O⁰ K) by
        rw [← FractionalIdeal.coeIdeal_mul, Ideal.sup_mul_inf,
          FractionalIdeal.coeIdeal_mul])
    rw [FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hS)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hF),
      FractionalIdeal.count_mul K p hA' hD', hcountS, hcountAD] at hprod
    omega
  have hDF : (D : FractionalIdeal O⁰ K) * (I ⊓ 1) =
      ((A ⊓ D : Ideal O) : FractionalIdeal O⁰ K) := by
    rw [FractionalIdeal.mul_inf, hDI, mul_one,
      FractionalIdeal.coeIdeal_inf]
  have hIinf : I ⊓ (1 : FractionalIdeal O⁰ K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDF
    exact (FractionalIdeal.coeIdeal_ne_zero.mpr hF) hDF.symm
  have hcountDF := congr_arg (FractionalIdeal.count K p) hDF
  rw [FractionalIdeal.count_mul K p hD' hIinf, hcountF] at hcountDF
  omega

private theorem isCoprime_of_count_eq_zero {a M : Ideal O}
    (ha : a ≠ 0) (hM : M ≠ 0)
    (hcount : ∀ p : PrimeIdeal K, p.asIdeal ∣ M →
      FractionalIdeal.count K p (a : FractionalIdeal O⁰ K) = 0) :
    IsCoprime a M := by
  apply Ideal.coprime_of_no_prime_ge
  intro P haP hMP hP
  have hP0 : P ≠ 0 := by
    intro h
    apply hM
    exact le_bot_iff.mp (hMP.trans_eq h)
  let p : PrimeIdeal K := ⟨P, hP, hP0⟩
  have hpM : p.asIdeal ∣ M := Ideal.dvd_iff_le.mpr hMP
  have hpcount := hcount p hpM
  have hmono := FractionalIdeal.count_mono K p
    (FractionalIdeal.coeIdeal_ne_zero.mpr ha) (show (a : FractionalIdeal O⁰ K) ≤
      (P : FractionalIdeal O⁰ K) by
        exact FractionalIdeal.coeIdeal_le_coeIdeal K |>.mpr haP)
  rw [FractionalIdeal.count_self, hpcount] at hmono
  omega

private theorem count_eq_zero_of_isCoprime {a M : Ideal O}
    (ha : a ≠ 0) (hcop : IsCoprime a M) (p : PrimeIdeal K)
    (hp : p.asIdeal ∣ M) :
    FractionalIdeal.count K p (a : FractionalIdeal O⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K p ha, Int.ofNat_eq_zero]
  by_contra hc
  have hpa : p.asIdeal ∣ a :=
    (Associates.count_ne_zero_iff_dvd ha p.irreducible).mp hc
  have haP : a ≤ p.asIdeal := Ideal.dvd_iff_le.mp hpa
  have hMP : M ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
  have : (⊤ : Ideal O) ≤ p.asIdeal := by
    rw [← hcop.sup_eq]
    exact sup_le haP hMP
  exact p.isPrime.ne_top (top_unique this)

private theorem exists_integralPart_coprime (m : RayModulus K)
    (I : RayIdealGroup m) :
    ∃ a : Ideal O, a ≠ 0 ∧ IsCoprime a m.finite ∧
      (a : FractionalIdeal O⁰ K) =
        ((I.1 : FractionalIdeal O⁰ K) ⊓ 1) := by
  have hI : (I.1 : FractionalIdeal O⁰ K) ≠ 0 := I.1.ne_zero
  have hF : (I.1 : FractionalIdeal O⁰ K) ⊓ 1 ≠ 0 := by
    intro h
    have hprod := FractionalIdeal.sup_mul_inf
      (I.1 : FractionalIdeal O⁰ K) 1
    rw [h, zero_mul, mul_one] at hprod
    exact hI hprod.symm
  obtain ⟨a, ha⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (show ((I.1 : FractionalIdeal O⁰ K) ⊓ 1) ≤ 1 from inf_le_right)
  have ha0 : a ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mp (ha.symm ▸ hF)
  refine ⟨a, ha0, ?_, ha⟩
  apply isCoprime_of_count_eq_zero ha0 m.finite_ne
  intro p hp
  rw [ha]
  exact count_inf_one_of_count_eq_zero (I.1 : FractionalIdeal O⁰ K) hI p (I.2 p hp)

private theorem exists_nonzero_mem_sub_one_of_isCoprime {a M : Ideal O}
    (ha : a ≠ 0) (hcop : IsCoprime a M) :
    ∃ x : O, x ≠ 0 ∧ x ∈ a ∧ x - 1 ∈ M := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop.exists
  by_cases hx0 : x = 0
  · have hM : M = ⊤ := by
      apply (Ideal.eq_top_iff_one M).mpr
      have hy1 : y = 1 := by simpa [hx0] using hxy
      rwa [← hy1]
    obtain ⟨z, hz⟩ := Submodule.nonzero_mem_of_bot_lt
      (bot_lt_iff_ne_bot.mpr ha)
    have hz' : (z : O) ≠ 0 := fun h ↦ hz (Subtype.ext h)
    exact ⟨z, hz', z.2, by rw [hM]; trivial⟩
  · refine ⟨x, hx0, hx, ?_⟩
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]
    exact M.neg_mem hy

private noncomputable def rayIdealOfCoprime (m : RayModulus K)
    (a : Ideal O) (ha : a ≠ 0) (hcop : IsCoprime a m.finite) :
    RayIdealGroup m :=
  ⟨Units.mk0 (a : FractionalIdeal O⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr ha),
    fun p hp ↦ count_eq_zero_of_isCoprime ha hcop p hp⟩

@[simp] private theorem rayIdealOfCoprime_val (m : RayModulus K)
    (a : Ideal O) (ha : a ≠ 0) (hcop : IsCoprime a m.finite) :
    ((rayIdealOfCoprime m a ha hcop).1 : FractionalIdeal O⁰ K) = a := rfl

/-- Blueprint equation (4) (`rayClass_admissibleGenerators`): an ideal in a
fixed ray class is represented by a generator in a translated congruence
lattice, modulo the congruence-and-sign unit subgroup. -/
theorem rayClass_admissibleGenerators (m : RayModulus K)
    (c : RayClassGroup m) :
    ∃ b : Ideal (NumberField.RingOfIntegers K),
      b ≠ 0 ∧ IsCoprime b m.finite ∧
      ∀ a : Ideal (NumberField.RingOfIntegers K),
        a ≠ 0 → IsCoprime a m.finite →
        (RayClassGroup.IsClassOfIdeal m a c ↔
          ∃ α : Kˣ,
            (a : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) *
                (b : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
              FractionalIdeal.spanSingleton
                (NumberField.RingOfIntegers K)⁰ (α : K) ∧
            RayAdmissible m α) := by
  classical
  obtain ⟨I, hIc⟩ := RayClassGroup.mk_surjective m c
  obtain ⟨j, hj0, hjcop, hj⟩ := exists_integralPart_coprime m I
  obtain ⟨d, hd0, hdj, hdm⟩ :=
    exists_nonzero_mem_sub_one_of_isCoprime hj0 hjcop
  have hd2j : d ^ 2 ∈ j := by
    simpa [pow_two] using j.mul_mem_left d hdj
  have hd2m : d ^ 2 - 1 ∈ m.finite := by
    rw [show d ^ 2 - 1 = (d - 1) * (d + 1) by ring]
    exact m.finite.mul_mem_right (d + 1) hdm
  have hd2cop : IsCoprime (Ideal.span {d ^ 2}) m.finite := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff]
    intro x hx
    have hone : (1 : O) ∈ Ideal.span {d ^ 2} ⊔ m.finite := by
      have hdspan : d ^ 2 ∈ Ideal.span {d ^ 2} ⊔ m.finite :=
        Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton (d ^ 2)))
      have hdiff : d ^ 2 - 1 ∈ Ideal.span {d ^ 2} ⊔ m.finite :=
        Ideal.mem_sup_right hd2m
      have : (1 : O) = d ^ 2 - (d ^ 2 - 1) := by ring
      rw [this]
      exact (Ideal.span {d ^ 2} ⊔ m.finite).sub_mem hdspan hdiff
    simpa only [smul_eq_mul, mul_one] using
      (Ideal.span {d ^ 2} ⊔ m.finite).smul_mem x hone
  let α : Kˣ := Units.mk0 (algebraMap O K (d ^ 2))
    ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 (pow_ne_zero 2 hd0))
  have hαadm : RayAdmissible m α := by
    constructor
    · refine ⟨d ^ 2, 1, one_ne_zero, ?_, hd2cop, ?_, hd2m⟩
      · simp [α]
      · rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq]
    · intro σ hσ
      change 0 < σ (algebraMap O K (d ^ 2))
      simpa only [map_pow] using sq_pos_of_ne_zero ((map_ne_zero σ).2
        ((map_ne_zero_iff (algebraMap O K)
          (FaithfulSMul.algebraMap_injective O K)).2 hd0))
  have hspan_le : FractionalIdeal.spanSingleton O⁰ (α : K) ≤
      (I.1 : FractionalIdeal O⁰ K) := by
    rw [show (α : K) = algebraMap O K (d ^ 2) by rfl,
      ← FractionalIdeal.coeIdeal_span_singleton]
    apply le_trans (FractionalIdeal.coeIdeal_le_coeIdeal K |>.mpr
      ((Ideal.span_singleton_le_iff_mem j).mpr hd2j))
    rw [hj]
    exact inf_le_left
  have hprod_le : FractionalIdeal.spanSingleton O⁰ (α : K) *
      (I.1 : FractionalIdeal O⁰ K)⁻¹ ≤ 1 := by
    calc
      _ ≤ (I.1 : FractionalIdeal O⁰ K) *
          (I.1 : FractionalIdeal O⁰ K)⁻¹ :=
        mul_le_mul_right' hspan_le _
      _ = 1 := mul_inv_cancel₀ I.1.ne_zero
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hprod_le
  have hspanα0 : FractionalIdeal.spanSingleton O⁰ (α : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr α.ne_zero
  have hb0 : b ≠ 0 := by
    apply (FractionalIdeal.coeIdeal_ne_zero (K := K)).mp
    rw [hb]
    exact mul_ne_zero hspanα0 (inv_ne_zero I.1.ne_zero)
  have hbcount : ∀ p : PrimeIdeal K, p.asIdeal ∣ m.finite →
      FractionalIdeal.count K p (b : FractionalIdeal O⁰ K) = 0 := by
    intro p hp
    rw [hb, FractionalIdeal.count_mul K p hspanα0 (inv_ne_zero I.1.ne_zero),
      FractionalIdeal.count_inv,
      show FractionalIdeal.spanSingleton O⁰ (α : K) =
          (Ideal.span {d ^ 2} : FractionalIdeal O⁰ K) by
        rw [show (α : K) = algebraMap O K (d ^ 2) by rfl,
          FractionalIdeal.coeIdeal_span_singleton],
      count_eq_zero_of_isCoprime (by simpa using pow_ne_zero 2 hd0) hd2cop p hp,
      I.2 p hp, neg_zero, add_zero]
  have hbcop : IsCoprime b m.finite :=
    isCoprime_of_count_eq_zero hb0 m.finite_ne hbcount
  let B : RayIdealGroup m := rayIdealOfCoprime m b hb0 hbcop
  have hBIval : (((B * I).1 : FractionalIdealGroup (K := K)) :
      FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ (α : K) := by
    change (b : FractionalIdeal O⁰ K) *
      (I.1 : FractionalIdeal O⁰ K) = _
    rw [hb, mul_assoc, inv_mul_cancel₀ I.1.ne_zero, mul_one]
  have hBI : RayClassGroup.mk m (B * I) = 1 :=
    (RayClassGroup.principal_iff m (B * I)).2 ⟨α, hαadm, hBIval⟩
  have hBc : RayClassGroup.mk m B = c⁻¹ := by
    rw [map_mul, hIc] at hBI
    exact eq_inv_of_mul_eq_one_left hBI
  refine ⟨b, hb0, hbcop, ?_⟩
  intro a ha0 hacop
  let A : RayIdealGroup m := rayIdealOfCoprime m a ha0 hacop
  have hAclass : RayClassGroup.IsClassOfIdeal m a c ↔
      RayClassGroup.mk m A = c := by
    constructor
    · rintro ⟨A', hA', hA'c⟩
      have hAA' : A' = A := by
        apply Subtype.ext
        apply Units.ext
        simpa [A] using hA'
      rwa [hAA'] at hA'c
    · intro hAc
      exact ⟨A, by simp [A], hAc⟩
  rw [hAclass]
  constructor
  · intro hAc
    have hAB : RayClassGroup.mk m (A * B) = 1 := by
      rw [map_mul, hAc, hBc, mul_inv_cancel]
    obtain ⟨β, hβadm, hβ⟩ :=
      (RayClassGroup.principal_iff m (A * B)).1 hAB
    exact ⟨β, by simpa [A, B] using hβ, hβadm⟩
  · rintro ⟨β, hβ, hβadm⟩
    have hABval : (((A * B).1 : FractionalIdealGroup (K := K)) :
        FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ (β : K) := by
      simpa [A, B] using hβ
    have hAB : RayClassGroup.mk m (A * B) = 1 :=
      (RayClassGroup.principal_iff m (A * B)).2 ⟨β, hβadm, hABval⟩
    rw [map_mul, hBc, mul_inv_eq_one] at hAB
    exact hAB

private theorem tendsto_div_of_sub_isBigO_rpow
    (f : ℝ → ℝ) (ρ : ℝ) (d : ℕ) (hd : 0 < d)
    (h : Asymptotics.IsBigO atTop (fun x : ℝ => f x - ρ * x)
      (fun x : ℝ => Real.rpow x (1 - 1 / (d : ℝ)))) :
    Tendsto (fun x : ℝ => f x / x) atTop (𝓝 ρ) := by
  have hdR : 0 < (1 / (d : ℝ)) := div_pos one_pos (Nat.cast_pos.mpr hd)
  have hg : Tendsto
      (fun x : ℝ => Real.rpow x (1 - 1 / (d : ℝ)) * x⁻¹)
      atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop hdR).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    symm
    rw [show 1 - 1 / (d : ℝ) = 1 + (-(1 / (d : ℝ))) by ring]
    change (x ^ (1 + (-(1 / (d : ℝ))))) * x⁻¹ =
      x ^ (-(1 / (d : ℝ)))
    rw [Real.rpow_add hx (1 : ℝ) (-(1 / (d : ℝ))), Real.rpow_one]
    field_simp
  have he : Tendsto
      (fun x : ℝ => (f x - ρ * x) * x⁻¹) atTop (𝓝 0) :=
    (h.mul (Asymptotics.isBigO_refl (fun x : ℝ => x⁻¹) atTop)).trans_tendsto hg
  rw [← tendsto_sub_nhds_zero_iff]
  apply he.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open Submodule NumberField.Units NumberField.Units.dirichletUnitTheorem

/-- A nonzero principal ideal admitting a ray-admissible generator. -/
private def RayAdmissiblyPrincipal (m : RayModulus K) (I : (Ideal O)⁰) : Prop :=
  ∃ α : Kˣ, RayAdmissible m α ∧
    (I.1 : FractionalIdeal O⁰ K) =
      FractionalIdeal.spanSingleton O⁰ (α : K)

private theorem RayAdmissiblyPrincipal.isPrincipal
    {m : RayModulus K} {I : (Ideal O)⁰}
    (h : RayAdmissiblyPrincipal m I) : IsPrincipal I.1 := by
  obtain ⟨α, _hα, hI⟩ := h
  have hmem : (α : K) ∈ (I.1 : FractionalIdeal O⁰ K) := by
    rw [hI]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨a, _ha, haα⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp hmem
  have hIa : I.1 = Ideal.span {a} := by
    apply (FractionalIdeal.coeIdeal_injective (K := K))
    change (I.1 : FractionalIdeal O⁰ K) =
      (Ideal.span {a} : FractionalIdeal O⁰ K)
    rw [hI, FractionalIdeal.coeIdeal_span_singleton, haα]
  rw [hIa, Submodule.isPrincipal_iff]
  exact ⟨a, rfl⟩

/-- Principal nonzero ideals divisible by `B`. -/
private abbrev RayPrincipalDvd (B : (Ideal O)⁰) :=
  {I : (Ideal O)⁰ // B.1 ∣ I.1 ∧ IsPrincipal I.1}

/-- Mathlib's fundamental-cone equivalence, restricted to the ideal lattice
of `B` but with the norm condition omitted. -/
private noncomputable def rayIdealSetPrincipalDvdEquiv (B : (Ideal O)⁰) :
    idealSet K B ≃ RayPrincipalDvd B × torsion K :=
  calc
    idealSet K B ≃
        {a : integerSet K // (preimageOfMemIntegerSet a).1 ∈ B.1} :=
      idealSetEquiv K B
    _ ≃ {p : {I : (Ideal O)⁰ // IsPrincipal I.1} × torsion K // B.1 ∣ p.1.1} :=
      Equiv.subtypeEquiv (integerSetEquiv K) (fun a => by
        change (preimageOfMemIntegerSet a).1 ∈ B.1 ↔
          B.1 ∣ ((integerSetEquiv K a).1.1 : Ideal O)
        rw [integerSetEquiv_apply_fst, Ideal.dvd_span_singleton])
    _ ≃ {I : {I : (Ideal O)⁰ // IsPrincipal I.1} // B.1 ∣ I.1} × torsion K :=
      @Equiv.prodSubtypeFstEquivSubtypeProd
        {I : (Ideal O)⁰ // IsPrincipal I.1} (torsion K) (fun I => B.1 ∣ I.1)
    _ ≃ {I : (Ideal O)⁰ // IsPrincipal I.1 ∧ B.1 ∣ I.1} × torsion K :=
      Equiv.prodCongrLeft fun _ => Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal O)⁰ => IsPrincipal I.1) (fun I => B.1 ∣ I.1)
    _ ≃ RayPrincipalDvd B × torsion K :=
      Equiv.prodCongrLeft fun _ => Equiv.subtypeEquivRight fun _ => by rw [and_comm]

/-- Multiplication by `B` identifies ideals whose product with `B` is
principal with principal ideals divisible by `B`. -/
private noncomputable def rayPrincipalMulEquiv (B : (Ideal O)⁰) :
    {A : (Ideal O)⁰ // IsPrincipal (B * A).1} ≃ RayPrincipalDvd B :=
  calc
    _ ≃ {J : {I : (Ideal O)⁰ // B ∣ I} // IsPrincipal J.1.1} :=
      Equiv.subtypeEquiv (Equiv.dvd B) (fun A => by rw [Equiv.dvd_apply])
    _ ≃ {I : (Ideal O)⁰ // B ∣ I ∧ IsPrincipal I.1} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal O)⁰ => B ∣ I) (fun I => IsPrincipal I.1)
    _ ≃ RayPrincipalDvd B :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun I => by
        simp only [Equiv.refl_apply]
        rw [nonZeroDivisors_dvd_iff_dvd_coe])

/-- The canonical fundamental-cone points for the ideal lattice of `B`,
identified with ideals `A` for which `B * A` is principal, together with the
usual torsion multiplicity. -/
private noncomputable def rayIdealSetMulEquiv (B : (Ideal O)⁰) :
    idealSet K B ≃ {A : (Ideal O)⁰ // IsPrincipal (B * A).1} × torsion K :=
  (rayIdealSetPrincipalDvdEquiv B).trans
    (Equiv.prodCongr (rayPrincipalMulEquiv B).symm (Equiv.refl _))

private def RayRepresentativeProperty (m : RayModulus K)
    (B A : (Ideal O)⁰) (x : ℝ) : Prop :=
  IsCoprime A.1 m.finite ∧ RayAdmissiblyPrincipal m (B * A) ∧
    (Ideal.absNorm A.1 : ℝ) ≤ x

/-- The actual lattice-point count used below.  Its ambient set is
`fundamentalCone K ∩ idealLattice K B`; the ray-generator condition cuts it
into finitely many translates of the congruence sublattice and sign chambers.
The definition deliberately retains every torsion representative. -/
private noncomputable def rayCanonicalGeneratorCounting
    (m : RayModulus K) (B : (Ideal O)⁰) (x : ℝ) : ℕ :=
  Nat.card {z : idealSet K B //
    RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x}

private noncomputable def rayRepresentativeCountingNZ
    (m : RayModulus K) (B : (Ideal O)⁰) (x : ℝ) : ℕ :=
  Nat.card {A : (Ideal O)⁰ // RayRepresentativeProperty m B A x}

private noncomputable def rayCanonicalGeneratorEquiv
    (m : RayModulus K) (B : (Ideal O)⁰) (x : ℝ) :
    {z : idealSet K B //
      RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x} ≃
      {A : (Ideal O)⁰ // RayRepresentativeProperty m B A x} × torsion K :=
  calc
    _ ≃ {p : {A : (Ideal O)⁰ // IsPrincipal (B * A).1} × torsion K //
          RayRepresentativeProperty m B p.1.1 x} :=
      Equiv.subtypeEquiv (rayIdealSetMulEquiv B) (fun _ => Iff.rfl)
    _ ≃ {A : {A : (Ideal O)⁰ // IsPrincipal (B * A).1} //
          RayRepresentativeProperty m B A.1 x} × torsion K :=
      @Equiv.prodSubtypeFstEquivSubtypeProd
        {A : (Ideal O)⁰ // IsPrincipal (B * A).1} (torsion K)
        (fun A => RayRepresentativeProperty m B A.1 x)
    _ ≃ {A : (Ideal O)⁰ // RayRepresentativeProperty m B A x} × torsion K :=
      Equiv.prodCongrLeft fun _ =>
        @Equiv.subtypeSubtypeEquivSubtype ((Ideal O)⁰)
          (fun A => IsPrincipal (B * A).1)
          (fun A => RayRepresentativeProperty m B A x)
          (fun {A : (Ideal O)⁰} (h : RayRepresentativeProperty m B A x) =>
            RayAdmissiblyPrincipal.isPrincipal h.2.1)

private theorem rayCanonicalGeneratorCounting_eq_mul
    (m : RayModulus K) (B : (Ideal O)⁰) (x : ℝ) :
    rayCanonicalGeneratorCounting m B x =
      rayRepresentativeCountingNZ m B x * torsionOrder K := by
  rw [rayCanonicalGeneratorCounting, rayRepresentativeCountingNZ, torsionOrder,
    ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  exact Nat.card_congr (rayCanonicalGeneratorEquiv m B x)

private def idealNeEquiv : {a : Ideal O // a ≠ 0} ≃ (Ideal O)⁰ where
  toFun a := ⟨a.1, mem_nonZeroDivisors_of_ne_zero a.2⟩
  invFun a := ⟨a.1, nonZeroDivisors.coe_ne_zero a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem rayAdmissiblyPrincipal_mul_iff
    (m : RayModulus K) (B A : (Ideal O)⁰) :
    RayAdmissiblyPrincipal m (B * A) ↔
      ∃ α : Kˣ,
        (A.1 : FractionalIdeal O⁰ K) * (B.1 : FractionalIdeal O⁰ K) =
          FractionalIdeal.spanSingleton O⁰ (α : K) ∧
        RayAdmissible m α := by
  constructor
  · rintro ⟨α, hα, hspan⟩
    refine ⟨α, ?_, hα⟩
    rw [← hspan, Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul, mul_comm]
  · rintro ⟨α, hspan, hα⟩
    refine ⟨α, hα, ?_⟩
    rw [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul, mul_comm, hspan]

private theorem rayIdealCounting_eq_rep
    (m : RayModulus K) (c : RayClassGroup m)
    (b : Ideal O) (hb0 : b ≠ 0)
    (hb : ∀ a : Ideal O, a ≠ 0 → IsCoprime a m.finite →
      (RayClassGroup.IsClassOfIdeal m a c ↔
        ∃ α : Kˣ,
          (a : FractionalIdeal O⁰ K) * (b : FractionalIdeal O⁰ K) =
            FractionalIdeal.spanSingleton O⁰ (α : K) ∧
          RayAdmissible m α)) (x : ℝ) :
    rayIdealCounting m c x =
      rayRepresentativeCountingNZ m
        ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩ x := by
  let B : (Ideal O)⁰ := ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩
  rw [rayIdealCounting, rayRepresentativeCountingNZ]
  apply Nat.card_congr
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun a : Ideal O => a ≠ 0)
    (fun a => IsCoprime a m.finite ∧ RayClassGroup.IsClassOfIdeal m a c ∧
      (Ideal.absNorm a : ℝ) ≤ x)).symm |>.trans ?_
  exact Equiv.subtypeEquiv idealNeEquiv (fun a => by
    change (IsCoprime a.1 m.finite ∧ RayClassGroup.IsClassOfIdeal m a.1 c ∧
        (Ideal.absNorm a.1 : ℝ) ≤ x) ↔
      RayRepresentativeProperty m B (idealNeEquiv a) x
    rw [RayRepresentativeProperty]
    constructor
    · rintro ⟨hcop, hclass, hnorm⟩
      refine ⟨hcop, ?_, hnorm⟩
      rw [rayAdmissiblyPrincipal_mul_iff]
      exact (hb a.1 a.2 hcop).mp hclass
    · rintro ⟨hcop, hprincipal, hnorm⟩
      refine ⟨hcop, (hb a.1 a.2 hcop).mpr ?_, hnorm⟩
      simpa [B, idealNeEquiv] using
        (rayAdmissiblyPrincipal_mul_iff m B (idealNeEquiv a)).mp hprincipal)

open NU.Chebotarev.Discrepancy

noncomputable section
open scoped Classical

private abbrev ConeRankPlace (K : Type*) [Field K] [NumberField K] :=
  {w : InfinitePlace K // w ≠ w₀}
private abbrev ConeComplexPlace (K : Type*) [Field K] [NumberField K] :=
  {w : InfinitePlace K // IsComplex w}
private abbrev ConeRealPlace (K : Type*) [Field K] [NumberField K] :=
  {w : InfinitePlace K // IsReal w}
private abbrev ConeBoundaryParameter (K : Type*) [Field K] [NumberField K] :=
  ConeRankPlace K ⊕ ConeComplexPlace K
private abbrev ConeFace (K : Type*) [Field K] [NumberField K] :=
  Unit ⊕ (Unit ⊕ (ConeRankPlace K × Bool))
private abbrev ConeSign (K : Type*) [Field K] [NumberField K] :=
  ConeRealPlace K → Bool

private theorem coneBoundaryParameter_card :
    Fintype.card (ConeBoundaryParameter K) + 1 = Module.finrank ℚ K := by
  classical
  have hrank : Fintype.card (ConeRankPlace K) =
      Fintype.card (InfinitePlace K) - 1 := by
    simpa only [Fintype.card_subtype_eq, Fintype.card_unique] using
      (Fintype.card_subtype_compl (fun w : InfinitePlace K => w = w₀))
  have hplace := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hdegree := card_add_two_mul_card_eq_rank K
  change Fintype.card (ConeRankPlace K ⊕ ConeComplexPlace K) + 1 = _
  rw [Fintype.card_sum]
  change Fintype.card (ConeRankPlace K) + nrComplexPlaces K + 1 = _
  have hpos : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  rw [hrank, hplace]
  omega

private def coneFaceLog (f : ConeFace K)
    (p : ConeBoundaryParameter K → ℝ) : realSpace K := fun w =>
  if hw : w = w₀ then 0 else
    match f with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => p (Sum.inl ⟨w, hw⟩)
    | Sum.inr (Sum.inr (i, upper)) =>
        if _hi : w = i.1 then if upper then 1 else 0 else p (Sum.inl ⟨w, hw⟩)

private def coneFaceRadius (f : ConeFace K)
    (p : ConeBoundaryParameter K → ℝ) : ℝ :=
  match f with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (i, _)) => p (Sum.inl i)

private noncomputable def conePolarReconstruct (s : ConeSign K) (r : realSpace K)
    (p : ConeBoundaryParameter K → ℝ) : mixedSpace K :=
  (fun w => if s w then -(r w.1) else r w.1,
    fun w => Complex.ofRealCLM (r w.1) *
      (Complex.ofRealCLM (Real.cos (2 * Real.pi * p (Sum.inr w) - Real.pi)) +
        Complex.ofRealCLM (Real.sin (2 * Real.pi * p (Sum.inr w) - Real.pi)) * Complex.I))

private noncomputable def coneBoundaryChart (j : ConeSign K × ConeFace K)
    (p : ConeBoundaryParameter K → ℝ) : mixedSpace K :=
  conePolarReconstruct j.1
    (coneFaceRadius j.2 p • expMapBasis (coneFaceLog j.2 p)) p

private theorem contDiff_expMapBasis :
    ContDiff ℝ 1 (fun x : realSpace K => expMapBasis x) := by
  rw [contDiff_pi]
  intro w
  change ContDiff ℝ 1 (fun x : realSpace K =>
    Real.exp ((w.mult : ℝ)⁻¹ * ((completeBasis K).equivFunL.symm x) w))
  fun_prop

private theorem coneFaceRadius_contDiff (f : ConeFace K) :
    ContDiff ℝ 1 (coneFaceRadius f) := by
  rcases f with f0 | f
  · unfold coneFaceRadius
    fun_prop
  · rcases f with f1 | ⟨i, upper⟩
    · unfold coneFaceRadius
      fun_prop
    · unfold coneFaceRadius
      fun_prop

private theorem coneFaceLog_contDiff (f : ConeFace K) :
    ContDiff ℝ 1 (coneFaceLog f) := by
  rcases f with f0 | f
  · rw [contDiff_pi]
    intro w
    simp only [coneFaceLog]
    fun_prop
  · rcases f with f1 | ⟨i, upper⟩
    · rw [contDiff_pi]
      intro w
      by_cases hw : w = w₀
      · simp [coneFaceLog, hw]
        fun_prop
      · simp [coneFaceLog, hw]
        fun_prop
    · rw [contDiff_pi]
      intro w
      by_cases hw : w = w₀
      · simp [coneFaceLog, hw]
        fun_prop
      · by_cases hi : w = i.1
        · cases upper <;> simp [coneFaceLog, hw, hi, i.property] <;> fun_prop
        · simp [coneFaceLog, hw, hi]
          fun_prop

private def coneSignOf (x : mixedSpace K) : ConeSign K :=
  fun w => decide (x.1 w < 0)

private noncomputable def conePhase (x : mixedSpace K) (w : ConeComplexPlace K) : ℝ :=
  (Complex.arg (x.2 w) + Real.pi) / (2 * Real.pi)

private theorem conePhase_mem_Icc (x : mixedSpace K) (w : ConeComplexPlace K) :
    conePhase x w ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  constructor
  · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg (x.2 w)]) hp.le
  · apply (div_le_one hp).2
    linarith [Complex.arg_le_pi (x.2 w)]

private theorem conePhase_angle (x : mixedSpace K) (w : ConeComplexPlace K) :
    2 * Real.pi * conePhase x w - Real.pi = Complex.arg (x.2 w) := by
  rw [conePhase]
  field_simp [Real.pi_ne_zero]
  ring

private theorem conePolarReconstruct_self (x : mixedSpace K)
    (p : ConeBoundaryParameter K → ℝ)
    (hp : ∀ w : ConeComplexPlace K, p (Sum.inr w) = conePhase x w) :
    conePolarReconstruct (coneSignOf x) (normAtAllPlaces x) p = x := by
  ext w
  · rw [conePolarReconstruct]
    simp only [coneSignOf, Bool.decide_coe, decide_eq_true_eq]
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.prop, Real.norm_eq_abs]
    by_cases hw : x.1 w < 0
    · rw [if_pos hw, abs_of_neg hw, neg_neg]
    · rw [if_neg hw, abs_of_nonneg (le_of_not_gt hw)]
  · rw [conePolarReconstruct]
    simp only
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.prop, hp w,
      conePhase_angle]
    simpa only [Complex.ofRealCLM_apply, Complex.exp_ofReal_mul_I] using
      Complex.norm_mul_exp_arg_mul_I (x.2 w)

private theorem coneBoundaryChart_contDiff (j : ConeSign K × ConeFace K) :
    ContDiff ℝ 1 (coneBoundaryChart j) := by
  have hr := coneFaceRadius_contDiff j.2
  have hl := coneFaceLog_contDiff j.2
  have he := contDiff_expMapBasis (K := K)
  have hmag : ContDiff ℝ 1 (fun p : ConeBoundaryParameter K → ℝ =>
      coneFaceRadius j.2 p • expMapBasis (coneFaceLog j.2 p)) := by
    fun_prop
  unfold coneBoundaryChart conePolarReconstruct
  apply ContDiff.prodMk
  · rw [contDiff_pi]
    intro w
    split <;> fun_prop
  · rw [contDiff_pi]
    intro w
    fun_prop

private theorem normAtAllPlaces_eq_zero_iff {x : mixedSpace K} :
    normAtAllPlaces x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply forall_normAtPlace_eq_zero_iff.mp
    intro w
    simpa [normAtAllPlaces_apply] using congrFun h w
  · rintro rfl
    ext w
    simp [normAtAllPlaces_apply]

private theorem coneBoundaryCharts_cover :
    frontier (normLeOne K) ⊆
      ⋃ j : ConeSign K × ConeFace K, coneBoundaryChart j '' unitCube := by
  classical
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    let p : ConeBoundaryParameter K → ℝ := 0
    rw [Set.mem_iUnion]
    refine ⟨(coneSignOf (0 : mixedSpace K), Sum.inl ()), p, ?_, ?_⟩
    · exact ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
    · simp [coneBoundaryChart, coneFaceRadius, conePolarReconstruct]
      constructor <;> funext w <;> rfl
  have hxcl : x ∈ closure (normLeOne K) := hx.1
  have hcompact := closure_normLeOne_subset K hxcl
  rw [compactSet_eq_union] at hcompact
  rcases hcompact with hcompact | hzero
  swap
  · have hz : normAtAllPlaces x = 0 := by simpa using hzero
    exact (hx0 (normAtAllPlaces_eq_zero_iff.mp hz)).elim
  obtain ⟨y, hycl, hy⟩ := hcompact
  have hynot : y ∉ interior (paramSet K) := by
    intro hyint
    have hxint : x ∈ interior (normLeOne K) :=
      subset_interior_normLeOne K ⟨y, hyint, hy⟩
    exact hx.2 hxint
  rw [closure_paramSet, Set.mem_univ_pi] at hycl
  rw [interior_paramSet, Set.mem_univ_pi] at hynot
  by_cases hy0 : y w₀ = 0
  · let p : ConeBoundaryParameter K → ℝ := fun q =>
      match q with
      | Sum.inl i => y i.1
      | Sum.inr w => conePhase x w
    have hp : p ∈ unitCube := by
      constructor
      · intro q
        rcases q with i | w
        · have hi := hycl i.1
          simp only [if_neg i.property] at hi
          simpa [p] using hi.1
        · exact (conePhase_mem_Icc x w).1
      · intro q
        rcases q with i | w
        · have hi := hycl i.1
          simp only [if_neg i.property] at hi
          simpa [p] using hi.2
        · exact (conePhase_mem_Icc x w).2
    have hlog : coneFaceLog (K := K) (Sum.inr (Sum.inl ())) p = y := by
      funext w
      by_cases hw : w = w₀
      · simp [coneFaceLog, hw, hy0]
      · simp [coneFaceLog, hw, p]
    rw [Set.mem_iUnion]
    refine ⟨(coneSignOf x, Sum.inr (Sum.inl ())), p, hp, ?_⟩
    rw [coneBoundaryChart, coneFaceRadius, one_smul, hlog, hy]
    apply conePolarReconstruct_self
    intro w
    rfl
  · have hy0neg : y w₀ < 0 := by
      have := hycl w₀
      simp only [if_pos rfl, Set.mem_Iic] at this
      exact lt_of_le_of_ne this hy0
    push_neg at hynot
    obtain ⟨w, hwbad⟩ := hynot
    have hw : w ≠ w₀ := by
      intro h
      subst w
      apply hwbad
      simpa using hy0neg
    let i : ConeRankPlace K := ⟨w, hw⟩
    have hiIcc : y w ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [hw] using hycl w
    have hiend : y w = 0 ∨ y w = 1 := by
      have hnot : ¬(0 < y w ∧ y w < 1) := by
        simpa [hw] using hwbad
      rcases hiIcc with ⟨hlo, hhi⟩
      by_cases hzero : y w = 0
      · exact Or.inl hzero
      · right
        have hpos : 0 < y w := lt_of_le_of_ne hlo (Ne.symm hzero)
        have hge : 1 ≤ y w := le_of_not_gt fun hlt => hnot ⟨hpos, hlt⟩
        exact le_antisymm hhi hge
    let upper : Bool := decide (y w = 1)
    have hiupper : (if upper then (1 : ℝ) else 0) = y w := by
      rcases hiend with h | h
      · simp [upper, h]
      · simp [upper, h]
    let p : ConeBoundaryParameter K → ℝ := fun q =>
      match q with
      | Sum.inl j => if j = i then Real.exp (y w₀) else y j.1
      | Sum.inr v => conePhase x v
    have hp : p ∈ unitCube := by
      constructor
      · intro q
        rcases q with j | v
        · by_cases hji : j = i
          · simp [p, hji, Real.exp_nonneg]
          · have hj := hycl j.1
            simp only [if_neg j.property] at hj
            simpa [p, hji] using hj.1
        · exact (conePhase_mem_Icc x v).1
      · intro q
        rcases q with j | v
        · by_cases hji : j = i
          · simp only [p, hji, if_pos]
            exact Real.exp_le_one_iff.mpr hy0neg.le
          · have hj := hycl j.1
            simp only [if_neg j.property] at hj
            simpa [p, hji] using hj.2
        · exact (conePhase_mem_Icc x v).2
    have hlog : coneFaceLog (K := K) (Sum.inr (Sum.inr (i, upper))) p =
        fun v => if v = w₀ then 0 else y v := by
      funext v
      by_cases hv0 : v = w₀
      · simp [coneFaceLog, hv0]
      · by_cases hvi : v = i.1
        · have hvw : v = w := by simpa [i] using hvi
          rw [hvw]
          have hwi : w = i.1 := rfl
          simp [coneFaceLog, hw, hwi, hiupper]
        · simp [coneFaceLog, hv0, hvi, p]
          have hsub : (⟨v, hv0⟩ : ConeRankPlace K) ≠ i := by
            intro h
            exact hvi (congrArg Subtype.val h)
          simp [hsub]
    have hradius : coneFaceRadius (K := K) (Sum.inr (Sum.inr (i, upper))) p =
        Real.exp (y w₀) := by
      simp [coneFaceRadius, p]
    rw [Set.mem_iUnion]
    refine ⟨(coneSignOf x, Sum.inr (Sum.inr (i, upper))), p, hp, ?_⟩
    rw [coneBoundaryChart, hradius, hlog, ← expMapBasis_apply'' y, hy]
    apply conePolarReconstruct_self
    intro v
    rfl

private noncomputable def normLeOneLipschitzBoundaryCover :
    LipschitzBoundaryCover (κ := ConeBoundaryParameter K) (normLeOne K) :=
  LipschitzBoundaryCover.ofContDiff coneBoundaryChart coneBoundaryChart_contDiff
    coneBoundaryCharts_cover

private noncomputable def rayInfinitePlace (σ : K →+* ℝ) : InfinitePlace K :=
  InfinitePlace.mk (Complex.ofRealHom.comp σ)

private theorem rayInfinitePlace_isReal (σ : K →+* ℝ) :
    IsReal (rayInfinitePlace σ) := by
  rw [rayInfinitePlace, isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  simp

private noncomputable def rayRealCoordinate (σ : K →+* ℝ) (x : mixedSpace K) : ℝ :=
  x.1 ⟨rayInfinitePlace σ, rayInfinitePlace_isReal σ⟩

private theorem rayRealCoordinate_mixedEmbedding (σ : K →+* ℝ) (x : K) :
    rayRealCoordinate σ (mixedEmbedding K x) = σ x := by
  apply Complex.ofReal_injective
  rw [rayRealCoordinate, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  unfold rayInfinitePlace
  rw [embedding_mk_eq_of_isReal]
  · rfl
  · apply ComplexEmbedding.isReal_iff.mpr
    ext y
    simp

private def raySignHalfSpace (σ : K →+* ℝ) (positive : Bool) : Set (mixedSpace K) :=
  if positive then {x | 0 < rayRealCoordinate σ x}
  else {x | rayRealCoordinate σ x < 0}

private theorem frontier_raySignHalfSpace_subset (σ : K →+* ℝ) (positive : Bool) :
    frontier (raySignHalfSpace σ positive) ⊆ {x | rayRealCoordinate σ x = 0} := by
  let e : mixedSpace K →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj ⟨rayInfinitePlace σ, rayInfinitePlace_isReal σ⟩).comp
      (ContinuousLinearMap.fst ℝ _ _)
  have he : Function.Surjective e := fun r =>
    ⟨(fun _ => r, 0), by simp [e, rayRealCoordinate]⟩
  cases positive
  · change frontier (e ⁻¹' Set.Iio 0) ⊆ e ⁻¹' {0}
    rw [e.frontier_preimage he, frontier_Iio]
  · change frontier (e ⁻¹' Set.Ioi 0) ⊆ e ⁻¹' {0}
    rw [e.frontier_preimage he, frontier_Ioi]

private theorem eq_zero_of_mem_closure_normLeOne_of_realCoordinate_eq_zero
    {x : mixedSpace K} (hx : x ∈ closure (normLeOne K))
    (σ : K →+* ℝ) (hσ : rayRealCoordinate σ x = 0) : x = 0 := by
  have hc := closure_normLeOne_subset K hx
  rw [compactSet_eq_union] at hc
  rcases hc with ⟨y, _hy, hy⟩ | hy
  · have hw := congrFun hy (rayInfinitePlace σ)
    have hcoord : x.1 ⟨rayInfinitePlace σ, rayInfinitePlace_isReal σ⟩ = 0 := hσ
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isReal (rayInfinitePlace_isReal σ),
      hcoord, norm_zero] at hw
    exfalso
    exact (expMapBasis_pos y (rayInfinitePlace σ)).ne' hw
  · apply normAtAllPlaces_eq_zero_iff.mp
    simpa using hy

private def raySignRegionFinset (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) (s : Finset (↥m.infinite)) : Set (mixedSpace K) :=
  normLeOne K ∩ ⋂ σ ∈ s, raySignHalfSpace σ.1 (e σ)

private noncomputable def raySignRegion (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) : Set (mixedSpace K) :=
  raySignRegionFinset m e Finset.univ

private theorem raySignRegionFinset_subset (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) (s : Finset (↥m.infinite)) :
    raySignRegionFinset m e s ⊆ normLeOne K := Set.inter_subset_left

private noncomputable def raySignRegionFinsetBoundaryCover (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) (s : Finset (↥m.infinite)) :
    LipschitzBoundaryCover (κ := ConeBoundaryParameter K) (raySignRegionFinset m e s) := by
  classical
  apply Classical.choice
  induction s using Finset.induction with
  | empty =>
      exact ⟨by simpa [raySignRegionFinset] using
        (normLeOneLipschitzBoundaryCover (K := K))⟩
  | @insert σ s hσ ih =>
      obtain ⟨ih⟩ := ih
      refine ⟨?_⟩
      have heq : raySignRegionFinset m e (insert σ s) =
          raySignRegionFinset m e s ∩ raySignHalfSpace σ.1 (e σ) := by
        ext x
        simp [raySignRegionFinset]
        aesop
      rw [heq]
      apply ih.interOfLipschitzCut 1 0 (fun _ _ => 0)
      · intro j
        exact LipschitzWith.const 0
      · intro x hx
        rw [Set.mem_iUnion]
        refine ⟨0, 0, ?_, ?_⟩
        · exact ⟨fun _ => le_rfl, fun _ => zero_le_one⟩
        · have hxnorm : x ∈ closure (normLeOne K) :=
            (closure_mono (raySignRegionFinset_subset m e s)) hx.1
          have hxcoord : rayRealCoordinate σ.1 x = 0 :=
            frontier_raySignHalfSpace_subset σ.1 (e σ) hx.2
          exact (eq_zero_of_mem_closure_normLeOne_of_realCoordinate_eq_zero
            hxnorm σ.1 hxcoord).symm

private noncomputable def raySignRegionBoundaryCover (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) :
    LipschitzBoundaryCover (κ := ConeBoundaryParameter K) (raySignRegion m e) :=
  raySignRegionFinsetBoundaryCover m e Finset.univ

private theorem rayInfinitePlace_injective :
    Function.Injective (rayInfinitePlace (K := K)) := by
  intro σ τ h
  simp only [rayInfinitePlace, InfinitePlace.mk_eq_iff] at h
  rcases h with h | h
  · ext x
    have hx := congrFun (congrArg DFunLike.coe h) x
    exact Complex.ofReal_injective hx
  · ext x
    have hx := congrFun (congrArg DFunLike.coe h) x
    simpa using congrArg Complex.re hx

private theorem isOpen_raySignHalfSpace (σ : K →+* ℝ) (positive : Bool) :
    IsOpen (raySignHalfSpace σ positive) := by
  let f : mixedSpace K →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj ⟨rayInfinitePlace σ, rayInfinitePlace_isReal σ⟩).comp
      (ContinuousLinearMap.fst ℝ _ _)
  cases positive
  · exact isOpen_lt f.continuous continuous_const
  · exact isOpen_lt continuous_const f.continuous

private theorem raySignRegion_isBounded (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) : IsBounded (raySignRegion m e) :=
  (isBounded_normLeOne K).subset (raySignRegionFinset_subset m e Finset.univ)

private theorem raySignRegion_measureReal_pos (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) : 0 < volume.real (raySignRegion m e) := by
  classical
  let a : realSpace K := fun w => if w = w₀ then -1 else 2⁻¹
  have ha : a ∈ interior (paramSet K) := by
    rw [interior_paramSet, Set.mem_univ_pi]
    intro w
    by_cases hw : w = w₀
    · norm_num [a, hw]
    · norm_num [a, hw]
  let z0 : mixedSpace K := mixedSpaceOfRealSpace (expMapBasis a)
  have hz0int : z0 ∈ interior (normLeOne K) := by
    apply subset_interior_normLeOne K
    refine ⟨a, ha, ?_⟩
    exact (normAtAllPlaces_mixedSpaceOfRealSpace
      (fun w => (expMapBasis_pos a w).le)).symm
  let signs : Set (ConeRealPlace K) :=
    {w | ∃ σ : ↥m.infinite, e σ = false ∧ rayInfinitePlace σ.1 = w.1}
  let z : mixedSpace K := negAt signs z0
  have hnormmem : negAt signs '' normLeOne K = normLeOne K := by
    rw [← negAt_preimage]
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro hx
      exact ⟨fundamentalCone.mem_of_normAtPlace_eq hx.1
        (fun w => (normAtPlace_negAt signs x w).symm), by simpa using hx.2⟩
    · intro hx
      exact ⟨fundamentalCone.mem_of_normAtPlace_eq hx.1
        (fun w => normAtPlace_negAt signs x w), by simpa using hx.2⟩
  have hzint : z ∈ interior (normLeOne K) := by
    have hzimage : z ∈ (negAt signs).toHomeomorph '' interior (normLeOne K) :=
      ⟨z0, hz0int, rfl⟩
    rw [(negAt signs).toHomeomorph.image_interior] at hzimage
    have hnormmem' : (negAt signs).toHomeomorph '' normLeOne K = normLeOne K := by
      simpa using hnormmem
    rw [hnormmem'] at hzimage
    exact hzimage
  have hzcoord (σ : ↥m.infinite) :
      if e σ then 0 < rayRealCoordinate σ.1 z else rayRealCoordinate σ.1 z < 0 := by
    have hz0pos : 0 < rayRealCoordinate σ.1 z0 := by
      change 0 < expMapBasis a (rayInfinitePlace σ.1)
      exact expMapBasis_pos _ _
    by_cases he : e σ = true
    · rw [if_pos he]
      have hnot : (⟨rayInfinitePlace σ.1, rayInfinitePlace_isReal σ.1⟩ : ConeRealPlace K)
          ∉ signs := by
        rintro ⟨τ, hτ, heq⟩
        have hστ : σ = τ := Subtype.ext (rayInfinitePlace_injective heq).symm
        subst τ
        simp [he] at hτ
      change 0 < (negAt signs z0).1
        ⟨rayInfinitePlace σ.1, rayInfinitePlace_isReal σ.1⟩
      rw [negAt_apply_isReal_and_notMem _ hnot]
      exact hz0pos
    · rw [if_neg he]
      have hmem : (⟨rayInfinitePlace σ.1, rayInfinitePlace_isReal σ.1⟩ : ConeRealPlace K)
          ∈ signs := ⟨σ, Bool.eq_false_of_not_eq_true he, rfl⟩
      change (negAt signs z0).1
        ⟨rayInfinitePlace σ.1, rayInfinitePlace_isReal σ.1⟩ < 0
      rw [negAt_apply_isReal_and_mem _ hmem]
      exact neg_neg_of_pos hz0pos
  have hopen : IsOpen (⋂ σ : ↥m.infinite, raySignHalfSpace σ.1 (e σ)) :=
    isOpen_iInter_of_finite fun σ => isOpen_raySignHalfSpace σ.1 (e σ)
  have hzH : z ∈ ⋂ σ : ↥m.infinite, raySignHalfSpace σ.1 (e σ) := by
    rw [Set.mem_iInter]
    intro σ
    cases h : e σ
    · simpa [raySignHalfSpace, h] using hzcoord σ
    · simpa [raySignHalfSpace, h] using hzcoord σ
  have hzregion : z ∈ interior (raySignRegion m e) := by
    refine (interior_maximal ?_ (isOpen_interior.inter hopen)) ⟨hzint, hzH⟩
    intro x hx
    refine ⟨interior_subset hx.1, ?_⟩
    simpa [raySignRegion, raySignRegionFinset] using hx.2
  have hvol : 0 < volume (raySignRegion m e) :=
    (isOpen_interior.measure_pos volume ⟨z, hzregion⟩).trans_le
      (measure_mono interior_subset)
  rw [Measure.real_def]
  exact ENNReal.toReal_pos hvol.ne'
    (raySignRegion_isBounded m e).measure_lt_top.ne

private abbrev RayResidueSignData (m : RayModulus K) :=
  (O ⧸ m.finite) × ((σ : ↥m.infinite) → Bool)

private noncomputable def integralRayDatum (m : RayModulus K) (y : O) :
    RayResidueSignData m :=
  (Ideal.Quotient.mk m.finite y,
    fun σ => decide (0 < σ.1 (algebraMap O K y)))

private noncomputable def unitRayDatum (m : RayModulus K) (u : Oˣ) :
    RayResidueSignData m :=
  (Ideal.Quotient.mk m.finite ((u⁻¹ : Oˣ) : O),
    fun σ => decide (0 < σ.1 (algebraMap O K (u : O))))

private abbrev GoodRayDatum (m : RayModulus K) :=
  {q : RayResidueSignData m // ∃ u : Oˣ, unitRayDatum m u = q}

private theorem integralRayDatum_eq_unit_iff (m : RayModulus K)
    (y : O) (hy : y ≠ 0) (u : Oˣ) :
    integralRayDatum m y = unitRayDatum m u ↔
      (u : O) * y - 1 ∈ m.finite ∧
      ∀ σ ∈ m.infinite, 0 < σ (algebraMap O K ((u : O) * y)) := by
  have hyK : algebraMap O K y ≠ 0 :=
    (map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hy
  have huK : algebraMap O K (u : O) ≠ 0 :=
    (map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 u.ne_zero
  constructor
  · intro h
    have hres := congrArg Prod.fst h
    have hdiff : y - ((u⁻¹ : Oˣ) : O) ∈ m.finite := Ideal.Quotient.eq.mp hres
    have hcong : (u : O) * y - 1 ∈ m.finite := by
      have hm := m.finite.mul_mem_left (u : O) hdiff
      convert hm using 1
      rw [mul_sub]
      simp
    refine ⟨hcong, ?_⟩
    intro σ hσ
    have hsign := congrFun (congrArg Prod.snd h) ⟨σ, hσ⟩
    have hyσ : σ (algebraMap O K y) ≠ 0 := (map_ne_zero σ).2 hyK
    have huσ : σ (algebraMap O K (u : O)) ≠ 0 := (map_ne_zero σ).2 huK
    rw [map_mul]
    by_cases hu : 0 < σ (algebraMap O K (u : O))
    · have hypos : 0 < σ (algebraMap O K y) := by
        simpa [integralRayDatum, unitRayDatum, hu] using hsign
      simpa only [map_mul] using mul_pos hu hypos
    · have huneg : σ (algebraMap O K (u : O)) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hu) huσ
      have hynpos : ¬0 < σ (algebraMap O K y) := by
        intro hypos
        simp [integralRayDatum, unitRayDatum, hu, hypos] at hsign
      have hyneg : σ (algebraMap O K y) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hynpos) hyσ
      simpa only [map_mul] using mul_pos_of_neg_of_neg huneg hyneg
  · rintro ⟨hcong, hpos⟩
    apply Prod.ext
    · apply Ideal.Quotient.eq.mpr
      have hm := m.finite.mul_mem_left ((u⁻¹ : Oˣ) : O) hcong
      convert hm using 1
      rw [mul_sub]
      simp
    · funext σ
      have hp := hpos σ.1 σ.2
      rw [map_mul] at hp
      have huσ : σ.1 (algebraMap O K (u : O)) ≠ 0 := (map_ne_zero σ.1).2 huK
      by_cases hu : 0 < σ.1 (algebraMap O K (u : O))
      · have hypos : 0 < σ.1 (algebraMap O K y) :=
          pos_of_mul_pos_right (by simpa only [map_mul] using hp) hu.le
        simp [integralRayDatum, unitRayDatum, hu, hypos]
      · have huneg : σ.1 (algebraMap O K (u : O)) < 0 :=
          lt_of_le_of_ne (le_of_not_gt hu) huσ
        have hyneg : σ.1 (algebraMap O K y) < 0 :=
          neg_of_mul_pos_right (by simpa only [map_mul] using hp) huneg.le
        simp [integralRayDatum, unitRayDatum, hu, not_lt_of_ge hyneg.le]

private theorem rayAdmissible_integral_iff (m : RayModulus K)
    (y : O) (hy : y ≠ 0) (hycop : IsCoprime (Ideal.span {y}) m.finite) :
    RayAdmissible m (Units.mk0 (algebraMap O K y)
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 hy)) ↔
      y - 1 ∈ m.finite ∧ ∀ σ ∈ m.infinite, 0 < σ (algebraMap O K y) := by
  constructor
  · rintro ⟨⟨β, γ, hγ, hfrac, _hβcop, hγcop, hcong⟩, hpos⟩
    have hγK : algebraMap O K γ ≠ 0 :=
      (map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 hγ
    have hβγK : algebraMap O K β =
        algebraMap O K y * algebraMap O K γ := by
      apply (div_eq_iff hγK).mp
      simpa using hfrac
    have hβγ : β = y * γ := by
      apply (FaithfulSMul.algebraMap_injective O K)
      simpa only [map_mul] using hβγK
    have hprod : (y - 1) * γ ∈ m.finite := by
      rw [show (y - 1) * γ = y * γ - γ by ring, ← hβγ]
      exact hcong
    obtain ⟨a, ha, b, hb, hab⟩ := hγcop.exists
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have hfirst : (y - 1) * (γ * c) ∈ m.finite := by
      rw [← mul_assoc]
      exact m.finite.mul_mem_right c hprod
    have hsecond : (y - 1) * b ∈ m.finite := m.finite.mul_mem_left (y - 1) hb
    refine ⟨?_, hpos⟩
    rw [show y - 1 = (y - 1) * (γ * c) + (y - 1) * b by
      rw [← mul_add, hab, mul_one]]
    exact m.finite.add_mem hfirst hsecond
  · rintro ⟨hcong, hpos⟩
    constructor
    · refine ⟨y, 1, one_ne_zero, ?_, hycop, ?_, hcong⟩
      · simp
      · rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq]
    · exact hpos

private theorem rayAdmissiblyPrincipal_span_iff (m : RayModulus K) (I : (Ideal O)⁰)
    (y : O) (hy : y ≠ 0) (hI : I.1 = Ideal.span {y})
    (hycop : IsCoprime (Ideal.span {y}) m.finite) :
    RayAdmissiblyPrincipal m I ↔ ∃ u : Oˣ,
      (u : O) * y - 1 ∈ m.finite ∧
      ∀ σ ∈ m.infinite, 0 < σ (algebraMap O K ((u : O) * y)) := by
  constructor
  · rintro ⟨α, hαadm, hαspan⟩
    have hspan : FractionalIdeal.spanSingleton O⁰ (algebraMap O K y) =
        FractionalIdeal.spanSingleton O⁰ (α : K) := by
      rw [← FractionalIdeal.coeIdeal_span_singleton, ← hI, hαspan]
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
    have huy : (u : O) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    let α' : Kˣ := Units.mk0 (algebraMap O K ((u : O) * y))
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 huy)
    have hα' : α' = α := by
      apply Units.ext
      change algebraMap O K ((u : O) * y) = (α : K)
      simpa [Units.smul_def, Algebra.smul_def] using hu
    have hcop' : IsCoprime (Ideal.span {(u : O) * y}) m.finite := by
      rw [← Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul]
      exact hycop
    refine ⟨u, ?_⟩
    rw [← rayAdmissible_integral_iff m ((u : O) * y) huy hcop']
    change RayAdmissible m α'
    rwa [hα']
  · rintro ⟨u, hu⟩
    have huy : (u : O) * y ≠ 0 := mul_ne_zero u.ne_zero hy
    let α : Kˣ := Units.mk0 (algebraMap O K ((u : O) * y))
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 huy)
    have hcop' : IsCoprime (Ideal.span {(u : O) * y}) m.finite := by
      rw [← Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul]
      exact hycop
    refine ⟨α, (rayAdmissible_integral_iff m ((u : O) * y) huy hcop').2 hu, ?_⟩
    rw [hI, FractionalIdeal.coeIdeal_span_singleton]
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
    refine ⟨u, ?_⟩
    change (u : O) • algebraMap O K y = algebraMap O K ((u : O) * y)
    simp [Algebra.smul_def]

private theorem rayPrincipalMulEquiv_apply_val (B : (Ideal O)⁰)
    (A : {A : (Ideal O)⁰ // IsPrincipal (B * A).1}) :
    (rayPrincipalMulEquiv B A).1 = B * A.1 := by
  simp [rayPrincipalMulEquiv, Equiv.subtypeSubtypeEquivSubtypeInter]

private theorem rayPrincipalMulEquiv_symm_apply_val (B : (Ideal O)⁰)
    (I : RayPrincipalDvd B) :
    B * ((rayPrincipalMulEquiv B).symm I).1 = I.1 := by
  calc
    B * ((rayPrincipalMulEquiv B).symm I).1 =
        (rayPrincipalMulEquiv B ((rayPrincipalMulEquiv B).symm I)).1 :=
      (rayPrincipalMulEquiv_apply_val B ((rayPrincipalMulEquiv B).symm I)).symm
    _ = I.1 := congrArg Subtype.val ((rayPrincipalMulEquiv B).apply_symm_apply I)

private theorem idealSetEquiv_eq_idealSetMap (B : (Ideal O)⁰) (z : idealSet K B) :
    ((idealSetEquiv K B z).1 : integerSet K) = idealSetMap K B z := rfl

private theorem rayIdealSetPrincipalDvdEquiv_fst (B : (Ideal O)⁰) (z : idealSet K B) :
    ((rayIdealSetPrincipalDvdEquiv B z).1.1 : Ideal O) =
      Ideal.span {(preimageOfMemIntegerSet (idealSetMap K B z) : O)} := by
  rw [← idealSetEquiv_eq_idealSetMap B z]
  simp [rayIdealSetPrincipalDvdEquiv, Equiv.prodCongrLeft,
    Equiv.subtypeSubtypeEquivSubtypeInter, Equiv.prodSubtypeFstEquivSubtypeProd]
  rfl

private theorem rayIdealSetMulEquiv_ideal (B : (Ideal O)⁰) (z : idealSet K B) :
    ((B * (rayIdealSetMulEquiv B z).1.1).1 : Ideal O) =
      Ideal.span {(preimageOfMemIntegerSet (idealSetMap K B z) : O)} := by
  have hmul : B * (rayIdealSetMulEquiv B z).1.1 =
      (rayIdealSetPrincipalDvdEquiv B z).1.1 := by
    change B * ((rayPrincipalMulEquiv B).symm
      (rayIdealSetPrincipalDvdEquiv B z).1).1 =
        (rayIdealSetPrincipalDvdEquiv B z).1.1
    exact rayPrincipalMulEquiv_symm_apply_val B (rayIdealSetPrincipalDvdEquiv B z).1
  rw [hmul]
  exact rayIdealSetPrincipalDvdEquiv_fst B z

private theorem rayIdealSetMulEquiv_absNorm (B : (Ideal O)⁰) (z : idealSet K B) :
    (Ideal.absNorm (B * (rayIdealSetMulEquiv B z).1.1).1 : ℝ) =
      mixedEmbedding.norm (z : mixedSpace K) := by
  rw [rayIdealSetMulEquiv_ideal B z, Ideal.absNorm_span_singleton]
  exact intNorm_coe (idealSetMap K B z)

private theorem preimage_idealSetMap_ne_zero (B : (Ideal O)⁰) (z : idealSet K B) :
    (preimageOfMemIntegerSet (idealSetMap K B z) : O) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero _

private theorem rayIdealSetMulEquiv_norm_eq (B : (Ideal O)⁰) (z : idealSet K B) :
    mixedEmbedding.norm (z : mixedSpace K) =
      (Ideal.absNorm B.1 : ℝ) *
        (Ideal.absNorm (rayIdealSetMulEquiv B z).1.1.1 : ℝ) := by
  rw [← rayIdealSetMulEquiv_absNorm B z]
  simp only [Submonoid.coe_mul, map_mul, Nat.cast_mul]

private theorem isCoprime_span_of_unit_congruence (m : RayModulus K)
    (y : O) (u : Oˣ) (h : (u : O) * y - 1 ∈ m.finite) :
    IsCoprime (Ideal.span {y}) m.finite := by
  have huy : IsCoprime (Ideal.span {(u : O) * y}) m.finite := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨(u : O) * y, Ideal.subset_span (Set.mem_singleton _),
      1 - (u : O) * y, ?_, by ring⟩
    simpa only [neg_sub] using m.finite.neg_mem h
  rwa [Ideal.span_singleton_mul_left_unit u.isUnit y] at huy

private theorem rayRepresentativeProperty_iff_datum (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite)
    (z : idealSet K B) (x : ℝ) :
    RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x ↔
      ∃ q : GoodRayDatum m,
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x := by
  let A : (Ideal O)⁰ := (rayIdealSetMulEquiv B z).1.1
  let y : O := preimageOfMemIntegerSet (idealSetMap K B z)
  have hy : y ≠ 0 := preimage_idealSetMap_ne_zero B z
  have hI : (B * A).1 = Ideal.span {y} := rayIdealSetMulEquiv_ideal B z
  have hnorm : mixedEmbedding.norm (z : mixedSpace K) =
      (Ideal.absNorm B.1 : ℝ) * (Ideal.absNorm A.1 : ℝ) :=
    rayIdealSetMulEquiv_norm_eq B z
  have hNB : 0 < (Ideal.absNorm B.1 : ℝ) :=
    Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors B)
  constructor
  · rintro ⟨hAcop, hprincipal, hAx⟩
    have hycop : IsCoprime (Ideal.span {y}) m.finite := by
      rw [← hI]
      exact hB.mul_left hAcop
    obtain ⟨u, hu⟩ :=
      (rayAdmissiblyPrincipal_span_iff m (B * A) y hy hI hycop).mp hprincipal
    let q : GoodRayDatum m := ⟨unitRayDatum m u, u, rfl⟩
    refine ⟨q, (integralRayDatum_eq_unit_iff m y hy u).2 hu, ?_⟩
    rw [hnorm]
    exact (mul_le_mul_iff_of_pos_left hNB).2 hAx
  · rintro ⟨q, hdatum, hnormx⟩
    obtain ⟨u, huq⟩ := q.2
    have hdu : integralRayDatum m y = unitRayDatum m u := hdatum.trans huq.symm
    have hu := (integralRayDatum_eq_unit_iff m y hy u).1 hdu
    have hycop : IsCoprime (Ideal.span {y}) m.finite :=
      isCoprime_span_of_unit_congruence m y u hu.1
    have hBAcop : IsCoprime (B.1 * A.1) m.finite := by
      rw [← Submonoid.coe_mul, hI]
      exact hycop
    refine ⟨IsCoprime.of_mul_left_right hBAcop,
      (rayAdmissiblyPrincipal_span_iff m (B * A) y hy hI hycop).2 ⟨u, hu⟩, ?_⟩
    rw [hnorm] at hnormx
    exact (mul_le_mul_iff_of_pos_left hNB).1 hnormx

private theorem exists_rayDatumLift (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (q : RayResidueSignData m) :
    ∃ y : O, y ∈ B.1 ∧ Ideal.Quotient.mk m.finite y = q.1 := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective q.1
  obtain ⟨b, hb, c, hc, hbc⟩ := hB.exists
  refine ⟨a * b, B.1.mul_mem_left a hb, ?_⟩
  rw [← ha]
  apply Ideal.Quotient.eq.mpr
  have : a * b - a = -a * c := by
    calc
      a * b - a = a * (b - 1) := by ring
      _ = a * (-c) := by rw [show b - 1 = -c by rw [← hbc]; ring]
      _ = -a * c := by ring
  rw [this]
  exact m.finite.mul_mem_left (-a) hc

private noncomputable def rayDatumLift (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (q : RayResidueSignData m) : O :=
  Classical.choose (exists_rayDatumLift m B hB q)

private theorem rayDatumLift_mem (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (q : RayResidueSignData m) :
    rayDatumLift m B hB q ∈ B.1 :=
  (Classical.choose_spec (exists_rayDatumLift m B hB q)).1

private theorem rayDatumLift_mod (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (q : RayResidueSignData m) :
    Ideal.Quotient.mk m.finite (rayDatumLift m B hB q) = q.1 :=
  (Classical.choose_spec (exists_rayDatumLift m B hB q)).2

private noncomputable def rayCongruenceIdeal (m : RayModulus K) (B : (Ideal O)⁰) :
    (Ideal O)⁰ :=
  ⟨B.1 * m.finite, mem_nonZeroDivisors_of_ne_zero
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero B) m.finite_ne)⟩

private theorem mixedEmbedding_sub_mem_rayCongruenceLattice_iff
    (m : RayModulus K) (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite)
    (q : RayResidueSignData m) (y : O) :
    mixedEmbedding K y - mixedEmbedding K (rayDatumLift m B hB q) ∈
        mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (rayCongruenceIdeal m B)) ↔
      y ∈ B.1 ∧ Ideal.Quotient.mk m.finite y = q.1 := by
  let v : O := rayDatumLift m B hB q
  constructor
  · intro h
    rw [mem_idealLattice] at h
    obtain ⟨a, ha, haemb⟩ := h
    change a ∈ ((rayCongruenceIdeal m B : Ideal O) : FractionalIdeal O⁰ K) at ha
    obtain ⟨z, hz, hza⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp ha
    have hzy : z = y - v := by
      apply (FaithfulSMul.algebraMap_injective O K)
      apply mixedEmbedding_injective K
      rw [hza, haemb]
      dsimp only [v]
      change mixedEmbedding K (algebraMap O K y) -
        mixedEmbedding K (algebraMap O K (rayDatumLift m B hB q)) = _
      rw [map_sub, map_sub]
    have hzprod : z ∈ B.1 * m.finite := hz
    have hzB : z ∈ B.1 := (Ideal.mul_le_right : B.1 * m.finite ≤ B.1) hzprod
    have hzM : z ∈ m.finite := (Ideal.mul_le_left : B.1 * m.finite ≤ m.finite) hzprod
    have hyB : y ∈ B.1 := by
      rw [hzy] at hzB
      have := B.1.add_mem hzB (rayDatumLift_mem m B hB q)
      simpa [v] using this
    refine ⟨hyB, ?_⟩
    rw [← rayDatumLift_mod m B hB q]
    apply Ideal.Quotient.eq.mpr
    rwa [hzy] at hzM
  · rintro ⟨hyB, hymod⟩
    rw [mem_idealLattice]
    refine ⟨algebraMap O K (y - rayDatumLift m B hB q), ?_, ?_⟩
    · change algebraMap O K (y - rayDatumLift m B hB q) ∈
        ((rayCongruenceIdeal m B : Ideal O) : FractionalIdeal O⁰ K)
      apply FractionalIdeal.mem_coeIdeal_of_mem O⁰
      change y - rayDatumLift m B hB q ∈ B.1 * m.finite
      rw [Ideal.mul_eq_inf_of_isCoprime hB]
      refine ⟨B.1.sub_mem hyB (rayDatumLift_mem m B hB q), ?_⟩
      apply Ideal.Quotient.eq.mp
      rwa [rayDatumLift_mod m B hB q]
    · simp

private theorem integralRayDatum_snd_eq_iff (m : RayModulus K)
    (y : O) (hy : y ≠ 0) (e : (σ : ↥m.infinite) → Bool) :
    (integralRayDatum m y).2 = e ↔
      ∀ σ : ↥m.infinite, mixedEmbedding K y ∈ raySignHalfSpace σ.1 (e σ) := by
  have hyK : algebraMap O K y ≠ 0 :=
    (map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hy
  constructor
  · intro h σ
    have hσ := congrFun h σ
    have hnz : σ.1 (algebraMap O K y) ≠ 0 := (map_ne_zero σ.1).2 hyK
    cases he : e σ
    · have hnpos : ¬0 < σ.1 (algebraMap O K y) := by
        simpa [integralRayDatum, he] using hσ
      have hneg := lt_of_le_of_ne (le_of_not_gt hnpos) hnz
      simpa [raySignHalfSpace, he, rayRealCoordinate_mixedEmbedding] using hneg
    · have hpos : 0 < σ.1 (algebraMap O K y) := by
        simpa [integralRayDatum, he] using hσ
      simpa [raySignHalfSpace, he, rayRealCoordinate_mixedEmbedding] using hpos
  · intro h
    funext σ
    have hσ := h σ
    cases he : e σ
    · have hneg : σ.1 (algebraMap O K y) < 0 := by
        simpa [raySignHalfSpace, he, rayRealCoordinate_mixedEmbedding] using hσ
      simp [integralRayDatum, he, not_lt_of_ge hneg.le]
    · have hpos : 0 < σ.1 (algebraMap O K y) := by
        simpa [raySignHalfSpace, he, rayRealCoordinate_mixedEmbedding] using hσ
      simp [integralRayDatum, he, hpos]

private theorem mem_raySignRegion_iff (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) (z : mixedSpace K) :
    z ∈ raySignRegion m e ↔
      z ∈ normLeOne K ∧ ∀ σ : ↥m.infinite, z ∈ raySignHalfSpace σ.1 (e σ) := by
  simp [raySignRegion, raySignRegionFinset]

private theorem mem_rpow_smul_raySignRegion_iff (m : RayModulus K)
    (e : (σ : ↥m.infinite) → Bool) (z : mixedSpace K) {s : ℝ} (hs : 0 < s) :
    z ∈ Real.rpow s ((Module.finrank ℚ K : ℝ)⁻¹) • raySignRegion m e ↔
      z ∈ fundamentalCone K ∧ mixedEmbedding.norm z ≤ s ∧
        ∀ σ : ↥m.infinite, z ∈ raySignHalfSpace σ.1 (e σ) := by
  let d := Module.finrank ℚ K
  let t := Real.rpow s (d : ℝ)⁻¹
  have hd : 0 < d := Module.finrank_pos
  have ht : 0 < t := Real.rpow_pos_of_pos hs _
  have htd : t ^ d = s := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_inv_rpow hs.le (Nat.cast_ne_zero.mpr hd.ne')
  change z ∈ t • raySignRegion m e ↔ _
  constructor
  · rw [Set.mem_smul_set]
    rintro ⟨y, hy, rfl⟩
    have hyr := (mem_raySignRegion_iff m e y).1 hy
    refine ⟨fundamentalCone.smul_mem_of_mem hyr.1.1 ht.ne', ?_, ?_⟩
    · rw [mixedEmbedding.norm_smul, abs_of_pos ht,
        show Module.finrank ℚ K = d from rfl, htd]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hyr.1.2 hs.le
    · intro σ
      have hc : rayRealCoordinate σ.1 (t • y) = t * rayRealCoordinate σ.1 y := by
        simp [rayRealCoordinate]
      cases he : e σ
      · have hn : rayRealCoordinate σ.1 y < 0 := by
          simpa [raySignHalfSpace, he] using hyr.2 σ
        simpa [raySignHalfSpace, he, hc] using mul_neg_of_pos_of_neg ht hn
      · have hp : 0 < rayRealCoordinate σ.1 y := by
          simpa [raySignHalfSpace, he] using hyr.2 σ
        simpa [raySignHalfSpace, he, hc] using mul_pos ht hp
  · rintro ⟨hzc, hzn, hzs⟩
    let y : mixedSpace K := t⁻¹ • z
    have hzy : t • y = z := by
      dsimp only [y]
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hyc := fundamentalCone.smul_mem_of_mem hzc (inv_ne_zero ht.ne')
    have hyn : mixedEmbedding.norm y ≤ 1 := by
      have heq : mixedEmbedding.norm z = s * mixedEmbedding.norm y := by
        rw [← hzy, mixedEmbedding.norm_smul, abs_of_pos ht,
          show Module.finrank ℚ K = d from rfl, htd]
      nlinarith [mixedEmbedding.norm_nonneg y]
    have hys : ∀ σ : ↥m.infinite, y ∈ raySignHalfSpace σ.1 (e σ) := by
      intro σ
      have hc : rayRealCoordinate σ.1 z = t * rayRealCoordinate σ.1 y := by
        rw [← hzy]
        simp [rayRealCoordinate]
      cases he : e σ
      · have hn : rayRealCoordinate σ.1 z < 0 := by
          simpa [raySignHalfSpace, he] using hzs σ
        have : rayRealCoordinate σ.1 y < 0 := by
          rw [hc] at hn
          nlinarith
        simpa [raySignHalfSpace, he] using this
      · have hp : 0 < rayRealCoordinate σ.1 z := by
          simpa [raySignHalfSpace, he] using hzs σ
        have : 0 < rayRealCoordinate σ.1 y := by
          rw [hc] at hp
          nlinarith
        simpa [raySignHalfSpace, he] using this
    rw [Set.mem_smul_set]
    exact ⟨y, (mem_raySignRegion_iff m e y).2 ⟨⟨hyc, hyn⟩, hys⟩, hzy⟩

private theorem exists_integer_of_mem_rayCongruence_affine
    (m : RayModulus K) (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite)
    (q : RayResidueSignData m) (x : mixedSpace K)
    (hx : x - mixedEmbedding K (rayDatumLift m B hB q) ∈
      mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))) :
    ∃ y : O, y ∈ B.1 ∧ Ideal.Quotient.mk m.finite y = q.1 ∧ mixedEmbedding K y = x := by
  rw [mem_idealLattice] at hx
  obtain ⟨a, ha, haemb⟩ := hx
  change a ∈ ((rayCongruenceIdeal m B : Ideal O) : FractionalIdeal O⁰ K) at ha
  obtain ⟨k, hk, hka⟩ := (FractionalIdeal.mem_coeIdeal O⁰).mp ha
  let y := rayDatumLift m B hB q + k
  refine ⟨y, ?_, ?_, ?_⟩
  · exact B.1.add_mem (rayDatumLift_mem m B hB q)
      ((Ideal.mul_le_right : B.1 * m.finite ≤ B.1) hk)
  · rw [← rayDatumLift_mod m B hB q]
    apply Ideal.Quotient.eq.mpr
    rw [show y - rayDatumLift m B hB q = k by simp [y]]
    exact (Ideal.mul_le_left : B.1 * m.finite ≤ m.finite) hk
  · apply_fun fun z => z - mixedEmbedding K (rayDatumLift m B hB q)
    · change mixedEmbedding K (algebraMap O K y) - _ = _
      rw [show algebraMap O K y = algebraMap O K (rayDatumLift m B hB q) + a by
        simp only [y, map_add, hka], map_add]
      rw [haemb]
      abel
    · intro z w h
      simpa using congrArg (fun v => v + mixedEmbedding K (rayDatumLift m B hB q)) h

private theorem ne_zero_of_mem_fundamentalCone {x : mixedSpace K}
    (hx : x ∈ fundamentalCone K) : x ≠ 0 := by
  intro h
  subst x
  simpa using fundamentalCone.norm_pos_of_mem hx

private noncomputable def rayDatumFiberEquiv (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) (q : GoodRayDatum m)
    {s : ℝ} (hs : 0 < s) :
    {z : idealSet K B //
      integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ s} ≃
    {x : mixedSpace K //
      x ∈ s ^ ((Module.finrank ℚ K : ℝ)⁻¹) • raySignRegion m q.1.2 ∧
      x - mixedEmbedding K (rayDatumLift m B hB q.1) ∈
        mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))} where
  toFun z := by
    let y : O := (preimageOfMemIntegerSet (idealSetMap K B z.1) : O)
    have hy : y ≠ 0 := preimage_idealSetMap_ne_zero B z.1
    have hfst := congrArg Prod.fst z.2.1
    have hsnd := congrArg Prod.snd z.2.1
    have hsign := (integralRayDatum_snd_eq_iff m y hy q.1.2).1 hsnd
    have hyemb : mixedEmbedding K y = (z.1 : mixedSpace K) := by
      simpa [y] using mixedEmbedding_preimageOfMemIntegerSet (idealSetMap K B z.1)
    refine ⟨z.1, ?_, ?_⟩
    · apply (mem_rpow_smul_raySignRegion_iff m q.1.2 z.1 hs).2
      refine ⟨z.1.2.1, z.2.2, ?_⟩
      intro σ
      rw [← hyemb]
      exact hsign σ
    · rw [← hyemb]
      apply (mixedEmbedding_sub_mem_rayCongruenceLattice_iff m B hB q.1 y).2
      exact ⟨preimage_of_IdealSetMap K B z.1, hfst⟩
  invFun x := by
    let ex := exists_integer_of_mem_rayCongruence_affine m B hB q.1 x.1 x.2.2
    let y : O := Classical.choose ex
    have hyB : y ∈ B.1 := (Classical.choose_spec ex).1
    have hyres : Ideal.Quotient.mk m.finite y = q.1.1 :=
      (Classical.choose_spec ex).2.1
    have hyemb : mixedEmbedding K y = x.1 := (Classical.choose_spec ex).2.2
    have hr := (mem_rpow_smul_raySignRegion_iff m q.1.2 x.1 hs).1 x.2.1
    have hy : y ≠ 0 := by
      intro h
      apply ne_zero_of_mem_fundamentalCone hr.1
      rw [← hyemb, h]
      simp
    let z : idealSet K B := ⟨x.1, mem_idealSet.mpr ⟨hr.1, y, hyB, hyemb⟩⟩
    have hpre : (preimageOfMemIntegerSet (idealSetMap K B z) : O) = y := by
      apply (FaithfulSMul.algebraMap_injective O K)
      apply mixedEmbedding_injective K
      rw [mixedEmbedding_preimageOfMemIntegerSet]
      exact hyemb.symm
    refine ⟨z, ?_, hr.2.1⟩
    rw [hpre]
    apply Prod.ext
    · exact hyres
    · apply (integralRayDatum_snd_eq_iff m y hy q.1.2).2
      intro σ
      rw [hyemb]
      exact hr.2.2 σ
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

private theorem rayDatumFiber_count_isBigO_raw (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) (q : GoodRayDatum m) :
    (fun x : ℝ =>
      (Nat.card {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} : ℝ) -
      (volume.real (raySignRegion m q.1.2) /
        ZLattice.covolume (mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))) *
        (Ideal.absNorm B.1 : ℝ)) * x) =O[atTop]
      (fun x : ℝ => x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  let L := mixedEmbedding.idealLattice K
    (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))
  let v := mixedEmbedding K (rayDatumLift m B hB q.1)
  let NB : ℝ := Ideal.absNorm B.1
  have hNB : 0 < NB := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors B)
  have hdim : Fintype.card (ConeBoundaryParameter K) + 1 =
      Module.finrank ℝ (mixedSpace K) := by
    rw [mixedEmbedding.finrank]
    exact coneBoundaryParameter_card (K := K)
  have h0 := LipschitzBoundaryCover.affineLatticePointCount_rpow_isBigO
      (L := L) (μ := volume) (data := raySignRegionBoundaryCover m q.1.2)
      (Module.Free.chooseBasis ℤ L) (raySignRegion_isBounded m q.1.2) hdim v
  have hk : Tendsto (fun x : ℝ => NB * x) atTop atTop := by
    simpa [mul_comm, NB] using
      (tendsto_id.atTop_mul_const' (show 0 < (Ideal.absNorm B.1 : ℝ) from hNB))
  have hc := h0.comp_tendsto hk
  have hf : ((fun x : ℝ =>
      (Discrepancy.affineLatticePointCount L v
        (x ^ (Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹ • raySignRegion m q.1.2) : ℝ) -
      volume.real (raySignRegion m q.1.2) / ZLattice.covolume L * x) ∘
        fun x : ℝ => NB * x) =ᶠ[atTop] fun x : ℝ =>
      (Nat.card {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} : ℝ) -
      (volume.real (raySignRegion m q.1.2) / ZLattice.covolume L *
        (Ideal.absNorm B.1 : ℝ)) * x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, mixedEmbedding.finrank]
    rw [Discrepancy.affineLatticePointCount_eq_natCard]
    have hcard := Nat.card_congr (rayDatumFiberEquiv m B hB q (mul_pos hNB hx))
    dsimp only [L, v]
    rw [← hcard]
    change _ - _ * (NB * x) = _ - (_ * NB) * x
    ring
  have hright : (fun x : ℝ => (NB * x) ^ (1 - 1 /
      (Module.finrank ℝ (mixedSpace K) : ℝ))) =O[atTop]
      (fun x : ℝ => x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
    have heq : (fun x : ℝ => (NB * x) ^ (1 - 1 /
        (Module.finrank ℝ (mixedSpace K) : ℝ))) =ᶠ[atTop]
        (fun x : ℝ => NB ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) *
          x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [mixedEmbedding.finrank, Real.mul_rpow hNB.le hx]
    exact (Asymptotics.isBigO_const_mul_self _ _ _).congr' heq.symm EventuallyEq.rfl
  exact (hc.congr' hf EventuallyEq.rfl).trans hright

private noncomputable def rayDatumCoefficient (m : RayModulus K)
    (q : GoodRayDatum m) : ℝ :=
  volume.real (raySignRegion m q.1.2) /
    ((Ideal.absNorm m.finite : ℝ) *
      (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |NumberField.discr K|)

private theorem rayDatumCoefficient_eq (m : RayModulus K) (B : (Ideal O)⁰)
    (q : GoodRayDatum m) :
    volume.real (raySignRegion m q.1.2) /
      ZLattice.covolume (mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))) *
      (Ideal.absNorm B.1 : ℝ) = rayDatumCoefficient m q := by
  have hNB : (Ideal.absNorm B.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors B)
  rw [mixedEmbedding.covolume_idealLattice, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  change _ / (((Ideal.absNorm (B.1 * m.finite) : ℕ) : ℝ) *
    (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |NumberField.discr K|) *
      (Ideal.absNorm B.1 : ℝ) = _
  rw [map_mul, Nat.cast_mul]
  unfold rayDatumCoefficient
  field_simp

private theorem rayDatumFiber_count_isBigO (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) (q : GoodRayDatum m) :
    (fun x : ℝ =>
      (Nat.card {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} : ℝ) -
      rayDatumCoefficient m q * x) =O[atTop]
      (fun x : ℝ => x ^ ((Module.finrank ℚ K - 1 : ℝ) /
        (Module.finrank ℚ K : ℝ))) := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  have he : 1 - 1 / (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ K - 1 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    field_simp
  simpa only [rayDatumCoefficient_eq m B q, he] using
    rayDatumFiber_count_isBigO_raw m B hB q

private theorem finite_rayDatumFiber (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (q : GoodRayDatum m) (x : ℝ) :
    Finite {z : idealSet K B //
      integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
      mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} := by
  let s : ℝ := (Ideal.absNorm B.1 : ℝ) * x
  by_cases hs : 0 < s
  · let S := s ^ ((Module.finrank ℚ K : ℝ)⁻¹) • raySignRegion m q.1.2
    let L := mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K (rayCongruenceIdeal m B))
    let v := mixedEmbedding K (rayDatumLift m B hB q.1)
    letI : Finite {y : mixedSpace K // y ∈ S ∧ y - v ∈ L} :=
      Discrepancy.finite_affineLatticePointSubtype L v
        ((raySignRegion_isBounded m q.1.2).smul₀ _)
    exact Finite.of_equiv _ (rayDatumFiberEquiv m B hB q hs).symm
  · haveI : IsEmpty {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} :=
      ⟨fun z => (not_lt_of_ge (z.2.2.trans (le_of_not_gt hs)))
        (fundamentalCone.norm_pos_of_mem z.1.2.1)⟩
    infer_instance

private noncomputable def rayGoodDatumFor (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (x : ℝ) (z : idealSet K B)
    (hz : RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x) :
    GoodRayDatum m :=
  Classical.choose ((rayRepresentativeProperty_iff_datum m B hB z x).1 hz)

private theorem rayGoodDatumFor_spec (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (x : ℝ) (z : idealSet K B)
    (hz : RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x) :
    integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) =
        (rayGoodDatumFor m B hB x z hz).1 ∧
      mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x :=
  Classical.choose_spec ((rayRepresentativeProperty_iff_datum m B hB z x).1 hz)

private theorem rayGoodDatumFor_eq (m : RayModulus K) (B : (Ideal O)⁰)
    (hB : IsCoprime B.1 m.finite) (x : ℝ) (z : idealSet K B)
    (hz : RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x)
    (q : GoodRayDatum m)
    (hq : integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1) :
    rayGoodDatumFor m B hB x z hz = q := by
  apply Subtype.ext
  exact (rayGoodDatumFor_spec m B hB x z hz).1.symm.trans hq

private noncomputable def rayCanonicalGeneratorDatumEquiv (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) (x : ℝ) :
    {z : idealSet K B //
      RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x} ≃
    Σ q : GoodRayDatum m, {z : idealSet K B //
      integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
      mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} where
  toFun z := ⟨rayGoodDatumFor m B hB x z.1 z.2, z.1,
    rayGoodDatumFor_spec m B hB x z.1 z.2⟩
  invFun p := ⟨p.2.1, (rayRepresentativeProperty_iff_datum m B hB p.2.1 x).2
    ⟨p.1, p.2.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨q, z⟩
    have hq := rayGoodDatumFor_eq m B hB x z.1
      ((rayRepresentativeProperty_iff_datum m B hB z.1 x).2 ⟨q, z.2⟩) q z.2.1
    refine Sigma.ext hq ?_
    apply (Subtype.heq_iff_coe_eq (fun _ => by dsimp; rw [hq])).2
    rfl

private noncomputable instance (m : RayModulus K) : Fintype (GoodRayDatum m) := by
  letI : Finite (O ⧸ m.finite) :=
    Ring.HasFiniteQuotients.finiteQuotient m.finite_ne
  exact Fintype.ofFinite _

private theorem rayCanonicalGeneratorCounting_eq_sum (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) (x : ℝ) :
    rayCanonicalGeneratorCounting m B x =
      ∑ q : GoodRayDatum m, Nat.card {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} := by
  classical
  letI : Finite (O ⧸ m.finite) :=
    Ring.HasFiniteQuotients.finiteQuotient m.finite_ne
  letI : Fintype (GoodRayDatum m) := Fintype.ofFinite _
  letI (q : GoodRayDatum m) : Finite {z : idealSet K B //
      integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
      mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} :=
    finite_rayDatumFiber m B hB q x
  rw [rayCanonicalGeneratorCounting]
  calc
    Nat.card {z : idealSet K B //
        RayRepresentativeProperty m B (rayIdealSetMulEquiv B z).1.1 x} =
        Nat.card (Σ q : GoodRayDatum m, {z : idealSet K B //
          integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
          mixedEmbedding.norm (z : mixedSpace K) ≤
            (Ideal.absNorm B.1 : ℝ) * x}) :=
      Nat.card_congr (rayCanonicalGeneratorDatumEquiv m B hB x)
    _ = _ := Nat.card_sigma

private noncomputable def rayTotalCoefficient (m : RayModulus K) : ℝ := by
  letI : Finite (O ⧸ m.finite) :=
    Ring.HasFiniteQuotients.finiteQuotient m.finite_ne
  letI : Fintype (GoodRayDatum m) := Fintype.ofFinite _
  exact ∑ q : GoodRayDatum m, rayDatumCoefficient m q

private theorem rayCanonicalGeneratorCounting_isBigO (m : RayModulus K)
    (B : (Ideal O)⁰) (hB : IsCoprime B.1 m.finite) :
    (fun x : ℝ => (rayCanonicalGeneratorCounting m B x : ℝ) -
      rayTotalCoefficient m * x) =O[atTop]
      (fun x : ℝ => x ^ ((Module.finrank ℚ K - 1 : ℝ) /
        (Module.finrank ℚ K : ℝ))) := by
  classical
  letI : Finite (O ⧸ m.finite) :=
    Ring.HasFiniteQuotients.finiteQuotient m.finite_ne
  letI : Fintype (GoodRayDatum m) := Fintype.ofFinite _
  have hsum := Asymptotics.IsBigO.sum (s := Finset.univ) (g := fun x : ℝ =>
      x ^ ((Module.finrank ℚ K - 1 : ℝ) / (Module.finrank ℚ K : ℝ)))
    (A := fun q x =>
      (Nat.card {z : idealSet K B //
        integralRayDatum m (preimageOfMemIntegerSet (idealSetMap K B z)) = q.1 ∧
        mixedEmbedding.norm (z : mixedSpace K) ≤ (Ideal.absNorm B.1 : ℝ) * x} : ℝ) -
      rayDatumCoefficient m q * x)
    (fun q _ => rayDatumFiber_count_isBigO m B hB q)
  apply hsum.congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  rw [rayCanonicalGeneratorCounting_eq_sum m B hB x, Nat.cast_sum,
    Finset.sum_sub_distrib]
  simp only [rayTotalCoefficient, Finset.sum_mul]

private theorem rayDatumCoefficient_pos (m : RayModulus K) (q : GoodRayDatum m) :
    0 < rayDatumCoefficient m q := by
  let M : (Ideal O)⁰ :=
    ⟨m.finite, mem_nonZeroDivisors_of_ne_zero m.finite_ne⟩
  have hM : 0 < (Ideal.absNorm m.finite : ℝ) :=
    Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors M)
  have hdiscZ : 0 < |NumberField.discr K| :=
    abs_pos.mpr (NumberField.discr_ne_zero K)
  have hdisc : 0 < (|NumberField.discr K| : ℝ) := by exact_mod_cast hdiscZ
  unfold rayDatumCoefficient
  exact div_pos (raySignRegion_measureReal_pos m q.1.2)
    (mul_pos (mul_pos hM (pow_pos (by norm_num) _)) (Real.sqrt_pos.2 hdisc))

private noncomputable def rayOneGoodDatum (m : RayModulus K) : GoodRayDatum m :=
  ⟨unitRayDatum m 1, 1, rfl⟩

private theorem rayTotalCoefficient_pos (m : RayModulus K) :
    0 < rayTotalCoefficient m := by
  rw [rayTotalCoefficient]
  exact Finset.sum_pos (fun q _ => rayDatumCoefficient_pos m q)
    ⟨rayOneGoodDatum m, Finset.mem_univ _⟩

/-- Quantitative Davenport boundary estimate for the finite union of
translated congruence lattices and sign chambers occurring inside Mathlib's
fundamental cone.  The normalization by the norm of `B` is built into
`RayRepresentativeProperty`; hence the leading coefficient `Λ` is independent
of `B`. -/
private theorem rayCanonicalGenerator_boundary_estimate (m : RayModulus K) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ B : (Ideal O)⁰, IsCoprime B.1 m.finite →
      Asymptotics.IsBigO atTop
        (fun x : ℝ => (rayCanonicalGeneratorCounting m B x : ℝ) - Λ * x)
        (fun x : ℝ => Real.rpow x
          (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  refine ⟨rayTotalCoefficient m, rayTotalCoefficient_pos m, ?_⟩
  intro B hB
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  have he : (Module.finrank ℚ K - 1 : ℝ) / (Module.finrank ℚ K : ℝ) =
      1 - 1 / (Module.finrank ℚ K : ℝ) := by
    field_simp
  simpa only [he, Real.rpow_eq_pow] using
    rayCanonicalGeneratorCounting_isBigO m B hB

/-- The geometry-of-numbers input for a translated congruence lattice in the
fundamental unit sector. The error function records boundary cells, and the
same `ρ` for every class records cancellation of the representative ideal's
norm against the covolume of its lattice. -/
private theorem rayClass_congruenceLattice_count (m : RayModulus K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : RayClassGroup m,
      ∃ error : ℝ → ℝ,
        (∀ x : ℝ, (rayIdealCounting m c x : ℝ) = ρ * x + error x) ∧
        Asymptotics.IsBigO atTop error
          (fun x : ℝ => Real.rpow x
            (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  obtain ⟨Λ, hΛ, hboundary⟩ := rayCanonicalGenerator_boundary_estimate m
  let τ : ℝ := torsionOrder K
  have hτ : 0 < τ := Nat.cast_pos.mpr (torsionOrder_pos K)
  let ρ : ℝ := Λ / τ
  refine ⟨ρ, div_pos hΛ hτ, fun c => ?_⟩
  obtain ⟨b, hb0, hbcop, hb⟩ := rayClass_admissibleGenerators m c
  let B : (Ideal O)⁰ := ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩
  have hO := hboundary B hbcop
  let error : ℝ → ℝ := fun x => (rayIdealCounting m c x : ℝ) - ρ * x
  refine ⟨error, fun x => by simp only [error]; ring, ?_⟩
  have hscaled := hO.const_mul_left τ⁻¹
  apply hscaled.congr (fun x => ?_) (fun _ => rfl)
  have hcountNat : rayCanonicalGeneratorCounting m B x =
      rayIdealCounting m c x * torsionOrder K := by
    rw [rayCanonicalGeneratorCounting_eq_mul,
      ← rayIdealCounting_eq_rep m c b hb0 hb x]
  have hcount : (rayCanonicalGeneratorCounting m B x : ℝ) =
      (rayIdealCounting m c x : ℝ) * τ := by
    change (rayCanonicalGeneratorCounting m B x : ℝ) =
      (rayIdealCounting m c x : ℝ) * (torsionOrder K : ℝ)
    exact_mod_cast hcountNat
  rw [hcount]
  dsimp only [error, ρ, τ]
  field_simp [Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)]

/-- Blueprint Theorem 5.2, proposed declaration
`RayClassGroup.tendsto_idealCount`: every ray class has the same positive
leading constant `ρ_(K,m)`. -/
theorem RayClassGroup.tendsto_idealCount (m : RayModulus K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : RayClassGroup m,
      Tendsto (fun x : ℝ => (rayIdealCounting m c x : ℝ) / x) atTop (𝓝 ρ) := by
  obtain ⟨ρ, hρ, hcount⟩ := rayClass_congruenceLattice_count m
  refine ⟨ρ, hρ, fun c ↦ ?_⟩
  obtain ⟨error, herror, hO⟩ := hcount c
  apply tendsto_div_of_sub_isBigO_rpow
    (fun x : ℝ ↦ (rayIdealCounting m c x : ℝ)) ρ (Module.finrank ℚ K)
    Module.finrank_pos
  simpa only [herror, add_sub_cancel_left] using hO

/-- Blueprint Theorem 5.2, equation (3),
`RayClassGroup.idealCount_sub_linear_isBigO`: the common leading term has the
quantitative error `O(x^(1-1/[K:Q]))` (and hence `O(1)` in degree one). -/
theorem RayClassGroup.idealCount_sub_linear_isBigO (m : RayModulus K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : RayClassGroup m,
      Asymptotics.IsBigO atTop
        (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
        (fun x : ℝ =>
          Real.rpow x
            (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  obtain ⟨ρ, hρ, hcount⟩ := rayClass_congruenceLattice_count m
  refine ⟨ρ, hρ, fun c ↦ ?_⟩
  obtain ⟨error, herror, hO⟩ := hcount c
  simpa only [herror, add_sub_cancel_left] using hO

end
end NU.Chebotarev
