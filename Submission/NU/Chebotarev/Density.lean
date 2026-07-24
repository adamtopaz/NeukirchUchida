import Mathlib

/-!
# M1. Prime sets and density algebra

Blueprint §2 (elementary density bookkeeping), §9 (the Dirichlet-density-only
variant), and §10.2 (recommended core definitions). This file is independent of
Galois theory.
-/

open Filter Topology
open scoped BigOperators

namespace NU.Chebotarev

/-- The nonzero prime ideals of the ring of integers of `K` (blueprint §10.2). -/
abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a prime ideal, as a natural number. -/
noncomputable def PrimeIdeal.norm (p : PrimeIdeal K) : ℕ :=
  Ideal.absNorm p.asIdeal

/-- Number of primes in `S` of norm at most `x` (blueprint §10.2). -/
noncomputable def primeCounting (S : Set (PrimeIdeal K)) (x : ℝ) : ℕ :=
  Nat.card {p : PrimeIdeal K // p ∈ S ∧ (PrimeIdeal.norm p : ℝ) ≤ x}

/-- Natural density of a set of primes, normalized by `x / log x`
(blueprint §10.2; equivalence with the `Li x` normalization is in
`NaturalDensity.lean`). -/
def HasPrimeDensity (S : Set (PrimeIdeal K)) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => (primeCounting S x : ℝ) / (x / Real.log x))
    atTop (𝓝 δ)

/-- Lower prime-number-theorem density from blueprint §2. -/
noncomputable def lowerPrimeDensity (S : Set (PrimeIdeal K)) : ℝ :=
  liminf (fun x : ℝ => (primeCounting S x : ℝ) / (x / Real.log x)) atTop

/-- Upper prime-number-theorem density from blueprint §2. -/
noncomputable def upperPrimeDensity (S : Set (PrimeIdeal K)) : ℝ :=
  limsup (fun x : ℝ => (primeCounting S x : ℝ) / (x / Real.log x)) atTop

/-- The prime Dirichlet series of `S` on the real axis. -/
noncomputable def dirichletPrimeSum (S : Set (PrimeIdeal K)) (s : ℝ) : ℝ := by
  classical
  exact ∑' p : PrimeIdeal K,
    if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0

/-- The Dirichlet-density normalization from blueprint §9. -/
noncomputable def dirichletNormalizer (s : ℝ) : ℝ :=
  Real.log (1 / (s - 1))

/-- A set of prime ideals has Dirichlet density `δ` (blueprint §9). -/
def HasDirichletDensity (S : Set (PrimeIdeal K)) (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ => dirichletPrimeSum S s / dirichletNormalizer s)
    (𝓝[>] (1 : ℝ)) (𝓝 δ)

/-- Lower Dirichlet density from blueprint §9. -/
noncomputable def lowerDirichletDensity (S : Set (PrimeIdeal K)) : ℝ :=
  liminf (fun s : ℝ => dirichletPrimeSum S s / dirichletNormalizer s)
    (𝓝[>] (1 : ℝ))

/-- Upper Dirichlet density from blueprint §9. -/
noncomputable def upperDirichletDensity (S : Set (PrimeIdeal K)) : ℝ :=
  limsup (fun s : ℝ => dirichletPrimeSum S s / dirichletNormalizer s)
    (𝓝[>] (1 : ℝ))

/-- Symmetric difference, used to state finite-partition lemmas without choosing
extra set notation. -/
def symmetricDifference {α : Type*} (A B : Set α) : Set α :=
  (A \ B) ∪ (B \ A)

private theorem tendsto_x_div_log_atTop :
    Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 * max b 0))] with x hx hsqrt
  have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ x)
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by linarith : 1 < x))]
  have hsq : (Real.sqrt x)^2 = x := Real.sq_sqrt (by linarith)
  have hb : b ≤ Real.sqrt x / 2 := by
    have : 2 * b ≤ Real.sqrt x := le_trans (by gcongr; exact le_max_left _ _) hsqrt
    linarith
  have hlog' : Real.log x ≤ Real.sqrt x * 2 := by linarith [hlog]
  have hmul := mul_le_mul_of_nonneg_left hlog' (Real.sqrt_nonneg x)
  have hlogpos : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  have hblog := mul_le_mul_of_nonneg_right hb hlogpos
  nlinarith

private theorem tendsto_dirichletNormalizer_atTop :
    Tendsto dirichletNormalizer (𝓝[>] (1 : ℝ)) atTop := by
  change Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop
  apply Real.tendsto_log_atTop.comp
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h := (continuousAt_id.sub
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 1)).tendsto
      convert h.mono_left nhdsWithin_le_nhds using 1 <;> ext <;> simp
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (show 0 < s - 1 from sub_pos.mpr hs)
  convert tendsto_inv_nhdsGT_zero.comp hsub using 1 <;> simp [Function.comp_def]

private theorem idealNormSet_finite (x : ℝ) :
    {I : Ideal (NumberField.RingOfIntegers K) |
      (Ideal.absNorm I : ℝ) ≤ x}.Finite := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge x
  apply (Ideal.finite_setOf_absNorm_le
    (S := NumberField.RingOfIntegers K) n).subset
  intro I hI
  exact_mod_cast hI.trans hn

/-- Blueprint Lemma 2.1 (`ideal_linear_bound`): nonzero integral ideals of
bounded norm are `O(x)`. -/
theorem ideal_linear_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x →
      Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ x} ≤ A * x := by
  let c : ℝ :=
    (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      NumberField.Units.regulator K * NumberField.classNumber K) /
      (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|)
  let B : ℝ := |c| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlim : Tendsto (fun s : ℝ =>
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I ≤ s} : ℝ) / s) atTop (𝓝 c) := by
    exact NumberField.Ideal.tendsto_norm_le_div_atTop K
  have hcB : c < B := by dsimp [B]; linarith [le_abs_self c]
  have hev : ∀ᶠ x : ℝ in atTop,
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I ≤ x} : ℝ) / x < B :=
    hlim (Iio_mem_nhds hcB)
  rw [eventually_atTop] at hev
  obtain ⟨b, hb⟩ := hev
  let t := max b 1
  let N : ℝ := Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
    Ideal.absNorm I ≤ t}
  refine ⟨B + N, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  by_cases htx : t ≤ x
  · have hratio := hb x (le_trans (le_max_left b 1) htx)
    have hall : (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I ≤ x} : ℝ) < B * x :=
      (div_lt_iff₀ hxpos).mp hratio
    letI : Fintype {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ x} := (idealNormSet_finite (K := K) x).fintype
    have hsub : Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ x} ≤
        Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ x} := by
      apply Nat.card_le_card_of_injective
        (fun a => (⟨a.1, a.2.2⟩ :
          {I : Ideal (NumberField.RingOfIntegers K) //
            (Ideal.absNorm I : ℝ) ≤ x}))
      intro a d had
      apply Subtype.ext
      exact congrArg (fun z : {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ x} => z.1) had
    have hsubR : (Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ x} : ℝ) ≤
        Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ x} := by exact_mod_cast hsub
    norm_cast
    exact (hsubR.trans hall.le).trans (by
      have hN : 0 ≤ N := Nat.cast_nonneg _
      nlinarith)
  · have hxt : x ≤ t := le_of_not_ge htx
    letI : Fintype {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ t} := (idealNormSet_finite (K := K) t).fintype
    have hsub : Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ x} ≤
        Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          (Ideal.absNorm I : ℝ) ≤ t} := by
      apply Nat.card_le_card_of_injective
        (fun a => (⟨a.1, a.2.2.trans hxt⟩ :
          {I : Ideal (NumberField.RingOfIntegers K) //
            (Ideal.absNorm I : ℝ) ≤ t}))
      intro a d had
      apply Subtype.ext
      exact congrArg (fun z : {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ t} => z.1) had
    have hsubR : (Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ x} : ℝ) ≤ N := by
      change _ ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        (Ideal.absNorm I : ℝ) ≤ t} : ℝ)
      exact_mod_cast hsub
    norm_cast
    exact hsubR.trans (by
      have hN : 0 ≤ N := Nat.cast_nonneg _
      nlinarith)

private theorem coeff_sum (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n,
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} =
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
      I ≠ 0 ∧ Ideal.absNorm I ≤ n} := by
  rw [← Finset.card_preimage_eq_sum_card_image_eq
    (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  apply Nat.card_congr
  refine
    { toFun := fun I => ⟨I.1, ?_⟩
      invFun := fun I => ⟨I.1, ?_⟩
      left_inv := fun I => by ext; rfl
      right_inv := fun I => by ext; rfl }
  · have hI : 1 ≤ Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 ≤ n := by
      simpa only [Set.mem_preimage, Finset.mem_coe, Finset.mem_Icc] using I.2
    exact ⟨(Ideal.absNorm_eq_zero_iff.not.mp (Nat.one_le_iff_ne_zero.mp hI.1)), hI.2⟩
  · have hne : Ideal.absNorm I.1 ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr I.2.1
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, I.2.2⟩

private theorem summable_ideal_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun I : Ideal (NumberField.RingOfIntegers K) =>
      Real.rpow (Ideal.absNorm I : ℝ) (-s)) := by
  classical
  let a : ℕ → ℝ := fun n => Nat.card
    {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n}
  obtain ⟨A, hA, hideal⟩ := ideal_linear_bound (K := K)
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨A, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    change (∑ k ∈ Finset.Icc 1 n, (Nat.card
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} : ℝ)) ≤
        A * Real.rpow (n : ℝ) 1
    rw [show Real.rpow (n : ℝ) 1 = (n : ℝ) ^ (1 : ℝ) from rfl,
      Real.rpow_one, ← Nat.cast_sum, coeff_sum]
    simpa only [Nat.cast_le] using hideal n (by exact_mod_cast hn)
  have hL : LSeriesSummable (fun n => (a n : ℂ)) (s : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO
      (fun _ => Nat.cast_nonneg _) (by norm_num) (by simpa using hs)
  have hnorm : Summable (fun n => ‖LSeries.term (fun n => (a n : ℂ)) (s : ℂ) n‖) :=
    summable_norm_iff.mpr hL
  have ha : Summable (fun n => a n * Real.rpow (n : ℝ) (-s)) := by
    apply hnorm.congr
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      rw [if_pos rfl]
      simp only [Nat.cast_zero]
      rw [show Real.rpow 0 (-s) = (0 : ℝ) ^ (-s) from rfl,
        Real.zero_rpow (by linarith : -s ≠ 0), mul_zero]
    · rw [if_neg hn]
      have han : 0 ≤ a n := Nat.cast_nonneg _
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg han,
        Complex.ofReal_re]
      rw [div_eq_mul_inv]
      exact congrArg (a n * ·) (Real.rpow_neg (Nat.cast_nonneg n) s).symm
  letI (n : ℕ) : Fintype
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  have hsigma : Summable (fun z : Σ n : ℕ,
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} =>
      Real.rpow (Ideal.absNorm z.2.1 : ℝ) (-s)) := by
    apply (summable_sigma_of_nonneg
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · apply ha.congr
      intro n
      rw [tsum_fintype]
      simp_rw [show ∀ I : {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = n}, Ideal.absNorm I.1 = n from fun I => I.2]
      simp [a, Nat.card_eq_fintype_card]
  exact ((Equiv.sigmaFiberEquiv (fun I : Ideal
    (NumberField.RingOfIntegers K) => Ideal.absNorm I)).summable_iff).mp hsigma

private theorem summable_prime_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun p : PrimeIdeal K => Real.rpow (PrimeIdeal.norm p : ℝ) (-s)) := by
  apply ((summable_ideal_rpow (K := K) s hs).comp_injective
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective).congr
  intro p
  rfl

/-- Blueprint Lemma 2.2, proposed declaration
`PrimeIdeal.norm_pow_inertiaDeg`: the norm in a number-field tower is the
base norm raised to the relative residue degree. -/
theorem PrimeIdeal.norm_pow_inertiaDeg
    {E : Type*} [Field E] [NumberField E] [Algebra K E]
    (q : PrimeIdeal E) (p : PrimeIdeal K)
    (hqp : q.asIdeal.LiesOver p.asIdeal) :
    PrimeIdeal.norm q = PrimeIdeal.norm p ^
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  exact (Ideal.absNorm_pow_inertiaDeg p.asIdeal q.asIdeal).symm

/-- Blueprint Lemma 2.2, proposed declaration
`PrimeIdeal.count_residueDegree_ge_two`: primes of relative residue degree at
least two have counting function `O(x^(1/2))`. -/
theorem PrimeIdeal.count_residueDegree_ge_two
    {E : Type*} [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] :
    Asymptotics.IsBigO atTop
      (fun x : ℝ =>
        (primeCounting
          {q : PrimeIdeal E |
            2 ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)} x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
  classical
  let contract : PrimeIdeal E → PrimeIdeal K := fun q =>
    ⟨q.asIdeal.under (NumberField.RingOfIntegers K), inferInstance, by
      intro h
      letI : q.asIdeal.LiesOver (⊥ : Ideal (NumberField.RingOfIntegers K)) := ⟨by simpa [h]⟩
      exact q.ne_bot (Ideal.eq_bot_of_liesOver_bot
        (NumberField.RingOfIntegers K) q.asIdeal)⟩
  obtain ⟨A, hA, hideal⟩ := ideal_linear_bound (K := K)
  rw [Asymptotics.isBigO_iff]
  refine ⟨(Module.finrank K E : ℝ) * A, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  let Q : Set (PrimeIdeal E) := {q | 2 ≤ q.asIdeal.inertiaDeg
      (NumberField.RingOfIntegers K) ∧ (PrimeIdeal.norm q : ℝ) ≤ x}
  let P : Set (PrimeIdeal K) := {p | (PrimeIdeal.norm p : ℝ) ≤ Real.sqrt x}
  have hQfin : Q.Finite := by
    obtain ⟨n : ℕ, hn⟩ := exists_nat_ge x
    apply Set.Finite.of_finite_image (f := fun q : PrimeIdeal E => q.asIdeal)
    · exact (Ideal.finite_setOf_absNorm_le
          (S := NumberField.RingOfIntegers E) n).subset (by
        rintro I ⟨q, hq, rfl⟩
        exact_mod_cast hq.2.trans hn)
    · intro p _ q _ hpq
      exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq
  have hPfin : P.Finite := by
    obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (Real.sqrt x)
    apply Set.Finite.of_finite_image (f := fun p : PrimeIdeal K => p.asIdeal)
    · exact (Ideal.finite_setOf_absNorm_le
          (S := NumberField.RingOfIntegers K) n).subset (by
        rintro I ⟨p, hp, rfl⟩
        exact_mod_cast hp.trans hn)
    · intro p _ q _ hpq
      exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq
  have hmap : ∀ q ∈ hQfin.toFinset, contract q ∈ hPfin.toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq ⊢
    have hover : q.asIdeal.LiesOver (contract q).asIdeal := ⟨rfl⟩
    have hn := PrimeIdeal.norm_pow_inertiaDeg q (contract q) hover
    have hone : 1 ≤ PrimeIdeal.norm (contract q) :=
      Nat.one_le_iff_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr (contract q).ne_bot)
    have hpows : PrimeIdeal.norm (contract q) ^ 2 ≤
        PrimeIdeal.norm (contract q) ^ q.asIdeal.inertiaDeg
          (NumberField.RingOfIntegers K) :=
      Nat.pow_le_pow_right (Nat.zero_lt_of_lt hone) hq.1
    apply (Real.le_sqrt (Nat.cast_nonneg _) (by linarith : 0 ≤ x)).2
    rw [← Nat.cast_pow]
    exact (Nat.cast_le.mpr (hpows.trans_eq hn.symm)).trans hq.2
  letI := FaithfulSMul.of_field_isFractionRing
    (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers E) K E
  letI : NoZeroSMulDivisors (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers E) := ⟨by
    intro c y h
    rw [Algebra.smul_def] at h
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hc | hy
    · exact Or.inl ((map_eq_zero_iff _
        (FaithfulSMul.algebraMap_injective _ _)).mp hc)
    · exact Or.inr hy⟩
  have hfiber : ∀ p ∈ hPfin.toFinset,
      (hQfin.toFinset.filter fun q => contract q = p).card ≤ Module.finrank K E := by
    intro p hp
    apply le_trans (Finset.card_le_card_of_injOn
      (fun q : PrimeIdeal E => q.asIdeal) ?_ ?_)
      (Ideal.card_primesOverFinset_le_finrank
        (S := NumberField.RingOfIntegers E) K E p.ne_bot)
    · intro q hq
      have hq' : q ∈ hQfin.toFinset.filter (fun q => contract q = p) := hq
      have hqe : contract q = p := (Finset.mem_filter.mp hq').2
      apply (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot _).mpr
      refine ⟨inferInstance, ⟨?_⟩⟩
      simpa [contract] using (congrArg (fun z : PrimeIdeal K => z.asIdeal) hqe).symm
    · intro q hq r hr hqr
      exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hqr
  have hcard := Finset.card_le_mul_card_image_of_maps_to hmap
    (Module.finrank K E) hfiber
  have hIfin : {a : Ideal (NumberField.RingOfIntegers K) |
      a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x}.Finite := by
    obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (Real.sqrt x)
    exact (Ideal.finite_setOf_absNorm_le
      (S := NumberField.RingOfIntegers K) n).subset (by
        intro a ha
        exact_mod_cast ha.2.trans hn)
  letI : Fintype {a : Ideal (NumberField.RingOfIntegers K) //
      a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x} := hIfin.fintype
  have hPideal : hPfin.toFinset.card ≤ Nat.card
      {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x} := by
    rw [← Set.ncard_eq_toFinset_card P hPfin]
    refine Nat.card_le_card_of_injective (f :=
      fun p : P => (⟨p.1.asIdeal, p.1.ne_bot, p.2⟩ :
        {a : Ideal (NumberField.RingOfIntegers K) //
          a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x})) ?_
    intro p q hpq
    apply Subtype.ext
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      (congrArg Subtype.val hpq)
  have hsqrt : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlin := hideal (Real.sqrt x) hsqrt
  have hnat : hQfin.toFinset.card ≤ Module.finrank K E *
      Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
        a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x} :=
    hcard.trans (Nat.mul_le_mul_left _ hPideal)
  unfold primeCounting
  change (Q.ncard : ℝ) ≤ _
  rw [Set.ncard_eq_toFinset_card Q hQfin]
  calc
    (hQfin.toFinset.card : ℝ) ≤ (Module.finrank K E : ℝ) *
        Nat.card {a : Ideal (NumberField.RingOfIntegers K) //
          a ≠ 0 ∧ (Ideal.absNorm a : ℝ) ≤ Real.sqrt x} := by exact_mod_cast hnat
    _ ≤ (Module.finrank K E : ℝ) * (A * Real.sqrt x) := by gcongr
    _ = (Module.finrank K E : ℝ) * A * Real.sqrt x := by ring

/-- Blueprint Lemma 2.3 (`finite_primeSet_hasPrimeDensity_zero`). -/
theorem finite_primeSet_hasPrimeDensity_zero
    {S : Set (PrimeIdeal K)} (hS : S.Finite) :
    HasPrimeDensity S 0 := by
  letI := hS.fintype
  have hbound (x : ℝ) : primeCounting S x ≤ Nat.card S := by
    unfold primeCounting
    apply Nat.card_le_card_of_injective
      (fun p : {p : PrimeIdeal K // p ∈ S ∧ (PrimeIdeal.norm p : ℝ) ≤ x } =>
        (⟨p, p.2.1⟩ : S))
    intro a b hab
    exact Subtype.ext (congrArg (fun z : S => (z : PrimeIdeal K)) hab)
  unfold HasPrimeDensity
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ x / Real.log x :=
    tendsto_x_div_log_atTop.eventually (eventually_ge_atTop 0)
  refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (Nat.card S : ℝ)) atTop (𝓝 (Nat.card S : ℝ))).div_atTop
      tendsto_x_div_log_atTop)
  · filter_upwards [hnonneg] with x hx
    exact div_nonneg (Nat.cast_nonneg _) hx
  filter_upwards [hnonneg] with x hx
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hbound x)) hx

/-- Blueprint Lemma 2.3 (`finite_primeSet_hasDirichletDensity_zero`). -/
theorem finite_primeSet_hasDirichletDensity_zero
    {S : Set (PrimeIdeal K)} (hS : S.Finite) :
    HasDirichletDensity S 0 := by
  classical
  let t := hS.toFinset
  have hsum (s : ℝ) : dirichletPrimeSum S s =
      ∑ p ∈ t, if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0 := by
    unfold dirichletPrimeSum
    rw [tsum_eq_sum]
    intro p hp
    simp only [t, Set.Finite.mem_toFinset] at hp
    simp [hp]
  have hterm (p : PrimeIdeal K) : Tendsto
      (fun s : ℝ => if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0)
      (𝓝[>] (1 : ℝ))
      (𝓝 (if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-1) else 0)) := by
    split_ifs with hp
    · have hne : (PrimeIdeal.norm p : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr (IsDedekindDomain.HeightOneSpectrum.ne_bot p))
      convert ((Real.continuousAt_const_rpow hne).comp
        (continuousAt_id.neg : ContinuousAt (fun s : ℝ => -s) 1)).tendsto
        |>.mono_left nhdsWithin_le_nhds using 1 <;> simp [Function.comp_def]
    · exact tendsto_const_nhds
  have hnum : Tendsto (fun s : ℝ => dirichletPrimeSum S s)
      (𝓝[>] (1 : ℝ))
      (𝓝 (∑ p ∈ t, if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-1) else 0)) := by
    apply (tendsto_finset_sum t fun p _ => hterm p).congr'
    filter_upwards with s
    simp_rw [hsum s]
  unfold HasDirichletDensity
  exact hnum.div_atTop tendsto_dirichletNormalizer_atTop

/-- Blueprint Lemma 2.3 (`sqrt_bound_hasPrimeDensity_zero`): an
`O(x^(1/2))` counting bound is negligible for PNT density. -/
theorem sqrt_bound_hasPrimeDensity_zero (S : Set (PrimeIdeal K))
    (hS : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting S x : ℝ)) (fun x : ℝ => Real.sqrt x)) :
    HasPrimeDensity S 0 := by
  have hlog : (fun x : ℝ => Real.log x) =o[atTop]
      fun x => Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hprod :
      (fun x : ℝ => (primeCounting S x : ℝ) * Real.log x) =o[atTop]
        fun x => Real.sqrt x * Real.sqrt x := hS.mul_isLittleO hlog
  have hsqrt :
      (fun x : ℝ => (primeCounting S x : ℝ) * Real.log x) =o[atTop]
        fun x => x := by
    apply hprod.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.mul_self_sqrt hx]
  unfold HasPrimeDensity
  apply hsqrt.tendsto_div_nhds_zero.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp

/-- Blueprint Lemma 2.3 (`sqrt_bound_hasDirichletDensity_zero`): an
`O(x^(1/2))` counting bound is negligible for Dirichlet density. -/
theorem sqrt_bound_hasDirichletDensity_zero (S : Set (PrimeIdeal K))
    (hS : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting S x : ℝ)) (fun x : ℝ => Real.sqrt x)) :
    HasDirichletDensity S 0 := by
  classical
  let a : ℕ → ℝ := fun n => Nat.card
    {p : S // PrimeIdeal.norm p.1 = n}
  have hfiber (k : ℕ) : {p : S | PrimeIdeal.norm p.1 = k}.Finite := by
    apply Set.Finite.of_finite_image (f := fun p : S => p.1.asIdeal)
    · exact (Ideal.finite_setOf_absNorm_eq k).subset (by
        rintro I ⟨p, hp, hpI⟩
        rw [← hpI]
        exact hp)
    · intro p _ q _ hpq
      apply Subtype.ext
      exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq
  have hcoeff (n : ℕ) :
      ∑ k ∈ Finset.Icc 1 n, a k = primeCounting S n := by
    have hcoeffN : ∑ k ∈ Finset.Icc 1 n,
        Nat.card {p : S // PrimeIdeal.norm p.1 = k} = primeCounting S n := by
      rw [← Finset.card_preimage_eq_sum_card_image_eq
        (f := fun p : S => PrimeIdeal.norm p.1) (fun k _ => hfiber k)]
      apply Nat.card_congr
      refine
        { toFun := fun p => ⟨p.1.1, p.1.2, by
            exact_mod_cast (Finset.mem_Icc.mp p.2).2⟩
          invFun := fun p => ⟨⟨p.1, p.2.1⟩, by
            change PrimeIdeal.norm p.1 ∈ Finset.Icc 1 n
            apply Finset.mem_Icc.mpr
            refine ⟨Nat.one_le_iff_ne_zero.mpr
              (Ideal.absNorm_eq_zero_iff.not.mpr p.1.ne_bot), ?_⟩
            exact_mod_cast p.2.2⟩
          left_inv := fun p => by ext <;> rfl
          right_inv := fun p => by ext <;> rfl }
    simpa only [a, Nat.cast_sum] using congrArg (fun m : ℕ => (m : ℝ)) hcoeffN
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff] at hS ⊢
    obtain ⟨C, hC⟩ := hS
    refine ⟨C, ?_⟩
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hC] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      hcoeff]
    have hcountnonneg : 0 ≤ (primeCounting S (n : ℝ) : ℝ) := Nat.cast_nonneg _
    calc
      (primeCounting S (n : ℝ) : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hcountnonneg,
          abs_of_nonneg (Real.sqrt_nonneg _)] using hn
      _ = C * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]
  have hL : LSeriesSummable (fun n => a n) ((3 / 4 : ℝ) : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO
      (fun _ => Nat.cast_nonneg _) (by norm_num) (by norm_num)
  have ha : Summable (fun n => a n * Real.rpow (n : ℝ) (-(3 / 4 : ℝ))) := by
    apply (summable_norm_iff.mpr hL).congr
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      rw [if_pos rfl]
      simp only [Nat.cast_zero]
      rw [show Real.rpow 0 (-(3 / 4 : ℝ)) = (0 : ℝ) ^ (-(3 / 4 : ℝ)) from rfl,
        Real.zero_rpow (by norm_num), mul_zero]
    · rw [if_neg hn]
      have han : 0 ≤ a n := Nat.cast_nonneg _
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg han,
        Complex.ofReal_re]
      rw [div_eq_mul_inv]
      exact congrArg (a n * ·) (Real.rpow_neg (Nat.cast_nonneg n) _).symm
  letI (n : ℕ) : Fintype {p : S // PrimeIdeal.norm p.1 = n} :=
    (hfiber n).fintype
  have hsum : Summable (fun z : Σ n : ℕ,
      {p : S // PrimeIdeal.norm p.1 = n} =>
      Real.rpow (PrimeIdeal.norm z.2.1.1 : ℝ) (-(3 / 4 : ℝ))) := by
    apply (summable_sigma_of_nonneg
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · apply ha.congr
      intro n
      rw [tsum_fintype]
      simp_rw [show ∀ p : {p : S // PrimeIdeal.norm p.1 = n},
        PrimeIdeal.norm p.1.1 = n from fun p => p.2]
      simp [a, Nat.card_eq_fintype_card]
  have hbaseS : Summable (fun p : S =>
      Real.rpow (PrimeIdeal.norm p.1 : ℝ) (-(3 / 4 : ℝ))) := by
    exact ((Equiv.sigmaFiberEquiv (fun p : S => PrimeIdeal.norm p.1)).summable_iff).mp hsum
  have hbase : Summable (fun p : PrimeIdeal K =>
      if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-(3 / 4 : ℝ)) else 0) := by
    have hind := (summable_subtype_iff_indicator (s := S)
      (f := fun p : PrimeIdeal K =>
        Real.rpow (PrimeIdeal.norm p : ℝ) (-(3 / 4 : ℝ)))).mp hbaseS
    apply hind.congr
    intro p
    by_cases hp : p ∈ S <;> simp [Set.indicator, hp]
  have hbound (s : ℝ) (hs : 1 < s) :
      0 ≤ dirichletPrimeSum S s ∧
        dirichletPrimeSum S s ≤ dirichletPrimeSum S (3 / 4) := by
    have hsumm : Summable (fun p : PrimeIdeal K =>
        if p ∈ S then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0) := by
      apply (summable_prime_rpow (K := K) s hs).of_nonneg_of_le
      · intro p
        split_ifs with hp
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · exact le_rfl
      · intro p
        split_ifs
        · exact le_rfl
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    constructor
    · unfold dirichletPrimeSum
      exact tsum_nonneg fun p => by
        split_ifs with hp
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · exact le_rfl
    · unfold dirichletPrimeSum
      apply hsumm.tsum_le_tsum _ hbase
      intro p
      split_ifs with hp
      · apply Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast
            (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)))
        linarith
      · exact le_rfl
  unfold HasDirichletDensity
  have htop := tendsto_dirichletNormalizer_atTop
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < dirichletNormalizer s :=
    htop.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' ?_ ?_
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => dirichletPrimeSum S (3 / 4))
      (𝓝[>] (1 : ℝ)) (𝓝 _)).div_atTop htop)
  · filter_upwards [self_mem_nhdsWithin, hpos] with s hs hp
    exact div_nonneg (hbound s hs).1 hp.le
  · filter_upwards [self_mem_nhdsWithin, hpos] with s hs hp
    exact div_le_div_of_nonneg_right (hbound s hs).2 hp.le

private theorem primeCountingSet_finite (S : Set (PrimeIdeal K)) (x : ℝ) :
    {p : PrimeIdeal K | p ∈ S ∧ (PrimeIdeal.norm p : ℝ) ≤ x}.Finite := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge x
  refine Set.Finite.of_finite_image
    (f := fun p : PrimeIdeal K => p.asIdeal) ?_ ?_
  · apply (Ideal.finite_setOf_absNorm_le
      (S := NumberField.RingOfIntegers K) n).subset
    rintro I ⟨p, hp, rfl⟩
    change Ideal.absNorm p.asIdeal ≤ n
    exact_mod_cast hp.2.trans hn
  · intro p _ q _ hpq
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq

private theorem primeCounting_le_add_of_subset
    {A B C : Set (PrimeIdeal K)} (h : A ⊆ B ∪ C) (x : ℝ) :
    primeCounting A x ≤ primeCounting B x + primeCounting C x := by
  unfold primeCounting
  let AX := {p : PrimeIdeal K | p ∈ A ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  let BX := {p : PrimeIdeal K | p ∈ B ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  let CX := {p : PrimeIdeal K | p ∈ C ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  change AX.ncard ≤ BX.ncard + CX.ncard
  apply le_trans (Set.ncard_le_ncard (t := BX ∪ CX) ?_
    ((primeCountingSet_finite B x).union (primeCountingSet_finite C x)))
  · exact Set.ncard_union_le BX CX
  · intro p hp
    rcases h hp.1 with hpB | hpC
    · exact Or.inl ⟨hpB, hp.2⟩
    · exact Or.inr ⟨hpC, hp.2⟩

/-- Blueprint §2/§9 finite-union bookkeeping (`hasPrimeDensity_finite_iUnion`). -/
theorem hasPrimeDensity_finite_iUnion
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K)) (δ : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ S)
    (hδ : ∀ i, HasPrimeDensity (S i) (δ i)) :
    HasPrimeDensity (⋃ i, S i) (∑ i, δ i) := by
  have hcount (x : ℝ) :
      primeCounting (⋃ i, S i) x = ∑ i, primeCounting (S i) x := by
    unfold primeCounting
    let A : ι → Set (PrimeIdeal K) := fun i =>
      {p | p ∈ S i ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
    have hAfin : ∀ i, (A i).Finite := fun i => primeCountingSet_finite (S i) x
    have hAdisj : Pairwise (Function.onFun Disjoint A) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro p hpi hpj
      exact Set.disjoint_left.1
        (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hpi.1 hpj.1
    change Nat.card {p // p ∈ (⋃ i, S i) ∧
      (PrimeIdeal.norm p : ℝ) ≤ x} = _
    have hunion : {p : PrimeIdeal K | p ∈ (⋃ i, S i) ∧
        (PrimeIdeal.norm p : ℝ) ≤ x} = ⋃ i, A i := by
      ext p
      simp [A]
    change ({p : PrimeIdeal K | p ∈ (⋃ i, S i) ∧
      (PrimeIdeal.norm p : ℝ) ≤ x}).ncard = ∑ i, (A i).ncard
    rw [hunion, Set.ncard_iUnion_of_finite hAfin hAdisj]
    simp only [finsum_eq_sum_of_fintype]
  unfold HasPrimeDensity at hδ ⊢
  convert tendsto_finsetSum Finset.univ (fun i _ => hδ i) using 1
  funext x
  rw [hcount, Nat.cast_sum, Finset.sum_div]

/-- Blueprint §2/§9 finite-union bookkeeping
(`hasDirichletDensity_finite_iUnion`). -/
theorem hasDirichletDensity_finite_iUnion
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K)) (δ : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ S)
    (hδ : ∀ i, HasDirichletDensity (S i) (δ i)) :
    HasDirichletDensity (⋃ i, S i) (∑ i, δ i) := by
  classical
  unfold HasDirichletDensity at hδ ⊢
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => hδ i)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← Finset.sum_div]
  congr 1
  unfold dirichletPrimeSum
  have hbase := summable_prime_rpow (K := K) s hs
  have hf : ∀ i ∈ (Finset.univ : Finset ι), Summable (fun p : PrimeIdeal K =>
      if p ∈ S i then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0) := by
    intro i hi
    apply hbase.of_nonneg_of_le
    · intro p
      split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · intro p
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [← Summable.tsum_finsetSum hf]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ ⋃ i, S i
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    rw [if_pos (Set.mem_iUnion_of_mem i hi), Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j hj hji
      rw [if_neg]
      intro hjmem
      exact Set.disjoint_left.1
        (hdisj (Set.mem_univ i) (Set.mem_univ j) (Ne.symm hji)) hi hjmem
    · simp
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    intro hmem
    exact hp (Set.mem_iUnion_of_mem i hmem)

/-- Blueprint §2/§9 negligible-set replacement for PNT density. -/
theorem HasPrimeDensity.congr_of_symmetricDifference_zero
    {S T : Set (PrimeIdeal K)} {δ : ℝ}
    (hS : HasPrimeDensity S δ)
    (hST : HasPrimeDensity (symmetricDifference S T) 0) :
    HasPrimeDensity T δ := by
  let D := symmetricDifference S T
  have hTD : T ⊆ S ∪ D := by
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl hs
    · exact Or.inr (Or.inr ⟨hp, hs⟩)
  have hSD : S ⊆ T ∪ D := by
    intro p hp
    by_cases ht : p ∈ T
    · exact Or.inl ht
    · exact Or.inr (Or.inl ⟨hp, ht⟩)
  have hdiff : ∀ x : ℝ,
      |(primeCounting T x : ℝ) - (primeCounting S x : ℝ)| ≤
        (primeCounting D x : ℝ) := by
    intro x
    have h₁ : (primeCounting T x : ℝ) ≤
        primeCounting S x + primeCounting D x := by
      exact_mod_cast primeCounting_le_add_of_subset hTD x
    have h₂ : (primeCounting S x : ℝ) ≤
        primeCounting T x + primeCounting D x := by
      exact_mod_cast primeCounting_le_add_of_subset hSD x
    rw [abs_le]
    constructor <;> linarith
  have hden : ∀ᶠ x : ℝ in atTop, 0 < x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
  have hz : Tendsto (fun x : ℝ =>
      |((primeCounting T x : ℝ) / (x / Real.log x)) -
        ((primeCounting S x : ℝ) / (x / Real.log x))|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _)
      (show ∀ᶠ x : ℝ in atTop,
        |(primeCounting T x : ℝ) / (x / Real.log x) -
          (primeCounting S x : ℝ) / (x / Real.log x)| ≤
          (primeCounting D x : ℝ) / (x / Real.log x) by
        filter_upwards [hden] with x hx
        rw [← sub_div, abs_div, abs_of_pos hx]
        exact div_le_div_of_nonneg_right (hdiff x) hx.le)
    exact hST
  unfold HasPrimeDensity at hS ⊢
  have hzero : Tendsto (fun x : ℝ =>
      (primeCounting T x : ℝ) / (x / Real.log x) -
        (primeCounting S x : ℝ) / (x / Real.log x)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    convert hz using 1 <;> simp [Function.comp_def]
  simpa only [sub_add_cancel, zero_add] using hzero.add hS

/-- Blueprint §2/§9 negligible-set replacement for Dirichlet density. -/
theorem HasDirichletDensity.congr_of_symmetricDifference_zero
    {S T : Set (PrimeIdeal K)} {δ : ℝ}
    (hS : HasDirichletDensity S δ)
    (hST : HasDirichletDensity (symmetricDifference S T) 0) :
    HasDirichletDensity T δ := by
  classical
  let D := symmetricDifference S T
  have hTD : T ⊆ S ∪ D := by
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl hs
    · exact Or.inr (Or.inr ⟨hp, hs⟩)
  have hSD : S ⊆ T ∪ D := by
    intro p hp
    by_cases ht : p ∈ T
    · exact Or.inl ht
    · exact Or.inr (Or.inl ⟨hp, ht⟩)
  have hsum_le {A B C : Set (PrimeIdeal K)} (h : A ⊆ B ∪ C)
      (s : ℝ) (hs : 1 < s) :
      dirichletPrimeSum A s ≤ dirichletPrimeSum B s + dirichletPrimeSum C s := by
    unfold dirichletPrimeSum
    let f : Set (PrimeIdeal K) → PrimeIdeal K → ℝ := fun U p =>
      if p ∈ U then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0
    have hbase := summable_prime_rpow (K := K) s hs
    have hsum (U : Set (PrimeIdeal K)) : Summable (f U) := by
      apply hbase.of_nonneg_of_le
      · intro p
        simp only [f]
        split_ifs
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · exact le_rfl
      · intro p
        simp only [f]
        split_ifs
        · exact le_rfl
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    change (∑' p, f A p) ≤ (∑' p, f B p) + ∑' p, f C p
    rw [← (hsum B).tsum_add (hsum C)]
    apply Summable.tsum_le_tsum _ (hsum A) ((hsum B).add (hsum C))
    intro p
    simp only [f]
    have hterm : 0 ≤ Real.rpow (PrimeIdeal.norm p : ℝ) (-s) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hite (U : Set (PrimeIdeal K)) :
        0 ≤ if p ∈ U then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0 := by
      split_ifs
      · exact hterm
      · exact le_rfl
    by_cases hp : p ∈ A
    · rw [if_pos hp]
      rcases h hp with hpB | hpC
      · rw [if_pos hpB]
        exact le_add_of_nonneg_right (hite C)
      · rw [if_pos hpC]
        exact le_add_of_nonneg_left (hite B)
    · rw [if_neg hp]
      exact add_nonneg (hite B) (hite C)
  have hdiff : ∀ s : ℝ, 1 < s →
      |dirichletPrimeSum T s - dirichletPrimeSum S s| ≤ dirichletPrimeSum D s := by
    intro s hs
    have h₁ := hsum_le hTD s hs
    have h₂ := hsum_le hSD s hs
    rw [abs_le]
    constructor <;> linarith
  have hlt2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have hden : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < dirichletNormalizer s := by
    filter_upwards [self_mem_nhdsWithin, hlt2] with s hs hs2
    unfold dirichletNormalizer
    apply Real.log_pos
    rw [one_lt_div₀ (sub_pos.mpr hs)]
    linarith
  have hz : Tendsto (fun s : ℝ =>
      |dirichletPrimeSum T s / dirichletNormalizer s -
        dirichletPrimeSum S s / dirichletNormalizer s|) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
      (show ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
        |dirichletPrimeSum T s / dirichletNormalizer s -
          dirichletPrimeSum S s / dirichletNormalizer s| ≤
          dirichletPrimeSum D s / dirichletNormalizer s by
        filter_upwards [hden, self_mem_nhdsWithin] with s hpos hs
        rw [← sub_div, abs_div, abs_of_pos hpos]
        exact div_le_div_of_nonneg_right (hdiff s hs) hpos.le)
    exact hST
  unfold HasDirichletDensity at hS ⊢
  have hzero : Tendsto (fun s : ℝ =>
      dirichletPrimeSum T s / dirichletNormalizer s -
        dirichletPrimeSum S s / dirichletNormalizer s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    convert hz using 1 <;> simp [Function.comp_def]
  simpa only [sub_add_cancel, zero_add] using hzero.add hS

private theorem primeCounting_iUnion_eq_sum
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K))
    (hdisj : Set.PairwiseDisjoint Set.univ S) (x : ℝ) :
    primeCounting (⋃ i, S i) x = ∑ i, primeCounting (S i) x := by
  unfold primeCounting
  let A : ι → Set (PrimeIdeal K) := fun i =>
    {p | p ∈ S i ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  have hAfin : ∀ i, (A i).Finite := fun i => primeCountingSet_finite (S i) x
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro p hpi hpj
    exact Set.disjoint_left.1
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hpi.1 hpj.1
  have hunion : {p : PrimeIdeal K | p ∈ (⋃ i, S i) ∧
      (PrimeIdeal.norm p : ℝ) ≤ x} = ⋃ i, A i := by
    ext p
    simp [A]
  change ({p : PrimeIdeal K | p ∈ (⋃ i, S i) ∧
    (PrimeIdeal.norm p : ℝ) ≤ x}).ncard = ∑ i, (A i).ncard
  rw [hunion, Set.ncard_iUnion_of_finite hAfin hAdisj]
  simp only [finsum_eq_sum_of_fintype]

private theorem dirichletPrimeSum_iUnion_eq_sum
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K))
    (hdisj : Set.PairwiseDisjoint Set.univ S) (s : ℝ) (hs : 1 < s) :
    dirichletPrimeSum (⋃ i, S i) s = ∑ i, dirichletPrimeSum (S i) s := by
  classical
  unfold dirichletPrimeSum
  have hbase := summable_prime_rpow (K := K) s hs
  have hf : ∀ i ∈ (Finset.univ : Finset ι), Summable (fun p : PrimeIdeal K =>
      if p ∈ S i then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0) := by
    intro i hi
    apply hbase.of_nonneg_of_le
    · intro p
      split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · intro p
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [← Summable.tsum_finsetSum hf]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ ⋃ i, S i
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨i, hi⟩ := hp
    rw [if_pos (Set.mem_iUnion_of_mem i hi), Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro j hj hji
      rw [if_neg]
      intro hjmem
      exact Set.disjoint_left.1
        (hdisj (Set.mem_univ i) (Set.mem_univ j) (Ne.symm hji)) hi hjmem
    · simp
  · rw [if_neg hp]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    intro hmem
    exact hp (Set.mem_iUnion_of_mem i hmem)

private theorem finite_liminf_squeeze
    {ι β : Type*} [Fintype ι] (l : Filter β) [NeBot l]
    (f : ι → β → ℝ) (δ : ι → ℝ)
    (hnonneg : ∀ i, ∀ᶠ x in l, 0 ≤ f i x)
    (hsum : Tendsto (fun x => ∑ i, f i x) l (𝓝 (∑ i, δ i)))
    (hlower : ∀ i, δ i ≤ liminf (f i) l) :
    ∀ i, Tendsto (f i) l (𝓝 (δ i)) := by
  classical
  intro i
  have hbelow (j : ι) : l.IsBoundedUnder (· ≥ ·) (f j) := ⟨0, hnonneg j⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.eventually_lt_of_lt_liminf (ha.trans_le (hlower i)) (hbelow i)
  · intro b hb
    let e : ℝ := (b - δ i) / ((Fintype.card ι : ℝ) + 1)
    have he : 0 < e := div_pos (sub_pos.mpr hb) (by positivity)
    have hlo (j : ι) : ∀ᶠ x in l, δ j - e < f j x :=
      Filter.eventually_lt_of_lt_liminf
        ((sub_lt_self _ he).trans_le (hlower j)) (hbelow j)
    have hall : ∀ᶠ x in l, ∀ j, δ j - e < f j x :=
      Filter.eventually_all.2 hlo
    have htot : ∀ᶠ x in l, (∑ j, f j x) < (∑ j, δ j) + e :=
      hsum (Iio_mem_nhds (lt_add_of_pos_right _ he))
    filter_upwards [hall, htot] with x hx htx
    have hcomp : ∑ j ∈ Finset.univ.erase i, (δ j - e) ≤
        ∑ j ∈ Finset.univ.erase i, f j x :=
      Finset.sum_le_sum fun j hj => (hx j).le
    have hδsplit : ∑ j, δ j = δ i + ∑ j ∈ Finset.univ.erase i, δ j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring
    have hfsplit : ∑ j, f j x = f i x + ∑ j ∈ Finset.univ.erase i, f j x := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring
    have hcard : ((Finset.univ.erase i).card : ℝ) + 1 = Fintype.card ι := by
      exact_mod_cast Finset.card_erase_add_one (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hcomp
    rw [hδsplit, hfsplit] at htx
    have heq : e * ((Fintype.card ι : ℝ) + 1) = b - δ i := by
      dsimp [e]
      field_simp
    nlinarith [hcard, heq]

/-- Blueprint Lemma 2.4 (`finite_partition_squeeze`), in the PNT-density
normalization. -/
theorem finite_partition_squeeze
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K)) (δ : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ S)
    (hcover : HasPrimeDensity
      (symmetricDifference (⋃ i, S i) (Set.univ : Set (PrimeIdeal K))) 0)
    (hall : HasPrimeDensity (Set.univ : Set (PrimeIdeal K)) 1)
    (hlower : ∀ i, δ i ≤ lowerPrimeDensity (S i))
    (hsum : ∑ i, δ i = 1) :
    ∀ i, HasPrimeDensity (S i) (δ i) := by
  classical
  let U : Set (PrimeIdeal K) := ⋃ i, S i
  have hsymm : symmetricDifference (Set.univ : Set (PrimeIdeal K)) U =
      symmetricDifference U Set.univ := by
    ext p
    simp [symmetricDifference]
  have hU : HasPrimeDensity U 1 := by
    apply hall.congr_of_symmetricDifference_zero
    rw [hsymm]
    exact hcover
  let f : ι → ℝ → ℝ := fun i x =>
    (primeCounting (S i) x : ℝ) / (x / Real.log x)
  have hden : ∀ᶠ x : ℝ in atTop, 0 < x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
  have hnonneg : ∀ i, ∀ᶠ x : ℝ in atTop, 0 ≤ f i x := by
    intro i
    filter_upwards [hden] with x hx
    exact div_nonneg (Nat.cast_nonneg _) hx.le
  have ht : Tendsto (fun x : ℝ => ∑ i, f i x) atTop (𝓝 (∑ i, δ i)) := by
    rw [hsum]
    unfold HasPrimeDensity at hU
    apply hU.congr'
    filter_upwards with x
    simp only [f]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      ← primeCounting_iUnion_eq_sum S hdisj x]
  have hl : ∀ i, δ i ≤ liminf (f i) atTop := by
    exact hlower
  exact finite_liminf_squeeze atTop f δ hnonneg ht hl

/-- Blueprint Lemma 2.4 and §9 (`finite_partition_squeeze_dirichlet`), the
identical squeeze for lower/upper Dirichlet density. -/
theorem finite_partition_squeeze_dirichlet
    {ι : Type*} [Fintype ι] (S : ι → Set (PrimeIdeal K)) (δ : ι → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ S)
    (hcover : HasDirichletDensity
      (symmetricDifference (⋃ i, S i) (Set.univ : Set (PrimeIdeal K))) 0)
    (hall : HasDirichletDensity (Set.univ : Set (PrimeIdeal K)) 1)
    (hlower : ∀ i, δ i ≤ lowerDirichletDensity (S i))
    (hsum : ∑ i, δ i = 1) :
    ∀ i, HasDirichletDensity (S i) (δ i) := by
  classical
  let U : Set (PrimeIdeal K) := ⋃ i, S i
  have hsymm : symmetricDifference (Set.univ : Set (PrimeIdeal K)) U =
      symmetricDifference U Set.univ := by
    ext p
    simp [symmetricDifference]
  have hU : HasDirichletDensity U 1 := by
    apply hall.congr_of_symmetricDifference_zero
    rw [hsymm]
    exact hcover
  let f : ι → ℝ → ℝ := fun i s =>
    dirichletPrimeSum (S i) s / dirichletNormalizer s
  have hlt2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have hden : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < dirichletNormalizer s := by
    filter_upwards [self_mem_nhdsWithin, hlt2] with s hs hs2
    unfold dirichletNormalizer
    apply Real.log_pos
    rw [one_lt_div₀ (sub_pos.mpr hs)]
    linarith
  have hnonneg : ∀ i, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 ≤ f i s := by
    intro i
    filter_upwards [hden] with s hs
    have hnum : 0 ≤ dirichletPrimeSum (S i) s := by
      unfold dirichletPrimeSum
      apply tsum_nonneg
      intro p
      split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    exact div_nonneg hnum hs.le
  have ht : Tendsto (fun s : ℝ => ∑ i, f i s) (𝓝[>] (1 : ℝ))
      (𝓝 (∑ i, δ i)) := by
    rw [hsum]
    unfold HasDirichletDensity at hU
    apply hU.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [f]
    rw [← Finset.sum_div, ← dirichletPrimeSum_iUnion_eq_sum S hdisj s hs]
  have hl : ∀ i, δ i ≤ liminf (f i) (𝓝[>] (1 : ℝ)) := by
    exact hlower
  exact finite_liminf_squeeze (𝓝[>] (1 : ℝ)) f δ hnonneg ht hl

end NU.Chebotarev
