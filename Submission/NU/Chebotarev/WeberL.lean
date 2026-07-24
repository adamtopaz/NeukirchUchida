import Submission.NU.Chebotarev.RayClassAsymptotics

/-!
# M6a. Partial zeta functions and Weber L-series

Blueprint §5.3--§5.4 and §9. Characters are `MulChar`-style unit-valued
multiplicative characters, and all Euler products omit the finite modulus
explicitly, as required by §10.5(4)--(5).
-/

open Filter Topology MeasureTheory Asymptotics
open scoped BigOperators nonZeroDivisors

namespace NU.Chebotarev

variable {K : Type*} [Field K] [NumberField K]

/-- Finite-order ray-class characters, represented by Mathlib's `MulChar`
interface and coerced to `ℂ` only in analytic definitions (blueprint §10.5(4)). -/
abbrev RayClassCharacter (m : RayModulus K) := MulChar (RayClassGroup m) ℂ

/-- Blueprint §5.3, proposed declaration `rayClassPartialZeta`: the partial
zeta series of a ray class, initially used on `re(s) > 1`. -/
noncomputable def rayClassPartialZeta (m : RayModulus K)
    (c : RayClassGroup m) (s : ℂ) : ℂ := by
  classical
  exact ∑' a : Ideal (NumberField.RingOfIntegers K),
    if a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c then
      Complex.cpow (Ideal.absNorm a : ℂ) (-s)
    else 0

/-- Evaluation of a ray-class character on a nonzero integral ideal. The
relational class predicate makes this zero until primeness-to-the-modulus and
uniqueness are supplied by a theorem. -/
noncomputable def rayClassCharacterValue (m : RayModulus K)
    (ψ : RayClassCharacter m) (a : Ideal (NumberField.RingOfIntegers K)) : ℂ := by
  classical
  exact ∑' c : RayClassGroup m,
    if RayClassGroup.IsClassOfIdeal m a c then ψ c else 0

/-- Blueprint §5.4, proposed declaration `weberLSeries`: the ray-character
series `Σ_c ψ(c) ζ_c(s)`. -/
noncomputable def weberLSeries (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) : ℂ :=
  ∑' c : RayClassGroup m, ψ c * rayClassPartialZeta m c s

/-- The explicitly incomplete Euler product for a Weber L-series, with all
prime factors dividing `m₀` removed (blueprint §5.4 and §10.5(5)). -/
noncomputable def weberLEulerProduct (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) : ℂ := by
  classical
  exact ∏' p : PrimeIdeal K,
    if p.asIdeal ∣ m.finite then 1 else
      (1 - rayClassCharacterValue m ψ p.asIdeal *
        Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹

/-- The incomplete Dedekind zeta series with finite Euler factors at primes
dividing `m₀` removed. -/
noncomputable def incompleteDedekindZeta (m : RayModulus K) (s : ℂ) : ℂ := by
  classical
  exact ∑' a : Ideal (NumberField.RingOfIntegers K),
    if a ≠ 0 ∧ IsCoprime a m.finite then
      Complex.cpow (Ideal.absNorm a : ℂ) (-s)
    else 0

/-- The corresponding explicitly incomplete Dedekind Euler product. -/
noncomputable def incompleteDedekindZetaEulerProduct
    (m : RayModulus K) (s : ℂ) : ℂ := by
  classical
  exact ∏' p : PrimeIdeal K,
    if p.asIdeal ∣ m.finite then 1 else
      (1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹

/-- The absolutely convergent logarithmic Euler series `ell(s,ψ)` used in the
Dirichlet-density-only argument of blueprint §9. -/
noncomputable def weberLogEulerSeries (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) : ℂ := by
  classical
  exact ∑' p : PrimeIdeal K,
    if p.asIdeal ∣ m.finite then 0 else
      ∑' r : ℕ,
        rayClassCharacterValue m ψ p.asIdeal ^ (r + 1) /
          ((r + 1 : ℂ) *
            Complex.cpow (PrimeIdeal.norm p : ℂ) ((r + 1 : ℂ) * s))

local notation "O" => NumberField.RingOfIntegers K

private noncomputable def weberPrivateCoeff (m : RayModulus K)
    (c : RayClassGroup m) (n : ℕ) : ℕ :=
  Nat.card {a : {a : Ideal O // a ≠ 0 ∧ IsCoprime a m.finite ∧
    RayClassGroup.IsClassOfIdeal m a c} // Ideal.absNorm a.1 = n}

private theorem weberPrivateCoeff_sum (m : RayModulus K) (c : RayClassGroup m) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, weberPrivateCoeff m c k = rayIdealCounting m c n := by
  classical
  change ∑ k ∈ Finset.Icc 1 n, Nat.card
      {a : {a : Ideal O // a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c} // Ideal.absNorm a.1 = k} = _
  rw [← Finset.card_preimage_eq_sum_card_image_eq]
  · apply Nat.card_congr
    refine
      { toFun := fun a => ⟨a.1.1, a.1.2.1, a.1.2.2.1, a.1.2.2.2, ?_⟩
        invFun := fun a => ⟨⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1⟩, ?_⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    · exact_mod_cast (Finset.mem_Icc.mp a.2).2
    · have hne : Ideal.absNorm a.1 ≠ 0 :=
        Ideal.absNorm_eq_zero_iff.not.mpr a.2.1
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, by exact_mod_cast a.2.2.2.2⟩
  · intro k hk
    exact Set.Finite.preimage
      (s := {a : Ideal O | Ideal.absNorm a = k})
      (f := fun a : {a : Ideal O // a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c} => a.1)
      Subtype.val_injective.injOn (Ideal.finite_setOf_absNorm_eq k)

private noncomputable def weberPrivateErrorCoeff (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (n : ℕ) : ℂ := (weberPrivateCoeff m c n : ℂ) - ρ

private theorem weberPrivateError_partial_sum (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k =
      (rayIdealCounting m c n : ℂ) - ρ * n := by
  simp_rw [weberPrivateErrorCoeff]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Nat.cast_sum, Nat.card_Icc, weberPrivateCoeff_sum]
  simp only [Nat.add_sub_cancel]
  ring

private theorem weberPrivateError_bigO (m : RayModulus K) (c : RayClassGroup m)
    (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ)))) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  have hnat := hO.comp_tendsto tendsto_natCast_atTop_atTop
  apply Asymptotics.IsBigO.of_norm_left
  apply (hnat.norm_left.congr_left fun n => ?_).congr_right fun n => rfl
  rw [Function.comp_apply, weberPrivateError_partial_sum, ← Complex.norm_real]
  congr 1
  norm_cast

private theorem weberPrivateCoeff_LSeriesSummable (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (weberPrivateCoeff m c n : ℂ)) s := by
  have hq : 1 - 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by positivity
    linarith
  have hpow : Asymptotics.IsBigO atTop
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ)))
      (fun n : ℕ => Real.rpow (n : ℝ) 1) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnon1 : 0 ≤ Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnon2 : 0 ≤ Real.rpow (n : ℝ) 1 := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [abs_of_nonneg hnon1, abs_of_nonneg hnon2]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hq
  have herr := (hO.comp_tendsto tendsto_natCast_atTop_atTop).trans hpow
  have hlin : Asymptotics.IsBigO atTop
      (fun n : ℕ => ρ * (n : ℝ)) (fun n : ℕ => Real.rpow (n : ℝ) 1) := by
    apply ((Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left ρ).congr_right
    intro n
    simp
  have hcount : Asymptotics.IsBigO atTop
      (fun n : ℕ => (rayIdealCounting m c n : ℝ))
      (fun n : ℕ => Real.rpow (n : ℝ) 1) := by
    apply (herr.add hlin).congr_left
    intro n
    simp only [Function.comp_apply]
    ring
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1)
  · apply hcount.congr_left
    intro n
    rw [← Nat.cast_sum, weberPrivateCoeff_sum]
  · exact fun n => Nat.cast_nonneg _
  · norm_num
  · exact hs

private theorem weberPrivatePartialZeta_eq_LSeries (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    rayClassPartialZeta m c s = LSeries (fun n => (weberPrivateCoeff m c n : ℂ)) s := by
  classical
  let A := {a : Ideal O // a ≠ 0 ∧ IsCoprime a m.finite ∧
    RayClassGroup.IsClassOfIdeal m a c}
  let B : ℕ → Type _ := fun n => {a : A // Ideal.absNorm a.1 = n}
  letI (n : ℕ) : Fintype (B n) :=
    Set.Finite.fintype (Set.Finite.preimage
      (s := {a : Ideal O | Ideal.absNorm a = n})
      (f := fun a : A => a.1) Subtype.val_injective.injOn
      (Ideal.finite_setOf_absNorm_eq n))
  let f : A → ℂ := fun a => Complex.cpow (Ideal.absNorm a.1 : ℂ) (-s)
  have hL := weberPrivateCoeff_LSeriesSummable m c ρ hO s hs
  have hnorm : Summable (fun z : Σ n, B n => ‖f z.2.1‖) := by
    apply (summable_sigma_of_nonneg fun _ => norm_nonneg _).2
    constructor
    · intro n
      exact Summable.of_finite
    · apply (summable_norm_iff.mpr hL).congr
      intro n
      rw [tsum_fintype, LSeries.norm_term_eq]
      by_cases hn : n = 0
      · subst n
        simp only [if_pos rfl, weberPrivateCoeff, B]
        have hempty : IsEmpty {a : A // Ideal.absNorm a.1 = 0} :=
          ⟨fun a => (a.1.2.1 (Ideal.absNorm_eq_zero_iff.mp a.2))⟩
        simp
      · rw [if_neg hn]
        simp_rw [f, show ∀ a : B n, Ideal.absNorm a.1.1 = n from fun a => a.2]
        rw [Finset.sum_const, nsmul_eq_mul, Complex.norm_natCast]
        have hcp : ‖Complex.cpow (n : ℂ) (-s)‖ =
            Real.rpow (n : ℝ) (-s).re :=
          Complex.norm_cpow_eq_rpow_re_of_pos
            (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (-s)
        rw [hcp, Complex.neg_re, weberPrivateCoeff]
        rw [Finset.card_univ, show Fintype.card (B n) = Nat.card (B n) by
          exact Fintype.card_eq_nat_card]
        simp only [B]
        rw [div_eq_mul_inv]
        have hneg : Real.rpow (n : ℝ) (-s.re) =
            (Real.rpow (n : ℝ) s.re)⁻¹ :=
          Real.rpow_neg (Nat.cast_nonneg n) s.re
        rw [hneg]
        rfl
  have hsigma : Summable (fun z : Σ n, B n => f z.2.1) :=
    summable_norm_iff.mp hnorm
  have hA : Summable f := by
    let e := Equiv.sigmaFiberEquiv (fun a : A => Ideal.absNorm a.1)
    exact (e.summable_iff (f := f)).mp hsigma
  rw [rayClassPartialZeta]
  rw [show (fun a : Ideal O => if a ≠ 0 ∧ IsCoprime a m.finite ∧
      RayClassGroup.IsClassOfIdeal m a c then
        Complex.cpow (Ideal.absNorm a : ℂ) (-s) else 0) =
      Set.indicator {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c}
        (fun a => Complex.cpow (Ideal.absNorm a : ℂ) (-s)) by
    funext a
    by_cases ha : a ≠ 0 ∧ IsCoprime a m.finite ∧
      RayClassGroup.IsClassOfIdeal m a c
    · rw [if_pos ha, Set.indicator_apply,
        if_pos (show a ∈ {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
          RayClassGroup.IsClassOfIdeal m a c} from ha)]
    · rw [if_neg ha, Set.indicator_apply,
        if_neg (show a ∉ {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
          RayClassGroup.IsClassOfIdeal m a c} from ha)]]
  rw [← tsum_subtype]
  change (∑' a : A, f a) = _
  let e := Equiv.sigmaFiberEquiv (fun a : A => Ideal.absNorm a.1)
  rw [← e.tsum_eq f]
  have he : (fun z => f (e z)) = fun z : Σ n, B n => f z.2.1 := rfl
  rw [he, hsigma.tsum_sigma]
  change (∑' n, ∑' a : B n, f a.1) =
    ∑' n, LSeries.term (fun n => (weberPrivateCoeff m c n : ℂ)) s n
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simp_rw [f, show ∀ a : B n, Ideal.absNorm a.1.1 = n from fun a => a.2]
  by_cases hn : n = 0
  · subst n
    have hempty : IsEmpty (B 0) :=
      ⟨fun a => (a.1.2.1 (Ideal.absNorm_eq_zero_iff.mp a.2))⟩
    simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, weberPrivateCoeff, show Fintype.card (B n) = Nat.card (B n) by
        exact Fintype.card_eq_nat_card]
    simp only [B]
    have hcp : Complex.cpow (n : ℂ) (-s) = (Complex.cpow (n : ℂ) s)⁻¹ :=
      Complex.cpow_neg (n : ℂ) s
    rw [hcp, div_eq_mul_inv]
    have heq : Complex.cpow (n : ℂ) s = (n : ℂ) ^ s := rfl
    rw [heq]

private noncomputable def weberPrivatePartialTerm (m : RayModulus K)
    (c : RayClassGroup m) (s : ℂ) (a : Ideal O) : ℂ := by
  classical
  exact if a ≠ 0 ∧ IsCoprime a m.finite ∧
      RayClassGroup.IsClassOfIdeal m a c then
    Complex.cpow (Ideal.absNorm a : ℂ) (-s) else 0

private theorem weberPrivatePartialZeta_summable (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    Summable (weberPrivatePartialTerm m c s) := by
  classical
  change Summable (fun a : Ideal O =>
    if a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c then
      Complex.cpow (Ideal.absNorm a : ℂ) (-s) else 0)
  let A := {a : Ideal O // a ≠ 0 ∧ IsCoprime a m.finite ∧
    RayClassGroup.IsClassOfIdeal m a c}
  let B : ℕ → Type _ := fun n => {a : A // Ideal.absNorm a.1 = n}
  letI (n : ℕ) : Fintype (B n) :=
    Set.Finite.fintype (Set.Finite.preimage
      (s := {a : Ideal O | Ideal.absNorm a = n})
      (f := fun a : A => a.1) Subtype.val_injective.injOn
      (Ideal.finite_setOf_absNorm_eq n))
  let f : A → ℂ := fun a => Complex.cpow (Ideal.absNorm a.1 : ℂ) (-s)
  have hL := weberPrivateCoeff_LSeriesSummable m c ρ hO s hs
  have hnorm : Summable (fun z : Σ n, B n => ‖f z.2.1‖) := by
    apply (summable_sigma_of_nonneg fun _ => norm_nonneg _).2
    constructor
    · intro n
      exact Summable.of_finite
    · apply (summable_norm_iff.mpr hL).congr
      intro n
      rw [tsum_fintype, LSeries.norm_term_eq]
      by_cases hn : n = 0
      · subst n
        simp only [weberPrivateCoeff, B]
        have hempty : IsEmpty {a : A // Ideal.absNorm a.1 = 0} :=
          ⟨fun a => (a.1.2.1 (Ideal.absNorm_eq_zero_iff.mp a.2))⟩
        simp
      · rw [if_neg hn]
        simp_rw [f, show ∀ a : B n, Ideal.absNorm a.1.1 = n from fun a => a.2]
        rw [Finset.sum_const, nsmul_eq_mul, Complex.norm_natCast]
        have hcp : ‖Complex.cpow (n : ℂ) (-s)‖ =
            Real.rpow (n : ℝ) (-s).re :=
          Complex.norm_cpow_eq_rpow_re_of_pos
            (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (-s)
        rw [hcp, Complex.neg_re, weberPrivateCoeff, Finset.card_univ,
          show Fintype.card (B n) = Nat.card (B n) by
            exact Fintype.card_eq_nat_card]
        simp only [B]
        rw [div_eq_mul_inv]
        have hneg : Real.rpow (n : ℝ) (-s.re) =
            (Real.rpow (n : ℝ) s.re)⁻¹ :=
          Real.rpow_neg (Nat.cast_nonneg n) s.re
        rw [hneg]
        rfl
  have hsigma : Summable (fun z : Σ n, B n => f z.2.1) :=
    summable_norm_iff.mp hnorm
  have hA : Summable f := by
    let e := Equiv.sigmaFiberEquiv (fun a : A => Ideal.absNorm a.1)
    exact (e.summable_iff (f := f)).mp hsigma
  have hind : Summable (Set.indicator
      {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c}
      (fun a => Complex.cpow (Ideal.absNorm a : ℂ) (-s))) :=
    summable_subtype_iff_indicator.mp hA
  apply hind.congr
  intro a
  by_cases ha : a ≠ 0 ∧ IsCoprime a m.finite ∧
      RayClassGroup.IsClassOfIdeal m a c
  · rw [Set.indicator_apply,
      if_pos (show a ∈ {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c} from ha), if_pos ha]
  · rw [Set.indicator_apply,
      if_neg (show a ∉ {a : Ideal O | a ≠ 0 ∧ IsCoprime a m.finite ∧
        RayClassGroup.IsClassOfIdeal m a c} from ha), if_neg ha]

private theorem weberPrivateError_LSeriesSummable (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (weberPrivateErrorCoeff m c ρ) s := by
  apply LSeriesSummable.sub (weberPrivateCoeff_LSeriesSummable m c ρ hO s hs)
  have hconst := (LSeriesSummable_one_iff.mpr hs).smul (ρ : ℂ)
  refine (LSeriesSummable_congr s (f := fun _ => (ρ : ℂ))
    (g := (ρ : ℂ) • (1 : ℕ → ℂ)) ?_).mpr hconst
  intro n hn
  simp

private noncomputable def weberPrivateErrorStep (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, weberPrivateErrorCoeff m c ρ k

private noncomputable def weberPrivateErrorContinuation (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (s : ℂ) : ℂ :=
  s * mellin (weberPrivateErrorStep m c ρ) (-s)

private theorem weberPrivateErrorStep_locallyIntegrable (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) :
    LocallyIntegrableOn (weberPrivateErrorStep m c ρ) (Set.Ioi 0) := by
  have h := (locallyIntegrableOn_mul_sum_Icc (weberPrivateErrorCoeff m c ρ) (m := 1)
    (a := 0) le_rfl (locallyIntegrableOn_const 1)).mono_set
      Set.Ioi_subset_Ici_self
  convert h using 1
  funext t
  simp [weberPrivateErrorStep]

private theorem weberPrivateErrorStep_bigO (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ)))) :
    Asymptotics.IsBigO atTop (weberPrivateErrorStep m c ρ)
      (fun t : ℝ => Real.rpow t
        (1 - 1 / (Module.finrank ℚ K : ℝ))) := by
  have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hq : 0 ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hd
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
    (Asymptotics.isEquivalent_nat_floor.isBigO.rpow hq
      (eventually_ge_atTop 0))

private theorem weberPrivateErrorStep_bigO_zero (m : RayModulus K)
    (c : RayClassGroup m) (ρ b : ℝ) :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) (weberPrivateErrorStep m c ρ)
      (fun t : ℝ => Real.rpow t (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [zero_mul, norm_nonneg, le_zero_iff]
  simp only [weberPrivateErrorStep]
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht.2
  simp [this]

private theorem weberPrivateErrorContinuation_differentiableAt (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    DifferentiableAt ℂ (weberPrivateErrorContinuation m c ρ) s := by
  let q : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  have hmel : DifferentiableAt ℂ (mellin (weberPrivateErrorStep m c ρ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (weberPrivateErrorStep_locallyIntegrable m c ρ)
      (a := -q) (b := (-s).re - 1)
    · simpa [q] using weberPrivateErrorStep_bigO m c ρ hO
    · change (-s).re < -q
      dsimp [q] at hs ⊢
      linarith
    · exact weberPrivateErrorStep_bigO_zero m c ρ ((-s).re - 1)
    · simp
  unfold weberPrivateErrorContinuation
  fun_prop

private theorem weberPrivateMellin_eq_integral (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (s : ℂ) :
    mellin (weberPrivateErrorStep m c ρ) (-s) =
      ∫ t : ℝ in Set.Ioi 1, weberPrivateErrorStep m c ρ t *
        (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with t ht
  by_cases h1 : 1 < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from zero_lt_one.trans h1),
      Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from h1)]
    rw [show -s - 1 = -(s + 1) by ring, mul_comm]
  · by_cases h0 : 0 < t
    · have ht1 : t < 1 := lt_of_le_of_ne (le_of_not_gt h1) ht
      have hfloor : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht1
      rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from h0),
        Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) from h1),
        weberPrivateErrorStep, hfloor]
      simp
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from h0),
        Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) from fun h => h0 (zero_lt_one.trans h))]

private theorem weberPrivateErrorContinuation_eq_LSeries (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hOreal : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    weberPrivateErrorContinuation m c ρ s = LSeries (weberPrivateErrorCoeff m c ρ) s := by
  rw [weberPrivateErrorContinuation, weberPrivateMellin_eq_integral]
  symm
  exact LSeries_eq_mul_integral _
    (by
      have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hd)
    (lt_trans (by
      have hd : (0 : ℝ) < Module.finrank ℚ K := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
      have : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := one_div_pos.mpr hd
      linarith) hs)
    (weberPrivateError_LSeriesSummable m c ρ hOreal s hs) hO

private noncomputable def weberPrivatePartialContinuation (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ) (s : ℂ) : ℂ :=
  ρ * riemannZeta s + weberPrivateErrorContinuation m c ρ s

private theorem weberPrivatePartialContinuation_eq (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hOreal : Asymptotics.IsBigO atTop
      (fun x : ℝ => (rayIdealCounting m c x : ℝ) - ρ * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ))))
    (s : ℂ) (hs : 1 < s.re) :
    weberPrivatePartialContinuation m c ρ s = rayClassPartialZeta m c s := by
  have he := weberPrivateError_LSeriesSummable m c ρ hOreal s hs
  have hc := weberPrivateCoeff_LSeriesSummable m c ρ hOreal s hs
  have hone := LSeriesSummable_one_iff.mpr hs
  have hconst := hone.smul (ρ : ℂ)
  calc
    weberPrivatePartialContinuation m c ρ s =
        ρ * LSeries (1 : ℕ → ℂ) s + LSeries (weberPrivateErrorCoeff m c ρ) s := by
      rw [weberPrivatePartialContinuation, LSeries_one_eq_riemannZeta hs,
        weberPrivateErrorContinuation_eq_LSeries m c ρ hOreal hO s hs]
    _ = LSeries ((ρ : ℂ) • (1 : ℕ → ℂ)) s +
        LSeries (weberPrivateErrorCoeff m c ρ) s := by rw [LSeries_smul]
    _ = LSeries ((ρ : ℂ) • (1 : ℕ → ℂ) + weberPrivateErrorCoeff m c ρ) s :=
      (LSeries_add hconst he).symm
    _ = LSeries (fun n => (weberPrivateCoeff m c n : ℂ)) s := by
      apply LSeries_congr
      intro n hn
      simp [weberPrivateErrorCoeff]
    _ = rayClassPartialZeta m c s :=
      (weberPrivatePartialZeta_eq_LSeries m c ρ hOreal s hs).symm

private theorem weberPrivateMulChar_sum_eq_zero {G : Type*} [CommGroup G] [Finite G]
    (ψ : MulChar G ℂ) (hψ : ψ ≠ 1) : ∑' c : G, ψ c = 0 := by
  classical
  letI := Fintype.ofFinite G
  rw [tsum_fintype]
  have hex : ∃ d : G, ψ d ≠ 1 := by
    by_contra h
    push Not at h
    apply hψ
    apply MulChar.ext'
    intro d
    rw [MulChar.one_apply (Group.isUnit d)]
    exact h d
  obtain ⟨d, hd⟩ := hex
  have hre : ∑ c : G, ψ c = ∑ c : G, ψ (d * c) := by
    let e : G ≃ G := Equiv.mulLeft d
    exact (e.sum_comp ψ).symm
  simp_rw [map_mul, ← Finset.mul_sum] at hre
  have hz : (1 - ψ d) * ∑ c : G, ψ c = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hre
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd.symm)

private theorem weberPrivate_count_eq_zero_of_isCoprime
    {a M : Ideal O} (ha : a ≠ 0) (hcop : IsCoprime a M)
    (p : PrimeIdeal K) (hp : p.asIdeal ∣ M) :
    FractionalIdeal.count K p (a : FractionalIdeal O⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K p ha, Int.ofNat_eq_zero]
  by_contra hc
  have hpa : p.asIdeal ∣ a :=
    (Associates.count_ne_zero_iff_dvd ha p.irreducible).mp hc
  have haP : a ≤ p.asIdeal := Ideal.dvd_iff_le.mp hpa
  have hMP : M ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
  have htop : (⊤ : Ideal O) ≤ p.asIdeal := by
    rw [← hcop.sup_eq]
    exact sup_le haP hMP
  exact p.isPrime.ne_top (top_unique htop)

private noncomputable def weberPrivateRayIdealOfCoprime (m : RayModulus K)
    (a : Ideal O) (ha : a ≠ 0) (hcop : IsCoprime a m.finite) :
    RayIdealGroup m :=
  ⟨Units.mk0 (a : FractionalIdeal O⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr ha),
    fun p hp => weberPrivate_count_eq_zero_of_isCoprime ha hcop p hp⟩

private theorem weberPrivate_isClassOfIdeal (m : RayModulus K)
    (a : Ideal O) (ha : a ≠ 0) (hcop : IsCoprime a m.finite) :
    RayClassGroup.IsClassOfIdeal m a
      (RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha hcop)) := by
  refine ⟨weberPrivateRayIdealOfCoprime m a ha hcop, ?_, rfl⟩
  rfl

private theorem weberPrivate_isClassOfIdeal_unique (m : RayModulus K)
    (a : Ideal O) {c d : RayClassGroup m}
    (hc : RayClassGroup.IsClassOfIdeal m a c)
    (hd : RayClassGroup.IsClassOfIdeal m a d) : c = d := by
  obtain ⟨I, hIa, hIc⟩ := hc
  obtain ⟨J, hJa, hJd⟩ := hd
  have hIJ : I = J := by
    apply Subtype.ext
    apply Units.ext
    exact hIa.trans hJa.symm
  rw [← hIc, ← hJd, hIJ]

private theorem weberPrivate_prime_isCoprime (m : RayModulus K)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    IsCoprime p.asIdeal m.finite := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hpP hmP hP
  have hpmax : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hpeq : p.asIdeal = P := hpmax.eq_of_le hP.ne_top hpP
  apply hp
  rw [Ideal.dvd_iff_le, hpeq]
  exact hmP

private theorem weberPrivate_trivialCharacterValue (m : RayModulus K)
    (a : Ideal O) (ha : a ≠ 0) (hcop : IsCoprime a m.finite) :
    rayClassCharacterValue m 1 a = 1 := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  let c : RayClassGroup m :=
    RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha hcop)
  have hac : RayClassGroup.IsClassOfIdeal m a c :=
    weberPrivate_isClassOfIdeal m a ha hcop
  rw [rayClassCharacterValue, tsum_fintype, Finset.sum_eq_single c]
  · rw [if_pos hac, MulChar.one_apply (Group.isUnit c)]
  · intro d hd hdc
    have had : ¬RayClassGroup.IsClassOfIdeal m a d := by
      intro had
      exact hdc (weberPrivate_isClassOfIdeal_unique m a had hac)
    rw [if_neg had]
  · simp

private theorem weberPrivateErrorContinuation_analytic (m : RayModulus K)
    (c : RayClassGroup m) (ρ : ℝ)
    (hO : Asymptotics.IsBigO atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, weberPrivateErrorCoeff m c ρ k)
      (fun n : ℕ => Real.rpow (n : ℝ)
        (1 - 1 / (Module.finrank ℚ K : ℝ)))) :
    AnalyticOnNhd ℂ (weberPrivateErrorContinuation m c ρ)
      {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (weberPrivateErrorContinuation_differentiableAt m c ρ hO s hs).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

private abbrev weberPrivateFactoredFinsupp {ι : Type*} [DecidableEq ι]
    (t : Finset ι) := {e : ι →₀ ℕ // e.support ⊆ t}

private noncomputable def weberPrivateInsertFactorEquiv {ι : Type*} [DecidableEq ι]
    (p : ι) (t : Finset ι) (hp : p ∉ t) :
    ℕ × weberPrivateFactoredFinsupp t ≃
      weberPrivateFactoredFinsupp (insert p t) where
  toFun ne := ⟨Finsupp.single p ne.1 + ne.2.1, fun q hq => by
    apply Finset.mem_insert.mpr
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact Or.inl (Finset.mem_singleton.mp
        (Finsupp.support_single_subset h))
    · exact Or.inr (ne.2.2 h)⟩
  invFun e := ⟨e.1 p, ⟨e.1.erase p, fun q hq => by
    rw [Finsupp.support_erase] at hq
    have hqi := e.2 (Finset.erase_subset p e.1.support hq)
    exact (Finset.mem_insert.mp hqi).resolve_left (Finset.ne_of_mem_erase hq)⟩⟩
  left_inv ne := by
    apply Prod.ext
    · simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      have : ne.2.1 p = 0 := Finsupp.notMem_support_iff.mp
        (fun h => hp (ne.2.2 h))
      simp [this]
    · apply Subtype.ext
      ext q
      by_cases hqp : q = p
      · subst q
        simp only [Finsupp.erase_same]
        have : ne.2.1 p = 0 := Finsupp.notMem_support_iff.mp
          (fun h => hp (ne.2.2 h))
        exact this.symm
      · simp [Finsupp.erase_ne hqp]
  right_inv e := by
    apply Subtype.ext
    exact Finsupp.single_add_erase p e.1

private noncomputable def weberPrivateFactorTerm {ι : Type*}
    (x : ι → ℂ) (e : ι →₀ ℕ) : ℂ :=
  e.prod fun p n => x p ^ n

private theorem weberPrivateFactorTerm_insertEquiv {ι : Type*} [DecidableEq ι]
    (x : ι → ℂ) (p : ι) (t : Finset ι) (hp : p ∉ t)
    (ne : ℕ × weberPrivateFactoredFinsupp t) :
    weberPrivateFactorTerm x (weberPrivateInsertFactorEquiv p t hp ne).1 =
      x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1 := by
  change weberPrivateFactorTerm x (Finsupp.single p ne.1 + ne.2.1) = _
  unfold weberPrivateFactorTerm
  rw [Finsupp.prod_add_index]
  · rw [Finsupp.prod_single_index]
    simp
  · intro q hq
    simp
  · intro q hq a b
    exact pow_add (x q) a b

private theorem weberPrivateFiniteFactor_hasSum {ι : Type*} [DecidableEq ι]
    (x : ι → ℂ) (hx : ∀ p, ‖x p‖ < 1) (t : Finset ι) :
    Summable (fun e : weberPrivateFactoredFinsupp t =>
      ‖weberPrivateFactorTerm x e.1‖) ∧
      HasSum (fun e : weberPrivateFactoredFinsupp t =>
        weberPrivateFactorTerm x e.1)
        (∏ p ∈ t, (1 - x p)⁻¹) := by
  induction t using Finset.induction with
  | empty =>
      let z : weberPrivateFactoredFinsupp (∅ : Finset ι) := ⟨0, by simp⟩
      letI : Unique (weberPrivateFactoredFinsupp (∅ : Finset ι)) :=
        { default := z
          uniq := fun e => by
            apply Subtype.ext
            ext p
            have hp : p ∉ e.1.support := fun hp => by simpa using e.2 hp
            exact Finsupp.notMem_support_iff.mp hp }
      constructor
      · exact Summable.of_finite
      · convert hasSum_unique (fun e : weberPrivateFactoredFinsupp
            (∅ : Finset ι) => weberPrivateFactorTerm x e.1) using 1
        rw [show default = z from Subsingleton.elim _ _]
        simp [z, weberPrivateFactorTerm]
  | @insert p t hp ih =>
      have hpNorm : Summable (fun n : ℕ => ‖x p ^ n‖) :=
        (summable_geometric_iff_norm_lt_one.mpr (hx p)).norm
      have hpSum : HasSum (fun n : ℕ => x p ^ n) (1 - x p)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (hx p)
      have hnormPair : Summable
          (fun ne : ℕ × weberPrivateFactoredFinsupp t =>
            ‖x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1‖) := by
        simpa only [norm_mul] using
          Summable.mul_of_nonneg hpNorm ih.1
            (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hmul : Summable
          (fun ne : ℕ × weberPrivateFactoredFinsupp t =>
            x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1) :=
        summable_mul_of_summable_norm
          (f := fun n => x p ^ n)
          (g := fun e : weberPrivateFactoredFinsupp t =>
            weberPrivateFactorTerm x e.1) hpNorm ih.1
      have hpairValue :
          (∑' ne : ℕ × weberPrivateFactoredFinsupp t,
            x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1) =
            (1 - x p)⁻¹ * ∏ q ∈ t, (1 - x q)⁻¹ := by
        calc
          _ = (∑' n : ℕ, x p ^ n) *
              ∑' e : weberPrivateFactoredFinsupp t,
                weberPrivateFactorTerm x e.1 :=
            (hpSum.summable.tsum_mul_tsum ih.2.summable hmul).symm
          _ = _ := by rw [hpSum.tsum_eq, ih.2.tsum_eq]
      have hsumPair : HasSum
          (fun ne : ℕ × weberPrivateFactoredFinsupp t =>
            x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1)
          ((1 - x p)⁻¹ * ∏ q ∈ t, (1 - x q)⁻¹) := by
        rw [← hpairValue]
        exact hmul.hasSum
      constructor
      · apply ((weberPrivateInsertFactorEquiv p t hp).summable_iff).mp
        convert hnormPair using 1
        funext ne
        change ‖weberPrivateFactorTerm x
          (weberPrivateInsertFactorEquiv p t hp ne).1‖ =
            ‖x p ^ ne.1 * weberPrivateFactorTerm x ne.2.1‖
        rw [weberPrivateFactorTerm_insertEquiv]
      · rw [Finset.prod_insert hp]
        apply ((weberPrivateInsertFactorEquiv p t hp).hasSum_iff).mp
        convert hsumPair using 1
        funext ne
        exact weberPrivateFactorTerm_insertEquiv x p t hp ne

private theorem weberPrivateEulerProduct_hasProd {ι : Type*} [DecidableEq ι]
    (x : ι → ℂ)
    (hsum : Summable (fun e : ι →₀ ℕ => ‖weberPrivateFactorTerm x e‖)) :
    HasProd (fun p => (1 - x p)⁻¹)
      (∑' e : ι →₀ ℕ, weberPrivateFactorTerm x e) := by
  have hx (p : ι) : ‖x p‖ < 1 := by
    have h := hsum.comp_injective (Finsupp.single_injective p)
    have h' : Summable (fun n : ℕ => ‖x p ^ n‖) := by
      apply h.congr
      intro n
      simp [weberPrivateFactorTerm]
    exact summable_geometric_iff_norm_lt_one.mp (Summable.of_norm h')
  have hfinite (t : Finset ι) := weberPrivateFiniteFactor_hasSum x hx t
  let f : Finset ι → (ι →₀ ℕ) → ℂ := fun t e =>
    if e.support ⊆ t then weberPrivateFactorTerm x e else 0
  have hpoint (e : ι →₀ ℕ) :
      Tendsto (fun t : Finset ι => f t e) atTop
        (𝓝 (weberPrivateFactorTerm x e)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop e.support] with t ht
    simp [f, ht]
  have hbound : ∀ᶠ t : Finset ι in atTop, ∀ e,
      ‖f t e‖ ≤ ‖weberPrivateFactorTerm x e‖ := by
    filter_upwards [] with t e
    simp only [f]
    split_ifs
    · exact le_rfl
    · simp
  have hlim : Tendsto (fun t : Finset ι => ∑' e, f t e) atTop
      (𝓝 (∑' e, weberPrivateFactorTerm x e)) :=
    tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have heq (t : Finset ι) :
      ∑' e, f t e = ∏ p ∈ t, (1 - x p)⁻¹ := by
    let A : Set (ι →₀ ℕ) := {e | e.support ⊆ t}
    calc
      (∑' e, f t e) =
          ∑' e, A.indicator (weberPrivateFactorTerm x) e := by
        apply tsum_congr
        intro e
        simp only [f, A, Set.indicator_apply, Set.mem_setOf_eq]
      _ = ∑' e : A, weberPrivateFactorTerm x e.1 :=
        (tsum_subtype A (weberPrivateFactorTerm x)).symm
      _ = _ := (hfinite t).2.tsum_eq
  rw [HasProd]
  apply hlim.congr'
  filter_upwards [] with t
  exact heq t

private noncomputable def weberPrivateIdealFactorization
    (a : {a : Ideal O // a ≠ 0}) : PrimeIdeal K →₀ ℕ :=
  let h := FractionalIdeal.finite_factors (a.1 : FractionalIdeal O⁰ K)
  Finsupp.mk h.toFinset
    (fun p => (FractionalIdeal.count K p
      (a.1 : FractionalIdeal O⁰ K)).toNat)
    (fun p => by
      rw [h.mem_toFinset]
      change FractionalIdeal.count K p (a.1 : FractionalIdeal O⁰ K) ≠ 0 ↔
        (FractionalIdeal.count K p (a.1 : FractionalIdeal O⁰ K)).toNat ≠ 0
      have hp := FractionalIdeal.count_coe_nonneg K p a.1
      constructor
      · intro hc hto
        apply hc
        exact le_antisymm (Int.toNat_eq_zero.mp hto) hp
      · intro hc hzero
        apply hc
        rw [hzero, Int.toNat_zero])

private theorem weberPrivateIdealFactorization_apply
    (a : {a : Ideal O // a ≠ 0}) (p : PrimeIdeal K) :
    weberPrivateIdealFactorization a p =
      (FractionalIdeal.count K p (a.1 : FractionalIdeal O⁰ K)).toNat := by
  rfl

private noncomputable def weberPrivateIdealOfFactorization
    (e : PrimeIdeal K →₀ ℕ) : Ideal O :=
  e.prod fun p n => p.asIdeal ^ n

private theorem weberPrivateIdealOfFactorization_ne_zero
    (e : PrimeIdeal K →₀ ℕ) : weberPrivateIdealOfFactorization e ≠ 0 := by
  classical
  unfold weberPrivateIdealOfFactorization Finsupp.prod
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ p.ne_bot

private theorem weberPrivate_count_idealOfFactorization
    (e : PrimeIdeal K →₀ ℕ) (p : PrimeIdeal K) :
    FractionalIdeal.count K p
      (weberPrivateIdealOfFactorization e : FractionalIdeal O⁰ K) = (e p : ℤ) := by
  classical
  let ez : PrimeIdeal K →₀ ℤ :=
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) e
  have hc := FractionalIdeal.count_finsuppProd K p ez
  have hprod : ez.prod (fun q (n : ℤ) =>
      (q.asIdeal : FractionalIdeal O⁰ K) ^ n) =
      e.prod (fun q n => (q.asIdeal : FractionalIdeal O⁰ K) ^ n) := by
    dsimp [ez]
    simpa only [zpow_natCast] using
      (Finsupp.prod_mapRange_index
        (g := e) (f := fun n : ℕ => (n : ℤ))
        (h := fun q (n : ℤ) => (q.asIdeal : FractionalIdeal O⁰ K) ^ n)
        (by intro; simp))
  rw [hprod] at hc
  have hcoe :
      (weberPrivateIdealOfFactorization e : FractionalIdeal O⁰ K) =
        e.prod (fun q n => (q.asIdeal : FractionalIdeal O⁰ K) ^ n) := by
    unfold weberPrivateIdealOfFactorization Finsupp.prod
    change (FractionalIdeal.coeIdealHom O⁰ K)
      (∏ q ∈ e.support, q.asIdeal ^ e q) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro q hq
    exact map_pow (FractionalIdeal.coeIdealHom O⁰ K) q.asIdeal (e q)
  rw [hcoe, hc]
  rfl

private noncomputable def weberPrivateIdealFactorEquiv :
    {a : Ideal O // a ≠ 0} ≃ (PrimeIdeal K →₀ ℕ) where
  toFun := weberPrivateIdealFactorization
  invFun e := ⟨weberPrivateIdealOfFactorization e,
    weberPrivateIdealOfFactorization_ne_zero e⟩
  left_inv a := by
    apply Subtype.ext
    apply FractionalIdeal.coeIdeal_injective (K := K)
    let b := weberPrivateIdealOfFactorization
      (weberPrivateIdealFactorization a)
    have hb : (b : FractionalIdeal O⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr
        (weberPrivateIdealOfFactorization_ne_zero
          (weberPrivateIdealFactorization a))
    change (b : FractionalIdeal O⁰ K) = (a.1 : FractionalIdeal O⁰ K)
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hb,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
        (FractionalIdeal.coeIdeal_ne_zero.mpr a.2)]
    apply finprod_congr
    intro p
    congr 1
    rw [weberPrivate_count_idealOfFactorization,
      weberPrivateIdealFactorization_apply]
    exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K p a.1)
  right_inv e := by
    ext p
    rw [weberPrivateIdealFactorization_apply,
      weberPrivate_count_idealOfFactorization]
    simp

private theorem weberPrivateRiemannZeta_meromorphicAt (s : ℂ) :
    MeromorphicAt riemannZeta s := by
  by_cases hs : s = 1
  · subst s
    have hmer : MeromorphicAt
        (fun z : ℂ => (z - 1)⁻¹ + riemannZeta₀ z) 1 :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt.inv.add
        (differentiable_riemannZeta₀.analyticAt 1).meromorphicAt
    apply hmer.congr
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (riemannZeta_eq_inv_sub_add (by simpa using hz)).symm
  · exact (analyticOn_riemannZeta s (by simp [hs])).meromorphicAt

/-- Blueprint Proposition 5.3 (`rayClassPartialZeta_continuation`): each partial
zeta has meromorphic continuation to `re(s) > 1-1/d`, only a possible simple
pole at one, and the same positive residue for every ray class. -/
theorem rayClassPartialZeta_continuation (m : RayModulus K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : RayClassGroup m,
      ∃ F : ℂ → ℂ,
        MeromorphicOn F {s : ℂ |
          1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
        (∀ s : ℂ, 1 < s.re → F s = rayClassPartialZeta m c s) ∧
        (∀ s : ℂ,
          1 - 1 / (Module.finrank ℚ K : ℝ) < s.re → s ≠ 1 →
            AnalyticAt ℂ F s) ∧
        Tendsto (fun s : ℂ => (s - 1) * F s) (𝓝[≠] (1 : ℂ)) (𝓝 (ρ : ℂ)) := by
  obtain ⟨ρ, hρ, hO⟩ := RayClassGroup.idealCount_sub_linear_isBigO m
  refine ⟨ρ, hρ, fun c => ?_⟩
  have hOn := weberPrivateError_bigO m c ρ (hO c)
  let F := weberPrivatePartialContinuation m c ρ
  have herr := weberPrivateErrorContinuation_analytic m c ρ hOn
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change MeromorphicAt
      ((fun _ : ℂ => (ρ : ℂ)) * riemannZeta +
        weberPrivateErrorContinuation m c ρ) z
    have hconst : MeromorphicAt (fun _ : ℂ => (ρ : ℂ)) z :=
      analyticAt_const.meromorphicAt
    have herror := (herr z hz).meromorphicAt
    exact (hconst.mul (weberPrivateRiemannZeta_meromorphicAt z)).add herror
  · intro z hz
    exact weberPrivatePartialContinuation_eq m c ρ (hO c) hOn z hz
  · intro z hz hzne
    change AnalyticAt ℂ
      ((fun _ : ℂ => (ρ : ℂ)) * riemannZeta +
        weberPrivateErrorContinuation m c ρ) z
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (ρ : ℂ)) z := analyticAt_const
    have hzeta : AnalyticAt ℂ riemannZeta z :=
      analyticOn_riemannZeta z (by simp [hzne])
    exact (hconst.mul hzeta).add (herr z hz)
  · have hd : (0 : ℝ) < Module.finrank ℚ K := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hone : 1 - 1 / (Module.finrank ℚ K : ℝ) < (1 : ℂ).re := by
      simp only [Complex.one_re]
      have : (0 : ℝ) < 1 / Module.finrank ℚ K := one_div_pos.mpr hd
      linarith
    have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
      tendsto_const_nhds
    have hsub : Tendsto (fun z : ℂ => z - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      simpa only [sub_self] using hid.sub hconst
    have herror : Tendsto
        (fun z : ℂ => (z - 1) * weberPrivateErrorContinuation m c ρ z)
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      simpa using hsub.mul
        ((herr (1 : ℂ) hone).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hlim := (riemannZeta_residue_one.const_mul (ρ : ℂ)).add herror
    convert hlim using 1
    · funext z
      simp only [F, weberPrivatePartialContinuation]
      ring
    · simp

private theorem weberPrivate_characterValue_eq (m : RayModulus K)
    (ψ : RayClassCharacter m) (a : Ideal O) (ha : a ≠ 0)
    (hcop : IsCoprime a m.finite) :
    rayClassCharacterValue m ψ a =
      ψ (RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha hcop)) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  let c : RayClassGroup m :=
    RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha hcop)
  have hac : RayClassGroup.IsClassOfIdeal m a c :=
    weberPrivate_isClassOfIdeal m a ha hcop
  rw [rayClassCharacterValue, tsum_fintype, Finset.sum_eq_single c]
  · rw [if_pos hac]
  · intro d hd hdc
    have had : ¬RayClassGroup.IsClassOfIdeal m a d := by
      intro had
      exact hdc (weberPrivate_isClassOfIdeal_unique m a had hac)
    rw [if_neg had]
  · simp

private theorem weberPrivate_rayIdealClass_mul (m : RayModulus K)
    (a b : Ideal O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hca : IsCoprime a m.finite) (hcb : IsCoprime b m.finite) :
    RayClassGroup.mk m
        (weberPrivateRayIdealOfCoprime m (a * b) (mul_ne_zero ha hb)
          (hca.mul_left hcb)) =
      RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha hca) *
        RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m b hb hcb) := by
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((a * b : Ideal O) : FractionalIdeal O⁰ K) =
    (a : FractionalIdeal O⁰ K) * (b : FractionalIdeal O⁰ K)
  exact FractionalIdeal.coeIdeal_mul a b

private theorem weberPrivate_characterValue_mul (m : RayModulus K)
    (ψ : RayClassCharacter m) (a b : Ideal O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hca : IsCoprime a m.finite) (hcb : IsCoprime b m.finite) :
    rayClassCharacterValue m ψ (a * b) =
      rayClassCharacterValue m ψ a * rayClassCharacterValue m ψ b := by
  rw [weberPrivate_characterValue_eq m ψ (a * b) (mul_ne_zero ha hb)
      (hca.mul_left hcb),
    weberPrivate_characterValue_eq m ψ a ha hca,
    weberPrivate_characterValue_eq m ψ b hb hcb,
    weberPrivate_rayIdealClass_mul m a b ha hb hca hcb, map_mul]

private noncomputable def weberPrivateIdealTerm (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (a : Ideal O) : ℂ := by
  classical
  exact if ha : a ≠ 0 then
    if hcop : IsCoprime a m.finite then
      rayClassCharacterValue m ψ a * Complex.cpow (Ideal.absNorm a : ℂ) (-s)
    else 0
  else 0

private theorem weberPrivateIdealTerm_zero (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) :
    weberPrivateIdealTerm m ψ s 0 = 0 := by
  simp [weberPrivateIdealTerm]

private theorem weberPrivateIdealTerm_one (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) :
    weberPrivateIdealTerm m ψ s 1 = 1 := by
  have hone : (1 : Ideal O) ≠ 0 := one_ne_zero
  have hcop : IsCoprime (1 : Ideal O) m.finite := isCoprime_one_left
  rw [weberPrivateIdealTerm, dif_pos hone, dif_pos hcop,
    weberPrivate_characterValue_eq m ψ 1 hone hcop]
  have hRay : weberPrivateRayIdealOfCoprime m 1 hone hcop = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((1 : Ideal O) : FractionalIdeal O⁰ K) = 1
    simp
  rw [hRay, map_one]
  simp

private theorem weberPrivateIdealTerm_mul (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (a b : Ideal O) :
    weberPrivateIdealTerm m ψ s (a * b) =
      weberPrivateIdealTerm m ψ s a * weberPrivateIdealTerm m ψ s b := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [weberPrivateIdealTerm]
  by_cases hb : b = 0
  · subst b
    simp [weberPrivateIdealTerm]
  rw [weberPrivateIdealTerm, dif_pos (mul_ne_zero ha hb)]
  simp only [weberPrivateIdealTerm, dif_pos ha, dif_pos hb]
  by_cases hca : IsCoprime a m.finite <;>
    by_cases hcb : IsCoprime b m.finite
  · rw [dif_pos (hca.mul_left hcb), dif_pos hca, dif_pos hcb,
      weberPrivate_characterValue_mul m ψ a b ha hb hca hcb,
      Ideal.absNorm.map_mul]
    have hpow : Complex.cpow ((Ideal.absNorm a * Ideal.absNorm b : ℕ) : ℂ) (-s) =
        Complex.cpow (Ideal.absNorm a : ℂ) (-s) *
          Complex.cpow (Ideal.absNorm b : ℂ) (-s) := by
      rw [Nat.cast_mul]
      simpa only [Complex.cpow_eq_pow, ← Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (Ideal.absNorm a))
          (Nat.cast_nonneg (Ideal.absNorm b)) (-s)
    rw [hpow]
    ring
  · rw [dif_neg (fun h => hcb (IsCoprime.of_mul_left_right h)),
      dif_pos hca, dif_neg hcb, mul_zero]
  · rw [dif_neg (fun h => hca (IsCoprime.of_mul_left_left h)),
      dif_neg hca, zero_mul]
  · rw [dif_neg (fun h => hca (IsCoprime.of_mul_left_left h)),
      dif_neg hca, zero_mul]

private noncomputable def weberPrivateIdealTermHom (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := weberPrivateIdealTerm m ψ s
  map_zero' := weberPrivateIdealTerm_zero m ψ s
  map_one' := weberPrivateIdealTerm_one m ψ s
  map_mul' := weberPrivateIdealTerm_mul m ψ s

private theorem weberPrivateIdealTerm_prime (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (p : PrimeIdeal K) :
    weberPrivateIdealTerm m ψ s p.asIdeal = by
      classical
      exact if p.asIdeal ∣ m.finite then 0 else
        rayClassCharacterValue m ψ p.asIdeal *
          Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) := by
  classical
  have hp0 : p.asIdeal ≠ (0 : Ideal O) := p.ne_bot
  simp only [weberPrivateIdealTerm, dif_pos hp0]
  by_cases hp : p.asIdeal ∣ m.finite
  · rw [if_pos hp]
    apply dif_neg
    intro hcop
    have htop : (⊤ : Ideal O) ≤ p.asIdeal := by
      rw [← hcop.sup_eq]
      exact sup_le le_rfl (Ideal.dvd_iff_le.mp hp)
    exact p.isPrime.ne_top (top_unique htop)
  · rw [if_neg hp, dif_pos (weberPrivate_prime_isCoprime m p hp)]
    rfl

private theorem weberPrivateFactorTerm_eq_idealTerm
    (m : RayModulus K) (ψ : RayClassCharacter m) (s : ℂ)
    (e : PrimeIdeal K →₀ ℕ) :
    weberPrivateFactorTerm
        (fun p => weberPrivateIdealTerm m ψ s p.asIdeal) e =
      weberPrivateIdealTerm m ψ s (weberPrivateIdealOfFactorization e) := by
  let f := weberPrivateIdealTermHom m ψ s
  change e.prod (fun p n => f p.asIdeal ^ n) =
    f (e.prod fun p n => p.asIdeal ^ n)
  unfold Finsupp.prod
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [map_pow]

private theorem weberPrivateIdealTerm_eq_classSum (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (a : Ideal O) :
    weberPrivateIdealTerm m ψ s a =
      ∑' c : RayClassGroup m, ψ c * weberPrivatePartialTerm m c s a := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  rw [tsum_fintype]
  by_cases ha : a ≠ 0 ∧ IsCoprime a m.finite
  · let c : RayClassGroup m :=
      RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha.1 ha.2)
    have hac : RayClassGroup.IsClassOfIdeal m a c :=
      weberPrivate_isClassOfIdeal m a ha.1 ha.2
    rw [weberPrivateIdealTerm, dif_pos ha.1, dif_pos ha.2,
      weberPrivate_characterValue_eq m ψ a ha.1 ha.2,
      Finset.sum_eq_single c]
    · rw [weberPrivatePartialTerm, if_pos ⟨ha.1, ha.2, hac⟩]
    · intro d hd hdc
      have had : ¬RayClassGroup.IsClassOfIdeal m a d := by
        intro had
        exact hdc (weberPrivate_isClassOfIdeal_unique m a had hac)
      rw [weberPrivatePartialTerm, if_neg (fun h => had h.2.2), mul_zero]
    · simp
  · have hz : weberPrivateIdealTerm m ψ s a = 0 := by
      rw [weberPrivateIdealTerm]
      by_cases hane : a ≠ 0
      · rw [dif_pos hane, dif_neg (fun hcop => ha ⟨hane, hcop⟩)]
      · rw [dif_neg hane]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    rw [weberPrivatePartialTerm, if_neg (fun h => ha ⟨h.1, h.2.1⟩), mul_zero]

private theorem weberPrivateIdealTerm_summable (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (hs : 1 < s.re) :
    Summable (weberPrivateIdealTerm m ψ s) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hO⟩ := RayClassGroup.idealCount_sub_linear_isBigO m
  have hsumm (c : RayClassGroup m) :
      Summable (fun a => ψ c * weberPrivatePartialTerm m c s a) :=
    (weberPrivatePartialZeta_summable m c ρ (hO c) s hs).mul_left (ψ c)
  have hsumFin (t : Finset (RayClassGroup m)) : Summable (fun a : Ideal O =>
      ∑ c ∈ t, ψ c * weberPrivatePartialTerm m c s a) := by
    induction t using Finset.induction with
    | empty => simp
    | @insert c t hc ih =>
        simpa only [Finset.sum_insert hc] using (hsumm c).add ih
  have hsum : Summable (fun a : Ideal O =>
      ∑ c : RayClassGroup m, ψ c * weberPrivatePartialTerm m c s a) := by
    simpa using hsumFin Finset.univ
  apply hsum.congr
  intro a
  rw [weberPrivateIdealTerm_eq_classSum m ψ s a, tsum_fintype]

private theorem weberPrivateIdealTerm_tsum (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (hs : 1 < s.re) :
    ∑' a : Ideal O, weberPrivateIdealTerm m ψ s a = weberLSeries m ψ s := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hO⟩ := RayClassGroup.idealCount_sub_linear_isBigO m
  have hsumm (c : RayClassGroup m) :
      Summable (fun a => ψ c * weberPrivatePartialTerm m c s a) :=
    (weberPrivatePartialZeta_summable m c ρ (hO c) s hs).mul_left (ψ c)
  unfold weberLSeries
  rw [tsum_fintype (f := fun c : RayClassGroup m =>
    ψ c * rayClassPartialZeta m c s)]
  change (∑' a : Ideal O, weberPrivateIdealTerm m ψ s a) =
    ∑ c : RayClassGroup m, ψ c *
      ∑' a : Ideal O, weberPrivatePartialTerm m c s a
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun c (_ : c ∈
    (Finset.univ : Finset (RayClassGroup m))) => hsumm c)]
  apply tsum_congr
  intro a
  rw [weberPrivateIdealTerm_eq_classSum m ψ s a, tsum_fintype]

/-- Blueprint §5.4 (`weberLSeries_eq_eulerProduct`): unique factorization and
absolute convergence identify the Weber series and its incomplete Euler
product on `re(s)>1`. -/
theorem weberLSeries_eq_eulerProduct (m : RayModulus K)
    (ψ : RayClassCharacter m) (s : ℂ) (hs : 1 < s.re) :
    weberLSeries m ψ s = weberLEulerProduct m ψ s := by
  classical
  let x : PrimeIdeal K → ℂ := fun p =>
    if p.asIdeal ∣ m.finite then 0 else
      rayClassCharacterValue m ψ p.asIdeal *
        Complex.cpow (PrimeIdeal.norm p : ℂ) (-s)
  have hx (p : PrimeIdeal K) :
      x p = weberPrivateIdealTerm m ψ s p.asIdeal := by
    exact (weberPrivateIdealTerm_prime m ψ s p).symm
  have hsumIdeal := weberPrivateIdealTerm_summable m ψ s hs
  have hsumSubtype : Summable (fun a : {a : Ideal O // a ≠ 0} =>
      ‖weberPrivateIdealTerm m ψ s a.1‖) :=
    hsumIdeal.norm.comp_injective Subtype.val_injective
  have hsumFactor : Summable (fun e : PrimeIdeal K →₀ ℕ =>
      ‖weberPrivateFactorTerm x e‖) := by
    apply (weberPrivateIdealFactorEquiv (K := K)).summable_iff.mp
    convert hsumSubtype using 1
    funext a
    change ‖weberPrivateFactorTerm x
      (weberPrivateIdealFactorEquiv (K := K) a)‖ =
        ‖weberPrivateIdealTerm m ψ s a.1‖
    rw [show x = fun p => weberPrivateIdealTerm m ψ s p.asIdeal from funext hx,
      weberPrivateFactorTerm_eq_idealTerm]
    have haeq := (weberPrivateIdealFactorEquiv (K := K)).left_inv a
    exact congrArg (fun z : {a : Ideal O // a ≠ 0} =>
      ‖weberPrivateIdealTerm m ψ s z.1‖) haeq
  have hprod := weberPrivateEulerProduct_hasProd x hsumFactor
  have hfactorTsum :
      (∑' e : PrimeIdeal K →₀ ℕ, weberPrivateFactorTerm x e) =
        ∑' a : Ideal O, weberPrivateIdealTerm m ψ s a := by
    calc
      _ = ∑' a : {a : Ideal O // a ≠ 0},
          weberPrivateFactorTerm x
            (weberPrivateIdealFactorEquiv (K := K) a) :=
        (weberPrivateIdealFactorEquiv (K := K)).tsum_eq
          (weberPrivateFactorTerm x) |>.symm
      _ = ∑' a : {a : Ideal O // a ≠ 0},
          weberPrivateIdealTerm m ψ s a.1 := by
        apply tsum_congr
        intro a
        rw [show x = fun p => weberPrivateIdealTerm m ψ s p.asIdeal from funext hx,
          weberPrivateFactorTerm_eq_idealTerm]
        have haeq := (weberPrivateIdealFactorEquiv (K := K)).left_inv a
        exact congrArg (fun z : {a : Ideal O // a ≠ 0} =>
          weberPrivateIdealTerm m ψ s z.1) haeq
      _ = _ := tsum_subtype_eq_of_support_subset (fun a ha hzero => by
        subst a
        exact ha (weberPrivateIdealTerm_zero m ψ s))
  calc
    weberLSeries m ψ s =
        ∑' a : Ideal O, weberPrivateIdealTerm m ψ s a :=
      (weberPrivateIdealTerm_tsum m ψ s hs).symm
    _ = ∑' e : PrimeIdeal K →₀ ℕ, weberPrivateFactorTerm x e :=
      hfactorTsum.symm
    _ = ∏' p : PrimeIdeal K, (1 - x p)⁻¹ := hprod.tprod_eq.symm
    _ = weberLEulerProduct m ψ s := by
      unfold weberLEulerProduct
      apply tprod_congr
      intro p
      simp only [x]
      by_cases hp : p.asIdeal ∣ m.finite
      · rw [if_pos hp, if_pos hp, sub_zero, inv_one]
      · rw [if_neg hp, if_neg hp]


/-- Blueprint Corollary 5.4 (`weberLSeries_analytic_of_ne_one`): a nontrivial
ray character cancels the common polar part. -/
theorem weberLSeries_analytic_of_ne_one (m : RayModulus K)
    (ψ : RayClassCharacter m) (hψ : ψ ≠ 1) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F {s : ℂ |
        1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → F s = weberLSeries m ψ s := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hO⟩ := RayClassGroup.idealCount_sub_linear_isBigO m
  have hOn (c : RayClassGroup m) :=
    weberPrivateError_bigO m c ρ (hO c)
  let F : ℂ → ℂ := fun s => ∑' c : RayClassGroup m,
    ψ c * weberPrivateErrorContinuation m c ρ s
  refine ⟨F, ?_, ?_⟩
  · change AnalyticOnNhd ℂ (fun s => ∑' c : RayClassGroup m,
      ψ c * weberPrivateErrorContinuation m c ρ s) _
    have hfin : AnalyticOnNhd ℂ
        (fun s => ∑ c : RayClassGroup m,
          ψ c * weberPrivateErrorContinuation m c ρ s)
        {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
      apply Finset.univ.analyticOnNhd_fun_sum
      intro c hc
      exact (show AnalyticOnNhd ℂ (fun _ : ℂ => ψ c) _ from
        analyticOnNhd_const).mul
          (weberPrivateErrorContinuation_analytic m c ρ (hOn c))
    simpa only [tsum_fintype] using hfin
  · intro s hs
    change (∑' c : RayClassGroup m,
      ψ c * weberPrivateErrorContinuation m c ρ s) = weberLSeries m ψ s
    rw [tsum_fintype, weberLSeries, tsum_fintype]
    have hpartial (c : RayClassGroup m) : rayClassPartialZeta m c s =
        ρ * riemannZeta s + weberPrivateErrorContinuation m c ρ s :=
      (weberPrivatePartialContinuation_eq m c ρ (hO c) (hOn c) s hs).symm
    simp_rw [hpartial, mul_add, Finset.sum_add_distrib]
    have hsum : ∑ c : RayClassGroup m, ψ c = 0 := by
      simpa [tsum_fintype] using weberPrivateMulChar_sum_eq_zero ψ hψ
    rw [← Finset.sum_mul, hsum, zero_mul, zero_add]

/-- Blueprint Corollary 5.4 (`weberLSeries_trivial`): on `re(s) > 1`, the
trivial Weber series is the Dedekind zeta series with precisely the modulus
factors removed. -/
theorem weberLSeries_trivial (m : RayModulus K) (s : ℂ) (hs : 1 < s.re) :
    weberLSeries m 1 s = incompleteDedekindZeta m s := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hO⟩ := RayClassGroup.idealCount_sub_linear_isBigO m
  have hsumm (c : RayClassGroup m) :
      Summable (weberPrivatePartialTerm m c s) :=
    weberPrivatePartialZeta_summable m c ρ (hO c) s hs
  have hone (c : RayClassGroup m) : (1 : RayClassCharacter m) c = 1 :=
    MulChar.one_apply (Group.isUnit c)
  rw [weberLSeries, tsum_fintype, incompleteDedekindZeta]
  simp_rw [hone, one_mul, rayClassPartialZeta]
  change (∑ c : RayClassGroup m, ∑' a : Ideal O,
      weberPrivatePartialTerm m c s a) = _
  rw [← Summable.tsum_finsetSum (fun c (_ : c ∈
    (Finset.univ : Finset (RayClassGroup m))) => hsumm c)]
  apply tsum_congr
  intro a
  by_cases ha : a ≠ 0 ∧ IsCoprime a m.finite
  · let c : RayClassGroup m :=
      RayClassGroup.mk m (weberPrivateRayIdealOfCoprime m a ha.1 ha.2)
    have hac : RayClassGroup.IsClassOfIdeal m a c :=
      weberPrivate_isClassOfIdeal m a ha.1 ha.2
    rw [if_pos ha]
    rw [Finset.sum_eq_single c]
    · rw [weberPrivatePartialTerm, if_pos ⟨ha.1, ha.2, hac⟩]
    · intro d hd hdc
      have had : ¬ RayClassGroup.IsClassOfIdeal m a d := by
        intro had
        exact hdc (weberPrivate_isClassOfIdeal_unique m a had hac)
      rw [weberPrivatePartialTerm, if_neg (fun h => had h.2.2)]
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro c hc
    rw [weberPrivatePartialTerm, if_neg (fun h => ha ⟨h.1, h.2.1⟩)]

private theorem weberPrivateDedekindZeta_eq_idealTsum (s : ℂ)
    (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑' a : Ideal O,
        if a ≠ 0 then Complex.cpow (Ideal.absNorm a : ℂ) (-s) else 0 := by
  classical
  let m : RayModulus K :=
    { finite := ⊤
      finite_ne := by rw [← Ideal.one_eq_top]; exact one_ne_zero
      infinite := ∅ }
  let f : Ideal O → ℂ := fun a =>
    if a ≠ 0 then Complex.cpow (Ideal.absNorm a : ℂ) (-s) else 0
  have hterm (a : Ideal O) : weberPrivateIdealTerm m 1 s a = f a := by
    by_cases ha : a ≠ 0
    · have hcop : IsCoprime a m.finite := by
        dsimp [m]
        rw [Ideal.isCoprime_iff_sup_eq]
        exact sup_top_eq a
      rw [weberPrivateIdealTerm, dif_pos ha, dif_pos hcop,
        weberPrivate_trivialCharacterValue m a ha hcop, one_mul]
      simp only [f, if_pos ha]
    · rw [weberPrivateIdealTerm, dif_neg ha]
      simp only [f, if_neg ha]
  have hsum : Summable f :=
    (weberPrivateIdealTerm_summable m 1 s hs).congr hterm
  let B : ℕ → Type _ := fun n => {a : Ideal O // Ideal.absNorm a = n}
  letI (n : ℕ) : Fintype (B n) :=
    Set.Finite.fintype (Ideal.finite_setOf_absNorm_eq n)
  let e := Equiv.sigmaFiberEquiv (fun a : Ideal O => Ideal.absNorm a)
  have hsigma : Summable (fun z : Σ n, B n => f z.2.1) := by
    apply (e.summable_iff (f := f)).mpr hsum
  rw [NumberField.dedekindZeta, LSeries]
  symm
  calc
    (∑' a : Ideal O, f a) = ∑' z : Σ n, B n, f z.2.1 :=
      (e.tsum_eq f).symm
    _ = ∑' n, ∑' a : B n, f a.1 := hsigma.tsum_sigma
    _ = ∑' n, LSeries.term
        (fun n => Nat.card {I : Ideal O // Ideal.absNorm I = n}) s n := by
      apply tsum_congr
      intro n
      rw [tsum_fintype]
      by_cases hn : n = 0
      · subst n
        have hzero (a : B 0) : a.1 = 0 := Ideal.absNorm_eq_zero_iff.mp a.2
        simp_rw [f, hzero]
        simp [LSeries.term_def]
      · have hne : ∀ a : B n, a.1 ≠ 0 := by
          intro a hzero
          apply hn
          simpa [hzero] using a.2.symm
        simp_rw [f, if_pos (hne _)]
        simp_rw [show ∀ a : B n, Ideal.absNorm a.1 = n from fun a => a.2]
        rw [Finset.sum_const, nsmul_eq_mul, LSeries.term_def, if_neg hn,
          Finset.card_univ, show Fintype.card (B n) = Nat.card (B n) by
            exact Fintype.card_eq_nat_card]
        rw [Complex.cpow_eq_pow, Complex.cpow_neg, div_eq_mul_inv]

/-- Blueprint §5.4, proposed declaration `dedekindZeta_eulerProduct`: the
Dedekind zeta Euler product on `re(s)>1`. -/
theorem dedekindZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∏' p : PrimeIdeal K,
        (1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹ := by
  classical
  let m : RayModulus K :=
    { finite := ⊤
      finite_ne := by rw [← Ideal.one_eq_top]; exact one_ne_zero
      infinite := ∅ }
  calc
    NumberField.dedekindZeta K s = incompleteDedekindZeta m s := by
      rw [weberPrivateDedekindZeta_eq_idealTsum s hs, incompleteDedekindZeta]
      apply tsum_congr
      intro a
      by_cases ha : a ≠ 0
      · rw [if_pos ha, if_pos ⟨ha, by
          dsimp [m]
          rw [Ideal.isCoprime_iff_sup_eq]
          exact sup_top_eq a⟩]
      · rw [if_neg ha, if_neg (fun h => ha h.1)]
    _ = weberLSeries m 1 s := (weberLSeries_trivial m s hs).symm
    _ = weberLEulerProduct m 1 s := weberLSeries_eq_eulerProduct m 1 s hs
    _ = ∏' p : PrimeIdeal K,
        (1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹ := by
      unfold weberLEulerProduct
      apply tprod_congr
      intro p
      have hp : ¬p.asIdeal ∣ m.finite := by
        rw [Ideal.dvd_iff_le]
        intro h
        exact p.isPrime.ne_top (top_unique h)
      rw [if_neg hp,
        weberPrivate_trivialCharacterValue m p.asIdeal p.ne_bot
          (weberPrivate_prime_isCoprime m p hp), one_mul]

/-- Blueprint §5.4 (`incompleteDedekindZeta_eulerProduct`): the finite-factor
removal is explicit. -/
theorem incompleteDedekindZeta_eulerProduct (m : RayModulus K)
    (s : ℂ) (hs : 1 < s.re) :
    incompleteDedekindZeta m s = incompleteDedekindZetaEulerProduct m s := by
  calc
    incompleteDedekindZeta m s = weberLSeries m 1 s :=
      (weberLSeries_trivial m s hs).symm
    _ = weberLEulerProduct m 1 s :=
      weberLSeries_eq_eulerProduct m 1 s hs
    _ = incompleteDedekindZetaEulerProduct m s := by
      unfold weberLEulerProduct incompleteDedekindZetaEulerProduct
      apply tprod_congr
      intro p
      by_cases hp : p.asIdeal ∣ m.finite
      · rw [if_pos hp, if_pos hp]
      · rw [if_neg hp, if_neg hp,
          weberPrivate_trivialCharacterValue m p.asIdeal p.ne_bot
            (weberPrivate_prime_isCoprime m p hp), one_mul]

end NU.Chebotarev
