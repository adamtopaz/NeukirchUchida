import Submission.NU.LocalTheory.Cohomology.KummerLowDegree
import Submission.NU.LocalTheory.NumberField.Place
import Submission.NU.LCFT.Basic.Norm

/-!
# Tame local norm lines

This module contains the completion comparison, the complete discretely
valued norm-line calculation, and its global consequence from Blueprint
§5.2.  The local field is represented by an actual complete `ℤᵐ⁰`-valued
field, so completeness is not hidden in an informal hypothesis bundle.
-/

open WithZero
open scoped NumberField TensorProduct

namespace NU.LocalTheory

noncomputable section

private theorem completion_principalUnit_iff
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) (x : Mˣ) :
    Units.map (NumberField.FinitePlace.embedding v).toMonoidHom x ∈
        (v.adicCompletionIntegers M).principalUnitGroup ↔
      x ∈ (primeValuationSubring v).principalUnitGroup := by
  let w := v.valuation M
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  rw [A.mem_principalUnitGroup_iff, B.mem_principalUnitGroup_iff]
  have hA : A = w.valuationSubring :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
  rw [hA]
  change (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰).valuationSubring.valuation
      (NumberField.FinitePlace.embedding v (x : M) - 1) < 1 ↔
    w.valuationSubring.valuation ((x : M) - 1) < 1
  have hlocal := (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰)).lt_iff_lt
      (x := NumberField.FinitePlace.embedding v (x : M) - 1) (y := 1)
  have hglobal := (Valuation.isEquiv_valuation_valuationSubring w).lt_iff_lt
      (x := (x : M) - 1) (y := 1)
  calc
    (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰).valuationSubring.valuation
        (NumberField.FinitePlace.embedding v (x : M) - 1) < 1 ↔
      Valued.v (NumberField.FinitePlace.embedding v (x : M) - 1) < 1 := by
        simpa only [map_one] using hlocal.symm
    _ ↔ w ((x : M) - 1) < 1 := by
      have hemb : NumberField.FinitePlace.embedding v ((x : M) - 1) =
          NumberField.FinitePlace.embedding v (x : M) - 1 := by simp
      rw [← hemb, NumberField.FinitePlace.embedding_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    _ ↔ w.valuationSubring.valuation ((x : M) - 1) < 1 := by
      simpa only [map_one] using hglobal

private def modNMap {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    (n : ℕ) (f : P →+ Q) : ModN P n →ₗ[ZMod n] ModN Q n :=
  (ModN.liftEquiv').symm ⟨(ModN.mkQ n).comp f, by
    intro g
    change n • ModN.mkQ n (f g) = 0
    rw [← map_nsmul]
    change (LinearMap.range (LinearMap.lsmul ℤ Q (n : ℤ))).mkQ
      (n • f g) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨f g, by simp⟩⟩

@[simp]
private theorem modNMap_mkQ {P Q : Type*} [AddCommGroup P]
    [AddCommGroup Q] (n : ℕ) (f : P →+ Q) (g : P) :
    modNMap n f (ModN.mkQ n g) = ModN.mkQ n (f g) := by
  rfl

private def modNLinearEquiv {P Q : Type*} [AddCommGroup P]
    [AddCommGroup Q] (n : ℕ) (e : P ≃+ Q) :
    ModN P n ≃ₗ[ZMod n] ModN Q n :=
  { modNMap n e.toAddMonoidHom with
    invFun := modNMap n e.symm.toAddMonoidHom
    left_inv := by
      intro x
      obtain ⟨g, rfl⟩ :=
        (LinearMap.range (LinearMap.lsmul ℤ P (n : ℤ))).mkQ_surjective x
      change modNMap n e.symm.toAddMonoidHom
        (modNMap n e.toAddMonoidHom (ModN.mkQ n g)) = ModN.mkQ n g
      rw [modNMap_mkQ, modNMap_mkQ]
      simp
    right_inv := by
      intro x
      obtain ⟨g, rfl⟩ :=
        (LinearMap.range (LinearMap.lsmul ℤ Q (n : ℤ))).mkQ_surjective x
      change modNMap n e.toAddMonoidHom
        (modNMap n e.symm.toAddMonoidHom (ModN.mkQ n g)) = ModN.mkQ n g
      rw [modNMap_mkQ, modNMap_mkQ]
      simp }

@[simp]
private theorem modNLinearEquiv_mkQ {P Q : Type*} [AddCommGroup P]
    [AddCommGroup Q] (n : ℕ) (e : P ≃+ Q) (g : P) :
    modNLinearEquiv n e (ModN.mkQ n g) = ModN.mkQ n (e g) := by
  rfl

/-- The valuation subring supplied by a `ℤᵐ⁰`-valued field. -/
abbrev valuedIntegerRing (Q : Type*) [Field Q] [Valued Q ℤᵐ⁰] :
    ValuationSubring Q :=
  (Valued.v : Valuation Q ℤᵐ⁰).valuationSubring

/-- Residue characteristic of the canonical valued integer ring. -/
def valuedResidueCharacteristic (Q : Type*) [Field Q] [Valued Q ℤᵐ⁰] : ℕ :=
  ringChar (IsLocalRing.ResidueField (valuedIntegerRing Q))

/-- Blueprint (5.4), `eq:completion-quotient`: completion induces an
isomorphism on the principal-unit quotient modulo `ℓ`-th powers.  The
characterizing equation records the canonical map on global units. -/
theorem completion_quotient {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (v : FinitePlace M) :
    ∃ e : PrincipalUnitModEll (primeValuationSubring v) ℓ ≃ₗ[ZMod ℓ]
        PrincipalUnitModEll (v.adicCompletionIntegers M) ℓ,
      ∀ x : Mˣ,
        e (principalUnitModEllClass (primeValuationSubring v) ℓ x) =
          principalUnitModEllClass (v.adicCompletionIntegers M) ℓ
            (Units.map (NumberField.FinitePlace.embedding v).toMonoidHom x) := by
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  let uemb : Mˣ →* (v.adicCompletion M)ˣ :=
    Units.map (NumberField.FinitePlace.embedding v).toMonoidHom
  have huemb : A.principalUnitGroup ≤
      Subgroup.comap uemb B.principalUnitGroup := by
    intro x hx
    exact (completion_principalUnit_iff v x).2 hx
  let qmap : (Mˣ ⧸ A.principalUnitGroup) →*
      ((v.adicCompletion M)ˣ ⧸ B.principalUnitGroup) :=
    QuotientGroup.map A.principalUnitGroup B.principalUnitGroup uemb huemb
  have hqinj : Function.Injective qmap := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A.principalUnitGroup y
      rw [MonoidHom.mem_ker] at hy
      change (QuotientGroup.mk (uemb x) :
        (v.adicCompletion M)ˣ ⧸ B.principalUnitGroup) = 1 at hy
      rw [QuotientGroup.eq_one_iff] at hy
      change (QuotientGroup.mk x : Mˣ ⧸ A.principalUnitGroup) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (completion_principalUnit_iff v x).1 hy
    · exact bot_le
  have hqsurj : Function.Surjective qmap := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective B.principalUnitGroup y
    let uy : v.adicCompletion M := (u : v.adicCompletion M)
    have huy0 : uy ≠ 0 := Units.ne_zero u
    have hopen : Metric.ball uy ‖uy‖ ∈ nhds uy :=
      Metric.ball_mem_nhds uy (norm_pos_iff.mpr huy0)
    obtain ⟨x, hxball⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap M v).mem_nhds hopen
    have hxclose : ‖algebraMap M (v.adicCompletion M) x - uy‖ < ‖uy‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      simp only [map_zero, zero_sub, norm_neg] at hxclose
      exact lt_irrefl _ hxclose
    let xu : Mˣ := Units.mk0 x hx0
    have hratio : uemb xu * u⁻¹ ∈ B.principalUnitGroup := by
      rw [B.mem_principalUnitGroup_iff]
      apply (Valuation.isEquiv_valuation_valuationSubring
        (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰)).lt_iff_lt.mp
      have hnorm : ‖algebraMap M (v.adicCompletion M) x * uy⁻¹ - 1‖ < 1 := by
        have hid : algebraMap M (v.adicCompletion M) x * uy⁻¹ - 1 =
            (algebraMap M (v.adicCompletion M) x - uy) * uy⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ huy0]
        rw [hid, norm_mul, norm_inv]
        rw [← div_eq_mul_inv]
        exact (div_lt_one (norm_pos_iff.mpr huy0)).2 hxclose
      have hembalg : NumberField.FinitePlace.embedding v x =
          algebraMap M (v.adicCompletion M) x := by
        rw [NumberField.FinitePlace.embedding_apply]
        rfl
      have hval : ((uemb xu * u⁻¹ : (v.adicCompletion M)ˣ) :
          v.adicCompletion M) =
          algebraMap M (v.adicCompletion M) x * uy⁻¹ := by
        simp [uemb, xu, uy, hembalg]
      rw [hval]
      simpa only [map_one] using
        (Valued.toNormedField.norm_lt_one_iff.mp hnorm)
    refine ⟨QuotientGroup.mk' A.principalUnitGroup xu, ?_⟩
    change (QuotientGroup.mk (uemb xu) :
      (v.adicCompletion M)ˣ ⧸ B.principalUnitGroup) = QuotientGroup.mk u
    apply (QuotientGroup.mk'_eq_mk' B.principalUnitGroup).2
    refine ⟨(uemb xu)⁻¹ * u, ?_, ?_⟩
    · simpa [mul_comm] using B.principalUnitGroup.inv_mem hratio
    · simp
  let qe : (Mˣ ⧸ A.principalUnitGroup) ≃*
      ((v.adicCompletion M)ˣ ⧸ B.principalUnitGroup) :=
    MulEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
  let e : PrincipalUnitModEll A ℓ ≃ₗ[ZMod ℓ]
      PrincipalUnitModEll B ℓ :=
    modNLinearEquiv ℓ (MulEquiv.toAdditive qe)
  refine ⟨e, ?_⟩
  intro x
  change e (ModN.mkQ ℓ (Additive.ofMul (QuotientGroup.mk x))) =
    ModN.mkQ ℓ (Additive.ofMul (QuotientGroup.mk (uemb x)))
  rw [show e = modNLinearEquiv ℓ (MulEquiv.toAdditive qe) by rfl,
    modNLinearEquiv_mkQ]
  rfl

@[simp]
private theorem principalUnitModEllClass_mul'
    {F : Type*} [Field F] (A : ValuationSubring F) (n : ℕ)
    (x y : Fˣ) :
    principalUnitModEllClass A n (x * y) =
      principalUnitModEllClass A n x + principalUnitModEllClass A n y := by
  rfl

private theorem cyclic_pow_factorization
    {G : Type*} [CommGroup G] [IsCyclic G]
    {ℓ : ℕ} [Fact ℓ.Prime] (b : G)
    (hb : ¬ ∃ y : G, y ^ ℓ = b) :
    ∀ x : G, ∃ (m : ℕ) (y : G), x = y ^ ℓ * b ^ m := by
  obtain ⟨g, hg⟩ := exists_zpow_surjective G
  obtain ⟨r, hr⟩ := hg b
  change g ^ r = b at hr
  intro x
  obtain ⟨s, hs⟩ := hg x
  change g ^ s = x at hs
  have hrdiv : ¬ (ℓ : ℤ) ∣ r := by
    rintro ⟨t, rfl⟩
    apply hb
    refine ⟨g ^ t, ?_⟩
    calc
      (g ^ t) ^ ℓ = g ^ (t * (ℓ : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
      _ = g ^ ((ℓ : ℤ) * t) := by rw [mul_comm]
      _ = b := hr
  have hrmod : (r : ZMod ℓ) ≠ 0 := by
    rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  let m : ℕ := ((s : ZMod ℓ) * (r : ZMod ℓ)⁻¹).val
  have hm : (m : ZMod ℓ) = (s : ZMod ℓ) * (r : ZMod ℓ)⁻¹ := by
    exact ZMod.natCast_zmod_val _
  have hzero : ((s - (m : ℤ) * r : ℤ) : ZMod ℓ) = 0 := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hm]
    field_simp
    simp
  have hdiv : (ℓ : ℤ) ∣ s - (m : ℤ) * r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  obtain ⟨t, ht⟩ := hdiv
  have hst : s = t * (ℓ : ℤ) + r * (m : ℤ) := by
    calc
      s = (s - (m : ℤ) * r) + (m : ℤ) * r := by ring
      _ = (ℓ : ℤ) * t + (m : ℤ) * r := by rw [ht]
      _ = t * (ℓ : ℤ) + r * (m : ℤ) := by ring
  refine ⟨m, g ^ t, ?_⟩
  calc
    x = g ^ s := hs.symm
    _ = g ^ (t * (ℓ : ℤ) + r * (m : ℤ)) := by rw [hst]
    _ = g ^ (t * (ℓ : ℤ)) * g ^ (r * (m : ℤ)) := by rw [zpow_add]
    _ = (g ^ t) ^ ℓ * (g ^ r) ^ m := by
      congr 1 <;> rw [← zpow_natCast, ← zpow_mul]
    _ = (g ^ t) ^ ℓ * b ^ m := by rw [hr]

/-- A factorization as an `n`-th power times a principal unit has trivial class. -/
private theorem principalUnitModEllClass_eq_zero_of_factor
    {F : Type*} [Field F] (A : ValuationSubring F) (n : ℕ)
    (a x u : Fˣ) (hu : u ∈ A.principalUnitGroup)
    (h : a = x ^ n * u) : principalUnitModEllClass A n a = 0 := by
  rw [h]
  change ModN.mkQ n (n • Additive.ofMul
    (QuotientGroup.mk x : Fˣ ⧸ A.principalUnitGroup) +
      Additive.ofMul (QuotientGroup.mk u : Fˣ ⧸ A.principalUnitGroup)) = 0
  rw [(QuotientGroup.eq_one_iff u).2 hu]
  let gx : Additive (Fˣ ⧸ A.principalUnitGroup) :=
    Additive.ofMul (QuotientGroup.mk x)
  change ModN.mkQ n (n • gx + 0) = 0
  calc
    ModN.mkQ n (n • gx + 0) = ModN.mkQ n (n • gx) :=
      congrArg (ModN.mkQ n) (add_zero (n • gx))
    _ = 0 := by
      rw [map_nsmul]
      change (LinearMap.range (LinearMap.lsmul ℤ _ (n : ℤ))).mkQ (n • gx) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨gx, by simp⟩

private theorem principalUnitModEllClass_pow'
    {F : Type*} [Field F] (A : ValuationSubring F) (n m : ℕ)
    (x : Fˣ) :
    principalUnitModEllClass A n (x ^ m) =
      m • principalUnitModEllClass A n x := by
  unfold principalUnitModEllClass
  change ModN.mkQ n (m • Additive.ofMul
    (QuotientGroup.mk x : Fˣ ⧸ A.principalUnitGroup)) =
      m • ModN.mkQ n (Additive.ofMul
        (QuotientGroup.mk x : Fˣ ⧸ A.principalUnitGroup))
  rw [map_nsmul]

private theorem principalUnitModEllClass_eq_zero_of_mem'
    {F : Type*} [Field F] (A : ValuationSubring F) (n : ℕ)
    (u : Fˣ) (hu : u ∈ A.principalUnitGroup) :
    principalUnitModEllClass A n u = 0 := by
  change ModN.mkQ n (Additive.ofMul
    (QuotientGroup.mk u : Fˣ ⧸ A.principalUnitGroup)) = 0
  rw [(QuotientGroup.eq_one_iff u).2 hu]
  rfl

private theorem principalUnitModEllClass_eq_zero_of_pow'
    {F : Type*} [Field F] (A : ValuationSubring F) (n : ℕ)
    (x y : Fˣ) (hxy : y ^ n = x) :
    principalUnitModEllClass A n x = 0 := by
  change ModN.mkQ n (Additive.ofMul
    (QuotientGroup.mk x : Fˣ ⧸ A.principalUnitGroup)) = 0
  rw [← hxy]
  change ModN.mkQ n (n • Additive.ofMul
    (QuotientGroup.mk y : Fˣ ⧸ A.principalUnitGroup)) = 0
  rw [map_nsmul]
  change (LinearMap.range (LinearMap.lsmul ℤ _ (n : ℤ))).mkQ
    (n • Additive.ofMul
      (QuotientGroup.mk y : Fˣ ⧸ A.principalUnitGroup)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Additive.ofMul
    (QuotientGroup.mk y : Fˣ ⧸ A.principalUnitGroup), by simp⟩

private theorem normalizedValuation_le_iff'
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    NU.LCFT.normalizedValuation K x ≤ NU.LCFT.normalizedValuation K y ↔
      ValuativeRel.valuation K (y : K) ≤ ValuativeRel.valuation K (x : K) := by
  have hnonneg : 0 ≤ NU.LCFT.normalizedValuation K (y * x⁻¹) ↔
      ValuativeRel.valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 := by
    unfold NU.LCFT.normalizedValuation NU.LCFT.normalizedValuationHom
    rw [(NU.LCFT.exists_normalizedValuationHom K).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  rw [NU.LCFT.normalizedValuation_mul] at hnonneg
  have hinv : NU.LCFT.normalizedValuation K x⁻¹ =
      -NU.LCFT.normalizedValuation K x := by
    simp [NU.LCFT.normalizedValuation]
  rw [hinv] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ NU.LCFT.normalizedValuation K y -
      NU.LCFT.normalizedValuation K x ↔
      ValuativeRel.valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change ValuativeRel.valuation K (y : K) /
      ValuativeRel.valuation K (x : K) ≤ 1 ↔ _
  rw [div_le_one₀ ((ValuativeRel.valuation K).pos_iff.mpr x.ne_zero)]

private theorem normalizedValuation_lt_iff'
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    NU.LCFT.normalizedValuation K x < NU.LCFT.normalizedValuation K y ↔
      ValuativeRel.valuation K (y : K) < ValuativeRel.valuation K (x : K) := by
  simpa only [not_le] using (normalizedValuation_le_iff' K y x).not

private theorem normalizedValuation_eq_zero_iff_valuation_eq_one'
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) :
    NU.LCFT.normalizedValuation K x = 0 ↔
      ValuativeRel.valuation K (x : K) = 1 := by
  have hone : NU.LCFT.normalizedValuation K (1 : Units K) = 0 := by
    simp [NU.LCFT.normalizedValuation]
  constructor
  · intro hx
    apply le_antisymm
    · have h := (normalizedValuation_le_iff' K (1 : Units K) x).1 (by rw [hone, hx])
      simpa only [Units.val_one, map_one] using h
    · have h := (normalizedValuation_le_iff' K x (1 : Units K)).1 (by rw [hone, hx])
      simpa only [Units.val_one, map_one] using h
  · intro hx
    apply le_antisymm
    · rw [← hone]
      apply (normalizedValuation_le_iff' K x (1 : Units K)).2
      simpa only [Units.val_one, map_one, hx, le_refl]
    · rw [← hone]
      apply (normalizedValuation_le_iff' K (1 : Units K) x).2
      simpa only [Units.val_one, map_one, hx, le_refl]

/-- Residual tame local-field calculation for an already identified cyclic
Kummer extension.  This is the ramification/residue-norm computation: every
norm is, up to a principal unit, an `ℓ`-th power times a power of the
radicand. -/
private theorem tame_cyclic_norm_factorization_core
    {Q R : Type*} [Field Q] [Field R]
    [Valued Q ℤᵐ⁰] [CompleteSpace Q]
    [(Valued.v : Valuation Q ℤᵐ⁰).IsRankOneDiscrete]
    [Finite (IsLocalRing.ResidueField (valuedIntegerRing Q))]
    [Algebra Q R] [FiniteDimensional Q R]
    {ℓ : ℕ} [Fact ℓ.Prime] [IsGalois Q R] [IsCyclic (R ≃ₐ[Q] R)]
    (hℓodd : Odd ℓ) (hres : valuedResidueCharacteristic Q ≠ ℓ)
    (ζ : Q) (hζ : IsPrimitiveRoot ζ ℓ) (a : Qˣ)
    (ha : principalUnitModEllClass (valuedIntegerRing Q) ℓ a ≠ 0)
    (α : R) (hαpow : α ^ ℓ = algebraMap Q R (a : Q))
    (hαgen : Algebra.adjoin Q ({α} : Set R) = ⊤)
    (hdegree : Module.finrank Q R = ℓ) :
    ∀ z : Rˣ, ∃ (m : ℕ) (q u : Qˣ),
      u ∈ (valuedIntegerRing Q).principalUnitGroup ∧
        Units.map (Algebra.norm Q) z = q ^ ℓ * a ^ m * u := by
  classical
  let vQ : Valuation Q ℤᵐ⁰ := Valued.v
  letI : vQ.RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (e := (2 : NNReal)) vQ (by norm_num)
  letI : NontriviallyNormedField Q :=
    Valued.toNontriviallyNormedField Q ℤᵐ⁰
  letI : IsDiscreteValuationRing (valuedIntegerRing Q) :=
    Valuation.valuationSubring_isDiscreteValuationRing vQ
  letI : IsDiscreteValuationRing (Valued.integer Q) := by
    change IsDiscreteValuationRing (valuedIntegerRing Q)
    infer_instance
  letI : Finite (Valued.ResidueField Q) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (valuedIntegerRing Q)))
  letI : ProperSpace Q :=
    (@Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      Q ℤᵐ⁰ _ _ _ _).2 ⟨inferInstance, inferInstance, inferInstance⟩
  letI : LocallyCompactSpace Q := by infer_instance
  letI : ValuativeRel Q := ValuativeRel.ofValuation vQ
  letI : vQ.Compatible := Valuation.Compatible.ofValuation vQ
  letI : IsValuativeTopology Q := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using vQ.exists_setOf_restrict_le_iff 0 s
  letI : ValuativeRel.IsNontrivial Q :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vQ).2 inferInstance
  letI : IsNonarchimedeanLocalField Q :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  letI : NontriviallyNormedField R :=
    spectralNorm.nontriviallyNormedField Q R
  letI : NormedSpace Q R := spectralNorm.normedSpace Q R
  letI : NormedAlgebra Q R := spectralNorm.normedAlgebra Q R
  letI : IsUltrametricDist R := ⟨by
    intro x y z
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    change spectralNorm Q R (x - z) ≤
      max (spectralNorm Q R (x - y)) (spectralNorm Q R (y - z))
    rw [show x - z = (x - y) + (y - z) by abel]
    exact isNonarchimedean_spectralNorm (K := Q) (L := R) _ _⟩
  let vR : Valuation R NNReal := NormedField.valuation
  letI : ValuativeRel R := ValuativeRel.ofValuation vR
  letI : vR.Compatible := Valuation.Compatible.ofValuation vR
  letI : Valued R NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation R NNReal).Compatible := by
    rw [show (Valued.v : Valuation R NNReal) = NormedField.valuation from rfl]
    infer_instance
  letI : IsValuativeTopology R := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using
      (Valued.v : Valuation R NNReal).exists_setOf_restrict_le_iff 0 s
  letI : ProperSpace R := FiniteDimensional.proper Q R
  letI : LocallyCompactSpace R := by infer_instance
  letI : ValuativeRel.IsNontrivial R :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vR).2 inferInstance
  letI : IsNonarchimedeanLocalField R :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  letI : ValuativeExtension Q R := ⟨by
    intro x y
    rw [Valuation.Compatible.vle_iff_le (v := vR),
      Valuation.Compatible.vle_iff_le (v := vQ)]
    change ‖algebraMap Q R x‖₊ ≤ ‖algebraMap Q R y‖₊ ↔ vQ x ≤ vQ y
    rw [← NNReal.coe_le_coe]
    change spectralNorm Q R (algebraMap Q R x) ≤
      spectralNorm Q R (algebraMap Q R y) ↔ vQ x ≤ vQ y
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff⟩
  letI : ContinuousSMul Q R := by infer_instance

  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (Fact.out : ℓ.Prime).ne_zero] at hαpow
    exact (map_ne_zero (algebraMap Q R)).2 a.ne_zero hαpow.symm
  let αu : Rˣ := Units.mk0 α hα0
  have hαunits : αu ^ ℓ = Units.map (algebraMap Q R) a := by
    apply Units.ext
    exact hαpow
  have hαint : IsIntegral Q α := by
    refine ⟨Polynomial.X ^ ℓ - Polynomial.C (a : Q),
      Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, ?_⟩
    simp [hαpow]
  let pb : PowerBasis Q R := PowerBasis.ofAdjoinEqTop hαint hαgen
  have hpgen : pb.gen = α := PowerBasis.ofAdjoinEqTop_gen hαint hαgen
  have hpdim : pb.dim = ℓ := by rw [← pb.finrank, hdegree]
  have hnoPow : ∀ x : Q, x ^ ℓ ≠ (a : Q) := by
    intro x hx
    apply ha
    by_cases hx0 : x = 0
    · subst x
      exact (a.ne_zero (by
        simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
    · change ModN.mkQ ℓ (Additive.ofMul
        (QuotientGroup.mk a : Qˣ ⧸ (valuedIntegerRing Q).principalUnitGroup)) = 0
      have hu : (Units.mk0 x hx0) ^ ℓ = a := by
        apply Units.ext
        simpa using hx
      rw [← hu]
      change ModN.mkQ ℓ (ℓ • Additive.ofMul
        (QuotientGroup.mk (Units.mk0 x hx0) :
          Qˣ ⧸ (valuedIntegerRing Q).principalUnitGroup)) = 0
      rw [map_nsmul]
      change (LinearMap.range (LinearMap.lsmul ℤ _ (ℓ : ℤ))).mkQ
        (ℓ • Additive.ofMul (QuotientGroup.mk (Units.mk0 x hx0) :
          Qˣ ⧸ (valuedIntegerRing Q).principalUnitGroup)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨Additive.ofMul (QuotientGroup.mk (Units.mk0 x hx0) :
        Qˣ ⧸ (valuedIntegerRing Q).principalUnitGroup), by simp⟩
  have hfmin : minpoly Q pb.gen = Polynomial.X ^ ℓ - Polynomial.C (a : Q) := by
    have hirr : Irreducible (Polynomial.X ^ ℓ - Polynomial.C (a : Q)) :=
      X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime) hnoPow
    exact (minpoly.eq_of_irreducible_of_monic hirr
      (by simp [hpgen, hαpow])
      (Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero)).symm
  have hnormα : Units.map (Algebra.norm Q) αu = a := by
    apply Units.ext
    change Algebra.norm Q α = (a : Q)
    rw [← hpgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hfmin, hpdim]
    have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    simp [hℓpos.ne, hℓodd.neg_one_pow]
  intro z
  let ordQ : Qˣ → ℤ := NU.LCFT.normalizedValuation Q
  let ordR : Rˣ → ℤ := NU.LCFT.normalizedValuation R
  let e := NU.LCFT.ramificationIndex Q R
  let f := NU.LCFT.residueDegree Q R
  have hαord : (ℓ : ℤ) * ordR αu = (e : ℤ) * ordQ a := by
    have h := congrArg ordR hαunits
    rw [show ordR (Units.map (algebraMap Q R) a) =
      (e : ℤ) * ordQ a by
        exact NU.LCFT.normalizedValuation_algebraMap Q R a] at h
    simpa [ordR, NU.LCFT.normalizedValuation] using h
  have hef : e * f = ℓ := by
    rw [← hdegree]
    exact (NU.LCFT.finrank_eq_ramificationIndex_mul_residueDegree Q R).symm
  by_cases hdiv : (ℓ : ℤ) ∣ ordQ a
  · obtain ⟨k, hk⟩ := hdiv
    obtain ⟨d, hd⟩ := NU.LCFT.normalizedValuation_surjective Q k
    have hd' : ordQ d = k := hd
    let b : Qˣ := a * (d ^ ℓ)⁻¹
    have hbord : ordQ b = 0 := by
      change NU.LCFT.normalizedValuation Q (a * (d ^ ℓ)⁻¹) = 0
      rw [NU.LCFT.normalizedValuation_mul]
      simp only [ordQ, NU.LCFT.normalizedValuation, map_inv, map_pow,
        toAdd_inv, toAdd_pow]
      change ordQ a + -(ℓ • ordQ d) = 0
      rw [hd', hk]
      simp [nsmul_eq_mul]
    let βu : Rˣ := αu * (Units.map (algebraMap Q R) d)⁻¹
    have hβunits : βu ^ ℓ = Units.map (algebraMap Q R) b := by
      rw [show βu = αu * (Units.map (algebraMap Q R) d)⁻¹ by rfl,
        mul_pow, hαunits]
      simp [b]
    have hℓz : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hβord : ordR βu = 0 := by
      have h := congrArg ordR hβunits
      have hmap : ordR (Units.map (algebraMap Q R) b) = (e : ℤ) * ordQ b :=
        NU.LCFT.normalizedValuation_algebraMap Q R b
      rw [hmap, hbord, mul_zero] at h
      have hpow : ordR (βu ^ ℓ) = (ℓ : ℤ) * ordR βu := by
        simp [ordR, NU.LCFT.normalizedValuation]
      rw [hpow] at h
      exact (mul_eq_zero.mp h).resolve_left hℓz
    let β : R := (βu : R)
    have hβ0 : β ≠ 0 := βu.ne_zero
    have hβpow : β ^ ℓ = algebraMap Q R (b : Q) := by
      exact congrArg Units.val hβunits
    have hβint : IsIntegral Q β := by
      refine ⟨Polynomial.X ^ ℓ - Polynomial.C (b : Q),
        Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, ?_⟩
      simp [hβpow]
    have hβgen : Algebra.adjoin Q ({β} : Set R) = ⊤ := by
      apply top_unique
      rw [← hαgen]
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      have hαβ : α = β * algebraMap Q R (d : Q) := by
        simp [β, βu, αu]
      rw [hαβ]
      exact (Algebra.adjoin Q ({β} : Set R)).mul_mem
        (Algebra.subset_adjoin (Set.mem_singleton β))
        ((Algebra.adjoin Q ({β} : Set R)).algebraMap_mem (d : Q))
    let pbβ : PowerBasis Q R := PowerBasis.ofAdjoinEqTop hβint hβgen
    have hpβgen : pbβ.gen = β := PowerBasis.ofAdjoinEqTop_gen hβint hβgen
    have hpβdim : pbβ.dim = ℓ := by rw [← pbβ.finrank, hdegree]
    have hbcan : ValuativeRel.valuation Q (b : Q) = 1 :=
      (normalizedValuation_eq_zero_iff_valuation_eq_one' Q b).1
        (by simpa [ordQ] using hbord)
    have hbval : vQ (b : Q) = 1 :=
      (ValuativeRel.isEquiv (ValuativeRel.valuation Q) vQ).eq_one_iff_eq_one.mp hbcan
    have hβcan : ValuativeRel.valuation R (βu : R) = 1 :=
      (normalizedValuation_eq_zero_iff_valuation_eq_one' R βu).1
        (by simpa [ordR] using hβord)
    let A := valuedIntegerRing Q
    let B := (ValuativeRel.valuation R).valuationSubring
    let intMap : A →+* B :=
      { toFun := fun x => ⟨algebraMap Q R (x : Q), by
          apply (Valuation.mem_valuationSubring_iff _ _).2
          apply (Valuation.Compatible.vle_iff_le
            (v := ValuativeRel.valuation R) (algebraMap Q R (x : Q)) 1).mp
          have hxprop := x.prop
          change vQ (x : Q) ≤ 1 at hxprop
          have hxQ : (x : Q) ≤ᵥ (1 : Q) :=
            (Valuation.Compatible.vle_iff_le (v := vQ) (x : Q) 1).mpr
              (by simpa only [map_one] using hxprop)
          simpa using
            (ValuativeExtension.vle_iff_vle (A := Q) (B := R) (x : Q) 1).2 hxQ⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp
        map_zero' := by ext; simp
        map_add' := by intro x y; ext; simp }
    letI : IsLocalHom intMap := by
      apply IsLocalHom.mk
      intro x hx
      rw [B.valuation_eq_one_iff] at hx
      rw [A.valuation_eq_one_iff]
      have hxcan : ValuativeRel.valuation R (algebraMap Q R (x : Q)) = 1 :=
        (Valuation.isEquiv_valuation_valuationSubring
          (ValuativeRel.valuation R)).eq_one_iff_eq_one.mpr hx
      have hxleR : algebraMap Q R (x : Q) ≤ᵥ (1 : R) :=
        (Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation R) (algebraMap Q R (x : Q)) 1).mpr
          (by simpa only [map_one] using hxcan.le)
      have hxgeR : (1 : R) ≤ᵥ algebraMap Q R (x : Q) :=
        (Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation R) 1 (algebraMap Q R (x : Q))).mpr
          (by simpa only [map_one] using hxcan.ge)
      have hxleQ : (x : Q) ≤ᵥ (1 : Q) :=
        (ValuativeExtension.vle_iff_vle (A := Q) (B := R) (x : Q) 1).mp
          (by simpa using hxleR)
      have hxgeQ : (1 : Q) ≤ᵥ (x : Q) :=
        (ValuativeExtension.vle_iff_vle (A := Q) (B := R) 1 (x : Q)).mp
          (by simpa using hxgeR)
      have hxvQ : vQ (x : Q) = 1 := by
        apply le_antisymm
        · simpa only [map_one] using
            (Valuation.Compatible.vle_iff_le (v := vQ) (x : Q) 1).mp hxleQ
        · simpa only [map_one] using
            (Valuation.Compatible.vle_iff_le (v := vQ) 1 (x : Q)).mp hxgeQ
      exact (Valuation.isEquiv_valuation_valuationSubring vQ).eq_one_iff_eq_one.mp hxvQ
    let kQ := IsLocalRing.ResidueField A
    let kR := IsLocalRing.ResidueField B
    let resMap : kQ →+* kR := IsLocalRing.ResidueField.map intMap
    letI : Algebra kQ kR := resMap.toAlgebra
    let bA : A := ⟨(b : Q), by
      change vQ (b : Q) ≤ 1
      exact hbval.le⟩
    have hbAunit : IsUnit bA :=
      (A.valuation_eq_one_iff bA).2
        ((Valuation.isEquiv_valuation_valuationSubring vQ).eq_one_iff_eq_one.mp hbval)
    let βB : B := ⟨β, by
      apply (Valuation.mem_valuationSubring_iff _ _).2
      exact hβcan.le⟩
    have hβBunit : IsUnit βB :=
      (B.valuation_eq_one_iff βB).2
        ((Valuation.isEquiv_valuation_valuationSubring
          (ValuativeRel.valuation R)).eq_one_iff_eq_one.mp hβcan)
    let bbar : kQ := IsLocalRing.residue A bA
    let βbar : kR := IsLocalRing.residue B βB
    have hbbar0 : bbar ≠ 0 := (hbAunit.map (IsLocalRing.residue A)).ne_zero
    have hβbar0 : βbar ≠ 0 := (hβBunit.map (IsLocalRing.residue B)).ne_zero
    let bbarU : kQˣ := Units.mk0 bbar hbbar0
    let βbarU : kRˣ := Units.mk0 βbar hβbar0
    have hβBpow : βB ^ ℓ = intMap bA := by
      apply Subtype.ext
      exact hβpow
    have hβbarpow : βbar ^ ℓ = algebraMap kQ kR bbar := by
      have h := congrArg (IsLocalRing.residue B) hβBpow
      rw [map_pow] at h
      calc
        βbar ^ ℓ = IsLocalRing.residue B (intMap bA) := h
        _ = resMap bbar := (IsLocalRing.ResidueField.map_residue intMap bA).symm
        _ = algebraMap kQ kR bbar := rfl
    let fbar : Polynomial kQ := Polynomial.X ^ ℓ - Polynomial.C bbar
    have hfbarroot : Polynomial.aeval βbar fbar = 0 := by
      simp [fbar, hβbarpow]
    have hbbarNoPow : ¬ ∃ y : kQ, y ^ ℓ = bbar := by
      rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        intro hy0
        rw [hy0, zero_pow (Fact.out : ℓ.Prime).ne_zero] at hy
        exact hbbar0 hy.symm
      let yu : kQˣ := Units.mk0 y hy0
      obtain ⟨xu, hxu⟩ := A.surjective_unitGroupToResidueFieldUnits yu
      let xq : Qˣ := (xu : Qˣ)
      have hxgroup : xq ∈ A.unitGroup := xu.prop
      have hbgroup : b ∈ A.unitGroup := by
        rw [A.mem_unitGroup_iff]
        exact (Valuation.isEquiv_valuation_valuationSubring vQ).eq_one_iff_eq_one.mp hbval
      let bu : A.unitGroup := ⟨b, hbgroup⟩
      have hbu : A.unitGroupToResidueFieldUnits bu = bbarU := by
        apply Units.ext
        rfl
      let u : Qˣ := b * (xq ^ ℓ)⁻¹
      have hugroup : u ∈ A.unitGroup :=
        A.unitGroup.mul_mem hbgroup (A.unitGroup.inv_mem (A.unitGroup.pow_mem hxgroup ℓ))
      let uA : A.unitGroup := ⟨u, hugroup⟩
      have hures : A.unitGroupToResidueFieldUnits uA = 1 := by
        change A.unitGroupToResidueFieldUnits bu *
          (A.unitGroupToResidueFieldUnits xu ^ ℓ)⁻¹ = 1
        rw [hbu, hxu]
        have hyu : yu ^ ℓ = bbarU := by
          apply Units.ext
          exact hy
        rw [hyu]
        simp
      have huker : uA ∈ A.unitGroupToResidueFieldUnits.ker :=
        MonoidHom.mem_ker.mpr hures
      rw [A.ker_unitGroupToResidueFieldUnits] at huker
      have hu : u ∈ A.principalUnitGroup := by
        change u ∈ A.principalUnitGroup at huker
        exact huker
      have hfac : a = (d * xq) ^ ℓ * u := by
        simp only [u, b, mul_pow]
        symm
        calc
          d ^ ℓ * xq ^ ℓ * (a * (d ^ ℓ)⁻¹ * (xq ^ ℓ)⁻¹) =
              a * (d ^ ℓ * (d ^ ℓ)⁻¹) * (xq ^ ℓ * (xq ^ ℓ)⁻¹) := by ac_rfl
          _ = a := by simp
      exact ha (principalUnitModEllClass_eq_zero_of_factor A ℓ a (d * xq) u hu hfac)
    have hfbar : Irreducible fbar := by
      apply X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime)
      intro y hy
      exact hbbarNoPow ⟨y, hy⟩
    have hminβbar : minpoly kQ βbar = fbar :=
      (minpoly.eq_of_irreducible_of_monic hfbar hfbarroot
        (Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero)).symm
    let c : Fin pbβ.dim → Q := fun i => pbβ.basis.repr (z : R) i
    let support : Finset (Fin pbβ.dim) := Finset.univ.filter fun i => c i ≠ 0
    have hsupport : support.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hc : ∀ i, c i = 0 := by
        intro i
        by_contra hi
        have : i ∈ support := by simp [support, hi]
        simpa [hempty] using this
      have hrepr : pbβ.basis.repr (z : R) = 0 := by
        ext i
        simpa [c] using hc i
      have hz0 : (z : R) = 0 := by
        apply pbβ.basis.repr.injective
        simpa using hrepr
      exact z.ne_zero hz0
    let cOrd : Fin pbβ.dim → ℤ := fun i =>
      if hi : c i = 0 then 0 else ordQ (Units.mk0 (c i) hi)
    obtain ⟨s, hs, hsmin⟩ := Finset.exists_min_image support cOrd hsupport
    have hcs : c s ≠ 0 := by simpa [support] using hs
    let cs : Qˣ := Units.mk0 (c s) hcs
    let diQ : Fin pbβ.dim → Q := fun i => c i / c s
    have hdi_mem (i : Fin pbβ.dim) : vQ (diQ i) ≤ 1 := by
      by_cases hci : c i = 0
      · simp [diQ, hci]
      · have hmin : ordQ cs ≤ ordQ (Units.mk0 (c i) hci) := by
          have hmin' := hsmin i (by simp [support, hci])
          rw [show cOrd s = ordQ cs by simp [cOrd, hcs, cs],
            show cOrd i = ordQ (Units.mk0 (c i) hci) by simp [cOrd, hci]] at hmin'
          exact hmin'
        have hcan := (normalizedValuation_le_iff' Q cs (Units.mk0 (c i) hci)).1
          (by simpa [ordQ] using hmin)
        have hraw : vQ (c i) ≤ vQ (c s) :=
          (ValuativeRel.isEquiv (ValuativeRel.valuation Q) vQ).le_iff_le.mp hcan
        change vQ (c i / c s) ≤ 1
        rw [map_div₀]
        exact (div_le_one₀ ((vQ).pos_iff.mpr hcs)).2 hraw
    let diA : Fin pbβ.dim → A := fun i => ⟨diQ i, hdi_mem i⟩
    have hdi_s : diA s = 1 := by
      apply Subtype.ext
      simp [diA, diQ, hcs]
    let z0 : Rˣ := z * (Units.map (algebraMap Q R) cs)⁻¹
    let z0B : B := ∑ i, intMap (diA i) * βB ^ (i : ℕ)
    have hsum : ∑ i, algebraMap Q R (c i) * β ^ (i : ℕ) = (z : R) := by
      simpa [c, PowerBasis.coe_basis, hpβgen, Algebra.smul_def] using
        pbβ.basis.sum_repr (z : R)
    have hz0Bsum : (z0B : R) =
        ∑ i, algebraMap Q R (diQ i) * β ^ (i : ℕ) := by
      simp [z0B, intMap, diA, βB, β]
    have hz0val : (z0 : R) =
        (z : R) * (algebraMap Q R (c s))⁻¹ := by
      simp [z0, cs]
    have hz0B : (z0B : R) = (z0 : R) := by
      rw [hz0Bsum, hz0val, ← hsum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [diQ, map_div₀]
      field_simp [hcs]
    let pbar : Polynomial kQ := ∑ i : Fin pbβ.dim,
      Polynomial.C (IsLocalRing.residue A (diA i)) * Polynomial.X ^ (i : ℕ)
    have hpeval : Polynomial.aeval βbar pbar = IsLocalRing.residue B z0B := by
      change Polynomial.eval₂ (algebraMap kQ kR) βbar pbar = _
      rw [show pbar = ∑ i : Fin pbβ.dim,
        Polynomial.C (IsLocalRing.residue A (diA i)) *
          Polynomial.X ^ (i : ℕ) by rfl,
        Polynomial.eval₂_finset_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, map_mul, map_pow]
      rw [show algebraMap kQ kR (IsLocalRing.residue A (diA i)) =
        resMap (IsLocalRing.residue A (diA i)) by rfl,
        IsLocalRing.ResidueField.map_residue]
    have hpcoeff : pbar.coeff (s : ℕ) = 1 := by
      rw [show pbar = ∑ i : Fin pbβ.dim,
        Polynomial.C (IsLocalRing.residue A (diA i)) *
          Polynomial.X ^ (i : ℕ) by rfl]
      change Polynomial.lcoeff kQ (s : ℕ) (∑ i : Fin pbβ.dim,
        Polynomial.C (IsLocalRing.residue A (diA i)) *
          Polynomial.X ^ (i : ℕ)) = 1
      rw [map_sum]
      rw [Finset.sum_eq_single s]
      · simp [hdi_s]
      · intro i _ his
        have hnat : (s : ℕ) ≠ (i : ℕ) := fun h => his (Fin.ext h.symm)
        simp [hnat]
      · simp
    have hpnonzero : pbar ≠ 0 := by
      intro hp0
      rw [hp0, Polynomial.coeff_zero] at hpcoeff
      exact zero_ne_one hpcoeff
    have hpdeg : pbar.natDegree < ℓ := by
      have hle : pbar.natDegree ≤ ℓ - 1 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro i _
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
          (Nat.le_pred_of_lt (by simpa [hpβdim] using i.isLt))
      exact hle.trans_lt (Nat.pred_lt (Fact.out : ℓ.Prime).ne_zero)
    have hpnotroot : Polynomial.aeval βbar pbar ≠ 0 := by
      intro hp0
      have hdvd := minpoly.dvd kQ βbar hp0
      rw [hminβbar] at hdvd
      have hle := Polynomial.natDegree_le_of_dvd hdvd hpnonzero
      have hfdeg : fbar.natDegree = ℓ := by simp [fbar]
      rw [hfdeg] at hle
      exact (not_le_of_gt hpdeg) hle
    have hz0res : IsLocalRing.residue B z0B ≠ 0 := by
      rw [← hpeval]
      exact hpnotroot
    have hz0Bunit : IsUnit z0B :=
      IsLocalRing.notMem_maximalIdeal.mp fun hzmem =>
        hz0res ((IsLocalRing.residue_eq_zero_iff z0B).2 hzmem)
    have hz0Bval : B.valuation (z0B : R) = 1 :=
      (B.valuation_eq_one_iff z0B).1 hz0Bunit
    have hz0can : ValuativeRel.valuation R (z0 : R) = 1 := by
      rw [← hz0B]
      exact (Valuation.isEquiv_valuation_valuationSubring
        (ValuativeRel.valuation R)).eq_one_iff_eq_one.mpr hz0Bval
    have hz0ord : ordR z0 = 0 := by
      apply (normalizedValuation_eq_zero_iff_valuation_eq_one' R z0).2
      exact hz0can
    let nz : Qˣ := Units.map (Algebra.norm Q) z0
    have hnord : ordQ nz = 0 := by
      change NU.LCFT.normalizedValuation Q (NU.LCFT.normUnitsHom Q R z0) = 0
      rw [NU.LCFT.normalizedValuation_norm]
      change (f : ℤ) * ordR z0 = 0
      rw [hz0ord, mul_zero]
    have hncan : ValuativeRel.valuation Q (nz : Q) = 1 :=
      (normalizedValuation_eq_zero_iff_valuation_eq_one' Q nz).1
        (by simpa [ordQ] using hnord)
    have hnval : vQ (nz : Q) = 1 := by
      exact (ValuativeRel.isEquiv (ValuativeRel.valuation Q) vQ).eq_one_iff_eq_one.mp hncan
    have hnGroup : nz ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      exact (Valuation.isEquiv_valuation_valuationSubring vQ).eq_one_iff_eq_one.mp hnval
    let nzA : A.unitGroup := ⟨nz, hnGroup⟩
    let nbar : kQˣ := A.unitGroupToResidueFieldUnits nzA
    have hbbarUNoPow : ¬ ∃ y : kQˣ, y ^ ℓ = bbarU := by
      rintro ⟨y, hy⟩
      apply hbbarNoPow
      refine ⟨(y : kQ), ?_⟩
      exact congrArg Units.val hy
    obtain ⟨m, qbar, hqbar⟩ :=
      cyclic_pow_factorization (ℓ := ℓ) bbarU hbbarUNoPow nbar
    obtain ⟨qA, hqA⟩ := A.surjective_unitGroupToResidueFieldUnits qbar
    let q : Qˣ := (qA : Qˣ)
    have hqGroup : q ∈ A.unitGroup := qA.prop
    have hbGroup : b ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      exact (Valuation.isEquiv_valuation_valuationSubring vQ).eq_one_iff_eq_one.mp hbval
    let bAunit : A.unitGroup := ⟨b, hbGroup⟩
    have hbAres : A.unitGroupToResidueFieldUnits bAunit = bbarU := by
      apply Units.ext
      rfl
    let u : Qˣ := nz * (q ^ ℓ * b ^ m)⁻¹
    have huGroup : u ∈ A.unitGroup :=
      A.unitGroup.mul_mem hnGroup (A.unitGroup.inv_mem
        (A.unitGroup.mul_mem (A.unitGroup.pow_mem hqGroup ℓ)
          (A.unitGroup.pow_mem hbGroup m)))
    let uA : A.unitGroup := ⟨u, huGroup⟩
    have huRes : A.unitGroupToResidueFieldUnits uA = 1 := by
      change A.unitGroupToResidueFieldUnits nzA *
        (A.unitGroupToResidueFieldUnits (qA ^ ℓ * bAunit ^ m))⁻¹ = 1
      rw [show A.unitGroupToResidueFieldUnits nzA = nbar by rfl,
        map_mul, map_pow, map_pow, hqA, hbAres, hqbar]
      simp
    have huKer : uA ∈ A.unitGroupToResidueFieldUnits.ker :=
      MonoidHom.mem_ker.mpr huRes
    rw [A.ker_unitGroupToResidueFieldUnits] at huKer
    have hu : u ∈ A.principalUnitGroup := by
      change u ∈ A.principalUnitGroup at huKer
      exact huKer
    have hnfac : nz = q ^ ℓ * b ^ m * u := by
      simp only [u]
      symm
      calc
        q ^ ℓ * b ^ m * (nz * (q ^ ℓ * b ^ m)⁻¹) =
            nz * ((q ^ ℓ * b ^ m) * (q ^ ℓ * b ^ m)⁻¹) := by ac_rfl
        _ = nz := by simp
    have hnormcs : Units.map (Algebra.norm Q)
        (Units.map (algebraMap Q R).toMonoidHom cs) = cs ^ ℓ := by
      apply Units.ext
      change Algebra.norm Q (algebraMap Q R (cs : Q)) = ((cs ^ ℓ : Qˣ) : Q)
      rw [Algebra.norm_algebraMap, hdegree]
      rfl
    have hnz : nz = Units.map (Algebra.norm Q) z * (cs ^ ℓ)⁻¹ := by
      rw [show nz = Units.map (Algebra.norm Q) z0 by rfl,
        show z0 = z * (Units.map (algebraMap Q R) cs)⁻¹ by rfl,
        map_mul, map_inv]
      exact congrArg (fun t : Qˣ => Units.map (Algebra.norm Q) z * t⁻¹) hnormcs
    let qt : Qˣ := cs * q * (d ^ m)⁻¹
    refine ⟨m, qt, u, hu, ?_⟩
    have hnormz : Units.map (Algebra.norm Q) z = cs ^ ℓ * nz := by
      rw [hnz]
      symm
      calc
        cs ^ ℓ * (Units.map (Algebra.norm Q) z * (cs ^ ℓ)⁻¹) =
            Units.map (Algebra.norm Q) z * (cs ^ ℓ * (cs ^ ℓ)⁻¹) := by ac_rfl
        _ = Units.map (Algebra.norm Q) z := by simp
    rw [hnormz, hnfac]
    simp only [qt, b, mul_pow]
    have hdpow : ((d ^ ℓ)⁻¹) ^ m = ((d ^ m)⁻¹) ^ ℓ := by
      simp only [inv_pow]
      calc
        ((d ^ ℓ) ^ m)⁻¹ = (d ^ (ℓ * m))⁻¹ :=
          congrArg Inv.inv (pow_mul d ℓ m).symm
        _ = (d ^ (m * ℓ))⁻¹ := by rw [mul_comm]
        _ = ((d ^ m) ^ ℓ)⁻¹ := congrArg Inv.inv (pow_mul d m ℓ)
    rw [hdpow]
    simp only [mul_assoc]
    rw [mul_left_comm (a ^ m) (((d ^ m)⁻¹) ^ ℓ) u]
  · have he_dvd : e ∣ ℓ := ⟨f, hef.symm⟩
    have he_cases : e = 1 ∨ e = ℓ :=
      (Fact.out : ℓ.Prime).eq_one_or_self_of_dvd e he_dvd
    have he : e = ℓ := by
      rcases he_cases with he | he
      · exfalso
        apply hdiv
        refine ⟨ordR αu, ?_⟩
        simpa [he] using hαord.symm
      · exact he
    have hℓz : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hαord' : ordR αu = ordQ a := by
      apply mul_left_cancel₀ hℓz
      simpa [he] using hαord
    let c : Fin pb.dim → Q := fun i => pb.basis.repr (z : R) i
    let support : Finset (Fin pb.dim) := Finset.univ.filter fun i => c i ≠ 0
    have hsupport : support.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hc : ∀ i, c i = 0 := by
        intro i
        by_contra hi
        have : i ∈ support := by simp [support, hi]
        simpa [hempty] using this
      have hrepr : pb.basis.repr (z : R) = 0 := by
        ext i
        simpa [c] using hc i
      have hz0 : (z : R) = 0 := by
        apply pb.basis.repr.injective
        simpa using hrepr
      exact z.ne_zero hz0
    let score : Fin pb.dim → ℤ := fun i =>
      if hi : c i = 0 then 0 else
        (ℓ : ℤ) * ordQ (Units.mk0 (c i) hi) + (i : ℤ) * ordQ a
    obtain ⟨s, hs, hsmin⟩ := Finset.exists_min_image support score hsupport
    have hcs : c s ≠ 0 := by simpa [support] using hs
    let cs : Qˣ := Units.mk0 (c s) hcs
    let lead : Rˣ := Units.map (algebraMap Q R) cs * αu ^ (s : ℕ)
    have haMod : (ordQ a : ZMod ℓ) ≠ 0 := by
      rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hscore_ne {i j : Fin pb.dim} (hi : c i ≠ 0) (hj : c j ≠ 0)
        (hij : i ≠ j) : score i ≠ score j := by
      intro heq
      have heqz := congrArg (fun n : ℤ => (n : ZMod ℓ)) heq
      dsimp [score] at heqz
      rw [dif_neg hi, dif_neg hj] at heqz
      push_cast at heqz
      have hcast : (i.val : ZMod ℓ) * (ordQ a : ZMod ℓ) =
          (j.val : ZMod ℓ) * (ordQ a : ZMod ℓ) := by
        simpa using heqz
      have hijcast : (i.val : ZMod ℓ) = (j.val : ZMod ℓ) :=
        mul_right_cancel₀ haMod hcast
      have hijmod : i.val ≡ j.val [MOD ℓ] :=
        (ZMod.natCast_eq_natCast_iff i.val j.val ℓ).mp hijcast
      apply hij
      apply Fin.ext
      apply Nat.ModEq.eq_of_lt_of_lt hijmod
      · simpa [hpdim] using i.isLt
      · simpa [hpdim] using j.isLt
    let term : Fin pb.dim → R := fun i => algebraMap Q R (c i) * α ^ (i : ℕ)
    have hsum : ∑ i, term i = (z : R) := by
      simpa [term, c, PowerBasis.coe_basis, hpgen, Algebra.smul_def] using
        pb.basis.sum_repr (z : R)
    have hterm_ord (i : Fin pb.dim) (hi : c i ≠ 0) :
        ordR (Units.map (algebraMap Q R) (Units.mk0 (c i) hi) * αu ^ (i : ℕ)) =
          score i := by
      change NU.LCFT.normalizedValuation R
        (Units.map (algebraMap Q R) (Units.mk0 (c i) hi) * αu ^ (i : ℕ)) = _
      rw [NU.LCFT.normalizedValuation_mul,
        NU.LCFT.normalizedValuation_algebraMap]
      have hpow : NU.LCFT.normalizedValuation R (αu ^ (i : ℕ)) =
          (i : ℤ) * ordR αu := by
        simp [ordR, NU.LCFT.normalizedValuation]
      rw [hpow]
      change (e : ℤ) * ordQ (Units.mk0 (c i) hi) +
        (i : ℤ) * ordR αu = score i
      rw [he, hαord']
      simp [score, hi]
    have hsord : ordR lead = score s := by
      simpa [lead, cs] using hterm_ord s hcs
    have hterm_lt : ∀ i ∈ Finset.univ \ {s},
        ValuativeRel.valuation R (term i) < ValuativeRel.valuation R (lead : R) := by
      intro i hi
      have hi' := Finset.mem_sdiff.mp hi
      have his : i ≠ s := by simpa using hi'.2
      by_cases hci : c i = 0
      · have hlead0 : (lead : R) ≠ 0 := lead.ne_zero
        simp [term, hci, hlead0, (ValuativeRel.valuation R).pos_iff]
      · let ti : Rˣ := Units.map (algebraMap Q R) (Units.mk0 (c i) hci) *
          αu ^ (i : ℕ)
        have hiord : ordR ti = score i := hterm_ord i hci
        have hsi_le : score s ≤ score i :=
          hsmin i (by simp [support, hci])
        have hsi : score s < score i :=
          lt_of_le_of_ne hsi_le (hscore_ne hcs hci his.symm)
        have hord : ordR lead < ordR ti := by rw [hsord, hiord]; exact hsi
        have hv := (normalizedValuation_lt_iff' R lead ti).1 (by
          simpa [ordR] using hord)
        simpa [term, ti, lead, cs, αu] using hv
    have hterms : term s = (lead : R) := by
      simp [term, lead, cs, αu]
    have hsplit : (z : R) = (lead : R) +
        ∑ i ∈ Finset.univ \ {s}, term i := by
      rw [← hsum]
      simpa [hterms] using
        (Finset.sum_eq_add_sum_sdiff_singleton_of_mem
          (s := Finset.univ) (i := s) (Finset.mem_univ s) term)
    let rest : R := ∑ i ∈ Finset.univ \ {s}, term i
    have hrest : ValuativeRel.valuation R rest <
        ValuativeRel.valuation R (lead : R) := by
      apply Valuation.map_sum_lt
      · exact (ValuativeRel.valuation R).ne_zero_iff.mpr lead.ne_zero
      · exact hterm_lt
    let w : Rˣ := z * lead⁻¹
    have hwsub : (w : R) - 1 = rest * (lead : R)⁻¹ := by
      dsimp [w]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hsplit]
      field_simp [lead.ne_zero]
      dsimp [rest]
      abel
    have hwsmall : ValuativeRel.valuation R ((w : R) - 1) < 1 := by
      rw [hwsub, map_mul, map_inv₀]
      change ValuativeRel.valuation R rest /
          ValuativeRel.valuation R (lead : R) < 1
      rw [div_lt_one₀ ((ValuativeRel.valuation R).pos_iff.mpr lead.ne_zero)]
      exact hrest
    let B := (ValuativeRel.valuation R).valuationSubring
    have hequivR : (ValuativeRel.valuation R).IsEquiv vR :=
      ValuativeRel.isEquiv _ _
    have hwsmall_vR : vR ((w : R) - 1) < 1 := by
      simpa only [map_one] using hequivR.lt_iff_lt.mp hwsmall
    let ws : (R ≃ₐ[Q] R) → Rˣ := fun σ =>
      Units.map σ.toRingEquiv.toMonoidHom w
    have hws : ∀ σ, ws σ ∈ B.principalUnitGroup := by
      intro σ
      rw [B.mem_principalUnitGroup_iff]
      apply (Valuation.isEquiv_valuation_valuationSubring
        (ValuativeRel.valuation R)).lt_iff_lt.mp
      apply hequivR.lt_iff_lt.mpr
      have heq : ((ws σ : R) - 1) = σ ((w : R) - 1) := by
        simp [ws]
      rw [heq]
      dsimp [vR]
      simp only [nnnorm_one]
      change ‖σ ((w : R) - 1)‖₊ < 1
      rw [← NNReal.coe_lt_coe]
      change spectralNorm Q R (σ ((w : R) - 1)) < 1
      rw [← spectralNorm_eq_of_equiv σ]
      exact_mod_cast hwsmall_vR
    let pw : Rˣ := ∏ σ, ws σ
    have hpw : pw ∈ B.principalUnitGroup := by
      apply B.principalUnitGroup.prod_mem
      intro σ _
      exact hws σ
    let nw : Qˣ := Units.map (Algebra.norm Q) w
    let embU : Qˣ →* Rˣ := Units.map (algebraMap Q R)
    have hemb : embU nw = pw := by
      apply Units.ext
      simpa [embU, nw, pw, ws] using
        (Algebra.norm_eq_prod_automorphisms Q (w : R))
    have hnwp : embU nw ∈ B.principalUnitGroup := hemb ▸ hpw
    have hnwB := (B.mem_principalUnitGroup_iff (embU nw)).mp hnwp
    have hnwcan : ValuativeRel.valuation R (((embU nw : R) - 1)) < 1 :=
      (Valuation.isEquiv_valuation_valuationSubring
        (ValuativeRel.valuation R)).lt_iff_lt.mpr hnwB
    have hnwvR : vR (((embU nw : R) - 1)) < 1 := by
      simpa only [map_one] using hequivR.lt_iff_lt.mp hnwcan
    have hnwnormR : ‖algebraMap Q R ((nw : Q) - 1)‖ < 1 := by
      have hnwvR' : ‖((embU nw : R) - 1)‖₊ < 1 := hnwvR
      rw [← NNReal.coe_lt_coe] at hnwvR'
      simpa [embU] using hnwvR'
    have hnwnormQ : ‖(nw : Q) - 1‖ < 1 := by
      change spectralNorm Q R (algebraMap Q R ((nw : Q) - 1)) < 1 at hnwnormR
      rw [spectralNorm_extends] at hnwnormR
      exact hnwnormR
    have hnwvQ : vQ ((nw : Q) - 1) < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mp hnwnormQ
    have hnwpA : nw ∈ (valuedIntegerRing Q).principalUnitGroup := by
      rw [(valuedIntegerRing Q).mem_principalUnitGroup_iff]
      apply (Valuation.isEquiv_valuation_valuationSubring vQ).lt_iff_lt.mp
      simpa only [map_one] using hnwvQ
    have hzfac : z = lead * w := by simp [w]
    have hnormlead : Units.map (Algebra.norm Q) lead = cs ^ ℓ * a ^ (s : ℕ) := by
      rw [show lead = Units.map (algebraMap Q R) cs * αu ^ (s : ℕ) by rfl,
        map_mul, map_pow, hnormα]
      congr 1
      apply Units.ext
      change Algebra.norm Q (algebraMap Q R (cs : Q)) = ((cs ^ ℓ : Qˣ) : Q)
      rw [Algebra.norm_algebraMap, hdegree]
      rfl
    refine ⟨s, cs, nw, hnwpA, ?_⟩
    calc
      Units.map (Algebra.norm Q) z =
          Units.map (Algebra.norm Q) (lead * w) := by rw [hzfac]
      _ = Units.map (Algebra.norm Q) lead * nw := by rw [map_mul]
      _ = cs ^ ℓ * a ^ (s : ℕ) * nw := by rw [hnormlead]

/-- Blueprint Lemma 5.3 (`lem:tame-norm-line`): in a complete discretely
valued field with finite residue field, every norm class lies on the line
spanned by the Kummer radicand. -/
theorem tame_norm_line {Q R : Type*} [Field Q] [Field R]
    [Valued Q ℤᵐ⁰] [CompleteSpace Q]
    [(Valued.v : Valuation Q ℤᵐ⁰).IsRankOneDiscrete]
    [Finite (IsLocalRing.ResidueField (valuedIntegerRing Q))]
    [Algebra Q R] [FiniteDimensional Q R]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (hres : valuedResidueCharacteristic Q ≠ ℓ)
    (ζ : Q) (hζ : IsPrimitiveRoot ζ ℓ) (a : Qˣ)
    (ha : principalUnitModEllClass (valuedIntegerRing Q) ℓ a ≠ 0)
    (hR : IsKummerRadicalExtension Q R ℓ a) :
    ∀ z : Rˣ,
      principalUnitModEllClass (valuedIntegerRing Q) ℓ
          (Units.map (Algebra.norm Q) z) ∈
        Submodule.span (ZMod ℓ)
          {principalUnitModEllClass (valuedIntegerRing Q) ℓ a} := by
  obtain ⟨α, hαpow, hαgen, hdegree⟩ := hR
  have hnoPow : ∀ x : Q, x ^ ℓ ≠ (a : Q) := by
    intro x hx
    apply ha
    by_cases hx0 : x = 0
    · subst x
      exact (Units.ne_zero a (by
        simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
    · apply principalUnitModEllClass_eq_zero_of_pow'
        (valuedIntegerRing Q) ℓ a (Units.mk0 x hx0)
      apply Units.ext
      simpa using hx
  let f : Polynomial Q := Polynomial.X ^ ℓ - Polynomial.C (a : Q)
  have hf : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime) hnoPow
  letI : Fact (Irreducible f) := ⟨hf⟩
  have hprim : (primitiveRoots ℓ Q).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (Fact.out : ℓ.Prime).pos).2 hζ⟩
  letI : Polynomial.IsSplittingField Q R f := by
    constructor
    · change (Polynomial.X ^ ℓ - Polynomial.C (a : Q)).map
          (algebraMap Q R) |>.Splits
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot
        (hζ.map_of_injective (algebraMap Q R).injective) hαpow
    · apply top_unique
      rw [← hαgen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff]
      change α ∈ f.rootSet R
      rw [Polynomial.mem_rootSet_of_ne (Irreducible.ne_zero hf)]
      simp [f, hαpow]
  letI : IsGalois Q R :=
    isGalois_of_isSplittingField_X_pow_sub_C hprim hf R
  letI : IsCyclic (R ≃ₐ[Q] R) :=
    isCyclic_of_isSplittingField_X_pow_sub_C hprim hf R
  intro z
  obtain ⟨m, q, u, hu, hfactor⟩ :=
    tame_cyclic_norm_factorization_core hℓodd hres ζ hζ a ha α hαpow
      hαgen hdegree z
  have hq : principalUnitModEllClass (valuedIntegerRing Q) ℓ (q ^ ℓ) = 0 :=
    principalUnitModEllClass_eq_zero_of_pow'
      (valuedIntegerRing Q) ℓ (q ^ ℓ) q rfl
  have hu' : principalUnitModEllClass (valuedIntegerRing Q) ℓ u = 0 :=
    principalUnitModEllClass_eq_zero_of_mem' (valuedIntegerRing Q) ℓ u hu
  rw [hfactor, principalUnitModEllClass_mul',
    principalUnitModEllClass_mul', hq, principalUnitModEllClass_pow', hu',
    zero_add, add_zero]
  exact (Submodule.span (ZMod ℓ)
    {principalUnitModEllClass (valuedIntegerRing Q) ℓ a}).nsmul_mem
      (Submodule.subset_span (Set.mem_singleton _)) m

/-- Norms commute with the completion/base-change map in the Kummer
situation.  This is the exact compatibility used by the global-to-local
argument. -/
theorem norm_completion_compatibility
    {M E Eᵥ : Type*} [Field M] [Field E] [Field Eᵥ]
    [NumberField M] [Algebra M E] [FiniteDimensional M E]
    (v : FinitePlace M) [Algebra (v.adicCompletion M) Eᵥ]
    [FiniteDimensional (v.adicCompletion M) Eᵥ]
    (j : E →+* Eᵥ)
    (hj : j.comp (algebraMap M E) =
      (algebraMap (v.adicCompletion M) Eᵥ).comp
        (NumberField.FinitePlace.embedding v))
    (hgen : Algebra.adjoin (v.adicCompletion M) (Set.range j) = ⊤)
    (hdegree : Module.finrank M E =
      Module.finrank (v.adicCompletion M) Eᵥ)
    (z : Eˣ) :
    algebraMap M (v.adicCompletion M) (Algebra.norm M (z : E)) =
      Algebra.norm (v.adicCompletion M)
        (Units.map j.toMonoidHom z : Eᵥ) := by
  let K := v.adicCompletion M
  letI : Algebra M Eᵥ :=
    RingHom.toAlgebra ((algebraMap K Eᵥ).comp
      (NumberField.FinitePlace.embedding v))
  letI : IsScalarTower M K Eᵥ := IsScalarTower.of_algebraMap_eq' rfl
  let jAlg : E →ₐ[M] Eᵥ :=
    { j with
      commutes' := fun x => DFunLike.congr_fun hj x }
  let φ : K ⊗[M] E →ₐ[K] Eᵥ :=
    Algebra.TensorProduct.lift (Algebra.ofId K Eᵥ) jAlg
      (fun _ _ => Commute.all _ _)
  have hφsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro x ⟨y, rfl⟩
    refine ⟨(1 : K) ⊗ₜ[M] y, ?_⟩
    simp [φ, jAlg]
  have hdim : Module.finrank K (K ⊗[M] E) = Module.finrank K Eᵥ := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdegree]
  have hφinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hφsurj
  let e : K ⊗[M] E ≃ₐ[K] Eᵥ := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have he_apply : e (1 ⊗ₜ[M] (z : E)) = j (z : E) := by
    simp [e, φ, jAlg]
  have hbase : Algebra.norm K (1 ⊗ₜ[M] (z : E) : K ⊗[M] E) =
      algebraMap M K (Algebra.norm M (z : E)) := by
    rw [Algebra.norm_apply, ← Algebra.baseChange_lmul,
      LinearMap.det_baseChange]
    rfl
  change algebraMap M K (Algebra.norm M (z : E)) =
    Algebra.norm K (j (z : E))
  rw [← he_apply, Algebra.norm_eq_of_algEquiv e, hbase]

private def completionIntegerHom'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    primeValuationSubring v →+* v.adicCompletionIntegers M where
  toFun x := ⟨NumberField.FinitePlace.embedding v (x : M), by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [NumberField.FinitePlace.embedding_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    let w := v.valuation M
    have hA : primeValuationSubring v = w.valuationSubring :=
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
    have hx : (x : M) ∈ w.valuationSubring := hA ▸ x.prop
    exact hx⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private instance completionIntegerHom_isLocal'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    IsLocalHom (completionIntegerHom' v) := by
  apply IsLocalHom.mk
  intro x hx
  let w := v.valuation M
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  rw [B.valuation_eq_one_iff] at hx
  rw [A.valuation_eq_one_iff]
  have hA : A = w.valuationSubring :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
  have hequivGlobal : w.IsEquiv A.valuation := by
    rw [hA]
    exact Valuation.isEquiv_valuation_valuationSubring w
  apply hequivGlobal.eq_one_iff_eq_one.mp
  have hequivLocal :
      (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰).IsEquiv B.valuation := by
    exact Valuation.isEquiv_valuation_valuationSubring _
  have hraw : Valued.v (NumberField.FinitePlace.embedding v (x : M)) = 1 :=
    hequivLocal.eq_one_iff_eq_one.mpr hx
  rw [NumberField.FinitePlace.embedding_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hraw
  exact hraw

private theorem ringChar_eq_of_fieldHom' {k l : Type*} [Field k] [Field l]
    (f : k →+* l) : ringChar k = ringChar l := by
  apply Nat.dvd_antisymm
  · apply ringChar.dvd
    apply f.injective
    simpa only [map_natCast, map_zero] using
      (CharP.cast_eq_zero l (ringChar l))
  · apply ringChar.dvd
    rw [← map_natCast f, CharP.cast_eq_zero k (ringChar k), map_zero]

private def completionResidueMap'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    IsLocalRing.ResidueField (primeValuationSubring v) →+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers M) :=
  IsLocalRing.ResidueField.map (completionIntegerHom' v)

private theorem completionResidueMap_surjective'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    Function.Surjective (completionResidueMap' v) := by
  intro y
  obtain ⟨b, rfl⟩ :=
    (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers M)) y
  let K := v.adicCompletion M
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  have hopen : Metric.ball (b : K) 1 ∈ nhds (b : K) :=
    Metric.ball_mem_nhds _ zero_lt_one
  obtain ⟨x, hxball⟩ :=
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap M v).mem_nhds hopen
  have hxdiffnorm : ‖algebraMap M K x - (b : K)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hxball
  have hxdiff : Valued.v (algebraMap M K x - (b : K)) < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mp hxdiffnorm
  have hbraw : Valued.v (b : K) ≤ 1 := b.prop
  have hxraw : Valued.v (algebraMap M K x) ≤ 1 := by
    rw [show algebraMap M K x = (algebraMap M K x - (b : K)) + b by abel]
    exact (Valued.v.map_add _ _).trans (max_le hxdiff.le hbraw)
  have hembalg : NumberField.FinitePlace.embedding v x = algebraMap M K x := by
    rw [NumberField.FinitePlace.embedding_apply]
    rfl
  have hxglobal : (v.valuation M) x ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
      ← NumberField.FinitePlace.embedding_apply, hembalg]
    exact hxraw
  have hA : A = (v.valuation M).valuationSubring :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
  have hxA : x ∈ A := by
    rw [hA]
    exact hxglobal
  let xa : A := ⟨x, hxA⟩
  refine ⟨IsLocalRing.residue A xa, ?_⟩
  rw [completionResidueMap', IsLocalRing.ResidueField.map_residue]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    B.valuation_lt_one_iff]
  apply (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation K ℤᵐ⁰)).lt_iff_lt.mp
  simpa [completionIntegerHom', xa, hembalg] using hxdiff

private noncomputable def quotientEquivResidueFieldAt'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    (𝓞 M ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (primeValuationSubring v) := by
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)

private theorem residueFieldAt_finite'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    Finite (IsLocalRing.ResidueField (primeValuationSubring v)) :=
  Finite.of_equiv (𝓞 M ⧸ v.asIdeal)
    (quotientEquivResidueFieldAt' v).toEquiv

private theorem completion_residueCharacteristic_eq'
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    valuedResidueCharacteristic (v.adicCompletion M) = residueCharacteristic v := by
  let f := completionResidueMap' v
  change ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers M)) =
    ringChar (IsLocalRing.ResidueField (primeValuationSubring v))
  exact (ringChar_eq_of_fieldHom' f).symm

private theorem not_pairIndependent_zero_left'
    {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    {x y : V} (hx : x = 0) : ¬PairIndependent (k := k) x y := by
  intro h
  have h' := (linearIndependent_fin2.mp h).2 0
  apply h'
  simp [pairVector, hx]

private theorem not_pairIndependent_of_eq_smul'
    {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    {x y : V} (c : k) (hy : y = c • x) :
    ¬PairIndependent (k := k) x y := by
  intro h
  have h' : y ≠ 0 ∧ ∀ a : k, a • y ≠ x := by
    simpa [pairVector] using linearIndependent_fin2.mp h
  by_cases hc : c = 0
  · apply h'.1
    rw [hy, hc, zero_smul]
  · apply h'.2 c⁻¹
    rw [hy, ← mul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Blueprint Lemma 5.4 (`lem:global-norm-local-line`): a global norm and
its Kummer radicand have linearly dependent images in the tame local
principal-unit quotient. -/
theorem global_norm_local_line {M E : Type*} [Field M] [Field E]
    [NumberField M] [Algebra M E] [FiniteDimensional M E]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (hE : IsKummerRadicalExtension M E ℓ a)
    (hNorm : IsUnitNorm M E b) (v : FinitePlace M)
    (hv : residueCharacteristic v ≠ ℓ) :
    ¬PairIndependent (k := ZMod ℓ)
      (principalUnitModEllClass (primeValuationSubring v) ℓ a)
      (principalUnitModEllClass (primeValuationSubring v) ℓ b) := by
  let A := primeValuationSubring v
  let K := v.adicCompletion M
  let B := v.adicCompletionIntegers M
  let emb : M →+* K := NumberField.FinitePlace.embedding v
  let aK : Kˣ := Units.map emb.toMonoidHom a
  let bK : Kˣ := Units.map emb.toMonoidHom b
  let xa := principalUnitModEllClass A ℓ a
  let xb := principalUnitModEllClass A ℓ b
  by_cases ha0 : xa = 0
  · exact not_pairIndependent_zero_left' ha0
  obtain ⟨eq, heq⟩ := completion_quotient (ℓ := ℓ) v
  have heqa : eq xa = principalUnitModEllClass B ℓ aK := by
    simpa [A, B, emb, aK, xa] using heq a
  have heqb : eq xb = principalUnitModEllClass B ℓ bK := by
    simpa [A, B, emb, bK, xb] using heq b
  have haK : principalUnitModEllClass B ℓ aK ≠ 0 := by
    rw [← heqa]
    exact fun h => ha0 (eq.injective (h.trans (map_zero eq).symm))
  have hnoPow : ∀ x : K, x ^ ℓ ≠ (aK : K) := by
    intro x hx
    apply haK
    by_cases hx0 : x = 0
    · subst x
      exact (Units.ne_zero aK (by
        simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
    · apply principalUnitModEllClass_eq_zero_of_pow' B ℓ aK (Units.mk0 x hx0)
      apply Units.ext
      simpa using hx
  let fK : Polynomial K := Polynomial.X ^ ℓ - Polynomial.C (aK : K)
  have hfK : Irreducible fK :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime) hnoPow
  letI : Fact (Irreducible fK) := ⟨hfK⟩
  let R := AdjoinRoot fK
  letI : Field R := inferInstance
  letI : Algebra K R := inferInstance
  letI : FiniteDimensional K R :=
    (AdjoinRoot.powerBasis (Irreducible.ne_zero hfK)).finite
  have hrootK : (AdjoinRoot.root fK : R) ^ ℓ =
      algebraMap K R (aK : K) := by
    simpa [R, fK] using root_X_pow_sub_C_pow ℓ (aK : K)
  have hRK : IsKummerRadicalExtension K R ℓ aK := by
    refine ⟨AdjoinRoot.root fK, hrootK, AdjoinRoot.adjoinRoot_eq_top, ?_⟩
    rw [(AdjoinRoot.powerBasis (Irreducible.ne_zero hfK)).finrank]
    simp [fK]
  obtain ⟨α, hαpow, hαgen, hEdegree⟩ := hE
  let fM : Polynomial M := Polynomial.X ^ ℓ - Polynomial.C (a : M)
  have hfMroot : Polynomial.aeval α fM = 0 := by
    simp [fM, hαpow]
  have hfM : Irreducible fM := by
    apply X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime)
    intro x hx
    apply hnoPow (emb x)
    simpa [aK, emb] using congrArg emb hx
  have hαint : IsIntegral M α :=
    ⟨fM, Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero,
      hfMroot⟩
  let pb : PowerBasis M E := PowerBasis.ofAdjoinEqTop hαint hαgen
  have hpgen : pb.gen = α := PowerBasis.ofAdjoinEqTop_gen hαint hαgen
  have hfMmin : fM = minpoly M pb.gen := by
    apply minpoly.eq_of_irreducible_of_monic hfM
    · simpa [hpgen] using hfMroot
    · exact Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero
  have hminroot : Polynomial.aeval (AdjoinRoot.root fM)
      (minpoly M pb.gen) = 0 := by
    rw [← hfMmin]
    simpa [Polynomial.aeval_def] using AdjoinRoot.eval₂_root fM
  have hpbroot : Polynomial.aeval pb.gen fM = 0 := by
    simpa [hpgen] using hfMroot
  let eME : AdjoinRoot fM ≃ₐ[M] E :=
    AdjoinRoot.equiv' fM pb hminroot hpbroot
  let iMR : M →+* R := (algebraMap K R).comp emb
  have hfMRroot : Polynomial.eval₂ iMR (AdjoinRoot.root fK) fM = 0 := by
    simp only [fM, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change (AdjoinRoot.root fK : R) ^ ℓ - iMR (a : M) = 0
    apply sub_eq_zero.mpr
    rw [hrootK]
    simp [iMR, aK, emb]
  let baseLift : AdjoinRoot fM →+* R :=
    AdjoinRoot.lift iMR (AdjoinRoot.root fK) hfMRroot
  let j : E →+* R := baseLift.comp eME.symm.toRingEquiv.toRingHom
  have hj : j.comp (algebraMap M E) =
      (algebraMap K R).comp emb := by
    ext x
    simp [j, baseLift, iMR, eME]
  have heMEroot : eME (AdjoinRoot.root fM) = α := by
    simp [eME, pb, hpgen]
  have hjα : j α = AdjoinRoot.root fK := by
    rw [← heMEroot]
    simp [j, baseLift]
  have hjgen : Algebra.adjoin K (Set.range j) = ⊤ := by
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := fK)]
    apply Algebra.adjoin_mono
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨α, hjα⟩
  have hdegree : Module.finrank M E = Module.finrank K R := by
    rw [hEdegree, (AdjoinRoot.powerBasis (Irreducible.ne_zero hfK)).finrank]
    simp [fK]
  obtain ⟨z, hz⟩ := hNorm
  let zR : Rˣ := Units.map j.toMonoidHom z
  have hnormcomp := norm_completion_compatibility v j hj hjgen hdegree z
  have hnormunits : Units.map (Algebra.norm K) zR = bK := by
    apply Units.ext
    change Algebra.norm K (j (z : E)) = emb (b : M)
    calc
      Algebra.norm K (j (z : E)) =
          algebraMap M K (Algebra.norm M (z : E)) := by
        simpa [K, zR] using hnormcomp.symm
      _ = emb (b : M) := by rw [hz]; rfl
  letI : Finite (IsLocalRing.ResidueField (primeValuationSubring v)) :=
    residueFieldAt_finite' v
  letI : Finite (IsLocalRing.ResidueField (valuedIntegerRing K)) := by
    change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers M))
    exact Finite.of_surjective (completionResidueMap' v)
      (completionResidueMap_surjective' v)
  letI : CompleteSpace K := inferInstance
  letI : (Valued.v : Valuation K ℤᵐ⁰).IsRankOneDiscrete := inferInstance
  have hresK : valuedResidueCharacteristic K ≠ ℓ := by
    rw [completion_residueCharacteristic_eq' v]
    exact hv
  have hζK : IsPrimitiveRoot (emb ζ) ℓ := hζ.map_of_injective emb.injective
  have hline := tame_norm_line hℓodd hresK (emb ζ) hζK aK haK hRK zR
  rw [hnormunits] at hline
  rw [Submodule.mem_span_singleton] at hline
  obtain ⟨c, hc⟩ := hline
  have hglobal : xb = c • xa := by
    apply eq.injective
    rw [eq.map_smul, heqa, heqb]
    exact hc.symm
  exact not_pairIndependent_of_eq_smul' c hglobal

end

end NU.LocalTheory
