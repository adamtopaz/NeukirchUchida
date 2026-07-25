import Submission.NU.LocalTheory.Main
import Submission.NU.Chebotarev.FieldCrossing
import Submission.NU.LCFT.FundamentalClass.DeepUnits
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.NumberTheory.Padics.AddChar

/-!
# Deep principal units as a finite-rank `Z_p`-module

This file is a standalone proving target for the complete-PID/deep-unit input
to local invariant recovery.  In particular, it does not import
`NU.NeukirchUchida.LocalInvariants`.
-/

open scoped NumberField ValuativeRel WithZero

namespace NU.NeukirchUchida.Bridges

noncomputable section

open NU.LCFT

/-- A bundled prime supplies the `Fact` instance required by `PadicInt`. -/
instance natPrimesFact (p : Nat.Primes) : Fact (p : ℕ).Prime :=
  ⟨p.2⟩

/-- The local degree `e(v/ℚ) f(v/ℚ)` attached to a finite place. -/
noncomputable def finitePlaceLocalDegree
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) : ℕ :=
  v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ) *
    v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ)

/-- Density identifies the residue field of a number-field completion with
the residue field at the original finite prime. -/
private noncomputable def completionResidueEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    ((𝓞 K) ⧸ v.asIdeal) ≃+*
      Valued.ResidueField (v.adicCompletion K) := by
  let F := v.adicCompletion K
  let A := NU.LocalTheory.primeValuationSubring v
  let B := v.adicCompletionIntegers K
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Algebra (𝓞 K) A :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let eA := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A
  letI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_equiv ((𝓞 K) ⧸ v.asIdeal) eA.toEquiv
  let emb : K →+* F := algebraMap K F
  have hemb_mem (a : A) : emb (a : K) ∈ B := by
    rw [show B = v.adicCompletionIntegers K from rfl,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((a : K) : F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have ha : (a : K) ∈ (v.valuation K).valuationSubring := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact a.property
    exact ha
  let f : A →+* B := RingHom.codRestrict
    (emb.comp A.subtype) B hemb_mem
  have hfmax : IsLocalRing.maximalIdeal A ≤
      Ideal.comap f (IsLocalRing.maximalIdeal B) := by
    intro a ha
    rw [Ideal.mem_comap, B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v ((f a : B) : F) < Valued.v (1 : F)
    rw [map_one]
    have ha' : v.valuation K (a : K) < 1 := by
      have hA : A = (v.valuation K).valuationSubring :=
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
      let ea : A ≃+* (v.valuation K).valuationSubring :=
        RingEquiv.subringCongr
          (congrArg (fun W : ValuationSubring K => W.toSubring) hA)
      have hea : ea a ∈ IsLocalRing.maximalIdeal
          ((v.valuation K).valuationSubring) := by
        change a ∈ IsLocalRing.maximalIdeal A at ha
        simpa [ea] using ha
      exact (Valuation.mem_maximalIdeal_iff K
        (v := v.valuation K)).mp hea
    change Valued.v ((a : K) : F) < 1
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  letI : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 3 0).mp hfmax
  let rf : IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField B := IsLocalRing.ResidueField.map f
  have hrf : Function.Surjective rf := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    have hopen : Metric.ball (b : F) 1 ∈ nhds (b : F) :=
      Metric.ball_mem_nhds _ zero_lt_one
    obtain ⟨x, hx⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).mem_nhds
        hopen
    have hxclose : ‖algebraMap K F x - (b : F)‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hvclose : Valued.v (algebraMap K F x - (b : F)) < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mp hxclose
    have hxcoe : (x : F) = algebraMap K F x := rfl
    have hvclose' : Valued.v ((x : F) - (b : F)) < 1 := by
      rw [hxcoe]
      exact hvclose
    have hxint : v.valuation K x ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      rw [show (x : F) = ((x : F) - (b : F)) + (b : F) by ring]
      exact Valuation.map_add_le _ hvclose'.le b.property
    let a : A := ⟨x, by
      rw [show A = (v.valuation K).valuationSubring from
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v]
      exact hxint⟩
    refine ⟨IsLocalRing.residue A a, ?_⟩
    rw [show rf = IsLocalRing.ResidueField.map f from rfl,
      IsLocalRing.ResidueField.map_residue]
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
      B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v (((f a : B) - b : B) : F) < Valued.v (1 : F)
    rw [map_one]
    change Valued.v ((x : F) - (b : F)) < 1
    exact hvclose'
  let er : IsLocalRing.ResidueField A ≃+*
      IsLocalRing.ResidueField B :=
    RingEquiv.ofBijective rf ⟨rf.injective, hrf⟩
  exact eA.trans er

/-- In particular, the residue field of a number-field completion is finite. -/
private theorem completionResidueFinite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv ((𝓞 K) ⧸ v.asIdeal)
    (completionResidueEquiv v).toEquiv

/-- The canonical valuation relation on a number-field completion. -/
@[reducible] private noncomputable def completionValuativeRel
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion K) _)

/-- A number-field completion, with its canonical valuation relation, is a
nonarchimedean local field. -/
private theorem completionIsLocalField
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    completionResidueFinite v
  letI : ProperSpace (v.adicCompletion K) :=
    (@Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (v.adicCompletion K) _ _ _ _).2 ⟨inferInstance, inferInstance, inferInstance⟩
  letI : LocallyCompactSpace (v.adicCompletion K) := by infer_instance
  let vF := (Valued.v : Valuation (v.adicCompletion K) _)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  letI : IsValuativeTopology (v.adicCompletion K) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using vF.exists_setOf_restrict_le_iff 0 s
  letI : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vF).2 inferInstance
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The residue cardinality of the completion is the absolute norm of the
finite prime. -/
private theorem completionResidueCard_eq_norm
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    residueCard (v.adicCompletion K) =
      NU.Chebotarev.PrimeIdeal.norm v := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  let vF := (Valued.v : Valuation F _)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  have hv : (ValuativeRel.valuation F).IsEquiv vF :=
    ValuativeRel.isEquiv _ _
  have hsub : (ValuativeRel.valuation F).valuationSubring =
      vF.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mp hv
  let eR : (ValuativeRel.valuation F).valuationSubring ≃+*
      vF.valuationSubring :=
    RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring hsub)
  let ek : LocalResidueField F ≃+* Valued.ResidueField F :=
    IsLocalRing.ResidueField.mapEquiv eR
  rw [residueCard, NU.Chebotarev.PrimeIdeal.norm,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (ek.toEquiv.trans (completionResidueEquiv v).toEquiv.symm)

/-- Residue characteristic is the norm of the prime contracted to `ℤ`. -/
private theorem residueCharacteristic_eq_absNorm_under
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.residueCharacteristic v =
      Ideal.absNorm (Ideal.under ℤ v.asIdeal) := by
  letI : Algebra (𝓞 K) (NU.LocalTheory.primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (NU.LocalTheory.primeValuationSubring v)
  calc
    NU.LocalTheory.residueCharacteristic v =
        ringChar ((𝓞 K) ⧸ v.asIdeal) := by
      rw [NU.LocalTheory.residueCharacteristic, ringChar.eq_iff]
      exact (e.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 K) ⧸ v.asIdeal))
    _ = Ideal.absNorm (Ideal.under ℤ v.asIdeal) :=
      Ideal.ringChar_quot v.asIdeal

/-- At a rational place, residue characteristic equals ideal norm. -/
private theorem rational_residueCharacteristic_eq_norm
    (q : NU.LocalTheory.FinitePlace ℚ) :
    NU.LocalTheory.residueCharacteristic q =
      NU.Chebotarev.PrimeIdeal.norm q := by
  letI : q.asIdeal.IsMaximal := q.isMaximal
  let J : Ideal ℤ := Ideal.map Rat.ringOfIntegersEquiv q.asIdeal
  letI : J.IsMaximal :=
    Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv
  letI : Field ((𝓞 ℚ) ⧸ q.asIdeal) :=
    Ideal.Quotient.field q.asIdeal
  letI : Field (ℤ ⧸ J) := Ideal.Quotient.field J
  let e : ((𝓞 ℚ) ⧸ q.asIdeal) ≃+* (ℤ ⧸ J) :=
    Ideal.quotientEquiv q.asIdeal J Rat.ringOfIntegersEquiv rfl
  have hchar : ringChar ((𝓞 ℚ) ⧸ q.asIdeal) =
      ringChar (ℤ ⧸ J) := by
    rw [ringChar.eq_iff]
    exact (e.toRingHom.charP_iff_charP _).mpr
      (ringChar.charP (ℤ ⧸ J))
  have hJunder : Ideal.under ℤ J = J := by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap]
    rfl
  have hnormJ : ringChar (ℤ ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.ringChar_quot, hJunder]
  have hnorm : Ideal.absNorm J = Ideal.absNorm q.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr e.symm.toEquiv
  calc
    NU.LocalTheory.residueCharacteristic q =
        ringChar ((𝓞 ℚ) ⧸ q.asIdeal) := by
      rw [NU.LocalTheory.residueCharacteristic, ringChar.eq_iff]
      letI : Algebra (𝓞 ℚ)
          (NU.LocalTheory.primeValuationSubring q) :=
        show Algebra (𝓞 ℚ)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ q) from
            inferInstance
      letI : IsLocalization.AtPrime
          (NU.LocalTheory.primeValuationSubring q) q.asIdeal :=
        show IsLocalization.AtPrime
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ q)
            q.asIdeal from inferInstance
      let eq := IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal
        (NU.LocalTheory.primeValuationSubring q)
      exact (eq.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 ℚ) ⧸ q.asIdeal))
    _ = ringChar (ℤ ⧸ J) := hchar
    _ = Ideal.absNorm J := hnormJ
    _ = Ideal.absNorm q.asIdeal := hnorm
    _ = NU.Chebotarev.PrimeIdeal.norm q := rfl

/-- Restriction of a number-field place preserves residue characteristic. -/
private theorem residueCharacteristic_restrictFinitePlace
    (K : Type*) {L : Type*}
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : NU.LocalTheory.FinitePlace L) :
    NU.LocalTheory.residueCharacteristic
        (NU.LocalTheory.restrictFinitePlace K v) =
      NU.LocalTheory.residueCharacteristic v := by
  rw [residueCharacteristic_eq_absNorm_under,
    residueCharacteristic_eq_absNorm_under,
    NU.LocalTheory.restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

/-- At a rational place, the residue characteristic is its positive prime
integer generator. -/
private theorem rational_residueCharacteristic_eq_natGenerator
    (q : NU.LocalTheory.FinitePlace ℚ) :
    NU.LocalTheory.residueCharacteristic q =
      Rat.HeightOneSpectrum.natGenerator q := by
  rw [residueCharacteristic_eq_absNorm_under]
  have halg : algebraMap ℤ (𝓞 ℚ) =
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom := by
    ext n
    simp only [algebraMap_int_eq, eq_intCast, map_intCast,
      Rat.IsIntegralClosure.intEquiv,
      NumberField.RingOfIntegers.equiv, IsIntegralClosure.equiv,
      IsIntegralClosure.lift, IsIntegralClosure.mk', algebraMap.coe_inj,
      Classical.choose_eq, AlgEquiv.symm_toRingEquiv,
      RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.symm_toEquiv_eq_symm, AlgEquiv.symm_symm,
      RingEquiv.toRingHom_eq_coe]
  have hunder : Ideal.under ℤ q.asIdeal =
      Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)} := by
    rw [Ideal.under_def, halg]
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    calc
      Ideal.comap e.symm.toRingHom q.asIdeal =
          Ideal.map e.toRingHom q.asIdeal := Ideal.comap_symm e
      _ = Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)} :=
        (Rat.HeightOneSpectrum.span_natGenerator q).symm
  rw [hunder, Ideal.absNorm_span_singleton]
  simp

/-- The residue characteristic is coprime to one less than the residue
norm. -/
private theorem residueCharacteristic_coprime_norm_sub_one
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    (p : ℕ).Coprime (NU.Chebotarev.PrimeIdeal.norm v - 1) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hnorm : NU.Chebotarev.PrimeIdeal.norm v =
      NU.Chebotarev.PrimeIdeal.norm q ^
        q.asIdeal.inertiaDeg v.asIdeal := by
    exact NU.Chebotarev.PrimeIdeal.norm_pow_inertiaDeg
      v q inferInstance
  have hq : NU.Chebotarev.PrimeIdeal.norm q =
      NU.LocalTheory.residueCharacteristic v := by
    rw [← rational_residueCharacteristic_eq_norm,
      residueCharacteristic_restrictFinitePlace]
  have hf : 0 < q.asIdeal.inertiaDeg v.asIdeal :=
    Ideal.inertiaDeg_pos q.asIdeal v.asIdeal
  rw [hnorm, hq, ← hp]
  have hpow : ((p : ℕ) ^ q.asIdeal.inertiaDeg v.asIdeal).Coprime
      ((p : ℕ) ^ q.asIdeal.inertiaDeg v.asIdeal - 1) :=
    (Nat.coprime_self_sub_right (pow_pos p.2.pos _)).2
      (Nat.coprime_one_right _)
  exact (Nat.coprime_pow_left_iff hf _ _).mp hpow

/-- The rational prime indexed by a restricted place is its residue
characteristic. -/
private theorem rationalPrimeOfPlace_eq
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    (Rat.HeightOneSpectrum.primesEquiv q : ℕ) =
      NU.LocalTheory.residueCharacteristic v := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  change Rat.HeightOneSpectrum.natGenerator q = _
  rw [← rational_residueCharacteristic_eq_natGenerator q,
    residueCharacteristic_restrictFinitePlace]

/-- The map between adic completions induced by restriction of a finite
place. -/
private noncomputable def rationalCompletionMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    q.adicCompletion ℚ →+* v.adicCompletion K := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let f : WithVal (q.valuation ℚ) →+* WithVal (v.valuation K) :=
    algebraMap _ _
  have hf : UniformContinuous f :=
    IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
      ℚ K q v
  exact UniformSpace.Completion.mapRingHom f hf.continuous

@[simp] private theorem rationalCompletionMap_algebraMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (x : ℚ) :
    rationalCompletionMap v
        (algebraMap ℚ
          ((NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletion ℚ) x) =
      algebraMap ℚ (v.adicCompletion K) x := by
  simpa only [eq_ratCast] using map_ratCast (rationalCompletionMap v) x

private theorem continuous_rationalCompletionMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Continuous (rationalCompletionMap v) := by
  exact UniformSpace.Completion.continuous_map

/-- The completed valuation at the restricted rational place is the
restriction of the completed valuation at `v`. -/
private theorem rationalCompletionMap_hasExtension
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
      (rationalCompletionMap v).toAlgebra
    (Valued.v : Valuation (q.adicCompletion ℚ) ℤᵐ⁰).HasExtension
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
    (rationalCompletionMap v).toAlgebra
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change rationalCompletionMap v x ∈
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer ↔
    x ∈ (Valued.v : Valuation (q.adicCompletion ℚ) ℤᵐ⁰).integer
  let A : Set (q.adicCompletion ℚ) :=
    (Valued.v : Valuation (q.adicCompletion ℚ) ℤᵐ⁰).integer
  let B : Set (v.adicCompletion K) :=
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer
  let f : q.adicCompletion ℚ → v.adicCompletion K :=
    rationalCompletionMap v
  have hclosed : IsClosed {y | y ∈ A ↔ f y ∈ B} := by
    have hA : IsClopen A := Valued.isClopen_integer _
    have hB : IsClopen B := Valued.isClopen_integer _
    have hf : Continuous f := continuous_rationalCompletionMap v
    rw [show {y | y ∈ A ↔ f y ∈ B} =
        (A ∩ f ⁻¹' B) ∪ (Aᶜ ∩ f ⁻¹' Bᶜ) by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_compl_iff]
      tauto]
    exact ((hA.inter (hB.preimage hf)).union
      (hA.compl.inter (hB.compl.preimage hf))).isClosed
  rw [iff_comm]
  change x ∈ A ↔ f x ∈ B
  refine DenseRange.induction_on (q.denseRange_algebraMap ℚ) x hclosed ?_
  intro a
  change (algebraMap ℚ (q.adicCompletion ℚ) a ∈ A ↔
    f (algebraMap ℚ (q.adicCompletion ℚ) a) ∈ B)
  rw [show f (algebraMap ℚ (q.adicCompletion ℚ) a) =
      algebraMap ℚ (v.adicCompletion K) a from
    rationalCompletionMap_algebraMap v a]
  change Valued.v (algebraMap ℚ (q.adicCompletion ℚ) a) ≤ 1 ↔
    Valued.v (algebraMap ℚ (v.adicCompletion K) a) ≤ 1
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K q v a]
  exact (pow_le_one_iff (M := ℤᵐ⁰)
    (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
      v.asIdeal q.ne_bot)).symm

/-- In `ℤᵐ⁰`, being strictly below one is the same as being at most
the largest element below one. -/
private theorem withZeroMulInt_lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  cases x with
  | zero => simp
  | coe a =>
      change WithZero.exp (Multiplicative.toAdd a) < WithZero.exp 0 ↔
        WithZero.exp (Multiplicative.toAdd a) ≤ WithZero.exp (-1 : ℤ)
      rw [WithZero.exp_lt_exp, WithZero.exp_le_exp]
      omega

/-- The extension of completed rational fields is finite. -/
private theorem rationalCompletionMap_module_finite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
      (rationalCompletionMap v).toAlgebra
    Module.Finite (q.adicCompletion ℚ) (v.adicCompletion K) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
    (rationalCompletionMap v).toAlgebra
  letI : ContinuousSMul (q.adicCompletion ℚ) (v.adicCompletion K) :=
    ⟨by
      have h := ((continuous_rationalCompletionMap v).comp continuous_fst).mul
        continuous_snd
      change Continuous fun z : q.adicCompletion ℚ × v.adicCompletion K =>
        rationalCompletionMap v z.1 * z.2
      convert h using 1
      rfl⟩
  letI : IsScalarTower ℚ (q.adicCompletion ℚ) (v.adicCompletion K) :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (rationalCompletionMap_algebraMap v x).symm
  infer_instance

/-- The valuation-subring extension of the completed rational fields is
finite. -/
private theorem rationalCompletionIntegers_module_finite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
      (rationalCompletionMap v).toAlgebra
    letI : (Valued.v : Valuation (q.adicCompletion ℚ) ℤᵐ⁰).HasExtension
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) :=
      rationalCompletionMap_hasExtension v
    letI : Algebra (q.adicCompletionIntegers ℚ)
        (v.adicCompletionIntegers K) :=
      Valuation.HasExtension.instAlgebraInteger
    Module.Finite (q.adicCompletionIntegers ℚ)
      (v.adicCompletionIntegers K) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  let Fb := q.adicCompletion ℚ
  let F := v.adicCompletion K
  letI : Algebra Fb F := (rationalCompletionMap v).toAlgebra
  letI : ContinuousSMul Fb F :=
    ⟨by
      have h := ((continuous_rationalCompletionMap v).comp continuous_fst).mul
        continuous_snd
      change Continuous fun z : Fb × F => rationalCompletionMap v z.1 * z.2
      convert h using 1
      rfl⟩
  letI : IsScalarTower ℚ Fb F :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (rationalCompletionMap_algebraMap v x).symm
  letI : Module.Finite Fb F := rationalCompletionMap_module_finite v
  letI : (Valued.v : Valuation Fb ℤᵐ⁰).HasExtension
      (Valued.v : Valuation F ℤᵐ⁰) :=
    rationalCompletionMap_hasExtension v
  letI : Algebra (q.adicCompletionIntegers ℚ)
      (v.adicCompletionIntegers K) :=
    Valuation.HasExtension.instAlgebraInteger
  letI : ValuativeRel Fb := completionValuativeRel q
  letI : ValuativeRel F := completionValuativeRel v
  let vFb := (Valued.v : Valuation Fb ℤᵐ⁰)
  let vF := (Valued.v : Valuation F ℤᵐ⁰)
  letI : vFb.Compatible := Valuation.Compatible.ofValuation vFb
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  letI : IsNonarchimedeanLocalField Fb := completionIsLocalField q
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  letI : ValuativeExtension Fb F := ⟨fun a b => by
    rw [Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation F),
      Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation Fb),
      (ValuativeRel.isEquiv (ValuativeRel.valuation F) vF).le_iff_le,
      (ValuativeRel.isEquiv (ValuativeRel.valuation Fb) vFb).le_iff_le]
    exact Valuation.HasExtension.val_map_le_iff vFb vF a b⟩
  letI : (ValuativeRel.valuation Fb).HasExtension
      (ValuativeRel.valuation F) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  have hfin : Module.Finite (RingOfIntegers Fb) (RingOfIntegers F) :=
    ringOfIntegers_module_finite Fb F
  have hFb : (ValuativeRel.valuation Fb).valuationSubring =
      vFb.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mp
      (ValuativeRel.isEquiv (ValuativeRel.valuation Fb) vFb)
  have hF : (ValuativeRel.valuation F).valuationSubring =
      vF.valuationSubring :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mp
      (ValuativeRel.isEquiv (ValuativeRel.valuation F) vF)
  let eFb : (ValuativeRel.valuation Fb).valuationSubring ≃+*
      vFb.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hFb)
  let eF : (ValuativeRel.valuation F).valuationSubring ≃+*
      vF.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hF)
  letI : Module.Finite
      ((ValuativeRel.valuation Fb).valuationSubring)
      ((ValuativeRel.valuation F).valuationSubring) := hfin
  exact Module.Finite.of_equiv_equiv eFb eF (by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    change ((algebraMap vFb.valuationSubring vF.valuationSubring
        (eFb x) : vF.valuationSubring) : F) =
      ((eF (algebraMap
        (ValuativeRel.valuation Fb).valuationSubring
        (ValuativeRel.valuation F).valuationSubring x) :
          vF.valuationSubring) : F)
    rw [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]
    rw [show ((eFb x : vFb.valuationSubring) : Fb) = (x : Fb) by
      exact RingEquiv.coe_subringCongr_apply _ _]
    rw [show ((eF (algebraMap
          (ValuativeRel.valuation Fb).valuationSubring
          (ValuativeRel.valuation F).valuationSubring x) :
            vF.valuationSubring) : F) =
        ((algebraMap
          (ValuativeRel.valuation Fb).valuationSubring
          (ValuativeRel.valuation F).valuationSubring x :
            (ValuativeRel.valuation F).valuationSubring) : F) by
      exact RingEquiv.coe_subringCongr_apply _ _]
    exact (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
      (ValuativeRel.valuation Fb) (ValuativeRel.valuation F) x).symm)

set_option maxHeartbeats 800000

/-- The degree of the extension of completions is the usual local degree
of the finite place. -/
private theorem rationalCompletion_finrank_eq_localDegree
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
      (rationalCompletionMap v).toAlgebra
    Module.finrank (q.adicCompletion ℚ) (v.adicCompletion K) =
      finitePlaceLocalDegree v := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  let Fb := q.adicCompletion ℚ
  let F := v.adicCompletion K
  letI : Algebra Fb F := (rationalCompletionMap v).toAlgebra
  letI : ContinuousSMul Fb F :=
    ⟨by
      have h := ((continuous_rationalCompletionMap v).comp continuous_fst).mul
        continuous_snd
      change Continuous fun z : Fb × F => rationalCompletionMap v z.1 * z.2
      convert h using 1
      rfl⟩
  letI : IsScalarTower ℚ Fb F :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (rationalCompletionMap_algebraMap v x).symm
  letI : Module.Finite Fb F := rationalCompletionMap_module_finite v
  let vFb := (Valued.v : Valuation Fb ℤᵐ⁰)
  let vF := (Valued.v : Valuation F ℤᵐ⁰)
  let A := vFb.valuationSubring
  let B := vF.valuationSubring
  letI : vFb.HasExtension vF := rationalCompletionMap_hasExtension v
  letI : Algebra A B := Valuation.HasExtension.instAlgebraInteger
  letI : IsScalarTower A Fb F :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring vFb
  letI : IsScalarTower A B F :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring' vFb vF
  letI : Module.Finite A B :=
    rationalCompletionIntegers_module_finite v
  let pA : Ideal A := IsLocalRing.maximalIdeal A
  let pB : Ideal B := IsLocalRing.maximalIdeal B
  letI : pA.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : pB.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  letI : Field (A ⧸ pA) := Ideal.Quotient.field pA
  letI : Field (B ⧸ pB) := Ideal.Quotient.field pB
  letI : pB.LiesOver pA := ⟨by
    ext x
    exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
      vFb vF).symm⟩
  letI : Algebra (A ⧸ pA) (B ⧸ pB) :=
    Ideal.Quotient.algebraOfLiesOver pB pA
  have hcardA : Nat.card (A ⧸ pA) =
      NU.Chebotarev.PrimeIdeal.norm q := by
    rw [NU.Chebotarev.PrimeIdeal.norm, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (completionResidueEquiv q).toEquiv).symm
  have hcardB : Nat.card (B ⧸ pB) =
      NU.Chebotarev.PrimeIdeal.norm v := by
    rw [NU.Chebotarev.PrimeIdeal.norm, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (completionResidueEquiv v).toEquiv).symm
  have hlocalCard :=
    Module.natCard_eq_pow_finrank (K := A ⧸ pA) (V := B ⧸ pB)
  have hlocalPow : NU.Chebotarev.PrimeIdeal.norm q ^
        pA.inertiaDeg pB = NU.Chebotarev.PrimeIdeal.norm v := by
    rw [← hcardA, ← hcardB, Ideal.inertiaDeg_algebraMap]
    exact hlocalCard.symm
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hglobalPow : NU.Chebotarev.PrimeIdeal.norm q ^
        q.asIdeal.inertiaDeg v.asIdeal =
      NU.Chebotarev.PrimeIdeal.norm v := by
    exact (NU.Chebotarev.PrimeIdeal.norm_pow_inertiaDeg
      v q inferInstance).symm
  have hnormq : NU.Chebotarev.PrimeIdeal.norm q =
      NU.LocalTheory.residueCharacteristic v := by
    calc
      NU.Chebotarev.PrimeIdeal.norm q =
          NU.LocalTheory.residueCharacteristic q :=
        (rational_residueCharacteristic_eq_norm q).symm
      _ = NU.LocalTheory.residueCharacteristic v :=
        residueCharacteristic_restrictFinitePlace ℚ v
  have hinertia : pA.inertiaDeg pB =
      q.asIdeal.inertiaDeg v.asIdeal := by
    apply Nat.pow_right_injective
      (show 2 ≤ NU.Chebotarev.PrimeIdeal.norm q by
        rw [← rational_residueCharacteristic_eq_norm,
          rational_residueCharacteristic_eq_natGenerator]
        exact (Rat.HeightOneSpectrum.primesEquiv q).property.two_le)
    exact hlocalPow.trans hglobalPow.symm
  obtain ⟨π, hπ⟩ := q.intValuation_exists_uniformizer
  let πFb : Fb := algebraMap ℚ Fb (π : ℚ)
  have hπFb : vFb πFb = WithZero.exp (-1 : ℤ) := by
    dsimp [πFb]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [show (algebraMap ℚ ℚ) (π : ℚ) =
      algebraMap (𝓞 ℚ) ℚ π by simp]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact hπ
  let πA : A := ⟨πFb, by
    change vFb πFb ≤ 1
    rw [hπFb, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega⟩
  obtain ⟨ϖ, hϖ⟩ := v.intValuation_exists_uniformizer
  let ϖF : F := algebraMap K F (ϖ : K)
  have hϖF : vF ϖF = WithZero.exp (-1 : ℤ) := by
    dsimp [ϖF]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [show (algebraMap K K) (ϖ : K) =
      algebraMap (𝓞 K) K ϖ by simp]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact hϖ
  let ϖB : B := ⟨ϖF, by
    change vF ϖF ≤ 1
    rw [hϖF, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega⟩
  have hpA : pA = Ideal.span {πA} := by
    apply Ideal.ext
    intro x
    have hmax : x ∈ IsLocalRing.maximalIdeal A ↔
        vFb (x : Fb) < 1 :=
      Valuation.mem_maximalIdeal_iff Fb vFb
    have hspan : x ∈ Ideal.span {πA} ↔
        vFb (algebraMap A Fb x) ≤ vFb (algebraMap A Fb πA) := by
      rw [Ideal.mem_span_singleton]
      exact Valuation.Integers.dvd_iff_le
        (Valuation.valuationSubring.integers vFb)
    rw [hmax, hspan]
    change vFb (x : Fb) < 1 ↔ vFb (x : Fb) ≤ vFb (πA : Fb)
    rw [show vFb (πA : Fb) = WithZero.exp (-1 : ℤ) from hπFb]
    exact withZeroMulInt_lt_one_iff_le_exp_neg_one _
  have hpB : pB = Ideal.span {ϖB} := by
    apply Ideal.ext
    intro x
    have hmax : x ∈ IsLocalRing.maximalIdeal B ↔
        vF (x : F) < 1 :=
      Valuation.mem_maximalIdeal_iff F vF
    have hspan : x ∈ Ideal.span {ϖB} ↔
        vF (algebraMap B F x) ≤ vF (algebraMap B F ϖB) := by
      rw [Ideal.mem_span_singleton]
      exact Valuation.Integers.dvd_iff_le
        (Valuation.valuationSubring.integers vF)
    rw [hmax, hspan]
    change vF (x : F) < 1 ↔ vF (x : F) ≤ vF (ϖB : F)
    rw [show vF (ϖB : F) = WithZero.exp (-1 : ℤ) from hϖF]
    exact withZeroMulInt_lt_one_iff_le_exp_neg_one _
  have hpA0 : pA ≠ ⊥ := by
    rw [hpA, ne_eq, Ideal.span_singleton_eq_bot]
    intro hzero
    have hz := congrArg vFb (congrArg Subtype.val hzero)
    change vFb (πA : Fb) = vFb (0 : Fb) at hz
    rw [map_zero, show vFb (πA : Fb) = WithZero.exp (-1 : ℤ) from hπFb]
      at hz
    exact WithZero.exp_ne_zero hz
  have hramification : pA.ramificationIdx pB =
      q.asIdeal.ramificationIdx v.asIdeal := by
    let e := q.asIdeal.ramificationIdx v.asIdeal
    let mπ : B := algebraMap A B πA
    have hmπF : (mπ : F) = rationalCompletionMap v πFb := by
      change ((algebraMap A B πA : B) : F) = _
      calc
        ((algebraMap A B πA : B) : F) =
            algebraMap Fb F (πA : Fb) := rfl
        _ = rationalCompletionMap v πFb := by
          rw [RingHom.algebraMap_toAlgebra]
    have hqπ : q.valuation ℚ (π : ℚ) = WithZero.exp (-1 : ℤ) := by
      rw [show (π : ℚ) = algebraMap (𝓞 ℚ) ℚ π by rfl,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact hπ
    have hmval : vF (mπ : F) = WithZero.exp (-(e : ℤ)) := by
      rw [hmπF, show πFb = algebraMap ℚ Fb (π : ℚ) from rfl,
        rationalCompletionMap_algebraMap]
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply]
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K q v
        (π : ℚ), hqπ, ← WithZero.exp_nsmul]
      congr 1
      simp [e]
    have hpowval : vF ((ϖB ^ e : B) : F) =
        WithZero.exp (-(e : ℤ)) := by
      change vF ((ϖB : F) ^ e) = _
      rw [map_pow, show vF (ϖB : F) = WithZero.exp (-1 : ℤ) from hϖF,
        ← WithZero.exp_nsmul]
      congr 1
      simp
    have hdvd : mπ ∣ ϖB ^ e := by
      apply (Valuation.Integers.dvd_iff_le
        (Valuation.valuationSubring.integers vF)).mpr
      change vF ((ϖB ^ e : B) : F) ≤ vF (mπ : F)
      rw [hpowval, hmval]
    have hdvd' : ϖB ^ e ∣ mπ := by
      apply (Valuation.Integers.dvd_iff_le
        (Valuation.valuationSubring.integers vF)).mpr
      change vF (mπ : F) ≤ vF ((ϖB ^ e : B) : F)
      rw [hpowval, hmval]
    have hassoc : Associated mπ (ϖB ^ e) :=
      associated_of_dvd_dvd hdvd hdvd'
    have hmap : Ideal.map (algebraMap A B) pA = pB ^ e := by
      rw [hpA, Ideal.map_span, Set.image_singleton, hpB,
        Ideal.span_singleton_pow]
      exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
    have hnot : ¬ Ideal.map (algebraMap A B) pA ≤ pB ^ (e + 1) := by
      rw [hmap]
      intro hle
      have heq : pB ^ e = pB ^ (e + 1) :=
        le_antisymm hle (Ideal.pow_le_pow_right (Nat.le_succ e))
      have hc := congr_arg Order.coheight heq
      rw [show pB = IsLocalRing.maximalIdeal B from rfl,
        IsDiscreteValuationRing.coheight_pow_maximalIdeal,
        IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
      have : e = e + 1 := by exact_mod_cast hc
      omega
    exact Ideal.ramificationIdx_spec hmap.le hnot
  have hdegree := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (S := B) Fb F (p := pA) hpA0
  change Module.finrank Fb F = finitePlaceLocalDegree v
  rw [← hdegree, hramification, hinertia,
    Ideal.ramificationIdx_eq_ramificationIdx' q.asIdeal v.asIdeal q.ne_bot,
    Ideal.inertiaDeg_eq_inertiaDeg' q.asIdeal v.asIdeal]
  rfl

set_option maxHeartbeats 200000

/-- The rational place under `v` is the place indexed by its residue
prime. -/
private theorem rationalPlace_eq_primesEquiv_symm
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    Rat.HeightOneSpectrum.primesEquiv.symm p =
      NU.LocalTheory.restrictFinitePlace ℚ v := by
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change (p : ℕ) = Rat.HeightOneSpectrum.natGenerator
    (NU.LocalTheory.restrictFinitePlace ℚ v)
  exact hp.trans (rationalPrimeOfPlace_eq v).symm

/-- The standard `p`-adic field is the completion at the rational place
under `v`. -/
private noncomputable def padicRationalCompletionEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    ℚ_[p] ≃A[ℚ] q.adicCompletion ℚ :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) p).trans
    (ContinuousAlgEquiv.cast
      (A := fun w : NU.LocalTheory.FinitePlace ℚ => w.adicCompletion ℚ)
      (rationalPlace_eq_primesEquiv_symm v p hp))

/-- The analogous equivalence of integer rings. -/
private noncomputable def padicIntegerRationalCompletionEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    ℤ_[p] ≃A[ℤ] q.adicCompletionIntegers ℚ :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p).trans
    (ContinuousAlgEquiv.cast
      (A := fun w : NU.LocalTheory.FinitePlace ℚ =>
        w.adicCompletionIntegers ℚ)
      (rationalPlace_eq_primesEquiv_symm v p hp))

private theorem adicCompletionIntegers_cast_val
    {q r : NU.LocalTheory.FinitePlace ℚ} (h : q = r)
    (x : q.adicCompletionIntegers ℚ) :
    ((cast (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
        ↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ w)) h) x :
          r.adicCompletionIntegers ℚ) : r.adicCompletion ℚ) =
    cast (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w) h)
      (x : q.adicCompletion ℚ) := by
  cases h
  rfl

private theorem padicIntegerRationalCompletionEquiv_coe
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (x : ℤ_[p]) :
    ((padicIntegerRationalCompletionEquiv v p hp x :
        (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletionIntegers ℚ) :
      (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletion ℚ) =
    padicRationalCompletionEquiv v p hp (x : ℚ_[p]) := by
  let hq := rationalPlace_eq_primesEquiv_symm v p hp
  let a := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p x
  let ac : (Rat.HeightOneSpectrum.primesEquiv.symm p).adicCompletion ℚ := a.1
  let b := Padic.adicCompletionEquiv (𝓞 ℚ) p (x : ℚ_[p])
  have hab : ac = b :=
    PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) p x
  simp only [padicIntegerRationalCompletionEquiv,
    padicRationalCompletionEquiv, ContinuousAlgEquiv.trans_apply,
    ContinuousAlgEquiv.cast_apply, Equiv.cast_apply, eq_cast_iff_heq]
  have h₁ :
      (cast (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
        ↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ w)) hq) a).1 ≍
      cast (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w) hq) ac :=
    heq_of_eq (adicCompletionIntegers_cast_val hq a)
  have h₂ : cast (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w) hq) ac ≍ ac :=
    cast_heq (congrArg (fun w : NU.LocalTheory.FinitePlace ℚ =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w) hq) ac
  exact h₁.trans (h₂.trans (heq_of_eq hab))

/-- Restriction of the completed field map to valuation rings. -/
private noncomputable def rationalCompletionIntegerMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    let q := NU.LocalTheory.restrictFinitePlace ℚ v
    q.adicCompletionIntegers ℚ →+* v.adicCompletionIntegers K := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion K) :=
    (rationalCompletionMap v).toAlgebra
  letI : (Valued.v : Valuation (q.adicCompletion ℚ) ℤᵐ⁰).HasExtension
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) :=
    rationalCompletionMap_hasExtension v
  letI : Algebra (q.adicCompletionIntegers ℚ)
      (v.adicCompletionIntegers K) :=
    Valuation.HasExtension.instAlgebraInteger
  exact algebraMap _ _

private theorem continuous_rationalCompletionIntegerMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Continuous (rationalCompletionIntegerMap v) := by
  apply Continuous.subtype_mk
  have h : Continuous fun x :
      (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletionIntegers ℚ =>
      rationalCompletionMap v (x :
        (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletion ℚ) :=
    (continuous_rationalCompletionMap v).comp continuous_subtype_val
  convert h using 1
  rfl

/-- The continuous field embedding `ℚ_p → K_v`. -/
private noncomputable def padicPlaceMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    ℚ_[p] →+* v.adicCompletion K :=
  (rationalCompletionMap v).comp
    (padicRationalCompletionEquiv v p hp).toRingEquiv.toRingHom

private theorem continuous_padicPlaceMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    Continuous (padicPlaceMap v p hp) := by
  have h := (continuous_rationalCompletionMap v).comp
    (padicRationalCompletionEquiv v p hp).continuous
  convert h using 1
  rfl

/-- The compatible continuous integer-ring embedding `ℤ_p → 𝓞_{K_v}`. -/
private noncomputable def padicIntegerPlaceMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    ℤ_[p] →+* v.adicCompletionIntegers K :=
  (rationalCompletionIntegerMap v).comp
    (padicIntegerRationalCompletionEquiv v p hp).toRingEquiv.toRingHom

private theorem continuous_padicIntegerPlaceMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    Continuous (padicIntegerPlaceMap v p hp) := by
  have h := (continuous_rationalCompletionIntegerMap v).comp
    (padicIntegerRationalCompletionEquiv v p hp).continuous
  convert h using 1
  rfl

private theorem padicIntegerPlaceMap_coe
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (x : ℤ_[p]) :
    ((padicIntegerPlaceMap v p hp x : v.adicCompletionIntegers K) :
        v.adicCompletion K) =
      padicPlaceMap v p hp (x : ℚ_[p]) := by
  change ((rationalCompletionIntegerMap v
      (padicIntegerRationalCompletionEquiv v p hp x) :
        v.adicCompletionIntegers K) : v.adicCompletion K) =
    rationalCompletionMap v
      (padicRationalCompletionEquiv v p hp (x : ℚ_[p]))
  calc
    ((rationalCompletionIntegerMap v
        (padicIntegerRationalCompletionEquiv v p hp x) :
          v.adicCompletionIntegers K) : v.adicCompletion K) =
      rationalCompletionMap v
        ((padicIntegerRationalCompletionEquiv v p hp x :
          (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletionIntegers ℚ) :
            (NU.LocalTheory.restrictFinitePlace ℚ v).adicCompletion ℚ) := rfl
    _ = _ := congrArg (rationalCompletionMap v)
      (padicIntegerRationalCompletionEquiv_coe v p hp x)

/-- The integer ring of `K_v` is finite of the local degree over `ℤ_p`. -/
private theorem padicIntegerCompletion_module_finite_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    let B := v.adicCompletionIntegers K
    letI : Algebra ℤ_[p] B := (padicIntegerPlaceMap v p hp).toAlgebra
    Module.Finite ℤ_[p] B ∧
      Module.finrank ℤ_[p] B = finitePlaceLocalDegree v := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  let Fb := q.adicCompletion ℚ
  let F := v.adicCompletion K
  let A := q.adicCompletionIntegers ℚ
  let B := v.adicCompletionIntegers K
  let eQ := padicRationalCompletionEquiv v p hp
  let eZ := padicIntegerRationalCompletionEquiv v p hp
  letI : Algebra Fb F := (rationalCompletionMap v).toAlgebra
  letI : ContinuousSMul Fb F :=
    ⟨by
      have h := ((continuous_rationalCompletionMap v).comp continuous_fst).mul
        continuous_snd
      change Continuous fun z : Fb × F => rationalCompletionMap v z.1 * z.2
      convert h using 1
      rfl⟩
  letI : IsScalarTower ℚ Fb F :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (rationalCompletionMap_algebraMap v x).symm
  letI : Module.Finite Fb F := rationalCompletionMap_module_finite v
  letI : (Valued.v : Valuation Fb ℤᵐ⁰).HasExtension
      (Valued.v : Valuation F ℤᵐ⁰) := rationalCompletionMap_hasExtension v
  letI : Algebra A B := Valuation.HasExtension.instAlgebraInteger
  letI : Module.Finite A B := rationalCompletionIntegers_module_finite v
  letI : Algebra ℚ_[p] F := (padicPlaceMap v p hp).toAlgebra
  letI : Algebra ℤ_[p] B := (padicIntegerPlaceMap v p hp).toAlgebra
  letI : Algebra ℤ_[p] ℚ_[p] := inferInstance
  letI : Algebra ℤ_[p] F :=
    ((padicPlaceMap v p hp).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have hsquareZ : (algebraMap ℤ_[p] B).comp eZ.symm.toRingEquiv.toRingHom =
      (RingEquiv.refl B).toRingHom.comp (algebraMap A B) := by
    apply RingHom.ext
    intro x
    change padicIntegerPlaceMap v p hp (eZ.symm x) =
      algebraMap A B x
    change rationalCompletionIntegerMap v (eZ (eZ.symm x)) =
      rationalCompletionIntegerMap v x
    rw [eZ.apply_symm_apply]
  letI : Module.Finite ℤ_[p] B :=
    Module.Finite.of_equiv_equiv eZ.symm.toRingEquiv (RingEquiv.refl B)
      hsquareZ
  have hsquareQ : (algebraMap ℚ_[p] F).comp eQ.symm.toRingEquiv.toRingHom =
      (RingEquiv.refl F).toRingHom.comp (algebraMap Fb F) := by
    apply RingHom.ext
    intro x
    change rationalCompletionMap v (eQ (eQ.symm x)) =
      rationalCompletionMap v x
    rw [eQ.apply_symm_apply]
  letI : Module.Finite ℚ_[p] F :=
    Module.Finite.of_equiv_equiv eQ.symm.toRingEquiv (RingEquiv.refl F)
      hsquareQ
  letI : IsScalarTower ℤ_[p] ℚ_[p] F :=
    .of_algebraMap_eq fun _ => rfl
  letI : Algebra B F := inferInstance
  letI : IsScalarTower ℤ_[p] B F :=
    .of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (padicIntegerPlaceMap_coe v p hp x).symm
  letI : FaithfulSMul ℤ_[p] B :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[p] B).2 (by
      intro x y hxy
      change padicIntegerPlaceMap v p hp x =
        padicIntegerPlaceMap v p hp y at hxy
      have h := congrArg (fun z : B => (z : F)) hxy
      rw [padicIntegerPlaceMap_coe, padicIntegerPlaceMap_coe] at h
      exact Subtype.val_injective ((padicPlaceMap v p hp).injective h))
  have hfrac := Algebra.IsAlgebraic.finrank_of_isFractionRing
    ℤ_[p] ℚ_[p] B F
  have hsquareQ' : (algebraMap Fb F).comp eQ.toRingEquiv.toRingHom =
      (RingEquiv.refl F).toRingHom.comp (algebraMap ℚ_[p] F) := by
    apply RingHom.ext
    intro x
    rfl
  have hfield : Module.finrank ℚ_[p] F = Module.finrank Fb F :=
    Algebra.finrank_eq_of_equiv_equiv eQ.toRingEquiv (RingEquiv.refl F)
      hsquareQ'
  refine ⟨inferInstance, ?_⟩
  rw [← hfrac, hfield, rationalCompletion_finrank_eq_localDegree]

/-- Products preserve topological additive equivalences. -/
private def continuousAddEquivProdCongr
    {A B C D : Type*}
    [Add A] [Add B] [Add C] [Add D]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ+ B) (f : C ≃ₜ+ D) :
    A × C ≃ₜ+ B × D :=
  ContinuousAddEquiv.mk'
    (Homeomorph.prodCongr e.toHomeomorph f.toHomeomorph)
    (fun x y => by
      apply Prod.ext
      · exact e.map_add x.1 y.1
      · exact f.map_add x.2 y.2)

/-- Products preserve topological multiplicative equivalences. -/
private def continuousMulEquivProdCongr
    {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : A × C ≃ₜ* B × D :=
  ContinuousMulEquiv.mk'
    (Homeomorph.prodCongr e.toHomeomorph f.toHomeomorph)
    (fun x y => by
      apply Prod.ext
      · exact e.map_mul x.1 y.1
      · exact f.map_mul x.2 y.2)

/-- Every nonzero quotient of `ℤ_p` is finite. -/
private theorem padicInt_quotient_finite
    (p : Nat.Primes) (I : Ideal ℤ_[p]) (hI : I ≠ ⊥) :
    Finite (ℤ_[p] ⧸ I) := by
  letI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod (p : ℕ))
      PadicInt.residueField.toEquiv.symm
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal ℤ_[p]
      (inferInstance :
        (IsLocalRing.maximalIdeal ℤ_[p]).IsPrincipal) I hI
  exact ⟨n, hn ▸ le_rfl⟩

/-- The torsion submodule of a finite `ℤ_p`-module is finite. -/
private theorem padicModule_torsion_finite
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Finite (Submodule.torsion ℤ_[p] M) := by
  let T := Submodule.torsion ℤ_[p] M
  letI : Module.Finite ℤ_[p] T := inferInstance
  obtain ⟨ι, fi, q, hq, e, ⟨equiv⟩⟩ :=
    Module.equiv_directSum_of_isTorsion
      (R := ℤ_[p]) (M := T)
      (Submodule.torsion_isTorsion (R := ℤ_[p]) (M := M))
  letI : Fintype ι := fi
  have hquot (i : ι) :
      Finite (ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i) := by
    apply padicInt_quotient_finite p
    exact fun h => pow_ne_zero (e i) (hq i).ne_zero
      (Submodule.span_singleton_eq_bot.mp h)
  letI (i : ι) : Finite (ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i) :=
    hquot i
  let de := DirectSum.linearEquivFunOnFintype ℤ_[p] ι
    (fun i => ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i)
  exact Finite.of_injective (fun x => de (equiv x))
    (de.injective.comp equiv.injective)

/-- A finite torsion-free module over `ℤ_p` is free. -/
private theorem padicModule_free_of_finite_torsionFree
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M] :
    Module.Free ℤ_[p] M := by
  exact Module.free_of_finite_type_torsion_free'

/-- Every linear map out of a finite torsion-free topological
`ℤ_p`-module is continuous. -/
private theorem padicModule_linearMap_continuous_of_finite_torsionFree
    (p : Nat.Primes) (M N : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M]
    [AddCommGroup N] [Module ℤ_[p] N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousSMul ℤ_[p] N]
    (f : M →ₗ[ℤ_[p]] N) : Continuous f := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ_[p]) (M := M)
  let e : (Fin n → ℤ_[p]) ≃ M := b.equivFun.symm.toEquiv
  have he : Continuous e := by
    have hs : Continuous fun x : Fin n → ℤ_[p] =>
        ∑ i, x i • b i := by
      fun_prop
    convert hs using 1
    funext x
    exact b.equivFun_symm_apply x
  let h : (Fin n → ℤ_[p]) ≃ₜ M :=
    he.homeoOfEquivCompactToT2
  have hf : Continuous fun x : Fin n → ℤ_[p] =>
      ∑ i, x i • f (b i) := by
    fun_prop
  have hc := hf.comp h.symm.continuous
  convert hc using 1
  funext x
  change f x = ∑ i, (b.equivFun x) i • f (b i)
  calc
    f x = f (∑ i, (b.equivFun x) i • b i) := by
      congr 1
      symm
      rw [← b.equivFun_symm_apply,
        b.equivFun.symm_apply_apply]
    _ = ∑ i, f ((b.equivFun x) i • b i) := by rw [map_sum]
    _ = _ := by simp

/-- The algebraic torsion splitting of a finite compact `ℤ_p`-module is
automatically topological. -/
private theorem padicModule_torsionProdQuotientContinuousAddEquiv
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [CompactSpace M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Nonempty
      ((Submodule.torsion ℤ_[p] M ×
          (M ⧸ Submodule.torsion ℤ_[p] M)) ≃ₜ+ M) := by
  let T := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Finite T := padicModule_torsion_finite p M
  have hTfinite : (T : Set M).Finite := Set.toFinite _
  letI : IsClosed (T : Set M) := hTfinite.isClosed
  letI : CompactSpace Q := isCompact_univ_iff.mp (by
    have hcomp :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).image
        T.continuous_mkQ
    have hsurj : Function.Surjective T.mkQ :=
      Submodule.Quotient.mk_surjective T
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at hcomp
    exact hcomp)
  letI : Module.Finite ℤ_[p] Q := inferInstance
  letI : Module.Free ℤ_[p] Q :=
    padicModule_free_of_finite_torsionFree p Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (P := Q) (Submodule.mkQ T)
    (LinearMap.id (R := ℤ_[p]) (M := Q))
    (Submodule.Quotient.mk_surjective T)
  let e : (T × Q) ≃ₗ[ℤ_[p]] M :=
    lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hs
  let fT : T →ₗ[ℤ_[p]] M := e.toLinearMap.comp
    (LinearMap.inl ℤ_[p] T Q)
  let fQ : Q →ₗ[ℤ_[p]] M := e.toLinearMap.comp
    (LinearMap.inr ℤ_[p] T Q)
  have hfT : Continuous fT := continuous_of_discreteTopology
  have hfQ : Continuous fQ :=
    padicModule_linearMap_continuous_of_finite_torsionFree
      p Q M fQ
  have he : Continuous e := by
    have hc :=
      (hfT.comp continuous_fst).add (hfQ.comp continuous_snd)
    convert hc using 1
    funext x
    change e x = fT x.1 + fQ x.2
    calc
      e x = e ((x.1, 0) + (0, x.2)) := by
        congr 1
        ext <;> simp
      _ = e (x.1, 0) + e (0, x.2) := e.map_add _ _
      _ = fT x.1 + fQ x.2 := rfl
  let h : (T × Q) ≃ₜ M :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he
  exact ⟨ContinuousAddEquiv.mk' h
    (fun x y => e.map_add x y)⟩

/-- A finite torsion-free topological `ℤ_p`-module is topologically a finite
power of `ℤ_p`. -/
private theorem padicModule_continuousAddEquivPi_of_finite_torsionFree
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M] :
    Nonempty
      ((Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃ₜ+ M) := by
  letI : Module.Free ℤ_[p] M :=
    padicModule_free_of_finite_torsionFree p M
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ_[p]) (M := M)
  have hn : Module.finrank ℤ_[p] M = n := by
    simpa using Module.finrank_eq_card_basis b
  subst n
  let e : (Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃+ M :=
    b.equivFun.symm.toAddEquiv
  have he : Continuous e := by
    have hs : Continuous fun
        x : Fin (Module.finrank ℤ_[p] M) → ℤ_[p] =>
        ∑ i, x i • b i := by
      fun_prop
    convert hs using 1
    funext x
    exact b.equivFun_symm_apply x
  let h : (Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃ₜ M :=
    he.homeoOfEquivCompactToT2
  exact ⟨ContinuousAddEquiv.mk' h
    (fun x y => e.map_add x y)⟩

/-- Complete topological structure theorem for a finite compact
`ℤ_p`-module. -/
private theorem padicModule_torsionProdFreeContinuousAddEquiv
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [CompactSpace M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Nonempty
      ((Submodule.torsion ℤ_[p] M ×
          (Fin (Module.finrank ℤ_[p]
            (M ⧸ Submodule.torsion ℤ_[p] M)) → ℤ_[p])) ≃ₜ+ M) := by
  let T := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Finite T := padicModule_torsion_finite p M
  have hTfinite : (T : Set M).Finite := Set.toFinite _
  letI : IsClosed (T : Set M) := hTfinite.isClosed
  letI : Module.Finite ℤ_[p] Q := inferInstance
  obtain ⟨freeEquiv⟩ :=
    padicModule_continuousAddEquivPi_of_finite_torsionFree p Q
  obtain ⟨splitEquiv⟩ :=
    padicModule_torsionProdQuotientContinuousAddEquiv p M
  let leftEquiv : T ≃ₜ+ T := ContinuousAddEquiv.refl T
  exact ⟨(continuousAddEquivProdCongr leftEquiv freeEquiv).trans
    splitEquiv⟩

/-- Equality of the underlying valuation forces equality of the normalized
integer valuation. -/
private theorem normalizedValuation_eq_of_valuation_eq
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x y : Units F)
    (hxy : ValuativeRel.valuation F (x : F) =
      ValuativeRel.valuation F (y : F)) :
    normalizedValuation F x = normalizedValuation F y := by
  let z : Units F := x * y⁻¹
  have hzval : ValuativeRel.valuation F (z : F) = 1 := by
    dsimp [z]
    simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    rw [hxy]
    exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 y.ne_zero)
  have hzint : ∃ a : RingOfIntegers F, (a : F) = (z : F) := by
    exact ⟨⟨z, (Valuation.mem_integer_iff _ _).2 hzval.le⟩, rfl⟩
  have hznonneg : 0 ≤ normalizedValuation F z :=
    (exists_normalizedValuationHom F).choose_spec.2 z |>.2 hzint
  have hzinvval : ValuativeRel.valuation F (z⁻¹ : F) = 1 := by
    rw [map_inv₀, hzval, inv_one]
  have hzinvint : ∃ a : RingOfIntegers F,
      (a : F) = ((z⁻¹ : Units F) : F) := by
    let a : RingOfIntegers F :=
      ⟨((z⁻¹ : Units F) : F), (Valuation.mem_integer_iff _ _).2 (by
        simpa using hzinvval.le)⟩
    exact ⟨a, rfl⟩
  have hzinvnonneg : 0 ≤ normalizedValuation F z⁻¹ :=
    (exists_normalizedValuationHom F).choose_spec.2 z⁻¹ |>.2 hzinvint
  have hzinv : normalizedValuation F z⁻¹ =
      -normalizedValuation F z := by
    simp [normalizedValuation]
  have hz0 : normalizedValuation F z = 0 := by omega
  rw [show normalizedValuation F z = normalizedValuation F x -
      normalizedValuation F y by
    dsimp [z]
    simp [normalizedValuation, sub_eq_add_neg]] at hz0
  omega

/-- The normalized valuation is continuous on the multiplicative group. -/
private theorem continuous_normalizedValuation
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Continuous (normalizedValuation F) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_def]
  intro s hs
  have hxs : normalizedValuation F x ∈ s := mem_of_mem_nhds hs
  have hlocF : {y : F | ValuativeRel.valuation F y =
      ValuativeRel.valuation F (x : F)} ∈ nhds (x : F) := by
    have hx0 : ValuativeRel.valuation F (x : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 x.ne_zero
    have h := Valued.locally_const (R := F) (x := (x : F)) (by
      simpa only [IsValuativeTopology.v_eq_valuation] using hx0)
    simpa only [IsValuativeTopology.v_eq_valuation] using h
  have hlocU : {y : Units F | ValuativeRel.valuation F (y : F) =
      ValuativeRel.valuation F (x : F)} ∈ nhds x := by
    exact Units.continuous_val.continuousAt.preimage_mem_nhds hlocF
  apply Filter.mem_of_superset hlocU
  intro y hy
  change normalizedValuation F y ∈ s
  rw [normalizedValuation_eq_of_valuation_eq F y x hy]
  exact hxs

private theorem continuous_normalizedValuationHom
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Continuous (normalizedValuationHom F) := by
  change Continuous (normalizedValuation F)
  exact continuous_normalizedValuation F

/-- The section of normalized valuation determined by a uniformizer. -/
private noncomputable def valuationSection
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Multiplicative ℤ →* Units F :=
  zpowersHom (Units F) (defaultUniformizer F).val

@[simp] private theorem valuationSection_spec
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : Multiplicative ℤ) :
    normalizedValuationHom F (valuationSection F n) = n := by
  let π := defaultUniformizer F
  have hπ : normalizedValuationHom F π.val =
      Multiplicative.ofAdd (1 : ℤ) := by
    apply Multiplicative.toAdd.injective
    exact π.valuation_eq_one
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd
    (normalizedValuationHom F (π.val ^ Multiplicative.toAdd n)) =
      Multiplicative.toAdd n
  rw [map_zpow, hπ]
  simp

/-- Splitting normalized valuation into its integer coordinate and unit
kernel. -/
private noncomputable def valuationSplitMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Units F ≃* Multiplicative ℤ × (normalizedValuationHom F).ker where
  toFun u :=
    (normalizedValuationHom F u,
      ⟨(valuationSection F (normalizedValuationHom F u))⁻¹ * u, by
        change normalizedValuationHom F
          ((valuationSection F (normalizedValuationHom F u))⁻¹ * u) = 1
        rw [map_mul, map_inv, valuationSection_spec F]
        simp⟩)
  invFun z := valuationSection F z.1 * z.2
  left_inv u := by
    dsimp
    simp
  right_inv z := by
    have hordz : normalizedValuationHom F
        (valuationSection F z.1 * z.2) = z.1 := by
      rw [map_mul, valuationSection_spec F, z.2.property, mul_one]
    apply Prod.ext
    · exact hordz
    · apply Subtype.ext
      change (valuationSection F
          (normalizedValuationHom F
            (valuationSection F z.1 * z.2)))⁻¹ *
          (valuationSection F z.1 * z.2) = z.2
      rw [hordz]
      simp
  map_mul' x y := by
    apply Prod.ext
    · exact map_mul (normalizedValuationHom F) x y
    · apply Subtype.ext
      change (valuationSection F
          (normalizedValuationHom F (x * y)))⁻¹ * (x * y) =
        ((valuationSection F (normalizedValuationHom F x))⁻¹ * x) *
          ((valuationSection F (normalizedValuationHom F y))⁻¹ * y)
      rw [map_mul, map_mul, mul_inv_rev]
      ac_rfl

/-- The valuation splitting as a topological group equivalence. -/
private noncomputable def valuationSplitContinuousMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Units F ≃ₜ* Multiplicative ℤ × (normalizedValuationHom F).ker := by
  let e := valuationSplitMulEquiv F
  let s := valuationSection F
  have hord : Continuous (normalizedValuationHom F) :=
    continuous_normalizedValuationHom F
  have hs : Continuous s := continuous_of_discreteTopology
  have he : Continuous e := by
    apply Continuous.prodMk hord
    exact Continuous.subtype_mk
      ((hs.comp hord).inv.mul continuous_id) _
  have hei : Continuous e.symm := by
    exact (hs.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  exact ContinuousMulEquiv.mk' (Homeomorph.mk e.toEquiv he hei)
    e.map_mul

/-- The kernel of normalized valuation is exactly the unit group of the
valuation subring. -/
private theorem normalizedValuationHom_ker_eq_unitGroup
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    (normalizedValuationHom F).ker =
      (ValuativeRel.valuation F).valuationSubring.unitGroup := by
  let A := (ValuativeRel.valuation F).valuationSubring
  ext x
  change normalizedValuationHom F x = 1 ↔ x ∈ A.unitGroup
  constructor
  · intro hx
    have hn : Multiplicative.toAdd (normalizedValuationHom F x) = 0 := by
      rw [hx]
      rfl
    have hnx : 0 ≤ Multiplicative.toAdd (normalizedValuationHom F x) :=
      hn.ge
    have hnxi : 0 ≤
        Multiplicative.toAdd (normalizedValuationHom F x⁻¹) := by
      rw [map_inv]
      change 0 ≤ -Multiplicative.toAdd (normalizedValuationHom F x)
      rw [hn]
      simp
    obtain ⟨a, ha⟩ :=
      (exists_normalizedValuationHom F).choose_spec.2 x |>.mp hnx
    obtain ⟨b, hb⟩ :=
      (exists_normalizedValuationHom F).choose_spec.2 x⁻¹ |>.mp hnxi
    let au : Units A :=
      { val := a
        inv := b
        val_inv := by
          apply Subtype.ext
          change (a : F) * (b : F) = 1
          rw [ha, hb]
          simpa [Units.val_inv_eq_inv_val] using
            mul_inv_cancel₀ x.ne_zero
        inv_val := by
          apply Subtype.ext
          change (b : F) * (a : F) = 1
          rw [ha, hb]
          simpa [Units.val_inv_eq_inv_val] using
            inv_mul_cancel₀ x.ne_zero }
    let zA : A.unitGroup := A.unitGroupMulEquiv.symm au
    have hz : (zA : Units F) = x := by
      apply Units.ext
      exact ha
    rw [← hz]
    exact zA.property
  · intro hx
    let zA : A.unitGroup := ⟨x, hx⟩
    let au : Units A := A.unitGroupMulEquiv zA
    have ha : ((au : A) : F) = (x : F) := rfl
    have hb : (((au⁻¹ : Units A) : A) : F) = (x⁻¹ : Units F) := rfl
    have hn : 0 ≤ Multiplicative.toAdd (normalizedValuationHom F x) := by
      apply (exists_normalizedValuationHom F).choose_spec.2 x |>.mpr
      exact ⟨(au : A), ha⟩
    have hni : 0 ≤
        Multiplicative.toAdd (normalizedValuationHom F x⁻¹) := by
      apply (exists_normalizedValuationHom F).choose_spec.2 x⁻¹ |>.mpr
      let b : RingOfIntegers F :=
        ⟨(((au⁻¹ : Units A) : A) : F),
          (au⁻¹ : Units A).val.property⟩
      exact ⟨b, hb⟩
    have hnle : Multiplicative.toAdd
        (normalizedValuationHom F x) ≤ 0 := by
      rw [map_inv] at hni
      simpa using hni
    have hnzero : Multiplicative.toAdd
        (normalizedValuationHom F x) = 0 := le_antisymm hnle hn
    apply Multiplicative.toAdd.injective
    exact hnzero

/-- Topological transport of the normalized-valuation kernel to local units. -/
private noncomputable def valuationKernelContinuousMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    (normalizedValuationHom F).ker ≃ₜ*
      (ValuativeRel.valuation F).valuationSubring.unitGroup := by
  let e := MulEquiv.subgroupCongr
    (normalizedValuationHom_ker_eq_unitGroup F)
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hei : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  exact ContinuousMulEquiv.mk' (Homeomorph.mk e.toEquiv he hei) e.map_mul

/-- The cyclic subgroup generated by a uniformizer is the valuation
factor. -/
private noncomputable def valuationFactorMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Multiplicative ℤ ≃* Subgroup.zpowers (defaultUniformizer F).val := by
  let f := (valuationSection F).rangeRestrict
  exact MulEquiv.ofBijective f
    ⟨fun a b h => by
        have hh := congrArg (fun u : Units F =>
          normalizedValuationHom F u) (congrArg Subtype.val h)
        have ha : normalizedValuationHom F (f a : Units F) = a := by
          exact valuationSection_spec F a
        have hb : normalizedValuationHom F (f b : Units F) = b := by
          exact valuationSection_spec F b
        exact ha.symm.trans (hh.trans hb),
      MonoidHom.rangeRestrict_surjective _⟩

/-- Topological identification of the valuation factor with `ℤ`. -/
private noncomputable def valuationFactorContinuousMulEquiv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Subgroup.zpowers (defaultUniformizer F).val ≃ₜ* Multiplicative ℤ := by
  let e := valuationFactorMulEquiv F
  have he : Continuous e := continuous_of_discreteTopology
  have hinv (x : Subgroup.zpowers (defaultUniformizer F).val) :
      e.symm x = normalizedValuationHom F x := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    have hx : x = e (Multiplicative.ofAdd n) := by
      apply Subtype.ext
      change (x : Units F) = (defaultUniformizer F).val ^ n
      exact hn.symm
    rw [hx, e.symm_apply_apply]
    exact (valuationSection_spec F (Multiplicative.ofAdd n)).symm
  have hei : Continuous e.symm := by
    convert (continuous_normalizedValuationHom F).comp
      continuous_subtype_val using 1
    funext x
    exact hinv x
  exact (ContinuousMulEquiv.mk' (Homeomorph.mk e.toEquiv he hei)
    e.map_mul).symm

/-- The valuation factor together with the residual local-unit kernel. -/
private structure LocalUnitValuationData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] where
  valuationFactor : Subgroup (Units F)
  unitEquiv : Units F ≃ₜ* valuationFactor ×
    (ValuativeRel.valuation F).valuationSubring.unitGroup
  valuationEquiv : valuationFactor ≃ₜ* Multiplicative ℤ

private theorem localUnitValuationData_exists
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    Nonempty (LocalUnitValuationData F) := by
  let Z := Subgroup.zpowers (defaultUniformizer F).val
  let e : Units F ≃ₜ* Z ×
      (ValuativeRel.valuation F).valuationSubring.unitGroup :=
    (valuationSplitContinuousMulEquiv F).trans
      (continuousMulEquivProdCongr
        (valuationFactorContinuousMulEquiv F).symm
        (valuationKernelContinuousMulEquiv F))
  exact ⟨{
    valuationFactor := Z
    unitEquiv := e
    valuationEquiv := valuationFactorContinuousMulEquiv F }⟩

section TeichmullerSplitting

variable (F : Type*) [Field F] [ValuativeRel F] [UniformSpace F]
  [IsUniformAddGroup F] [IsNonarchimedeanLocalField F]

private theorem ringOfIntegers_isPrecomplete :
    IsPrecomplete (LocalMaximalIdeal F) (RingOfIntegers F) := by
  let R := RingOfIntegers F
  let I := LocalMaximalIdeal F
  constructor
  intro f hf
  obtain ⟨e, he⟩ := ringOfIntegers_inverseLimit F
  let c : AdicCompatibleFamily R I :=
    { value := fun n => Ideal.Quotient.mk (I ^ n) (f n)
      compatible := fun n => by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
        have h := hf (m := n) (n := n + 1) n.le_succ
        rw [SModEq.sub_mem] at h
        simp only [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at h
        simpa only [neg_sub] using (I ^ n).neg_mem h }
  refine ⟨e.symm c, fun n => ?_⟩
  rw [SModEq.sub_mem]
  simp only [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
  rw [← Ideal.Quotient.eq]
  calc
    Ideal.Quotient.mk (I ^ n) (f n) = c.value n := rfl
    _ = (e (e.symm c)).value n := by rw [e.apply_symm_apply]
    _ = Ideal.Quotient.mk (I ^ n) (e.symm c) := he _ _

private theorem ringOfIntegers_isAdicComplete :
    IsAdicComplete (LocalMaximalIdeal F) (RingOfIntegers F) := by
  letI : IsPrecomplete (LocalMaximalIdeal F) (RingOfIntegers F) :=
    ringOfIntegers_isPrecomplete F
  exact { }

private theorem ringOfIntegers_henselianLocalRing :
    HenselianLocalRing (RingOfIntegers F) := by
  letI : IsAdicComplete (LocalMaximalIdeal F) (RingOfIntegers F) :=
    ringOfIntegers_isAdicComplete F
  letI : HenselianRing (RingOfIntegers F) (LocalMaximalIdeal F) :=
    inferInstance
  apply (HenselianLocalRing.TFAE (RingOfIntegers F)).out 1 0 |>.mp
  intro f hf a₀ hroot hderiv
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a₀
  have hevalzero : IsLocalRing.residue (RingOfIntegers F) (f.eval a) = 0 := by
    simpa [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq]
      using hroot
  have heval : f.eval a ∈ LocalMaximalIdeal F :=
    (IsLocalRing.residue_eq_zero_iff _).mp hevalzero
  have hderiv' : IsLocalRing.residue (RingOfIntegers F)
      (f.derivative.eval a) ≠ 0 := by
    simpa [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq]
      using hderiv
  have hunitR : IsUnit (f.derivative.eval a) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hderiv'
  have hunit : IsUnit
      (Ideal.Quotient.mk (LocalMaximalIdeal F) (f.derivative.eval a)) :=
    hunitR.map (Ideal.Quotient.mk (LocalMaximalIdeal F))
  obtain ⟨b, hbroot, hb⟩ := HenselianRing.is_henselian f hf a heval hunit
  refine ⟨b, hbroot, ?_⟩
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hb

private theorem residueCard_gt_one : 1 < residueCard F := by
  have hpos : 0 < residueCard F := Nat.card_pos
  have hne : residueCard F ≠ 1 := by
    intro h
    have hs : Subsingleton (LocalResidueField F) :=
      (Nat.card_eq_one_iff_unique.mp h).1
    exact one_ne_zero (hs.elim 1 0)
  omega

private theorem residueCard_sub_one_cast :
    ((residueCard F - 1 : ℕ) : LocalResidueField F) = -1 := by
  letI := Fintype.ofFinite (LocalResidueField F)
  rw [Nat.cast_sub (residueCard_gt_one F).le]
  rw [show ((residueCard F : ℕ) : LocalResidueField F) = 0 by
    simpa [residueCard, Nat.card_eq_fintype_card] using
      Nat.cast_card_eq_zero (LocalResidueField F)]
  simp

private theorem exists_teichmullerGenerator :
    ∃ (g : Units (LocalResidueField F)) (t : Units (RingOfIntegers F)),
      (∀ x, x ∈ Subgroup.zpowers g) ∧
      orderOf g = residueCard F - 1 ∧
      Units.map (IsLocalRing.residue (RingOfIntegers F)) t = g ∧
      t ^ (residueCard F - 1) = 1 := by
  let R := RingOfIntegers F
  let k := LocalResidueField F
  let N := residueCard F - 1
  letI : HenselianLocalRing R := ringOfIntegers_henselianLocalRing F
  obtain ⟨g, hgen⟩ :=
    (inferInstance : IsCyclic (Units k)).exists_generator
  have hgorder : orderOf g = N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen,
      Nat.card_units]
    rfl
  have hgpow : g ^ N = 1 := by
    rw [← hgorder]
    exact pow_orderOf_eq_one g
  have hgvalpow : (g : k) ^ N = 1 :=
    congrArg Units.val hgpow
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (g : k)
  let f : Polynomial R := Polynomial.X ^ N - 1
  have hfmonic : f.Monic := by
    exact Polynomial.monic_X_pow_sub_C _ (by
      exact (Nat.sub_pos_of_lt (residueCard_gt_one F)).ne')
  have hfroot : Polynomial.aeval (g : k) f = 0 := by
    simp [f, hgvalpow]
  have hfderiv : Polynomial.aeval (g : k) f.derivative ≠ 0 := by
    rw [Polynomial.aeval_def]
    simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    have hNcast : algebraMap R k (N : R) = -1 := by
      rw [map_natCast]
      exact residueCard_sub_one_cast F
    rw [hNcast]
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero)
      (pow_ne_zero _ g.ne_zero)
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨t, htroot, htres⟩ :=
    hH f hfmonic (g : k) hfroot hfderiv
  have htpow : t ^ N = 1 := by
    apply sub_eq_zero.mp
    simpa [f, Polynomial.IsRoot.def] using htroot
  have hNpos : 0 < N := Nat.sub_pos_of_lt (residueCard_gt_one F)
  let tu : Units R := Units.mkOfMulEqOne t (t ^ (N - 1)) (by
    rw [← pow_succ']
    simpa [Nat.sub_add_cancel hNpos] using htpow)
  refine ⟨g, tu, hgen, hgorder, ?_, ?_⟩
  · apply Units.ext
    exact htres
  · apply Units.ext
    exact htpow

private theorem principalUnitGroup_le_unitGroup :
    (ValuativeRel.valuation F).valuationSubring.principalUnitGroup ≤
      (ValuativeRel.valuation F).valuationSubring.unitGroup := by
  let v := ValuativeRel.valuation F
  let A := v.valuationSubring
  intro u hu
  rw [A.mem_principalUnitGroup_iff] at hu
  rw [A.mem_unitGroup_iff]
  have hraw : v ((u : F) - 1) < 1 := by
    have h := (Valuation.isEquiv_valuation_valuationSubring v).lt_iff_lt
      (x := ((u : F) - 1)) (y := (1 : F))
    simpa only [map_one] using h.mpr hu
  have huv : v (u : F) = 1 := by
    rw [show (u : F) = ((u : F) - 1) + 1 by ring]
    exact v.map_add_eq_of_lt_right (by simpa using hraw)
  exact (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one.mp huv

private theorem principalUnitGroup_isOpen :
    IsOpen (((ValuativeRel.valuation F).valuationSubring.principalUnitGroup :
      Subgroup (Units F)) : Set (Units F)) := by
  let A := (ValuativeRel.valuation F).valuationSubring
  have hball : IsOpen {x : F | ValuativeRel.valuation F x < 1} := by
    have h := (ValuativeRel.valuation F).isOpen_ball (1 : _)
    simpa [Valuation.restrict_lt_iff_lt_embedding] using h
  have hpre : IsOpen {u : Units F |
      ValuativeRel.valuation F ((u : F) - 1) < 1} := by
    exact hball.preimage (Units.continuous_val.sub continuous_const)
  convert hpre using 1
  ext u
  rw [SetLike.mem_coe, A.mem_principalUnitGroup_iff]
  simpa only [Set.mem_setOf_eq, map_one] using
    ((Valuation.isEquiv_valuation_valuationSubring
      (ValuativeRel.valuation F)).lt_iff_lt
        (x := ((u : F) - 1)) (y := (1 : F))).symm

/-- The principal-unit group of a number-field completion is compact in the
ambient unit group. -/
private theorem completionPrincipalUnitGroup_isCompact
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    IsCompact
      (((ValuativeRel.valuation (v.adicCompletion K)).valuationSubring.principalUnitGroup :
          Subgroup (Units (v.adicCompletion K))) :
          Set (Units (v.adicCompletion K))) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  let w := ValuativeRel.valuation F
  let A := w.valuationSubring
  let P := A.principalUnitGroup
  have hsphere : IsCompact {x : Units F | w (x : F) = 1} := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himage :
        Units.val '' {x : Units F | w (x : F) = 1} =
          {x : F | w.restrict x = 1} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact w.restrict_eq_one_iff.mpr hy
      · intro hx
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          simp at hx
        let y : Units F := Units.mk0 x hx0
        exact ⟨y, w.restrict_eq_one_iff.mp hx, rfl⟩
    rw [himage]
    have hO : IsCompact (RingOfIntegers F : Set F) := by
      change IsCompact {x : F | x ∈ RingOfIntegers F}
      simpa only [Subtype.range_coe_subtype] using
        (isCompact_range (continuous_subtype_val : Continuous
          ((↑) : RingOfIntegers F → F)))
    apply IsCompact.of_isClosed_subset hO (w.isClosed_sphere 1)
    intro x hx
    exact (Valuation.mem_integer_iff _ _).mpr
      (w.restrict_eq_one_iff.mp hx).le
  have hPclosed : IsClosed (P : Set (Units F)) :=
    P.isClosed_of_isOpen (principalUnitGroup_isOpen F)
  have hPsubset : (P : Set (Units F)) ⊆ {x : Units F | w (x : F) = 1} := by
    intro u hu
    have hu' := principalUnitGroup_le_unitGroup F hu
    rw [A.mem_unitGroup_iff] at hu'
    exact (Valuation.isEquiv_valuation_valuationSubring w).eq_one_iff_eq_one.mpr hu'
  exact hsphere.of_isClosed_subset hPclosed hPsubset

private theorem continuous_monoidHom_of_isOpen_ker
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hker : IsOpen (f.ker : Set G)) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_def]
  intro s hs
  have hfx : f x ∈ s := mem_of_mem_nhds hs
  let m : G ≃ₜ G := Homeomorph.mulLeft x
  have hfiber : f ⁻¹' ({f x} : Set H) = m '' (f.ker : Set G) := by
    ext y
    constructor
    · intro hy
      change f y = f x at hy
      refine ⟨x⁻¹ * y, ?_, ?_⟩
      · change f (x⁻¹ * y) = 1
        rw [map_mul, map_inv, hy]
        simp
      · dsimp [m]
        simp
    · rintro ⟨z, hz, rfl⟩
      change f (x * z) = f x
      rw [map_mul, hz, mul_one]
  have hopen : IsOpen (f ⁻¹' ({f x} : Set H)) := by
    rw [hfiber, m.isOpen_image]
    exact hker
  apply Filter.mem_of_superset (hopen.mem_nhds (by simp))
  intro y hy
  change f y ∈ s
  change f y = f x at hy
  rw [hy]
  exact hfx

private structure LocalUnitTeichmullerData where
  teichmullerFactor : Subgroup (Units F)
  unitEquiv :
    (ValuativeRel.valuation F).valuationSubring.unitGroup ≃ₜ*
      teichmullerFactor ×
        (ValuativeRel.valuation F).valuationSubring.principalUnitGroup
  teichmullerEquiv : teichmullerFactor ≃ₜ*
    Multiplicative (ZMod (residueCard F - 1))

private theorem localUnitTeichmullerData_exists :
    Nonempty (LocalUnitTeichmullerData F) := by
  let A := (ValuativeRel.valuation F).valuationSubring
  let R := RingOfIntegers F
  let k := IsLocalRing.ResidueField A
  let N := residueCard F - 1
  have hNpos : 0 < N := Nat.sub_pos_of_lt (residueCard_gt_one F)
  letI : NeZero N := ⟨hNpos.ne'⟩
  obtain ⟨g, t, hgen, hgorder, htred, htpow⟩ :=
    exists_teichmullerGenerator F
  let zA : A.unitGroup := A.unitGroupMulEquiv.symm t
  let z : Units F := zA
  have hzred : A.unitGroupToResidueFieldUnits zA = g := by
    exact htred
  have hzt : z = ringUnitsToFieldUnits F t := by
    rfl
  have hmapinj : Function.Injective (ringUnitsToFieldUnits F) :=
    Units.map_injective (fun x y h => Subtype.ext h)
  have hzorder : orderOf z = N := by
    rw [hzt, orderOf_injective (ringUnitsToFieldUnits F) hmapinj]
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one htpow
    · have hgorder' : orderOf g = N := hgorder
      have hdiv := orderOf_map_dvd
        (Units.map (IsLocalRing.residue R).toMonoidHom) t
      have htred' : Units.map (IsLocalRing.residue R).toMonoidHom t = g :=
        htred
      rw [htred'] at hdiv
      exact hgorder' ▸ hdiv
  let T : Subgroup (Units F) := Subgroup.zpowers z
  let zT : T := ⟨z, Subgroup.mem_zpowers z⟩
  have hzTgen : ∀ x : T, x ∈ Subgroup.zpowers zT := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    apply Subgroup.mem_zpowers_iff.mpr
    exact ⟨n, Subtype.ext hn⟩
  have hcardT : Nat.card T = N := by
    rw [Nat.card_zpowers, hzorder]
  let ez : Multiplicative (ZMod N) ≃* T :=
    zmodMulEquivOfGenerator hzTgen hcardT
  letI : Finite T := Finite.of_equiv
    (Multiplicative (ZMod N)) ez.toEquiv
  have hTle : T ≤ A.unitGroup :=
    Subgroup.zpowers_le.mpr zA.property
  let ti : T →* A.unitGroup :=
    MonoidHom.codRestrict T.subtype A.unitGroup
      (fun x => hTle x.property)
  let tr : T →* Units k := A.unitGroupToResidueFieldUnits.comp ti
  have htrz : tr zT = g := by
    exact hzred
  have htrsurj : Function.Surjective tr := by
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen y)
    refine ⟨zT ^ n, ?_⟩
    rw [map_zpow, htrz]
    exact hn
  have hcardk : Nat.card (Units k) = N := by
    rw [Nat.card_units]
    rfl
  have htrbij : Function.Bijective tr :=
    (Nat.bijective_iff_surjective_and_card tr).mpr
      ⟨htrsurj, hcardT.trans hcardk.symm⟩
  let trEquiv : T ≃* Units k := MulEquiv.ofBijective tr htrbij
  letI : TopologicalSpace (Units k) := ⊥
  letI : DiscreteTopology (Units k) := ⟨rfl⟩
  letI : DiscreteTopology T := inferInstance
  let ctr : T ≃ₜ* Units k :=
    ContinuousMulEquiv.mk'
      (Homeomorph.mk trEquiv.toEquiv
        continuous_of_discreteTopology continuous_of_discreteTopology)
      trEquiv.map_mul
  let cez : T ≃ₜ* Multiplicative (ZMod N) :=
    (ContinuousMulEquiv.mk'
      (Homeomorph.mk ez.toEquiv
        continuous_of_discreteTopology continuous_of_discreteTopology)
      ez.map_mul).symm
  let r := A.unitGroupToResidueFieldUnits
  let sec : Units k →* A.unitGroup :=
    ti.comp trEquiv.symm.toMonoidHom
  have hsec (y : Units k) : r (sec y) = y := by
    change tr (trEquiv.symm y) = y
    exact trEquiv.apply_symm_apply y
  let eR : A.unitGroup ≃* Units k × r.ker :=
    { toFun := fun u =>
        (r u, ⟨(sec (r u))⁻¹ * u, by
          change r ((sec (r u))⁻¹ * u) = 1
          rw [map_mul, map_inv, hsec]
          simp⟩)
      invFun := fun y => sec y.1 * y.2
      left_inv := fun u => by
        dsimp
        simp
      right_inv := fun y => by
        have hry : r (sec y.1 * y.2) = y.1 := by
          rw [map_mul, hsec, y.2.property, mul_one]
        apply Prod.ext
        · exact hry
        · apply Subtype.ext
          change (sec (r (sec y.1 * y.2)))⁻¹ *
            (sec y.1 * y.2) = y.2
          rw [hry]
          simp
      map_mul' := fun x y => by
        apply Prod.ext
        · exact map_mul r x y
        · apply Subtype.ext
          change (sec (r (x * y)))⁻¹ * (x * y) =
            ((sec (r x))⁻¹ * x) * ((sec (r y))⁻¹ * y)
          rw [map_mul, map_mul, mul_inv_rev]
          ac_rfl }
  have hrkerOpen : IsOpen (r.ker : Set A.unitGroup) := by
    rw [show r.ker = Subgroup.comap A.unitGroup.subtype
      A.principalUnitGroup from A.ker_unitGroupToResidueFieldUnits]
    exact (principalUnitGroup_isOpen F).preimage continuous_subtype_val
  have hr : Continuous r :=
    continuous_monoidHom_of_isOpen_ker r hrkerOpen
  have hsecContinuous : Continuous sec := continuous_of_discreteTopology
  have heR : Continuous eR := by
    apply Continuous.prodMk hr
    exact Continuous.subtype_mk
      ((hsecContinuous.comp hr).inv.mul continuous_id) _
  have heRi : Continuous eR.symm := by
    exact (hsecContinuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  let ceR : A.unitGroup ≃ₜ* Units k × r.ker :=
    ContinuousMulEquiv.mk' (Homeomorph.mk eR.toEquiv heR heRi)
      eR.map_mul
  let P := A.principalUnitGroup
  let eK : r.ker ≃* P :=
    { toFun := fun x => ⟨((x : A.unitGroup) : Units F), by
        change (x : A.unitGroup) ∈ Subgroup.comap A.unitGroup.subtype P
        rw [← A.ker_unitGroupToResidueFieldUnits]
        exact x.property⟩
      invFun := fun x =>
        ⟨⟨(x : Units F), principalUnitGroup_le_unitGroup F x.property⟩, by
          rw [A.ker_unitGroupToResidueFieldUnits]
          exact x.property⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        rfl }
  have heK : Continuous eK := by
    dsimp only [eK]
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  have heKi : Continuous eK.symm := by
    dsimp only [eK]
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let ceK : r.ker ≃ₜ* P :=
    ContinuousMulEquiv.mk' (Homeomorph.mk eK.toEquiv heK heKi)
      eK.map_mul
  exact ⟨{
    teichmullerFactor := T
    unitEquiv := ceR.trans
      (continuousMulEquivProdCongr ctr.symm ceK)
    teichmullerEquiv := cez }⟩

end TeichmullerSplitting

/-- The precise module-theoretic datum extracted from the cofinal filtration
of deep principal units.  This is the only input needed by the complete-PID
classification layer below. -/
private structure DeepPrincipalUnitModuleData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (p : Nat.Primes) (rank : ℕ) where
  module : Module ℤ_[p]
    (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  compactSpace : CompactSpace
    (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  continuousSMul : let _ := module
    ContinuousSMul ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  moduleFinite : let _ := module
    Module.Finite ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  quotientFinrank : let _ := module
    Module.finrank ℤ_[p]
      ((Additive
          (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) ⧸
        Submodule.torsion ℤ_[p]
          (Additive
            (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)) =
      rank
  pPowerTorsion_spec : let _ := module
    ∀ u : Units F,
      (∃ hu : u ∈
          (ValuativeRel.valuation F).valuationSubring.principalUnitGroup,
        Additive.ofMul
          (⟨u, hu⟩ :
            (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) ∈
          Submodule.torsion ℤ_[p]
            (Additive
              (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)) ↔
        ∃ a : ℕ, u ^ ((p : ℕ) ^ a) = 1

/-- The two factors supplied by the complete-PID classification of principal
units. -/
private structure PrincipalUnitDecompositionData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (p : Nat.Primes) (rank : ℕ) where
  pPowerTorsion : Subgroup (Units F)
  freePrincipalUnits : Subgroup (Units F)
  principalEquiv :
    (ValuativeRel.valuation F).valuationSubring.principalUnitGroup ≃ₜ*
      pPowerTorsion × freePrincipalUnits
  pPowerTorsion_spec : ∀ u : Units F,
    u ∈ pPowerTorsion ↔ ∃ a : ℕ, u ^ ((p : ℕ) ^ a) = 1
  freePrincipalUnitsEquiv :
    freePrincipalUnits ≃ₜ* Multiplicative (Fin rank → ℤ_[p])

/-- Classify the principal-unit module once the datum extracted from deep
units has been supplied. -/
private theorem principalUnitDecompositionData_exists
    (F : Type*) [Field F] [ValuativeRel F] [UniformSpace F]
    [IsUniformAddGroup F] [IsNonarchimedeanLocalField F]
    (p : Nat.Primes) (rank : ℕ)
    (d : DeepPrincipalUnitModuleData F p rank) :
    Nonempty (PrincipalUnitDecompositionData F p rank) := by
  let P := (ValuativeRel.valuation F).valuationSubring.principalUnitGroup
  let M := Additive P
  letI : Module ℤ_[p] M := d.module
  letI : CompactSpace M := d.compactSpace
  letI : T2Space M := T2Space.of_injective_continuous
    Additive.toMul.injective continuous_id
  letI : ContinuousSMul ℤ_[p] M := d.continuousSMul
  letI : Module.Finite ℤ_[p] M := d.moduleFinite
  let T := Submodule.torsion ℤ_[p] M
  let V := Fin rank → ℤ_[p]
  letI : AddCommGroup T := inferInstance
  letI : Group (Multiplicative T) := inferInstance
  letI : Finite T := padicModule_torsion_finite p M
  obtain ⟨c⟩ := padicModule_torsionProdFreeContinuousAddEquiv p M
  rw [d.quotientFinrank] at c
  let cm : P ≃* Multiplicative T × Multiplicative V :=
    { toFun := fun u =>
        (Multiplicative.ofAdd (c.symm (Additive.ofMul u)).1,
          Multiplicative.ofAdd (c.symm (Additive.ofMul u)).2)
      invFun := fun z =>
        Additive.toMul (c (Multiplicative.toAdd z.1,
          Multiplicative.toAdd z.2))
      left_inv := fun u => by
        apply Additive.ofMul.injective
        exact c.apply_symm_apply (Additive.ofMul u)
      right_inv := fun z => by
        apply Prod.ext <;> apply Multiplicative.toAdd.injective
        · exact congrArg Prod.fst
            (c.symm_apply_apply
              (Multiplicative.toAdd z.1, Multiplicative.toAdd z.2))
        · exact congrArg Prod.snd
            (c.symm_apply_apply
              (Multiplicative.toAdd z.1, Multiplicative.toAdd z.2))
      map_mul' := fun x y => by
        apply Prod.ext <;> apply Multiplicative.toAdd.injective
        · exact congrArg Prod.fst (c.symm.map_add
            (Additive.ofMul x) (Additive.ofMul y))
        · exact congrArg Prod.snd (c.symm.map_add
            (Additive.ofMul x) (Additive.ofMul y)) }
  have hcm : Continuous cm := by
    change Continuous fun u : P => c.symm (Additive.ofMul u)
    exact c.symm.continuous
  have hcmi : Continuous cm.symm := by
    change Continuous fun z : T × V => c z
    exact c.continuous
  let ccm : P ≃ₜ* Multiplicative T × Multiplicative V :=
    ContinuousMulEquiv.mk' (Homeomorph.mk cm.toEquiv hcm hcmi) cm.map_mul
  let ti : Multiplicative T →* Units F :=
    { toFun := fun x =>
        (((Multiplicative.toAdd x : T).1.toMul : P) : Units F)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hti : Function.Injective ti := by
    intro x y h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact h
  let vAxis : V →+ T × V :=
    { toFun := fun x => (0, x)
      map_zero' := rfl
      map_add' := fun _ _ => by simp }
  let viP : Multiplicative V →* P :=
    (AddEquiv.toMultiplicative c.toAddEquiv).toMonoidHom.comp
      (AddMonoidHom.toMultiplicative vAxis)
  let vi : Multiplicative V →* Units F := P.subtype.comp viP
  have hvi : Function.Injective vi := by
    intro x y h
    apply Multiplicative.toAdd.injective
    have hc : c (0, Multiplicative.toAdd x) =
        c (0, Multiplicative.toAdd y) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact h
    exact congrArg Prod.snd (c.injective hc)
  let tf := ti.rangeRestrict
  let te : Multiplicative T ≃* ti.range :=
    MulEquiv.ofBijective tf
      ⟨fun _ _ h => hti
          (congrArg (fun z : ti.range => (z : Units F)) h),
        MonoidHom.rangeRestrict_surjective _⟩
  letI : Finite (Multiplicative T) :=
    Finite.of_equiv T Multiplicative.toAdd
  have htf : Continuous tf := by
    apply Continuous.subtype_mk
    change Continuous fun x : T =>
      (((x : Additive P).toMul : P) : Units F)
    exact continuous_subtype_val.comp continuous_subtype_val
  let cte : Multiplicative T ≃ₜ* ti.range :=
    ContinuousMulEquiv.mk' htf.homeoOfEquivCompactToT2 te.map_mul
  let vf := vi.rangeRestrict
  let ve : Multiplicative V ≃* vi.range :=
    MulEquiv.ofBijective vf
      ⟨fun _ _ h => hvi
          (congrArg (fun z : vi.range => (z : Units F)) h),
        MonoidHom.rangeRestrict_surjective _⟩
  have hviContinuous : Continuous vi := by
    change Continuous fun x : V =>
      ((Additive.toMul (c (0, x)) : P) : Units F)
    exact continuous_subtype_val.comp
      (c.continuous.comp (continuous_const.prodMk continuous_id))
  have hvf : Continuous vf :=
    Continuous.subtype_mk hviContinuous _
  let cve : Multiplicative V ≃ₜ* vi.range :=
    ContinuousMulEquiv.mk' hvf.homeoOfEquivCompactToT2 ve.map_mul
  let ec := ccm.trans (continuousMulEquivProdCongr cte cve)
  refine ⟨{
    pPowerTorsion := ti.range
    freePrincipalUnits := vi.range
    principalEquiv := ec
    pPowerTorsion_spec := ?_
    freePrincipalUnitsEquiv := cve.symm }⟩
  intro u
  constructor
  · rintro ⟨x, rfl⟩
    apply (d.pPowerTorsion_spec _).mp
    refine ⟨((Multiplicative.toAdd x : T).1.toMul : P).property, ?_⟩
    exact (Multiplicative.toAdd x : T).property
  · intro hpw
    obtain ⟨hu, htu⟩ := (d.pPowerTorsion_spec u).mpr hpw
    let x : T := ⟨Additive.ofMul (⟨u, hu⟩ : P), htu⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    rfl

/-- The output package consumed by `LocalInvariants` after classifying the
cofinal deep principal-unit lattice over the complete PID `ℤ_p`.

The last factor is the profinite finite-rank `ℤ_p`-module.  Together with the
first two factors, `productEquiv` records the valuation/Teichmüller product
decomposition; `pPowerTorsion_spec` separates the finite torsion before the
free lattice is formed. -/
structure LocalUnitDecompositionData
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes) (rank : ℕ) where
  valuationFactor : Subgroup (Units (v.adicCompletion K))
  teichmullerFactor : Subgroup (Units (v.adicCompletion K))
  pPowerTorsion : Subgroup (Units (v.adicCompletion K))
  freePrincipalUnits : Subgroup (Units (v.adicCompletion K))
  productEquiv :
    Units (v.adicCompletion K) ≃ₜ*
      valuationFactor × teichmullerFactor × pPowerTorsion ×
        freePrincipalUnits
  valuationEquiv : valuationFactor ≃ₜ* Multiplicative ℤ
  teichmullerEquiv :
    teichmullerFactor ≃ₜ*
      Multiplicative (ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1))
  pPowerTorsion_spec : ∀ u : Units (v.adicCompletion K),
    u ∈ pPowerTorsion ↔ ∃ a : ℕ, u ^ ((p : ℕ) ^ a) = 1
  freePrincipalUnitsEquiv :
    freePrincipalUnits ≃ₜ*
      Multiplicative
        (Fin rank → ℤ_[p])

/-- The `ℤ_p`-action and its continuity, extracted from the cofinal deep-unit
filtration. -/
private structure DeepPrincipalUnitActionData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (p : Nat.Primes) where
  module : Module ℤ_[p]
    (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  continuousSMul : let _ := module
    ContinuousSMul ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)

/-- The finite lattice and its rank after quotienting by torsion. -/
private structure DeepPrincipalUnitLatticeData
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (p : Nat.Primes) (rank : ℕ)
    (module : Module ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)) where
  moduleFinite : let _ := module
    Module.Finite ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)
  quotientFinrank : let _ := module
    Module.finrank ℤ_[p]
      ((Additive
          (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) ⧸
        Submodule.torsion ℤ_[p]
          (Additive
            (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)) =
      rank

/-- Assemble the continuous `ℤ_p`-action from the deep-unit filtration. -/
private theorem deepUnitFiltration_actionData_exists
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    Nonempty (DeepPrincipalUnitActionData (v.adicCompletion K) p) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  let w := ValuativeRel.valuation F
  let vF := (Valued.v : Valuation F ℤᵐ⁰)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  let A := w.valuationSubring
  let P := A.principalUnitGroup
  let M := Additive P
  let B := v.adicCompletionIntegers K
  letI : CompactSpace P := isCompact_iff_compactSpace.mp
    (completionPrincipalUnitGroup_isCompact v)
  let r : P → F := fun u => (u : Units F) - 1
  have hr : Continuous r :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  have hrnorm (u : P) : ‖r u‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    have hw : w (r u) < w 1 := by
      apply (Valuation.isEquiv_valuation_valuationSubring w).lt_iff_lt.mpr
      have hu := (A.mem_principalUnitGroup_iff (u : Units F)).mp u.property
      simpa only [map_one] using hu
    have hv : vF (r u) < vF 1 :=
      (ValuativeRel.isEquiv w vF).lt_iff_lt.mp hw
    simpa [vF] using hv
  obtain ⟨u₀, -, hu₀⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hr.norm.continuousOn
  let q : ℝ := ‖r u₀‖
  have hq_nonneg : 0 ≤ q := norm_nonneg _
  have hq_lt_one : q < 1 := hrnorm u₀
  have hr_le (u : P) : ‖r u‖ ≤ q := hu₀ (Set.mem_univ u)
  let coeffMap : ℤ_[p] → F := fun z =>
    ((padicIntegerPlaceMap v p hp z : B) : F)
  have hcoeffMap : Continuous coeffMap :=
    continuous_subtype_val.comp (continuous_padicIntegerPlaceMap v p hp)
  have hcoeffMap_norm (z : ℤ_[p]) : ‖coeffMap z‖ ≤ 1 := by
    apply Valued.toNormedField.norm_le_one_iff.mpr
    exact (padicIntegerPlaceMap v p hp z).property
  let term (n : ℕ) : C(ℤ_[p] × P, F) :=
    ⟨fun x => coeffMap (Ring.choose x.1 n) * r x.2 ^ n,
      (hcoeffMap.comp
        ((PadicInt.continuous_choose n).comp continuous_fst)).mul
        ((hr.comp continuous_snd).pow n)⟩
  have hterm_norm (n : ℕ) : ‖term n‖ ≤ q ^ n := by
    rw [ContinuousMap.norm_le_of_nonempty]
    intro x
    change ‖coeffMap (Ring.choose x.1 n) * r x.2 ^ n‖ ≤ q ^ n
    rw [norm_mul, norm_pow]
    calc
      ‖coeffMap (Ring.choose x.1 n)‖ * ‖r x.2‖ ^ n ≤
          1 * q ^ n := mul_le_mul
        (hcoeffMap_norm _) (pow_le_pow_left₀ (norm_nonneg _) (hr_le _) n)
        (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = q ^ n := one_mul _
  have hterm_zero : Filter.Tendsto term Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg (term n)) hterm_norm
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
  have hterm_summable : Summable term :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by
      simpa only [Nat.cofinite_eq_atTop] using hterm_zero)
  let power : C(ℤ_[p] × P, F) := ∑' n, term n
  have hpower_apply (z : ℤ_[p]) (u : P) :
      power (z, u) = ∑' n, term n (z, u) := by
    exact (ContinuousMap.tsum_apply hterm_summable (z, u)).symm
  have hpower_nat (m : ℕ) (u : P) :
      power ((m : ℤ_[p]), u) = ((u : Units F) : F) ^ m := by
    rw [hpower_apply, tsum_eq_sum (s := Finset.range (m + 1))]
    · change (∑ n ∈ Finset.range (m + 1),
          coeffMap (Ring.choose (m : ℤ_[p]) n) * r u ^ n) = _
      simp only [Ring.choose_natCast]
      have hcoeffNat (n : ℕ) : coeffMap (n : ℤ_[p]) = (n : F) := by
        change ((padicIntegerPlaceMap v p hp (n : ℤ_[p]) : B) : F) = (n : F)
        rw [map_natCast]
        rfl
      simp_rw [hcoeffNat]
      rw [show ((u : Units F) : F) = r u + 1 by simp [r]]
      simpa [add_pow, mul_comm, mul_left_comm, mul_assoc]
    · intro n hn
      have hmn : m < n := by
        have : m + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
        omega
      change coeffMap (Ring.choose (m : ℤ_[p]) n) * r u ^ n = 0
      rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hmn]
      simp [coeffMap]
  have hpower_zero (u : P) : power (0, u) = 1 := by
    simpa using hpower_nat 0 u
  have hpower_add (z₁ z₂ : ℤ_[p]) (u : P) :
      power (z₁ + z₂, u) = power (z₁, u) * power (z₂, u) := by
    let f : ℤ_[p] × ℤ_[p] → F := fun z => power (z.1 + z.2, u)
    let g : ℤ_[p] × ℤ_[p] → F := fun z => power (z.1, u) * power (z.2, u)
    have hf : Continuous f := power.continuous.comp
      ((continuous_fst.add continuous_snd).prodMk continuous_const)
    have hg : Continuous g :=
      (power.continuous.comp (continuous_fst.prodMk continuous_const)).mul
        (power.continuous.comp (continuous_snd.prodMk continuous_const))
    have hfg : f = g :=
      (PadicInt.denseRange_natCast.prodMap
        PadicInt.denseRange_natCast).equalizer hf hg (by
          funext z
          change f ((z.1 : ℤ_[p]), (z.2 : ℤ_[p])) =
            g ((z.1 : ℤ_[p]), (z.2 : ℤ_[p]))
          dsimp only [f, g]
          rw [← Nat.cast_add, hpower_nat, hpower_nat, hpower_nat, pow_add])
    exact congrFun hfg (z₁, z₂)
  let powerUnit (z : ℤ_[p]) (u : P) : Units F :=
    { val := power (z, u)
      inv := power (-z, u)
      val_inv := by rw [← hpower_add, add_neg_cancel, hpower_zero]
      inv_val := by rw [← hpower_add, neg_add_cancel, hpower_zero] }
  have hpowerUnit_continuous :
      Continuous fun x : ℤ_[p] × P => powerUnit x.1 x.2 := by
    rw [Units.continuous_iff]
    constructor
    · exact power.continuous
    · exact power.continuous.comp
        ((continuous_fst.neg.prodMk continuous_snd))
  have hPclosed : IsClosed (P : Set (Units F)) :=
    P.isClosed_of_isOpen (principalUnitGroup_isOpen F)
  have hpowerUnit_mem (z : ℤ_[p]) (u : P) : powerUnit z u ∈ P := by
    refine DenseRange.induction_on PadicInt.denseRange_natCast z ?_ ?_
    · exact hPclosed.preimage
        (hpowerUnit_continuous.comp (continuous_id.prodMk continuous_const))
    · intro n
      have heq : powerUnit (n : ℤ_[p]) u = (u : Units F) ^ n := by
        apply Units.ext
        exact hpower_nat n u
      rw [heq]
      exact P.pow_mem u.property n
  let powerP (z : ℤ_[p]) (u : P) : P :=
    ⟨powerUnit z u, hpowerUnit_mem z u⟩
  have hpowerP_continuous :
      Continuous fun x : ℤ_[p] × P => powerP x.1 x.2 :=
    Continuous.subtype_mk hpowerUnit_continuous _
  have hpower_mul_base (z : ℤ_[p]) (u₁ u₂ : P) :
      powerP z (u₁ * u₂) = powerP z u₁ * powerP z u₂ := by
    apply Subtype.ext
    apply Units.ext
    let f : ℤ_[p] → F := fun a => power (a, u₁ * u₂)
    let g : ℤ_[p] → F := fun a => power (a, u₁) * power (a, u₂)
    have hf : Continuous f :=
      power.continuous.comp (continuous_id.prodMk continuous_const)
    have hg : Continuous g :=
      (power.continuous.comp (continuous_id.prodMk continuous_const)).mul
        (power.continuous.comp (continuous_id.prodMk continuous_const))
    have hfg : f = g := PadicInt.denseRange_natCast.equalizer hf hg (by
      funext n
      change power ((n : ℤ_[p]), u₁ * u₂) =
        power ((n : ℤ_[p]), u₁) * power ((n : ℤ_[p]), u₂)
      simp only [hpower_nat, Subgroup.coe_mul, Units.val_mul, mul_pow])
    exact congrFun hfg z
  have hpower_mul_scalar (z₁ z₂ : ℤ_[p]) (u : P) :
      powerP (z₁ * z₂) u = powerP z₁ (powerP z₂ u) := by
    apply Subtype.ext
    apply Units.ext
    let f : ℤ_[p] × ℤ_[p] → F := fun z => power (z.1 * z.2, u)
    let g : ℤ_[p] × ℤ_[p] → F := fun z => power (z.1, powerP z.2 u)
    have hf : Continuous f := power.continuous.comp
      ((continuous_fst.mul continuous_snd).prodMk continuous_const)
    have hg : Continuous g := power.continuous.comp
      (continuous_fst.prodMk
        (hpowerP_continuous.comp (continuous_snd.prodMk continuous_const)))
    have hfg : f = g :=
      (PadicInt.denseRange_natCast.prodMap
        PadicInt.denseRange_natCast).equalizer hf hg (by
          funext z
          change f ((z.1 : ℤ_[p]), (z.2 : ℤ_[p])) =
            g ((z.1 : ℤ_[p]), (z.2 : ℤ_[p]))
          dsimp only [f, g]
          rw [← Nat.cast_mul, hpower_nat, hpower_nat]
          rw [show (((powerP (z.2 : ℤ_[p]) u : P) : Units F) : F) =
            ((u : Units F) : F) ^ z.2 from hpower_nat z.2 u]
          rw [← pow_mul, Nat.mul_comm])
    exact congrFun hfg (z₁, z₂)
  let smul : SMul ℤ_[p] M :=
    ⟨fun z u => Additive.ofMul (powerP z (Additive.toMul u))⟩
  let module : Module ℤ_[p] M := @Module.ofMinimalAxioms ℤ_[p] M _ _ smul
    (fun z u₁ u₂ => by
      apply Additive.toMul.injective
      exact hpower_mul_base z (Additive.toMul u₁) (Additive.toMul u₂))
    (fun z₁ z₂ u => by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact hpower_add z₁ z₂ (Additive.toMul u))
    (fun z₁ z₂ u => by
      apply Additive.toMul.injective
      exact hpower_mul_scalar z₁ z₂ (Additive.toMul u))
    (fun u => by
      change Additive.ofMul (powerP (1 : ℤ_[p]) (Additive.toMul u)) = u
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      simpa using hpower_nat 1 (Additive.toMul u))
  let continuousSMul : let _ := module; ContinuousSMul ℤ_[p] M := by
    letI : Module ℤ_[p] M := module
    exact ⟨by
      change Continuous fun x : ℤ_[p] × P => powerP x.1 x.2
      exact hpowerP_continuous⟩
  exact ⟨{
    module := module
    continuousSMul := continuousSMul }⟩

/-- Principal units in the local completion form a compact space. -/
private theorem deepUnitFiltration_compactSpace_exists
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    Nonempty (CompactSpace
      (Additive
        (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring.principalUnitGroup)) := by
  exact ⟨isCompact_iff_compactSpace.mp
    (completionPrincipalUnitGroup_isCompact v)⟩

/-- The residue prime is topologically nilpotent in the completion. -/
private theorem completion_residuePrime_norm_lt_one
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    ‖(p : v.adicCompletion K)‖ < 1 := by
  have hpQ : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    exact (inv_lt_one₀ hpR).2 (by exact_mod_cast p.2.one_lt)
  have htQ : Filter.Tendsto (fun n => (p : ℚ_[p]) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hpQ
  have htF : Filter.Tendsto
      (fun n => (p : v.adicCompletion K) ^ n)
      Filter.atTop (nhds 0) := by
    have hmap :=
      (continuous_padicPlaceMap v p hp).continuousAt.tendsto.comp htQ
    rw [map_zero] at hmap
    apply hmap.congr'
    filter_upwards with n
    change padicPlaceMap v p hp ((p : ℚ_[p]) ^ n) =
      (p : v.adicCompletion K) ^ n
    rw [map_pow, map_natCast]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp htF

/-- A rational integer prime to the residue characteristic remains a unit
in the completed integer ring. -/
private theorem completion_natCast_norm_eq_one_of_coprime
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (n : ℕ) (hn : (p : ℕ).Coprime n) :
    ‖(n : v.adicCompletion K)‖ = 1 := by
  let B := v.adicCompletionIntegers K
  let z : ℤ_[p] := n
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr hn)
  have hzmap : IsUnit (padicIntegerPlaceMap v p hp z) :=
    hz.map (padicIntegerPlaceMap v p hp)
  obtain ⟨u, hu⟩ := hzmap
  have hnormu : ‖(((u : B) : v.adicCompletion K))‖ = 1 := by
    rw [NumberField.FinitePlace.norm_def]
    have hv : Valued.v (((u : B) : v.adicCompletion K)) = 1 := by
      exact (Valuation.integer.integers
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).valuation_unit u
    rw [hv]
    simp
  have hmapval : (padicIntegerPlaceMap v p hp z : B) = u := hu.symm
  rw [← hmapval] at hnormu
  have hcoe :
      ((padicIntegerPlaceMap v p hp z : B) : v.adicCompletion K) =
        (n : v.adicCompletion K) := by
    rw [show z = (n : ℤ_[p]) from rfl, map_natCast]
    rfl
  rw [← hcoe]
  exact hnormu

/-- Factorial denominators have at most geometric growth in the completed
nonarchimedean norm. -/
private theorem completion_factorial_inv_norm_le
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (n : ℕ) :
    ‖((n.factorial : v.adicCompletion K)⁻¹)‖ ≤
      ‖(p : v.adicCompletion K)‖⁻¹ ^ n := by
  let k := padicValNat (p : ℕ) n.factorial
  have hfact : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hpk : (p : ℕ) ^ k ∣ n.factorial :=
    (padicValNat_dvd_iff_le hfact).mpr le_rfl
  let m := n.factorial / (p : ℕ) ^ k
  have hfac : (p : ℕ) ^ k * m = n.factorial :=
    Nat.mul_div_cancel' hpk
  have hmnot : ¬(p : ℕ) ∣ m := by
    intro hm
    apply pow_succ_padicValNat_not_dvd (p := (p : ℕ)) hfact
    obtain ⟨t, ht⟩ := hm
    have hd : (p : ℕ) ^ (k + 1) ∣ (p : ℕ) ^ k * m := by
      refine ⟨t, ?_⟩
      rw [ht, pow_succ]
      ac_rfl
    exact hd.trans (dvd_of_eq hfac)
  have hmcop : (p : ℕ).Coprime m :=
    p.2.coprime_iff_not_dvd.mpr hmnot
  have hnormm : ‖(m : v.adicCompletion K)‖ = 1 :=
    completion_natCast_norm_eq_one_of_coprime v p hp m hmcop
  have hnormfac : ‖(n.factorial : v.adicCompletion K)‖ =
      ‖(p : v.adicCompletion K)‖ ^ k := by
    rw [← hfac, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
      hnormm, mul_one]
  rw [norm_inv, hnormfac, ← inv_pow]
  apply pow_le_pow_right₀
  · have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
    have hpF : (p : v.adicCompletion K) ≠ 0 := by
      simpa using
        (map_ne_zero (algebraMap K (v.adicCompletion K))).mpr hpK
    exact (one_le_inv₀ (norm_pos_iff.mpr hpF)).mpr
      (IsUltrametricDist.norm_natCast_le_one (v.adicCompletion K) (p : ℕ))
  · exact padicValNat_factorial_le (p : ℕ) n

set_option maxHeartbeats 800000 in
/-- The exponential series has a nonzero convergence radius over the
number-field completion. -/
private theorem completion_expSeries_radius_pos
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    let F := v.adicCompletion K
    let hF : NontriviallyNormedField F :=
      Valued.toNontriviallyNormedField F ℤᵐ⁰
    letI : Field F := hF.toNormedField.toField
    letI : NontriviallyNormedField F := hF
    0 < (NormedSpace.expSeries F F).radius := by
  let F := v.adicCompletion K
  let ρ : ℝ := ‖(p : F)‖
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  have hpF : (p : F) ≠ 0 := by
    simpa using (map_ne_zero (algebraMap K F)).mpr hpK
  have hρpos : 0 < ρ := norm_pos_iff.mpr hpF
  have hρlt : ρ < 1 := completion_residuePrime_norm_lt_one v p hp
  let hF : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F ℤᵐ⁰
  letI : Field F := hF.toNormedField.toField
  letI : NontriviallyNormedField F := hF
  dsimp only
  let r : NNReal := ⟨ρ ^ 2, sq_nonneg ρ⟩
  have hs : Summable fun n =>
      ‖NormedSpace.expSeries F F n‖ * (r : ℝ) ^ n := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.property n))
      (fun n => ?_) (summable_geometric_of_lt_one hρpos.le hρlt)
    have hc : ‖NormedSpace.expSeries F F n‖ ≤ ρ⁻¹ ^ n := by
      rw [NormedSpace.expSeries_eq_ofScalars,
        FormalMultilinearSeries.ofScalars_norm]
      exact completion_factorial_inv_norm_le v p hp n
    calc
      ‖NormedSpace.expSeries F F n‖ * (r : ℝ) ^ n ≤
          ρ⁻¹ ^ n * (ρ ^ 2) ^ n :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg (sq_nonneg ρ) n)
      _ = ρ ^ n := by
        rw [← mul_pow]
        field_simp
  have hrle : (r : ENNReal) ≤
      (NormedSpace.expSeries F F).radius :=
    (NormedSpace.expSeries F F).le_radius_of_summable_norm hs
  have hrpos : 0 < r := by
    change 0 < ρ ^ 2
    positivity
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hrpos) hrle

/-- On a sufficiently small completed-integer lattice, the local
exponential is an injective `ℤ_p`-linear map with open image in the
principal units. -/
private theorem deepUnitFiltration_exponentialLattice_exists
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (module : Module ℤ_[p]
      (Additive
        (completionValuativeRel v).valuation.valuationSubring.principalUnitGroup))
    (continuousSMul : let _ := module
      ContinuousSMul ℤ_[p]
        (Additive
          (completionValuativeRel v).valuation.valuationSubring.principalUnitGroup)) :
    let F := v.adicCompletion K
    let B := v.adicCompletionIntegers K
    letI : ValuativeRel F := completionValuativeRel v
    letI : Algebra ℤ_[p] B := (padicIntegerPlaceMap v p hp).toAlgebra
    let _ := module
    ∃ L : B →ₗ[ℤ_[p]]
        Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup,
      Function.Injective L ∧ IsOpen (L.range : Set
        (Additive
          (ValuativeRel.valuation F).valuationSubring.principalUnitGroup)) := by
  let F := v.adicCompletion K
  let B := v.adicCompletionIntegers K
  let completionTopology : TopologicalSpace F := inferInstance
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  let w := ValuativeRel.valuation F
  let vF := (Valued.v : Valuation F ℤᵐ⁰)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  let A := w.valuationSubring
  let P := A.principalUnitGroup
  let M := Additive P
  letI : Module ℤ_[p] M := module
  letI : ContinuousSMul ℤ_[p] M := continuousSMul
  letI : Algebra ℤ_[p] B := (padicIntegerPlaceMap v p hp).toAlgebra
  let hF : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F ℤᵐ⁰
  letI : NontriviallyNormedField F := hF
  letI : CharZero F := ⟨by
    intro m n hmn
    apply Nat.cast_injective (R := K)
    apply (algebraMap K F).injective
    simpa using hmn⟩
  letI : CompleteSpace F := inferInstance
  have htopology :
      hF.toNormedField.toUniformSpace.toTopologicalSpace =
        completionTopology := by
    rfl
  have hradius : 0 < (NormedSpace.expSeries F F).radius := by
    simpa only [F, hF] using completion_expSeries_radius_pos v p hp
  have hderiv :=
    hasStrictFDerivAt_exp_zero_of_radius_pos
      (𝕂 := F) (𝔸 := F) hradius
  have hderiv' : HasStrictFDerivAt NormedSpace.exp
      ((1 : F ≃L[F] F) : F →L[F] F) 0 := by
    simpa using hderiv
  let e := hderiv'.toOpenPartialHomeomorph NormedSpace.exp
  have he0 : (0 : F) ∈ e.source :=
    hderiv'.mem_toOpenPartialHomeomorph_source
  have heNhds : e.source ∈ nhds (0 : F) :=
    e.open_source.mem_nhds he0
  have hballNhds : Metric.eball (0 : F)
      (NormedSpace.expSeries F F).radius ∈ nhds 0 :=
    Metric.eball_mem_nhds _ hradius
  have hprincipal : {x : F | ‖NormedSpace.exp x - 1‖ < 1} ∈ nhds 0 := by
    have hcont : ContinuousAt
        (fun x : F => NormedSpace.exp x - 1) 0 :=
      hderiv.continuousAt.sub continuousAt_const
    have htarget : Metric.ball (0 : F) 1 ∈
        nhds ((fun x : F => NormedSpace.exp x - 1) 0) := by
      simpa only [NormedSpace.exp_zero, sub_self] using
        Metric.ball_mem_nhds (0 : F) zero_lt_one
    have heq : {x : F | ‖NormedSpace.exp x - 1‖ < 1} =
        (fun x : F => NormedSpace.exp x - 1) ⁻¹'
          Metric.ball 0 1 := by
      ext x
      simp [Metric.mem_ball, dist_zero_right]
    rw [heq]
    exact hcont htarget
  have hgood : e.source ∩
      (Metric.eball (0 : F) (NormedSpace.expSeries F F).radius ∩
        {x : F | ‖NormedSpace.exp x - 1‖ < 1}) ∈ nhds 0 :=
    Filter.inter_mem heNhds (Filter.inter_mem hballNhds hprincipal)
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp hgood
  rw [Metric.isOpen_iff] at hUopen
  obtain ⟨ε, hεpos, hballU⟩ := hUopen 0 h0U
  have hpNorm : ‖(p : F)‖ < 1 :=
    completion_residuePrime_norm_lt_one v p hp
  have hpPow : Filter.Tendsto (fun n : ℕ => (p : F) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hpNorm
  have hpEventually : ∀ᶠ n in Filter.atTop,
      (p : F) ^ n ∈ Metric.ball (0 : F) ε :=
    hpPow (Metric.ball_mem_nhds _ hεpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpEventually
  let c : F := (p : F) ^ N
  have hcNorm : ‖c‖ < ε := by
    have h := hN N le_rfl
    simpa only [c, Metric.mem_ball, dist_zero_right] using h
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)
  let cx : B → F := fun b => c * (b : F)
  have hBnorm (b : B) : ‖(b : F)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr b.property
  have hcxU (b : B) : cx b ∈ U := by
    apply hballU
    simp only [Metric.mem_ball, dist_zero_right, cx, norm_mul]
    exact lt_of_le_of_lt
      (mul_le_of_le_one_right (norm_nonneg c) (hBnorm b)) hcNorm
  have hcxSource (b : B) : cx b ∈ e.source :=
    (hUsub (hcxU b)).1
  have hcxBall (b : B) : cx b ∈ Metric.eball (0 : F)
      (NormedSpace.expSeries F F).radius :=
    (hUsub (hcxU b)).2.1
  have hcxPrincipal (b : B) :
      ‖NormedSpace.exp (cx b) - 1‖ < 1 :=
    (hUsub (hcxU b)).2.2
  let expIsUnit (b : B) : IsUnit (NormedSpace.exp (cx b)) :=
    NormedSpace.isUnit_exp_of_mem_ball (hcxBall b)
  let expUnit (b : B) : Units F := (expIsUnit b).unit
  have hexpUnit_val (b : B) : ((expUnit b : Units F) : F) =
      NormedSpace.exp (cx b) :=
    (expIsUnit b).unit_spec
  have hexpUnit_mem (b : B) : expUnit b ∈ P := by
    rw [A.mem_principalUnitGroup_iff]
    have hv : vF (NormedSpace.exp (cx b) - 1) < vF 1 := by
      dsimp only [vF]
      simpa only [map_one] using
        (Valued.toNormedField.norm_lt_one_iff.mp (hcxPrincipal b))
    have hw : w (NormedSpace.exp (cx b) - 1) < w 1 :=
      (ValuativeRel.isEquiv w vF).lt_iff_lt.mpr hv
    have hA :=
      (Valuation.isEquiv_valuation_valuationSubring w).lt_iff_lt.mp hw
    simpa only [hexpUnit_val, map_one] using hA
  let expP (b : B) : P := ⟨expUnit b, hexpUnit_mem b⟩
  have hexpP_val (b : B) : (((expP b : P) : Units F) : F) =
      NormedSpace.exp (cx b) :=
    hexpUnit_val b
  have hexpP_zero : expP 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hexpP_val]
    simp [cx, NormedSpace.exp_zero]
  have hexpP_add (b₁ b₂ : B) :
      expP (b₁ + b₂) = expP b₁ * expP b₂ := by
    apply Subtype.ext
    apply Units.ext
    rw [hexpP_val]
    change NormedSpace.exp (cx (b₁ + b₂)) =
      NormedSpace.exp (cx b₁) * NormedSpace.exp (cx b₂)
    have hcxAdd : cx (b₁ + b₂) = cx b₁ + cx b₂ := by
      simp [cx, mul_add]
    rw [hcxAdd, NormedSpace.exp_add_of_mem_ball
      (hcxBall b₁) (hcxBall b₂)]
  let coeffMap : ℤ_[p] → F := fun z =>
    ((padicIntegerPlaceMap v p hp z : B) : F)
  have hcoeffMap : Continuous coeffMap :=
    continuous_subtype_val.comp (continuous_padicIntegerPlaceMap v p hp)
  have hcx_smul (z : ℤ_[p]) (b : B) :
      cx (z • b) = coeffMap z * cx b := by
    change c * (((padicIntegerPlaceMap v p hp z : B) : F) * (b : F)) =
      ((padicIntegerPlaceMap v p hp z : B) : F) * (c * (b : F))
    ring
  have hcoeffMap_nat (n : ℕ) : coeffMap (n : ℤ_[p]) = (n : F) := by
    change ((padicIntegerPlaceMap v p hp (n : ℤ_[p]) : B) : F) = (n : F)
    rw [map_natCast]
    rfl
  have hcx_nat (n : ℕ) (b : B) :
      cx ((n : ℤ_[p]) • b) = n • cx b := by
    rw [hcx_smul, hcoeffMap_nat]
    exact (nsmul_eq_mul n (cx b)).symm
  have hexp_nsmul (n : ℕ) (b : B) :
      NormedSpace.exp (n • cx b) = NormedSpace.exp (cx b) ^ n := by
    induction n with
    | zero => simp [NormedSpace.exp_zero]
    | succ n ih =>
        rw [succ_nsmul, pow_succ]
        have hnBall : n • cx b ∈ Metric.eball (0 : F)
            (NormedSpace.expSeries F F).radius := by
          rw [← hcx_nat]
          exact hcxBall ((n : ℤ_[p]) • b)
        rw [NormedSpace.exp_add_of_mem_ball (𝕂 := F)
          hnBall (hcxBall b), ih]
  have hexpP_smul (z : ℤ_[p]) (b : B) :
      expP (z • b) = Additive.toMul (z • Additive.ofMul (expP b)) := by
    let f : ℤ_[p] → F := fun a => NormedSpace.exp (cx (a • b))
    let g : ℤ_[p] → F := fun a =>
      (((Additive.toMul (a • Additive.ofMul (expP b)) : P) : Units F) : F)
    have harg : Continuous fun a : ℤ_[p] => cx (a • b) := by
      apply Continuous.congr
        (hcoeffMap.mul continuous_const)
      intro a
      exact (hcx_smul a b).symm
    have hf : Continuous f := by
      change Continuous
        (NormedSpace.exp ∘ fun a : ℤ_[p] => cx (a • b))
      exact NormedSpace.continuousOn_exp.comp_continuous harg
        (fun a => hcxBall (a • b))
    have htoF : Continuous fun m : M =>
        (((Additive.toMul m : P) : Units F) : F) := by
      change Continuous fun u : P => (((u : P) : Units F) : F)
      exact Units.continuous_val.comp continuous_subtype_val
    have hsmul : Continuous fun a : ℤ_[p] =>
        a • Additive.ofMul (expP b) :=
      continuous_smul.comp (continuous_id.prodMk continuous_const)
    have hg : Continuous g := htoF.comp hsmul
    have hfg : f = g :=
      PadicInt.denseRange_natCast.equalizer hf hg (by
        funext n
        have hfn : f (n : ℤ_[p]) =
            NormedSpace.exp (cx b) ^ n := by
          dsimp only [f]
          rw [hcx_nat, hexp_nsmul]
        have hgn : g (n : ℤ_[p]) =
            NormedSpace.exp (cx b) ^ n := by
          dsimp only [g]
          rw [Nat.cast_smul_eq_nsmul]
          change (((expP b : P) : Units F) : F) ^ n = _
          rw [hexpP_val]
        exact hfn.trans hgn.symm)
    apply Subtype.ext
    apply Units.ext
    rw [hexpP_val]
    exact congrFun hfg z
  let L : B →ₗ[ℤ_[p]] M :=
    { toFun := fun b => Additive.ofMul (expP b)
      map_add' := fun b₁ b₂ => by
        apply Additive.toMul.injective
        exact hexpP_add b₁ b₂
      map_smul' := fun z b => by
        apply Additive.toMul.injective
        exact hexpP_smul z b }
  let valM : M → F := fun m =>
    (((Additive.toMul m : P) : Units F) : F)
  have hvalM_continuous : Continuous valM := by
    change Continuous fun u : P => (((u : P) : Units F) : F)
    exact Units.continuous_val.comp continuous_subtype_val
  have hvalM_injective : Function.Injective valM := by
    intro m₁ m₂ h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact h
  have hL_val (b : B) : valM (L b) = NormedSpace.exp (cx b) := by
    exact hexpP_val b
  have hLinj : Function.Injective L := by
    intro b₁ b₂ h
    have hval := congrArg valM h
    rw [hL_val, hL_val] at hval
    have hcxEq : cx b₁ = cx b₂ := by
      apply e.injOn (hcxSource b₁) (hcxSource b₂)
      have hefun : (e : F → F) = NormedSpace.exp :=
        hderiv'.toOpenPartialHomeomorph_coe
      rw [hefun]
      exact hval
    apply Subtype.ext
    change c * (b₁ : F) = c * (b₂ : F) at hcxEq
    exact mul_left_cancel₀ hc hcxEq
  let hcHomeo : F ≃ₜ F := Homeomorph.mulLeft₀ c hc
  let C : Set F := hcHomeo '' (B : Set F)
  have hBopen : IsOpen (B : Set F) := by
    change IsOpen ((Valued.v : Valuation F ℤᵐ⁰).integer : Set F)
    exact Valued.isOpen_integer F
  have hCopen : IsOpen C :=
    hcHomeo.isOpenMap _ hBopen
  have hCsource : C ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    simpa only [hcHomeo, Homeomorph.coe_mulLeft₀, cx] using
      hcxSource (⟨y, hy⟩ : B)
  let E : Set F := NormedSpace.exp '' C
  have hEopen : IsOpen E := by
    have hopen := e.isOpen_image_of_subset_source hCopen hCsource
    have hefun : (e : F → F) = NormedSpace.exp :=
      hderiv'.toOpenPartialHomeomorph_coe
    rw [hefun] at hopen
    change @IsOpen F completionTopology E
    rw [← htopology]
    exact hopen
  have hcxC (b : B) : cx b ∈ C := by
    refine ⟨(b : F), b.property, ?_⟩
    rfl
  have hrange : (L.range : Set M) = valM ⁻¹' E := by
    ext m
    constructor
    · rintro ⟨b, rfl⟩
      change valM (L b) ∈ E
      refine ⟨cx b, hcxC b, ?_⟩
      exact (hL_val b).symm
    · intro hm
      change valM m ∈ E at hm
      obtain ⟨x, hxC, hx⟩ := hm
      obtain ⟨y, hy, hxy⟩ := hxC
      let b : B := ⟨y, hy⟩
      have hcxb : cx b = x := by
        simpa only [b, cx, hcHomeo, Homeomorph.coe_mulLeft₀] using hxy
      refine ⟨b, ?_⟩
      apply hvalM_injective
      rw [hL_val, hcxb]
      exact hx
  refine ⟨L, hLinj, ?_⟩
  rw [hrange]
  exact hEopen.preimage hvalM_continuous

/-- The committed completion lattice bridge supplies finite generation and
computes the torsion-free rank. -/
private theorem deepUnitFiltration_latticeData_exists
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (rank : ℕ) (hrank : rank = finitePlaceLocalDegree v)
    (module : Module ℤ_[p]
      (Additive
        (completionValuativeRel v).valuation.valuationSubring.principalUnitGroup))
    (continuousSMul : let _ := module
      ContinuousSMul ℤ_[p]
        (Additive
          (completionValuativeRel v).valuation.valuationSubring.principalUnitGroup)) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    Nonempty (DeepPrincipalUnitLatticeData
      (v.adicCompletion K) p rank module) := by
  let F := v.adicCompletion K
  let B := v.adicCompletionIntegers K
  letI : ValuativeRel F := completionValuativeRel v
  let P := (ValuativeRel.valuation F).valuationSubring.principalUnitGroup
  let M := Additive P
  letI : Module ℤ_[p] M := module
  letI : ContinuousSMul ℤ_[p] M := continuousSMul
  letI : CompactSpace M := isCompact_iff_compactSpace.mp
    (completionPrincipalUnitGroup_isCompact v)
  letI : Algebra ℤ_[p] B := (padicIntegerPlaceMap v p hp).toAlgebra
  obtain ⟨hBfinite, hBrank⟩ :=
    padicIntegerCompletion_module_finite_finrank v p hp
  letI : Module.Finite ℤ_[p] B := hBfinite
  obtain ⟨L, hLinj, hLopen⟩ :=
    deepUnitFiltration_exponentialLattice_exists
      v p hp module continuousSMul
  let N : Submodule ℤ_[p] M := L.range
  letI : Module.Finite ℤ_[p] N := Module.Finite.range L
  letI : Finite (M ⧸ N) :=
    AddSubgroup.quotient_finite_of_isOpen N.toAddSubgroup hLopen
  letI : Module.Finite ℤ_[p] (M ⧸ N) := Module.Finite.of_finite
  letI : Module.Finite ℤ_[p] M :=
    Module.Finite.of_submodule_quotient N
  have hNrank : Module.finrank ℤ_[p] N = finitePlaceLocalDegree v := by
    rw [← hBrank]
    exact (LinearEquiv.ofInjective L hLinj).finrank_eq.symm
  have hQtor : Module.IsTorsion ℤ_[p] (M ⧸ N) := by
    intro x
    let q := Nat.card (M ⧸ N)
    have hqpos : 0 < q := Nat.card_pos
    let a₀ : ℤ_[p] := q
    have ha₀ : a₀ ≠ 0 := by
      dsimp [a₀]
      exact_mod_cast hqpos.ne'
    let a : ↥(nonZeroDivisors ℤ_[p]) :=
      ⟨a₀, mem_nonZeroDivisors_iff_ne_zero.mpr ha₀⟩
    refine ⟨a, ?_⟩
    change a₀ • x = 0
    rw [show a₀ = (q : ℤ_[p]) from rfl,
      Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero']
  have hQrank : Module.finrank ℤ_[p] (M ⧸ N) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr hQtor
  have hMrank : Module.finrank ℤ_[p] M = finitePlaceLocalDegree v := by
    rw [← N.finrank_quotient_add_finrank, hQrank, zero_add, hNrank]
  have htorRank : Module.finrank ℤ_[p]
      (M ⧸ Submodule.torsion ℤ_[p] M) = rank := by
    rw [finrank_quotient_eq_of_le_torsion (le_refl _), hMrank, ← hrank]
  exact ⟨{
    moduleFinite := inferInstance
    quotientFinrank := htorRank }⟩

/-- Torsion for the filtration action is exactly the group of `p`-power
roots of unity. -/
private theorem deepUnitFiltration_pPowerTorsion_spec
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (module : Module ℤ_[p]
      (Additive
        (completionValuativeRel v).valuation.valuationSubring.principalUnitGroup)) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    let _ := module
    ∀ u : Units (v.adicCompletion K),
      (∃ hu : u ∈
          (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring.principalUnitGroup,
        Additive.ofMul
          (⟨u, hu⟩ :
            (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring.principalUnitGroup) ∈
          Submodule.torsion ℤ_[p]
            (Additive
              (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring.principalUnitGroup)) ↔
        ∃ a : ℕ, u ^ ((p : ℕ) ^ a) = 1 := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  let w := ValuativeRel.valuation F
  let A := w.valuationSubring
  let P := A.principalUnitGroup
  let M := Additive P
  letI : Module ℤ_[p] M := module
  dsimp only
  intro u
  constructor
  · rintro ⟨hu, htor⟩
    rw [Submodule.mem_torsion_iff] at htor
    obtain ⟨c, hcsmul⟩ := htor
    have hc : (c : ℤ_[p]) ≠ 0 :=
      nonZeroDivisors.ne_zero c.property
    change (c : ℤ_[p]) • Additive.ofMul (⟨u, hu⟩ : P) = 0 at hcsmul
    obtain ⟨a, e, hceq⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc
        PadicInt.irreducible_p
    have hpsmul : ((p : ℤ_[p]) ^ a) •
        Additive.ofMul (⟨u, hu⟩ : P) = 0 := by
      rw [hceq, mul_smul] at hcsmul
      exact e.isUnit.smul_eq_zero.mp hcsmul
    refine ⟨a, ?_⟩
    have hnsmul : ((p : ℕ) ^ a) •
        Additive.ofMul (⟨u, hu⟩ : P) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ_[p]]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpsmul
    exact congrArg (fun x : P => ((Additive.toMul x : P) : Units F)) hnsmul
  · rintro ⟨a, hpow⟩
    let N : ℕ := (p : ℕ) ^ a
    have hN : N ≠ 0 := pow_ne_zero _ p.2.ne_zero
    have hpowN : u ^ N = 1 := by
      simpa only [N] using hpow
    have hpowF : (u : F) ^ N = 1 :=
      congrArg Units.val hpowN
    have hvpow : w (u : F) ^ N = 1 := by
      simpa only [map_pow, map_one] using congrArg w hpowF
    have hv : w (u : F) = 1 := by
      apply pow_left_injective hN
      simpa using hvpow
    have huA : u ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      exact (Valuation.isEquiv_valuation_valuationSubring w).eq_one_iff_eq_one.mp hv
    let uA : A.unitGroup := ⟨u, huA⟩
    let r := A.unitGroupToResidueFieldUnits
    let y := r uA
    have huApow : uA ^ N = 1 := by
      apply Subtype.ext
      exact hpowN
    have hypow : y ^ N = 1 := by
      have hymap := congrArg r huApow
      simpa only [map_pow, map_one, y] using hymap
    have horderN : orderOf y ∣ N :=
      orderOf_dvd_of_pow_eq_one hypow
    have horderQ : orderOf y ∣
        Nat.card (IsLocalRing.ResidueField A) - 1 := by
      have h := orderOf_dvd_natCard y
      rw [Nat.card_units (IsLocalRing.ResidueField w.valuationSubring)] at h
      exact h
    have hq : Nat.card (IsLocalRing.ResidueField A) =
        NU.Chebotarev.PrimeIdeal.norm v := by
      change residueCard (v.adicCompletion K) = _
      exact completionResidueCard_eq_norm v
    have hcop : N.Coprime
        (Nat.card (IsLocalRing.ResidueField A) - 1) := by
      simpa only [N, hq] using
        (residueCharacteristic_coprime_norm_sub_one v p hp).pow_left a
    have horderOne : orderOf y ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd horderN horderQ
    have hy : y = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp horderOne)
    have hu : u ∈ P := by
      change uA ∈ Subgroup.comap A.unitGroup.subtype P
      rw [← A.ker_unitGroupToResidueFieldUnits]
      exact hy
    refine ⟨hu, ?_⟩
    rw [Submodule.mem_torsion_iff]
    let c : ℤ_[p] := (p : ℤ_[p]) ^ a
    have hp0 : (p : ℤ_[p]) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    have hc : c ∈ nonZeroDivisors ℤ_[p] :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hp0)
    let s : ↥(nonZeroDivisors ℤ_[p]) := ⟨c, hc⟩
    refine ⟨s, ?_⟩
    change c • Additive.ofMul (⟨u, hu⟩ : P) = 0
    rw [show c = (((p : ℕ) ^ a : ℕ) : ℤ_[p]) by simp [c],
      Nat.cast_smul_eq_nsmul]
    have hpowP : (⟨u, hu⟩ : P) ^ ((p : ℕ) ^ a) = 1 := by
      apply Subtype.ext
      exact hpow
    exact congrArg Additive.ofMul hpowP

/-- The filtration-to-module interface from the cofinal filtration in
`DeepUnits` to its complete-PID module.  Concretely,
`deepUnitFiltration_exists` supplies the
open cofinal groups `V i`; the Hensel logarithm charts on sufficiently deep
levels transport scalar multiplication by `ℤ_p`, and cofinality identifies
the completion with the full principal-unit group.  The graded residue
coordinates give finite generation, the local degree gives the displayed
rank, and the characteristic equality identifies module torsion with
`p`-power roots of unity. -/
private theorem deepUnitFiltration_principalModuleData_exists
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (rank : ℕ)
    (hrank : rank = finitePlaceLocalDegree v) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    Nonempty
      (DeepPrincipalUnitModuleData (v.adicCompletion K) p rank) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  obtain ⟨action⟩ := deepUnitFiltration_actionData_exists v p hp
  letI : Module ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) :=
    action.module
  letI : ContinuousSMul ℤ_[p]
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) :=
    action.continuousSMul
  obtain ⟨compact⟩ := deepUnitFiltration_compactSpace_exists v
  letI : CompactSpace
      (Additive (ValuativeRel.valuation F).valuationSubring.principalUnitGroup) :=
    compact
  obtain ⟨lattice⟩ :=
    deepUnitFiltration_latticeData_exists v p hp rank hrank action.module
      action.continuousSMul
  have torsionSpec :=
    deepUnitFiltration_pPowerTorsion_spec v p hp action.module
  exact ⟨{
    module := action.module
    compactSpace := compact
    continuousSMul := action.continuousSMul
    moduleFinite := lattice.moduleFinite
    quotientFinrank := lattice.quotientFinrank
    pPowerTorsion_spec := torsionSpec }⟩

/-- Assemble valuation, Teichmüller, torsion, and free principal-unit factors
from the three independent local classifications. -/
private theorem localUnitDecomposition_completePIDClassification
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (rank : ℕ)
    (hrank : rank = finitePlaceLocalDegree v) :
    Nonempty (LocalUnitDecompositionData v p rank) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  obtain ⟨valuation⟩ := localUnitValuationData_exists F
  obtain ⟨teichmuller⟩ := localUnitTeichmullerData_exists F
  obtain ⟨deepModule⟩ :=
    deepUnitFiltration_principalModuleData_exists v p hp rank hrank
  obtain ⟨principal⟩ :=
    principalUnitDecompositionData_exists F p rank deepModule
  have hq : residueCard F = NU.Chebotarev.PrimeIdeal.norm v :=
    completionResidueCard_eq_norm v
  let teichmullerEquiv : teichmuller.teichmullerFactor ≃ₜ*
      Multiplicative
        (ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)) := by
    rw [← hq]
    exact teichmuller.teichmullerEquiv
  let unitRest :
      (ValuativeRel.valuation F).valuationSubring.unitGroup ≃ₜ*
        teichmuller.teichmullerFactor ×
          principal.pPowerTorsion × principal.freePrincipalUnits :=
    teichmuller.unitEquiv.trans
      (continuousMulEquivProdCongr
        (ContinuousMulEquiv.refl teichmuller.teichmullerFactor)
        principal.principalEquiv)
  let productEquiv : Units F ≃ₜ*
      valuation.valuationFactor × teichmuller.teichmullerFactor ×
        principal.pPowerTorsion × principal.freePrincipalUnits :=
    valuation.unitEquiv.trans
      (continuousMulEquivProdCongr
        (ContinuousMulEquiv.refl valuation.valuationFactor) unitRest)
  exact ⟨{
    valuationFactor := valuation.valuationFactor
    teichmullerFactor := teichmuller.teichmullerFactor
    pPowerTorsion := principal.pPowerTorsion
    freePrincipalUnits := principal.freePrincipalUnits
    productEquiv := productEquiv
    valuationEquiv := valuation.valuationEquiv
    teichmullerEquiv := teichmullerEquiv
    pPowerTorsion_spec := principal.pPowerTorsion_spec
    freePrincipalUnitsEquiv := principal.freePrincipalUnitsEquiv }⟩

/-- **Deep-unit complete-PID bridge (Blueprint `lem:units`; nu-inv12 blocker
report: "the complete-PID classification step for principal units").**
For the residue prime `p`, the cofinal deep principal units of the local
completion form a profinite `ℤ_p`-module with finite torsion and finite-rank
free quotient.  Splitting that module and adjoining the valuation and
prime-to-`p` Teichmüller factors gives `LocalUnitDecompositionData`.

This is the public standalone form of the blocked core formerly called
`localUnitDecomposition_completePIDClassification`.  The equality `hp` pins
`p` to the residue characteristic and prevents the module structure from
being chosen at an unrelated prime.  See `local_invariants_recovery.tex`,
`lem:units`, and the nu-inv12 blocker report. -/
theorem deepUnitModule_localUnitDecomposition
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (rank : ℕ)
    (hrank : rank = finitePlaceLocalDegree v) :
    Nonempty (LocalUnitDecompositionData v p rank) := by
  exact localUnitDecomposition_completePIDClassification v p hp rank hrank

end

end NU.NeukirchUchida.Bridges
