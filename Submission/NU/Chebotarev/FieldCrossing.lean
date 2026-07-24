import Submission.NU.Chebotarev.Cyclotomic
import Submission.NU.Chebotarev.Deuring

/-!
# M7. Chebotarev field crossing and Dirichlet-density Chebotarev

Blueprint §7--§9. Auxiliary cyclotomic extensions are selected using only
Dirichlet's theorem and ramification, never Chebotarev (design caution
§10.5(6)). This module reaches the full Dirichlet-density milestone.
-/

open Filter Topology
open scoped BigOperators TensorProduct

namespace NU.Chebotarev

universe u v w

/-- Absolute cyclotomic fields of prime conductor are disjoint from a number
field whose discriminant is prime to the conductor.  The common ambient
number field is constructed inside an algebraic closure solely to invoke the
discriminant criterion for linear disjointness. -/
private theorem fieldCrossing_absolute_cyclotomic_tensor_isDomain
    {L : Type*} [Field L] [NumberField L]
    (p : ℕ) (hp : Nat.Prime p)
    (hpd : ¬ p ∣ (NumberField.discr L).natAbs) :
    IsDomain (L ⊗[ℚ] CyclotomicField p ℚ) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.ne_zero⟩
  let C := CyclotomicField p ℚ
  let Ω := AlgebraicClosure ℚ
  let f : L →ₐ[ℚ] Ω := IsAlgClosed.lift
  let g : C →ₐ[ℚ] Ω := IsAlgClosed.lift
  let A : IntermediateField ℚ Ω := f.fieldRange
  let B : IntermediateField ℚ Ω := g.fieldRange
  let eA : L ≃ₐ[ℚ] A := AlgHom.equivFieldRange f
  let eB : C ≃ₐ[ℚ] B := AlgHom.equivFieldRange g
  letI : FiniteDimensional ℚ A := eA.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional ℚ B := eB.toLinearEquiv.finiteDimensional
  let U : IntermediateField ℚ Ω := A ⊔ B
  letI : FiniteDimensional ℚ U := IntermediateField.finiteDimensional_sup A B
  letI : NumberField U := NumberField.mk
  let iA : A →ₐ[ℚ] U := IntermediateField.inclusion le_sup_left
  let iB : B →ₐ[ℚ] U := IntermediateField.inclusion le_sup_right
  let fU : L →ₐ[ℚ] U := iA.comp eA.toAlgHom
  let gU : C →ₐ[ℚ] U := iB.comp eB.toAlgHom
  let A' : IntermediateField ℚ U := fU.fieldRange
  let B' : IntermediateField ℚ U := gU.fieldRange
  let eA' : L ≃ₐ[ℚ] A' := AlgHom.equivFieldRange fU
  let eB' : C ≃ₐ[ℚ] B' := AlgHom.equivFieldRange gU
  letI : IsCyclotomicExtension {p} ℚ C := by
    dsimp [C]
    exact CyclotomicField.isCyclotomicExtension p ℚ
  letI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {p} ℚ C
  letI : IsGalois ℚ B' := IsGalois.of_algEquiv eB'
  have hdiscA : NumberField.discr A' = NumberField.discr L :=
    (NumberField.discr_eq_discr_of_algEquiv L eA').symm
  have hdiscB : NumberField.discr B' =
      (-1) ^ ((p - 1) / 2) * (p : ℤ) ^ (p - 2) := by
    rw [← NumberField.discr_eq_discr_of_algEquiv C eB']
    exact IsCyclotomicExtension.Rat.discr_prime p C
  have hpcoprime : p.Coprime (NumberField.discr L).natAbs :=
    (hp.coprime_iff_not_dvd).2 hpd
  have hcop : IsCoprime (NumberField.discr B') (NumberField.discr A') := by
    rw [Int.isCoprime_iff_nat_coprime, hdiscA, hdiscB,
      Int.natAbs_mul, Int.natAbs_pow]
    simp only [Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
    exact hpcoprime.pow_left (p - 2)
  have H : B'.LinearDisjoint A' :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr U B' A' hcop
  exact H.symm.isDomain'

/-- Base change of an absolutely disjoint prime cyclotomic field.  The tensor
product `K ⊗[ℚ] ℚ(ζ_p)` is first identified as the `p`-cyclotomic extension
of `K`; cancellation of base change then gives the required relative tensor
product domain. -/
private theorem fieldCrossing_relative_cyclotomic_data
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) (hp : Nat.Prime p)
    (hKC : IsDomain (K ⊗[ℚ] CyclotomicField p ℚ))
    (hLC : IsDomain (L ⊗[ℚ] CyclotomicField p ℚ)) :
    IsDomain (L ⊗[K] CyclotomicField p K) ∧
      Module.finrank K (CyclotomicField p K) = p - 1 ∧
      IsCyclic (Gal(CyclotomicField p K/K)) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.ne_zero⟩
  letI : NeZero (p : K) := ⟨by exact_mod_cast hp.ne_zero⟩
  let C := CyclotomicField p ℚ
  let P := K ⊗[ℚ] C
  letI : IsDomain P := hKC
  have hfield : IsField P :=
    Algebra.TensorProduct.isField_of_isAlgebraic ℚ K C
      (Or.inl (Algebra.IsAlgebraic.of_finite ℚ K))
  letI : Field P := hfield.toField
  have hC : IsCyclotomicExtension {p} ℚ C :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let ζ : C := IsCyclotomicExtension.zeta p ℚ C
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ C
  let ι : C →ₐ[ℚ] P := Algebra.TensorProduct.includeRight
  let ζP : P := ι ζ
  have hι : Function.Injective ι := by
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ K).injective
  have hζP : IsPrimitiveRoot ζP p := hζ.map_of_injective hι
  have hgenC : Algebra.adjoin ℚ ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hright (y : C) : ι y ∈ Algebra.adjoin K ({ζP} : Set P) := by
    have hy : y ∈ Algebra.adjoin ℚ ({ζ} : Set C) := by rw [hgenC]; trivial
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff.mp hy]
        exact Algebra.subset_adjoin (R := K) (Set.mem_singleton ζP)
    | algebraMap q =>
        rw [ι.commutes]
        change algebraMap K P (algebraMap ℚ K q) ∈ Algebra.adjoin K ({ζP} : Set P)
        exact Subalgebra.algebraMap_mem _ _
    | add x y hx hy ihx ihy =>
        rw [map_add]
        exact (Algebra.adjoin K ({ζP} : Set P)).add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact (Algebra.adjoin K ({ζP} : Set P)).mul_mem ihx ihy
  have hgenP : Algebra.adjoin K ({ζP} : Set P) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using TensorProduct.induction_on with
    | zero => exact (Algebra.adjoin K ({ζP} : Set P)).zero_mem
    | tmul x y =>
        rw [show x ⊗ₜ[ℚ] y = algebraMap K P x * ι y by
          rw [Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self_apply,
            mul_one, one_mul]]
        exact (Algebra.adjoin K ({ζP} : Set P)).mul_mem
          (Subalgebra.algebraMap_mem _ x) (hright y)
    | add x y ihx ihy =>
        exact (Algebra.adjoin K ({ζP} : Set P)).add_mem ihx ihy
  letI : IsCyclotomicExtension {p} K P := by
    rw [IsCyclotomicExtension.iff_adjoin_eq_top]
    constructor
    · intro n hn hn0
      simp only [Set.mem_singleton_iff] at hn
      subst n
      exact ⟨ζP, hζP⟩
    · apply top_unique
      rw [← hgenP]
      apply Algebra.adjoin_mono
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨p, Set.mem_singleton p, hp.ne_zero, hζP.pow_eq_one⟩
  let M := CyclotomicField p K
  letI : IsCyclotomicExtension {p} K M :=
    CyclotomicField.isCyclotomicExtension p K
  let eM : M ≃ₐ[K] P := IsCyclotomicExtension.algEquiv {p} K M P
  have hdomain : IsDomain (L ⊗[K] M) := by
    let e : L ⊗[K] M ≃ₐ[K] L ⊗[ℚ] C :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L) eM).trans
        (Algebra.TensorProduct.cancelBaseChange ℚ K K L C)
    letI : IsDomain (L ⊗[ℚ] C) := hLC
    exact e.toMulEquiv.isDomain _
  have hdegree : Module.finrank K M = p - 1 := by
    rw [eM.toLinearEquiv.finrank_eq]
    change Module.finrank K (K ⊗[ℚ] C) = p - 1
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
      IsCyclotomicExtension.Rat.finrank p C, Nat.totient_prime hp]
  have hcyclic : IsCyclic Gal(M/K) := by
    letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
    let hζM := IsCyclotomicExtension.zeta_spec p K M
    exact isCyclic_of_injective (hζM.autToPow K) (hζM.autToPow_injective K)
  exact ⟨hdomain, hdegree, hcyclic⟩

/-- Unramifiedness descends through a tower of number fields. -/
private theorem fieldCrossing_unramified_descends
    {K A B : Type*} [Field K] [NumberField K]
    [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (p : PrimeIdeal K) (h : IsUnramifiedPrime (K := K) (L := B) p) :
    IsUnramifiedPrime (K := K) (L := A) p := by
  intro Q hQp
  obtain ⟨Pideal, hPmax, hPQ⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers B) Q.asIdeal
  let P : PrimeIdeal B :=
    ⟨Pideal, hPmax.isPrime, by
      intro hbot
      apply Q.ne_bot
      have hover := hPQ.over
      rw [hbot] at hover
      simpa using hover⟩
  have hPq : P.asIdeal.LiesOver Q.asIdeal := hPQ
  have hPp : P.asIdeal.LiesOver p.asIdeal := by
    letI : P.asIdeal.LiesOver Q.asIdeal := hPq
    letI : Q.asIdeal.LiesOver p.asIdeal := hQp
    exact Ideal.LiesOver.trans P.asIdeal Q.asIdeal p.asIdeal
  letI : P.asIdeal.LiesOver Q.asIdeal := hPq
  letI : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) P.asIdeal := h P hPp
  exact Algebra.IsUnramifiedAt.of_liesOver
    (NumberField.RingOfIntegers K) Q.asIdeal P.asIdeal

/-- The compositum/fixed-field part of field crossing.  The tensor-product
compositum has Galois group the product, and the order divisibility hypothesis
makes the projection of `⟨(σ, τ)⟩` to the cyclotomic factor injective. -/
private theorem fieldCrossing_pair_algebraic
    {K L M : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsMulCommutative Gal(L/K)]
    (ell : ℕ) [IsCyclotomicExtension {ell} K M]
    (_m : RayModulus K) (hell : 1 ≤ ell)
    (_hmod : IsCyclotomicModulus ell _m)
    (_hram : RamificationSupported (M := M) _m)
    (hdisj : IsDomain (L ⊗[K] M))
    (sigma : Gal(L/K)) (tau : Gal(M/K))
    (horder : orderOf sigma ∣ orderOf tau) :
    HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := L) sigma ∩
        frobeniusElementPrimeSet (K := K) (L := M) tau)
      (1 / ((Nat.card Gal(L/K) : ℝ) * Nat.card Gal(M/K))) := by
  let N := L ⊗[K] M
  letI : IsDomain N := hdisj
  have hfield : IsField N :=
    Algebra.TensorProduct.isField_of_isAlgebraic K L M
      (Or.inl (Algebra.IsAlgebraic.of_finite K L))
  letI : Field N := hfield.toField
  letI : NumberField N := NumberField.of_module_finite K N
  letI : FiniteDimensional K N := by infer_instance
  let pairHom : Gal(L/K) × Gal(M/K) →* Gal(N/K) := by
    refine
      { toFun := fun s => Algebra.TensorProduct.congr s.1 s.2
        map_one' := Algebra.TensorProduct.congr_refl
        map_mul' := ?_ }
    intro a b
    apply AlgEquiv.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [Prod.fst_mul, Prod.snd_mul, Algebra.TensorProduct.congr_apply,
          Algebra.TensorProduct.map_tmul]
        change (a.1 * b.1) x ⊗ₜ[K] (a.2 * b.2) y =
          a.1 (b.1 x) ⊗ₜ[K] a.2 (b.2 y)
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  have hpairHom : Function.Injective pairHom := by
    intro a b hab
    apply Prod.ext
    · apply AlgEquiv.ext
      intro x
      have hx := congrArg (fun e : Gal(N/K) =>
        e ((Algebra.TensorProduct.includeLeft : L →ₐ[K] N) x)) hab
      apply Algebra.TensorProduct.includeLeft_injective (S := K) (A := L) (B := M)
        (algebraMap K M).injective
      dsimp [pairHom] at hx
      rw [Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        map_one, map_one] at hx
      change (a.1 x ⊗ₜ[K] (1 : M) : N) = b.1 x ⊗ₜ[K] (1 : M)
      exact hx
    · apply AlgEquiv.ext
      intro y
      have hy := congrArg (fun e : Gal(N/K) =>
        e ((Algebra.TensorProduct.includeRight : M →ₐ[K] N) y)) hab
      apply Algebra.TensorProduct.includeRight_injective (A := L) (B := M)
        (algebraMap K L).injective
      dsimp [pairHom] at hy
      rw [Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        map_one, map_one] at hy
      change ((1 : L) ⊗ₜ[K] a.2 y : N) = (1 : L) ⊗ₜ[K] b.2 y
      exact hy
  have hlow : Nat.card Gal(L/K) * Nat.card Gal(M/K) ≤ Nat.card Gal(N/K) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective pairHom hpairHom
  have hupp : Nat.card Gal(N/K) ≤ Module.finrank K N := by
    calc
      Nat.card Gal(N/K) ≤ Nat.card (N →ₐ[K] N) :=
        Nat.card_le_card_of_injective (fun e : Gal(N/K) => e.toAlgHom)
          AlgEquiv.coe_toAlgHom_injective
      _ ≤ Module.finrank K N := card_algHom_le_finrank K N N
  have hfin : Module.finrank K N =
      Module.finrank K L * Module.finrank K M := Module.finrank_tensorProduct
  have hcardprod : Nat.card Gal(L/K) * Nat.card Gal(M/K) =
      Module.finrank K N := by
    rw [hfin, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
  have hcard : Nat.card Gal(N/K) = Module.finrank K N := by omega
  letI : IsGalois K N := IsGalois.of_card_aut_eq_finrank K N hcard
  have hcardN : Nat.card Gal(N/K) =
      Nat.card Gal(L/K) * Nat.card Gal(M/K) := hcard.trans hcardprod.symm
  letI : Fintype (Gal(L/K) × Gal(M/K)) := Fintype.ofFinite _
  letI : Fintype Gal(N/K) := Fintype.ofFinite _
  have hpairBij : Function.Bijective pairHom :=
    (Fintype.bijective_iff_injective_and_card pairHom).2 ⟨hpairHom, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        Nat.card_prod, hcardN]⟩
  let pairEquiv : Gal(L/K) × Gal(M/K) ≃* Gal(N/K) :=
    MulEquiv.ofBijective pairHom hpairBij
  let iL : L →ₐ[K] N := Algebra.TensorProduct.includeLeft
  let iM : M →ₐ[K] N := Algebra.TensorProduct.includeRight
  have hpairLeft (a : Gal(L/K)) (b : Gal(M/K)) (x : L) :
      pairEquiv (a, b) (iL x) = iL (a x) := by
    change (Algebra.TensorProduct.congr a b)
      (x ⊗ₜ[K] (1 : M)) = a x ⊗ₜ[K] (1 : M)
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    change (a x ⊗ₜ[K] (1 : M) : N) = a x ⊗ₜ[K] (1 : M)
    rfl
  have hpairRight (a : Gal(L/K)) (b : Gal(M/K)) (y : M) :
      pairEquiv (a, b) (iM y) = iM (b y) := by
    change (Algebra.TensorProduct.congr a b)
      ((1 : L) ⊗ₜ[K] y) = (1 : L) ⊗ₜ[K] b y
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    change ((1 : L) ⊗ₜ[K] b y : N) = (1 : L) ⊗ₜ[K] b y
    rfl
  let rho : Gal(N/K) := pairEquiv (sigma, tau)
  let C : Subgroup Gal(N/K) := Subgroup.zpowers rho
  let E : IntermediateField K N := IntermediateField.fixedField C
  let B : IntermediateField K N := iM.fieldRange
  have hfix : (E ⊔ B).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField]
    apply le_antisymm
    · intro s hs
      rcases hs with ⟨hsC, hsB⟩
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hsC
      have hsz (y : M) : s (iM y) = iM y :=
        (IntermediateField.mem_fixingSubgroup_iff B s).mp hsB (iM y) ⟨y, rfl⟩
      have htauz : tau ^ z = 1 := by
        apply AlgEquiv.ext
        intro y
        apply iM.injective
        change iM ((tau ^ z) y) = iM y
        calc
          iM ((tau ^ z) y) = (pairEquiv ((sigma, tau) ^ z)) (iM y) := by
            change iM ((tau ^ z) y) = pairEquiv (sigma ^ z, tau ^ z) (iM y)
            exact (hpairRight (sigma ^ z) (tau ^ z) y).symm
          _ = (rho ^ z) (iM y) := by rw [map_zpow]
          _ = s (iM y) := by rw [hz]
          _ = iM y := hsz y
      have hsigmaDiv : (orderOf sigma : ℤ) ∣ (orderOf tau : ℤ) :=
        Int.natCast_dvd_natCast.mpr horder
      have htauDiv : (orderOf tau : ℤ) ∣ z :=
        orderOf_dvd_iff_zpow_eq_one.mpr htauz
      have hsigmaz : sigma ^ z = 1 :=
        orderOf_dvd_iff_zpow_eq_one.mp (hsigmaDiv.trans htauDiv)
      have hsone : s = 1 := by
        rw [← hz, ← map_zpow]
        change pairEquiv (sigma ^ z, tau ^ z) = 1
        rw [hsigmaz, htauz]
        exact map_one pairEquiv
      exact Subgroup.mem_bot.mpr hsone
    · exact bot_le
  have hsup : E ⊔ B = ⊤ := by
    apply (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := N)).injective
    rw [IsGalois.intermediateFieldEquivSubgroup_apply,
      IsGalois.intermediateFieldEquivSubgroup_apply, hfix,
      IntermediateField.fixingSubgroup_top]
  have hnell : ell ≠ 0 := by omega
  letI : NeZero ell := ⟨hnell⟩
  let zeta : M := IsCyclotomicExtension.zeta ell K M
  have hzeta : IsPrimitiveRoot zeta ell := IsCyclotomicExtension.zeta_spec ell K M
  let zetaN : N := iM zeta
  have hzetaN : IsPrimitiveRoot zetaN ell := hzeta.map_of_injective iM.injective
  have hgenM : Algebra.adjoin K ({zeta} : Set M) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hzeta
  have hgenM' : IntermediateField.adjoin K ({zeta} : Set M) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K _ hgenM
  have hB : B = IntermediateField.adjoin K ({zetaN} : Set N) := by
    calc
      B = IntermediateField.map iM ⊤ := AlgHom.fieldRange_eq_map iM
      _ = IntermediateField.map iM (IntermediateField.adjoin K ({zeta} : Set M)) := by
        rw [hgenM']
      _ = IntermediateField.adjoin K (iM '' ({zeta} : Set M)) :=
        IntermediateField.adjoin_map K _ iM
      _ = IntermediateField.adjoin K ({zetaN} : Set N) := by
        congr 1
        ext x
        simp [zetaN]
  have htopE : IntermediateField.adjoin E ({zetaN} : Set N) = ⊤ := by
    apply (IntermediateField.restrictScalars_eq_top_iff
      (K := K) (F := E) (E := N)).mp
    rw [IntermediateField.restrictScalars_adjoin,
      IntermediateField.adjoin_union, IntermediateField.adjoin_self,
      ← hB, hsup]
  have hAlgTop : Algebra.adjoin E ({zetaN} : Set N) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
    · rw [htopE]
      rfl
    · intro x hx
      exact Algebra.IsAlgebraic.isAlgebraic x
  letI : IsCyclotomicExtension {ell} E N := by
    rw [IsCyclotomicExtension.iff_adjoin_eq_top]
    constructor
    · intro n hn hn0
      simp only [Set.mem_singleton_iff] at hn
      subst n
      exact ⟨zetaN, hzetaN⟩
    · apply top_unique
      rw [← hAlgTop]
      apply Algebra.adjoin_mono
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨ell, Set.mem_singleton ell, hnell, hzetaN.pow_eq_one⟩
  let eC : C ≃* Gal(N/E) := IntermediateField.subgroupEquivAlgEquiv C
  let rhoE : Gal(N/E) := eC ⟨rho, Subgroup.mem_zpowers rho⟩
  have hrhoE : AlgEquiv.restrictScalarsHom K rhoE = rho := by
    ext x
    rfl
  have hsetUp : deuringUpstairsPrimeSet (K := K) (L := N) rho =
      frobeniusElementPrimeSet (K := E) (L := N) rhoE := by
    ext q
    constructor
    · rintro ⟨hunr, P, hPq, hP⟩
      refine ⟨hunr, P, hPq, ?_⟩
      apply AlgEquiv.restrictScalarsHom_injective K
      rw [hP, hrhoE]
    · rintro ⟨hunr, P, hPq, hP⟩
      refine ⟨hunr, P, hPq, ?_⟩
      rw [hP, hrhoE]
  have hcardE : Nat.card Gal(N/E) = orderOf rho := by
    rw [← Nat.card_congr eC.toEquiv, Nat.card_zpowers]
  have hup : HasDirichletDensity
      (deuringUpstairsPrimeSet (K := K) (L := N) rho)
      (1 / (orderOf rho : ℝ)) := by
    rw [hsetUp]
    obtain ⟨mE, hmodE, hramE⟩ :=
      exists_cyclotomicModulus (K := E) (M := N) ell hell
    have h := cyclotomic_chebotarev_dirichletDensity_of_modulus
      (K := E) (M := N) (F := N) ell mE hell hmodE hramE rhoE
    rw [hcardE] at h
    exact h
  letI : IsMulCommutative Gal(M/K) :=
    IsCyclotomicExtension.isMulCommutative {ell} K M
  have hcomm (a b : Gal(N/K)) : a * b = b * a := by
    obtain ⟨a, rfl⟩ := pairEquiv.surjective a
    obtain ⟨b, rfl⟩ := pairEquiv.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    apply Prod.ext
    · exact IsMulCommutative.is_comm.comm _ _
    · exact IsMulCommutative.is_comm.comm _ _
  letI : IsMulCommutative Gal(N/K) := ⟨⟨hcomm⟩⟩
  have hcentral : Subgroup.centralizer ({rho} : Set Gal(N/K)) = ⊤ := by
    ext s
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_top, iff_true]
    exact hcomm s rho
  have hfactor : (deuringFactor rho : ℝ) *
      (1 / (Nat.card Gal(N/K) : ℝ)) = 1 / (orderOf rho : ℝ) := by
    have htopcard : Nat.card (⊤ : Subgroup Gal(N/K)) = Nat.card Gal(N/K) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ : Gal(N/K) => Subgroup.mem_top _))
    unfold deuringFactor
    rw [Nat.cast_div_charZero (deuringFactor_isInteger rho), hcentral, htopcard]
    have hG : (Nat.card Gal(N/K) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have ho : (orderOf rho : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (orderOf_pos rho).ne'
    field_simp
  have hbase : HasDirichletDensity
      (frobeniusPrimeSet (K := K) (L := N) (ConjClasses.mk rho))
      (1 / (Nat.card Gal(N/K) : ℝ)) := by
    apply (deuring_dirichletDensity (K := K) (L := N) rho _).mp
    rw [hfactor]
    exact hup
  have hclassElem :
      frobeniusPrimeSet (K := K) (L := N) (ConjClasses.mk rho) =
        frobeniusElementPrimeSet (K := K) (L := N) rho := by
    ext p
    constructor
    · rintro ⟨hunr, P, hPp, hP⟩
      refine ⟨hunr, P, hPp, ?_⟩
      change ConjClasses.mk (arithFrobeniusAt (K := K) (L := N) P) =
        ConjClasses.mk rho at hP
      have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hP
      apply hc.eq_of_right_mem_center
      apply Set.mem_center_iff.mpr
      refine ⟨fun x => IsMulCommutative.is_comm.comm rho x, ?_, ?_⟩
      · exact fun _ _ => (mul_assoc _ _ _).symm
      · exact fun _ _ => mul_assoc _ _ _
    · rintro ⟨hunr, P, hPp, hP⟩
      refine ⟨hunr, P, hPp, ?_⟩
      unfold frobeniusClassAt
      rw [hP]
  have hNelem : HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := N) rho)
      (1 / (Nat.card Gal(N/K) : ℝ)) := by
    rw [← hclassElem]
    exact hbase
  letI : Algebra M N := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower K M N := Algebra.TensorProduct.right_isScalarTower
  have hrestrictL (a : Gal(L/K)) (b : Gal(M/K)) :
      AlgEquiv.restrictNormalHom L (pairEquiv (a, b)) = a := by
    apply AlgEquiv.ext
    intro x
    apply iL.injective
    calc
      iL ((AlgEquiv.restrictNormalHom L (pairEquiv (a, b))) x) =
          pairEquiv (a, b) (iL x) :=
        AlgEquiv.restrictNormal_commutes (pairEquiv (a, b)) L x
      _ = iL (a x) := hpairLeft a b x
  have hrestrictM (a : Gal(L/K)) (b : Gal(M/K)) :
      AlgEquiv.restrictNormalHom M (pairEquiv (a, b)) = b := by
    apply AlgEquiv.ext
    intro y
    apply iM.injective
    calc
      iM ((AlgEquiv.restrictNormalHom M (pairEquiv (a, b))) y) =
          pairEquiv (a, b) (iM y) :=
        AlgEquiv.restrictNormal_commutes (pairEquiv (a, b)) M y
      _ = iM (b y) := hpairRight a b y
  have hrhoL : AlgEquiv.restrictNormalHom L rho = sigma := hrestrictL sigma tau
  have hrhoM : AlgEquiv.restrictNormalHom M rho = tau := hrestrictM sigma tau
  let underL : PrimeIdeal N → PrimeIdeal L := fun P =>
    ⟨P.asIdeal.under (NumberField.RingOfIntegers L), inferInstance, by
      intro h
      letI : P.asIdeal.LiesOver
          (⊥ : Ideal (NumberField.RingOfIntegers L)) := ⟨by simp [h]⟩
      exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot
        (NumberField.RingOfIntegers L) P.asIdeal)⟩
  let underM : PrimeIdeal N → PrimeIdeal M := fun P =>
    ⟨P.asIdeal.under (NumberField.RingOfIntegers M), inferInstance, by
      intro h
      letI : P.asIdeal.LiesOver
          (⊥ : Ideal (NumberField.RingOfIntegers M)) := ⟨by simp [h]⟩
      exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot
        (NumberField.RingOfIntegers M) P.asIdeal)⟩
  have underL_lies (p : PrimeIdeal K) (P : PrimeIdeal N)
      (hPp : P.asIdeal.LiesOver p.asIdeal) :
      (underL P).asIdeal.LiesOver p.asIdeal := by
    constructor
    change p.asIdeal = (P.asIdeal.under (NumberField.RingOfIntegers L)).under
      (NumberField.RingOfIntegers K)
    rw [Ideal.under_under]
    exact hPp.over
  have underM_lies (p : PrimeIdeal K) (P : PrimeIdeal N)
      (hPp : P.asIdeal.LiesOver p.asIdeal) :
      (underM P).asIdeal.LiesOver p.asIdeal := by
    constructor
    change p.asIdeal = (P.asIdeal.under (NumberField.RingOfIntegers M)).under
      (NumberField.RingOfIntegers K)
    rw [Ideal.under_under]
    exact hPp.over
  let SN := frobeniusElementPrimeSet (K := K) (L := N) rho
  let T := frobeniusElementPrimeSet (K := K) (L := L) sigma ∩
    frobeniusElementPrimeSet (K := K) (L := M) tau
  have hNsub : SN ⊆ T := by
    intro p hp
    rcases hp with ⟨hunrN, P, hPp, hPrho⟩
    have hunrL : IsUnramifiedPrime (K := K) (L := L) p :=
      fieldCrossing_unramified_descends p hunrN
    have hunrM : IsUnramifiedPrime (K := K) (L := M) p :=
      fieldCrossing_unramified_descends p hunrN
    have hPL : P.asIdeal.LiesOver (underL P).asIdeal := ⟨rfl⟩
    have hPM : P.asIdeal.LiesOver (underM P).asIdeal := ⟨rfl⟩
    have hfL := arithFrobAt_restrict (K := K) (L := N) (M := L)
      P (underL P) hPL (hunrN P hPp)
    have hfM := arithFrobAt_restrict (K := K) (L := N) (M := M)
      P (underM P) hPM (hunrN P hPp)
    rw [hPrho, hrhoL] at hfL
    rw [hPrho, hrhoM] at hfM
    exact ⟨⟨hunrL, underL P, underL_lies p P hPp, hfL.symm⟩,
      ⟨hunrM, underM P, underM_lies p P hPp, hfM.symm⟩⟩
  have hAway (p : PrimeIdeal K) (hp : p ∈ T)
      (hunrN : IsUnramifiedPrime (K := K) (L := N) p) : p ∈ SN := by
    rcases hp with ⟨⟨hunrL, QL, hQLp, hQLsigma⟩,
      ⟨hunrM, QM, hQMp, hQMtau⟩⟩
    obtain ⟨Pideal, hPmax, hPp'⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := NumberField.RingOfIntegers N) p.asIdeal
    let P : PrimeIdeal N :=
      ⟨Pideal, hPmax.isPrime, by
        intro hbot
        apply p.ne_bot
        have hover := hPp'.over
        rw [hbot] at hover
        simpa using hover⟩
    have hPp : P.asIdeal.LiesOver p.asIdeal := hPp'
    have hPL : P.asIdeal.LiesOver (underL P).asIdeal := ⟨rfl⟩
    have hPM : P.asIdeal.LiesOver (underM P).asIdeal := ⟨rfl⟩
    have hfrobL : arithFrobeniusAt (K := K) (L := L) (underL P) = sigma := by
      have hc : IsConj (arithFrobeniusAt (K := K) (L := L) (underL P))
          (arithFrobeniusAt (K := K) (L := L) QL) := by
        unfold arithFrobeniusAt
        apply isConj_arithFrobAt (NumberField.RingOfIntegers K) Gal(L/K)
          (underL P).asIdeal QL.asIdeal
        exact (underL_lies p P hPp).over.symm.trans hQLp.over
      rw [hQLsigma] at hc
      apply hc.eq_of_right_mem_center
      apply Set.mem_center_iff.mpr
      refine ⟨fun x => IsMulCommutative.is_comm.comm sigma x, ?_, ?_⟩
      · exact fun _ _ => mul_assoc _ _ _
      · exact fun _ _ => mul_assoc _ _ _
    have hfrobM : arithFrobeniusAt (K := K) (L := M) (underM P) = tau := by
      have hc : IsConj (arithFrobeniusAt (K := K) (L := M) (underM P))
          (arithFrobeniusAt (K := K) (L := M) QM) := by
        unfold arithFrobeniusAt
        apply isConj_arithFrobAt (NumberField.RingOfIntegers K) Gal(M/K)
          (underM P).asIdeal QM.asIdeal
        exact (underM_lies p P hPp).over.symm.trans hQMp.over
      rw [hQMtau] at hc
      apply hc.eq_of_right_mem_center
      apply Set.mem_center_iff.mpr
      refine ⟨fun x => IsMulCommutative.is_comm.comm tau x, ?_, ?_⟩
      · exact fun _ _ => mul_assoc _ _ _
      · exact fun _ _ => mul_assoc _ _ _
    let g := arithFrobeniusAt (K := K) (L := N) P
    have hgL : AlgEquiv.restrictNormalHom L g = sigma :=
      (arithFrobAt_restrict (K := K) (L := N) (M := L)
        P (underL P) hPL (hunrN P hPp)).trans hfrobL
    have hgM : AlgEquiv.restrictNormalHom M g = tau :=
      (arithFrobAt_restrict (K := K) (L := N) (M := M)
        P (underM P) hPM (hunrN P hPp)).trans hfrobM
    obtain ⟨ab, hab⟩ := pairEquiv.surjective g
    rcases ab with ⟨a, b⟩
    have ha : a = sigma := by
      calc
        a = AlgEquiv.restrictNormalHom L (pairEquiv (a, b)) :=
          (hrestrictL a b).symm
        _ = AlgEquiv.restrictNormalHom L g := congrArg _ hab
        _ = sigma := hgL
    have hb : b = tau := by
      calc
        b = AlgEquiv.restrictNormalHom M (pairEquiv (a, b)) :=
          (hrestrictM a b).symm
        _ = AlgEquiv.restrictNormalHom M g := congrArg _ hab
        _ = tau := hgM
    have hg : g = rho := by
      calc
        g = pairEquiv (a, b) := hab.symm
        _ = pairEquiv (sigma, tau) := by rw [ha, hb]
        _ = rho := rfl
    exact ⟨hunrN, P, hPp, hg⟩
  have hdiff : symmetricDifference SN T ⊆
      {p : PrimeIdeal K | ¬ IsUnramifiedPrime (K := K) (L := N) p} := by
    intro p hp
    rcases hp with hp | hp
    · exact (hp.2 (hNsub hp.1)).elim
    · intro hunrN
      exact hp.2 (hAway p hp.1 hunrN)
  have hdiff0 : HasDirichletDensity (symmetricDifference SN T) 0 :=
    finite_primeSet_hasDirichletDensity_zero
      ((ramifiedPrimes_finite (K := K) (L := N)).subset hdiff)
  have hSN : HasDirichletDensity SN
      (1 / (Nat.card Gal(N/K) : ℝ)) := hNelem
  have hT : HasDirichletDensity T
      (1 / (Nat.card Gal(N/K) : ℝ)) :=
    hSN.congr_of_symmetricDifference_zero hdiff0
  rw [hcardN] at hT
  simpa only [T, Nat.cast_mul] using hT

/-- The algebraic field-crossing core: the ramification argument selecting an
auxiliary cyclotomic field, and the compositum/fixed-field realization of a
simultaneous Frobenius pair.  This isolates the part of the blueprint that
requires a developed API for tensor-product composita of number fields. -/
private theorem fieldCrossing_algebraic_core
    (_U : Type u) (_V : Type v) (_W : Type w) :
    (∀ {K : Type u} {L : Type v} [Field K] [NumberField K]
      [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L],
      ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → ∀ avoid : Finset ℕ,
      ∃ ℓ : ℕ,
        Nat.Prime ℓ ∧ ℓ ∉ avoid ∧ Nat.ModEq (n ^ k) ℓ 1 ∧
        IsDomain (L ⊗[K] CyclotomicField ℓ K) ∧
        Module.finrank K (CyclotomicField ℓ K) = ℓ - 1 ∧
        IsCyclic (Gal(CyclotomicField ℓ K/K))) ∧
    (∀ {K : Type u} {L : Type v} {M : Type w} [Field K] [NumberField K]
      [Field L] [NumberField L] [Field M] [NumberField M]
      [Algebra K L] [Algebra K M]
      [FiniteDimensional K L] [FiniteDimensional K M]
      [IsGalois K L] [IsGalois K M] [IsMulCommutative (Gal(L/K))],
      ∀ (ℓ : ℕ) [IsCyclotomicExtension {ℓ} K M],
      ∀ (m : RayModulus K), 1 ≤ ℓ → IsCyclotomicModulus ℓ m →
      RamificationSupported (M := M) m → IsDomain (L ⊗[K] M) →
      ∀ (σ : Gal(L/K)) (τ : Gal(M/K)), orderOf σ ∣ orderOf τ →
      HasDirichletDensity
        (frobeniusElementPrimeSet (K := K) (L := L) σ ∩
          frobeniusElementPrimeSet (K := K) (L := M) τ)
        (1 / ((Nat.card (Gal(L/K)) : ℝ) * Nat.card (Gal(M/K))))) := by
  constructor
  · intro K L _ _ _ _ _ _ n k hn hk avoid
    let q := n ^ k
    have hq : q ≠ 0 := pow_ne_zero k (Nat.ne_of_gt hn)
    letI : NeZero q := ⟨hq⟩
    let bound := avoid.sum id + (NumberField.discr L).natAbs
    have hone : IsUnit (1 : ZMod q) := isUnit_one
    obtain ⟨p, hpbound, hp, hpeq⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod hone bound
    have hmod : Nat.ModEq q p 1 :=
      (ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hpeq)
    have hpavoid : p ∉ avoid := by
      intro hpa
      have hle : p ≤ avoid.sum id :=
        Finset.single_le_sum (fun i _ => Nat.zero_le i) hpa
      dsimp [bound] at hpbound
      omega
    have hpdiscL : ¬p ∣ (NumberField.discr L).natAbs := by
      intro hpd
      have hdpos : 0 < (NumberField.discr L).natAbs :=
        Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
      have hle := Nat.le_of_dvd hdpos hpd
      dsimp [bound] at hpbound
      omega
    have hpdiscK : ¬p ∣ (NumberField.discr K).natAbs := by
      intro hpd
      apply hpdiscL
      exact hpd.trans (Int.natAbs_dvd_natAbs.mpr
        (NumberField.discr_dvd_discr K L))
    have hKC := fieldCrossing_absolute_cyclotomic_tensor_isDomain
      (L := K) p hp hpdiscK
    have hLC := fieldCrossing_absolute_cyclotomic_tensor_isDomain
      (L := L) p hp hpdiscL
    have hrelative := fieldCrossing_relative_cyclotomic_data
      (K := K) (L := L) p hp hKC hLC
    refine ⟨p, hp, hpavoid, ?_, hrelative.1, hrelative.2.1, hrelative.2.2⟩
    simpa only [q] using hmod
  · intro K L M _ _ _ _ _ _ _ _ _ _ _ _ _ ell _ m hell hmod hram hdisj sigma tau horder
    exact fieldCrossing_pair_algebraic ell m hell hmod hram hdisj sigma tau horder

/-- Blueprint Lemma 7.1, proposed declaration
`exists_disjoint_cyclotomicExtension`: for every `k`, choose a rational prime
`ell ≡ 1 mod n^k`, outside a prescribed finite set, such that
`K(ζ_ell)/K` is cyclic of degree `ell-1` and linearly disjoint from `L/K`.
`IsDomain (L ⊗[K] M)` is the intrinsic tensor-product formulation of linear
disjointness, equivalent here to `L ∩ M = K`. -/
theorem exists_disjoint_cyclotomicExtension
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (avoid : Finset ℕ) :
    ∃ ℓ : ℕ,
      Nat.Prime ℓ ∧ ℓ ∉ avoid ∧ Nat.ModEq (n ^ k) ℓ 1 ∧
      IsDomain (L ⊗[K] CyclotomicField ℓ K) ∧
      Module.finrank K (CyclotomicField ℓ K) = ℓ - 1 ∧
      IsCyclic (Gal(CyclotomicField ℓ K/K)) := by
  exact (fieldCrossing_algebraic_core K L K).1 n k hn hk avoid

/-- The proportion of elements in a canonical cyclic group of order `N` whose
order is divisible by `n` (blueprint Lemma 7.2). -/
noncomputable def cyclicOrderDivisibleProportion (n N : ℕ) : ℝ :=
  Nat.card {h : Multiplicative (ZMod N) // n ∣ orderOf h} / (N : ℝ)

private theorem fieldCrossing_bad_divisor_witness
    (n k N d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hN : 0 < N)
    (hpow : n ^ k ∣ N) (hdN : d ∣ N) (hd : 0 < d)
    (hbad : ¬ n ∣ d) :
    ∃ p ∈ n.primeFactors,
      let r := (k - 1) * n.factorization p + 1
      d ∣ N / p ^ r ∧ 2 ^ k ≤ p ^ r := by
  have hfacnot : ¬ n.factorization ≤ d.factorization := by
    intro hfac
    exact hbad ((Nat.factorization_le_iff_dvd hn.ne' hd.ne').mp hfac)
  rw [Finsupp.le_def] at hfacnot
  push Not at hfacnot
  obtain ⟨p, hp⟩ := hfacnot
  have hpa : 0 < n.factorization p := lt_of_le_of_lt (Nat.zero_le _) hp
  have hpmem : p ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hpa.ne'
  have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpmem).1
  refine ⟨p, hpmem, ?_⟩
  let a := n.factorization p
  let r := (k - 1) * a + 1
  have ha : 1 ≤ a := hpa
  have hfacN : (n ^ k).factorization ≤ N.factorization :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero k hn.ne') hN.ne').mpr hpow
  have hkaN : k * a ≤ N.factorization p := by
    have hpN := hfacN p
    rw [Nat.factorization_pow] at hpN
    simpa [a, nsmul_eq_mul, mul_comm] using hpN
  have hrka : r ≤ k * a := by
    have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
    calc
      r = (k - 1) * a + 1 := rfl
      _ ≤ (k - 1) * a + a := Nat.add_le_add_left ha _
      _ = (k - 1 + 1) * a := by rw [add_mul, one_mul]
      _ = k * a := by rw [hks]
  have hpowp : p ^ r ∣ N :=
    (hpprime.pow_dvd_iff_le_factorization hN.ne').mpr (hrka.trans hkaN)
  have hfacd : d.factorization ≤ N.factorization :=
    (Nat.factorization_le_iff_dvd hd.ne' hN.ne').mpr hdN
  have hmul : p ^ r * d ∣ N := by
    rw [← Nat.factorization_le_iff_dvd
      (mul_ne_zero (pow_ne_zero _ hpprime.ne_zero) hd.ne') hN.ne']
    intro q
    rw [Nat.factorization_mul (pow_ne_zero _ hpprime.ne_zero) hd.ne', Finsupp.add_apply]
    by_cases hqp : q = p
    · subst q
      rw [hpprime.factorization_pow, Finsupp.single_eq_same]
      have hdp : d.factorization p + 1 ≤ a := hp
      calc
        r + d.factorization p ≤ r + (a - 1) := Nat.add_le_add_left
          (Nat.le_sub_of_add_le hdp) r
        _ = (k - 1) * a + a := by
          dsimp [r]
          omega
        _ = (k - 1 + 1) * a := by rw [add_mul, one_mul]
        _ = k * a := by rw [Nat.sub_add_cancel hk]
        _ ≤ N.factorization p := hkaN
    · rw [hpprime.factorization_pow, Finsupp.single_eq_of_ne hqp]
      simp only [zero_add]
      exact hfacd q
  have hdr : d ∣ N / p ^ r := by
    rw [Nat.dvd_div_iff_mul_dvd hpowp]
    simpa [Nat.mul_comm] using hmul
  have hkr : k ≤ r := by
    have hmulone : (k - 1) * 1 ≤ (k - 1) * a :=
      Nat.mul_le_mul_left (k - 1) ha
    simpa [r, Nat.sub_add_cancel hk] using Nat.add_le_add_right hmulone 1
  have htwo : 2 ^ k ≤ p ^ r :=
    (Nat.pow_le_pow_left hpprime.two_le k).trans
      (Nat.pow_le_pow_right hpprime.pos hkr)
  exact ⟨hdr, htwo⟩

private theorem fieldCrossing_cyclic_bad_card_le
    (n k N : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hN : 0 < N)
    (hpow : n ^ k ∣ N) :
    Nat.card {x : Multiplicative (ZMod N) // ¬ n ∣ orderOf x} ≤
      (n + 1) * (N / 2 ^ k) := by
  classical
  let G := Multiplicative (ZMod N)
  letI : NeZero N := ⟨hN.ne'⟩
  letI : Fintype G := Multiplicative.fintype
  have hcard : Nat.card G = N := by
    calc
      Nat.card G = Nat.card (ZMod N) := Nat.card_congr Multiplicative.toAdd
      _ = N := Nat.card_zmod N
  let r : ℕ → ℕ := fun p => (k - 1) * n.factorization p + 1
  let D : ℕ → ℕ := fun p => N / p ^ r p
  let B : ℕ → Finset G := fun p => Finset.univ.filter fun x => x ^ D p = 1
  let bad : Finset G := Finset.univ.filter fun x => ¬ n ∣ orderOf x
  have hcover : bad ⊆ n.primeFactors.biUnion B := by
    intro x hx
    have hxbad : ¬n ∣ orderOf x := (Finset.mem_filter.mp hx).2
    have hxdvd : orderOf x ∣ N := by
      have hFcard : Fintype.card G = N :=
        (Nat.card_eq_fintype_card.symm).trans hcard
      simpa only [hFcard] using (orderOf_dvd_card (x := x))
    obtain ⟨p, hpmem, hdiv, htwo⟩ := fieldCrossing_bad_divisor_witness
      n k N (orderOf x) hn hk hN hpow hxdvd (orderOf_pos x) hxbad
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hpmem, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa only [D, r] using hdiv
  have hB (p : ℕ) (hp : p ∈ n.primeFactors) :
      (B p).card ≤ N / 2 ^ k := by
    have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have ha : 1 ≤ n.factorization p := by
      rw [← Nat.support_factorization] at hp
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
    have hrka : r p ≤ k * n.factorization p := by
      calc
        r p = (k - 1) * n.factorization p + 1 := rfl
        _ ≤ (k - 1) * n.factorization p + n.factorization p :=
          Nat.add_le_add_left ha _
        _ = (k - 1 + 1) * n.factorization p := by rw [add_mul, one_mul]
        _ = k * n.factorization p := by rw [Nat.sub_add_cancel hk]
    have hpa_dvd : p ^ n.factorization p ∣ n :=
      (hpprime.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
    have hpk_dvd : p ^ (k * n.factorization p) ∣ n ^ k := by
      rw [Nat.mul_comm]
      simpa only [pow_mul] using (pow_dvd_pow_of_dvd hpa_dvd k)
    have hpr_dvd : p ^ r p ∣ N :=
      (pow_dvd_pow p hrka).trans (hpk_dvd.trans hpow)
    have hDpos : 0 < D p := by
      dsimp [D]
      exact Nat.div_pos (Nat.le_of_dvd hN hpr_dvd) (pow_pos hpprime.pos _)
    have hcardB : (B p).card ≤ D p := by
      simpa only [B] using
        (IsCyclic.card_pow_eq_one_le (α := G) hDpos)
    have htwo : 2 ^ k ≤ p ^ r p := by
      have hkr : k ≤ r p := by
        have hmulone : (k - 1) * 1 ≤ (k - 1) * n.factorization p :=
          Nat.mul_le_mul_left (k - 1) ha
        simpa [r, Nat.sub_add_cancel hk] using Nat.add_le_add_right hmulone 1
      exact (Nat.pow_le_pow_left hpprime.two_le k).trans
        (Nat.pow_le_pow_right hpprime.pos hkr)
    exact hcardB.trans (Nat.div_le_div_left htwo (pow_pos (by omega) k))
  have hpfcard : n.primeFactors.card ≤ n + 1 := by
    calc
      n.primeFactors.card ≤ (Finset.range (n + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le
          (Nat.le_of_dvd hn (Nat.mem_primeFactors.mp hp).2.1)
      _ = n + 1 := Finset.card_range _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change bad.card ≤ (n + 1) * (N / 2 ^ k)
  calc
    bad.card ≤ (n.primeFactors.biUnion B).card := Finset.card_le_card hcover
    _ ≤ ∑ p ∈ n.primeFactors, (B p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ n.primeFactors, N / 2 ^ k := by
      apply Finset.sum_le_sum
      intro p hp
      exact hB p hp
    _ = n.primeFactors.card * (N / 2 ^ k) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ (n + 1) * (N / 2 ^ k) := Nat.mul_le_mul_right _ hpfcard

/-- Blueprint Lemma 7.2, proposed declaration
`cyclic_proportion_orderOf_dvd_tendsto_one`: if `n^k ∣ N_k`, the proportion
of elements of a cyclic group of order `N_k` whose order is divisible by `n`
tends to one. -/
theorem cyclic_proportion_orderOf_dvd_tendsto_one
    (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hNpos : ∀ k, 0 < N k) (hdiv : ∀ k, n ^ k ∣ N k) :
    Tendsto (fun k : ℕ => cyclicOrderDivisibleProportion n (N k))
      atTop (𝓝 1) := by
  classical
  let good : ℕ → ℕ := fun k =>
    Nat.card {x : Multiplicative (ZMod (N k)) // n ∣ orderOf x}
  let bad : ℕ → ℕ := fun k =>
    Nat.card {x : Multiplicative (ZMod (N k)) // ¬ n ∣ orderOf x}
  have htotal (k : ℕ) : good k + bad k = N k := by
    letI : NeZero (N k) := ⟨(hNpos k).ne'⟩
    change Nat.card {x : Multiplicative (ZMod (N k)) // n ∣ orderOf x} +
      Nat.card {x : Multiplicative (ZMod (N k)) // ¬n ∣ orderOf x} = N k
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not
      (fun x : Multiplicative (ZMod (N k)) => n ∣ orderOf x)
      (s := Finset.univ)
    have hcard : Fintype.card (Multiplicative (ZMod (N k))) = N k := by
      calc
        Fintype.card (Multiplicative (ZMod (N k))) = Fintype.card (ZMod (N k)) :=
          Fintype.card_congr Multiplicative.toAdd
        _ = N k := ZMod.card _
    simpa only [Finset.card_univ, hcard] using hpart
  have hdist (k : ℕ) :
      ‖cyclicOrderDivisibleProportion n (N k) - 1‖ =
        (bad k : ℝ) / N k := by
    have hgoodle : good k ≤ N k := by
      have ht := htotal k
      omega
    have hNreal : (0 : ℝ) < N k := Nat.cast_pos.mpr (hNpos k)
    have hprop_le : (good k : ℝ) / N k ≤ 1 := by
      rw [div_le_one hNreal]
      exact_mod_cast hgoodle
    unfold cyclicOrderDivisibleProportion
    change ‖(good k : ℝ) / N k - 1‖ = (bad k : ℝ) / N k
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hprop_le)]
    have ht : (good k : ℝ) + bad k = N k := by exact_mod_cast htotal k
    field_simp
    linarith
  have hbound : ∀ᶠ k : ℕ in atTop,
      ‖cyclicOrderDivisibleProportion n (N k) - 1‖ ≤
        (n + 1 : ℝ) * (1 / 2 : ℝ) ^ k := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    rw [hdist]
    have hb := fieldCrossing_cyclic_bad_card_le n k (N k)
      (Nat.zero_lt_of_lt hn) hk (hNpos k) (hdiv k)
    have hbR : (bad k : ℝ) ≤ ((n + 1) * (N k / 2 ^ k) : ℕ) := by
      exact_mod_cast hb
    have hNreal : (0 : ℝ) < N k := Nat.cast_pos.mpr (hNpos k)
    calc
      (bad k : ℝ) / N k ≤ ((n + 1) * (N k / 2 ^ k) : ℕ) / (N k : ℝ) :=
        div_le_div_of_nonneg_right hbR hNreal.le
      _ ≤ ((n + 1 : ℝ) * ((N k : ℝ) / (2 ^ k : ℕ))) / (N k : ℝ) := by
        push_cast
        gcongr
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          (Nat.cast_div_le : ((N k / 2 ^ k : ℕ) : ℝ) ≤ _)
      _ = (n + 1 : ℝ) * (1 / 2 : ℝ) ^ k := by
        push_cast
        rw [one_div, inv_pow]
        field_simp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)).const_mul (n + 1 : ℝ)

/-- Blueprint equation (14)'s elementary order input
(`orderOf_prod_eq_right_of_dvd`): if `ord(σ) ∣ ord(τ)`, then
`ord((σ,τ)) = ord(τ)`. -/
theorem orderOf_prod_eq_right_of_dvd
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (σ : G) (τ : H) (h : orderOf σ ∣ orderOf τ) :
    orderOf (σ, τ) = orderOf τ := by
  rw [Prod.orderOf_mk, Nat.lcm_eq_right_iff_dvd.mpr h]

/-- The good auxiliary elements `S_σ = {τ : ord(σ) ∣ ord(τ)}` from blueprint
§7.2. -/
def fieldCrossingGoodElements {G H : Type*} [Group G] [Group H]
    (σ : G) : Set H :=
  {τ | orderOf σ ∣ orderOf τ}

/-- Blueprint equation (15) (`fieldCrossing_pair_dirichletDensity`): for a good
auxiliary element, the simultaneous Frobenius pair has Dirichlet density
`1/(|G||H|)`. The intersection is the base-prime realization of the pair set
under linear disjointness. -/
theorem fieldCrossing_pair_dirichletDensity
    {K L M : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsMulCommutative (Gal(L/K))]
    (ℓ : ℕ) [IsCyclotomicExtension {ℓ} K M]
    (m : RayModulus K) (hℓ : 1 ≤ ℓ)
    (hmod : IsCyclotomicModulus ℓ m)
    (hram : RamificationSupported (M := M) m)
    (hdisj : IsDomain (L ⊗[K] M))
    (σ : Gal(L/K)) (τ : Gal(M/K))
    (horder : orderOf σ ∣ orderOf τ) :
    HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := L) σ ∩
        frobeniusElementPrimeSet (K := K) (L := M) τ)
      (1 / ((Nat.card (Gal(L/K)) : ℝ) * Nat.card (Gal(M/K)))) := by
  exact (fieldCrossing_algebraic_core K L M).2
    ℓ m hℓ hmod hram hdisj σ τ horder

private theorem fieldCrossing_coeff_sum
    {K : Type*} [Field K] [NumberField K] (n : ℕ) :
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
    exact ⟨(Ideal.absNorm_eq_zero_iff.not.mp
      (Nat.one_le_iff_ne_zero.mp hI.1)), hI.2⟩
  · have hne : Ideal.absNorm I.1 ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr I.2.1
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, I.2.2⟩

private theorem fieldCrossing_summable_ideal_rpow
    {K : Type*} [Field K] [NumberField K] (s : ℝ) (hs : 1 < s) :
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
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    change (∑ k ∈ Finset.Icc 1 n, (Nat.card
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = k} : ℝ)) ≤
        A * Real.rpow (n : ℝ) 1
    rw [show Real.rpow (n : ℝ) 1 = (n : ℝ) ^ (1 : ℝ) from rfl,
      Real.rpow_one, ← Nat.cast_sum, fieldCrossing_coeff_sum]
    simpa only [Nat.cast_le] using hideal n (by exact_mod_cast hn)
  have hL : LSeriesSummable (fun n => (a n : ℂ)) (s : ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO
      (fun _ => Nat.cast_nonneg _) (by norm_num) (by simpa using hs)
  have hnorm : Summable
      (fun n => ‖LSeries.term (fun n => (a n : ℂ)) (s : ℂ) n‖) :=
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

private theorem fieldCrossing_summable_prime_rpow
    {K : Type*} [Field K] [NumberField K] (s : ℝ) (hs : 1 < s) :
    Summable (fun p : PrimeIdeal K =>
      Real.rpow (PrimeIdeal.norm p : ℝ) (-s)) := by
  apply ((fieldCrossing_summable_ideal_rpow (K := K) s hs).comp_injective
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective).congr
  intro p
  rfl

private theorem fieldCrossing_dirichletPrimeSum_mono
    {K : Type*} [Field K] [NumberField K]
    {S T : Set (PrimeIdeal K)} (hST : S ⊆ T)
    (s : ℝ) (hs : 1 < s) :
    dirichletPrimeSum S s ≤ dirichletPrimeSum T s := by
  classical
  unfold dirichletPrimeSum
  let f : Set (PrimeIdeal K) → PrimeIdeal K → ℝ := fun U p =>
    if p ∈ U then Real.rpow (PrimeIdeal.norm p : ℝ) (-s) else 0
  have hbase := fieldCrossing_summable_prime_rpow (K := K) s hs
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
  apply (hsum S).tsum_le_tsum _ (hsum T)
  intro p
  simp only [f]
  by_cases hp : p ∈ S
  · rw [if_pos hp, if_pos (hST hp)]
  · rw [if_neg hp]
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl

private theorem fieldCrossing_lowerDirichletDensity_ge_of_subset
    {K : Type*} [Field K] [NumberField K]
    {S T : Set (PrimeIdeal K)} {δ : ℝ}
    (hST : S ⊆ T) (hS : HasDirichletDensity S δ) :
    δ ≤ lowerDirichletDensity T := by
  let fS : ℝ → ℝ := fun s =>
    dirichletPrimeSum S s / dirichletNormalizer s
  let fT : ℝ → ℝ := fun s =>
    dirichletPrimeSum T s / dirichletNormalizer s
  let fU : ℝ → ℝ := fun s =>
    dirichletPrimeSum (Set.univ : Set (PrimeIdeal K)) s /
      dirichletNormalizer s
  have hlt2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  have hden : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < dirichletNormalizer s := by
    filter_upwards [self_mem_nhdsWithin, hlt2] with s hs hs2
    unfold dirichletNormalizer
    apply Real.log_pos
    rw [one_lt_div₀ (sub_pos.mpr hs)]
    linarith
  have hSTev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), fS s ≤ fT s := by
    filter_upwards [self_mem_nhdsWithin, hden] with s hs hpos
    exact div_le_div_of_nonneg_right
      (fieldCrossing_dirichletPrimeSum_mono hST s hs) hpos.le
  have hTUev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), fT s ≤ fU s := by
    filter_upwards [self_mem_nhdsWithin, hden] with s hs hpos
    exact div_le_div_of_nonneg_right
      (fieldCrossing_dirichletPrimeSum_mono (Set.subset_univ T) s hs) hpos.le
  have hSlim : Tendsto fS (𝓝[>] (1 : ℝ)) (𝓝 δ) := hS
  have hUlim : Tendsto fU (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    allPrimes_dirichletDensity_one (K := K)
  have hTupper : (𝓝[>] (1 : ℝ)).IsCoboundedUnder (· ≥ ·) fT := by
    obtain ⟨b, hb⟩ := hUlim.isBoundedUnder_le
    exact (show (𝓝[>] (1 : ℝ)).IsBoundedUnder (· ≤ ·) fT from
      ⟨b, (hTUev.and hb).mono fun _ h => h.1.trans h.2⟩).isCoboundedUnder_ge
  change δ ≤ liminf fT (𝓝[>] (1 : ℝ))
  rw [← hSlim.liminf_eq]
  exact Filter.liminf_le_liminf hSTev hSlim.isBoundedUnder_ge hTupper

private theorem frobeniusElementPrimeSet_disjoint
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))]
    {g h : Gal(L/K)} (hgh : g ≠ h) :
    Disjoint (frobeniusElementPrimeSet (K := K) (L := L) g)
      (frobeniusElementPrimeSet (K := K) (L := L) h) := by
  apply Set.disjoint_left.2
  intro p hpg hph
  rcases hpg with ⟨hunr, P, hPp, hPg⟩
  rcases hph with ⟨_, Q, hQp, hQh⟩
  apply hgh
  have hc : IsConj (arithFrobeniusAt (K := K) (L := L) P)
      (arithFrobeniusAt (K := K) (L := L) Q) := by
    unfold arithFrobeniusAt
    apply isConj_arithFrobAt (NumberField.RingOfIntegers K) (Gal(L/K))
      P.asIdeal Q.asIdeal
    exact hPp.over.symm.trans hQp.over
  rw [hPg, hQh] at hc
  apply hc.eq_of_right_mem_center
  apply Set.mem_center_iff.mpr
  refine ⟨fun x => IsMulCommutative.is_comm.comm h x, ?_, ?_⟩
  · exact fun _ _ => mul_assoc _ _ _
  · exact fun _ _ => mul_assoc _ _ _

private theorem abelian_chebotarev_lower_bound
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))]
    (σ : Gal(L/K)) :
    1 / (Nat.card (Gal(L/K)) : ℝ) ≤
      lowerDirichletDensity
        (frobeniusElementPrimeSet (K := K) (L := L) σ) := by
  classical
  let G := Gal(L/K)
  let n := orderOf σ
  have hn : 1 ≤ n := orderOf_pos σ
  let ℓ : ℕ → ℕ := fun k => Classical.choose
    (exists_disjoint_cyclotomicExtension (K := K) (L := L)
      n (k + 1) hn (Nat.succ_pos k) ∅)
  have hℓ (k : ℕ) :
      Nat.Prime (ℓ k) ∧ (ℓ k) ∉ (∅ : Finset ℕ) ∧
        Nat.ModEq (n ^ (k + 1)) (ℓ k) 1 ∧
        IsDomain (L ⊗[K] CyclotomicField (ℓ k) K) ∧
        Module.finrank K (CyclotomicField (ℓ k) K) = ℓ k - 1 ∧
        IsCyclic (Gal(CyclotomicField (ℓ k) K/K)) :=
    Classical.choose_spec
      (exists_disjoint_cyclotomicExtension (K := K) (L := L)
        n (k + 1) hn (Nat.succ_pos k) ∅)
  let N : ℕ → ℕ := fun k => ℓ k - 1
  have hNpos (k : ℕ) : 0 < N k := by
    dsimp [N]
    exact Nat.sub_pos_of_lt (Nat.Prime.one_lt (hℓ k).1)
  have hNdiv (k : ℕ) : n ^ k ∣ N k := by
    have hle : 1 ≤ ℓ k := (hℓ k).1.one_lt.le
    have hd : n ^ (k + 1) ∣ ℓ k - 1 :=
      (Nat.modEq_iff_dvd' hle).mp (hℓ k).2.2.1.symm
    exact (pow_dvd_pow n (Nat.le_succ k)).trans hd
  have hprop : Tendsto
      (fun k => cyclicOrderDivisibleProportion n (N k)) atTop (𝓝 1) :=
    cyclic_proportion_orderOf_dvd_tendsto_one n hn N hNpos hNdiv
  have hlowerAux (k : ℕ) :
      cyclicOrderDivisibleProportion n (N k) / (Nat.card G : ℝ) ≤
        lowerDirichletDensity
          (frobeniusElementPrimeSet (K := K) (L := L) σ) := by
    let M := CyclotomicField (ℓ k) K
    have hprime : Nat.Prime (ℓ k) := (hℓ k).1
    have hdisj : IsDomain (L ⊗[K] M) := (hℓ k).2.2.2.1
    have hfin : Module.finrank K M = ℓ k - 1 := (hℓ k).2.2.2.2.1
    have hcyc : IsCyclic Gal(M/K) := (hℓ k).2.2.2.2.2
    letI : FiniteDimensional K M :=
      IsCyclotomicExtension.finiteDimensional {(ℓ k)} K M
    letI : IsGalois K M := IsCyclotomicExtension.isGalois {(ℓ k)} K M
    letI : IsCyclic Gal(M/K) := hcyc
    letI : IsMulCommutative Gal(M/K) := IsCyclic.isMulCommutative
    have hMcard : Nat.card Gal(M/K) = N k := by
      rw [IsGalois.card_aut_eq_finrank, hfin]
    obtain ⟨m, hmod, hram⟩ :=
      exists_cyclotomicModulus (K := K) (M := M) (ℓ k) hprime.one_lt.le
    let T := {τ : Gal(M/K) // n ∣ orderOf τ}
    let A : T → Set (PrimeIdeal K) := fun τ =>
      frobeniusElementPrimeSet (K := K) (L := L) σ ∩
        frobeniusElementPrimeSet (K := K) (L := M) τ
    have hAdisj : Set.PairwiseDisjoint Set.univ A := by
      intro a ha b hb hab
      apply Set.disjoint_left.2
      intro p hpa hpb
      exact Set.disjoint_left.1
        (frobeniusElementPrimeSet_disjoint (K := K) (L := M)
          (show a.val ≠ b.val from fun h => hab (Subtype.ext h))) hpa.2 hpb.2
    have hA (τ : T) : HasDirichletDensity (A τ)
        (1 / ((Nat.card G : ℝ) * Nat.card Gal(M/K))) := by
      exact fieldCrossing_pair_dirichletDensity
        (K := K) (L := L) (M := M) (ℓ k) m hprime.one_lt.le
        hmod hram hdisj σ τ.val τ.prop
    have hU : HasDirichletDensity (⋃ τ, A τ)
        ((Nat.card T : ℝ) /
          ((Nat.card G : ℝ) * Nat.card Gal(M/K))) := by
      have hu := hasDirichletDensity_finite_iUnion A
        (fun _ : T => 1 / ((Nat.card G : ℝ) * Nat.card Gal(M/K)))
        hAdisj hA
      convert hu using 1
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      simp only [nsmul_eq_mul]
      ring
    have hsub : (⋃ τ, A τ) ⊆
        frobeniusElementPrimeSet (K := K) (L := L) σ := by
      intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨τ, hτ⟩ := hp
      exact hτ.1
    have hbound := fieldCrossing_lowerDirichletDensity_ge_of_subset hsub hU
    let e : Multiplicative (ZMod (N k)) ≃* Gal(M/K) := by
      rw [← hMcard]
      exact zmodCyclicMulEquiv hcyc
    let eGood : {x : Multiplicative (ZMod (N k)) // n ∣ orderOf x} ≃ T :=
      Equiv.subtypeEquiv e.toEquiv (fun x => by
        change n ∣ orderOf x ↔ n ∣ orderOf (e x)
        rw [e.orderOf_eq])
    have hgood : Nat.card T =
        Nat.card {x : Multiplicative (ZMod (N k)) // n ∣ orderOf x} := by
      exact (Nat.card_congr eGood).symm
    calc
      cyclicOrderDivisibleProportion n (N k) / (Nat.card G : ℝ) =
          (Nat.card T : ℝ) /
            ((Nat.card G : ℝ) * Nat.card Gal(M/K)) := by
        unfold cyclicOrderDivisibleProportion
        rw [← hgood, ← hMcard]
        ring
      _ ≤ lowerDirichletDensity
          (frobeniusElementPrimeSet (K := K) (L := L) σ) := hbound
  apply le_of_tendsto (hprop.div_const (Nat.card G : ℝ))
  exact Eventually.of_forall hlowerAux

/-- Blueprint Theorem 7.3 and §9 (`abelian_chebotarev_dirichletDensity`):
Chebotarev for each element of a finite abelian extension, in Dirichlet
density. -/
theorem abelian_chebotarev_dirichletDensity
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))]
    (σ : Gal(L/K)) :
    HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := L) σ)
      (1 / (Nat.card (Gal(L/K)) : ℝ)) := by
  classical
  let G := Gal(L/K)
  let S : G → Set (PrimeIdeal K) := fun g =>
    frobeniusElementPrimeSet (K := K) (L := L) g
  let δ : G → ℝ := fun _ => 1 / (Nat.card G : ℝ)
  letI : Fintype G := Fintype.ofFinite G
  have hSdisj : Set.PairwiseDisjoint Set.univ S := by
    intro g hg h hh hgh
    exact frobeniusElementPrimeSet_disjoint hgh
  have hcover : HasDirichletDensity
      (symmetricDifference (⋃ g, S g) (Set.univ : Set (PrimeIdeal K))) 0 := by
    have hsub : symmetricDifference (⋃ g, S g)
        (Set.univ : Set (PrimeIdeal K)) ⊆
        {p : PrimeIdeal K | ¬ IsUnramifiedPrime (K := K) (L := L) p} := by
      intro p hp
      rcases hp with hp | hp
      · exact (hp.2 trivial).elim
      · intro hunr
        apply hp.2
        obtain ⟨Pideal, hPmax, hPp⟩ :=
          Ideal.exists_maximal_ideal_liesOver_of_isIntegral
            (S := NumberField.RingOfIntegers L) p.asIdeal
        let P : PrimeIdeal L :=
          ⟨Pideal, hPmax.isPrime, by
            intro hbot
            apply p.ne_bot
            have hover := hPp.over
            rw [hbot] at hover
            simpa using hover⟩
        let g := arithFrobeniusAt (K := K) (L := L) P
        apply Set.mem_iUnion_of_mem g
        exact ⟨hunr, P, hPp, rfl⟩
    exact finite_primeSet_hasDirichletDensity_zero
      ((ramifiedPrimes_finite (K := K) (L := L)).subset hsub)
  have hsum : ∑ g : G, δ g = 1 := by
    simp only [δ]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_eq_nat_card]
    have hG0 : (Nat.card G : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  have hallLower : ∀ g, δ g ≤ lowerDirichletDensity (S g) := by
    intro g
    exact abelian_chebotarev_lower_bound g
  exact finite_partition_squeeze_dirichlet S δ hSdisj hcover
    (allPrimes_dirichletDensity_one (K := K)) hallLower hsum σ

/-- Blueprint Theorem 1.2, §8, and §9
(`chebotarev_dirichletDensity`): the full Chebotarev theorem for Dirichlet
density. This is milestone M7 and uses Deuring after the abelian theorem. -/
theorem chebotarev_dirichletDensity
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (C : ConjClasses (Gal(L/K))) :
    HasDirichletDensity
      (frobeniusPrimeSet (K := K) (L := L) C)
      ((C.carrier.ncard : ℝ) / (Nat.card (Gal(L/K)) : ℝ)) := by
  induction C using Quotient.inductionOn with
  | _ g =>
    change HasDirichletDensity
      (frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g))
      (((ConjClasses.mk g).carrier.ncard : ℝ) /
        (Nat.card (Gal(L/K)) : ℝ))
    let E := deuringFixedField g
    let H : Subgroup (Gal(L/K)) := Subgroup.zpowers g
    let e : H ≃* Gal(L/E) := IntermediateField.subgroupEquivAlgEquiv H
    let gE : Gal(L/E) := e ⟨g, Subgroup.mem_zpowers g⟩
    have hgE : AlgEquiv.restrictScalarsHom K gE = g := by
      ext x
      rfl
    have hset : deuringUpstairsPrimeSet (K := K) (L := L) g =
        frobeniusElementPrimeSet (K := E) (L := L) gE := by
      ext q
      constructor
      · rintro ⟨hunr, P, hPq, hP⟩
        refine ⟨hunr, P, hPq, ?_⟩
        apply AlgEquiv.restrictScalarsHom_injective K
        rw [hP, hgE]
      · rintro ⟨hunr, P, hPq, hP⟩
        refine ⟨hunr, P, hPq, ?_⟩
        rw [hP, hgE]
    have hcardE : Nat.card Gal(L/E) = orderOf g := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_zpowers]
    letI : IsCyclic Gal(L/E) := (e.isCyclic).mp inferInstance
    letI : IsMulCommutative Gal(L/E) := IsCyclic.isMulCommutative
    have hup : HasDirichletDensity
        (deuringUpstairsPrimeSet (K := K) (L := L) g)
        (1 / (orderOf g : ℝ)) := by
      rw [hset]
      have h := abelian_chebotarev_dirichletDensity (K := E) (L := L) gE
      rw [hcardE] at h
      exact h
    have hdivC : Nat.card
        (Subgroup.centralizer ({g} : Set (Gal(L/K)))) ∣
        Nat.card (Gal(L/K)) := Subgroup.card_subgroup_dvd_card _
    have hclass : (ConjClasses.mk g).carrier.ncard =
        Nat.card (Gal(L/K)) /
          Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) := by
      letI : Fintype (Gal(L/K)) := Fintype.ofFinite _
      letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
      letI : Fintype (MulAction.stabilizer (ConjAct (Gal(L/K))) g) :=
        Fintype.ofFinite _
      rw [← Set.fintypeCard_eq_ncard]
      rw [ConjClasses.card_carrier]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      rw [ConjAct.stabilizer_eq_centralizer]
      rfl
    have hfactor : (deuringFactor g : ℝ) *
          (((ConjClasses.mk g).carrier.ncard : ℝ) /
            (Nat.card (Gal(L/K)) : ℝ)) =
        1 / (orderOf g : ℝ) := by
      rw [hclass]
      unfold deuringFactor
      rw [Nat.cast_div_charZero (deuringFactor_isInteger g),
        Nat.cast_div_charZero hdivC]
      have hG : (Nat.card (Gal(L/K)) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hC : (Nat.card
          (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have ho : (orderOf g : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (orderOf_pos g).ne'
      field_simp
    apply (deuring_dirichletDensity (K := K) (L := L) g _).mp
    rw [hfactor]
    exact hup

end NU.Chebotarev
