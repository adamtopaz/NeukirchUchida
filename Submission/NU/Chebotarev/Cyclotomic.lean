import Submission.NU.Chebotarev.WeberL
import Submission.NU.Chebotarev.Frobenius

/-!
# M6b. The cyclotomic case without reciprocity

Blueprint §6 and §9. The image subgroup of the elementary ideal map remains
explicit through the zeta factorization; surjectivity is a conclusion of the
pole-order argument, never an assumption (design caution §10.5(3)).
-/

open Filter Topology
open scoped BigOperators nonZeroDivisors IsMulCommutative

namespace NU.Chebotarev

variable {K M F : Type*} [Field K] [NumberField K]
  [Field M] [NumberField M] [Field F] [NumberField F]
  [Algebra K M] [Algebra K F] [Algebra M F] [IsScalarTower K M F]
  [FiniteDimensional K M] [IsGalois K M]

/-- The modulus contains the cyclotomic conductor and all real places, as in
blueprint §6 before Lemma 6.1. -/
def IsCyclotomicModulus (n : ℕ) (m : RayModulus K) : Prop :=
  Ideal.span {algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ)} ∣ m.finite ∧
    ∀ σ : K →+* ℝ, σ ∈ m.infinite

/-- Every prime ramified in `M/K` is among the finite Euler factors removed by
the modulus (blueprint §6). -/
def RamificationSupported (m : RayModulus K) : Prop :=
  ∀ Q : PrimeIdeal M,
    ¬Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal →
      Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite

/-- Blueprint §6 setup (`exists_cyclotomicModulus`): one can enlarge the
finite part to contain the conductor and all ramified primes, and select every
real place in the infinite part. -/
theorem exists_cyclotomicModulus (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : RayModulus K,
      IsCyclotomicModulus n m ∧ RamificationSupported (M := M) m := by
  classical
  let S : Set (PrimeIdeal K) :=
    {p | ¬IsUnramifiedPrime (L := M) p}
  have hS : S.Finite := ramifiedPrimes_finite (K := K) (L := M)
  let J : Ideal (NumberField.RingOfIntegers K) :=
    ∏ p ∈ hS.toFinset, p.asIdeal
  have hJ : J ≠ 0 := by
    dsimp [J]
    apply (Finset.prod_ne_zero_iff).2
    intro p hp
    exact p.ne_bot
  have hn0 : algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ) ≠ 0 := by
    apply (map_ne_zero_iff (algebraMap ℤ (NumberField.RingOfIntegers K))
      (FaithfulSMul.algebraMap_injective ℤ
        (NumberField.RingOfIntegers K))).2
    exact_mod_cast (Nat.ne_of_gt hn)
  letI := Fintype.ofFinite (K →+* ℝ)
  let m : RayModulus K :=
    { finite := Ideal.span
        {algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ)} * J
      finite_ne := mul_ne_zero (by simpa using hn0) hJ
      infinite := Finset.univ }
  refine ⟨m, ?_, ?_⟩
  · constructor
    · exact dvd_mul_right _ _
    · intro σ
      simp [m]
  · intro Q hQ
    let p : PrimeIdeal K :=
      ⟨Q.asIdeal.under (NumberField.RingOfIntegers K), inferInstance, by
        intro hp
        letI : Q.asIdeal.LiesOver
            (⊥ : Ideal (NumberField.RingOfIntegers K)) := ⟨by simpa [hp]⟩
        exact Q.ne_bot
          (Ideal.eq_bot_of_liesOver_bot
            (NumberField.RingOfIntegers K) Q.asIdeal)⟩
    have hQp : Q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
    have hpS : p ∈ S := by
      intro hp
      exact hQ (hp Q hQp)
    have hpJ : p.asIdeal ∣ J :=
      Finset.dvd_prod_of_mem (fun q : PrimeIdeal K => q.asIdeal)
        ((Set.Finite.mem_toFinset hS).2 hpS)
    change p.asIdeal ∣ m.finite
    exact dvd_mul_of_dvd_right hpJ _

/-- Unit-valued finite-group characters. This is the alternative explicitly
allowed by design caution §10.5(4); coercion to `ℂ` happens only in series. -/
abbrev UnitCharacter (G : Type*) [Group G] := G →* ℂˣ

/-- Pull a unit-valued finite character back along a group homomorphism and form
its Weber series. -/
noncomputable def weberLSeriesAlong {G : Type*} [Group G]
    (m : RayModulus K) (ν : RayClassGroup m →* G)
    (χ : UnitCharacter G) (s : ℂ) : ℂ :=
  ∑' c : RayClassGroup m, (χ (ν c) : ℂ) * rayClassPartialZeta m c s

/-- Corestrict a homomorphism to its explicit image subgroup. -/
def corestrictToRange {G H : Type*} [Group G] [Group H] (ν : G →* H) :
    G →* MonoidHom.range ν :=
  ν.codRestrict (MonoidHom.range ν) (fun x => ⟨x, rfl⟩)

/-- The incomplete Dedekind zeta Euler product of `M`, removing every prime
above a base prime dividing `m₀` (blueprint equation (10), §10.5(5)). -/
noncomputable def incompleteExtensionZeta (m : RayModulus K) (s : ℂ) : ℂ := by
  classical
  exact ∏' Q : PrimeIdeal M,
    if Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite then 1 else
      (1 - Complex.cpow (PrimeIdeal.norm Q : ℂ) (-s))⁻¹

open NumberField
open NumberField.mixedEmbedding
private noncomputable def cyclotomicIdealFactors {K : Type*} [Field K] [NumberField K]
    (I : FractionalIdealGroup (K := K)) : PrimeIdeal K →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun p => FractionalIdeal.count K p
      (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K))
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors
      (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)))
@[simp] private theorem cyclotomicIdealFactors_apply {K : Type*} [Field K] [NumberField K]
    (I : FractionalIdealGroup (K := K)) (p : PrimeIdeal K) :
    cyclotomicIdealFactors I p = FractionalIdeal.count K p
      (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := rfl
@[simp] private theorem cyclotomicIdealFactors_one {K : Type*} [Field K] [NumberField K] :
    cyclotomicIdealFactors (1 : FractionalIdealGroup (K := K)) = 0 := by
  ext p
  rw [cyclotomicIdealFactors_apply, Finsupp.zero_apply]
  exact FractionalIdeal.count_one K p
@[simp] private theorem cyclotomicIdealFactors_mul {K : Type*} [Field K] [NumberField K]
    (I J : FractionalIdealGroup (K := K)) : cyclotomicIdealFactors (I * J) = cyclotomicIdealFactors I + cyclotomicIdealFactors J := by
  ext p
  rw [cyclotomicIdealFactors_apply, Finsupp.add_apply, cyclotomicIdealFactors_apply, cyclotomicIdealFactors_apply]
  exact FractionalIdeal.count_mul K p I.ne_zero J.ne_zero
private noncomputable def cyclotomicFreeIdealMap {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (f : PrimeIdeal K → G) : FractionalIdealGroup (K := K) →* G := by
  classical
  exact {
  toFun I := (cyclotomicIdealFactors I).prod fun p e => f p ^ e
  map_one' := by rw [cyclotomicIdealFactors_one, Finsupp.prod_zero_index]
  map_mul' I J := by
    rw [cyclotomicIdealFactors_mul]
    apply Finsupp.prod_add_index
    · intro p hp
      simp
    · intro p hp a b
      exact zpow_add (f p) a b
  }
private theorem cyclotomicFreeIdealMap_eq_finprod {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (u : PrimeIdeal K → G) (I : FractionalIdealGroup (K := K)) :
    (cyclotomicIdealFactors I).prod (fun p e => u p ^ e) =
      ∏ᶠ p : PrimeIdeal K, u p ^ FractionalIdeal.count K p
        (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  classical
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := (cyclotomicIdealFactors I).support)]
  · rfl
  · intro p hp
    change u p ^ FractionalIdeal.count K p
      (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ≠ 1 at hp
    by_contra hnot
    have hz : cyclotomicIdealFactors I p = 0 := Finsupp.notMem_support_iff.mp (by simpa using hnot)
    rw [cyclotomicIdealFactors_apply] at hz
    rw [hz, zpow_zero] at hp
    exact hp rfl
private theorem cyclotomic_facNorm {K : Type*} [Field K] [NumberField K]
    (J : Ideal (NumberField.RingOfIntegers K)) (hJ : J ≠ 0) :
    (∏ᶠ p : PrimeIdeal K, (PrimeIdeal.norm p : ℚ) ^
      (FractionalIdeal.count K p
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K))) =
      (Ideal.absNorm J : ℚ) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization'
    (K := K) (I := (J : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K))
    (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)
  have hsupp : Function.HasFiniteMulSupport
      (fun p : PrimeIdeal K =>
        (p.asIdeal : FractionalIdeal
          (NumberField.RingOfIntegers K)⁰ K) ^
          FractionalIdeal.count K p
            (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) := by
    apply (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors
      (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K))).subset
    intro p hp hcount
    change (p.asIdeal : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K) ^
        FractionalIdeal.count K p
          (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ≠ 1 at hp
    rw [hcount, zpow_zero] at hp
    exact hp rfl
  have hmap := (FractionalIdeal.absNorm : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K →*₀ ℚ).toMonoidHom.map_finprod hsupp
  rw [hfac] at hmap
  change FractionalIdeal.absNorm
    (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = _ at hmap
  rw [FractionalIdeal.coeIdeal_absNorm] at hmap
  calc
    _ = ∏ᶠ p : PrimeIdeal K,
        FractionalIdeal.absNorm
          ((p.asIdeal : FractionalIdeal
            (NumberField.RingOfIntegers K)⁰ K) ^
            FractionalIdeal.count K p
              (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) := by
      apply finprod_congr
      intro p
      let P : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K := p.asIdeal
      let e := FractionalIdeal.count K p
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
      have hz := map_zpow₀
        (FractionalIdeal.absNorm : FractionalIdeal
          (NumberField.RingOfIntegers K)⁰ K →*₀ ℚ) P e
      calc
        (PrimeIdeal.norm p : ℚ) ^ e = FractionalIdeal.absNorm P ^ e := by
          congr 1
          rw [FractionalIdeal.coeIdeal_absNorm]
          rfl
        _ = FractionalIdeal.absNorm (P ^ e) := hz.symm
    _ = _ := hmap.symm
private theorem cyclotomic_facNorm_nat {K : Type*} [Field K] [NumberField K]
    (J : Ideal (NumberField.RingOfIntegers K)) (hJ : J ≠ 0) :
    (∏ᶠ p : PrimeIdeal K, PrimeIdeal.norm p ^
      ((Associates.mk p.asIdeal).count (Associates.mk J).factors)) =
      Ideal.absNorm J := by
  let e : PrimeIdeal K → ℕ := fun p =>
    (Associates.mk p.asIdeal).count (Associates.mk J).factors
  have hcast := (Nat.castRingHom ℚ).toMonoidHom.map_finprod_of_preimage_one
    (fun x hx => by
      apply Nat.cast_injective (R := ℚ)
      simpa using hx) (fun p : PrimeIdeal K => PrimeIdeal.norm p ^ e p)
  have hq := cyclotomic_facNorm J hJ
  simp_rw [FractionalIdeal.count_coe K _ hJ, zpow_natCast] at hq
  change (∏ᶠ p : PrimeIdeal K, (PrimeIdeal.norm p : ℚ) ^ e p) =
    (Ideal.absNorm J : ℚ) at hq
  apply Nat.cast_injective (R := ℚ)
  change (Nat.castRingHom ℚ) (∏ᶠ p : PrimeIdeal K, PrimeIdeal.norm p ^ e p) =
    (Ideal.absNorm J : ℚ)
  exact hcast.trans (by simpa [e] using hq)
private theorem cyclotomic_facNorm_zmod {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (J : Ideal (NumberField.RingOfIntegers K)) (hJ : J ≠ 0) :
    (∏ᶠ p : PrimeIdeal K, (PrimeIdeal.norm p : ZMod n) ^
      ((Associates.mk p.asIdeal).count (Associates.mk J).factors)) =
      (Ideal.absNorm J : ZMod n) := by
  let e : PrimeIdeal K → ℕ := fun p =>
    (Associates.mk p.asIdeal).count (Associates.mk J).factors
  have hevent : ∀ᶠ p : PrimeIdeal K in Filter.cofinite, e p = 0 := by
    simpa [e, FractionalIdeal.count_coe K _ hJ] using
      (FractionalIdeal.finite_factors
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K))
  have hsupp : Function.HasFiniteMulSupport
      (fun p : PrimeIdeal K => PrimeIdeal.norm p ^ e p) := by
    apply (Filter.eventually_cofinite.mp hevent).subset
    intro p hp he
    change PrimeIdeal.norm p ^ e p ≠ 1 at hp
    rw [he, pow_zero] at hp
    exact hp rfl
  have hmap := (Nat.castRingHom (ZMod n)).toMonoidHom.map_finprod hsupp
  have hnat := cyclotomic_facNorm_nat J hJ
  change (∏ᶠ p : PrimeIdeal K, (PrimeIdeal.norm p : ZMod n) ^ e p) = _
  rw [← hnat]
  exact (by simpa [e] using hmap.symm)
private theorem cyclotomic_unit_facNorm {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (m : RayModulus K) (u : PrimeIdeal K → (ZMod n)ˣ)
    (hu : ∀ p : PrimeIdeal K, ¬p.asIdeal ∣ m.finite →
      (u p : ZMod n) = (PrimeIdeal.norm p : ZMod n))
    (J : Ideal (NumberField.RingOfIntegers K)) (hJ : J ≠ 0)
    (hcop : IsCoprime J m.finite) :
    ((∏ᶠ p : PrimeIdeal K, u p ^
      (FractionalIdeal.count K p
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) : (ZMod n)ˣ) : ZMod n) =
      (Ideal.absNorm J : ZMod n) := by
  classical
  let e : PrimeIdeal K → ℕ := fun p =>
    (Associates.mk p.asIdeal).count (Associates.mk J).factors
  have heq (p : PrimeIdeal K) :
      FractionalIdeal.count K p
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = (e p : ℤ) := by
    exact FractionalIdeal.count_coe K p hJ
  have hevent : ∀ᶠ p : PrimeIdeal K in Filter.cofinite, e p = 0 := by
    simpa [e, heq] using (FractionalIdeal.finite_factors
      (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K))
  have hsupp : Function.HasFiniteMulSupport
      (fun p : PrimeIdeal K => u p ^
        FractionalIdeal.count K p
          (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) := by
    apply (Filter.eventually_cofinite.mp hevent).subset
    intro p hp he
    change u p ^ FractionalIdeal.count K p
      (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ≠ 1 at hp
    rw [heq, he, Int.ofNat_zero, zpow_zero] at hp
    exact hp rfl
  have hmap := (Units.coeHom (ZMod n)).map_finprod hsupp
  calc
    ((∏ᶠ p : PrimeIdeal K, u p ^
      FractionalIdeal.count K p
        (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : (ZMod n)ˣ) : ZMod n) =
      ∏ᶠ p : PrimeIdeal K,
        ((u p ^ FractionalIdeal.count K p
          (J : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : (ZMod n)ˣ) : ZMod n) := hmap
    _ =
      ∏ᶠ p : PrimeIdeal K, (PrimeIdeal.norm p : ZMod n) ^ e p := by
        apply finprod_congr
        intro p
        rw [heq, zpow_natCast, Units.val_pow_eq_pow_val]
        by_cases hp : p.asIdeal ∣ m.finite
        · have hnot : ¬p.asIdeal ∣ J := by
            intro hpJ
            have htop : (⊤ : Ideal (NumberField.RingOfIntegers K)) ≤ p.asIdeal := by
              rw [← hcop.sup_eq]
              exact sup_le (Ideal.dvd_iff_le.mp hpJ) (Ideal.dvd_iff_le.mp hp)
            exact p.isPrime.ne_top (top_unique htop)
          have he0 : e p = 0 := by
            by_contra he0
            exact hnot ((Associates.count_ne_zero_iff_dvd hJ p.irreducible).mp he0)
          rw [he0, pow_zero, pow_zero]
        · rw [hu p hp]
    _ = (Ideal.absNorm J : ZMod n) := cyclotomic_facNorm_zmod n J hJ
private theorem algebraNorm_pos_of_pos_at_real {K : Type*} [Field K] [NumberField K]
    (x : K) (hx0 : x ≠ 0) (hx : ∀ σ : K →+* ℝ, 0 < σ x) :
    0 < Algebra.norm ℚ x := by
  classical
  have hcomplex (w : {w : InfinitePlace K // InfinitePlace.IsComplex w}) :
      (∏ j : Fin 2, (indexEquiv K) (Sum.inr (w, j)) x) =
        (Complex.normSq (w.1.embedding x) : ℂ) := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp [Complex.mul_conj]
  have hprod : (∏ σ : K →+* ℂ, σ x) =
      (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
          ((InfinitePlace.embedding_of_isReal w.2) x : ℂ)) *
        ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
          (Complex.normSq (w.1.embedding x) : ℂ) := by
    calc
      (∏ σ : K →+* ℂ, σ x) =
          ∏ i : index K, (indexEquiv K i) x := by
        symm
        exact Fintype.prod_equiv (indexEquiv K)
          (fun i => (indexEquiv K i) x) (fun σ => σ x) (fun _ => rfl)
      _ = (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
            (indexEquiv K (Sum.inl w)) x) *
          ∏ wj : {w : InfinitePlace K // InfinitePlace.IsComplex w} × Fin 2,
            (indexEquiv K (Sum.inr wj)) x := Fintype.prod_sum_type _
      _ = (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
            (indexEquiv K (Sum.inl w)) x) *
          ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
            ∏ j : Fin 2, (indexEquiv K (Sum.inr (w, j))) x := by
              rw [Fintype.prod_prod_type]
      _ = _ := by
        congr 1
        · apply Finset.prod_congr rfl
          intro w hw
          rw [indexEquiv_apply_isReal,
            ← InfinitePlace.embedding_of_isReal_apply]
        · apply Finset.prod_congr rfl
          intro w hw
          exact hcomplex w
  have hreal : 0 < ∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
      (InfinitePlace.embedding_of_isReal w.2) x :=
    Finset.prod_pos fun w _ => hx _
  have hcomp : 0 < ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
      Complex.normSq (w.1.embedding x) := by
    apply Finset.prod_pos
    intro w hw
    exact Complex.normSq_pos.mpr ((map_ne_zero w.1.embedding).mpr hx0)
  have hnorm := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv RingHom.equivRatAlgHom
    (fun f : K →+* ℂ => f x) (fun φ : K →ₐ[ℚ] ℂ => φ x)
    (fun f => by simp [RingHom.equivRatAlgHom_apply]), hprod] at hnorm
  have hrprod :
      (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
        ((InfinitePlace.embedding_of_isReal w.2) x : ℂ)) =
      ((∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
        (InfinitePlace.embedding_of_isReal w.2) x : ℝ) : ℂ) := by
    symm
    simpa using Complex.ofReal_prod (Finset.univ :
      Finset {w : InfinitePlace K // InfinitePlace.IsReal w})
      (fun w => (InfinitePlace.embedding_of_isReal w.2) x)
  have hcprod :
      (∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
        (Complex.normSq (w.1.embedding x) : ℂ)) =
      ((∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
        Complex.normSq (w.1.embedding x) : ℝ) : ℂ) := by
    symm
    simpa using Complex.ofReal_prod (Finset.univ :
      Finset {w : InfinitePlace K // InfinitePlace.IsComplex w})
      (fun w => Complex.normSq (w.1.embedding x))
  have hre := congrArg Complex.re hnorm
  have hre' : ((Algebra.norm ℚ x : ℚ) : ℝ) =
      (∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
        (InfinitePlace.embedding_of_isReal w.2) x) *
      ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
        Complex.normSq (w.1.embedding x) := by
    calc
      ((Algebra.norm ℚ x : ℚ) : ℝ) =
          ((algebraMap ℚ ℂ (Algebra.norm ℚ x)).re) := by simp
      _ = ((∏ w : {w : InfinitePlace K // InfinitePlace.IsReal w},
            ((InfinitePlace.embedding_of_isReal w.2) x : ℂ)) *
          ∏ w : {w : InfinitePlace K // InfinitePlace.IsComplex w},
            (Complex.normSq (w.1.embedding x) : ℂ)).re := hre
      _ = _ := by rw [hrprod, hcprod]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  apply (Rat.cast_pos (K := ℝ)).mp
  rw [hre']
  exact mul_pos hreal hcomp
private theorem algebraNorm_modEq {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (β γ : NumberField.RingOfIntegers K)
    (h : β - γ ∈ Ideal.span
      {algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ)}) :
    (Algebra.norm ℤ β : ZMod n) = (Algebra.norm ℤ γ : ZMod n) := by
  classical
  let b := Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers K)
  let L := Algebra.leftMulMatrix b
  let f : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  have hβ : β = γ + a * algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ) := by
    calc
      β = γ + (β - γ) := by abel
      _ = _ := by rw [← ha]
  have hnmat : (L (algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ))).map f = 0 := by
    rw [show L (algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ)) =
      algebraMap ℤ (Matrix (Module.Free.ChooseBasisIndex ℤ
        (NumberField.RingOfIntegers K))
        (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) ℤ) (n : ℤ) by
          exact L.commutes (n : ℤ)]
    ext i j
    change f ((algebraMap ℤ (Matrix _ _ ℤ)) (n : ℤ) i j) = 0
    rw [Matrix.algebraMap_matrix_apply]
    by_cases hij : i = j <;> simp [hij, f]
  have hmat : (L β).map f = (L γ).map f := by
    rw [hβ, map_add, map_mul, Matrix.map_add f (map_add f),
      Matrix.map_mul, hnmat, mul_zero, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  change f (L β).det = f (L γ).det
  rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply, hmat]

private theorem absNorm_span_modEq {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (α : Kˣ) (β γ : NumberField.RingOfIntegers K)
    (hγ : γ ≠ 0)
    (hfrac : algebraMap (NumberField.RingOfIntegers K) K β /
      algebraMap (NumberField.RingOfIntegers K) K γ = (α : K))
    (hpos : ∀ σ : K →+* ℝ, 0 < σ α)
    (hcong : β - γ ∈ Ideal.span
      {algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ)}) :
    (Ideal.absNorm (Ideal.span {β}) : ZMod n) =
      (Ideal.absNorm (Ideal.span {γ}) : ZMod n) := by
  have hβ : β ≠ 0 := by
    intro hβ
    subst β
    simp only [map_zero, zero_div] at hfrac
    exact α.ne_zero hfrac.symm
  have hnormα : 0 < Algebra.norm ℚ (α : K) := algebraNorm_pos_of_pos_at_real (α : K) α.ne_zero hpos
  have hmul : algebraMap (NumberField.RingOfIntegers K) K β =
      (α : K) * algebraMap (NumberField.RingOfIntegers K) K γ := by
    exact (div_eq_iff ((map_ne_zero_iff
      (algebraMap (NumberField.RingOfIntegers K) K)
      (FaithfulSMul.algebraMap_injective _ _)).2 hγ)).mp hfrac
  have hnormmul : Algebra.norm ℚ
      (algebraMap (NumberField.RingOfIntegers K) K β) =
      Algebra.norm ℚ (α : K) * Algebra.norm ℚ
        (algebraMap (NumberField.RingOfIntegers K) K γ) := by
    rw [hmul, map_mul]
  have hnormγ0 : Algebra.norm ℚ
      (algebraMap (NumberField.RingOfIntegers K) K γ) ≠ 0 := by
    rw [Algebra.norm_ne_zero_iff]
    exact (map_ne_zero_iff
      (algebraMap (NumberField.RingOfIntegers K) K)
      (FaithfulSMul.algebraMap_injective _ _)).2 hγ
  have hprodQ : 0 < Algebra.norm ℚ
      (algebraMap (NumberField.RingOfIntegers K) K β) *
      Algebra.norm ℚ (algebraMap (NumberField.RingOfIntegers K) K γ) := by
    rw [hnormmul, mul_assoc]
    exact mul_pos hnormα (mul_self_pos.mpr hnormγ0)
  have hprodQ' : 0 < (Algebra.norm ℤ β : ℚ) *
      (Algebra.norm ℤ γ : ℚ) := by
    simpa only [Algebra.coe_norm_int] using hprodQ
  have hprodZ : 0 < Algebra.norm ℤ β * Algebra.norm ℤ γ := by
    exact_mod_cast hprodQ'
  have hnormcong : (Algebra.norm ℤ β : ZMod n) =
      (Algebra.norm ℤ γ : ZMod n) := algebraNorm_modEq n β γ hcong
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
  rcases (mul_pos_iff.mp hprodZ) with hpp | hnn
  · have hβabs : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β :=
      Int.natAbs_of_nonneg hpp.1.le
    have hγabs : ((Algebra.norm ℤ γ).natAbs : ℤ) = Algebra.norm ℤ γ :=
      Int.natAbs_of_nonneg hpp.2.le
    have hβcast := congrArg (fun z : ℤ => (z : ZMod n)) hβabs
    have hγcast := congrArg (fun z : ℤ => (z : ZMod n)) hγabs
    simp only [Int.cast_natCast] at hβcast hγcast
    rw [hβcast, hγcast, hnormcong]
  · have hβabs : ((Algebra.norm ℤ β).natAbs : ℤ) = -Algebra.norm ℤ β := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    have hγabs : ((Algebra.norm ℤ γ).natAbs : ℤ) = -Algebra.norm ℤ γ := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    have hβcast := congrArg (fun z : ℤ => (z : ZMod n)) hβabs
    have hγcast := congrArg (fun z : ℤ => (z : ZMod n)) hγabs
    simp only [Int.cast_natCast, Int.cast_neg] at hβcast hγcast
    rw [hβcast, hγcast, hnormcong]
open scoped BigOperators nonZeroDivisors
private noncomputable def cyclotomicPrimeAbove
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] (p : PrimeIdeal K) : PrimeIdeal F := by
  let q := Classical.choice (p.asIdeal.nonempty_primesOver
    (S := NumberField.RingOfIntegers F))
  refine ⟨q.1, q.2.1, ?_⟩
  intro hq
  have hover := q.2.2
  letI : q.1.LiesOver p.asIdeal := hover
  apply p.ne_bot
  rw [hover.over]
  simpa [hq]
private theorem cyclotomicPrimeAbove_liesOver
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] (p : PrimeIdeal K) :
    (cyclotomicPrimeAbove (F := F) p).asIdeal.LiesOver p.asIdeal := by
  dsimp [cyclotomicPrimeAbove]
  generalize_proofs h
  exact (Classical.choice (p.asIdeal.nonempty_primesOver
    (S := NumberField.RingOfIntegers F))).2.2

private noncomputable def cyclotomicPrimeFrob
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p : PrimeIdeal K) : Gal(F/K) :=
  arithFrobeniusAt (K := K) (L := F) (cyclotomicPrimeAbove (F := F) p)

private theorem cyclotomicPrimeUnit_eq_norm
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (n : ℕ) [NeZero n] (m : RayModulus K) [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    ((IsCyclotomicExtension.zeta_spec n K F).autToPow K (cyclotomicPrimeFrob (F := F) p) : ZMod n) =
      (PrimeIdeal.norm p : ZMod n) := by
  let P := cyclotomicPrimeAbove (F := F) p
  have hPp : P.asIdeal.LiesOver p.asIdeal := cyclotomicPrimeAbove_liesOver p
  have hnP : algebraMap ℤ (NumberField.RingOfIntegers F) (n : ℤ) ∉ P.asIdeal := by
    intro hnmem
    have hnunder : algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ) ∈
        P.asIdeal.under (NumberField.RingOfIntegers K) := by
      rw [Ideal.mem_under]
      simpa using hnmem
    have hnp : algebraMap ℤ (NumberField.RingOfIntegers K) (n : ℤ) ∈ p.asIdeal := by
      rw [hPp.over]
      exact hnunder
    apply hp
    exact dvd_trans (Ideal.dvd_iff_le.mpr
      ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hnp)) hmod.1
  let ζ := IsCyclotomicExtension.zeta n K F
  have hζ := IsCyclotomicExtension.zeta_spec n K F
  let ζI : NumberField.RingOfIntegers F := ⟨ζ, by
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (by
        intro hn0
        apply hnP
        simp [hn0])
    · simpa [Polynomial.eval₂_sub, Polynomial.eval₂_pow] using
        sub_eq_zero.mpr hζ.pow_eq_one⟩
  have hζI : ζI ^ n = 1 := by
    apply NumberField.RingOfIntegers.coe_injective (K := F)
    exact hζ.pow_eq_one
  have hmain := (IsArithFrobAt.arithFrobAt
    (NumberField.RingOfIntegers K) (Gal(F/K)) P.asIdeal).apply_of_pow_eq_one
      (m := n) hζI (by simpa [ζI] using hnP)
  have hcard : Nat.card (NumberField.RingOfIntegers K ⧸
      P.asIdeal.under (NumberField.RingOfIntegers K)) = PrimeIdeal.norm p := by
    rw [← hPp.over]
    rfl
  rw [hcard] at hmain
  have hact : cyclotomicPrimeFrob (F := F) p ζ = ζ ^ PrimeIdeal.norm p := by
    change algebraMap (NumberField.RingOfIntegers F) F
      ((arithFrobAt (NumberField.RingOfIntegers K) (Gal(F/K)) P.asIdeal) • ζI) = _
    change algebraMap (NumberField.RingOfIntegers F) F
      ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers F)
        (arithFrobAt (NumberField.RingOfIntegers K) (Gal(F/K)) P.asIdeal)) ζI) = _
    rw [hmain]
    simp only [map_pow]
    rfl
  have hspec := hζ.autToPow_spec K (cyclotomicPrimeFrob (F := F) p)
  change ζ ^ (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n).val) =
    cyclotomicPrimeFrob (F := F) p ζ at hspec
  have hpows : ζ ^ (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n).val) =
      ζ ^ PrimeIdeal.norm p := hspec.trans hact
  change (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n)) =
    (PrimeIdeal.norm p : ZMod n)
  rw [← ZMod.natCast_zmod_val
    (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n))]
  apply (ZMod.natCast_eq_natCast_iff _ _ n).2
  have hpowsU : hζ.toRootsOfUnity ^
      (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n).val) =
      hζ.toRootsOfUnity ^ PrimeIdeal.norm p := by
    apply rootsOfUnity.coe_injective
    simpa only [rootsOfUnity.coe_pow, hζ.val_toRootsOfUnity_coe] using hpows
  have hm := (pow_eq_pow_iff_modEq
    (x := hζ.toRootsOfUnity)
    (n := (((hζ.autToPow K (cyclotomicPrimeFrob (F := F) p) : (ZMod n)ˣ) : ZMod n).val))
    (m := PrimeIdeal.norm p)).mp hpowsU
  rw [← Subgroup.orderOf_coe, ← orderOf_units, hζ.val_toRootsOfUnity_coe,
    ← hζ.eq_orderOf] at hm
  exact hm
private noncomputable def cyclotomicPrimeFrobAway
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (m : RayModulus K) (p : PrimeIdeal K) : Gal(F/K) := by
  classical
  exact if p.asIdeal ∣ m.finite then 1 else cyclotomicPrimeFrob (F := F) p

private noncomputable def cyclotomicFreeFrobenius
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (n : ℕ) [IsCyclotomicExtension {n} K F]
    (m : RayModulus K) : FractionalIdealGroup (K := K) →* Gal(F/K) := by
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  exact cyclotomicFreeIdealMap (cyclotomicPrimeFrobAway (F := F) m)

private theorem cyclotomic_aut_freeFrobenius
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K F]
    (m : RayModulus K) (X : FractionalIdealGroup (K := K)) :
    (IsCyclotomicExtension.zeta_spec n K F).autToPow K
      (cyclotomicFreeFrobenius (F := F) n m X) =
      ∏ᶠ p : PrimeIdeal K,
        ((IsCyclotomicExtension.zeta_spec n K F).autToPow K
          (cyclotomicPrimeFrobAway (F := F) m p)) ^
        FractionalIdeal.count K p
          (X : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  let hζ := IsCyclotomicExtension.zeta_spec n K F
  calc
    hζ.autToPow K (cyclotomicFreeFrobenius (F := F) n m X) =
        (cyclotomicIdealFactors X).prod fun p e =>
          hζ.autToPow K ((cyclotomicPrimeFrobAway (F := F) m p) ^ e) := by
      exact map_finsuppProd (hζ.autToPow K) (cyclotomicIdealFactors X)
        (fun p e => (cyclotomicPrimeFrobAway (F := F) m p) ^ e)
    _ = (cyclotomicIdealFactors X).prod fun p e =>
          (hζ.autToPow K (cyclotomicPrimeFrobAway (F := F) m p)) ^ e := by
      apply Finset.prod_congr rfl
      intro p hp
      exact map_zpow (hζ.autToPow K) _ _
    _ = _ := cyclotomicFreeIdealMap_eq_finprod
      (fun p => hζ.autToPow K (cyclotomicPrimeFrobAway (F := F) m p)) X

private theorem cyclotomicFreeFrobenius_kills
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (n : ℕ) (m : RayModulus K) [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m) :
    RayPrincipalSubgroup m ≤
      ((cyclotomicFreeFrobenius (F := F) n m).comp (RayIdealGroup m).subtype).ker := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  let hζ := IsCyclotomicExtension.zeta_spec n K F
  let prime : PrimeIdeal K → Gal(F/K) := cyclotomicPrimeFrobAway (F := F) m
  let u : PrimeIdeal K → (ZMod n)ˣ := fun p => hζ.autToPow K (prime p)
  have hu : ∀ p : PrimeIdeal K, ¬p.asIdeal ∣ m.finite →
      (u p : ZMod n) = (PrimeIdeal.norm p : ZMod n) := by
    intro p hp
    dsimp [u, prime, cyclotomicPrimeFrobAway]
    rw [if_neg hp]
    exact cyclotomicPrimeUnit_eq_norm n m hn hmod p hp
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro I ⟨α, hα, hI⟩
  rcases hα.1 with ⟨β, γ, hγ, hfrac, hβcop, hγcop, hcong⟩
  have hβ : β ≠ 0 := by
    intro hβ
    subst β
    simp only [map_zero, zero_div] at hfrac
    exact α.ne_zero hfrac.symm
  let B : FractionalIdealGroup (K := K) :=
    Units.mk0 (Ideal.span {β} : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa))
  let C : FractionalIdealGroup (K := K) :=
    Units.mk0 (Ideal.span {γ} : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa))
  have hIC : I.1 = B * C⁻¹ := by
    apply Units.ext
    change (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      (B : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) *
      ((C⁻¹ : FractionalIdealGroup (K := K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
    rw [hI, Units.val_inv_eq_inv_val]
    change FractionalIdeal.spanSingleton
      (NumberField.RingOfIntegers K)⁰ (α : K) =
      (Ideal.span {β} : FractionalIdeal
        (NumberField.RingOfIntegers K)⁰ K) *
      (Ideal.span {γ} : FractionalIdeal
        (NumberField.RingOfIntegers K)⁰ K)⁻¹
    simp only [FractionalIdeal.coeIdeal_span_singleton]
    rw [FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    rw [← hfrac]
    simp only [div_eq_mul_inv]
  have hBnorm := cyclotomic_unit_facNorm n m u hu (Ideal.span {β})
    (by simpa using hβ) hβcop
  have hCnorm := cyclotomic_unit_facNorm n m u hu (Ideal.span {γ})
    (by simpa using hγ) hγcop
  have hBaut : ((hζ.autToPow K (cyclotomicFreeFrobenius (F := F) n m B) : (ZMod n)ˣ) :
      ZMod n) = (Ideal.absNorm (Ideal.span {β}) : ZMod n) := by
    rw [cyclotomic_aut_freeFrobenius n m B]
    exact hBnorm
  have hCaut : ((hζ.autToPow K (cyclotomicFreeFrobenius (F := F) n m C) : (ZMod n)ˣ) :
      ZMod n) = (Ideal.absNorm (Ideal.span {γ}) : ZMod n) := by
    rw [cyclotomic_aut_freeFrobenius n m C]
    exact hCnorm
  have habs : (Ideal.absNorm (Ideal.span {β}) : ZMod n) =
      (Ideal.absNorm (Ideal.span {γ}) : ZMod n) :=
    absNorm_span_modEq n α β γ hγ hfrac
      (fun σ => hα.2 σ (hmod.2 σ))
      (Ideal.dvd_iff_le.mp hmod.1 hcong)
  have hBCaut : hζ.autToPow K (cyclotomicFreeFrobenius (F := F) n m B) =
      hζ.autToPow K (cyclotomicFreeFrobenius (F := F) n m C) := by
    apply Units.ext
    exact hBaut.trans (habs.trans hCaut.symm)
  have hBC : cyclotomicFreeFrobenius (F := F) n m B = cyclotomicFreeFrobenius (F := F) n m C :=
    hζ.autToPow_injective K hBCaut
  change cyclotomicFreeFrobenius (F := F) n m I.1 = 1
  rw [hIC, map_mul, map_inv, hBC, mul_inv_cancel]


private theorem cyclotomicRestrictPrimeFrob
    {K M F : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Field F] [NumberField F]
    [Algebra K M] [Algebra K F] [Algebra M F] [IsScalarTower K M F]
    [FiniteDimensional K M] [FiniteDimensional K F]
    [IsGalois K M] [IsGalois K F] [IsMulCommutative (Gal(M/K))]
    (m : RayModulus K) (hram : RamificationSupported (M := M) m)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite)
    (P : PrimeIdeal F) (hPp : P.asIdeal.LiesOver p.asIdeal)
    (Q : PrimeIdeal M) (hQp : Q.asIdeal.LiesOver p.asIdeal) :
    AlgEquiv.restrictNormalHom M (arithFrobeniusAt (K := K) (L := F) P) =
      arithFrobeniusAt (K := K) (L := M) Q := by
  let q : PrimeIdeal M :=
    ⟨P.asIdeal.under (NumberField.RingOfIntegers M), inferInstance, by
      intro hq
      apply p.ne_bot
      rw [hPp.over, ← Ideal.under_under
        (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers M) P.asIdeal, hq]
      simp⟩
  have hPq : P.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hqp : q.asIdeal.LiesOver p.asIdeal := by
    constructor
    change p.asIdeal = (P.asIdeal.under (NumberField.RingOfIntegers M)).under
      (NumberField.RingOfIntegers K)
    rw [Ideal.under_under, hPp.over]
  have hunrq : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) q.asIdeal := by
    by_contra hq
    apply hp
    have hd := hram q hq
    simpa only [← hqp.over] using hd
  let s := arithFrobeniusAt (K := K) (L := F) P
  let r : Gal(M/K) := AlgEquiv.restrictNormalHom M s
  have hr : IsArithFrobAt (NumberField.RingOfIntegers K) r q.asIdeal := by
    intro x
    rw [hPq.over, Ideal.mem_under, Ideal.under_under]
    have hs := (IsArithFrobAt.arithFrobAt
      (NumberField.RingOfIntegers K) (Gal(F/K)) P.asIdeal)
      (algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers F) x)
    have hact : algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers F)
        ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers M) r) x) =
        (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers F) s)
          (algebraMap (NumberField.RingOfIntegers M)
            (NumberField.RingOfIntegers F) x) := by
      apply NumberField.RingOfIntegers.coe_injective (K := F)
      change algebraMap M F
          (r (algebraMap (NumberField.RingOfIntegers M) M x)) =
        s (algebraMap M F
          (algebraMap (NumberField.RingOfIntegers M) M x))
      exact AlgEquiv.restrictNormal_commutes s M
        (algebraMap (NumberField.RingOfIntegers M) M x)
    change (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers F) s)
        (algebraMap (NumberField.RingOfIntegers M)
          (NumberField.RingOfIntegers F) x) -
      (algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers F) x) ^
        Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) ∈ P.asIdeal at hs
    simpa only [map_sub, map_pow, hact] using hs
  letI : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) q.asIdeal := hunrq
  have heq := hr.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
      (Gal(M/K)) q.asIdeal) q.asIdeal.primeCompl_le_nonZeroDivisors
  have hrq : r = arithFrobeniusAt (K := K) (L := M) q := by
    have hfield : r.toRingEquiv.toRingHom =
        (arithFrobeniusAt (K := K) (L := M) q).toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers M)
      intro x
      exact congrArg Subtype.val (DFunLike.congr_fun heq x)
    ext x
    exact DFunLike.congr_fun hfield x
  change r = _
  rw [hrq]
  apply isConj_iff_eq.mp
  apply isConj_arithFrobAt
  rw [← hqp.over, ← hQp.over]

/-- Blueprint Lemma 6.1, proposed declaration `cyclotomicIdealMap`: the
multiplicative Frobenius map on ideals descends through the ray class quotient.
No surjectivity is built into this definition. -/
noncomputable def cyclotomicIdealMap
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m) :
    RayClassGroup m →* Gal(M/K) := by
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let idealToF : RayIdealGroup m →* Gal(F/K) :=
    (cyclotomicFreeFrobenius (F := F) n m).comp (RayIdealGroup m).subtype
  let idealToM : RayIdealGroup m →* Gal(M/K) :=
    (AlgEquiv.restrictNormalHom M).comp idealToF
  have hkF : RayPrincipalSubgroup m ≤ idealToF.ker :=
    cyclotomicFreeFrobenius_kills (F := F) n m hn hmod
  have hkM : RayPrincipalSubgroup m ≤ idealToM.ker := by
    intro I hI
    have hIF : I ∈ idealToF.ker := hkF hI
    rw [MonoidHom.mem_ker] at hIF ⊢
    change AlgEquiv.restrictNormalHom M (idealToF I) = 1
    rw [hIF, map_one]
  exact QuotientGroup.lift (RayPrincipalSubgroup m) idealToM hkM

/-- Blueprint Lemma 6.1 and equation (9) (`cyclotomicIdealMap_on_prime`): on a
prime away from the modulus, the elementary ideal map is arithmetic Frobenius
in `M/K`. -/
theorem cyclotomicIdealMap_on_prime
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite)
    (c : RayClassGroup m)
    (hc : RayClassGroup.IsClassOfIdeal m p.asIdeal c)
    (Q : PrimeIdeal M) (hQp : Q.asIdeal.LiesOver p.asIdeal) :
    cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram c =
      arithFrobeniusAt (K := K) (L := M) Q := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  rcases hc with ⟨I, hI, rfl⟩
  have hfac : cyclotomicIdealFactors I.1 = Finsupp.single p 1 := by
    ext q
    rw [cyclotomicIdealFactors_apply, Finsupp.single_apply, hI,
      FractionalIdeal.count_maximal K q p]
  change AlgEquiv.restrictNormalHom M
    (cyclotomicFreeFrobenius (F := F) n m I.1) = _
  change AlgEquiv.restrictNormalHom M
    ((cyclotomicIdealFactors I.1).prod fun q e =>
      cyclotomicPrimeFrobAway (F := F) m q ^ e) = _
  rw [hfac, Finsupp.prod_single_index (by simp), zpow_one]
  rw [show cyclotomicPrimeFrobAway (F := F) m p =
    cyclotomicPrimeFrob (F := F) p by
      simp [cyclotomicPrimeFrobAway, hp]]
  exact cyclotomicRestrictPrimeFrob m hram p hp
    (cyclotomicPrimeAbove (F := F) p)
    (cyclotomicPrimeAbove_liesOver p) Q hQp

private noncomputable def cyclotomicPullbackCharacter {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G)
    (χ : UnitCharacter G) : RayClassCharacter m :=
  MulChar.ofUnitHom ((χ.comp ν).comp (Units.coeHom (RayClassGroup m)))

private theorem cyclotomicPullbackCharacter_apply {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G)
    (χ : UnitCharacter G) (c : RayClassGroup m) :
    cyclotomicPullbackCharacter m ν χ c = (χ (ν c) : ℂ) := by
  let u : (RayClassGroup m)ˣ := (Group.isUnit c).unit
  rw [← (Group.isUnit c).unit_spec]
  rw [cyclotomicPullbackCharacter, MulChar.ofUnitHom_coe]
  rfl

private theorem cyclotomicWeberAlong_eq_pullback {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G)
    (χ : UnitCharacter G) (s : ℂ) :
    weberLSeriesAlong m ν χ s = weberLSeries m (cyclotomicPullbackCharacter m ν χ) s := by
  unfold weberLSeriesAlong weberLSeries
  apply tsum_congr
  intro c
  rw [cyclotomicPullbackCharacter_apply]

private theorem cyclotomicPullbackCharacter_ne_one {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G)
    (hν : Function.Surjective ν) (χ : UnitCharacter G) (hχ : χ ≠ 1) :
    cyclotomicPullbackCharacter m ν χ ≠ 1 := by
  intro h
  apply hχ
  apply MonoidHom.ext
  intro g
  obtain ⟨c, rfl⟩ := hν g
  have hc := DFunLike.congr_fun h c
  change cyclotomicPullbackCharacter m ν χ c = (1 : RayClassCharacter m) c at hc
  rw [cyclotomicPullbackCharacter_apply, MulChar.one_apply (Group.isUnit c)] at hc
  apply Units.ext
  simpa using hc

private theorem cyclotomicWeberAlongOneContinuation {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G) :
    ∃ W : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → W s = weberLSeriesAlong m ν 1 s) ∧
      Tendsto (fun s : ℂ => (s - 1) * W s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hcont⟩ := rayClassPartialZeta_continuation m
  let F : RayClassGroup m → ℂ → ℂ := fun c => Classical.choose (hcont c)
  have hFeq (c : RayClassGroup m) (s : ℂ) (hs : 1 < s.re) :
      F c s = rayClassPartialZeta m c s :=
    (Classical.choose_spec (hcont c)).2.1 s hs
  have hFres (c : RayClassGroup m) :
      Tendsto (fun s : ℂ => (s - 1) * F c s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (ρ : ℂ)) :=
    (Classical.choose_spec (hcont c)).2.2.2
  let W : ℂ → ℂ := fun s => ∑ c : RayClassGroup m, F c s
  let R : ℂ := Fintype.card (RayClassGroup m) * ρ
  refine ⟨W, R, ?_, ?_, ?_⟩
  · dsimp [R]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
      (Complex.ofReal_ne_zero.mpr hρ.ne')
  · intro s hs
    dsimp [W]
    rw [weberLSeriesAlong, tsum_fintype]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hFeq c s hs]
    simp
  · have hsum := tendsto_finset_sum Finset.univ (fun c _ => hFres c)
    convert hsum using 1
    · funext s
      dsimp [W]
      rw [Finset.mul_sum]
    · simp [R]

private theorem cyclotomicWeberAlongNontrivialContinuation {K G : Type*} [Field K] [NumberField K]
    [CommGroup G] (m : RayModulus K) (ν : RayClassGroup m →* G)
    (hν : Function.Surjective ν) (χ : UnitCharacter G) (hχ : χ ≠ 1) :
    ∃ W : ℂ → ℂ,
      AnalyticOnNhd ℂ W {s : ℂ |
        1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} ∧
      ∀ s : ℂ, 1 < s.re → W s = weberLSeriesAlong m ν χ s := by
  have hcyclotomicPullbackCharacter := cyclotomicPullbackCharacter_ne_one m ν hν χ hχ
  obtain ⟨W, hWan, hWeq⟩ :=
    weberLSeries_analytic_of_ne_one m (cyclotomicPullbackCharacter m ν χ) hcyclotomicPullbackCharacter
  refine ⟨W, hWan, fun s hs => ?_⟩
  rw [hWeq s hs, ← cyclotomicWeberAlong_eq_pullback]


private theorem cyclotomicClassOfIdeal_unique {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) (a : Ideal (NumberField.RingOfIntegers K))
    {c d : RayClassGroup m} (hc : RayClassGroup.IsClassOfIdeal m a c)
    (hd : RayClassGroup.IsClassOfIdeal m a d) : c = d := by
  obtain ⟨I, hIa, hIc⟩ := hc
  obtain ⟨J, hJa, hJd⟩ := hd
  have hIJ : I = J := by
    apply Subtype.ext
    apply Units.ext
    exact hIa.trans hJa.symm
  rw [← hIc, ← hJd, hIJ]

private noncomputable def cyclotomicPrimeRayIdeal {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    RayIdealGroup m := by
  classical
  let u : FractionalIdealGroup (K := K) :=
    Units.mk0 (p.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)
  refine ⟨u, ?_⟩
  intro q hq
  change FractionalIdeal.count K q
    (p.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = 0
  rw [FractionalIdeal.count_maximal]
  rw [if_neg]
  intro h
  apply hp
  simpa [h] using hq

private theorem cyclotomicPrimeRayIdeal_val {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    (((cyclotomicPrimeRayIdeal m p hp).1 : FractionalIdealGroup (K := K)) :
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      (p.asIdeal : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  simp [cyclotomicPrimeRayIdeal]

private theorem cyclotomicTrivialPrimeCharacterValue {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    rayClassCharacterValue m 1 p.asIdeal = 1 := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  let I := cyclotomicPrimeRayIdeal m p hp
  let c := RayClassGroup.mk m I
  have hc : RayClassGroup.IsClassOfIdeal m p.asIdeal c :=
    ⟨I, cyclotomicPrimeRayIdeal_val m p hp, rfl⟩
  rw [rayClassCharacterValue, tsum_fintype, Finset.sum_eq_single c]
  · rw [if_pos hc, MulChar.one_apply (Group.isUnit c)]
  · intro d hd hdc
    rw [if_neg]
    intro had
    exact hdc (cyclotomicClassOfIdeal_unique m p.asIdeal had hc)
  · simp

private noncomputable def cyclotomicLiftedModulus
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : RayModulus K) : RayModulus M where
  finite := Ideal.map (algebraMap (NumberField.RingOfIntegers K)
    (NumberField.RingOfIntegers M)) m.finite
  finite_ne := by
    intro h
    apply m.finite_ne
    apply le_antisymm _ bot_le
    intro x hx
    have hfx := Ideal.mem_map_of_mem
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers M)) hx
    rw [h] at hfx
    change (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers M)) x = 0 at hfx
    change x = 0
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    apply (algebraMap K M).injective
    have hxM := congrArg
      (algebraMap (NumberField.RingOfIntegers M) M) hfx
    rw [← IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers M) M,
      map_zero] at hxM
    rw [← IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers K) K M, map_zero]
    simpa using hxM
  infinite := ∅

private theorem cyclotomicLiftedModulus_dvd_iff
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : RayModulus K) (Q : PrimeIdeal M) :
    Q.asIdeal ∣ (cyclotomicLiftedModulus (M := M) m).finite ↔
      Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite := by
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  exact Ideal.map_le_iff_le_comap

private theorem cyclotomicIncompleteZeta_eq_weber
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : RayModulus K) (s : ℂ) (hs : 1 < s.re) :
    incompleteExtensionZeta (M := M) m s =
      weberLSeries (cyclotomicLiftedModulus (M := M) m) 1 s := by
  rw [weberLSeries_eq_eulerProduct _ _ s hs]
  unfold incompleteExtensionZeta weberLEulerProduct
  apply tprod_congr
  intro Q
  rw [cyclotomicLiftedModulus_dvd_iff]
  by_cases hQ : Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite
  · simp [hQ]
  · rw [if_neg hQ, if_neg hQ,
      cyclotomicTrivialPrimeCharacterValue _ Q (fun h => hQ ((cyclotomicLiftedModulus_dvd_iff m Q).mp h)),
      one_mul]

private theorem cyclotomicWeberOneContinuation {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) :
    ∃ W : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → W s = weberLSeries m 1 s) ∧
      Tendsto (fun s : ℂ => (s - 1) * W s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hcont⟩ := rayClassPartialZeta_continuation m
  let F : RayClassGroup m → ℂ → ℂ := fun c => Classical.choose (hcont c)
  have hFeq (c : RayClassGroup m) (s : ℂ) (hs : 1 < s.re) :
      F c s = rayClassPartialZeta m c s :=
    (Classical.choose_spec (hcont c)).2.1 s hs
  have hFres (c : RayClassGroup m) :
      Tendsto (fun s : ℂ => (s - 1) * F c s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (ρ : ℂ)) :=
    (Classical.choose_spec (hcont c)).2.2.2
  let W : ℂ → ℂ := fun s => ∑ c : RayClassGroup m, F c s
  let R : ℂ := Fintype.card (RayClassGroup m) * ρ
  refine ⟨W, R, ?_, ?_, ?_⟩
  · dsimp [R]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Complex.ofReal_ne_zero.mpr hρ.ne')
  · intro s hs
    dsimp [W]
    rw [weberLSeries, tsum_fintype]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hFeq c s hs, MulChar.one_apply (Group.isUnit c), one_mul]
  · have hsum := tendsto_finset_sum Finset.univ (fun c _ => hFres c)
    convert hsum using 1
    · funext s
      dsimp [W]
      rw [Finset.mul_sum]
    · simp [R]

private theorem cyclotomicIncompleteZetaContinuation
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : RayModulus K) :
    ∃ Z : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → Z s = incompleteExtensionZeta (M := M) m s) ∧
      Tendsto (fun s : ℂ => (s - 1) * Z s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  obtain ⟨Z, ρ, hρ, hZeq, hZres⟩ :=
    cyclotomicWeberOneContinuation (cyclotomicLiftedModulus (M := M) m)
  refine ⟨Z, ρ, hρ, ?_, hZres⟩
  intro s hs
  rw [hZeq s hs, cyclotomicIncompleteZeta_eq_weber m s hs]




private noncomputable def cyclotomicCharEvalEquivRoots
    {G : Type*} [Finite G] [CommGroup G] (a : G) :
    UnitCharacter (Subgroup.zpowers a) ≃ rootsOfUnity (orderOf a) ℂ := by
  classical
  let B := Subgroup.zpowers a
  letI : NeZero (orderOf a) := ⟨(orderOf_pos a).ne'⟩
  letI := Fintype.ofFinite (UnitCharacter B)
  letI := Fintype.ofFinite (rootsOfUnity (orderOf a) ℂ)
  let b : B := ⟨a, Subgroup.mem_zpowers a⟩
  let ev : UnitCharacter B → rootsOfUnity (orderOf a) ℂ := fun ψ =>
    ⟨ψ b, by
      change (ψ b) ^ orderOf a = 1
      have hbpow : b ^ orderOf a = 1 := by
        apply Subtype.ext
        exact pow_orderOf_eq_one a
      simpa using congrArg ψ hbpow⟩
  have hev : Function.Injective ev := by
    intro ψ φ h
    apply MonoidHom.ext
    intro x
    apply Units.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have hb : ψ b = φ b := congrArg Subtype.val h
    have hx : x = b ^ k := by
      apply Subtype.ext
      exact hk.symm
    rw [hx, map_zpow, map_zpow, hb]
  exact Equiv.ofBijective ev ((Fintype.bijective_iff_injective_and_card ev).mpr
    ⟨hev, by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity,
        Nat.card_zpowers]
      exact (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (orderOf a)).symm⟩)


private theorem cyclotomic_prod_rootsOfUnity_one_sub (d : ℕ) [NeZero d] [Fintype (rootsOfUnity d ℂ)] (z : ℂ) :
    (∏ r : rootsOfUnity d ℂ, (1 - ((r : ℂˣ) : ℂ) * z)) = 1 - z ^ d := by
  classical
  let ζ : ℂ := (HasEnoughRootsOfUnity.exists_primitiveRoot ℂ d).choose
  have hζ : IsPrimitiveRoot ζ d :=
    (HasEnoughRootsOfUnity.exists_primitiveRoot ℂ d).choose_spec
  let ζu : ℂˣ := (hζ.isUnit (NeZero.ne d)).unit
  have hζu : IsPrimitiveRoot ζu d := hζ.isUnit_unit (NeZero.ne d)
  let f : Fin d → rootsOfUnity d ℂ := fun i =>
    ⟨ζu ^ (i : ℕ), by
      rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      apply hζu.pow_inj i.isLt j.isLt
      exact congrArg Subtype.val hij
    · intro r
      obtain ⟨i, hi, hir⟩ := hζu.eq_pow_of_mem_rootsOfUnity r.2
      exact ⟨⟨i, hi⟩, Subtype.ext hir⟩
  let e : Fin d ≃ rootsOfUnity d ℂ := Equiv.ofBijective f hf
  rw [← e.prod_comp]
  change (∏ i : Fin d, (1 - ζ ^ (i : ℕ) * z)) = 1 - z ^ d
  by_cases hz : z = 0
  · subst z
    simp [zero_pow (NeZero.ne d)]
  have hpoly := congrArg (Polynomial.eval z⁻¹)
    (X_pow_sub_C_eq_prod hζ (NeZero.pos d) (one_pow d))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod] at hpoly
  have hpoly' : (z ^ d)⁻¹ - 1 =
      ∏ i : Fin d, (z⁻¹ - ζ ^ (i : ℕ)) := by
    calc
      (z ^ d)⁻¹ - 1 = z⁻¹ ^ d - 1 := by rw [inv_pow]
      _ = ∏ i ∈ Finset.range d, (z⁻¹ - ζ ^ i) := by simpa using hpoly
      _ = ∏ i : Fin d, (z⁻¹ - ζ ^ (i : ℕ)) :=
        (Fin.prod_univ_eq_prod_range (fun i => z⁻¹ - ζ ^ i) d).symm
  calc
    (∏ i : Fin d, (1 - ζ ^ (i : ℕ) * z)) =
        ∏ i : Fin d, (z * (z⁻¹ - ζ ^ (i : ℕ))) := by
      apply Finset.prod_congr rfl
      intro i hi
      field_simp
    _ = (∏ _i : Fin d, z) * ∏ i : Fin d, (z⁻¹ - ζ ^ (i : ℕ)) := by
      exact Finset.prod_mul_distrib
    _ = z ^ d * ((z ^ d)⁻¹ - 1) := by
      rw [hpoly', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = 1 - z ^ d := by
      field_simp [pow_ne_zero d hz]



private theorem cyclotomic_prod_zpowers_characters_one_sub
    {G : Type*} [Finite G] [CommGroup G] (a : G)
    [Fintype (UnitCharacter (Subgroup.zpowers a))] (z : ℂ) :
    (∏ ψ : UnitCharacter (Subgroup.zpowers a),
      (1 - (ψ ⟨a, Subgroup.mem_zpowers a⟩ : ℂ) * z)) =
      1 - z ^ orderOf a := by
  classical
  letI : NeZero (orderOf a) := ⟨(orderOf_pos a).ne'⟩
  letI := Fintype.ofFinite (rootsOfUnity (orderOf a) ℂ)
  let e := cyclotomicCharEvalEquivRoots a
  calc
    (∏ ψ : UnitCharacter (Subgroup.zpowers a),
        (1 - (ψ ⟨a, Subgroup.mem_zpowers a⟩ : ℂ) * z)) =
      ∏ r : rootsOfUnity (orderOf a) ℂ,
        (1 - ((r : ℂˣ) : ℂ) * z) := by
        apply Fintype.prod_equiv e
        intro ψ
        rfl
    _ = 1 - z ^ orderOf a := cyclotomic_prod_rootsOfUnity_one_sub (orderOf a) z

private theorem cyclotomic_prod_characters_one_sub
    {G : Type*} [Finite G] [CommGroup G] (a : G)
    [Fintype (UnitCharacter G)]
    [Fintype (UnitCharacter (Subgroup.zpowers a))] (z : ℂ) :
    (∏ χ : UnitCharacter G, (1 - (χ a : ℂ) * z)) =
      (1 - z ^ orderOf a) ^ (Subgroup.zpowers a).index := by
  classical
  let B := Subgroup.zpowers a
  let b : B := ⟨a, Subgroup.mem_zpowers a⟩
  let res : UnitCharacter G →* UnitCharacter B := MonoidHom.restrictHom B ℂˣ
  have hres : Function.Surjective res :=
    MonoidHom.restrict_surjective (M := ℂ) B
  have hcard (ψ : UnitCharacter B) :
      Fintype.card {χ : UnitCharacter G // res χ = ψ} = B.index := by
    obtain ⟨χ₀, hχ₀⟩ := hres ψ
    let E : {χ : UnitCharacter G // res χ = ψ} ≃ res.ker :=
      (Equiv.setCongr (show {χ : UnitCharacter G | res χ = ψ} =
          res ⁻¹' {res χ₀} by
        ext χ
        change (res χ = ψ) ↔ (res χ = res χ₀)
        rw [hχ₀])).trans (MonoidHom.fiberEquivKer res χ₀)
    rw [Fintype.card_eq_nat_card, Nat.card_congr E,
      CommGroup.card_restrictHom_ker, ← Subgroup.index_eq_card]
  calc
    (∏ χ : UnitCharacter G, (1 - (χ a : ℂ) * z)) =
        ∏ ψ : UnitCharacter B,
          ∏ χ : {χ : UnitCharacter G // res χ = ψ},
            (1 - (χ.1 a : ℂ) * z) :=
      (Fintype.prod_fiberwise res
        (fun χ : UnitCharacter G => (1 - (χ a : ℂ) * z))).symm
    _ = ∏ ψ : UnitCharacter B, (1 - (ψ b : ℂ) * z) ^ B.index := by
      apply Finset.prod_congr rfl
      intro ψ hψ
      calc
        (∏ χ : {χ : UnitCharacter G // res χ = ψ},
            (1 - (χ.1 a : ℂ) * z)) =
            ∏ _χ : {χ : UnitCharacter G // res χ = ψ},
              (1 - (ψ b : ℂ) * z) := by
          apply Finset.prod_congr rfl
          intro χ hχ
          have hr := congrArg (fun f : UnitCharacter B => f b) χ.2
          change χ.1 a = ψ b at hr
          rw [hr]
        _ = (1 - (ψ b : ℂ) * z) ^
            Fintype.card {χ : UnitCharacter G // res χ = ψ} := by
          rw [Finset.prod_const, Finset.card_univ]
        _ = (1 - (ψ b : ℂ) * z) ^ B.index := by rw [hcard ψ]
    _ = (∏ ψ : UnitCharacter B, (1 - (ψ b : ℂ) * z)) ^ B.index := by
      rw [Finset.prod_pow]
    _ = (1 - z ^ orderOf a) ^ B.index :=
      congrArg (· ^ B.index) (cyclotomic_prod_zpowers_characters_one_sub a z)


private noncomputable def cyclotomicContractPrime
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (Q : PrimeIdeal M) : PrimeIdeal K :=
  ⟨Q.asIdeal.under (NumberField.RingOfIntegers K), inferInstance, by
    intro h
    letI : Q.asIdeal.LiesOver (⊥ : Ideal (NumberField.RingOfIntegers K)) := ⟨by simpa [h]⟩
    exact Q.ne_bot (Ideal.eq_bot_of_liesOver_bot
      (NumberField.RingOfIntegers K) Q.asIdeal)⟩

@[simp] private theorem cyclotomicContractPrime_asIdeal
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (Q : PrimeIdeal M) :
    (cyclotomicContractPrime (K := K) Q).asIdeal =
      Q.asIdeal.under (NumberField.RingOfIntegers K) := rfl

private noncomputable def cyclotomicPrimeFiberEquiv
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (p : PrimeIdeal K) :
    {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p} ≃
      p.asIdeal.primesOver (NumberField.RingOfIntegers M) where
  toFun Q := ⟨Q.1.asIdeal, Q.1.isPrime, ⟨by
    simpa using (congrArg (fun q : PrimeIdeal K => q.asIdeal) Q.2).symm⟩⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, by
    intro h
    apply p.ne_bot
    rw [Q.2.2.over]
    simpa [h]⟩, by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact Q.2.2.over.symm⟩
  left_inv Q := by
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

private theorem cyclotomicPrimeCharacterValue {K : Type*} [Field K] [NumberField K]
    (m : RayModulus K) (ψ : RayClassCharacter m)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    rayClassCharacterValue m ψ p.asIdeal =
      ψ (RayClassGroup.mk m (cyclotomicPrimeRayIdeal m p hp)) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  let I := cyclotomicPrimeRayIdeal m p hp
  let c := RayClassGroup.mk m I
  have hc : RayClassGroup.IsClassOfIdeal m p.asIdeal c :=
    ⟨I, cyclotomicPrimeRayIdeal_val m p hp, rfl⟩
  rw [rayClassCharacterValue, tsum_fintype, Finset.sum_eq_single c]
  · rw [if_pos hc]
  · intro d hd hdc
    rw [if_neg]
    intro had
    exact hdc (cyclotomicClassOfIdeal_unique m p.asIdeal had hc)
  · simp

open scoped Classical in
private theorem cyclotomicLocalEulerFactor
    {K M F : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Field F] [NumberField F]
    [Algebra K M] [Algebra K F] [Algebra M F] [IsScalarTower K M F]
    [FiniteDimensional K M] [IsGalois K M]
    (n : ℕ) (m : RayModulus K) [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m) (s : ℂ)
    (p : PrimeIdeal K) :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    let A := MonoidHom.range ν
    let νA : RayClassGroup m →* A := corestrictToRange ν
    (∏' Q : {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p},
      if Q.1.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite then 1 else
        (1 - Complex.cpow (PrimeIdeal.norm Q.1 : ℂ) (-s))⁻¹) =
      ((∏' χ : UnitCharacter A,
        if p.asIdeal ∣ m.finite then 1 else
          (1 - rayClassCharacterValue m
              (cyclotomicPullbackCharacter m νA χ) p.asIdeal *
            Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹) ^ A.index) := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let A := MonoidHom.range ν
  let νA : RayClassGroup m →* A := corestrictToRange ν
  letI := Fintype.ofFinite (UnitCharacter A)
  letI := Fintype.ofEquiv
    (p.asIdeal.primesOver (NumberField.RingOfIntegers M))
    (cyclotomicPrimeFiberEquiv (M := M) p).symm
  dsimp only
  rw [tprod_fintype, tprod_fintype]
  by_cases hp : p.asIdeal ∣ m.finite
  · simp only [hp, if_pos, Finset.prod_const_one, one_pow]
    apply Finset.prod_eq_one
    intro Q hQ
    rw [if_pos]
    rw [← cyclotomicContractPrime_asIdeal, Q.2]
    exact hp
  · simp only [hp, if_false]
    let I := cyclotomicPrimeRayIdeal m p hp
    let c := RayClassGroup.mk m I
    have hc : RayClassGroup.IsClassOfIdeal m p.asIdeal c :=
      ⟨I, cyclotomicPrimeRayIdeal_val m p hp, rfl⟩
    let Q₀ := cyclotomicPrimeAbove (F := M) p
    have hQ₀p : Q₀.asIdeal.LiesOver p.asIdeal :=
      cyclotomicPrimeAbove_liesOver p
    have hQ₀unr : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) Q₀.asIdeal := by
      by_contra h
      apply hp
      have hd := hram Q₀ h
      simpa only [← hQ₀p.over] using hd
    let a : A := νA c
    have ha : (a : Gal(M/K)) = arithFrobeniusAt (K := K) (L := M) Q₀ := by
      change ν c = _
      exact cyclotomicIdealMap_on_prime
        (M := M) (F := F) n m hn hmod hram p hp c hc Q₀ hQ₀p
    have haorder : orderOf a =
        (Q₀.asIdeal.under (NumberField.RingOfIntegers K)).inertiaDeg Q₀.asIdeal := by
      rw [← arithFrobAt_order_eq_inertiaDeg Q₀ hQ₀unr, ← ha]
      exact (orderOf_injective A.subtype A.subtype_injective a).symm
    let B := Subgroup.zpowers a
    letI := Fintype.ofFinite (UnitCharacter B)
    have hnormQ (Q : {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p}) :
        PrimeIdeal.norm Q.1 = PrimeIdeal.norm p ^ orderOf a := by
      have hQp : Q.1.asIdeal.LiesOver p.asIdeal := by
        constructor
        simpa using (congrArg (fun q : PrimeIdeal K => q.asIdeal) Q.2).symm
      rw [PrimeIdeal.norm_pow_inertiaDeg Q.1 p hQp, haorder]
      letI : Q.1.asIdeal.LiesOver p.asIdeal := hQp
      letI : Q₀.asIdeal.LiesOver p.asIdeal := hQ₀p
      rw [Ideal.inertiaDeg_eq_inertiaDeg' p.asIdeal Q.1.asIdeal,
        Ideal.inertiaDeg_eq_inertiaDeg'
          (Q₀.asIdeal.under (NumberField.RingOfIntegers K)) Q₀.asIdeal,
        Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal Q.1.asIdeal Q₀.asIdeal
          (Gal(M/K))]
    have hzpow : Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) ^ orderOf a =
        Complex.cpow ((PrimeIdeal.norm p ^ orderOf a : ℕ) : ℂ) (-s) := by
      calc
        Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) ^ orderOf a =
            Complex.cpow (PrimeIdeal.norm p : ℂ) ((orderOf a : ℂ) * (-s)) :=
          (Complex.cpow_nat_mul (PrimeIdeal.norm p : ℂ) (orderOf a) (-s)).symm
        _ = Complex.cpow ((PrimeIdeal.norm p : ℂ) ^ orderOf a) (-s) :=
          Complex.natCast_cpow_natCast_mul (PrimeIdeal.norm p) (orderOf a) (-s)
        _ = Complex.cpow ((PrimeIdeal.norm p ^ orderOf a : ℕ) : ℂ) (-s) := by
          rw [Nat.cast_pow]
    have hfiber : Fintype.card
        {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p} =
        B.index * A.index := by
      have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
        p.asIdeal (NumberField.RingOfIntegers M) (Gal(M/K))
      have hramidx : p.asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers M) = 1 := by
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q₀.asIdeal (Gal(M/K)),
          ← Ideal.ramificationIdx_eq_ramificationIdx'
            (Q₀.asIdeal.under (NumberField.RingOfIntegers K)) Q₀.asIdeal
            (Ideal.under_ne_bot (NumberField.RingOfIntegers K) Q₀.ne_bot)]
        letI : Algebra.IsUnramifiedAt
            (NumberField.RingOfIntegers K) Q₀.asIdeal := hQ₀unr
        exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt Q₀.ne_bot
      have hinertia : p.asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers M) = orderOf a := by
        rw [Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal Q₀.asIdeal (Gal(M/K)),
          ← Ideal.inertiaDeg_eq_inertiaDeg'
            (Q₀.asIdeal.under (NumberField.RingOfIntegers K)) Q₀.asIdeal,
          haorder]
      rw [hramidx, hinertia, one_mul] at hfund
      have hfund' : Fintype.card
          {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p} * orderOf a =
          Nat.card (Gal(M/K)) := by
        rw [Fintype.card_congr (cyclotomicPrimeFiberEquiv (M := M) p),
          Set.fintypeCard_eq_ncard]
        exact hfund
      have hB := Subgroup.card_mul_index B
      have hA := Subgroup.card_mul_index A
      rw [Nat.card_zpowers] at hB
      apply Nat.mul_right_cancel (orderOf_pos a)
      rw [hfund']
      calc
        Nat.card (Gal(M/K)) = Nat.card A * A.index := hA.symm
        _ = (orderOf a * B.index) * A.index := by rw [hB]
        _ = (B.index * A.index) * orderOf a := by ac_rfl
    have hchar : (∏ χ : UnitCharacter A,
        (1 - rayClassCharacterValue m
              (cyclotomicPullbackCharacter m νA χ) p.asIdeal *
            Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹) =
        ((1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) ^ orderOf a)⁻¹) ^
          B.index := by
      have hvalue (χ : UnitCharacter A) :
          rayClassCharacterValue m
              (cyclotomicPullbackCharacter m νA χ) p.asIdeal = χ a := by
        rw [cyclotomicPrimeCharacterValue m _ p hp,
          cyclotomicPullbackCharacter_apply]
      simp_rw [hvalue]
      rw [Finset.prod_inv_distrib]
      rw [cyclotomic_prod_characters_one_sub a]
      rw [← inv_pow]
    rw [hchar, ← pow_mul, ← hfiber]
    calc
      (∏ Q : {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p},
          if Q.1.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite then 1 else
            (1 - Complex.cpow (PrimeIdeal.norm Q.1 : ℂ) (-s))⁻¹) =
          ∏ _Q : {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p},
            (1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) ^ orderOf a)⁻¹ := by
        apply Finset.prod_congr rfl
        intro Q hQ
        rw [if_neg]
        · rw [hnormQ Q, ← hzpow]
        · intro hd
          apply hp
          rw [← cyclotomicContractPrime_asIdeal, Q.2] at hd
          exact hd
      _ = (1 - Complex.cpow (PrimeIdeal.norm p : ℂ) (-s) ^ orderOf a)⁻¹ ^
          Fintype.card {Q : PrimeIdeal M // cyclotomicContractPrime (K := K) Q = p} := by
        rw [Finset.prod_const, Finset.card_univ]


private theorem cyclotomicFactorCoeffSum (n : ℕ) :
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

private theorem cyclotomicFactorSummableIdealRpow (s : ℝ) (hs : 1 < s) :
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
      Real.rpow_one, ← Nat.cast_sum, cyclotomicFactorCoeffSum]
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

private theorem cyclotomicFactorSummablePrimeRpow (s : ℝ) (hs : 1 < s) :
    Summable (fun p : PrimeIdeal K => Real.rpow (PrimeIdeal.norm p : ℝ) (-s)) := by
  apply ((cyclotomicFactorSummableIdealRpow (K := K) s hs).comp_injective
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective).congr
  intro p
  rfl


private theorem cyclotomicMultipliableInvOneSub {ι : Type*} (x : ι → ℂ) (q : ℝ)
    (hx : Summable (fun i => ‖x i‖)) (hq0 : q < 1)
    (hq : ∀ i, ‖x i‖ ≤ q) :
    Multipliable (fun i => (1 - x i)⁻¹) := by
  let c : ℝ := (1 - q)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (sub_nonneg.mpr hq0.le)
  have hden (i : ι) : 1 - x i ≠ 0 := by
    intro h
    have he : x i = 1 := (sub_eq_zero.mp h).symm
    have hi := hq i
    rw [he, norm_one] at hi
    linarith
  have hbound (i : ι) : ‖x i * (1 - x i)⁻¹‖ ≤ c * ‖x i‖ := by
    rw [norm_mul, norm_inv]
    have hlo : 1 - q ≤ ‖1 - x i‖ := by
      calc
        1 - q ≤ 1 - ‖x i‖ := sub_le_sub_left (hq i) 1
        _ ≤ ‖1 - x i‖ := by
          simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (x i)
    have hpos : 0 < 1 - q := sub_pos.mpr hq0
    have hinv : ‖1 - x i‖⁻¹ ≤ c := by
      dsimp [c]
      exact inv_anti₀ hpos hlo
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hinv (norm_nonneg (x i))
  have hs : Summable (fun i => ‖x i * (1 - x i)⁻¹‖) := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound
    exact hx.mul_left c
  have hm := multipliable_one_add_of_summable hs
  apply hm.congr
  intro i
  field_simp [hden i]
  ring


private theorem cyclotomicEulerFactors_multipliable (u : PrimeIdeal K → ℂ)
    (hu : ∀ p, ‖u p‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : PrimeIdeal K =>
      (1 - u p * Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹) := by
  let x : PrimeIdeal K → ℂ := fun p =>
    u p * Complex.cpow (PrimeIdeal.norm p : ℂ) (-s)
  have hnorm (p : PrimeIdeal K) : ‖x p‖ ≤
      Real.rpow (PrimeIdeal.norm p : ℝ) (-s.re) := by
    dsimp [x]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos]
    · exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hu p)
    · have hn0 : PrimeIdeal.norm p ≠ 0 := by
        rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
        exact p.ne_bot
      exact Nat.pos_of_ne_zero hn0
  have hx : Summable (fun p : PrimeIdeal K => ‖x p‖) := by
    apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) hnorm
    exact cyclotomicFactorSummablePrimeRpow s.re hs
  let q : ℝ := Real.rpow 2 (-s.re)
  have hq0 : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  have hq (p : PrimeIdeal K) : ‖x p‖ ≤ q := by
    apply (hnorm p).trans
    dsimp [q]
    apply Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) _ (by linarith)
    norm_cast
    have hn0 : PrimeIdeal.norm p ≠ 0 := by
      rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
      exact p.ne_bot
    have hn1 : PrimeIdeal.norm p ≠ 1 := by
      rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_one_iff]
      exact p.isPrime.ne_top
    omega
  exact cyclotomicMultipliableInvOneSub x q hx hq0 hq




/-- Blueprint Proposition 6.2, equation (10), proposed declaration
`cyclotomic_zeta_eq_prod_weberL`. The product is over characters of the
*explicit image* `A`, and the exponent is the index `[Gal(M/K):A]`. -/
theorem cyclotomic_zeta_eq_prod_weberL
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    (s : ℂ) (hs : 1 < s.re) :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    let A := MonoidHom.range ν
    incompleteExtensionZeta (M := M) m s =
      (∏' χ : UnitCharacter A,
        weberLSeriesAlong m (corestrictToRange ν) χ s) ^ A.index := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let A := MonoidHom.range ν
  let νA : RayClassGroup m →* A := corestrictToRange ν
  letI := Fintype.ofFinite (UnitCharacter A)
  dsimp only
  let up : PrimeIdeal M → ℂ := fun Q =>
    if Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite then 1 else
      (1 - Complex.cpow (PrimeIdeal.norm Q : ℂ) (-s))⁻¹
  let base : UnitCharacter A → PrimeIdeal K → ℂ := fun χ p =>
    if p.asIdeal ∣ m.finite then 1 else
      (1 - rayClassCharacterValue m (cyclotomicPullbackCharacter m νA χ) p.asIdeal *
        Complex.cpow (PrimeIdeal.norm p : ℂ) (-s))⁻¹
  let uUp : PrimeIdeal M → ℂ := fun Q =>
    if Q.asIdeal.under (NumberField.RingOfIntegers K) ∣ m.finite then 0 else 1
  have huUp (Q : PrimeIdeal M) : ‖uUp Q‖ ≤ 1 := by
    dsimp [uUp]
    split <;> simp
  have hUp : Multipliable up := by
    apply (cyclotomicEulerFactors_multipliable uUp huUp s hs).congr
    intro Q
    simp only [up, uUp]
    split <;> simp_all
  let uBase : UnitCharacter A → PrimeIdeal K → ℂ := fun χ p =>
    if p.asIdeal ∣ m.finite then 0 else
      rayClassCharacterValue m (cyclotomicPullbackCharacter m νA χ) p.asIdeal
  have huBase (χ : UnitCharacter A) (p : PrimeIdeal K) : ‖uBase χ p‖ ≤ 1 := by
    by_cases hp : p.asIdeal ∣ m.finite
    · simp [uBase, hp]
    · dsimp [uBase]
      rw [if_neg hp, cyclotomicPrimeCharacterValue m _ p hp,
        cyclotomicPullbackCharacter_apply]
      exact le_of_eq (((Units.coeHom ℂ).comp χ).isOfFinOrder
        (isOfFinOrder_of_finite (νA (RayClassGroup.mk m (cyclotomicPrimeRayIdeal m p hp))))).norm_eq_one
  have hBase (χ : UnitCharacter A) : Multipliable (base χ) := by
    apply (cyclotomicEulerFactors_multipliable (uBase χ) (huBase χ) s hs).congr
    intro p
    simp only [base, uBase]
    split <;> simp_all
  let P : PrimeIdeal K → ℂ := fun p => ∏ χ : UnitCharacter A, base χ p
  have hP : Multipliable P := by
    let chars : Finset (UnitCharacter A) := Finset.univ
    have haux (t : Finset (UnitCharacter A)) :
        Multipliable (fun p : PrimeIdeal K => ∏ χ ∈ t, base χ p) := by
      induction t using Finset.induction with
      | empty => simpa using (multipliable_one :
          Multipliable (fun _p : PrimeIdeal K => (1 : ℂ)))
      | @insert χ t hχ ih =>
          simpa only [Finset.prod_insert hχ] using (hBase χ).mul ih
    simpa [P, chars] using haux chars
  have hinterchange :
      (∏' p : PrimeIdeal K, P p) =
        ∏ χ : UnitCharacter A, ∏' p : PrimeIdeal K, base χ p := by
    simpa only [P] using
      (Multipliable.tprod_finsetProd
        (s := (Finset.univ : Finset (UnitCharacter A)))
        (fun χ _ => hBase χ))
  let contract : PrimeIdeal M → PrimeIdeal K := cyclotomicContractPrime (K := K)
  let E := Equiv.sigmaFiberEquiv contract
  have hSigma : Multipliable (up ∘ E) := (E.multipliable_iff).mpr hUp
  letI (p : PrimeIdeal K) : Fintype {Q : PrimeIdeal M // contract Q = p} :=
    Fintype.ofEquiv (p.asIdeal.primesOver (NumberField.RingOfIntegers M))
      (cyclotomicPrimeFiberEquiv (M := M) p).symm
  have hFiber (p : PrimeIdeal K) :
      Multipliable (fun Q : {Q : PrimeIdeal M // contract Q = p} => up Q.1) :=
    (hasProd_fintype _).multipliable
  have hregroup : incompleteExtensionZeta (M := M) m s =
      ∏' p : PrimeIdeal K, (P p) ^ A.index := by
    calc
      incompleteExtensionZeta (M := M) m s = ∏' Q : PrimeIdeal M, up Q := rfl
      _ = ∏' x : Σ p, {Q : PrimeIdeal M // contract Q = p}, up (E x) :=
        (E.tprod_eq up).symm
      _ = ∏' p : PrimeIdeal K,
          ∏' Q : {Q : PrimeIdeal M // contract Q = p}, up Q.1 := by
        exact Multipliable.tprod_sigma' hFiber hSigma
      _ = ∏' p : PrimeIdeal K, (P p) ^ A.index := by
        apply tprod_congr
        intro p
        have hlocal :=
          cyclotomicLocalEulerFactor (M := M) (F := F) n m hn hmod hram s p
        change (∏' Q : {Q : PrimeIdeal M // contract Q = p}, up Q.1) =
          ((∏' χ : UnitCharacter A, base χ p) ^ A.index) at hlocal
        rw [tprod_fintype, tprod_fintype] at hlocal
        rw [tprod_fintype]
        exact hlocal
  have hWeber (χ : UnitCharacter A) :
      weberLSeriesAlong m νA χ s = ∏' p : PrimeIdeal K, base χ p := by
    calc
      weberLSeriesAlong m νA χ s = weberLSeries m (cyclotomicPullbackCharacter m νA χ) s :=
        cyclotomicWeberAlong_eq_pullback m νA χ s
      _ = weberLEulerProduct m (cyclotomicPullbackCharacter m νA χ) s :=
        weberLSeries_eq_eulerProduct m _ s hs
      _ = ∏' p : PrimeIdeal K, base χ p := by rfl
  rw [tprod_fintype]
  calc
    incompleteExtensionZeta (M := M) m s =
        ∏' p : PrimeIdeal K, (P p) ^ A.index := hregroup
    _ = (∏' p : PrimeIdeal K, P p) ^ A.index := hP.tprod_pow A.index
    _ = (∏ χ : UnitCharacter A, ∏' p : PrimeIdeal K, base χ p) ^ A.index := by
      rw [hinterchange]
    _ = (∏ χ : UnitCharacter A, weberLSeriesAlong m νA χ s) ^ A.index := by
      congr 1
      apply Finset.prod_congr rfl
      intro χ hχ
      exact (hWeber χ).symm


private theorem cyclotomicWeberOneMeromorphicContinuation
    {K : Type*} [Field K] [NumberField K] (m : RayModulus K) :
    ∃ W : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → W s = weberLSeries m 1 s) ∧
      MeromorphicAt W 1 ∧
      Tendsto (fun s : ℂ => (s - 1) * W s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  obtain ⟨ρ, hρ, hcont⟩ := rayClassPartialZeta_continuation m
  let F : RayClassGroup m → ℂ → ℂ := fun c => Classical.choose (hcont c)
  have hFeq (c : RayClassGroup m) (s : ℂ) (hs : 1 < s.re) :
      F c s = rayClassPartialZeta m c s :=
    (Classical.choose_spec (hcont c)).2.1 s hs
  have hFres (c : RayClassGroup m) :
      Tendsto (fun s : ℂ => (s - 1) * F c s)
        (𝓝[≠] (1 : ℂ)) (𝓝 (ρ : ℂ)) :=
    (Classical.choose_spec (hcont c)).2.2.2
  let W : ℂ → ℂ := fun s => ∑ c : RayClassGroup m, F c s
  let R : ℂ := Fintype.card (RayClassGroup m) * ρ
  refine ⟨W, R, ?_, ?_, ?_, ?_⟩
  · dsimp [R]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Complex.ofReal_ne_zero.mpr hρ.ne')
  · intro s hs
    dsimp [W]
    rw [weberLSeries, tsum_fintype]
    apply Finset.sum_congr rfl
    intro c hc
    rw [hFeq c s hs, MulChar.one_apply (Group.isUnit c), one_mul]
  · dsimp [W]
    apply MeromorphicAt.fun_sum
    intro c hc
    exact (Classical.choose_spec (hcont c)).1 1 (by
      change 1 - 1 / (Module.finrank ℚ K : ℝ) < (1 : ℂ).re
      have hd : (0 : ℝ) < Module.finrank ℚ K := by
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
      have hdinv : (0 : ℝ) < 1 / Module.finrank ℚ K := one_div_pos.mpr hd
      simpa only [Complex.one_re] using sub_lt_self (1 : ℝ) hdinv)
  · have hsum := tendsto_finsetSum Finset.univ (fun c _ => hFres c)
    convert hsum using 1
    · funext s
      dsimp [W]
      rw [Finset.mul_sum]
    · simp [R]

private theorem cyclotomicWeberAlongOneMeromorphicContinuation
    {K G : Type*} [Field K] [NumberField K] [CommGroup G]
    (m : RayModulus K) (ν : RayClassGroup m →* G) :
    ∃ W : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → W s = weberLSeriesAlong m ν 1 s) ∧
      MeromorphicAt W 1 ∧
      Tendsto (fun s : ℂ => (s - 1) * W s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  obtain ⟨W, ρ, hρ, hWeq, hWmer, hWres⟩ :=
    cyclotomicWeberOneMeromorphicContinuation m
  refine ⟨W, ρ, hρ, ?_, hWmer, hWres⟩
  intro s hs
  rw [hWeq s hs]
  unfold weberLSeries weberLSeriesAlong
  apply tsum_congr
  intro c
  rw [MulChar.one_apply (Group.isUnit c)]
  simp

private theorem cyclotomicIncompleteZetaMeromorphicContinuation
    {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] (m : RayModulus K) :
    ∃ Z : ℂ → ℂ, ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → Z s = incompleteExtensionZeta (M := M) m s) ∧
      MeromorphicAt Z 1 ∧
      Tendsto (fun s : ℂ => (s - 1) * Z s) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  obtain ⟨Z, ρ, hρ, hZeq, hZmer, hZres⟩ :=
    cyclotomicWeberOneMeromorphicContinuation
      (cyclotomicLiftedModulus (M := M) m)
  refine ⟨Z, ρ, hρ, ?_, hZmer, hZres⟩
  intro s hs
  rw [hZeq s hs, cyclotomicIncompleteZeta_eq_weber m s hs]

private theorem cyclotomic_meromorphicOrder_eq_neg_one
    (Z : ℂ → ℂ) (hZmer : MeromorphicAt Z 1)
    (R : ℂ) (hR : R ≠ 0)
    (hZres : Tendsto (fun s : ℂ => (s - 1) * Z s)
      (𝓝[≠] (1 : ℂ)) (𝓝 R)) :
    meromorphicOrderAt Z 1 = ((-1 : ℤ) : WithTop ℤ) := by
  have hlin : MeromorphicAt (fun s : ℂ => s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hmul : MeromorphicAt (fun s : ℂ => (s - 1) * Z s) 1 :=
    hlin.mul hZmer
  have hordMul : meromorphicOrderAt (fun s : ℂ => (s - 1) * Z s) 1 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hmul).mp ⟨R, hR, hZres⟩
  rw [fun_meromorphicOrderAt_mul hlin hZmer,
    meromorphicOrderAt_id_sub_const] at hordMul
  have hne : meromorphicOrderAt Z 1 ≠ ⊤ := by
    intro htop
    rw [htop] at hordMul
    simp at hordMul
  lift meromorphicOrderAt Z 1 to ℤ using hne with k
  norm_cast at hordMul ⊢
  omega

/-- Blueprint Proposition 6.3, equation (11) (`cyclotomic_poleOrder`): taking
orders at one gives `-1 = [H:A](-1 + Σ_{χ≠1} rχ)` with every `rχ ≥ 0`. -/
theorem cyclotomic_poleOrder
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m) :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    let A := MonoidHom.range ν
    ∃ r : {χ : UnitCharacter A // χ ≠ 1} → ℕ,
      (-1 : ℤ) = (A.index : ℤ) *
        (-1 + ∑' χ : {χ : UnitCharacter A // χ ≠ 1}, (r χ : ℤ)) := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let A := MonoidHom.range ν
  let νA : RayClassGroup m →* A := corestrictToRange ν
  letI := Fintype.ofFinite (UnitCharacter A)
  have hνA : Function.Surjective νA := by
    exact MonoidHom.rangeRestrict_surjective ν
  have hstrip : 1 - 1 / (Module.finrank ℚ K : ℝ) < (1 : ℂ).re := by
    have hd : (0 : ℝ) < Module.finrank ℚ K := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hdinv : (0 : ℝ) < 1 / Module.finrank ℚ K := one_div_pos.mpr hd
    simpa only [Complex.one_re] using sub_lt_self (1 : ℝ) hdinv
  obtain ⟨Z, RZ, hRZ, hZeq, hZmer, hZres⟩ :=
    cyclotomicIncompleteZetaMeromorphicContinuation (M := M) m
  obtain ⟨T, RT, hRT, hTeq, hTmer, hTres⟩ :=
    cyclotomicWeberAlongOneMeromorphicContinuation m νA
  have hZorder : meromorphicOrderAt Z 1 = ((-1 : ℤ) : WithTop ℤ) :=
    cyclotomic_meromorphicOrder_eq_neg_one Z hZmer RZ hRZ hZres
  have hTorder : meromorphicOrderAt T 1 = ((-1 : ℤ) : WithTop ℤ) :=
    cyclotomic_meromorphicOrder_eq_neg_one T hTmer RT hRT hTres
  let O : (χ : UnitCharacter A) → χ ≠ 1 → ℂ → ℂ := fun χ hχ =>
    Classical.choose (cyclotomicWeberAlongNontrivialContinuation m νA hνA χ hχ)
  have hOan (χ : UnitCharacter A) (hχ : χ ≠ 1) :
      AnalyticOnNhd ℂ (O χ hχ)
        {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
    (Classical.choose_spec
      (cyclotomicWeberAlongNontrivialContinuation m νA hνA χ hχ)).1
  have hOeq (χ : UnitCharacter A) (hχ : χ ≠ 1)
      (s : ℂ) (hs : 1 < s.re) :
      O χ hχ s = weberLSeriesAlong m νA χ s :=
    (Classical.choose_spec
      (cyclotomicWeberAlongNontrivialContinuation m νA hνA χ hχ)).2 s hs
  let W : UnitCharacter A → ℂ → ℂ := fun χ =>
    if hχ : χ = 1 then T else O χ hχ
  have hWeq (χ : UnitCharacter A) (s : ℂ) (hs : 1 < s.re) :
      W χ s = weberLSeriesAlong m νA χ s := by
    by_cases hχ : χ = 1
    · subst χ
      simpa [W] using hTeq s hs
    · simpa [W, hχ] using hOeq χ hχ s hs
  have hWmer (χ : UnitCharacter A) : MeromorphicAt (W χ) 1 := by
    by_cases hχ : χ = 1
    · subst χ
      simpa [W] using hTmer
    · have h := (hOan χ hχ 1 hstrip).meromorphicAt
      simpa [W, hχ] using h
  have hWone : W 1 = T := by
    simp [W]
  let PW : ℂ → ℂ := fun s => ∏ χ : UnitCharacter A, W χ s
  have hPWmer : MeromorphicAt PW 1 := by
    dsimp [PW]
    apply MeromorphicAt.fun_prod
    intro χ hχ
    exact hWmer χ
  have hPWorder : meromorphicOrderAt PW 1 =
      ∑ χ : UnitCharacter A, meromorphicOrderAt (W χ) 1 := by
    have haux (t : Finset (UnitCharacter A)) :
        meromorphicOrderAt (fun s : ℂ => ∏ χ ∈ t, W χ s) 1 =
          ∑ χ ∈ t, meromorphicOrderAt (W χ) 1 := by
      induction t using Finset.induction with
      | empty => simp [meromorphicOrderAt_const]
      | @insert χ t hχ ih =>
          simp only [Finset.prod_insert hχ, Finset.sum_insert hχ]
          rw [fun_meromorphicOrderAt_mul (hWmer χ)
              (MeromorphicAt.fun_prod fun η hη => hWmer η), ih]
    simpa [PW] using haux Finset.univ
  have hPWpowMer : MeromorphicAt (fun s => PW s ^ A.index) 1 :=
    hPWmer.fun_pow A.index
  have hcoeNhds : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcoe : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoeNhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast ne_of_gt hx
  have heqReal : (fun x : ℝ => Z (x : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => PW (x : ℂ) ^ A.index) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hs : 1 < (x : ℂ).re := by simpa using hx
    rw [hZeq (x : ℂ) hs]
    have hzeta := cyclotomic_zeta_eq_prod_weberL
      (M := M) (F := F) n m hn hmod hram (x : ℂ) hs
    change incompleteExtensionZeta (M := M) m (x : ℂ) =
      (∏' χ : UnitCharacter A, weberLSeriesAlong m νA χ (x : ℂ)) ^ A.index
      at hzeta
    rw [tprod_fintype] at hzeta
    rw [hzeta]
    congr 1
    apply Finset.prod_congr rfl
    intro χ hχ
    exact (hWeq χ (x : ℂ) hs).symm
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), Z z = PW z ^ A.index :=
    hcoe.frequently heqReal.frequently
  have heqGerm : Z =ᶠ[𝓝[≠] (1 : ℂ)] (fun s => PW s ^ A.index) :=
    (hZmer.frequently_eq_iff_eventuallyEq hPWpowMer).mp hfreq
  have horderEq : meromorphicOrderAt Z 1 =
      meromorphicOrderAt (fun s => PW s ^ A.index) 1 :=
    meromorphicOrderAt_congr heqGerm
  have hindexPos : 0 < A.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have horderWithTop : ((-1 : ℤ) : WithTop ℤ) =
      (A.index : WithTop ℤ) *
        ∑ χ : UnitCharacter A, meromorphicOrderAt (W χ) 1 := by
    rw [hZorder] at horderEq
    rw [fun_meromorphicOrderAt_pow hPWmer, hPWorder] at horderEq
    exact horderEq
  have horder_ne_top (χ : UnitCharacter A) :
      meromorphicOrderAt (W χ) 1 ≠ ⊤ := by
    intro htop
    have hsumtop : (∑ η : UnitCharacter A,
        meromorphicOrderAt (W η) 1) = ⊤ := by
      apply WithTop.sum_eq_top.mpr
      exact ⟨χ, Finset.mem_univ χ, htop⟩
    rw [hsumtop] at horderWithTop
    have hindexne : (A.index : WithTop ℤ) ≠ 0 := by
      exact_mod_cast hindexPos.ne'
    rw [WithTop.mul_top hindexne] at horderWithTop
    exact WithTop.coe_ne_top horderWithTop
  let ord : UnitCharacter A → ℤ := fun χ =>
    (meromorphicOrderAt (W χ) 1).untop (horder_ne_top χ)
  have hord (χ : UnitCharacter A) :
      (ord χ : WithTop ℤ) = meromorphicOrderAt (W χ) 1 :=
    WithTop.coe_untop _ _
  have hordOne : ord 1 = -1 := by
    apply WithTop.coe_eq_coe.mp
    rw [hord, hWone, hTorder]
  have horderInt : (-1 : ℤ) = A.index * ∑ χ : UnitCharacter A, ord χ := by
    have h := horderWithTop
    simp_rw [← hord] at h
    norm_cast at h
  have hord_nonneg (χ : UnitCharacter A) (hχ : χ ≠ 1) : 0 ≤ ord χ := by
    have han := (hOan χ hχ 1 hstrip).meromorphicOrderAt_nonneg
    have hword : meromorphicOrderAt (W χ) 1 =
        meromorphicOrderAt (O χ hχ) 1 := by
      apply meromorphicOrderAt_congr
      filter_upwards with z
      simp [W, hχ]
    rw [← hword, ← hord] at han
    exact_mod_cast han
  let r : {χ : UnitCharacter A // χ ≠ 1} → ℕ := fun χ =>
    Int.toNat (ord χ.1)
  have hr (χ : {χ : UnitCharacter A // χ ≠ 1}) :
      (r χ : ℤ) = ord χ.1 := by
    exact Int.toNat_of_nonneg (hord_nonneg χ.1 χ.2)
  have hsum : (∑ χ : UnitCharacter A, ord χ) =
      ord 1 + ∑ χ : {χ : UnitCharacter A // χ ≠ 1}, ord χ.1 := by
    rw [← Finset.sum_subtype (s := (Finset.univ.erase (1 : UnitCharacter A)))
      (by intro χ; simp) ord]
    have h := Finset.sum_erase_add (Finset.univ : Finset (UnitCharacter A))
      ord (Finset.mem_univ (1 : UnitCharacter A))
    rw [← h]
    ac_rfl
  refine ⟨r, ?_⟩
  rw [tsum_fintype]
  calc
    (-1 : ℤ) = A.index * ∑ χ : UnitCharacter A, ord χ := horderInt
    _ = A.index * (ord 1 +
        ∑ χ : {χ : UnitCharacter A // χ ≠ 1}, ord χ.1) := by rw [hsum]
    _ = (A.index : ℤ) *
        (-1 + ∑ χ : {χ : UnitCharacter A // χ ≠ 1}, (r χ : ℤ)) := by
      rw [hordOne]
      congr 2
      apply Finset.sum_congr rfl
      intro χ hχ
      exact (hr χ).symm


/-- Blueprint Proposition 6.3, proposed declaration
`cyclotomicIdealMap_surjective`: the pole-order equation forces the temporary
image subgroup to be the whole Galois group. -/
theorem cyclotomicIdealMap_surjective
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m) :
    Function.Surjective
      (cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram) := by
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let A := MonoidHom.range ν
  obtain ⟨r, hr⟩ := cyclotomic_poleOrder (M := M) (F := F) n m hn hmod hram
  have hdivNeg : (A.index : ℤ) ∣ (-1 : ℤ) := by
    refine ⟨-1 + ∑' χ : {χ : UnitCharacter A // χ ≠ 1}, (r χ : ℤ), ?_⟩
    simpa [A, ν] using hr
  have hdivOne : (A.index : ℤ) ∣ (1 : ℤ) := dvd_neg.mp (by simpa using hdivNeg)
  have hindex : A.index = 1 := by
    exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdivOne)
  apply MonoidHom.range_eq_top.mp
  change A = ⊤
  exact Subgroup.index_eq_one.mp hindex

/-- Blueprint Proposition 6.3 (`cyclotomic_weberL_ne_zero_at_one`): after
surjectivity, every nontrivial pulled-back character has a continuation that
is holomorphic and nonzero at `s=1`. This is the at-one result used by §9; it
does not use the Dedekind zero-free line. -/
theorem cyclotomic_weberL_ne_zero_at_one
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    (χ : UnitCharacter (Gal(M/K))) (hχ : χ ≠ 1) :
    ∃ W : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        W s = weberLSeriesAlong m
          (cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram) χ s) ∧
      AnalyticAt ℂ W 1 ∧ W 1 ≠ 0 := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let A := MonoidHom.range ν
  let νA : RayClassGroup m →* A := corestrictToRange ν
  have hν : Function.Surjective ν :=
    cyclotomicIdealMap_surjective (M := M) (F := F) n m hn hmod hram
  have hνA : Function.Surjective νA := by
    exact MonoidHom.rangeRestrict_surjective ν
  have hAtop : A = ⊤ := MonoidHom.range_eq_top.mpr hν
  have hAindex : A.index = 1 := Subgroup.index_eq_one.mpr hAtop
  let χA : UnitCharacter A := χ.comp A.subtype
  have hχA : χA ≠ 1 := by
    intro h
    apply hχ
    apply MonoidHom.ext
    intro g
    obtain ⟨c, hc⟩ := hν g
    let a : A := ⟨g, ⟨c, hc⟩⟩
    have ha := DFunLike.congr_fun h a
    simpa [χA, a] using ha
  obtain ⟨W, hWan, hWeq⟩ :=
    cyclotomicWeberAlongNontrivialContinuation m νA hνA χA hχA
  have hstrip : 1 - 1 / (Module.finrank ℚ K : ℝ) < (1 : ℂ).re := by
    have hd : (0 : ℝ) < Module.finrank ℚ K := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    simp only [Complex.one_re]
    have : (0 : ℝ) < 1 / Module.finrank ℚ K := one_div_pos.mpr hd
    linarith
  have hWat : AnalyticAt ℂ W 1 := hWan 1 hstrip
  refine ⟨W, ?_, hWat, ?_⟩
  · intro s hs
    rw [hWeq s hs]
    unfold νA χA corestrictToRange
    unfold weberLSeriesAlong
    apply tsum_congr
    intro c
    rfl
  · intro hWzero
    letI := Fintype.ofFinite (UnitCharacter A)
    obtain ⟨T, RT, hRT, hTeq, hTres⟩ := cyclotomicWeberAlongOneContinuation m νA
    obtain ⟨Z, RZ, hRZ, hZeq, hZres⟩ :=
      cyclotomicIncompleteZetaContinuation (M := M) m
    let O : (η : UnitCharacter A) → η ≠ 1 → ℂ → ℂ :=
      fun η hη => Classical.choose
        (cyclotomicWeberAlongNontrivialContinuation m νA hνA η hη)
    have hOan (η : UnitCharacter A) (hη : η ≠ 1) :
        AnalyticOnNhd ℂ (O η hη) {s : ℂ |
          1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
      (Classical.choose_spec
        (cyclotomicWeberAlongNontrivialContinuation m νA hνA η hη)).1
    have hOeq (η : UnitCharacter A) (hη : η ≠ 1)
        (s : ℂ) (hs : 1 < s.re) :
        O η hη s = weberLSeriesAlong m νA η s :=
      (Classical.choose_spec
        (cyclotomicWeberAlongNontrivialContinuation m νA hνA η hη)).2 s hs
    let Wf : UnitCharacter A → ℂ → ℂ := fun η =>
      if hη : η = 1 then T
      else if η = χA then W else O η hη
    have hWfEq (η : UnitCharacter A) (s : ℂ) (hs : 1 < s.re) :
        Wf η s = weberLSeriesAlong m νA η s := by
      by_cases hη : η = 1
      · subst η
        simpa [Wf] using hTeq s hs
      · by_cases hηχ : η = χA
        · subst η
          simpa [Wf, hχA] using hWeq s hs
        · simpa [Wf, hη, hηχ] using hOeq η hη s hs
    have hWfCont (η : UnitCharacter A) (hη : η ≠ 1) :
        ContinuousAt (Wf η) 1 := by
      by_cases hηχ : η = χA
      · subst η
        simpa [Wf, hχA] using hWat.continuousAt
      · have h := (hOan η hη 1 hstrip).continuousAt
        simpa [Wf, hη, hηχ] using h
    let V : UnitCharacter A → ℂ → ℂ := fun η s =>
      if η = 1 then (s - 1) * Wf η s else Wf η s
    let b : UnitCharacter A → ℂ := fun η =>
      if η = 1 then RT else Wf η 1
    have hcoeNhds : Tendsto (fun x : ℝ => (x : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hcoe : Tendsto (fun x : ℝ => (x : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hcoeNhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast ne_of_gt hx
    have hV (η : UnitCharacter A) :
        Tendsto (fun x : ℝ => V η (x : ℂ))
          (𝓝[>] (1 : ℝ)) (𝓝 (b η)) := by
      by_cases hη : η = 1
      · subst η
        simp only [V, b, Wf, if_pos, dif_pos]
        exact (hTres.comp hcoe).congr'
          (Filter.Eventually.of_forall fun _ => rfl)
      · have ht := (hWfCont η hη).tendsto.comp hcoeNhds
        simp only [V, b, if_neg hη]
        exact ht.congr' (Filter.Eventually.of_forall fun _ => rfl)
    have hprod := tendsto_finset_prod Finset.univ
      (fun η _ => hV η)
    have hbzero : ∏ η : UnitCharacter A, b η = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ χA)
      simp [b, Wf, hχA, hWzero]
    have hprod0 : Tendsto
        (fun x : ℝ => ∏ η : UnitCharacter A, V η (x : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      simpa only [hbzero] using hprod
    have hVprod (s : ℂ) :
        (∏ η : UnitCharacter A, V η s) =
          (s - 1) * ∏ η : UnitCharacter A, Wf η s := by
      rw [← Finset.mul_prod_erase Finset.univ (fun η => V η s)
          (Finset.mem_univ (1 : UnitCharacter A)),
        ← Finset.mul_prod_erase Finset.univ (fun η => Wf η s)
          (Finset.mem_univ (1 : UnitCharacter A))]
      simp only [V, if_pos]
      rw [mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro η hη
      have hηone : η ≠ 1 := by
        simpa using (Finset.mem_erase.mp hη).1
      simp [V, hηone]
    have heq : (fun x : ℝ => ((x : ℂ) - 1) * Z x) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun x : ℝ => ∏ η : UnitCharacter A, V η (x : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hs : 1 < (x : ℂ).re := by simpa using hx
      rw [hVprod]
      congr 1
      rw [hZeq (x : ℂ) hs]
      have hzeta := cyclotomic_zeta_eq_prod_weberL
        (M := M) (F := F) n m hn hmod hram (x : ℂ) hs
      change incompleteExtensionZeta (M := M) m (x : ℂ) =
        (∏' η : UnitCharacter A, weberLSeriesAlong m νA η (x : ℂ)) ^ A.index
        at hzeta
      rw [hAindex, pow_one, tprod_fintype] at hzeta
      rw [hzeta]
      apply Finset.prod_congr rfl
      intro η hη
      exact (hWfEq η (x : ℂ) hs).symm
    have hleft := hZres.comp hcoe
    have hzero : RZ = 0 := tendsto_nhds_unique_of_eventuallyEq hleft hprod0 heq
    exact hRZ hzero


/-! ### Logarithmic Euler series for the Dirichlet-density argument -/

private noncomputable def cyclotomicDensityPrimeClass
    (m : RayModulus K) (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    RayClassGroup m :=
  RayClassGroup.mk m (cyclotomicPrimeRayIdeal m p hp)

private theorem cyclotomicDensityPrimeClass_isClass
    (m : RayModulus K) (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    RayClassGroup.IsClassOfIdeal m p.asIdeal
      (cyclotomicDensityPrimeClass m p hp) :=
  ⟨cyclotomicPrimeRayIdeal m p hp,
    cyclotomicPrimeRayIdeal_val m p hp, rfl⟩

private theorem cyclotomicDensity_characterValue
    {G : Type*} [CommGroup G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
    rayClassCharacterValue m (cyclotomicPullbackCharacter m ν χ) p.asIdeal =
      (χ (ν (cyclotomicDensityPrimeClass m p hp)) : ℂ) := by
  classical
  letI := Fintype.ofFinite (RayClassGroup m)
  let c := cyclotomicDensityPrimeClass m p hp
  have hc : RayClassGroup.IsClassOfIdeal m p.asIdeal c :=
    cyclotomicDensityPrimeClass_isClass m p hp
  rw [rayClassCharacterValue, tsum_fintype, Finset.sum_eq_single c]
  · rw [if_pos hc, cyclotomicPullbackCharacter_apply]
  · intro d hd hdc
    rw [if_neg]
    intro had
    exact hdc (cyclotomicClassOfIdeal_unique m p.asIdeal had hc)
  · simp

private noncomputable def cyclotomicDensityEulerTerm
    {G : Type*} [CommGroup G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (p : PrimeIdeal K) : ℂ := by
  classical
  exact if hp : p.asIdeal ∣ m.finite then 0 else
    (χ (ν (cyclotomicDensityPrimeClass m p hp)) : ℂ) *
      (Real.rpow (PrimeIdeal.norm p : ℝ) (-s) : ℂ)

private noncomputable def cyclotomicDensityLog
    {G : Type*} [CommGroup G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G) (s : ℝ) : ℂ :=
  ∑' p : PrimeIdeal K,
    Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹

private theorem cyclotomicDensity_norm_term
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (p : PrimeIdeal K) :
    ‖cyclotomicDensityEulerTerm m ν χ s p‖ ≤
      Real.rpow (PrimeIdeal.norm p : ℝ) (-s) := by
  classical
  unfold cyclotomicDensityEulerTerm
  split_ifs with hp
  · simpa using Real.rpow_nonneg (Nat.cast_nonneg (PrimeIdeal.norm p)) (-s)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hchar : ‖((χ (ν (cyclotomicDensityPrimeClass m p hp)) : ℂ))‖ = 1 :=
      (((Units.coeHom ℂ).comp χ).isOfFinOrder
        (isOfFinOrder_of_finite
          (ν (cyclotomicDensityPrimeClass m p hp)))).norm_eq_one
    rw [hchar, one_mul]
    exact le_of_eq (abs_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg (PrimeIdeal.norm p)) (-s)))

private theorem cyclotomicDensity_norm_term_lt_one
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) (p : PrimeIdeal K) :
    ‖cyclotomicDensityEulerTerm m ν χ s p‖ < 1 := by
  apply lt_of_le_of_lt (cyclotomicDensity_norm_term m ν χ s p)
  have hnorm : 2 ≤ PrimeIdeal.norm p := by
    have hn0 : PrimeIdeal.norm p ≠ 0 := by
      rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
      exact p.ne_bot
    have hn1 : PrimeIdeal.norm p ≠ 1 := by
      rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_one_iff]
      exact p.isPrime.ne_top
    omega
  have hpow : 1 < Real.rpow (PrimeIdeal.norm p : ℝ) s :=
    Real.one_lt_rpow (by exact_mod_cast hnorm) (by linarith)
  rw [show Real.rpow (PrimeIdeal.norm p : ℝ) (-s) =
    (Real.rpow (PrimeIdeal.norm p : ℝ) s)⁻¹ from
      Real.rpow_neg (Nat.cast_nonneg _) s]
  exact inv_lt_one_of_one_lt₀ hpow

private theorem cyclotomicDensity_logTerm_bound
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) (p : PrimeIdeal K) :
    ‖Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹‖ ≤
      2 * Real.rpow (PrimeIdeal.norm p : ℝ) (-s) := by
  let x := cyclotomicDensityEulerTerm m ν χ s p
  have hx : ‖x‖ < 1 := cyclotomicDensity_norm_term_lt_one m ν χ s hs p
  have hxhalf : ‖x‖ ≤ (1 / 2 : ℝ) := by
    apply (cyclotomicDensity_norm_term m ν χ s p).trans
    have hnorm : 2 ≤ PrimeIdeal.norm p := by
      have hn0 : PrimeIdeal.norm p ≠ 0 := by
        rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
        exact p.ne_bot
      have hn1 : PrimeIdeal.norm p ≠ 1 := by
        rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_one_iff]
        exact p.isPrime.ne_top
      omega
    calc
      Real.rpow (PrimeIdeal.norm p : ℝ) (-s) ≤ Real.rpow 2 (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num)
          (by exact_mod_cast hnorm) (by linarith)
      _ ≤ Real.rpow 2 (-1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num [Real.rpow_neg, Real.rpow_one]
  have hrem := Complex.norm_log_one_sub_inv_sub_self_le hx
  have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
    have hden : (1 / 2 : ℝ) ≤ 1 - ‖x‖ := by linarith
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at this ⊢
    exact this
  have hrem' : ‖Complex.log (1 - x)⁻¹ - x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 := hrem
      _ ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖x‖ ^ 2 := by ring
      _ ≤ ‖x‖ := by nlinarith [norm_nonneg x, hxhalf]
  calc
    ‖Complex.log (1 - x)⁻¹‖ ≤ ‖Complex.log (1 - x)⁻¹ - x‖ + ‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Complex.log (1 - x)⁻¹ - x) x
    _ ≤ 2 * ‖x‖ := by linarith
    _ ≤ 2 * Real.rpow (PrimeIdeal.norm p : ℝ) (-s) := by
      gcongr
      exact cyclotomicDensity_norm_term m ν χ s p

private theorem cyclotomicDensity_log_summable
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) :
    Summable (fun p : PrimeIdeal K =>
      Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹) := by
  apply Summable.of_norm_bounded
    ((cyclotomicFactorSummablePrimeRpow (K := K) s hs).mul_left 2)
  intro p
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      cyclotomicDensity_logTerm_bound m ν χ s hs p

private theorem cyclotomicDensity_exp_log
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) :
    Complex.exp (cyclotomicDensityLog m ν χ s) =
      weberLSeriesAlong m ν χ (s : ℂ) := by
  let ψ := cyclotomicPullbackCharacter m ν χ
  have hlog := cyclotomicDensity_log_summable m ν χ s hs
  have hprod := hlog.hasSum.cexp.tprod_eq
  change (∏' p : PrimeIdeal K,
      Complex.exp
        (Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹)) =
    Complex.exp (cyclotomicDensityLog m ν χ s) at hprod
  have hexp (p : PrimeIdeal K) :
      Complex.exp
          (Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹) =
        (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹ := by
    apply Complex.exp_log
    apply inv_ne_zero
    apply sub_ne_zero.mpr
    intro hx
    have hn := congrArg norm hx
    rw [norm_one] at hn
    linarith [cyclotomicDensity_norm_term_lt_one m ν χ s hs p]
  simp_rw [hexp] at hprod
  rw [cyclotomicWeberAlong_eq_pullback,
    weberLSeries_eq_eulerProduct m ψ (s : ℂ) (by simpa using hs)]
  rw [← hprod]
  unfold weberLEulerProduct
  apply tprod_congr
  intro p
  classical
  by_cases hp : p.asIdeal ∣ m.finite
  · simp [cyclotomicDensityEulerTerm, hp]
  · rw [if_neg hp, cyclotomicDensityEulerTerm, dif_neg hp,
      cyclotomicDensity_characterValue m ν χ p hp]
    have hpow :
        (Real.rpow (PrimeIdeal.norm p : ℝ) (-s) : ℂ) =
          Complex.cpow (PrimeIdeal.norm p : ℂ) (-(s : ℂ)) := by
      simpa using Complex.ofReal_cpow
        (Nat.cast_nonneg (PrimeIdeal.norm p)) (-s)
    rw [hpow]

/-- Blueprint §9: the already-declared double logarithmic Euler series is
absolutely convergent on the real half-line and agrees with the logarithmic
Euler-factor sum used below. -/
private theorem cyclotomicDensity_weberLogEulerSeries_eq
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) :
    weberLogEulerSeries m (cyclotomicPullbackCharacter m ν χ) (s : ℂ) =
      cyclotomicDensityLog m ν χ s := by
  classical
  unfold weberLogEulerSeries cyclotomicDensityLog
  apply tsum_congr
  intro p
  by_cases hp : p.asIdeal ∣ m.finite
  · simp [hp, cyclotomicDensityEulerTerm]
  · rw [if_neg hp]
    let a : ℂ := (χ (ν (cyclotomicDensityPrimeClass m p hp)) : ℂ)
    let q : ℝ := Real.rpow (PrimeIdeal.norm p : ℝ) (-s)
    let x : ℂ := a * q
    have hx : ‖x‖ < 1 := by
      convert cyclotomicDensity_norm_term_lt_one m ν χ s hs p using 1
      simp [x, q, a, cyclotomicDensityEulerTerm, hp]
    have hpow (r : ℕ) :
        x ^ (r + 1) =
          a ^ (r + 1) /
            Complex.cpow (PrimeIdeal.norm p : ℂ)
              (((r + 1 : ℕ) : ℂ) * (s : ℂ)) := by
      have hnpos : (0 : ℝ) < PrimeIdeal.norm p := by
        exact_mod_cast Nat.pos_of_ne_zero (by
          rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
          exact p.ne_bot)
      have hreal :
          q ^ (r + 1) =
            (Real.rpow (PrimeIdeal.norm p : ℝ)
              (((r + 1 : ℕ) : ℝ) * s))⁻¹ := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) (-s) (r + 1)]
        convert Real.rpow_neg (Nat.cast_nonneg (PrimeIdeal.norm p))
          (((r + 1 : ℕ) : ℝ) * s) using 1 <;> push_cast <;> ring
      have hcomplex :
          Complex.cpow (PrimeIdeal.norm p : ℂ)
              (((r + 1 : ℕ) : ℂ) * (s : ℂ)) =
            (Real.rpow (PrimeIdeal.norm p : ℝ)
              (((r + 1 : ℕ) : ℝ) * s) : ℂ) := by
        symm
        simpa using Complex.ofReal_cpow (le_of_lt hnpos)
          (((r + 1 : ℕ) : ℝ) * s)
      dsimp [x]
      rw [mul_pow, ← Complex.ofReal_pow, hreal, Complex.ofReal_inv,
        div_eq_mul_inv]
      congr 1
      exact congrArg Inv.inv hcomplex.symm
    have htaylor := Complex.hasSum_taylorSeries_neg_log hx
    have hshift : HasSum (fun r : ℕ => x ^ (r + 1) / (r + 1 : ℂ))
        (-Complex.log (1 - x)) := by
      simpa using (hasSum_nat_add_iff' 1).2 htaylor
    have hslit : 1 - x ∈ Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one (z := -x) (by simpa)
    have hlog : Complex.log (1 - x)⁻¹ = -Complex.log (1 - x) :=
      Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)
    rw [cyclotomicDensityEulerTerm, dif_neg hp]
    change (∑' r : ℕ,
      rayClassCharacterValue m (cyclotomicPullbackCharacter m ν χ) p.asIdeal ^ (r + 1) /
        ((r + 1 : ℂ) * Complex.cpow (PrimeIdeal.norm p : ℂ)
          ((r + 1 : ℂ) * (s : ℂ)))) = Complex.log (1 - x)⁻¹
    rw [cyclotomicDensity_characterValue m ν χ p hp]
    change (∑' r : ℕ,
      a ^ (r + 1) / ((r + 1 : ℂ) * Complex.cpow (PrimeIdeal.norm p : ℂ)
        ((r + 1 : ℂ) * (s : ℂ)))) = _
    have hterm (r : ℕ) :
        a ^ (r + 1) / ((r + 1 : ℂ) *
            Complex.cpow (PrimeIdeal.norm p : ℂ) ((r + 1 : ℂ) * (s : ℂ))) =
          x ^ (r + 1) / (r + 1 : ℂ) := by
      rw [hpow]
      field_simp
      congr 2 <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring
    simp_rw [hterm]
    rw [hshift.tsum_eq, hlog]

private noncomputable def cyclotomicDensityPrimeSeries
    {G : Type*} [CommGroup G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G) (s : ℝ) : ℂ :=
  ∑' p : PrimeIdeal K, cyclotomicDensityEulerTerm m ν χ s p

private theorem cyclotomicDensity_term_summable
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) :
    Summable (cyclotomicDensityEulerTerm m ν χ s) := by
  apply Summable.of_norm_bounded
    (cyclotomicFactorSummablePrimeRpow (K := K) s hs)
  exact cyclotomicDensity_norm_term m ν χ s

private theorem cyclotomicDensity_log_sub_term_bound
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) (p : PrimeIdeal K) :
    ‖Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹ -
        cyclotomicDensityEulerTerm m ν χ s p‖ ≤
      Real.rpow (PrimeIdeal.norm p : ℝ) (-2) := by
  let x := cyclotomicDensityEulerTerm m ν χ s p
  have hx : ‖x‖ < 1 := cyclotomicDensity_norm_term_lt_one m ν χ s hs p
  have hxhalf : ‖x‖ ≤ (1 / 2 : ℝ) := by
    apply (cyclotomicDensity_norm_term m ν χ s p).trans
    have hnorm : 2 ≤ PrimeIdeal.norm p := by
      have hn0 : PrimeIdeal.norm p ≠ 0 := by
        rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
        exact p.ne_bot
      have hn1 : PrimeIdeal.norm p ≠ 1 := by
        rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_one_iff]
        exact p.isPrime.ne_top
      omega
    calc
      Real.rpow (PrimeIdeal.norm p : ℝ) (-s) ≤ Real.rpow 2 (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num)
          (by exact_mod_cast hnorm) (by linarith)
      _ ≤ Real.rpow 2 (-1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num [Real.rpow_neg, Real.rpow_one]
  have hrem := Complex.norm_log_one_sub_inv_sub_self_le hx
  have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
    have hden : (1 / 2 : ℝ) ≤ 1 - ‖x‖ := by linarith
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at h ⊢
    exact h
  have hx2 : ‖x‖ ^ 2 ≤ Real.rpow (PrimeIdeal.norm p : ℝ) (-2) := by
    calc
      ‖x‖ ^ 2 ≤ Real.rpow (PrimeIdeal.norm p : ℝ) (-s) ^ 2 := by
        gcongr
        exact cyclotomicDensity_norm_term m ν χ s p
      _ = Real.rpow (PrimeIdeal.norm p : ℝ) (-s * 2) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg _) (-s) 2).symm
      _ ≤ Real.rpow (PrimeIdeal.norm p : ℝ) (-2) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · have hn0 : PrimeIdeal.norm p ≠ 0 := by
            rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
            exact p.ne_bot
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        · linarith
  calc
    _ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 := hrem
    _ ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖x‖ ^ 2 := by ring
    _ ≤ _ := hx2

/-- The prime-power terms of order at least two are uniformly bounded as
`s → 1⁺`. -/
private theorem cyclotomicDensity_log_sub_primeSeries_bound
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G)
    (s : ℝ) (hs : 1 < s) :
    ‖cyclotomicDensityLog m ν χ s -
        cyclotomicDensityPrimeSeries m ν χ s‖ ≤
      ∑' p : PrimeIdeal K, Real.rpow (PrimeIdeal.norm p : ℝ) (-2) := by
  have hb := cyclotomicFactorSummablePrimeRpow (K := K) 2 (by norm_num)
  have hr : Summable (fun p : PrimeIdeal K =>
      Complex.log (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹ -
        cyclotomicDensityEulerTerm m ν χ s p) := by
    apply Summable.of_norm_bounded hb
    exact cyclotomicDensity_log_sub_term_bound m ν χ s hs
  rw [cyclotomicDensityLog, cyclotomicDensityPrimeSeries,
    ← (cyclotomicDensity_log_summable m ν χ s hs).tsum_sub
      (cyclotomicDensity_term_summable m ν χ s hs)]
  exact (norm_tsum_le_tsum_norm hr.norm).trans
    (hr.norm.tsum_le_tsum
      (cyclotomicDensity_log_sub_term_bound m ν χ s hs) hb)

private theorem cyclotomicDensity_normalizer_atTop :
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
      exact sub_pos.mpr (show 1 < s from hs)
  convert tendsto_inv_nhdsGT_zero.comp hsub using 1 <;> simp [Function.comp_def]

private theorem cyclotomicDensityLog_continuousOn
    {G : Type*} [CommGroup G] [Finite G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (χ : UnitCharacter G) :
    ContinuousOn (cyclotomicDensityLog m ν χ) (Set.Ioi 1) := by
  intro s hs
  change 1 < s at hs
  let a : ℝ := (1 + s) / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a]; linarith
  have hev : ∀ᶠ t : ℝ in 𝓝 s, a < t := Ioi_mem_nhds has
  have hpoint (p : PrimeIdeal K) : Tendsto
      (fun t : ℝ => Complex.log
        (1 - cyclotomicDensityEulerTerm m ν χ t p)⁻¹)
      (𝓝 s)
      (𝓝 (Complex.log
        (1 - cyclotomicDensityEulerTerm m ν χ s p)⁻¹)) := by
    have heuler : Continuous
        (fun t : ℝ => cyclotomicDensityEulerTerm m ν χ t p) := by
      classical
      unfold cyclotomicDensityEulerTerm
      split
      · exact continuous_const
      · apply Continuous.mul continuous_const
        apply Complex.continuous_ofReal.comp
        have hn0 : (PrimeIdeal.norm p : ℝ) ≠ 0 := by
          intro h
          have h' : PrimeIdeal.norm p = 0 := by exact_mod_cast h
          rw [PrimeIdeal.norm, Ideal.absNorm_eq_zero_iff] at h'
          exact p.ne_bot h'
        exact (Real.continuous_const_rpow hn0).comp continuous_neg
    have hbase : ContinuousAt
        (fun t : ℝ => 1 - cyclotomicDensityEulerTerm m ν χ t p) s :=
      continuousAt_const.sub heuler.continuousAt
    have hslit : 1 - cyclotomicDensityEulerTerm m ν χ s p ∈
        Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one
          (z := -cyclotomicDensityEulerTerm m ν χ s p) (by
            simpa using cyclotomicDensity_norm_term_lt_one m ν χ s hs p)
    have ht := (hbase.clog hslit).neg.tendsto
    rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)]
    apply ht.congr'
    filter_upwards [Ioi_mem_nhds hs] with t ht
    have hxt := cyclotomicDensity_norm_term_lt_one m ν χ t ht p
    have hslit' : 1 - cyclotomicDensityEulerTerm m ν χ t p ∈
        Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one
          (z := -cyclotomicDensityEulerTerm m ν χ t p) (by simpa)
    exact (Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit')).symm
  have hbound : ∀ᶠ t : ℝ in 𝓝 s, ∀ p : PrimeIdeal K,
      ‖Complex.log (1 - cyclotomicDensityEulerTerm m ν χ t p)⁻¹‖ ≤
        2 * Real.rpow (PrimeIdeal.norm p : ℝ) (-a) := by
    filter_upwards [hev] with t ht p
    calc
      _ ≤ 2 * Real.rpow (PrimeIdeal.norm p : ℝ) (-t) :=
        cyclotomicDensity_logTerm_bound m ν χ t (ha.trans ht) p
      _ ≤ 2 * Real.rpow (PrimeIdeal.norm p : ℝ) (-a) := by
        gcongr
        apply Real.rpow_le_rpow_of_exponent_le
        · have hn0 : PrimeIdeal.norm p ≠ 0 := by
            rw [PrimeIdeal.norm, ne_eq, Ideal.absNorm_eq_zero_iff]
            exact p.ne_bot
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        · linarith
  have hcont : ContinuousAt (cyclotomicDensityLog m ν χ) s :=
    tendsto_tsum_of_dominated_convergence
      ((cyclotomicFactorSummablePrimeRpow (K := K) a ha).mul_left 2)
      hpoint hbound
  exact hcont.continuousWithinAt

private theorem cyclotomicDensity_exp_one_locallyConstant
    {S : Set ℝ} (d : ℝ → ℂ) (hd : ContinuousOn d S)
    (hexp : ∀ s ∈ S, Complex.exp (d s) = 1) :
    IsLocallyConstant (fun s : S => d s) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : ContinuousAt (fun s : S => d s) x :=
    (continuousOn_iff_continuous_restrict.mp hd).continuousAt
  have hev : ∀ᶠ y : S in 𝓝 x, ‖d y - d x‖ < 2 * Real.pi := by
    have ht := hcont.tendsto
    rw [Metric.tendsto_nhds] at ht
    filter_upwards [ht (2 * Real.pi) (by positivity)] with y hy
    simpa only [dist_eq_norm] using hy
  filter_upwards [hev] with y hy
  obtain ⟨n : ℤ, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    ((hexp y y.2).trans (hexp x x.2).symm)
  have hn0 : n = 0 := by
    by_contra hnzero
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hi : (1 : ℤ) ≤ |n| := Int.one_le_abs hnzero
      exact_mod_cast hi
    have hnorm : ‖d y - d x‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, add_sub_cancel_left]
      simp only [norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      rw [abs_of_pos Real.pi_pos]
      ring
    rw [hnorm] at hy
    nlinarith [Real.pi_pos]
  rw [hn0] at hn
  simpa using hn

/-- A continuous lift through `exp` of a nonvanishing function at `1` has a
finite limit on the real axis.  This is the local holomorphic-logarithm step
of blueprint §9, expressed without choosing a global logarithm. -/
private theorem cyclotomicDensity_log_tendsto_of_exp
    (D : ℝ → ℂ) (W : ℝ → ℂ)
    (hD : ContinuousOn D (Set.Ioi 1))
    (hW : ContinuousOn W (Set.Ioi 1))
    (hWat : ContinuousAt W 1) (hW1 : W 1 ≠ 0)
    (hexp : ∀ s : ℝ, 1 < s → Complex.exp (D s) = W s) :
    ∃ c : ℂ, Tendsto D (𝓝[>] (1 : ℝ)) (𝓝 c) := by
  let R : ℝ → ℂ := fun s => W s / W 1
  have hR1 : R 1 = 1 := by simp [R, hW1]
  have hRcont : ContinuousAt R 1 := hWat.div_const _
  have hnear : {s : ℝ | ‖R s - 1‖ < 1 / 2} ∈ 𝓝 (1 : ℝ) := by
    have hsub := hRcont.tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝 1) (𝓝 1))
    rw [hR1, sub_self] at hsub
    have ht := tendsto_norm.comp hsub
    exact ht (Iio_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 / 2 : ℝ)))
  obtain ⟨l, b, hlb, hbsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnear
  have hb : 1 < b := hlb.2
  let S : Set ℝ := Set.Ioo 1 b
  let B : ℝ → ℂ := fun s => Complex.log (R s)
  let z₀ : ℂ := Complex.log (W 1)
  let d : ℝ → ℂ := fun s => D s - B s - z₀
  have hRsmall (s : ℝ) (hs : s ∈ S) : ‖R s - 1‖ < 1 / 2 :=
    hbsub ⟨hlb.1.trans hs.1, hs.2⟩
  have hRslit (s : ℝ) (hs : s ∈ S) : R s ∈ Complex.slitPlane := by
    have := Complex.mem_slitPlane_of_norm_lt_one
      (z := R s - 1) ((hRsmall s hs).trans (by norm_num))
    simpa only [add_sub_cancel] using this
  have hWcontS : ContinuousOn W S :=
    hW.mono (fun s hs => hs.1)
  have hRcontS : ContinuousOn R S := by
    intro s hs
    change ContinuousWithinAt (fun t => W t / W 1) S s
    exact (hWcontS s hs).div_const _
  have hBcont : ContinuousOn B S := by
    intro s hs
    exact (hRcontS s hs).clog (hRslit s hs)
  have hdcont : ContinuousOn d S :=
    (hD.mono (fun s hs => hs.1)).sub hBcont |>.sub continuousOn_const
  have hdexp (s : ℝ) (hs : s ∈ S) : Complex.exp (d s) = 1 := by
    have hRne : R s ≠ 0 := Complex.slitPlane_ne_zero (hRslit s hs)
    have hz : Complex.exp z₀ = W 1 := Complex.exp_log hW1
    have hB : Complex.exp (B s) = R s := Complex.exp_log hRne
    dsimp [d]
    rw [Complex.exp_sub, Complex.exp_sub, hexp s hs.1, hB, hz]
    dsimp [R]
    have hWs : W s ≠ 0 := by
      rw [← hexp s hs.1]
      exact Complex.exp_ne_zero _
    field_simp [hW1, hWs]
  have hdloc := cyclotomicDensity_exp_one_locallyConstant d hdcont hdexp
  let s₀ : ℝ := (1 + b) / 2
  have hs₀ : s₀ ∈ S := by
    constructor <;> dsimp [s₀] <;> linarith
  letI : PreconnectedSpace S :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hdeq (s : ℝ) (hs : s ∈ S) : d s = d s₀ :=
    hdloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨s₀, hs₀⟩
  have hRt : Tendsto R (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    simpa only [hR1] using hRcont.tendsto.mono_left nhdsWithin_le_nhds
  have hBt : Tendsto B (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => Complex.log z) 1 := by
      simpa only [id_eq] using
        (continuousAt_id.clog Complex.one_mem_slitPlane)
    have hlog := hc.tendsto.comp hRt
    change Tendsto (fun s : ℝ => Complex.log (R s))
      (𝓝[>] (1 : ℝ)) (𝓝 0)
    simpa only [Function.comp_def, Complex.log_one] using hlog
  refine ⟨d s₀ + z₀, ?_⟩
  have hlim : Tendsto (fun x => B x + (d s₀ + z₀))
      (𝓝[>] (1 : ℝ)) (𝓝 (d s₀ + z₀)) := by
    simpa only [zero_add] using hBt.add (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => d s₀ + z₀) (𝓝[>] (1 : ℝ)) (𝓝 (d s₀ + z₀)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds hb)] with s hs hs_b
  have hds := hdeq s ⟨hs, hs_b⟩
  rw [← hds]
  dsimp [d]
  ring

private theorem cyclotomicDensity_trivial_log_asymptotic
    (D W : ℝ → ℂ) (ρ : ℂ) (hρ : ρ ≠ 0)
    (hexp : ∀ s : ℝ, 1 < s → Complex.exp (D s) = W s)
    (hres : Tendsto (fun s : ℝ => ((s - 1 : ℝ) : ℂ) * W s)
      (𝓝[>] (1 : ℝ)) (𝓝 ρ)) :
    Tendsto (fun s : ℝ => (D s).re - dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.log ‖ρ‖)) := by
  have hlogres : Tendsto
      (fun s : ℝ => Real.log ‖((s - 1 : ℝ) : ℂ) * W s‖)
      (𝓝[>] (1 : ℝ)) (𝓝 (Real.log ‖ρ‖)) := by
    exact (tendsto_norm.comp hres).log (norm_ne_zero_iff.mpr hρ)
  apply hlogres.congr'
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, hlt] with s hs hs2
  have hWne : W s ≠ 0 := by
    rw [← hexp s hs]
    exact Complex.exp_ne_zero _
  have hDlog : (D s).re = Real.log ‖W s‖ := by
    rw [← hexp s hs, Complex.norm_exp, Real.log_exp]
  rw [hDlog]
  unfold dirichletNormalizer
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hs), Real.log_mul (sub_ne_zero.mpr hs.ne')
      (norm_ne_zero_iff.mpr hWne), one_div, Real.log_inv]
  ring

private theorem cyclotomicDensity_tendsto_zero_of_tendsto
    (a : ℂ) (D : ℝ → ℂ) (c : ℂ)
    (hD : Tendsto D (𝓝[>] (1 : ℝ)) (𝓝 c)) :
    Tendsto (fun s : ℝ => (a * D s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hnum : Tendsto (fun s : ℝ => (a * D s).re)
      (𝓝[>] (1 : ℝ)) (𝓝 ((a * c).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul hD))
  exact hnum.div_atTop cyclotomicDensity_normalizer_atTop

private theorem cyclotomicDensity_trivial_ratio
    (D : ℝ → ℂ) (c : ℝ)
    (hD : Tendsto (fun s : ℝ => (D s).re - dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 c)) :
    Tendsto (fun s : ℝ => (D s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hz := (hD.div_atTop cyclotomicDensity_normalizer_atTop).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (1 : ℝ)) (𝓝 1))
  have hz' : Tendsto
      (fun x => ((D x).re - dirichletNormalizer x) /
        dirichletNormalizer x + 1)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by simpa only [zero_add] using hz
  apply hz'.congr'
  have hne : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), dirichletNormalizer s ≠ 0 :=
    cyclotomicDensity_normalizer_atTop.eventually (eventually_ne_atTop 0)
  filter_upwards [hne] with s hs
  field_simp
  ring

private theorem cyclotomicDensity_nontrivial_log_tendsto
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    [IsMulCommutative (Gal(M/K))]
    (χ : UnitCharacter (Gal(M/K))) (hχ : χ ≠ 1) :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    ∃ c : ℂ, Tendsto (cyclotomicDensityLog m ν χ)
      (𝓝[>] (1 : ℝ)) (𝓝 c) := by
  classical
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  have hν : Function.Surjective ν :=
    cyclotomicIdealMap_surjective (M := M) (F := F) n m hn hmod hram
  obtain ⟨W, hWan, hWeq⟩ :=
    cyclotomicWeberAlongNontrivialContinuation m ν hν χ hχ
  obtain ⟨W', hW'eq, hW'an, hW'ne⟩ :=
    cyclotomic_weberL_ne_zero_at_one (M := M) (F := F)
      n m hn hmod hram χ hχ
  have hstrip (s : ℝ) (hs : 1 ≤ s) :
      1 - 1 / (Module.finrank ℚ K : ℝ) < (s : ℂ).re := by
    simp only [Complex.ofReal_re]
    have hd : (0 : ℝ) < Module.finrank ℚ K := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    have hi : 0 < 1 / (Module.finrank ℚ K : ℝ) := one_div_pos.mpr hd
    linarith
  have hWcont : ContinuousOn (fun s : ℝ => W (s : ℂ)) (Set.Ioi 1) := by
    intro s hs
    have ha := (hWan (s : ℂ) (hstrip s hs.le)).continuousAt
    exact (ha.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hWat : ContinuousAt (fun s : ℝ => W (s : ℂ)) 1 := by
    have ht := (hWan (1 : ℂ) (hstrip 1 le_rfl)).continuousAt.comp_of_eq
      (x := (1 : ℝ)) Complex.continuous_ofReal.continuousAt (by norm_num)
    simpa only [Function.comp_def] using ht
  have hW'at : ContinuousAt (fun s : ℝ => W' (s : ℂ)) 1 := by
    have ht := hW'an.continuousAt.comp_of_eq
      (x := (1 : ℝ)) Complex.continuous_ofReal.continuousAt (by norm_num)
    simpa only [Function.comp_def] using ht
  have hEq : (fun s : ℝ => W (s : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun s : ℝ => W' (s : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hWeq (s : ℂ) (by simpa using hs), hW'eq (s : ℂ) (by simpa using hs)]
  have hWone : W 1 = W' 1 :=
    tendsto_nhds_unique_of_eventuallyEq
      (hWat.tendsto.mono_left nhdsWithin_le_nhds)
      (hW'at.tendsto.mono_left nhdsWithin_le_nhds) hEq
  have hWne : W 1 ≠ 0 := hWone ▸ hW'ne
  apply cyclotomicDensity_log_tendsto_of_exp
    (cyclotomicDensityLog m ν χ) (fun s : ℝ => W (s : ℂ))
    (cyclotomicDensityLog_continuousOn m ν χ) hWcont hWat hWne
  intro s hs
  rw [cyclotomicDensity_exp_log m ν χ s hs, hWeq (s : ℂ) (by simpa)]

private theorem cyclotomicDensity_trivial_log_ratio
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    [IsMulCommutative (Gal(M/K))] :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    Tendsto (fun s : ℝ =>
      (cyclotomicDensityLog m ν 1 s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  classical
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  obtain ⟨W, ρ, hρ, hWeq, hres⟩ :=
    cyclotomicWeberAlongOneContinuation m ν
  have hcoe : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact_mod_cast ne_of_gt hx
  have hresR : Tendsto (fun s : ℝ => ((s - 1 : ℝ) : ℂ) * W s)
      (𝓝[>] (1 : ℝ)) (𝓝 ρ) := by
    convert hres.comp hcoe using 1
    funext s
    push_cast
    rfl
  have hasym := cyclotomicDensity_trivial_log_asymptotic
    (cyclotomicDensityLog m ν 1) (fun s : ℝ => W s) ρ hρ
    (fun s hs => by
      rw [cyclotomicDensity_exp_log m ν 1 s hs,
        hWeq (s : ℂ) (by simpa)]) hresR
  exact cyclotomicDensity_trivial_ratio _ _ hasym

private theorem cyclotomicDensity_character_orthogonality
    {G : Type*} [CommGroup G] [Finite G] [DecidableEq G]
    [Fintype (UnitCharacter G)] (x : G) :
    ∑ χ : UnitCharacter G, (χ x : ℂ) =
      if x = 1 then (Nat.card G : ℂ) else 0 := by
  classical
  by_cases hx : x = 1
  · subst x
    simp only [map_one, Units.val_one, if_pos]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_eq_nat_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  · rw [if_neg hx]
    obtain ⟨ψ : UnitCharacter G, hψ⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
    let e : UnitCharacter G ≃ UnitCharacter G := Equiv.mulLeft ψ
    have hre : (∑ χ : UnitCharacter G, (χ x : ℂ)) =
        ∑ χ : UnitCharacter G, ((ψ * χ) x : ℂ) := by
      exact (e.sum_comp (fun χ : UnitCharacter G => (χ x : ℂ))).symm
    have hfac : (∑ χ : UnitCharacter G, ((ψ * χ) x : ℂ)) =
        (ψ x : ℂ) * ∑ χ : UnitCharacter G, (χ x : ℂ) := by
      simp_rw [MonoidHom.mul_apply, Units.val_mul]
      rw [Finset.mul_sum]
    rw [hfac] at hre
    have hz : (1 - (ψ x : ℂ)) * ∑ χ : UnitCharacter G, (χ x : ℂ) = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]
      exact hre
    apply (mul_eq_zero.mp hz).resolve_left
    apply sub_ne_zero.mpr
    intro h
    apply hψ
    exact Units.ext h.symm

private def cyclotomicDensityGoodPrimeSet
    {G : Type*} [CommGroup G] (m : RayModulus K)
    (ν : RayClassGroup m →* G) (g : G) : Set (PrimeIdeal K) :=
  {p | ∃ hp : ¬p.asIdeal ∣ m.finite,
    ν (cyclotomicDensityPrimeClass m p hp) = g}

private theorem cyclotomicDensity_orthogonality_series
    {G : Type*} [CommGroup G] [Finite G] [DecidableEq G]
    [Fintype (UnitCharacter G)] (m : RayModulus K) (ν : RayClassGroup m →* G) (g : G)
    (s : ℝ) (hs : 1 < s) :
    ∑ χ : UnitCharacter G,
        (χ g : ℂ)⁻¹ * cyclotomicDensityPrimeSeries m ν χ s =
      (Nat.card G : ℂ) *
        (dirichletPrimeSum (cyclotomicDensityGoodPrimeSet m ν g) s : ℂ) := by
  classical
  have hsum (χ : UnitCharacter G) : Summable (fun p : PrimeIdeal K =>
      (χ g : ℂ)⁻¹ * cyclotomicDensityEulerTerm m ν χ s p) :=
    (cyclotomicDensity_term_summable m ν χ s hs).mul_left _
  unfold cyclotomicDensityPrimeSeries
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ (_ : χ ∈
    (Finset.univ : Finset (UnitCharacter G))) => hsum χ)]
  unfold dirichletPrimeSum
  rw [Complex.ofReal_tsum]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  by_cases hp : p.asIdeal ∣ m.finite
  · have hnot : p ∉ cyclotomicDensityGoodPrimeSet m ν g := by
      rintro ⟨hp', -⟩
      exact hp' hp
    simp [cyclotomicDensityEulerTerm, hp, hnot]
  · let c := cyclotomicDensityPrimeClass m p hp
    have hchar (χ : UnitCharacter G) :
        (χ g : ℂ)⁻¹ * cyclotomicDensityEulerTerm m ν χ s p =
          (χ (g⁻¹ * ν c) : ℂ) *
            (Real.rpow (PrimeIdeal.norm p : ℝ) (-s) : ℂ) := by
      rw [cyclotomicDensityEulerTerm, dif_neg hp]
      dsimp [c]
      rw [map_mul, map_inv, Units.val_mul]
      change (↑(χ g) : ℂ)⁻¹ *
          ((↑(χ (ν (cyclotomicDensityPrimeClass m p hp))) : ℂ) *
            (Real.rpow (PrimeIdeal.norm p : ℝ) (-s) : ℂ)) =
        (↑((χ g)⁻¹) : ℂ) *
          (↑(χ (ν (cyclotomicDensityPrimeClass m p hp))) : ℂ) *
            (Real.rpow (PrimeIdeal.norm p : ℝ) (-s) : ℂ)
      rw [Units.val_inv_eq_inv_val]
      ac_rfl
    simp_rw [hchar, ← Finset.sum_mul]
    rw [cyclotomicDensity_character_orthogonality]
    by_cases heq : ν c = g
    · have hone : g⁻¹ * ν c = 1 := by simp [heq]
      rw [if_pos hone]
      have hmem : p ∈ cyclotomicDensityGoodPrimeSet m ν g := ⟨hp, heq⟩
      rw [if_pos hmem]
    · have hne : g⁻¹ * ν c ≠ 1 := by
        intro h
        apply heq
        exact (inv_mul_eq_one.mp h).symm
      rw [if_neg hne]
      have hnot : p ∉ cyclotomicDensityGoodPrimeSet m ν g := by
        rintro ⟨hp', heq'⟩
        have hproof : hp' = hp := Subsingleton.elim _ _
        subst hp'
        exact heq heq'
      rw [if_neg hnot]
      simp

private theorem cyclotomicDensity_bounded_re_div_normalizer
    (E : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖E s‖ ≤ C) :
    Tendsto (fun s : ℝ => (E s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < dirichletNormalizer s :=
    cyclotomicDensity_normalizer_atTop.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
    (show ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |(E s).re / dirichletNormalizer s| ≤ C / dirichletNormalizer s by
      filter_upwards [hE, hpos] with s hs hp
      rw [abs_div, abs_of_pos hp]
      exact div_le_div_of_nonneg_right
        ((Complex.abs_re_le_norm (E s)).trans hs) hp.le)
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => C)
    (𝓝[>] (1 : ℝ)) (𝓝 C)).div_atTop cyclotomicDensity_normalizer_atTop

private theorem cyclotomicDensity_goodPrimeSet
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    [IsMulCommutative (Gal(M/K))] (g : Gal(M/K)) :
    let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
    HasDirichletDensity (cyclotomicDensityGoodPrimeSet m ν g)
      (1 / (Nat.card (Gal(M/K)) : ℝ)) := by
  classical
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  letI := Fintype.ofFinite (UnitCharacter (Gal(M/K)))
  let coeff : UnitCharacter (Gal(M/K)) → ℂ := fun χ => (χ g : ℂ)⁻¹
  let D : UnitCharacter (Gal(M/K)) → ℝ → ℂ := fun χ =>
    cyclotomicDensityLog m ν χ
  let P : UnitCharacter (Gal(M/K)) → ℝ → ℂ := fun χ =>
    cyclotomicDensityPrimeSeries m ν χ
  let LD : ℝ → ℂ := fun s => ∑ χ, coeff χ * D χ s
  let LP : ℝ → ℂ := fun s => ∑ χ, coeff χ * P χ s
  have hχ (χ : UnitCharacter (Gal(M/K))) :
      Tendsto (fun s : ℝ => (coeff χ * D χ s).re / dirichletNormalizer s)
        (𝓝[>] (1 : ℝ)) (𝓝 (if χ = 1 then 1 else 0)) := by
    by_cases htriv : χ = 1
    · subst χ
      simpa [coeff, D] using
        cyclotomicDensity_trivial_log_ratio (M := M) (F := F)
          n m hn hmod hram
    · obtain ⟨c, hc⟩ := cyclotomicDensity_nontrivial_log_tendsto
        (M := M) (F := F) n m hn hmod hram χ htriv
      simpa [htriv, coeff, D] using
        cyclotomicDensity_tendsto_zero_of_tendsto (coeff χ) (D χ) c hc
  have hLD : Tendsto (fun s : ℝ => (LD s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have hsum := tendsto_finsetSum Finset.univ (fun χ _ => hχ χ)
    have hone : (∑ χ : UnitCharacter (Gal(M/K)),
        if χ = 1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single (1 : UnitCharacter (Gal(M/K)))]
      · simp
      · intro χ hχmem hχne
        simp [hχne]
      · simp
    rw [hone] at hsum
    apply hsum.congr'
    filter_upwards with s
    change (∑ c : UnitCharacter (Gal(M/K)),
        (coeff c * D c s).re / dirichletNormalizer s) =
      (∑ χ : UnitCharacter (Gal(M/K)), coeff χ * D χ s).re /
        dirichletNormalizer s
    calc
      _ = (∑ c : UnitCharacter (Gal(M/K)), (coeff c * D c s).re) /
          dirichletNormalizer s :=
        (Finset.sum_div Finset.univ
          (fun c : UnitCharacter (Gal(M/K)) => (coeff c * D c s).re)
          (dirichletNormalizer s)).symm
      _ = _ := by
        congr 1
        exact (map_sum Complex.reAddGroupHom
          (fun c : UnitCharacter (Gal(M/K)) => coeff c * D c s)
          Finset.univ).symm
  let C : ℝ := ∑' p : PrimeIdeal K,
    Real.rpow (PrimeIdeal.norm p : ℝ) (-2)
  have hC : 0 ≤ C := tsum_nonneg fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcoeff (χ : UnitCharacter (Gal(M/K))) : ‖coeff χ‖ = 1 := by
    have hb := (((Units.coeHom ℂ).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite g)).norm_eq_one
    change ‖(χ g : ℂ)‖ = 1 at hb
    dsimp [coeff]
    rw [norm_inv, hb, inv_one]
  have herrorBound : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖LD s - LP s‖ ≤
      Fintype.card (UnitCharacter (Gal(M/K))) * C := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [show LD s - LP s = ∑ χ : UnitCharacter (Gal(M/K)),
        coeff χ * (D χ s - P χ s) by
      simp only [LD, LP]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro χ hχmem
      ring]
    calc
      ‖∑ χ : UnitCharacter (Gal(M/K)), coeff χ * (D χ s - P χ s)‖ ≤
          ∑ χ : UnitCharacter (Gal(M/K)), ‖coeff χ * (D χ s - P χ s)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _χ : UnitCharacter (Gal(M/K)), C := by
        apply Finset.sum_le_sum
        intro χ hχmem
        rw [norm_mul, hcoeff, one_mul]
        exact cyclotomicDensity_log_sub_primeSeries_bound m ν χ s hs
      _ = Fintype.card (UnitCharacter (Gal(M/K))) * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have herr := cyclotomicDensity_bounded_re_div_normalizer
    (fun s => LD s - LP s)
    (Fintype.card (UnitCharacter (Gal(M/K))) * C)
    (mul_nonneg (Nat.cast_nonneg _) hC) herrorBound
  have hLP : Tendsto (fun s : ℝ => (LP s).re / dirichletNormalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have h := hLD.sub herr
    have h' : Tendsto (fun x => (LD x).re / dirichletNormalizer x -
        (LD x - LP x).re / dirichletNormalizer x)
        (𝓝[>] (1 : ℝ)) (𝓝 1) := by simpa only [sub_zero] using h
    apply h'.congr'
    filter_upwards with s
    simp only [Complex.sub_re]
    ring
  have horth : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      LP s = (Nat.card (Gal(M/K)) : ℂ) *
        (dirichletPrimeSum (cyclotomicDensityGoodPrimeSet m ν g) s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact cyclotomicDensity_orthogonality_series m ν g s hs
  unfold HasDirichletDensity
  have hcard : (Nat.card (Gal(M/K)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Gal(M/K))).ne'
  have hscaled : Tendsto (fun s : ℝ =>
      (Nat.card (Gal(M/K)) : ℝ) *
        (dirichletPrimeSum (cyclotomicDensityGoodPrimeSet m ν g) s /
          dirichletNormalizer s))
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    apply hLP.congr'
    filter_upwards [horth] with s hs
    rw [hs]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have ht := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ((Nat.card (Gal(M/K)) : ℝ))⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 ((Nat.card (Gal(M/K)) : ℝ)⁻¹))).mul hscaled
  have hfinal : Tendsto (fun s : ℝ =>
      dirichletPrimeSum (cyclotomicDensityGoodPrimeSet m ν g) s /
        dirichletNormalizer s) (𝓝[>] (1 : ℝ))
      (𝓝 ((Nat.card (Gal(M/K)) : ℝ)⁻¹)) := by
    convert ht using 1
    · funext s
      field_simp
    · simp
  simpa only [ν, inv_eq_one_div] using hfinal

/-- Blueprint §9 (`cyclotomic_chebotarev_dirichletDensity_of_modulus`): the
selected-modulus form of cyclotomic Chebotarev for Dirichlet density. -/
theorem cyclotomic_chebotarev_dirichletDensity_of_modulus
    (n : ℕ) (m : RayModulus K)
    [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (hmod : IsCyclotomicModulus n m)
    (hram : RamificationSupported (M := M) m)
    (g : Gal(M/K)) :
    HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := M) g)
      (1 / (Nat.card (Gal(M/K)) : ℝ)) := by
  classical
  letI : IsAbelianGalois K F :=
    IsCyclotomicExtension.isAbelianGalois {n} K F
  letI : IsAbelianGalois K M := IsAbelianGalois.tower_bot K M F
  let ν := cyclotomicIdealMap (M := M) (F := F) n m hn hmod hram
  let S := cyclotomicDensityGoodPrimeSet m ν g
  let T := frobeniusElementPrimeSet (K := K) (L := M) g
  have hS : HasDirichletDensity S
      (1 / (Nat.card (Gal(M/K)) : ℝ)) := by
    simpa only [S, ν] using
      cyclotomicDensity_goodPrimeSet (M := M) (F := F)
        n m hn hmod hram g
  have hout (p : PrimeIdeal K) (hp : ¬p.asIdeal ∣ m.finite) :
      p ∈ S ↔ p ∈ T := by
    have hunr : IsUnramifiedPrime (L := M) p := by
      intro Q hQp
      by_contra hQ
      apply hp
      have hd := hram Q hQ
      simpa only [hQp.over] using hd
    constructor
    · rintro ⟨hp', heq⟩
      have hproof : hp' = hp := Subsingleton.elim _ _
      subst hp'
      obtain ⟨Qideal, hQmax, hQp⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral
          (S := NumberField.RingOfIntegers M) p.asIdeal
      let Q : PrimeIdeal M :=
        ⟨Qideal, hQmax.isPrime, by
          intro hbot
          apply p.ne_bot
          have hover := hQp.over
          rw [hbot] at hover
          simpa using hover⟩
      have hQlies : Q.asIdeal.LiesOver p.asIdeal := hQp
      refine ⟨hunr, Q, hQlies, ?_⟩
      rw [← heq]
      exact (cyclotomicIdealMap_on_prime (M := M) (F := F)
        n m hn hmod hram p hp
        (cyclotomicDensityPrimeClass m p hp)
        (cyclotomicDensityPrimeClass_isClass m p hp) Q hQlies).symm
    · rintro ⟨hunr', Q, hQp, hQg⟩
      refine ⟨hp, ?_⟩
      rw [cyclotomicIdealMap_on_prime (M := M) (F := F)
        n m hn hmod hram p hp
        (cyclotomicDensityPrimeClass m p hp)
        (cyclotomicDensityPrimeClass_isClass m p hp) Q hQp, hQg]
  let B : Set (PrimeIdeal K) := {p | p.asIdeal ∣ m.finite}
  have hB : B.Finite := by
    exact Ideal.finite_factors m.finite_ne
  have hdiff : symmetricDifference S T ⊆ B := by
    intro p hpST
    by_contra hpB
    have hpaway : ¬p.asIdeal ∣ m.finite := hpB
    rcases hpST with hpST | hpTS
    · exact hpST.2 ((hout p hpaway).mp hpST.1)
    · exact hpTS.2 ((hout p hpaway).mpr hpTS.1)
  apply hS.congr_of_symmetricDifference_zero
  exact finite_primeSet_hasDirichletDensity_zero (hB.subset hdiff)

/-- Blueprint Theorem 6.6 and §9
(`cyclotomic_chebotarev_dirichletDensity`): cyclotomic Chebotarev for
Dirichlet density, with the auxiliary modulus existentially eliminated. Its
proof needs nonvanishing only at `s=1`. -/
theorem cyclotomic_chebotarev_dirichletDensity
    (n : ℕ) [IsCyclotomicExtension {n} K F]
    (hn : 1 ≤ n) (g : Gal(M/K)) :
    HasDirichletDensity
      (frobeniusElementPrimeSet (K := K) (L := M) g)
      (1 / (Nat.card (Gal(M/K)) : ℝ)) := by
  obtain ⟨m, hmod, hram⟩ := exists_cyclotomicModulus (K := K) (M := M) n hn
  exact cyclotomic_chebotarev_dirichletDensity_of_modulus
    (M := M) (F := F) n m hn hmod hram g

/-- Blueprint §9 (`allPrimes_dirichletDensity_one`), obtained by taking the
trivial cyclotomic extension. -/
theorem allPrimes_dirichletDensity_one :
    HasDirichletDensity (Set.univ : Set (PrimeIdeal K)) 1 := by
  letI : IsCyclotomicExtension {1} K K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
      (A := K) (B := K)
      (fun x => ⟨x, (Algebra.algebraMap_self_apply x).symm⟩)
  have h := cyclotomic_chebotarev_dirichletDensity
    (K := K) (M := K) (F := K) 1 (by omega) (1 : Gal(K/K))
  have hset :
      frobeniusElementPrimeSet (K := K) (L := K) (1 : Gal(K/K)) = Set.univ := by
    ext p
    simp only [frobeniusElementPrimeSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    constructor
    · intro P hP
      change Algebra.FormallyUnramified (NumberField.RingOfIntegers K)
        (Localization.AtPrime P.asIdeal)
      infer_instance
    · let P : PrimeIdeal K := p
      refine ⟨P, ⟨rfl⟩, ?_⟩
      exact Subsingleton.elim _ _
  rw [hset] at h
  have hcard : Nat.card Gal(K/K) = 1 := Nat.card_unique
  rw [hcard] at h
  norm_num at h ⊢
  exact h

end NU.Chebotarev
