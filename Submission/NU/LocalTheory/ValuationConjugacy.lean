import Submission.NU.LocalTheory.NumberField.ValuationBridge
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Conjugacy of algebraic nonarchimedean valuations

This file supplies the valuation-theoretic conjugacy input used to prove
Henselianity of decomposition fields.  A valuation is extended by maximality
of local subrings.  Conjugacy is then reduced to transitivity on center primes
in the integral closure and recovered at finite number-field subextensions.
-/

open IsDedekindDomain
open scoped NumberField Pointwise

namespace NU.LocalTheory

noncomputable section

private theorem ringOfIntegers_le_valuationSubring
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    ∀ a : 𝓞 F, (a : F) ∈ A := by
  intro a
  apply (Subring.isIntegrallyClosed_iff.mp
    (inferInstance : IsIntegrallyClosed A))
  exact a.2.tower_top

private def valuationIntegralCenter
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal A).comap
    ((algebraMap (𝓞 F) F).codRestrict A
      (ringOfIntegers_le_valuationSubring A))

private instance valuationIntegralCenter_isPrime
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    (valuationIntegralCenter A).IsPrime :=
  (IsLocalRing.maximalIdeal A).comap_isPrime _

private theorem valuationIntegralCenter_primeValuationSubring
    {F : Type*} [Field F] [NumberField F] (v : FinitePlace F) :
    valuationIntegralCenter (primeValuationSubring v) = v.asIdeal := by
  change valuationIntegralCenter
    (HeightOneSpectrum.valuationSubringAtPrime F v) = v.asIdeal
  apply Ideal.ext
  intro x
  change (⟨(x : F), ringOfIntegers_le_valuationSubring
      (HeightOneSpectrum.valuationSubringAtPrime F v) x⟩ :
        HeightOneSpectrum.valuationSubringAtPrime F v) ∈
      IsLocalRing.maximalIdeal
        (HeightOneSpectrum.valuationSubringAtPrime F v) ↔ x ∈ v.asIdeal
  rw [show (⟨(x : F), ringOfIntegers_le_valuationSubring
      (HeightOneSpectrum.valuationSubringAtPrime F v) x⟩ :
        HeightOneSpectrum.valuationSubringAtPrime F v) =
      algebraMap (𝓞 F)
        (HeightOneSpectrum.valuationSubringAtPrime F v) x by
    apply Subtype.ext
    rfl]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (HeightOneSpectrum.valuationSubringAtPrime F v) v.asIdeal x

private def valuationComapMap
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : A.comap f →+* A where
  toFun x := ⟨f x, x.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

private theorem valuationComapMap_isLocal
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : IsLocalHom (valuationComapMap f A) := by
  apply IsLocalHom.mk
  intro x hx
  have hfx0 : f (x : F) ≠ 0 := by
    intro hzero
    apply IsUnit.ne_zero hx
    apply Subtype.ext
    exact hzero
  have hx0 : (x : F) ≠ 0 := (map_ne_zero f).mp hfx0
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hyval : (y : E) = (f (x : F))⁻¹ := by
    apply (mul_left_cancel₀ hfx0)
    have hy' := congrArg Subtype.val hy
    change f (x : F) * (y : E) = 1 at hy'
    rw [hy', mul_inv_cancel₀ hfx0]
  let y' : A.comap f := ⟨(x : F)⁻¹, by
    change f ((x : F)⁻¹) ∈ A
    rw [map_inv₀, ← hyval]
    exact y.property⟩
  exact isUnit_iff_exists_inv.mpr ⟨y', by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0⟩

private theorem valuationIntegralCenter_comap
    {F E : Type*} [Field F] [Field E] [CharZero F] [CharZero E]
    (f : F →+* E) (A : ValuationSubring E) :
    valuationIntegralCenter (A.comap f) =
      (valuationIntegralCenter A).comap
        (NumberField.RingOfIntegers.mapRingHom f) := by
  letI : IsLocalHom (valuationComapMap f A) :=
    valuationComapMap_isLocal f A
  apply Ideal.ext
  intro x
  change (⟨(x : F), ringOfIntegers_le_valuationSubring
      (A.comap f) x⟩ : A.comap f) ∈
        IsLocalRing.maximalIdeal (A.comap f) ↔
    (⟨f (x : F), ringOfIntegers_le_valuationSubring A
      (NumberField.RingOfIntegers.mapRingHom f x)⟩ : A) ∈
        IsLocalRing.maximalIdeal A
  have hm := IsLocalRing.maximalIdeal_comap (valuationComapMap f A)
  have hx := (Ideal.ext_iff.mp hm
    ⟨(x : F), ringOfIntegers_le_valuationSubring (A.comap f) x⟩).symm
  change _ ↔ valuationComapMap f A
    ⟨(x : F), ringOfIntegers_le_valuationSubring (A.comap f) x⟩ ∈
      IsLocalRing.maximalIdeal A at hx
  exact hx

private def valuationSubringSmulEquiv
    {G F : Type*} [Group G] [Field F] [MulSemiringAction G F]
    (g : G) (A : ValuationSubring F) : A ≃+* (g • A : ValuationSubring F) where
  toFun x := ⟨g • (x : F),
    ValuationSubring.smul_mem_pointwise_smul g (x : F) A x.property⟩
  invFun x := ⟨g⁻¹ • (x : F),
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)
  map_mul' x y := by ext; exact MulSemiringAction.smul_mul g (x : F) (y : F)

private theorem valuationIntegralCenter_smul
    {G F : Type*} [Group G] [Field F] [CharZero F]
    [MulSemiringAction G F] (g : G) (A : ValuationSubring F) :
    valuationIntegralCenter (g • A) = g • valuationIntegralCenter A := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change (⟨(x : F), ringOfIntegers_le_valuationSubring (g • A) x⟩ :
      (g • A : ValuationSubring F)) ∈
        IsLocalRing.maximalIdeal (g • A : ValuationSubring F) ↔
    (⟨((g⁻¹ • x : 𝓞 F) : F), ringOfIntegers_le_valuationSubring A (g⁻¹ • x)⟩ :
      A) ∈ IsLocalRing.maximalIdeal A
  simp only [IsLocalRing.mem_maximalIdeal]
  apply not_congr
  let e := valuationSubringSmulEquiv g A
  let y : A := ⟨((g⁻¹ • x : 𝓞 F) : F),
    ringOfIntegers_le_valuationSubring A (g⁻¹ • x)⟩
  have he := isUnit_map_iff e y
  have hey : e y = (⟨(x : F),
      ringOfIntegers_le_valuationSubring (g • A) x⟩ :
        (g • A : ValuationSubring F)) := by
    apply Subtype.ext
    change g • (g⁻¹ • (x : F)) = (x : F)
    simp
  rw [← hey]
  exact he

private theorem isUnit_mk_valuationSubring_iff
    {F : Type*} [Field F] (A : ValuationSubring F) (x : F) (hx : x ∈ A) :
    IsUnit (⟨x, hx⟩ : A) ↔ x ≠ 0 ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have hy' := congrArg Subtype.val hy
    change x * (y : F) = 1 at hy'
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hy'
      exact zero_ne_one hy'
    refine ⟨hx0, ?_⟩
    have heq : (y : F) = x⁻¹ := by
      apply (mul_left_cancel₀ hx0)
      rw [hy', mul_inv_cancel₀ hx0]
    rw [← heq]
    exact y.property
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

private theorem valuationSubring_eq_of_integralCenter_eq
    (K : Type*) {F : Type*} [Field K] [NumberField K]
    [Field F] [CharZero F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (A B : ValuationSubring F)
    (hA : A.comap (algebraMap K F) ≠ ⊤)
    (hB : B.comap (algebraMap K F) ≠ ⊤)
    (hcenter : valuationIntegralCenter A = valuationIntegralCenter B) :
    A = B := by
  apply ValuationSubring.ext
  intro x
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  letI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (S := {x})
      (fun y _ => Algebra.IsIntegral.isIntegral y)
  letI : NumberField L := NumberField.of_module_finite K L
  let AL : ValuationSubring L := A.comap L.val.toRingHom
  let BL : ValuationSubring L := B.comap L.val.toRingHom
  have hAL : AL ≠ ⊤ := by
    intro htop
    apply hA
    apply ValuationSubring.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      have hy : algebraMap K L y ∈ AL := by rw [htop]; trivial
      exact hy
  have hBL : BL ≠ ⊤ := by
    intro htop
    apply hB
    apply ValuationSubring.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      have hy : algebraMap K L y ∈ BL := by rw [htop]; trivial
      exact hy
  obtain ⟨v, hv, _⟩ := numberField_valuations AL hAL
  obtain ⟨w, hw, _⟩ := numberField_valuations BL hBL
  have hcenterL : valuationIntegralCenter AL = valuationIntegralCenter BL := by
    dsimp only [AL, BL]
    rw [valuationIntegralCenter_comap,
      valuationIntegralCenter_comap, hcenter]
  have hvw : v = w := by
    apply HeightOneSpectrum.ext
    rw [← valuationIntegralCenter_primeValuationSubring v,
      ← valuationIntegralCenter_primeValuationSubring w,
      ← hv, ← hw, hcenterL]
  have hAB : AL = BL := by rw [hv, hw, hvw]
  let y : L := ⟨x, IntermediateField.subset_adjoin K {x}
    (Set.mem_singleton x)⟩
  have hy := ValuationSubring.ext_iff.mp hAB y
  exact hy

/-- A valuation subring extends along every field embedding. -/
theorem exists_valuationSubring_extension
    {E F : Type*} [Field E] [Field F] (f : E →+* F)
    (B : ValuationSubring E) :
    ∃ A : ValuationSubring F, A.comap f = B := by
  let S : LocalSubring F := LocalSubring.map f B.toLocalSubring
  obtain ⟨A, hSA⟩ := S.exists_le_valuationSubring
  let e : B →+* S.toSubring :=
    { toFun := fun x => ⟨f x, by
        rw [LocalSubring.map_toSubring]
        exact ⟨x, x.property, rfl⟩⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := fun x y => by ext; exact map_add f (x : E) (y : E)
      map_mul' := fun x y => by ext; exact map_mul f (x : E) (y : E) }
  have he : Function.Surjective e := by
    intro y
    have hy : (y : F) ∈ Subring.map f B.toSubring := by
      simpa [S, LocalSubring.map_toSubring] using y.property
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    simpa [e] using hxy
  let i : S.toSubring →+* A := Subring.inclusion hSA.1
  letI : IsLocalHom e := IsLocalHom.of_surjective e he
  letI : IsLocalHom i := hSA.2
  let d : B →+* A := i.comp e
  letI : IsLocalHom d := RingHom.isLocalHom_comp i e
  have hBA : B.toLocalSubring ≤ (A.comap f).toLocalSubring := by
    let j : B →+* A.comap f :=
      { toFun := fun x => ⟨x, by
          apply hSA.1
          simpa [e] using (e x).property⟩
        map_zero' := rfl
        map_one' := rfl
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl }
    have hj : IsLocalHom j := by
      apply IsLocalHom.mk
      intro x hx
      have hu := hx.map (valuationComapMap f A)
      have hdu : IsUnit (d x) := by
        convert hu using 1
        apply Subtype.ext
        rfl
      exact (isUnit_map_iff d x).mp hdu
    exact ⟨fun x hx => by
      apply hSA.1
      simpa [e] using (e ⟨x, hx⟩).property, hj⟩
  have hlocal := B.isMax_toLocalSubring.eq_of_le hBA
  refine ⟨A, ?_⟩
  apply ValuationSubring.toSubring_injective
  exact (congrArg LocalSubring.toSubring hlocal).symm

/-- Two nontrivial algebraic valuations agreeing on an intermediate field
are conjugate by an automorphism over that field. -/
theorem exists_smul_of_valuationSubring_comap_eq
    (K : Type*) {F : Type*} [Field K] [NumberField K]
    [Field F] [CharZero F] [Algebra K F] [Algebra.IsAlgebraic K F]
    [IsAlgClosed F] (Z : IntermediateField K F)
    (A B : ValuationSubring F)
    (hA : A.comap (algebraMap K F) ≠ ⊤)
    (hB : B.comap (algebraMap K F) ≠ ⊤)
    (hcomap : A.comap Z.val.toRingHom = B.comap Z.val.toRingHom) :
    ∃ σ : Gal(F / Z), B = σ • A := by
  letI : IsAlgClosure Z F := IsAlgClosure.mk inferInstance inferInstance
  letI : Normal Z F := IsAlgClosure.normal Z F
  letI : IsGalois Z F := IsGalois.mk
  let R := 𝓞 F
  let G := Gal(F / Z)
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : ContinuousSMul G R :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun x => by
      have hx := stabilizer_isOpen_of_isIntegral (K := Z) (x : F)
      have heq : (MulAction.stabilizer G x : Set G) =
          (MulAction.stabilizer Gal(F / Z) (x : F) : Set Gal(F / Z)) := by
        ext g
        change (g • x = x) ↔ (g • (x : F) = (x : F))
        constructor
        · exact fun h => congrArg Subtype.val h
        · intro h
          apply Subtype.ext
          exact h
      rw [heq]
      exact hx
  let R₀ := FixedPoints.subring R G
  letI : Algebra R₀ R := (Subring.subtype R₀).toAlgebra
  letI : SMulCommClass G R₀ R :=
    { smul_comm := fun g a x => by
        change g • ((a : R) * x) = (a : R) * (g • x)
        calc
          _ = (g • (a : R)) * (g • x) :=
            MulSemiringAction.smul_mul g (a : R) x
          _ = _ := by rw [a.property g] }
  letI : Algebra.IsInvariant R₀ R G :=
    { isInvariant := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }
  let P : Ideal R := valuationIntegralCenter A
  let Q : Ideal R := valuationIntegralCenter B
  have hunder : P.under R₀ = Q.under R₀ := by
    apply Ideal.ext
    intro x
    let xf : F := ((x : R) : F)
    have hfixed : ∀ g : G, g xf = xf := by
      intro g
      have hx := congrArg Subtype.val (x.property g)
      exact hx
    obtain ⟨z, hz⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed xf).mpr hfixed
    have hinv := ValuationSubring.ext_iff.mp hcomap z⁻¹
    change algebraMap Z F z⁻¹ ∈ A ↔ algebraMap Z F z⁻¹ ∈ B at hinv
    rw [map_inv₀, hz] at hinv
    change (⟨xf, ringOfIntegers_le_valuationSubring A (x : R)⟩ : A) ∈
        IsLocalRing.maximalIdeal A ↔
      (⟨xf, ringOfIntegers_le_valuationSubring B (x : R)⟩ : B) ∈
        IsLocalRing.maximalIdeal B
    simp only [IsLocalRing.mem_maximalIdeal]
    apply not_congr
    rw [isUnit_mk_valuationSubring_iff,
      isUnit_mk_valuationSubring_iff]
    exact and_congr_right (fun _ => hinv)
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (G := G) (A := R₀) (B := R) P Q hunder
  have hcenter : valuationIntegralCenter (σ • A) =
      valuationIntegralCenter B := by
    rw [valuationIntegralCenter_smul, ← hσ]
  have hσA : (σ • A).comap (algebraMap K F) ≠ ⊤ := by
    have heq : (σ • A).comap (algebraMap K F) =
        A.comap (algebraMap K F) := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ (algebraMap K F x) = algebraMap K F x := by
        calc
          σ⁻¹ (algebraMap K F x) =
              σ⁻¹ (algebraMap Z F (algebraMap K Z x)) := by rfl
          _ = algebraMap Z F (algebraMap K Z x) := σ⁻¹.commutes _
          _ = algebraMap K F x := by rfl
      rw [AlgEquiv.smul_def, hfix]
    rwa [heq]
  have heq := valuationSubring_eq_of_integralCenter_eq K (σ • A) B
    hσA hB hcenter
  exact ⟨σ, heq.symm⟩

/-- A valuation on an algebraic extension that is trivial on the base is
trivial everywhere. -/
theorem valuationSubring_eq_top_of_comap_eq_top
    (K : Type*) {F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra.IsAlgebraic K F]
    (A : ValuationSubring F)
    (hA : A.comap (algebraMap K F) = ⊤) : A = ⊤ := by
  have hbase (x : K) : algebraMap K F x ∈ A := by
    exact (ValuationSubring.ext_iff.mp hA x).mpr trivial
  let f : K →+* A := (algebraMap K F).codRestrict A hbase
  letI : Algebra K A := f.toAlgebra
  letI : IsScalarTower K A F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply top_unique
  intro x _
  apply (Subring.isIntegrallyClosed_iff.mp
    (inferInstance : IsIntegrallyClosed A))
  exact (show IsIntegral K x from
    Algebra.IsIntegral.isIntegral x).tower_top

/-- A nontrivial valuation on an algebraic extension of a number field has
no proper nontrivial coarsening. -/
theorem valuationSubring_eq_or_eq_top_of_algebraic
    (K : Type*) {F : Type*} [Field K] [NumberField K]
    [Field F] [CharZero F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (A B : ValuationSubring F)
    (hA : A.comap (algebraMap K F) ≠ ⊤) (hAB : A ≤ B) :
    B = A ∨ B = ⊤ := by
  by_cases hBtop : B = ⊤
  · exact Or.inr hBtop
  have hB : B.comap (algebraMap K F) ≠ ⊤ := by
    intro htop
    exact hBtop (valuationSubring_eq_top_of_comap_eq_top K B htop)
  let AK := A.comap (algebraMap K F)
  let BK := B.comap (algebraMap K F)
  have hbaseLe : AK ≤ BK := fun x hx => hAB hx
  obtain ⟨v, hv, _⟩ := numberField_valuations AK hA
  letI : Ring.KrullDimLE 1 AK := by
    rw [hv]
    change Ring.KrullDimLE 1
      (HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  have hbaseEq : AK = BK :=
    ValuationSubring.eq_of_le_of_ne_top AK hbaseLe hB
  have hcenterLe : valuationIntegralCenter B ≤ valuationIntegralCenter A := by
    intro x hx
    change (⟨(x : F), ringOfIntegers_le_valuationSubring B x⟩ : B) ∈
        IsLocalRing.maximalIdeal B at hx
    change (⟨(x : F), ringOfIntegers_le_valuationSubring A x⟩ : A) ∈
      IsLocalRing.maximalIdeal A
    simp only [IsLocalRing.mem_maximalIdeal] at hx ⊢
    intro hunit
    exact hx (hunit.map (ValuationSubring.inclusion A B hAB))
  have hcenterComap :
      (valuationIntegralCenter A).comap
          (NumberField.RingOfIntegers.mapRingHom (algebraMap K F)) =
        (valuationIntegralCenter B).comap
          (NumberField.RingOfIntegers.mapRingHom (algebraMap K F)) := by
    rw [← valuationIntegralCenter_comap,
      ← valuationIntegralCenter_comap]
    change valuationIntegralCenter AK = valuationIntegralCenter BK
    rw [hbaseEq]
  have hcenterEq : valuationIntegralCenter A = valuationIntegralCenter B := by
    apply le_antisymm
    · by_contra hnot
      have hne : valuationIntegralCenter B ≠ valuationIntegralCenter A :=
        fun h => hnot h.ge
      have hlt : valuationIntegralCenter B < valuationIntegralCenter A :=
        lt_of_le_of_ne hcenterLe hne
      have hc := Ideal.IsIntegral.comap_lt_comap
        (R := 𝓞 K) hlt
      exact (ne_of_lt hc) hcenterComap.symm
    · exact hcenterLe
  exact Or.inl (valuationSubring_eq_of_integralCenter_eq K A B
    hA hB hcenterEq).symm

end

end NU.LocalTheory
