import Submission.NU.NeukirchUchida.RegularKernel

/-!
# The cyclic finite-quotient step

Blueprint §5.  Chebotarev supplies an absolute-degree-one prime with a
prescribed Frobenius generator, (L4) transports its normalized lift, and
prime transitivity turns the comparison into conjugation at a cyclic finite
level.
-/

open scoped NumberField Pointwise

namespace NU.NeukirchUchida

noncomputable section

/-- Package a recorded inclusion as an ambient finite extension. -/
noncomputable def extensionOfLE
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field) :
    NumberFieldExtension F where
  field := N
  le_base := hFN

/-- A base prime is unramified in an ambient extension. -/
def IsUnramifiedAbove
    {F : NumberFieldInOmega} (N : NumberFieldExtension F)
    (v : NU.LocalTheory.FinitePlace F.field) : Prop :=
  (∃ w : NU.LocalTheory.FinitePlace N.field.field,
    NU.LocalTheory.restrictFinitePlace F.field w = v) ∧
  ∀ w : NU.LocalTheory.FinitePlace N.field.field,
    NU.LocalTheory.restrictFinitePlace F.field w = v →
      relativeRamificationIndex N v w = 1

/-- The integral equivalence between the literal bottom intermediate field
and `ℚ`. -/
noncomputable def rationalBottomIntegersEquiv :
    NumberField.RingOfIntegers rationalNumberField.field ≃+*
      NumberField.RingOfIntegers ℚ :=
  NumberField.RingOfIntegers.mapRingEquiv
    (IntermediateField.botEquiv ℚ Omega).toRingEquiv

/-- Restricting an absolute prime to the literal rational field and then
transporting along `botEquiv` gives its ordinary rational restriction. -/
theorem rationalBottomIntegersEquiv_finitePrime
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        rationalBottomIntegersEquiv (finitePrime rationalNumberField P) =
      rationalPrime F (finitePrime F P) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  let hbot : rationalNumberField.field ≤ F.field := bot_le
  letI : Algebra rationalNumberField.field F.field :=
    (IntermediateField.inclusion hbot).toRingHom.toAlgebra
  let L := extensionOfLE rationalNumberField F hbot
  have hres := restrictFinitePlace_finitePrime rationalNumberField L P
  have hideal := congrArg
    IsDedekindDomain.HeightOneSpectrum.asIdeal hres
  rw [NU.LocalTheory.restrictFinitePlace_asIdeal] at hideal
  have hmaps : (algebraMap (𝓞 rationalNumberField.field) (𝓞 F.field)).comp
      rationalBottomIntegersEquiv.symm.toRingHom =
        algebraMap (𝓞 ℚ) (𝓞 F.field) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((IntermediateField.botEquiv ℚ Omega).symm (x : ℚ) : Omega) =
      algebraMap ℚ Omega x
    exact congrArg Subtype.val
      (IntermediateField.botEquiv_symm (F := ℚ) (E := Omega) x)
  change Ideal.comap rationalBottomIntegersEquiv.symm
      (finitePrime rationalNumberField P).asIdeal = _
  rw [← hideal]
  change Ideal.comap rationalBottomIntegersEquiv.symm
      (Ideal.comap (algebraMap (𝓞 rationalNumberField.field) (𝓞 F.field))
        (finitePrime F P).asIdeal) = _
  calc
    Ideal.comap rationalBottomIntegersEquiv.symm
        (Ideal.comap (algebraMap (𝓞 rationalNumberField.field) (𝓞 F.field))
          (finitePrime F P).asIdeal) =
      Ideal.comap ((algebraMap (𝓞 rationalNumberField.field)
        (𝓞 F.field)).comp rationalBottomIntegersEquiv.symm.toRingHom)
          (finitePrime F P).asIdeal :=
        Ideal.comap_comap _ _
    _ = Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 F.field))
        (finitePrime F P).asIdeal := by rw [hmaps]
    _ = (rationalPrime F (finitePrime F P)).asIdeal :=
      (NU.LocalTheory.restrictFinitePlace_asIdeal ℚ
        (finitePrime F P)).symm

/-- The residual local-global Frobenius input: Chebotarev supplies the
absolute-degree-one prime, while local unramified theory supplies a normalized
lift and uniqueness of its image at the chosen finite level. -/
private def DegreeOneFrobeniusConstruction : Prop :=
  ∀ (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (s : relativeGaloisGroup F N hFN),
    Subgroup.zpowers s = ⊤ →
    ∃ P : AbsolutePrime,
      IsAbsoluteDegreeOne F (finitePrime F P) ∧
      IsUnramifiedAbove (extensionOfLE F N hFN) (finitePrime F P) ∧
      ∃ phi : decompositionGroup F P,
        IsArithmeticFrobeniusLift F P phi ∧
        finiteQuotientMap F N hFN phi.1 = s ∧
        ∀ psi : decompositionGroup F P,
          IsArithmeticFrobeniusLift F P psi →
          finiteQuotientMap F N hFN psi.1 = s

/-- The remaining local lifting step after Chebotarev has produced an
unramified finite prime whose arithmetic Frobenius is the prescribed cyclic
generator.  It prolongs that prime to `Omega`, lifts the normalized Frobenius,
and records uniqueness of its image in the selected finite quotient. -/
private def FinitePrimeFrobeniusLiftingConstruction : Prop :=
  ∀ (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (s : relativeGaloisGroup F N hFN),
    Subgroup.zpowers s = ⊤ →
    ∀ (q : NU.Chebotarev.PrimeIdeal ℚ)
      (w : NU.Chebotarev.PrimeIdeal N.field),
      NU.Chebotarev.IsUnramifiedPrime (K := ℚ) (L := N.field) q →
      w.asIdeal.LiesOver q.asIdeal →
      IsArithFrobAt (𝓞 ℚ) s.1 w.asIdeal →
      ∃ P : AbsolutePrime,
        IsAbsoluteDegreeOne F (finitePrime F P) ∧
        IsUnramifiedAbove (extensionOfLE F N hFN) (finitePrime F P) ∧
        ∃ phi : decompositionGroup F P,
          IsArithmeticFrobeniusLift F P phi ∧
          finiteQuotientMap F N hFN phi.1 = s ∧
          ∀ psi : decompositionGroup F P,
            IsArithmeticFrobeniusLift F P psi →
            finiteQuotientMap F N hFN psi.1 = s

private theorem frobeniusIntegral_mem
    {E : Type*} [Field E] [CharZero E] (A : ValuationSubring E) :
    ∀ a : 𝓞 E, (a : E) ∈ A := by
  intro a
  apply (Subring.isIntegrallyClosed_iff.mp
    (inferInstance : IsIntegrallyClosed A))
  exact a.2.tower_top

private def frobeniusIntegralCenter
    {E : Type*} [Field E] [CharZero E] (A : ValuationSubring E) :
    Ideal (𝓞 E) :=
  (IsLocalRing.maximalIdeal A).comap
    ((algebraMap (𝓞 E) E).codRestrict A
      (frobeniusIntegral_mem A))

private instance frobeniusIntegralCenter_isPrime
    {E : Type*} [Field E] [CharZero E] (A : ValuationSubring E) :
    (frobeniusIntegralCenter A).IsPrime :=
  (IsLocalRing.maximalIdeal A).comap_isPrime _

private def frobeniusValuationComapMap
    {E L : Type*} [Field E] [Field L] (f : E →+* L)
    (A : ValuationSubring L) : A.comap f →+* A where
  toFun x := ⟨f x, x.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

private theorem frobeniusValuationComapMap_isLocal
    {E L : Type*} [Field E] [Field L] (f : E →+* L)
    (A : ValuationSubring L) : IsLocalHom (frobeniusValuationComapMap f A) := by
  apply IsLocalHom.mk
  intro x hx
  have hfx0 : f (x : E) ≠ 0 := by
    intro hzero
    apply IsUnit.ne_zero hx
    apply Subtype.ext
    exact hzero
  have hx0 : (x : E) ≠ 0 := (map_ne_zero f).mp hfx0
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hyval : (y : L) = (f (x : E))⁻¹ := by
    apply (mul_left_cancel₀ hfx0)
    have hy' := congrArg Subtype.val hy
    change f (x : E) * (y : L) = 1 at hy'
    rw [hy', mul_inv_cancel₀ hfx0]
  let y' : A.comap f := ⟨(x : E)⁻¹, by
    change f ((x : E)⁻¹) ∈ A
    rw [map_inv₀, ← hyval]
    exact y.property⟩
  exact isUnit_iff_exists_inv.mpr ⟨y', by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0⟩

private theorem frobeniusIntegralCenter_comap
    {E L : Type*} [Field E] [Field L] [CharZero E] [CharZero L]
    (f : E →+* L) (A : ValuationSubring L) :
    frobeniusIntegralCenter (A.comap f) =
      (frobeniusIntegralCenter A).comap
        (NumberField.RingOfIntegers.mapRingHom f) := by
  letI : IsLocalHom (frobeniusValuationComapMap f A) :=
    frobeniusValuationComapMap_isLocal f A
  apply Ideal.ext
  intro x
  change (⟨(x : E), frobeniusIntegral_mem
      (A.comap f) x⟩ : A.comap f) ∈
        IsLocalRing.maximalIdeal (A.comap f) ↔
    (⟨f (x : E), frobeniusIntegral_mem A
      (NumberField.RingOfIntegers.mapRingHom f x)⟩ : A) ∈
        IsLocalRing.maximalIdeal A
  have hm := IsLocalRing.maximalIdeal_comap (frobeniusValuationComapMap f A)
  have hx := (Ideal.ext_iff.mp hm
    ⟨(x : E), frobeniusIntegral_mem (A.comap f) x⟩).symm
  change _ ↔ frobeniusValuationComapMap f A
    ⟨(x : E), frobeniusIntegral_mem (A.comap f) x⟩ ∈
      IsLocalRing.maximalIdeal A at hx
  exact hx

private def frobeniusValuationSmulEquiv
    {H E : Type*} [Group H] [Field E] [MulSemiringAction H E]
    (g : H) (A : ValuationSubring E) : A ≃+* (g • A : ValuationSubring E) where
  toFun x := ⟨g • (x : E),
    ValuationSubring.smul_mem_pointwise_smul g (x : E) A x.property⟩
  invFun x := ⟨g⁻¹ • (x : E),
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; exact smul_add g (x : E) (y : E)
  map_mul' x y := by ext; exact MulSemiringAction.smul_mul g (x : E) (y : E)

private theorem frobeniusIntegralCenter_smul
    {H E : Type*} [Group H] [Field E] [CharZero E]
    [MulSemiringAction H E] (g : H) (A : ValuationSubring E) :
    frobeniusIntegralCenter (g • A) = g • frobeniusIntegralCenter A := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change (⟨(x : E), frobeniusIntegral_mem (g • A) x⟩ :
      (g • A : ValuationSubring E)) ∈
        IsLocalRing.maximalIdeal (g • A : ValuationSubring E) ↔
    (⟨((g⁻¹ • x : 𝓞 E) : E), frobeniusIntegral_mem A (g⁻¹ • x)⟩ :
      A) ∈ IsLocalRing.maximalIdeal A
  simp only [IsLocalRing.mem_maximalIdeal]
  apply not_congr
  let e := frobeniusValuationSmulEquiv g A
  let y : A := ⟨((g⁻¹ • x : 𝓞 E) : E),
    frobeniusIntegral_mem A (g⁻¹ • x)⟩
  have he := isUnit_map_iff e y
  have hey : e y = (⟨(x : E),
      frobeniusIntegral_mem (g • A) x⟩ :
        (g • A : ValuationSubring E)) := by
    apply Subtype.ext
    change g • (g⁻¹ • (x : E)) = (x : E)
    simp
  rw [← hey]
  exact he

private theorem frobeniusIntegralCenter_primeValuationSubring
    {E : Type*} [Field E] [NumberField E]
    (v : NU.LocalTheory.FinitePlace E) :
    frobeniusIntegralCenter (NU.LocalTheory.primeValuationSubring v) = v.asIdeal := by
  change frobeniusIntegralCenter
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) = v.asIdeal
  apply Ideal.ext
  intro x
  change (⟨(x : E), frobeniusIntegral_mem
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) x⟩ :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) ∈
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) ↔ x ∈ v.asIdeal
  rw [show (⟨(x : E), frobeniusIntegral_mem
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) x⟩ :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) =
      algebraMap (𝓞 E)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) x by
    apply Subtype.ext
    rfl]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E v) v.asIdeal x

private theorem valuationSubring_eq_of_frobeniusCenter_eq
    (K : Type*) {E : Type*} [Field K] [NumberField K]
    [Field E] [CharZero E] [Algebra K E] [Algebra.IsAlgebraic K E]
    (A C : ValuationSubring E)
    (hA : A.comap (algebraMap K E) ≠ ⊤)
    (hC : C.comap (algebraMap K E) ≠ ⊤)
    (hcenter : frobeniusIntegralCenter A = frobeniusIntegralCenter C) : A = C := by
  apply ValuationSubring.ext
  intro x
  let L : IntermediateField K E := IntermediateField.adjoin K {x}
  letI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (S := {x})
      (fun y _ => Algebra.IsIntegral.isIntegral y)
  letI : NumberField L := NumberField.of_module_finite K L
  let AL : ValuationSubring L := A.comap L.val.toRingHom
  let CL : ValuationSubring L := C.comap L.val.toRingHom
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
  have hCL : CL ≠ ⊤ := by
    intro htop
    apply hC
    apply ValuationSubring.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      have hy : algebraMap K L y ∈ CL := by rw [htop]; trivial
      exact hy
  obtain ⟨v, hv, _⟩ := NU.LocalTheory.numberField_valuations AL hAL
  obtain ⟨w, hw, _⟩ := NU.LocalTheory.numberField_valuations CL hCL
  have hcenterL : frobeniusIntegralCenter AL = frobeniusIntegralCenter CL := by
    dsimp only [AL, CL]
    rw [frobeniusIntegralCenter_comap, frobeniusIntegralCenter_comap, hcenter]
  have hvw : v = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [← frobeniusIntegralCenter_primeValuationSubring v,
      ← frobeniusIntegralCenter_primeValuationSubring w,
      ← hv, ← hw, hcenterL]
  have hAC : AL = CL := by rw [hv, hw, hvw]
  let y : L := ⟨x, IntermediateField.subset_adjoin K {x}
    (Set.mem_singleton x)⟩
  have hy := ValuationSubring.ext_iff.mp hAC y
  exact hy

private theorem frobeniusIntegralCenter_under
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    (frobeniusIntegralCenter P.valuationSubring).under (𝓞 F.field) =
      (finitePrime F P).asIdeal := by
  rw [Ideal.under_def]
  change Ideal.comap
      (NumberField.RingOfIntegers.mapRingHom F.field.val.toRingHom)
        (frobeniusIntegralCenter P.valuationSubring) = _
  rw [← frobeniusIntegralCenter_comap,
    ← primeValuationSubring_finitePrime,
    frobeniusIntegralCenter_primeValuationSubring]

private theorem exists_normalizedArithmeticFrobenius
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    ∃ phi : decompositionGroup F P,
      IsArithmeticFrobeniusLift F P phi := by
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsAlgebraic F.field Omega :=
    IntermediateField.isAlgebraic_tower_top
  letI : IsAlgClosure F.field Omega :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, inferInstance⟩
  letI : IsGalois F.field Omega := IsGalois.mk
  let G := Omega ≃ₐ[F.field] Omega
  let B := 𝓞 Omega
  letI : Algebra.IsAlgebraic ℤ Omega :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := ℤ) (K := ℚ) (C := Omega)).mpr
        (show Algebra.IsAlgebraic ℚ Omega from inferInstance)
  letI : IsFractionRing B Omega :=
    integralClosure.isFractionRing_of_algebraic
      (A := ℤ) (L := Omega) (fun x hx => by
        apply (Int.cast_injective (α := Omega))
        simpa using hx)
  letI : IsGaloisGroup G F.field Omega := IsGaloisGroup.of_isGalois F.field Omega
  letI : IsGaloisGroup G (𝓞 F.field) B :=
    IsGaloisGroup.of_isFractionRing G (𝓞 F.field) B F.field Omega
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  letI : ContinuousSMul G B :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun x => by
      have hx := stabilizer_isOpen_of_isIntegral (K := F.field) (x : Omega)
      have heq : (MulAction.stabilizer G x : Set G) =
          (MulAction.stabilizer (Omega ≃ₐ[F.field] Omega) (x : Omega) : Set G) := by
        ext g
        change (g • x = x) ↔ (g • (x : Omega) = (x : Omega))
        constructor
        · exact fun h => congrArg Subtype.val h
        · intro h
          apply Subtype.ext
          exact h
      rw [heq]
      exact hx
  let Q : Ideal B := frobeniusIntegralCenter P.valuationSubring
  let v := finitePrime F P
  have hQv : Q.under (𝓞 F.field) = v.asIdeal := frobeniusIntegralCenter_under F P
  letI : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
  haveI : Q.IsPrime := frobeniusIntegralCenter_isPrime P.valuationSubring
  have hInt : Algebra.IsIntegral (𝓞 F.field ⧸ v.asIdeal) (B ⧸ Q) := by
    infer_instance
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  letI : Field (𝓞 F.field ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (B ⧸ Q) :=
    (isField_of_isIntegral_of_isField'
      (R := 𝓞 F.field ⧸ v.asIdeal) (S := B ⧸ Q)
      (Field.toIsField (𝓞 F.field ⧸ v.asIdeal))).toField
  haveI : Fintype (𝓞 F.field ⧸ v.asIdeal) := Fintype.ofFinite _
  have hAlg : Algebra.IsAlgebraic (𝓞 F.field ⧸ v.asIdeal) (B ⧸ Q) := by
    exact Algebra.IsIntegral.isAlgebraic
  let frob : (B ⧸ Q) ≃ₐ[(𝓞 F.field ⧸ v.asIdeal)] (B ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  have hfrob (x : B ⧸ Q) : frob x = x ^ NU.Chebotarev.PrimeIdeal.norm v := by
    change x ^ Fintype.card (𝓞 F.field ⧸ v.asIdeal) = _
    simp only [NU.Chebotarev.PrimeIdeal.norm, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := G) v.asIdeal Q frob
  have hgcenter : frobeniusIntegralCenter (g.1 • P.valuationSubring) =
      frobeniusIntegralCenter P.valuationSubring := by
    rw [frobeniusIntegralCenter_smul]
    exact g.2
  have hcomap : (g.1 • P.valuationSubring).comap
      (algebraMap F.field Omega) =
        P.valuationSubring.comap (algebraMap F.field Omega) := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change g.1.symm (algebraMap F.field Omega x) ∈ P.valuationSubring ↔ _
    rw [g.1.symm.commutes]
  have hnontrivial : P.valuationSubring.comap
      (algebraMap F.field Omega) ≠ ⊤ :=
    absolutePrime_comap_nontrivial F P
  have hPstab : g.1 • P.valuationSubring = P.valuationSubring := by
    apply valuationSubring_eq_of_frobeniusCenter_eq F.field
    · rw [hcomap]
      exact hnontrivial
    · exact hnontrivial
    · exact hgcenter
  let gammaQ : RationalAbsoluteGaloisGroup := g.1.restrictScalars ℚ
  let gammaF : absoluteGaloisGroup F := ⟨gammaQ, by
    intro x
    change g.1 (algebraMap F.field Omega x) = algebraMap F.field Omega x
    exact g.1.commutes x⟩
  have hprime : (gammaF : absoluteGaloisGroup F) • P = P := by
    apply AbsolutePrime.ext
    change g.1 • P.valuationSubring = P.valuationSubring
    exact hPstab
  let phi : decompositionGroup F P := ⟨gammaF, hprime⟩
  let m := IsLocalRing.maximalIdeal P.valuationSubring
  let toP : B →+* P.valuationSubring :=
    (algebraMap B Omega).codRestrict P.valuationSubring
      (frobeniusIntegral_mem P.valuationSubring)
  have hactionB (a : B) :
      absoluteResidueAction F P phi (Ideal.Quotient.mk m (toP a)) =
        (Ideal.Quotient.mk m (toP a)) ^
          NU.Chebotarev.PrimeIdeal.norm v := by
    have hgaQ := DFunLike.congr_fun hg (Ideal.Quotient.mk Q a)
    have hgaQ' : Ideal.Quotient.mk Q (g.1 • a) =
        (Ideal.Quotient.mk Q a) ^ NU.Chebotarev.PrimeIdeal.norm v := by
      calc
        Ideal.Quotient.mk Q (g.1 • a) = frob (Ideal.Quotient.mk Q a) := hgaQ
        _ = _ := hfrob (Ideal.Quotient.mk Q a)
    have hmemQ : g.1 • a - a ^ NU.Chebotarev.PrimeIdeal.norm v ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
      exact hgaQ'
    obtain ⟨y, hy, hact⟩ := absoluteResidueAction_mk F P phi (toP a)
    rw [hact, ← map_pow]
    apply Ideal.Quotient.eq.mpr
    change y - (toP a) ^ NU.Chebotarev.PrimeIdeal.norm v ∈ m
    change toP (g.1 • a - a ^ NU.Chebotarev.PrimeIdeal.norm v) ∈ m at hmemQ
    convert hmemQ using 1
    apply Subtype.ext
    change (y : Omega) - (a : Omega) ^
        NU.Chebotarev.PrimeIdeal.norm v =
      g.1 (a : Omega) - (a : Omega) ^
        NU.Chebotarev.PrimeIdeal.norm v
    rw [hy]
    rfl
  have hnormalized : IsArithmeticFrobeniusLift F P phi := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    let Efield : IntermediateField ℚ Omega :=
      IntermediateField.adjoin ℚ ({(x : Omega)} : Set Omega)
    letI : FiniteDimensional ℚ Efield :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (x : Omega))
    let E : NumberFieldInOmega :=
      { field := Efield
        finite := by infer_instance }
    letI : NumberField E.field := NumberField.of_module_finite ℚ E.field
    let u := finitePrime E P
    let xE : E.field := ⟨(x : Omega),
      IntermediateField.subset_adjoin ℚ ({(x : Omega)} : Set Omega)
        (Set.mem_singleton (x : Omega))⟩
    have hxE : xE ∈ NU.LocalTheory.primeValuationSubring u := by
      rw [primeValuationSubring_finitePrime]
      exact x.property
    obtain ⟨b, c, hcnmem, hbc⟩ :=
      (NU.LocalTheory.mem_primeValuationSubring_iff u xE).mp hxE
    let iE : E.field →+* Omega := E.field.val.toRingHom
    let bB : B := NumberField.RingOfIntegers.mapRingHom iE b
    let cB : B := NumberField.RingOfIntegers.mapRingHom iE c
    let bP : P.valuationSubring := toP bB
    let cP : P.valuationSubring := toP cB
    let X : AbsoluteResidueField P := Ideal.Quotient.mk m x
    let bbar : AbsoluteResidueField P := Ideal.Quotient.mk m bP
    let cbar : AbsoluteResidueField P := Ideal.Quotient.mk m cP
    have hrelP : x * cP = bP := by
      apply Subtype.ext
      have hv := congrArg E.field.val hbc
      change (x : Omega) * (cB : Omega) = (bB : Omega)
      simpa [xE, bB, cB, iE] using hv
    have hrel : X * cbar = bbar := by
      exact congrArg (Ideal.Quotient.mk m) hrelP
    have hcbar : cbar ≠ 0 := by
      intro hc
      have hcm : cP ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hc
      have hcQ : cB ∈ Q := hcm
      have hcunder : c ∈ Q.under (𝓞 E.field) := by
        rw [Ideal.mem_under]
        exact hcQ
      have hQE := frobeniusIntegralCenter_under E P
      rw [hQE] at hcunder
      exact hcnmem hcunder
    have hbaction := hactionB bB
    have hcaction := hactionB cB
    apply mul_right_cancel₀ (pow_ne_zero _ hcbar)
    calc
      absoluteResidueAction F P phi X *
          cbar ^ NU.Chebotarev.PrimeIdeal.norm v =
        absoluteResidueAction F P phi X *
          absoluteResidueAction F P phi cbar := by rw [hcaction]
      _ = absoluteResidueAction F P phi (X * cbar) := by
        rw [map_mul]
      _ = absoluteResidueAction F P phi bbar := by rw [hrel]
      _ = bbar ^ NU.Chebotarev.PrimeIdeal.norm v := hbaction
      _ = (X * cbar) ^ NU.Chebotarev.PrimeIdeal.norm v := by rw [hrel]
      _ = X ^ NU.Chebotarev.PrimeIdeal.norm v *
          cbar ^ NU.Chebotarev.PrimeIdeal.norm v := by rw [mul_pow]
  exact ⟨phi, hnormalized⟩

private theorem finitePrime_surjective_for_frobenius
    (N : NumberFieldInOmega) : Function.Surjective (finitePrime N) := by
  intro w
  obtain ⟨W, hW⟩ := NU.LocalTheory.exists_valuationSubring_extension
    N.field.val.toRingHom (NU.LocalTheory.primeValuationSubring w)
  have hWtop : W ≠ ⊤ := by
    intro htop
    have h := hW
    rw [htop] at h
    have hbad : NU.LocalTheory.primeValuationSubring w = ⊤ := h.symm
    exact NU.LocalTheory.primeValuationSubring_ne_top w hbad
  have hfiniteN : NU.LocalTheory.IsAbsoluteFinitePlaceIn N.field Omega W :=
    ⟨hWtop, w, hW⟩
  have hfiniteQ : NU.LocalTheory.IsAbsoluteFinitePlaceIn ℚ Omega W :=
    (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
      ℚ N.field Omega W).mpr hfiniteN
  let P : AbsolutePrime := ⟨W, hfiniteQ⟩
  refine ⟨P, ?_⟩
  apply (NU.LocalTheory.numberField_valuations
    (NU.LocalTheory.primeValuationSubring w)
    (NU.LocalTheory.primeValuationSubring_ne_top w)).unique
  · rw [primeValuationSubring_finitePrime]
    exact hW.symm
  · rfl

private theorem absoluteNorm_eq_of_degreeOne
    (F : NumberFieldInOmega) (P : AbsolutePrime)
    (q : NU.Chebotarev.PrimeIdeal ℚ)
    (hqv : rationalPrime F (finitePrime F P) = q)
    (hdegree : IsAbsoluteDegreeOne F (finitePrime F P)) :
    Nat.card (𝓞 ℚ ⧸ q.asIdeal) =
      NU.Chebotarev.PrimeIdeal.norm (finitePrime F P) := by
  let v := finitePrime F P
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [← hqv]
    rfl⟩
  have hf : absoluteResidueDegree F v = 1 := by
    change absoluteRamificationIndex F v * absoluteResidueDegree F v = 1 at hdegree
    apply Nat.eq_one_of_dvd_one
    refine ⟨absoluteRamificationIndex F v, ?_⟩
    rw [Nat.mul_comm]
    exact hdegree.symm
  have hf' : v.asIdeal.inertiaDeg' (𝓞 ℚ) = 1 := hf
  have hf'' : q.asIdeal.inertiaDeg v.asIdeal = 1 := by
    rw [Ideal.inertiaDeg_eq_inertiaDeg' q.asIdeal v.asIdeal]
    exact hf'
  have hnorm := (Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
    v.asIdeal q.asIdeal inferInstance q.ne_bot).symm
  rw [hf'', pow_one] at hnorm
  calc
    Nat.card (𝓞 ℚ ⧸ q.asIdeal) = Ideal.absNorm q.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = Ideal.absNorm v.asIdeal := hnorm
    _ = NU.Chebotarev.PrimeIdeal.norm v := rfl

private theorem normalizedLift_isArithFrobAt_finite
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (P : AbsolutePrime) (w : NU.Chebotarev.PrimeIdeal N.field)
    (hPN : finitePrime N P = w)
    (psi : decompositionGroup F P)
    (hpsi : IsArithmeticFrobeniusLift F P psi)
    (hcard : Nat.card (𝓞 ℚ ⧸ w.asIdeal.under (𝓞 ℚ)) =
      NU.Chebotarev.PrimeIdeal.norm (finitePrime F P)) :
    IsArithFrobAt (𝓞 ℚ) (finiteQuotientMap F N hFN psi.1).1 w.asIdeal := by
  let B := 𝓞 Omega
  let Q : Ideal B := frobeniusIntegralCenter P.valuationSubring
  let m := IsLocalRing.maximalIdeal P.valuationSubring
  let toP : B →+* P.valuationSubring :=
    (algebraMap B Omega).codRestrict P.valuationSubring
      (frobeniusIntegral_mem P.valuationSubring)
  intro a
  let aB : B := NumberField.RingOfIntegers.mapRingHom
    N.field.val.toRingHom a
  let aP : P.valuationSubring := toP aB
  obtain ⟨y, hy, hact⟩ := absoluteResidueAction_mk F P psi aP
  have hn := hpsi (Ideal.Quotient.mk m aP)
  rw [hact, ← map_pow] at hn
  have hmemP : y - aP ^ NU.Chebotarev.PrimeIdeal.norm
      (finitePrime F P) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
    exact hn
  rw [hcard]
  have hcenterN : Q.under (𝓞 N.field) = w.asIdeal := by
    rw [frobeniusIntegralCenter_under N P, hPN]
  rw [← hcenterN, Ideal.mem_under]
  change toP (NumberField.RingOfIntegers.mapRingHom N.field.val.toRingHom
      ((finiteQuotientMap F N hFN psi.1).1 • a -
        a ^ NU.Chebotarev.PrimeIdeal.norm (finitePrime F P))) ∈ m
  convert hmemP using 1
  apply Subtype.ext
  change (finiteQuotientMap F N hFN psi.1).1 (a : N.field) -
      (a : N.field) ^ NU.Chebotarev.PrimeIdeal.norm (finitePrime F P) =
    (y : Omega) - (a : Omega) ^
      NU.Chebotarev.PrimeIdeal.norm (finitePrime F P)
  rw [hy]
  congr 1
  exact finiteQuotientMap_apply F N hFN psi.1 (a : N.field)

set_option maxHeartbeats 800000 in
/-- Fallback seam for the infinite local prolongation/normalized-lift step.
The global Chebotarev choice is proved in `degreeOneFrobeniusConstruction`
below; only this local passage from an exact finite Frobenius remains in the
ledger. -/
private theorem finitePrimeFrobeniusLiftingConstruction :
    FinitePrimeFrobeniusLiftingConstruction := by
  intro F N hFN _ s hs q w hunramified hwq hfrob
  letI : Algebra F.field N.field :=
    (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.field N.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  obtain ⟨P, hPN⟩ := finitePrime_surjective_for_frobenius N w
  let v := finitePrime F P
  have hwv : NU.LocalTheory.restrictFinitePlace F.field w = v := by
    rw [← hPN]
    exact restrictFinitePlace_finitePrime F (extensionOfLE F N hFN) P
  have hqv : rationalPrime F v = q := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 F.field)) v.asIdeal = q.asIdeal
    rw [← hwv]
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 F.field))
      (Ideal.comap (algebraMap (𝓞 F.field) (𝓞 N.field)) w.asIdeal) = q.asIdeal
    rw [Ideal.comap_comap]
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 N.field)) w.asIdeal = q.asIdeal
    exact hwq.over.symm
  have hunrw : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    hunramified w hwq
  letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := hunrw
  have hs_eq : s.1 = NU.Chebotarev.arithFrobeniusAt
      (K := ℚ) (L := N.field) w := by
    have heq := hfrob.eq_of_isUnramifiedAt
      (IsArithFrobAt.arithFrobAt (𝓞 ℚ)
        (N.field ≃ₐ[ℚ] N.field) w.asIdeal)
      w.asIdeal.primeCompl_le_nonZeroDivisors
    have hfield : s.1.toRingEquiv.toRingHom =
        (NU.Chebotarev.arithFrobeniusAt
          (K := ℚ) (L := N.field) w).toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := 𝓞 N.field)
      intro x
      exact congrArg Subtype.val (DFunLike.congr_fun heq x)
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hfield x
  have hdegree : IsAbsoluteDegreeOne F v := by
    apply (degreeOne_iff_rationalDecompositionGroup_le F P).mpr
    intro gamma hgamma
    let G := RationalAbsoluteGaloisGroup
    let B := 𝓞 Omega
    let Q : Ideal B := frobeniusIntegralCenter P.valuationSubring
    have hval : (gamma : G) • P.valuationSubring = P.valuationSubring := by
      have hp := congrArg AbsolutePrime.valuationSubring hgamma
      exact (smul_absolutePrime_valuationSubring (gamma : G) P).symm.trans hp
    have hQstab : (gamma : G) • Q = Q := by
      change (gamma : G) • frobeniusIntegralCenter P.valuationSubring =
        frobeniusIntegralCenter P.valuationSubring
      rw [← frobeniusIntegralCenter_smul, hval]
    let sigmaN : N.field ≃ₐ[ℚ] N.field :=
      AlgEquiv.restrictNormalHom N.field (gamma : G)
    have hsigmaw : sigmaN • w.asIdeal = w.asIdeal := by
      have hcenterN : Q.under (𝓞 N.field) = w.asIdeal := by
        rw [frobeniusIntegralCenter_under N P, hPN]
      apply Ideal.ext
      intro a
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      rw [← hcenterN, Ideal.mem_under, Ideal.mem_under]
      have hmap : algebraMap (𝓞 N.field) B (sigmaN⁻¹ • a) =
        (gamma : G)⁻¹ • algebraMap (𝓞 N.field) B a := by
        apply Subtype.ext
        change N.field.val (sigmaN⁻¹ (a : N.field)) =
          (gamma : G)⁻¹ (N.field.val (a : N.field))
        rw [show sigmaN⁻¹ = AlgEquiv.restrictNormalHom N.field
          (gamma : G)⁻¹ by
            dsimp [sigmaN]
            exact (map_inv (AlgEquiv.restrictNormalHom N.field) (gamma : G)).symm]
        exact AlgEquiv.restrictNormal_commutes (gamma : G)⁻¹ N.field (a : N.field)
      rw [hmap]
      calc
        (gamma : G)⁻¹ • algebraMap (𝓞 N.field) B a ∈ Q ↔
          algebraMap (𝓞 N.field) B a ∈ (gamma : G) • Q := by
              rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        _ ↔ _ := by rw [hQstab]
    have hsigma_mem : sigmaN ∈
        NU.Chebotarev.decompositionSubgroup (K := ℚ) (L := N.field) w :=
      hsigmaw
    have hgen := NU.Chebotarev.arithFrobAt_generates_decomposition w hunrw
    rw [hgen, ← hs_eq, Subgroup.mem_zpowers_iff] at hsigma_mem
    obtain ⟨n, hn⟩ := hsigma_mem
    intro x
    let y : N.field := ⟨x.1, hFN x.2⟩
    have hfix : (s ^ n).1 y = y := (s ^ n).2 x
    calc
      gamma x.1 = N.field.val (sigmaN y) :=
        (AlgEquiv.restrictNormal_commutes (gamma : G) N.field y).symm
      _ = N.field.val ((s.1 ^ n) y) := by rw [hn]
      _ = N.field.val y := congrArg N.field.val hfix
      _ = x.1 := rfl
  have hunramifiedAbove :
      IsUnramifiedAbove (extensionOfLE F N hFN) v := by
    refine ⟨⟨w, hwv⟩, ?_⟩
    intro w' hw'v
    have hover : w'.asIdeal.LiesOver v.asIdeal := ⟨by
      change v.asIdeal =
        (NU.LocalTheory.restrictFinitePlace F.field w').asIdeal
      rw [hw'v]⟩
    letI : w'.asIdeal.LiesOver v.asIdeal := hover
    letI : v.asIdeal.LiesOver q.asIdeal := ⟨by
      exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hqv.symm⟩
    have hw'q : w'.asIdeal.LiesOver q.asIdeal :=
      Ideal.LiesOver.trans w'.asIdeal v.asIdeal q.asIdeal
    have hunrw' : Algebra.IsUnramifiedAt (𝓞 ℚ) w'.asIdeal :=
      hunramified w' hw'q
    letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w'.asIdeal := hunrw'
    have hunrF : Algebra.IsUnramifiedAt (𝓞 F.field) w'.asIdeal :=
      Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 ℚ) w'.asIdeal
    letI : Algebra.IsUnramifiedAt (𝓞 F.field) w'.asIdeal := hunrF
    change w'.asIdeal.ramificationIdx' (𝓞 F.field) = 1
    rw [← Ideal.ramificationIdx_eq_ramificationIdx'
      v.asIdeal w'.asIdeal v.ne_bot]
    have hu := (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      w'.ne_bot).mp hunrF
    simpa [← hover.over] using hu
  have hcard : Nat.card (𝓞 ℚ ⧸ w.asIdeal.under (𝓞 ℚ)) =
      NU.Chebotarev.PrimeIdeal.norm v := by
    rw [← hwq.over]
    exact absoluteNorm_eq_of_degreeOne F P q hqv hdegree
  have himage (psi : decompositionGroup F P)
      (hpsi : IsArithmeticFrobeniusLift F P psi) :
      finiteQuotientMap F N hFN psi.1 = s := by
    have hpsiFinite := normalizedLift_isArithFrobAt_finite
      F N hFN P w hPN psi hpsi hcard
    have heq := hpsiFinite.eq_of_isUnramifiedAt hfrob
      w.asIdeal.primeCompl_le_nonZeroDivisors
    apply Subtype.ext
    have hfield :
        (finiteQuotientMap F N hFN psi.1).1.toRingEquiv.toRingHom =
          s.1.toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := 𝓞 N.field)
      intro x
      exact congrArg Subtype.val (DFunLike.congr_fun heq x)
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hfield x
  obtain ⟨phi, hphi⟩ := exists_normalizedArithmeticFrobenius F P
  exact ⟨P, hdegree, hunramifiedAbove, phi, hphi,
    himage phi hphi, himage⟩

/-- Chebotarev over the common normal level supplies a rational prime with
Frobenius conjugate to `s`.  Conjugating the chosen prime makes the finite
Frobenius literally `s`; the remaining local lift is delegated to the single
seam above. -/
private theorem degreeOneFrobeniusConstruction :
    DegreeOneFrobeniusConstruction := by
  intro F N hFN _ s hs
  let S := NU.Chebotarev.frobeniusPrimeSet
    (K := ℚ) (L := N.field) (ConjClasses.mk s.1)
  have hden := NU.Chebotarev.chebotarev_dirichletDensity
    (K := ℚ) (L := N.field) (ConjClasses.mk s.1)
  have hnum : (0 : ℝ) < ((ConjClasses.mk s.1).carrier.ncard : ℝ) := by
    exact_mod_cast ((Set.ncard_pos (s := (ConjClasses.mk s.1).carrier)).2
      (show (ConjClasses.mk s.1).carrier.Nonempty from
        ⟨s.1, ConjClasses.mem_carrier_mk⟩))
  have hdenom : (0 : ℝ) < Nat.card (N.field ≃ₐ[ℚ] N.field) := by
    exact_mod_cast Nat.card_pos (α := N.field ≃ₐ[ℚ] N.field)
  have hpositive : (0 : ℝ) <
      ((ConjClasses.mk s.1).carrier.ncard : ℝ) /
        (Nat.card (N.field ≃ₐ[ℚ] N.field) : ℝ) :=
    div_pos hnum hdenom
  have hnonempty : S.Nonempty := by
    by_contra hempty
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hfin : S.Finite := by
      rw [hSempty]
      exact Set.finite_empty
    have hzero : NU.Chebotarev.HasDirichletDensity S 0 :=
      NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfin
    have heq : ((ConjClasses.mk s.1).carrier.ncard : ℝ) /
        (Nat.card (N.field ≃ₐ[ℚ] N.field) : ℝ) = 0 :=
      tendsto_nhds_unique hden hzero
    exact (ne_of_gt hpositive) heq
  obtain ⟨q, hq⟩ := hnonempty
  rcases hq with ⟨hunramified, w, hwq, hclass⟩
  let f : N.field ≃ₐ[ℚ] N.field :=
    NU.Chebotarev.arithFrobeniusAt (K := ℚ) (L := N.field) w
  have hconj : IsConj f s.1 := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact hclass
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  let w' : NU.Chebotarev.PrimeIdeal N.field :=
    { asIdeal := a • w.asIdeal
      isPrime := w.isPrime.smul a
      ne_bot := by
        intro hbot
        apply w.ne_bot
        have h := congrArg (fun I : Ideal (𝓞 N.field) => a⁻¹ • I) hbot
        simpa using h }
  have hw'q : w'.asIdeal.LiesOver q.asIdeal := ⟨by
    change q.asIdeal = Ideal.under (𝓞 ℚ) (a • w.asIdeal)
    rw [Ideal.under_smul]
    exact hwq.over⟩
  have hfrob : IsArithFrobAt (𝓞 ℚ) s.1 w'.asIdeal := by
    have hf := IsArithFrobAt.arithFrobAt
      (𝓞 ℚ) (N.field ≃ₐ[ℚ] N.field) w.asIdeal
    have hfc := hf.conj a
    change IsArithFrobAt (𝓞 ℚ) (a * f * a⁻¹) w'.asIdeal at hfc
    rw [ha] at hfc
    exact hfc
  exact finitePrimeFrobeniusLiftingConstruction
    F N hFN s hs q w' hunramified hw'q hfrob

/-- Strengthened Frobenius choice retaining the uniqueness of the normalized
lift's image in the selected unramified finite quotient. -/
theorem exists_degreeOne_arithmeticFrobenius_unique
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (s : relativeGaloisGroup F N hFN)
    (hs : Subgroup.zpowers s = ⊤) :
    ∃ P : AbsolutePrime,
      IsAbsoluteDegreeOne F (finitePrime F P) ∧
      IsUnramifiedAbove (extensionOfLE F N hFN) (finitePrime F P) ∧
      ∃ phi : decompositionGroup F P,
        IsArithmeticFrobeniusLift F P phi ∧
        finiteQuotientMap F N hFN phi.1 = s ∧
        ∀ psi : decompositionGroup F P,
          IsArithmeticFrobeniusLift F P psi →
          finiteQuotientMap F N hFN psi.1 = s :=
  degreeOneFrobeniusConstruction F N hFN s hs

/-- Blueprint §5.1, the absolute-degree-one Frobenius choice used in
`prop:cyclic`: a prescribed cyclic generator is represented by a normalized
arithmetic Frobenius lift at an unramified absolute-degree-one prime. -/
theorem exists_degreeOne_arithmeticFrobenius
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (s : relativeGaloisGroup F N hFN)
    (hs : Subgroup.zpowers s = ⊤) :
    ∃ P : AbsolutePrime,
      IsAbsoluteDegreeOne F (finitePrime F P) ∧
      IsUnramifiedAbove (extensionOfLE F N hFN) (finitePrime F P) ∧
      ∃ phi : decompositionGroup F P,
        IsArithmeticFrobeniusLift F P phi ∧
        finiteQuotientMap F N hFN phi.1 = s := by
  obtain ⟨P, hdegree, hunramified, phi, hfrob, hphi, _⟩ :=
    exists_degreeOne_arithmeticFrobenius_unique F N hFN s hs
  exact ⟨P, hdegree, hunramified, phi, hfrob, hphi⟩

/-- A rewrite-friendly form of (L4) when the target prime and lift are
identified by explicit equalities. -/
theorem arithmeticFrobeniusLift_iff_of_apply
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P Q : AbsolutePrime) (hQ : primeCorrespondence theta P = Q)
    (g : decompositionGroup F₁ P) (g' : decompositionGroup F₂ Q)
    (hg : g'.1 = theta g.1) :
    IsArithmeticFrobeniusLift F₁ P g ↔
      IsArithmeticFrobeniusLift F₂ Q g' := by
  subst Q
  have heq : decompositionGroupEquiv theta P g = g' := by
    apply Subtype.ext
    rw [decompositionGroupEquiv_apply]
    exact hg.symm
  rw [← heq]
  exact primeCorrespondence_frobeniusLift_L4 theta P g

/-- A Frobenius generator makes the open absolute group the product of the
level kernel and the decomposition group; this is blueprint
`eq:product-G2` (and, after transport, `eq:product-G1`). -/
theorem levelKernel_sup_decompositionGroup_eq_top
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (P : AbsolutePrime)
    (phi : decompositionGroup F P)
    (hgen : Subgroup.zpowers (finiteQuotientMap F N hFN phi.1) = ⊤) :
    (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F) ⊔
      decompositionGroup F P = ⊤ := by
  apply top_unique
  intro x hx
  let q := finiteQuotientMap F N hFN
  have hmem : q x ∈ Subgroup.zpowers (q phi.1) := by
    rw [hgen]
    trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  let d : absoluteGaloisGroup F := phi.1 ^ n
  have hd : d ∈ decompositionGroup F P :=
    (decompositionGroup F P).zpow_mem phi.2 n
  let k : absoluteGaloisGroup F := x * d⁻¹
  have hqk : q k = 1 := by
    dsimp [k, d]
    rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  have hk : k ∈ (absoluteGaloisGroup N).subgroupOf
      (absoluteGaloisGroup F) := by
    intro y
    calc
      k.1 y.1 = N.field.val ((q k).1 y) :=
        (finiteQuotientMap_apply F N hFN k y).symm
      _ = N.field.val y := by rw [hqk]; rfl
  have hksup : k ∈
      (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F) ⊔
        decompositionGroup F P :=
    (show (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F) ≤ _
      from le_sup_left) hk
  have hdsup : d ∈
      (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F) ⊔
        decompositionGroup F P :=
    (show decompositionGroup F P ≤ _ from le_sup_right) hd
  have hmul := ((absoluteGaloisGroup N).subgroupOf
      (absoluteGaloisGroup F) ⊔ decompositionGroup F P).mul_mem hksup hdsup
  simpa [k, d, mul_assoc] using hmul

/-- Restriction of an ambient automorphism to a common finite normal level. -/
noncomputable def ambientRestriction
    (N : NumberFieldInOmega) [IsGalois ℚ N.field] :
    RationalAbsoluteGaloisGroup →* (N.field ≃ₐ[ℚ] N.field) :=
  AlgEquiv.restrictNormalHom N.field

/-- Defining equation for ambient restriction. -/
@[simp]
theorem ambientRestriction_apply
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (alpha : RationalAbsoluteGaloisGroup) (x : N.field) :
    N.field.val (ambientRestriction N alpha x) = alpha (N.field.val x) :=
  AlgEquiv.restrictNormal_commutes alpha N.field x

/-- The finite-level conjugation map `alpha_{*,N}`.  Its source and target
are the literal relative Galois subgroups of `Gal(N/ℚ)`. -/
noncomputable def finiteConjugationIso
    (F₁ F₂ N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field) :
    relativeGaloisGroup F₁ N h₁ ≃*
      relativeGaloisGroup F₂ N h₂ := by
  let a := ambientRestriction N alpha
  let forward : relativeGaloisGroup F₁ N h₁ →
      relativeGaloisGroup F₂ N h₂ := fun g =>
    ⟨a⁻¹ * g.1 * a, by
      intro x
      let y : N.field := ⟨x.1, h₂ x.2⟩
      have haxF₁ : alpha x.1 ∈ F₁.field := by
        rw [← hfield, mem_conjugateField_iff]
        simp
      let z : F₁.field := ⟨alpha x.1, haxF₁⟩
      have hgy : g.1 (a y) = a y := by
        have hay : a y = ⟨z.1, h₁ z.2⟩ := by
          apply N.field.val.injective
          exact ambientRestriction_apply N alpha y
        rw [hay]
        exact g.2 z
      change a.symm (g.1 (a y)) = y
      rw [hgy, a.symm_apply_apply]⟩
  have hsymmfield : conjugateField alpha.symm F₁.field = F₂.field := by
    ext x
    rw [mem_conjugateField_iff, ← hfield, mem_conjugateField_iff]
    simp
  let backward : relativeGaloisGroup F₂ N h₂ →
      relativeGaloisGroup F₁ N h₁ := fun g =>
    ⟨a * g.1 * a⁻¹, by
      intro x
      let y : N.field := ⟨x.1, h₁ x.2⟩
      have haxF₂ : alpha.symm x.1 ∈ F₂.field := by
        rw [← hsymmfield, mem_conjugateField_iff]
        simp
      let z : F₂.field := ⟨alpha.symm x.1, haxF₂⟩
      have hgy : g.1 (a.symm y) = a.symm y := by
        have hay : a.symm y = ⟨z.1, h₂ z.2⟩ := by
          apply N.field.val.injective
          have ha_inv : a.symm = ambientRestriction N alpha.symm := by
            change (ambientRestriction N alpha)⁻¹ = _
            rw [← map_inv]
            rfl
          rw [ha_inv]
          exact ambientRestriction_apply N alpha.symm y
        rw [hay]
        exact g.2 z
      change a (g.1 (a.symm y)) = y
      rw [hgy, a.apply_symm_apply]⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro g
        apply Subtype.ext
        simp [forward, backward, a, mul_assoc]
      right_inv := by
        intro g
        apply Subtype.ext
        simp [forward, backward, a, mul_assoc]
      map_mul' := by
        intro g h
        apply Subtype.ext
        simp [forward, a, mul_assoc] }

/-- Defining equation for finite-level contravariant conjugation. -/
@[simp]
theorem finiteConjugationIso_apply
    (F₁ F₂ N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field)
    (g : relativeGaloisGroup F₁ N h₁) :
    (finiteConjugationIso F₁ F₂ N h₁ h₂ alpha hfield g).1 =
      (ambientRestriction N alpha)⁻¹ * g.1 *
        ambientRestriction N alpha := by
  rfl

/-- Blueprint Proposition `prop:cyclic`: if `N/F₂` is cyclic, the quotient
isomorphism induced by `theta` is induced by one ambient conjugation carrying
`F₂` literally onto `F₁`.

Absolute degree one is essential in the proof: it is what upgrades the local
decomposition group to a subgroup of `G_{F_i}` before the product argument. -/
theorem cyclic_quotient_is_conjugation
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂)
    [IsCyclic (relativeGaloisGroup F₂ N h₂)] :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∃ hfield : conjugateField alpha F₂.field = F₁.field,
        finiteConjugationIso F₁ F₂ N h₁ h₂ alpha hfield =
          finiteQuotientIso theta N h₁ h₂ hN := by
  obtain ⟨s, hs_mem⟩ :=
    (IsCyclic.exists_generator : ∃ s : relativeGaloisGroup F₂ N h₂,
      ∀ x, x ∈ Subgroup.zpowers s)
  have hs : Subgroup.zpowers s = ⊤ := by
    apply top_unique
    intro x hx
    exact hs_mem x
  obtain ⟨P₂, hdegree₂, hunramified₂, phi₂, hfrob₂, hphi₂, hunique₂⟩ :=
    exists_degreeOne_arithmeticFrobenius_unique F₂ N h₂ s hs
  obtain ⟨P₁, rfl⟩ := (primeCorrespondence theta).surjective P₂
  let phi₁ : decompositionGroup F₁ P₁ :=
    (decompositionGroupEquiv theta P₁).symm phi₂
  have htheta_phi : theta phi₁.1 = phi₂.1 := by
    have h := decompositionGroupEquiv_apply theta P₁ phi₁
    have heq : decompositionGroupEquiv theta P₁ phi₁ = phi₂ :=
      (decompositionGroupEquiv theta P₁).apply_symm_apply phi₂
    rw [heq] at h
    exact h.symm
  have hdegree₁ : IsAbsoluteDegreeOne F₁ (finitePrime F₁ P₁) :=
    (primeCorrespondence_degreeOne_iff theta P₁).mpr hdegree₂
  have hfrob₁ : IsArithmeticFrobeniusLift F₁ P₁ phi₁ := by
    apply (primeCorrespondence_frobeniusLift_L4 theta P₁ phi₁).mpr
    have heq : decompositionGroupEquiv theta P₁ phi₁ = phi₂ :=
      (decompositionGroupEquiv theta P₁).apply_symm_apply phi₂
    rw [heq]
    exact hfrob₂
  let sigmaN := finiteQuotientIso theta N h₁ h₂ hN
  let t : relativeGaloisGroup F₁ N h₁ := finiteQuotientMap F₁ N h₁ phi₁.1
  have hsigma_t : sigmaN t = s := by
    dsimp [sigmaN, t]
    rw [finiteQuotientIso_comp_restriction]
    have : theta phi₁.1 = phi₂.1 := htheta_phi
    rw [this, hphi₂]
  have ht : Subgroup.zpowers t = ⊤ := by
    apply top_unique
    intro x hx
    have hmem : sigmaN x ∈ Subgroup.zpowers s := by
      rw [hs]
      trivial
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, sigmaN.injective ?_⟩
    rw [map_zpow, hsigma_t, hn]
  have hproduct₁ := levelKernel_sup_decompositionGroup_eq_top
    F₁ N h₁ P₁ phi₁ ht
  have hgen₂ : Subgroup.zpowers
      (finiteQuotientMap F₂ N h₂ phi₂.1) = ⊤ := by
    rw [hphi₂]
    exact hs
  have hproduct₂ := levelKernel_sup_decompositionGroup_eq_top
    F₂ N h₂ (primeCorrespondence theta P₁) phi₂ hgen₂
  have hrational :
      finitePrime rationalNumberField (primeCorrespondence theta P₁) =
        finitePrime rationalNumberField P₁ := by
    apply (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      rationalBottomIntegersEquiv).injective
    rw [rationalBottomIntegersEquiv_finitePrime F₂,
      rationalBottomIntegersEquiv_finitePrime F₁]
    exact (primeCorrespondence_invariants_L3 theta P₁).1.symm
  obtain ⟨alphaQ, halpha⟩ := exists_smul_of_finitePrime_eq
    rationalNumberField (primeCorrespondence theta P₁) P₁ hrational
  let alpha : RationalAbsoluteGaloisGroup := alphaQ.1
  have halpha' : alpha • primeCorrespondence theta P₁ = P₁ := halpha
  have halpha_inv : alpha.symm • P₁ = primeCorrespondence theta P₁ :=
    inv_smul_eq_iff.mpr halpha'.symm
  have halpha_inv' : (alpha⁻¹ : RationalAbsoluteGaloisGroup) • P₁ =
      primeCorrespondence theta P₁ := halpha_inv
  let c₂ : absoluteGaloisGroup F₂ →* RationalAbsoluteGaloisGroup :=
    { toFun := fun g => alpha * g.1 * alpha⁻¹
      map_one' := by
        change alpha * (1 : RationalAbsoluteGaloisGroup) * alpha⁻¹ = 1
        group
      map_mul' := by
        intro g h
        change alpha * (g.1 * h.1) * alpha⁻¹ =
          (alpha * g.1 * alpha⁻¹) * (alpha * h.1 * alpha⁻¹)
        group }
  have hconj₂ (g : absoluteGaloisGroup F₂) :
      c₂ g ∈ absoluteGaloisGroup F₁ := by
    let K₂ := (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₂)
    let D₂ := decompositionGroup F₂ (primeCorrespondence theta P₁)
    have hK : K₂ ≤ Subgroup.comap c₂ (absoluteGaloisGroup F₁) := by
      intro k hk
      change c₂ k ∈ absoluteGaloisGroup F₁
      intro x
      let y : N.field := ⟨x.1, h₁ x.2⟩
      let z : N.field := (ambientRestriction N alpha).symm y
      have hz : z.1 = alpha.symm x.1 := by
        have ha_inv : (ambientRestriction N alpha).symm =
            ambientRestriction N alpha.symm := by
          change (ambientRestriction N alpha)⁻¹ = _
          rw [← map_inv]
          rfl
        change N.field.val ((ambientRestriction N alpha).symm y) = _
        rw [ha_inv]
        exact ambientRestriction_apply N alpha.symm y
      have hkz : k.1 z.1 = z.1 := hk z
      change alpha (k.1 (alpha.symm x.1)) = x.1
      rw [← hz, hkz, hz, alpha.apply_symm_apply]
    have hD : D₂ ≤ Subgroup.comap c₂ (absoluteGaloisGroup F₁) := by
      intro d hd
      change alpha * d.1 * alpha⁻¹ ∈ absoluteGaloisGroup F₁
      apply (degreeOne_iff_rationalDecompositionGroup_le F₁ P₁).mp hdegree₁
      have hd' : d.1 • primeCorrespondence theta P₁ =
          primeCorrespondence theta P₁ := hd
      calc
        (alpha * d.1 * alpha⁻¹) • P₁ =
            alpha • (d.1 • (alpha⁻¹ • P₁)) := by
              rw [mul_smul, mul_smul]
        _ = alpha • (d.1 • primeCorrespondence theta P₁) := by
          rw [halpha_inv']
        _ = alpha • primeCorrespondence theta P₁ := by rw [hd']
        _ = P₁ := halpha'
    have hle : K₂ ⊔ D₂ ≤ Subgroup.comap c₂ (absoluteGaloisGroup F₁) :=
      sup_le hK hD
    apply hle
    rw [hproduct₂]
    trivial
  let c₁ : absoluteGaloisGroup F₁ →* RationalAbsoluteGaloisGroup :=
    { toFun := fun g => alpha⁻¹ * g.1 * alpha
      map_one' := by
        change alpha⁻¹ * (1 : RationalAbsoluteGaloisGroup) * alpha = 1
        group
      map_mul' := by
        intro g h
        change alpha⁻¹ * (g.1 * h.1) * alpha =
          (alpha⁻¹ * g.1 * alpha) * (alpha⁻¹ * h.1 * alpha)
        group }
  have hconj₁ (g : absoluteGaloisGroup F₁) :
      c₁ g ∈ absoluteGaloisGroup F₂ := by
    let K₁ := (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₁)
    let D₁ := decompositionGroup F₁ P₁
    have hK : K₁ ≤ Subgroup.comap c₁ (absoluteGaloisGroup F₂) := by
      intro k hk
      change c₁ k ∈ absoluteGaloisGroup F₂
      intro x
      let y : N.field := ⟨x.1, h₂ x.2⟩
      let z : N.field := ambientRestriction N alpha y
      have hz : z.1 = alpha x.1 := ambientRestriction_apply N alpha y
      have hkz : k.1 z.1 = z.1 := hk z
      change alpha.symm (k.1 (alpha x.1)) = x.1
      rw [← hz, hkz, hz, alpha.symm_apply_apply]
    have hD : D₁ ≤ Subgroup.comap c₁ (absoluteGaloisGroup F₂) := by
      intro d hd
      change alpha⁻¹ * d.1 * alpha ∈ absoluteGaloisGroup F₂
      apply (degreeOne_iff_rationalDecompositionGroup_le F₂
        (primeCorrespondence theta P₁)).mp hdegree₂
      have hd' : d.1 • P₁ = P₁ := hd
      calc
        (alpha⁻¹ * d.1 * alpha) • primeCorrespondence theta P₁ =
            alpha⁻¹ • (d.1 •
              (alpha • primeCorrespondence theta P₁)) := by
                rw [mul_smul, mul_smul]
        _ = alpha⁻¹ • (d.1 • P₁) := by rw [halpha']
        _ = alpha⁻¹ • P₁ := by rw [hd']
        _ = primeCorrespondence theta P₁ := halpha_inv
    have hle : K₁ ⊔ D₁ ≤ Subgroup.comap c₁ (absoluteGaloisGroup F₂) :=
      sup_le hK hD
    apply hle
    rw [hproduct₁]
    trivial
  have hgroup : Subgroup.map (MulAut.conj alpha).toMonoidHom
      (absoluteGaloisGroup F₂) = absoluteGaloisGroup F₁ := by
    apply le_antisymm
    · rintro y ⟨g, hg, rfl⟩
      exact hconj₂ ⟨g, hg⟩
    · intro y hy
      have hback := hconj₁ ⟨y, hy⟩
      refine ⟨alpha⁻¹ * y * alpha, hback, ?_⟩
      change alpha * (alpha⁻¹ * y * alpha) * alpha⁻¹ = y
      group
  have hset : (conjugateField alpha F₂.field : Set Omega) =
      alpha • (F₂.field : Set Omega) := by
    ext x
    rw [show x ∈ (conjugateField alpha F₂.field : Set Omega) ↔
      alpha.symm x ∈ F₂.field from mem_conjugateField_iff alpha F₂.field x]
    simp only [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  have hfix : (conjugateField alpha F₂.field).fixingSubgroup =
      F₁.field.fixingSubgroup := by
    change fixingSubgroup RationalAbsoluteGaloisGroup
        (conjugateField alpha F₂.field : Set Omega) =
      fixingSubgroup RationalAbsoluteGaloisGroup (F₁.field : Set Omega)
    rw [hset,
      SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj]
    exact hgroup
  have hfield : conjugateField alpha F₂.field = F₁.field := by
    letI : IsGalois ℚ Omega := by
      letI : IsAlgClosure ℚ Omega :=
        ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
      exact ⟨⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup
        (conjugateField alpha F₂.field),
      ← InfiniteGalois.fixedField_fixingSubgroup F₁.field, hfix]
  let eta : absoluteGaloisGroup F₂ ≃ₜ* absoluteGaloisGroup F₁ :=
    { toFun := fun g => ⟨c₂ g, hconj₂ g⟩
      invFun := fun g => ⟨c₁ g, hconj₁ g⟩
      left_inv := by
        intro g
        apply Subtype.ext
        change alpha⁻¹ * (alpha * g.1 * alpha⁻¹) * alpha = g.1
        group
      right_inv := by
        intro g
        apply Subtype.ext
        change alpha * (alpha⁻¹ * g.1 * alpha) * alpha⁻¹ = g.1
        group
      map_mul' := by
        intro g h
        apply Subtype.ext
        exact map_mul c₂ g h
      continuous_toFun := by
        change Continuous (fun g : absoluteGaloisGroup F₂ =>
          (⟨alpha * g.1 * alpha⁻¹, hconj₂ g⟩ : absoluteGaloisGroup F₁))
        fun_prop
      continuous_invFun := by
        change Continuous (fun g : absoluteGaloisGroup F₁ =>
          (⟨alpha⁻¹ * g.1 * alpha, hconj₁ g⟩ : absoluteGaloisGroup F₂))
        fun_prop }
  have hmapD : Subgroup.map eta.toMulEquiv.toMonoidHom
      (decompositionGroup F₂ (primeCorrespondence theta P₁)) =
        decompositionGroup F₁ P₁ := by
    ext g
    constructor
    · rintro ⟨d, hd, rfl⟩
      change (alpha * d.1 * alpha⁻¹) • P₁ = P₁
      have hd' : d.1 • primeCorrespondence theta P₁ =
          primeCorrespondence theta P₁ := hd
      calc
        (alpha * d.1 * alpha⁻¹) • P₁ =
            alpha • (d.1 • (alpha⁻¹ • P₁)) := by
              rw [mul_smul, mul_smul]
        _ = alpha • (d.1 • primeCorrespondence theta P₁) := by
          rw [halpha_inv']
        _ = alpha • primeCorrespondence theta P₁ := by rw [hd']
        _ = P₁ := halpha'
    · intro hg
      let d : absoluteGaloisGroup F₂ := eta.symm g
      have hd : d ∈ decompositionGroup F₂
          (primeCorrespondence theta P₁) := by
        change d.1 • primeCorrespondence theta P₁ =
          primeCorrespondence theta P₁
        have hg' : g.1 • P₁ = P₁ := hg
        change (alpha⁻¹ * g.1 * alpha) •
          primeCorrespondence theta P₁ = primeCorrespondence theta P₁
        calc
          (alpha⁻¹ * g.1 * alpha) • primeCorrespondence theta P₁ =
              alpha⁻¹ • (g.1 •
                (alpha • primeCorrespondence theta P₁)) := by
                  rw [mul_smul, mul_smul]
          _ = alpha⁻¹ • (g.1 • P₁) := by rw [halpha']
          _ = alpha⁻¹ • P₁ := by rw [hg']
          _ = primeCorrespondence theta P₁ := halpha_inv'
      refine ⟨d, hd, ?_⟩
      exact eta.apply_symm_apply g
  have hprimeEta : primeCorrespondence eta
      (primeCorrespondence theta P₁) = P₁ :=
    (eq_primeCorrespondence_of_map_decompositionGroup eta
      (primeCorrespondence theta P₁) P₁ hmapD).symm
  let psi : decompositionGroup F₁ P₁ :=
    ⟨eta phi₂.1, by
      have hm : eta phi₂.1 ∈ Subgroup.map eta.toMulEquiv.toMonoidHom
          (decompositionGroup F₂ (primeCorrespondence theta P₁)) :=
        ⟨phi₂.1, phi₂.2, rfl⟩
      rw [hmapD] at hm
      exact hm⟩
  have hfrobPsi : IsArithmeticFrobeniusLift F₁ P₁ psi :=
    (arithmeticFrobeniusLift_iff_of_apply eta
      (primeCorrespondence theta P₁) P₁ hprimeEta phi₂ psi rfl).mp hfrob₂
  have hpsi_under : psi.1.1 = alpha * phi₂.1.1 * alpha⁻¹ := rfl
  let chi₂ := decompositionGroupEquiv theta P₁ psi
  have hfrobChi₂ : IsArithmeticFrobeniusLift F₂
      (primeCorrespondence theta P₁) chi₂ :=
    (primeCorrespondence_frobeniusLift_L4 theta P₁ psi).mp hfrobPsi
  have hchi₂ : finiteQuotientMap F₂ N h₂ chi₂.1 = s :=
    hunique₂ chi₂ hfrobChi₂
  have hqpsi : finiteQuotientMap F₁ N h₁ psi.1 = t := by
    apply sigmaN.injective
    calc
      sigmaN (finiteQuotientMap F₁ N h₁ psi.1) =
          finiteQuotientMap F₂ N h₂ (theta psi.1) :=
        finiteQuotientIso_comp_restriction theta N h₁ h₂ hN psi.1
      _ = finiteQuotientMap F₂ N h₂ chi₂.1 := by
        have h := decompositionGroupEquiv_apply theta P₁ psi
        exact congrArg (finiteQuotientMap F₂ N h₂) h.symm
      _ = s := hchi₂
      _ = sigmaN t := hsigma_t.symm
  have hrestrictPsi : (finiteQuotientMap F₁ N h₁ psi.1).1 =
      ambientRestriction N alpha *
        (finiteQuotientMap F₂ N h₂ phi₂.1).1 *
          (ambientRestriction N alpha)⁻¹ := by
    change AlgEquiv.restrictNormalHom N.field psi.1.1 = _
    rw [hpsi_under, map_mul, map_mul, map_inv]
    rfl
  have honGenerator :
      finiteConjugationIso F₁ F₂ N h₁ h₂ alpha hfield t = s := by
    apply Subtype.ext
    rw [finiteConjugationIso_apply]
    have hqpsi' := congrArg Subtype.val hqpsi
    have hphi₂' := congrArg Subtype.val hphi₂
    rw [hrestrictPsi, hphi₂'] at hqpsi'
    rw [← hqpsi']
    group
  refine ⟨alpha, hfield, ?_⟩
  apply MulEquiv.ext
  intro g
  have hg : g ∈ Subgroup.zpowers t := by
    rw [ht]
    trivial
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← hn, map_zpow, map_zpow, honGenerator, hsigma_t]

end

end NU.NeukirchUchida
