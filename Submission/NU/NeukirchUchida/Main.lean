import Submission.NU.NeukirchUchida.Compactness

/-!
# The Neukirch--Uchida theorem

Final assembly from blueprint §7: the pointed theorem `thm:main`, the outer
form `cor:outer`, and transport to arbitrary chosen separable closures.
-/

open scoped NumberField Pointwise

namespace NU.NeukirchUchida

noncomputable section

/-- `alpha` induces `theta` when it carries the target field onto the source
field and its contravariant conjugation map is exactly `theta`. -/
def Induces
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (alpha : RationalAbsoluteGaloisGroup) : Prop :=
  ∃ hfield : conjugateField alpha F₂.field = F₁.field,
    ambientConjugationIso F₁ F₂ alpha hfield = theta

/-- Unfolded defining equation for `Induces`. -/
theorem induces_iff
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (alpha : RationalAbsoluteGaloisGroup) :
    Induces theta alpha ↔
      ∃ hfield : conjugateField alpha F₂.field = F₁.field,
        ambientConjugationIso F₁ F₂ alpha hfield = theta :=
  Iff.rfl

/-- Blueprint Theorem `thm:main` (Neukirch--Uchida, pointed form).

Every topological isomorphism `G_{F₁} ≃ G_{F₂}` is induced by a unique
`alpha ∈ G_ℚ`, with the contravariant convention
`theta(g) = alpha⁻¹ g alpha` and the literal field equality
`alpha(F₂) = F₁`. -/
theorem neukirchUchida
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    ∃! alpha : RationalAbsoluteGaloisGroup, Induces theta alpha := by
  obtain ⟨alpha, hfield, halpha⟩ :=
    exists_global_inducingAutomorphism theta
  refine ⟨alpha, ⟨hfield, halpha⟩, ?_⟩
  intro beta hbeta
  obtain ⟨hfieldBeta, hbetaTheta⟩ := hbeta
  exact (global_inducingAutomorphism_unique theta alpha beta
    hfield hfieldBeta halpha hbetaTheta).symm

/-! ## Outer form -/

/-- Two pointed profinite isomorphisms differ only by an inner automorphism
of the target. -/
def IsInnerConjugate
    {F₁ F₂ : NumberFieldInOmega}
    (theta phi : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) : Prop :=
  ∃ h : absoluteGaloisGroup F₂,
    ∀ g : absoluteGaloisGroup F₁,
      phi g = h⁻¹ * theta g * h

/-- Inner conjugacy is an equivalence relation. -/
theorem isInnerConjugate_equivalence
    (F₁ F₂ : NumberFieldInOmega) :
    Equivalence (@IsInnerConjugate F₁ F₂) := by
  constructor
  · intro theta
    exact ⟨1, by simp⟩
  · intro theta phi h
    obtain ⟨a, ha⟩ := h
    refine ⟨a⁻¹, fun g => ?_⟩
    rw [ha g]
    group
  · intro theta phi psi h₁ h₂
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    refine ⟨a * b, fun g => ?_⟩
    rw [hb g, ha g]
    group

/-- The setoid defining outer isomorphisms. -/
def outerIsoSetoid (F₁ F₂ : NumberFieldInOmega) :
    Setoid (absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) where
  r := IsInnerConjugate
  iseqv := isInnerConjugate_equivalence F₁ F₂

/-- Outer isomorphisms from `G_{F₁}` to `G_{F₂}`. -/
abbrev OuterIso (F₁ F₂ : NumberFieldInOmega) :=
  Quotient (outerIsoSetoid F₁ F₂)

/-- A field isomorphism between the embedded number fields extends to an
ambient automorphism of `Omega`. -/
theorem exists_ambientExtension
    {F₁ F₂ : NumberFieldInOmega} (e : F₂.field ≃ₐ[ℚ] F₁.field) :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∀ x : F₂.field, alpha x.1 = (e x).1 := by
  let f : F₂.field →ₐ[ℚ] Omega := F₁.field.val.comp e.toAlgHom
  letI : IsAlgClosure ℚ Omega :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  letI : Algebra.IsAlgebraic F₂.field Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) F₂.field
  obtain ⟨f', hf'⟩ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ) (L := F₂.field) (E := Omega) (M := Omega) f
  let alpha : RationalAbsoluteGaloisGroup :=
    AlgEquiv.ofBijective f' (Algebra.IsAlgebraic.algHom_bijective f')
  refine ⟨alpha, fun x => ?_⟩
  exact DFunLike.congr_fun hf' x

/-- A selected ambient extension of a number-field isomorphism. -/
noncomputable def ambientExtension
    {F₁ F₂ : NumberFieldInOmega} (e : F₂.field ≃ₐ[ℚ] F₁.field) :
    RationalAbsoluteGaloisGroup :=
  (exists_ambientExtension e).choose

/-- Defining restriction equation for the selected ambient extension. -/
@[simp]
theorem ambientExtension_apply
    {F₁ F₂ : NumberFieldInOmega} (e : F₂.field ≃ₐ[ℚ] F₁.field)
    (x : F₂.field) :
    ambientExtension e x.1 = (e x).1 :=
  (exists_ambientExtension e).choose_spec x

/-- The selected extension carries `F₂` literally onto `F₁`. -/
theorem ambientExtension_field
    {F₁ F₂ : NumberFieldInOmega} (e : F₂.field ≃ₐ[ℚ] F₁.field) :
    conjugateField (ambientExtension e) F₂.field = F₁.field := by
  ext y
  constructor
  · intro hy
    rw [mem_conjugateField_iff] at hy
    let x : F₂.field := ⟨(ambientExtension e).symm y, hy⟩
    have h := ambientExtension_apply e x
    have hy' : y = (e x).1 := by simpa [x] using h
    rw [hy']
    exact (e x).2
  · intro hy
    rw [mem_conjugateField_iff]
    let z : F₁.field := ⟨y, hy⟩
    let x : F₂.field := e.symm z
    have h : ambientExtension e x.1 = y := by
      simpa [x, z] using ambientExtension_apply e x
    rw [← h, AlgEquiv.symm_apply_apply]
    exact x.2

private theorem conjugateField_eq_of_apply
    {F₁ F₂ : NumberFieldInOmega} (e : F₂.field ≃ₐ[ℚ] F₁.field)
    (alpha : RationalAbsoluteGaloisGroup)
    (halpha : ∀ x : F₂.field, alpha x.1 = (e x).1) :
    conjugateField alpha F₂.field = F₁.field := by
  ext y
  constructor
  · intro hy
    rw [mem_conjugateField_iff] at hy
    let x : F₂.field := ⟨alpha.symm y, hy⟩
    have h := halpha x
    have hy' : y = (e x).1 := by simpa [x] using h
    rw [hy']
    exact (e x).2
  · intro hy
    rw [mem_conjugateField_iff]
    let z : F₁.field := ⟨y, hy⟩
    let x : F₂.field := e.symm z
    have h : alpha x.1 = y := by
      simpa [x, z] using halpha x
    rw [← h, AlgEquiv.symm_apply_apply]
    exact x.2

private noncomputable def fieldEquivOfAmbient
    {F₁ F₂ : NumberFieldInOmega} (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field) :
    F₂.field ≃ₐ[ℚ] F₁.field where
  toFun x := ⟨alpha x.1, by
    rw [← hfield, mem_conjugateField_iff]
    simpa using x.2⟩
  invFun x := ⟨alpha.symm x.1, by
    have hx : x.1 ∈ conjugateField alpha F₂.field := hfield.symm ▸ x.2
    rwa [mem_conjugateField_iff] at hx⟩
  left_inv x := by
    apply Subtype.ext
    exact alpha.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact alpha.apply_symm_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul alpha x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add alpha x.1 y.1
  commutes' x := by
    apply Subtype.ext
    exact alpha.commutes x

/-- The natural contravariant map from field isomorphisms to outer
isomorphisms.  Quotienting makes it independent of the selected ambient
extension. -/
noncomputable def fieldIsoToOuterIso
    (F₁ F₂ : NumberFieldInOmega) :
    (F₂.field ≃ₐ[ℚ] F₁.field) → OuterIso F₁ F₂ :=
  fun e => Quotient.mk (outerIsoSetoid F₁ F₂)
    (ambientConjugationIso F₁ F₂ (ambientExtension e)
      (ambientExtension_field e))

/-- Independence of the chosen extension: every ambient extension of the
same base-field isomorphism defines the same outer class.  This equation is
what makes `fieldIsoToOuterIso` natural rather than a bare choice. -/
theorem fieldIsoToOuterIso_eq_mk_of_extension
    (F₁ F₂ : NumberFieldInOmega)
    (e : F₂.field ≃ₐ[ℚ] F₁.field)
    (alpha : RationalAbsoluteGaloisGroup)
    (halpha : ∀ x : F₂.field, alpha x.1 = (e x).1)
    (hfield : conjugateField alpha F₂.field = F₁.field) :
    fieldIsoToOuterIso F₁ F₂ e =
      Quotient.mk (outerIsoSetoid F₁ F₂)
        (ambientConjugationIso F₁ F₂ alpha hfield) := by
  let h : absoluteGaloisGroup F₂ :=
    ⟨(ambientExtension e)⁻¹ * alpha, by
      intro x
      change (ambientExtension e).symm (alpha x.1) = x.1
      rw [halpha x, ← ambientExtension_apply e x,
        AlgEquiv.symm_apply_apply]⟩
  apply Quotient.sound
  refine ⟨h, fun g => ?_⟩
  apply Subtype.ext
  change alpha⁻¹ * g.1 * alpha =
    h.1⁻¹ * ((ambientExtension e)⁻¹ * g.1 * ambientExtension e) * h.1
  dsimp [h]
  group

/-- Blueprint Corollary `cor:outer`: the natural contravariant map is a
bijection `Iso(F₂,F₁) ≃ OutIso(G_{F₁},G_{F₂})`. -/
theorem fieldIsoToOuterIso_bijective
    (F₁ F₂ : NumberFieldInOmega) :
    Function.Bijective (fieldIsoToOuterIso F₁ F₂) := by
  constructor
  · intro e f hef
    let thetaE := ambientConjugationIso F₁ F₂ (ambientExtension e)
      (ambientExtension_field e)
    let thetaF := ambientConjugationIso F₁ F₂ (ambientExtension f)
      (ambientExtension_field f)
    have hquot :
        Quotient.mk (outerIsoSetoid F₁ F₂) thetaE =
          Quotient.mk (outerIsoSetoid F₁ F₂) thetaF := hef
    obtain ⟨h, hh⟩ := Quotient.exact hquot
    let alpha : RationalAbsoluteGaloisGroup := ambientExtension e * h.1
    have halpha (x : F₂.field) : alpha x.1 = (e x).1 := by
      change ambientExtension e (h.1 x.1) = (e x).1
      have hhfix : h.1 x.1 = x.1 := h.2 x
      rw [hhfix, ambientExtension_apply]
    have hfieldAlpha : conjugateField alpha F₂.field = F₁.field :=
      conjugateField_eq_of_apply e alpha halpha
    have hthetaAlpha :
        ambientConjugationIso F₁ F₂ alpha hfieldAlpha = thetaF := by
      apply ContinuousMulEquiv.ext
      intro g
      apply Subtype.ext
      calc
        (ambientConjugationIso F₁ F₂ alpha hfieldAlpha g).1 =
            h.1⁻¹ * (thetaE g).1 * h.1 := by
          change alpha⁻¹ * g.1 * alpha =
            h.1⁻¹ * ((ambientExtension e)⁻¹ * g.1 * ambientExtension e) * h.1
          dsimp [alpha]
          group
        _ = (thetaF g).1 := congrArg Subtype.val (hh g).symm
    have heq : ambientExtension f = alpha :=
      (neukirchUchida thetaF).unique
        ⟨ambientExtension_field f, rfl⟩
        ⟨hfieldAlpha, hthetaAlpha⟩
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc
      (e x).1 = alpha x.1 := (halpha x).symm
      _ = ambientExtension f x.1 := by rw [heq]
      _ = (f x).1 := ambientExtension_apply f x
  · intro q
    refine Quotient.inductionOn q ?_
    intro theta
    obtain ⟨alpha, ⟨hfield, htheta⟩, _⟩ := neukirchUchida theta
    let e : F₂.field ≃ₐ[ℚ] F₁.field := fieldEquivOfAmbient alpha hfield
    refine ⟨e, ?_⟩
    calc
      fieldIsoToOuterIso F₁ F₂ e =
          Quotient.mk (outerIsoSetoid F₁ F₂)
            (ambientConjugationIso F₁ F₂ alpha hfield) :=
        fieldIsoToOuterIso_eq_mk_of_extension F₁ F₂ e alpha
          (fun _ => rfl) hfield
      _ = Quotient.mk (outerIsoSetoid F₁ F₂) theta := by rw [htheta]

/-- Automorphism specialization of `cor:outer`. -/
theorem automorphism_outer_bijective (F : NumberFieldInOmega) :
    Function.Bijective (fieldIsoToOuterIso F F) :=
  fieldIsoToOuterIso_bijective F F

private theorem ringEquiv_symm_algebraMap
    {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (e0 : K ≃+* K') (e : L ≃+* L')
    (he : ∀ x : K, e (algebraMap K L x) = algebraMap K' L' (e0 x))
    (x : K') :
    e.symm (algebraMap K' L' x) = algebraMap K L (e0.symm x) := by
  apply e.injective
  simp [he]

private noncomputable def semilinearAutCongr
    {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (e0 : K ≃+* K') (e : L ≃+* L')
    (he : ∀ x : K, e (algebraMap K L x) = algebraMap K' L' (e0 x)) :
    (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L') where
  toFun g :=
    { e.symm.trans (g.toRingEquiv.trans e) with
      commutes' := fun x => by
        change e (g (e.symm (algebraMap K' L' x))) = algebraMap K' L' x
        rw [ringEquiv_symm_algebraMap e0 e he, g.commutes, he,
          e0.apply_symm_apply] }
  invFun g :=
    { e.trans (g.toRingEquiv.trans e.symm) with
      commutes' := fun x => by
        change e.symm (g (e (algebraMap K L x))) = algebraMap K L x
        rw [he, g.commutes, ringEquiv_symm_algebraMap e0 e he,
          e0.symm_apply_apply] }
  left_inv g := by
    ext x
    simp
  right_inv g := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

@[simp]
private theorem semilinearAutCongr_apply
    {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (e0 : K ≃+* K') (e : L ≃+* L')
    (he : ∀ x : K, e (algebraMap K L x) = algebraMap K' L' (e0 x))
    (g : L ≃ₐ[K] L) (x : L') :
    semilinearAutCongr e0 e he g x = e (g (e.symm x)) :=
  rfl

private theorem continuous_semilinearAutCongr
    {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [Algebra.IsIntegral K L]
    (e0 : K ≃+* K') (e : L ≃+* L')
    (he : ∀ x : K, e (algebraMap K L x) = algebraMap K' L' (e0 x)) :
    Continuous (semilinearAutCongr e0 e he) := by
  classical
  apply continuous_of_continuousAt_one
    (semilinearAutCongr e0 e he).toMonoidHom
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  have hs' : s ∈ nhds (1 : L' ≃ₐ[K'] L') := by simpa using hs
  obtain ⟨E, hEfin, hEs⟩ :=
    (krullTopology_mem_nhds_one_iff K' L' s).mp hs'
  letI : FiniteDimensional K' E := hEfin
  let b := Module.finBasis K' E
  let S : Set L := Set.range fun i => e.symm (b i).1
  have hS : S.Finite := Set.finite_range _
  letI : Fintype S := hS.fintype
  let D : IntermediateField K L := IntermediateField.adjoin K S
  letI : FiniteDimensional K D :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      Algebra.IsIntegral.isIntegral x
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨D, inferInstance, fun g hg => ?_⟩
  apply hEs
  change semilinearAutCongr e0 e he g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let xE : E := ⟨x, hx⟩
  have hfix (i : Fin (Module.finrank K' E)) :
      semilinearAutCongr e0 e he g (b i).1 = (b i).1 := by
    rw [semilinearAutCongr_apply]
    have hmemS : e.symm (b i).1 ∈ S := Set.mem_range_self i
    have hmemD : e.symm (b i).1 ∈ D :=
      (IntermediateField.subset_adjoin K S) hmemS
    have hgfix :=
      ((IntermediateField.mem_fixingSubgroup_iff D g).mp hg)
        (e.symm (b i).1) hmemD
    rw [hgfix, e.apply_symm_apply]
  have hmaps :
      (semilinearAutCongr e0 e he g).toLinearMap.comp E.val.toLinearMap =
        E.val.toLinearMap := by
    apply b.ext
    exact hfix
  exact DFunLike.congr_fun hmaps xE

private noncomputable def semilinearAutCongrHomeomorph
    {K K' L L' : Type*}
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    [Algebra.IsIntegral K L] [Algebra.IsIntegral K' L']
    (e0 : K ≃+* K') (e : L ≃+* L')
    (he : ∀ x : K, e (algebraMap K L x) = algebraMap K' L' (e0 x)) :
    (L ≃ₐ[K] L) ≃ₜ* (L' ≃ₐ[K'] L') where
  toMulEquiv := semilinearAutCongr e0 e he
  continuous_toFun := continuous_semilinearAutCongr e0 e he
  continuous_invFun := by
    let he' : ∀ x : K',
        e.symm (algebraMap K' L' x) = algebraMap K L (e0.symm x) :=
      ringEquiv_symm_algebraMap e0 e he
    exact continuous_semilinearAutCongr e0.symm e.symm he'

private noncomputable def numberFieldEmbedding
    (K : Type*) [Field K] [NumberField K] : K →ₐ[ℚ] Omega := by
  letI : IsAlgClosed Omega := AlgebraicClosure.isAlgClosed ℚ
  exact IsAlgClosed.lift

private noncomputable def ambientModel
    (K : Type*) [Field K] [NumberField K] : NumberFieldInOmega where
  field := (numberFieldEmbedding K).fieldRange
  finite := Module.Finite.equiv (numberFieldEmbedding K).equivFieldRange.toLinearEquiv

private noncomputable def ambientBaseEquiv
    (K : Type*) [Field K] [NumberField K] :
    K ≃ₐ[ℚ] (ambientModel K).field :=
  (numberFieldEmbedding K).equivFieldRange

private noncomputable def sepClosureComparison
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    Ksep ≃+* AlgebraicClosure (ambientModel K).field :=
  IsAlgClosure.equivOfEquiv Ksep (AlgebraicClosure (ambientModel K).field)
    (ambientBaseEquiv K).toRingEquiv

@[simp]
private theorem sepClosureComparison_algebraMap
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (x : K) :
    sepClosureComparison K Ksep (algebraMap K Ksep x) =
      algebraMap (ambientModel K).field
        (AlgebraicClosure (ambientModel K).field) (ambientBaseEquiv K x) := by
  exact IsAlgClosure.equivOfEquiv_algebraMap Ksep
    (AlgebraicClosure (ambientModel K).field)
    (ambientBaseEquiv K).toRingEquiv x

private noncomputable def closureGaloisEquiv
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] :
    (Ksep ≃ₐ[K] Ksep) ≃ₜ* absoluteGaloisGroup (ambientModel K) := by
  letI : Algebra.IsIntegral K Ksep := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsIntegral (ambientModel K).field
      (AlgebraicClosure (ambientModel K).field) :=
    Algebra.IsAlgebraic.isIntegral
  exact (semilinearAutCongrHomeomorph
    (ambientBaseEquiv K).toRingEquiv (sepClosureComparison K Ksep)
    (sepClosureComparison_algebraMap K Ksep)).trans
      (ambientAbsoluteGaloisEquiv (ambientModel K)).symm

private noncomputable def ambientSepEquiv
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] : Ksep ≃+* Omega :=
  (sepClosureComparison K Ksep).trans
    (ambientClosureEquiv (ambientModel K)).toRingEquiv

@[simp]
private theorem ambientSepEquiv_algebraMap
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (x : K) :
    ambientSepEquiv K Ksep (algebraMap K Ksep x) =
      (ambientBaseEquiv K x).1 := by
  rw [ambientSepEquiv, RingEquiv.trans_apply,
    sepClosureComparison_algebraMap]
  change ambientClosureEquiv (ambientModel K)
      (algebraMap (ambientModel K).field
        (AlgebraicClosure (ambientModel K).field) (ambientBaseEquiv K x)) = _
  rw [ambientClosureEquiv_algebraMap]
  rfl

private noncomputable def ambientFieldEquiv
    {F₁ F₂ : NumberFieldInOmega} (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field) :
    F₂.field ≃ₐ[ℚ] F₁.field where
  toFun x := ⟨alpha x.1, by
    rw [← hfield, mem_conjugateField_iff]
    simpa using x.2⟩
  invFun x := ⟨alpha.symm x.1, by
    have hx : x.1 ∈ conjugateField alpha F₂.field := hfield.symm ▸ x.2
    rwa [mem_conjugateField_iff] at hx⟩
  left_inv x := by
    apply Subtype.ext
    exact alpha.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact alpha.apply_symm_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul alpha x.1 y.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add alpha x.1 y.1
  commutes' x := by
    apply Subtype.ext
    exact alpha.commutes x

@[simp]
private theorem ambientFieldEquiv_apply
    {F₁ F₂ : NumberFieldInOmega} (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field) (x : F₂.field) :
    (ambientFieldEquiv alpha hfield x).1 = alpha x.1 :=
  rfl

private theorem closureGaloisEquiv_spec
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (g : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    ambientClosureEquiv (ambientModel K)
        (sepClosureComparison K Ksep (g x)) =
      ((closureGaloisEquiv K Ksep g).1 : RationalAbsoluteGaloisGroup)
        (ambientClosureEquiv (ambientModel K)
          (sepClosureComparison K Ksep x)) := by
  let h : Field.absoluteGaloisGroup (ambientModel K).field :=
    semilinearAutCongr (ambientBaseEquiv K).toRingEquiv
      (sepClosureComparison K Ksep)
      (sepClosureComparison_algebraMap K Ksep) g
  let a : absoluteGaloisGroup (ambientModel K) :=
    (ambientAbsoluteGaloisEquiv (ambientModel K)).symm h
  have ha : ambientAbsoluteGaloisEquiv (ambientModel K) a = h :=
    (ambientAbsoluteGaloisEquiv (ambientModel K)).apply_symm_apply h
  have hac : a = closureGaloisEquiv K Ksep g := rfl
  have hs := ambientAbsoluteGaloisEquiv_spec (ambientModel K) a
    (sepClosureComparison K Ksep x)
  rw [ha] at hs
  rw [← hac]
  simpa [h] using hs

private theorem ambientSepEquiv_spec
    (K Ksep : Type*) [Field K] [NumberField K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (g : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    ambientSepEquiv K Ksep (g x) =
      ((closureGaloisEquiv K Ksep g).1 : RationalAbsoluteGaloisGroup)
        (ambientSepEquiv K Ksep x) := by
  exact closureGaloisEquiv_spec K Ksep g x

private noncomputable def ambientEquivOfClosureEquiv
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (e0 : K₂ ≃+* K₁) (e : Ksep₂ ≃+* Ksep₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x)) :
    RationalAbsoluteGaloisGroup where
  toRingEquiv := (ambientSepEquiv K₂ Ksep₂).symm.trans
    (e.trans (ambientSepEquiv K₁ Ksep₁))
  commutes' x := by
    change ambientSepEquiv K₁ Ksep₁
      (e ((ambientSepEquiv K₂ Ksep₂).symm (algebraMap ℚ Omega x))) =
        algebraMap ℚ Omega x
    have hq₂ : ambientSepEquiv K₂ Ksep₂
        (algebraMap K₂ Ksep₂ (algebraMap ℚ K₂ x)) =
          algebraMap ℚ Omega x := by
      rw [ambientSepEquiv_algebraMap]
      exact congrArg Subtype.val ((ambientBaseEquiv K₂).commutes x)
    have hq₂symm : (ambientSepEquiv K₂ Ksep₂).symm
        (algebraMap ℚ Omega x) =
          algebraMap K₂ Ksep₂ (algebraMap ℚ K₂ x) := by
      apply (ambientSepEquiv K₂ Ksep₂).injective
      rw [RingEquiv.apply_symm_apply]
      exact hq₂.symm
    have he0 : e0 (algebraMap ℚ K₂ x) = algebraMap ℚ K₁ x := by
      exact map_ratCast e0 x
    calc
      ambientSepEquiv K₁ Ksep₁
          (e ((ambientSepEquiv K₂ Ksep₂).symm (algebraMap ℚ Omega x))) =
          ambientSepEquiv K₁ Ksep₁
            (e (algebraMap K₂ Ksep₂ (algebraMap ℚ K₂ x))) := by rw [hq₂symm]
      _ = ambientSepEquiv K₁ Ksep₁
          (algebraMap K₁ Ksep₁ (e0 (algebraMap ℚ K₂ x))) := by rw [he]
      _ = (ambientBaseEquiv K₁ (e0 (algebraMap ℚ K₂ x))).1 :=
        ambientSepEquiv_algebraMap K₁ Ksep₁ _
      _ = (ambientBaseEquiv K₁ (algebraMap ℚ K₁ x)).1 := by rw [he0]
      _ = algebraMap ℚ Omega x :=
        congrArg Subtype.val ((ambientBaseEquiv K₁).commutes x)

@[simp]
private theorem ambientEquivOfClosureEquiv_apply_comparison
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (e0 : K₂ ≃+* K₁) (e : Ksep₂ ≃+* Ksep₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x))
    (x : Ksep₂) :
    ambientEquivOfClosureEquiv e0 e he (ambientSepEquiv K₂ Ksep₂ x) =
      ambientSepEquiv K₁ Ksep₁ (e x) := by
  simp [ambientEquivOfClosureEquiv]

@[simp]
private theorem ambientEquivOfClosureEquiv_apply_base
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (e0 : K₂ ≃+* K₁) (e : Ksep₂ ≃+* Ksep₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x))
    (x : K₂) :
    ambientEquivOfClosureEquiv e0 e he (ambientBaseEquiv K₂ x).1 =
      (ambientBaseEquiv K₁ (e0 x)).1 := by
  rw [← ambientSepEquiv_algebraMap K₂ Ksep₂ x,
    ambientEquivOfClosureEquiv_apply_comparison, he,
    ambientSepEquiv_algebraMap]

private theorem ambientEquivOfClosureEquiv_field
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (e0 : K₂ ≃+* K₁) (e : Ksep₂ ≃+* Ksep₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x)) :
    conjugateField (ambientEquivOfClosureEquiv e0 e he) (ambientModel K₂).field =
      (ambientModel K₁).field := by
  ext x
  rw [mem_conjugateField_iff]
  constructor
  · intro hx
    let y₂ : (ambientModel K₂).field :=
      ⟨(ambientEquivOfClosureEquiv e0 e he).symm x, hx⟩
    let z₂ : K₂ := (ambientBaseEquiv K₂).symm y₂
    have hz := ambientEquivOfClosureEquiv_apply_base e0 e he z₂
    have hy₂ : (ambientBaseEquiv K₂ z₂).1 = y₂.1 := by
      exact congrArg Subtype.val ((ambientBaseEquiv K₂).apply_symm_apply y₂)
    have hxeq : x = (ambientBaseEquiv K₁ (e0 z₂)).1 := by
      calc
        x = ambientEquivOfClosureEquiv e0 e he y₂.1 := by simp [y₂]
        _ = ambientEquivOfClosureEquiv e0 e he
            (ambientBaseEquiv K₂ z₂).1 := by rw [hy₂]
        _ = (ambientBaseEquiv K₁ (e0 z₂)).1 := hz
    rw [hxeq]
    exact (ambientBaseEquiv K₁ (e0 z₂)).2
  · intro hx
    let y₁ : (ambientModel K₁).field := ⟨x, hx⟩
    let z₁ : K₁ := (ambientBaseEquiv K₁).symm y₁
    let z₂ : K₂ := e0.symm z₁
    have hz := ambientEquivOfClosureEquiv_apply_base e0 e he z₂
    have hy₁ : (ambientBaseEquiv K₁ (e0 z₂)).1 = x := by
      change (ambientBaseEquiv K₁ (e0 (e0.symm z₁))).1 = x
      rw [e0.apply_symm_apply]
      exact congrArg Subtype.val ((ambientBaseEquiv K₁).apply_symm_apply y₁)
    have hpre : (ambientEquivOfClosureEquiv e0 e he).symm x =
        (ambientBaseEquiv K₂ z₂).1 := by
      apply (ambientEquivOfClosureEquiv e0 e he).injective
      rw [AlgEquiv.apply_symm_apply, ambientEquivOfClosureEquiv_apply_base,
        hy₁]
    rw [hpre]
    exact (ambientBaseEquiv K₂ z₂).2

@[simp]
private theorem ambientEquivOfClosureEquiv_symm_apply_comparison
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (e0 : K₂ ≃+* K₁) (e : Ksep₂ ≃+* Ksep₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x))
    (x : Ksep₁) :
    (ambientEquivOfClosureEquiv e0 e he).symm
        (ambientSepEquiv K₁ Ksep₁ x) =
      ambientSepEquiv K₂ Ksep₂ (e.symm x) := by
  apply (ambientEquivOfClosureEquiv e0 e he).injective
  simp

/-! ## Transport between choices of separable closure -/

/-- Blueprint closure-transport statement following `thm:main`.

For arbitrary chosen separable closures, a profinite isomorphism is induced
by a unique field isomorphism of closures.  The first conjunct says that the
closure isomorphism restricts to a base-field isomorphism; the second is the
pointwise contravariant conjugation equation. -/
theorem neukirchUchida_closureTransport
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    [IsSepClosure K₁ Ksep₁] [IsSepClosure K₂ Ksep₂]
    (theta : (Ksep₁ ≃ₐ[K₁] Ksep₁) ≃ₜ*
      (Ksep₂ ≃ₐ[K₂] Ksep₂)) :
    ∃! e : Ksep₂ ≃+* Ksep₁,
      (∃ e0 : K₂ ≃+* K₁,
        ∀ x : K₂,
          e (algebraMap K₂ Ksep₂ x) =
            algebraMap K₁ Ksep₁ (e0 x)) ∧
      ∀ (g : Ksep₁ ≃ₐ[K₁] Ksep₁) (x : Ksep₂),
        theta g x = e.symm (g (e x)) := by
  let F₁ := ambientModel K₁
  let F₂ := ambientModel K₂
  let c₁ := closureGaloisEquiv K₁ Ksep₁
  let c₂ := closureGaloisEquiv K₂ Ksep₂
  let thetaOmega : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂ :=
    c₁.symm.trans (theta.trans c₂)
  obtain ⟨alpha, ⟨hfield, htheta⟩, halphaUnique⟩ :=
    neukirchUchida thetaOmega
  let q₁ := ambientSepEquiv K₁ Ksep₁
  let q₂ := ambientSepEquiv K₂ Ksep₂
  let e : Ksep₂ ≃+* Ksep₁ :=
    q₂.trans (alpha.toRingEquiv.trans q₁.symm)
  let eF : F₂.field ≃ₐ[ℚ] F₁.field := ambientFieldEquiv alpha hfield
  let e0 : K₂ ≃+* K₁ :=
    ((ambientBaseEquiv K₂).trans
      (eF.trans (ambientBaseEquiv K₁).symm)).toRingEquiv
  have hebase (x : K₂) :
      e (algebraMap K₂ Ksep₂ x) =
        algebraMap K₁ Ksep₁ (e0 x) := by
    apply q₁.injective
    simp [e, e0, eF, q₁, q₂, ambientFieldEquiv_apply]
  refine ⟨e, ⟨⟨e0, hebase⟩, ?_⟩, ?_⟩
  · intro g x
    have he_apply (y : Ksep₂) : q₁ (e y) = alpha (q₂ y) := by
      simp [e, q₁, q₂]
    have he_symm_apply (y : Ksep₁) : q₂ (e.symm y) = alpha.symm (q₁ y) := by
      simp [e, q₁, q₂]
    have hgroups : c₂ (theta g) =
        ambientConjugationIso F₁ F₂ alpha hfield (c₁ g) := by
      calc
        c₂ (theta g) = thetaOmega (c₁ g) := by
          simp [thetaOmega]
        _ = ambientConjugationIso F₁ F₂ alpha hfield (c₁ g) := by
          rw [← htheta]
    apply q₂.injective
    rw [ambientSepEquiv_spec K₂ Ksep₂ (theta g) x,
      he_symm_apply, ambientSepEquiv_spec K₁ Ksep₁ g (e x),
      he_apply]
    have hp := DFunLike.congr_fun (congrArg Subtype.val hgroups) (q₂ x)
    simpa using hp
  · intro f hf
    obtain ⟨⟨f0, hfbase⟩, hfconj⟩ := hf
    let beta : RationalAbsoluteGaloisGroup :=
      ambientEquivOfClosureEquiv f0 f hfbase
    have hfieldBeta : conjugateField beta F₂.field = F₁.field :=
      ambientEquivOfClosureEquiv_field f0 f hfbase
    have hthetaBeta :
        ambientConjugationIso F₁ F₂ beta hfieldBeta = thetaOmega := by
      apply ContinuousMulEquiv.ext
      intro a
      apply Subtype.ext
      apply AlgEquiv.ext
      intro z
      let g : Ksep₁ ≃ₐ[K₁] Ksep₁ := c₁.symm a
      let x : Ksep₂ := q₂.symm z
      have hc₁ : c₁ g = a := c₁.apply_symm_apply a
      have hq₂ : q₂ x = z := q₂.apply_symm_apply z
      have hthetaOmega : thetaOmega a = c₂ (theta g) := by
        simp [thetaOmega, g]
      calc
        ((ambientConjugationIso F₁ F₂ beta hfieldBeta a).1 :
            RationalAbsoluteGaloisGroup) z =
            beta.symm (a.1 (beta z)) := rfl
        _ = beta.symm (a.1 (beta (q₂ x))) := by rw [hq₂]
        _ = beta.symm (a.1 (q₁ (f x))) := by
          rw [ambientEquivOfClosureEquiv_apply_comparison]
        _ = beta.symm ((c₁ g).1 (q₁ (f x))) := by rw [hc₁]
        _ = beta.symm (q₁ (g (f x))) := by
          rw [ambientSepEquiv_spec K₁ Ksep₁]
        _ = q₂ (f.symm (g (f x))) := by
          rw [ambientEquivOfClosureEquiv_symm_apply_comparison]
        _ = q₂ (theta g x) := congrArg q₂ (hfconj g x).symm
        _ = (c₂ (theta g)).1 (q₂ x) := by
          rw [ambientSepEquiv_spec K₂ Ksep₂]
        _ = (thetaOmega a).1 z := by rw [hthetaOmega, hq₂]
    have hbeta : beta = alpha :=
      halphaUnique beta ⟨hfieldBeta, hthetaBeta⟩
    apply RingEquiv.ext
    intro x
    apply q₁.injective
    calc
      q₁ (f x) = beta (q₂ x) :=
        (ambientEquivOfClosureEquiv_apply_comparison f0 f hfbase x).symm
      _ = alpha (q₂ x) := by rw [hbeta]
      _ = q₁ (e x) := by simp [e, q₁, q₂]

private theorem range_map_eq_of_base_equiv
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    (e : Ksep₂ ≃+* Ksep₁) (e0 : K₂ ≃+* K₁)
    (he : ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x)) :
    (algebraMap K₂ Ksep₂).range.map e.toRingHom =
      (algebraMap K₁ Ksep₁).range := by
  ext y
  constructor
  · intro hy
    rw [Subring.mem_map] at hy
    obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hy
    exact ⟨e0 x, (he x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := e0.symm x
    refine (Subring.mem_map).mpr
      ⟨algebraMap K₂ Ksep₂ y, ⟨y, rfl⟩, ?_⟩
    simpa [y] using he y

private theorem exists_base_equiv_of_range_map_eq
    {K₁ K₂ Ksep₁ Ksep₂ : Type*}
    [Field K₁] [Field K₂] [Field Ksep₁] [Field Ksep₂]
    [Algebra K₁ Ksep₁] [Algebra K₂ Ksep₂]
    (e : Ksep₂ ≃+* Ksep₁)
    (h : (algebraMap K₂ Ksep₂).range.map e.toRingHom =
      (algebraMap K₁ Ksep₁).range) :
    ∃ e0 : K₂ ≃+* K₁, ∀ x : K₂,
      e (algebraMap K₂ Ksep₂ x) = algebraMap K₁ Ksep₁ (e0 x) := by
  classical
  have hmem (x : K₂) :
      e (algebraMap K₂ Ksep₂ x) ∈ (algebraMap K₁ Ksep₁).range := by
    rw [← h, Subring.mem_map]
    exact ⟨algebraMap K₂ Ksep₂ x, ⟨x, rfl⟩, rfl⟩
  let f : K₂ → K₁ := fun x => (RingHom.mem_range.mp (hmem x)).choose
  have hf (x : K₂) :
      algebraMap K₁ Ksep₁ (f x) = e (algebraMap K₂ Ksep₂ x) :=
    (RingHom.mem_range.mp (hmem x)).choose_spec
  let fHom : K₂ →+* K₁ :=
    { toFun := f
      map_one' := by
        apply (algebraMap K₁ Ksep₁).injective
        simpa using hf (1 : K₂)
      map_mul' := fun x y => by
        apply (algebraMap K₁ Ksep₁).injective
        rw [map_mul, hf, hf, hf, map_mul, map_mul]
      map_zero' := by
        apply (algebraMap K₁ Ksep₁).injective
        simpa using hf (0 : K₂)
      map_add' := fun x y => by
        apply (algebraMap K₁ Ksep₁).injective
        rw [map_add, hf, hf, hf, map_add, map_add] }
  have hinj : Function.Injective fHom := by
    intro x y hxy
    apply (algebraMap K₂ Ksep₂).injective
    apply e.injective
    rw [← hf, ← hf]
    exact congrArg (algebraMap K₁ Ksep₁) hxy
  have hsurj : Function.Surjective fHom := by
    intro y
    have hy : algebraMap K₁ Ksep₁ y ∈
        (algebraMap K₂ Ksep₂).range.map e.toRingHom := by
      rw [h]
      exact ⟨y, rfl⟩
    rw [Subring.mem_map] at hy
    obtain ⟨z, ⟨x, hx⟩, hz⟩ := hy
    subst z
    refine ⟨x, ?_⟩
    change f x = y
    apply (algebraMap K₁ Ksep₁).injective
    rw [hf]
    exact hz
  let e0 : K₂ ≃+* K₁ := RingEquiv.ofBijective fHom ⟨hinj, hsurj⟩
  refine ⟨e0, fun x => ?_⟩
  exact (hf x).symm

end

end NU.NeukirchUchida

namespace NU.NeukirchUchida

/-- The binding comparator theorem, verbatim from `Challenge.lean` (namespaced
here so that `Solution.lean`'s root-level declaration does not collide; the
statement text between the theorem name and `:= by` is byte-identical).

Proved as the composition of the
pointed theorem `NU.NeukirchUchida.neukirchUchida` with
`NU.NeukirchUchida.neukirchUchida_closureTransport`, transporting from the
single ambient closure to the two chosen separable closures. -/
theorem neukirch_uchida {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  let home := he.homeomorph ϕ
  have hinv : home.invFun = ϕ.invFun := by
    funext g
    apply ϕ.injective
    exact (home.apply_symm_apply g).trans (ϕ.apply_symm_apply g).symm
  let theta : (K₁' ≃ₐ[K₁] K₁') ≃ₜ* (K₂' ≃ₐ[K₂] K₂') :=
    { toMulEquiv := ϕ
      continuous_toFun := he.continuous
      continuous_invFun := by
        rw [← hinv]
        exact home.continuous_invFun }
  obtain ⟨σ, ⟨⟨σ0, hσ0⟩, hσ⟩, hunique⟩ :=
    neukirchUchida_closureTransport theta
  refine ⟨σ, ⟨range_map_eq_of_base_equiv σ σ0 hσ0, ?_⟩, ?_⟩
  · intro g
    apply RingEquiv.ext
    intro x
    exact hσ g x
  · intro τ hτ
    obtain ⟨τ0, hτ0⟩ := exists_base_equiv_of_range_map_eq τ hτ.1
    apply hunique τ
    refine ⟨⟨τ0, hτ0⟩, fun g x => ?_⟩
    change ϕ g x = _
    exact congrArg (fun r : K₂' ≃+* K₂' => r x) (hτ.2 g)

end NU.NeukirchUchida
