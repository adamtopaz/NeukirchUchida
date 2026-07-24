import Submission.NU.NeukirchUchida.LocalInterface

/-!
# Corresponding fields and primes

Blueprint §1.3 and §2.1.  This file defines corresponding intermediate
fields by the literal fixed-field construction in the one ambient closure,
descends the equivariant absolute-prime correspondence to finite primes, and
states `lem:degree-one-decomp`.
-/

open scoped NumberField Pointwise
open IsDedekindDomain

namespace NU.NeukirchUchida

noncomputable section

/-- Inclusion reverses pointwise stabilizers. -/
theorem absoluteGaloisGroup_mono
    {F K : NumberFieldInOmega} (hFK : F.field ≤ K.field) :
    absoluteGaloisGroup K ≤ absoluteGaloisGroup F := by
  intro g hg x
  exact hg ⟨x.1, hFK x.2⟩

/-- The subgroup `G_K`, regarded as an open subgroup of `G_F`. -/
def relativeAbsoluteSubgroup
    {F : NumberFieldInOmega} (K : NumberFieldExtension F) :
    Subgroup (absoluteGaloisGroup F) :=
  (absoluteGaloisGroup K.field).subgroupOf (absoluteGaloisGroup F)

/-- The natural inclusion `G_K → G_F`. -/
def absoluteGaloisInclusion
    {F : NumberFieldInOmega} (K : NumberFieldExtension F) :
    absoluteGaloisGroup K.field →* absoluteGaloisGroup F :=
  Subgroup.inclusion (absoluteGaloisGroup_mono K.le_base)

/-- Defining equation for the inclusion of ambient stabilizers. -/
@[simp]
theorem absoluteGaloisInclusion_apply
    {F : NumberFieldInOmega} (K : NumberFieldExtension F)
    (g : absoluteGaloisGroup K.field) :
    (absoluteGaloisInclusion K g).1 = g.1 :=
  rfl

/-- The image in `G_ℚ` of `G_K` under an isomorphism `G_{F₁} ≃ G_{F₂}`. -/
def correspondingAbsoluteSubgroup
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    Subgroup RationalAbsoluteGaloisGroup :=
  Subgroup.map (absoluteGaloisGroup F₂).subtype
    (Subgroup.map theta.toMulEquiv.toMonoidHom
      (relativeAbsoluteSubgroup K₁))

private theorem rationalOmega_isGalois : IsGalois ℚ Omega := by
  letI : IsAlgClosure ℚ Omega :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  exact ⟨⟩

private theorem correspondingAbsoluteSubgroup_isOpen
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    IsOpen (correspondingAbsoluteSubgroup theta K₁ :
      Set RationalAbsoluteGaloisGroup) := by
  have hK : IsOpen (absoluteGaloisGroup K₁.field :
      Set RationalAbsoluteGaloisGroup) := by
    exact IntermediateField.fixingSubgroup_isOpen K₁.field.field
  have hrel : IsOpen (relativeAbsoluteSubgroup K₁ :
      Set (absoluteGaloisGroup F₁)) :=
    Subgroup.subgroupOf_isOpen _ _ hK
  have hmap : IsOpen
      (Subgroup.map theta.toMulEquiv.toMonoidHom
        (relativeAbsoluteSubgroup K₁) :
          Set (absoluteGaloisGroup F₂)) := by
    rw [Subgroup.coe_map]
    exact theta.toHomeomorph.isOpenMap _ hrel
  have hF₂ : IsOpen (absoluteGaloisGroup F₂ :
      Set RationalAbsoluteGaloisGroup) := by
    exact IntermediateField.fixingSubgroup_isOpen F₂.field
  rw [correspondingAbsoluteSubgroup, Subgroup.coe_map]
  exact hF₂.isOpenMap_subtype_val _ hmap

private theorem correspondingAbsoluteSubgroup_isClosed
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    IsClosed (correspondingAbsoluteSubgroup theta K₁ :
      Set RationalAbsoluteGaloisGroup) :=
  (correspondingAbsoluteSubgroup theta K₁).isClosed_of_isOpen
    (correspondingAbsoluteSubgroup_isOpen theta K₁)

/-- Blueprint equation `eq:corresponding-field`: the correspondent is the
literal fixed field of the mapped subgroup.  Finiteness is part of the target
and follows from openness of `G_{K₁}`. -/
noncomputable def correspondingField
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) : NumberFieldInOmega where
  field := IntermediateField.fixedField
    (correspondingAbsoluteSubgroup theta K₁)
  finite := by
    letI : IsGalois ℚ Omega := rationalOmega_isGalois
    let H := correspondingAbsoluteSubgroup theta K₁
    have hfix : (IntermediateField.fixedField H).fixingSubgroup = H := by
      exact InfiniteGalois.fixingSubgroup_fixedField
        ⟨H, correspondingAbsoluteSubgroup_isClosed theta K₁⟩
    have hopen : IsOpen
        ((IntermediateField.fixedField H).fixingSubgroup :
          Set RationalAbsoluteGaloisGroup) := by
      rw [hfix]
      exact correspondingAbsoluteSubgroup_isOpen theta K₁
    exact (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField H)).mp hopen

/-- The corresponding field contains the target base field. -/
theorem le_correspondingField
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    F₂.field ≤ (correspondingField theta K₁).field := by
  apply (IntermediateField.le_iff_le _ _).2
  exact Subgroup.map_subtype_le _

/-- The correspondent, packaged as an ambient extension of `F₂`. -/
noncomputable def correspondingExtension
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) : NumberFieldExtension F₂ where
  field := correspondingField theta K₁
  le_base := le_correspondingField theta K₁

/-- Fixed-field defining equation for a corresponding field.  This is the
closed-subgroup form of `sigma(G_K) = G_{K'}` from blueprint §1.3. -/
theorem fixingSubgroup_correspondingField
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    absoluteGaloisGroup (correspondingField theta K₁) =
      correspondingAbsoluteSubgroup theta K₁ := by
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨correspondingAbsoluteSubgroup theta K₁,
      correspondingAbsoluteSubgroup_isClosed theta K₁⟩

/-- Two finite extensions correspond when the second is literally the fixed
field selected by `eq:corresponding-field`. -/
def AreCorresponding
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) (K₂ : NumberFieldExtension F₂) : Prop :=
  K₂.field.field = (correspondingField theta K₁).field

/-- The canonical corresponding extension satisfies `AreCorresponding`. -/
@[simp]
theorem areCorresponding_correspondingExtension
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    AreCorresponding theta K₁ (correspondingExtension theta K₁) :=
  rfl

/-- Correspondence preserves inclusions of finite intermediate fields. -/
theorem correspondingField_mono
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K L : NumberFieldExtension F₁)
    (hKL : K.field.field ≤ L.field.field) :
    (correspondingField theta K).field ≤
      (correspondingField theta L).field := by
  apply IntermediateField.fixedField_le
  apply Subgroup.map_mono
  apply Subgroup.map_mono
  exact Subgroup.subgroupOf_mono _ (absoluteGaloisGroup_mono hKL)

private theorem fixedField_sup_private
    (H K : Subgroup RationalAbsoluteGaloisGroup) :
    IntermediateField.fixedField (H ⊔ K) =
      IntermediateField.fixedField H ⊓ IntermediateField.fixedField K := by
  apply le_antisymm
  · exact le_inf
      (IntermediateField.fixedField_le le_sup_left)
      (IntermediateField.fixedField_le le_sup_right)
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hH : H ≤ MulAction.stabilizer RationalAbsoluteGaloisGroup x := by
      intro h hh
      exact (IntermediateField.mem_fixedField_iff H x).mp hx.1 h hh
    have hK : K ≤ MulAction.stabilizer RationalAbsoluteGaloisGroup x := by
      intro k hk
      exact (IntermediateField.mem_fixedField_iff K x).mp hx.2 k hk
    exact (sup_le hH hK) hg

private theorem fixingSubgroup_inf_finite
    (K L : NumberFieldInOmega) :
    (K.field ⊓ L.field).fixingSubgroup =
      K.field.fixingSubgroup ⊔ L.field.fixingSubgroup := by
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  let H := K.field.fixingSubgroup ⊔ L.field.fixingSubgroup
  have hopen : IsOpen (H : Set RationalAbsoluteGaloisGroup) := by
    apply Subgroup.isOpen_mono le_sup_left
    exact IntermediateField.fixingSubgroup_isOpen K.field
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H := by
    exact InfiniteGalois.fixingSubgroup_fixedField
      ⟨H, H.isClosed_of_isOpen hopen⟩
  have hfield : IntermediateField.fixedField H = K.field ⊓ L.field := by
    rw [fixedField_sup_private,
      InfiniteGalois.fixedField_fixingSubgroup K.field,
      InfiniteGalois.fixedField_fixingSubgroup L.field]
  rw [← hfield]
  exact hfix

private theorem eq_of_fixingSubgroup_eq
    (K L : IntermediateField ℚ Omega)
    (h : K.fixingSubgroup = L.fixingSubgroup) : K = L := by
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  rw [← InfiniteGalois.fixedField_fixingSubgroup K,
    ← InfiniteGalois.fixedField_fixingSubgroup L, h]

/-- Correspondence transports intersections literally. -/
theorem correspondingField_inf
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K L : NumberFieldExtension F₁) :
    (correspondingField theta
      { field :=
          { field := K.field.field ⊓ L.field.field
            finite := by infer_instance }
        le_base := le_inf K.le_base L.le_base }).field =
      (correspondingField theta K).field ⊓
        (correspondingField theta L).field := by
  let M : NumberFieldExtension F₁ :=
    { field :=
        { field := K.field.field ⊓ L.field.field
          finite := by infer_instance }
      le_base := le_inf K.le_base L.le_base }
  change (correspondingField theta M).field = _
  apply eq_of_fixingSubgroup_eq
  change absoluteGaloisGroup (correspondingField theta M) = _
  rw [fixingSubgroup_correspondingField theta M]
  have htarget :
      ((correspondingField theta K).field ⊓
        (correspondingField theta L).field).fixingSubgroup =
      absoluteGaloisGroup (correspondingField theta K) ⊔
        absoluteGaloisGroup (correspondingField theta L) :=
    fixingSubgroup_inf_finite
      (correspondingField theta K) (correspondingField theta L)
  rw [htarget, fixingSubgroup_correspondingField theta K,
    fixingSubgroup_correspondingField theta L]
  have hsource : absoluteGaloisGroup M.field =
      absoluteGaloisGroup K.field ⊔ absoluteGaloisGroup L.field := by
    exact fixingSubgroup_inf_finite K.field L.field
  have hrel : relativeAbsoluteSubgroup M =
      relativeAbsoluteSubgroup K ⊔ relativeAbsoluteSubgroup L := by
    rw [relativeAbsoluteSubgroup, hsource,
      Subgroup.subgroupOf_sup
        (absoluteGaloisGroup_mono K.le_base)
        (absoluteGaloisGroup_mono L.le_base)]
    rfl
  rw [correspondingAbsoluteSubgroup, hrel,
    Subgroup.map_sup, Subgroup.map_sup]
  rfl

/-- Correspondence transports composita literally. -/
theorem correspondingField_sup
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K L : NumberFieldExtension F₁) :
    (correspondingField theta
      { field :=
          { field := K.field.field ⊔ L.field.field
            finite := IntermediateField.finiteDimensional_sup
              K.field.field L.field.field }
        le_base := K.le_base.trans le_sup_left }).field =
      (correspondingField theta K).field ⊔
        (correspondingField theta L).field := by
  let M : NumberFieldExtension F₁ :=
    { field :=
        { field := K.field.field ⊔ L.field.field
          finite := IntermediateField.finiteDimensional_sup
            K.field.field L.field.field }
      le_base := K.le_base.trans le_sup_left }
  change (correspondingField theta M).field = _
  apply eq_of_fixingSubgroup_eq
  change absoluteGaloisGroup (correspondingField theta M) = _
  rw [fixingSubgroup_correspondingField theta M,
    IntermediateField.fixingSubgroup_sup]
  change correspondingAbsoluteSubgroup theta M =
    absoluteGaloisGroup (correspondingField theta K) ⊓
      absoluteGaloisGroup (correspondingField theta L)
  rw [fixingSubgroup_correspondingField theta K,
    fixingSubgroup_correspondingField theta L]
  have hsource : absoluteGaloisGroup M.field =
      absoluteGaloisGroup K.field ⊓ absoluteGaloisGroup L.field := by
    exact IntermediateField.fixingSubgroup_sup
  have hrel : relativeAbsoluteSubgroup M =
      relativeAbsoluteSubgroup K ⊓ relativeAbsoluteSubgroup L := by
    change (absoluteGaloisGroup M.field).comap
        (absoluteGaloisGroup F₁).subtype = _
    rw [hsource, Subgroup.comap_inf]
    rfl
  rw [correspondingAbsoluteSubgroup, hrel,
    Subgroup.map_inf _ _ _ theta.injective,
    Subgroup.map_inf _ _ _
      (absoluteGaloisGroup F₂).subtype_injective]
  rfl

/-- Restriction of `theta` to corresponding open subgroups.  Its equation
below pins it to `theta`; it is not an arbitrary equivalence. -/
noncomputable def correspondingRestrictedIso
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    absoluteGaloisGroup K₁.field ≃ₜ*
      absoluteGaloisGroup (correspondingField theta K₁) := by
  let toF₁ : absoluteGaloisGroup K₁.field →
      absoluteGaloisGroup F₁ := fun g => absoluteGaloisInclusion K₁ g
  let toF₂ : absoluteGaloisGroup K₁.field →
      absoluteGaloisGroup F₂ := fun g => theta (toF₁ g)
  have hto (g : absoluteGaloisGroup K₁.field) :
      (toF₂ g : RationalAbsoluteGaloisGroup) ∈
        absoluteGaloisGroup (correspondingField theta K₁) := by
    rw [fixingSubgroup_correspondingField]
    refine ⟨toF₂ g, ?_, rfl⟩
    refine ⟨toF₁ g, ?_, rfl⟩
    exact g.2
  let forward : absoluteGaloisGroup K₁.field →
      absoluteGaloisGroup (correspondingField theta K₁) :=
    fun g => ⟨toF₂ g, hto g⟩
  let intoF₂ : absoluteGaloisGroup (correspondingField theta K₁) →
      absoluteGaloisGroup F₂ := fun h =>
    ⟨h.1, absoluteGaloisGroup_mono
      (le_correspondingField theta K₁) h.2⟩
  have hback (h : absoluteGaloisGroup (correspondingField theta K₁)) :
      ((theta.symm (intoF₂ h) : absoluteGaloisGroup F₁) :
        RationalAbsoluteGaloisGroup) ∈ absoluteGaloisGroup K₁.field := by
    have hh : (h : RationalAbsoluteGaloisGroup) ∈
        correspondingAbsoluteSubgroup theta K₁ := by
      rw [← fixingSubgroup_correspondingField theta K₁]
      exact h.2
    have hinner : intoF₂ h ∈
        Subgroup.map theta.toMulEquiv.toMonoidHom
          (relativeAbsoluteSubgroup K₁) := by
      rcases hh with ⟨y, hy, heq⟩
      have hyh : y = intoF₂ h := by
        apply Subtype.ext
        exact heq
      rwa [← hyh]
    exact Subgroup.mem_map_equiv.mp hinner
  let backward : absoluteGaloisGroup (correspondingField theta K₁) →
      absoluteGaloisGroup K₁.field := fun h =>
    ⟨(theta.symm (intoF₂ h) : absoluteGaloisGroup F₁), hback h⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro g
    apply Subtype.ext
    change ((theta.symm (theta (toF₁ g)) : absoluteGaloisGroup F₁) :
      RationalAbsoluteGaloisGroup) = g.1
    exact congrArg Subtype.val (theta.symm_apply_apply (toF₁ g))
  · intro h
    apply Subtype.ext
    change ((theta (theta.symm (intoF₂ h)) : absoluteGaloisGroup F₂) :
      RationalAbsoluteGaloisGroup) = h.1
    exact congrArg Subtype.val (theta.apply_symm_apply (intoF₂ h))
  · intro g h
    apply Subtype.ext
    change ((theta (toF₁ (g * h)) : absoluteGaloisGroup F₂) :
      RationalAbsoluteGaloisGroup) =
        ((theta (toF₁ g) * theta (toF₁ h) : absoluteGaloisGroup F₂) :
          RationalAbsoluteGaloisGroup)
    exact congrArg Subtype.val (map_mul theta (toF₁ g) (toF₁ h))
  · have hinc : Continuous toF₁ := by
      change Continuous (fun g : absoluteGaloisGroup K₁.field =>
        (⟨g.1, absoluteGaloisGroup_mono K₁.le_base g.2⟩ :
          absoluteGaloisGroup F₁))
      exact continuous_subtype_val.subtype_mk _
    exact (continuous_subtype_val.comp
      (theta.continuous_toFun.comp hinc)).subtype_mk _
  · have hinto : Continuous intoF₂ := by
      dsimp only [intoF₂]
      fun_prop
    exact (continuous_subtype_val.comp
      (theta.continuous_invFun.comp hinto)).subtype_mk _

/-- Defining equation for restriction to corresponding open subgroups. -/
@[simp]
theorem correspondingRestrictedIso_apply
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁)
    (g : absoluteGaloisGroup K₁.field) :
    (correspondingRestrictedIso theta K₁ g).1 =
      theta (absoluteGaloisInclusion K₁ g) := by
  rfl

private theorem valuationSubring_comap_ne_top_of_local
    {F E : Type*} [Field F] [Field E]
    (A : ValuationSubring F) (hA : A ≠ ⊤)
    (i : F →+* E) (W : ValuationSubring E)
    (hi : ∀ a : A, i a.1 ∈ W)
    (hloc : IsLocalHom
      (i.comp A.toSubring.subtype |>.codRestrict W.toSubring hi)) :
    W.comap i ≠ ⊤ := by
  obtain ⟨x, _, hx⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hA)
  have hx0 : x ≠ 0 := by
    intro h
    apply hx
    simp [h]
  have hxinv : x⁻¹ ∈ A.nonunits :=
    A.inv_mem_nonunits_iff.mpr (Or.inr hx)
  let a : A := ⟨x⁻¹, A.nonunits_subset hxinv⟩
  have ha0 : a ≠ 0 := by
    intro h
    exact inv_ne_zero hx0 (congrArg Subtype.val h)
  intro htop
  have ha_nonunit : ¬IsUnit a := by
    simpa [IsLocalRing.mem_maximalIdeal] using
      A.coe_mem_nonunits_iff.mp hxinv
  let f : A →+* W :=
    (i.comp A.toSubring.subtype).codRestrict W.toSubring hi
  letI : IsLocalHom f := hloc
  have hfa_nonunit : ¬IsUnit (f a) := by
    intro h
    exact ha_nonunit (IsUnit.of_map f a h)
  apply hfa_nonunit
  have hinvW : i (a.1⁻¹) ∈ W := by
    have : a.1⁻¹ ∈ W.comap i := by
      rw [htop]
      trivial
    exact this
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨i (a.1⁻¹), hinvW⟩, ?_⟩
  apply Subtype.ext
  dsimp [f, a]
  rw [← map_mul]
  rw [show A.toSubring.subtype
    (⟨x⁻¹, A.nonunits_subset hxinv⟩ : A) = x⁻¹ from rfl,
    inv_inv, inv_mul_cancel₀ hx0, map_one]

private theorem finitePrime_surjective (F : NumberFieldInOmega) :
    Function.Surjective (finitePrime F) := by
  intro v
  let A := NU.LocalTheory.primeValuationSubring v
  let i : F.field →+* Omega := F.field.val.toRingHom
  let f : A →+* Omega := i.comp A.toSubring.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  have hcomap_ne : W.comap i ≠ ⊤ := by
    apply valuationSubring_comap_ne_top_of_local A
      (NU.LocalTheory.primeValuationSubring_ne_top v) i W hW
    exact hlocal
  have hle : A ≤ W.comap i := by
    intro x hx
    exact hW ⟨x, hx⟩
  letI : Ring.KrullDimLE 1 A := by
    change Ring.KrullDimLE 1
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F.field v)
    infer_instance
  have hcomap : W.comap i = A := by
    exact (ValuationSubring.eq_of_le_of_ne_top A hle hcomap_ne).symm
  have hWtop : W ≠ ⊤ := by
    intro h
    apply hcomap_ne
    rw [h]
    rfl
  let j : ℚ →+* Omega := algebraMap ℚ Omega
  have hQcomap : W.comap j ≠ ⊤ := by
    intro htop
    apply hWtop
    apply top_unique
    intro x _
    have hj (r : ℚ) : j r ∈ W := by
      have : r ∈ W.comap j := by
        rw [htop]
        trivial
      exact this
    let jW : ℚ →+* W := j.codRestrict W.toSubring hj
    letI : Algebra ℚ W := jW.toAlgebra
    letI : IsScalarTower ℚ W Omega := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      rfl
    have hxQ : IsIntegral ℚ x := by
      letI : Algebra.IsAlgebraic ℚ Omega :=
        AlgebraicClosure.isAlgebraic ℚ
      letI : Algebra.IsIntegral ℚ Omega :=
        Algebra.IsAlgebraic.isIntegral
      exact Algebra.IsIntegral.isIntegral x
    have hxW : IsIntegral W x := hxQ.tower_top
    exact (Subring.isIntegrallyClosed_iff.mp
      (inferInstance : IsIntegrallyClosed W)) hxW
  obtain ⟨q, hq, _⟩ :=
    NU.LocalTheory.numberField_valuations (W.comap j) hQcomap
  let P : AbsolutePrime := ⟨W, hWtop, q, hq⟩
  refine ⟨P, ?_⟩
  apply (NU.LocalTheory.numberField_valuations A
    (NU.LocalTheory.primeValuationSubring_ne_top v)).unique
  · rw [primeValuationSubring_finitePrime, hcomap]
  · rfl

private theorem primeValuationSubring_conjugate
    (k K : Type*) [Field k] [Field K]
    [NumberField k] [NumberField K] [Algebra k K]
    (sigma : K ≃ₐ[k] K) (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.conjugateFinitePlace k sigma v) =
      sigma • NU.LocalTheory.primeValuationSubring v := by
  ext x
  rw [NU.LocalTheory.mem_primeValuationSubring_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.aut_inv,
    NU.LocalTheory.mem_primeValuationSubring_iff]
  constructor
  · rintro ⟨a, b, hb, hab⟩
    refine ⟨sigma.symm • a, sigma.symm • b, ?_, ?_⟩
    · intro hbmem
      apply hb
      rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact hbmem
    · rw [show ((sigma.symm • b : 𝓞 K) : K) =
          sigma.symm (b : K) by rfl,
        show ((sigma.symm • a : 𝓞 K) : K) =
          sigma.symm (a : K) by rfl]
      calc
        sigma.symm x * sigma.symm (b : K) =
            sigma.symm (x * (b : K)) :=
          (map_mul sigma.symm x (b : K)).symm
        _ = sigma.symm (a : K) := congrArg sigma.symm hab
  · rintro ⟨a, b, hb, hab⟩
    refine ⟨sigma • a, sigma • b, ?_, ?_⟩
    · rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      simpa only [inv_smul_smul] using hb
    · rw [show ((sigma • b : 𝓞 K) : K) = sigma (b : K) by rfl,
        show ((sigma • a : 𝓞 K) : K) = sigma (a : K) by rfl]
      have hact : sigma.symm x * (b : K) = (a : K) := by
        simpa only [AlgEquiv.smul_def] using hab
      calc
        x * sigma (b : K) = sigma (sigma.symm x) * sigma (b : K) := by
          rw [sigma.apply_symm_apply]
        _ = sigma (sigma.symm x * (b : K)) :=
          (map_mul sigma (sigma.symm x) (b : K)).symm
        _ = sigma (a : K) := congrArg sigma hact

/-- Restriction of an absolute prime commutes with restriction along an
ambient number-field extension. -/
theorem restrictFinitePlace_finitePrime
    (F : NumberFieldInOmega) (L : NumberFieldExtension F)
    (P : AbsolutePrime) :
    NU.LocalTheory.restrictFinitePlace F.field (finitePrime L.field P) =
      finitePrime F P := by
  let w := finitePrime L.field P
  let v := NU.LocalTheory.restrictFinitePlace F.field w
  let A := P.valuationSubring.comap F.field.val.toRingHom
  let B := NU.LocalTheory.primeValuationSubring v
  have hBA : B ≤ A := by
    intro x hx
    rw [NU.LocalTheory.mem_primeValuationSubring_iff] at hx
    obtain ⟨a, b, hb, hab⟩ := hx
    have hbN : NumberField.RingOfIntegers.mapRingHom
        (algebraMap F.field L.field.field) b ∉ w.asIdeal := by
      exact hb
    have habN : algebraMap F.field L.field.field x *
        (NumberField.RingOfIntegers.mapRingHom
          (algebraMap F.field L.field.field) b : L.field.field) =
        (NumberField.RingOfIntegers.mapRingHom
          (algebraMap F.field L.field.field) a : L.field.field) := by
      simpa only [NumberField.RingOfIntegers.mapRingHom_apply,
        map_mul] using congrArg (algebraMap F.field L.field.field) hab
    have hxw : algebraMap F.field L.field.field x ∈
        NU.LocalTheory.primeValuationSubring w := by
      rw [NU.LocalTheory.mem_primeValuationSubring_iff]
      exact ⟨NumberField.RingOfIntegers.mapRingHom
          (algebraMap F.field L.field.field) a,
        NumberField.RingOfIntegers.mapRingHom
          (algebraMap F.field L.field.field) b, hbN, habN⟩
    rw [primeValuationSubring_finitePrime] at hxw
    change F.field.val x ∈ P.valuationSubring at hxw
    exact hxw
  letI : Ring.KrullDimLE 1 B := by
    change Ring.KrullDimLE 1
      (HeightOneSpectrum.valuationSubringAtPrime F.field v)
    infer_instance
  have hB : B = A :=
    ValuationSubring.eq_of_le_of_ne_top B hBA
      (absolutePrime_comap_nontrivial F P)
  apply (NU.LocalTheory.numberField_valuations A
    (absolutePrime_comap_nontrivial F P)).unique
  · exact hB.symm
  · rw [primeValuationSubring_finitePrime]

private theorem finitePrime_ambient_smul
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (g : RationalAbsoluteGaloisGroup) (P : AbsolutePrime) :
    finitePrime N (g • P) =
      NU.LocalTheory.conjugateFinitePlace ℚ
        (AlgEquiv.restrictNormalHom N.field g) (finitePrime N P) := by
  let sigma : N.field ≃ₐ[ℚ] N.field :=
    AlgEquiv.restrictNormalHom N.field g
  have hvals : NU.LocalTheory.primeValuationSubring
      (finitePrime N (g • P)) =
      NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.conjugateFinitePlace ℚ sigma (finitePrime N P)) := by
    rw [primeValuationSubring_finitePrime,
      primeValuationSubring_conjugate,
      primeValuationSubring_finitePrime]
    ext x
    change N.field.val x ∈ g • P.valuationSubring ↔
      x ∈ sigma • P.valuationSubring.comap N.field.val.toRingHom
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change g⁻¹ (N.field.val x) ∈ P.valuationSubring ↔
      N.field.val (sigma⁻¹ x) ∈ P.valuationSubring
    rw [show N.field.val (sigma⁻¹ x) = g⁻¹ (N.field.val x) by
      rw [show sigma⁻¹ = AlgEquiv.restrictNormalHom N.field g⁻¹ by
        dsimp only [sigma]
        exact (map_inv (AlgEquiv.restrictNormalHom N.field) g).symm]
      exact AlgEquiv.restrictNormal_commutes g⁻¹ N.field x]
  apply (NU.LocalTheory.numberField_valuations
    (NU.LocalTheory.primeValuationSubring (finitePrime N (g • P)))
    (NU.LocalTheory.primeValuationSubring_ne_top
      (finitePrime N (g • P)))).unique
  · rfl
  · exact hvals

private theorem finitePrime_eq_of_overfield_eq
    (K M : NumberFieldInOmega) (hKM : K.field ≤ M.field)
    (P Q : AbsolutePrime)
    (hPM : finitePrime M P = finitePrime M Q) :
    finitePrime K P = finitePrime K Q := by
  have hvalsM : P.valuationSubring.comap M.field.val.toRingHom =
      Q.valuationSubring.comap M.field.val.toRingHom := by
    rw [← primeValuationSubring_finitePrime,
      ← primeValuationSubring_finitePrime, hPM]
  have hvalsK : NU.LocalTheory.primeValuationSubring (finitePrime K P) =
      NU.LocalTheory.primeValuationSubring (finitePrime K Q) := by
    rw [primeValuationSubring_finitePrime,
      primeValuationSubring_finitePrime]
    ext x
    let y : M.field := ⟨x.1, hKM x.2⟩
    exact SetLike.ext_iff.mp hvalsM y
  apply (NU.LocalTheory.numberField_valuations
    (NU.LocalTheory.primeValuationSubring (finitePrime K P))
    (NU.LocalTheory.primeValuationSubring_ne_top
      (finitePrime K P))).unique
  · rfl
  · exact hvalsK

private structure RationalGaloisExtension
    (F : NumberFieldInOmega) where
  toExtension : NumberFieldExtension F
  isGalois : IsGalois ℚ toExtension.field.field

private noncomputable def rationalGaloisExtensionSup
    {F : NumberFieldInOmega}
    (L M : RationalGaloisExtension F) :
    RationalGaloisExtension F := by
  let E := L.toExtension.field.field ⊔ M.toExtension.field.field
  let N := IntermediateField.normalClosure ℚ E Omega
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  letI : IsScalarTower ℚ E Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  refine
    { toExtension :=
        { field :=
            { field := N
              finite := ?_ }
          le_base := ?_ }
      isGalois := ?_ }
  · dsimp only [N, E]
    infer_instance
  · exact L.toExtension.le_base.trans
      (le_sup_left.trans (IntermediateField.le_normalClosure E))
  · exact IsGalois.normalClosure ℚ E Omega

private noncomputable def rationalGaloisExtensionContaining
    (F : NumberFieldInOmega) (x : Omega) :
    RationalGaloisExtension F := by
  let A := IntermediateField.adjoin ℚ ({x} : Set Omega)
  let E := F.field ⊔ A
  let N := IntermediateField.normalClosure ℚ E Omega
  letI : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Omega :=
    Algebra.IsAlgebraic.isIntegral
  letI : FiniteDimensional ℚ A :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
  letI : FiniteDimensional ℚ E := by
    dsimp only [E]
    exact IntermediateField.finiteDimensional_sup F.field A
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  refine
    { toExtension :=
        { field :=
            { field := N
              finite := normalClosure.is_finiteDimensional ℚ E Omega }
          le_base := le_sup_left.trans
            (IntermediateField.le_normalClosure E) }
      isGalois := IsGalois.normalClosure ℚ E Omega }

private theorem mem_rationalGaloisExtensionContaining
    (F : NumberFieldInOmega) (x : Omega) :
    x ∈ (rationalGaloisExtensionContaining F x).toExtension.field.field := by
  have hxA : x ∈ IntermediateField.adjoin ℚ ({x} : Set Omega) :=
    IntermediateField.subset_adjoin ℚ ({x} : Set Omega)
      (Set.mem_singleton x)
  have hxE : x ∈ F.field ⊔
      IntermediateField.adjoin ℚ ({x} : Set Omega) :=
    (le_sup_right : IntermediateField.adjoin ℚ ({x} : Set Omega) ≤
      F.field ⊔ IntermediateField.adjoin ℚ ({x} : Set Omega)) hxA
  exact IntermediateField.le_normalClosure
    (F.field ⊔ IntermediateField.adjoin ℚ ({x} : Set Omega)) hxE

private noncomputable instance
    {F : NumberFieldInOmega} (L : RationalGaloisExtension F) :
    IsGalois ℚ L.toExtension.field.field := L.isGalois

private def primeTransportSet
    (F : NumberFieldInOmega) (L : RationalGaloisExtension F)
    (P Q : AbsolutePrime) : Set (absoluteGaloisGroup F) :=
  {g | finitePrime L.toExtension.field (g • P) =
    finitePrime L.toExtension.field Q}

private theorem primeTransportSet_sup_subset_left
    (F : NumberFieldInOmega) (L M : RationalGaloisExtension F)
    (P Q : AbsolutePrime) :
    primeTransportSet F (rationalGaloisExtensionSup L M) P Q ⊆
      primeTransportSet F L P Q := by
  intro g hg
  apply finitePrime_eq_of_overfield_eq
    L.toExtension.field
    (rationalGaloisExtensionSup L M).toExtension.field
    _ (g • P) Q hg
  exact le_sup_left.trans
    (IntermediateField.le_normalClosure
      (L.toExtension.field.field ⊔ M.toExtension.field.field))

private theorem primeTransportSet_sup_subset_right
    (F : NumberFieldInOmega) (L M : RationalGaloisExtension F)
    (P Q : AbsolutePrime) :
    primeTransportSet F (rationalGaloisExtensionSup L M) P Q ⊆
      primeTransportSet F M P Q := by
  intro g hg
  apply finitePrime_eq_of_overfield_eq
    M.toExtension.field
    (rationalGaloisExtensionSup L M).toExtension.field
    _ (g • P) Q hg
  exact le_sup_right.trans
    (IntermediateField.le_normalClosure
      (L.toExtension.field.field ⊔ M.toExtension.field.field))

private theorem primeTransportSet_isClosed
    (F : NumberFieldInOmega) (L : RationalGaloisExtension F)
    (P Q : AbsolutePrime) :
    IsClosed (primeTransportSet F L P Q) := by
  let N := L.toExtension.field
  letI : IsGalois ℚ L.toExtension.field.field := L.isGalois
  letI : Normal ℚ L.toExtension.field.field := IsGalois.to_normal
  let r : absoluteGaloisGroup F → (N.field ≃ₐ[ℚ] N.field) :=
    fun g => AlgEquiv.restrictNormalHom N.field g.1
  let T : Set (N.field ≃ₐ[ℚ] N.field) :=
    {sigma | NU.LocalTheory.conjugateFinitePlace ℚ sigma (finitePrime N P) =
      finitePrime N Q}
  have hr0 : Continuous (fun g : absoluteGaloisGroup F =>
      AlgEquiv.restrictNormalHom L.toExtension.field.field g.1) := by
    exact (@InfiniteGalois.restrictNormalHom_continuous
      ℚ Omega inferInstance inferInstance inferInstance
      L.toExtension.field.field L.isGalois.to_normal).comp
      continuous_subtype_val
  have hr : Continuous r := by
    simpa only [r, N] using hr0
  have hset : primeTransportSet F L P Q = r ⁻¹' T := by
    ext g
    change finitePrime N ((g : RationalAbsoluteGaloisGroup) • P) =
        finitePrime N Q ↔
      NU.LocalTheory.conjugateFinitePlace ℚ
          (AlgEquiv.restrictNormalHom N.field g.1) (finitePrime N P) =
        finitePrime N Q
    rw [finitePrime_ambient_smul]
  rw [hset]
  exact (isClosed_discrete T).preimage hr

private theorem primeTransportSet_nonempty
    (F : NumberFieldInOmega) (L : RationalGaloisExtension F)
    (P Q : AbsolutePrime)
    (hPQ : finitePrime F P = finitePrime F Q) :
    (primeTransportSet F L P Q).Nonempty := by
  let N := L.toExtension.field
  let p := (finitePrime F P).asIdeal
  let Pn := (finitePrime N P).asIdeal
  let Qn := (finitePrime N Q).asIdeal
  have hrestrictP : NU.LocalTheory.restrictFinitePlace F.field
      (finitePrime N P) = finitePrime F P :=
    restrictFinitePlace_finitePrime F L.toExtension P
  have hrestrictQ : NU.LocalTheory.restrictFinitePlace F.field
      (finitePrime N Q) = finitePrime F Q :=
    restrictFinitePlace_finitePrime F L.toExtension Q
  have hPover : Pn.LiesOver p := ⟨by
    change p = (NU.LocalTheory.restrictFinitePlace F.field
      (finitePrime N P)).asIdeal
    exact congrArg HeightOneSpectrum.asIdeal hrestrictP.symm⟩
  have hQover : Qn.LiesOver p := ⟨by
    change p = (NU.LocalTheory.restrictFinitePlace F.field
      (finitePrime N Q)).asIdeal
    exact congrArg HeightOneSpectrum.asIdeal (hPQ.trans hrestrictQ.symm)⟩
  letI : Pn.LiesOver p := hPover
  letI : Qn.LiesOver p := hQover
  letI : IsGalois F.field N.field :=
    IsGalois.tower_top_of_isGalois ℚ F.field N.field
  obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    p Pn Qn (N.field ≃ₐ[F.field] N.field)
  have hplace : NU.LocalTheory.conjugateFinitePlace F.field sigma
      (finitePrime N P) = finitePrime N Q := by
    apply HeightOneSpectrum.ext
    exact hsigma
  letI : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : IsAlgClosure F.field Omega := by
    refine ⟨AlgebraicClosure.isAlgClosed ℚ, ?_⟩
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) F.field
  letI : IsScalarTower F.field N.field Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  obtain ⟨gF, hgF⟩ :=
    AlgEquiv.restrictNormalHom_surjective Omega sigma
  let gQ : RationalAbsoluteGaloisGroup := gF.restrictScalars ℚ
  let g : absoluteGaloisGroup F := ⟨gQ, fun x => gF.commutes x⟩
  refine ⟨g, ?_⟩
  change finitePrime N (gQ • P) = finitePrime N Q
  rw [finitePrime_ambient_smul]
  have hres : AlgEquiv.restrictNormalHom N.field gQ =
      sigma.restrictScalars ℚ := by
    apply AlgEquiv.ext
    intro x
    apply N.field.val.injective
    have hx := DFunLike.congr_fun hgF x
    calc
      N.field.val ((AlgEquiv.restrictNormalHom N.field gQ) x) =
          gQ (N.field.val x) :=
        AlgEquiv.restrictNormal_commutes gQ N.field x
      _ = gF (N.field.val x) := rfl
      _ = N.field.val ((AlgEquiv.restrictNormalHom N.field gF) x) :=
        (AlgEquiv.restrictNormal_commutes gF N.field x).symm
      _ = N.field.val (sigma x) := congrArg Subtype.val hx
      _ = N.field.val ((sigma.restrictScalars ℚ) x) := rfl
  rw [hres]
  exact hplace

/-- Absolute primes with the same restriction to `F` are conjugate under
`G_F`. -/
theorem exists_smul_of_finitePrime_eq
    (F : NumberFieldInOmega) (P Q : AbsolutePrime)
    (hPQ : finitePrime F P = finitePrime F Q) :
    ∃ g : absoluteGaloisGroup F, g • P = Q := by
  letI : Nonempty (RationalGaloisExtension F) :=
    ⟨rationalGaloisExtensionContaining F 0⟩
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  letI : CompactSpace RationalAbsoluteGaloisGroup := inferInstance
  have hopen : IsOpen (absoluteGaloisGroup F :
      Set RationalAbsoluteGaloisGroup) :=
    IntermediateField.fixingSubgroup_isOpen F.field
  have hclosed : IsClosed (absoluteGaloisGroup F :
      Set RationalAbsoluteGaloisGroup) :=
    (absoluteGaloisGroup F).isClosed_of_isOpen hopen
  letI : CompactSpace (absoluteGaloisGroup F) :=
    hclosed.isClosedEmbedding_subtypeVal.compactSpace
  let S := fun L : RationalGaloisExtension F =>
    primeTransportSet F L P Q
  have hdirected : Directed (· ⊇ ·) S := by
    intro L M
    refine ⟨rationalGaloisExtensionSup L M, ?_, ?_⟩
    · exact primeTransportSet_sup_subset_left F L M P Q
    · exact primeTransportSet_sup_subset_right F L M P Q
  have hnonempty : ∀ L, (S L).Nonempty := by
    intro L
    exact primeTransportSet_nonempty F L P Q hPQ
  have hclosedS : ∀ L, IsClosed (S L) := by
    intro L
    exact primeTransportSet_isClosed F L P Q
  have hcompactS : ∀ L, IsCompact (S L) := by
    intro L
    exact (hclosedS L).isCompact
  obtain ⟨g, hg⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      S hdirected hnonempty hcompactS hclosedS
  refine ⟨g, ?_⟩
  apply AbsolutePrime.ext
  ext x
  let L := rationalGaloisExtensionContaining F x
  have hgL : g ∈ primeTransportSet F L P Q :=
    Set.mem_iInter.mp hg L
  have hvals : (g • P).valuationSubring.comap
        L.toExtension.field.field.val.toRingHom =
      Q.valuationSubring.comap
        L.toExtension.field.field.val.toRingHom := by
    rw [← primeValuationSubring_finitePrime,
      ← primeValuationSubring_finitePrime, hgL]
  let y : L.toExtension.field.field :=
    ⟨x, mem_rationalGaloisExtensionContaining F x⟩
  exact SetLike.ext_iff.mp hvals y

private theorem finitePrime_smul
    (F : NumberFieldInOmega) (g : absoluteGaloisGroup F)
    (P : AbsolutePrime) :
    finitePrime F (g • P) = finitePrime F P := by
  apply (NU.LocalTheory.numberField_valuations
    (NU.LocalTheory.primeValuationSubring (finitePrime F P))
    (NU.LocalTheory.primeValuationSubring_ne_top (finitePrime F P))).unique
  · rw [primeValuationSubring_finitePrime,
      primeValuationSubring_finitePrime]
    ext x
    change (F.field.val x ∈ P.valuationSubring) ↔
      F.field.val x ∈
        (g : RationalAbsoluteGaloisGroup) • P.valuationSubring
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      show (g : RationalAbsoluteGaloisGroup)⁻¹ •
        F.field.val x = F.field.val x by
          exact g⁻¹.2 x]
  · rfl

private noncomputable def absolutePrimeLift
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) :
    AbsolutePrime :=
  (finitePrime_surjective F v).choose

@[simp]
private theorem finitePrime_absolutePrimeLift
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) :
    finitePrime F (absolutePrimeLift F v) = v :=
  (finitePrime_surjective F v).choose_spec

/-! ## Descent from absolute primes to finite primes -/

/-- The finite-prime bijection descended from (L2), blueprint
`eq:finite-prime-bijection`.  The defining restriction equation below is the
prime-orbit descent obligation; no global choice of a prolongation for each
finite prime appears in the interface. -/
noncomputable def finitePrimeCorrespondence
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    NU.LocalTheory.FinitePlace K₁.field.field ≃
      NU.LocalTheory.FinitePlace (correspondingField theta K₁).field := by
  let e := correspondingRestrictedIso theta K₁
  let f : NU.LocalTheory.FinitePlace K₁.field.field →
      NU.LocalTheory.FinitePlace (correspondingField theta K₁).field :=
    fun v => finitePrime (correspondingField theta K₁)
      (primeCorrespondence e (absolutePrimeLift K₁.field v))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v w hvw
    let P := absolutePrimeLift K₁.field v
    let Q := absolutePrimeLift K₁.field w
    change finitePrime (correspondingField theta K₁)
        (primeCorrespondence e P) =
      finitePrime (correspondingField theta K₁)
        (primeCorrespondence e Q) at hvw
    obtain ⟨h, hh⟩ := exists_smul_of_finitePrime_eq
      (correspondingField theta K₁)
      (primeCorrespondence e P) (primeCorrespondence e Q) hvw
    let g : absoluteGaloisGroup K₁.field := e.symm h
    have heq : primeCorrespondence e (g • P) =
        primeCorrespondence e Q := by
      rw [primeCorrespondence_equivariant_L2, e.apply_symm_apply]
      exact hh
    have hPQ : g • P = Q := (primeCorrespondence e).injective heq
    calc
      v = finitePrime K₁.field P :=
        (finitePrime_absolutePrimeLift K₁.field v).symm
      _ = finitePrime K₁.field (g • P) :=
        (finitePrime_smul K₁.field g P).symm
      _ = finitePrime K₁.field Q := congrArg (finitePrime K₁.field) hPQ
      _ = w := finitePrime_absolutePrimeLift K₁.field w
  · intro w
    let Q := absolutePrimeLift (correspondingField theta K₁) w
    let P := (primeCorrespondence e).symm Q
    let v := finitePrime K₁.field P
    have hsource : finitePrime K₁.field (absolutePrimeLift K₁.field v) =
        finitePrime K₁.field P := by
      simp only [finitePrime_absolutePrimeLift, v]
    obtain ⟨g, hg⟩ := exists_smul_of_finitePrime_eq K₁.field
      (absolutePrimeLift K₁.field v) P hsource
    refine ⟨v, ?_⟩
    change finitePrime (correspondingField theta K₁)
      (primeCorrespondence e (absolutePrimeLift K₁.field v)) = w
    calc
      finitePrime (correspondingField theta K₁)
          (primeCorrespondence e (absolutePrimeLift K₁.field v)) =
        finitePrime (correspondingField theta K₁)
          (e g • primeCorrespondence e (absolutePrimeLift K₁.field v)) :=
        (finitePrime_smul (correspondingField theta K₁) (e g)
          (primeCorrespondence e (absolutePrimeLift K₁.field v))).symm
      _ = finitePrime (correspondingField theta K₁)
          (primeCorrespondence e (g • absolutePrimeLift K₁.field v)) := by
        rw [primeCorrespondence_equivariant_L2]
      _ = finitePrime (correspondingField theta K₁)
          (primeCorrespondence e P) := by rw [hg]
      _ = finitePrime (correspondingField theta K₁) Q := by
        rw [show primeCorrespondence e P = Q by
          exact (primeCorrespondence e).apply_symm_apply Q]
      _ = w := finitePrime_absolutePrimeLift
        (correspondingField theta K₁) w

/-- Defining equation for finite-prime descent from (L2). -/
@[simp]
theorem finitePrimeCorrespondence_restrict
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) (P : AbsolutePrime) :
    finitePrimeCorrespondence theta K₁ (finitePrime K₁.field P) =
      finitePrime (correspondingField theta K₁)
        (primeCorrespondence (correspondingRestrictedIso theta K₁) P) := by
  let e := correspondingRestrictedIso theta K₁
  let Q := absolutePrimeLift K₁.field (finitePrime K₁.field P)
  have hsource : finitePrime K₁.field Q = finitePrime K₁.field P := by
    simp only [Q, finitePrime_absolutePrimeLift]
  obtain ⟨g, hg⟩ := exists_smul_of_finitePrime_eq K₁.field Q P hsource
  change finitePrime (correspondingField theta K₁)
      (primeCorrespondence e Q) =
    finitePrime (correspondingField theta K₁) (primeCorrespondence e P)
  calc
    finitePrime (correspondingField theta K₁) (primeCorrespondence e Q) =
        finitePrime (correspondingField theta K₁)
          (e g • primeCorrespondence e Q) :=
      (finitePrime_smul (correspondingField theta K₁) (e g)
        (primeCorrespondence e Q)).symm
    _ = finitePrime (correspondingField theta K₁)
        (primeCorrespondence e (g • Q)) := by
      rw [primeCorrespondence_equivariant_L2]
    _ = finitePrime (correspondingField theta K₁)
        (primeCorrespondence e P) := by rw [hg]

/-- The descended correspondence preserves the rational prime and the two
local invariants, by (L3). -/
theorem finitePrimeCorrespondence_invariants
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁)
    (v : NU.LocalTheory.FinitePlace K₁.field.field) :
    rationalPrime K₁.field v =
        rationalPrime (correspondingField theta K₁)
          (finitePrimeCorrespondence theta K₁ v) ∧
      absoluteRamificationIndex K₁.field v =
        absoluteRamificationIndex (correspondingField theta K₁)
          (finitePrimeCorrespondence theta K₁ v) ∧
      absoluteResidueDegree K₁.field v =
        absoluteResidueDegree (correspondingField theta K₁)
          (finitePrimeCorrespondence theta K₁ v) := by
  obtain ⟨P, rfl⟩ := finitePrime_surjective K₁.field v
  rw [finitePrimeCorrespondence_restrict]
  exact primeCorrespondence_invariants_L3
    (correspondingRestrictedIso theta K₁) P

/-- Equivariance of the descended finite-prime correspondence under the
finite quotient action (blueprint §1.3). -/
theorem finitePrimeCorrespondence_equivariant
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁)
    (g : absoluteGaloisGroup K₁.field) (P : AbsolutePrime) :
    finitePrime (correspondingField theta K₁)
        (primeCorrespondence (correspondingRestrictedIso theta K₁) (g • P)) =
      finitePrime (correspondingField theta K₁)
        (correspondingRestrictedIso theta K₁ g •
          primeCorrespondence (correspondingRestrictedIso theta K₁) P) := by
  rw [primeCorrespondence_equivariant_L2]

/-! ## Degree one and decomposition-group containment -/

/-- The absolute decomposition group `D_P^ℚ` as a subgroup of the literal
ambient `G_ℚ`. -/
def rationalDecompositionGroup (P : AbsolutePrime) :
    Subgroup RationalAbsoluteGaloisGroup :=
  MulAction.stabilizer RationalAbsoluteGaloisGroup P

/-- Intersecting the ambient decomposition group with `G_F` gives
`D_P^F`. -/
theorem decompositionGroup_eq_comap_rational
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    decompositionGroup F P =
      Subgroup.comap (absoluteGaloisGroup F).subtype
        (rationalDecompositionGroup P) :=
  rfl

/-- Blueprint Lemma `lem:degree-one-decomp`: a finite prime has absolute
local degree one exactly when the full rational decomposition group lies in
`G_F`; in that case `D_P^ℚ = D_P^F` after the literal inclusion. -/
theorem degreeOne_iff_rationalDecompositionGroup_le
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    IsAbsoluteDegreeOne F (finitePrime F P) ↔
      rationalDecompositionGroup P ≤ absoluteGaloisGroup F := by
  let L := rationalGaloisExtensionContaining F 0
  let N := L.toExtension.field
  let v := finitePrime F P
  let w := finitePrime N P
  let q := rationalPrime F v
  letI : IsGalois ℚ N.field := L.isGalois
  letI : Algebra F.field N.field :=
    inferInstanceAs (Algebra F.field L.toExtension.field.field)
  letI : IsScalarTower ℚ F.field N.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : IsGalois F.field N.field :=
    IsGalois.tower_top_of_isGalois ℚ F.field N.field
  have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by
    change v.asIdeal = (NU.LocalTheory.restrictFinitePlace F.field w).asIdeal
    exact congrArg HeightOneSpectrum.asIdeal
      (restrictFinitePlace_finitePrime F L.toExtension P).symm⟩
  have hvq : v.asIdeal.LiesOver q.asIdeal := ⟨by rfl⟩
  have hwq : w.asIdeal.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans w.asIdeal v.asIdeal q.asIdeal
  letI : w.asIdeal.LiesOver v.asIdeal := hwv
  letI : v.asIdeal.LiesOver q.asIdeal := hvq
  letI : w.asIdeal.LiesOver q.asIdeal := hwq
  let Dq := MulAction.stabilizer (N.field ≃ₐ[ℚ] N.field) w.asIdeal
  let Df := MulAction.stabilizer (N.field ≃ₐ[F.field] N.field) w.asIdeal
  have he : absoluteRamificationIndex F v =
      v.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
    change q.asIdeal.ramificationIdx' v.asIdeal = _
    exact Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal v.asIdeal
      q.ne_bot
  have hf : absoluteResidueDegree F v =
      v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    change q.asIdeal.inertiaDeg' v.asIdeal = _
    exact Ideal.inertiaDeg'_eq_inertiaDeg q.asIdeal v.asIdeal
  have hcardq : Nat.card Dq =
      w.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    calc
      Nat.card Dq = q.asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers N.field) *
        q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers N.field) := by
          exact Ideal.card_stabilizer_eq q.asIdeal w.asIdeal
      _ = _ := by
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal
            w.asIdeal (N.field ≃ₐ[ℚ] N.field),
          Ideal.inertiaDegIn_eq_inertiaDeg q.asIdeal w.asIdeal
            (N.field ≃ₐ[ℚ] N.field)]
  have hcardf : Nat.card Df =
      w.asIdeal.ramificationIdx (NumberField.RingOfIntegers F.field) *
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers F.field) := by
    calc
      Nat.card Df = v.asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers N.field) *
        v.asIdeal.inertiaDegIn (NumberField.RingOfIntegers N.field) := by
          exact Ideal.card_stabilizer_eq v.asIdeal w.asIdeal
      _ = _ := by
        rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal
            w.asIdeal (N.field ≃ₐ[F.field] N.field),
          Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal
            (N.field ≃ₐ[F.field] N.field)]
  have hcard : Nat.card Dq = absoluteLocalDegree F v * Nat.card Df := by
    rw [hcardq, hcardf, absoluteLocalDegree, he, hf,
      Ideal.ramificationIdx_tower v.asIdeal w.asIdeal,
      Ideal.inertiaDeg_tower v.asIdeal w.asIdeal]
    ring
  let inc : Df → Dq := fun sigma =>
    ⟨sigma.1.restrictScalars ℚ, by
      change sigma.1.restrictScalars ℚ • w.asIdeal = w.asIdeal
      change sigma.1 • w.asIdeal = w.asIdeal
      exact sigma.2⟩
  have hinc : Function.Injective inc := by
    intro sigma tau hst
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun (congrArg Subtype.val hst) x
    exact hx
  constructor
  · intro hdeg
    have hcardeq : Nat.card Df = Nat.card Dq := by
      rw [hcard, hdeg, one_mul]
    letI : Fintype Df := Fintype.ofFinite Df
    letI : Fintype Dq := Fintype.ofFinite Dq
    have hinc_bij : Function.Bijective inc :=
      (Fintype.bijective_iff_injective_and_card inc).2
        ⟨hinc, by
          simpa only [Nat.card_eq_fintype_card] using hcardeq⟩
    intro gamma hgamma
    let sigma : N.field ≃ₐ[ℚ] N.field :=
      AlgEquiv.restrictNormalHom N.field gamma
    have hplace : NU.LocalTheory.conjugateFinitePlace ℚ sigma w = w := by
      rw [← finitePrime_ambient_smul]
      change finitePrime N (gamma • P) = finitePrime N P
      rw [hgamma]
    let d : Dq := ⟨sigma, by
      change sigma • w.asIdeal = w.asIdeal
      exact congrArg HeightOneSpectrum.asIdeal hplace⟩
    obtain ⟨tau, htau⟩ := hinc_bij.2 d
    have hres : tau.1.restrictScalars ℚ = sigma :=
      congrArg Subtype.val htau
    intro x
    let y : N.field := ⟨x.1, L.toExtension.le_base x.2⟩
    have hy : tau.1 y = y := tau.1.commutes x
    calc
      gamma x.1 = N.field.val (sigma y) :=
        (AlgEquiv.restrictNormal_commutes gamma N.field y).symm
      _ = N.field.val ((tau.1.restrictScalars ℚ) y) := by rw [hres]
      _ = N.field.val y := congrArg N.field.val hy
      _ = x.1 := rfl
  · intro hle
    have hinc_surj : Function.Surjective inc := by
      intro d
      letI : IsGalois ℚ Omega := rationalOmega_isGalois
      obtain ⟨gamma, hgamma⟩ :=
        AlgEquiv.restrictNormalHom_surjective Omega d.1
      have hfinite : finitePrime N (gamma • P) = finitePrime N P := by
        rw [finitePrime_ambient_smul, hgamma]
        apply HeightOneSpectrum.ext
        exact d.2
      obtain ⟨k, hk⟩ := exists_smul_of_finitePrime_eq N
        (gamma • P) P hfinite
      let gamma' : RationalAbsoluteGaloisGroup :=
        (k : RationalAbsoluteGaloisGroup) * gamma
      have hstab : gamma' • P = P := by
        change ((k : RationalAbsoluteGaloisGroup) * gamma) • P = P
        rw [mul_smul]
        exact hk
      have hfix : gamma' ∈ absoluteGaloisGroup F := hle hstab
      have hkres : AlgEquiv.restrictNormalHom N.field
          (k : RationalAbsoluteGaloisGroup) = 1 := by
        apply AlgEquiv.ext
        intro x
        apply N.field.val.injective
        calc
          N.field.val ((AlgEquiv.restrictNormalHom N.field
              (k : RationalAbsoluteGaloisGroup)) x) = k.1 (N.field.val x) :=
            AlgEquiv.restrictNormal_commutes k.1 N.field x
          _ = N.field.val x := k.2 x
          _ = N.field.val
            ((1 : N.field ≃ₐ[ℚ] N.field) x) := rfl
      have hres : AlgEquiv.restrictNormalHom N.field gamma' = d.1 := by
        change AlgEquiv.restrictNormalHom N.field
          ((k : RationalAbsoluteGaloisGroup) * gamma) = d.1
        rw [map_mul, hkres, one_mul, hgamma]
      let tau0 : N.field ≃ₐ[F.field] N.field :=
        { d.1 with
          commutes' := fun x => by
            let y : N.field := ⟨x.1, L.toExtension.le_base x.2⟩
            apply N.field.val.injective
            calc
              N.field.val (d.1 y) =
                  N.field.val
                    ((AlgEquiv.restrictNormalHom N.field gamma') y) := by
                rw [hres]
              _ = gamma' (N.field.val y) :=
                AlgEquiv.restrictNormal_commutes gamma' N.field y
              _ = x.1 := hfix x
              _ = N.field.val y := rfl }
      let tau : Df := ⟨tau0, by
        change tau0 • w.asIdeal = w.asIdeal
        change d.1 • w.asIdeal = w.asIdeal
        exact d.2⟩
      refine ⟨tau, ?_⟩
      apply Subtype.ext
      rfl
    have hcardeq : Nat.card Df = Nat.card Dq :=
      Nat.card_congr (Equiv.ofBijective inc ⟨hinc, hinc_surj⟩)
    have hmul : 1 * Nat.card Df =
        absoluteLocalDegree F v * Nat.card Df := by
      calc
        1 * Nat.card Df = Nat.card Df := one_mul _
        _ = Nat.card Dq := hcardeq
        _ = absoluteLocalDegree F v * Nat.card Df := hcard
    have hpos : 0 < Nat.card Df := Nat.card_pos
    change absoluteLocalDegree F v = 1
    exact (Nat.eq_of_mul_eq_mul_right hpos hmul).symm

/-- The equality clause of `lem:degree-one-decomp`. -/
theorem map_decompositionGroup_eq_rational_of_degreeOne
    (F : NumberFieldInOmega) (P : AbsolutePrime)
    (hP : IsAbsoluteDegreeOne F (finitePrime F P)) :
    Subgroup.map (absoluteGaloisGroup F).subtype
      (decompositionGroup F P) = rationalDecompositionGroup P := by
  rw [decompositionGroup_eq_comap_rational]
  apply Subgroup.map_comap_eq_self
  intro g hg
  have hle :=
    (degreeOne_iff_rationalDecompositionGroup_le F P).mp hP
  exact ⟨⟨g, hle hg⟩, rfl⟩

/-! ## Named finite quotient maps -/

/-- The finite relative Galois group `Gal(N/F)`, represented inside
`Gal(N/ℚ)` by literal fixation of the embedded subfield `F`. -/
def relativeGaloisGroup
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field) :
    Subgroup (N.field ≃ₐ[ℚ] N.field) where
  carrier := {g | ∀ x : F.field,
    g ⟨x.1, hFN x.2⟩ = ⟨x.1, hFN x.2⟩}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    rw [AlgEquiv.mul_apply, hh x, hg x]
  inv_mem' := by
    intro g hg x
    let y : N.field := ⟨x.1, hFN x.2⟩
    change g⁻¹ y = y
    calc
      g⁻¹ y = g⁻¹ (g y) := congrArg g.symm (hg x).symm
      _ = y := g.symm_apply_apply y

/-- Restriction from `G_F` to the named finite quotient `Gal(N/F)`. -/
noncomputable def finiteQuotientMap
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field] :
    absoluteGaloisGroup F →* relativeGaloisGroup F N hFN where
  toFun g :=
    ⟨AlgEquiv.restrictNormalHom N.field g.1, by
      intro x
      apply N.field.val.injective
      calc
        N.field.val
            ((AlgEquiv.restrictNormalHom N.field g.1)
              ⟨x.1, hFN x.2⟩) =
            g.1 (N.field.val ⟨x.1, hFN x.2⟩) :=
          AlgEquiv.restrictNormal_commutes g.1 N.field _
        _ = N.field.val ⟨x.1, hFN x.2⟩ := g.2 x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (AlgEquiv.restrictNormalHom N.field)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (AlgEquiv.restrictNormalHom N.field) g.1 h.1

/-- Defining restriction equation for the named finite quotient map. -/
@[simp]
theorem finiteQuotientMap_apply
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field]
    (g : absoluteGaloisGroup F) (x : N.field) :
    N.field.val ((finiteQuotientMap F N hFN g).1 x) =
      g.1 (N.field.val x) :=
  AlgEquiv.restrictNormal_commutes g.1 N.field x

/-- The restriction map onto `Gal(N/F)` is surjective. -/
theorem finiteQuotientMap_surjective
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field] :
    Function.Surjective (finiteQuotientMap F N hFN) := by
  letI : IsGalois ℚ Omega := rationalOmega_isGalois
  intro sigma
  obtain ⟨g, hg⟩ :=
    AlgEquiv.restrictNormalHom_surjective Omega sigma.1
  have hfix : ∀ x : F.field, g x.1 = x.1 := by
    intro x
    let y : N.field := ⟨x.1, hFN x.2⟩
    have hy := DFunLike.congr_fun hg y
    calc
      g x.1 = N.field.val
          ((AlgEquiv.restrictNormalHom N.field g) y) :=
        (AlgEquiv.restrictNormal_commutes g N.field y).symm
      _ = N.field.val (sigma.1 y) := congrArg Subtype.val hy
      _ = x.1 := congrArg Subtype.val (sigma.2 x)
  let gF : absoluteGaloisGroup F := ⟨g, hfix⟩
  refine ⟨gF, ?_⟩
  apply Subtype.ext
  exact hg

/-- An isomorphism preserves a common normal level when it maps the two
copies of `G_N` exactly. -/
def PreservesNormalLevel
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field) : Prop :=
  Subgroup.map theta.toMulEquiv.toMonoidHom
      ((absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₁)) =
    (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₂)

private theorem finiteQuotientMap_ker
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    [IsGalois ℚ N.field] :
    (finiteQuotientMap F N hFN).ker =
      (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg x
    have hx := congrArg
      (fun e : relativeGaloisGroup F N hFN => e.1 x) hg
    calc
      g.1 x.1 = N.field.val ((finiteQuotientMap F N hFN g).1 x) :=
        (finiteQuotientMap_apply F N hFN g x).symm
      _ = N.field.val x := congrArg Subtype.val hx
  · intro hg
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    change (finiteQuotientMap F N hFN g).1 x = x
    apply N.field.val.injective
    calc
      N.field.val ((finiteQuotientMap F N hFN g).1 x) = g.1 x.1 :=
        finiteQuotientMap_apply F N hFN g x
      _ = x.1 := hg x

private def finiteQuotientTransportedHom
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₂ : F₂.field ≤ N.field) [IsGalois ℚ N.field] :
    absoluteGaloisGroup F₁ →*
      relativeGaloisGroup F₂ N h₂ :=
  (finiteQuotientMap F₂ N h₂).comp theta.toMonoidHom

private theorem finiteQuotient_ker_le_transport
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂) :
    (finiteQuotientMap F₁ N h₁).ker ≤
      (finiteQuotientTransportedHom theta N h₂).ker := by
  intro g hg
  rw [finiteQuotientMap_ker F₁ N h₁] at hg
  have htheta : theta g ∈
      (absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₂) := by
    rw [← hN]
    exact ⟨g, hg, rfl⟩
  change finiteQuotientMap F₂ N h₂ (theta g) = 1
  apply MonoidHom.mem_ker.mp
  rw [finiteQuotientMap_ker F₂ N h₂]
  exact htheta

private noncomputable def finiteQuotientDescendedHom
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂) :
    relativeGaloisGroup F₁ N h₁ →*
      relativeGaloisGroup F₂ N h₂ :=
  (finiteQuotientMap F₁ N h₁).liftOfSurjective
    (finiteQuotientMap_surjective F₁ N h₁)
    ⟨finiteQuotientTransportedHom theta N h₂,
      finiteQuotient_ker_le_transport theta N h₁ h₂ hN⟩

private theorem finiteQuotientDescendedHom_comp
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂)
    (g : absoluteGaloisGroup F₁) :
    finiteQuotientDescendedHom theta N h₁ h₂ hN
        (finiteQuotientMap F₁ N h₁ g) =
      finiteQuotientMap F₂ N h₂ (theta g) := by
  exact (finiteQuotientMap F₁ N h₁).liftOfRightInverse_comp_apply
    (Function.surjInv (finiteQuotientMap_surjective F₁ N h₁))
    (Function.rightInverse_surjInv
      (finiteQuotientMap_surjective F₁ N h₁))
    ⟨finiteQuotientTransportedHom theta N h₂,
      finiteQuotient_ker_le_transport theta N h₁ h₂ hN⟩ g

private theorem finiteQuotientDescendedHom_bijective
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂) :
    Function.Bijective
      (finiteQuotientDescendedHom theta N h₁ h₂ hN) := by
  have hinj : Function.Injective
      (finiteQuotientDescendedHom theta N h₁ h₂ hN) := by
    apply (MonoidHom.ker_eq_bot_iff
      (finiteQuotientDescendedHom theta N h₁ h₂ hN)).mp
    ext x
    simp only [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := finiteQuotientMap_surjective F₁ N h₁ x
      rw [finiteQuotientDescendedHom_comp] at hx
      have htheta : theta g ∈
          (finiteQuotientMap F₂ N h₂).ker := hx
      rw [finiteQuotientMap_ker F₂ N h₂, ← hN] at htheta
      rcases htheta with ⟨a, ha, heq⟩
      have hag : a = g := theta.injective heq
      apply MonoidHom.mem_ker.mp
      rw [finiteQuotientMap_ker F₁ N h₁, ← hag]
      exact ha
    · rintro rfl
      exact map_one _
  have hsurj : Function.Surjective
      (finiteQuotientDescendedHom theta N h₁ h₂ hN) := by
    intro y
    obtain ⟨g₂, rfl⟩ := finiteQuotientMap_surjective F₂ N h₂ y
    refine ⟨finiteQuotientMap F₁ N h₁ (theta.symm g₂), ?_⟩
    rw [finiteQuotientDescendedHom_comp, theta.apply_symm_apply]
  exact ⟨hinj, hsurj⟩

/-- The named quotient isomorphism induced by `theta` at a preserved normal
level. -/
noncomputable def finiteQuotientIso
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂) :
    relativeGaloisGroup F₁ N h₁ ≃*
      relativeGaloisGroup F₂ N h₂ := by
  exact MulEquiv.ofBijective
    (finiteQuotientDescendedHom theta N h₁ h₂ hN)
    (finiteQuotientDescendedHom_bijective theta N h₁ h₂ hN)

/-- Defining commuting equation for the finite quotient induced by
`theta`. -/
@[simp]
theorem finiteQuotientIso_comp_restriction
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (hN : PreservesNormalLevel theta N h₁ h₂)
    (g : absoluteGaloisGroup F₁) :
    finiteQuotientIso theta N h₁ h₂ hN
        (finiteQuotientMap F₁ N h₁ g) =
      finiteQuotientMap F₂ N h₂ (theta g) := by
  exact finiteQuotientDescendedHom_comp theta N h₁ h₂ hN g

end

end NU.NeukirchUchida
