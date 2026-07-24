import Submission.NU.LCFT.FundamentalClass.General
import Submission.NU.LCFT.LubinTate.ColemanNorm

/-!
# Completion data used by Neukirch--Uchida

This file isolates the proved finite-level and completion data needed by the
Neukirch--Uchida Maschke bridge.  In particular, its import closure does not
contain the unfinished finite-projection theorem.
-/

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel

universe u v w

/-- Valuation, topology, and compatibility data on a finite extension of a local field.

Inhabitation sketch: the unique extension of the normalized valuation to a finite separable
extension, with its valuation topology, supplies this record.  All compatibility fields are
propositions, so choosing different proofs does not create a second arithmetic extension. -/
structure LocalFieldExtensionData (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] where
  /-- The extended valuation relation. -/
  valuativeRel : ValuativeRel L
  /-- The valuation topology. -/
  topology : TopologicalSpace L
  /-- The extension is again a nonarchimedean local field. -/
  localField :
    letI : ValuativeRel L := valuativeRel
    letI : TopologicalSpace L := topology
    IsNonarchimedeanLocalField L
  /-- The displayed valuation extends the one on the base. -/
  valuativeExtension :
    letI : ValuativeRel L := valuativeRel
    letI : TopologicalSpace L := topology
    letI : IsNonarchimedeanLocalField L := localField
    ValuativeExtension K L
  /-- Scalar multiplication is continuous for the displayed topologies. -/
  continuousSMul :
    letI : ValuativeRel L := valuativeRel
    letI : TopologicalSpace L := topology
    ContinuousSMul K L

/-- Every finite separable extension of a nonarchimedean local field has compatible local-field
structure.  This is the instance-transport bridge for intermediate fields. -/
theorem localFieldExtensionData_exists
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Nonempty (LocalFieldExtensionData K L) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let vL : ValuativeRel L :=
    ValuativeRel.ofValuation (NormedField.valuation (K := L))
  let tL : TopologicalSpace L := inferInstance
  letI : ValuativeRel L := vL
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : TopologicalSpace L := tL
  letI : Valued L NNReal := NormedField.toValued
  have htop : IsValuativeTopology L := by
    apply IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
    have hv : (Valued.v : Valuation L NNReal) = NormedField.valuation := rfl
    rw [← hv]
    exact Valued.is_topological_valuation
  letI : IsValuativeTopology L := htop
  have hloc : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K L
  letI : LocallyCompactSpace L := hloc
  have hnontriv : ValuativeRel.IsNontrivial L := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance
  letI : ValuativeRel.IsNontrivial L := hnontriv
  let hL : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hloc
      toIsNontrivial := hnontriv }
  letI : IsNonarchimedeanLocalField L := hL
  let hKL : ValuativeExtension K L := by
    constructor
    intro a b
    change NormedField.valuation (algebraMap K L a) ≤
        NormedField.valuation (algebraMap K L b) ↔ a ≤ᵥ b
    rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    change spectralNorm K L (algebraMap K L a) ≤
        spectralNorm K L (algebraMap K L b) ↔ a ≤ᵥ b
    rw [spectralNorm_extends, spectralNorm_extends,
      Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    exact Valued.toNormedField.norm_le_iff
  letI : ValuativeExtension K L := hKL
  exact ⟨⟨vL, tL, hL, hKL, inferInstance⟩⟩

/-- The selected compatible local-field structure on a finite separable extension. -/
noncomputable def localFieldExtensionData
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    LocalFieldExtensionData K L :=
  (localFieldExtensionData_exists K L).some

/-- Coherence of the selected local-field bundles in a finite separable scalar tower.

The middle and top structures are *definitionally* the two `localFieldExtensionData` selections
from the same base.  The fields below identify the independently selected `L/E` bundle with the
direct `K/E` selection and supply the relative valuation/topology instances; proofs of projection
and norm functoriality therefore never have to combine independently captured structures. -/
structure SelectedLocalFieldTowerData
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [FiniteDimensional L E] [FiniteDimensional K E]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L E] [Algebra.IsSeparable K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Prop where
  /-- Selecting the valuation on `E` over the selected middle field gives the same valuation as
  selecting it directly over `K`. -/
  relative_valuativeRel_eq :
    let DL := localFieldExtensionData K L
    let DE := localFieldExtensionData K E
    letI : ValuativeRel L := DL.valuativeRel
    letI : TopologicalSpace L := DL.topology
    letI : IsNonarchimedeanLocalField L := DL.localField
    letI : ValuativeExtension K L := DL.valuativeExtension
    let DLE := localFieldExtensionData L E
    DLE.valuativeRel = DE.valuativeRel
  /-- The corresponding independently selected valuation topologies also agree. -/
  relative_topology_eq :
    let DL := localFieldExtensionData K L
    let DE := localFieldExtensionData K E
    letI : ValuativeRel L := DL.valuativeRel
    letI : TopologicalSpace L := DL.topology
    letI : IsNonarchimedeanLocalField L := DL.localField
    letI : ValuativeExtension K L := DL.valuativeExtension
    let DLE := localFieldExtensionData L E
    DLE.topology = DE.topology
  /-- The selected valuation on `E` extends the selected valuation on `L`. -/
  valuativeExtension :
    let DL := localFieldExtensionData K L
    let DE := localFieldExtensionData K E
    letI : ValuativeRel L := DL.valuativeRel
    letI : TopologicalSpace L := DL.topology
    letI : IsNonarchimedeanLocalField L := DL.localField
    letI : ValuativeExtension K L := DL.valuativeExtension
    letI : ValuativeRel E := DE.valuativeRel
    letI : TopologicalSpace E := DE.topology
    letI : IsNonarchimedeanLocalField E := DE.localField
    letI : ValuativeExtension K E := DE.valuativeExtension
    ValuativeExtension L E
  /-- Scalar multiplication is continuous for the same two selected topologies. -/
  continuousSMul :
    let DL := localFieldExtensionData K L
    let DE := localFieldExtensionData K E
    letI : ValuativeRel L := DL.valuativeRel
    letI : TopologicalSpace L := DL.topology
    letI : IsNonarchimedeanLocalField L := DL.localField
    letI : ValuativeExtension K L := DL.valuativeExtension
    letI : ContinuousSMul K L := DL.continuousSMul
    letI : ValuativeRel E := DE.valuativeRel
    letI : TopologicalSpace E := DE.topology
    letI : IsNonarchimedeanLocalField E := DE.localField
    letI : ValuativeExtension K E := DE.valuativeExtension
    letI : ContinuousSMul K E := DE.continuousSMul
    ContinuousSMul L E

private theorem localFieldExtension_valuativeRel_unique
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v₁ v₂ : ValuativeRel L) (t₁ t₂ : TopologicalSpace L)
    (hlocal₁ : @IsNonarchimedeanLocalField L _ v₁ t₁)
    (hlocal₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (hext₁ : @ValuativeExtension K L _ _ _ v₁ _)
    (hext₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  let v1 : Valuation L (letI : ValuativeRel L := v₁
      ValuativeRel.ValueGroupWithZero L) := by
    letI : ValuativeRel L := v₁
    exact ValuativeRel.valuation L
  let v2 : Valuation L (letI : ValuativeRel L := v₂
      ValuativeRel.ValueGroupWithZero L) := by
    letI : ValuativeRel L := v₂
    exact ValuativeRel.valuation L
  have hmem₁ (x : L) : v1 x ≤ 1 ↔ IsIntegral (RingOfIntegers K) x := by
    letI : ValuativeRel L := v₁
    letI : TopologicalSpace L := t₁
    letI : IsNonarchimedeanLocalField L := hlocal₁
    letI : ValuativeExtension K L := hext₁
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
      ringOfIntegers_module_finite K L
    change x ∈ (ValuativeRel.valuation L).integer ↔ _
    constructor
    · intro hx
      let ox : RingOfIntegers L := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers K) (RingOfIntegers L) L)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation L)).mem_of_integral
        hx.tower_top
  have hmem₂ (x : L) : v2 x ≤ 1 ↔ IsIntegral (RingOfIntegers K) x := by
    letI : ValuativeRel L := v₂
    letI : TopologicalSpace L := t₂
    letI : IsNonarchimedeanLocalField L := hlocal₂
    letI : ValuativeExtension K L := hext₂
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
      ringOfIntegers_module_finite K L
    change x ∈ (ValuativeRel.valuation L).integer ↔ _
    constructor
    · intro hx
      let ox : RingOfIntegers L := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers K) (RingOfIntegers L) L)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation L)).mem_of_integral
        hx.tower_top
  have heq : v1.IsEquiv v2 := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    exact (hmem₁ x).trans (hmem₂ x).symm
  apply @ValuativeRel.ext L _ v₁ v₂
  funext x y
  apply propext
  have h₁ : @ValuativeRel.vle L _ v₁ x y ↔ v1 x ≤ v1 y := by
    letI : ValuativeRel L := v₁
    exact Valuation.Compatible.vle_iff_le _ _
  have h₂ : @ValuativeRel.vle L _ v₂ x y ↔ v2 x ≤ v2 y := by
    letI : ValuativeRel L := v₂
    exact Valuation.Compatible.vle_iff_le _ _
  exact h₁.trans ((heq x y).trans h₂.symm)

private theorem localFieldExtension_topology_unique
    (L : Type v) [Field L]
    (v₁ v₂ : ValuativeRel L) (t₁ t₂ : TopologicalSpace L)
    (hlocal₁ : @IsNonarchimedeanLocalField L _ v₁ t₁)
    (hlocal₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (hv : v₁ = v₂) : t₁ = t₂ := by
  letI : ValuativeRel L := v₁
  have hlocal₂' : @IsNonarchimedeanLocalField L _ v₁ t₂ := by
    rw [hv]
    exact hlocal₂
  have h₁ : t₁ = (ValuativeRel.valuation L).subgroups_basis.topology := by
    letI : TopologicalSpace L := t₁
    letI : IsNonarchimedeanLocalField L := hlocal₁
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation L)
  have h₂ : t₂ = (ValuativeRel.valuation L).subgroups_basis.topology := by
    letI : TopologicalSpace L := t₂
    letI : IsNonarchimedeanLocalField L := hlocal₂'
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation L)
  exact h₁.trans h₂.symm

/-- The unique extension theorem, applied compatibly in a tower, supplies relative instances on
the exact globally selected bundles. -/
theorem selectedLocalFieldTowerData
    (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [FiniteDimensional L E] [FiniteDimensional K E]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L E] [Algebra.IsSeparable K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    SelectedLocalFieldTowerData K L E := by
  let DL := localFieldExtensionData K L
  let DE := localFieldExtensionData K E
  letI : ValuativeRel L := DL.valuativeRel
  letI : TopologicalSpace L := DL.topology
  letI : IsNonarchimedeanLocalField L := DL.localField
  letI : ValuativeExtension K L := DL.valuativeExtension
  letI : ContinuousSMul K L := DL.continuousSMul
  let DLE := localFieldExtensionData L E
  let hKE : @ValuativeExtension K E _ _ _ DLE.valuativeRel _ := by
    letI : ValuativeRel E := DLE.valuativeRel
    letI : TopologicalSpace E := DLE.topology
    letI : IsNonarchimedeanLocalField E := DLE.localField
    letI : ValuativeExtension L E := DLE.valuativeExtension
    constructor
    intro x y
    rw [IsScalarTower.algebraMap_apply K L E x,
      IsScalarTower.algebraMap_apply K L E y,
      ValuativeExtension.vle_iff_vle (A := L) (B := E),
      ValuativeExtension.vle_iff_vle (A := K) (B := L)]
  have hv : DLE.valuativeRel = DE.valuativeRel :=
    localFieldExtension_valuativeRel_unique K E DLE.valuativeRel DE.valuativeRel
      DLE.topology DE.topology DLE.localField DE.localField hKE DE.valuativeExtension
  have ht : DLE.topology = DE.topology :=
    localFieldExtension_topology_unique E DLE.valuativeRel DE.valuativeRel
      DLE.topology DE.topology DLE.localField DE.localField hv
  refine ⟨hv, ht, ?_, ?_⟩
  · change @ValuativeExtension L E _ _ _ DE.valuativeRel _
    let h := DLE.valuativeExtension
    rw [hv] at h
    exact h
  · change @ContinuousSMul L E inferInstance DL.topology DE.topology
    let h := DLE.continuousSMul
    rw [ht] at h
    exact h

/-- A finite abelian extension inside one ambient separable closure.

Inhabitation sketch: the trivial extension and every actual finite abelian intermediate field
inhabit the record.  Local-field data are not stored here: every consumer uses the one globally
selected bundle for `field`, so instance choices cannot split one field into several objects. -/
structure FiniteAbelianExtension (K : Type u) (Ksep : Type v)
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] where
  /-- The underlying finite Galois intermediate field. -/
  field : FiniteGaloisIntermediateField K Ksep
  /-- Commutativity of its Galois group. -/
  commutative : ∀ σ τ : (field ≃ₐ[K] field), σ * τ = τ * σ

/-- Compatible local-field structures exist on a finite abelian extension. -/
theorem FiniteAbelianExtension.localField
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : FiniteAbelianExtension K Ksep) :
    Nonempty (LocalFieldExtensionData K L.field) :=
  ⟨localFieldExtensionData K L.field⟩

/-- Taking the witness from `FiniteAbelianExtension.localField` recovers the global selection. -/
@[simp] theorem FiniteAbelianExtension.localField_some_eq_selected
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : FiniteAbelianExtension K Ksep) :
    L.localField.some = localFieldExtensionData K L.field := rfl

/-- The local-field structure on a finite abelian extension is the global selected bundle. -/
noncomputable def FiniteAbelianExtension.localFieldData
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : FiniteAbelianExtension K Ksep) : LocalFieldExtensionData K L.field :=
  localFieldExtensionData K L.field

/-- Defining coherence equation for finite abelian extension data. -/
@[simp] theorem FiniteAbelianExtension.localFieldData_eq_selected
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : FiniteAbelianExtension K Ksep) :
    L.localFieldData = localFieldExtensionData K L.field := rfl

/-- Genuine unramified arithmetic-Frobenius data on an intermediate extension.

Inhabitation sketch: an unramified extension with its extended valuation is inhabited by the
unique automorphism inducing `x ↦ x ^ |k_K|` on residues.  In the degree-three `F/F⁻¹` test,
`F⁻¹` still generates but fails `frobenius_residue`; hence the two opposite records cannot both be
constructed. -/
structure UnramifiedFiniteExtension
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : FiniteGaloisIntermediateField K Ksep) where
  /-- The compatible local-field structure used to formulate unramifiedness and reduction. -/
  localFieldData : LocalFieldExtensionData K L := localFieldExtensionData K L
  /-- This is the same selected bundle used by `finiteArtin`, not an independent choice. -/
  localFieldData_eq_selected : localFieldData = localFieldExtensionData K L
  /-- Valuation-theoretic unramifiedness (`e=1`). -/
  unramified :
    letI : ValuativeRel L := localFieldData.valuativeRel
    letI : TopologicalSpace L := localFieldData.topology
    letI : IsNonarchimedeanLocalField L := localFieldData.localField
    letI : ValuativeExtension K L := localFieldData.valuativeExtension
    IsUnramifiedLocalExtension K L
  /-- Arithmetic Frobenius. -/
  frobenius : L ≃ₐ[K] L
  /-- Frobenius preserves the valuation ring. -/
  frobenius_preserves_integral :
    letI : ValuativeRel L := localFieldData.valuativeRel
    letI : TopologicalSpace L := localFieldData.topology
    letI : IsNonarchimedeanLocalField L := localFieldData.localField
    ∀ x : RingOfIntegers L,
      ∃ y : RingOfIntegers L, (y : L) = frobenius (x : L)
  /-- The defining residue equation `x ↦ x^|k_K|`; this excludes inverse Frobenius. -/
  frobenius_residue :
    letI : ValuativeRel L := localFieldData.valuativeRel
    letI : TopologicalSpace L := localFieldData.topology
    letI : IsNonarchimedeanLocalField L := localFieldData.localField
    ∀ (x y : RingOfIntegers L),
      (y : L) = frobenius (x : L) →
        Ideal.Quotient.mk (LocalMaximalIdeal L) y =
          (Ideal.Quotient.mk (LocalMaximalIdeal L) x) ^ residueCard K
  /-- Arithmetic Frobenius generates the finite unramified Galois group. -/
  generates : Subgroup.zpowers frobenius = ⊤

/-- Arithmetic Frobenius supplied by genuine unramified extension data. -/
abbrev arithmeticFrobenius
    {K : Type u} {Ksep : Type v}
    [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {L : FiniteGaloisIntermediateField K Ksep} (hL : UnramifiedFiniteExtension L) :=
  hL.frobenius

namespace FiniteReciprocity

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

section CohomologicalNormalization

variable (K₀ L₀ : Type)
  [Field K₀] [Field L₀] [Algebra K₀ L₀]
  [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
  [ValuativeRel K₀] [TopologicalSpace K₀] [IsNonarchimedeanLocalField K₀]
  [ValuativeRel L₀] [TopologicalSpace L₀] [IsNonarchimedeanLocalField L₀]
  [ValuativeExtension K₀ L₀] [ContinuousSMul K₀ L₀]

/-- A base-field unit regarded as an invariant unit of the multiplicative Galois module. -/
def baseUnitInvariant (x : Units K₀) :
    Inhomogeneous.invariants0 (MulRep K₀ L₀) := by
  refine ⟨Additive.ofMul (Units.map (algebraMap K₀ L₀) x), ?_⟩
  intro σ
  change Additive.ofMul (Units.map σ.toRingEquiv.toRingHom.toMonoidHom
      (Units.map (algebraMap K₀ L₀).toMonoidHom x)) =
    Additive.ofMul (Units.map (algebraMap K₀ L₀).toMonoidHom x)
  apply Additive.toMul.injective
  apply Units.ext
  simp

/-- The degree-zero Tate class represented by a base-field unit. -/
def tateClassOfBaseUnit (x : Units K₀) : TateLowDegree.H0 (MulRep K₀ L₀) :=
  QuotientAddGroup.mk' (TateLowDegree.normRangeInInvariants (MulRep K₀ L₀))
    (baseUnitInvariant K₀ L₀ x)

/-- Concrete universe-zero data connecting the fundamental class, abstract reciprocity, and the
literal norm quotient.

Inhabitation sketch: Hilbert 90 and subgroupwise local fundamental classes supply `hypotheses`; a
normalized cocycle represents `fundamentalClassValue`; and `tateQuotient_apply` prevents an
inversion twist in the fixed-field/norm dictionary. -/
structure CohomologicalConstruction where
  hypotheses : AbstractReciprocity.Hypotheses (MulRep K₀ L₀)
  cocycle : Inhomogeneous.C2 (MulRep K₀ L₀)
  cocycle_mem : AbstractReciprocity.IsNormalizedCocycle2 (MulRep K₀ L₀) cocycle
  represents : AbstractReciprocity.cocycleClass2 (MulRep K₀ L₀) cocycle cocycle_mem =
    fundamentalClassValue K₀ L₀
  order_class : addOrderOf (fundamentalClassValue K₀ L₀) = Nat.card (L₀ ≃ₐ[K₀] L₀)
  tateQuotient : TateLowDegree.H0 (MulRep K₀ L₀) ≃+
    Additive (Units K₀ ⧸ normSubgroup K₀ L₀)
  tateQuotient_apply : ∀ x : Units K₀,
    tateQuotient (tateClassOfBaseUnit K₀ L₀ x) =
      Additive.ofMul (QuotientGroup.mk x : Units K₀ ⧸ normSubgroup K₀ L₀)

private noncomputable def reciprocityRestrictedH1Equiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    Inhomogeneous.H1 (Rep.res H.subtype (MulRep K L)) ≃+
      Inhomogeneous.H1 (MulRep (IntermediateField.fixedField H) L) := by
  let E := IntermediateField.fixedField H
  let eG : H ≃* (L ≃ₐ[E] L) := IntermediateField.subgroupEquivAlgEquiv H
  let eM : (Rep.res H.subtype (MulRep K L)).V ≃ₗ[ℤ] (MulRep E L).V :=
    LinearEquiv.refl ℤ (Additive (Units L))
  have he : ∀ g, eM.toLinearMap ∘ₗ (Rep.res H.subtype (MulRep K L)).ρ g =
      (MulRep E L).ρ (eG g) ∘ₗ eM.toLinearMap := by
    intro g
    ext x
    rfl
  exact (comparisonH1 _).trans
    ((groupCohomology.mapIso eG eM he 1).toLinearEquiv.toAddEquiv.trans
      (comparisonH1 _).symm)

private noncomputable def reciprocityRestrictedH2Equiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    Inhomogeneous.H2 (Rep.res H.subtype (MulRep K L)) ≃+
      Inhomogeneous.H2 (MulRep (IntermediateField.fixedField H) L) := by
  let E := IntermediateField.fixedField H
  let eG : H ≃* (L ≃ₐ[E] L) := IntermediateField.subgroupEquivAlgEquiv H
  let eM : (Rep.res H.subtype (MulRep K L)).V ≃ₗ[ℤ] (MulRep E L).V :=
    LinearEquiv.refl ℤ (Additive (Units L))
  have he : ∀ g, eM.toLinearMap ∘ₗ (Rep.res H.subtype (MulRep K L)).ρ g =
      (MulRep E L).ρ (eG g) ∘ₗ eM.toLinearMap := by
    intro g
    ext x
    rfl
  exact (comparisonH2 _).trans
    ((groupCohomology.mapIso eG eM he 2).toLinearEquiv.toAddEquiv.trans
      (comparisonH2 _).symm)

private structure ReciprocityFixedFieldLocalData
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (H : Subgroup (L ≃ₐ[K] L)) where
  valuativeRel : ValuativeRel (IntermediateField.fixedField H)
  localField : @IsNonarchimedeanLocalField (IntermediateField.fixedField H)
    (IntermediateField.fixedField H).toField valuativeRel inferInstance
  lowerExtension : @ValuativeExtension K (IntermediateField.fixedField H)
    _ _ _ valuativeRel _
  upperExtension : @ValuativeExtension (IntermediateField.fixedField H) L
    _ _ valuativeRel _ _

private noncomputable def reciprocityFixedFieldLocalData
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (H : Subgroup (L ≃ₐ[K] L)) : ReciprocityFixedFieldLocalData H := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := L) (Γ₀ := ValuativeRel.ValueGroupWithZero L)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := L).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L :=
    Valued.toNontriviallyNormedField L (ValuativeRel.ValueGroupWithZero L)
  let E := IntermediateField.fixedField H
  letI : NormedField E := inferInstance
  letI : NontriviallyNormedField E := by
    let hex := NormedField.exists_norm_lt K (by norm_num : (0 : ℝ) < 1)
    let a := Classical.choose hex
    have ha := Classical.choose_spec hex
    have ha0 : 0 < ‖a‖ := ha.1
    have ha1 : ‖a‖ < 1 := ha.2
    let ai : E := ⟨algebraMap K L a, by intro σ; simp⟩
    have hvalK : ValuativeRel.valuation K a < ValuativeRel.valuation K 1 :=
      Valued.toNormedField.norm_lt_iff.mp (by simpa using ha1)
    have hrelK : a <ᵥ (1 : K) :=
      (ValuativeRel.valuation K).vlt_iff_lt.mpr hvalK
    have hrelL : algebraMap K L a <ᵥ algebraMap K L (1 : K) :=
      ValuativeExtension.vlt_iff_vlt.mpr hrelK
    have hvalL : ValuativeRel.valuation L (algebraMap K L a) <
        ValuativeRel.valuation L (algebraMap K L (1 : K)) :=
      (ValuativeRel.valuation L).vlt_iff_lt.mp hrelL
    have hnormL : ‖algebraMap K L a‖ < ‖algebraMap K L (1 : K)‖ :=
      Valued.toNormedField.norm_lt_iff.mpr hvalL
    have hainz : ai ≠ 0 := by
      intro h
      have hh := congrArg Subtype.val h
      simp [ai] at hh
      exact (norm_pos_iff.mp ha0) ((algebraMap K L).injective (by simpa using hh))
    refine NontriviallyNormedField.mk ⟨ai⁻¹, ?_⟩
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hainz)).2 (by simpa [ai] using hnormL)
  letI : IsUltrametricDist E := inferInstance
  let vE := NormedField.valuation (K := E)
  letI : ValuativeRel E := ValuativeRel.ofValuation vE
  letI : vE.Compatible := Valuation.Compatible.ofValuation vE
  letI : vE.IsNontrivial := by
    obtain ⟨a, ha0, ha1⟩ :=
      NormedField.exists_norm_lt E (by norm_num : (0 : ℝ) < 1)
    refine ⟨a, ?_, ?_⟩
    · simpa [vE, NormedField.valuation_apply] using ha0.ne'
    · intro h
      have h' := congrArg (fun z : NNReal => (z : ℝ)) h
      change ‖a‖ = 1 at h'
      exact ha1.ne h'
  let normValuedE : Valued E NNReal := NormedField.toValued
  have htop : IsValuativeTopology E := by
    apply IsValuativeTopology.of_mem_nhds_zero_iff_vle vE
    intro s
    exact @Valued.is_topological_valuation E _ NNReal _ normValuedE s
  letI : IsValuativeTopology E := htop
  have hnontriv : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vE).2 inferInstance
  letI : ValuativeRel.IsNontrivial E := hnontriv
  have hloc : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K E
  letI : LocallyCompactSpace E := hloc
  let hlocal : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hloc
      toIsNontrivial := hnontriv }
  letI : IsNonarchimedeanLocalField E := hlocal
  let hupper : ValuativeExtension E L := by
    constructor
    intro a b
    rw [(ValuativeRel.valuation L).vle_iff_le]
    change ValuativeRel.valuation L (a : L) ≤ ValuativeRel.valuation L (b : L) ↔
      ‖a‖₊ ≤ ‖b‖₊
    rw [← NNReal.coe_le_coe]
    exact Valued.toNormedField.norm_le_iff.symm
  letI : ValuativeExtension E L := hupper
  let hlower : ValuativeExtension K E := by
    constructor
    intro a b
    rw [← ValuativeExtension.vle_iff_vle (A := E) (B := L)]
    simpa only [IsScalarTower.algebraMap_apply K E L] using
      (ValuativeExtension.vle_iff_vle (A := K) (B := L) a b)
  exact ⟨inferInstance, hlocal, hlower, hupper⟩

set_option maxHeartbeats 1000000 in
-- Fixed-field transport makes the subgroupwise generator proof elaboration intensive.
private theorem mulRepReciprocityHypotheses
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L] :
    AbstractReciprocity.Hypotheses (MulRep K L) := by
  constructor
  · intro S _
    let E := IntermediateField.fixedField S
    let D := reciprocityFixedFieldLocalData S
    letI : ValuativeRel E := D.valuativeRel
    letI : IsNonarchimedeanLocalField E := D.localField
    letI : ValuativeExtension K E := D.lowerExtension
    letI : ValuativeExtension E L := D.upperExtension
    have hlocal : Subsingleton (Inhomogeneous.H1 (MulRep E L)) :=
      localFundamentalClass_H1 E L
    have hres : Subsingleton (Inhomogeneous.H1
        (Rep.res S.subtype (MulRep K L))) :=
      ⟨fun x y => (reciprocityRestrictedH1Equiv S).injective (hlocal.elim _ _)⟩
    exact ⟨fun x y => (comparisonH1 _).symm.injective (hres.elim _ _)⟩
  · intro S _
    let E := IntermediateField.fixedField S
    let D := reciprocityFixedFieldLocalData S
    letI : ValuativeRel E := D.valuativeRel
    letI : IsNonarchimedeanLocalField E := D.localField
    letI : ValuativeExtension K E := D.lowerExtension
    letI : ValuativeExtension E L := D.upperExtension
    let e := reciprocityRestrictedH2Equiv S
    let c := comparisonH2 (Rep.res S.subtype (MulRep K L))
    let αres := e.symm (fundamentalClassValue E L)
    let α := c αres
    refine ⟨α, ?_, ?_⟩
    · calc
        addOrderOf α = addOrderOf αres :=
          addOrderOf_injective c.toAddMonoidHom c.injective αres
        _ = addOrderOf (fundamentalClassValue E L) :=
          addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective _
        _ = Module.finrank E L := (fundamentalClass E L).order_class
        _ = Nat.card S := IntermediateField.finrank_fixedField_eq_card S
    · intro β
      obtain ⟨n, hn⟩ := (fundamentalClass E L).generates (e (c.symm β))
      refine ⟨n, ?_⟩
      apply c.symm.injective
      rw [map_zsmul]
      dsimp only [α]
      rw [c.symm_apply_apply]
      apply e.injective
      rw [map_zsmul, e.apply_symm_apply, hn]

section NormQuotientDictionary

variable (K L : Type)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

private noncomputable def explicitMulRepInvariantsEquiv :
    Inhomogeneous.invariants0 (MulRep K L) ≃+ Additive (Units K) := by
  let f₀ : Additive (Units K) →+ Additive (Units L) :=
    (Units.map (algebraMap K L).toMonoidHom).toAdditive
  let f : Additive (Units K) →+ Inhomogeneous.invariants0 (MulRep K L) :=
    { toFun := fun x => ⟨f₀ x, by
          intro σ
          change Additive.ofMul (Units.map σ.toRingEquiv.toRingHom.toMonoidHom
            (Units.map (algebraMap K L).toMonoidHom x.toMul)) =
            Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul)
          apply Additive.toMul.injective
          apply Units.ext
          simp⟩
      map_zero' := Subtype.ext f₀.map_zero
      map_add' := fun x y => Subtype.ext (f₀.map_add x y) }
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap K L).injective
    have h' := congrArg (fun z : Inhomogeneous.invariants0 (MulRep K L) =>
      ((show Units L from Additive.toMul z.1) : L)) h
    exact h'
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hfixed : ∀ σ : L ≃ₐ[K] L,
        σ ((show Units L from Additive.toMul x) : L) =
          ((show Units L from Additive.toMul x) : L) := by
      intro σ
      have h := congrArg (fun z : Additive (Units L) => ((z.toMul : Units L) : L)) (hx σ)
      exact h
    rcases (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L)
      ((show Units L from Additive.toMul x) : L)).2 hfixed with ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyz
      rw [hyz, map_zero] at hy
      exact (show Units L from Additive.toMul x).ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    exact hy
  exact (AddEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

private theorem explicitMulRepInvariantsEquiv_baseUnit (x : Units K) :
    explicitMulRepInvariantsEquiv K L (baseUnitInvariant K L x) = Additive.ofMul x := by
  let e := explicitMulRepInvariantsEquiv K L
  apply e.symm.injective
  rw [e.symm_apply_apply]
  apply Subtype.ext
  rfl

private def tateNormQuotientHom :
    Inhomogeneous.invariants0 (MulRep K L) →+
      Additive (Units K ⧸ normSubgroup K L) :=
  (QuotientGroup.mk' (normSubgroup K L)).toAdditive.comp
    (explicitMulRepInvariantsEquiv K L).toAddMonoidHom

private theorem mem_tateNormRange_iff (x : Inhomogeneous.invariants0 (MulRep K L)) :
    x ∈ TateLowDegree.normRangeInInvariants (MulRep K L) ↔
      Additive.toMul (explicitMulRepInvariantsEquiv K L x) ∈ normSubgroup K L := by
  let e := explicitMulRepInvariantsEquiv K L
  constructor
  · rintro ⟨z, hz⟩
    let y : Units L := Additive.toMul z
    have hxbase : x = baseUnitInvariant K L (normUnitsHom K L y) := by
      apply Subtype.ext
      have hz' : (MulRep K L).norm.hom z = x.1 := hz
      rw [← hz']
      apply Additive.toMul.injective
      exact mulRep_norm K L y
    have heq := congrArg e hxbase
    rw [explicitMulRepInvariantsEquiv_baseUnit K L] at heq
    refine ⟨y, ?_⟩
    exact congrArg Additive.toMul heq.symm
  · rintro ⟨y, hy⟩
    have hxbase : baseUnitInvariant K L (Additive.toMul (e x)) = x := by
      apply e.injective
      rw [explicitMulRepInvariantsEquiv_baseUnit K L]
      rfl
    have hbaseval :
        Units.map (algebraMap K L).toMonoidHom (Additive.toMul (e x)) =
          Additive.toMul ((baseUnitInvariant K L (Additive.toMul (e x))).1 :
            Additive (Units L)) := rfl
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    change Additive.toMul ((MulRep K L).norm.hom (Additive.ofMul y)) =
      Additive.toMul x.1
    rw [mulRep_norm K L y, hy]
    exact hbaseval.trans (congrArg
      (fun z : Inhomogeneous.invariants0 (MulRep K L) => Additive.toMul z.1) hxbase)

private theorem tateNormQuotientHom_surjective :
    Function.Surjective (tateNormQuotientHom K L) :=
  (QuotientGroup.mk'_surjective (normSubgroup K L)).comp
    (explicitMulRepInvariantsEquiv K L).surjective

private theorem tateNormQuotientHom_ker :
    (tateNormQuotientHom K L).ker =
      TateLowDegree.normRangeInInvariants (MulRep K L) := by
  ext x
  rw [AddMonoidHom.mem_ker]
  change Additive.ofMul (QuotientGroup.mk (Additive.toMul
    (explicitMulRepInvariantsEquiv K L x))) = 0 ↔ _
  change (QuotientGroup.mk (Additive.toMul (explicitMulRepInvariantsEquiv K L x)) :
    Units K ⧸ normSubgroup K L) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact (mem_tateNormRange_iff K L x).symm

private theorem tateNormRange_le_ker :
    TateLowDegree.normRangeInInvariants (MulRep K L) ≤
      (tateNormQuotientHom K L).ker := by
  rw [tateNormQuotientHom_ker K L]

set_option maxHeartbeats 1000000 in
-- Making the concrete quotient lift unfold through the unit representation is elaboration-heavy.
private def tateQuotientAddHom :
    TateLowDegree.H0 (MulRep K L) →+ Additive (Units K ⧸ normSubgroup K L) :=
  @QuotientAddGroup.lift (Inhomogeneous.invariants0 (MulRep K L))
    (Additive (Units K ⧸ normSubgroup K L)) inferInstance inferInstance
    (TateLowDegree.normRangeInInvariants (MulRep K L)) inferInstance
    (tateNormQuotientHom K L) (tateNormRange_le_ker K L)

private theorem tateQuotientAddHom_bijective :
    Function.Bijective (tateQuotientAddHom K L) := by
  constructor
  · intro a b hab
    induction a using QuotientAddGroup.induction_on with
    | H x =>
      induction b using QuotientAddGroup.induction_on with
      | H y =>
        rw [tateQuotientAddHom, QuotientAddGroup.lift_mk,
          QuotientAddGroup.lift_mk] at hab
        apply QuotientAddGroup.eq.mpr
        rw [← tateNormQuotientHom_ker K L, AddMonoidHom.mem_ker,
          map_add, map_neg, hab]
        exact neg_add_cancel (tateNormQuotientHom K L y :
          Additive (Units K ⧸ normSubgroup K L))
  · intro y
    obtain ⟨x, hx⟩ := tateNormQuotientHom_surjective K L y
    refine ⟨QuotientAddGroup.mk x, ?_⟩
    rw [tateQuotientAddHom, QuotientAddGroup.lift_mk, hx]

private noncomputable def localTateQuotientEquiv :
    TateLowDegree.H0 (MulRep K L) ≃+ Additive (Units K ⧸ normSubgroup K L) :=
  AddEquiv.ofBijective (tateQuotientAddHom K L) (tateQuotientAddHom_bijective K L)

private theorem localTateQuotientEquiv_apply (x : Units K) :
    localTateQuotientEquiv K L (tateClassOfBaseUnit K L x) =
      Additive.ofMul (QuotientGroup.mk x : Units K ⧸ normSubgroup K L) := by
  rw [localTateQuotientEquiv]
  change tateQuotientAddHom K L (tateClassOfBaseUnit K L x) = _
  rw [tateQuotientAddHom, tateClassOfBaseUnit]
  change tateNormQuotientHom K L (baseUnitInvariant K L x) = _
  change Additive.ofMul (QuotientGroup.mk (Additive.toMul
    (explicitMulRepInvariantsEquiv K L (baseUnitInvariant K L x)))) = _
  rw [explicitMulRepInvariantsEquiv_baseUnit K L]
  rfl

end NormQuotientDictionary

/-- Construction of the concrete cohomological package. -/
theorem cohomologicalConstruction_exists :
    Nonempty (CohomologicalConstruction K₀ L₀) := by
  let M := MulRep K₀ L₀
  let C := (AbstractReciprocity.splittingModule_exists M
    (fundamentalClassValue K₀ L₀)).some
  refine ⟨{
    hypotheses := mulRepReciprocityHypotheses K₀ L₀
    cocycle := C.cocycle
    cocycle_mem := C.cocycle_mem
    represents := ?_
    order_class := ?_
    tateQuotient := localTateQuotientEquiv K₀ L₀
    tateQuotient_apply := localTateQuotientEquiv_apply K₀ L₀ }⟩
  · exact C.cocycle_class_eq
  · exact (fundamentalClass K₀ L₀).order_class.trans
      (IsGalois.card_aut_eq_finrank K₀ L₀).symm

/-- The selected concrete cohomological package. -/
noncomputable def cohomologicalConstruction : CohomologicalConstruction K₀ L₀ :=
  (cohomologicalConstruction_exists K₀ L₀).some

/-- The uncompensated map: remove upstream's compensation once, exposing the negative row sum. -/
noncomputable def cohomologicalRawTateEquiv :
    Additive (Abelianization (L₀ ≃ₐ[K₀] L₀)) ≃+ TateLowDegree.H0 (MulRep K₀ L₀) :=
  let D := cohomologicalConstruction K₀ L₀
  (AbstractReciprocity.abstractReciprocity (MulRep K₀ L₀) D.hypotheses
    (fundamentalClassValue K₀ L₀) D.order_class D.cocycle D.cocycle_mem D.represents).trans
      (AddEquiv.neg (TateLowDegree.H0 (MulRep K₀ L₀)))

/-- The raw norm--Tate map attached to the normalized local fundamental class.

The right-hand side literally instantiates `AbstractReciprocity.abstractReciprocity` at
`fundamentalClassValue K₀ L₀`.  The latter is the class whose retained invariant sends it to `1`.
The final negation removes the bar-generator compensation, so this is the *raw* map. -/
noncomputable def normalizedFundamentalClassRawNormTateEquiv :
    Additive (Abelianization (L₀ ≃ₐ[K₀] L₀)) ≃+
      Additive (Units K₀ ⧸ normSubgroup K₀ L₀) :=
  let D := cohomologicalConstruction K₀ L₀
  ((AbstractReciprocity.abstractReciprocity (MulRep K₀ L₀) D.hypotheses
    (fundamentalClassValue K₀ L₀) D.order_class D.cocycle D.cocycle_mem D.represents).trans
      (AddEquiv.neg (TateLowDegree.H0 (MulRep K₀ L₀)))).trans D.tateQuotient

/-- The named raw map is the concrete cohomological raw map followed by the literal Tate
quotient dictionary. -/
theorem normalizedFundamentalClassRawNormTateEquiv_def :
    normalizedFundamentalClassRawNormTateEquiv K₀ L₀ =
      (cohomologicalRawTateEquiv K₀ L₀).trans
        (cohomologicalConstruction K₀ L₀).tateQuotient := by
  rfl

/-- Reinsert the literal sign compensation and then identify `H⁰` with the norm quotient. -/
noncomputable def cohomologicalCompensatedNormTateEquiv :
    Additive (Abelianization (L₀ ≃ₐ[K₀] L₀)) ≃+
      Additive (Units K₀ ⧸ normSubgroup K₀ L₀) :=
  ((cohomologicalRawTateEquiv K₀ L₀).trans
    (AddEquiv.neg (TateLowDegree.H0 (MulRep K₀ L₀)))).trans
      (cohomologicalConstruction K₀ L₀).tateQuotient

/-- Before compensation, a Frobenius generator has the negative row-sum value. -/
theorem cohomologicalRawTateEquiv_apply (g : L₀ ≃ₐ[K₀] L₀) :
    cohomologicalRawTateEquiv K₀ L₀ (Additive.ofMul (Abelianization.of g)) =
      -AbstractReciprocity.rowSumClass (MulRep K₀ L₀)
        (cohomologicalConstruction K₀ L₀).cocycle
        (cohomologicalConstruction K₀ L₀).cocycle_mem g := by
  simp [cohomologicalRawTateEquiv, AbstractReciprocity.abstractReciprocity_apply]

/-- The reinserted negation changes `-rowSum` to the positive row sum. -/
theorem cohomologicalCompensatedTate_apply (g : L₀ ≃ₐ[K₀] L₀) :
    ((cohomologicalRawTateEquiv K₀ L₀).trans
      (AddEquiv.neg (TateLowDegree.H0 (MulRep K₀ L₀))))
        (Additive.ofMul (Abelianization.of g)) =
      AbstractReciprocity.rowSumClass (MulRep K₀ L₀)
        (cohomologicalConstruction K₀ L₀).cocycle
        (cohomologicalConstruction K₀ L₀).cocycle_mem g := by
  rw [AddEquiv.trans_apply, cohomologicalRawTateEquiv_apply]
  rfl

end CohomologicalNormalization

/-- A universe-zero local-field model used only as the source of the explicit universe bridge.

All structures are stored in one bundle, so the normalized fundamental class and abstract Tate
map below are formed with one coherent set of instances. -/
structure UniverseZeroLocalFieldModel where
  K₀ : Type
  L₀ : Type
  fieldK₀ : Field K₀
  fieldL₀ : Field L₀
  algebra :
    letI : Field K₀ := fieldK₀
    letI : Field L₀ := fieldL₀
    Algebra K₀ L₀
  finiteDimensional :
    letI : Field K₀ := fieldK₀
    letI : Field L₀ := fieldL₀
    letI : Algebra K₀ L₀ := algebra
    FiniteDimensional K₀ L₀
  isGalois :
    letI : Field K₀ := fieldK₀
    letI : Field L₀ := fieldL₀
    letI : Algebra K₀ L₀ := algebra
    letI : FiniteDimensional K₀ L₀ := finiteDimensional
    IsGalois K₀ L₀
  valuativeRelK₀ : ValuativeRel K₀
  topologyK₀ : TopologicalSpace K₀
  localFieldK₀ :
    letI : Field K₀ := fieldK₀
    letI : ValuativeRel K₀ := valuativeRelK₀
    letI : TopologicalSpace K₀ := topologyK₀
    IsNonarchimedeanLocalField K₀
  valuativeRelL₀ : ValuativeRel L₀
  topologyL₀ : TopologicalSpace L₀
  localFieldL₀ :
    letI : Field L₀ := fieldL₀
    letI : ValuativeRel L₀ := valuativeRelL₀
    letI : TopologicalSpace L₀ := topologyL₀
    IsNonarchimedeanLocalField L₀
  valuativeExtension :
    letI : Field K₀ := fieldK₀
    letI : Field L₀ := fieldL₀
    letI : Algebra K₀ L₀ := algebra
    letI : ValuativeRel K₀ := valuativeRelK₀
    letI : TopologicalSpace K₀ := topologyK₀
    letI : IsNonarchimedeanLocalField K₀ := localFieldK₀
    letI : ValuativeRel L₀ := valuativeRelL₀
    letI : TopologicalSpace L₀ := topologyL₀
    letI : IsNonarchimedeanLocalField L₀ := localFieldL₀
    ValuativeExtension K₀ L₀
  continuousSMul :
    letI : Field K₀ := fieldK₀
    letI : Field L₀ := fieldL₀
    letI : Algebra K₀ L₀ := algebra
    letI : TopologicalSpace K₀ := topologyK₀
    letI : TopologicalSpace L₀ := topologyL₀
    ContinuousSMul K₀ L₀

namespace UniverseZeroLocalFieldModel

instance (B : UniverseZeroLocalFieldModel) : Field B.K₀ := B.fieldK₀
instance (B : UniverseZeroLocalFieldModel) : Field B.L₀ := B.fieldL₀
instance (B : UniverseZeroLocalFieldModel) : Algebra B.K₀ B.L₀ := B.algebra
instance (B : UniverseZeroLocalFieldModel) : FiniteDimensional B.K₀ B.L₀ :=
  B.finiteDimensional
instance (B : UniverseZeroLocalFieldModel) : IsGalois B.K₀ B.L₀ := B.isGalois
instance (B : UniverseZeroLocalFieldModel) : ValuativeRel B.K₀ := B.valuativeRelK₀
instance (B : UniverseZeroLocalFieldModel) : TopologicalSpace B.K₀ := B.topologyK₀
instance (B : UniverseZeroLocalFieldModel) : IsNonarchimedeanLocalField B.K₀ :=
  B.localFieldK₀
instance (B : UniverseZeroLocalFieldModel) : ValuativeRel B.L₀ := B.valuativeRelL₀
instance (B : UniverseZeroLocalFieldModel) : TopologicalSpace B.L₀ := B.topologyL₀
instance (B : UniverseZeroLocalFieldModel) : IsNonarchimedeanLocalField B.L₀ :=
  B.localFieldL₀
instance (B : UniverseZeroLocalFieldModel) : ValuativeExtension B.K₀ B.L₀ :=
  B.valuativeExtension
instance (B : UniverseZeroLocalFieldModel) : ContinuousSMul B.K₀ B.L₀ :=
  B.continuousSMul

end UniverseZeroLocalFieldModel

/-- Explicit bridge from a universe-polymorphic raw map to the normalized universe-zero Tate map.

The ring equivalences and their algebra equation identify the two field extensions.  The equations
on Galois generators and quotient representatives pin both vertical equivalences to actual
transport, rather than allowing them to absorb an inversion or character twist.  The valuation
equations preserve the `+1` orientation of the normalized local fundamental class.  Finally,
`raw_eq_normalizedFundamentalClass` is the required commuting-square *field*: it identifies the
transported raw map with `AbstractReciprocity.abstractReciprocity` instantiated at that class. -/
structure UniverseBridge
    (raw : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Units K ⧸ normSubgroup K L)) where
  model : UniverseZeroLocalFieldModel
  baseEquiv : K ≃+* model.K₀
  extensionEquiv : L ≃+* model.L₀
  algebra_compatibility : ∀ x : K,
    extensionEquiv (algebraMap K L x) = algebraMap model.K₀ model.L₀ (baseEquiv x)
  galoisTransport : (L ≃ₐ[K] L) ≃* (model.L₀ ≃ₐ[model.K₀] model.L₀)
  galoisTransport_apply : ∀ (σ : L ≃ₐ[K] L) (x : L),
    extensionEquiv (σ x) = galoisTransport σ (extensionEquiv x)
  abelianizationTransport :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Abelianization (model.L₀ ≃ₐ[model.K₀] model.L₀))
  abelianizationTransport_of : ∀ σ : L ≃ₐ[K] L,
    abelianizationTransport (Additive.ofMul (Abelianization.of σ)) =
      Additive.ofMul (Abelianization.of (galoisTransport σ))
  normQuotientTransport :
    Additive (Units K ⧸ normSubgroup K L) ≃+
      Additive (Units model.K₀ ⧸ normSubgroup model.K₀ model.L₀)
  normQuotientTransport_mk : ∀ x : Units K,
    normQuotientTransport (Additive.ofMul
      (QuotientGroup.mk x : Units K ⧸ normSubgroup K L)) =
        Additive.ofMul (QuotientGroup.mk (Units.map baseEquiv.toRingHom x) :
          Units model.K₀ ⧸ normSubgroup model.K₀ model.L₀)
  base_valuation : ∀ x : Units K,
    normalizedValuation model.K₀ (Units.map baseEquiv.toRingHom x) =
      normalizedValuation K x
  extension_valuation : ∀ x : Units L,
    normalizedValuation model.L₀ (Units.map extensionEquiv.toRingHom x) =
      normalizedValuation L x
  raw_eq_normalizedFundamentalClass :
    raw.trans normQuotientTransport =
      abelianizationTransport.trans
        (normalizedFundamentalClassRawNormTateEquiv model.K₀ model.L₀)

/-- Universe-polymorphic finite Tate construction, pinned through an explicit universe bridge.

Unlike the rejected pair of freely chosen equivalences, `universeBridge` makes the raw map equal,
after actual field transport, to the abstract reciprocity map attached to the normalized local
fundamental class. -/
structure Construction where
  /-- The raw Tate map, whose bar-generator formula has the negative row-sum sign. -/
  rawNormTateEquiv : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
    Additive (Units K ⧸ normSubgroup K L)
  /-- The compensated Tate map. -/
  compensatedNormTateEquiv : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
    Additive (Units K ⧸ normSubgroup K L)
  /-- Defining sign equation: compensation is literal postcomposition by negation. -/
  compensation : compensatedNormTateEquiv =
    rawNormTateEquiv.trans (AddEquiv.neg (Additive (Units K ⧸ normSubgroup K L)))
  /-- Defining normalization equation, including the universe transport used by the public map. -/
  universeBridge : UniverseBridge K L rawNormTateEquiv

section UniverseModelConstruction

open scoped Topology
open Set Filter

private theorem localField_small
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Small.{0} K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  let π := (defaultUniformizer K).val
  let C : ℕ → Set K := fun n =>
    (fun a : RingOfIntegers K => (((π ^ n)⁻¹ : Units K) : K) * (a : K)) '' univ
  have hCcompact : ∀ n, IsCompact (C n) := by
    intro n
    exact isCompact_univ.image (continuous_const.mul continuous_subtype_val)
  have hCcover : ⋃ n, C n = univ := by
    rw [eq_univ_iff_forall]
    intro x
    by_cases hx : x = 0
    · subst x
      exact mem_iUnion.2 ⟨0, ⟨0, trivial, by simp⟩⟩
    · let xu : Units K := Units.mk0 x hx
      let n := (normalizedValuation K xu).natAbs
      have hn : 0 ≤ (n : ℤ) + normalizedValuation K xu := by
        have h := Int.le_natAbs (a := -normalizedValuation K xu)
        rw [Int.natAbs_neg] at h
        omega
      have hπn : normalizedValuation K (π ^ n) = (n : ℤ) := by
        calc
          normalizedValuation K (π ^ n) =
              (n : ℤ) * normalizedValuation K π := by simp [normalizedValuation]
          _ = (n : ℤ) := by
            rw [show normalizedValuation K π = 1 from
              (defaultUniformizer K).valuation_eq_one]
            simp
      have hint : 0 ≤ normalizedValuation K (π ^ n * xu) := by
        rw [normalizedValuation_mul, hπn]
        exact hn
      obtain ⟨a, ha⟩ :=
        ((exists_normalizedValuationHom K).choose_spec.2 (π ^ n * xu)).1 hint
      exact mem_iUnion.2 ⟨n, ⟨a, trivial, by
        change (((π ^ n)⁻¹ : Units K) : K) * (a : K) = x
        rw [ha]
        simp [xu]⟩⟩
  letI : SigmaCompactSpace K := isSigmaCompact_univ_iff.mp ⟨C, hCcompact, hCcover⟩
  letI : SecondCountableTopology K := EMetric.secondCountable_of_sigmaCompact K
  obtain ⟨S, -, hS⟩ := exists_seq_separating K isOpen_empty univ
  let f : K → Set ℕ := fun x => {n | x ∈ S n}
  apply small_of_injective (f := f)
  intro x y hxy
  exact hS x trivial y trivial fun n => Set.ext_iff.mp hxy n

@[reducible] private def transportVR {A B : Type*} [Field A] [Field B] [ValuativeRel B]
    (e : A ≃+* B) : ValuativeRel A where
  vle x y := e x ≤ᵥ e y
  vle_total x y := ValuativeRel.vle_total (e x) (e y)
  vle_trans hxy hyz := ValuativeRel.vle_trans hxy hyz
  vle_add hx hy := by simpa using ValuativeRel.vle_add hx hy
  mul_vle_mul_left h z := by simpa using ValuativeRel.mul_vle_mul_left h (e z)
  vle_mul_cancel {x y z} h hxy := by
    exact ValuativeRel.vle_mul_cancel (x := e x) (y := e y) (z := e z)
      (by simpa using h) (by simpa using hxy)
  not_vle_one_zero := by simpa using (ValuativeRel.not_vle_one_zero (R := B))
  vle_mul_comm := by simp [ValuativeRel.vle_mul_comm]

private theorem shrink_local
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : Small.{0} K := localField_small K
    let A := Shrink.{0} K
    letI : Field A := inferInstance
    let e : A ≃+* K := Shrink.ringEquiv K
    letI : ValuativeRel A := transportVR e
    letI : TopologicalSpace A := e.toEquiv.topologicalSpace
    IsNonarchimedeanLocalField A := by
  letI : Small.{0} K := localField_small K
  let A := Shrink.{0} K
  letI : Field A := inferInstance
  let e : A ≃+* K := Shrink.ringEquiv K
  letI : ValuativeRel A := transportVR e
  letI : TopologicalSpace A := e.toEquiv.topologicalSpace
  let h : A ≃ₜ K := e.toEquiv.homeomorph
  have he : Continuous e := continuous_induced_dom
  haveI : ContinuousAdd A := ⟨by
    apply (continuous_induced_rng (f := e)).2
    rw [show (e ∘ fun p : A × A => p.1 + p.2) =
        fun p => e p.1 + e p.2 by
      funext p
      exact e.map_add _ _]
    exact (he.comp continuous_fst).add (he.comp continuous_snd)⟩
  haveI : ContinuousNeg A := ⟨by
    apply (continuous_induced_rng (f := e)).2
    rw [show (e ∘ fun a : A => -a) = fun a => -e a by
      funext a
      exact e.map_neg a]
    exact he.neg⟩
  haveI : IsTopologicalAddGroup A := ⟨⟩
  have hlocal : LocallyCompactSpace A := h.isClosedEmbedding.locallyCompactSpace
  let w : Valuation A (ValuativeRel.ValueGroupWithZero K) :=
    (ValuativeRel.valuation K).comap e.toRingHom
  haveI hw : w.Compatible := by
    constructor
    intro x y
    change e x ≤ᵥ e y ↔ ValuativeRel.valuation K (e x) ≤ ValuativeRel.valuation K (e y)
    exact Valuation.Compatible.vle_iff_le _ _
  have hntriv : ValuativeRel.IsNontrivial A := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial w]
    obtain ⟨x, hx0, hx1⟩ :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (ValuativeRel.valuation K)).mp inferInstance
    obtain ⟨y, rfl⟩ := e.surjective x
    exact ⟨y, hx0, hx1⟩
  have htop : IsValuativeTopology A := by
    apply IsValuativeTopology.of_mem_nhds_zero_iff_vle w
    intro s
    -- transport the valuation-neighborhood criterion across e
    have heh : (h : A → K) = e := rfl
    rw [show s ∈ 𝓝 (0 : A) ↔ e '' s ∈ 𝓝 (0 : K) by
      have hz : h (0 : A) = (0 : K) := by rw [heh]; exact e.map_zero
      rw [← heh]
      simpa only [hz] using
        (h.isOpenEmbedding.image_mem_nhds (s := s) (x := (0 : A))).symm]
    rw [(ValuativeRel.valuation K).mem_nhds_zero_iff]
    let fw := MonoidWithZeroHom.ofClass w
    let fv := MonoidWithZeroHom.ofClass (ValuativeRel.valuation K)
    have hfw (z : A) : fw z = fv (e z) := rfl
    have hembed (z : A) :
        MonoidWithZeroHom.ValueGroup₀.embedding
            (MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z) =
          MonoidWithZeroHom.ValueGroup₀.embedding
            (MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z)) := by
      rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀,
        MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀, hfw]
    dsimp only [Valuation.restrict]
    constructor
    · rintro ⟨γ, hγ⟩
      obtain ⟨x, hx⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective fv γ.val
      obtain ⟨z₀, rfl⟩ := e.surjective x
      have hδ : MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z₀ ≠ 0 := by
        intro hz
        have hz' : fw z₀ = 0 :=
          MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.mp hz
        rw [hfw] at hz'
        have hz'' : MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z₀) = 0 :=
          MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.mpr hz'
        rw [hx] at hz''
        exact γ.ne_zero hz''
      let δ := Units.mk0 (MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z₀) hδ
      refine ⟨δ, ?_⟩
      intro z hz
      have hz' :=
        (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := fw)).lt_iff_lt.mpr hz
      change MonoidWithZeroHom.ValueGroup₀.embedding
          (MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z) <
        MonoidWithZeroHom.ValueGroup₀.embedding
          (MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z₀) at hz'
      rw [hembed z, hembed z₀, hx] at hz'
      have hz'' :=
        (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := fv)).lt_iff_lt.mp hz'
      exact e.injective.mem_set_image.mp (hγ hz'')
    · rintro ⟨γ, hγ⟩
      obtain ⟨z₀, hz₀⟩ :=
        MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective fw γ.val
      have hδ : MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z₀) ≠ 0 := by
        intro hz
        have hz' : fv (e z₀) = 0 :=
          MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.mp hz
        rw [← hfw] at hz'
        have hz'' : MonoidWithZeroHom.ValueGroup₀.restrict₀ fw z₀ = 0 :=
          MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.mpr hz'
        rw [hz₀] at hz''
        exact γ.ne_zero hz''
      let δ := Units.mk0 (MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z₀)) hδ
      refine ⟨δ, ?_⟩
      intro x hx
      obtain ⟨z, rfl⟩ := e.surjective x
      have hx' :=
        (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := fv)).lt_iff_lt.mpr hx
      change MonoidWithZeroHom.ValueGroup₀.embedding
          (MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z)) <
        MonoidWithZeroHom.ValueGroup₀.embedding
          (MonoidWithZeroHom.ValueGroup₀.restrict₀ fv (e z₀)) at hx'
      rw [← hembed z, ← hembed z₀, hz₀] at hx'
      have hx'' :=
        (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := fw)).lt_iff_lt.mp hx'
      exact ⟨z, hγ hx'', rfl⟩
  exact { toIsValuativeTopology := htop
          toLocallyCompactSpace := hlocal
          toIsNontrivial := hntriv }

private theorem int_addHom_eq_of_surjective_nonneg_iff
    {G : Type*} [AddGroup G] (f g : G →+ ℤ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h_nonneg : ∀ x, 0 ≤ f x ↔ 0 ≤ g x) : f = g := by
  have h_zero (x : G) : f x = 0 ↔ g x = 0 := by
    constructor
    · intro hx
      have h₁ : 0 ≤ g x := (h_nonneg x).mp (by omega)
      have h₂ : 0 ≤ g (-x) := (h_nonneg (-x)).mp (by simp [hx])
      rw [map_neg] at h₂
      omega
    · intro hx
      have h₁ : 0 ≤ f x := (h_nonneg x).mpr (by omega)
      have h₂ : 0 ≤ f (-x) := (h_nonneg (-x)).mpr (by simp [hx])
      rw [map_neg] at h₂
      omega
  obtain ⟨a, ha⟩ := hf 1
  obtain ⟨b, hb⟩ := hg 1
  have hga_nonneg : 0 ≤ g a := (h_nonneg a).mp (by omega)
  have hga_ne : g a ≠ 0 := by
    intro hga
    exact one_ne_zero (ha ▸ (h_zero a).mpr hga)
  have hfb_nonneg : 0 ≤ f b := (h_nonneg b).mpr (by omega)
  have hfb_ne : f b ≠ 0 := by
    intro hfb
    exact one_ne_zero (hb ▸ (h_zero b).mp hfb)
  have hab_g : g (a - (g a) • b) = 0 := by simp [hb]
  have hab_f : f (a - (g a) • b) = 0 := (h_zero _).mpr hab_g
  have hga_ge : 1 ≤ g a := by omega
  have hfb_ge : 1 ≤ f b := by omega
  have hga : g a = 1 := by
    simp [ha] at hab_f
    nlinarith
  apply AddMonoidHom.ext
  intro x
  have hx_f : f (x - (f x) • a) = 0 := by simp [ha]
  have hx_g : g (x - (f x) • a) = 0 := (h_zero _).mp hx_f
  simp [hga] at hx_g
  omega

private theorem normalizedValuation_ringEquiv
    {A : Type*} {K : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (e : A ≃+* K) (hrel : ∀ x y : A, (x ≤ᵥ y) ↔ (e x ≤ᵥ e y))
    (x : Units K) :
    normalizedValuation A (Units.map e.symm.toMonoidHom x) = normalizedValuation K x := by
  let f : Additive (Units K) →+ ℤ :=
    { toFun := fun x => normalizedValuation A
        (Units.map e.symm.toMonoidHom (Additive.toMul x))
      map_zero' := by simp [normalizedValuation]
      map_add' := by
        intro x y
        change normalizedValuation A
            (Units.map e.symm.toMonoidHom (Additive.toMul x * Additive.toMul y)) = _
        rw [map_mul, normalizedValuation_mul] }
  let g : Additive (Units K) →+ ℤ :=
    { toFun := fun x => normalizedValuation K (Additive.toMul x)
      map_zero' := by simp [normalizedValuation]
      map_add' := by
        intro x y
        exact normalizedValuation_mul K _ _ }
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom A).choose_spec.1 z
    refine ⟨Additive.ofMul (Units.map e.toMonoidHom a), ?_⟩
    change normalizedValuation A
      (Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom a)) = z
    have hmap : Units.map e.symm.toMonoidHom (Units.map e.toMonoidHom a) = a := by
      ext
      simp
    rw [hmap]
    exact ha
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom K).choose_spec.1 z
    exact ⟨Additive.ofMul a, ha⟩
  have hnonneg : ∀ y, 0 ≤ f y ↔ 0 ≤ g y := by
    intro y
    change 0 ≤ normalizedValuation A
        (Units.map e.symm.toMonoidHom (Additive.toMul y)) ↔
      0 ≤ normalizedValuation K (Additive.toMul y)
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := ((exists_normalizedValuationHom A).choose_spec.2
        (Units.map e.symm.toMonoidHom (Additive.toMul y))).1 hy
      apply ((exists_normalizedValuationHom K).choose_spec.2 (Additive.toMul y)).2
      refine ⟨⟨e a, ?_⟩, ?_⟩
      · have ha_prop := a.property
        change ValuativeRel.valuation A (a : A) ≤ 1 at ha_prop
        have ha_int : (a : A) ≤ᵥ 1 :=
          (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mpr ha_prop
        have hai := (hrel (a : A) 1).mp ha_int
        change ValuativeRel.valuation K (e (a : A)) ≤ 1
        exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) _ _).mp
          (by simpa using hai)
      · simpa using congrArg e ha
    · intro hy
      obtain ⟨a, ha⟩ := ((exists_normalizedValuationHom K).choose_spec.2
        (Additive.toMul y)).1 hy
      apply ((exists_normalizedValuationHom A).choose_spec.2
        (Units.map e.symm.toMonoidHom (Additive.toMul y))).2
      refine ⟨⟨e.symm a, ?_⟩, ?_⟩
      · have ha_prop := a.property
        change ValuativeRel.valuation K (a : K) ≤ 1 at ha_prop
        have ha_int : (a : K) ≤ᵥ 1 :=
          (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) _ _).mpr ha_prop
        have hai : (e.symm (a : K)) ≤ᵥ 1 :=
          (hrel _ _).mpr (by simpa using ha_int)
        change ValuativeRel.valuation A (e.symm (a : K)) ≤ 1
        exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) _ _).mp hai
      · simpa using congrArg e.symm ha
  have hfg := int_addHom_eq_of_surjective_nonneg_iff f g hf hg hnonneg
  exact DFunLike.congr_fun hfg (Additive.ofMul x)

private def transportAlgEquiv
    {K : Type*} {L : Type*} {K₀ : Type*} {L₀ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (b : K ≃+* K₀) (e : L ≃+* L₀)
    (h : ∀ x : K, e (algebraMap K L x) = algebraMap K₀ L₀ (b x))
    (σ : L ≃ₐ[K] L) : L₀ ≃ₐ[K₀] L₀ where
  toFun x := e (σ (e.symm x))
  invFun x := e (σ.symm (e.symm x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_mul' x y := by simp
  commutes' x := by
    have hpre : e.symm (algebraMap K₀ L₀ x) = algebraMap K L (b.symm x) := by
      apply e.injective
      simpa using (h (b.symm x)).symm
    rw [hpre, σ.commutes]
    simpa using h (b.symm x)

private def galoisTransportEquiv
    {K : Type*} {L : Type*} {K₀ : Type*} {L₀ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (b : K ≃+* K₀) (e : L ≃+* L₀)
    (h : ∀ x : K, e (algebraMap K L x) = algebraMap K₀ L₀ (b x)) :
    (L ≃ₐ[K] L) ≃* (L₀ ≃ₐ[K₀] L₀) where
  toFun := transportAlgEquiv b e h
  invFun := transportAlgEquiv b.symm e.symm (fun x => by
    apply e.injective
    simpa using (h (b.symm x)).symm)
  left_inv σ := by
    ext x
    simp [transportAlgEquiv]
  right_inv σ := by
    ext x
    simp [transportAlgEquiv]
  map_mul' σ τ := by
    ext x
    simp [transportAlgEquiv]

private noncomputable def normQuotientTransportEquiv
    {K : Type*} {L : Type*} {K₀ : Type*} {L₀ : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀] [FiniteDimensional K₀ L₀]
    (b : K ≃+* K₀) (e : L ≃+* L₀)
    (h : ∀ x : K, e (algebraMap K L x) = algebraMap K₀ L₀ (b x)) :
    Units K ⧸ normSubgroup K L ≃* Units K₀ ⧸ normSubgroup K₀ L₀ := by
  let ub : Units K ≃* Units K₀ := Units.mapEquiv b.toMulEquiv
  have hcomp : (algebraMap K₀ L₀).comp b.toRingHom =
      e.toRingHom.comp (algebraMap K L) := by
    ext x
    exact (h x).symm
  have hnorm (y : Units L) :
      ub (normUnitsHom K L y) =
        normUnitsHom K₀ L₀ (Units.map e.toMonoidHom y) := by
    apply Units.ext
    change b (Algebra.norm K (y : L)) = Algebra.norm K₀ (e (y : L))
    have hn := Algebra.norm_eq_of_equiv_equiv b e hcomp (y : L)
    simpa using congrArg b hn
  have hmem (x : Units K) :
      x ∈ normSubgroup K L ↔ ub x ∈ normSubgroup K₀ L₀ := by
    rw [mem_normSubgroup_iff, mem_normSubgroup_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Units.map e.toMonoidHom y, hnorm y |>.symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨Units.map e.symm.toMonoidHom y, ?_⟩
      apply ub.injective
      rw [hnorm]
      have hmap : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom y) = y := by
        ext
        simp
      rw [hmap]
      exact hy
  have hf : normSubgroup K L ≤
      Subgroup.comap ub.toMonoidHom (normSubgroup K₀ L₀) := fun x hx => (hmem x).mp hx
  have hb : normSubgroup K₀ L₀ ≤
      Subgroup.comap ub.symm.toMonoidHom (normSubgroup K L) := by
    intro x hx
    exact (hmem (ub.symm x)).mpr (by simpa using hx)
  let qf := QuotientGroup.map (normSubgroup K L) (normSubgroup K₀ L₀)
    ub.toMonoidHom hf
  let qb := QuotientGroup.map (normSubgroup K₀ L₀) (normSubgroup K L)
    ub.symm.toMonoidHom hb
  exact
    { toFun := qf
      invFun := qb
      left_inv := by
        rintro ⟨x⟩
        simp [qf, qb]
      right_inv := by
        rintro ⟨x⟩
        simp [qf, qb]
      map_mul' := qf.map_mul }

@[simp] private theorem normQuotientTransportEquiv_mk
    {K : Type*} {L : Type*} {K₀ : Type*} {L₀ : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀] [FiniteDimensional K₀ L₀]
    (b : K ≃+* K₀) (e : L ≃+* L₀)
    (h : ∀ x : K, e (algebraMap K L x) = algebraMap K₀ L₀ (b x))
    (x : Units K) :
    normQuotientTransportEquiv b e h (QuotientGroup.mk x) =
      QuotientGroup.mk (Units.map b.toRingHom x) := by
  change QuotientGroup.mk ((Units.mapEquiv b.toMulEquiv) x) = _
  congr 1

@[simp] private theorem galoisTransportEquiv_apply
    {K : Type*} {L : Type*} {K₀ : Type*} {L₀ : Type*}
    [Field K] [Field L] [Algebra K L]
    [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (b : K ≃+* K₀) (e : L ≃+* L₀)
    (h : ∀ x : K, e (algebraMap K L x) = algebraMap K₀ L₀ (b x))
    (σ : L ≃ₐ[K] L) (x : L) :
    galoisTransportEquiv b e h σ (e x) = e (σ x) := by
  simp [galoisTransportEquiv, transportAlgEquiv]

private structure UniverseModelData
    (K : Type u) (L : Type*)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L] where
  model : FiniteReciprocity.UniverseZeroLocalFieldModel
  baseEquiv : K ≃+* model.K₀
  extensionEquiv : L ≃+* model.L₀
  algebra_compatibility : ∀ x : K,
    extensionEquiv (algebraMap K L x) = algebraMap model.K₀ model.L₀ (baseEquiv x)
  base_valuation : ∀ x : Units K,
    normalizedValuation model.K₀ (Units.map baseEquiv.toRingHom x) =
      normalizedValuation K x
  extension_valuation : ∀ x : Units L,
    normalizedValuation model.L₀ (Units.map extensionEquiv.toRingHom x) =
      normalizedValuation L x

private noncomputable def universeModel
    {K : Type u} {L : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L] :
    UniverseModelData K L := by
  letI : Small.{0} K := localField_small K
  letI : Small.{0} L := localField_small L
  let K₀ := Shrink.{0} K
  let L₀ := Shrink.{0} L
  letI fieldK₀ : Field K₀ := inferInstance
  letI fieldL₀ : Field L₀ := inferInstance
  let eK : K₀ ≃+* K := Shrink.ringEquiv K
  let eL : L₀ ≃+* L := Shrink.ringEquiv L
  letI valuativeRelK₀ : ValuativeRel K₀ := transportVR eK
  letI valuativeRelL₀ : ValuativeRel L₀ := transportVR eL
  letI topologyK₀ : TopologicalSpace K₀ := eK.toEquiv.topologicalSpace
  letI topologyL₀ : TopologicalSpace L₀ := eL.toEquiv.topologicalSpace
  let localFieldK₀ : IsNonarchimedeanLocalField K₀ := shrink_local K
  let localFieldL₀ : IsNonarchimedeanLocalField L₀ := shrink_local L
  letI : IsNonarchimedeanLocalField K₀ := localFieldK₀
  letI : IsNonarchimedeanLocalField L₀ := localFieldL₀
  let algHom : K₀ →+* L₀ := eL.symm.toRingHom.comp
    ((algebraMap K L).comp eK.toRingHom)
  let algebraK₀L₀ : Algebra K₀ L₀ := algHom.toAlgebra
  letI : Algebra K₀ L₀ := algebraK₀L₀
  have hcomp : (algebraMap K₀ L₀).comp eK.symm.toRingHom =
      eL.symm.toRingHom.comp (algebraMap K L) := by
    rw [RingHom.algebraMap_toAlgebra algHom]
    ext x
    simp [algHom]
  let sem : L →ₛₗ[eK.symm.toRingHom] L₀ :=
    { toFun := eL.symm
      map_add' := eL.symm.map_add
      map_smul' := by
        intro c x
        simp only [Algebra.smul_def]
        rw [map_mul]
        congr 1
        exact DFunLike.congr_fun hcomp c |>.symm }
  letI : RingHomSurjective eK.symm.toRingHom := ⟨eK.symm.surjective⟩
  let finiteDimensionalK₀L₀ : FiniteDimensional K₀ L₀ :=
    Module.Finite.of_surjective sem eL.symm.surjective
  let isGaloisK₀L₀ : IsGalois K₀ L₀ :=
    IsGalois.of_equiv_equiv (F := K) (E := L) (M := K₀) (N := L₀)
      (f := eK.symm) (g := eL.symm) hcomp
  let valuativeExtensionK₀L₀ : ValuativeExtension K₀ L₀ := by
    constructor
    intro a b
    change eL (algebraMap K₀ L₀ a) ≤ᵥ eL (algebraMap K₀ L₀ b) ↔
      eK a ≤ᵥ eK b
    rw [RingHom.algebraMap_toAlgebra algHom]
    simpa [algHom] using
      (ValuativeExtension.vle_iff_vle (A := K) (B := L) (a := eK a) (b := eK b))
  have heK : Continuous eK := continuous_induced_dom
  have heL : Continuous eL := continuous_induced_dom
  let continuousSMulK₀L₀ : ContinuousSMul K₀ L₀ := ⟨by
    apply (continuous_induced_rng (f := eL)).2
    rw [show (eL ∘ fun p : K₀ × L₀ => p.1 • p.2) =
        fun p => eK p.1 • eL p.2 by
      funext p
      simp only [Function.comp_apply, Algebra.smul_def]
      rw [map_mul, RingHom.algebraMap_toAlgebra algHom]
      simp [algHom]]
    exact (heK.comp continuous_fst).smul (heL.comp continuous_snd)⟩
  let model : FiniteReciprocity.UniverseZeroLocalFieldModel :=
    { K₀ := K₀
      L₀ := L₀
      fieldK₀ := fieldK₀
      fieldL₀ := fieldL₀
      algebra := algebraK₀L₀
      finiteDimensional := finiteDimensionalK₀L₀
      isGalois := isGaloisK₀L₀
      valuativeRelK₀ := valuativeRelK₀
      topologyK₀ := topologyK₀
      localFieldK₀ := localFieldK₀
      valuativeRelL₀ := valuativeRelL₀
      topologyL₀ := topologyL₀
      localFieldL₀ := localFieldL₀
      valuativeExtension := valuativeExtensionK₀L₀
      continuousSMul := continuousSMulK₀L₀ }
  have hcompat : ∀ x : K,
      eL.symm (algebraMap K L x) = algebraMap K₀ L₀ (eK.symm x) := by
    intro x
    exact (DFunLike.congr_fun hcomp x).symm
  have hbval : ∀ x : Units K,
      normalizedValuation K₀ (Units.map eK.symm.toRingHom x) =
        normalizedValuation K x := by
    intro x
    exact normalizedValuation_ringEquiv eK (fun _ _ => Iff.rfl) x
  have heval : ∀ x : Units L,
      normalizedValuation L₀ (Units.map eL.symm.toRingHom x) =
        normalizedValuation L x := by
    intro x
    exact normalizedValuation_ringEquiv eL (fun _ _ => Iff.rfl) x
  exact
    { model := model
      baseEquiv := eK.symm
      extensionEquiv := eL.symm
      algebra_compatibility := hcompat
      base_valuation := hbval
      extension_valuation := heval }

end UniverseModelConstruction

/-- Construction of the universe-polymorphic finite Tate package. -/
theorem construction_exists : Nonempty (Construction K L) := by
  let data := universeModel (K := K) (L := L)
  let model := data.model
  let b : K ≃+* model.K₀ := data.baseEquiv
  let e : L ≃+* model.L₀ := data.extensionEquiv
  have hcompat : ∀ x : K,
      e (algebraMap K L x) = algebraMap model.K₀ model.L₀ (b x) :=
    data.algebra_compatibility
  let gt := galoisTransportEquiv b e hcompat
  let abT : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Abelianization (model.L₀ ≃ₐ[model.K₀] model.L₀)) :=
    gt.abelianizationCongr.toAdditive
  let nt : Additive (Units K ⧸ normSubgroup K L) ≃+
      Additive (Units model.K₀ ⧸ normSubgroup model.K₀ model.L₀) :=
    (normQuotientTransportEquiv b e hcompat).toAdditive
  let normalized :=
    normalizedFundamentalClassRawNormTateEquiv model.K₀ model.L₀
  let raw : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Units K ⧸ normSubgroup K L) :=
    (abT.trans normalized).trans nt.symm
  have hbval : ∀ x : Units K,
      normalizedValuation model.K₀ (Units.map b.toRingHom x) =
        normalizedValuation K x := data.base_valuation
  have heval : ∀ x : Units L,
      normalizedValuation model.L₀ (Units.map e.toRingHom x) =
        normalizedValuation L x := data.extension_valuation
  refine ⟨
    { rawNormTateEquiv := raw
      compensatedNormTateEquiv :=
        raw.trans (AddEquiv.neg (Additive (Units K ⧸ normSubgroup K L)))
      compensation := rfl
      universeBridge :=
        { model := model
          baseEquiv := b
          extensionEquiv := e
          algebra_compatibility := hcompat
          galoisTransport := gt
          galoisTransport_apply := fun σ x =>
            (galoisTransportEquiv_apply b e hcompat σ x).symm
          abelianizationTransport := abT
          abelianizationTransport_of := fun σ => by
            rfl
          normQuotientTransport := nt
          normQuotientTransport_mk := fun x => by
            exact normQuotientTransportEquiv_mk b e hcompat x
          base_valuation := hbval
          extension_valuation := heval
          raw_eq_normalizedFundamentalClass := by
            ext z
            simp [raw, normalized] } }⟩

/-- The selected finite Tate package; all public uses retain both defining equations. -/
noncomputable def construction : Construction K L :=
  (construction_exists K L).some

/-- The raw finite Tate map before Deviation 15's sign correction. -/
noncomputable def rawNormTateEquiv :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Units K ⧸ normSubgroup K L) :=
  (construction K L).rawNormTateEquiv

/-- The compensated finite Tate map. -/
noncomputable def compensatedNormTateEquiv :
    Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Units K ⧸ normSubgroup K L) :=
  (construction K L).compensatedNormTateEquiv

/-- Public defining equation displaying the compensating negation. -/
theorem compensatedNormTateEquiv_def :
    compensatedNormTateEquiv K L =
      (rawNormTateEquiv K L).trans
        (AddEquiv.neg (Additive (Units K ⧸ normSubgroup K L))) :=
  (construction K L).compensation

/-- Public defining equation transporting the raw map to abstract reciprocity for the normalized
local fundamental class. -/
theorem rawNormTateEquiv_universeBridge :
    let B := (construction K L).universeBridge
    (rawNormTateEquiv K L).trans B.normQuotientTransport =
      B.abelianizationTransport.trans
        (normalizedFundamentalClassRawNormTateEquiv B.model.K₀ B.model.L₀) :=
  (construction K L).universeBridge.raw_eq_normalizedFundamentalClass

/-- Finite reciprocity for a finite Galois scalar extension: definitionally the inverse of the
compensated Tate equivalence. -/
noncomputable def artin :
    (Units K ⧸ normSubgroup K L) ≃* Abelianization (L ≃ₐ[K] L) :=
  MulEquiv.toAdditive.symm (compensatedNormTateEquiv K L).symm

/-- Defining equation for finite reciprocity: the inverse direction is explicit. -/
theorem artin_defining_equation :
    MulEquiv.toAdditive (artin K L) = (compensatedNormTateEquiv K L).symm := by
  rfl

private theorem normalizedValuation_le_iff_bridge
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x y : Units F) :
    normalizedValuation F x ≤ normalizedValuation F y ↔
      ValuativeRel.valuation F (y : F) ≤ ValuativeRel.valuation F (x : F) := by
  have hnonneg : 0 ≤ normalizedValuation F (y * x⁻¹) ↔
      ValuativeRel.valuation F ((y * x⁻¹ : Units F) : F) ≤ 1 := by
    unfold normalizedValuation normalizedValuationHom
    rw [(exists_normalizedValuationHom F).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  have hone : normalizedValuation F (1 : Units F) = 0 := by
    simp [normalizedValuation]
  have hinv : normalizedValuation F x⁻¹ = -normalizedValuation F x := by
    have h := normalizedValuation_mul F x x⁻¹
    simp only [mul_inv_cancel, hone] at h
    omega
  rw [normalizedValuation_mul, hinv] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation F y - normalizedValuation F x ↔
      ValuativeRel.valuation F ((y * x⁻¹ : Units F) : F) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change ValuativeRel.valuation F (y : F) /
      ValuativeRel.valuation F (x : F) ≤ 1 ↔ _
  rw [div_le_one₀ ((ValuativeRel.valuation F).pos_iff.mpr x.ne_zero)]

private theorem valuativeExtension_of_normalizedValuation_ringEquiv
    {A B : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    (e : A ≃+* B)
    (hval : ∀ x : Units A,
      normalizedValuation B (Units.map e.toRingHom x) = normalizedValuation A x) :
    letI : Algebra A B := e.toRingHom.toAlgebra
    ValuativeExtension A B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  constructor
  intro a b
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp [ha]
  let au : Units A := Units.mk0 a ha
  let bu : Units A := Units.mk0 b hb
  let eau : Units B := Units.map e.toRingHom au
  let ebu : Units B := Units.map e.toRingHom bu
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B),
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A)]
  change ValuativeRel.valuation B (e a) ≤ ValuativeRel.valuation B (e b) ↔
    ValuativeRel.valuation A a ≤ ValuativeRel.valuation A b
  change ValuativeRel.valuation B (eau : B) ≤ ValuativeRel.valuation B (ebu : B) ↔
    ValuativeRel.valuation A (au : A) ≤ ValuativeRel.valuation A (bu : A)
  rw [← normalizedValuation_le_iff_bridge B ebu eau,
    ← normalizedValuation_le_iff_bridge A bu au, hval, hval]

private theorem ringEquiv_continuous_of_valuativeExtension
    {A B : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Algebra A B] [ValuativeExtension A B]
    (e : A ≃+* B) (halg : ∀ x : A, algebraMap A B x = e x) : Continuous e := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  rw [IsValuativeTopology.mem_nhds_iff'] at hs ⊢
  obtain ⟨γ, hγ⟩ := hs
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ.val
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz : ValuativeRel.valuation A z ≠ 0 := by
    intro hz
    have h := congrArg (ValuativeExtension.mapValueGroupWithZero A B) hz
    rw [map_zero, ValuativeExtension.mapValueGroupWithZero_valuation, halg, hy] at h
    exact γ.ne_zero h
  refine ⟨Units.mk0 (ValuativeRel.valuation A z) hz, ?_⟩
  intro w hw
  apply hγ
  change ValuativeRel.valuation B (e w - e x) < γ.val
  rw [← map_sub, ← halg, ← ValuativeExtension.mapValueGroupWithZero_valuation]
  have hmapz : ValuativeExtension.mapValueGroupWithZero A B
      (ValuativeRel.valuation A z) = γ.val := by
    rw [ValuativeExtension.mapValueGroupWithZero_valuation, halg, hy]
  rw [← hmapz]
  exact ValuativeExtension.mapValueGroupWithZero_strictMono hw

set_option maxHeartbeats 800000 in
private theorem finiteReciprocity_transportedC2_mem
    {G H : Type} [Group G] [Group H] {M : Rep ℤ G} {N : Rep ℤ H}
    (f : H →* G) (φ : Rep.res f M ⟶ N)
    (a : Inhomogeneous.C2 M) (ha : AbstractReciprocity.IsNormalizedCocycle2 M a) :
    AbstractReciprocity.IsNormalizedCocycle2 N (transportedC2 f φ a) := by
  constructor
  · change Inhomogeneous.d2 N (transportedC2 f φ a) = 0
    ext x y z
    change N.ρ x (φ.hom (a (f y) (f z))) - φ.hom (a (f (x * y)) (f z)) +
      φ.hom (a (f x) (f (y * z))) - φ.hom (a (f x) (f y)) = 0
    rw [← Rep.hom_comm_apply]
    have h := congrFun (congrFun (congrFun ha.1 (f x)) (f y)) (f z)
    change M.ρ (f x) (a (f y) (f z)) - a (f x * f y) (f z) +
      a (f x) (f y * f z) - a (f x) (f y) = 0 at h
    rw [map_mul, map_mul]
    rw [← map_sub, ← map_add, ← map_sub]
    change φ.hom (M.ρ (f x) (a (f y) (f z)) - a (f x * f y) (f z) +
      a (f x) (f y * f z) - a (f x) (f y)) = 0
    rw [h, map_zero]
  · constructor
    · intro x
      change φ.hom (a (f 1) (f x)) = 0
      rw [map_one, ha.2.1, map_zero]
    · intro x
      change φ.hom (a (f x) (f 1)) = 0
      rw [map_one, ha.2.2, map_zero]

set_option maxHeartbeats 800000 in
private theorem finiteReciprocity_transportedH2_cocycleClass_eq
    {G H : Type} [Group G] [Group H] {M : Rep ℤ G} {N : Rep ℤ H}
    (f : H →* G) (φ : Rep.res f M ⟶ N)
    (a : Inhomogeneous.C2 M) (ha : AbstractReciprocity.IsNormalizedCocycle2 M a) :
    transportedH2 f φ (AbstractReciprocity.cocycleClass2 M a ha) =
      AbstractReciprocity.cocycleClass2 N (transportedC2 f φ a)
        (finiteReciprocity_transportedC2_mem f φ a ha) := by
  apply (comparisonH2 N).injective
  simp [transportedH2]
  change groupCohomology.map f φ 2 (groupCohomology.H2π M _) =
    groupCohomology.H2π N _
  rw [groupCohomology.H2π_comp_map_apply]
  rfl

set_option maxHeartbeats 800000 in
private theorem finiteReciprocity_cohomologous2_of_cocycleClass_eq
    {G : Type} [Group G] (M : Rep ℤ G)
    (a b : Inhomogeneous.C2 M)
    (ha : AbstractReciprocity.IsNormalizedCocycle2 M a)
    (hb : AbstractReciprocity.IsNormalizedCocycle2 M b)
    (h : AbstractReciprocity.cocycleClass2 M a ha =
      AbstractReciprocity.cocycleClass2 M b hb) :
    AbstractReciprocity.Cohomologous2 M a b := by
  have hm : (⟨b, hb⟩ : Inhomogeneous.cocycles2 M) - ⟨a, ha⟩ ∈
      Inhomogeneous.coboundaries2 M := QuotientAddGroup.eq_iff_sub_mem.mp h.symm
  rcases hm with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

section UniverseZeroCompatibility

variable (K₀ L₀ : Type)
  [Field K₀] [Field L₀] [Algebra K₀ L₀]
  [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
  [ValuativeRel K₀] [TopologicalSpace K₀] [IsNonarchimedeanLocalField K₀]
  [ValuativeRel L₀] [TopologicalSpace L₀] [IsNonarchimedeanLocalField L₀]
  [ValuativeExtension K₀ L₀] [ContinuousSMul K₀ L₀]

set_option maxHeartbeats 2000000 in
private theorem normalizedFundamentalClassRawNormTateEquiv_bridge
    {raw : Additive (Abelianization (L₀ ≃ₐ[K₀] L₀)) ≃+
      Additive (Units K₀ ⧸ normSubgroup K₀ L₀)}
    (B : UniverseBridge K₀ L₀ raw) :
    (normalizedFundamentalClassRawNormTateEquiv K₀ L₀).trans
        B.normQuotientTransport =
      B.abelianizationTransport.trans
        (normalizedFundamentalClassRawNormTateEquiv B.model.K₀ B.model.L₀) := by
  let b := B.baseEquiv
  let e := B.extensionEquiv
  letI aKK₁ : Algebra K₀ B.model.K₀ := b.toRingHom.toAlgebra
  letI aLL₁ : Algebra L₀ B.model.L₀ := e.toRingHom.toAlgebra
  let aKL₁Hom : K₀ →+* B.model.L₀ :=
    (algebraMap B.model.K₀ B.model.L₀).comp b.toRingHom
  letI aKL₁ : Algebra K₀ B.model.L₀ := aKL₁Hom.toAlgebra
  letI stKK₁L₁ : IsScalarTower K₀ B.model.K₀ B.model.L₀ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI stKL₀L₁ : IsScalarTower K₀ L₀ B.model.L₀ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact (B.algebra_compatibility x).symm
  let bA : K₀ ≃ₐ[K₀] B.model.K₀ :=
    { b with commutes' := fun _ => rfl }
  let eA : L₀ ≃ₐ[L₀] B.model.L₀ :=
    { e with commutes' := fun _ => rfl }
  letI fdKK₁ : FiniteDimensional K₀ B.model.K₀ :=
    bA.toLinearEquiv.finiteDimensional
  letI fdLL₁ : FiniteDimensional L₀ B.model.L₀ :=
    eA.toLinearEquiv.finiteDimensional
  letI fdKL₁ : FiniteDimensional K₀ B.model.L₀ :=
    FiniteDimensional.trans K₀ L₀ B.model.L₀
  letI galKL₁ : IsGalois K₀ B.model.L₀ := by
    apply IsGalois.of_equiv_equiv (F := K₀) (E := L₀)
      (M := K₀) (N := B.model.L₀) (f := RingEquiv.refl K₀) (g := e)
    ext x
    rw [RingHom.algebraMap_toAlgebra]
    exact (B.algebra_compatibility x).symm
  letI veKK₁ : ValuativeExtension K₀ B.model.K₀ :=
    valuativeExtension_of_normalizedValuation_ringEquiv b B.base_valuation
  letI veLL₁ : ValuativeExtension L₀ B.model.L₀ :=
    valuativeExtension_of_normalizedValuation_ringEquiv e B.extension_valuation
  letI veKL₁ : ValuativeExtension K₀ B.model.L₀ := by
    constructor
    intro x y
    change (algebraMap B.model.K₀ B.model.L₀ (b x) ≤ᵥ
      algebraMap B.model.K₀ B.model.L₀ (b y)) ↔ x ≤ᵥ y
    rw [ValuativeExtension.vle_iff_vle (A := B.model.K₀) (B := B.model.L₀)]
    exact ValuativeExtension.vle_iff_vle (A := K₀) (B := B.model.K₀) x y
  have hbcont : Continuous b :=
    ringEquiv_continuous_of_valuativeExtension b (fun _ => rfl)
  have hecont : Continuous e :=
    ringEquiv_continuous_of_valuativeExtension e (fun _ => rfl)
  letI csKK₁ : ContinuousSMul K₀ B.model.K₀ :=
    continuousSMul_of_algebraMap K₀ B.model.K₀ (by
      change Continuous (b : K₀ → B.model.K₀)
      exact hbcont)
  letI csLL₁ : ContinuousSMul L₀ B.model.L₀ :=
    continuousSMul_of_algebraMap L₀ B.model.L₀ (by
      change Continuous (e : L₀ → B.model.L₀)
      exact hecont)
  letI csKL₁ : ContinuousSMul K₀ B.model.L₀ :=
    continuousSMul_of_algebraMap K₀ B.model.L₀ (by
      change Continuous ((algebraMap B.model.K₀ B.model.L₀) ∘ b)
      exact (continuous_algebraMap B.model.K₀ B.model.L₀).comp hbcont)
  obtain ⟨DI, hDI⟩ := fundamentalClass_inflation K₀ L₀ B.model.L₀
  obtain ⟨DR, hDR⟩ := fundamentalClass_restriction K₀ B.model.L₀ B.model.K₀
  let C₀ := cohomologicalConstruction K₀ L₀
  let C₁ := cohomologicalConstruction B.model.K₀ B.model.L₀
  let a₀ := C₀.cocycle
  let ha₀ := C₀.cocycle_mem
  let aI := transportedC2 DI.quotientHom DI.coefficient a₀
  let haI := finiteReciprocity_transportedC2_mem DI.quotientHom DI.coefficient a₀ ha₀
  let aR := transportedC2 DR.subgroupHom DR.coefficient aI
  let haR := finiteReciprocity_transportedC2_mem DR.subgroupHom DR.coefficient aI haI
  have hfin : Module.finrank L₀ B.model.L₀ = 1 := by
    apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    change Function.Bijective (e : L₀ → B.model.L₀)
    exact e.bijective
  have hclassI : AbstractReciprocity.cocycleClass2 (MulRep K₀ B.model.L₀) aI haI =
      fundamentalClassValue K₀ B.model.L₀ := by
    calc
      AbstractReciprocity.cocycleClass2 (MulRep K₀ B.model.L₀) aI haI =
          transportedH2 DI.quotientHom DI.coefficient
            (AbstractReciprocity.cocycleClass2 (MulRep K₀ L₀) a₀ ha₀) :=
        (finiteReciprocity_transportedH2_cocycleClass_eq
          DI.quotientHom DI.coefficient a₀ ha₀).symm
      _ = transportedH2 DI.quotientHom DI.coefficient
          (fundamentalClassValue K₀ L₀) := congrArg _ C₀.represents
      _ = (Module.finrank L₀ B.model.L₀ : ℤ) •
          fundamentalClassValue K₀ B.model.L₀ := hDI
      _ = fundamentalClassValue K₀ B.model.L₀ := by rw [hfin]; simp
  have hclassR : AbstractReciprocity.cocycleClass2
      (MulRep B.model.K₀ B.model.L₀) aR haR =
      fundamentalClassValue B.model.K₀ B.model.L₀ := by
    calc
      AbstractReciprocity.cocycleClass2 (MulRep B.model.K₀ B.model.L₀) aR haR =
          transportedH2 DR.subgroupHom DR.coefficient
            (AbstractReciprocity.cocycleClass2 (MulRep K₀ B.model.L₀) aI haI) :=
        (finiteReciprocity_transportedH2_cocycleClass_eq
          DR.subgroupHom DR.coefficient aI haI).symm
      _ = transportedH2 DR.subgroupHom DR.coefficient
          (fundamentalClassValue K₀ B.model.L₀) := congrArg _ hclassI
      _ = fundamentalClassValue B.model.K₀ B.model.L₀ := hDR
  have hcoh : AbstractReciprocity.Cohomologous2
      (MulRep B.model.K₀ B.model.L₀) aR C₁.cocycle :=
    finiteReciprocity_cohomologous2_of_cocycleClass_eq _ aR C₁.cocycle haR
      C₁.cocycle_mem (hclassR.trans C₁.represents.symm)
  have hgroup (τ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀) :
      DI.quotientHom (DR.subgroupHom τ) = B.galoisTransport.symm τ := by
    ext x
    apply e.injective
    calc
      e (DI.quotientHom (DR.subgroupHom τ) x) =
          DR.subgroupHom τ (e x) := by
        change e.toRingHom (DI.quotientHom (DR.subgroupHom τ) x) =
          DR.subgroupHom τ (e.toRingHom x)
        exact DI.quotientHom_apply (DR.subgroupHom τ) x
      _ = τ (e x) := DR.subgroupHom_apply τ (e x)
      _ = B.galoisTransport (B.galoisTransport.symm τ) (e x) := by simp
      _ = e (B.galoisTransport.symm τ x) :=
        (B.galoisTransport_apply (B.galoisTransport.symm τ) x).symm
  have hcoeffI (z : Additive (Units L₀)) :
      DI.coefficient.hom z = Additive.ofMul
        (Units.map e.toRingHom (Additive.toMul z)) := by
    apply Additive.toMul.injective
    change Additive.toMul (DI.coefficient.hom
      (Additive.ofMul (Additive.toMul z))) = _
    exact DI.coefficient_apply (Additive.toMul z)
  have hcoeffR (z : Additive (Units B.model.L₀)) :
      DR.coefficient.hom z = z := by
    change DR.coefficient.hom (Additive.ofMul (Additive.toMul z)) = z
    exact DR.coefficient_apply (Additive.toMul z)
  have haR_apply (τ υ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀) :
      aR τ υ = Additive.ofMul (Units.map e.toRingHom
        (Additive.toMul (a₀ (B.galoisTransport.symm τ)
          (B.galoisTransport.symm υ)))) := by
    change DR.coefficient.hom (DI.coefficient.hom
      (a₀ (DI.quotientHom (DR.subgroupHom τ))
        (DI.quotientHom (DR.subgroupHom υ)))) = _
    rw [hcoeffR, hcoeffI, hgroup, hgroup]
  have hgenerator (σ : L₀ ≃ₐ[K₀] L₀) :
      B.normQuotientTransport
          (normalizedFundamentalClassRawNormTateEquiv K₀ L₀
            (Additive.ofMul (Abelianization.of σ))) =
        normalizedFundamentalClassRawNormTateEquiv B.model.K₀ B.model.L₀
          (B.abelianizationTransport (Additive.ofMul (Abelianization.of σ))) := by
    let r₀ := AbstractReciprocity.rowSumInvariant (MulRep K₀ L₀) a₀ ha₀ σ
    let nr₀ : Inhomogeneous.invariants0 (MulRep K₀ L₀) := -r₀
    let x : Units K₀ := Additive.toMul
      (explicitMulRepInvariantsEquiv K₀ L₀ nr₀)
    let em : Additive (Units L₀) →+ Additive (Units B.model.L₀) :=
      (Units.map e.toRingHom).toAdditive
    let bx : Units B.model.K₀ := Units.map b.toRingHom x
    have hx : baseUnitInvariant K₀ L₀ x = nr₀ := by
      apply (explicitMulRepInvariantsEquiv K₀ L₀).injective
      rw [explicitMulRepInvariantsEquiv_baseUnit K₀ L₀]
      rfl
    have hr :
        (AbstractReciprocity.rowSumInvariant (MulRep B.model.K₀ B.model.L₀)
          aR haR (B.galoisTransport σ)).1 = em r₀.1 := by
      change (∑ τ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀,
          aR τ (B.galoisTransport σ)) =
        em (∑ τ : L₀ ≃ₐ[K₀] L₀, a₀ τ σ)
      calc
        (∑ τ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀,
            aR τ (B.galoisTransport σ)) =
            ∑ τ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀,
              em (a₀ (B.galoisTransport.symm τ) σ) := by
          apply Finset.sum_congr rfl
          intro τ _
          rw [haR_apply, B.galoisTransport.symm_apply_apply]
          rfl
        _ = ∑ τ : L₀ ≃ₐ[K₀] L₀, em (a₀ τ σ) := by
          simpa using (Equiv.sum_comp B.galoisTransport.toEquiv
            (fun τ => em (a₀ (B.galoisTransport.symm τ) σ))).symm
        _ = em (∑ τ : L₀ ≃ₐ[K₀] L₀, a₀ τ σ) := by rw [map_sum]
    have hbx : baseUnitInvariant B.model.K₀ B.model.L₀ bx =
        -AbstractReciprocity.rowSumInvariant (MulRep B.model.K₀ B.model.L₀)
          aR haR (B.galoisTransport σ) := by
      apply Subtype.ext
      have hbase : (baseUnitInvariant B.model.K₀ B.model.L₀ bx).1 =
          -(em r₀.1) := by
        calc
          (baseUnitInvariant B.model.K₀ B.model.L₀ bx).1 =
              em (baseUnitInvariant K₀ L₀ x).1 := by
            apply Additive.toMul.injective
            apply Units.ext
            exact (B.algebra_compatibility (x : K₀)).symm
          _ = em (nr₀.1) := congrArg em (congrArg Subtype.val hx)
          _ = em (-r₀.1) := rfl
          _ = -(em r₀.1) := map_neg em r₀.1
      exact hbase.trans (congrArg Neg.neg hr.symm)
    have hq₀ :
        -AbstractReciprocity.rowSumClass (MulRep K₀ L₀) a₀ ha₀ σ =
          tateClassOfBaseUnit K₀ L₀ x := by
      change -(QuotientAddGroup.mk r₀) =
        QuotientAddGroup.mk (baseUnitInvariant K₀ L₀ x)
      rw [← QuotientAddGroup.mk_neg]
      rw [hx]
    have hqR :
        -AbstractReciprocity.rowSumClass (MulRep B.model.K₀ B.model.L₀)
            aR haR (B.galoisTransport σ) =
          tateClassOfBaseUnit B.model.K₀ B.model.L₀ bx := by
      change -(QuotientAddGroup.mk
          (AbstractReciprocity.rowSumInvariant (MulRep B.model.K₀ B.model.L₀)
            aR haR (B.galoisTransport σ))) =
        QuotientAddGroup.mk (baseUnitInvariant B.model.K₀ B.model.L₀ bx)
      rw [← QuotientAddGroup.mk_neg]
      rw [hbx]
    have hrows := AbstractReciprocity.rowSumClass_coboundary_independent
      (MulRep B.model.K₀ B.model.L₀) aR C₁.cocycle haR C₁.cocycle_mem hcoh
        (B.galoisTransport σ)
    have hq₁ :
        -AbstractReciprocity.rowSumClass (MulRep B.model.K₀ B.model.L₀)
            C₁.cocycle C₁.cocycle_mem (B.galoisTransport σ) =
          tateClassOfBaseUnit B.model.K₀ B.model.L₀ bx := by
      rw [← hrows]
      exact hqR
    have heval₀ :
        normalizedFundamentalClassRawNormTateEquiv K₀ L₀
            (Additive.ofMul (Abelianization.of σ)) =
          Additive.ofMul (QuotientGroup.mk x : Units K₀ ⧸ normSubgroup K₀ L₀) := by
      rw [normalizedFundamentalClassRawNormTateEquiv_def, AddEquiv.trans_apply,
        cohomologicalRawTateEquiv_apply, hq₀]
      exact C₀.tateQuotient_apply x
    have heval₁ :
        normalizedFundamentalClassRawNormTateEquiv B.model.K₀ B.model.L₀
            (Additive.ofMul (Abelianization.of (B.galoisTransport σ))) =
          Additive.ofMul (QuotientGroup.mk bx :
            Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀) := by
      rw [normalizedFundamentalClassRawNormTateEquiv_def, AddEquiv.trans_apply,
        cohomologicalRawTateEquiv_apply, hq₁]
      exact C₁.tateQuotient_apply bx
    rw [heval₀, B.normQuotientTransport_mk, B.abelianizationTransport_of, heval₁]
  apply AddEquiv.ext
  intro z
  change B.normQuotientTransport
      (normalizedFundamentalClassRawNormTateEquiv K₀ L₀ z) =
    normalizedFundamentalClassRawNormTateEquiv B.model.K₀ B.model.L₀
      (B.abelianizationTransport z)
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
  have hz : z = Additive.ofMul (Abelianization.of σ) := by
    apply Additive.toMul.injective
    exact hσ.symm
  rw [hz]
  exact hgenerator σ

/-- The universe-zero specialization of the public construction agrees with the concrete
compensated abstract-reciprocity map.  The polymorphic statement is the stronger
`rawNormTateEquiv_universeBridge` equation above. -/
theorem compensatedNormTateEquiv_eq_abstractReciprocity :
    compensatedNormTateEquiv K₀ L₀ =
      cohomologicalCompensatedNormTateEquiv K₀ L₀ := by
  let B := (construction K₀ L₀).universeBridge
  have hbridge := rawNormTateEquiv_universeBridge K₀ L₀
  have hnormalized := normalizedFundamentalClassRawNormTateEquiv_bridge K₀ L₀ B
  have hraw : rawNormTateEquiv K₀ L₀ =
      normalizedFundamentalClassRawNormTateEquiv K₀ L₀ := by
    apply AddEquiv.ext
    intro x
    apply B.normQuotientTransport.injective
    exact DFunLike.congr_fun (hbridge.trans hnormalized.symm) x
  rw [compensatedNormTateEquiv_def, hraw,
    normalizedFundamentalClassRawNormTateEquiv_def]
  apply AddEquiv.ext
  intro x
  change -((cohomologicalConstruction K₀ L₀).tateQuotient
      (cohomologicalRawTateEquiv K₀ L₀ x)) =
    (cohomologicalConstruction K₀ L₀).tateQuotient
      (-(cohomologicalRawTateEquiv K₀ L₀ x))
  exact (@AddEquiv.map_neg
    (TateLowDegree.H0 (MulRep K₀ L₀))
    (Additive (Units K₀ ⧸ normSubgroup K₀ L₀))
    inferInstance inferInstance (cohomologicalConstruction K₀ L₀).tateQuotient
    (cohomologicalRawTateEquiv K₀ L₀ x)).symm

end UniverseZeroCompatibility

private theorem finiteReciprocity_self_ramificationIndex
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [ValuativeExtension F F] :
    ramificationIndex F F = 1 := by
  have h := normalizedValuation_algebraMap F F (defaultUniformizer F).val
  have hval := (defaultUniformizer F).valuation_eq_one
  simp [hval] at h
  exact_mod_cast h.symm

private noncomputable def finiteReciprocity_selfUnramifiedCyclicExtensionData
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [ValuativeExtension F F] [ContinuousSMul F F] :
    UnramifiedCyclicExtensionData F F := by
  letI : NeZero (Module.finrank F F) := ⟨Module.finrank_pos.ne'⟩
  let frob : F ≃ₐ[F] F := AlgEquiv.refl
  have hgen : Subgroup.zpowers frob = ⊤ := by
    apply top_unique
    intro σ _
    have hσ : σ = frob := Subsingleton.elim _ _
    rw [hσ]
    exact Subgroup.mem_zpowers frob
  have hmem : ∀ σ : F ≃ₐ[F] F, σ ∈ Subgroup.zpowers frob := by
    intro σ
    rw [hgen]
    exact Subgroup.mem_top σ
  let ef : Multiplicative (ZMod (Module.finrank F F)) ≃* (F ≃ₐ[F] F) :=
    zmodMulEquivOfGenerator hmem (IsGalois.card_aut_eq_finrank F F)
  refine {
    unramified := ⟨finiteReciprocity_self_ramificationIndex F⟩
    frobenius := frob
    frobenius_preserves_integral := ?_
    frobenius_residue := ?_
    frobenius_generates := hgen
    frobeniusEquiv := ef
    frobeniusEquiv_apply := fun _ => Subsingleton.elim _ _ }
  · intro x
    exact ⟨x, rfl⟩
  · intro x y hy
    letI : Fintype (LocalResidueField F) := Fintype.ofFinite _
    have hxy : y = x := by
      apply Subtype.ext
      simpa [frob] using hy
    rw [hxy]
    let z : LocalResidueField F := Ideal.Quotient.mk (LocalMaximalIdeal F) x
    change z = z ^ residueCard F
    simpa [residueCard, Nat.card_eq_fintype_card] using (FiniteField.pow_card z).symm

private theorem finiteReciprocity_H2_subsingleton_of_subsingleton_group
    {G : Type} [Group G] [Subsingleton G] (M : Rep ℤ G) :
    Subsingleton (Inhomogeneous.H2 M) := by
  constructor
  intro x y
  suffices hz : ∀ z : Inhomogeneous.H2 M, z = 0 by rw [hz x, hz y]
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H c =>
    have hc : c = 0 := by
      apply Subtype.ext
      funext g h
      have hg : g = 1 := Subsingleton.elim _ _
      have hh : h = 1 := Subsingleton.elim _ _
      subst hg
      subst hh
      exact c.2.2.1 1
    rw [hc]
    rfl

private noncomputable def finiteReciprocity_idCoefficient
    {G : Type} [Group G] (M : Rep ℤ G) :
    Rep.res (MonoidHom.id G) M ⟶ M := CategoryTheory.CategoryStruct.id M

private theorem finiteReciprocity_transportedH2_id
    {G : Type} [Group G] (M : Rep ℤ G) (x : Inhomogeneous.H2 M) :
    transportedH2 (MonoidHom.id G) (finiteReciprocity_idCoefficient M) x = x := by
  apply (comparisonH2 M).injective
  simp [transportedH2, finiteReciprocity_idCoefficient]

set_option maxHeartbeats 1000000 in
private theorem finiteReciprocity_fundamentalClass_eq_unramifiedClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K)
    (C : UnramifiedClassData K L D π) :
    fundamentalClassValue K L = C.class := by
  letI veLL : ValuativeExtension L L := ⟨fun _ _ => Iff.rfl⟩
  letI csLL : ContinuousSMul L L := inferInstance
  letI stKLL : IsScalarTower K L L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let upper := finiteReciprocity_selfUnramifiedCyclicExtensionData L
  let q : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L) := MonoidHom.id _
  let c : Rep.res q (MulRep K L) ⟶ MulRep K L := finiteReciprocity_idCoefficient (MulRep K L)
  let s : (L ≃ₐ[L] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  let sc : Rep.res s (MulRep K L) ⟶ MulRep L L := by
    let i : Additive (Units L) →+ Additive (Units L) := AddMonoidHom.id _
    exact Rep.ofHom ⟨i.toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      rfl⟩
  have hq (x : Inhomogeneous.H2 (MulRep K L)) : transportedH2 q c x = x :=
    finiteReciprocity_transportedH2_id (MulRep K L) x
  have hcomp : Algebra.adjoin K
      (Set.range (algebraMap L L) ∪ Set.range (algebraMap L L)) = ⊤ := by
    apply top_unique
    intro x _
    apply Algebra.subset_adjoin
    left
    exact ⟨x, rfl⟩
  have hintersection : Module.finrank K (⊤ : IntermediateField K L) =
      residueDegree K L := by
    rw [IntermediateField.finrank_top']
    have h := finrank_eq_ramificationIndex_mul_residueDegree K L
    rw [D.unramified.ramificationIndex_eq_one, one_mul] at h
    exact h
  have henvelope : Module.finrank L L = ramificationIndex K L := by
    rw [Module.finrank_self, D.unramified.ramificationIndex_eq_one]
  let Env : UnramifiedEnvelopeData K L L L π :=
    { source := D
      source_degree := rfl
      upper := upper
      compositum_eq_top := hcomp
      intersection := ⊤
      mem_intersection_iff := by
        intro x
        constructor
        · intro _
          exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
        · intro _
          trivial
      intersection_degree := hintersection
      envelope_degree_over_L := henvelope
      sourceClass := C
      sourceQuotient := q
      sourceQuotient_apply := by intro σ x; rfl
      sourceCoefficient := c
      sourceCoefficient_apply := by intro x; rfl
      psi := C.class
      psi_eq_inflated := (hq C.class).symm
      source_inflation_injective := by
        intro x y hxy
        rw [hq x, hq y] at hxy
        exact hxy
      psi_order := C.order_class
      upperSubgroup := s
      upperSubgroup_apply := by intro σ x; rfl
      upperCoefficient := sc
      upperCoefficient_apply := by intro x; rfl
      psi_restricts_zero :=
        (finiteReciprocity_H2_subsingleton_of_subsingleton_group (MulRep L L)).elim _ _
      descentQuotient := q
      descentQuotient_apply := by intro σ x; rfl
      descentCoefficient := c
      descentCoefficient_apply := by intro x; rfl
      descent_injective := by
        intro x y hxy
        rw [hq x, hq y] at hxy
        exact hxy
      psi_in_descent_range := ⟨C.class, hq C.class⟩
      descent_unique := by
        intro α β hα hβ
        rw [hq α] at hα
        rw [hq β] at hβ
        exact hα.trans hβ.symm }
  have h := (fundamentalClass K L).descends π L L Env
  change transportedH2 q c (fundamentalClassValue K L) = C.class at h
  rw [hq] at h
  exact h

private theorem finiteReciprocity_sum_carryExponent_one_of_one_lt (n : ℕ) [NeZero n]
    (hn : 1 < n) :
    (∑ r : ZMod n, (carryExponent n r 1 : ℤ)) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.pos n).ne'
  have hn2 : 1 < m + 1 := by omega
  letI : Fact (1 < m + 1) := ⟨hn2⟩
  have hval (i : Fin (m + 1)) : (ZMod.finEquiv (m + 1) i).val = i.val := by rfl
  rw [← Equiv.sum_comp (ZMod.finEquiv (m + 1)).toEquiv
    (fun r : ZMod (m + 1) => (carryExponent (m + 1) r 1 : ℤ))]
  calc
    (∑ x : Fin (m + 1),
        (carryExponent (m + 1) (ZMod.finEquiv (m + 1) x) 1 : ℤ)) =
        (carryExponent (m + 1)
          ((ZMod.finEquiv (m + 1)).toEquiv (Fin.last ((m + 1) - 1))) 1 : ℤ) := by
      apply Fintype.sum_eq_single
      intro b hb
      have hbval : b.val < m + 1 := b.isLt
      have hbne : b.val ≠ (m + 1) - 1 := by
        intro heq
        apply hb
        apply Fin.ext
        simpa using heq
      have hlt : b.val + 1 < m + 1 := by omega
      simp [carryExponent, hval, ZMod.val_one, hlt]
    _ = 1 := by simp [carryExponent, hval, ZMod.val_one]

set_option maxHeartbeats 1000000 in
private theorem finiteReciprocity_cohomologicalCompensated_unramified
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    FiniteReciprocity.cohomologicalCompensatedNormTateEquiv K L
        (Additive.ofMul (Abelianization.of D.frobenius)) =
      Additive.ofMul (QuotientGroup.mk π.val : Units K ⧸ normSubgroup K L) := by
  obtain ⟨C⟩ := carryCocycle_isGenerator K L D π
  let C₀ := FiniteReciprocity.cohomologicalConstruction K L
  have hfund : fundamentalClassValue K L = C.class :=
    finiteReciprocity_fundamentalClass_eq_unramifiedClass K L D π C
  have hclass : AbstractReciprocity.cocycleClass2 (MulRep K L)
      C₀.cocycle C₀.cocycle_mem =
      AbstractReciprocity.cocycleClass2 (MulRep K L) C.cocycle C.cocycle_mem :=
    C₀.represents.trans (hfund.trans C.class_eq_cocycle)
  have hcoh : AbstractReciprocity.Cohomologous2 (MulRep K L)
      C₀.cocycle C.cocycle :=
    finiteReciprocity_cohomologous2_of_cocycleClass_eq _ _ _ _ _ hclass
  have hrows := AbstractReciprocity.rowSumClass_coboundary_independent
    (MulRep K L) C₀.cocycle C.cocycle C₀.cocycle_mem C.cocycle_mem hcoh D.frobenius
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  have hq : AbstractReciprocity.rowSumClass (MulRep K L)
      C.cocycle C.cocycle_mem D.frobenius =
      FiniteReciprocity.tateClassOfBaseUnit K L π.val := by
    by_cases hn : n = 1
    · have hcard : Nat.card (L ≃ₐ[K] L) = 1 := by
        rw [IsGalois.card_aut_eq_finrank K L]
        exact hn
      letI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.mp hcard).1
      letI : Subsingleton (Abelianization (L ≃ₐ[K] L)) := by
        constructor
        intro x y
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
        congr 1
        exact Subsingleton.elim a b
      letI : Subsingleton (Units K ⧸ normSubgroup K L) :=
        ⟨fun x y => (FiniteReciprocity.artin K L).injective (Subsingleton.elim _ _)⟩
      letI : Subsingleton (TateLowDegree.H0 (MulRep K L)) :=
        ⟨fun x y => C₀.tateQuotient.injective (Subsingleton.elim _ _)⟩
      apply Subsingleton.elim
    · have hnlt : 1 < n := by
        have hnpos := NeZero.pos n
        omega
      letI : Fact (1 < n) := ⟨hnlt⟩
      have hF : D.frobeniusEquiv (Multiplicative.ofAdd (1 : ZMod n)) =
          D.frobenius := by
        rw [D.frobeniusEquiv_apply]
        simp [ZMod.val_one]
      apply QuotientAddGroup.eq.mpr
      change -AbstractReciprocity.rowSumInvariant (MulRep K L)
          C.cocycle C.cocycle_mem D.frobenius +
        FiniteReciprocity.baseUnitInvariant K L π.val ∈
          TateLowDegree.normRangeInInvariants (MulRep K L)
      have hrow : AbstractReciprocity.rowSumInvariant (MulRep K L)
          C.cocycle C.cocycle_mem D.frobenius =
          FiniteReciprocity.baseUnitInvariant K L π.val := by
        apply Subtype.ext
        let u : (MulRep K L).V :=
          Additive.ofMul (Units.map (algebraMap K L) π.val)
        change (∑ σ : L ≃ₐ[K] L, C.cocycle σ D.frobenius) = u
        rw [C.cocycle_eq_carry, ← hF]
        rw [← Equiv.sum_comp D.frobeniusEquiv.toEquiv
          (fun σ : L ≃ₐ[K] L => carryCocycle K L D π σ
            (D.frobeniusEquiv (Multiplicative.ofAdd (1 : ZMod n))))]
        have hterm (r : Multiplicative (ZMod n)) :
            carryCocycle K L D π (D.frobeniusEquiv r)
                (D.frobeniusEquiv (Multiplicative.ofAdd (1 : ZMod n))) =
              (carryExponent n r.toAdd 1 : ℤ) • u := by
          simp only [carryCocycle, MulEquiv.symm_apply_apply]
          have hs : (Multiplicative.ofAdd (1 : ZMod n)).toAdd = 1 := rfl
          rw [hs]
          by_cases hc : carryExponent n r.toAdd 1 = 0
          · rw [if_pos hc, hc]
            simp
          · have hle : carryExponent n r.toAdd 1 ≤ 1 := by
              simp only [carryExponent]
              split_ifs <;> omega
            have hone : carryExponent n r.toAdd 1 = 1 := by omega
            rw [if_neg hc, hone]
            simp [u]
        calc
          (∑ r : Multiplicative (ZMod n),
              carryCocycle K L D π (D.frobeniusEquiv.toEquiv r)
                (D.frobeniusEquiv (Multiplicative.ofAdd (1 : ZMod n)))) =
              ∑ r : Multiplicative (ZMod n),
                (carryExponent n r.toAdd 1 : ℤ) • u := by
            apply Finset.sum_congr rfl
            intro r _
            exact hterm r
          _ = ∑ r : ZMod n, (carryExponent n r 1 : ℤ) • u := by
            simpa using (Equiv.sum_comp Multiplicative.ofAdd
              (fun r : Multiplicative (ZMod n) =>
                (carryExponent n r.toAdd 1 : ℤ) • u)).symm
          _ = (∑ r : ZMod n, (carryExponent n r 1 : ℤ)) • u := by
            rw [Finset.sum_smul]
          _ = u := by rw [finiteReciprocity_sum_carryExponent_one_of_one_lt n hnlt, one_zsmul]
      rw [hrow]
      simp
  rw [FiniteReciprocity.cohomologicalCompensatedNormTateEquiv,
    AddEquiv.trans_apply, FiniteReciprocity.cohomologicalCompensatedTate_apply,
    hrows, hq]
  exact C₀.tateQuotient_apply π.val

private noncomputable def finiteReciprocity_ringOfIntegersEquiv
    {A B : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Algebra A B] [ValuativeExtension A B] [Algebra B A] [ValuativeExtension B A]
    (e : A ≃+* B) (he : ∀ x : A, algebraMap A B x = e x)
    (hes : ∀ x : B, algebraMap B A x = e.symm x) :
    RingOfIntegers A ≃+* RingOfIntegers B := by
  let f : RingOfIntegers A →+* RingOfIntegers B :=
    { toFun := fun x => ⟨e x, by
        change ValuativeRel.valuation B (e x) ≤ 1
        apply (Valuation.Compatible.vle_iff_le _ _).mp
        rw [← he]
        have hv := (ValuativeExtension.vle_iff_vle
          (A := A) (B := B) (x : A) 1).2
          ((Valuation.Compatible.vle_iff_le _ _).2
            ((Valuation.mem_integer_iff _ _).mp x.property))
        simpa using hv⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun x y => Subtype.ext (e.map_mul x y)
      map_zero' := Subtype.ext e.map_zero
      map_add' := fun x y => Subtype.ext (e.map_add x y) }
  let g : RingOfIntegers B →+* RingOfIntegers A :=
    { toFun := fun x => ⟨e.symm x, by
        change ValuativeRel.valuation A (e.symm x) ≤ 1
        apply (Valuation.Compatible.vle_iff_le _ _).mp
        rw [← hes]
        have hv := (ValuativeExtension.vle_iff_vle
          (A := B) (B := A) (x : B) 1).2
          ((Valuation.Compatible.vle_iff_le _ _).2
            ((Valuation.mem_integer_iff _ _).mp x.property))
        simpa using hv⟩
      map_one' := Subtype.ext e.symm.map_one
      map_mul' := fun x y => Subtype.ext (e.symm.map_mul x y)
      map_zero' := Subtype.ext e.symm.map_zero
      map_add' := fun x y => Subtype.ext (e.symm.map_add x y) }
  exact
    { toFun := f
      invFun := g
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      map_mul' := f.map_mul
      map_add' := f.map_add }

private theorem finiteReciprocity_ringOfIntegersEquiv_maximalIdeal
    {A B : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Algebra A B] [ValuativeExtension A B] [Algebra B A] [ValuativeExtension B A]
    (e : A ≃+* B) (he : ∀ x : A, algebraMap A B x = e x)
    (hes : ∀ x : B, algebraMap B A x = e.symm x) :
    LocalMaximalIdeal B = Ideal.map (finiteReciprocity_ringOfIntegersEquiv e he hes).toRingHom
      (LocalMaximalIdeal A) := by
  let eO := finiteReciprocity_ringOfIntegersEquiv e he hes
  ext y
  change y ∈ LocalMaximalIdeal B ↔ y ∈ Ideal.map eO (LocalMaximalIdeal A)
  rw [← eO.apply_symm_apply y, Ideal.apply_mem_of_equiv_iff]
  let x := eO.symm y
  change eO x ∈ LocalMaximalIdeal B ↔ x ∈ LocalMaximalIdeal A
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (eO x) ↔ ¬IsUnit x
  exact not_congr (isUnit_map_iff eO x)

private noncomputable def finiteReciprocity_residueEquiv
    {A B : Type*}
    [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [Field B] [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [Algebra A B] [ValuativeExtension A B] [Algebra B A] [ValuativeExtension B A]
    (e : A ≃+* B) (he : ∀ x : A, algebraMap A B x = e x)
    (hes : ∀ x : B, algebraMap B A x = e.symm x) :
    LocalResidueField A ≃+* LocalResidueField B :=
  Ideal.quotientEquiv (LocalMaximalIdeal A) (LocalMaximalIdeal B)
    (finiteReciprocity_ringOfIntegersEquiv e he hes)
    (finiteReciprocity_ringOfIntegersEquiv_maximalIdeal e he hes)

set_option maxHeartbeats 1000000 in
set_option linter.tacticCheckInstances false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteReciprocity_transportUnramifiedData
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    {raw : Additive (Abelianization (L ≃ₐ[K] L)) ≃+
      Additive (Units K ⧸ normSubgroup K L)}
    (B : FiniteReciprocity.UniverseBridge K L raw)
    (hunr : IsUnramifiedLocalExtension K L)
    (F : L ≃ₐ[K] L)
    (hpres : ∀ x : RingOfIntegers L,
      ∃ y : RingOfIntegers L, (y : L) = F (x : L))
    (hres : ∀ (x y : RingOfIntegers L), (y : L) = F (x : L) →
      Ideal.Quotient.mk (LocalMaximalIdeal L) y =
        (Ideal.Quotient.mk (LocalMaximalIdeal L) x) ^ residueCard K)
    (hgen : Subgroup.zpowers F = ⊤) :
    UnramifiedCyclicExtensionData B.model.K₀ B.model.L₀ := by
  let b := B.baseEquiv
  let e := B.extensionEquiv
  letI aKK₁ : Algebra K B.model.K₀ := b.toRingHom.toAlgebra
  letI aK₁K : Algebra B.model.K₀ K := b.symm.toRingHom.toAlgebra
  letI aLL₁ : Algebra L B.model.L₀ := e.toRingHom.toAlgebra
  letI aL₁L : Algebra B.model.L₀ L := e.symm.toRingHom.toAlgebra
  have hbval' (x : Units B.model.K₀) :
      normalizedValuation K (Units.map b.symm.toMonoidHom x) =
        normalizedValuation B.model.K₀ x := by
    have hm : Units.map b.toMonoidHom
        (Units.map b.symm.toMonoidHom x) = x := by
      apply Units.ext
      simp
    calc
      normalizedValuation K (Units.map b.symm.toMonoidHom x) =
          normalizedValuation B.model.K₀
            (Units.map b.toMonoidHom (Units.map b.symm.toMonoidHom x)) :=
        (B.base_valuation (Units.map b.symm.toMonoidHom x)).symm
      _ = normalizedValuation B.model.K₀ x := congrArg _ hm
  have heval' (x : Units B.model.L₀) :
      normalizedValuation L (Units.map e.symm.toMonoidHom x) =
        normalizedValuation B.model.L₀ x := by
    have hm : Units.map e.toMonoidHom
        (Units.map e.symm.toMonoidHom x) = x := by
      apply Units.ext
      simp
    calc
      normalizedValuation L (Units.map e.symm.toMonoidHom x) =
          normalizedValuation B.model.L₀
            (Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom x)) :=
        (B.extension_valuation (Units.map e.symm.toMonoidHom x)).symm
      _ = normalizedValuation B.model.L₀ x := congrArg _ hm
  letI veKK₁ : ValuativeExtension K B.model.K₀ :=
    valuativeExtension_of_normalizedValuation_ringEquiv b B.base_valuation
  letI veK₁K : ValuativeExtension B.model.K₀ K :=
    valuativeExtension_of_normalizedValuation_ringEquiv b.symm hbval'
  letI veLL₁ : ValuativeExtension L B.model.L₀ :=
    valuativeExtension_of_normalizedValuation_ringEquiv e B.extension_valuation
  letI veL₁L : ValuativeExtension B.model.L₀ L :=
    valuativeExtension_of_normalizedValuation_ringEquiv e.symm heval'
  let bO := finiteReciprocity_ringOfIntegersEquiv b (fun _ => rfl) (fun _ => rfl)
  let eO := finiteReciprocity_ringOfIntegersEquiv e (fun _ => rfl) (fun _ => rfl)
  let bq := finiteReciprocity_residueEquiv b (fun _ => rfl) (fun _ => rfl)
  let eq := finiteReciprocity_residueEquiv e (fun _ => rfl) (fun _ => rfl)
  have heq_mk (z : RingOfIntegers L) :
      eq (Ideal.Quotient.mk (LocalMaximalIdeal L) z) =
        Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) (eO z) := by
    rfl
  have hrescard : residueCard K = residueCard B.model.K₀ := by
    unfold residueCard
    exact Nat.card_congr bq.toEquiv
  let π : Uniformizer K := defaultUniformizer K
  let π₁ : Uniformizer B.model.K₀ :=
    ⟨Units.map b.toRingHom π.val, B.base_valuation π.val |>.trans π.valuation_eq_one⟩
  have hmapπ : Units.map (algebraMap B.model.K₀ B.model.L₀).toMonoidHom π₁.val =
      Units.map e.toMonoidHom (Units.map (algebraMap K L).toMonoidHom π.val) := by
    apply Units.ext
    exact (B.algebra_compatibility (π.val : K)).symm
  have hπL : normalizedValuation L
      (Units.map (algebraMap K L).toMonoidHom π.val) = 1 := by
    have hv := normalizedValuation_algebraMap K L π.val
    rw [π.valuation_eq_one, hunr.ramificationIndex_eq_one] at hv
    norm_num at hv
    exact hv
  have hπL₁ : normalizedValuation B.model.L₀
      (Units.map (algebraMap B.model.K₀ B.model.L₀).toMonoidHom π₁.val) = 1 := by
    rw [hmapπ]
    exact (B.extension_valuation
      (Units.map (algebraMap K L).toMonoidHom π.val)).trans hπL
  have hram : ramificationIndex B.model.K₀ B.model.L₀ = 1 := by
    have h := normalizedValuation_algebraMap B.model.K₀ B.model.L₀ π₁.val
    rw [π₁.valuation_eq_one] at h
    norm_num at h
    exact_mod_cast h.symm.trans hπL₁
  have heO_symm_val (x : RingOfIntegers B.model.L₀) :
      e ((eO.symm x : RingOfIntegers L) : L) = (x : B.model.L₀) :=
    congrArg Subtype.val (eO.apply_symm_apply x)
  let F₁ := B.galoisTransport F
  have hgen₁ : Subgroup.zpowers F₁ = ⊤ := by
    apply top_unique
    intro τ _
    obtain ⟨σ, rfl⟩ := B.galoisTransport.surjective τ
    have hs : σ ∈ Subgroup.zpowers F := by rw [hgen]; trivial
    rcases hs with ⟨z, rfl⟩
    exact ⟨z, by simp [F₁]⟩
  have hpres₁ : ∀ x : RingOfIntegers B.model.L₀,
      ∃ y : RingOfIntegers B.model.L₀, (y : B.model.L₀) = F₁ (x : B.model.L₀) := by
    intro x
    obtain ⟨y, hy⟩ := hpres (eO.symm x)
    refine ⟨eO y, ?_⟩
    change e (y : L) = F₁ (x : B.model.L₀)
    calc
      e (y : L) = e (F ((eO.symm x : RingOfIntegers L) : L)) := congrArg e hy
      _ = F₁ (e ((eO.symm x : RingOfIntegers L) : L)) :=
        B.galoisTransport_apply F _
      _ = F₁ (x : B.model.L₀) := congrArg F₁ (heO_symm_val x)
  have hres₁ : ∀ (x y : RingOfIntegers B.model.L₀),
      (y : B.model.L₀) = F₁ (x : B.model.L₀) →
      Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) y =
        (Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) x) ^
          residueCard B.model.K₀ := by
    intro x y hy
    have hxy : ((eO.symm y : RingOfIntegers L) : L) =
        F ((eO.symm x : RingOfIntegers L) : L) := by
      apply e.injective
      calc
        e ((eO.symm y : RingOfIntegers L) : L) = (y : B.model.L₀) :=
          heO_symm_val y
        _ = F₁ (x : B.model.L₀) := hy
        _ = F₁ (e ((eO.symm x : RingOfIntegers L) : L)) :=
          congrArg F₁ (heO_symm_val x).symm
        _ = e (F ((eO.symm x : RingOfIntegers L) : L)) :=
          (B.galoisTransport_apply F _).symm
    have hs := hres (eO.symm x) (eO.symm y) hxy
    rw [hrescard] at hs
    calc
      Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) y =
          Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) (eO (eO.symm y)) :=
        congrArg _ (eO.apply_symm_apply y).symm
      _ = eq (Ideal.Quotient.mk (LocalMaximalIdeal L) (eO.symm y)) := rfl
      _ = eq ((Ideal.Quotient.mk (LocalMaximalIdeal L) (eO.symm x)) ^
          residueCard B.model.K₀) := congrArg eq hs
      _ = (Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) (eO (eO.symm x))) ^
          residueCard B.model.K₀ := by
        rw [map_pow, heq_mk]
      _ = (Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) x) ^
          residueCard B.model.K₀ := congrArg (fun z =>
            Ideal.Quotient.mk (LocalMaximalIdeal B.model.L₀) z ^
              residueCard B.model.K₀) (eO.apply_symm_apply x)
  have hmem : ∀ σ : B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀,
      σ ∈ Subgroup.zpowers F₁ := by
    intro σ
    rw [hgen₁]
    trivial
  letI : NeZero (Module.finrank B.model.K₀ B.model.L₀) :=
    ⟨(Module.finrank_pos (R := B.model.K₀) (M := B.model.L₀)).ne'⟩
  let fEq : Multiplicative (ZMod (Module.finrank B.model.K₀ B.model.L₀)) ≃*
      (B.model.L₀ ≃ₐ[B.model.K₀] B.model.L₀) :=
    zmodMulEquivOfGenerator hmem
      (IsGalois.card_aut_eq_finrank B.model.K₀ B.model.L₀)
  exact
    { unramified := ⟨hram⟩
      frobenius := F₁
      frobenius_preserves_integral := hpres₁
      frobenius_residue := hres₁
      frobenius_generates := hgen₁
      frobeniusEquiv := fEq
      frobeniusEquiv_apply := by
        intro r
        have hr : (r.val : ZMod (Module.finrank B.model.K₀ B.model.L₀)) = r :=
          ZMod.natCast_zmod_val r
        calc
          fEq (Multiplicative.ofAdd r) =
              fEq (Multiplicative.ofAdd
                (r.val : ZMod (Module.finrank B.model.K₀ B.model.L₀))) :=
            congrArg fEq (congrArg Multiplicative.ofAdd hr.symm)
          _ = F₁ ^ (Int.ofNat r.val) := by
            rw [show fEq = zmodMulEquivOfGenerator hmem
              (IsGalois.card_aut_eq_finrank B.model.K₀ B.model.L₀) from rfl]
            simpa using zmodMulEquivOfGenerator_apply_ofAdd_intCast hmem
              (IsGalois.card_aut_eq_finrank B.model.K₀ B.model.L₀) (Int.ofNat r.val)
          _ = F₁ ^ r.val := zpow_natCast F₁ r.val }

end FiniteReciprocity

section FiniteArtin

variable (K : Type u) (Ksep : Type v)
  [Field K] [Field Ksep] [Algebra K Ksep]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The normalized finite Artin equivalence for an intermediate extension.  The local-field
structure is selected only to instantiate the finite-extension theorem; the defining equation
below pins the resulting map to compensated Tate reciprocity. -/
noncomputable def finiteArtin (L : FiniteGaloisIntermediateField K Ksep) :
    (Units K ⧸ normSubgroup K L) ≃* Abelianization (L ≃ₐ[K] L) := by
  let D := localFieldExtensionData K L
  letI : ValuativeRel L := D.valuativeRel
  letI : TopologicalSpace L := D.topology
  letI : IsNonarchimedeanLocalField L := D.localField
  letI : ValuativeExtension K L := D.valuativeExtension
  letI : ContinuousSMul K L := D.continuousSMul
  exact FiniteReciprocity.artin K L

/-- **R01**, Theorem `thm:finite-reciprocity`: the public map is inhabited by the explicitly
normalized construction, not by an unrelated `Nonempty.some`. -/
theorem finiteArtin_exists (L : FiniteGaloisIntermediateField K Ksep) :
    Nonempty ((Units K ⧸ normSubgroup K L) ≃*
      Abelianization (L ≃ₐ[K] L)) :=
  ⟨finiteArtin K Ksep L⟩

/-- Public defining equation tying `finiteArtin` to the inverse of the twice-displayed
raw-plus-neg compensated Tate equivalence. -/
theorem finiteArtin_defining_equation (L : FiniteGaloisIntermediateField K Ksep) :
    let D := localFieldExtensionData K L
    letI : ValuativeRel L := D.valuativeRel
    letI : TopologicalSpace L := D.topology
    letI : IsNonarchimedeanLocalField L := D.localField
    letI : ValuativeExtension K L := D.valuativeExtension
    letI : ContinuousSMul K L := D.continuousSMul
    MulEquiv.toAdditive (finiteArtin K Ksep L) =
      (FiniteReciprocity.compensatedNormTateEquiv K L).symm := by
  rfl

/-- The public universe-polymorphic Artin map is the inverse of the compensated normalized
fundamental-class map after the explicit universe bridge.  This is the canonicity equation of
blueprint lines 1709--1717; it rules out simultaneously twisting `raw`, `compensated`, and
`finiteArtin`. -/
theorem finiteArtin_universeBridge (L : FiniteGaloisIntermediateField K Ksep) :
    let D := localFieldExtensionData K L
    letI : ValuativeRel L := D.valuativeRel
    letI : TopologicalSpace L := D.topology
    letI : IsNonarchimedeanLocalField L := D.localField
    letI : ValuativeExtension K L := D.valuativeExtension
    letI : ContinuousSMul K L := D.continuousSMul
    let B := (FiniteReciprocity.construction K L).universeBridge
    (MulEquiv.toAdditive (finiteArtin K Ksep L)).symm.trans
        B.normQuotientTransport =
      B.abelianizationTransport.trans
        ((FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
          B.model.K₀ B.model.L₀).trans
            (AddEquiv.neg (Additive
              (Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀)))) := by
  let D := localFieldExtensionData K L
  letI : ValuativeRel L := D.valuativeRel
  letI : TopologicalSpace L := D.topology
  letI : IsNonarchimedeanLocalField L := D.localField
  letI : ValuativeExtension K L := D.valuativeExtension
  letI : ContinuousSMul K L := D.continuousSMul
  let C := FiniteReciprocity.construction K L
  let B := C.universeBridge
  have hArt := finiteArtin_defining_equation K Ksep L
  have hInv : (MulEquiv.toAdditive (finiteArtin K Ksep L)).symm =
      FiniteReciprocity.compensatedNormTateEquiv K L :=
    congrArg AddEquiv.symm hArt
  rw [hInv, FiniteReciprocity.compensatedNormTateEquiv_def]
  apply AddEquiv.ext
  intro x
  change B.normQuotientTransport (-C.rawNormTateEquiv x) =
    -FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
      B.model.K₀ B.model.L₀ (B.abelianizationTransport x)
  calc
    B.normQuotientTransport (-C.rawNormTateEquiv x) =
        -B.normQuotientTransport (C.rawNormTateEquiv x) := by
      exact @AddEquiv.map_neg
        (Additive (Units K ⧸ normSubgroup K L))
        (Additive (Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀))
        inferInstance inferInstance B.normQuotientTransport (C.rawNormTateEquiv x)
    _ = -FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
          B.model.K₀ B.model.L₀ (B.abelianizationTransport x) :=
      congrArg Neg.neg (DFunLike.congr_fun B.raw_eq_normalizedFundamentalClass x)

/-- **R01**, Corollary `cor:norm-index`: the norm index is the order of the abelianization. -/
theorem normSubgroup_index (L : FiniteGaloisIntermediateField K Ksep) :
    (normSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (finiteArtin K Ksep L).toEquiv

/-- **R02**, Corollary `cor:unramified-normalization`: a uniformizer maps to the uniquely pinned
arithmetic Frobenius. -/
theorem finiteArtin_uniformizer_unramified
    (L : FiniteGaloisIntermediateField K Ksep)
    (hL : UnramifiedFiniteExtension L) (π : Uniformizer K) :
    finiteArtin K Ksep L (QuotientGroup.mk π.val) =
      Abelianization.of (arithmeticFrobenius hL) := by
  let D := localFieldExtensionData K L
  letI : ValuativeRel L := D.valuativeRel
  letI : TopologicalSpace L := D.topology
  letI : IsNonarchimedeanLocalField L := D.localField
  letI : ValuativeExtension K L := D.valuativeExtension
  letI : ContinuousSMul K L := D.continuousSMul
  have hunr : IsUnramifiedLocalExtension K L := by
    let h := hL.unramified
    rw [hL.localFieldData_eq_selected] at h
    exact h
  have hpres : ∀ x : RingOfIntegers L,
      ∃ y : RingOfIntegers L, (y : L) = hL.frobenius (x : L) := by
    let h := hL.frobenius_preserves_integral
    rw [hL.localFieldData_eq_selected] at h
    exact h
  have hres : ∀ (x y : RingOfIntegers L),
      (y : L) = hL.frobenius (x : L) →
        Ideal.Quotient.mk (LocalMaximalIdeal L) y =
          (Ideal.Quotient.mk (LocalMaximalIdeal L) x) ^ residueCard K := by
    let h := hL.frobenius_residue
    rw [hL.localFieldData_eq_selected] at h
    exact h
  let C := FiniteReciprocity.construction K L
  let B := C.universeBridge
  let DU := FiniteReciprocity.finiteReciprocity_transportUnramifiedData
    B hunr hL.frobenius hpres hres hL.generates
  let b := B.baseEquiv
  let π₁ : Uniformizer B.model.K₀ :=
    ⟨Units.map b.toRingHom π.val, B.base_valuation π.val |>.trans π.valuation_eq_one⟩
  have hmodel := FiniteReciprocity.finiteReciprocity_cohomologicalCompensated_unramified
    B.model.K₀ B.model.L₀ DU π₁
  have hnormalized :
      ((FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
          B.model.K₀ B.model.L₀).trans
        (AddEquiv.neg (Additive
          (Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀))))
          (Additive.ofMul (Abelianization.of DU.frobenius)) =
        Additive.ofMul (QuotientGroup.mk π₁.val :
          Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀) := by
    rw [FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv_def]
    change -((FiniteReciprocity.cohomologicalConstruction
        B.model.K₀ B.model.L₀).tateQuotient
      (FiniteReciprocity.cohomologicalRawTateEquiv B.model.K₀ B.model.L₀
        (Additive.ofMul (Abelianization.of DU.frobenius)))) = _
    change (FiniteReciprocity.cohomologicalConstruction
        B.model.K₀ B.model.L₀).tateQuotient
      (-(FiniteReciprocity.cohomologicalRawTateEquiv B.model.K₀ B.model.L₀
        (Additive.ofMul (Abelianization.of DU.frobenius)))) = _ at hmodel
    rw [← hmodel]
    exact (@AddEquiv.map_neg
      (TateLowDegree.H0 (MulRep B.model.K₀ B.model.L₀))
      (Additive (Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀))
      inferInstance inferInstance
      (FiniteReciprocity.cohomologicalConstruction
        B.model.K₀ B.model.L₀).tateQuotient _).symm
  have hbridge := finiteArtin_universeBridge K Ksep L
  have hcomp :
      (MulEquiv.toAdditive (finiteArtin K Ksep L)).symm
          (Additive.ofMul (Abelianization.of hL.frobenius)) =
        Additive.ofMul (QuotientGroup.mk π.val : Units K ⧸ normSubgroup K L) := by
    apply B.normQuotientTransport.injective
    calc
      B.normQuotientTransport
          ((MulEquiv.toAdditive (finiteArtin K Ksep L)).symm
            (Additive.ofMul (Abelianization.of hL.frobenius))) =
          ((FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
              B.model.K₀ B.model.L₀).trans
            (AddEquiv.neg (Additive
              (Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀))))
            (B.abelianizationTransport
              (Additive.ofMul (Abelianization.of hL.frobenius))) :=
        DFunLike.congr_fun hbridge (Additive.ofMul (Abelianization.of hL.frobenius))
      _ = Additive.ofMul (QuotientGroup.mk π₁.val :
          Units B.model.K₀ ⧸ normSubgroup B.model.K₀ B.model.L₀) := by
        rw [B.abelianizationTransport_of]
        exact hnormalized
      _ = B.normQuotientTransport
          (Additive.ofMul (QuotientGroup.mk π.val : Units K ⧸ normSubgroup K L)) := by
        rw [B.normQuotientTransport_mk]
  apply (finiteArtin K Ksep L).symm.injective
  rw [(finiteArtin K Ksep L).symm_apply_apply]
  exact (congrArg Additive.toMul hcomp).symm

end FiniteArtin

section NormFunctoriality

variable (K : Type u) (E : Type v) (M : Type w)
  [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  [FiniteDimensional K E] [FiniteDimensional E M] [FiniteDimensional K M]
  [IsGalois K M] [IsGalois E M]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension K E] [ValuativeExtension E M] [ValuativeExtension K M]
  [ContinuousSMul K E] [ContinuousSMul E M] [ContinuousSMul K M]

/-- The field norm sends `N(M/E)` into `N(M/K)`, by the literal tower formula. -/
theorem normSubgroup_le_comap_norm :
    normSubgroup E M ≤ (normSubgroup K M).comap (normUnitsHom K E) := by
  rintro x ⟨y, rfl⟩
  exact ⟨y, normUnitsHom_tower K E M y⟩

/-- The actual norm map on Tate degree-zero quotients. -/
noncomputable def normOnQuotient :
    (Units E ⧸ normSubgroup E M) →* (Units K ⧸ normSubgroup K M) :=
  QuotientGroup.map (normSubgroup E M) (normSubgroup K M)
    (normUnitsHom K E) (normSubgroup_le_comap_norm K E M)

/-- Pointwise defining equation for the quotient norm. -/
@[simp] theorem normOnQuotient_mk (x : Units E) :
    normOnQuotient K E M (QuotientGroup.mk x) =
      (QuotientGroup.mk (normUnitsHom K E x) : Units K ⧸ normSubgroup K M) := by
  apply QuotientGroup.map_mk

/-- Literal inclusion `Gal(M/E) → Gal(M/K)` obtained by restricting scalars. -/
def galoisInclusion : (M ≃ₐ[E] M) →* (M ≃ₐ[K] M) :=
  AlgEquiv.restrictScalarsHom K

/-- Pointwise defining equation for subgroup inclusion. -/
@[simp] theorem galoisInclusion_apply (σ : M ≃ₐ[E] M) (x : M) :
    galoisInclusion K E M σ x = σ x := rfl

/-- Actual subgroup inclusion induced on abelianizations. -/
def inclusionAb : Abelianization (M ≃ₐ[E] M) →* Abelianization (M ≃ₐ[K] M) :=
  Abelianization.map (galoisInclusion K E M)

/-- Pointwise defining equation for inclusion on abelianizations. -/
@[simp] theorem inclusionAb_of (σ : M ≃ₐ[E] M) :
    inclusionAb K E M (Abelianization.of σ) =
      Abelianization.of (galoisInclusion K E M σ) := rfl

private theorem finiteReciprocity_restrictionToClosure_surjective
    (F : Type u) (E : Type v) (L : Type w)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L] :
    let Ω := AlgebraicClosure F
    let j : L →ₐ[F] Ω := IsAlgClosed.lift
    let r : (L ≃ₐ[F] L) → (E →ₐ[F] Ω) := fun g =>
      j.comp (g.toAlgHom.comp (IsScalarTower.toAlgHom F E L))
    Function.Surjective r := by
  dsimp only
  let Ω := AlgebraicClosure F
  let j : L →ₐ[F] Ω := IsAlgClosed.lift
  letI aLΩ : Algebra L Ω := j.toRingHom.toAlgebra
  letI stFLΩ : IsScalarTower F L Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let r : (L ≃ₐ[F] L) → (E →ₐ[F] Ω) := fun g =>
    j.comp (g.toAlgHom.comp (IsScalarTower.toAlgHom F E L))
  intro φ
  let aEΩ : Algebra E Ω := φ.toRingHom.toAlgebra
  letI : Algebra E Ω := aEΩ
  letI : IsScalarTower F E Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  let ψ : L →ₐ[E] Ω := IsAlgClosed.lift
  let ψF : L →ₐ[F] Ω := ψ.restrictScalars F
  let g : L ≃ₐ[F] L := AlgHom.restrictNormal' ψF L
  refine ⟨g, ?_⟩
  apply AlgHom.ext
  intro x
  change j (g (algebraMap E L x)) = φ x
  calc
    j (g (algebraMap E L x)) = ψF (algebraMap E L x) := by
      exact AlgHom.restrictNormal_commutes ψF L (algebraMap E L x)
    _ = φ x := by
      change ψ (algebraMap E L x) = φ x
      rw [ψ.commutes]
      rfl

private structure FiniteReciprocityGaloisEmbeddingDecomposition
    (F : Type u) (E : Type v) (L : Type w)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F L] where
  lift : (E →ₐ[F] AlgebraicClosure F) → (L ≃ₐ[F] L)
  lift_restrict : ∀ φ x,
    (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F)
        (lift φ (algebraMap E L x)) = φ x
  equiv : (E →ₐ[F] AlgebraicClosure F) × (L ≃ₐ[E] L) ≃ (L ≃ₐ[F] L)
  equiv_apply : ∀ φ h,
    equiv (φ, h) = lift φ * AlgEquiv.restrictScalarsHom F h

private noncomputable def finiteReciprocityGaloisEmbeddingDecomposition
    (F : Type u) (E : Type v) (L : Type w)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L] : FiniteReciprocityGaloisEmbeddingDecomposition F E L := by
  let Ω := AlgebraicClosure F
  let j : L →ₐ[F] Ω := IsAlgClosed.lift
  let r : (L ≃ₐ[F] L) → (E →ₐ[F] Ω) := fun g =>
    j.comp (g.toAlgHom.comp (IsScalarTower.toAlgHom F E L))
  have hr : Function.Surjective r :=
    finiteReciprocity_restrictionToClosure_surjective F E L
  let rep : (E →ₐ[F] Ω) → (L ≃ₐ[F] L) := Function.surjInv hr
  have hrep (φ : E →ₐ[F] Ω) : r (rep φ) = φ := Function.surjInv_eq hr φ
  let s : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L) := AlgEquiv.restrictScalarsHom F
  let toFun : (E →ₐ[F] Ω) × (L ≃ₐ[E] L) → (L ≃ₐ[F] L) :=
    fun p => rep p.1 * s p.2
  let invFun : (L ≃ₐ[F] L) → (E →ₐ[F] Ω) × (L ≃ₐ[E] L) := fun g =>
    let φ := r g
    let τ : L ≃ₐ[F] L := (rep φ)⁻¹ * g
    let h : L ≃ₐ[E] L :=
      { τ with
        commutes' := fun x => by
          change τ (algebraMap E L x) = algebraMap E L x
          apply (rep φ).injective
          rw [show τ (algebraMap E L x) =
            (rep φ)⁻¹ (g (algebraMap E L x)) by
              rw [AlgEquiv.mul_apply]]
          change rep φ ((rep φ).symm (g (algebraMap E L x))) = _
          rw [(rep φ).apply_symm_apply]
          apply j.injective
          calc
            j (g (algebraMap E L x)) = r g x := rfl
            _ = φ x := rfl
            _ = r (rep φ) x := (DFunLike.congr_fun (hrep φ) x).symm
            _ = j (rep φ (algebraMap E L x)) := rfl }
    (φ, h)
  refine
    { lift := rep
      lift_restrict := fun φ x => DFunLike.congr_fun (hrep φ) x
      equiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := by
            rintro ⟨φ, h⟩
            apply Prod.ext
            · apply AlgHom.ext
              intro x
              change r (rep φ * s h) x = φ x
              change j ((rep φ * s h) (algebraMap E L x)) = φ x
              rw [AlgEquiv.mul_apply]
              change j (rep φ (h (algebraMap E L x))) = φ x
              rw [h.commutes]
              exact DFunLike.congr_fun (hrep φ) x
            · apply AlgEquiv.ext
              intro x
              change ((rep (r (rep φ * s h)))⁻¹ * (rep φ * s h)) x = h x
              have hφ : r (rep φ * s h) = φ := by
                apply AlgHom.ext
                intro y
                change j ((rep φ * s h) (algebraMap E L y)) = φ y
                rw [AlgEquiv.mul_apply]
                change j (rep φ (h (algebraMap E L y))) = φ y
                rw [h.commutes]
                exact DFunLike.congr_fun (hrep φ) y
              rw [hφ]
              simp [s]
          right_inv := by
            intro g
            change rep (r g) * s ({ ((rep (r g))⁻¹ * g) with
              commutes' := _ } : L ≃ₐ[E] L) = g
            apply AlgEquiv.ext
            intro x
            simp [s] }
      equiv_apply := fun _ _ => rfl }

private theorem finiteReciprocity_normUnitsHom_eq_embeddingProduct
    (F : Type u) (E : Type v) (L : Type w)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L]
    (D : FiniteReciprocityGaloisEmbeddingDecomposition F E L) (x : Units E) :
    Units.map (algebraMap F L).toMonoidHom (normUnitsHom F E x) =
      ∏ φ : E →ₐ[F] AlgebraicClosure F,
        Units.map (D.lift φ).toRingEquiv.toRingHom
          (Units.map (algebraMap E L).toMonoidHom x) := by
  apply Units.ext
  apply (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F).injective
  change (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F)
      (algebraMap F L (((normUnitsHom F E x : Units F) : F))) =
    (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F)
      (((∏ φ : E →ₐ[F] AlgebraicClosure F,
        Units.map (D.lift φ).toRingEquiv.toRingHom
          (Units.map (algebraMap E L).toMonoidHom x) : Units L) : L))
  have hleft : ((normUnitsHom F E x : Units F) : F) = Algebra.norm F (x : E) := rfl
  have hright :
      (((∏ φ : E →ₐ[F] AlgebraicClosure F,
        Units.map (D.lift φ).toRingEquiv.toRingHom
          (Units.map (algebraMap E L).toMonoidHom x) : Units L) : L)) =
      ∏ φ : E →ₐ[F] AlgebraicClosure F,
        D.lift φ (algebraMap E L (x : E)) := by
    simp only [Units.coe_prod, Units.coe_map]
    rfl
  rw [hleft, hright, map_prod]
  letI : Algebra.IsSeparable F E :=
    Algebra.isSeparable_tower_bot_of_isSeparable F E L
  calc
    (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F)
        (algebraMap F L (Algebra.norm F (x : E))) =
      algebraMap F (AlgebraicClosure F) (Algebra.norm F (x : E)) := by
        exact (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F).commutes _
    _ = ∏ φ : E →ₐ[F] AlgebraicClosure F, φ (x : E) :=
      Algebra.norm_eq_prod_embeddings F (AlgebraicClosure F) (x : E)
    _ = ∏ φ : E →ₐ[F] AlgebraicClosure F,
        (IsAlgClosed.lift : L →ₐ[F] AlgebraicClosure F)
          (D.lift φ (algebraMap E L (x : E))) := by
      apply Finset.prod_congr rfl
      intro φ _
      exact (D.lift_restrict φ (x : E)).symm

private theorem finiteReciprocity_rowSum_coset
    (F E L : Type)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L]
    (D : FiniteReciprocityGaloisEmbeddingDecomposition F E L)
    (X : Rep ℤ (L ≃ₐ[F] L)) (a : Inhomogeneous.C2 X)
    (ha : Inhomogeneous.d2 X a = 0) (σ : L ≃ₐ[E] L) :
    (∑ φ : E →ₐ[F] AlgebraicClosure F,
      X.ρ (D.lift φ)
        (∑ h : L ≃ₐ[E] L,
          a ((AlgEquiv.restrictScalarsHom F :
              (L ≃ₐ[E] L) →* (L ≃ₐ[F] L)) h)
            ((AlgEquiv.restrictScalarsHom F :
              (L ≃ₐ[E] L) →* (L ≃ₐ[F] L)) σ))) =
      ∑ g : L ≃ₐ[F] L, a g ((AlgEquiv.restrictScalarsHom F :
        (L ≃ₐ[E] L) →* (L ≃ₐ[F] L)) σ) := by
  let s : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L) := AlgEquiv.restrictScalarsHom F
  have hc (φ : E →ₐ[F] AlgebraicClosure F) (h : L ≃ₐ[E] L) :
      X.ρ (D.lift φ) (a (s h) (s σ)) =
        a (D.lift φ * s h) (s σ) - a (D.lift φ) (s (h * σ)) +
          a (D.lift φ) (s h) := by
    have hz := congrFun (congrFun (congrFun ha (D.lift φ)) (s h)) (s σ)
    change X.ρ (D.lift φ) (a (s h) (s σ)) -
      a (D.lift φ * s h) (s σ) + a (D.lift φ) (s h * s σ) -
        a (D.lift φ) (s h) = 0 at hz
    rw [← map_mul] at hz
    calc
      X.ρ (D.lift φ) (a (s h) (s σ)) =
          (X.ρ (D.lift φ) (a (s h) (s σ)) -
            a (D.lift φ * s h) (s σ) + a (D.lift φ) (s (h * σ)) -
              a (D.lift φ) (s h)) +
            a (D.lift φ * s h) (s σ) - a (D.lift φ) (s (h * σ)) +
              a (D.lift φ) (s h) := by abel
      _ = a (D.lift φ * s h) (s σ) - a (D.lift φ) (s (h * σ)) +
              a (D.lift φ) (s h) := by rw [hz]; abel
  calc
    (∑ φ : E →ₐ[F] AlgebraicClosure F,
      X.ρ (D.lift φ) (∑ h : L ≃ₐ[E] L, a (s h) (s σ))) =
      ∑ φ : E →ₐ[F] AlgebraicClosure F,
        ∑ h : L ≃ₐ[E] L, X.ρ (D.lift φ) (a (s h) (s σ)) := by
      apply Finset.sum_congr rfl
      intro φ _
      rw [map_sum]
    _ =
      ∑ φ : E →ₐ[F] AlgebraicClosure F,
        ∑ h : L ≃ₐ[E] L,
          (a (D.lift φ * s h) (s σ) - a (D.lift φ) (s (h * σ)) +
            a (D.lift φ) (s h)) := by
      apply Finset.sum_congr rfl
      intro φ _
      apply Finset.sum_congr rfl
      intro h _
      exact hc φ h
    _ = ∑ φ : E →ₐ[F] AlgebraicClosure F,
        ∑ h : L ≃ₐ[E] L, a (D.lift φ * s h) (s σ) := by
      apply Finset.sum_congr rfl
      intro φ _
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hreindex : (∑ h : L ≃ₐ[E] L, a (D.lift φ) (s (h * σ))) =
          ∑ h : L ≃ₐ[E] L, a (D.lift φ) (s h) := by
        simpa using Equiv.sum_comp (Equiv.mulRight σ)
          (fun h : L ≃ₐ[E] L => a (D.lift φ) (s h))
      rw [hreindex]
      abel
    _ = ∑ g : L ≃ₐ[F] L, a g (s σ) := by
      calc
        (∑ φ : E →ₐ[F] AlgebraicClosure F,
            ∑ h : L ≃ₐ[E] L, a (D.lift φ * s h) (s σ)) =
          ∑ p : (E →ₐ[F] AlgebraicClosure F) × (L ≃ₐ[E] L),
            a (D.lift p.1 * s p.2) (s σ) :=
              (Fintype.sum_prod_type' (fun φ h =>
                a (D.lift φ * s h) (s σ))).symm
        _ = ∑ g : L ≃ₐ[F] L, a g (s σ) :=
          Fintype.sum_equiv D.equiv _ _ (fun p => by rw [D.equiv_apply])

private theorem finiteReciprocity_compensated_norm_typeZero
    (F E L : Type)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L] [IsGalois E L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F E] [ValuativeExtension E L] [ValuativeExtension F L]
    [ContinuousSMul F E] [ContinuousSMul E L] [ContinuousSMul F L] :
    (MonoidHom.toAdditive (normOnQuotient F E L)).comp
        (FiniteReciprocity.compensatedNormTateEquiv E L).toAddMonoidHom =
      (FiniteReciprocity.compensatedNormTateEquiv F L).toAddMonoidHom.comp
        (MonoidHom.toAdditive (inclusionAb F E L)) := by
  classical
  let CG := FiniteReciprocity.cohomologicalConstruction F L
  let CH := FiniteReciprocity.cohomologicalConstruction E L
  let a := CG.cocycle
  let ha := CG.cocycle_mem
  obtain ⟨R, hR⟩ := fundamentalClass_restriction F L E
  let aR := transportedC2 R.subgroupHom R.coefficient a
  let haR := FiniteReciprocity.finiteReciprocity_transportedC2_mem
    R.subgroupHom R.coefficient a ha
  have hclassR : AbstractReciprocity.cocycleClass2 (MulRep E L) aR haR =
      fundamentalClassValue E L := by
    calc
      AbstractReciprocity.cocycleClass2 (MulRep E L) aR haR =
          transportedH2 R.subgroupHom R.coefficient
            (AbstractReciprocity.cocycleClass2 (MulRep F L) a ha) :=
        (FiniteReciprocity.finiteReciprocity_transportedH2_cocycleClass_eq
          R.subgroupHom R.coefficient a ha).symm
      _ = transportedH2 R.subgroupHom R.coefficient
          (fundamentalClassValue F L) := congrArg _ CG.represents
      _ = fundamentalClassValue E L := hR
  have hcoh : AbstractReciprocity.Cohomologous2 (MulRep E L) aR CH.cocycle :=
    FiniteReciprocity.finiteReciprocity_cohomologous2_of_cocycleClass_eq
      (MulRep E L) aR CH.cocycle haR CH.cocycle_mem
        (hclassR.trans CH.represents.symm)
  let s : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L) := AlgEquiv.restrictScalarsHom F
  have hs (σ : L ≃ₐ[E] L) : R.subgroupHom σ = s σ := by
    apply AlgEquiv.ext
    intro x
    exact R.subgroupHom_apply σ x
  have hc (x : Additive (Units L)) : R.coefficient.hom x = x := by
    change R.coefficient.hom (Additive.ofMul (Additive.toMul x)) = x
    exact R.coefficient_apply (Additive.toMul x)
  have haR_apply (σ τ : L ≃ₐ[E] L) : aR σ τ = a (s σ) (s τ) := by
    change R.coefficient.hom (a (R.subgroupHom σ) (R.subgroupHom τ)) = _
    rw [hs, hs, hc]
  let D := finiteReciprocityGaloisEmbeddingDecomposition F E L
  have hgenerator (σ : L ≃ₐ[E] L) :
      MonoidHom.toAdditive (normOnQuotient F E L)
          (FiniteReciprocity.compensatedNormTateEquiv E L
            (Additive.ofMul (Abelianization.of σ))) =
        FiniteReciprocity.compensatedNormTateEquiv F L
          (MonoidHom.toAdditive (inclusionAb F E L)
            (Additive.ofMul (Abelianization.of σ))) := by
    let rR := AbstractReciprocity.rowSumInvariant (MulRep E L) aR haR σ
    let x : Units E := Additive.toMul
      (FiniteReciprocity.explicitMulRepInvariantsEquiv E L rR)
    have hx : FiniteReciprocity.baseUnitInvariant E L x = rR := by
      apply (FiniteReciprocity.explicitMulRepInvariantsEquiv E L).injective
      rw [FiniteReciprocity.explicitMulRepInvariantsEquiv_baseUnit E L]
      rfl
    have hrows := AbstractReciprocity.rowSumClass_coboundary_independent
      (MulRep E L) aR CH.cocycle haR CH.cocycle_mem hcoh σ
    have hqH : AbstractReciprocity.rowSumClass (MulRep E L)
        CH.cocycle CH.cocycle_mem σ =
          FiniteReciprocity.tateClassOfBaseUnit E L x := by
      rw [← hrows]
      change QuotientAddGroup.mk rR =
        QuotientAddGroup.mk (FiniteReciprocity.baseUnitInvariant E L x)
      rw [hx]
    have hevalH : FiniteReciprocity.compensatedNormTateEquiv E L
        (Additive.ofMul (Abelianization.of σ)) =
          Additive.ofMul (QuotientGroup.mk x : Units E ⧸ normSubgroup E L) := by
      rw [FiniteReciprocity.compensatedNormTateEquiv_eq_abstractReciprocity]
      rw [FiniteReciprocity.cohomologicalCompensatedNormTateEquiv,
        AddEquiv.trans_apply, FiniteReciprocity.cohomologicalCompensatedTate_apply,
        hqH]
      exact CH.tateQuotient_apply x
    let y : Units F := normUnitsHom F E x
    have hrestricted : (∑ h : L ≃ₐ[E] L, a (s h) (s σ)) = rR.1 := by
      change (∑ h : L ≃ₐ[E] L, a (s h) (s σ)) = ∑ h : L ≃ₐ[E] L, aR h σ
      apply Finset.sum_congr rfl
      intro h _
      exact (haR_apply h σ).symm
    have hnormAdd : Additive.ofMul
        (Units.map (algebraMap F L).toMonoidHom y) =
        ∑ φ : E →ₐ[F] AlgebraicClosure F,
          (MulRep F L).ρ (D.lift φ)
            (Additive.ofMul (Units.map (algebraMap E L).toMonoidHom x)) := by
      apply Additive.toMul.injective
      change Units.map (algebraMap F L).toMonoidHom y =
        ∏ φ : E →ₐ[F] AlgebraicClosure F,
          Units.map (D.lift φ).toRingEquiv.toRingHom
            (Units.map (algebraMap E L).toMonoidHom x)
      exact finiteReciprocity_normUnitsHom_eq_embeddingProduct F E L D x
    have hxval : Additive.ofMul (Units.map (algebraMap E L).toMonoidHom x) = rR.1 :=
      congrArg Subtype.val hx
    have hrow := finiteReciprocity_rowSum_coset F E L D (MulRep F L) a ha.1 σ
    have hxsum : (show (MulRep F L).V from
        Additive.ofMul (Units.map (algebraMap E L).toMonoidHom x)) =
          ∑ h : L ≃ₐ[E] L, a (s h) (s σ) := by
      exact hxval.trans hrestricted.symm
    have hreplace := congrArg
      (fun z : (MulRep F L).V =>
        ∑ φ : E →ₐ[F] AlgebraicClosure F, (MulRep F L).ρ (D.lift φ) z) hxsum
    have hbase : FiniteReciprocity.baseUnitInvariant F L y =
        AbstractReciprocity.rowSumInvariant (MulRep F L) a ha (s σ) := by
      apply Subtype.ext
      change Additive.ofMul (Units.map (algebraMap F L).toMonoidHom y) =
        ∑ g : L ≃ₐ[F] L, a g (s σ)
      exact hnormAdd.trans (hreplace.trans hrow)
    have hqG : AbstractReciprocity.rowSumClass (MulRep F L) a ha (s σ) =
        FiniteReciprocity.tateClassOfBaseUnit F L y := by
      change QuotientAddGroup.mk
          (AbstractReciprocity.rowSumInvariant (MulRep F L) a ha (s σ)) =
        QuotientAddGroup.mk (FiniteReciprocity.baseUnitInvariant F L y)
      rw [hbase]
    have hevalG : FiniteReciprocity.compensatedNormTateEquiv F L
        (Additive.ofMul (Abelianization.of (s σ))) =
          Additive.ofMul (QuotientGroup.mk y : Units F ⧸ normSubgroup F L) := by
      rw [FiniteReciprocity.compensatedNormTateEquiv_eq_abstractReciprocity]
      rw [FiniteReciprocity.cohomologicalCompensatedNormTateEquiv,
        AddEquiv.trans_apply, FiniteReciprocity.cohomologicalCompensatedTate_apply,
        hqG]
      exact CG.tateQuotient_apply y
    rw [hevalH]
    change Additive.ofMul (normOnQuotient F E L (QuotientGroup.mk x)) = _
    rw [normOnQuotient_mk]
    change Additive.ofMul (QuotientGroup.mk y) = _
    rw [show MonoidHom.toAdditive (inclusionAb F E L)
        (Additive.ofMul (Abelianization.of σ)) =
      Additive.ofMul (Abelianization.of (s σ)) by rfl]
    exact hevalG.symm
  apply AddMonoidHom.ext
  intro z
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
  have hz : z = Additive.ofMul (Abelianization.of σ) := by
    apply Additive.toMul.injective
    exact hσ.symm
  rw [hz]
  exact hgenerator σ

private theorem finiteReciprocity_normalized_transport
    (A B A' B' : Type)
    [Field A] [Field B] [Algebra A B]
    [FiniteDimensional A B] [IsGalois A B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeExtension A B] [ContinuousSMul A B]
    [Field A'] [Field B'] [Algebra A' B']
    [FiniteDimensional A' B'] [IsGalois A' B']
    [ValuativeRel A'] [TopologicalSpace A'] [IsNonarchimedeanLocalField A']
    [ValuativeRel B'] [TopologicalSpace B'] [IsNonarchimedeanLocalField B']
    [ValuativeExtension A' B'] [ContinuousSMul A' B']
    (b : A ≃+* A') (e : B ≃+* B')
    (h : ∀ x : A, e (algebraMap A B x) = algebraMap A' B' (b x))
    (hb : ∀ x : Units A,
      normalizedValuation A' (Units.map b.toRingHom x) = normalizedValuation A x)
    (he : ∀ x : Units B,
      normalizedValuation B' (Units.map e.toRingHom x) = normalizedValuation B x) :
    (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A B).trans
        (FiniteReciprocity.normQuotientTransportEquiv b e h).toAdditive =
      (FiniteReciprocity.galoisTransportEquiv b e h).abelianizationCongr.toAdditive.trans
        (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A' B') := by
  let model : FiniteReciprocity.UniverseZeroLocalFieldModel :=
    { K₀ := A'
      L₀ := B'
      fieldK₀ := inferInstance
      fieldL₀ := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      valuativeRelK₀ := inferInstance
      topologyK₀ := inferInstance
      localFieldK₀ := inferInstance
      valuativeRelL₀ := inferInstance
      topologyL₀ := inferInstance
      localFieldL₀ := inferInstance
      valuativeExtension := inferInstance
      continuousSMul := inferInstance }
  let gt := FiniteReciprocity.galoisTransportEquiv b e h
  let abT : Additive (Abelianization (B ≃ₐ[A] B)) ≃+
      Additive (Abelianization (B' ≃ₐ[A'] B')) := gt.abelianizationCongr.toAdditive
  let nt : Additive (Units A ⧸ normSubgroup A B) ≃+
      Additive (Units A' ⧸ normSubgroup A' B') :=
    (FiniteReciprocity.normQuotientTransportEquiv b e h).toAdditive
  let normalized :=
    FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A' B'
  let raw : Additive (Abelianization (B ≃ₐ[A] B)) ≃+
      Additive (Units A ⧸ normSubgroup A B) :=
    (abT.trans normalized).trans nt.symm
  let UB : FiniteReciprocity.UniverseBridge A B raw :=
    { model := model
      baseEquiv := b
      extensionEquiv := e
      algebra_compatibility := h
      galoisTransport := gt
      galoisTransport_apply := fun σ x =>
        (FiniteReciprocity.galoisTransportEquiv_apply b e h σ x).symm
      abelianizationTransport := abT
      abelianizationTransport_of := fun _ => rfl
      normQuotientTransport := nt
      normQuotientTransport_mk := fun x =>
        FiniteReciprocity.normQuotientTransportEquiv_mk b e h x
      base_valuation := hb
      extension_valuation := he
      raw_eq_normalizedFundamentalClass := by
        change raw.trans nt = abT.trans normalized
        apply AddEquiv.ext
        intro z
        change nt (nt.symm (normalized (abT z))) = normalized (abT z)
        exact nt.apply_symm_apply _ }
  exact FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv_bridge A B UB

private theorem finiteReciprocity_compensated_eq_normalized
    (A B : Type)
    [Field A] [Field B] [Algebra A B]
    [FiniteDimensional A B] [IsGalois A B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeExtension A B] [ContinuousSMul A B] :
    FiniteReciprocity.compensatedNormTateEquiv A B =
      (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A B).trans
        (AddEquiv.neg (Additive (Units A ⧸ normSubgroup A B))) := by
  rw [FiniteReciprocity.compensatedNormTateEquiv_eq_abstractReciprocity,
    FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv_def]
  apply AddEquiv.ext
  intro z
  change (FiniteReciprocity.cohomologicalConstruction A B).tateQuotient
      (-(FiniteReciprocity.cohomologicalRawTateEquiv A B z)) =
    -((FiniteReciprocity.cohomologicalConstruction A B).tateQuotient
      (FiniteReciprocity.cohomologicalRawTateEquiv A B z))
  exact @AddEquiv.map_neg
    (TateLowDegree.H0 (MulRep A B))
    (Additive (Units A ⧸ normSubgroup A B))
    inferInstance inferInstance
    (FiniteReciprocity.cohomologicalConstruction A B).tateQuotient
    (FiniteReciprocity.cohomologicalRawTateEquiv A B z)

private theorem finiteReciprocity_compensated_transport
    (A : Type u) (B : Type v) (A' B' : Type)
    [Field A] [Field B] [Algebra A B]
    [FiniteDimensional A B] [IsGalois A B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeExtension A B] [ContinuousSMul A B]
    [Field A'] [Field B'] [Algebra A' B']
    [FiniteDimensional A' B'] [IsGalois A' B']
    [ValuativeRel A'] [TopologicalSpace A'] [IsNonarchimedeanLocalField A']
    [ValuativeRel B'] [TopologicalSpace B'] [IsNonarchimedeanLocalField B']
    [ValuativeExtension A' B'] [ContinuousSMul A' B']
    (b : A ≃+* A') (e : B ≃+* B')
    (h : ∀ x : A, e (algebraMap A B x) = algebraMap A' B' (b x))
    (hb : ∀ x : Units A,
      normalizedValuation A' (Units.map b.toRingHom x) = normalizedValuation A x)
    (he : ∀ x : Units B,
      normalizedValuation B' (Units.map e.toRingHom x) = normalizedValuation B x) :
    (FiniteReciprocity.compensatedNormTateEquiv A B).trans
        (FiniteReciprocity.normQuotientTransportEquiv b e h).toAdditive =
      (FiniteReciprocity.galoisTransportEquiv b e h).abelianizationCongr.toAdditive.trans
        (FiniteReciprocity.compensatedNormTateEquiv A' B') := by
  let C := FiniteReciprocity.construction A B
  let U := C.universeBridge
  let gt := FiniteReciprocity.galoisTransportEquiv b e h
  let abT : Additive (Abelianization (B ≃ₐ[A] B)) ≃+
      Additive (Abelianization (B' ≃ₐ[A'] B')) := gt.abelianizationCongr.toAdditive
  let nt : Additive (Units A ⧸ normSubgroup A B) ≃+
      Additive (Units A' ⧸ normSubgroup A' B') :=
    (FiniteReciprocity.normQuotientTransportEquiv b e h).toAdditive
  let cb : A' ≃+* U.model.K₀ := b.symm.trans U.baseEquiv
  let ce : B' ≃+* U.model.L₀ := e.symm.trans U.extensionEquiv
  have hc : ∀ x : A',
      ce (algebraMap A' B' x) = algebraMap U.model.K₀ U.model.L₀ (cb x) := by
    intro x
    calc
      ce (algebraMap A' B' x) =
          U.extensionEquiv (algebraMap A B (b.symm x)) := by
        change U.extensionEquiv (e.symm (algebraMap A' B' x)) = _
        congr 1
        calc
          e.symm (algebraMap A' B' x) =
              e.symm (e (algebraMap A B (b.symm x))) := by
            rw [h (b.symm x), b.apply_symm_apply]
          _ = algebraMap A B (b.symm x) := e.symm_apply_apply _
      _ = algebraMap U.model.K₀ U.model.L₀
          (U.baseEquiv (b.symm x)) := U.algebra_compatibility _
      _ = algebraMap U.model.K₀ U.model.L₀ (cb x) := rfl
  have hcb : ∀ x : Units A',
      normalizedValuation U.model.K₀ (Units.map cb.toRingHom x) =
        normalizedValuation A' x := by
    intro x
    let xA : Units A := Units.map b.symm.toRingHom x
    calc
      normalizedValuation U.model.K₀ (Units.map cb.toRingHom x) =
          normalizedValuation U.model.K₀
            (Units.map U.baseEquiv.toRingHom xA) := by
        congr 1
      _ = normalizedValuation A xA := U.base_valuation xA
      _ = normalizedValuation A'
          (Units.map b.toRingHom xA) := (hb xA).symm
      _ = normalizedValuation A' x := by
        congr 1
        apply Units.ext
        simp [xA]
  have hce : ∀ x : Units B',
      normalizedValuation U.model.L₀ (Units.map ce.toRingHom x) =
        normalizedValuation B' x := by
    intro x
    let xB : Units B := Units.map e.symm.toRingHom x
    calc
      normalizedValuation U.model.L₀ (Units.map ce.toRingHom x) =
          normalizedValuation U.model.L₀
            (Units.map U.extensionEquiv.toRingHom xB) := by
        congr 1
      _ = normalizedValuation B xB := U.extension_valuation xB
      _ = normalizedValuation B'
          (Units.map e.toRingHom xB) := (he xB).symm
      _ = normalizedValuation B' x := by
        congr 1
        apply Units.ext
        simp [xB]
  let gt₂ := FiniteReciprocity.galoisTransportEquiv cb ce hc
  let abT₂ : Additive (Abelianization (B' ≃ₐ[A'] B')) ≃+
      Additive (Abelianization (U.model.L₀ ≃ₐ[U.model.K₀] U.model.L₀)) :=
    gt₂.abelianizationCongr.toAdditive
  let nt₂ : Additive (Units A' ⧸ normSubgroup A' B') ≃+
      Additive (Units U.model.K₀ ⧸ normSubgroup U.model.K₀ U.model.L₀) :=
    (FiniteReciprocity.normQuotientTransportEquiv cb ce hc).toAdditive
  have hnormalized := finiteReciprocity_normalized_transport
    A' B' U.model.K₀ U.model.L₀ cb ce hc hcb hce
  have hntcomp (q : Units A ⧸ normSubgroup A B) :
      Additive.toMul (nt₂ (nt (Additive.ofMul q))) =
        Additive.toMul (U.normQuotientTransport (Additive.ofMul q)) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change FiniteReciprocity.normQuotientTransportEquiv cb ce hc
        (FiniteReciprocity.normQuotientTransportEquiv b e h
          (QuotientGroup.mk x)) =
      Additive.toMul
        (U.normQuotientTransport (Additive.ofMul (QuotientGroup.mk x)))
    rw [FiniteReciprocity.normQuotientTransportEquiv_mk,
      FiniteReciprocity.normQuotientTransportEquiv_mk,
      U.normQuotientTransport_mk]
    congr 1
    apply Units.ext
    simp [cb]
  have hgtcomp (σ : B ≃ₐ[A] B) : gt₂ (gt σ) = U.galoisTransport σ := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := U.extensionEquiv.surjective y
    calc
      gt₂ (gt σ) (U.extensionEquiv x) =
          gt₂ (gt σ) (ce (e x)) := by simp [ce]
      _ = ce (gt σ (e x)) :=
        FiniteReciprocity.galoisTransportEquiv_apply cb ce hc (gt σ) (e x)
      _ = ce (e (σ x)) := by
        rw [FiniteReciprocity.galoisTransportEquiv_apply b e h σ x]
      _ = U.extensionEquiv (σ x) := by simp [ce]
      _ = U.galoisTransport σ (U.extensionEquiv x) :=
        U.galoisTransport_apply σ x
  have habcomp (z : Additive (Abelianization (B ≃ₐ[A] B))) :
      abT₂ (abT z) = U.abelianizationTransport z := by
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    have hz : z = Additive.ofMul (Abelianization.of σ) := by
      apply Additive.toMul.injective
      exact hσ.symm
    rw [hz, U.abelianizationTransport_of]
    change Additive.ofMul (Abelianization.of (gt₂ (gt σ))) =
      Additive.ofMul (Abelianization.of (U.galoisTransport σ))
    rw [hgtcomp]
  have hraw (z : Additive (Abelianization (B ≃ₐ[A] B))) :
      nt (FiniteReciprocity.rawNormTateEquiv A B z) =
        FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A' B' (abT z) := by
    apply nt₂.injective
    apply Additive.toMul.injective
    calc
      Additive.toMul (nt₂ (nt (FiniteReciprocity.rawNormTateEquiv A B z))) =
          Additive.toMul
            (U.normQuotientTransport
              (FiniteReciprocity.rawNormTateEquiv A B z)) :=
        hntcomp (Additive.toMul (FiniteReciprocity.rawNormTateEquiv A B z))
      _ = Additive.toMul
          (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
            U.model.K₀ U.model.L₀ (U.abelianizationTransport z)) := by
        exact congrArg Additive.toMul
          (DFunLike.congr_fun U.raw_eq_normalizedFundamentalClass z)
      _ = Additive.toMul
          (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
            U.model.K₀ U.model.L₀ (abT₂ (abT z))) := by rw [habcomp]
      _ = Additive.toMul
          (nt₂ (FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv
            A' B' (abT z))) := by
        exact congrArg Additive.toMul
          (DFunLike.congr_fun hnormalized (abT z)).symm
  rw [FiniteReciprocity.compensatedNormTateEquiv_def,
    finiteReciprocity_compensated_eq_normalized A' B']
  apply AddEquiv.ext
  intro z
  change nt (-FiniteReciprocity.rawNormTateEquiv A B z) =
    -FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A' B' (abT z)
  calc
    nt (-FiniteReciprocity.rawNormTateEquiv A B z) =
        -nt (FiniteReciprocity.rawNormTateEquiv A B z) := by
      exact @AddEquiv.map_neg
        (Additive (Units A ⧸ normSubgroup A B))
        (Additive (Units A' ⧸ normSubgroup A' B'))
        inferInstance inferInstance nt
        (FiniteReciprocity.rawNormTateEquiv A B z)
    _ = -FiniteReciprocity.normalizedFundamentalClassRawNormTateEquiv A' B' (abT z) :=
      congrArg Neg.neg (hraw z)

private theorem finiteReciprocity_artin_transport
    (A : Type u) (B : Type v) (A' B' : Type)
    [Field A] [Field B] [Algebra A B]
    [FiniteDimensional A B] [IsGalois A B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeExtension A B] [ContinuousSMul A B]
    [Field A'] [Field B'] [Algebra A' B']
    [FiniteDimensional A' B'] [IsGalois A' B']
    [ValuativeRel A'] [TopologicalSpace A'] [IsNonarchimedeanLocalField A']
    [ValuativeRel B'] [TopologicalSpace B'] [IsNonarchimedeanLocalField B']
    [ValuativeExtension A' B'] [ContinuousSMul A' B']
    (b : A ≃+* A') (e : B ≃+* B')
    (h : ∀ x : A, e (algebraMap A B x) = algebraMap A' B' (b x))
    (hb : ∀ x : Units A,
      normalizedValuation A' (Units.map b.toRingHom x) = normalizedValuation A x)
    (he : ∀ x : Units B,
      normalizedValuation B' (Units.map e.toRingHom x) = normalizedValuation B x)
    (q : Units A ⧸ normSubgroup A B) :
    (FiniteReciprocity.galoisTransportEquiv b e h).abelianizationCongr
        (FiniteReciprocity.artin A B q) =
      FiniteReciprocity.artin A' B'
        (FiniteReciprocity.normQuotientTransportEquiv b e h q) := by
  let gt := FiniteReciprocity.galoisTransportEquiv b e h
  let abT : Additive (Abelianization (B ≃ₐ[A] B)) ≃+
      Additive (Abelianization (B' ≃ₐ[A'] B')) := gt.abelianizationCongr.toAdditive
  let nt : Additive (Units A ⧸ normSubgroup A B) ≃+
      Additive (Units A' ⧸ normSubgroup A' B') :=
    (FiniteReciprocity.normQuotientTransportEquiv b e h).toAdditive
  let cA := FiniteReciprocity.compensatedNormTateEquiv A B
  let cA' := FiniteReciprocity.compensatedNormTateEquiv A' B'
  have hcomp := finiteReciprocity_compensated_transport A B A' B' b e h hb he
  have hp := DFunLike.congr_fun hcomp
    (Additive.ofMul (FiniteReciprocity.artin A B q))
  change nt (cA (Additive.ofMul (FiniteReciprocity.artin A B q))) =
    cA' (abT (Additive.ofMul (FiniteReciprocity.artin A B q))) at hp
  have hArtA := DFunLike.congr_fun
    (FiniteReciprocity.artin_defining_equation A B) (Additive.ofMul q)
  change Additive.ofMul (FiniteReciprocity.artin A B q) =
    cA.symm (Additive.ofMul q) at hArtA
  have hcA : cA (Additive.ofMul (FiniteReciprocity.artin A B q)) =
      Additive.ofMul q := by
    rw [hArtA]
    exact cA.apply_symm_apply _
  rw [hcA] at hp
  let q' := FiniteReciprocity.normQuotientTransportEquiv b e h q
  have hArtA' := DFunLike.congr_fun
    (FiniteReciprocity.artin_defining_equation A' B') (Additive.ofMul q')
  change Additive.ofMul (FiniteReciprocity.artin A' B' q') =
    cA'.symm (Additive.ofMul q') at hArtA'
  have hcA' : cA' (Additive.ofMul (FiniteReciprocity.artin A' B' q')) =
      Additive.ofMul q' := by
    rw [hArtA']
    exact cA'.apply_symm_apply _
  apply Additive.ofMul.injective
  change abT (Additive.ofMul (FiniteReciprocity.artin A B q)) =
    Additive.ofMul (FiniteReciprocity.artin A' B' q')
  apply cA'.injective
  calc
    cA' (abT (Additive.ofMul (FiniteReciprocity.artin A B q))) =
        nt (Additive.ofMul q) := hp.symm
    _ = Additive.ofMul q' := rfl
    _ = cA' (Additive.ofMul (FiniteReciprocity.artin A' B' q')) := hcA'.symm

private theorem finiteReciprocity_artin_norm_typeZero
    (F E L : Type)
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [FiniteDimensional F E] [FiniteDimensional E L] [FiniteDimensional F L]
    [IsGalois F L] [IsGalois E L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension F E] [ValuativeExtension E L] [ValuativeExtension F L]
    [ContinuousSMul F E] [ContinuousSMul E L] [ContinuousSMul F L] :
    (inclusionAb F E L).comp (FiniteReciprocity.artin E L).toMonoidHom =
      (FiniteReciprocity.artin F L).toMonoidHom.comp (normOnQuotient F E L) := by
  have hcomp := finiteReciprocity_compensated_norm_typeZero F E L
  apply MonoidHom.ext
  intro z
  apply (FiniteReciprocity.artin F L).symm.injective
  change (FiniteReciprocity.artin F L).symm
      (inclusionAb F E L (FiniteReciprocity.artin E L z)) =
    (FiniteReciprocity.artin F L).symm
      (FiniteReciprocity.artin F L (normOnQuotient F E L z))
  rw [(FiniteReciprocity.artin F L).symm_apply_apply]
  have hz := DFunLike.congr_fun hcomp
    (Additive.ofMul (FiniteReciprocity.artin E L z))
  change Additive.ofMul
      ((FiniteReciprocity.artin F L).symm
        (inclusionAb F E L (FiniteReciprocity.artin E L z))) =
    Additive.ofMul (normOnQuotient F E L z)
  have hArtH := DFunLike.congr_fun
    (FiniteReciprocity.artin_defining_equation E L) (Additive.ofMul z)
  change Additive.ofMul (FiniteReciprocity.artin E L z) =
    (FiniteReciprocity.compensatedNormTateEquiv E L).symm (Additive.ofMul z) at hArtH
  have hcH : FiniteReciprocity.compensatedNormTateEquiv E L
      (Additive.ofMul (FiniteReciprocity.artin E L z)) = Additive.ofMul z := by
    rw [hArtH]
    exact (FiniteReciprocity.compensatedNormTateEquiv E L).apply_symm_apply _
  change MonoidHom.toAdditive (normOnQuotient F E L)
      (FiniteReciprocity.compensatedNormTateEquiv E L
        (Additive.ofMul (FiniteReciprocity.artin E L z))) =
    FiniteReciprocity.compensatedNormTateEquiv F L
      (MonoidHom.toAdditive (inclusionAb F E L)
        (Additive.ofMul (FiniteReciprocity.artin E L z))) at hz
  rw [hcH] at hz
  have hdefG := congrArg
    (fun e : Additive (Units F ⧸ normSubgroup F L) ≃+
        Additive (Abelianization (L ≃ₐ[F] L)) => e.symm)
      (FiniteReciprocity.artin_defining_equation F L)
  change MulEquiv.toAdditive (FiniteReciprocity.artin F L).symm =
    FiniteReciprocity.compensatedNormTateEquiv F L at hdefG
  have hcG : FiniteReciprocity.compensatedNormTateEquiv F L
      (Additive.ofMul
        (inclusionAb F E L (FiniteReciprocity.artin E L z))) =
      Additive.ofMul ((FiniteReciprocity.artin F L).symm
        (inclusionAb F E L (FiniteReciprocity.artin E L z))) := by
    exact (DFunLike.congr_fun hdefG
      (Additive.ofMul
        (inclusionAb F E L (FiniteReciprocity.artin E L z)))).symm
  exact hcG.symm.trans hz.symm

private theorem finiteArtin_norm_core :
    (inclusionAb K E M).comp (FiniteReciprocity.artin E M).toMonoidHom =
      (FiniteReciprocity.artin K M).toMonoidHom.comp (normOnQuotient K E M) := by
  classical
  let DEM := FiniteReciprocity.universeModel (K := E) (L := M)
  let DKM := FiniteReciprocity.universeModel (K := K) (L := M)
  let K₀ := DKM.model.K₀
  let E₀ := DEM.model.K₀
  let M₀ := DKM.model.L₀
  letI fieldK₀ : Field K₀ := DKM.model.fieldK₀
  letI fieldE₀ : Field E₀ := DEM.model.fieldK₀
  letI fieldM₀ : Field M₀ := DKM.model.fieldL₀
  letI vrK₀ : ValuativeRel K₀ := DKM.model.valuativeRelK₀
  letI topK₀ : TopologicalSpace K₀ := DKM.model.topologyK₀
  letI localK₀ : IsNonarchimedeanLocalField K₀ := DKM.model.localFieldK₀
  letI vrE₀ : ValuativeRel E₀ := DEM.model.valuativeRelK₀
  letI topE₀ : TopologicalSpace E₀ := DEM.model.topologyK₀
  letI localE₀ : IsNonarchimedeanLocalField E₀ := DEM.model.localFieldK₀
  letI vrM₀ : ValuativeRel M₀ := DKM.model.valuativeRelL₀
  letI topM₀ : TopologicalSpace M₀ := DKM.model.topologyL₀
  letI localM₀ : IsNonarchimedeanLocalField M₀ := DKM.model.localFieldL₀
  let bK : K ≃+* K₀ := DKM.baseEquiv
  let bE : E ≃+* E₀ := DEM.baseEquiv
  let bM : M ≃+* M₀ := DKM.extensionEquiv
  let eK : K₀ ≃+* K := bK.symm
  let eE : E₀ ≃+* E := bE.symm
  let algHomK₀E₀ : K₀ →+* E₀ := bE.toRingHom.comp
    ((algebraMap K E).comp eK.toRingHom)
  letI algK₀E₀ : Algebra K₀ E₀ := algHomK₀E₀.toAlgebra
  letI algE₀M₀ : Algebra E₀ M₀ := DEM.model.algebra
  letI algK₀M₀ : Algebra K₀ M₀ := DKM.model.algebra
  let semKE : E →ₛₗ[bK.toRingHom] E₀ :=
    { toFun := bE
      map_add' := bE.map_add
      map_smul' := by
        intro c x
        simp only [Algebra.smul_def]
        rw [map_mul, RingHom.algebraMap_toAlgebra]
        simp [algHomK₀E₀, eK] }
  letI rsbK : RingHomSurjective bK.toRingHom := ⟨bK.surjective⟩
  letI fdK₀E₀ : FiniteDimensional K₀ E₀ :=
    Module.Finite.of_surjective semKE bE.surjective
  letI fdE₀M₀ : FiniteDimensional E₀ M₀ := DEM.model.finiteDimensional
  letI fdK₀M₀ : FiniteDimensional K₀ M₀ := DKM.model.finiteDimensional
  letI galK₀M₀ : IsGalois K₀ M₀ := DKM.model.isGalois
  letI galE₀M₀ : IsGalois E₀ M₀ := DEM.model.isGalois
  letI veK₀E₀ : ValuativeExtension K₀ E₀ := by
    constructor
    intro a b
    change eE (algebraMap K₀ E₀ a) ≤ᵥ eE (algebraMap K₀ E₀ b) ↔
      eK a ≤ᵥ eK b
    rw [RingHom.algebraMap_toAlgebra]
    simpa [algHomK₀E₀, eK, eE] using
      (ValuativeExtension.vle_iff_vle (A := K) (B := E)
        (a := eK a) (b := eK b))
  letI veE₀M₀ : ValuativeExtension E₀ M₀ := DEM.model.valuativeExtension
  letI veK₀M₀ : ValuativeExtension K₀ M₀ := DKM.model.valuativeExtension
  have heK : Continuous eK := continuous_induced_dom
  have heE : Continuous eE := continuous_induced_dom
  letI csK₀E₀ : ContinuousSMul K₀ E₀ := ⟨by
    apply (continuous_induced_rng (f := eE)).2
    rw [show (eE ∘ fun p : K₀ × E₀ => p.1 • p.2) =
        fun p => eK p.1 • eE p.2 by
      funext p
      simp only [Function.comp_apply, Algebra.smul_def]
      rw [map_mul, RingHom.algebraMap_toAlgebra]
      simp [algHomK₀E₀, eK, eE]]
    exact (heK.comp continuous_fst).smul (heE.comp continuous_snd)⟩
  letI csE₀M₀ : ContinuousSMul E₀ M₀ := DEM.model.continuousSMul
  letI csK₀M₀ : ContinuousSMul K₀ M₀ := DKM.model.continuousSMul
  have hKE : ∀ x : K,
      bE (algebraMap K E x) = algebraMap K₀ E₀ (bK x) := by
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    simp [algHomK₀E₀, eK]
  have hEM : ∀ x : E,
      bM (algebraMap E M x) = algebraMap E₀ M₀ (bE x) := by
    exact DEM.algebra_compatibility
  have hKM : ∀ x : K,
      bM (algebraMap K M x) = algebraMap K₀ M₀ (bK x) :=
    DKM.algebra_compatibility
  letI stK₀E₀M₀ : IsScalarTower K₀ E₀ M₀ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      obtain ⟨y, rfl⟩ := bK.surjective x
      rw [← hKM y, ← hKE y, ← hEM (algebraMap K E y)]
      congr 1
      exact IsScalarTower.algebraMap_apply K E M y
  let gtEM := FiniteReciprocity.galoisTransportEquiv bE bM hEM
  let gtKM := FiniteReciprocity.galoisTransportEquiv bK bM hKM
  have hgincl (σ : M ≃ₐ[E] M) :
      gtKM (galoisInclusion K E M σ) =
        galoisInclusion K₀ E₀ M₀ (gtEM σ) := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := bM.surjective y
    calc
      gtKM (galoisInclusion K E M σ) (bM x) =
          bM (galoisInclusion K E M σ x) :=
        FiniteReciprocity.galoisTransportEquiv_apply bK bM hKM
          (galoisInclusion K E M σ) x
      _ = bM (σ x) := rfl
      _ = gtEM σ (bM x) :=
        (FiniteReciprocity.galoisTransportEquiv_apply bE bM hEM σ x).symm
      _ = galoisInclusion K₀ E₀ M₀ (gtEM σ) (bM x) := rfl
  have hincl (a : Abelianization (M ≃ₐ[E] M)) :
      gtKM.abelianizationCongr (inclusionAb K E M a) =
        inclusionAb K₀ E₀ M₀ (gtEM.abelianizationCongr a) := by
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective a
    rw [← hσ]
    change Abelianization.of (gtKM (galoisInclusion K E M σ)) =
      Abelianization.of (galoisInclusion K₀ E₀ M₀ (gtEM σ))
    rw [hgincl]
  have hnorm (x : Units E) :
      Units.map bK.toRingHom (normUnitsHom K E x) =
        normUnitsHom K₀ E₀ (Units.map bE.toRingHom x) := by
    apply Units.ext
    change bK (Algebra.norm K (x : E)) =
      Algebra.norm K₀ (bE (x : E))
    have hcomp : (algebraMap K₀ E₀).comp bK.toRingHom =
        bE.toRingHom.comp (algebraMap K E) := by
      ext y
      exact (hKE y).symm
    have hn := Algebra.norm_eq_of_equiv_equiv bK bE hcomp (x : E)
    simpa using congrArg bK hn
  have hzero := finiteReciprocity_artin_norm_typeZero K₀ E₀ M₀
  apply MonoidHom.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | _ x =>
      simp only [MonoidHom.comp_apply, normOnQuotient_mk]
      let x₀ : Units E₀ := Units.map bE.toRingHom x
      have hartEM := finiteReciprocity_artin_transport E M E₀ M₀
        bE bM hEM DEM.base_valuation DKM.extension_valuation
        (QuotientGroup.mk x : Units E ⧸ normSubgroup E M)
      rw [FiniteReciprocity.normQuotientTransportEquiv_mk] at hartEM
      have hartKM := finiteReciprocity_artin_transport K M K₀ M₀
        bK bM hKM DKM.base_valuation DKM.extension_valuation
        (QuotientGroup.mk (normUnitsHom K E x) : Units K ⧸ normSubgroup K M)
      rw [FiniteReciprocity.normQuotientTransportEquiv_mk] at hartKM
      have hz := DFunLike.congr_fun hzero
        (QuotientGroup.mk x₀ : Units E₀ ⧸ normSubgroup E₀ M₀)
      change inclusionAb K₀ E₀ M₀
          (FiniteReciprocity.artin E₀ M₀ (QuotientGroup.mk x₀)) =
        FiniteReciprocity.artin K₀ M₀
          (normOnQuotient K₀ E₀ M₀ (QuotientGroup.mk x₀)) at hz
      rw [normOnQuotient_mk] at hz
      apply gtKM.abelianizationCongr.injective
      calc
        gtKM.abelianizationCongr
            (inclusionAb K E M
              (FiniteReciprocity.artin E M (QuotientGroup.mk x))) =
            inclusionAb K₀ E₀ M₀
              (gtEM.abelianizationCongr
                (FiniteReciprocity.artin E M (QuotientGroup.mk x))) :=
          hincl _
        _ = inclusionAb K₀ E₀ M₀
              (FiniteReciprocity.artin E₀ M₀ (QuotientGroup.mk x₀)) := by
          exact congrArg (inclusionAb K₀ E₀ M₀) hartEM
        _ = FiniteReciprocity.artin K₀ M₀
              (QuotientGroup.mk (normUnitsHom K₀ E₀ x₀)) := hz
        _ = FiniteReciprocity.artin K₀ M₀
              (QuotientGroup.mk
                (Units.map bK.toRingHom (normUnitsHom K E x))) := by
          rw [hnorm]
        _ = gtKM.abelianizationCongr
              (FiniteReciprocity.artin K M
                (QuotientGroup.mk (normUnitsHom K E x))) := hartKM.symm

/-- **R03**, Proposition `prop:finite-norm-functoriality`: norm and subgroup inclusion commute
with the two actual normalized finite Artin maps. -/
theorem finiteArtin_norm :
    (inclusionAb K E M).comp (FiniteReciprocity.artin E M).toMonoidHom =
      (FiniteReciprocity.artin K M).toMonoidHom.comp (normOnQuotient K E M) := by
  exact finiteArtin_norm_core K E M

end NormFunctoriality

section NormTopology

open Set

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

private theorem normalizedValuation_eq_zero_iff_valuation_eq_one
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x : Units F) :
    normalizedValuation F x = 0 ↔
      ValuativeRel.valuation F (x : F) = 1 := by
  constructor
  · intro hx
    have hxnonneg : 0 ≤ normalizedValuation F x := hx.ge
    have hinvnonneg : 0 ≤ normalizedValuation F x⁻¹ := by
      rw [show normalizedValuation F x⁻¹ = -normalizedValuation F x by
        simp [normalizedValuation], hx]
      norm_num
    obtain ⟨a, ha⟩ := ((exists_normalizedValuationHom F).choose_spec.2 x).mp hxnonneg
    obtain ⟨b, hb⟩ := ((exists_normalizedValuationHom F).choose_spec.2 x⁻¹).mp hinvnonneg
    have hxle : ValuativeRel.valuation F (x : F) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    have hinvle : ValuativeRel.valuation F ((x⁻¹ : Units F) : F) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact hb ▸ b.prop
    have honele : 1 ≤ ValuativeRel.valuation F (x : F) :=
      (inv_le_one₀ ((ValuativeRel.valuation F).pos_iff.mpr x.ne_zero)).mp (by
        simpa only [Units.val_inv_eq_inv_val, map_inv₀] using hinvle)
    exact le_antisymm hxle honele
  · intro hx
    have hxnonneg : 0 ≤ normalizedValuation F x := by
      apply ((exists_normalizedValuationHom F).choose_spec.2 x).mpr
      exact ⟨⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩, rfl⟩
    have hinvnonneg : 0 ≤ normalizedValuation F x⁻¹ := by
      apply ((exists_normalizedValuationHom F).choose_spec.2 x⁻¹).mpr
      refine ⟨⟨((x⁻¹ : Units F) : F), (Valuation.mem_integer_iff _ _).mpr ?_⟩, rfl⟩
      simp [hx]
    have hinv : normalizedValuation F x⁻¹ = -normalizedValuation F x := by
      simp [normalizedValuation]
    rw [hinv] at hinvnonneg
    omega

private theorem normalizedValuation_zero_set_isCompact
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsCompact {x : Units F | normalizedValuation F x = 0} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himage :
      Units.val '' {x : Units F | normalizedValuation F x = 0} =
        {x : F | (ValuativeRel.valuation F).restrict x = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (ValuativeRel.valuation F).restrict_eq_one_iff.mpr
        ((normalizedValuation_eq_zero_iff_valuation_eq_one F y).mp hy)
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        simp at hx
      let y : Units F := Units.mk0 x hx0
      exact ⟨y, (normalizedValuation_eq_zero_iff_valuation_eq_one F y).mpr
        ((ValuativeRel.valuation F).restrict_eq_one_iff.mp hx), rfl⟩
  rw [himage]
  have hO : IsCompact (RingOfIntegers F : Set F) := by
    change IsCompact {x : F | x ∈ RingOfIntegers F}
    simpa only [Subtype.range_coe_subtype] using
      (isCompact_range (continuous_subtype_val : Continuous
        ((↑) : RingOfIntegers F → F)))
  apply IsCompact.of_isClosed_subset hO
    ((ValuativeRel.valuation F).isClosed_sphere 1)
  intro x hx
  exact (Valuation.mem_integer_iff _ _).mpr
    ((ValuativeRel.valuation F).restrict_eq_one_iff.mp hx).le

/-- **R04**, Lemma `lem:norm-open`: the norm subgroup is closed for the actual local-field
topologies. -/
theorem normSubgroup_isClosed : IsClosed (normSubgroup K L : Set (Units K)) := by
  classical
  let V : Subgroup (Units K) := (normalizedValuationHom K).ker
  have hVset : (V : Set (Units K)) =
      {x : Units K | normalizedValuation K x = 0} := by
    ext x
    simp [V, normalizedValuation]
  have hVopen : IsOpen (V : Set (Units K)) := by
    rw [hVset]
    have hs := (ValuativeRel.valuation K).isOpen_sphere (r := 1) one_ne_zero
    have hp := hs.preimage Units.continuous_val
    convert hp using 1
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq,
      (ValuativeRel.valuation K).restrict_eq_one_iff,
      normalizedValuation_eq_zero_iff_valuation_eq_one]
  let N₀ : Subgroup (Units K) := normSubgroup K L ⊓ V
  have hN₀set : (N₀ : Set (Units K)) =
      normUnitsHom K L '' {y : Units L | normalizedValuation L y = 0} := by
    ext x
    constructor
    · intro hx
      have hxN : x ∈ normSubgroup K L := hx.1
      have hx0 : normalizedValuation K x = 0 :=
        (Set.ext_iff.mp hVset x).mp hx.2
      rcases hxN with ⟨y, rfl⟩
      have hy0 : normalizedValuation L y = 0 := by
        have hnorm := normalizedValuation_norm K L y
        rw [hx0] at hnorm
        have hf : 0 < residueDegree K L := by
          dsimp [residueDegree]
          exact (ramificationInvariants_exists K L).choose_spec.choose_spec.2.1
        nlinarith
      exact ⟨y, hy0, rfl⟩
    · rintro ⟨y, hy0, rfl⟩
      constructor
      · exact ⟨y, rfl⟩
      · change normUnitsHom K L y ∈ V
        apply (Set.ext_iff.mp hVset _).mpr
        change normalizedValuation K (normUnitsHom K L y) = 0
        change normalizedValuation L y = 0 at hy0
        rw [normalizedValuation_norm, hy0]
        simp
  have hN₀compact : IsCompact (N₀ : Set (Units K)) := by
    rw [hN₀set]
    exact (normalizedValuation_zero_set_isCompact L).image
      (continuous_normUnitsHom K L)
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  have hN₀closed : IsClosed (N₀ : Set (Units K)) := hN₀compact.isClosed
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm
  · intro x hx
    have hxO : x ∈ (fun y : Units K => x⁻¹ * y) ⁻¹' (V : Set (Units K)) := by
      simp [V]
    have hOopen : IsOpen ((fun y : Units K => x⁻¹ * y) ⁻¹' (V : Set (Units K))) :=
      hVopen.preimage (continuous_const.mul continuous_id)
    obtain ⟨a, haO, haN⟩ := (mem_closure_iff.mp hx _ hOopen hxO)
    have hxaV : x * a⁻¹ ∈ V := by
      have h := V.inv_mem haO
      simpa [mul_comm] using h
    have hxaClosure : x * a⁻¹ ∈ closure (normSubgroup K L : Set (Units K)) := by
      let e := Homeomorph.mulRight a⁻¹
      have hmem : e x ∈ e '' closure (normSubgroup K L : Set (Units K)) :=
        ⟨x, hx, rfl⟩
      rw [e.image_closure] at hmem
      have heN : e '' (normSubgroup K L : Set (Units K)) =
          (normSubgroup K L : Set (Units K)) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact (normSubgroup K L).mul_mem hz ((normSubgroup K L).inv_mem haN)
        · intro hy
          refine ⟨y * a, (normSubgroup K L).mul_mem hy haN, ?_⟩
          simp [e]
      rw [heN] at hmem
      exact hmem
    have hxaN₀closure : x * a⁻¹ ∈ closure (N₀ : Set (Units K)) := by
      have hz : x * a⁻¹ ∈ closure
          ((V : Set (Units K)) ∩ (normSubgroup K L : Set (Units K))) :=
        hVopen.inter_closure ⟨hxaV, hxaClosure⟩
      have hsets : (V : Set (Units K)) ∩ (normSubgroup K L : Set (Units K)) =
          (N₀ : Set (Units K)) := by
        ext y
        change (y ∈ V ∧ y ∈ normSubgroup K L) ↔
          (y ∈ normSubgroup K L ∧ y ∈ V)
        exact and_comm
      rwa [hsets] at hz
    have hxaN₀ : x * a⁻¹ ∈ N₀ := by
      rwa [hN₀closed.closure_eq] at hxaN₀closure
    have hxaN : x * a⁻¹ ∈ normSubgroup K L := hxaN₀.1
    have := (normSubgroup K L).mul_mem hxaN haN
    simpa [mul_assoc] using this
  · exact subset_closure

/-- **R04**, Lemma `lem:norm-open`: finite index plus closedness makes the norm subgroup open. -/
theorem normSubgroup_isOpen : IsOpen (normSubgroup K L : Set (Units K)) := by
  letI : Finite (Units K ⧸ normSubgroup K L) :=
    Finite.of_equiv (Abelianization (L ≃ₐ[K] L))
      (FiniteReciprocity.artin K L).symm.toEquiv
  letI : (normSubgroup K L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact (normSubgroup K L).isOpen_of_isClosed_of_finiteIndex
    (normSubgroup_isClosed K L)

end NormTopology
end

end NU.LCFT

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel

universe u v

variable (K : Type u) (Ksep : Type v)
  [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace Ksep]

/-- The chosen Lubin--Tate level, packaged as the finite Galois field proved in L03. -/
noncomputable def lubinTateFiniteGaloisField
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    FiniteGaloisIntermediateField K Ksep := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
  exact FiniteGaloisIntermediateField.mk level.field

/-- The chosen level as a finite abelian extension; abelianity comes from L03, not L02. -/
noncomputable def lubinTateFiniteAbelianExtension
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    FiniteAbelianExtension K Ksep where
  field := lubinTateFiniteGaloisField K Ksep π m hm
  commutative := (lubinTateGaloisData K Ksep π).commutative m hm

/-- The unit `-α_m` singled out by the primitive division point. -/
noncomputable def lubinTateNegGeneratorUnit
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    Units (lubinTateLevel K Ksep π m hm).field :=
  -(lubinTateLevel K Ksep π m hm).generatorUnit

private theorem normGroup_evaluation_C
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) (r : RingOfIntegers K) :
    L.evaluation (PowerSeries.C r) = algebraMap (RingOfIntegers K) L.field r := by
  letI : FiniteDimensional K L.field := L.finiteDimensional
  letI : ValuativeRel L.field := L.localFieldData.valuativeRel
  letI : TopologicalSpace L.field := L.localFieldData.topology
  rw [L.evaluation_apply, tsum_eq_single 0]
  · simp [PowerSeries.coeff_C]
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

private theorem normGroup_evaluation_X
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) :
    L.evaluation PowerSeries.X = L.generator := by
  letI : FiniteDimensional K L.field := L.finiteDimensional
  letI : ValuativeRel L.field := L.localFieldData.valuativeRel
  letI : TopologicalSpace L.field := L.localFieldData.topology
  rw [L.evaluation_apply, tsum_eq_single 1]
  · simp [PowerSeries.coeff_X]
  · intro n hn
    simp [PowerSeries.coeff_X, hn]

private theorem normGroup_evaluation_polynomial
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) (p : Polynomial (RingOfIntegers K)) :
    L.evaluation (p : PowerSeries (RingOfIntegers K)) =
      p.eval₂ (algebraMap (RingOfIntegers K) L.field) L.generator := by
  have hcomp : L.evaluation.comp
      (algebraMap (RingOfIntegers K) (PowerSeries (RingOfIntegers K))) =
      algebraMap (RingOfIntegers K) L.field := by
    apply RingHom.ext
    intro r
    exact normGroup_evaluation_C K Ksep π m hm L r
  have hX : PowerSeries.subst PowerSeries.X
      (p : PowerSeries (RingOfIntegers K)) =
        (p : PowerSeries (RingOfIntegers K)) := PowerSeries.X_subst _
  rw [← hX]
  have hs : PowerSeries.HasSubst
      (PowerSeries.X : PowerSeries (RingOfIntegers K)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero PowerSeries.constantCoeff_X
  rw [PowerSeries.subst_coe hs, Polynomial.aeval_def, Polynomial.hom_eval₂,
    hcomp, normGroup_evaluation_X K Ksep π m hm L]

private theorem normGroup_one_lt_residueCard : 1 < residueCard K := by
  letI := Fintype.ofFinite (LocalResidueField K)
  change 1 < Nat.card (LocalResidueField K)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

private theorem normGroup_uniformizerInteger_ne_zero (π : Uniformizer K) :
    uniformizerInteger K π ≠ 0 := by
  intro h
  apply π.val.ne_zero
  rw [← (uniformizer_integer_exists K π).choose_spec]
  exact congr_arg (fun x : RingOfIntegers K => (x : K)) h

private theorem normGroup_lubinTatePolynomial_monic_natDegree (π : Uniformizer K) :
    (lubinTatePolynomial K π).Monic ∧
      (lubinTatePolynomial K π).natDegree = residueCard K := by
  have hp := normGroup_uniformizerInteger_ne_zero K π
  have hq := normGroup_one_lt_residueCard K
  have hmonic : (lubinTatePolynomial K π).Monic := by
    rw [lubinTatePolynomial]
    apply (Polynomial.monic_X_pow (residueCard K)).add_of_right
    rw [Polynomial.degree_C_mul_X hp, Polynomial.degree_X_pow]
    exact_mod_cast hq
  refine ⟨hmonic, ?_⟩
  rw [lubinTatePolynomial, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · rw [Polynomial.natDegree_X_pow]
  · rw [Polynomial.natDegree_C_mul_X _ hp, Polynomial.natDegree_X_pow]
    exact hq

private theorem normGroup_lubinTateIterate_monic_natDegree
    (π : Uniformizer K) (n : ℕ) :
    (lubinTateIterate K π n).Monic ∧
      (lubinTateIterate K π n).natDegree = residueCard K ^ n := by
  induction n with
  | zero => simp [lubinTateIterate]
  | succ n ih =>
      have hf := normGroup_lubinTatePolynomial_monic_natDegree K π
      constructor
      · rw [lubinTateIterate]
        exact hf.1.comp ih.1 (by
          rw [ih.2]
          exact pow_ne_zero _
            (Nat.ne_of_gt (Nat.zero_lt_one.trans (normGroup_one_lt_residueCard K))))
      · rw [lubinTateIterate, Polynomial.natDegree_comp, hf.2, ih.2, pow_succ']

private theorem normGroup_primitive_monic_natDegree
    (π : Uniformizer K) (m : ℕ) :
    (primitiveDivisionPolynomial K π m).Monic ∧
      (primitiveDivisionPolynomial K π m).natDegree =
        (residueCard K - 1) * residueCard K ^ (m - 1) := by
  let d := (residueCard K - 1) * residueCard K ^ (m - 1)
  have hp := normGroup_uniformizerInteger_ne_zero K π
  have hq := normGroup_one_lt_residueCard K
  have hi := normGroup_lubinTateIterate_monic_natDegree K π (m - 1)
  have hpow : ((lubinTateIterate K π (m - 1)) ^ (residueCard K - 1)).Monic :=
    hi.1.pow _
  have hd : 0 < d :=
    mul_pos (Nat.sub_pos_of_lt hq) (pow_pos (Nat.zero_lt_one.trans hq) _)
  have hmonic : (primitiveDivisionPolynomial K π m).Monic := by
    rw [primitiveDivisionPolynomial]
    apply hpow.add_of_right
    rw [Polynomial.degree_C hp, Polynomial.degree_eq_natDegree hpow.ne_zero,
      Polynomial.natDegree_pow, hi.2]
    exact_mod_cast hd
  refine ⟨hmonic, ?_⟩
  rw [primitiveDivisionPolynomial,
    Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow, hi.2]
  · rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, hi.2]
    exact hd

private theorem normGroup_primitive_constantCoeff
    (π : Uniformizer K) (m : ℕ) :
    (primitiveDivisionPolynomial K π m).constantCoeff = uniformizerInteger K π := by
  have hit : (lubinTateIterate K π (m - 1)).constantCoeff = 0 := by
    induction m - 1 with
    | zero => simp [lubinTateIterate, Polynomial.coeff_zero_eq_eval_zero]
    | succ n ih =>
        change (lubinTateIterate K π n).coeff 0 = 0 at ih
        change ((lubinTatePolynomial K π).comp
          (lubinTateIterate K π n)).coeff 0 = 0
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
          ← Polynomial.coeff_zero_eq_eval_zero, ih]
        simp [lubinTatePolynomial]
        exact Nat.card_pos.ne'
  have hne : residueCard K - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (normGroup_one_lt_residueCard K)).ne'
  rw [primitiveDivisionPolynomial, map_add, map_pow, hit, zero_pow hne, add_zero]
  simp

private theorem normGroup_level_minpoly
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) :
    minpoly K L.generator =
      (primitiveDivisionPolynomial K π m).map
        (algebraMap (RingOfIntegers K) K) := by
  letI : FiniteDimensional K L.field := L.finiteDimensional
  let P := primitiveDivisionPolynomial K π m
  let PK := P.map (algebraMap (RingOfIntegers K) K)
  have hPmonic : P.Monic := (normGroup_primitive_monic_natDegree K π m).1
  have hPirr : Irreducible P :=
    (primitiveDivisionPolynomial_eisenstein K Ksep π m hm).1.irreducible
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime hPmonic.isPrimitive
      (by
        rw [(primitiveDivisionPolynomial_eisenstein K Ksep π m hm).2.1]
        exact mul_pos (Nat.sub_pos_of_lt (normGroup_one_lt_residueCard K))
          (pow_pos (Nat.zero_lt_one.trans (normGroup_one_lt_residueCard K)) _))
  have hPKmonic : PK.Monic := hPmonic.map _
  have hPKirr : Irreducible PK :=
    hPmonic.irreducible_iff_irreducible_map_fraction_map.mp hPirr
  have hroot_sep : (PK.map (algebraMap K Ksep)).IsRoot
      ((L.generator : L.field) : Ksep) := by
    dsimp only [PK, P]
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq
      (RingOfIntegers K) K Ksep]
    exact L.isRoot
  have hroot : Polynomial.aeval L.generator PK = 0 := by
    apply (algebraMap L.field Ksep).injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      ← IsScalarTower.algebraMap_eq K L.field Ksep]
    simpa [Polynomial.eval_map] using hroot_sep
  exact (minpoly.eq_of_irreducible_of_monic hPKirr hroot hPKmonic).symm

private noncomputable def normGroup_levelPowerBasis
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) : PowerBasis K L.field := by
  letI : FiniteDimensional K L.field := L.finiteDimensional
  have hint : IsIntegral K L.generator := IsIntegral.of_finite K L.generator
  have hfield : IntermediateField.adjoin K {L.generator} = ⊤ := by
    apply IntermediateField.lift_injective L.field
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    exact L.field_eq_adjoin.symm
  exact PowerBasis.ofAdjoinEqTop hint
    ((IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hint.isAlgebraic).mp hfield)

private theorem normGroup_levelPowerBasis_gen
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (L : LubinTateLevel K Ksep π m) :
    (normGroup_levelPowerBasis K Ksep π m hm L).gen = L.generator := by
  simp [normGroup_levelPowerBasis]

private theorem normGroup_negGenerator_norm
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    normUnitsHom K level.field (-level.generatorUnit) = π.val := by
  dsimp only
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  let pb := normGroup_levelPowerBasis K Ksep π m hm level
  have hpbgen : pb.gen = level.generator :=
    normGroup_levelPowerBasis_gen K Ksep π m hm level
  have hdim : pb.dim = Module.finrank K level.field := pb.finrank.symm
  apply Units.ext
  change Algebra.norm K (-((level.generatorUnit : Units level.field) : level.field)) =
    (π.val : K)
  have hπ : algebraMap (RingOfIntegers K) K (uniformizerInteger K π) =
      (π.val : K) := (uniformizer_integer_exists K π).choose_spec
  rw [show -((level.generatorUnit : Units level.field) : level.field) =
      algebraMap K level.field (-1) * pb.gen by
        rw [hpbgen, level.generatorUnit_val]
        simp]
  rw [map_mul, Algebra.norm_algebraMap,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hpbgen,
    normGroup_level_minpoly K Ksep π m hm level, Polynomial.coeff_map,
    show (primitiveDivisionPolynomial K π m).coeff 0 = uniformizerInteger K π by
      simpa using normGroup_primitive_constantCoeff K π m,
    hπ]
  rw [hdim, ← mul_assoc, ← pow_add,
    (Even.add_self (Module.finrank K level.field)).neg_one_pow, one_mul]

private theorem normGroup_integralUnit_evaluation
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
    ∀ u : Units (RingOfIntegers level.field),
      ∃ g : Units (PowerSeries (RingOfIntegers K)),
        ringUnitsToFieldUnits level.field u = Units.map level.evaluation.toMonoidHom g := by
  dsimp only
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation level.field) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  intro u
  obtain ⟨p, hp⟩ := level.integral_polynomial_coordinates (u : RingOfIntegers level.field)
  have hgenmax : level.integralGenerator ∈ LocalMaximalIdeal level.field := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    let w : Units (RingOfIntegers level.field) := hunit.unit
    have hw : (w : RingOfIntegers level.field) = level.integralGenerator := hunit.unit_spec
    let x : Units level.field := ringUnitsToFieldUnits level.field w
    have hxinv_nonneg : 0 ≤ normalizedValuation level.field x⁻¹ :=
      (exists_normalizedValuationHom level.field).choose_spec.2 x⁻¹ |>.2
        ⟨(w⁻¹ : Units (RingOfIntegers level.field)), rfl⟩
    have hx : x = level.generatorUnit := by
      apply Units.ext
      change ((w : RingOfIntegers level.field) : level.field) =
        (level.generatorUnit : level.field)
      rw [hw, level.integralGenerator_val, level.generatorUnit_val]
    have hxinv : normalizedValuation level.field x⁻¹ =
        -normalizedValuation level.field x := by
      simp [normalizedValuation]
    rw [hxinv, hx, level.generator_valuation] at hxinv_nonneg
    omega
  have hp0unit : IsUnit (p.coeff 0) := by
    by_contra hp0nonunit
    have hp0max : p.coeff 0 ∈ LocalMaximalIdeal K :=
      (IsLocalRing.mem_maximalIdeal (p.coeff 0)).2 ((mem_nonunits_iff).2 hp0nonunit)
    have hp0lt : ValuativeRel.valuation K (p.coeff 0 : K) < 1 :=
      (Valuation.mem_maximalIdeal_iff K (ValuativeRel.valuation K)).1 hp0max
    have hp0map : level.integerAlgebraMap (p.coeff 0) ∈
        LocalMaximalIdeal level.field := by
      apply (Valuation.mem_maximalIdeal_iff level.field
        (ValuativeRel.valuation level.field)).2
      rw [level.integerAlgebraMap_apply]
      rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K level.field]
      exact (Valuation.HasExtension.val_map_lt_one_iff
        (ValuativeRel.valuation K) (ValuativeRel.valuation level.field) _).2 hp0lt
    let pL : RingOfIntegers level.field :=
      p.eval₂ level.integerAlgebraMap level.integralGenerator
    have hpLval : (pL : level.field) =
        p.eval₂ (algebraMap (RingOfIntegers K) level.field) level.generator := by
      dsimp only [pL]
      change algebraMap (RingOfIntegers level.field) level.field
          (p.eval₂ level.integerAlgebraMap level.integralGenerator) = _
      rw [Polynomial.hom_eval₂]
      have hgen : algebraMap (RingOfIntegers level.field) level.field
          level.integralGenerator = level.generator := level.integralGenerator_val
      rw [hgen]
      have hmap : (algebraMap (RingOfIntegers level.field) level.field).comp
          level.integerAlgebraMap =
          algebraMap (RingOfIntegers K) level.field := by
        apply RingHom.ext
        intro r
        exact level.integerAlgebraMap_apply r
      rw [hmap]
    have hpL : pL = (u : RingOfIntegers level.field) := by
      apply Subtype.ext
      rw [hpLval]
      exact hp
    have hpLmax : pL ∈ LocalMaximalIdeal level.field := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      calc
        Ideal.Quotient.mk (LocalMaximalIdeal level.field) pL =
            Polynomial.eval₂
              ((Ideal.Quotient.mk (LocalMaximalIdeal level.field)).comp
                level.integerAlgebraMap)
              (Ideal.Quotient.mk (LocalMaximalIdeal level.field)
                level.integralGenerator) p := by
                  dsimp only [pL]
                  exact Polynomial.hom_eval₂ p level.integerAlgebraMap
                    (Ideal.Quotient.mk (LocalMaximalIdeal level.field))
                    level.integralGenerator
        _ = Polynomial.eval₂
              ((Ideal.Quotient.mk (LocalMaximalIdeal level.field)).comp
                level.integerAlgebraMap) 0 p := by
                  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hgenmax]
        _ = (Ideal.Quotient.mk (LocalMaximalIdeal level.field))
              (level.integerAlgebraMap (p.coeff 0)) := by
                  rw [Polynomial.eval₂_at_zero]
                  rfl
        _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp0map
    rw [hpL] at hpLmax
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hpLmax)) u.isUnit
  have hpseries : IsUnit (p : PowerSeries (RingOfIntegers K)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa only [Polynomial.constantCoeff_coe] using hp0unit
  let g : Units (PowerSeries (RingOfIntegers K)) := hpseries.unit
  refine ⟨g, ?_⟩
  apply Units.ext
  change (((u : Units (RingOfIntegers level.field)) : RingOfIntegers level.field) :
      level.field) = level.evaluation (g : PowerSeries (RingOfIntegers K))
  rw [show (g : PowerSeries (RingOfIntegers K)) =
      (p : PowerSeries (RingOfIntegers K)) from hpseries.unit_spec]
  rw [normGroup_evaluation_polynomial K Ksep π m hm level]
  exact hp.symm

private theorem normGroup_integralUnit_of_normalizedValuation_eq_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x : Units F)
    (hx : normalizedValuation F x = 0) :
    ∃ u : Units (RingOfIntegers F), ringUnitsToFieldUnits F u = x := by
  obtain ⟨a, ha⟩ := (exists_normalizedValuationHom F).choose_spec.2 x |>.1 hx.ge
  have hxinv : normalizedValuation F x⁻¹ = 0 := by
    have h := normalizedValuation_mul F x x⁻¹
    have hzero : normalizedValuation F 1 = 0 := by
      simp [normalizedValuation]
    rw [mul_inv_cancel, hzero, hx, zero_add] at h
    exact h.symm
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom F).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers F) :=
    { val := a
      inv := b
      val_inv := by apply Subtype.ext; dsimp; rw [ha, hb]; simp
      inv_val := by apply Subtype.ext; dsimp; rw [ha, hb]; simp }
  refine ⟨u, ?_⟩
  apply Units.ext
  exact ha

private theorem normGroup_normalizedValuation_ringUnit
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (u : Units (RingOfIntegers F)) :
    normalizedValuation F (ringUnitsToFieldUnits F u) = 0 := by
  have hnonneg : 0 ≤ normalizedValuation F (ringUnitsToFieldUnits F u) :=
    (exists_normalizedValuationHom F).choose_spec.2 _ |>.2 ⟨u, rfl⟩
  have hinvnonneg : 0 ≤ normalizedValuation F
      (ringUnitsToFieldUnits F u)⁻¹ :=
    (exists_normalizedValuationHom F).choose_spec.2 _ |>.2
      ⟨(u⁻¹ : Units (RingOfIntegers F)), rfl⟩
  have hinv : normalizedValuation F (ringUnitsToFieldUnits F u)⁻¹ =
      -normalizedValuation F (ringUnitsToFieldUnits F u) := by
    simp [normalizedValuation]
  omega

private theorem normGroup_rectangular_index
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    (rectangularSubgroup K π 1 m).index =
      Nat.card (Units (RingOfIntegers K ⧸ LocalMaximalIdeal K ^ m)) := by
  let unitPartField (x : Units K) : Units K :=
    π.val ^ (-normalizedValuation K x) * x
  have unitPartField_val (x : Units K) :
      normalizedValuation K (unitPartField x) = 0 := by
    rw [show unitPartField x = π.val ^ (-normalizedValuation K x) * x from rfl,
      normalizedValuation_mul]
    have hpow : normalizedValuation K (π.val ^ (-normalizedValuation K x)) =
        (-normalizedValuation K x) * normalizedValuation K π.val := by
      simp [normalizedValuation]
    rw [hpow, π.valuation_eq_one]
    simp
  let unitPart (x : Units K) : Units (RingOfIntegers K) :=
    (normGroup_integralUnit_of_normalizedValuation_eq_zero K
      (unitPartField x) (unitPartField_val x)).choose
  have unitPart_spec (x : Units K) :
      ringUnitsToFieldUnits K (unitPart x) = unitPartField x :=
    (normGroup_integralUnit_of_normalizedValuation_eq_zero K
      (unitPartField x) (unitPartField_val x)).choose_spec
  have hmapinj : Function.Injective (ringUnitsToFieldUnits K) :=
    Units.map_injective (fun _ _ h => Subtype.ext h)
  have unitPartField_one : unitPartField 1 = 1 := by
    simp [unitPartField, normalizedValuation]
  have unitPartField_mul (x y : Units K) :
      unitPartField (x * y) = unitPartField x * unitPartField y := by
    dsimp only [unitPartField]
    rw [normalizedValuation_mul, neg_add, zpow_add]
    ac_rfl
  let unitPartHom : Units K →* Units (RingOfIntegers K) :=
    { toFun := unitPart
      map_one' := by
        apply hmapinj
        rw [unitPart_spec, map_one, unitPartField_one]
      map_mul' := fun x y => by
        apply hmapinj
        rw [map_mul, unitPart_spec, unitPart_spec, unitPart_spec,
          unitPartField_mul] }
  have unitPartHom_spec (x : Units K) :
      ringUnitsToFieldUnits K (unitPartHom x) = unitPartField x :=
    unitPart_spec x
  have unitPartHom_ringUnit (u : Units (RingOfIntegers K)) :
      unitPartHom (ringUnitsToFieldUnits K u) = u := by
    apply hmapinj
    rw [unitPartHom_spec]
    simp only [unitPartField, normGroup_normalizedValuation_ringUnit K u, neg_zero,
      zpow_zero, one_mul]
  have unitPartHom_uniformizer : unitPartHom π.val = 1 := by
    apply hmapinj
    rw [unitPartHom_spec, map_one]
    simp [unitPartField, π.valuation_eq_one]
  let reduction : Units K →* Units
      (RingOfIntegers K ⧸ LocalMaximalIdeal K ^ m) :=
    (integralUnitReduction K m).comp unitPartHom
  have reduction_ker : reduction.ker = rectangularSubgroup K π 1 m := by
    apply le_antisymm
    · intro x hx
      change integralUnitReduction K m (unitPartHom x) = 1 at hx
      have hdecomp : x = π.val ^ normalizedValuation K x *
          ringUnitsToFieldUnits K (unitPartHom x) := by
        rw [unitPartHom_spec]
        dsimp only [unitPartField]
        simp
      rw [hdecomp]
      apply Subgroup.mul_mem_sup
      · apply Subgroup.mem_zpowers_iff.mpr
        refine ⟨normalizedValuation K x, ?_⟩
        simp
      · exact ⟨unitPartHom x, hx, rfl⟩
    · rw [rectangularSubgroup]
      apply sup_le
      · rw [Subgroup.zpowers_le]
        change reduction (π.val ^ 1) = 1
        simp only [pow_one]
        change integralUnitReduction K m (unitPartHom π.val) = 1
        rw [unitPartHom_uniformizer, map_one]
      · rintro x ⟨u, hu, rfl⟩
        change integralUnitReduction K m
          (unitPartHom (ringUnitsToFieldUnits K u)) = 1
        rw [unitPartHom_ringUnit, hu]
  have reduction_surjective : Function.Surjective reduction := by
    intro q
    obtain ⟨u, hu⟩ := (lubinTateLevel_galoisEquiv K Ksep π m hm).1 q
    refine ⟨ringUnitsToFieldUnits K u, ?_⟩
    change integralUnitReduction K m
      (unitPartHom (ringUnitsToFieldUnits K u)) = q
    rw [unitPartHom_ringUnit, hu]
  rw [← reduction_ker, Subgroup.index_eq_card]
  exact Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective reduction reduction_surjective).toEquiv

/--
**L06**, Theorem `thm:lt-norm-group`: integral units are actual evaluations at `α_m`, their
norms are the pinned primitive Coleman products in `U_K^m`, and the specific uniformizer
`-α_m` has norm `Q_m(0)=π`.
-/
theorem lubinTate_norm_inclusion
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
    normSubgroup K level.field ≤ rectangularSubgroup K π 1 m ∧
      (∀ u : Units (RingOfIntegers level.field),
        ∃ g : Units (PowerSeries (RingOfIntegers K)),
          ringUnitsToFieldUnits level.field u =
              Units.map level.evaluation.toMonoidHom g ∧
            normUnitsHom K level.field (ringUnitsToFieldUnits level.field u) =
              lubinTatePrimitiveProduct K Ksep π m hm g ∧
            normUnitsHom K level.field (ringUnitsToFieldUnits level.field u) ∈
              principalUnitSubgroup K m) ∧
      normUnitsHom K level.field (lubinTateNegGeneratorUnit K Ksep π m hm) = π.val ∧
      (primitiveDivisionPolynomial K π m).constantCoeff = uniformizerInteger K π := by
  dsimp only
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  have hnegNorm : normUnitsHom K level.field
      (lubinTateNegGeneratorUnit K Ksep π m hm) = π.val := by
    change normUnitsHom K level.field (-level.generatorUnit) = π.val
    exact normGroup_negGenerator_norm K Ksep π m hm
  have hunit (u : Units (RingOfIntegers level.field)) :
      ∃ g : Units (PowerSeries (RingOfIntegers K)),
        ringUnitsToFieldUnits level.field u =
            Units.map level.evaluation.toMonoidHom g ∧
          normUnitsHom K level.field (ringUnitsToFieldUnits level.field u) =
            lubinTatePrimitiveProduct K Ksep π m hm g ∧
          normUnitsHom K level.field (ringUnitsToFieldUnits level.field u) ∈
            principalUnitSubgroup K m := by
    obtain ⟨g, hg⟩ := normGroup_integralUnit_evaluation K Ksep π m hm u
    refine ⟨g, hg, ?_, ?_⟩
    · rw [hg]
      exact (colemanNorm_iteration_product K Ksep π m hm g).2.2.2.2.2.1.symm
    · rw [hg]
      rw [← (colemanNorm_iteration_product K Ksep π m hm g).2.2.2.2.2.1]
      exact (colemanNorm_iteration_product K Ksep π m hm g).2.2.2.2.2.2
  have hinclusion : normSubgroup K level.field ≤ rectangularSubgroup K π 1 m := by
    rintro x ⟨y, rfl⟩
    let ϖ : Units level.field := -level.generatorUnit
    let n : ℤ := normalizedValuation level.field y
    let z : Units level.field := ϖ ^ (-n) * y
    have hϖval : normalizedValuation level.field ϖ = 1 := by
      have hnegone : normalizedValuation level.field (-1 : Units level.field) = 0 := by
        have h := normalizedValuation_mul level.field
          (-1 : Units level.field) (-1 : Units level.field)
        have hone : normalizedValuation level.field 1 = 0 := by
          simp [normalizedValuation]
        rw [show (-1 : Units level.field) * (-1 : Units level.field) = 1 by
          ext
          simp, hone] at h
        omega
      dsimp only [ϖ]
      rw [show -level.generatorUnit =
          (-1 : Units level.field) * level.generatorUnit by
        ext
        simp]
      rw [normalizedValuation_mul, hnegone, zero_add, level.generator_valuation]
    have hzval : normalizedValuation level.field z = 0 := by
      rw [show z = ϖ ^ (-n) * y from rfl, normalizedValuation_mul]
      have hpow : normalizedValuation level.field (ϖ ^ (-n)) =
          (-n) * normalizedValuation level.field ϖ := by
        simp [normalizedValuation]
      rw [hpow, hϖval]
      dsimp only [n]
      simp
    obtain ⟨u, hu⟩ :=
      normGroup_integralUnit_of_normalizedValuation_eq_zero level.field z hzval
    have hy : y = ϖ ^ n * ringUnitsToFieldUnits level.field u := by
      rw [hu]
      dsimp only [z]
      simp
    have hϖnorm : normUnitsHom K level.field ϖ = π.val := by
      dsimp only [ϖ, lubinTateNegGeneratorUnit] at hnegNorm ⊢
      exact hnegNorm
    rw [hy, map_mul, map_zpow, hϖnorm]
    apply Subgroup.mul_mem_sup
    · apply Subgroup.zpow_mem
      simpa using Subgroup.mem_zpowers π.val
    · exact (hunit u).choose_spec.2.2
  exact ⟨hinclusion, hunit, hnegNorm, normGroup_primitive_constantCoeff K π m⟩

/--
**L07**, Theorem `thm:lt-norm-group`: the already-proved finite norm-index theorem turns the
L06 inclusions into `N(K_m^LT/K)=π^ℤ U_K^m`.
-/
theorem lubinTate_normSubgroup
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    normSubgroup K (lubinTateFiniteAbelianExtension K Ksep π m hm).field =
      rectangularSubgroup K π 1 m := by
  let L := lubinTateFiniteAbelianExtension K Ksep π m hm
  let G := L.field ≃ₐ[K] L.field
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := L.commutative }
  have hinclusion : normSubgroup K L.field ≤ rectangularSubgroup K π 1 m := by
    change normSubgroup K (lubinTateLevel K Ksep π m hm).field ≤
      rectangularSubgroup K π 1 m
    exact (lubinTate_norm_inclusion K Ksep π m hm).1
  have hnormIndex : (normSubgroup K L.field).index = Nat.card G := by
    calc
      (normSubgroup K L.field).index = Nat.card (Abelianization G) :=
        normSubgroup_index K Ksep L.field
      _ = Nat.card G :=
        Nat.card_congr (Abelianization.equivOfComm (H := G)).symm.toEquiv
  have hrectIndex : (rectangularSubgroup K π 1 m).index = Nat.card G := by
    rw [normGroup_rectangular_index K Ksep π m hm]
    exact Nat.card_congr (lubinTateGaloisEquiv K Ksep π m hm).toEquiv
  letI : (normSubgroup K L.field).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by
      rw [hnormIndex]
      exact Nat.card_pos.ne')
  apply le_antisymm hinclusion
  by_contra hnot
  have hstrict : normSubgroup K L.field < rectangularSubgroup K π 1 m :=
    lt_iff_le_and_ne.mpr ⟨hinclusion, fun h => hnot h.ge⟩
  have hlt := Subgroup.index_strictAnti hstrict
  rw [hnormIndex, hrectIndex] at hlt
  exact Nat.lt_irrefl _ hlt

end

end NU.LCFT

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel
open ValuativeRel

universe u v

variable (K : Type u) (Ksep : Type v)
  [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace Ksep]

private theorem e01_one_lt_residueCard : 1 < residueCard K := by
  letI := Fintype.ofFinite (LocalResidueField K)
  change 1 < Nat.card (LocalResidueField K)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

private theorem e01_normalizedValuation_ringUnit
    (u : Units (RingOfIntegers K)) :
    normalizedValuation K (ringUnitsToFieldUnits K u) = 0 := by
  have hnonneg : 0 ≤ normalizedValuation K (ringUnitsToFieldUnits K u) :=
    (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
  have hinvnonneg : 0 ≤ normalizedValuation K
      (ringUnitsToFieldUnits K u)⁻¹ :=
    (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
      ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
  have hinv : normalizedValuation K (ringUnitsToFieldUnits K u)⁻¹ =
      -normalizedValuation K (ringUnitsToFieldUnits K u) := by
    simp [normalizedValuation]
  omega

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem e01_principalUnitSubgroup_le_unitSubgroup (b : ℕ) :
    principalUnitSubgroup K b ≤ unitSubgroup K := by
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, rfl⟩

private theorem e01_rectangular_inf_unramified
    (π : Uniformizer K) (a b : ℕ) :
    rectangularSubgroup K π 1 b ⊓ unramifiedRectangularSubgroup K π a =
      rectangularSubgroup K π a b := by
  have hprincipal := e01_principalUnitSubgroup_le_unitSubgroup K b
  have hpow : Subgroup.zpowers (π.val ^ a) ≤ Subgroup.zpowers (π.val ^ 1) := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    refine ⟨(a : ℤ) * k, ?_⟩
    simp [← zpow_natCast, ← zpow_mul]
  ext x
  constructor
  · rintro ⟨hxb, hxa⟩
    change x ∈ Subgroup.zpowers (π.val ^ 1) ⊔ principalUnitSubgroup K b at hxb
    change x ∈ Subgroup.zpowers (π.val ^ a) ⊔ unitSubgroup K at hxa
    obtain ⟨p, hp, u, hu, hpu⟩ := Subgroup.mem_sup.mp hxb
    obtain ⟨q, hq, v, hv, hqv⟩ := Subgroup.mem_sup.mp hxa
    rw [Subgroup.mem_zpowers_iff] at hp hq
    obtain ⟨z, hz⟩ := hp
    obtain ⟨k, hk⟩ := hq
    obtain ⟨ui, hui⟩ := hprincipal hu
    obtain ⟨vi, hvi⟩ := hv
    have hu0 : normalizedValuation K u = 0 := by
      rw [← hui]
      exact e01_normalizedValuation_ringUnit K ui
    have hv0 : normalizedValuation K v = 0 := by
      rw [← hvi]
      exact e01_normalizedValuation_ringUnit K vi
    have hzpow (y : Units K) (n : ℤ) :
        normalizedValuation K (y ^ n) = n * normalizedValuation K y := by
      simp [normalizedValuation]
    have hπpow (n : ℕ) : normalizedValuation K (π.val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation K π.val = _
      rw [π.valuation_eq_one, mul_one]
    have hpval : normalizedValuation K p = z := by
      rw [← hz, hzpow, hπpow]
      simp
    have hqval : normalizedValuation K q = (a : ℤ) * k := by
      rw [← hk, hzpow, hπpow]
      ring
    have hzk : z = (a : ℤ) * k := by
      have hval := congrArg (normalizedValuation K) (hpu.trans hqv.symm)
      rw [normalizedValuation_mul, normalizedValuation_mul, hpval, hqval,
        hu0, hv0, add_zero, add_zero] at hval
      exact hval
    change x ∈ Subgroup.zpowers (π.val ^ a) ⊔ principalUnitSubgroup K b
    apply Subgroup.mem_sup.mpr
    refine ⟨p, ?_, u, hu, hpu⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [← hz, hzk]
    simp [← zpow_natCast, ← zpow_mul]
  · intro hx
    exact ⟨(sup_le_sup hpow le_rfl) hx, (sup_le_sup le_rfl hprincipal) hx⟩

private theorem e01_rectangular_relIndex
    (π : Uniformizer K) (a b : ℕ) :
    (rectangularSubgroup K π a b).relIndex (rectangularSubgroup K π 1 b) = a := by
  let H := rectangularSubgroup K π a b
  let J := rectangularSubgroup K π 1 b
  have hpow : Subgroup.zpowers (π.val ^ a) ≤ Subgroup.zpowers (π.val ^ 1) := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    refine ⟨(a : ℤ) * k, ?_⟩
    simp [← zpow_natCast, ← zpow_mul]
  have hHJ : H ≤ J := sup_le_sup hpow le_rfl
  let valMod : Units K →* Multiplicative (ZMod a) :=
    (Int.castAddHom (ZMod a)).toMultiplicative.comp (normalizedValuationHom K)
  let f : J →* Multiplicative (ZMod a) := valMod.comp J.subtype
  have hzpow (y : Units K) (n : ℤ) :
      normalizedValuation K (y ^ n) = n * normalizedValuation K y := by
    simp [normalizedValuation]
  have hπpow (n : ℕ) : normalizedValuation K (π.val ^ n) = (n : ℤ) := by
    change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ n)) = _
    rw [map_pow, toAdd_pow]
    change (n : ℤ) * normalizedValuation K π.val = _
    rw [π.valuation_eq_one, mul_one]
  have hker : H.subgroupOf J = f.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      change (x : Units K) ∈ Subgroup.zpowers (π.val ^ a) ⊔
        principalUnitSubgroup K b at hx
      obtain ⟨p, hp, u, hu, hpu⟩ := Subgroup.mem_sup.mp hx
      rw [Subgroup.mem_zpowers_iff] at hp
      obtain ⟨k, hk⟩ := hp
      obtain ⟨ui, hui⟩ := (e01_principalUnitSubgroup_le_unitSubgroup K b) hu
      have hu0 : normalizedValuation K u = 0 := by
        rw [← hui]
        exact e01_normalizedValuation_ringUnit K ui
      have hpval : normalizedValuation K p = (a : ℤ) * k := by
        rw [← hk, hzpow, hπpow]
        ring
      have hxval : normalizedValuation K (x : Units K) = (a : ℤ) * k := by
        have hv := congrArg (normalizedValuation K) hpu
        rw [normalizedValuation_mul, hpval, hu0, add_zero] at hv
        exact hv.symm
      apply Multiplicative.toAdd.injective
      change ((normalizedValuation K (x : Units K) : ℤ) : ZMod a) = 0
      rw [hxval, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨k, rfl⟩
    · intro hx
      have hcast : ((normalizedValuation K (x : Units K) : ℤ) : ZMod a) = 0 := by
        have := congrArg Multiplicative.toAdd hx
        change ((normalizedValuation K (x : Units K) : ℤ) : ZMod a) = 0 at this
        exact this
      have hxJ : (x : Units K) ∈ J := x.prop
      change (x : Units K) ∈ Subgroup.zpowers (π.val ^ 1) ⊔
        principalUnitSubgroup K b at hxJ
      obtain ⟨p, hp, u, hu, hpu⟩ := Subgroup.mem_sup.mp hxJ
      rw [Subgroup.mem_zpowers_iff] at hp
      obtain ⟨z, hz⟩ := hp
      obtain ⟨ui, hui⟩ := (e01_principalUnitSubgroup_le_unitSubgroup K b) hu
      have hu0 : normalizedValuation K u = 0 := by
        rw [← hui]
        exact e01_normalizedValuation_ringUnit K ui
      have hpval : normalizedValuation K p = z := by
        rw [← hz, hzpow, hπpow]
        simp
      have hxval : normalizedValuation K (x : Units K) = z := by
        have hv := congrArg (normalizedValuation K) hpu
        rw [normalizedValuation_mul, hpval, hu0, add_zero] at hv
        exact hv.symm
      rw [hxval, ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
      obtain ⟨k, hk⟩ := hcast
      change (x : Units K) ∈ H
      change (x : Units K) ∈ Subgroup.zpowers (π.val ^ a) ⊔
        principalUnitSubgroup K b
      apply Subgroup.mem_sup.mpr
      refine ⟨p, ?_, u, hu, hpu⟩
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      rw [← hz, hk]
      simp [← zpow_natCast, ← zpow_mul]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective y.toAdd
    let p : Units K := π.val ^ z
    have hpJ : p ∈ J := by
      change p ∈ Subgroup.zpowers (π.val ^ 1) ⊔ principalUnitSubgroup K b
      have hp : p ∈ Subgroup.zpowers (π.val ^ 1) := by
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨z, by simp [p]⟩
      exact (show Subgroup.zpowers (π.val ^ 1) ≤
        Subgroup.zpowers (π.val ^ 1) ⊔ principalUnitSubgroup K b from le_sup_left) hp
    refine ⟨⟨p, hpJ⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    change ((normalizedValuation K p : ℤ) : ZMod a) = y.toAdd
    rw [show normalizedValuation K p = z by
      dsimp only [p]
      rw [hzpow, π.valuation_eq_one, mul_one]]
    exact hz
  change (H.subgroupOf J).index = a
  rw [hker, Subgroup.index_ker, (MonoidHom.range_eq_top.mpr hsurj)]
  calc
    Nat.card (↥(⊤ : Subgroup (Multiplicative (ZMod a)))) =
        Nat.card (Multiplicative (ZMod a)) :=
      Nat.card_congr (Equiv.Set.univ (Multiplicative (ZMod a)))
    _ = Nat.card (ZMod a) := Nat.card_congr Multiplicative.toAdd
    _ = a := Nat.card_zmod a

private noncomputable def e01_transportLocalFieldData
    {E F : IntermediateField K Ksep}
    [FiniteDimensional K E] [FiniteDimensional K F]
    (h : E = F) (D : LubinTateLocalFieldData K Ksep E) :
    LubinTateLocalFieldData K Ksep F := by
  subst F
  exact D

private theorem e01_uniformizerInteger_ne_zero (π : Uniformizer K) :
    uniformizerInteger K π ≠ 0 := by
  intro h
  apply π.val.ne_zero
  rw [← (uniformizer_integer_exists K π).choose_spec]
  exact congr_arg (fun x : RingOfIntegers K => (x : K)) h

private theorem e01_lubinTatePolynomial_monic_natDegree (π : Uniformizer K) :
    (lubinTatePolynomial K π).Monic ∧
      (lubinTatePolynomial K π).natDegree = residueCard K := by
  have hp := e01_uniformizerInteger_ne_zero K π
  have hq := e01_one_lt_residueCard K
  have hm : (lubinTatePolynomial K π).Monic := by
    rw [lubinTatePolynomial]
    apply (Polynomial.monic_X_pow (residueCard K)).add_of_right
    rw [Polynomial.degree_C_mul_X hp, Polynomial.degree_X_pow]
    exact_mod_cast hq
  refine ⟨hm, ?_⟩
  rw [lubinTatePolynomial, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · rw [Polynomial.natDegree_X_pow]
  · rw [Polynomial.natDegree_C_mul_X _ hp, Polynomial.natDegree_X_pow]
    exact hq

private theorem e01_lubinTateIterate_monic_natDegree
    (π : Uniformizer K) (n : ℕ) :
    (lubinTateIterate K π n).Monic ∧
      (lubinTateIterate K π n).natDegree = residueCard K ^ n := by
  induction n with
  | zero => simp [lubinTateIterate]
  | succ n ih =>
      have hf := e01_lubinTatePolynomial_monic_natDegree K π
      constructor
      · rw [lubinTateIterate]
        exact hf.1.comp ih.1 (by
          rw [ih.2]
          exact pow_ne_zero _
            (Nat.ne_of_gt (Nat.zero_lt_one.trans (e01_one_lt_residueCard K))))
      · rw [lubinTateIterate, Polynomial.natDegree_comp, hf.2, ih.2, pow_succ']

private theorem e01_primitive_monic_natDegree
    (π : Uniformizer K) (m : ℕ) :
    (primitiveDivisionPolynomial K π m).Monic ∧
      (primitiveDivisionPolynomial K π m).natDegree =
        (residueCard K - 1) * residueCard K ^ (m - 1) := by
  let d := (residueCard K - 1) * residueCard K ^ (m - 1)
  have hp := e01_uniformizerInteger_ne_zero K π
  have hq := e01_one_lt_residueCard K
  have hi := e01_lubinTateIterate_monic_natDegree K π (m - 1)
  have hpow : ((lubinTateIterate K π (m - 1)) ^ (residueCard K - 1)).Monic :=
    hi.1.pow _
  have hd : 0 < d :=
    mul_pos (Nat.sub_pos_of_lt hq) (pow_pos (Nat.zero_lt_one.trans hq) _)
  have hmonic : (primitiveDivisionPolynomial K π m).Monic := by
    rw [primitiveDivisionPolynomial]
    apply hpow.add_of_right
    rw [Polynomial.degree_C hp, Polynomial.degree_eq_natDegree hpow.ne_zero,
      Polynomial.natDegree_pow, hi.2]
    exact_mod_cast hd
  refine ⟨hmonic, ?_⟩
  rw [primitiveDivisionPolynomial,
    Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow, hi.2]
  · rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, hi.2]
    exact hd

private theorem e01_normalizedValuation_inv
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x : Units F) :
    normalizedValuation F x⁻¹ = -normalizedValuation F x := by
  simp [normalizedValuation]

private theorem e01_isUnit_of_normalizedValuation_eq_zero
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (a : RingOfIntegers F) (ha : (a : F) ≠ 0)
    (hval : normalizedValuation F (Units.mk0 (a : F) ha) = 0) : IsUnit a := by
  let x : Units F := Units.mk0 (a : F) ha
  have hxinv : normalizedValuation F x⁻¹ = 0 := by
    rw [e01_normalizedValuation_inv F, hval, neg_zero]
  obtain ⟨c, hc⟩ := (exists_normalizedValuationHom F).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers F) :=
    { val := a
      inv := c
      val_inv := by
        apply Subtype.ext
        change (a : F) * (c : F) = 1
        rw [hc]
        exact mul_inv_cancel₀ ha
      inv_val := by
        apply Subtype.ext
        change (c : F) * (a : F) = 1
        rw [hc]
        exact inv_mul_cancel₀ ha }
  exact ⟨u, rfl⟩

private theorem e01_irreducible_of_normalizedValuation_eq_one
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : RingOfIntegers F) (hp0 : (p : F) ≠ 0)
    (hpval : normalizedValuation F (Units.mk0 (p : F) hp0) = 1) :
    Irreducible p := by
  let pu : Units F := Units.mk0 (p : F) hp0
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation F
        (Units.map (algebraMap (RingOfIntegers F) F) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation F
          (Units.map (algebraMap (RingOfIntegers F) F) u) :=
        (exists_normalizedValuationHom F).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation F
          (Units.map (algebraMap (RingOfIntegers F) F) u)⁻¹ :=
        (exists_normalizedValuationHom F).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers F)), rfl⟩
      rw [e01_normalizedValuation_inv F] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers F) F) u = pu := by
      apply Units.ext
      change (((u : Units (RingOfIntegers F)) : RingOfIntegers F) : F) = (p : F)
      rw [hu]
    rw [heq, hpval] at huval
    omega
  · intro x y hxy
    have hx0 : (x : F) ≠ 0 := by
      intro hx
      apply hp0
      rw [hxy]
      simp [hx]
    have hy0 : (y : F) ≠ 0 := by
      intro hy
      apply hp0
      rw [hxy]
      simp [hy]
    let xu : Units F := Units.mk0 (x : F) hx0
    let yu : Units F := Units.mk0 (y : F) hy0
    have hxnonneg : 0 ≤ normalizedValuation F xu :=
      (exists_normalizedValuationHom F).choose_spec.2 _ |>.2 ⟨x, rfl⟩
    have hynonneg : 0 ≤ normalizedValuation F yu :=
      (exists_normalizedValuationHom F).choose_spec.2 _ |>.2 ⟨y, rfl⟩
    have hmul : xu * yu = pu := by
      apply Units.ext
      simpa [xu, yu, pu] using congr_arg Subtype.val hxy.symm
    have hsum : normalizedValuation F xu + normalizedValuation F yu = 1 := by
      rw [← normalizedValuation_mul, hmul, hpval]
    rcases (show normalizedValuation F xu = 0 ∨ normalizedValuation F yu = 0 by omega) with hx | hy
    · exact Or.inl (e01_isUnit_of_normalizedValuation_eq_zero F x hx0 hx)
    · exact Or.inr (e01_isUnit_of_normalizedValuation_eq_zero F y hy0 hy)

private theorem existence_normalizedValuation_inv (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem existence_isUnit_of_normalizedValuation_eq_zero
    (a : RingOfIntegers K) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [existence_normalizedValuation_inv K, hval, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers K) :=
    { val := a
      inv := b
      val_inv := by
        apply Subtype.ext
        change (a : K) * (b : K) = 1
        rw [hb]
        exact mul_inv_cancel₀ ha
      inv_val := by
        apply Subtype.ext
        change (b : K) * (a : K) = 1
        rw [hb]
        exact inv_mul_cancel₀ ha }
  exact ⟨u, rfl⟩

private theorem existence_uniformizerInteger_irreducible (π : Uniformizer K) :
    Irreducible (uniformizerInteger K π) := by
  let ϖ := uniformizerInteger K π
  have hϖ : (ϖ : K) = (π.val : K) := (uniformizer_integer_exists K π).choose_spec
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation K
        (Units.map (algebraMap (RingOfIntegers K) K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
      rw [existence_normalizedValuation_inv K] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers K) K) u = π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
      rw [hu, hϖ]
    rw [heq, π.valuation_eq_one] at huval
    omega
  · intro a b hab
    have ha0 : (a : K) ≠ 0 := by
      intro ha
      have : (ϖ : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [ha]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    have hb0 : (b : K) ≠ 0 := by
      intro hb
      have : (ϖ : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [hb]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    let ua : Units K := Units.mk0 (a : K) ha0
    let ub : Units K := Units.mk0 (b : K) hb0
    have hva : 0 ≤ normalizedValuation K ua :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨a, rfl⟩
    have hvb : 0 ≤ normalizedValuation K ub :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨b, rfl⟩
    have huv : ua * ub = π.val := by
      apply Units.ext
      simpa [ua, ub, ← hϖ] using congr_arg Subtype.val hab.symm
    have hvsum : normalizedValuation K ua + normalizedValuation K ub = 1 := by
      rw [← normalizedValuation_mul, huv, π.valuation_eq_one]
    rcases (show normalizedValuation K ua = 0 ∨ normalizedValuation K ub = 0 by omega) with ha | hb
    · exact Or.inl (existence_isUnit_of_normalizedValuation_eq_zero K a ha0 ha)
    · exact Or.inr (existence_isUnit_of_normalizedValuation_eq_zero K b hb0 hb)

private theorem existence_uniformizerInteger_maximalIdeal (π : Uniformizer K) :
    Ideal.span ({uniformizerInteger K π} : Set (RingOfIntegers K)) =
      LocalMaximalIdeal K :=
  (existence_uniformizerInteger_irreducible K π).maximalIdeal_eq.symm

private theorem existence_normalizedValuation_le_iff (x y : Units K) :
    normalizedValuation K x ≤ normalizedValuation K y ↔
      valuation K (y : K) ≤ valuation K (x : K) := by
  have hnonneg : 0 ≤ normalizedValuation K (y * x⁻¹) ↔
      valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 := by
    unfold normalizedValuation normalizedValuationHom
    rw [(exists_normalizedValuationHom K).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  rw [normalizedValuation_mul, existence_normalizedValuation_inv K] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation K y - normalizedValuation K x ↔
      valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change valuation K (y : K) / valuation K (x : K) ≤ 1 ↔ _
  rw [div_le_one₀ ((valuation K).pos_iff.mpr x.ne_zero)]

private theorem existence_normalizedValuation_lt_iff (x y : Units K) :
    normalizedValuation K x < normalizedValuation K y ↔
      valuation K (y : K) < valuation K (x : K) := by
  simpa only [not_le] using (existence_normalizedValuation_le_iff K y x).not

/-- The explicit field `K_a^ur K_b^LT` in the fixed separable closure. -/
def rectangularCompositum (π : Uniformizer K)
    (a b : ℕ) (_ha : 1 ≤ a) (hb : 1 ≤ b) : IntermediateField K Ksep :=
  (unramifiedTower K Ksep).field (a - 1) ⊔ (lubinTateLevel K Ksep π b hb).field

/--
The complete E01 package on the literal rectangular compositum.  In particular, the extension
field is not a free field of this structure: every assertion is about `rectangularCompositum`.
-/
structure RectangularCompositumData (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) where
  /-- The explicit compositum is finite over `K`. -/
  finiteDimensional : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb)
  /-- It is Galois over `K`. -/
  isGalois :
    letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
      finiteDimensional
    IsGalois K (rectangularCompositum K Ksep π a b ha hb)
  /-- Its Galois group is abelian. -/
  commutative :
    letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
      finiteDimensional
    letI : IsGalois K (rectangularCompositum K Ksep π a b ha hb) := isGalois
    ∀ σ τ : (rectangularCompositum K Ksep π a b ha hb ≃ₐ[K]
      rectangularCompositum K Ksep π a b ha hb), σ * τ = τ * σ
  /-- The compositum carries the full compatible local-field instance bundle. -/
  localFieldData :
    letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
      finiteDimensional
    LubinTateLocalFieldData K Ksep (rectangularCompositum K Ksep π a b ha hb)
  /-- The unramified and totally ramified factors meet only in the base field. -/
  intersection_eq_bot :
    (unramifiedTower K Ksep).field (a - 1) ⊓
      (lubinTateLevel K Ksep π b hb).field = ⊥
  /-- The unramified factor is included by the literal left inclusion into the compositum. -/
  unramified_le :
    (unramifiedTower K Ksep).field (a - 1) ≤
      rectangularCompositum K Ksep π a b ha hb
  /-- The Lubin--Tate factor is included by the literal right inclusion into the compositum. -/
  lubinTate_le :
    (lubinTateLevel K Ksep π b hb).field ≤
      rectangularCompositum K Ksep π a b ha hb
  /-- Linear disjointness gives the expected compositum degree. -/
  finrank :
    letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
      finiteDimensional
    Module.finrank K (rectangularCompositum K Ksep π a b ha hb) =
      a * (residueCard K - 1) * residueCard K ^ (b - 1)
  /-- The norm of the explicit compositum is the rectangular subgroup. -/
  normSubgroup_eq :
    letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
      finiteDimensional
    normSubgroup K (rectangularCompositum K Ksep π a b ha hb) =
      rectangularSubgroup K π a b

set_option maxHeartbeats 800000 in
-- The Eisenstein base-change and scalar-tower synthesis in E01 need a larger elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
/--
**E01**, Proposition `prop:cofinal-norms`: construct the literal compositum
`K_a^ur K_b^LT`, prove linear disjointness and abelianity, compute its degree, and compute its
norm as `π^(aℤ)U_K^b`.  The target is definitionally explicit and cannot be supplied by E03.
-/
theorem rectangularClassField_exists (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nonempty (RectangularCompositumData K Ksep π a b ha hb) := by
  let E := (lubinTateLevel K Ksep π b hb).field
  let U := (unramifiedTower K Ksep).field (a - 1)
  letI : FiniteDimensional K E := (lubinTateLevel K Ksep π b hb).finiteDimensional
  letI : FiniteDimensional K U := (unramifiedTower K Ksep).finiteDimensional (a - 1)
  letI : ValuativeRel E := (lubinTateLevel K Ksep π b hb).localFieldData.valuativeRel
  letI : TopologicalSpace E := (lubinTateLevel K Ksep π b hb).localFieldData.topology
  letI : IsNonarchimedeanLocalField E :=
    (lubinTateLevel K Ksep π b hb).localFieldData.localField
  letI : ValuativeExtension K E :=
    (lubinTateLevel K Ksep π b hb).localFieldData.valuativeExtension
  letI : ContinuousSMul K E :=
    (lubinTateLevel K Ksep π b hb).localFieldData.continuousSMul
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  letI : IsNonarchimedeanLocalField U := unramifiedIntermediateFieldLocalField K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  letI : ValuativeExtension K U := unramifiedIntermediateFieldValuativeExtension K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  letI : ContinuousSMul K U := unramifiedIntermediateFieldContinuousSMul K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  letI : IsUnramifiedLocalExtension K U := unramifiedIntermediateFieldIsUnramified K Ksep U
    ((unramifiedTower K Ksep).unramified (a - 1))
  have hEg : IsGalois K E := (lubinTateGaloisData K Ksep π).isGalois b hb
  have hUg : IsGalois K U := (unramifiedTower K Ksep).isGalois (a - 1)
  let D := ((unramifiedTower K Ksep).compositum_localField E hEg (a - 1)).some
  let C : IntermediateField K Ksep := E ⊔ U
  letI : Algebra E C := intermediateFieldInclusionAlgebra K Ksep le_sup_left
  letI : Algebra U C := intermediateFieldInclusionAlgebra K Ksep le_sup_right
  letI : FiniteDimensional E C := D.finiteDimensional_left
  letI : FiniteDimensional U C := D.finiteDimensional_right
  letI : IsScalarTower K E C := D.scalarTower_left
  letI : IsScalarTower K U C := D.scalarTower_right
  letI : FiniteDimensional K C := FiniteDimensional.trans K E C
  letI : ValuativeRel C := D.compositumValuativeRel
  letI : TopologicalSpace C := D.compositumTopology
  letI : IsNonarchimedeanLocalField C := D.compositumLocalField
  letI : IsGalois K C := D.isGalois_base
  letI : IsGalois E C := D.isGalois_left
  letI : ValuativeExtension K C := D.valuativeExtension_base
  letI : ValuativeExtension E C := D.valuativeExtension_left
  letI : ContinuousSMul K C := D.continuousSMul_base
  letI : ContinuousSMul E C := D.continuousSMul_left
  letI : IsUnramifiedLocalExtension E C := D.unramified_left
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  let intMap : RingOfIntegers K →+* RingOfIntegers U :=
    { toFun := fun x => ⟨algebraMap K U (x : K), by
        rw [Valuation.mem_integer_iff]
        exact (Valuation.HasExtension.val_map_le_one_iff
          (ValuativeRel.valuation K) (ValuativeRel.valuation U) (x : K)).2
            ((Valuation.mem_integer_iff _ _).1 x.prop)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun x y => by apply Subtype.ext; simp }
  letI : Algebra (RingOfIntegers K) (RingOfIntegers U) := intMap.toAlgebra
  letI : IsScalarTower (RingOfIntegers K) (RingOfIntegers U) U :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let pK := uniformizerInteger K π
  let pU : RingOfIntegers U := algebraMap (RingOfIntegers K) (RingOfIntegers U) pK
  have hpUfield : (pU : U) = algebraMap K U (π.val : K) := by
    dsimp only [pU, pK]
    change algebraMap (RingOfIntegers U) U
      (algebraMap (RingOfIntegers K) (RingOfIntegers U) (uniformizerInteger K π)) = _
    rw [← IsScalarTower.algebraMap_apply (RingOfIntegers K) (RingOfIntegers U) U]
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K U]
    have hbase : algebraMap (RingOfIntegers K) K (uniformizerInteger K π) =
        (π.val : K) := (uniformizer_integer_exists K π).choose_spec
    rw [hbase]
  have hpU0 : (pU : U) ≠ 0 := by
    rw [hpUfield]
    exact (map_ne_zero (algebraMap K U)).2 π.val.ne_zero
  have hpUval : normalizedValuation U (Units.mk0 (pU : U) hpU0) = 1 := by
    have hu : Units.mk0 (pU : U) hpU0 = Units.map (algebraMap K U) π.val := by
      apply Units.ext
      exact hpUfield
    rw [hu, normalizedValuation_algebraMap,
      IsUnramifiedLocalExtension.ramificationIndex_eq_one,
      π.valuation_eq_one]
    norm_num
  have hpUirr : Irreducible pU :=
    e01_irreducible_of_normalizedValuation_eq_one U pU hpU0 hpUval
  have hmaxU : LocalMaximalIdeal U = Ideal.span ({pU} : Set (RingOfIntegers U)) :=
    hpUirr.maximalIdeal_eq
  let P := primitiveDivisionPolynomial K π b
  let PU := P.map intMap
  have hPmonic : P.Monic := (e01_primitive_monic_natDegree K π b).1
  have hPUmonic : PU.Monic := hPmonic.map intMap
  have hPnat : P.natDegree = (residueCard K - 1) * residueCard K ^ (b - 1) :=
    (e01_primitive_monic_natDegree K π b).2
  have hPUnat : PU.natDegree = P.natDegree := hPmonic.natDegree_map intMap
  have hPconst : P.coeff 0 = uniformizerInteger K π := by
    simpa [P] using (lubinTate_norm_inclusion K Ksep π b hb).2.2.2
  have hPUeis : PU.IsEisensteinAt (LocalMaximalIdeal U) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hPUmonic.leadingCoeff]
      intro hone
      exact (IsLocalRing.maximalIdeal.isMaximal (R := RingOfIntegers U)).ne_top
        ((Ideal.eq_top_iff_one (LocalMaximalIdeal U)).2 hone)
    · intro n hn
      rw [hPUnat] at hn
      have hcoeffK :=
        (primitiveDivisionPolynomial_eisenstein K Ksep π b hb).1.mem hn
      apply (Valuation.mem_maximalIdeal_iff U (ValuativeRel.valuation U)).2
      rw [show PU.coeff n = intMap (P.coeff n) by
        exact Polynomial.coeff_map intMap n]
      change ValuativeRel.valuation U
        (algebraMap K U ((P.coeff n : RingOfIntegers K) : K)) < 1
      exact (Valuation.HasExtension.val_map_lt_one_iff
        (ValuativeRel.valuation K) (ValuativeRel.valuation U) _).2
          ((Valuation.mem_maximalIdeal_iff K (ValuativeRel.valuation K)).1 hcoeffK)
    · rw [show PU.coeff 0 = pU by
        rw [Polynomial.coeff_map, hPconst]
        rfl]
      intro hmem
      rw [hmaxU, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨d, hd⟩ := hmem
      have hpUne : pU ≠ 0 := by
        intro h
        exact hpU0 (congr_arg (fun z : RingOfIntegers U => (z : U)) h)
      have hcancel : d * pU = 1 := by
        apply mul_right_cancel₀ hpUne
        calc
          (d * pU) * pU = d * pU ^ 2 := by ring
          _ = pU := hd
          _ = 1 * pU := by simp
      exact hpUirr.not_isUnit (IsUnit.of_mul_eq_one_right d hcancel)
  have hPUirr : Irreducible PU :=
    hPUeis.irreducible (IsLocalRing.maximalIdeal.isMaximal _).isPrime
      hPUmonic.isPrimitive (by
        rw [hPUnat, hPnat]
        exact mul_pos (Nat.sub_pos_of_lt (e01_one_lt_residueCard K))
          (pow_pos (Nat.zero_lt_one.trans (e01_one_lt_residueCard K)) _))
  let PUF := PU.map (algebraMap (RingOfIntegers U) U)
  have hPUFmonic : PUF.Monic := hPUmonic.map _
  have hPUFnat : PUF.natDegree = PU.natDegree := hPUmonic.natDegree_map _
  have hPUFirr : Irreducible PUF :=
    hPUmonic.irreducible_iff_irreducible_map_fraction_map.mp hPUirr
  let level := lubinTateLevel K Ksep π b hb
  let α : C := IntermediateField.inclusion (show E ≤ C from le_sup_left) level.generator
  have hroot : Polynomial.aeval α PUF = 0 := by
    apply (algebraMap C Ksep).injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rw [show PUF = PU.map (algebraMap (RingOfIntegers U) U) from rfl,
      Polynomial.eval₂_map]
    rw [show PU = P.map intMap from rfl, Polynomial.eval₂_map]
    have hcoeff : ((((algebraMap C Ksep).comp (algebraMap U C)).comp
        (algebraMap (RingOfIntegers U) U)).comp intMap) =
        algebraMap (RingOfIntegers K) Ksep := by
      apply RingHom.ext
      intro r
      change algebraMap C Ksep
        (algebraMap U C (algebraMap K U (r : K))) = algebraMap (RingOfIntegers K) Ksep r
      rw [← IsScalarTower.algebraMap_apply K U C,
        ← IsScalarTower.algebraMap_apply K C Ksep,
        IsScalarTower.algebraMap_apply (RingOfIntegers K) K Ksep]
      rfl
    rw [hcoeff]
    simpa [α, level, E, C, Polynomial.IsRoot.def, Polynomial.eval_map] using level.isRoot
  have hminpoly : minpoly U α = PUF :=
    (minpoly.eq_of_irreducible_of_monic hPUFirr hroot hPUFmonic).symm
  let A : IntermediateField U C := IntermediateField.adjoin U {α}
  let B : IntermediateField K C := A.restrictScalars K
  have hαA : α ∈ A := IntermediateField.subset_adjoin U {α} (Set.mem_singleton α)
  have hEle : E ≤ IntermediateField.lift B := by
    rw [show E = IntermediateField.adjoin K
      {(((level.generator : E) : Ksep))} from level.field_eq_adjoin]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hαB : α ∈ B := (IntermediateField.mem_restrictScalars K).2 hαA
    have hαlift := (IntermediateField.mem_lift α).2 hαB
    simpa [α, level, E, C] using hαlift
  have hUle : U ≤ IntermediateField.lift B := by
    intro x hx
    let xu : U := ⟨x, hx⟩
    let xC : C := IntermediateField.inclusion (show U ≤ C from le_sup_right) xu
    have hxA : xC ∈ A := by
      change algebraMap U C xu ∈ A
      exact A.algebraMap_mem xu
    have hxB : xC ∈ B := (IntermediateField.mem_restrictScalars K).2 hxA
    have hxlift := (IntermediateField.mem_lift xC).2 hxB
    simpa [xC, xu, C, U] using hxlift
  have hBlift : IntermediateField.lift B = C := by
    apply le_antisymm (IntermediateField.lift_le B)
    change E ⊔ U ≤ IntermediateField.lift B
    exact sup_le hEle hUle
  have hBtop : B = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [hBlift, IntermediateField.lift_top]
  have hAtop : A = ⊤ :=
    (IntermediateField.restrictScalars_eq_top_iff (F := U) (K := K)).1 hBtop
  have hαint : IsIntegral U α := ⟨PUF, hPUFmonic, hroot⟩
  let pb : PowerBasis U C := PowerBasis.ofAdjoinEqTop hαint
    ((IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hαint.isAlgebraic).mp hAtop)
  have hpbgen : pb.gen = α := by simp [pb]
  have hfinUC : Module.finrank U C =
      (residueCard K - 1) * residueCard K ^ (b - 1) := by
    calc
      Module.finrank U C = pb.dim := pb.finrank
      _ = (residueCard K - 1) * residueCard K ^ (b - 1) := by
        have hdeg := pb.degree_minpoly
        rw [hpbgen, hminpoly, Polynomial.degree_eq_natDegree hPUFmonic.ne_zero,
          hPUFnat, hPUnat, hPnat] at hdeg
        exact_mod_cast hdeg.symm
  have hfinU : Module.finrank K U = a := by
    rw [(unramifiedTower K Ksep).finrank (a - 1)]
    omega
  have hfinC : Module.finrank K C =
      a * (residueCard K - 1) * residueCard K ^ (b - 1) := by
    rw [← Module.finrank_mul_finrank K U C, hfinU, hfinUC]
    ring
  have hlinear : U.LinearDisjoint E := by
    apply IntermediateField.LinearDisjoint.of_finrank_sup
    rw [sup_comm]
    change Module.finrank K C = Module.finrank K U * Module.finrank K E
    rw [hfinC, hfinU, level.degree]
    ring
  have hinter : U ⊓ E = ⊥ := hlinear.inf_eq_bot
  let GE := E ≃ₐ[K] E
  let GU := U ≃ₐ[K] U
  letI : CommGroup GE :=
    { (inferInstance : Group GE) with
      mul_comm := (lubinTateGaloisData K Ksep π).commutative b hb }
  letI : IsCyclic GU := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨(unramifiedTower K Ksep).frobenius (a - 1),
      (unramifiedTower K Ksep).frobenius_generates (a - 1)⟩
  letI : CommGroup GU := IsCyclic.commGroup
  let rE : (C ≃ₐ[K] C) →* GE := AlgEquiv.restrictNormalHom E
  let rU : (C ≃ₐ[K] C) →* GU := AlgEquiv.restrictNormalHom U
  let r : (C ≃ₐ[K] C) →* GE × GU := rE.prod rU
  have hr_injective : Function.Injective r := by
    intro σ τ hστ
    have hEres : rE σ = rE τ := congrArg Prod.fst hστ
    have hUres : rU σ = rU τ := congrArg Prod.snd hστ
    let F : IntermediateField K C :=
      { carrier := {x | σ x = τ x}
        mul_mem' := fun {x y} hx hy => by
          change σ (x * y) = τ (x * y)
          rw [map_mul, map_mul, hx, hy]
        one_mem' := by simp
        add_mem' := fun {x y} hx hy => by
          change σ (x + y) = τ (x + y)
          rw [map_add, map_add, hx, hy]
        zero_mem' := by simp
        algebraMap_mem' := fun x => by simp
        inv_mem' := fun x hx => by
          change σ x⁻¹ = τ x⁻¹
          rw [map_inv₀, map_inv₀, hx] }
    have hErestrict : E.restrict (show E ≤ C from le_sup_left) ≤ F := by
      intro x hx
      change σ x = τ x
      let xe : E := ⟨((x : C) : Ksep),
        (IntermediateField.mem_restrict (show E ≤ C from le_sup_left) x).1 hx⟩
      have heq := congrArg (fun f : GE => f xe) hEres
      have hxalg : algebraMap E C xe = x := by apply Subtype.ext; rfl
      calc
        σ x = σ (algebraMap E C xe) := congrArg σ hxalg.symm
        _ = algebraMap E C ((σ.restrictNormal E) xe) :=
          (AlgEquiv.restrictNormal_commutes σ E xe).symm
        _ = algebraMap E C ((τ.restrictNormal E) xe) :=
          congrArg (algebraMap E C)
            (by simpa [rE, AlgEquiv.restrictNormalHom] using heq)
        _ = τ (algebraMap E C xe) := AlgEquiv.restrictNormal_commutes τ E xe
        _ = τ x := congrArg τ hxalg
    have hUrestrict : U.restrict (show U ≤ C from le_sup_right) ≤ F := by
      intro x hx
      change σ x = τ x
      let xu : U := ⟨((x : C) : Ksep),
        (IntermediateField.mem_restrict (show U ≤ C from le_sup_right) x).1 hx⟩
      have heq := congrArg (fun f : GU => f xu) hUres
      have hxalg : algebraMap U C xu = x := by apply Subtype.ext; rfl
      calc
        σ x = σ (algebraMap U C xu) := congrArg σ hxalg.symm
        _ = algebraMap U C ((σ.restrictNormal U) xu) :=
          (AlgEquiv.restrictNormal_commutes σ U xu).symm
        _ = algebraMap U C ((τ.restrictNormal U) xu) :=
          congrArg (algebraMap U C)
            (by simpa [rU, AlgEquiv.restrictNormalHom] using heq)
        _ = τ (algebraMap U C xu) := AlgEquiv.restrictNormal_commutes τ U xu
        _ = τ x := congrArg τ hxalg
    have hsup : E.restrict (show E ≤ C from le_sup_left) ⊔
        U.restrict (show U ≤ C from le_sup_right) = ⊤ := by
      apply IntermediateField.lift_injective C
      rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
        IntermediateField.lift_restrict, IntermediateField.lift_top]
    have hF : F = ⊤ := by
      rw [← top_le_iff, ← hsup]
      exact sup_le hErestrict hUrestrict
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ F := by rw [hF]; trivial
    change σ x = τ x at hx
    exact hx
  have hcomm : ∀ σ τ : (C ≃ₐ[K] C), σ * τ = τ * σ := by
    intro σ τ
    apply hr_injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  let GC := C ≃ₐ[K] C
  letI : CommGroup GC :=
    { (inferInstance : Group GC) with mul_comm := hcomm }
  have hnormE : normSubgroup K C ≤ normSubgroup K E := by
    rintro x ⟨y, rfl⟩
    exact ⟨normUnitsHom E C y, normUnitsHom_tower K E C y |>.symm⟩
  have hnormU : normSubgroup K C ≤ normSubgroup K U := by
    rintro x ⟨y, rfl⟩
    exact ⟨normUnitsHom U C y, normUnitsHom_tower K U C y |>.symm⟩
  have hEnorm : normSubgroup K E = rectangularSubgroup K π 1 b := by
    change normSubgroup K
      (lubinTateFiniteAbelianExtension K Ksep π b hb).field =
        rectangularSubgroup K π 1 b
    exact lubinTate_normSubgroup K Ksep π b hb
  have hUnorm : normSubgroup K U = unramifiedRectangularSubgroup K π a := by
    rw [normSubgroup_eq_unramifiedRectangular K U π, hfinU]
  have hnorm_le : normSubgroup K C ≤ rectangularSubgroup K π a b := by
    rw [← e01_rectangular_inf_unramified K π a b]
    exact le_inf (hnormE.trans_eq hEnorm) (hnormU.trans_eq hUnorm)
  have hJindex : (rectangularSubgroup K π 1 b).index =
      (residueCard K - 1) * residueCard K ^ (b - 1) := by
    calc
      (rectangularSubgroup K π 1 b).index = (normSubgroup K E).index :=
        congrArg Subgroup.index hEnorm.symm
      _ = Nat.card (Abelianization GE) :=
        normSubgroup_index K Ksep (lubinTateFiniteAbelianExtension K Ksep π b hb).field
      _ = Nat.card GE :=
        Nat.card_congr (Abelianization.equivOfComm (H := GE)).symm.toEquiv
      _ = Module.finrank K E := IsGalois.card_aut_eq_finrank K E
      _ = (residueCard K - 1) * residueCard K ^ (b - 1) := level.degree
  have hrectIndex : (rectangularSubgroup K π a b).index =
      a * (residueCard K - 1) * residueCard K ^ (b - 1) := by
    have hle : rectangularSubgroup K π a b ≤ rectangularSubgroup K π 1 b := by
      rw [← e01_rectangular_inf_unramified K π a b]
      exact inf_le_left
    rw [← Subgroup.relIndex_mul_index hle,
      e01_rectangular_relIndex K π a b, hJindex]
    ring
  have hnormIndex : (normSubgroup K C).index =
      a * (residueCard K - 1) * residueCard K ^ (b - 1) := by
    let FC : FiniteGaloisIntermediateField K Ksep :=
      FiniteGaloisIntermediateField.mk C
    calc
      (normSubgroup K C).index = Nat.card (Abelianization GC) :=
        normSubgroup_index K Ksep FC
      _ = Nat.card GC :=
        Nat.card_congr (Abelianization.equivOfComm (H := GC)).symm.toEquiv
      _ = Module.finrank K C := IsGalois.card_aut_eq_finrank K C
      _ = a * (residueCard K - 1) * residueCard K ^ (b - 1) := hfinC
  have hnorm : normSubgroup K C = rectangularSubgroup K π a b := by
    letI : (normSubgroup K C).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by
        rw [hnormIndex]
        exact mul_pos (mul_pos ha (Nat.sub_pos_of_lt (e01_one_lt_residueCard K)))
          (pow_pos (Nat.zero_lt_one.trans (e01_one_lt_residueCard K)) _)|>.ne')
    apply le_antisymm hnorm_le
    by_contra hnot
    have hstrict : normSubgroup K C < rectangularSubgroup K π a b :=
      lt_iff_le_and_ne.mpr ⟨hnorm_le, fun h => hnot h.ge⟩
    have hlt := Subgroup.index_strictAnti hstrict
    rw [hnormIndex, hrectIndex] at hlt
    exact Nat.lt_irrefl _ hlt
  let R := rectangularCompositum K Ksep π a b ha hb
  have hRC : R = C := by
    simp only [R, rectangularCompositum, C, E, U, sup_comm]
  have hfd : FiniteDimensional K R := by
    rw [hRC]
    infer_instance
  have hg :
      letI : FiniteDimensional K R := hfd
      IsGalois K R := by
    rw [hRC]
    exact D.isGalois_base
  have hc :
      letI : FiniteDimensional K R := hfd
      letI : IsGalois K R := hg
      ∀ σ τ : (R ≃ₐ[K] R), σ * τ = τ * σ := by
    rw [hRC]
    exact hcomm
  have hlocalC : LubinTateLocalFieldData K Ksep C :=
    { valuativeRel := D.compositumValuativeRel
      topology := D.compositumTopology
      localField := D.compositumLocalField
      valuativeExtension := D.valuativeExtension_base
      continuousSMul := D.continuousSMul_base }
  have hlocal :
      letI : FiniteDimensional K R := hfd
      LubinTateLocalFieldData K Ksep R :=
    e01_transportLocalFieldData K Ksep hRC.symm hlocalC
  have hfinR :
      letI : FiniteDimensional K R := hfd
      Module.finrank K R =
        a * (residueCard K - 1) * residueCard K ^ (b - 1) := by
    rw [hRC]
    exact hfinC
  have hnormR :
      letI : FiniteDimensional K R := hfd
      normSubgroup K R = rectangularSubgroup K π a b := by
    rw [hRC]
    exact hnorm
  refine ⟨{
    finiteDimensional := hfd
    isGalois := hg
    commutative := hc
    localFieldData := hlocal
    intersection_eq_bot := hinter
    unramified_le := le_sup_left
    lubinTate_le := le_sup_right
    finrank := hfinR
    normSubgroup_eq := hnormR }⟩

/-- The chosen proof/data package for the explicit rectangular compositum. -/
noncomputable def rectangularCompositumData (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    RectangularCompositumData K Ksep π a b ha hb :=
  (rectangularClassField_exists K Ksep π a b ha hb).some

/-- The explicit compositum packaged as a finite abelian extension. -/
noncomputable def rectangularClassField (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : FiniteAbelianExtension K Ksep := by
  let D := rectangularCompositumData K Ksep π a b ha hb
  letI : FiniteDimensional K (rectangularCompositum K Ksep π a b ha hb) :=
    D.finiteDimensional
  letI : IsGalois K (rectangularCompositum K Ksep π a b ha hb) := D.isGalois
  exact
    { field := FiniteGaloisIntermediateField.mk
        (rectangularCompositum K Ksep π a b ha hb)
      commutative := D.commutative }

/-- The field underlying `rectangularClassField` is literally `K_a^ur K_b^LT`. -/
theorem rectangularClassField_field (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (rectangularClassField K Ksep π a b ha hb).field.toIntermediateField =
      (unramifiedTower K Ksep).field (a - 1) ⊔
        (lubinTateLevel K Ksep π b hb).field := by
  rfl

/-- **E01**: the norm of the explicitly packaged compositum. -/
theorem norm_rectangularClassField (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    normSubgroup K (rectangularClassField K Ksep π a b ha hb).field =
      rectangularSubgroup K π a b := by
  exact (rectangularCompositumData K Ksep π a b ha hb).normSubgroup_eq

/-- **E01**: the degree of the explicitly packaged compositum. -/
theorem finrank_rectangularClassField (π : Uniformizer K)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Module.finrank K (rectangularClassField K Ksep π a b ha hb).field =
      a * (residueCard K - 1) * residueCard K ^ (b - 1) := by
  exact (rectangularCompositumData K Ksep π a b ha hb).finrank

/--
**E02**, Proposition `prop:cofinal-norms`: rectangular subgroups are cofinal among open
finite-index subgroups of `Kˣ`.
-/
theorem rectangularSubgroup_cofinal (π : Uniformizer K)
    (H : OpenFiniteIndexSubgroup (Units K)) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      rectangularSubgroup K π a b ≤ H.toSubgroup := by
  have hH : (H.toSubgroup : Set (Units K)) ∈ nhds (1 : Units K) :=
    H.toOpenSubgroup.isOpen.mem_nhds H.toSubgroup.one_mem
  have hbasis : (nhds (1 : Units K)).HasBasis (fun _ => True)
      (fun γ : Units (ValuativeRel.ValueGroupWithZero K) =>
        {x : Units K | valuation K ((x : K) - 1) < γ}) := by
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap]
    simpa only [Set.preimage_setOf_eq, Units.val_one] using
      ((IsValuativeTopology.hasBasis_nhds (R := K) (1 : K)).comap
        ((↑) : Units K → K))
  obtain ⟨γ, _, hγ⟩ := hbasis.mem_iff.mp hH
  obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective
    (K := K) (γ : ValuativeRel.ValueGroupWithZero K)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact γ.ne_zero hc.symm
  let y : Units K := Units.mk0 c hc0
  let b : ℕ := (normalizedValuation K y).natAbs + 1
  have hb : 1 ≤ b := Nat.le_add_left 1 _
  have hyb : normalizedValuation K y < (b : ℤ) := by
    have habs : normalizedValuation K y ≤ (normalizedValuation K y).natAbs :=
      Int.le_natAbs
    dsimp only [b]
    omega
  have hπbval : valuation K ((π.val ^ b : Units K) : K) < γ := by
    rw [← hc]
    apply (existence_normalizedValuation_lt_iff K y (π.val ^ b)).1
    rw [show normalizedValuation K (π.val ^ b) = (b : ℤ) by
      change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ b)) = _
      rw [map_pow, toAdd_pow]
      change (b : ℤ) * normalizedValuation K π.val = _
      rw [π.valuation_eq_one, mul_one]]
    exact hyb
  have hprincipal : principalUnitSubgroup K b ≤ H.toSubgroup := by
    intro x hx
    apply hγ
    obtain ⟨u, hu, rfl⟩ := hx
    have hquot := congr_arg Units.val hu
    have hdiff : (u : RingOfIntegers K) - 1 ∈ LocalMaximalIdeal K ^ b := by
      apply Ideal.Quotient.eq.mp
      exact hquot
    rw [← existence_uniformizerInteger_maximalIdeal K π,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hdiff
    obtain ⟨d, hd⟩ := hdiff
    by_cases hzero : (u : RingOfIntegers K) - 1 = 0
    · change valuation K
        (((ringUnitsToFieldUnits K u : Units K) : K) - 1) < γ
      have hfield : (((ringUnitsToFieldUnits K u : Units K) : K) - 1) = 0 := by
        exact congr_arg (fun z : RingOfIntegers K => (z : K)) hzero
      rw [hfield, map_zero]
      exact pos_iff_ne_zero.mpr γ.ne_zero
    · have hdiff0 : ((((u : RingOfIntegers K) - 1 : RingOfIntegers K) : K)) ≠ 0 := by
        intro h
        exact hzero (Subtype.ext h)
      have hd0 : (d : K) ≠ 0 := by
        intro h
        apply hzero
        rw [← hd]
        apply Subtype.ext
        simp [h]
      let du : Units K := Units.mk0
        ((((u : RingOfIntegers K) - 1 : RingOfIntegers K) : K)) hdiff0
      let dunit : Units K := Units.mk0 (d : K) hd0
      have hdunit : du = dunit * π.val ^ b := by
        apply Units.ext
        change ((((u : RingOfIntegers K) - 1 : RingOfIntegers K) : K)) =
          (d : K) * ((π.val ^ b : Units K) : K)
        have hp : (((uniformizerInteger K π) ^ b : RingOfIntegers K) : K) =
            ((π.val ^ b : Units K) : K) := by
          change (((uniformizerInteger K π : RingOfIntegers K) : K) ^ b) =
            (((π.val : Units K) : K) ^ b)
          have hbase : ((uniformizerInteger K π : RingOfIntegers K) : K) =
              ((π.val : Units K) : K) :=
            (uniformizer_integer_exists K π).choose_spec
          rw [hbase]
        calc
          ((((u : RingOfIntegers K) - 1 : RingOfIntegers K) : K)) =
              ((d * uniformizerInteger K π ^ b : RingOfIntegers K) : K) :=
            congr_arg (fun z : RingOfIntegers K => (z : K)) hd.symm
          _ = (d : K) * (((uniformizerInteger K π) ^ b : RingOfIntegers K) : K) := rfl
          _ = (d : K) * ((π.val ^ b : Units K) : K) := by rw [hp]
      have hdnonneg : 0 ≤ normalizedValuation K dunit :=
        (exists_normalizedValuationHom K).choose_spec.2 dunit |>.2 ⟨d, rfl⟩
      have hbdu : (b : ℤ) ≤ normalizedValuation K du := by
        rw [hdunit, normalizedValuation_mul]
        have hpow : normalizedValuation K (π.val ^ b) = (b : ℤ) := by
          change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ b)) = _
          rw [map_pow, toAdd_pow]
          change (b : ℤ) * normalizedValuation K π.val = _
          rw [π.valuation_eq_one, mul_one]
        rw [hpow]
        omega
      have hvalle : valuation K (du : K) ≤
          valuation K ((π.val ^ b : Units K) : K) :=
        (existence_normalizedValuation_le_iff K (π.val ^ b) du).1 (by
          simpa [show normalizedValuation K (π.val ^ b) = (b : ℤ) by
            change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ b)) = _
            rw [map_pow, toAdd_pow]
            change (b : ℤ) * normalizedValuation K π.val = _
            rw [π.valuation_eq_one, mul_one]] using hbdu)
      exact hvalle.trans_lt hπbval
  have hindex : H.toSubgroup.index ≠ 0 := H.finiteIndex'.index_ne_zero
  obtain ⟨a, ha, _, hπa⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hindex π.val
  refine ⟨a, b, ha, hb, ?_⟩
  rw [rectangularSubgroup]
  exact sup_le (Subgroup.zpowers_le.mpr (by simpa using hπa)) hprincipal

end

end NU.LCFT
