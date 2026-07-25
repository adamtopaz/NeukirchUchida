import Submission.NU.NeukirchUchida.LocalInvariants
import Submission.NU.Chebotarev.FieldCrossing

/-!
# Imported local, Chebotarev, and LCFT interfaces

This is the only module in the Neukirch--Uchida layer that imports the three
upstream packages.  It implements blueprint §1.2, `int:local`, `int:cheb`,
and `int:lcft`.  The global files import only this interface (transitively).

The ambient representation is the binding choice of blueprint §9.1: one
`Omega = AlgebraicClosure ℚ`, number fields embedded as intermediate fields,
and absolute Galois groups represented by their actual pointwise stabilizers
inside `Gal(Omega/ℚ)`.
-/

open scoped NumberField Pointwise Topology
open IsDedekindDomain

namespace NU.NeukirchUchida

noncomputable section

/-- The single ambient algebraic closure from blueprint §1 and §9.1. -/
abbrev Omega := AlgebraicClosure ℚ

/-- The ambient absolute Galois group `G_ℚ`. -/
abbrev RationalAbsoluteGaloisGroup := Omega ≃ₐ[ℚ] Omega

/-- A number field in the fixed ambient closure.

The `finite` field is the arithmetic content of the bundle; the underlying
field remains literally an `IntermediateField ℚ Omega`. -/
structure NumberFieldInOmega where
  /-- The embedded intermediate field. -/
  field : IntermediateField ℚ Omega
  /-- Finiteness over `ℚ`. -/
  finite : Module.Finite ℚ field

attribute [instance] NumberFieldInOmega.finite

/-- Every bundled ambient number field carries the standard `NumberField`
instance. -/
noncomputable instance (F : NumberFieldInOmega) : NumberField F.field :=
  NumberField.of_module_finite ℚ F.field

/-- The rational field, embedded as the bottom intermediate field. -/
noncomputable def rationalNumberField : NumberFieldInOmega where
  field := ⊥
  finite := by infer_instance

/-- Inhabitation sanity check for `NumberFieldInOmega`: `ℚ` is an explicit
inhabitant, so the bundle cannot become vacuous through instance capture. -/
instance numberFieldInOmegaNonempty : Nonempty NumberFieldInOmega :=
  ⟨rationalNumberField⟩

/-- A finite extension in the fixed ambient closure.  The inclusion field is
part of the data, so the induced algebra structure is not an arbitrary map. -/
structure NumberFieldExtension (K : NumberFieldInOmega) where
  /-- The upper number field. -/
  field : NumberFieldInOmega
  /-- The literal inclusion in `Omega`. -/
  le_base : K.field ≤ field.field

/-- The algebra structure attached to an ambient extension is induced by its
recorded literal inclusion. -/
noncomputable instance (K : NumberFieldInOmega) (L : NumberFieldExtension K) :
    Algebra K.field L.field.field :=
  (IntermediateField.inclusion L.le_base).toRingHom.toAlgebra

/-- The ambient extension algebra is compatible with the rational algebra. -/
instance (K : NumberFieldInOmega) (L : NumberFieldExtension K) :
    IsScalarTower ℚ K.field L.field.field := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- A finite extension between number fields is finite-dimensional. -/
instance (K : NumberFieldInOmega) (L : NumberFieldExtension K) :
    FiniteDimensional K.field L.field.field := by
  infer_instance

/-- Defining equation for the algebra map of an ambient extension. -/
@[simp]
theorem algebraMap_numberFieldExtension_apply
    (K : NumberFieldInOmega) (L : NumberFieldExtension K) (x : K.field) :
    algebraMap K.field L.field.field x =
      ⟨x.1, L.le_base x.2⟩ :=
  rfl

/-- The identity extension. -/
noncomputable def trivialNumberFieldExtension (K : NumberFieldInOmega) :
    NumberFieldExtension K where
  field := K
  le_base := le_rfl

/-- Inhabitation sanity check for ambient finite extensions. -/
instance numberFieldExtensionNonempty (K : NumberFieldInOmega) :
    Nonempty (NumberFieldExtension K) :=
  ⟨trivialNumberFieldExtension K⟩

/-- The closed pointwise stabilizer `G_F` inside the single `G_ℚ`.
This is not an abstract copy of an absolute Galois group. -/
def absoluteGaloisGroup (F : NumberFieldInOmega) :
    Subgroup RationalAbsoluteGaloisGroup :=
  F.field.fixingSubgroup

/-- Membership in `G_F` is literal pointwise fixation of `F`. -/
@[simp]
theorem mem_absoluteGaloisGroup_iff
    (F : NumberFieldInOmega) (g : RationalAbsoluteGaloisGroup) :
    g ∈ absoluteGaloisGroup F ↔ ∀ x : F.field, g x.1 = x.1 := by
  rfl

/-- The stabilizer model `G_F` is closed in `G_ℚ` (blueprint §9.1(2)). -/
theorem absoluteGaloisGroup_isClosed (F : NumberFieldInOmega) :
    IsClosed (absoluteGaloisGroup F : Set RationalAbsoluteGaloisGroup) := by
  exact IntermediateField.fixingSubgroup_isClosed F.field

/-- Conjugation of an embedded field by an element of `G_ℚ`. -/
def conjugateField (g : RationalAbsoluteGaloisGroup)
    (F : IntermediateField ℚ Omega) : IntermediateField ℚ Omega :=
  IntermediateField.map g.toAlgHom F

/-- Defining membership equation for field conjugation. -/
@[simp]
theorem mem_conjugateField_iff
    (g : RationalAbsoluteGaloisGroup)
    (F : IntermediateField ℚ Omega) (x : Omega) :
    x ∈ conjugateField g F ↔ g.symm x ∈ F := by
  rw [conjugateField, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, g.apply_symm_apply x⟩

/-- An absolute finite prime in the fixed closure: a nontrivial valuation
subring whose restriction to `ℚ` is a finite prime.  This is exactly the
compatible-valuation representation required by blueprint §9.1(3). -/
structure AbsolutePrime where
  /-- The valuation subring in `Omega`. -/
  valuationSubring : ValuationSubring Omega
  /-- Its restriction to `ℚ` is a nonarchimedean finite place. -/
  isFinite : NU.LocalTheory.IsAbsoluteFinitePlace ℚ valuationSubring

/-- Equality of absolute primes is determined by their valuation subrings. -/
@[ext]
theorem AbsolutePrime.ext {P Q : AbsolutePrime}
    (h : P.valuationSubring = Q.valuationSubring) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Absolute finite primes exist (extend, for example, the `2`-adic
valuation to `Omega`).  This is the inhabitation sanity check for
`AbsolutePrime`. -/
theorem absolutePrime_nonempty : Nonempty AbsolutePrime := by
  obtain ⟨P⟩ := NU.LocalTheory.absoluteFinitePlaceOf_nonempty ℚ
  exact ⟨⟨P.1, P.2⟩⟩

noncomputable instance : Nonempty AbsolutePrime := absolutePrime_nonempty

/-- Ambient automorphisms preserve the predicate of being an absolute finite
prime. -/
theorem smul_isAbsoluteFinitePlace
    (g : RationalAbsoluteGaloisGroup) (P : AbsolutePrime) :
    NU.LocalTheory.IsAbsoluteFinitePlace ℚ (g • P.valuationSubring) := by
  exact (NU.LocalTheory.conjugateAbsoluteFinitePlace ℚ g
    ⟨P.valuationSubring, P.isFinite⟩).2

/-- The literal ambient action on absolute primes. -/
noncomputable instance absolutePrimeAction :
    MulAction RationalAbsoluteGaloisGroup AbsolutePrime where
  smul g P := ⟨g • P.valuationSubring, smul_isAbsoluteFinitePlace g P⟩
  one_smul P := by
    apply AbsolutePrime.ext
    exact one_smul RationalAbsoluteGaloisGroup P.valuationSubring
  mul_smul g h P := by
    apply AbsolutePrime.ext
    exact mul_smul g h P.valuationSubring

/-- Defining equation for the action on the underlying valuation subring. -/
@[simp]
theorem smul_absolutePrime_valuationSubring
    (g : RationalAbsoluteGaloisGroup) (P : AbsolutePrime) :
    (g • P).valuationSubring = g • P.valuationSubring :=
  rfl

/-- The absolute decomposition group `D_P^F`, definitionally the stabilizer
of the absolute prime inside the closed subgroup `G_F`. -/
def decompositionGroup (F : NumberFieldInOmega) (P : AbsolutePrime) :
    Subgroup (absoluteGaloisGroup F) :=
  MulAction.stabilizer (absoluteGaloisGroup F) P

/-- The restriction of an absolute prime to an ambient number field remains
nontrivial. -/
theorem absolutePrime_comap_nontrivial
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    NU.LocalTheory.IsNontrivialValuation
      (P.valuationSubring.comap F.field.val.toRingHom) := by
  have hfinite :=
    (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
      ℚ F.field Omega P.valuationSubring).mp P.isFinite
  rcases hfinite with ⟨_, v, hv⟩
  change P.valuationSubring.comap (algebraMap F.field Omega) ≠ ⊤
  rw [hv]
  exact NU.LocalTheory.primeValuationSubring_ne_top v

/-- Restriction of an absolute prime to a finite prime of `F`. -/
noncomputable def finitePrime
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    NU.LocalTheory.FinitePlace F.field :=
  NU.LocalTheory.centerFinitePlace
    (P.valuationSubring.comap F.field.val.toRingHom)
    (absolutePrime_comap_nontrivial F P)

/-- Defining valuation-ring equation for finite-prime restriction. -/
@[simp]
theorem primeValuationSubring_finitePrime
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    NU.LocalTheory.primeValuationSubring (finitePrime F P) =
      P.valuationSubring.comap F.field.val.toRingHom :=
  NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _

/-- The rational prime below a finite prime. -/
noncomputable def rationalPrime
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) :
    NU.LocalTheory.FinitePlace ℚ :=
  NU.LocalTheory.restrictFinitePlace ℚ v

/-- The ramification index of a finite prime over its rational prime. -/
noncomputable def absoluteRamificationIndex
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) : ℕ :=
  v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ)

/-- The residue degree of a finite prime over its rational prime. -/
noncomputable def absoluteResidueDegree
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) : ℕ :=
  v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ)

/-- The absolute local degree `e(v/q) f(v/q)`. -/
noncomputable def absoluteLocalDegree
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) : ℕ :=
  absoluteRamificationIndex F v * absoluteResidueDegree F v

/-- Absolute local degree one, blueprint `def:degree-one`. -/
def IsAbsoluteDegreeOne
    (F : NumberFieldInOmega) (v : NU.LocalTheory.FinitePlace F.field) : Prop :=
  absoluteLocalDegree F v = 1

/-- The residue field of an absolute valuation. -/
abbrev AbsoluteResidueField (P : AbsolutePrime) :=
  P.valuationSubring ⧸ IsLocalRing.maximalIdeal P.valuationSubring

/-- The action of a decomposition group on the residue field. -/
noncomputable def absoluteResidueAction
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    decompositionGroup F P →*
      (AbsoluteResidueField P ≃+* AbsoluteResidueField P) := by
  let valuationEquiv (g : decompositionGroup F P) :
      P.valuationSubring ≃+* P.valuationSubring := by
    have hprime : (g.1 : absoluteGaloisGroup F) • P = P := g.2
    have hstab := congrArg AbsolutePrime.valuationSubring hprime
    have hstab' :
        (g.1.1 : RationalAbsoluteGaloisGroup) • P.valuationSubring =
          P.valuationSubring :=
      (smul_absolutePrime_valuationSubring
        (g.1.1 : RationalAbsoluteGaloisGroup) P).symm.trans hstab
    have hstab_inv :
        (g.1.1 : RationalAbsoluteGaloisGroup)⁻¹ • P.valuationSubring =
          P.valuationSubring := by
      calc
        (g.1.1 : RationalAbsoluteGaloisGroup)⁻¹ • P.valuationSubring =
            (g.1.1 : RationalAbsoluteGaloisGroup)⁻¹ •
              ((g.1.1 : RationalAbsoluteGaloisGroup) •
                P.valuationSubring) :=
          congrArg ((g.1.1 : RationalAbsoluteGaloisGroup)⁻¹ • ·) hstab'.symm
        _ = P.valuationSubring := inv_smul_smul _ _
    refine
      { toFun := fun x =>
          ⟨(g.1.1 : RationalAbsoluteGaloisGroup) x.1, ?_⟩
        invFun := fun x =>
          ⟨(g.1.1 : RationalAbsoluteGaloisGroup).symm x.1, ?_⟩
        left_inv := ?_
        right_inv := ?_
        map_add' := ?_
        map_mul' := ?_ }
    · have hm : (g.1.1 : RationalAbsoluteGaloisGroup) x.1 ∈
          (g.1.1 : RationalAbsoluteGaloisGroup) • P.valuationSubring := by
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        simpa using x.2
      exact (ValuationSubring.ext_iff.mp hstab' _).mp hm
    · have hm : (g.1.1 : RationalAbsoluteGaloisGroup).symm x.1 ∈
          (g.1.1 : RationalAbsoluteGaloisGroup)⁻¹ • P.valuationSubring := by
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        simpa using x.2
      exact (ValuationSubring.ext_iff.mp hstab_inv _).mp hm
    · intro x
      apply Subtype.ext
      exact (g.1.1 : RationalAbsoluteGaloisGroup).symm_apply_apply x.1
    · intro x
      apply Subtype.ext
      exact (g.1.1 : RationalAbsoluteGaloisGroup).apply_symm_apply x.1
    · intro x y
      apply Subtype.ext
      exact (g.1.1 : RationalAbsoluteGaloisGroup).map_mul x.1 y.1
    · intro x y
      apply Subtype.ext
      exact (g.1.1 : RationalAbsoluteGaloisGroup).map_add x.1 y.1
  let residueEquiv (g : decompositionGroup F P) :
      AbsoluteResidueField P ≃+* AbsoluteResidueField P := by
    let e := valuationEquiv g
    have hmapped :
        (IsLocalRing.maximalIdeal P.valuationSubring).map e.toRingHom =
          IsLocalRing.maximalIdeal P.valuationSubring :=
      IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
    have hmax : IsLocalRing.maximalIdeal P.valuationSubring =
        (IsLocalRing.maximalIdeal P.valuationSubring).map e := hmapped.symm
    exact Ideal.quotientEquiv
      (IsLocalRing.maximalIdeal P.valuationSubring)
      (IsLocalRing.maximalIdeal P.valuationSubring) e hmax
  refine
    { toFun := residueEquiv
      map_one' := ?_
      map_mul' := ?_ }
  · apply RingEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  · intro g h
    apply RingEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl

/-- Defining equation for `absoluteResidueAction`: it is induced by the
ambient automorphism on representatives, not an arbitrary residue action. -/
theorem absoluteResidueAction_mk
    (F : NumberFieldInOmega) (P : AbsolutePrime)
    (g : decompositionGroup F P) (x : P.valuationSubring) :
    ∃ y : P.valuationSubring,
      (y.1 : Omega) = (g.1.1 : RationalAbsoluteGaloisGroup) x.1 ∧
      absoluteResidueAction F P g
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal P.valuationSubring) x) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal P.valuationSubring) y := by
  have hprime : (g.1 : absoluteGaloisGroup F) • P = P := g.2
  have hstab := congrArg AbsolutePrime.valuationSubring hprime
  have hstab' :
      (g.1.1 : RationalAbsoluteGaloisGroup) • P.valuationSubring =
        P.valuationSubring :=
    (smul_absolutePrime_valuationSubring
      (g.1.1 : RationalAbsoluteGaloisGroup) P).symm.trans hstab
  have hmem : (g.1.1 : RationalAbsoluteGaloisGroup) x.1 ∈
      P.valuationSubring := by
    have hm : (g.1.1 : RationalAbsoluteGaloisGroup) x.1 ∈
        (g.1.1 : RationalAbsoluteGaloisGroup) • P.valuationSubring := by
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      simpa using x.2
    exact (ValuationSubring.ext_iff.mp hstab' _).mp hm
  refine ⟨⟨(g.1.1 : RationalAbsoluteGaloisGroup) x.1, hmem⟩, rfl, ?_⟩
  unfold absoluteResidueAction
  dsimp only
  rfl

/-- A normalized arithmetic Frobenius lift: on the absolute residue field it
is the `Norm(v)`-power map for the finite prime `v = finitePrime F P`.
This is `q ^ f`, not merely the norm `q` of the rational prime below `v`, so
the map fixes the embedded residue field of `F` in every residue degree.
This pins the Frobenius convention used by (L4). -/
def IsArithmeticFrobeniusLift
    (F : NumberFieldInOmega) (P : AbsolutePrime)
    (g : decompositionGroup F P) : Prop :=
  ∀ x : AbsoluteResidueField P,
    absoluteResidueAction F P g x =
      x ^ NU.Chebotarev.PrimeIdeal.norm (finitePrime F P)

/-! ## Bridge to the actual oriented LocalTheory theorem -/

/-- A comparison between Mathlib's chosen `AlgebraicClosure F` and the
single ambient closure. -/
noncomputable def ambientClosureEquiv (F : NumberFieldInOmega) :
    AlgebraicClosure F.field ≃ₐ[F.field] Omega := by
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsAlgebraic F.field Omega :=
    IntermediateField.isAlgebraic_tower_top
  letI : IsAlgClosure F.field Omega :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, inferInstance⟩
  exact IsAlgClosure.equiv F.field (AlgebraicClosure F.field) Omega

/-- The comparison is an `F`-algebra equivalence. -/
@[simp]
theorem ambientClosureEquiv_algebraMap
    (F : NumberFieldInOmega) (x : F.field) :
    ambientClosureEquiv F (algebraMap F.field (AlgebraicClosure F.field) x) =
      algebraMap F.field Omega x :=
  (ambientClosureEquiv F).commutes x

/-- Transport between the ambient stabilizer and the actual abstract
absolute Galois group used by `NU.LocalTheory.oriented_reconstruction_functorial`.
-/
noncomputable def ambientAbsoluteGaloisEquiv (F : NumberFieldInOmega) :
    absoluteGaloisGroup F ≃ₜ* Field.absoluteGaloisGroup F.field := by
  let omegaAutEquivAmbient :
      (Omega ≃ₐ[F.field] Omega) ≃* absoluteGaloisGroup F :=
    { toFun := fun σ => ⟨σ.restrictScalars ℚ, by
        change σ.restrictScalars ℚ ∈ F.field.fixingSubgroup
        rw [IntermediateField.mem_fixingSubgroup_iff F.field]
        intro x hx
        let y : F.field := ⟨x, hx⟩
        simpa [y] using σ.commutes y⟩
      invFun := fun g =>
        { g.1.toRingEquiv with
          commutes' := fun x => by
            change (g.1 : RationalAbsoluteGaloisGroup) x.1 = x.1
            exact ((IntermediateField.mem_fixingSubgroup_iff F.field g.1).mp
              g.2) x.1 x.2 }
      left_inv := fun σ => by
        apply AlgEquiv.ext
        intro x
        rfl
      right_inv := fun g => by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        rfl
      map_mul' := fun σ τ => by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        rfl }
  let mulEquiv : absoluteGaloisGroup F ≃*
      Field.absoluteGaloisGroup F.field :=
    ((AlgEquiv.autCongr (ambientClosureEquiv F)).trans
      omegaAutEquivAmbient).symm
  have hspec (g : absoluteGaloisGroup F)
      (x : AlgebraicClosure F.field) :
      ambientClosureEquiv F
          ((show AlgebraicClosure F.field ≃ₐ[F.field]
            AlgebraicClosure F.field from mulEquiv g) x) =
        (g.1 : RationalAbsoluteGaloisGroup) (ambientClosureEquiv F x) := by
    change ambientClosureEquiv F
        (((AlgEquiv.autCongr (ambientClosureEquiv F)).symm
          (omegaAutEquivAmbient.symm g)) x) = _
    rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
    simp [AlgEquiv.trans_apply, omegaAutEquivAmbient]
  have hcont : Continuous mulEquiv := by
    apply continuous_of_continuousAt_one mulEquiv.toMonoidHom
    rw [ContinuousAt, Filter.tendsto_def]
    intro s hs
    have hs' : s ∈ 𝓝 (1 : Field.absoluteGaloisGroup F.field) := by
      simpa using hs
    obtain ⟨E, hEfin, hEs⟩ :=
      (krullTopology_mem_nhds_one_iff F.field
        (AlgebraicClosure F.field) s).mp hs'
    letI : FiniteDimensional F.field E := hEfin
    let EΩ : IntermediateField F.field Omega :=
      E.map (ambientClosureEquiv F).toAlgHom
    let eE : E ≃ₐ[F.field] EΩ := by
      exact E.toSubalgebra.equivMapOfInjective
        (ambientClosureEquiv F).toAlgHom (ambientClosureEquiv F).injective
    letI : FiniteDimensional F.field EΩ :=
      Module.Finite.equiv eE.toLinearEquiv
    letI : FiniteDimensional ℚ EΩ := FiniteDimensional.trans ℚ F.field EΩ
    let Eℚ : IntermediateField ℚ Omega := EΩ.restrictScalars ℚ
    let eRestrict : EΩ ≃ₐ[ℚ] Eℚ :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    letI : FiniteDimensional ℚ Eℚ :=
      Module.Finite.equiv eRestrict.toLinearEquiv
    have hEℚopen : IsOpen
        (Subtype.val ⁻¹'
          (Eℚ.fixingSubgroup : Set RationalAbsoluteGaloisGroup) :
          Set (absoluteGaloisGroup F)) :=
      (IntermediateField.fixingSubgroup_isOpen Eℚ).preimage
        continuous_subtype_val
    have hEℚone : (1 : absoluteGaloisGroup F) ∈
        (Subtype.val ⁻¹'
          (Eℚ.fixingSubgroup : Set RationalAbsoluteGaloisGroup) :
          Set (absoluteGaloisGroup F)) := Eℚ.fixingSubgroup.one_mem
    apply Filter.mem_of_superset (hEℚopen.mem_nhds hEℚone)
    intro g hg
    apply hEs
    change (show AlgebraicClosure F.field ≃ₐ[F.field]
      AlgebraicClosure F.field from mulEquiv g) ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff E]
    intro x hx
    apply (ambientClosureEquiv F).injective
    rw [hspec]
    exact ((IntermediateField.mem_fixingSubgroup_iff Eℚ g.1).mp hg)
      (ambientClosureEquiv F x) (by
        change ambientClosureEquiv F x ∈ EΩ
        exact (IntermediateField.mem_map E).mpr ⟨x, hx, rfl⟩)
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : CompactSpace RationalAbsoluteGaloisGroup :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace (M := ℚ)
  letI : CompactSpace (absoluteGaloisGroup F) :=
    isCompact_iff_compactSpace.mp (absoluteGaloisGroup_isClosed F).isCompact
  letI : Algebra.IsAlgebraic F.field (AlgebraicClosure F.field) :=
    AlgebraicClosure.isAlgebraic F.field
  letI : Algebra.IsIntegral F.field (AlgebraicClosure F.field) :=
    Algebra.IsAlgebraic.isIntegral
  letI : T2Space (Field.absoluteGaloisGroup F.field) := krullTopology_t2
  have hhome : IsHomeomorph mulEquiv :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hcont, mulEquiv.bijective⟩
  let home := hhome.homeomorph mulEquiv
  have hinvfun : home.invFun = mulEquiv.invFun := by
    funext g
    apply mulEquiv.injective
    exact (home.apply_symm_apply g).trans (mulEquiv.apply_symm_apply g).symm
  exact
    { toMulEquiv := mulEquiv
      continuous_toFun := hcont
      continuous_invFun := by
        rw [← hinvfun]
        exact home.continuous_invFun }

/-- Defining conjugation equation for the ambient/abstract transport. -/
theorem ambientAbsoluteGaloisEquiv_spec
    (F : NumberFieldInOmega) (g : absoluteGaloisGroup F)
    (x : AlgebraicClosure F.field) :
    ambientClosureEquiv F
        ((show AlgebraicClosure F.field ≃ₐ[F.field] AlgebraicClosure F.field
          from ambientAbsoluteGaloisEquiv F g) x) =
      (g.1 : RationalAbsoluteGaloisGroup) (ambientClosureEquiv F x) := by
  let omegaAutEquivAmbient :
      (Omega ≃ₐ[F.field] Omega) ≃* absoluteGaloisGroup F :=
    { toFun := fun σ => ⟨σ.restrictScalars ℚ, by
        change σ.restrictScalars ℚ ∈ F.field.fixingSubgroup
        rw [IntermediateField.mem_fixingSubgroup_iff F.field]
        intro z hz
        let y : F.field := ⟨z, hz⟩
        simpa [y] using σ.commutes y⟩
      invFun := fun h =>
        { h.1.toRingEquiv with
          commutes' := fun z => by
            change (h.1 : RationalAbsoluteGaloisGroup) z.1 = z.1
            exact ((IntermediateField.mem_fixingSubgroup_iff F.field h.1).mp
              h.2) z.1 z.2 }
      left_inv := fun σ => by
        apply AlgEquiv.ext
        intro z
        rfl
      right_inv := fun h => by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro z
        rfl
      map_mul' := fun σ τ => by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro z
        rfl }
  change ambientClosureEquiv F
      (((AlgEquiv.autCongr (ambientClosureEquiv F)).symm
        (omegaAutEquivAmbient.symm g)) x) = _
  rw [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
  simp [AlgEquiv.trans_apply, omegaAutEquivAmbient]

/-- Transport an ambient profinite isomorphism to the exact input type of the
oriented LocalTheory theorem. -/
noncomputable def abstractAbsoluteGaloisIso
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    Field.absoluteGaloisGroup F₁.field ≃ₜ*
      Field.absoluteGaloisGroup F₂.field :=
  (ambientAbsoluteGaloisEquiv F₁).symm.trans
    (theta.trans (ambientAbsoluteGaloisEquiv F₂))

/-- The record/subtype identification at the common-ambient L1 seam. -/
private noncomputable def absolutePrimeSubtypeEquiv :
    NU.LocalTheory.AbsoluteFinitePlaceIn ℚ Omega ≃ AbsolutePrime where
  toFun P := ⟨P.1, P.2⟩
  invFun P := ⟨P.valuationSubring, P.isFinite⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport LocalTheory's abstract absolute places into the common ambient
prime representation. -/
private noncomputable def abstractPlaceEquiv (F : NumberFieldInOmega) :
    NU.LocalTheory.AbsoluteFinitePlaceOf F.field ≃ AbsolutePrime :=
  (NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension
    ℚ F.field Omega (ambientClosureEquiv F)).trans absolutePrimeSubtypeEquiv

private theorem abstractGaloisCompat (F : NumberFieldInOmega)
    (g : Field.absoluteGaloisGroup F.field)
    (x : AlgebraicClosure F.field) :
    ambientClosureEquiv F
        ((show AlgebraicClosure F.field ≃ₐ[F.field] AlgebraicClosure F.field
          from g) x) =
      ((ambientAbsoluteGaloisEquiv F).symm g) • ambientClosureEquiv F x := by
  change ambientClosureEquiv F
      ((show AlgebraicClosure F.field ≃ₐ[F.field] AlgebraicClosure F.field
        from g) x) =
    (((ambientAbsoluteGaloisEquiv F).symm g).1 :
      RationalAbsoluteGaloisGroup) (ambientClosureEquiv F x)
  simpa using ambientAbsoluteGaloisEquiv_spec F
    ((ambientAbsoluteGaloisEquiv F).symm g) x

private theorem ambientDecompositionGroup_eq
    (F : NumberFieldInOmega) (P : AbsolutePrime) :
    NU.LocalTheory.ambientDecompositionGroup P.valuationSubring =
      decompositionGroup F P := by
  ext g
  change (g • P.valuationSubring = P.valuationSubring) ↔ (g • P = P)
  constructor
  · intro h
    apply AbsolutePrime.ext
    exact (smul_absolutePrime_valuationSubring
      (g.1 : RationalAbsoluteGaloisGroup) P).trans h
  · intro h
    have hv := congrArg AbsolutePrime.valuationSubring h
    exact (smul_absolutePrime_valuationSubring
      (g.1 : RationalAbsoluteGaloisGroup) P).symm.trans hv

private theorem abstractPlaceEquiv_decompositionGroup
    (F : NumberFieldInOmega)
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf F.field) :
    Subgroup.map (ambientAbsoluteGaloisEquiv F).symm.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup F.field P.1) =
      decompositionGroup F (abstractPlaceEquiv F P) := by
  rw [← ambientDecompositionGroup_eq F (abstractPlaceEquiv F P)]
  simpa [abstractPlaceEquiv, absolutePrimeSubtypeEquiv] using
    NU.LocalTheory.map_absoluteDecompositionGroup_ambientOfFiniteExtension
      ℚ F.field Omega (absoluteGaloisGroup F)
      (ambientClosureEquiv F)
      (ambientAbsoluteGaloisEquiv F).symm.toMulEquiv
      (abstractGaloisCompat F) P

/-- (L1), blueprint `int:local`: an arbitrary profinite isomorphism gives a
bijective, unique correspondence of absolute finite primes and maps their
decomposition groups exactly.

This is the common-ambient wrapper around LocalTheory's proved
orientation-free `local_interface`; no cyclotomic-orientation recognition
hypothesis is used. -/
theorem existsUnique_primeCorrespondence_L1
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    ∃ e : AbsolutePrime ≃ AbsolutePrime,
      (∀ P,
        Subgroup.map theta.toMulEquiv.toMonoidHom (decompositionGroup F₁ P) =
          decompositionGroup F₂ (e P)) ∧
      (∀ P Q,
        Subgroup.map theta.toMulEquiv.toMonoidHom (decompositionGroup F₁ P) =
          decompositionGroup F₂ Q → Q = e P) := by
  let alpha := abstractAbsoluteGaloisIso theta
  obtain ⟨e₀, he₀, hunique₀, _⟩ := NU.LocalTheory.local_interface alpha
  let e : AbsolutePrime ≃ AbsolutePrime :=
    (abstractPlaceEquiv F₁).symm.trans (e₀.trans (abstractPlaceEquiv F₂))
  have hcomp :
      theta.toMulEquiv.toMonoidHom.comp
          (ambientAbsoluteGaloisEquiv F₁).symm.toMulEquiv.toMonoidHom =
        (ambientAbsoluteGaloisEquiv F₂).symm.toMulEquiv.toMonoidHom.comp
          alpha.toMulEquiv.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    apply (ambientAbsoluteGaloisEquiv F₂).injective
    change ambientAbsoluteGaloisEquiv F₂
        (theta ((ambientAbsoluteGaloisEquiv F₁).symm g)) =
      ambientAbsoluteGaloisEquiv F₂
        ((ambientAbsoluteGaloisEquiv F₂).symm (alpha g))
    rw [(ambientAbsoluteGaloisEquiv F₂).apply_symm_apply]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro P
    let P₀ := (abstractPlaceEquiv F₁).symm P
    have hlocal := he₀ P₀
    have hsource := abstractPlaceEquiv_decompositionGroup F₁ P₀
    have htarget := abstractPlaceEquiv_decompositionGroup F₂ (e₀ P₀)
    rw [show P = abstractPlaceEquiv F₁ P₀ by simp [P₀], ← hsource,
      Subgroup.map_map]
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
    change Subgroup.map (theta.toMulEquiv.toMonoidHom.comp
        (ambientAbsoluteGaloisEquiv F₁).symm.toMulEquiv.toMonoidHom)
        (NU.LocalTheory.absoluteDecompositionGroup F₁.field P₀.1) =
      decompositionGroup F₂ (abstractPlaceEquiv F₂ (e₀ P₀))
    rw [← htarget, ← hlocal, Subgroup.map_map, hcomp]
  · intro P Q hQ
    let P₀ := (abstractPlaceEquiv F₁).symm P
    let Q₀ := (abstractPlaceEquiv F₂).symm Q
    have hsource := abstractPlaceEquiv_decompositionGroup F₁ P₀
    have htarget := abstractPlaceEquiv_decompositionGroup F₂ Q₀
    have hlocal :
        Subgroup.map alpha.toMulEquiv.toMonoidHom
            (NU.LocalTheory.absoluteDecompositionGroup F₁.field P₀.1) =
          NU.LocalTheory.absoluteDecompositionGroup F₂.field Q₀.1 := by
      apply Subgroup.map_injective
        (f := (ambientAbsoluteGaloisEquiv F₂).symm.toMulEquiv.toMonoidHom)
        (ambientAbsoluteGaloisEquiv F₂).symm.injective
      rw [Subgroup.map_map, htarget, ← hcomp,
        ← Subgroup.map_map, hsource]
      simpa [P₀, Q₀] using hQ
    have hQ₀ : Q₀ = e₀ P₀ := (hunique₀ P₀ Q₀).mp hlocal
    simpa [P₀, Q₀, e] using congrArg (abstractPlaceEquiv F₂) hQ₀

/-- The absolute-prime equivalence selected by (L1). -/
noncomputable def primeCorrespondence
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    AbsolutePrime ≃ AbsolutePrime :=
  (existsUnique_primeCorrespondence_L1 theta).choose

/-- Defining decomposition-group equation for the selected (L1)
correspondence. -/
@[simp]
theorem map_decompositionGroup_primeCorrespondence
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) :
    Subgroup.map theta.toMulEquiv.toMonoidHom (decompositionGroup F₁ P) =
      decompositionGroup F₂ (primeCorrespondence theta P) :=
  (existsUnique_primeCorrespondence_L1 theta).choose_spec.1 P

/-- Uniqueness clause of (L1). -/
theorem eq_primeCorrespondence_of_map_decompositionGroup
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P Q : AbsolutePrime)
    (hQ : Subgroup.map theta.toMulEquiv.toMonoidHom
      (decompositionGroup F₁ P) = decompositionGroup F₂ Q) :
    Q = primeCorrespondence theta P :=
  (existsUnique_primeCorrespondence_L1 theta).choose_spec.2 P Q hQ

/-- The isomorphism between corresponding decomposition groups, obtained by
restricting `theta`; its defining equation rules out an arbitrary group
isomorphism. -/
noncomputable def decompositionGroupEquiv
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) :
    decompositionGroup F₁ P ≃ₜ*
      decompositionGroup F₂ (primeCorrespondence theta P) := by
  have hmap := map_decompositionGroup_primeCorrespondence theta P
  refine
    { toFun := fun g => ⟨theta g.1, ?_⟩
      invFun := fun h => ⟨theta.symm h.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have hgmap : theta g.1 ∈ Subgroup.map theta.toMulEquiv.toMonoidHom
        (decompositionGroup F₁ P) := ⟨g.1, g.2, rfl⟩
    rwa [hmap] at hgmap
  · have hhmap : h.1 ∈ Subgroup.map theta.toMulEquiv.toMonoidHom
        (decompositionGroup F₁ P) := by
      rw [hmap]
      exact h.2
    rcases hhmap with ⟨g, hg, hgh⟩
    have heq : theta.symm h.1 = g := by
      rw [← hgh]
      exact theta.symm_apply_apply g
    rwa [heq]
  · intro g
    apply Subtype.ext
    exact theta.symm_apply_apply g.1
  · intro h
    apply Subtype.ext
    exact theta.apply_symm_apply h.1
  · intro g h
    apply Subtype.ext
    exact theta.map_mul g.1 h.1
  · apply Continuous.subtype_mk
    exact theta.continuous_toFun.comp continuous_subtype_val
  · apply Continuous.subtype_mk
    exact theta.continuous_invFun.comp continuous_subtype_val

/-- Defining equation for the restricted decomposition-group equivalence. -/
@[simp]
theorem decompositionGroupEquiv_apply
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) (g : decompositionGroup F₁ P) :
    (decompositionGroupEquiv theta P g).1 = theta g.1 := by
  rfl

/-- (L2), blueprint `int:local`: equivariance of the absolute-prime
correspondence. -/
theorem primeCorrespondence_equivariant_L2
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (g : absoluteGaloisGroup F₁) (P : AbsolutePrime) :
    primeCorrespondence theta (g • P) =
      theta g • primeCorrespondence theta P := by
  symm
  apply eq_primeCorrespondence_of_map_decompositionGroup theta
  have hsource :
      decompositionGroup F₁ (g • P) =
        Subgroup.map (MulAut.conj g).toMonoidHom
          (decompositionGroup F₁ P) := by
    change MulAction.stabilizer (absoluteGaloisGroup F₁) (g • P) = _
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g P
  have htarget :
      decompositionGroup F₂ (theta g • primeCorrespondence theta P) =
        Subgroup.map (MulAut.conj (theta g)).toMonoidHom
          (decompositionGroup F₂ (primeCorrespondence theta P)) := by
    change MulAction.stabilizer (absoluteGaloisGroup F₂)
      (theta g • primeCorrespondence theta P) = _
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj
      (theta g) (primeCorrespondence theta P)
  have hconjhom :
      theta.toMulEquiv.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (theta g)).toMonoidHom.comp
          theta.toMulEquiv.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change theta (g * x * g⁻¹) = theta g * theta x * (theta g)⁻¹
    simp
  calc
    Subgroup.map theta.toMulEquiv.toMonoidHom
        (decompositionGroup F₁ (g • P)) =
      Subgroup.map theta.toMulEquiv.toMonoidHom
        (Subgroup.map (MulAut.conj g).toMonoidHom
          (decompositionGroup F₁ P)) := by rw [hsource]
    _ = Subgroup.map (MulAut.conj (theta g)).toMonoidHom
          (Subgroup.map theta.toMulEquiv.toMonoidHom
            (decompositionGroup F₁ P)) := by
      rw [Subgroup.map_map, Subgroup.map_map, hconjhom]
    _ = Subgroup.map (MulAut.conj (theta g)).toMonoidHom
          (decompositionGroup F₂ (primeCorrespondence theta P)) := by
      rw [map_decompositionGroup_primeCorrespondence]
    _ = decompositionGroup F₂
          (theta g • primeCorrespondence theta P) := htarget.symm

/-- (L3), blueprint `int:local`: corresponding finite primes lie over the
same rational prime and have the same ramification index and residue degree
over `ℚ`.  Consequently absolute local degree one is preserved. -/
theorem primeCorrespondence_invariants_L3
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) :
    rationalPrime F₁ (finitePrime F₁ P) =
        rationalPrime F₂ (finitePrime F₂ (primeCorrespondence theta P)) ∧
      absoluteRamificationIndex F₁ (finitePrime F₁ P) =
        absoluteRamificationIndex F₂
          (finitePrime F₂ (primeCorrespondence theta P)) ∧
      absoluteResidueDegree F₁ (finitePrime F₁ P) =
        absoluteResidueDegree F₂
          (finitePrime F₂ (primeCorrespondence theta P)) := by
  let Q := primeCorrespondence theta P
  let P₁ : LocalInvariants.AmbientAbsolutePlace F₁.field Omega :=
    ⟨P.valuationSubring,
      (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
        ℚ F₁.field Omega P.valuationSubring).mp P.isFinite⟩
  let P₂ : LocalInvariants.AmbientAbsolutePlace F₂.field Omega :=
    ⟨Q.valuationSubring,
      (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
        ℚ F₂.field Omega Q.valuationSubring).mp Q.isFinite⟩
  let R₁ : LocalInvariants.AbsoluteGaloisActionRealization
      F₁.field Omega (absoluteGaloisGroup F₁) :=
    { closureEquiv := ambientClosureEquiv F₁
      galoisEquiv := (ambientAbsoluteGaloisEquiv F₁).symm
      action_compat := abstractGaloisCompat F₁ }
  let R₂ : LocalInvariants.AbsoluteGaloisActionRealization
      F₂.field Omega (absoluteGaloisGroup F₂) :=
    { closureEquiv := ambientClosureEquiv F₂
      galoisEquiv := (ambientAbsoluteGaloisEquiv F₂).symm
      action_compat := abstractGaloisCompat F₂ }
  have hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
      (NU.LocalTheory.ambientDecompositionGroup
        (G := absoluteGaloisGroup F₁) P₁.1) =
    NU.LocalTheory.ambientDecompositionGroup
      (G := absoluteGaloisGroup F₂) P₂.1 := by
    change Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup P.valuationSubring) =
      NU.LocalTheory.ambientDecompositionGroup Q.valuationSubring
    rw [ambientDecompositionGroup_eq F₁ P,
      ambientDecompositionGroup_eq F₂ Q]
    exact map_decompositionGroup_primeCorrespondence theta P
  have hfinite₁ : LocalInvariants.ambientFinitePlace P₁ =
      finitePrime F₁ P := by
    let A := P.valuationSubring.comap F₁.field.val.toRingHom
    have hA : NU.LocalTheory.IsNontrivialValuation A :=
      absolutePrime_comap_nontrivial F₁ P
    apply (NU.LocalTheory.numberField_valuations A hA).unique
    · calc
        A = P.valuationSubring.comap
            (algebraMap F₁.field Omega) := by
          apply ValuationSubring.ext
          intro x
          rfl
        _ = NU.LocalTheory.primeValuationSubring
            (LocalInvariants.ambientFinitePlace P₁) :=
          (LocalInvariants.primeValuationSubring_ambientFinitePlace P₁).symm
    · exact (primeValuationSubring_finitePrime F₁ P).symm
  have hfinite₂ : LocalInvariants.ambientFinitePlace P₂ =
      finitePrime F₂ Q := by
    let A := Q.valuationSubring.comap F₂.field.val.toRingHom
    have hA : NU.LocalTheory.IsNontrivialValuation A :=
      absolutePrime_comap_nontrivial F₂ Q
    apply (NU.LocalTheory.numberField_valuations A hA).unique
    · calc
        A = Q.valuationSubring.comap
            (algebraMap F₂.field Omega) := by
          apply ValuationSubring.ext
          intro x
          rfl
        _ = NU.LocalTheory.primeValuationSubring
            (LocalInvariants.ambientFinitePlace P₂) :=
          (LocalInvariants.primeValuationSubring_ambientFinitePlace P₂).symm
    · exact (primeValuationSubring_finitePrime F₂ Q).symm
  have h := LocalInvariants.ambientInvariants_preserved
    R₁ R₂ theta P₁ P₂ hmap
  simpa only [LocalInvariants.ambientRationalPrime,
    LocalInvariants.ambientRamificationIndex,
    LocalInvariants.ambientResidueDegree, rationalPrime,
    absoluteRamificationIndex, absoluteResidueDegree,
    hfinite₁, hfinite₂, Q] using h

/-- Degree-one consequence of (L3). -/
theorem primeCorrespondence_degreeOne_iff
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) :
    IsAbsoluteDegreeOne F₁ (finitePrime F₁ P) ↔
      IsAbsoluteDegreeOne F₂
        (finitePrime F₂ (primeCorrespondence theta P)) := by
  have h := primeCorrespondence_invariants_L3 theta P
  simp only [IsAbsoluteDegreeOne, absoluteLocalDegree]
  rw [h.2.1, h.2.2]

/-- (L4), blueprint `int:local`: the corresponding local isomorphism carries
normalized arithmetic Frobenius lifts onto normalized arithmetic Frobenius
lifts. -/
theorem primeCorrespondence_frobeniusLift_L4
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (P : AbsolutePrime) (g : decompositionGroup F₁ P) :
    IsArithmeticFrobeniusLift F₁ P g ↔
      IsArithmeticFrobeniusLift F₂ (primeCorrespondence theta P)
        (decompositionGroupEquiv theta P g) := by
  let Q := primeCorrespondence theta P
  let P₁ : LocalInvariants.AmbientAbsolutePlace F₁.field Omega :=
    ⟨P.valuationSubring,
      (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
        ℚ F₁.field Omega P.valuationSubring).mp P.isFinite⟩
  let P₂ : LocalInvariants.AmbientAbsolutePlace F₂.field Omega :=
    ⟨Q.valuationSubring,
      (NU.LocalTheory.isAbsoluteFinitePlaceIn_iff_of_finite_extension
        ℚ F₂.field Omega Q.valuationSubring).mp Q.isFinite⟩
  let R₁ : LocalInvariants.AbsoluteGaloisActionRealization
      F₁.field Omega (absoluteGaloisGroup F₁) :=
    { closureEquiv := ambientClosureEquiv F₁
      galoisEquiv := (ambientAbsoluteGaloisEquiv F₁).symm
      action_compat := abstractGaloisCompat F₁ }
  let R₂ : LocalInvariants.AbsoluteGaloisActionRealization
      F₂.field Omega (absoluteGaloisGroup F₂) :=
    { closureEquiv := ambientClosureEquiv F₂
      galoisEquiv := (ambientAbsoluteGaloisEquiv F₂).symm
      action_compat := abstractGaloisCompat F₂ }
  have hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
      (NU.LocalTheory.ambientDecompositionGroup
        (G := absoluteGaloisGroup F₁) P₁.1) =
    NU.LocalTheory.ambientDecompositionGroup
      (G := absoluteGaloisGroup F₂) P₂.1 := by
    change Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup P.valuationSubring) =
      NU.LocalTheory.ambientDecompositionGroup Q.valuationSubring
    rw [ambientDecompositionGroup_eq F₁ P,
      ambientDecompositionGroup_eq F₂ Q]
    exact map_decompositionGroup_primeCorrespondence theta P
  have hfinite₁ : LocalInvariants.ambientFinitePlace P₁ =
      finitePrime F₁ P := by
    let A := P.valuationSubring.comap F₁.field.val.toRingHom
    have hA : NU.LocalTheory.IsNontrivialValuation A :=
      absolutePrime_comap_nontrivial F₁ P
    apply (NU.LocalTheory.numberField_valuations A hA).unique
    · calc
        A = P.valuationSubring.comap
            (algebraMap F₁.field Omega) := by
          apply ValuationSubring.ext
          intro x
          rfl
        _ = NU.LocalTheory.primeValuationSubring
            (LocalInvariants.ambientFinitePlace P₁) :=
          (LocalInvariants.primeValuationSubring_ambientFinitePlace P₁).symm
    · exact (primeValuationSubring_finitePrime F₁ P).symm
  have hfinite₂ : LocalInvariants.ambientFinitePlace P₂ =
      finitePrime F₂ Q := by
    let A := Q.valuationSubring.comap F₂.field.val.toRingHom
    have hA : NU.LocalTheory.IsNontrivialValuation A :=
      absolutePrime_comap_nontrivial F₂ Q
    apply (NU.LocalTheory.numberField_valuations A hA).unique
    · calc
        A = Q.valuationSubring.comap
            (algebraMap F₂.field Omega) := by
          apply ValuationSubring.ext
          intro x
          rfl
        _ = NU.LocalTheory.primeValuationSubring
            (LocalInvariants.ambientFinitePlace P₂) :=
          (LocalInvariants.primeValuationSubring_ambientFinitePlace P₂).symm
    · exact (primeValuationSubring_finitePrime F₂ Q).symm
  have frobenius_iff_actsAsPower :
      ∀ (F : NumberFieldInOmega) (S : AbsolutePrime)
          (u : decompositionGroup F S),
        IsArithmeticFrobeniusLift F S u ↔
          LocalInvariants.ActsAsPowerOnResidue S.valuationSubring u.1
            (NU.Chebotarev.PrimeIdeal.norm (finitePrime F S)) := by
    intro F S u
    constructor
    · intro hu x y hxy
      obtain ⟨z, hz, haction⟩ := absoluteResidueAction_mk F S u x
      have hzy : z = y := by
        apply Subtype.ext
        simpa using hz.trans hxy.symm
      rw [← hzy]
      exact haction.symm.trans
        (hu (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal S.valuationSubring) x))
    · intro hu z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨y, hy, haction⟩ := absoluteResidueAction_mk F S u x
      rw [haction]
      apply hu x y
      change (y : Omega) =
        (u.1.1 : RationalAbsoluteGaloisGroup) (x : Omega)
      exact hy
  have hg : g.1 ∈ NU.LocalTheory.ambientDecompositionGroup
      (G := absoluteGaloisGroup F₁) P₁.1 := by
    change g.1 ∈ NU.LocalTheory.ambientDecompositionGroup P.valuationSubring
    rw [ambientDecompositionGroup_eq F₁ P]
    exact g.2
  have hpower := LocalInvariants.arithmeticFrobeniusPower_preserved
    R₁ R₂ theta P₁ P₂ hmap g.1 hg
  change LocalInvariants.ActsAsPowerOnResidue P.valuationSubring g.1
      (NU.Chebotarev.PrimeIdeal.norm
        (LocalInvariants.ambientFinitePlace P₁)) ↔
    LocalInvariants.ActsAsPowerOnResidue Q.valuationSubring (theta g.1)
      (NU.Chebotarev.PrimeIdeal.norm
        (LocalInvariants.ambientFinitePlace P₂)) at hpower
  rw [hfinite₁, hfinite₂] at hpower
  rw [frobenius_iff_actsAsPower F₁ P g,
    frobenius_iff_actsAsPower F₂ Q
      (decompositionGroupEquiv theta P g)]
  simpa only [decompositionGroupEquiv_apply] using hpower

/-! ## Exact wrappers around the proved/current upstream declarations -/

/-- Chebotarev wrapper (`int:cheb`) against the proved real declaration
`NU.Chebotarev.chebotarev_dirichletDensity`. -/
theorem chebotarev_dirichletDensity
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (C : ConjClasses (Gal(L/K))) :
    NU.Chebotarev.HasDirichletDensity
      (NU.Chebotarev.frobeniusPrimeSet (K := K) (L := L) C)
      ((C.carrier.ncard : ℝ) / (Nat.card (Gal(L/K)) : ℝ)) := by
  exact NU.Chebotarev.chebotarev_dirichletDensity C

end

end NU.NeukirchUchida
