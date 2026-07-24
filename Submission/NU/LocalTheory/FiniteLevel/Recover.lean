import Submission.NU.LocalTheory.Packets.Stabilizer

/-!
# Cyclotomically oriented recovery at finite Galois levels

The recovery construction in this file is formed directly on the marked
subgroups `G_L ∩ C_ℓ`.  In particular, neither `packetImagesAtOddPrime` nor
`recoveredDecompositionCollection` mentions a cyclotomic field.  Actual
fields `L(μ_ℓ)` occur only in the comparison theorems at the end of the file.
-/

open IsDedekindDomain
open scoped NumberField

namespace NU.LocalTheory

noncomputable section

/-- A finite Galois intermediate field in the fixed algebraic closure.

The bottom intermediate field supplies the explicit inhabitant below, so
this bundle cannot become vacuous through missing typeclass instances. -/
structure GaloisLevel (K : Type*) [Field K] [NumberField K] where
  field : IntermediateField K (AlgebraicClosure K)
  finiteDimensional : FiniteDimensional K field
  numberField : NumberField field
  isGalois : IsGalois K field

attribute [instance] GaloisLevel.finiteDimensional
  GaloisLevel.numberField GaloisLevel.isGalois

/-- The identity finite Galois level. -/
noncomputable def trivialGaloisLevel (K : Type*) [Field K] [NumberField K] :
    GaloisLevel K where
  field := ⊥
  finiteDimensional := by infer_instance
  numberField := NumberField.of_module_finite K _
  isGalois := by infer_instance

/-- Inhabitation sanity check for finite Galois levels. -/
instance galoisLevelNonempty (K : Type*) [Field K] [NumberField K] :
    Nonempty (GaloisLevel K) :=
  ⟨trivialGaloisLevel K⟩

/-- Inclusion of finite Galois levels inside the fixed algebraic closure. -/
def GaloisLevel.LE {K : Type*} [Field K] [NumberField K]
    (L M : GaloisLevel K) : Prop :=
  L.field ≤ M.field

/-- A family is directed and cofinal among finite Galois intermediate
fields.  Nonemptiness is explicit, so an empty index type cannot satisfy the
predicate. -/
def IsCofinalGaloisSystem {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K) : Prop :=
  Nonempty ι ∧
    (∀ i j, ∃ k, (Λ i).LE (Λ k) ∧ (Λ j).LE (Λ k)) ∧
    (∀ L : GaloisLevel K, ∃ i, L.LE (Λ i))

/-- Restriction from the absolute Galois group to a finite Galois level. -/
noncomputable def absoluteRestriction {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) :
    Field.absoluteGaloisGroup K →* (L.field ≃ₐ[K] L.field) := by
  change (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    (L.field ≃ₐ[K] L.field)
  exact AlgEquiv.restrictNormalHom L.field

/-- Defining equation for absolute restriction. -/
theorem absoluteRestriction_apply {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (σ : Field.absoluteGaloisGroup K) (x : L.field) :
    ((absoluteRestriction L σ x : L.field) : AlgebraicClosure K) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ)
        (x : AlgebraicClosure K) :=
  AlgEquiv.restrictNormal_commutes
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ) L.field x

/-- The subgroup fixing a finite Galois level. -/
def levelKernel {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) : Subgroup (Field.absoluteGaloisGroup K) :=
  (absoluteRestriction L).ker

instance levelKernel_normal {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) : (levelKernel L).Normal :=
  MonoidHom.normal_ker (absoluteRestriction L)

/-- The image of a subgroup at a finite Galois level. -/
def finiteLevelImage {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Subgroup (L.field ≃ₐ[K] L.field) :=
  Subgroup.map (absoluteRestriction L) H

/-- The auxiliary indices used by the reconstruction: odd primes only. -/
abbrev OddPrime := {p : Nat.Primes // Odd (p : ℕ)}

instance oddPrimeFact (p : OddPrime) : Fact (p : ℕ).Prime :=
  ⟨p.1.2⟩

instance oddPrimeNeZero (p : OddPrime) : NeZero (p : ℕ) :=
  ⟨p.1.2.ne_zero⟩

/-- View an absolute Galois element as its underlying algebra equivalence. -/
@[reducible] def absoluteGaloisAlgEquiv {K : Type*} [Field K]
    (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  σ

/-- An absolute Galois element fixes every `n`-th root of unity. -/
def FixesRootsOfUnity (K : Type*) [Field K] (n : ℕ)
    (σ : Field.absoluteGaloisGroup K) : Prop :=
  ∀ ζ : AlgebraicClosure K, ζ ^ n = 1 →
    absoluteGaloisAlgEquiv σ ζ = ζ

/-- The genuine mod-`n` cyclotomic kernel. -/
def cyclotomicKernel (K : Type*) [Field K] (n : ℕ) :
    Subgroup (Field.absoluteGaloisGroup K) where
  carrier := {σ | FixesRootsOfUnity K n σ}
  one_mem' := by
    intro ζ hζ
    rfl
  mul_mem' := by
    intro σ τ hσ hτ ζ hζ
    rw [show absoluteGaloisAlgEquiv (σ * τ) =
      absoluteGaloisAlgEquiv σ * absoluteGaloisAlgEquiv τ from rfl,
      AlgEquiv.mul_apply, hτ ζ hζ, hσ ζ hζ]
  inv_mem' := by
    intro σ hσ ζ hζ
    let η : AlgebraicClosure K := absoluteGaloisAlgEquiv σ⁻¹ ζ
    have hη : η ^ n = 1 := by
      dsimp [η]
      calc
        (absoluteGaloisAlgEquiv σ⁻¹ ζ) ^ n =
            absoluteGaloisAlgEquiv σ⁻¹ (ζ ^ n) := by
              symm
              exact map_pow (absoluteGaloisAlgEquiv σ⁻¹) ζ n
        _ = absoluteGaloisAlgEquiv σ⁻¹ 1 := by rw [hζ]
        _ = 1 := map_one _
    have hfix : absoluteGaloisAlgEquiv σ η = η := hσ η hη
    have hcancel : absoluteGaloisAlgEquiv σ η = ζ := by
      dsimp [η]
      change absoluteGaloisAlgEquiv σ
        ((absoluteGaloisAlgEquiv σ).symm ζ) = ζ
      exact (absoluteGaloisAlgEquiv σ).apply_symm_apply ζ
    exact hfix.symm.trans hcancel

/-- A genuine odd-prime cyclotomic kernel is open. -/
theorem cyclotomicKernel_isOpen (K : Type*) [Field K] (p : OddPrime) :
    IsOpen (cyclotomicKernel K (p : ℕ) :
      Set (Field.absoluteGaloisGroup K)) := by
  haveI : Algebra.IsIntegral K (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.isIntegral
  let roots := Polynomial.nthRootsFinset (p : ℕ)
    (1 : AlgebraicClosure K)
  have hopen : IsOpen (⋂ ζ ∈ roots,
      {σ : Field.absoluteGaloisGroup K |
        absoluteGaloisAlgEquiv σ ζ = ζ}) := by
    apply isOpen_biInter_finset
    intro ζ _
    change IsOpen (MulAction.stabilizer
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ζ :
        Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
    exact @stabilizer_isOpen_of_isIntegral K (AlgebraicClosure K)
      _ _ _ this ζ
  have heq : (cyclotomicKernel K (p : ℕ) :
      Set (Field.absoluteGaloisGroup K)) =
      ⋂ ζ ∈ roots, {σ : Field.absoluteGaloisGroup K |
        absoluteGaloisAlgEquiv σ ζ = ζ} := by
    ext σ
    simp only [cyclotomicKernel, FixesRootsOfUnity,
      Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h ζ hζ
      apply h ζ
      exact (Polynomial.mem_nthRootsFinset (R := AlgebraicClosure K)
        p.2.pos 1).1 (by simpa [roots] using hζ)
    · intro h ζ hζ
      apply h ζ
      simpa [roots] using
        (Polynomial.mem_nthRootsFinset (R := AlgebraicClosure K)
          p.2.pos 1).2 hζ
  rw [heq]
  exact hopen

/-- A genuine odd-prime cyclotomic kernel is closed. -/
theorem cyclotomicKernel_isClosed (K : Type*) [Field K] (p : OddPrime) :
    IsClosed (cyclotomicKernel K (p : ℕ) :
      Set (Field.absoluteGaloisGroup K)) := by
  exact (cyclotomicKernel K (p : ℕ)).isClosed_of_isOpen
    (cyclotomicKernel_isOpen K p)

/-- A genuine odd-prime cyclotomic kernel is normal. -/
theorem cyclotomicKernel_normal (K : Type*) [Field K] (p : OddPrime) :
    (cyclotomicKernel K (p : ℕ)).Normal := by
  constructor
  intro σ hσ g ζ hζ
  have hroot : (absoluteGaloisAlgEquiv g⁻¹ ζ) ^ (p : ℕ) = 1 := by
    rw [← map_pow, hζ, map_one]
  change absoluteGaloisAlgEquiv (g * σ * g⁻¹) ζ = ζ
  rw [show absoluteGaloisAlgEquiv (g * σ * g⁻¹) =
    absoluteGaloisAlgEquiv g * absoluteGaloisAlgEquiv σ *
      absoluteGaloisAlgEquiv g⁻¹ from rfl,
    AlgEquiv.mul_apply, AlgEquiv.mul_apply, hσ _ hroot]
  exact (absoluteGaloisAlgEquiv g).apply_symm_apply ζ

/-- Explicit odd-prime cyclotomic input for reconstruction.

The defining equality rules out arbitrary or trivial marked subgroups.  The
canonical bundle below is an explicit inhabitant. -/
structure CyclotomicOrientation (K : Type*) [Field K] where
  kernel : OddPrime → Subgroup (Field.absoluteGaloisGroup K)
  kernel_eq_cyclotomic :
    ∀ p, kernel p = cyclotomicKernel K (p : ℕ)
  kernel_isOpen :
    ∀ p, IsOpen (kernel p : Set (Field.absoluteGaloisGroup K))
  kernel_isClosed :
    ∀ p, IsClosed (kernel p : Set (Field.absoluteGaloisGroup K))
  kernel_normal :
    ∀ p, (kernel p).Normal

/-- The canonical orientation supplied by the genuine odd-prime kernels. -/
noncomputable def canonicalCyclotomicOrientation (K : Type*) [Field K] :
    CyclotomicOrientation K where
  kernel p := cyclotomicKernel K (p : ℕ)
  kernel_eq_cyclotomic _ := rfl
  kernel_isOpen p := cyclotomicKernel_isOpen K p
  kernel_isClosed p := cyclotomicKernel_isClosed K p
  kernel_normal p := cyclotomicKernel_normal K p

/-- Inhabitation sanity check for the explicit orientation bundle. -/
instance cyclotomicOrientationNonempty (K : Type*) [Field K] :
    Nonempty (CyclotomicOrientation K) :=
  ⟨canonicalCyclotomicOrientation K⟩

instance orientationKernel_normal {K : Type*} [Field K]
    (orientation : CyclotomicOrientation K) (p : OddPrime) :
    (orientation.kernel p).Normal :=
  orientation.kernel_normal p

/-- The marked subgroup `G_L ∩ C_ℓ` on which the packet construction is
actually performed. -/
def orientedCyclotomicLevel {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) : Subgroup (Field.absoluteGaloisGroup K) :=
  levelKernel L ⊓ orientation.kernel p

/-- Comparison with the genuine kernel, without replacing the marked
subgroup in the construction. -/
theorem orientedCyclotomicLevel_eq_genuine
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    orientedCyclotomicLevel orientation L p =
      levelKernel L ⊓ cyclotomicKernel K (p : ℕ) := by
  rw [orientedCyclotomicLevel, orientation.kernel_eq_cyclotomic p]

/-- Backwards-compatible name for the marked-level equality. -/
theorem orientedCyclotomicLevel_eq
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    orientedCyclotomicLevel orientation L p =
      levelKernel L ⊓ cyclotomicKernel K (p : ℕ) :=
  orientedCyclotomicLevel_eq_genuine orientation L p

instance orientedCyclotomicLevel_normal
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) : (orientedCyclotomicLevel orientation L p).Normal := by
  unfold orientedCyclotomicLevel
  infer_instance

/-- The finite quotient `G_K/(G_L ∩ C_ℓ)`, constructed solely from the
marked subgroup. -/
abbrev orientedCyclotomicQuotient
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :=
  Field.absoluteGaloisGroup K ⧸ orientedCyclotomicLevel orientation L p

/-- Restriction from the marked cyclotomic quotient to `Gal(L/K)`. -/
noncomputable def orientedRestriction
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    orientedCyclotomicQuotient orientation L p →*
      (L.field ≃ₐ[K] L.field) :=
  QuotientGroup.lift (orientedCyclotomicLevel orientation L p)
    (absoluteRestriction L) (by
      intro g hg
      exact hg.1)

/-- Defining equation for restriction from the marked quotient. -/
@[simp]
theorem orientedRestriction_mk
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (g : Field.absoluteGaloisGroup K) :
    orientedRestriction orientation L p (QuotientGroup.mk g) =
      absoluteRestriction L g := by
  unfold orientedRestriction
  apply QuotientGroup.lift_mk

/-- Restriction of the marked quotient onto the finite Galois level is
surjective; this rules out a trivial quotient map in the recovery data. -/
theorem orientedRestriction_surjective
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    Function.Surjective (orientedRestriction orientation L p) := by
  intro σ
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
    (AlgebraicClosure K) σ
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [orientedRestriction_mk]
  exact hg

private noncomputable def topologicalAbelianizationTransport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) :
    TopologicalAbelianization G ≃* TopologicalAbelianization H := by
  have hrange : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  have hcomm : Subgroup.map e.toMonoidHom (commutator G) = commutator H := by
    rw [map_commutator_eq, hrange]
    rfl
  have hclosure : Subgroup.map e.toMonoidHom
      (Subgroup.topologicalClosure (commutator G)) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    change e '' closure (commutator G : Set G) =
      closure (commutator H : Set H)
    calc
      e '' closure (commutator G : Set G) =
          closure (e '' (commutator G : Set G)) := by
            exact e.toHomeomorph.image_closure _
      _ = closure (commutator H : Set H) := by
        congr 1
        change (Subgroup.map e.toMonoidHom (commutator G) : Set H) = _
        exact congrArg (fun S : Subgroup H => (S : Set H)) hcomm
  exact QuotientGroup.congr _ _ e.toMulEquiv hclosure

@[simp]
private theorem topologicalAbelianizationTransport_mk
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (g : G) :
    topologicalAbelianizationTransport e (QuotientGroup.mk g) =
      QuotientGroup.mk (e g) := by
  rfl

private def modNTransport
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (f : A →+ B) : ModN A n →ₗ[ZMod n] ModN B n :=
  (ModN.liftEquiv').symm ⟨(ModN.mkQ n).comp f, by
    intro a
    change n • ModN.mkQ n (f a) = 0
    calc
      n • ModN.mkQ n (f a) =
          (n : ZMod n) • ModN.mkQ n (f a) :=
        (Nat.cast_smul_eq_nsmul (ZMod n) n _).symm
      _ = 0 := by rw [ZMod.natCast_self, zero_smul]⟩

@[simp]
private theorem modNTransport_mkQ
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (f : A →+ B) (a : A) :
    modNTransport n f (ModN.mkQ n a) = ModN.mkQ n (f a) := by
  rfl

-- Quotient induction through `ModN` needs extra elaboration budget.
set_option maxHeartbeats 800000 in
private theorem modNTransport_comp_symm
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (a : A ≃+ B) :
    (modNTransport n a.toAddMonoidHom).comp
        (modNTransport n a.symm.toAddMonoidHom) = LinearMap.id := by
  ext x
  obtain ⟨z, rfl⟩ := (LinearMap.range
    (LinearMap.lsmul ℤ B (n : ℤ))).mkQ_surjective x
  change modNTransport n a.toAddMonoidHom
    (modNTransport n a.symm.toAddMonoidHom (ModN.mkQ n z)) =
      ModN.mkQ n z
  rw [modNTransport_mkQ, modNTransport_mkQ]
  change ModN.mkQ n (a (a.symm z)) = ModN.mkQ n z
  rw [a.apply_symm_apply]

/-- A continuous group equivalence induces the canonical linear equivalence
on elementary quotients. -/
noncomputable def elementaryQuotientTransport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) :
    ElementaryQuotient G n ≃ₗ[ZMod n] ElementaryQuotient H n := by
  let a : Additive (TopologicalAbelianization G) ≃+
      Additive (TopologicalAbelianization H) :=
    (topologicalAbelianizationTransport e).toAdditive
  let f : ElementaryQuotient G n →ₗ[ZMod n] ElementaryQuotient H n :=
    modNTransport n a.toAddMonoidHom
  let g : ElementaryQuotient H n →ₗ[ZMod n] ElementaryQuotient G n :=
    modNTransport n a.symm.toAddMonoidHom
  have hfg : f.comp g = LinearMap.id :=
    modNTransport_comp_symm n a
  have hgf : g.comp f = LinearMap.id := by
    simpa [f, g] using modNTransport_comp_symm n a.symm
  exact LinearEquiv.ofLinear f g hfg hgf

/-- Defining equation for transport on elementary classes. -/
@[simp]
theorem elementaryQuotientTransport_elementaryClass
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (g : G) :
    elementaryQuotientTransport n e (elementaryClass n g) =
      elementaryClass n (e g) := by
  change elementaryQuotientTransport n e (ModN.mkQ n
      (Additive.ofMul (QuotientGroup.mk g))) = _
  simp [elementaryQuotientTransport, elementaryClass]

/-- Conjugation by an absolute element preserves the marked level. -/
def conjugateInOrientedCyclotomicLevel
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (g : Field.absoluteGaloisGroup K)
    (h : orientedCyclotomicLevel orientation L p) :
    orientedCyclotomicLevel orientation L p :=
  ⟨g * (h : Field.absoluteGaloisGroup K) * g⁻¹,
    (orientedCyclotomicLevel_normal orientation L p).conj_mem
      (h : Field.absoluteGaloisGroup K) h.property g⟩

private theorem orientedElementaryClass_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Function.Surjective (elementaryClass (G := G) n) := by
  intro x
  obtain ⟨y, rfl⟩ :=
    (LinearMap.range (LinearMap.lsmul ℤ
      (Additive (TopologicalAbelianization G)) (n : ℤ))).mkQ_surjective x
  cases y with
  | ofMul q =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, rfl⟩

private def orientedElementaryClassHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : G →* Multiplicative (ElementaryQuotient G n) :=
  AddMonoidHom.toMultiplicativeRight <|
    (ModN.mkQ n).comp <| MonoidHom.toAdditiveLeft <|
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator G))

@[simp]
private theorem orientedElementaryClassHom_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (g : G) :
    (orientedElementaryClassHom n g).toAdd = elementaryClass n g :=
  rfl

private theorem orientedElementaryClass_conj
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (g h : G) :
    elementaryClass n (g * h * g⁻¹) = elementaryClass n h := by
  have hconj : orientedElementaryClassHom n (g * h * g⁻¹) =
      orientedElementaryClassHom n h := by
    rw [map_mul, map_mul, map_inv]
    simp [mul_assoc]
  exact congrArg Multiplicative.toAdd hconj

private noncomputable def conjugationOnOrientedCyclotomicLevel
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (g : Field.absoluteGaloisGroup K) :
    orientedCyclotomicLevel orientation L p ≃ₜ*
      orientedCyclotomicLevel orientation L p where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

@[simp]
private theorem conjugationOnOrientedCyclotomicLevel_apply
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (g : Field.absoluteGaloisGroup K)
    (h : orientedCyclotomicLevel orientation L p) :
    conjugationOnOrientedCyclotomicLevel orientation L p g h =
      conjugateInOrientedCyclotomicLevel orientation L p g h := by
  apply Subtype.ext
  exact MulAut.conjNormal_apply g h

private noncomputable def orientedPacketActionHom
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    Field.absoluteGaloisGroup K →*
      (ElementaryQuotient (orientedCyclotomicLevel orientation L p) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
        ElementaryQuotient (orientedCyclotomicLevel orientation L p) (p : ℕ)) where
  toFun g := elementaryQuotientTransport (p : ℕ)
    (conjugationOnOrientedCyclotomicLevel orientation L p g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := orientedElementaryClass_surjective (p : ℕ) x
    rw [elementaryQuotientTransport_elementaryClass]
    change elementaryClass (p : ℕ)
      (conjugateInOrientedCyclotomicLevel orientation L p 1 h) =
        elementaryClass (p : ℕ) h
    congr 1
  map_mul' := by
    intro g k
    apply LinearEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := orientedElementaryClass_surjective (p : ℕ) x
    simp only [elementaryQuotientTransport_elementaryClass,
      conjugationOnOrientedCyclotomicLevel_apply, LinearEquiv.mul_apply]
    congr 1

set_option maxHeartbeats 8000000 in
private theorem orientedPacketActionHom_kills
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    orientedCyclotomicLevel orientation L p ≤
      (orientedPacketActionHom orientation L p).ker := by
  intro g hg
  change orientedPacketActionHom orientation L p g = 1
  apply LinearEquiv.ext
  intro x
  obtain ⟨h, rfl⟩ := orientedElementaryClass_surjective (p : ℕ) x
  rw [show orientedPacketActionHom orientation L p g =
      elementaryQuotientTransport (p : ℕ)
        (conjugationOnOrientedCyclotomicLevel orientation L p g) from rfl,
    elementaryQuotientTransport_elementaryClass]
  change elementaryClass (p : ℕ)
    (conjugateInOrientedCyclotomicLevel orientation L p g h) =
      elementaryClass (p : ℕ) h
  exact orientedElementaryClass_conj (p : ℕ) ⟨g, hg⟩ h

/-- The conjugation action of the marked finite quotient on the elementary
quotient of `G_L ∩ C_ℓ`. -/
noncomputable def orientedPacketAction
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    orientedCyclotomicQuotient orientation L p →*
      (ElementaryQuotient (orientedCyclotomicLevel orientation L p) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
        ElementaryQuotient (orientedCyclotomicLevel orientation L p) (p : ℕ)) :=
  QuotientGroup.lift (orientedCyclotomicLevel orientation L p)
    (orientedPacketActionHom orientation L p)
    (orientedPacketActionHom_kills orientation L p)

/-- Defining equation for the marked packet action on elementary classes.
It pins the action to conjugation and excludes the trivial action model. -/
@[simp]
theorem orientedPacketAction_elementaryClass
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (g : Field.absoluteGaloisGroup K)
    (h : orientedCyclotomicLevel orientation L p) :
    orientedPacketAction orientation L p (QuotientGroup.mk g)
        (elementaryClass (p : ℕ) h) =
      elementaryClass (p : ℕ)
        (conjugateInOrientedCyclotomicLevel orientation L p g h) := by
  rw [orientedPacketAction, QuotientGroup.lift_mk]
  exact elementaryQuotientTransport_elementaryClass (p : ℕ)
    (conjugationOnOrientedCyclotomicLevel orientation L p g) h

/-- Transport a marked-level packet by the quotient action. -/
noncomputable def conjugateOrientedPacket
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) (σ : orientedCyclotomicQuotient orientation L p)
    (P : GroupSubspace (orientedCyclotomicLevel orientation L p) (p : ℕ)) :
    GroupSubspace (orientedCyclotomicLevel orientation L p) (p : ℕ) :=
  P.map (orientedPacketAction orientation L p σ).toLinearMap

/-- Stabilizer of a packet formed on the marked subgroup. -/
noncomputable def orientedPacketStabilizer
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime)
    (P : GroupSubspace (orientedCyclotomicLevel orientation L p) (p : ℕ)) :
    Subgroup (orientedCyclotomicQuotient orientation L p) where
  carrier := {σ | conjugateOrientedPacket orientation L p σ P = P}
  one_mem' := by
    simp [conjugateOrientedPacket]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq] at hσ hτ ⊢
    change P.map (orientedPacketAction orientation L p σ).toLinearMap = P at hσ
    change P.map (orientedPacketAction orientation L p τ).toLinearMap = P at hτ
    calc
      conjugateOrientedPacket orientation L p (σ * τ) P =
          P.map (((orientedPacketAction orientation L p σ).toLinearMap).comp
            (orientedPacketAction orientation L p τ).toLinearMap) := by
              rw [conjugateOrientedPacket, map_mul]
              congr 1
      _ = (P.map (orientedPacketAction orientation L p τ).toLinearMap).map
          (orientedPacketAction orientation L p σ).toLinearMap :=
            Submodule.map_comp _ _ _
      _ = P := by rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ ⊢
    change P.map (orientedPacketAction orientation L p σ).toLinearMap = P at hσ
    calc
      conjugateOrientedPacket orientation L p σ⁻¹ P =
          P.map (orientedPacketAction orientation L p σ).symm.toLinearMap := by
            rw [conjugateOrientedPacket, map_inv]
            congr 1
      _ = (P.map (orientedPacketAction orientation L p σ).toLinearMap).map
          (orientedPacketAction orientation L p σ).symm.toLinearMap := by rw [hσ]
      _ = P := by
        rw [← Submodule.map_comp]
        convert Submodule.map_id P using 1
        ext x
        simp

/-- Images in `Gal(L/K)` of stabilizers of packets formed directly on the
marked group `G_L ∩ C_ℓ`. -/
noncomputable def packetImagesAtOddPrime
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) : Set (Subgroup (L.field ≃ₐ[K] L.field)) :=
  {D | ∃ P : GroupSubspace
      (orientedCyclotomicLevel orientation L p) (p : ℕ),
    IsPacket (p : ℕ) P ∧
      D = Subgroup.map (orientedRestriction orientation L p)
        (orientedPacketStabilizer orientation L p P)}

/-- The recovered finite decomposition collection.  Its packet planes,
actions, stabilizers, and projections all depend on the orientation. -/
noncomputable def recoveredDecompositionCollection
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K) :
    Set (Subgroup (L.field ≃ₐ[K] L.field)) :=
  {D | ∃ p : OddPrime, D ∈ packetImagesAtOddPrime orientation L p}

/-- Unfolded membership makes the orientation dependence literal: removing
`orientation` removes the group on which `P` and its action are typed. -/
@[simp]
theorem mem_recoveredDecompositionCollection
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (D : Subgroup (L.field ≃ₐ[K] L.field)) :
    D ∈ recoveredDecompositionCollection orientation L ↔
      ∃ p : OddPrime,
        ∃ P : GroupSubspace
            (orientedCyclotomicLevel orientation L p) (p : ℕ),
          IsPacket (p : ℕ) P ∧
            D = Subgroup.map (orientedRestriction orientation L p)
              (orientedPacketStabilizer orientation L p P) :=
  Iff.rfl

/-- There is an odd auxiliary prime different from any prescribed residue
characteristic. -/
theorem exists_oddPrime_ne (r : ℕ) :
    ∃ p : OddPrime, (p : ℕ) ≠ r := by
  obtain ⟨q, hqbound, hqprime⟩ :=
    Nat.exists_infinite_primes (max 3 (r + 1))
  have hq3 : 3 ≤ q := (le_max_left 3 (r + 1)).trans hqbound
  have hqr : r < q := by
    omega
  exact ⟨⟨⟨q, hqprime⟩, hqprime.odd_iff.mpr hq3⟩, ne_of_gt hqr⟩

/-- Finite decomposition groups away from one fixed auxiliary prime. -/
def decompositionCollectionAway
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (p : OddPrime) :
    Set (Subgroup (M ≃ₐ[K] M)) :=
  {D | ∃ w : FinitePlace M,
    residueCharacteristic w ≠ (p : ℕ) ∧ D = decompositionGroup K w}

/-! ## Comparison with the arithmetic cyclotomic overfield

`CyclotomicField` first appears here.  Nothing above uses an arithmetic model
of the marked subgroup. -/

/-- The chosen-root fact formerly used by the arithmetic construction,
retained in existential form for comparison proofs so no arithmetic choice
enters the marked-kernel construction. -/
theorem exists_cyclotomicPrimitiveRoot_forComparison
    (L : Type*) [Field L] [NumberField L] (n : ℕ) [NeZero n] :
    ∃ ζ : CyclotomicField n L, IsPrimitiveRoot ζ n :=
  IsCyclotomicExtension.exists_isPrimitiveRoot L (CyclotomicField n L)
    (S := {n}) (n := n) (Set.mem_singleton n) (NeZero.ne n)

/-- The arithmetic comparison field `L(μ_ℓ)` is Galois over `K`. -/
theorem cyclotomicOverfield_isGalois_forComparison
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    IsGalois K (CyclotomicField (p : ℕ) L.field) := by
  let A := AlgebraicClosure K
  let roots : Set A :=
    {x | ∃ n ∈ ({(p : ℕ)} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  let R : IntermediateField K A := IntermediateField.adjoin K roots
  have hroot : ∀ n ∈ ({(p : ℕ)} : Set ℕ), n ≠ 0 →
      ∃ r : A, IsPrimitiveRoot r n := by
    intro n hn _
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot A (p : ℕ)
  letI : IsCyclotomicExtension ({(p : ℕ)} : Set ℕ) K R :=
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({(p : ℕ)} : Set ℕ) K A hroot
  letI : IsGalois K R :=
    IsCyclotomicExtension.isGalois ({(p : ℕ)} : Set ℕ) K R
  let E₀ : IntermediateField K A := L.field ⊔ R
  letI : Normal K E₀ := by
    dsimp [E₀]
    infer_instance
  letI : Algebra.IsSeparable K E₀ := by
    dsimp [E₀]
    infer_instance
  letI : IsGalois K E₀ := ⟨⟩
  let E : IntermediateField L.field A :=
    IntermediateField.adjoin L.field roots
  have hE : E.restrictScalars K = E₀ := by
    apply le_antisymm
    · intro x hx
      change x ∈ E at hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          exact ((le_sup_right : R ≤ E₀)
            (IntermediateField.subset_adjoin K roots hx))
      | algebraMap x => exact (le_sup_left : L.field ≤ E₀) x.property
      | add x y _ _ hx hy => exact E₀.add_mem hx hy
      | mul x y _ _ hx hy => exact E₀.mul_mem hx hy
      | inv x _ hx => exact E₀.inv_mem hx
    · apply sup_le
      · intro x hx
        change x ∈ E
        exact IntermediateField.algebraMap_mem E ⟨x, hx⟩
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        change x ∈ E
        exact IntermediateField.subset_adjoin L.field roots hx
  letI : IsGalois K E := by
    have h : IsGalois K (E.restrictScalars K) := by
      rw [hE]
      infer_instance
    exact h
  have hCE : Nonempty
      (CyclotomicField (p : ℕ) L.field ≃ₐ[L.field] E) :=
    IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
      ({(p : ℕ)} : Set ℕ) L.field
      (CyclotomicField (p : ℕ) L.field) A
  let eK : CyclotomicField (p : ℕ) L.field ≃ₐ[K] E :=
    hCE.some.restrictScalars K
  exact eK.transfer_galois.mpr (inferInstance : IsGalois K E)

private theorem residueCharacteristic_eq_absNorm_under
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    residueCharacteristic v = Ideal.absNorm (Ideal.under ℤ v.asIdeal) := by
  letI : Algebra (𝓞 K) (primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (HeightOneSpectrum.valuationSubringAtPrime K v) from inferInstance
  letI : IsLocalization.AtPrime (primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (HeightOneSpectrum.valuationSubringAtPrime K v) v.asIdeal from inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (primeValuationSubring v)
  calc
    residueCharacteristic v = ringChar ((𝓞 K) ⧸ v.asIdeal) := by
      rw [residueCharacteristic, ringChar.eq_iff]
      exact (e.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 K) ⧸ v.asIdeal))
    _ = Ideal.absNorm (Ideal.under ℤ v.asIdeal) := Ideal.ringChar_quot _

private theorem residueCharacteristic_restrictFinitePlace
    (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : FinitePlace M) :
    residueCharacteristic (restrictFinitePlace L w) =
      residueCharacteristic w := by
  rw [residueCharacteristic_eq_absNorm_under,
    residueCharacteristic_eq_absNorm_under, restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

private theorem exists_finitePlace_over
    (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : FinitePlace L) :
    ∃ v : FinitePlace M, restrictFinitePlace L v = w := by
  let q := Classical.choice
    (w.asIdeal.nonempty_primesOver (S := 𝓞 M))
  have hq0 : q.1 ≠ ⊥ := by
    intro h
    apply w.ne_bot
    rw [q.2.2.over]
    change Ideal.comap (algebraMap (𝓞 L) (𝓞 M)) q.1 = ⊥
    rw [h]
    exact Ideal.comap_bot_of_injective
      (algebraMap (𝓞 L) (𝓞 M))
      (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 M))
  let v : FinitePlace M := ⟨q.1, q.2.1, hq0⟩
  refine ⟨v, ?_⟩
  apply HeightOneSpectrum.ext
  exact q.2.2.over.symm

/-- Transport a plane along a continuous group equivalence. -/
noncomputable def transportGroupSubspace
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (P : GroupSubspace G n) :
    GroupSubspace H n :=
  P.map (elementaryQuotientTransport n e).toLinearMap

private def comparisonRoots (K : Type*) [Field K] (p : OddPrime) :
    Set (AlgebraicClosure K) :=
  {x | ∃ n ∈ ({(p : ℕ)} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}

private noncomputable def comparisonRootField
    (K : Type*) [Field K] (p : OddPrime) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K (comparisonRoots K p)

private noncomputable def comparisonE0
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    IntermediateField K (AlgebraicClosure K) :=
  L.field ⊔ comparisonRootField K p

private noncomputable def comparisonEL
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    IntermediateField L.field (AlgebraicClosure K) :=
  IntermediateField.adjoin L.field (comparisonRoots K p)

private theorem comparisonEL_restrict
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    (comparisonEL L p).restrictScalars K = comparisonE0 L p := by
  apply le_antisymm
  · intro x hx
    change x ∈ comparisonEL L p at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        exact ((le_sup_right : comparisonRootField K p ≤ comparisonE0 L p)
          (IntermediateField.subset_adjoin K (comparisonRoots K p) hx))
    | algebraMap x => exact (le_sup_left : L.field ≤ comparisonE0 L p) x.property
    | add x y _ _ hx hy => exact (comparisonE0 L p).add_mem hx hy
    | mul x y _ _ hx hy => exact (comparisonE0 L p).mul_mem hx hy
    | inv x _ hx => exact (comparisonE0 L p).inv_mem hx
  · apply sup_le
    · intro x hx
      change x ∈ comparisonEL L p
      exact IntermediateField.algebraMap_mem (comparisonEL L p) ⟨x, hx⟩
    · change IntermediateField.adjoin K (comparisonRoots K p) ≤
        (comparisonEL L p).restrictScalars K
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change x ∈ comparisonEL L p
      exact IntermediateField.subset_adjoin L.field (comparisonRoots K p) hx

private noncomputable def comparisonCycloEquiv
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    CyclotomicField (p : ℕ) L.field ≃ₐ[L.field] comparisonEL L p :=
  (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
    ({(p : ℕ)} : Set ℕ) L.field
    (CyclotomicField (p : ℕ) L.field) (AlgebraicClosure K)).some

private theorem comparison_fixesEL
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hL : ∀ x : L.field, σ (x : AlgebraicClosure K) = x)
    (hroots : ∀ x : AlgebraicClosure K, x ^ (p : ℕ) = 1 → σ x = x) :
    ∀ y ∈ comparisonEL L p, σ y = y := by
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨n, hn, hn0, hx⟩
      subst n
      exact hroots x hx
  | algebraMap x => exact hL x
  | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
  | mul x y _ _ hx hy => simpa using congrArg₂ (· * ·) hx hy
  | inv x _ hx => simpa using congrArg Inv.inv hx

private noncomputable def comparisonLevelToAutEL
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    orientedCyclotomicLevel o L p ≃*
      (AlgebraicClosure K ≃ₐ[comparisonEL L p] AlgebraicClosure K) where
  toFun u :=
    { (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from u.1) with
      commutes' := fun x => by
        let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := u.1
        have hL : ∀ z : L.field, σ (z : AlgebraicClosure K) = z := by
          intro z
          have hk := MonoidHom.mem_ker.mp u.property.1
          have happ := DFunLike.congr_fun hk z
          have hv := congrArg Subtype.val happ
          rw [absoluteRestriction_apply] at hv
          exact hv
        have hxE : (x : AlgebraicClosure K) ∈ comparisonEL L p := x.property
        have hc : u.1 ∈ cyclotomicKernel K (p : ℕ) := by
          rw [← o.kernel_eq_cyclotomic p]
          exact u.property.2
        exact comparison_fixesEL L p σ hL (fun z hz => hc z hz) x hxE }
  invFun τ := by
    let σ : Field.absoluteGaloisGroup K :=
      (τ.restrictScalars L.field).restrictScalars K
    refine ⟨σ, ?_⟩
    change σ ∈ levelKernel L ∧ σ ∈ o.kernel p
    constructor
    · change absoluteRestriction L σ = 1
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [absoluteRestriction_apply]
      simpa [σ] using
        τ.commutes ⟨algebraMap L.field (AlgebraicClosure K) x,
          IntermediateField.algebraMap_mem (comparisonEL L p) x⟩
    · rw [o.kernel_eq_cyclotomic]
      intro ζ hζ
      simpa [σ] using
        τ.commutes ⟨ζ, IntermediateField.subset_adjoin L.field (comparisonRoots K p)
          ⟨(p : ℕ), Set.mem_singleton _, p.1.2.ne_zero, hζ⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  right_inv τ := by
    apply AlgEquiv.ext
    intro x
    rfl
  map_mul' _ _ := by
    apply AlgEquiv.ext
    intro x
    rfl

private noncomputable instance comparisonEL_scalarTower
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    IsScalarTower K (comparisonEL L p) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private noncomputable instance comparisonEL_isAlgClosure
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    IsAlgClosure (comparisonEL L p) (AlgebraicClosure K) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (comparisonEL L p)⟩

private noncomputable instance comparisonEL_isGalois
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) : IsGalois K (comparisonEL L p) := by
  let eK : CyclotomicField (p : ℕ) L.field ≃ₐ[K] comparisonEL L p :=
    (comparisonCycloEquiv L p).restrictScalars K
  exact eK.transfer_galois.mp
    (cyclotomicOverfield_isGalois_forComparison L p)

private noncomputable def comparisonClosureRingEquiv
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃+*
      AlgebraicClosure K := by
  exact IsAlgClosure.equivOfEquiv
    (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
    (AlgebraicClosure K) (comparisonCycloEquiv L p).toRingEquiv

private noncomputable def comparisonAutELToAbsolute
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    (AlgebraicClosure K ≃ₐ[comparisonEL L p] AlgebraicClosure K) ≃*
      Field.absoluteGaloisGroup (CyclotomicField (p : ℕ) L.field) where
  toFun τ := by
    let j := comparisonClosureRingEquiv L p
    let r : AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃+*
        AlgebraicClosure (CyclotomicField (p : ℕ) L.field) :=
      j.trans (τ.toRingEquiv.trans j.symm)
    exact
      { r with
        commutes' := fun c => by
          change j.symm (τ (j (algebraMap
            (CyclotomicField (p : ℕ) L.field)
            (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) c))) =
              algebraMap (CyclotomicField (p : ℕ) L.field)
                (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) c
          apply j.injective
          rw [j.apply_symm_apply]
          change τ (j (algebraMap (CyclotomicField (p : ℕ) L.field)
            (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) c)) = _
          have hj : j (algebraMap (CyclotomicField (p : ℕ) L.field)
              (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) c) =
            algebraMap (comparisonEL L p) (AlgebraicClosure K)
              (comparisonCycloEquiv L p c) := by
            dsimp [j, comparisonClosureRingEquiv]
            exact IsAlgClosure.equivOfEquiv_algebraMap
              (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
              (AlgebraicClosure K) (comparisonCycloEquiv L p).toRingEquiv c
          rw [hj]
          exact τ.commutes (comparisonCycloEquiv L p c) }
  invFun σ := by
    let j := comparisonClosureRingEquiv L p
    let r : AlgebraicClosure K ≃+* AlgebraicClosure K :=
      j.symm.trans ((show AlgebraicClosure
        (CyclotomicField (p : ℕ) L.field) ≃ₐ[
          CyclotomicField (p : ℕ) L.field]
          AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from σ).toRingEquiv.trans j)
    exact
      { r with
        commutes' := fun e => by
          obtain ⟨c, rfl⟩ := (comparisonCycloEquiv L p).surjective e
          let cA := algebraMap (CyclotomicField (p : ℕ) L.field)
            (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) c
          let eA := algebraMap (comparisonEL L p) (AlgebraicClosure K)
            (comparisonCycloEquiv L p c)
          have hj : j cA = eA :=
            IsAlgClosure.equivOfEquiv_algebraMap
              (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
              (AlgebraicClosure K) (comparisonCycloEquiv L p).toRingEquiv c
          have hjs : j.symm eA = cA := by
            rw [← hj, j.symm_apply_apply]
          change j ((show AlgebraicClosure
            (CyclotomicField (p : ℕ) L.field) ≃ₐ[
              CyclotomicField (p : ℕ) L.field]
              AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from σ)
                (j.symm eA)) = eA
          rw [hjs, (show AlgebraicClosure
            (CyclotomicField (p : ℕ) L.field) ≃ₐ[
              CyclotomicField (p : ℕ) L.field]
              AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from σ).commutes]
          exact hj }
  left_inv τ := by
    apply AlgEquiv.ext
    intro x
    simp [comparisonClosureRingEquiv]
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [comparisonClosureRingEquiv]
  map_mul' τ₁ τ₂ := by
    apply AlgEquiv.ext
    intro x
    let j := comparisonClosureRingEquiv L p
    change j.symm (τ₁ (τ₂ (j x))) =
      j.symm (τ₁ (j (j.symm (τ₂ (j x)))))
    rw [j.apply_symm_apply]

private noncomputable def comparisonRestrictionToEL
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    Field.absoluteGaloisGroup K →* (comparisonEL L p ≃ₐ[K] comparisonEL L p) := by
  change (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    (comparisonEL L p ≃ₐ[K] comparisonEL L p)
  exact AlgEquiv.restrictNormalHom (comparisonEL L p)

@[simp]
private theorem comparisonRestrictionToEL_apply
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K) (x : comparisonEL L p) :
    (((comparisonRestrictionToEL L p g) x : comparisonEL L p) : AlgebraicClosure K) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
        (x : AlgebraicClosure K) :=
  AlgEquiv.restrictNormal_commutes
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
    (comparisonEL L p) x

private noncomputable def comparisonQuotientHom
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    Field.absoluteGaloisGroup K →*
      (CyclotomicField (p : ℕ) L.field ≃ₐ[K]
        CyclotomicField (p : ℕ) L.field) :=
  (comparisonCycloEquiv L p).restrictScalars K |>.autCongr.symm.toMonoidHom.comp
    (comparisonRestrictionToEL L p)

private theorem comparisonQuotientHom_surjective
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime) :
    Function.Surjective (comparisonQuotientHom L p) := by
  intro σ
  let eK := (comparisonCycloEquiv L p).restrictScalars K
  obtain ⟨τ, rfl⟩ := eK.autCongr.symm.surjective σ
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
    (AlgebraicClosure K) τ
  refine ⟨g, ?_⟩
  change eK.autCongr.symm (comparisonRestrictionToEL L p g) = _
  rw [show comparisonRestrictionToEL L p g = τ from hg]

private theorem comparisonQuotientHom_ker
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    (comparisonQuotientHom L p).ker = orientedCyclotomicLevel o L p := by
  ext g
  constructor
  · intro hg
    have hr : comparisonRestrictionToEL L p g = 1 := by
      change comparisonQuotientHom L p g = 1 at hg
      let eK := (comparisonCycloEquiv L p).restrictScalars K
      change eK.autCongr.symm (comparisonRestrictionToEL L p g) = 1 at hg
      apply eK.autCongr.symm.injective
      exact hg.trans (map_one eK.autCongr.symm).symm
    change g ∈ levelKernel L ∧ g ∈ o.kernel p
    constructor
    · change absoluteRestriction L g = 1
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [absoluteRestriction_apply]
      let y : comparisonEL L p :=
        ⟨algebraMap L.field (AlgebraicClosure K) x,
          IntermediateField.algebraMap_mem (comparisonEL L p) x⟩
      have he := DFunLike.congr_fun hr y
      have hev := congrArg Subtype.val he
      rw [comparisonRestrictionToEL_apply] at hev
      simpa [y] using hev
    · rw [o.kernel_eq_cyclotomic]
      intro ζ hζ
      let y : comparisonEL L p :=
        ⟨ζ, IntermediateField.subset_adjoin L.field (comparisonRoots K p)
          ⟨(p : ℕ), Set.mem_singleton _, p.1.2.ne_zero, hζ⟩⟩
      have he := DFunLike.congr_fun hr y
      have hev := congrArg Subtype.val he
      rw [comparisonRestrictionToEL_apply] at hev
      simpa [y] using hev
  · intro hg
    change comparisonQuotientHom L p g = 1
    let eK := (comparisonCycloEquiv L p).restrictScalars K
    change eK.autCongr.symm (comparisonRestrictionToEL L p g) = 1
    rw [← map_one eK.autCongr.symm]
    congr 1
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hL : ∀ z : L.field,
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
            (z : AlgebraicClosure K) = z := by
      intro z
      have hk := MonoidHom.mem_ker.mp hg.1
      have happ := DFunLike.congr_fun hk z
      have hv := congrArg Subtype.val happ
      rw [absoluteRestriction_apply] at hv
      exact hv
    have hc : g ∈ cyclotomicKernel K (p : ℕ) := by
      rw [← o.kernel_eq_cyclotomic p]
      exact hg.2
    rw [comparisonRestrictionToEL_apply]
    exact comparison_fixesEL L p g hL (fun z hz => hc z hz) x x.property

private noncomputable def comparisonQuotientMulEquiv
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    orientedCyclotomicQuotient o L p ≃*
      (CyclotomicField (p : ℕ) L.field ≃ₐ[K]
        CyclotomicField (p : ℕ) L.field) :=
  (QuotientGroup.quotientMulEquivOfEq (comparisonQuotientHom_ker o L p).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (comparisonQuotientHom L p)
      (comparisonQuotientHom_surjective L p))

@[simp]
private theorem comparisonQuotientMulEquiv_mk
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K) :
    comparisonQuotientMulEquiv o L p (QuotientGroup.mk g) =
      comparisonQuotientHom L p g := by
  rfl

private theorem comparisonQuotient_restrict
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K) :
    galoisRestriction K L.field (CyclotomicField (p : ℕ) L.field)
        (comparisonQuotientMulEquiv o L p (QuotientGroup.mk g)) =
      absoluteRestriction L g := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L.field
    (CyclotomicField (p : ℕ) L.field)).injective
  rw [galoisRestriction_apply]
  change comparisonQuotientHom L p g
      (algebraMap L.field (CyclotomicField (p : ℕ) L.field) x) =
    algebraMap L.field (CyclotomicField (p : ℕ) L.field)
      (absoluteRestriction L g x)
  let eK := (comparisonCycloEquiv L p).restrictScalars K
  change eK.symm (comparisonRestrictionToEL L p g
      (eK (algebraMap L.field (CyclotomicField (p : ℕ) L.field) x))) = _
  apply eK.injective
  rw [eK.apply_symm_apply]
  have he : eK (algebraMap L.field
      (CyclotomicField (p : ℕ) L.field) x) =
      algebraMap L.field (comparisonEL L p) x := by
    change comparisonCycloEquiv L p
      (algebraMap L.field (CyclotomicField (p : ℕ) L.field) x) = _
    exact (comparisonCycloEquiv L p).commutes x
  have he' : eK (algebraMap L.field
      (CyclotomicField (p : ℕ) L.field) (absoluteRestriction L g x)) =
      algebraMap L.field (comparisonEL L p) (absoluteRestriction L g x) := by
    change comparisonCycloEquiv L p
      (algebraMap L.field (CyclotomicField (p : ℕ) L.field)
        (absoluteRestriction L g x)) = _
    exact (comparisonCycloEquiv L p).commutes (absoluteRestriction L g x)
  rw [he, he']
  apply Subtype.ext
  rw [comparisonRestrictionToEL_apply]
  change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      (x : AlgebraicClosure K) =
    ((absoluteRestriction L g x : L.field) : AlgebraicClosure K)
  exact (absoluteRestriction_apply L g x).symm

private noncomputable def comparisonLevelMulEquiv
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    orientedCyclotomicLevel o L p ≃*
      Field.absoluteGaloisGroup (CyclotomicField (p : ℕ) L.field) :=
  (comparisonLevelToAutEL o L p).trans (comparisonAutELToAbsolute L p)

private noncomputable def comparisonSemilinearLift
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K) :
    AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃+*
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field) :=
  (comparisonClosureRingEquiv L p).trans
    ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g).toRingEquiv.trans
      (comparisonClosureRingEquiv L p).symm)

private theorem comparisonSemilinearLift_commutes
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K)
    (x : CyclotomicField (p : ℕ) L.field) :
    comparisonSemilinearLift L p g
        (algebraMap (CyclotomicField (p : ℕ) L.field)
          (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) x) =
      algebraMap (CyclotomicField (p : ℕ) L.field)
        (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
        (comparisonQuotientHom L p g x) := by
  let j := comparisonClosureRingEquiv L p
  let e := comparisonCycloEquiv L p
  apply j.injective
  change j (j.symm ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      (j (algebraMap (CyclotomicField (p : ℕ) L.field)
        (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) x)))) =
    j (algebraMap (CyclotomicField (p : ℕ) L.field)
      (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
      (comparisonQuotientHom L p g x))
  rw [j.apply_symm_apply]
  have hj (y : CyclotomicField (p : ℕ) L.field) :
      j (algebraMap (CyclotomicField (p : ℕ) L.field)
        (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) y) =
      algebraMap (comparisonEL L p) (AlgebraicClosure K) (e y) := by
    dsimp [j, e, comparisonClosureRingEquiv]
    exact IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
      (AlgebraicClosure K) (comparisonCycloEquiv L p).toRingEquiv y
  rw [hj, hj]
  calc
    (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
        (algebraMap (comparisonEL L p) (AlgebraicClosure K) (e x)) =
      algebraMap (comparisonEL L p) (AlgebraicClosure K)
        (comparisonRestrictionToEL L p g (e x)) :=
          (comparisonRestrictionToEL_apply L p g (e x)).symm
    _ = algebraMap (comparisonEL L p) (AlgebraicClosure K)
        (e (comparisonQuotientHom L p g x)) := by
      congr 1
      change comparisonRestrictionToEL L p g (e x) =
        e (e.symm (comparisonRestrictionToEL L p g (e x)))
      rw [e.apply_symm_apply]

@[simp]
private theorem comparisonLevelMulEquiv_apply
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime)
    (h : orientedCyclotomicLevel o L p)
    (x : AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) :
    (show AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃ₐ[
      CyclotomicField (p : ℕ) L.field]
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from
        comparisonLevelMulEquiv o L p h) x =
      comparisonSemilinearLift L p h.1 x := by
  rfl

private theorem comparisonLevelMulEquiv_conjugate
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime)
    (g : Field.absoluteGaloisGroup K)
    (h : orientedCyclotomicLevel o L p)
    (x : AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) :
    (show AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃ₐ[
      CyclotomicField (p : ℕ) L.field]
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from
        comparisonLevelMulEquiv o L p
          (conjugateInOrientedCyclotomicLevel o L p g h)) x =
      comparisonSemilinearLift L p g
        ((show AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃ₐ[
          CyclotomicField (p : ℕ) L.field]
          AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from
            comparisonLevelMulEquiv o L p h)
          ((comparisonSemilinearLift L p g).symm x)) := by
  change (comparisonClosureRingEquiv L p).symm
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
        g * h.1 * g⁻¹) (comparisonClosureRingEquiv L p x)) = _
  rw [comparisonLevelMulEquiv_apply]
  simp only [comparisonSemilinearLift, RingEquiv.trans_apply,
    RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply]
  let j := comparisonClosureRingEquiv L p
  apply j.injective
  rw [j.apply_symm_apply, j.apply_symm_apply]
  change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from h.1)
        ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (j x))) = _
  rfl

private theorem comparisonLevelMulEquiv_continuous
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    Continuous (comparisonLevelMulEquiv o L p) := by
  apply continuous_of_continuousAt_one
    (comparisonLevelMulEquiv o L p).toMonoidHom
  rw [continuousAt_def]
  intro V hV
  have hV1 : V ∈ nhds (1 : Field.absoluteGaloisGroup
      (CyclotomicField (p : ℕ) L.field)) := by
    rw [map_one] at hV
    exact hV
  obtain ⟨T, hTfin, hTV⟩ :=
    (krullTopology_mem_nhds_one_iff
      (CyclotomicField (p : ℕ) L.field)
      (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) V).mp hV1
  letI : FiniteDimensional (CyclotomicField (p : ℕ) L.field) T := hTfin
  letI : FiniteDimensional L.field
      (CyclotomicField (p : ℕ) L.field) :=
    IsCyclotomicExtension.finiteDimensional
      ({(p : ℕ)} : Set ℕ) L.field
      (CyclotomicField (p : ℕ) L.field)
  letI : FiniteDimensional K
      (CyclotomicField (p : ℕ) L.field) :=
    FiniteDimensional.trans K L.field (CyclotomicField (p : ℕ) L.field)
  letI : IsScalarTower K (CyclotomicField (p : ℕ) L.field) T :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : FiniteDimensional K T :=
    FiniteDimensional.trans K (CyclotomicField (p : ℕ) L.field) T
  let j := comparisonClosureRingEquiv L p
  let f : T →ₐ[K] AlgebraicClosure K :=
    { toFun := fun x => j (x : AlgebraicClosure
          (CyclotomicField (p : ℕ) L.field))
      map_one' := by simp
      map_mul' := fun _ _ => by simp
      map_zero' := by simp
      map_add' := fun _ _ => by simp
      commutes' := fun k => by
        have hj := IsAlgClosure.equivOfEquiv_algebraMap
          (AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
          (AlgebraicClosure K) (comparisonCycloEquiv L p).toRingEquiv
          (algebraMap K (CyclotomicField (p : ℕ) L.field) k)
        change j (algebraMap K (AlgebraicClosure
          (CyclotomicField (p : ℕ) L.field)) k) =
            algebraMap K (AlgebraicClosure K) k
        rw [show j (algebraMap K (AlgebraicClosure
            (CyclotomicField (p : ℕ) L.field)) k) =
          algebraMap (comparisonEL L p) (AlgebraicClosure K)
            (comparisonCycloEquiv L p
              (algebraMap K (CyclotomicField (p : ℕ) L.field) k)) by
                exact hj]
        have hbase : comparisonCycloEquiv L p
            (algebraMap K (CyclotomicField (p : ℕ) L.field) k) =
            algebraMap K (comparisonEL L p) k :=
          (comparisonCycloEquiv L p).restrictScalars K |>.commutes k
        calc
          algebraMap (comparisonEL L p) (AlgebraicClosure K)
              (comparisonCycloEquiv L p
                (algebraMap K (CyclotomicField (p : ℕ) L.field) k)) =
              algebraMap (comparisonEL L p) (AlgebraicClosure K)
                (algebraMap K (comparisonEL L p) k) := congrArg _ hbase
          _ = algebraMap K (AlgebraicClosure K) k :=
            IsScalarTower.algebraMap_apply K (comparisonEL L p)
              (AlgebraicClosure K) k }
  let J : IntermediateField K (AlgebraicClosure K) := f.fieldRange
  let eTJ : T ≃ₐ[K] J := AlgEquiv.ofInjectiveField f
  letI : FiniteDimensional K J := eTJ.toLinearEquiv.finiteDimensional
  let W : Set (orientedCyclotomicLevel o L p) :=
    (fun u => (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from u.1)) ⁻¹'
      (J.fixingSubgroup : Set
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  have hWopen : IsOpen W := by
    exact J.fixingSubgroup_isOpen.preimage continuous_subtype_val
  apply Filter.mem_of_superset (hWopen.mem_nhds (by
    exact J.fixingSubgroup.one_mem))
  intro u hu
  apply hTV
  change (show AlgebraicClosure (CyclotomicField (p : ℕ) L.field) ≃ₐ[
      CyclotomicField (p : ℕ) L.field]
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from
        comparisonLevelMulEquiv o L p u) ∈ T.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let xT : T := ⟨x, hx⟩
  let y : J := ⟨f xT, ⟨xT, rfl⟩⟩
  have hu' : (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from u.1) ∈
      J.fixingSubgroup := hu
  have huy : (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from u.1)
      (y : AlgebraicClosure K) = y :=
    (IntermediateField.mem_fixingSubgroup_iff J _).mp hu' y y.property
  change (show AlgebraicClosure
      (CyclotomicField (p : ℕ) L.field) ≃ₐ[
        CyclotomicField (p : ℕ) L.field]
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field) from
        comparisonLevelMulEquiv o L p u) x = x
  change j.symm
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from u.1)
        (j x)) = x
  apply j.injective
  rw [j.apply_symm_apply]
  exact huy

private noncomputable def comparisonLevelContinuousEquiv
    {K : Type*} [Field K] [NumberField K]
    (o : CyclotomicOrientation K) (L : GaloisLevel K) (p : OddPrime) :
    orientedCyclotomicLevel o L p ≃ₜ*
      Field.absoluteGaloisGroup (CyclotomicField (p : ℕ) L.field) := by
  let e := comparisonLevelMulEquiv o L p
  have hlevel : IsClosed (levelKernel L :
      Set (Field.absoluteGaloisGroup K)) := by
    have hc : Continuous (absoluteRestriction L) := by
      change Continuous (AlgEquiv.restrictNormalHom L.field)
      exact InfiniteGalois.restrictNormalHom_continuous L.field
    have heq : (levelKernel L : Set (Field.absoluteGaloisGroup K)) =
        (absoluteRestriction L) ⁻¹' {1} := by
      ext g
      simp [levelKernel]
    rw [heq]
    exact isClosed_singleton.preimage hc
  have hclosed : IsClosed (orientedCyclotomicLevel o L p :
      Set (Field.absoluteGaloisGroup K)) := by
    simpa [orientedCyclotomicLevel] using
      hlevel.inter (o.kernel_isClosed p)
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    absoluteGaloisGroup_compactSpace
  letI : CompactSpace (orientedCyclotomicLevel o L p) :=
    hclosed.isClosedEmbedding_subtypeVal.compactSpace
  have hcont : Continuous e := comparisonLevelMulEquiv_continuous o L p
  letI : Algebra.IsIntegral
      (CyclotomicField (p : ℕ) L.field)
      (AlgebraicClosure (CyclotomicField (p : ℕ) L.field)) :=
    Algebra.IsAlgebraic.isIntegral
  letI : T2Space (Field.absoluteGaloisGroup
      (CyclotomicField (p : ℕ) L.field)) := by
    change T2Space (AlgebraicClosure
      (CyclotomicField (p : ℕ) L.field) ≃ₐ[
        CyclotomicField (p : ℕ) L.field]
      AlgebraicClosure (CyclotomicField (p : ℕ) L.field))
    infer_instance
  have hquot : Topology.IsQuotientMap e :=
    hcont.isClosedMap.isQuotientMap hcont e.surjective
  have hinv : Continuous e.symm := hquot.continuous_iff.mpr (by
    convert (continuous_id : Continuous (id :
      orientedCyclotomicLevel o L p → orientedCyclotomicLevel o L p)) using 1
    funext x
    exact e.symm_apply_apply x)
  exact
    { toMulEquiv := e
      continuous_toFun := hcont
      continuous_invFun := hinv }

private def comparisonContinuousMonoidHom
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) : G →ₜ* H :=
  ContinuousMonoidHom.mk e.toMulEquiv.toMonoidHom e.continuous_toFun

private def comparisonPullCharacter
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) (a : ContinuousCharacter H n) :
    ContinuousCharacter G n :=
  a.comp (additiveContinuousHom (comparisonContinuousMonoidHom e))

private theorem comparisonCupZero_pull
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) {a b : ContinuousCharacter H n}
    (h : CupZero n a b) :
    CupZero n (comparisonPullCharacter n e a)
      (comparisonPullCharacter n e b) := by
  obtain ⟨c, hc⟩ := h
  let c' : C(G, ZMod n) :=
    ⟨fun g => c (e g), c.continuous.comp e.continuous_toFun⟩
  refine ⟨c', ?_⟩
  intro σ τ
  change a (Additive.ofMul (e σ)) * b (Additive.ofMul (e τ)) =
    c (e σ) + c (e τ) - c (e (σ * τ))
  simpa only [continuousCharacterValue, map_mul] using hc (e σ) (e τ)

private theorem comparisonEvaluation_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x : ElementaryQuotient G n)
    (a : ContinuousCharacter H n) :
    evaluation n (elementaryQuotientTransport n e x) a =
      evaluation n x (comparisonPullCharacter n e a) := by
  obtain ⟨g, rfl⟩ := orientedElementaryClass_surjective n x
  rw [elementaryQuotientTransport_elementaryClass,
    evaluation_elementaryClass, evaluation_elementaryClass]
  rfl

private theorem comparisonEvaluationDet_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x y : ElementaryQuotient G n)
    (a b : ContinuousCharacter H n) :
    evaluationDet (elementaryQuotientTransport n e x)
        (elementaryQuotientTransport n e y) a b =
      evaluationDet x y (comparisonPullCharacter n e a)
        (comparisonPullCharacter n e b) := by
  simp only [evaluationDet, comparisonEvaluation_transport]

private theorem comparisonPlaneBasis_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    {n : ℕ} [Fact n.Prime] (e : G ≃ₜ* H)
    (P : GroupSubspace G n) {x y : ElementaryQuotient G n}
    (h : IsPlaneBasis P x y) :
    IsPlaneBasis (P.map (elementaryQuotientTransport n e).toLinearMap)
      (elementaryQuotientTransport n e x)
      (elementaryQuotientTransport n e y) := by
  refine ⟨⟨x, h.1, rfl⟩, ⟨y, h.2.1, rfl⟩, ?_, ?_⟩
  · have hmap := h.2.2.1.map'
      (elementaryQuotientTransport n e).toLinearMap
      (elementaryQuotientTransport n e).ker
    change LinearIndependent (ZMod n)
      (fun i => elementaryQuotientTransport n e (pairVector x y i)) at hmap
    have hfun : (fun i => elementaryQuotientTransport n e (pairVector x y i)) =
        pairVector (elementaryQuotientTransport n e x)
          (elementaryQuotientTransport n e y) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at hmap
    exact hmap
  · rw [← h.2.2.2]
    calc
      pairSpan (elementaryQuotientTransport n e x)
          (elementaryQuotientTransport n e y) =
          Submodule.span (ZMod n)
            {(elementaryQuotientTransport n e) x,
              (elementaryQuotientTransport n e) y} := rfl
      _ = Submodule.span (ZMod n)
          ((elementaryQuotientTransport n e) '' {x, y}) := by
            rw [Set.image_pair]
      _ = Submodule.map (elementaryQuotientTransport n e).toLinearMap
          (Submodule.span (ZMod n) {x, y}) :=
            (LinearMap.map_span _ _).symm
      _ = Submodule.map (elementaryQuotientTransport n e).toLinearMap
          (pairSpan x y) := rfl

private theorem comparisonPacket_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) [Fact n.Prime] (e : G ≃ₜ* H)
    (P : GroupSubspace G n) (hP : IsPacket n P) :
    IsPacket n (P.map (elementaryQuotientTransport n e).toLinearMap) := by
  obtain ⟨x, y, hxy, hzero⟩ := hP
  refine ⟨elementaryQuotientTransport n e x,
    elementaryQuotientTransport n e y,
    comparisonPlaneBasis_transport e P hxy, ?_⟩
  intro a b hab
  rw [comparisonEvaluationDet_transport]
  exact hzero _ _ (comparisonCupZero_pull n e hab)

private theorem comparisonElementaryTransport_symm
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) :
    elementaryQuotientTransport n e.symm =
      (elementaryQuotientTransport n e).symm := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := orientedElementaryClass_surjective n x
  apply (elementaryQuotientTransport n e).injective
  simp

-- Normalizing the two dependent submodule transports is elaboration-heavy.
set_option maxHeartbeats 800000 in
private theorem comparisonPacket_iff
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) [Fact n.Prime] (e : G ≃ₜ* H) (P : GroupSubspace G n) :
    IsPacket n (P.map (elementaryQuotientTransport n e).toLinearMap) ↔
      IsPacket n P := by
  constructor
  · intro hP
    let E := elementaryQuotientTransport n e
    have hback := comparisonPacket_transport n e.symm
      (P.map E.toLinearMap) hP
    rw [comparisonElementaryTransport_symm n e] at hback
    rw [← Submodule.map_comp] at hback
    have hcomp : E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, Submodule.map_id] at hback
    exact hback
  · exact comparisonPacket_transport n e P

-- The dependent comparison package needs extra elaboration budget.
set_option maxHeartbeats 800000 in
/-- Blueprint §10.1(5): the marked group `G_L ∩ C_ℓ` is continuously
equivalent to `G_{L(μ_ℓ)}`.  The same comparison supplies the quotient
identification, commutes with restriction to `L`, transports packets, and
intertwines the two packet actions.  These equations make the equivalences
canonical enough for the recovery argument rather than arbitrary group
isomorphisms. -/
theorem exists_orientedCyclotomicComparison
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    ∃ eLevel : orientedCyclotomicLevel orientation L p ≃ₜ*
        Field.absoluteGaloisGroup (CyclotomicField (p : ℕ) L.field),
      ∃ eQuotient : orientedCyclotomicQuotient orientation L p ≃*
          (CyclotomicField (p : ℕ) L.field ≃ₐ[K]
            CyclotomicField (p : ℕ) L.field),
        (∀ g : Field.absoluteGaloisGroup K,
          galoisRestriction K L.field (CyclotomicField (p : ℕ) L.field)
              (eQuotient (QuotientGroup.mk g)) =
            absoluteRestriction L g) ∧
        (∀ P : GroupSubspace
            (orientedCyclotomicLevel orientation L p) (p : ℕ),
          IsPacket (p : ℕ) (transportGroupSubspace (p : ℕ) eLevel P) ↔
            IsPacket (p : ℕ) P) ∧
        ∀ (γ : orientedCyclotomicQuotient orientation L p)
            (x : ElementaryQuotient
              (orientedCyclotomicLevel orientation L p) (p : ℕ)),
          elementaryQuotientTransport (p : ℕ) eLevel
              (orientedPacketAction orientation L p γ x) =
            packetAction K (CyclotomicField (p : ℕ) L.field) (p : ℕ)
              (eQuotient γ)
              (elementaryQuotientTransport (p : ℕ) eLevel x) := by
  let eLevel := comparisonLevelContinuousEquiv orientation L p
  let eQuotient := comparisonQuotientMulEquiv orientation L p
  refine ⟨eLevel, eQuotient, ?_, ?_, ?_⟩
  · exact comparisonQuotient_restrict orientation L p
  · intro P
    exact comparisonPacket_iff (p : ℕ) eLevel P
  · intro γ x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    obtain ⟨h, rfl⟩ := orientedElementaryClass_surjective (p : ℕ) x
    rw [orientedPacketAction_elementaryClass,
      elementaryQuotientTransport_elementaryClass,
      elementaryQuotientTransport_elementaryClass]
    obtain ⟨ζ, hζ⟩ :=
      exists_cyclotomicPrimitiveRoot_forComparison L.field (p : ℕ)
    apply (kummerDualEquiv ζ hζ).injective
    apply AddMonoidHom.ext
    intro u
    cases u with
    | ofMul u =>
      simp only [kummerDualEquiv_apply]
      conv_rhs =>
        rw [← kummerDualEquiv_apply ζ hζ]
      rw [kummerDualEquiv_packetAction_apply,
        kummerDualEquiv_apply, evaluation_elementaryClass,
        evaluation_elementaryClass]
      let M := CyclotomicField (p : ℕ) L.field
      let A := AlgebraicClosure M
      let σ : M ≃ₐ[K] M := comparisonQuotientHom L p g
      let τ : Field.absoluteGaloisGroup M :=
        comparisonLevelMulEquiv orientation L p h
      let τ' : Field.absoluteGaloisGroup M :=
        comparisonLevelMulEquiv orientation L p
          (conjugateInOrientedCyclotomicLevel orientation L p g h)
      let s : A ≃+* A := comparisonSemilinearLift L p g
      let u₀ : Mˣ := Units.map σ.symm.toRingEquiv.toMonoidHom u
      let c : ZMod (p : ℕ) :=
        ((packetCyclotomicCharacter K M (p : ℕ) ζ hζ σ :
          (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ))
      let a : ZMod (p : ℕ) :=
        continuousCharacterValue (kummerCharacter ζ hζ u₀) τ
      have hσ : eQuotient (QuotientGroup.mk g) = σ := by
        rfl
      rw [hσ]
      obtain ⟨α, hαpow, hαact⟩ :=
        kummerCharacter_definingEquation ζ hζ u₀
      let β : A := s α
      have hs (z : M) :
          s (algebraMap M A z) = algebraMap M A (σ z) := by
        exact comparisonSemilinearLift_commutes L p g z
      have hβpow : β ^ (p : ℕ) = algebraMap M A (u : M) := by
        calc
          β ^ (p : ℕ) = s (α ^ (p : ℕ)) := by
            exact (map_pow s α (p : ℕ)).symm
          _ = s (algebraMap M A (u₀ : M)) := congrArg s hαpow
          _ = algebraMap M A (σ (u₀ : M)) := hs (u₀ : M)
          _ = algebraMap M A (u : M) := by
            congr 1
            simp [u₀, σ]
      let ζA : A := algebraMap M A ζ
      have hζA : IsPrimitiveRoot ζA (p : ℕ) :=
        hζ.map_of_injective (algebraMap M A).injective
      have hpowmul : ζA ^ (c * a).val = ζA ^ (c.val * a.val) := by
        rw [ZMod.val_mul]
        exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hζA.pow_eq_one
      have hβact :
          (show A ≃ₐ[M] A from τ') β = ζA ^ (c * a).val * β := by
        calc
          (show A ≃ₐ[M] A from τ') β =
              s ((show A ≃ₐ[M] A from τ) (s.symm β)) := by
            exact comparisonLevelMulEquiv_conjugate
              orientation L p g h β
          _ = s ((show A ≃ₐ[M] A from τ) α) := by
            rw [show s.symm β = α by
              exact s.symm_apply_apply α]
          _ = s (ζA ^ a.val * α) := by
            rw [show (show A ≃ₐ[M] A from τ) α =
              ζA ^ a.val * α by exact hαact τ]
          _ = s ζA ^ a.val * s α := by
            rw [map_mul, map_pow]
          _ = (algebraMap M A (σ ζ)) ^ a.val * β := by
            rw [hs ζ]
          _ = (algebraMap M A (ζ ^ c.val)) ^ a.val * β := by
            rw [show σ ζ = ζ ^ c.val by
              exact packetCyclotomicCharacter_spec K M (p : ℕ) ζ hζ σ]
          _ = ζA ^ (c.val * a.val) * β := by
            simp only [map_pow, pow_mul, ζA]
          _ = ζA ^ (c * a).val * β := by rw [hpowmul]
      have hvalue := kummerCharacterValue_eq_of_action
        ζ hζ u β hβpow τ' (c * a) hβact
      exact hvalue

private theorem elementaryQuotientTransport_symm
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) :
    (elementaryQuotientTransport n e).symm =
      elementaryQuotientTransport n e.symm := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := orientedElementaryClass_surjective n x
  apply (elementaryQuotientTransport n e).injective
  simp

set_option maxHeartbeats 3000000 in
/-- Packet/action transport across
`G_L ∩ C_ℓ ≃ G_{L(μ_ℓ)}` identifies the oriented packet images with the
usual arithmetic cyclotomic-level packet images.  The proof explicitly
consumes `exists_orientedCyclotomicComparison`. -/
theorem packetImagesAtOddPrime_eq_cyclotomicComparison
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    packetImagesAtOddPrime orientation L p =
      {D | ∃ P : GroupSubspace
          (Field.absoluteGaloisGroup
            (CyclotomicField (p : ℕ) L.field)) (p : ℕ),
        IsPacket (p : ℕ) P ∧
          D = Subgroup.map
            (galoisRestriction K L.field
              (CyclotomicField (p : ℕ) L.field))
            (packetStabilizer K P)} := by
  obtain ⟨eLevel, eQuotient, hrestrict, hpacket, haction⟩ :=
    exists_orientedCyclotomicComparison orientation L p
  let E := elementaryQuotientTransport (p : ℕ) eLevel
  have hconj (γ : orientedCyclotomicQuotient orientation L p)
      (P : GroupSubspace
        (orientedCyclotomicLevel orientation L p) (p : ℕ)) :
      transportGroupSubspace (p : ℕ) eLevel
          (conjugateOrientedPacket orientation L p γ P) =
        conjugatePacket K (eQuotient γ)
          (transportGroupSubspace (p : ℕ) eLevel P) := by
    rw [transportGroupSubspace, conjugateOrientedPacket,
      conjugatePacket, transportGroupSubspace,
      ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    ext x
    exact haction γ x
  have hstab (P : GroupSubspace
      (orientedCyclotomicLevel orientation L p) (p : ℕ)) :
      Subgroup.map eQuotient.toMonoidHom
          (orientedPacketStabilizer orientation L p P) =
        packetStabilizer K
          (transportGroupSubspace (p : ℕ) eLevel P) := by
    ext τ
    rw [Subgroup.mem_map_equiv]
    change conjugateOrientedPacket orientation L p (eQuotient.symm τ) P = P ↔
      conjugatePacket K τ
        (transportGroupSubspace (p : ℕ) eLevel P) =
          transportGroupSubspace (p : ℕ) eLevel P
    constructor
    · intro h
      rw [← eQuotient.apply_symm_apply τ,
        ← hconj (eQuotient.symm τ) P, h]
    · intro h
      apply Submodule.map_injective_of_injective E.injective
      change transportGroupSubspace (p : ℕ) eLevel
          (conjugateOrientedPacket orientation L p (eQuotient.symm τ) P) =
        transportGroupSubspace (p : ℕ) eLevel P
      rw [hconj, eQuotient.apply_symm_apply, h]
  have hres :
      (galoisRestriction K L.field
        (CyclotomicField (p : ℕ) L.field)).comp eQuotient.toMonoidHom =
      orientedRestriction orientation L p := by
    apply MonoidHom.ext
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact hrestrict g
  ext D
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨transportGroupSubspace (p : ℕ) eLevel P,
      (hpacket P).2 hP, ?_⟩
    rw [← hstab, Subgroup.map_map, hres]
  · rintro ⟨Q, hQ, rfl⟩
    let P : GroupSubspace
        (orientedCyclotomicLevel orientation L p) (p : ℕ) :=
      Q.map E.symm.toLinearMap
    have hmap : transportGroupSubspace (p : ℕ) eLevel P = Q := by
      dsimp [transportGroupSubspace, P, E]
      rw [← Submodule.map_comp]
      convert Submodule.map_id Q using 1
      ext x
      simp
    refine ⟨P, (hpacket P).1 (hmap ▸ hQ), ?_⟩
    rw [← hmap, ← hstab, Subgroup.map_map, hres]

set_option maxHeartbeats 3000000 in
/-- At one auxiliary prime, packet stabilizers recover exactly the
finite decomposition groups of residue characteristic away from that prime. -/
theorem packetImagesAtOddPrime_eq_decompositionCollectionAway
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    packetImagesAtOddPrime orientation L p =
      decompositionCollectionAway K L.field p := by
  rw [packetImagesAtOddPrime_eq_cyclotomicComparison orientation L p]
  let M := CyclotomicField (p : ℕ) L.field
  letI : IsGalois K M := cyclotomicOverfield_isGalois_forComparison L p
  obtain ⟨ζ, hζ⟩ :=
    exists_cyclotomicPrimitiveRoot_forComparison L.field (p : ℕ)
  have hpackets := packet_theorem p.2 ζ hζ
  ext D
  constructor
  · rintro ⟨P, hP, rfl⟩
    have hpMem : P ∈
        {Q : GroupSubspace (Field.absoluteGaloisGroup M) (p : ℕ) |
          IsPacket (p : ℕ) Q} := hP
    rw [hpackets] at hpMem
    obtain ⟨w, hw, rfl⟩ := hpMem
    refine ⟨restrictFinitePlace L.field w, ?_, ?_⟩
    · rwa [residueCharacteristic_restrictFinitePlace]
    · rw [packetStabilizer_eq_decompositionGroup K M ζ hζ w hw,
        tower_surjectivity K L.field M w]
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hwv⟩ := exists_finitePlace_over L.field (M := M) v
    have hw : residueCharacteristic w ≠ (p : ℕ) := by
      rw [← residueCharacteristic_restrictFinitePlace L.field w, hwv]
      exact hv
    refine ⟨groupLocalPlane ζ hζ w, ?_, ?_⟩
    · have hlocal : groupLocalPlane ζ hζ w ∈
          {Q : GroupSubspace (Field.absoluteGaloisGroup M) (p : ℕ) |
            ∃ w : FinitePlace M, residueCharacteristic w ≠ (p : ℕ) ∧
              Q = groupLocalPlane ζ hζ w} :=
        ⟨w, hw, rfl⟩
      rw [← hpackets] at hlocal
      exact hlocal
    · rw [packetStabilizer_eq_decompositionGroup K M ζ hζ w hw,
        tower_surjectivity K L.field M w, hwv]

/-- Every marked packet-stabilizer image is a finite decomposition group. -/
theorem packetImagesAtOddPrime_subset_decompositionCollection
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime) :
    packetImagesAtOddPrime orientation L p ⊆
      decompositionCollection K L.field := by
  rw [packetImagesAtOddPrime_eq_decompositionCollectionAway orientation L p]
  rintro D ⟨w, _, rfl⟩
  exact ⟨w, rfl⟩

/-- Blueprint Proposition 7.2 (`prop:finite-reconstruction`): the union of
marked-kernel packet stabilizers is exactly `Dec(L/K)`.  The arithmetic
cyclotomic field enters only through the preceding comparison theorem. -/
theorem finite_reconstruction
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K) :
    decompositionCollection K L.field =
      recoveredDecompositionCollection orientation L := by
  ext D
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨p, hp⟩ := exists_oddPrime_ne (residueCharacteristic w)
    refine ⟨p, ?_⟩
    rw [packetImagesAtOddPrime_eq_decompositionCollectionAway]
    exact ⟨w, hp.symm, rfl⟩
  · rintro ⟨p, hp⟩
    exact packetImagesAtOddPrime_subset_decompositionCollection
      orientation L p hp

/-- Exact one-prime specialization used by marked-level correctness
(`cofinal_descent_orientation_free.tex`, `prop:marked-correct`).  If the
finite level lies below the marked kernel, its marked group is `G_L` itself.
The proof specializes the existing cyclotomic comparison, packet theorem,
stabilizer identification, and tower-surjectivity interfaces; it introduces
no independent finite-recovery axiom and has no depth/usability premise. -/
theorem packetImagesAtOddPrime_eq_decompositionCollectionAway_of_le
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K)
    (p : OddPrime)
    (hmarked : levelKernel L ≤ orientation.kernel p) :
    packetImagesAtOddPrime orientation L p =
      decompositionCollectionAway K L.field p := by
  have hlevel : orientedCyclotomicLevel orientation L p = levelKernel L := by
    rw [orientedCyclotomicLevel, inf_eq_left.mpr hmarked]
  have hcomparison :=
    packetImagesAtOddPrime_eq_cyclotomicComparison orientation L p
  obtain ⟨ζ, hζ⟩ :=
    exists_cyclotomicPrimitiveRoot_forComparison L.field (p : ℕ)
  have hpackets := packet_theorem p.2 ζ hζ
  have hstabilizers :
      ∀ (w : FinitePlace (CyclotomicField (p : ℕ) L.field))
          (hw : residueCharacteristic w ≠ (p : ℕ)),
        packetStabilizer K (groupLocalPlane ζ hζ w) =
          decompositionGroup K w := by
    intro w hw
    exact packetStabilizer_eq_decompositionGroup K
      (CyclotomicField (p : ℕ) L.field) ζ hζ w hw
  letI : IsGalois K (CyclotomicField (p : ℕ) L.field) :=
    cyclotomicOverfield_isGalois_forComparison L p
  have htower :
      ∀ w : FinitePlace (CyclotomicField (p : ℕ) L.field),
        Subgroup.map
            (galoisRestriction K L.field
              (CyclotomicField (p : ℕ) L.field))
            (decompositionGroup K w) =
          decompositionGroup K (restrictFinitePlace L.field w) := by
    intro w
    exact tower_surjectivity K L.field
      (CyclotomicField (p : ℕ) L.field) w
  exact packetImagesAtOddPrime_eq_decompositionCollectionAway
    orientation L p

end

end NU.LocalTheory
