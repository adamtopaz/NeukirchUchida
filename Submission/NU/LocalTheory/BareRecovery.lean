import Submission.NU.LocalTheory.InverseLimit.AbsolutePlace
import Submission.NU.LocalTheory.FKSchmidt
import Submission.NU.LocalTheory.ValuationConjugacy

/-!
# Orientation-free recovery by cofinal descent

This module implements the bare terminal layer of
`cofinal_descent_orientation_free.tex`, version 3.  The predicate at a level
uses only the elementary quotient of that level, packets, and conjugation.
Cyclotomic kernels occur only later, in arithmetic correctness proofs after
cofinal descent; they are not data of `bareCrit`, `bareRecoveredAtPrime`, or
`bareRecovered`.
-/

open IsDedekindDomain
open scoped NumberField Pointwise

namespace NU.LocalTheory

noncomputable section

/-! ## Open normal levels and their quotients -/

/-- An open normal subgroup, bundled so every quotient below carries its
actual normality proof.  The fields are properties of `toSubgroup`; there is
no independent or potentially trivial quotient model in this structure. -/
structure OpenNormalSubgroup (G : Type*) [Group G] [TopologicalSpace G] where
  toSubgroup : Subgroup G
  isOpen' : IsOpen (toSubgroup : Set G)
  normal' : toSubgroup.Normal

instance {G : Type*} [Group G] [TopologicalSpace G] :
    Coe (OpenNormalSubgroup G) (Subgroup G) :=
  ⟨OpenNormalSubgroup.toSubgroup⟩

instance {G : Type*} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) : U.toSubgroup.Normal :=
  U.normal'

@[ext]
theorem OpenNormalSubgroup.ext {G : Type*} [Group G] [TopologicalSpace G]
    {U V : OpenNormalSubgroup G} (h : U.toSubgroup = V.toSubgroup) : U = V := by
  cases U
  cases V
  simp_all

/-- The full group is the explicit inhabitant of the type of open normal
levels. -/
def topOpenNormalSubgroup (G : Type*) [Group G] [TopologicalSpace G] :
    OpenNormalSubgroup G where
  toSubgroup := ⊤
  isOpen' := isOpen_univ
  normal' := inferInstance

/-- Inhabitation sanity check: open normal levels cannot become vacuous. -/
instance openNormalSubgroupNonempty (G : Type*) [Group G]
    [TopologicalSpace G] : Nonempty (OpenNormalSubgroup G) :=
  ⟨topOpenNormalSubgroup G⟩

/-- Inclusion of open normal levels. -/
def OpenNormalSubgroup.LE {G : Type*} [Group G] [TopologicalSpace G]
    (U V : OpenNormalSubgroup G) : Prop :=
  U.toSubgroup ≤ V.toSubgroup

/-- The canonical quotient map at an open normal level. -/
def openNormalQuotientMap {G : Type*} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) : G →* G ⧸ U.toSubgroup :=
  QuotientGroup.mk' U.toSubgroup

/-- Defining equation for the canonical quotient map. -/
@[simp]
theorem openNormalQuotientMap_apply {G : Type*} [Group G]
    [TopologicalSpace G] (U : OpenNormalSubgroup G) (g : G) :
    openNormalQuotientMap U g = QuotientGroup.mk g :=
  rfl

/-- The image of a subgroup in the quotient at `U`. -/
def openNormalQuotientImage {G : Type*} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) (H : Subgroup G) :
    Subgroup (G ⧸ U.toSubgroup) :=
  Subgroup.map (openNormalQuotientMap U) H

/-! ## The bare packet criterion -/

/-- Conjugation by an ambient element preserves a normal level. -/
def conjugateInOpenNormal {G : Type*} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) (g : G) (h : U.toSubgroup) :
    U.toSubgroup :=
  ⟨g * (h : G) * g⁻¹,
    U.normal'.conj_mem (h : G) h.property g⟩

/-- Every elementary class has a representative in the original group. -/
private theorem bareElementaryClass_surjective
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

/-- The elementary-class map, bundled multiplicatively. -/
private def bareElementaryClassHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : G →* Multiplicative (ElementaryQuotient G n) :=
  AddMonoidHom.toMultiplicativeRight <|
    (ModN.mkQ n).comp <| MonoidHom.toAdditiveLeft <|
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator G))

@[simp]
private theorem bareElementaryClassHom_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (g : G) :
    (bareElementaryClassHom n g).toAdd = elementaryClass n g :=
  rfl

/-- Inner automorphisms act trivially on the elementary quotient. -/
private theorem bareElementaryClass_conj
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (g h : G) :
    elementaryClass n (g * h * g⁻¹) = elementaryClass n h := by
  have hconj : bareElementaryClassHom n (g * h * g⁻¹) =
      bareElementaryClassHom n h := by
    rw [map_mul, map_mul, map_inv]
    simp [mul_assoc]
  exact congrArg Multiplicative.toAdd hconj

/-- Conjugation on a normal level as a topological group automorphism. -/
private noncomputable def conjugationOnOpenNormal
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (g : G) : U.toSubgroup ≃ₜ* U.toSubgroup where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

@[simp]
private theorem conjugationOnOpenNormal_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (g : G) (h : U.toSubgroup) :
    conjugationOnOpenNormal U g h = conjugateInOpenNormal U g h := by
  apply Subtype.ext
  exact MulAut.conjNormal_apply g h

/-- Conjugation on the elementary quotient before descent modulo `U`. -/
private noncomputable def bareActionHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime) :
    G →* (ElementaryQuotient U.toSubgroup (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      ElementaryQuotient U.toSubgroup (p : ℕ)) where
  toFun g := elementaryQuotientTransport (p : ℕ)
    (conjugationOnOpenNormal U g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := bareElementaryClass_surjective (p : ℕ) x
    rw [elementaryQuotientTransport_elementaryClass]
    change elementaryClass (p : ℕ) (conjugateInOpenNormal U 1 h) =
      elementaryClass (p : ℕ) h
    congr 1
    apply Subtype.ext
    simp [conjugateInOpenNormal]
  map_mul' := by
    intro g k
    apply LinearEquiv.ext
    intro x
    obtain ⟨h, rfl⟩ := bareElementaryClass_surjective (p : ℕ) x
    simp only [elementaryQuotientTransport_elementaryClass,
      conjugationOnOpenNormal_apply, LinearEquiv.mul_apply]
    congr 1
    apply Subtype.ext
    simp [conjugateInOpenNormal, mul_assoc]

private theorem bareActionHom_kills
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime) :
    U.toSubgroup ≤ (bareActionHom U p).ker := by
  intro g hg
  change bareActionHom U p g = 1
  apply LinearEquiv.ext
  intro x
  obtain ⟨h, rfl⟩ := bareElementaryClass_surjective (p : ℕ) x
  rw [show bareActionHom U p g = elementaryQuotientTransport (p : ℕ)
    (conjugationOnOpenNormal U g) from rfl,
    elementaryQuotientTransport_elementaryClass]
  change elementaryClass (p : ℕ) (conjugateInOpenNormal U g h) =
    elementaryClass (p : ℕ) h
  exact bareElementaryClass_conj (p : ℕ) ⟨g, hg⟩ h

/-- The action of `G/U` on `X_U^ℓ` induced by conjugation.  The elementary
class equation below pins this to conjugation and rules out a trivial-action
implementation. -/
noncomputable def barePacketAction {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime) :
    (G ⧸ U.toSubgroup) →*
      (ElementaryQuotient U.toSubgroup (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
        ElementaryQuotient U.toSubgroup (p : ℕ)) :=
  QuotientGroup.lift U.toSubgroup (bareActionHom U p)
    (bareActionHom_kills U p)

/-- Defining equation for the bare conjugation action on elementary
classes. -/
@[simp]
theorem barePacketAction_elementaryClass {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime) (g : G)
    (h : U.toSubgroup) :
    barePacketAction U p (QuotientGroup.mk g)
        (elementaryClass (p : ℕ) h) =
      elementaryClass (p : ℕ) (conjugateInOpenNormal U g h) := by
  rw [barePacketAction, QuotientGroup.lift_mk]
  exact elementaryQuotientTransport_elementaryClass (p : ℕ)
    (conjugationOnOpenNormal U g) h

/-- Transport a level packet by the bare quotient action. -/
noncomputable def conjugateBarePacket {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime)
    (σ : G ⧸ U.toSubgroup)
    (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    GroupSubspace U.toSubgroup (p : ℕ) :=
  P.map (barePacketAction U p σ).toLinearMap

/-- Stabilizer of a packet under the bare conjugation action of `G/U`. -/
noncomputable def barePacketStabilizer {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime)
    (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    Subgroup (G ⧸ U.toSubgroup) where
  carrier := {σ | conjugateBarePacket U p σ P = P}
  one_mem' := by
    simp [conjugateBarePacket]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq] at hσ hτ ⊢
    change P.map (barePacketAction U p σ).toLinearMap = P at hσ
    change P.map (barePacketAction U p τ).toLinearMap = P at hτ
    calc
      conjugateBarePacket U p (σ * τ) P =
          P.map (((barePacketAction U p σ).toLinearMap).comp
            (barePacketAction U p τ).toLinearMap) := by
              rw [conjugateBarePacket, map_mul]
              congr 1
      _ = (P.map (barePacketAction U p τ).toLinearMap).map
          (barePacketAction U p σ).toLinearMap :=
            Submodule.map_comp _ _ _
      _ = P := by rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ ⊢
    change P.map (barePacketAction U p σ).toLinearMap = P at hσ
    calc
      conjugateBarePacket U p σ⁻¹ P =
          P.map (barePacketAction U p σ).symm.toLinearMap := by
            rw [conjugateBarePacket, map_inv]
            congr 1
      _ = (P.map (barePacketAction U p σ).toLinearMap).map
          (barePacketAction U p σ).symm.toLinearMap := by rw [hσ]
      _ = P := by
        rw [← Submodule.map_comp]
        convert Submodule.map_id P using 1
        ext x
        simp

/-- The bare criterion `Crit_U^ℓ`.  It refers only to packets of `X_U^ℓ`
and their stabilizers for conjugation by `G/U`; in particular it contains no
cyclotomic kernel or roots-of-unity datum.  `IsPacket` includes an actual
`IsPlaneBasis`, hence membership, linear independence, and exact span. -/
noncomputable def bareCrit {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : OpenNormalSubgroup G) (p : OddPrime) :
    Set (Subgroup (G ⧸ U.toSubgroup)) :=
  {D | ∃ P : GroupSubspace U.toSubgroup (p : ℕ),
    IsPacket (p : ℕ) P ∧ D = barePacketStabilizer U p P}

/-- Unfolded membership in `Crit_U^ℓ`. -/
@[simp]
theorem mem_bareCrit {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : OpenNormalSubgroup G) (p : OddPrime)
    (D : Subgroup (G ⧸ U.toSubgroup)) :
    D ∈ bareCrit U p ↔
      ∃ P : GroupSubspace U.toSubgroup (p : ℕ),
        IsPacket (p : ℕ) P ∧ D = barePacketStabilizer U p P :=
  Iff.rfl

/-- The plane nondegeneracy in bare criterion membership, displayed without
hiding it behind the packet abbreviation. -/
theorem mem_bareCrit_iff_exists_plane {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (p : OddPrime)
    (D : Subgroup (G ⧸ U.toSubgroup)) :
    D ∈ bareCrit U p ↔
      ∃ (P : GroupSubspace U.toSubgroup (p : ℕ))
          (x y : ElementaryQuotient U.toSubgroup (p : ℕ)),
        IsPlaneBasis P x y ∧
          (∀ a b : ContinuousCharacter U.toSubgroup (p : ℕ),
            CupZero (p : ℕ) a b → evaluationDet x y a b = 0) ∧
          D = barePacketStabilizer U p P := by
  simp only [bareCrit, Set.mem_setOf_eq, IsPacket]
  aesop

/-! ## Equivariance -/

/-- Transport an open normal level along a topological group isomorphism. -/
def OpenNormalSubgroup.map {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (α : G ≃ₜ* G') (U : OpenNormalSubgroup G) :
    OpenNormalSubgroup G' where
  toSubgroup := Subgroup.map α.toMulEquiv.toMonoidHom U.toSubgroup
  isOpen' := α.toHomeomorph.isOpenMap U.toSubgroup U.isOpen'
  normal' := U.normal'.map α.toMulEquiv.toMonoidHom α.surjective

/-- Membership equation for transport of an open normal level. -/
@[simp]
theorem OpenNormalSubgroup.mem_map {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (α : G ≃ₜ* G') (U : OpenNormalSubgroup G) (g : G) :
    α g ∈ (U.map α).toSubgroup ↔ g ∈ U.toSubgroup := by
  change (∃ x ∈ U.toSubgroup, α x = α g) ↔ g ∈ U.toSubgroup
  constructor
  · rintro ⟨x, hx, hα⟩
    simpa [α.injective hα] using hx
  · intro hg
    exact ⟨g, hg, rfl⟩

/-- The quotient isomorphism induced by `α`; its representative equation is
recorded separately so this cannot be an arbitrary abstract equivalence. -/
noncomputable def openNormalQuotientEquiv {G G' : Type*}
    [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    (α : G ≃ₜ* G') (U : OpenNormalSubgroup G) :
    (G ⧸ U.toSubgroup) ≃* (G' ⧸ (U.map α).toSubgroup) :=
  QuotientGroup.congr U.toSubgroup (U.map α).toSubgroup α.toMulEquiv rfl

/-- Defining equation for the induced quotient isomorphism. -/
@[simp]
theorem openNormalQuotientEquiv_mk {G G' : Type*}
    [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    (α : G ≃ₜ* G') (U : OpenNormalSubgroup G) (g : G) :
    openNormalQuotientEquiv α U (QuotientGroup.mk g) =
      QuotientGroup.mk (α g) :=
  rfl

/-- Mapping subgroups along a group equivalence is injective. -/
theorem subgroupMap_mulEquiv_injective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    Function.Injective (Subgroup.map e.toMonoidHom) := by
  intro A B h
  have h' := congrArg (Subgroup.map e.symm.toMonoidHom) h
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  simpa only [Subgroup.map_map, he, Subgroup.map_id] using h'

/-- Mapping a subgroup forward after mapping it backward along an
equivalence returns the subgroup. -/
theorem subgroupMap_mulEquiv_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (D : Subgroup H) :
    Subgroup.map e.toMonoidHom
        (Subgroup.map e.symm.toMonoidHom D) = D := by
  rw [Subgroup.map_map]
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  rw [he, Subgroup.map_id]

/-- A topological group equivalence restricted to an open normal level. -/
private noncomputable def openNormalSubgroupEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) :
    U.toSubgroup ≃ₜ* (U.map e).toSubgroup where
  toFun x := ⟨e x, (OpenNormalSubgroup.mem_map e U x).2 x.property⟩
  invFun y := ⟨e.symm y, by
    rw [← OpenNormalSubgroup.mem_map e U]
    simpa using y.property⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y
  map_mul' x y := by ext; exact e.map_mul x y
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.continuous_invFun.comp continuous_subtype_val

@[simp]
private theorem openNormalSubgroupEquiv_apply
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (x : U.toSubgroup) :
    (openNormalSubgroupEquiv e U x : H) = e x :=
  rfl

private def continuousMonoidHomOfEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) : G →ₜ* H :=
  ContinuousMonoidHom.mk e.toMulEquiv.toMonoidHom e.continuous_toFun

/-- Pull a continuous character back along a topological group equivalence. -/
private def pullContinuousCharacter
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) (a : ContinuousCharacter H n) :
    ContinuousCharacter G n :=
  a.comp (additiveContinuousHom (continuousMonoidHomOfEquiv e))

private theorem cupZero_pull_equiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) {a b : ContinuousCharacter H n}
    (h : CupZero n a b) :
    CupZero n (pullContinuousCharacter n e a)
      (pullContinuousCharacter n e b) := by
  obtain ⟨c, hc⟩ := h
  let c' : C(G, ZMod n) :=
    ⟨fun g => c (e g), c.continuous.comp e.continuous_toFun⟩
  refine ⟨c', ?_⟩
  intro σ τ
  change a (Additive.ofMul (e σ)) * b (Additive.ofMul (e τ)) =
    c (e σ) + c (e τ) - c (e (σ * τ))
  simpa only [continuousCharacterValue, map_mul] using hc (e σ) (e τ)

private theorem evaluation_transport_equiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x : ElementaryQuotient G n)
    (a : ContinuousCharacter H n) :
    evaluation n (elementaryQuotientTransport n e x) a =
      evaluation n x (pullContinuousCharacter n e a) := by
  obtain ⟨g, rfl⟩ := bareElementaryClass_surjective n x
  rw [elementaryQuotientTransport_elementaryClass,
    evaluation_elementaryClass, evaluation_elementaryClass]
  rfl

private theorem evaluationDet_transport_equiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x y : ElementaryQuotient G n)
    (a b : ContinuousCharacter H n) :
    evaluationDet (elementaryQuotientTransport n e x)
        (elementaryQuotientTransport n e y) a b =
      evaluationDet x y (pullContinuousCharacter n e a)
        (pullContinuousCharacter n e b) := by
  simp only [evaluationDet, evaluation_transport_equiv]

private theorem isPlaneBasis_transport
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

/-- Packets are preserved by transport of topological group structure. -/
private theorem isPacket_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) [Fact n.Prime] (e : G ≃ₜ* H)
    (P : GroupSubspace G n) (hP : IsPacket n P) :
    IsPacket n (P.map (elementaryQuotientTransport n e).toLinearMap) := by
  obtain ⟨x, y, hxy, hzero⟩ := hP
  refine ⟨elementaryQuotientTransport n e x,
    elementaryQuotientTransport n e y,
    isPlaneBasis_transport e P hxy, ?_⟩
  intro a b hab
  rw [evaluationDet_transport_equiv]
  exact hzero _ _ (cupZero_pull_equiv n e hab)

private theorem barePacketAction_intertwines
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (p : OddPrime)
    (σ : G ⧸ U.toSubgroup)
    (x : ElementaryQuotient U.toSubgroup (p : ℕ)) :
    elementaryQuotientTransport (p : ℕ) (openNormalSubgroupEquiv e U)
        (barePacketAction U p σ x) =
      barePacketAction (U.map e) p (openNormalQuotientEquiv e U σ)
        (elementaryQuotientTransport (p : ℕ)
          (openNormalSubgroupEquiv e U) x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  obtain ⟨h, rfl⟩ := bareElementaryClass_surjective (p : ℕ) x
  simp only [barePacketAction_elementaryClass,
    elementaryQuotientTransport_elementaryClass,
    openNormalQuotientEquiv_mk]
  congr 1
  apply Subtype.ext
  simp [conjugateInOpenNormal]

set_option maxHeartbeats 800000 in
-- Dependent submodule transport makes elaboration exceed the project default.
private theorem conjugateBarePacket_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (p : OddPrime)
    (σ : G ⧸ U.toSubgroup) (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    conjugateBarePacket (U.map e) p (openNormalQuotientEquiv e U σ)
        (P.map (elementaryQuotientTransport (p : ℕ)
          (openNormalSubgroupEquiv e U)).toLinearMap) =
      (conjugateBarePacket U p σ P).map
        (elementaryQuotientTransport (p : ℕ)
          (openNormalSubgroupEquiv e U)).toLinearMap := by
  rw [conjugateBarePacket, conjugateBarePacket,
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact (barePacketAction_intertwines e U p σ x).symm

private theorem barePacketStabilizer_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (p : OddPrime)
    (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    Subgroup.map (openNormalQuotientEquiv e U).toMonoidHom
        (barePacketStabilizer U p P) =
      barePacketStabilizer (U.map e) p
        (P.map (elementaryQuotientTransport (p : ℕ)
          (openNormalSubgroupEquiv e U)).toLinearMap) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change conjugateBarePacket (U.map e) p (openNormalQuotientEquiv e U σ)
      (P.map (elementaryQuotientTransport (p : ℕ)
        (openNormalSubgroupEquiv e U)).toLinearMap) = _
    rw [conjugateBarePacket_map, hσ]
  · intro hτ
    refine ⟨(openNormalQuotientEquiv e U).symm τ, ?_,
      (openNormalQuotientEquiv e U).apply_symm_apply τ⟩
    change conjugateBarePacket U p ((openNormalQuotientEquiv e U).symm τ) P = P
    apply Submodule.map_injective_of_injective
      (elementaryQuotientTransport (p : ℕ)
        (openNormalSubgroupEquiv e U)).injective
    rw [← conjugateBarePacket_map]
    change conjugateBarePacket (U.map e) p τ
      (P.map (elementaryQuotientTransport (p : ℕ)
        (openNormalSubgroupEquiv e U)).toLinearMap) = _ at hτ
    simpa using hτ

private theorem elementaryQuotientTransport_symm
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) :
    elementaryQuotientTransport n e.symm =
      (elementaryQuotientTransport n e).symm := by
  ext x
  obtain ⟨h, rfl⟩ := bareElementaryClass_surjective n x
  apply (elementaryQuotientTransport n e).injective
  simp

set_option maxHeartbeats 800000 in
-- The reverse transport normalizes two dependent submodule maps.
/-- Equivariance of the bare level criterion. -/
theorem bareCrit_equivariant {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    [IsTopologicalGroup G] [IsTopologicalGroup G']
    (α : G ≃ₜ* G') (U : OpenNormalSubgroup G) (p : OddPrime) :
    Set.image
        (Subgroup.map (openNormalQuotientEquiv α U).toMonoidHom)
        (bareCrit U p) =
      bareCrit (U.map α) p := by
  let eU := openNormalSubgroupEquiv α U
  let E := elementaryQuotientTransport (p : ℕ) eU
  ext D
  constructor
  · rintro ⟨D₀, ⟨P, hP, rfl⟩, rfl⟩
    refine ⟨P.map E.toLinearMap, isPacket_transport (p : ℕ) eU P hP, ?_⟩
    exact barePacketStabilizer_map α U p P
  · rintro ⟨Q, hQ, rfl⟩
    let P : GroupSubspace U.toSubgroup (p : ℕ) := Q.map E.symm.toLinearMap
    have hEsymm : E.symm = elementaryQuotientTransport (p : ℕ) eU.symm :=
      (elementaryQuotientTransport_symm (p : ℕ) eU).symm
    have hP : IsPacket (p : ℕ) P := by
      change IsPacket (p : ℕ) (Q.map E.symm.toLinearMap)
      rw [hEsymm]
      exact isPacket_transport (p : ℕ) eU.symm Q hQ
    refine ⟨barePacketStabilizer U p P, ⟨P, hP, rfl⟩, ?_⟩
    rw [barePacketStabilizer_map]
    congr 2
    dsimp [P]
    rw [← Submodule.map_comp]
    have hcomp : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, Submodule.map_id]

/-! ## Passing levels and the filter form -/

/-- Cofinality of a set of open normal levels: every open subgroup contains
a member.  This is the filter form and mentions no chosen system object. -/
def IsCofinalOpenNormalSet {G : Type*} [Group G] [TopologicalSpace G]
    (S : Set (OpenNormalSubgroup G)) : Prop :=
  ∀ V : Subgroup G, IsOpen (V : Set G) →
    ∃ U : OpenNormalSubgroup G, U ∈ S ∧ U.toSubgroup ≤ V

/-- A downward-directed cofinal system, used only as an equivalent proof
interface.  The terminal definition below uses `IsCofinalOpenNormalSet`
instead. -/
def IsCofinalOpenNormalSystem {G : Type*} [Group G]
    [TopologicalSpace G] (S : Set (OpenNormalSubgroup G)) : Prop :=
  S.Nonempty ∧
    (∀ U ∈ S, ∀ V ∈ S,
      ∃ W ∈ S, W.toSubgroup ≤ U.toSubgroup ∧
        W.toSubgroup ≤ V.toSubgroup) ∧
    IsCofinalOpenNormalSet S

/-- A cofinal set of open normal subgroups is automatically downward
directed. -/
theorem cofinalOpenNormalSet_directed {G : Type*} [Group G]
    [TopologicalSpace G] (S : Set (OpenNormalSubgroup G))
    (hS : IsCofinalOpenNormalSet S) :
    ∀ U ∈ S, ∀ V ∈ S,
      ∃ W ∈ S, W.toSubgroup ≤ U.toSubgroup ∧
        W.toSubgroup ≤ V.toSubgroup := by
  intro U _ V _
  obtain ⟨W, hWS, hW⟩ := hS (U.toSubgroup ⊓ V.toSubgroup)
    (U.isOpen'.inter V.isOpen')
  exact ⟨W, hWS, hW.trans inf_le_left, hW.trans inf_le_right⟩

/-- Automatic directedness, including the nonempty sanity check, identifies
cofinal sets with cofinal systems. -/
theorem cofinalOpenNormalSystem_iff {G : Type*} [Group G]
    [TopologicalSpace G] (S : Set (OpenNormalSubgroup G)) :
    IsCofinalOpenNormalSystem S ↔ IsCofinalOpenNormalSet S := by
  constructor
  · exact fun h => h.2.2
  · intro h
    obtain ⟨U, hUS, _⟩ := h (⊤ : Subgroup G) isOpen_univ
    exact ⟨⟨U, hUS⟩, cofinalOpenNormalSet_directed S h, h⟩

/-- A level passes for `(H,ℓ)` when the exact quotient image of `H` belongs
to the bare criterion at that level. -/
def IsPassingLevel {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (p : OddPrime) (H : Subgroup G)
    (U : OpenNormalSubgroup G) : Prop :=
  openNormalQuotientImage U H ∈ bareCrit U p

/-- The set of all passing levels for `(H,ℓ)`. -/
def passingLevels {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (p : OddPrime) (H : Subgroup G) :
    Set (OpenNormalSubgroup G) :=
  {U | IsPassingLevel p H U}

/-- Remark `equivalent-forms(a)`: the filter form is equivalent to existence
of a cofinal system all of whose members pass. -/
theorem passingLevels_cofinal_iff_exists_system
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (p : OddPrime) (H : Subgroup G) :
    IsCofinalOpenNormalSet (passingLevels p H) ↔
      ∃ S : Set (OpenNormalSubgroup G),
        IsCofinalOpenNormalSystem S ∧
          ∀ U ∈ S, IsPassingLevel p H U := by
  constructor
  · intro h
    exact ⟨passingLevels p H,
      (cofinalOpenNormalSystem_iff (passingLevels p H)).2 h,
      fun _ hU => hU⟩
  · rintro ⟨S, hS, hpass⟩ V hV
    obtain ⟨U, hUS, hUV⟩ := hS.2.2 V hV
    exact ⟨U, hpass U hUS, hUV⟩

/-- Extraction: restricting a cofinal system to levels below an open
subgroup is again a cofinal system. -/
theorem cofinalSystem_restrict {G : Type*} [Group G]
    [TopologicalSpace G] (S : Set (OpenNormalSubgroup G))
    (hS : IsCofinalOpenNormalSystem S) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) :
    IsCofinalOpenNormalSystem
      {U | U ∈ S ∧ U.toSubgroup ≤ V} := by
  rw [cofinalOpenNormalSystem_iff]
  intro W hW
  obtain ⟨U, hUS, hU⟩ := hS.2.2 (W ⊓ V) (hW.inter hV)
  exact ⟨U, ⟨hUS, hU.trans inf_le_right⟩, hU.trans inf_le_left⟩

/-- The orientation-free collection `𝒟_ℓ(G)`.  Condition (D2') is exactly
cofinality of the set of passing levels; it does not quantify over or store a
system and does not mention a cyclotomic orientation. -/
def bareRecoveredAtPrime (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (p : OddPrime) : Set (Subgroup G) :=
  {H | IsClosed (H : Set G) ∧
    ¬IsProcyclic H ∧
    IsCofinalOpenNormalSet (passingLevels p H)}

/-- The orientation-free collection `𝒟(G)=⋃_{ℓ odd} 𝒟_ℓ(G)`. -/
def bareRecovered (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Set (Subgroup G) :=
  {H | ∃ p : OddPrime, H ∈ bareRecoveredAtPrime G p}

/-- Unfolded membership in `𝒟_ℓ(G)`, displaying (D1) and the exact filter
form (D2'). -/
@[simp]
theorem mem_bareRecoveredAtPrime {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (p : OddPrime) (H : Subgroup G) :
    H ∈ bareRecoveredAtPrime G p ↔
      IsClosed (H : Set G) ∧ ¬IsProcyclic H ∧
        (∀ V : Subgroup G, IsOpen (V : Set G) →
          ∃ U : OpenNormalSubgroup G,
            IsPassingLevel p H U ∧ U.toSubgroup ≤ V) :=
  Iff.rfl

/-- Unfolded membership in `𝒟(G)`. -/
@[simp]
theorem mem_bareRecovered {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) :
    H ∈ bareRecovered G ↔
      ∃ p : OddPrime, H ∈ bareRecoveredAtPrime G p :=
  Iff.rfl

/-- Quotient images commute with transport of the ambient group. -/
private theorem openNormalQuotientImage_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (A : Subgroup G) :
    openNormalQuotientImage (U.map e)
        (Subgroup.map e.toMulEquiv.toMonoidHom A) =
      Subgroup.map (openNormalQuotientEquiv e U).toMonoidHom
        (openNormalQuotientImage U A) := by
  rw [openNormalQuotientImage, openNormalQuotientImage,
    Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem isPassingLevel_map_iff
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) (p : OddPrime)
    (A : Subgroup G) :
    IsPassingLevel p (Subgroup.map e.toMulEquiv.toMonoidHom A) (U.map e) ↔
      IsPassingLevel p A U := by
  rw [IsPassingLevel, IsPassingLevel, openNormalQuotientImage_map]
  constructor
  · intro h
    rw [← bareCrit_equivariant e U p] at h
    obtain ⟨D, hD, hmap⟩ := h
    have hinj := subgroupMap_mulEquiv_injective (openNormalQuotientEquiv e U)
    have heq : D = openNormalQuotientImage U A := hinj hmap
    rwa [heq] at hD
  · intro h
    rw [← bareCrit_equivariant e U p]
    exact ⟨openNormalQuotientImage U A, h, rfl⟩

/-- Transport of cofinal systems under a topological group isomorphism. -/
theorem cofinalSystem_equivariant {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    (α : G ≃ₜ* G') (S : Set (OpenNormalSubgroup G))
    (hS : IsCofinalOpenNormalSystem S) :
    IsCofinalOpenNormalSystem (OpenNormalSubgroup.map α '' S) := by
  rw [cofinalOpenNormalSystem_iff]
  intro V hV
  let V' : Subgroup G := Subgroup.comap α.toMulEquiv.toMonoidHom V
  have hV' : IsOpen (V' : Set G) := by
    change IsOpen (α ⁻¹' (V : Set G'))
    exact α.toHomeomorph.isOpen_preimage.mpr hV
  obtain ⟨U, hUS, hUV⟩ := hS.2.2 V' hV'
  refine ⟨U.map α, ⟨U, hUS, rfl⟩, ?_⟩
  exact Subgroup.map_le_iff_le_comap.mpr hUV

/-- The restriction of an ambient equivalence to a subgroup and its image. -/
private noncomputable def subgroupMapContinuousEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (A : Subgroup G) :
    A ≃ₜ* Subgroup.map e.toMulEquiv.toMonoidHom A where
  toFun x := ⟨e x, ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    rcases y.property with ⟨x, hx, hxy⟩
    have heq : e.symm (y : H) = x := by
      rw [← hxy]
      change e.symm (e x) = x
      exact e.symm_apply_apply x
    rwa [heq]⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y
  map_mul' x y := by ext; exact e.map_mul x y
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.continuous_invFun.comp continuous_subtype_val

private theorem isProcyclic_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (A : Subgroup G) (hA : IsProcyclic A) :
    IsProcyclic (Subgroup.map e.toMulEquiv.toMonoidHom A) := by
  let B := Subgroup.map e.toMulEquiv.toMonoidHom A
  let eA : A ≃ₜ* B := subgroupMapContinuousEquiv e A
  obtain ⟨x, hx⟩ := hA
  refine ⟨eA x, ?_⟩
  have himage : eA '' (Subgroup.zpowers x : Set A) =
      ((Subgroup.zpowers (eA x) : Subgroup B) : Set B) := by
    have hm := MonoidHom.map_zpowers eA.toMulEquiv.toMonoidHom x
    exact congrArg (fun S : Subgroup B => (S : Set B)) hm
  have hset : closure (((Subgroup.zpowers (eA x) : Subgroup B) : Set B)) =
      Set.univ := by
    calc
      closure (((Subgroup.zpowers (eA x) : Subgroup B) : Set B)) =
          closure (eA '' (Subgroup.zpowers x : Set A)) :=
        congrArg closure himage.symm
      _ = eA '' closure (Subgroup.zpowers x : Set A) :=
        (eA.toHomeomorph.image_closure _).symm
      _ = eA '' ((⊤ : Subgroup A) : Set A) := by
        rw [← Subgroup.topologicalClosure_coe, hx]
      _ = Set.univ := by
        ext y
        simp
  apply SetLike.coe_injective
  simpa only [Subgroup.topologicalClosure_coe, Subgroup.coe_top] using hset

private theorem isProcyclic_map_iff
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (A : Subgroup G) :
    IsProcyclic (Subgroup.map e.toMulEquiv.toMonoidHom A) ↔ IsProcyclic A := by
  constructor
  · intro h
    have hback := isProcyclic_map e.symm
      (Subgroup.map e.toMulEquiv.toMonoidHom A) h
    have heq : Subgroup.map e.symm.toMulEquiv.toMonoidHom
        (Subgroup.map e.toMulEquiv.toMonoidHom A) = A := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id A using 2
      ext x
      exact e.symm_apply_apply x
    rwa [heq] at hback
  · exact isProcyclic_map e A

private theorem isClosed_subgroupMap_iff
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (A : Subgroup G) :
    IsClosed ((Subgroup.map e.toMulEquiv.toMonoidHom A : Subgroup H) : Set H) ↔
      IsClosed (A : Set G) := by
  have hcarrier :
      ((Subgroup.map e.toMulEquiv.toMonoidHom A : Subgroup H) : Set H) =
        e '' (A : Set G) := by
    ext y
    constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩
  rw [hcarrier]
  exact e.toHomeomorph.isClosed_image

private theorem mem_bareRecoveredAtPrime_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (p : OddPrime) (A : Subgroup G)
    (hA : A ∈ bareRecoveredAtPrime G p) :
    Subgroup.map e.toMulEquiv.toMonoidHom A ∈ bareRecoveredAtPrime H p := by
  obtain ⟨hclosed, hnonpro, hcofinal⟩ := hA
  refine ⟨(isClosed_subgroupMap_iff e A).2 hclosed, ?_, ?_⟩
  · intro hpro
    exact hnonpro ((isProcyclic_map_iff e A).1 hpro)
  · intro V hV
    let V' : Subgroup G := Subgroup.comap e.toMulEquiv.toMonoidHom V
    have hV' : IsOpen (V' : Set G) := by
      change IsOpen (e ⁻¹' (V : Set H))
      exact e.toHomeomorph.isOpen_preimage.mpr hV
    obtain ⟨U, hpass, hUV⟩ := hcofinal V' hV'
    refine ⟨U.map e, (isPassingLevel_map_iff e U p A).2 hpass, ?_⟩
    exact Subgroup.map_le_iff_le_comap.mpr hUV

/-- Functoriality of `𝒟_ℓ`. -/
theorem bareRecoveredAtPrime_functorial
    {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    [IsTopologicalGroup G] [IsTopologicalGroup G']
    (α : G ≃ₜ* G') (p : OddPrime) :
    Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
        (bareRecoveredAtPrime G p) =
      bareRecoveredAtPrime G' p := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact mem_bareRecoveredAtPrime_map α p A hA
  · intro hB
    let A := Subgroup.map α.symm.toMulEquiv.toMonoidHom B
    have hA : A ∈ bareRecoveredAtPrime G p :=
      mem_bareRecoveredAtPrime_map α.symm p B hB
    exact ⟨A, hA, subgroupMap_mulEquiv_symm α.toMulEquiv B⟩

/-- Functoriality of `𝒟`. -/
theorem bareRecovered_functorial
    {G G' : Type*} [Group G] [Group G']
    [TopologicalSpace G] [TopologicalSpace G']
    [IsTopologicalGroup G] [IsTopologicalGroup G']
    (α : G ≃ₜ* G') :
    Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
        (bareRecovered G) =
      bareRecovered G' := by
  ext B
  constructor
  · rintro ⟨A, ⟨p, hA⟩, rfl⟩
    exact ⟨p, mem_bareRecoveredAtPrime_map α p A hA⟩
  · rintro ⟨p, hB⟩
    let A := Subgroup.map α.symm.toMulEquiv.toMonoidHom B
    have hA : A ∈ bareRecoveredAtPrime G p :=
      mem_bareRecoveredAtPrime_map α.symm p B hB
    exact ⟨A, ⟨p, hA⟩, subgroupMap_mulEquiv_symm α.toMulEquiv B⟩

/-! ## Arithmetic levels and marked-level correctness -/

/-- An open subgroup is closed, so an open normal level has the closed
subgroup package required by infinite Galois correspondence. -/
def OpenNormalSubgroup.toClosedSubgroup {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) : ClosedSubgroup G :=
  ⟨U.toSubgroup, Subgroup.isClosed_of_isOpen U.toSubgroup U.isOpen'⟩

instance {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : OpenNormalSubgroup G) :
    U.toClosedSubgroup.toSubgroup.Normal :=
  U.normal'

/-- The same closed subgroup with the absolute Galois group unfolded to its
actual algebra-automorphism type. -/
def absoluteOpenNormalClosedSubgroup
    (K : Type*) [Field K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  change ClosedSubgroup (Field.absoluteGaloisGroup K)
  exact U.toClosedSubgroup

instance (K : Type*) [Field K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (absoluteOpenNormalClosedSubgroup K U).toSubgroup.Normal := by
  change U.toSubgroup.Normal
  exact U.normal'

/-- The finite Galois field fixed by an open normal subgroup.  Finiteness and
Galoisness are obtained from the open-normal clauses, so the bundle has no
independent field choice. -/
noncomputable def galoisLevelOfOpenNormal
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    GaloisLevel K where
  field := IntermediateField.fixedField
    (absoluteOpenNormalClosedSubgroup K U).toSubgroup
  finiteDimensional := by
    apply (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField
        (absoluteOpenNormalClosedSubgroup K U).toSubgroup)).1
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (absoluteOpenNormalClosedSubgroup K U)]
    exact U.isOpen'
  numberField := by
    letI : FiniteDimensional K
        (IntermediateField.fixedField
          (absoluteOpenNormalClosedSubgroup K U).toSubgroup) := by
      apply (InfiniteGalois.isOpen_iff_finite
        (IntermediateField.fixedField
          (absoluteOpenNormalClosedSubgroup K U).toSubgroup)).1
      rw [InfiniteGalois.fixingSubgroup_fixedField
        (absoluteOpenNormalClosedSubgroup K U)]
      exact U.isOpen'
    exact NumberField.of_module_finite K _
  isGalois := by
    apply (InfiniteGalois.normal_iff_isGalois
      (IntermediateField.fixedField
        (absoluteOpenNormalClosedSubgroup K U).toSubgroup)).1
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (absoluteOpenNormalClosedSubgroup K U)]
    exact U.normal'

/-- The fixed-field level has exactly the prescribed kernel. -/
@[simp]
theorem levelKernel_galoisLevelOfOpenNormal
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    levelKernel (galoisLevelOfOpenNormal K U) = U.toSubgroup := by
  change (AlgEquiv.restrictNormalHom
    (IntermediateField.fixedField
      (absoluteOpenNormalClosedSubgroup K U).toSubgroup)).ker =
        (absoluteOpenNormalClosedSubgroup K U).toSubgroup
  rw [IntermediateField.restrictNormalHom_ker,
    InfiniteGalois.fixingSubgroup_fixedField
      (absoluteOpenNormalClosedSubgroup K U)]

/-- Inclusion of open normal subgroups reverses inclusion of their fixed
Galois levels. -/
theorem galoisLevelOfOpenNormal_antitone
    (K : Type*) [Field K] [NumberField K]
    {U V : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    (hUV : U.LE V) :
    (galoisLevelOfOpenNormal K V).LE
      (galoisLevelOfOpenNormal K U) := by
  apply IntermediateField.fixedField_le
  exact hUV

/-- The canonical arithmetic identification `G_K/U ≃ Gal(M_U/K)`. -/
noncomputable def openNormalArithmeticEquiv
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (Field.absoluteGaloisGroup K ⧸ U.toSubgroup) ≃*
      ((galoisLevelOfOpenNormal K U).field ≃ₐ[K]
        (galoisLevelOfOpenNormal K U).field) := by
  change ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ⧸
      (absoluteOpenNormalClosedSubgroup K U).toSubgroup) ≃*
    ((IntermediateField.fixedField
      (absoluteOpenNormalClosedSubgroup K U).toSubgroup) ≃ₐ[K]
      (IntermediateField.fixedField
        (absoluteOpenNormalClosedSubgroup K U).toSubgroup))
  exact InfiniteGalois.normalAutEquivQuotient
    (absoluteOpenNormalClosedSubgroup K U)

/-- Defining equation for the arithmetic quotient identification. -/
@[simp]
theorem openNormalArithmeticEquiv_mk
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (g : Field.absoluteGaloisGroup K) :
    openNormalArithmeticEquiv K U (QuotientGroup.mk g) =
      absoluteRestriction (galoisLevelOfOpenNormal K U) g := by
  change InfiniteGalois.normalAutEquivQuotient
      (absoluteOpenNormalClosedSubgroup K U) (QuotientGroup.mk g) =
    AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (absoluteOpenNormalClosedSubgroup K U).toSubgroup) g
  rfl

/-- Subgroup images agree under the canonical arithmetic quotient
identification. -/
theorem openNormalArithmeticEquiv_image
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Subgroup.map (openNormalArithmeticEquiv K U).toMonoidHom
        (openNormalQuotientImage U H) =
      finiteLevelImage (galoisLevelOfOpenNormal K U) H := by
  rw [openNormalQuotientImage, finiteLevelImage, Subgroup.map_map]
  congr 1

/-- A marked level is an open normal subgroup contained in the genuine
mod-`p` cyclotomic kernel.  This predicate is used only in correctness
proofs, never in the bare criterion or terminal recovered collection. -/
def IsMarkedLevel (K : Type*) [Field K] (p : OddPrime)
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) : Prop :=
  U.toSubgroup ≤ cyclotomicKernel K (p : ℕ)

/-- The marked levels form a cofinal system. -/
theorem markedLevels_cofinal
    (K : Type*) [Field K] [NumberField K] (p : OddPrime) :
    IsCofinalOpenNormalSystem
      {U : OpenNormalSubgroup (Field.absoluteGaloisGroup K) |
        IsMarkedLevel K p U} := by
  rw [cofinalOpenNormalSystem_iff]
  intro V hV
  have hopen : IsOpen ((V : Set (Field.absoluteGaloisGroup K)) ∩
      (cyclotomicKernel K (p : ℕ) : Set (Field.absoluteGaloisGroup K))) :=
    hV.inter (cyclotomicKernel_isOpen K p)
  have hone : (1 : Field.absoluteGaloisGroup K) ∈
      ((V : Set (Field.absoluteGaloisGroup K)) ∩
        (cyclotomicKernel K (p : ℕ) : Set (Field.absoluteGaloisGroup K))) :=
    ⟨V.one_mem, (cyclotomicKernel K (p : ℕ)).one_mem⟩
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    absoluteGaloisGroup_compactSpace
  letI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) :=
    absoluteGaloisGroup_totallyDisconnectedSpace
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  let U : OpenNormalSubgroup (Field.absoluteGaloisGroup K) :=
    { toSubgroup := N.toSubgroup
      isOpen' := N.isOpen'
      normal' := N.isNormal' }
  refine ⟨U, ?_, ?_⟩
  · intro g hg
    exact (hN hg).2
  · intro g hg
    exact (hN hg).1

/-- Absolute finite places away from `p`, with the residue characteristic
recorded on the restriction to the number field. -/
def IsAbsoluteFinitePlaceAway
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (W : ValuationSubring (AlgebraicClosure K)) : Prop :=
  IsAbsoluteFinitePlace K W ∧
    ∃ v : FinitePlace K,
      W.comap (algebraMap K (AlgebraicClosure K)) =
        primeValuationSubring v ∧
      residueCharacteristic v ≠ (p : ℕ)

/-- Absolute decomposition groups whose residue characteristic differs from
`p`. -/
def absoluteDecompositionCollectionAway
    (K : Type*) [Field K] [NumberField K] (p : OddPrime) :
    Set (Subgroup (Field.absoluteGaloisGroup K)) :=
  {H | ∃ W : ValuationSubring (AlgebraicClosure K),
    IsAbsoluteFinitePlaceAway K p W ∧
      H = absoluteDecompositionGroup K W}

/-- Finite decomposition groups away from `p`, transported back to the
literal quotient `G_K/U`. -/
def quotientDecompositionCollectionAway
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime) :
    Set (Subgroup (Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) :=
  {D | ∃ w : FinitePlace (galoisLevelOfOpenNormal K U).field,
    residueCharacteristic w ≠ (p : ℕ) ∧
      D = Subgroup.map (openNormalArithmeticEquiv K U).symm.toMonoidHom
        (decompositionGroup K w)}

/-- The identity homeomorphism between equal ambient subgroups. -/
private def subgroupContinuousMulEquivOfEq
    {G : Type*} [Group G] [TopologicalSpace G]
    {A B : Subgroup G} (h : A = B) : A ≃ₜ* B where
  toFun x := ⟨x, by rw [← h]; exact x.property⟩
  invFun y := ⟨y, by rw [h]; exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

private theorem bare_orientedPacketAction_intertwines
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime)
    (hlevel : orientedCyclotomicLevel (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p = U.toSubgroup)
    (σ : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)
    (x : ElementaryQuotient U.toSubgroup (p : ℕ)) :
    elementaryQuotientTransport (p : ℕ)
        (subgroupContinuousMulEquivOfEq hlevel.symm)
        (barePacketAction U p σ x) =
      orientedPacketAction (canonicalCyclotomicOrientation K)
        (galoisLevelOfOpenNormal K U) p
        (QuotientGroup.quotientMulEquivOfEq hlevel.symm σ)
        (elementaryQuotientTransport (p : ℕ)
          (subgroupContinuousMulEquivOfEq hlevel.symm) x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective σ
  obtain ⟨u, rfl⟩ := bareElementaryClass_surjective (p : ℕ) x
  simp only [barePacketAction_elementaryClass,
    orientedPacketAction_elementaryClass,
    elementaryQuotientTransport_elementaryClass,
    QuotientGroup.quotientMulEquivOfEq_mk]
  congr 1

set_option maxHeartbeats 800000 in
-- Two dependent packet maps are normalized across the marked-level equality.
private theorem conjugateBarePacket_eq_conjugateOrientedPacket
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime)
    (hlevel : orientedCyclotomicLevel (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p = U.toSubgroup)
    (σ : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)
    (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    conjugateOrientedPacket (canonicalCyclotomicOrientation K)
        (galoisLevelOfOpenNormal K U) p
        (QuotientGroup.quotientMulEquivOfEq hlevel.symm σ)
        (P.map (elementaryQuotientTransport (p : ℕ)
          (subgroupContinuousMulEquivOfEq hlevel.symm)).toLinearMap) =
      (conjugateBarePacket U p σ P).map
        (elementaryQuotientTransport (p : ℕ)
          (subgroupContinuousMulEquivOfEq hlevel.symm)).toLinearMap := by
  rw [conjugateOrientedPacket, conjugateBarePacket,
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact (bare_orientedPacketAction_intertwines K U p hlevel σ x).symm

private theorem barePacketStabilizer_map_marked
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime)
    (hlevel : orientedCyclotomicLevel (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p = U.toSubgroup)
    (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    Subgroup.map (QuotientGroup.quotientMulEquivOfEq hlevel.symm).toMonoidHom
        (barePacketStabilizer U p P) =
      orientedPacketStabilizer (canonicalCyclotomicOrientation K)
        (galoisLevelOfOpenNormal K U) p
        (P.map (elementaryQuotientTransport (p : ℕ)
          (subgroupContinuousMulEquivOfEq hlevel.symm)).toLinearMap) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change conjugateOrientedPacket (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p
      (QuotientGroup.quotientMulEquivOfEq hlevel.symm σ) _ = _
    rw [conjugateBarePacket_eq_conjugateOrientedPacket K U p hlevel σ P,
      hσ]
  · intro hτ
    let eQ := QuotientGroup.quotientMulEquivOfEq hlevel.symm
    refine ⟨eQ.symm τ, ?_, eQ.apply_symm_apply τ⟩
    change conjugateBarePacket U p (eQ.symm τ) P = P
    apply Submodule.map_injective_of_injective
      (elementaryQuotientTransport (p : ℕ)
        (subgroupContinuousMulEquivOfEq hlevel.symm)).injective
    rw [← conjugateBarePacket_eq_conjugateOrientedPacket K U p hlevel
      (eQ.symm τ) P]
    change conjugateOrientedPacket (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p τ _ = _ at hτ
    simpa [eQ] using hτ

private theorem orientedRestriction_comp_markedQuotientEquiv
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime)
    (hlevel : orientedCyclotomicLevel (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p = U.toSubgroup) :
    (orientedRestriction (canonicalCyclotomicOrientation K)
        (galoisLevelOfOpenNormal K U) p).comp
      (QuotientGroup.quotientMulEquivOfEq hlevel.symm).toMonoidHom =
        (openNormalArithmeticEquiv K U).toMonoidHom := by
  ext g
  simp

set_option maxHeartbeats 800000 in
-- Reverse packet transport normalizes a dependent submodule composition.
/-- At a marked level, transport of the bare packet construction through the
canonical arithmetic quotient is the existing oriented one-prime
construction.  The hypothesis makes the marked intersection equal to `U`;
no depth or usability condition is present. -/
theorem bareCrit_eq_orientedPacketImages_of_marked
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime) (hU : IsMarkedLevel K p U) :
    Set.image
        (Subgroup.map (openNormalArithmeticEquiv K U).toMonoidHom)
        (bareCrit U p) =
      packetImagesAtOddPrime (canonicalCyclotomicOrientation K)
        (galoisLevelOfOpenNormal K U) p := by
  let L := galoisLevelOfOpenNormal K U
  let o := canonicalCyclotomicOrientation K
  have hlevel : orientedCyclotomicLevel o L p = U.toSubgroup := by
    rw [orientedCyclotomicLevel, inf_eq_left.mpr]
    · exact levelKernel_galoisLevelOfOpenNormal K U
    · simpa [L, o, IsMarkedLevel, canonicalCyclotomicOrientation] using hU
  let eL := subgroupContinuousMulEquivOfEq hlevel.symm
  let eQ := QuotientGroup.quotientMulEquivOfEq hlevel.symm
  let E := elementaryQuotientTransport (p : ℕ) eL
  rw [packetImagesAtOddPrime]
  ext D
  constructor
  · rintro ⟨D₀, ⟨P, hP, rfl⟩, rfl⟩
    refine ⟨P.map E.toLinearMap, isPacket_transport (p : ℕ) eL P hP, ?_⟩
    rw [← barePacketStabilizer_map_marked K U p hlevel,
      Subgroup.map_map,
      orientedRestriction_comp_markedQuotientEquiv K U p hlevel]
  · rintro ⟨Q, hQ, rfl⟩
    let P : GroupSubspace U.toSubgroup (p : ℕ) := Q.map E.symm.toLinearMap
    have hEsymm : E.symm = elementaryQuotientTransport (p : ℕ) eL.symm :=
      (elementaryQuotientTransport_symm (p : ℕ) eL).symm
    have hP : IsPacket (p : ℕ) P := by
      change IsPacket (p : ℕ) (Q.map E.symm.toLinearMap)
      rw [hEsymm]
      exact isPacket_transport (p : ℕ) eL.symm Q hQ
    have hmapP : P.map E.toLinearMap = Q := by
      dsimp [P]
      rw [← Submodule.map_comp]
      have hcomp : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
        ext x
        simp
      rw [hcomp, Submodule.map_id]
    refine ⟨barePacketStabilizer U p P, ⟨P, hP, rfl⟩, ?_⟩
    rw [← hmapP, ← barePacketStabilizer_map_marked K U p hlevel,
      Subgroup.map_map,
      orientedRestriction_comp_markedQuotientEquiv K U p hlevel]

/-- Exact marked-level correctness, in finite terms.  This is the existing
oriented finite-level theorem specialized at `U ⊆ C_p`, where the marked
intersection is literally `U`; it is not a new finite-level recovery proof. -/
theorem bareCrit_marked_correct_finite
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime) (hU : IsMarkedLevel K p U) :
    bareCrit U p = quotientDecompositionCollectionAway K U p := by
  have hmarked :
      levelKernel (galoisLevelOfOpenNormal K U) ≤
        (canonicalCyclotomicOrientation K).kernel p := by
    simpa [IsMarkedLevel, canonicalCyclotomicOrientation] using hU
  have horiented :=
    packetImagesAtOddPrime_eq_decompositionCollectionAway_of_le
      (canonicalCyclotomicOrientation K)
      (galoisLevelOfOpenNormal K U) p hmarked
  have htransport := bareCrit_eq_orientedPacketImages_of_marked K U p hU
  have htotal :
      Set.image
          (Subgroup.map (openNormalArithmeticEquiv K U).toMonoidHom)
          (bareCrit U p) =
        decompositionCollectionAway K
          (galoisLevelOfOpenNormal K U).field p :=
    htransport.trans horiented
  let e := openNormalArithmeticEquiv K U
  ext D
  constructor
  · intro hD
    have hm : Subgroup.map e.toMonoidHom D ∈
        decompositionCollectionAway K
          (galoisLevelOfOpenNormal K U).field p := by
      rw [← htotal]
      exact ⟨D, hD, rfl⟩
    obtain ⟨w, hw, hDw⟩ := hm
    refine ⟨w, hw, ?_⟩
    apply subgroupMap_mulEquiv_injective e
    calc
      Subgroup.map e.toMonoidHom D = decompositionGroup K w := hDw
      _ = Subgroup.map e.toMonoidHom
          (Subgroup.map e.symm.toMonoidHom (decompositionGroup K w)) :=
        (subgroupMap_mulEquiv_symm e (decompositionGroup K w)).symm
  · rintro ⟨w, hw, rfl⟩
    have hm : decompositionGroup K w ∈
        Set.image (Subgroup.map e.toMonoidHom) (bareCrit U p) := by
      rw [htotal]
      exact ⟨w, hw, rfl⟩
    obtain ⟨D, hD, hDw⟩ := hm
    have hEq : D =
        Subgroup.map e.symm.toMonoidHom (decompositionGroup K w) := by
      apply subgroupMap_mulEquiv_injective e
      calc
        Subgroup.map e.toMonoidHom D = decompositionGroup K w := hDw
        _ = Subgroup.map e.toMonoidHom
            (Subgroup.map e.symm.toMonoidHom (decompositionGroup K w)) :=
          (subgroupMap_mulEquiv_symm e (decompositionGroup K w)).symm
    rwa [← hEq]

/-- The residue characteristic of a finite place is the norm of its
prime ideal contracted to `ℤ`. -/
private theorem residueCharacteristic_eq_absNorm_under_aux
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

/-- Restriction through a number-field extension preserves residue
characteristic. -/
private theorem residueCharacteristic_restrictFinitePlace_aux
    (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : FinitePlace M) :
    residueCharacteristic (restrictFinitePlace L w) =
      residueCharacteristic w := by
  rw [residueCharacteristic_eq_absNorm_under_aux,
    residueCharacteristic_eq_absNorm_under_aux, restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

/-- Contracting a prime-local valuation ring through a number-field
extension gives the valuation ring at the contracted prime. -/
private theorem primeValuationSubring_comap_restrict_aux
    (K : Type*) {L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : FinitePlace L) :
    (primeValuationSubring w).comap (algebraMap K L) =
      primeValuationSubring (restrictFinitePlace K w) := by
  let v := restrictFinitePlace K w
  have hle : primeValuationSubring v ≤
      (primeValuationSubring w).comap (algebraMap K L) := by
    intro x hx
    rw [mem_primeValuationSubring_iff] at hx
    rw [ValuationSubring.mem_comap, mem_primeValuationSubring_iff]
    obtain ⟨a, b, hb, hab⟩ := hx
    refine ⟨algebraMap (𝓞 K) (𝓞 L) a,
      algebraMap (𝓞 K) (𝓞 L) b, ?_, ?_⟩
    · intro hbw
      apply hb
      change b ∈ (restrictFinitePlace K w).asIdeal
      exact hbw
    · have hcoe (c : 𝓞 K) :
          ((algebraMap (𝓞 K) (𝓞 L) c : 𝓞 L) : L) =
            algebraMap K L (c : K) := by
        calc
          _ = algebraMap (𝓞 K) L c :=
            (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L c).symm
          _ = algebraMap K L (c : K) :=
            IsScalarTower.algebraMap_apply (𝓞 K) K L c
      rw [hcoe, hcoe, ← map_mul, hab]
  have hne : (primeValuationSubring w).comap (algebraMap K L) ≠ ⊤ := by
    obtain ⟨a, ha, ha0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have haw : algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal := by
      exact ha
    have hlt : w.valuation L
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) < 1 :=
      (w.valuation_lt_one_iff_mem
        (algebraMap (𝓞 K) (𝓞 L) a)).2 haw
    have hmap0 : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).2 (by exact_mod_cast ha0)
    have hpos : 0 < w.valuation L (algebraMap K L (a : K)) :=
      (w.valuation L).pos_iff.mpr hmap0
    have hcoe :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) =
          algebraMap K L (a : K) := by
      calc
        _ = algebraMap (𝓞 K) L a :=
          (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a).symm
        _ = algebraMap K L (a : K) :=
          IsScalarTower.algebraMap_apply (𝓞 K) K L a
    rw [hcoe] at hlt
    have hinv : 1 < (w.valuation L (algebraMap K L (a : K)))⁻¹ :=
      (one_lt_inv₀ hpos).2 hlt
    intro htop
    have hz : (a : K)⁻¹ ∈
        (primeValuationSubring w).comap (algebraMap K L) := by
      rw [htop]
      trivial
    rw [ValuationSubring.mem_comap, primeValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hz
    rw [map_inv₀, Valuation.map_inv] at hz
    exact (not_le_of_gt hinv) hz
  letI : Ring.KrullDimLE 1 (primeValuationSubring v) := by
    change Ring.KrullDimLE 1
      (HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  exact (ValuationSubring.eq_of_le_of_ne_top
    (primeValuationSubring v) hle hne).symm

/-- Restriction along the identity inclusion fixes a finite place. -/
private theorem restrictLevelPlace_refl
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (w : FinitePlace L.field) :
    restrictLevelPlace (L := L) (M := L) le_rfl w = w := by
  letI : Algebra L.field L.field :=
    (IntermediateField.inclusion (show L.field ≤ L.field from le_rfl)).toAlgebra
  apply HeightOneSpectrum.ext
  rw [restrictLevelPlace, restrictFinitePlace_asIdeal]
  ext x
  change algebraMap (𝓞 L.field) (𝓞 L.field) x ∈ w.asIdeal ↔ _
  have hx : algebraMap (𝓞 L.field) (𝓞 L.field) x = x := by
    apply Subtype.ext
    rfl
  rw [hx]

/-- Restriction of finite places composes through nested Galois levels. -/
private theorem restrictLevelPlace_trans
    {K : Type*} [Field K] [NumberField K]
    {L M N : GaloisLevel K} (hLM : L.LE M) (hMN : M.LE N)
    (w : FinitePlace N.field) :
    restrictLevelPlace hLM (restrictLevelPlace hMN w) =
      restrictLevelPlace (hLM.trans hMN) w := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  letI : Algebra M.field N.field := (IntermediateField.inclusion hMN).toAlgebra
  letI : Algebra L.field N.field :=
    (IntermediateField.inclusion (hLM.trans hMN)).toAlgebra
  letI : IsScalarTower L.field M.field N.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply HeightOneSpectrum.ext
  rw [restrictLevelPlace, restrictLevelPlace, restrictLevelPlace,
    restrictFinitePlace_asIdeal, restrictFinitePlace_asIdeal,
    restrictFinitePlace_asIdeal]
  ext x
  change algebraMap (𝓞 M.field) (𝓞 N.field)
      (algebraMap (𝓞 L.field) (𝓞 M.field) x) ∈ w.asIdeal ↔
    algebraMap (𝓞 L.field) (𝓞 N.field) x ∈ w.asIdeal
  have hx : algebraMap (𝓞 M.field) (𝓞 N.field)
      (algebraMap (𝓞 L.field) (𝓞 M.field) x) =
        algebraMap (𝓞 L.field) (𝓞 N.field) x := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply L.field M.field N.field x
  rw [hx]

/-- A finite place prolongs through an inclusion of finite Galois levels. -/
private theorem exists_finitePlace_over_level
    {K : Type*} [Field K] [NumberField K]
    {L M : GaloisLevel K} (hLM : L.LE M) (w : FinitePlace L.field) :
    ∃ v : FinitePlace M.field, restrictLevelPlace hLM v = w := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  let q := Classical.choice
    (w.asIdeal.nonempty_primesOver (S := 𝓞 M.field))
  have hq0 : q.1 ≠ ⊥ := by
    intro h
    apply w.ne_bot
    rw [q.2.2.over]
    change Ideal.comap (algebraMap (𝓞 L.field) (𝓞 M.field)) q.1 = ⊥
    rw [h]
    exact Ideal.comap_bot_of_injective
      (algebraMap (𝓞 L.field) (𝓞 M.field))
      (FaithfulSMul.algebraMap_injective (𝓞 L.field) (𝓞 M.field))
  let v : FinitePlace M.field := ⟨q.1, q.2.1, hq0⟩
  refine ⟨v, ?_⟩
  apply HeightOneSpectrum.ext
  exact q.2.2.over.symm

/-- There are finitely many prolongations of a fixed finite place through a
finite Galois level. -/
private theorem finite_places_over_level
    {K : Type*} [Field K] [NumberField K]
    {L M : GaloisLevel K} (hLM : L.LE M) (w : FinitePlace L.field) :
    Set.Finite {v : FinitePlace M.field | restrictLevelPlace hLM v = w} := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  let f : {v : FinitePlace M.field | restrictLevelPlace hLM v = w} →
      w.asIdeal.primesOver (𝓞 M.field) := fun v =>
    ⟨v.1.asIdeal, v.1.isPrime, by
      rw [Ideal.liesOver_iff]
      have hv := congrArg HeightOneSpectrum.asIdeal v.2
      exact hv.symm⟩
  have hf : Function.Injective f := by
    intro v z hvz
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    exact congrArg Subtype.val hvz
  letI : Fintype (w.asIdeal.primesOver (𝓞 M.field)) :=
    (IsDedekindDomain.primesOver_finite w.asIdeal (𝓞 M.field)).fintype
  letI : Finite {v : FinitePlace M.field |
      restrictLevelPlace hLM v = w} := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp inferInstance

/-- The compositum used to direct all finite Galois levels above a fixed
one. -/
private noncomputable def placeSupGaloisLevel
    {K : Type*} [Field K] [NumberField K]
    (L M : GaloisLevel K) : GaloisLevel K where
  field := L.field ⊔ M.field
  finiteDimensional := L.field.finiteDimensional_sup M.field
  numberField := NumberField.of_module_finite K _
  isGalois := by infer_instance

/-- Every finite-level place has an absolute prolongation, constructed by
the proved finite-inverse-system compactness theorem. -/
private theorem exists_absolutePlace_over_level
    (K : Type*) [Field K] [NumberField K]
    (L : GaloisLevel K) (w : FinitePlace L.field) :
    ∃ W : ValuationSubring (AlgebraicClosure K),
      IsAbsoluteFinitePlace K W ∧
        W.comap L.field.val.toRingHom = primeValuationSubring w := by
  let ι := {M : GaloisLevel K // L.LE M}
  let Λ : ι → GaloisLevel K := fun M => M.1
  letI : Preorder ι :=
    { le := fun M N => M.1.LE N.1
      le_refl := fun _ => le_rfl
      le_trans := fun _ _ _ h₁ h₂ => h₁.trans h₂ }
  letI : IsDirected ι (· ≤ ·) := IsDirected.mk fun M N => by
    let T := placeSupGaloisLevel M.1 N.1
    let i : ι := ⟨T, M.2.trans le_sup_left⟩
    refine ⟨i, ?_, ?_⟩
    · change M.1.field ≤ T.field
      exact le_sup_left
    · change N.1.field ≤ T.field
      exact le_sup_right
  let S : ι → Type _ := fun M =>
    {v : FinitePlace (Λ M).field // restrictLevelPlace M.2 v = w}
  letI (M : ι) : Finite (S M) :=
    Set.finite_coe_iff.mpr (finite_places_over_level M.2 w)
  letI (M : ι) : Nonempty (S M) := by
    obtain ⟨v, hv⟩ := exists_finitePlace_over_level M.2 w
    exact ⟨⟨v, hv⟩⟩
  let r : ∀ {M N : ι}, M ≤ N → S N → S M := fun {M N} h v =>
    ⟨restrictLevelPlace h v.1, by
      rw [restrictLevelPlace_trans]
      exact v.2⟩
  have rid : ∀ M (v : S M), r (le_refl M) v = v := by
    intro M v
    apply Subtype.ext
    exact restrictLevelPlace_refl (Λ M) v.1
  have rcomp : ∀ {M N T : ι} (hMN : M ≤ N) (hNT : N ≤ T)
      (v : S T), r hMN (r hNT v) = r (hMN.trans hNT) v := by
    intro M N T hMN hNT v
    apply Subtype.ext
    exact restrictLevelPlace_trans hMN hNT v.1
  obtain ⟨x, hx⟩ := finite_inverse_system_compactness S r rid rcomp
  have hΛ : IsCofinalGaloisSystem Λ := by
    refine ⟨⟨⟨L, le_rfl⟩⟩, ?_, ?_⟩
    · intro M N
      obtain ⟨T, hMT, hNT⟩ := exists_ge_ge M N
      exact ⟨T, hMT, hNT⟩
    · intro M
      let T := placeSupGaloisLevel L M
      exact ⟨⟨T, le_sup_left⟩, le_sup_right⟩
  have hcompat : IsCompatiblePlaceFamily Λ (fun M => (x M).1) := by
    intro M N hMN
    exact congrArg Subtype.val (hx hMN)
  obtain ⟨W, hW⟩ := exists_union_valuationSubring Λ hΛ
    (fun M => (x M).1) hcompat
  let i0 : ι := ⟨L, le_rfl⟩
  have hWL : W.comap L.field.val.toRingHom = primeValuationSubring w := by
    rw [hW i0]
    congr 1
    exact (restrictLevelPlace_refl L (x i0).1).symm.trans (x i0).2
  have hbase : W.comap (algebraMap K (AlgebraicClosure K)) =
      primeValuationSubring (restrictFinitePlace K w) := by
    calc
      W.comap (algebraMap K (AlgebraicClosure K)) =
          (W.comap L.field.val.toRingHom).comap
            (algebraMap K L.field) := by
        ext y
        simp only [ValuationSubring.mem_comap]
        rfl
      _ = (primeValuationSubring w).comap (algebraMap K L.field) := by
        rw [hWL]
      _ = primeValuationSubring (restrictFinitePlace K w) :=
        primeValuationSubring_comap_restrict_aux K w
  have hWne : W ≠ ⊤ := by
    intro htop
    apply primeValuationSubring_ne_top w
    rw [← hWL, htop]
    ext y
    simp
  exact ⟨W, ⟨hWne, restrictFinitePlace K w, hbase⟩, hWL⟩

/-- Finite and absolute formulations of the marked-level right-hand side
agree by extension and tower surjectivity of decomposition groups. -/
theorem quotientDecompositionCollectionAway_eq_absoluteImages
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime) :
    quotientDecompositionCollectionAway K U p =
      {D | ∃ W : ValuationSubring (AlgebraicClosure K),
        IsAbsoluteFinitePlaceAway K p W ∧
          D = openNormalQuotientImage U
            (absoluteDecompositionGroup K W)} := by
  let L := galoisLevelOfOpenNormal K U
  let e := openNormalArithmeticEquiv K U
  ext D
  constructor
  · rintro ⟨w, hwaway, rfl⟩
    obtain ⟨W, hW, hWL⟩ := exists_absolutePlace_over_level K L w
    have hplace : absolutePlaceAtLevel W hW L = w := by
      let A := W.comap L.field.val.toRingHom
      have hA : IsNontrivialValuation A :=
        absolutePlace_comap_nontrivial W hW L
      simpa [absolutePlaceAtLevel, centerFinitePlace, A] using
        ((numberField_valuations A hA).choose_spec.2 w hWL).symm
    have hbase : W.comap (algebraMap K (AlgebraicClosure K)) =
        primeValuationSubring (restrictFinitePlace K w) := by
      calc
        W.comap (algebraMap K (AlgebraicClosure K)) =
            (W.comap L.field.val.toRingHom).comap
              (algebraMap K L.field) := by
          ext y
          simp only [ValuationSubring.mem_comap]
          rfl
        _ = (primeValuationSubring w).comap
            (algebraMap K L.field) := by rw [hWL]
        _ = primeValuationSubring (restrictFinitePlace K w) :=
          primeValuationSubring_comap_restrict_aux K w
    refine ⟨W, ⟨hW, ⟨restrictFinitePlace K w, hbase, ?_⟩⟩, ?_⟩
    · rw [residueCharacteristic_restrictFinitePlace_aux]
      exact hwaway
    · apply subgroupMap_mulEquiv_injective e
      rw [subgroupMap_mulEquiv_symm,
        openNormalArithmeticEquiv_image,
        absoluteDecompositionGroup_finiteImage W hW L, hplace]
  · rintro ⟨W, haway, rfl⟩
    let w := absolutePlaceAtLevel W haway.1 L
    obtain ⟨v, hvbase, hvaway⟩ := haway.2
    have hlevel : primeValuationSubring w =
        W.comap L.field.val.toRingHom :=
      primeValuationSubring_centerFinitePlace _ _
    have hbaseRestrict :
        W.comap (algebraMap K (AlgebraicClosure K)) =
          primeValuationSubring (restrictFinitePlace K w) := by
      calc
        W.comap (algebraMap K (AlgebraicClosure K)) =
            (W.comap L.field.val.toRingHom).comap
              (algebraMap K L.field) := by
          ext y
          simp only [ValuationSubring.mem_comap]
          rfl
        _ = (primeValuationSubring w).comap
            (algebraMap K L.field) := by rw [hlevel]
        _ = primeValuationSubring (restrictFinitePlace K w) :=
          primeValuationSubring_comap_restrict_aux K w
    have hbaseNontrivial :
        IsNontrivialValuation
          (W.comap (algebraMap K (AlgebraicClosure K))) := by
      rw [hvbase]
      exact primeValuationSubring_ne_top v
    have hrestrict : restrictFinitePlace K w = v := by
      have hu := numberField_valuations
        (W.comap (algebraMap K (AlgebraicClosure K))) hbaseNontrivial
      exact (hu.choose_spec.2 (restrictFinitePlace K w) hbaseRestrict).trans
        (hu.choose_spec.2 v hvbase).symm
    refine ⟨w, ?_, ?_⟩
    · rw [← residueCharacteristic_restrictFinitePlace_aux K w, hrestrict]
      exact hvaway
    · apply subgroupMap_mulEquiv_injective e
      rw [subgroupMap_mulEquiv_symm,
        openNormalArithmeticEquiv_image,
        absoluteDecompositionGroup_finiteImage W haway.1 L]

/-- Exact marked-level correctness in the absolute form
`Crit_U^p = {π_U(D_P) : char κ(P) ≠ p}`.  There are no auxiliary depth or
usability hypotheses. -/
theorem bareCrit_marked_correct
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (p : OddPrime) (hU : IsMarkedLevel K p U) :
    bareCrit U p =
      {D | ∃ W : ValuationSubring (AlgebraicClosure K),
        IsAbsoluteFinitePlaceAway K p W ∧
          D = openNormalQuotientImage U
            (absoluteDecompositionGroup K W)} := by
  rw [bareCrit_marked_correct_finite K U p hU,
    quotientDecompositionCollectionAway_eq_absoluteImages]

/-! ## Completeness and anchored soundness -/

/-- A fiber of evaluation at an algebraic element is open in the Krull
topology. -/
private theorem algEquiv_fiber_isOpen
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x y : Ω) :
    IsOpen {g : Ω ≃ₐ[K] Ω | g x = y} := by
  by_cases h : ∃ g : Ω ≃ₐ[K] Ω, g x = y
  · obtain ⟨g₀, hg₀⟩ := h
    have heq : {g : Ω ≃ₐ[K] Ω | g x = y} =
        g₀ • (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)) := by
      ext g
      rw [mem_leftCoset_iff, Set.mem_setOf_eq]
      change (g x = y) ↔ (g₀⁻¹ * g) x = x
      constructor
      · intro hg
        change g₀.symm (g x) = x
        rw [hg, ← hg₀]
        exact g₀.symm_apply_apply x
      · intro hg
        have := congrArg g₀ hg
        simpa [hg₀] using this
    rw [heq]
    exact (stabilizer_isOpen_of_isIntegral x).leftCoset g₀
  · have heq : {g : Ω ≃ₐ[K] Ω | g x = y} = ∅ := by
      ext g
      constructor
      · intro hg
        exact (h ⟨g, hg⟩).elim
      · intro hg
        exact hg.elim
    rw [heq]
    exact isOpen_empty

/-- Evaluation at one algebraic element has clopen preimages of arbitrary
subsets of the algebraic closure. -/
private theorem algEquiv_eval_preimage_isClopen
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x : Ω) (S : Set Ω) :
    IsClopen {g : Ω ≃ₐ[K] Ω | g x ∈ S} := by
  have heq : {g : Ω ≃ₐ[K] Ω | g x ∈ S} =
      ⋃ y ∈ S, {g : Ω ≃ₐ[K] Ω | g x = y} := by
    ext g
    simp
  have hopen : IsOpen {g : Ω ≃ₐ[K] Ω | g x ∈ S} := by
    rw [heq]
    exact isOpen_biUnion fun y _ => algEquiv_fiber_isOpen x y
  have hcompl : {g : Ω ≃ₐ[K] Ω | g x ∈ S}ᶜ =
      {g : Ω ≃ₐ[K] Ω | g x ∈ Sᶜ} := by
    ext g
    simp
  refine ⟨?_, hopen⟩
  apply isOpen_compl_iff.mp
  rw [hcompl]
  rw [show {g : Ω ≃ₐ[K] Ω | g x ∈ Sᶜ} =
      ⋃ y ∈ Sᶜ, {g : Ω ≃ₐ[K] Ω | g x = y} by
        ext g
        simp]
  exact isOpen_biUnion fun y _ => algEquiv_fiber_isOpen x y

private theorem mem_stabilizer_valuationSubring_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (W : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) :
    g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) W ↔
      ∀ x : Ω, x ∈ W ↔ g x ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg x
    have hmem := ValuationSubring.smul_mem_pointwise_smul_iff
      (g := g) (S := W) (x := x)
    rw [hg] at hmem
    simpa [AlgEquiv.smul_def] using hmem.symm
  · intro hg
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := g) (S := W) (x := x)]
    change (g⁻¹ x ∈ W) ↔ x ∈ W
    simpa using hg (g⁻¹ x)

/-- Absolute decomposition groups are closed in the Krull topology. -/
theorem absoluteDecompositionGroup_isClosed
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) :
    IsClosed (absoluteDecompositionGroup K W :
      Set (Field.absoluteGaloisGroup K)) := by
  change IsClosed ((MulAction.stabilizer
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W) :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  have heq : ((MulAction.stabilizer
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W) :
        Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) =
      ⋂ x : AlgebraicClosure K,
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          x ∈ W ↔ g x ∈ W} := by
    ext g
    constructor
    · intro hg
      have hs := (mem_stabilizer_valuationSubring_iff W g).mp hg
      rw [Set.mem_iInter]
      exact hs
    · intro hg
      apply (mem_stabilizer_valuationSubring_iff W g).mpr
      rw [Set.mem_iInter] at hg
      exact hg
  rw [heq]
  apply isClosed_iInter
  intro x
  by_cases hx : x ∈ W
  · have hset : {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        x ∈ W ↔ g x ∈ W} =
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          g x ∈ (W : Set _)} := by
      ext g
      simp [hx]
    rw [hset]
    exact (algEquiv_eval_preimage_isClopen
      (K := K) (Ω := AlgebraicClosure K) x (W : Set _)).1
  · have hset : {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        x ∈ W ↔ g x ∈ W} =
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          g x ∈ (W : Set _)}ᶜ := by
      ext g
      simp [hx]
    rw [hset]
    exact (algEquiv_eval_preimage_isClopen
      (K := K) (Ω := AlgebraicClosure K) x (W : Set _)).2.isClosed_compl

/-- Completeness: every absolute decomposition group away from `p` belongs
to `𝒟_p`, witnessed by the canonical cofinal system of marked levels. -/
theorem bare_recovery_complete
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlaceAway K p W) :
    absoluteDecompositionGroup K W ∈
      bareRecoveredAtPrime (Field.absoluteGaloisGroup K) p := by
  refine ⟨absoluteDecompositionGroup_isClosed K W,
    absoluteDecompositionGroup_not_procyclic W hW.1, ?_⟩
  intro V hV
  obtain ⟨U, hmarked, hUV⟩ := (markedLevels_cofinal K p).2.2 V hV
  refine ⟨U, ?_, hUV⟩
  change openNormalQuotientImage U (absoluteDecompositionGroup K W) ∈
    bareCrit U p
  rw [bareCrit_marked_correct K U p hmarked]
  exact ⟨W, hW, rfl⟩

/-- The finite-place witness set `S_U` used in anchored soundness.  Its
membership condition is equality of decomposition subgroups, not conjugacy,
and its elements are finite places of `M_U`, not absolute prolongations. -/
def bareFiniteWitnesses
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    Set (FinitePlace (galoisLevelOfOpenNormal K U).field) :=
  {w | residueCharacteristic w ≠ (p : ℕ) ∧
    decompositionGroup K w =
      finiteLevelImage (galoisLevelOfOpenNormal K U) H}

/-- The compositum of two finite Galois levels. -/
private noncomputable def supGaloisLevel
    {K : Type*} [Field K] [NumberField K]
    (L M : GaloisLevel K) : GaloisLevel K where
  field := L.field ⊔ M.field
  finiteDimensional := L.field.finiteDimensional_sup M.field
  numberField := NumberField.of_module_finite K _
  isGalois := by infer_instance

/-- All bundled finite Galois levels form a cofinal system. -/
private theorem allGaloisLevels_cofinal
    (K : Type*) [Field K] [NumberField K] :
    IsCofinalGaloisSystem (fun L : GaloisLevel K => L) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro L M
    exact ⟨supGaloisLevel L M, le_sup_left, le_sup_right⟩
  · intro L
    exact ⟨L, le_rfl⟩

private theorem levelKernel_eq_fixingSubgroup
    (K : Type*) [Field K] [NumberField K] (L : GaloisLevel K) :
    levelKernel L = L.field.fixingSubgroup := by
  change (AlgEquiv.restrictNormalHom L.field).ker = L.field.fixingSubgroup
  exact IntermediateField.restrictNormalHom_ker L.field

private def kernelOpenNormal
    (K : Type*) [Field K] [NumberField K] (L : GaloisLevel K) :
    OpenNormalSubgroup (Field.absoluteGaloisGroup K) where
  toSubgroup := levelKernel L
  isOpen' := by
    rw [levelKernel_eq_fixingSubgroup K L]
    exact IntermediateField.fixingSubgroup_isOpen L.field
  normal' := inferInstance

private noncomputable def levelQuotientEquiv
    (K : Type*) [Field K] [NumberField K] (L : GaloisLevel K) :
    (Field.absoluteGaloisGroup K ⧸ (kernelOpenNormal K L).toSubgroup) ≃*
      (L.field ≃ₐ[K] L.field) :=
  (QuotientGroup.quotientMulEquivOfEq
    (show (kernelOpenNormal K L).toSubgroup = levelKernel L from rfl)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (absoluteRestriction L)
        (AlgEquiv.restrictNormalHom_surjective
          (F := K) (K₁ := L.field) (AlgebraicClosure K)))

@[simp]
private theorem levelQuotientEquiv_mk
    (K : Type*) [Field K] [NumberField K] (L : GaloisLevel K)
    (g : Field.absoluteGaloisGroup K) :
    levelQuotientEquiv K L (QuotientGroup.mk g) =
      absoluteRestriction L g :=
  rfl

private theorem levelQuotientImage_eq
    (K : Type*) [Field K] [NumberField K] (L : GaloisLevel K)
    (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Subgroup.map (levelQuotientEquiv K L).toMonoidHom
        (openNormalQuotientImage (kernelOpenNormal K L) H) =
      finiteLevelImage L H := by
  rw [openNormalQuotientImage, finiteLevelImage, Subgroup.map_map]
  congr 1

/-- Step 1: a closed non-procyclic subgroup has a noncyclic finite reference
quotient.  This `U₀` is external: it is not asserted to be a passing level. -/
theorem exists_external_noncyclic_anchor
    (K : Type*) [Field K] [NumberField K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (hnonpro : ¬IsProcyclic H) :
    ∃ U₀ : OpenNormalSubgroup (Field.absoluteGaloisGroup K),
      ¬IsCyclic (openNormalQuotientImage U₀ H) := by
  by_contra h
  push Not at h
  apply hnonpro
  apply cyclic_finite_images_imply_procyclic
    (fun L : GaloisLevel K => L) (allGaloisLevels_cofinal K) H hclosed
  intro L
  have hc := h (kernelOpenNormal K L)
  have himage : IsCyclic
      (Subgroup.map (levelQuotientEquiv K L).toMonoidHom
        (openNormalQuotientImage (kernelOpenNormal K L) H)) :=
    (Subgroup.equivMapOfInjective
      (openNormalQuotientImage (kernelOpenNormal K L) H)
      (levelQuotientEquiv K L).toMonoidHom
      (levelQuotientEquiv K L).injective).isCyclic.mp hc
  rw [levelQuotientImage_eq] at himage
  exact himage

/-- Restriction between quotient levels induced by inclusion. -/
private noncomputable def openNormalQuotientTransition
    {G : Type*} [Group G] [TopologicalSpace G]
    {U V : OpenNormalSubgroup G} (hUV : U.LE V) :
    (G ⧸ U.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) hUV

@[simp]
private theorem openNormalQuotientTransition_mk
    {G : Type*} [Group G] [TopologicalSpace G]
    {U V : OpenNormalSubgroup G} (hUV : U.LE V) (g : G) :
    openNormalQuotientTransition hUV (QuotientGroup.mk g) =
      QuotientGroup.mk g :=
  rfl

private theorem openNormalQuotientTransition_image
    {G : Type*} [Group G] [TopologicalSpace G]
    {U V : OpenNormalSubgroup G} (hUV : U.LE V) (H : Subgroup G) :
    Subgroup.map (openNormalQuotientTransition hUV)
        (openNormalQuotientImage U H) = openNormalQuotientImage V H := by
  rw [openNormalQuotientImage, openNormalQuotientImage, Subgroup.map_map]
  congr 1

private theorem noncyclic_finiteImage_of_anchor
    (K : Type*) [Field K] [NumberField K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (U₀ U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hanchor : ¬IsCyclic (openNormalQuotientImage U₀ H))
    (hbelow : U.LE U₀) :
    ¬IsCyclic (finiteLevelImage (galoisLevelOfOpenNormal K U) H) := by
  intro hcycFinite
  let e := openNormalArithmeticEquiv K U
  have hcycQuot : IsCyclic (openNormalQuotientImage U H) := by
    have heq := openNormalArithmeticEquiv_image K U H
    have hmap : IsCyclic
        (Subgroup.map e.toMonoidHom (openNormalQuotientImage U H)) := by
      rwa [heq]
    exact (Subgroup.equivMapOfInjective (openNormalQuotientImage U H)
      e.toMonoidHom e.injective).isCyclic.mpr hmap
  apply hanchor
  have hmapcyc : IsCyclic
      (Subgroup.map (openNormalQuotientTransition hbelow)
        (openNormalQuotientImage U H)) :=
    isCyclic_of_surjective
      ((openNormalQuotientTransition hbelow).subgroupMap
        (openNormalQuotientImage U H))
      ((openNormalQuotientTransition hbelow).subgroupMap_surjective
        (openNormalQuotientImage U H))
  rwa [openNormalQuotientTransition_image] at hmapcyc

/-- Steps 0--2: after extracting marked passing levels below the external
anchor, the exact finite-place witness set is nonempty and finite. -/
theorem bareFiniteWitnesses_nonempty_finite_of_anchor
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (U₀ U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hanchor : ¬IsCyclic (openNormalQuotientImage U₀ H))
    (hbelow : U.LE U₀) (hmarked : IsMarkedLevel K p U)
    (hpass : IsPassingLevel p H U) :
    (bareFiniteWitnesses K p H U).Nonempty ∧
      (bareFiniteWitnesses K p H U).Finite := by
  have hcrit : openNormalQuotientImage U H ∈ bareCrit U p := hpass
  rw [bareCrit_marked_correct_finite K U p hmarked] at hcrit
  obtain ⟨w, hwaway, hwquot⟩ := hcrit
  let L := galoisLevelOfOpenNormal K U
  let e := openNormalArithmeticEquiv K U
  have hwimage : decompositionGroup K w = finiteLevelImage L H := by
    have hm := congrArg (Subgroup.map e.toMonoidHom) hwquot
    rw [subgroupMap_mulEquiv_symm] at hm
    calc
      decompositionGroup K w =
          Subgroup.map e.toMonoidHom (openNormalQuotientImage U H) := hm.symm
      _ = finiteLevelImage L H := openNormalArithmeticEquiv_image K U H
  have hnon : ¬IsCyclic (finiteLevelImage L H) :=
    noncyclic_finiteImage_of_anchor K H U₀ U hanchor hbelow
  have hdecomp : ∀ _ : Unit, finiteLevelImage L H ∈
      decompositionCollection K L.field := by
    intro _
    exact ⟨w, hwimage⟩
  have hsystem := finite_witness_system (fun _ : Unit => L) H () hnon
    hdecomp () le_rfl
  constructor
  · exact ⟨w, hwaway, hwimage⟩
  · exact hsystem.2.subset (by
      intro v hv
      exact hv.2)

/-- The residue characteristic of a finite place is the norm of its
prime ideal contracted to `ℤ`. -/
private theorem residueCharacteristic_eq_absNorm_under
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    residueCharacteristic v = Ideal.absNorm (Ideal.under ℤ v.asIdeal) := by
  letI : Algebra (𝓞 K) (primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime (primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (primeValuationSubring v)
  calc
    residueCharacteristic v = ringChar ((𝓞 K) ⧸ v.asIdeal) := by
      rw [residueCharacteristic, ringChar.eq_iff]
      exact (e.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 K) ⧸ v.asIdeal))
    _ = Ideal.absNorm (Ideal.under ℤ v.asIdeal) := Ideal.ringChar_quot _

/-- Restriction through a number-field extension preserves residue
characteristic. -/
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

/-- Restriction of finite places along an inclusion `U' ⊆ U`. -/
noncomputable def restrictOpenNormalPlace
    (K : Type*) [Field K] [NumberField K]
    {U' U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    (hU'U : U'.LE U)
    (w : FinitePlace (galoisLevelOfOpenNormal K U').field) :
    FinitePlace (galoisLevelOfOpenNormal K U).field :=
  restrictLevelPlace (galoisLevelOfOpenNormal_antitone K hU'U) w

/-- Restriction at an unchanged open normal level is the identity. -/
private theorem restrictOpenNormalPlace_refl
    (K : Type*) [Field K] [NumberField K]
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (w : FinitePlace (galoisLevelOfOpenNormal K U).field) :
    restrictOpenNormalPlace K (U := U) (U' := U) le_rfl w = w := by
  unfold restrictOpenNormalPlace
  exact restrictLevelPlace_refl (galoisLevelOfOpenNormal K U) w

/-- Open-normal place restriction composes down a tower. -/
private theorem restrictOpenNormalPlace_trans
    (K : Type*) [Field K] [NumberField K]
    {W V U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    (hVU : V.LE U) (hWV : W.LE V)
    (w : FinitePlace (galoisLevelOfOpenNormal K W).field) :
    restrictOpenNormalPlace K hVU
        (restrictOpenNormalPlace K hWV w) =
      restrictOpenNormalPlace K (hWV.trans hVU) w := by
  unfold restrictOpenNormalPlace
  exact restrictLevelPlace_trans
    (galoisLevelOfOpenNormal_antitone K hVU)
    (galoisLevelOfOpenNormal_antitone K hWV) w

/-- Step 3: one inclusion of levels supplies the transition map on the exact
witness sets.  No canonical ambient system and no surjectivity hypothesis on
inverse-system transitions is used. -/
theorem restrictOpenNormalPlace_mem_bareFiniteWitnesses
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    {U' U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    (hU'U : U'.LE U)
    {w : FinitePlace (galoisLevelOfOpenNormal K U').field}
    (hw : w ∈ bareFiniteWitnesses K p H U') :
    restrictOpenNormalPlace K hU'U w ∈
      bareFiniteWitnesses K p H U := by
  refine ⟨?_, ?_⟩
  · unfold restrictOpenNormalPlace restrictLevelPlace
    rw [residueCharacteristic_restrictFinitePlace]
    exact hw.1
  · exact restrictLevelPlace_mem_finiteWitnesses H
      (galoisLevelOfOpenNormal_antitone K hU'U) hw.2

/-- Soundness by anchored descent (Steps 0--5): extraction into `C_p`, an
external noncyclic anchor, the finite sets `S_U`, restriction transitions,
finite-inverse-system compactness, gluing to an absolute place, and equality
of closed subgroups from cofinal quotient images. -/
theorem bare_recovery_sound
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (hH : H ∈ bareRecoveredAtPrime (Field.absoluteGaloisGroup K) p) :
    ∃ W : ValuationSubring (AlgebraicClosure K),
      IsAbsoluteFinitePlaceAway K p W ∧
        H = absoluteDecompositionGroup K W := by
  obtain ⟨hclosed, hnonpro, hpassing⟩ := hH
  obtain ⟨U₀, hanchor⟩ :=
    exists_external_noncyclic_anchor K H hclosed hnonpro
  let Good := fun U : OpenNormalSubgroup (Field.absoluteGaloisGroup K) =>
    IsMarkedLevel K p U ∧ IsPassingLevel p H U ∧ U.LE U₀
  have hGood : IsCofinalOpenNormalSet {U | Good U} := by
    intro V hV
    let V' : Subgroup (Field.absoluteGaloisGroup K) :=
      (V ⊓ U₀.toSubgroup) ⊓ cyclotomicKernel K (p : ℕ)
    have hV' : IsOpen (V' : Set (Field.absoluteGaloisGroup K)) :=
      (hV.inter U₀.isOpen').inter (cyclotomicKernel_isOpen K p)
    obtain ⟨U, hpass, hU⟩ := hpassing V' hV'
    refine ⟨U, ?_, ?_⟩
    · exact ⟨hU.trans inf_le_right, hpass,
        hU.trans (inf_le_left.trans inf_le_right)⟩
    · exact hU.trans (inf_le_left.trans inf_le_left)
  let ι := {U : OpenNormalSubgroup (Field.absoluteGaloisGroup K) // Good U}
  let Λ : ι → GaloisLevel K := fun U => galoisLevelOfOpenNormal K U.1
  letI : Preorder ι :=
    { le := fun U V => V.1.LE U.1
      le_refl := fun _ => le_rfl
      le_trans := fun _ _ _ hUV hVW => hVW.trans hUV }
  letI : IsDirected ι (· ≤ ·) := IsDirected.mk fun U V => by
    obtain ⟨W, hW, hWU, hWV⟩ :=
      cofinalOpenNormalSet_directed {T | Good T} hGood U.1 U.2 V.1 V.2
    exact ⟨⟨W, hW⟩, hWU, hWV⟩
  let S : ι → Type _ := fun U =>
    {w : FinitePlace (Λ U).field // w ∈ bareFiniteWitnesses K p H U.1}
  letI (U : ι) : Finite (S U) :=
    Set.finite_coe_iff.mpr
      (bareFiniteWitnesses_nonempty_finite_of_anchor K p H U₀ U.1
        hanchor U.2.2.2 U.2.1 U.2.2.1).2
  letI (U : ι) : Nonempty (S U) := by
    obtain ⟨w, hw⟩ :=
      (bareFiniteWitnesses_nonempty_finite_of_anchor K p H U₀ U.1
        hanchor U.2.2.2 U.2.1 U.2.2.1).1
    exact ⟨⟨w, hw⟩⟩
  let r : ∀ {U V : ι}, U ≤ V → S V → S U := fun {U V} h w =>
    ⟨restrictOpenNormalPlace K h w.1,
      restrictOpenNormalPlace_mem_bareFiniteWitnesses K p H h w.2⟩
  have rid : ∀ U (w : S U), r (le_refl U) w = w := by
    intro U w
    apply Subtype.ext
    exact restrictOpenNormalPlace_refl K U.1 w.1
  have rcomp : ∀ {U V W : ι} (hUV : U ≤ V) (hVW : V ≤ W)
      (w : S W), r hUV (r hVW w) = r (hUV.trans hVW) w := by
    intro U V W hUV hVW w
    apply Subtype.ext
    exact restrictOpenNormalPlace_trans K hUV hVW w.1
  obtain ⟨x, hx⟩ := finite_inverse_system_compactness S r rid rcomp
  have hΛ : IsCofinalGaloisSystem Λ := by
    have hι : Nonempty ι := by
      obtain ⟨U, hU, _⟩ := hGood (⊤ : Subgroup _ ) isOpen_univ
      exact ⟨⟨U, hU⟩⟩
    refine ⟨hι, ?_, ?_⟩
    · intro U V
      obtain ⟨W, hUW, hVW⟩ := exists_ge_ge U V
      exact ⟨W,
        galoisLevelOfOpenNormal_antitone K hUW,
        galoisLevelOfOpenNormal_antitone K hVW⟩
    · intro M
      obtain ⟨U, hU, hUkernel⟩ :=
        hGood (kernelOpenNormal K M).toSubgroup
          (kernelOpenNormal K M).isOpen'
      refine ⟨⟨U, hU⟩, ?_⟩
      change M.field ≤ (galoisLevelOfOpenNormal K U).field
      rw [← InfiniteGalois.fixedField_fixingSubgroup M.field]
      apply IntermediateField.fixedField_le
      rw [← levelKernel_eq_fixingSubgroup K M]
      exact hUkernel
  have hcompat : IsCompatiblePlaceFamily Λ (fun U => (x U).1) := by
    intro U V hUV
    have hsub : V.1.LE U.1 := by
      change V.1.toSubgroup ≤ U.1.toSubgroup
      rw [← levelKernel_galoisLevelOfOpenNormal K V.1,
        ← levelKernel_galoisLevelOfOpenNormal K U.1,
        levelKernel_eq_fixingSubgroup K (Λ V),
        levelKernel_eq_fixingSubgroup K (Λ U)]
      intro g hg
      change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) ∈
          (Λ V).field.fixingSubgroup at hg
      change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) ∈
          (Λ U).field.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
      intro y hy
      exact hg y (hUV hy)
    have hr := congrArg Subtype.val (hx hsub)
    exact hr
  obtain ⟨W, hWlevels⟩ := exists_union_valuationSubring Λ hΛ
    (fun U => (x U).1) hcompat
  let i₀ : ι := Classical.choice (show Nonempty ι from hΛ.1)
  let w₀ : FinitePlace (Λ i₀).field := (x i₀).1
  have hW₀ : W.comap (Λ i₀).field.val.toRingHom =
      primeValuationSubring w₀ := hWlevels i₀
  have hbase : W.comap (algebraMap K (AlgebraicClosure K)) =
      primeValuationSubring (restrictFinitePlace K w₀) := by
    calc
      W.comap (algebraMap K (AlgebraicClosure K)) =
          (W.comap (Λ i₀).field.val.toRingHom).comap
            (algebraMap K (Λ i₀).field) := by
        ext y
        simp only [ValuationSubring.mem_comap]
        rfl
      _ = (primeValuationSubring w₀).comap
          (algebraMap K (Λ i₀).field) := by rw [hW₀]
      _ = primeValuationSubring (restrictFinitePlace K w₀) :=
        primeValuationSubring_comap_restrict_aux K w₀
  have hWne : W ≠ ⊤ := by
    intro htop
    apply primeValuationSubring_ne_top w₀
    rw [← hW₀, htop]
    ext y
    simp
  have hWabs : IsAbsoluteFinitePlace K W :=
    ⟨hWne, restrictFinitePlace K w₀, hbase⟩
  have hWaway : IsAbsoluteFinitePlaceAway K p W := by
    refine ⟨hWabs, restrictFinitePlace K w₀, hbase, ?_⟩
    rw [residueCharacteristic_restrictFinitePlace]
    exact (x i₀).2.1
  refine ⟨W, hWaway, ?_⟩
  apply closed_subgroups_eq_of_cofinal_images Λ hΛ H
    (absoluteDecompositionGroup K W) hclosed
    (absoluteDecompositionGroup_isClosed K W)
  intro U
  have hplace : absolutePlaceAtLevel W hWabs (Λ U) = (x U).1 := by
    let A := W.comap (Λ U).field.val.toRingHom
    have hA : IsNontrivialValuation A :=
      absolutePlace_comap_nontrivial W hWabs (Λ U)
    simpa [absolutePlaceAtLevel, centerFinitePlace, A] using
      ((numberField_valuations A hA).choose_spec.2 (x U).1
        (hWlevels U)).symm
  rw [absoluteDecompositionGroup_finiteImage W hWabs (Λ U), hplace]
  exact (x U).2.2.symm

/-- Orientation-free recovery at one odd prime. -/
theorem bare_reconstruction_at_prime
    (K : Type*) [Field K] [NumberField K] (p : OddPrime) :
    bareRecoveredAtPrime (Field.absoluteGaloisGroup K) p =
      absoluteDecompositionCollectionAway K p := by
  ext H
  constructor
  · intro hH
    obtain ⟨W, hW, rfl⟩ := bare_recovery_sound K p H hH
    exact ⟨W, hW, rfl⟩
  · rintro ⟨W, hW, rfl⟩
    exact bare_recovery_complete K p W hW

/-- Orientation-free recovery from the bare profinite group: the union over
odd primes is exactly the collection of all absolute finite-place
decomposition groups. -/
theorem bare_reconstruction
    (K : Type*) [Field K] [NumberField K] :
    bareRecovered (Field.absoluteGaloisGroup K) =
      absoluteDecompositionCollection K := by
  ext H
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨W, hW, rfl⟩ := bare_recovery_sound K p H hp
    exact ⟨W, hW.1, rfl⟩
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨v, hv⟩ := hW.2
    obtain ⟨p, hp⟩ := exists_oddPrime_ne (residueCharacteristic v)
    exact ⟨p, bare_recovery_complete K p W
      ⟨hW, v, hv, hp.symm⟩⟩

/-! ## The qualified generic form -/

/-- Remark `equivalent-forms(b)`, with its essential (D1) qualification.
For a **closed, non-procyclic** subgroup of the absolute Galois group of a
number field, filter cofinality of all passing levels is equivalent to saying
that the passing members of every cofinal system are cofinal.  No such
converse is asserted for an arbitrary profinite group or without (D1). -/
theorem passingLevels_cofinal_iff_generic_of_D1
    (K : Type*) [Field K] [NumberField K] (p : OddPrime)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (hD1 : ¬IsProcyclic H) :
    IsCofinalOpenNormalSet (passingLevels p H) ↔
      ∀ S : Set (OpenNormalSubgroup (Field.absoluteGaloisGroup K)),
        IsCofinalOpenNormalSystem S →
          IsCofinalOpenNormalSet
            {U | U ∈ S ∧ IsPassingLevel p H U} := by
  constructor
  · intro hcofinal S hS
    obtain ⟨W, hW, hHW⟩ := bare_recovery_sound K p H
      ⟨hclosed, hD1, hcofinal⟩
    intro V hV
    have hopen : IsOpen ((V : Set (Field.absoluteGaloisGroup K)) ∩
        (cyclotomicKernel K (p : ℕ) :
          Set (Field.absoluteGaloisGroup K))) :=
      hV.inter (cyclotomicKernel_isOpen K p)
    obtain ⟨U, hUS, hU⟩ := hS.2.2
      (V ⊓ cyclotomicKernel K (p : ℕ)) hopen
    have hmarked : IsMarkedLevel K p U :=
      hU.trans inf_le_right
    refine ⟨U, ⟨hUS, ?_⟩, hU.trans inf_le_left⟩
    change openNormalQuotientImage U H ∈ bareCrit U p
    rw [hHW, bareCrit_marked_correct K U p hmarked]
    exact ⟨W, hW, rfl⟩
  · intro hgeneric V hV
    have h := hgeneric
      {U : OpenNormalSubgroup (Field.absoluteGaloisGroup K) |
        IsMarkedLevel K p U} (markedLevels_cofinal K p)
    obtain ⟨U, hU, hUV⟩ := h V hV
    exact ⟨U, hU.2, hUV⟩

/-! ## Henselian decomposition fields and distinctness -/

/-- Henselianity expressed as unique prolongation to every algebraic
intermediate extension inside a fixed algebraic closure. -/
def IsHenselianValuationIn
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring F) : Prop :=
  ∀ E : IntermediateField F Ω,
    ∃! B : ValuationSubring E,
      B.comap (algebraMap F E) = A

/-- Unique prolongation inside a fixed algebraic closure is invariant under
changing the base field by an equivalence compatible with its embedding. -/
private theorem isHenselianValuationIn_equiv
    {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
    [Algebra F Ω] [Algebra F' Ω]
    (e : F ≃+* F')
    (he : ∀ x : F,
      algebraMap F' Ω (e x) = algebraMap F Ω x)
    (A : ValuationSubring F)
    (hA : IsHenselianValuationIn F Ω A) :
    IsHenselianValuationIn F' Ω
      (A.comap e.symm.toRingHom) := by
  intro E'
  let E : IntermediateField F Ω :=
    { E'.toSubfield with
      algebraMap_mem' := fun x => by
        rw [← he x]
        exact E'.algebraMap_mem (e x) }
  have hEE : E.toSubring = E'.toSubring := by
    ext x
    rfl
  let eE : E ≃+* E' := RingEquiv.subringCongr hEE
  have heE (x : F) :
      eE (algebraMap F E x) = algebraMap F' E' (e x) := by
    apply Subtype.ext
    exact (he x).symm
  obtain ⟨B, hB, hBuniq⟩ := hA E
  let B' : ValuationSubring E' := B.comap eE.symm.toRingHom
  have hB' : B'.comap (algebraMap F' E') =
      A.comap e.symm.toRingHom := by
    apply ValuationSubring.ext
    intro x
    change eE.symm (algebraMap F' E' x) ∈ B ↔ e.symm x ∈ A
    have hinv : eE.symm (algebraMap F' E' x) =
        algebraMap F E (e.symm x) := by
      apply eE.injective
      rw [eE.apply_symm_apply, heE, e.apply_symm_apply]
    rw [hinv]
    exact ValuationSubring.ext_iff.mp hB (e.symm x)
  refine ⟨B', hB', ?_⟩
  intro C' hC'
  let C : ValuationSubring E := C'.comap eE.toRingHom
  have hC : C.comap (algebraMap F E) = A := by
    apply ValuationSubring.ext
    intro x
    change eE (algebraMap F E x) ∈ C' ↔ x ∈ A
    rw [heE]
    simpa using ValuationSubring.ext_iff.mp hC' (e x)
  have hCB : C = B := hBuniq C hC
  apply ValuationSubring.ext
  intro x
  have hx := ValuationSubring.ext_iff.mp hCB (eE.symm x)
  simpa [B', C] using hx

/-- Independence of two valuations: their only common coarsening is the
trivial valuation.  Inclusion of valuation subrings is the coarsening
order. -/
def IndependentValuationSubrings {F : Type*} [Field F]
    (A B : ValuationSubring F) : Prop :=
  ∀ C : ValuationSubring F, A ≤ C → B ≤ C → C = ⊤

/-- Rank one in the exact form needed for the independence bridge: a
nontrivial valuation has no proper nontrivial coarsening. -/
def IsRankOneValuationSubring {F : Type*} [Field F]
    (A : ValuationSubring F) : Prop :=
  A ≠ ⊤ ∧
    ∀ C : ValuationSubring F, A ≤ C → C = A ∨ C = ⊤

/-- Inequivalent nontrivial rank-one valuations are independent. -/
theorem independent_of_rankOne_of_ne {F : Type*} [Field F]
    {A B : ValuationSubring F}
    (hA : IsRankOneValuationSubring A)
    (hB : IsRankOneValuationSubring B) (hne : A ≠ B) :
    IndependentValuationSubrings A B := by
  intro C hAC hBC
  rcases hA.2 C hAC with hCA | hCtop
  · subst C
    rcases hB.2 A hBC with hAB | hAtop
    · exact (hne hAB).elim
    · exact hAtop
  · exact hCtop

/-- The decomposition field fixed by an absolute decomposition group. -/
def decompositionField
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField
    (show Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) from
      absoluteDecompositionGroup K W)

/-- The decomposition group bundled with its Krull-closedness. -/
def decompositionGroupClosedSubgroup
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) :
    ClosedSubgroup (Field.absoluteGaloisGroup K) :=
  ⟨absoluteDecompositionGroup K W,
    absoluteDecompositionGroup_isClosed K W⟩

/-- The group fixing the decomposition field is exactly the decomposition
group, rather than merely its closure. -/
theorem decompositionField_fixingSubgroup
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) :
    (decompositionField K W).fixingSubgroup =
      absoluteDecompositionGroup K W := by
  change (IntermediateField.fixedField
    (absoluteDecompositionGroup K W)).fixingSubgroup = _
  rw [show absoluteDecompositionGroup K W =
      (decompositionGroupClosedSubgroup K W).toSubgroup from rfl,
    InfiniteGalois.fixingSubgroup_fixedField]

/-- Restriction of the chosen absolute place supplies a prolongation at every
intermediate extension. -/
theorem decompositionField_restriction_prolongation
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (E : IntermediateField (decompositionField K W) (AlgebraicClosure K)) :
    (W.comap E.val.toRingHom).comap
        (algebraMap (decompositionField K W) E) =
      W.comap (decompositionField K W).val.toRingHom := by
  apply ValuationSubring.ext
  intro x
  rfl

/-- The group-theoretic core of decomposition-field Henselianity.  Once the
standard conjugacy theorem for prolongations is supplied, every conjugating
automorphism lies in the decomposition group and therefore fixes `W`. -/
theorem decompositionField_isHenselian_of_prolongation_conjugacy
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hconj : ∀ (E : IntermediateField (decompositionField K W)
        (AlgebraicClosure K)) (B : ValuationSubring E),
      B.comap (algebraMap (decompositionField K W) E) =
          W.comap (decompositionField K W).val.toRingHom →
        ∃ σ : (decompositionField K W).fixingSubgroup,
          B = (σ.1 • W).comap E.val.toRingHom) :
    IsHenselianValuationIn (decompositionField K W) (AlgebraicClosure K)
      (W.comap (decompositionField K W).val.toRingHom) := by
  intro E
  refine ⟨W.comap E.val.toRingHom,
    decompositionField_restriction_prolongation K W E, ?_⟩
  intro B hB
  obtain ⟨σ, hσ⟩ := hconj E B hB
  rw [hσ]
  have hmem : σ.1 ∈ absoluteDecompositionGroup K W := by
    rw [← decompositionField_fixingSubgroup K W]
    exact σ.property
  have hfix : σ.1 • W = W := MulAction.mem_stabilizer_iff.mp hmem
  rw [hfix]

/-- Henselianity of the decomposition field: the restricted place has a
unique prolongation to every algebraic extension inside the fixed algebraic
closure. -/
theorem decompositionField_isHenselian
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) :
    IsHenselianValuationIn (decompositionField K W) (AlgebraicClosure K)
      (W.comap (decompositionField K W).val.toRingHom) := by
  apply decompositionField_isHenselian_of_prolongation_conjugacy K W
  intro E B hB
  obtain ⟨A, hAE⟩ := exists_valuationSubring_extension E.val.toRingHom B
  let Z := decompositionField K W
  have hAW : A.comap Z.val.toRingHom = W.comap Z.val.toRingHom := by
    apply ValuationSubring.ext
    intro z
    have h1 := ValuationSubring.ext_iff.mp hAE (algebraMap Z E z)
    change algebraMap Z (AlgebraicClosure K) z ∈ A ↔
      algebraMap Z E z ∈ B at h1
    have h2 := ValuationSubring.ext_iff.mp hB z
    change algebraMap Z E z ∈ B ↔
      algebraMap Z (AlgebraicClosure K) z ∈ W at h2
    exact h1.trans h2
  obtain ⟨_, v, hv⟩ := hW
  have hWbase : W.comap (algebraMap K (AlgebraicClosure K)) ≠ ⊤ := by
    rw [hv]
    exact primeValuationSubring_ne_top v
  have hAbaseEq : A.comap (algebraMap K (AlgebraicClosure K)) =
      W.comap (algebraMap K (AlgebraicClosure K)) := by
    apply ValuationSubring.ext
    intro x
    exact ValuationSubring.ext_iff.mp hAW (algebraMap K Z x)
  have hAbase : A.comap (algebraMap K (AlgebraicClosure K)) ≠ ⊤ := by
    rwa [hAbaseEq]
  obtain ⟨σ, hσ⟩ := exists_smul_of_valuationSubring_comap_eq K Z W A
    hWbase hAbase hAW.symm
  let τ : Z.fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv Z).symm σ
  refine ⟨τ, ?_⟩
  have hτ : τ.1 • W = σ • W := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change τ.1⁻¹ x ∈ W ↔ σ⁻¹ x ∈ W
    rw [show τ.1⁻¹ x = σ⁻¹ x by rfl]
  have hτA : τ.1 • W = A := hτ.trans hσ.symm
  exact hAE.symm.trans (congrArg (fun V : ValuationSubring
    (AlgebraicClosure K) => V.comap E.val.toRingHom) hτA.symm)

/-- Restrictions of absolute finite places to their decomposition fields are
nontrivial rank-one valuations.  This is the rank-one input that turns
inequivalence into the independence hypothesis of F. K. Schmidt's theorem. -/
theorem decompositionField_place_rankOne
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) :
    IsRankOneValuationSubring
      (W.comap (decompositionField K W).val.toRingHom) := by
  let Z := decompositionField K W
  let A := W.comap Z.val.toRingHom
  have hAbaseEq : A.comap (algebraMap K Z) =
      W.comap (algebraMap K (AlgebraicClosure K)) := by
    apply ValuationSubring.ext
    intro x
    rfl
  obtain ⟨_, v, hv⟩ := hW
  have hAbase : A.comap (algebraMap K Z) ≠ ⊤ := by
    rw [hAbaseEq, hv]
    exact primeValuationSubring_ne_top v
  refine ⟨?_, ?_⟩
  · intro htop
    apply hAbase
    change A = ⊤ at htop
    rw [htop]
    rfl
  · intro C hAC
    exact valuationSubring_eq_or_eq_top_of_algebraic K A C hAbase hAC

/-- The imported real-valued rank-one bridge, expressed in this module's
coarsening predicate. -/
theorem fkSchmidt_rank_one_bridge_realValuation
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (Z : IntermediateField ℚ Ω)
    (v : FKSchmidt.RealValuation Z)
    (hv : FKSchmidt.realValuationSubring v ≠ ⊤) :
    IsRankOneValuationSubring (FKSchmidt.realValuationSubring v) := by
  simpa only [IsRankOneValuationSubring,
    FKSchmidt.IsRankOneValuationSubring] using
      FKSchmidt.rank_one_bridge Z v hv

/-- The fully proved imported F. K. Schmidt contradiction in its actual
normalized real-valuation interface. -/
theorem fkSchmidt_consumed_realValuations
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω)
    (hG : Z.fixingSubgroup ≠ ⊥)
    (v₁ v₂ : FKSchmidt.RealValuation Z)
    (h₁ : FKSchmidt.realValuationSubring v₁ ≠ ⊤)
    (h₂ : FKSchmidt.realValuationSubring v₂ ≠ ⊤)
    (hne : FKSchmidt.realValuationSubring v₁ ≠
      FKSchmidt.realValuationSubring v₂)
    (hhens₁ : FKSchmidt.IsHenselian v₁)
    (hhens₂ : FKSchmidt.IsHenselian v₂) : False :=
  FKSchmidt.consumed Z hG v₁ v₂ h₁ h₂ hne hhens₁ hhens₂

open scoped IntermediateField

private theorem henselianBridge_valueGroup_mulArchimedean
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) : MulArchimedean A.ValueGroup := by
  constructor
  intro x y hy
  obtain ⟨a, rfl⟩ := A.valuation_surjective x
  obtain ⟨b, rfl⟩ := A.valuation_surjective y
  let L : IntermediateField ℚ F := ℚ⟮a, b⟯
  letI : Algebra ℚ L := L.algebra'
  let aL : L := IntermediateField.AdjoinPair.gen₁ ℚ a b
  let bL : L := IntermediateField.AdjoinPair.gen₂ ℚ a b
  letI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin_pair
      (K := ℚ) (L := F)
      (Algebra.IsIntegral.isIntegral a) (Algebra.IsIntegral.isIntegral b)
  letI : NumberField L := NumberField.of_module_finite ℚ L
  let C : ValuationSubring L := A.comap L.val.toRingHom
  have hb_not : b ∉ A := by
    rw [← A.valuation_le_one_iff]
    exact not_le.mpr hy
  have hC : C ≠ ⊤ := by
    intro htop
    apply hb_not
    have hbL : bL ∈ C := by rw [htop]; exact ValuationSubring.mem_top _
    change L.val bL ∈ A at hbL
    have hbval : L.val bL = b := rfl
    rwa [hbval] at hbL
  obtain ⟨p, hp, _⟩ := numberField_valuations C hC
  let w := p.valuation L
  have hvalring :
      (A.valuation.comap L.val.toRingHom).valuationSubring = C := by
    apply ValuationSubring.ext
    intro z
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      A.valuation_le_one_iff]
    rfl
  have hwvalring : w.valuationSubring = C := by
    rw [hp, primeValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hequiv : (A.valuation.comap L.val.toRingHom).IsEquiv w :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2
      (hvalring.trans hwvalring.symm)
  have hyL : ¬ (A.valuation.comap L.val.toRingHom) bL ≤
      (A.valuation.comap L.val.toRingHom) 1 := by
    change ¬ A.valuation (L.val bL) ≤ A.valuation (L.val 1)
    rw [show L.val bL = b by rfl, map_one]
    exact not_le.mpr hy
  have hyw : 1 < w bL := by
    rw [show 1 = w 1 from (map_one w).symm, ← not_le]
    exact (hequiv bL 1).not.mp hyL
  letI : w.IsNontrivial := by
    rw [Valuation.IsNontrivial_iff_exists_one_lt]
    exact ⟨bL, hyw⟩
  letI : w.RankOne := by
    dsimp only [w]
    infer_instance
  have harch : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) :=
    w.nonempty_rankOne_iff_mulArchimedean.mp ⟨inferInstance⟩
  letI := harch
  have hywr : 1 < w.restrict bL := by
    rw [show 1 = w.restrict 1 from (map_one w.restrict).symm,
      Valuation.restrict_lt_iff]
    simpa only [map_one] using hyw
  obtain ⟨n, hn⟩ := MulArchimedean.arch (w.restrict aL) hywr
  have hn' : w aL ≤ w (bL ^ n) := by
    rw [← Valuation.restrict_le_iff]
    simpa using hn
  have hn'' := (hequiv aL (bL ^ n)).mpr hn'
  refine ⟨n, ?_⟩
  change A.valuation a ≤ A.valuation b ^ n
  change A.valuation (L.val.toRingHom aL) ≤
    A.valuation (L.val.toRingHom (bL ^ n)) at hn''
  have haL : L.val.toRingHom aL = a := rfl
  have hbL : L.val.toRingHom bL = b := rfl
  simpa only [haL, map_pow, hbL] using hn''


private noncomputable def henselianBridge_valueEmbeddingData
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) :
    {e : Additive A.ValueGroupˣ →+o ℝ //
      Function.Injective e ∧
        e |Additive.ofMul (Units.mk0 (A.valuation π)
          ((A.valuation.ne_zero_iff).2 hπ0))| = 1} := by
  classical
  letI : MulArchimedean A.ValueGroup := henselianBridge_valueGroup_mulArchimedean A
  letI : MulArchimedean A.ValueGroupˣ :=
    Units.mulArchimedean_iff.mpr inferInstance
  letI : Archimedean (Additive A.ValueGroupˣ) := inferInstance
  let πv : Additive A.ValueGroupˣ :=
    Additive.ofMul (Units.mk0 (A.valuation π)
      ((A.valuation.ne_zero_iff).2 hπ0))
  letI : One (Additive A.ValueGroupˣ) := ⟨|πv|⟩
  letI : ZeroLEOneClass (Additive A.ValueGroupˣ) := ⟨abs_nonneg πv⟩
  have hπv : πv ≠ 0 := by
    intro h
    apply hπ
    apply_fun Additive.toMul at h
    simpa [πv, Units.ext_iff] using h
  letI : NeZero (1 : Additive A.ValueGroupˣ) :=
    ⟨abs_ne_zero.mpr hπv⟩
  refine ⟨Archimedean.embedReal (Additive A.ValueGroupˣ),
    Archimedean.embedReal_injective _, ?_⟩
  exact Archimedean.embedReal_one

private noncomputable def henselianBridge_valueEmbedding
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) : Additive A.ValueGroupˣ →+o ℝ :=
  henselianBridge_valueEmbeddingData A π hπ0 hπ

private theorem henselianBridge_valueEmbedding_injective
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) :
    Function.Injective (henselianBridge_valueEmbedding A π hπ0 hπ) :=
  (henselianBridge_valueEmbeddingData A π hπ0 hπ).property.1

private theorem henselianBridge_valueEmbedding_abs_anchor
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) :
    henselianBridge_valueEmbedding A π hπ0 hπ
      |Additive.ofMul (Units.mk0 (A.valuation π)
        ((A.valuation.ne_zero_iff).2 hπ0))| = 1 :=
  (henselianBridge_valueEmbeddingData A π hπ0 hπ).property.2

private noncomputable def henselianBridge_normalizedRealValuation
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) : FKSchmidt.RealValuation F := by
  classical
  let e := henselianBridge_valueEmbedding A π hπ0 hπ
  let f : F → WithTop ℝ := fun x =>
    if hx : x = 0 then ⊤ else
      ((-e (Additive.ofMul (Units.mk0 (A.valuation x)
        ((A.valuation.ne_zero_iff).2 hx))) : ℝ) : WithTop ℝ)
  refine AddValuation.of f ?_ ?_ ?_ ?_
  · simp [f]
  · simp [f, e]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp [f]
    by_cases hy : y = 0
    · subst y
      simp [f]
    by_cases hxy : x + y = 0
    · simp [f, hx, hy, hxy]
    simp only [f, dif_neg hx, dif_neg hy, dif_neg hxy,
      WithTop.coe_min, WithTop.coe_le_coe]
    rcases A.valuation.map_add' x y with h | h
    · apply (min_le_left _ _).trans
      have hm : e (Additive.ofMul (Units.mk0 (A.valuation (x + y))
          ((A.valuation.ne_zero_iff).2 hxy))) ≤
          e (Additive.ofMul (Units.mk0 (A.valuation x)
            ((A.valuation.ne_zero_iff).2 hx))) := by
        apply OrderHomClass.mono e
        change Units.mk0 (A.valuation (x + y))
          ((A.valuation.ne_zero_iff).2 hxy) ≤
          Units.mk0 (A.valuation x) ((A.valuation.ne_zero_iff).2 hx)
        rw [← Units.val_le_val]
        simpa only [Units.val_mk0] using h
      exact_mod_cast neg_le_neg hm
    · apply (min_le_right _ _).trans
      have hm : e (Additive.ofMul (Units.mk0 (A.valuation (x + y))
          ((A.valuation.ne_zero_iff).2 hxy))) ≤
          e (Additive.ofMul (Units.mk0 (A.valuation y)
            ((A.valuation.ne_zero_iff).2 hy))) := by
        apply OrderHomClass.mono e
        change Units.mk0 (A.valuation (x + y))
          ((A.valuation.ne_zero_iff).2 hxy) ≤
          Units.mk0 (A.valuation y) ((A.valuation.ne_zero_iff).2 hy)
        rw [← Units.val_le_val]
        simpa only [Units.val_mk0] using h
      exact_mod_cast neg_le_neg hm
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp [f]
    by_cases hy : y = 0
    · subst y
      simp [f]
    have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [f, dif_neg hx, dif_neg hy, dif_neg hxy0,
      ← WithTop.coe_add, WithTop.coe_eq_coe]
    have huv :
        Additive.ofMul (Units.mk0 (A.valuation (x * y))
          ((A.valuation.ne_zero_iff).2 hxy0)) =
        Additive.ofMul (Units.mk0 (A.valuation x)
          ((A.valuation.ne_zero_iff).2 hx)) +
        Additive.ofMul (Units.mk0 (A.valuation y)
          ((A.valuation.ne_zero_iff).2 hy)) := by
      apply Additive.toMul.injective
      change Units.mk0 (A.valuation (x * y))
          ((A.valuation.ne_zero_iff).2 hxy0) =
        Units.mk0 (A.valuation x) ((A.valuation.ne_zero_iff).2 hx) *
          Units.mk0 (A.valuation y) ((A.valuation.ne_zero_iff).2 hy)
      simp only [A.valuation.map_mul, Units.mk0_mul]
    rw [huv, map_add]
    abel


private theorem henselianBridge_normalizedRealValuation_subring
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) :
    FKSchmidt.realValuationSubring
      (henselianBridge_normalizedRealValuation A π hπ0 hπ) = A := by
  classical
  apply ValuationSubring.ext
  intro x
  rw [FKSchmidt.mem_realValuationSubring]
  by_cases hx : x = 0
  · subst x
    simp
  rw [← A.valuation_le_one_iff]
  let e := henselianBridge_valueEmbedding A π hπ0 hπ
  have he : StrictMono e :=
    (OrderHomClass.mono e).strictMono_of_injective
      (henselianBridge_valueEmbedding_injective A π hπ0 hπ)
  have hunit : A.valuation x ≤ 1 ↔
      Additive.ofMul (Units.mk0 (A.valuation x)
        ((A.valuation.ne_zero_iff).2 hx)) ≤ 0 := by
    change A.valuation x ≤ 1 ↔
      Units.mk0 (A.valuation x) ((A.valuation.ne_zero_iff).2 hx) ≤ 1
    rw [← Units.val_le_val]
    simp
  rw [hunit, ← he.le_iff_le]
  rw [show (henselianBridge_normalizedRealValuation A π hπ0 hπ) x =
      ((-e (Additive.ofMul (Units.mk0 (A.valuation x)
        ((A.valuation.ne_zero_iff).2 hx))) : ℝ) : WithTop ℝ) by
    simp [henselianBridge_normalizedRealValuation, e, hx]]
  change (0 : WithTop ℝ) ≤
      ((-e (Additive.ofMul (Units.mk0 (A.valuation x)
        ((A.valuation.ne_zero_iff).2 hx))) : ℝ) : WithTop ℝ) ↔
    e (Additive.ofMul (Units.mk0 (A.valuation x)
      ((A.valuation.ne_zero_iff).2 hx))) ≤ e 0
  norm_cast
  simp

private theorem henselianBridge_normalizedRealValuation_anchor_of_lt
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) (hπlt : A.valuation π < 1) :
    henselianBridge_normalizedRealValuation A π hπ0 hπ π = (1 : WithTop ℝ) := by
  let e := henselianBridge_valueEmbedding A π hπ0 hπ
  let πv : Additive A.ValueGroupˣ :=
    Additive.ofMul (Units.mk0 (A.valuation π)
      ((A.valuation.ne_zero_iff).2 hπ0))
  have hπvlt : πv < 0 := by
    change Units.mk0 (A.valuation π) ((A.valuation.ne_zero_iff).2 hπ0) < 1
    rw [← Units.val_lt_val]
    simpa using hπlt
  have habs := henselianBridge_valueEmbedding_abs_anchor A π hπ0 hπ
  rw [abs_of_neg hπvlt, map_neg] at habs
  rw [show henselianBridge_normalizedRealValuation A π hπ0 hπ π =
      ((-e πv : ℝ) : WithTop ℝ) by
    simp [henselianBridge_normalizedRealValuation, e, πv, hπ0]]
  rw [habs]
  norm_num

private theorem henselianBridge_normalizedRealValuation_anchor_of_gt
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) (hπgt : 1 < A.valuation π) :
    henselianBridge_normalizedRealValuation A π hπ0 hπ π = ((-1 : ℝ) : WithTop ℝ) := by
  let e := henselianBridge_valueEmbedding A π hπ0 hπ
  let πv : Additive A.ValueGroupˣ :=
    Additive.ofMul (Units.mk0 (A.valuation π)
      ((A.valuation.ne_zero_iff).2 hπ0))
  have hπvgt : 0 < πv := by
    change (1 : A.ValueGroupˣ) <
      Units.mk0 (A.valuation π) ((A.valuation.ne_zero_iff).2 hπ0)
    rw [← Units.val_lt_val]
    simpa using hπgt
  have habs := henselianBridge_valueEmbedding_abs_anchor A π hπ0 hπ
  rw [abs_of_pos hπvgt] at habs
  rw [show henselianBridge_normalizedRealValuation A π hπ0 hπ π =
      ((-e πv : ℝ) : WithTop ℝ) by
    simp [henselianBridge_normalizedRealValuation, e, πv, hπ0]]
  rw [habs]

private theorem henselianBridge_normalizedRealValuation_anchor_order_ne_zero
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (A : ValuationSubring F) (π : F) (hπ0 : π ≠ 0)
    (hπ : A.valuation π ≠ 1) :
    FKSchmidt.order (henselianBridge_normalizedRealValuation A π hπ0 hπ) π ≠ 0 := by
  rcases lt_or_gt_of_ne hπ with hlt | hgt
  · have hv := henselianBridge_normalizedRealValuation_anchor_of_lt A π hπ0 hπ hlt
    have hord : FKSchmidt.order (henselianBridge_normalizedRealValuation A π hπ0 hπ) π = 1 := by
      apply WithTop.coe_injective
      rw [FKSchmidt.coe_order_of_ne _ hπ0, hv]
      rfl
    rw [hord]
    norm_num
  · have hv := henselianBridge_normalizedRealValuation_anchor_of_gt A π hπ0 hπ hgt
    have hord : FKSchmidt.order (henselianBridge_normalizedRealValuation A π hπ0 hπ) π = -1 := by
      apply WithTop.coe_injective
      rw [FKSchmidt.coe_order_of_ne _ hπ0, hv]
    rw [hord]
    norm_num

private theorem henselianBridge_order_zpow_of_ne {F : Type*} [Field F]
    (v : FKSchmidt.RealValuation F) {x : F} (hx : x ≠ 0) (m : ℤ) :
    FKSchmidt.order v (x ^ m) = (m : ℝ) * FKSchmidt.order v x := by
  cases m with
  | ofNat n => simpa using FKSchmidt.order_pow_of_ne v hx n
  | negSucc n =>
      rw [zpow_negSucc,
        FKSchmidt.order_inv_of_ne v (pow_ne_zero _ hx),
        FKSchmidt.order_pow_of_ne v hx]
      push_cast
      ring

private theorem henselianBridge_order_le_order_iff_of_subring_eq
    {F : Type*} [Field F] (v w : FKSchmidt.RealValuation F)
    (h : FKSchmidt.realValuationSubring v =
      FKSchmidt.realValuationSubring w)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    FKSchmidt.order v x ≤ FKSchmidt.order v y ↔
      FKSchmidt.order w x ≤ FKSchmidt.order w y := by
  have hequiv : (AddValuation.toValuation v).IsEquiv
      (AddValuation.toValuation w) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 h
  have hle := hequiv y x
  change v x ≤ v y ↔ w x ≤ w y at hle
  rw [← FKSchmidt.coe_order_of_ne v hx,
    ← FKSchmidt.coe_order_of_ne v hy,
    ← FKSchmidt.coe_order_of_ne w hx,
    ← FKSchmidt.coe_order_of_ne w hy] at hle
  exact_mod_cast hle

private theorem henselianBridge_not_order_lt_of_subring_eq_of_anchor
    {F : Type*} [Field F] (v w : FKSchmidt.RealValuation F)
    (π : F) (hπ0 : π ≠ 0)
    (hring : FKSchmidt.realValuationSubring v =
      FKSchmidt.realValuationSubring w)
    (hπ : v π = w π) (hπorder : FKSchmidt.order v π ≠ 0)
    {x : F} (hx : x ≠ 0) :
    ¬ FKSchmidt.order v x < FKSchmidt.order w x := by
  intro hab
  have hπord : FKSchmidt.order v π = FKSchmidt.order w π := by
    apply WithTop.coe_injective
    rw [FKSchmidt.coe_order_of_ne v hπ0,
      FKSchmidt.coe_order_of_ne w hπ0, hπ]
  let a := FKSchmidt.order v x
  let b := FKSchmidt.order w x
  let c := FKSchmidt.order v π
  have hc : c ≠ 0 := hπorder
  obtain ⟨q, hqa, hqb⟩ : ∃ q : ℚ,
      a < (q : ℝ) * c ∧ (q : ℝ) * c < b := by
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · have hdiv : b / c < a / c := by
        apply (div_lt_iff_of_neg hcneg).2
        rw [div_mul_cancel₀ a hc]
        exact hab
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hdiv
      exact ⟨q, (lt_div_iff_of_neg hcneg).1 hq2,
        (div_lt_iff_of_neg hcneg).1 hq1⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        ((div_lt_div_iff_of_pos_right hcpos).2 hab)
      exact ⟨q, (div_lt_iff₀ hcpos).1 hq1,
        (lt_div_iff₀ hcpos).1 hq2⟩
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hqden : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have hleft : (q.den : ℝ) * a < (q.num : ℝ) * c := by
    calc
      (q.den : ℝ) * a < (q.den : ℝ) * ((q : ℝ) * c) :=
        mul_lt_mul_of_pos_left hqa hden
      _ = (q.num : ℝ) * c := by rw [← mul_assoc, mul_comm (q.den : ℝ), hqden]
  have hright : (q.num : ℝ) * c < (q.den : ℝ) * b := by
    calc
      (q.num : ℝ) * c = (q.den : ℝ) * ((q : ℝ) * c) := by
        rw [← mul_assoc, mul_comm (q.den : ℝ), hqden]
      _ < (q.den : ℝ) * b := mul_lt_mul_of_pos_left hqb hden
  have htransfer := (henselianBridge_order_le_order_iff_of_subring_eq v w hring
    (pow_ne_zero _ hx) (zpow_ne_zero _ hπ0)).mp (show
      FKSchmidt.order v (x ^ q.den) ≤
        FKSchmidt.order v (π ^ q.num) by
      rw [FKSchmidt.order_pow_of_ne v hx,
        henselianBridge_order_zpow_of_ne v hπ0]
      exact hleft.le)
  rw [FKSchmidt.order_pow_of_ne w hx,
    henselianBridge_order_zpow_of_ne w hπ0, ← hπord] at htransfer
  exact (not_lt_of_ge htransfer) hright

private theorem henselianBridge_realValuation_eq_of_subring_eq_of_anchor
    {F : Type*} [Field F] (v w : FKSchmidt.RealValuation F)
    (π : F) (hπ0 : π ≠ 0)
    (hring : FKSchmidt.realValuationSubring v =
      FKSchmidt.realValuationSubring w)
    (hπ : v π = w π) (hπorder : FKSchmidt.order v π ≠ 0) :
    v = w := by
  have hπord : FKSchmidt.order v π = FKSchmidt.order w π := by
    apply WithTop.coe_injective
    rw [FKSchmidt.coe_order_of_ne v hπ0,
      FKSchmidt.coe_order_of_ne w hπ0, hπ]
  have hπorder' : FKSchmidt.order w π ≠ 0 := by
    rwa [← hπord]
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  have horder : FKSchmidt.order v x = FKSchmidt.order w x :=
    le_antisymm
      (le_of_not_gt (henselianBridge_not_order_lt_of_subring_eq_of_anchor
        w v π hπ0 hring.symm hπ.symm hπorder' hx))
      (le_of_not_gt (henselianBridge_not_order_lt_of_subring_eq_of_anchor
        v w π hπ0 hring hπ hπorder hx))
  rw [← FKSchmidt.coe_order_of_ne v hx,
    ← FKSchmidt.coe_order_of_ne w hx, horder]

private theorem henselianBridge_normalizedRealValuation_comap
    {F E : Type*} [Field F] [Field E]
    [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E]
    (f : F →+* E) (A : ValuationSubring F) (B : ValuationSubring E)
    (hBA : B.comap f = A) (π : F) (hπ0 : π ≠ 0)
    (hπA : A.valuation π ≠ 1) (hπB : B.valuation (f π) ≠ 1) :
    (henselianBridge_normalizedRealValuation B (f π) ((map_ne_zero f).2 hπ0) hπB).comap f =
      henselianBridge_normalizedRealValuation A π hπ0 hπA := by
  let vA := henselianBridge_normalizedRealValuation A π hπ0 hπA
  let vB := henselianBridge_normalizedRealValuation B (f π) ((map_ne_zero f).2 hπ0) hπB
  have hsubA : FKSchmidt.realValuationSubring vA = A :=
    henselianBridge_normalizedRealValuation_subring A π hπ0 hπA
  have hsubB : FKSchmidt.realValuationSubring vB = B :=
    henselianBridge_normalizedRealValuation_subring B (f π) ((map_ne_zero f).2 hπ0) hπB
  have hsubComap : FKSchmidt.realValuationSubring (vB.comap f) = A := by
    apply ValuationSubring.ext
    intro x
    rw [FKSchmidt.mem_realValuationSubring]
    change 0 ≤ vB (f x) ↔ x ∈ A
    rw [← FKSchmidt.mem_realValuationSubring, hsubB]
    exact ValuationSubring.ext_iff.mp hBA x
  have hcanComap : (B.valuation.comap f).valuationSubring = A := by
    apply ValuationSubring.ext
    intro x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      B.valuation_le_one_iff]
    exact ValuationSubring.ext_iff.mp hBA x
  have hequiv : A.valuation.IsEquiv (B.valuation.comap f) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 (by
      rw [A.valuationSubring_valuation, hcanComap])
  have hanchor : vA π = (vB.comap f) π ∧ FKSchmidt.order vA π ≠ 0 := by
    rcases lt_or_gt_of_ne hπA with hπAlt | hπAgt
    · have ht := (hequiv 1 π).not.mp (not_le.mpr hπAlt)
      have hπBlt : B.valuation (f π) < 1 := by
        rw [← not_le]
        simpa only [Valuation.comap_apply, map_one] using ht
      have hvA := henselianBridge_normalizedRealValuation_anchor_of_lt
        A π hπ0 hπA hπAlt
      have hvB := henselianBridge_normalizedRealValuation_anchor_of_lt
        B (f π) ((map_ne_zero f).2 hπ0) hπB hπBlt
      constructor
      · change vA π = vB (f π)
        exact hvA.trans hvB.symm
      · have hord : FKSchmidt.order vA π = 1 := by
          apply WithTop.coe_injective
          rw [FKSchmidt.coe_order_of_ne vA hπ0, hvA]
          rfl
        rw [hord]
        norm_num
    · have ht := (hequiv π 1).not.mp (not_le.mpr hπAgt)
      have hπBgt : 1 < B.valuation (f π) := by
        rw [← not_le]
        simpa only [Valuation.comap_apply, map_one] using ht
      have hvA := henselianBridge_normalizedRealValuation_anchor_of_gt
        A π hπ0 hπA hπAgt
      have hvB := henselianBridge_normalizedRealValuation_anchor_of_gt
        B (f π) ((map_ne_zero f).2 hπ0) hπB hπBgt
      constructor
      · change vA π = vB (f π)
        exact hvA.trans hvB.symm
      · have hord : FKSchmidt.order vA π = -1 := by
          apply WithTop.coe_injective
          rw [FKSchmidt.coe_order_of_ne vA hπ0, hvA]
        rw [hord]
        norm_num
  exact (henselianBridge_realValuation_eq_of_subring_eq_of_anchor
    vA (vB.comap f) π hπ0 (hsubA.trans hsubComap.symm)
    hanchor.1 hanchor.2).symm

private theorem henselianBridge_unique_valuationSubring_extension
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω) (A : ValuationSubring Z)
    (hA : IsHenselianValuationIn Z Ω A)
    (E : Type*) [Field E] [Algebra Z E]
    (hE : Algebra.IsAlgebraic Z E) :
    ∃! B : ValuationSubring E,
      B.comap (algebraMap Z E) = A := by
  classical
  obtain ⟨B, hB⟩ :=
    exists_valuationSubring_extension (algebraMap Z E) A
  refine ⟨B, hB, ?_⟩
  intro C hC
  let ι : E →ₐ[Z] Ω := IsAlgClosed.lift
  let I : IntermediateField Z Ω := ι.fieldRange
  let e : E ≃ₐ[Z] I := AlgEquiv.ofInjectiveField ι
  let BI : ValuationSubring I := B.comap e.symm.toRingHom
  let CI : ValuationSubring I := C.comap e.symm.toRingHom
  have he (z : Z) : e (algebraMap Z E z) = algebraMap Z I z :=
    e.commutes z
  have hBI : BI.comap (algebraMap Z I) = A := by
    apply ValuationSubring.ext
    intro z
    change e.symm (algebraMap Z I z) ∈ B ↔ z ∈ A
    rw [show e.symm (algebraMap Z I z) = algebraMap Z E z by
      apply e.injective
      rw [e.apply_symm_apply, he]]
    exact ValuationSubring.ext_iff.mp hB z
  have hCI : CI.comap (algebraMap Z I) = A := by
    apply ValuationSubring.ext
    intro z
    change e.symm (algebraMap Z I z) ∈ C ↔ z ∈ A
    rw [show e.symm (algebraMap Z I z) = algebraMap Z E z by
      apply e.injective
      rw [e.apply_symm_apply, he]]
    exact ValuationSubring.ext_iff.mp hC z
  have hIC : BI = CI := (hA I).unique hBI hCI
  apply ValuationSubring.ext
  intro x
  have hx := ValuationSubring.ext_iff.mp hIC (e x)
  simpa [BI, CI] using hx.symm

/-- Residual representation bridge: a nontrivial Henselian valuation ring on
an algebraic extension of `ℚ` admits a normalized real-valued presentation.
This is the sole fallback obligation in the arithmetic tail. -/
private theorem exists_henselian_realValuation_of_subring
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω) (A : ValuationSubring Z)
    (hA_nontrivial : A ≠ ⊤)
    (hA_henselian : IsHenselianValuationIn Z Ω A) :
    ∃ v : FKSchmidt.RealValuation Z,
      FKSchmidt.realValuationSubring v = A ∧
        FKSchmidt.IsHenselian v := by
  classical
  let j : Z →ₐ[ℚ] Ω :=
    { toRingHom := Z.toSubfield.subtype
      commutes' := fun q => by norm_num }
  letI : Algebra.IsAlgebraic ℚ Z :=
    Algebra.IsAlgebraic.of_injective j j.injective
  have hnon : A.valuation.IsNontrivial :=
    not_not.mp ((not_congr A.eq_top_iff).mp hA_nontrivial)
  letI : A.valuation.IsNontrivial := hnon
  obtain ⟨π, hπval0, hπval1⟩ :=
    Valuation.IsNontrivial.exists_val_nontrivial (v := A.valuation)
  have hπ0 : π ≠ 0 := A.valuation.ne_zero_iff.mp hπval0
  let v := henselianBridge_normalizedRealValuation A π hπ0 hπval1
  have hvA : FKSchmidt.realValuationSubring v = A :=
    henselianBridge_normalizedRealValuation_subring A π hπ0 hπval1
  refine ⟨v, hvA, ?_⟩
  intro E _ _ hE
  letI : Algebra.IsAlgebraic Z E := hE
  letI : Algebra ℚ E :=
    ((algebraMap Z E).comp (algebraMap ℚ Z)).toAlgebra
  letI : IsScalarTower ℚ Z E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsAlgebraic ℚ E :=
    Algebra.IsAlgebraic.trans ℚ Z E
  obtain ⟨B, hB, hBuniq⟩ :=
    henselianBridge_unique_valuationSubring_extension Z A hA_henselian E hE
  have hcanComap :
      (B.valuation.comap (algebraMap Z E)).valuationSubring = A := by
    apply ValuationSubring.ext
    intro x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      B.valuation_le_one_iff]
    exact ValuationSubring.ext_iff.mp hB x
  have hequiv : A.valuation.IsEquiv
      (B.valuation.comap (algebraMap Z E)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 (by
      rw [A.valuationSubring_valuation, hcanComap])
  have hπB : B.valuation (algebraMap Z E π) ≠ 1 := by
    intro hp
    apply hπval1
    apply (hequiv.eq_one_iff_eq_one).mpr
    simpa only [Valuation.comap_apply] using hp
  let wB := henselianBridge_normalizedRealValuation B (algebraMap Z E π)
    ((map_ne_zero (algebraMap Z E)).2 hπ0) hπB
  have hwB : FKSchmidt.Extends (algebraMap Z E) v wB :=
    henselianBridge_normalizedRealValuation_comap (algebraMap Z E) A B hB π hπ0
      hπval1 hπB
  refine ⟨wB, hwB, ?_⟩
  intro w hw
  let C : ValuationSubring E := FKSchmidt.realValuationSubring w
  have hC : C.comap (algebraMap Z E) = A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_comap]
    change 0 ≤ w (algebraMap Z E x) ↔ x ∈ A
    have hx := DFunLike.congr_fun hw x
    change w (algebraMap Z E x) = v x at hx
    rw [hx, ← FKSchmidt.mem_realValuationSubring, hvA]
  have hCB : C = B := hBuniq C hC
  have hring : FKSchmidt.realValuationSubring w =
      FKSchmidt.realValuationSubring wB :=
    hCB.trans (henselianBridge_normalizedRealValuation_subring B
      (algebraMap Z E π) ((map_ne_zero (algebraMap Z E)).2 hπ0) hπB).symm
  have hwπ := DFunLike.congr_fun hw π
  change w (algebraMap Z E π) = v π at hwπ
  have hwBπ := DFunLike.congr_fun hwB π
  change wB (algebraMap Z E π) = v π at hwBπ
  have horder : FKSchmidt.order wB (algebraMap Z E π) ≠ 0 := by
    have heq : FKSchmidt.order wB (algebraMap Z E π) =
        FKSchmidt.order v π := by
      apply WithTop.coe_injective
      rw [FKSchmidt.coe_order_of_ne wB
          ((map_ne_zero (algebraMap Z E)).2 hπ0),
        FKSchmidt.coe_order_of_ne v hπ0, hwBπ]
    rw [heq]
    exact henselianBridge_normalizedRealValuation_anchor_order_ne_zero
      A π hπ0 hπval1
  exact (henselianBridge_realValuation_eq_of_subring_eq_of_anchor
    wB w (algebraMap Z E π) ((map_ne_zero (algebraMap Z E)).2 hπ0)
    hring.symm (hwBπ.trans hwπ.symm) horder).symm

/-- **F. K. Schmidt, exact consumed form**
(`fk_schmidt_two_henselian_valuations.tex`, `cor:consumed`).

If `Z` is a subfield of an algebraic closure `Ω` of `ℚ` and its absolute
Galois group `G_Z` is nontrivial, then `Z` cannot carry two inequivalent
nontrivial nonarchimedean valuations for which it is Henselian.

A `ValuationSubring` is the valuation-ring presentation of a
nonarchimedean valuation; inequivalence is therefore literal inequality.
This named obligation is intentionally ready to move unchanged to the
independent `FKSchmidt.lean` development. -/
theorem fkSchmidt_two_henselian_valuations
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω)
    (hGZ : Z.fixingSubgroup ≠ ⊥)
    (A B : ValuationSubring Z)
    (hA_nontrivial : A ≠ ⊤) (hB_nontrivial : B ≠ ⊤)
    (hA_henselian : IsHenselianValuationIn Z Ω A)
    (hB_henselian : IsHenselianValuationIn Z Ω B)
    (hinequivalent : A ≠ B) :
    False := by
  obtain ⟨vA, hvA, hvAhens⟩ :=
    exists_henselian_realValuation_of_subring Z A
      hA_nontrivial hA_henselian
  obtain ⟨vB, hvB, hvBhens⟩ :=
    exists_henselian_realValuation_of_subring Z B
      hB_nontrivial hB_henselian
  exact fkSchmidt_consumed_realValuations Z hGZ vA vB
    (by rwa [hvA]) (by rwa [hvB])
    (by simpa only [hvA, hvB] using hinequivalent)
    hvAhens hvBhens

/-- Distinct absolute finite places have distinct decomposition groups.
The proof passes to their common decomposition field.  Equality of the
restricted places contradicts unique prolongation; inequality supplies the
two valuations in the exact consumed F. K. Schmidt theorem. -/
theorem absoluteDecompositionGroup_ne_of_ne
    (K : Type*) [Field K] [NumberField K]
    (P Q : ValuationSubring (AlgebraicClosure K))
    (hP : IsAbsoluteFinitePlace K P)
    (hQ : IsAbsoluteFinitePlace K Q) (hPQ : P ≠ Q) :
    absoluteDecompositionGroup K P ≠
      absoluteDecompositionGroup K Q := by
  intro hgroups
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)
  let Z : IntermediateField ℚ (AlgebraicClosure K) :=
    (decompositionField K P).restrictScalars ℚ
  let A : ValuationSubring Z := P.comap Z.val.toRingHom
  let B : ValuationSubring Z := Q.comap Z.val.toRingHom
  have hdata :
      Z.fixingSubgroup ≠ ⊥ ∧
        A ≠ ⊤ ∧ B ≠ ⊤ ∧
        IsHenselianValuationIn Z (AlgebraicClosure K) A ∧
        IsHenselianValuationIn Z (AlgebraicClosure K) B ∧
        A ≠ B := by
    have hDPne : absoluteDecompositionGroup K P ≠ ⊥ := by
      intro hbot
      apply absoluteDecompositionGroup_not_procyclic P hP
      rw [hbot]
      refine ⟨1, ?_⟩
      rw [Subgroup.zpowers_eq_bot.mpr rfl]
      apply top_unique
      intro x _
      have hx : x = 1 := by
        apply Subtype.ext
        exact x.property
      rw [hx]
      exact Subgroup.one_mem _
    obtain ⟨σ, hσ⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDPne
    let τ : AlgebraicClosure K ≃ₐ[ℚ] AlgebraicClosure K :=
      σ.1.restrictScalars ℚ
    have hτmem : τ ∈ Z.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hσfix : σ.1 ∈ (decompositionField K P).fixingSubgroup := by
        rw [decompositionField_fixingSubgroup K P]
        exact σ.property
      exact (IntermediateField.mem_fixingSubgroup_iff
        (decompositionField K P) σ.1).mp hσfix x hx
    have hτne : τ ≠ 1 := by
      intro hτ
      apply hσ
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hτ x
    have hZne : Z.fixingSubgroup ≠ ⊥ := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mpr
      refine ⟨⟨τ, hτmem⟩, ?_⟩
      intro h
      exact hτne (congrArg Subtype.val h)
    have hAne : A ≠ ⊤ := by
      intro htop
      apply hP.1
      apply valuationSubring_eq_top_of_comap_eq_top Z P
      apply ValuationSubring.ext
      intro x
      have hx := ValuationSubring.ext_iff.mp htop x
      exact hx
    have hBne : B ≠ ⊤ := by
      intro htop
      apply hQ.1
      apply valuationSubring_eq_top_of_comap_eq_top Z Q
      apply ValuationSubring.ext
      intro x
      have hx := ValuationSubring.ext_iff.mp htop x
      exact hx
    have hfield : decompositionField K P = decompositionField K Q := by
      unfold decompositionField
      rw [hgroups]
    let DP := decompositionField K P
    have hDPZ : DP.toSubring = Z.toSubring := by
      ext x
      rfl
    let eP : DP ≃+* Z := RingEquiv.subringCongr hDPZ
    have heP (x : DP) :
        algebraMap Z (AlgebraicClosure K) (eP x) =
          algebraMap DP (AlgebraicClosure K) x := by
      rfl
    have hAhens0 := isHenselianValuationIn_equiv eP heP
      (P.comap DP.val.toRingHom)
      (decompositionField_isHenselian K P hP)
    have hPA : (P.comap DP.val.toRingHom).comap
        eP.symm.toRingHom = A := by
      apply ValuationSubring.ext
      intro x
      rfl
    have hAhens : IsHenselianValuationIn Z (AlgebraicClosure K) A := by
      rw [← hPA]
      exact hAhens0
    let DQ := decompositionField K Q
    have hDQZ : DQ.toSubring = Z.toSubring := by
      change (decompositionField K Q).toSubring =
        (decompositionField K P).toSubring
      rw [hfield]
    let eQ : DQ ≃+* Z := RingEquiv.subringCongr hDQZ
    have heQ (x : DQ) :
        algebraMap Z (AlgebraicClosure K) (eQ x) =
          algebraMap DQ (AlgebraicClosure K) x := by
      rfl
    have hBhens0 := isHenselianValuationIn_equiv eQ heQ
      (Q.comap DQ.val.toRingHom)
      (decompositionField_isHenselian K Q hQ)
    have hQB : (Q.comap DQ.val.toRingHom).comap
        eQ.symm.toRingHom = B := by
      apply ValuationSubring.ext
      intro x
      rfl
    have hBhens : IsHenselianValuationIn Z (AlgebraicClosure K) B := by
      rw [← hQB]
      exact hBhens0
    have hAB : A ≠ B := by
      intro heq
      apply hPQ
      let E : IntermediateField Z (AlgebraicClosure K) := ⊤
      have hPE : (P.comap E.val.toRingHom).comap
          (algebraMap Z E) = A := by
        apply ValuationSubring.ext
        intro x
        rfl
      have hQE : (Q.comap E.val.toRingHom).comap
          (algebraMap Z E) = A := by
        apply ValuationSubring.ext
        intro x
        change ((x : AlgebraicClosure K) ∈ Q) ↔ ((x : Z) ∈ A)
        have hx := ValuationSubring.ext_iff.mp heq x
        exact hx.symm
      have hext : P.comap E.val.toRingHom = Q.comap E.val.toRingHom :=
        (hAhens E).unique hPE hQE
      apply ValuationSubring.ext
      intro x
      exact ValuationSubring.ext_iff.mp hext ⟨x, trivial⟩
    exact ⟨hZne, hAne, hBne, hAhens, hBhens, hAB⟩
  exact fkSchmidt_two_henselian_valuations Z hdata.1 A B
    hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
    hdata.2.2.2.2.2

/-! ## Orientation-free interface (L1) -/

/-- Absolute finite places, bundled for the correspondence interface. -/
abbrev AbsoluteFinitePlaceOf
    (K : Type*) [Field K] [NumberField K] :=
  {W : ValuationSubring (AlgebraicClosure K) //
    IsAbsoluteFinitePlace K W}

/-- Every number field has a finite place, obtained by lying over the
rational prime `2`. -/
private theorem finitePlace_nonempty
    (K : Type*) [Field K] [NumberField K] : Nonempty (FinitePlace K) := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : p.IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  let q := Classical.choice (p.nonempty_primesOver (S := 𝓞 K))
  have hq0 : q.1 ≠ ⊥ := by
    intro h
    have hp0 : p ≠ ⊥ := by
      simpa [p] using (show (2 : ℤ) ≠ 0 by norm_num)
    apply hp0
    rw [q.2.2.over]
    change Ideal.comap (algebraMap ℤ (𝓞 K)) q.1 = ⊥
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
  exact ⟨⟨q.1, q.2.1, hq0⟩⟩

/-- Absolute finite places exist.  This is the explicit inhabitation sanity
check for the bundled type used by (L1). -/
theorem absoluteFinitePlaceOf_nonempty
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (AbsoluteFinitePlaceOf K) := by
  let L := trivialGaloisLevel K
  let w : FinitePlace L.field := Classical.choice (finitePlace_nonempty L.field)
  obtain ⟨W, hW, _⟩ := exists_absolutePlace_over_level K L w
  exact ⟨⟨W, hW⟩⟩

noncomputable instance absoluteFinitePlaceOfNonempty
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (AbsoluteFinitePlaceOf K) :=
  absoluteFinitePlaceOf_nonempty K

/-! ### Transport to a common ambient algebraic closure -/

/-- The finite-place predicate in an arbitrary ambient extension.  For the
chosen `AlgebraicClosure K` this is definitionally `IsAbsoluteFinitePlace`.
The general form is the adapter needed by a common-ambient model. -/
def IsAbsoluteFinitePlaceIn
    (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (W : ValuationSubring Ω) : Prop :=
  W ≠ ⊤ ∧ ∃ v : FinitePlace K,
    W.comap (algebraMap K Ω) = primeValuationSubring v

/-- Ambient absolute finite places, bundled by their valuation subring. -/
abbrev AbsoluteFinitePlaceIn
    (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] :=
  {W : ValuationSubring Ω // IsAbsoluteFinitePlaceIn K Ω W}

/-- Transport a valuation subring forward along a field equivalence. -/
def transportValuationSubring
    {L Ω : Type*} [Field L] [Field Ω]
    (e : L ≃+* Ω) (W : ValuationSubring L) : ValuationSubring Ω :=
  W.comap e.symm.toRingHom

/-- Membership equation pinning valuation-subring transport to the supplied
field equivalence. -/
@[simp]
theorem mem_transportValuationSubring
    {L Ω : Type*} [Field L] [Field Ω]
    (e : L ≃+* Ω) (W : ValuationSubring L) (x : Ω) :
    x ∈ transportValuationSubring e W ↔ e.symm x ∈ W :=
  Iff.rfl

/-- A base-algebra equivalence transports exactly the finite places over
that base. -/
theorem isAbsoluteFinitePlaceIn_transport_iff
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    (e : L ≃ₐ[K] Ω) (W : ValuationSubring L) :
    IsAbsoluteFinitePlaceIn K Ω
        (transportValuationSubring e.toRingEquiv W) ↔
      IsAbsoluteFinitePlaceIn K L W := by
  have htop : transportValuationSubring e.toRingEquiv W = ⊤ ↔ W = ⊤ := by
    constructor
    · intro h
      ext x
      have hx := ValuationSubring.ext_iff.mp h (e x)
      simpa [transportValuationSubring] using hx
    · rintro rfl
      ext x
      simp [transportValuationSubring]
  have hcomap :
      (transportValuationSubring e.toRingEquiv W).comap
          (algebraMap K Ω) =
        W.comap (algebraMap K L) := by
    ext x
    simp [transportValuationSubring]
  constructor
  · rintro ⟨hne, v, hv⟩
    exact ⟨fun h => hne (htop.mpr h), v, hcomap ▸ hv⟩
  · rintro ⟨hne, v, hv⟩
    refine ⟨fun h => hne (htop.mp h), v, ?_⟩
    rw [hcomap, hv]

/-- Transport from Mathlib's chosen algebraic closure to a supplied common
ambient closure.  The value equation below prevents this from being an
arbitrary equivalence of place types. -/
noncomputable def ambientAbsoluteFinitePlaceEquiv
    (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (e : AlgebraicClosure K ≃ₐ[K] Ω) :
    AbsoluteFinitePlaceOf K ≃ AbsoluteFinitePlaceIn K Ω where
  toFun P := ⟨transportValuationSubring e.toRingEquiv P.1,
    (isAbsoluteFinitePlaceIn_transport_iff K
      (AlgebraicClosure K) Ω e P.1).2 P.2⟩
  invFun P := ⟨transportValuationSubring e.symm.toRingEquiv P.1,
    (isAbsoluteFinitePlaceIn_transport_iff K Ω
      (AlgebraicClosure K) e.symm P.1).2 P.2⟩
  left_inv P := by
    apply Subtype.ext
    ext x
    simp [transportValuationSubring]
  right_inv P := by
    apply Subtype.ext
    ext x
    simp [transportValuationSubring]

/-- Defining valuation-ring equation for ambient place transport. -/
@[simp]
theorem ambientAbsoluteFinitePlaceEquiv_val
    (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (e : AlgebraicClosure K ≃ₐ[K] Ω) (P : AbsoluteFinitePlaceOf K) :
    (ambientAbsoluteFinitePlaceEquiv K Ω e P).1 =
      transportValuationSubring e.toRingEquiv P.1 :=
  rfl

/-- Contracting a prime-local valuation ring through a number-field
extension gives the valuation ring at the contracted prime. -/
private theorem primeValuationSubring_comap_restrict
    (K : Type*) {L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : FinitePlace L) :
    (primeValuationSubring w).comap (algebraMap K L) =
      primeValuationSubring (restrictFinitePlace K w) := by
  let v := restrictFinitePlace K w
  have hle : primeValuationSubring v ≤
      (primeValuationSubring w).comap (algebraMap K L) := by
    intro x hx
    rw [mem_primeValuationSubring_iff] at hx
    rw [ValuationSubring.mem_comap, mem_primeValuationSubring_iff]
    obtain ⟨a, b, hb, hab⟩ := hx
    refine ⟨algebraMap (𝓞 K) (𝓞 L) a,
      algebraMap (𝓞 K) (𝓞 L) b, ?_, ?_⟩
    · intro hbw
      apply hb
      change b ∈ (restrictFinitePlace K w).asIdeal
      exact hbw
    · have hcoe (c : 𝓞 K) :
          ((algebraMap (𝓞 K) (𝓞 L) c : 𝓞 L) : L) =
            algebraMap K L (c : K) := by
        calc
          _ = algebraMap (𝓞 K) L c :=
            (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L c).symm
          _ = algebraMap K L (c : K) :=
            IsScalarTower.algebraMap_apply (𝓞 K) K L c
      rw [hcoe, hcoe, ← map_mul, hab]
  have hne : (primeValuationSubring w).comap (algebraMap K L) ≠ ⊤ := by
    obtain ⟨a, ha, ha0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have haw : algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal := by
      exact ha
    have hlt : w.valuation L
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) < 1 :=
      (w.valuation_lt_one_iff_mem
        (algebraMap (𝓞 K) (𝓞 L) a)).2 haw
    have hmap0 : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).2 (by exact_mod_cast ha0)
    have hpos : 0 < w.valuation L (algebraMap K L (a : K)) :=
      (w.valuation L).pos_iff.mpr hmap0
    have hcoe :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) =
          algebraMap K L (a : K) := by
      calc
        _ = algebraMap (𝓞 K) L a :=
          (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a).symm
        _ = algebraMap K L (a : K) :=
          IsScalarTower.algebraMap_apply (𝓞 K) K L a
    rw [hcoe] at hlt
    have hinv : 1 < (w.valuation L (algebraMap K L (a : K)))⁻¹ :=
      (one_lt_inv₀ hpos).2 hlt
    intro htop
    have hz : (a : K)⁻¹ ∈
        (primeValuationSubring w).comap (algebraMap K L) := by
      rw [htop]
      trivial
    rw [ValuationSubring.mem_comap, primeValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hz
    rw [map_inv₀, Valuation.map_inv] at hz
    exact (not_le_of_gt hinv) hz
  letI : Ring.KrullDimLE 1 (primeValuationSubring v) := by
    change Ring.KrullDimLE 1
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  exact (ValuationSubring.eq_of_le_of_ne_top
    (primeValuationSubring v) hle hne).symm

/-- Finite-place status in a common algebraic closure is unchanged after a
finite extension of number-field bases.  This is the lying-over/restriction
adapter used when downstream represents every absolute prime over `ℚ`.
See `cofinal_descent_orientation_free.tex`, `cor:L1`. -/
theorem isAbsoluteFinitePlaceIn_iff_of_finite_extension
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    (W : ValuationSubring Ω) :
    IsAbsoluteFinitePlaceIn K Ω W ↔
      IsAbsoluteFinitePlaceIn L Ω W := by
  have hcomp :
      (W.comap (algebraMap L Ω)).comap (algebraMap K L) =
        W.comap (algebraMap K Ω) := by
    ext x
    simp only [ValuationSubring.mem_comap]
    rw [← IsScalarTower.algebraMap_apply K L Ω]
  constructor
  · rintro ⟨hWne, v, hv⟩
    let A := W.comap (algebraMap L Ω)
    have hA : A ≠ ⊤ := by
      intro htop
      apply primeValuationSubring_ne_top v
      rw [← hv, ← hcomp]
      ext x
      simp [A, htop]
    obtain ⟨w, hw, _⟩ := numberField_valuations A hA
    exact ⟨hWne, w, hw⟩
  · rintro ⟨hWne, w, hw⟩
    refine ⟨hWne, restrictFinitePlace K w, ?_⟩
    rw [← hcomp, hw, primeValuationSubring_comap_restrict K w]

/-- Identity-on-valuation-rings rebasing of ambient finite places across a
finite extension of number fields. -/
noncomputable def ambientAbsoluteFinitePlaceRebaseEquiv
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L] :
    AbsoluteFinitePlaceIn K Ω ≃ AbsoluteFinitePlaceIn L Ω where
  toFun P := ⟨P.1,
    (isAbsoluteFinitePlaceIn_iff_of_finite_extension K L Ω P.1).1 P.2⟩
  invFun P := ⟨P.1,
    (isAbsoluteFinitePlaceIn_iff_of_finite_extension K L Ω P.1).2 P.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rebase transport does not alter the ambient valuation ring. -/
@[simp]
theorem ambientAbsoluteFinitePlaceRebaseEquiv_val
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    (P : AbsoluteFinitePlaceIn K Ω) :
    (ambientAbsoluteFinitePlaceRebaseEquiv K L Ω P).1 = P.1 :=
  rfl

/-- Direct common-ambient adapter: an absolute place over `L` is transported
to `Ω` and then viewed over the lower number field `K`.  With `K = ℚ`, this
is the place equivalence required by the NU campaign's `AbsolutePrime`. -/
noncomputable def ambientAbsoluteFinitePlaceEquivOfFiniteExtension
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    (e : AlgebraicClosure L ≃ₐ[L] Ω) :
    AbsoluteFinitePlaceOf L ≃ AbsoluteFinitePlaceIn K Ω :=
  (ambientAbsoluteFinitePlaceEquiv L Ω e).trans
    (ambientAbsoluteFinitePlaceRebaseEquiv K L Ω).symm

/-- The direct adapter is pinned to forward transport of the valuation
subring along the supplied closure equivalence. -/
@[simp]
theorem ambientAbsoluteFinitePlaceEquivOfFiniteExtension_val
    (K L Ω : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    (e : AlgebraicClosure L ≃ₐ[L] Ω) (P : AbsoluteFinitePlaceOf L) :
    (ambientAbsoluteFinitePlaceEquivOfFiniteExtension K L Ω e P).1 =
      transportValuationSubring e.toRingEquiv P.1 := by
  rw [ambientAbsoluteFinitePlaceEquivOfFiniteExtension]
  exact ambientAbsoluteFinitePlaceEquiv_val L Ω e P

/-- Conjugation of an absolute finite place. -/
noncomputable def conjugateAbsoluteFinitePlace
    (K : Type*) [Field K] [NumberField K]
    (g : Field.absoluteGaloisGroup K) (P : AbsoluteFinitePlaceOf K) :
    AbsoluteFinitePlaceOf K := by
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
  refine ⟨σ • (P : ValuationSubring (AlgebraicClosure K)), ?_⟩
  rcases P.2 with ⟨hne, v, hv⟩
  refine ⟨?_, v, ?_⟩
  · intro htop
    apply hne
    change σ • P.1 = ⊤ at htop
    have h := congrArg
      (fun W : ValuationSubring (AlgebraicClosure K) => σ⁻¹ • W) htop
    have htopfix : σ⁻¹ •
        (⊤ : ValuationSubring (AlgebraicClosure K)) = ⊤ := by
      ext x
      simp [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa only [inv_smul_smul, htopfix] using h
  · apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change σ.symm (algebraMap K (AlgebraicClosure K) x) ∈ P.1 ↔ _
    rw [σ.symm.commutes]
    exact ValuationSubring.ext_iff.mp hv x

/-- Defining equation for conjugation of absolute finite places. -/
@[simp]
theorem conjugateAbsoluteFinitePlace_val
    (K : Type*) [Field K] [NumberField K]
    (g : Field.absoluteGaloisGroup K) (P : AbsoluteFinitePlaceOf K) :
    (conjugateAbsoluteFinitePlace K g P :
      ValuationSubring (AlgebraicClosure K)) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) • P.1 :=
  rfl

/-- Stabilizer of an ambient valuation subring under a supplied group of
field automorphisms.  This is the representation-independent target of
absolute decomposition-group transport. -/
def ambientDecompositionGroup
    {Ω G : Type*} [Field Ω] [Group G] [MulSemiringAction G Ω]
    (W : ValuationSubring Ω) : Subgroup G :=
  MulAction.stabilizer G W

/-- Transport of absolute decomposition groups to a common ambient closure.
The compatibility equation is exactly the defining equation provided by a
closure/Galois-group comparison such as the NU campaign's
`ambientClosureEquiv` and `ambientAbsoluteGaloisEquiv_spec`. -/
theorem map_absoluteDecompositionGroup_ambient
    {K Ω G : Type*} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [Group G] [MulSemiringAction G Ω]
    (eΩ : AlgebraicClosure K ≃ₐ[K] Ω)
    (eG : Field.absoluteGaloisGroup K ≃* G)
    (hcompat : ∀ (g : Field.absoluteGaloisGroup K)
        (x : AlgebraicClosure K),
      eΩ ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) x) =
        eG g • eΩ x)
    (P : AbsoluteFinitePlaceOf K) :
    Subgroup.map eG.toMonoidHom (absoluteDecompositionGroup K P.1) =
      ambientDecompositionGroup
        (ambientAbsoluteFinitePlaceEquiv K Ω eΩ P).1 := by
  let W := transportValuationSubring eΩ.toRingEquiv P.1
  have hinv (g : Field.absoluteGaloisGroup K) (x : Ω) :
      eΩ.symm ((eG g)⁻¹ • x) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (eΩ.symm x) := by
    apply eΩ.injective
    rw [eΩ.apply_symm_apply]
    symm
    calc
      eΩ ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (eΩ.symm x)) = eG (g⁻¹) • eΩ (eΩ.symm x) :=
        hcompat g⁻¹ (eΩ.symm x)
      _ = (eG g)⁻¹ • x := by simp
  have hstab (g : Field.absoluteGaloisGroup K) :
      g ∈ absoluteDecompositionGroup K P.1 ↔
        eG g ∈ ambientDecompositionGroup W := by
    change
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) • P.1 =
          P.1) ↔ eG g • W = W
    constructor
    · intro hg
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change (eΩ.symm ((eG g)⁻¹ • x) ∈ P.1) ↔
        eΩ.symm x ∈ P.1
      rw [hinv]
      have hm := ValuationSubring.ext_iff.mp hg (eΩ.symm x)
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hm
      exact hm
    · intro hg
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hm := ValuationSubring.ext_iff.mp hg (eΩ x)
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hm
      simp only [W, mem_transportValuationSubring] at hm
      have hi : eΩ.toRingEquiv.symm ((eG g)⁻¹ • eΩ x) =
          (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
            (eΩ.toRingEquiv.symm (eΩ x)) := by
        exact hinv g (eΩ x)
      have hs : eΩ.toRingEquiv.symm (eΩ x) = x := eΩ.symm_apply_apply x
      rw [hi, hs] at hm
      exact hm
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hstab g).mp hg
  · intro hy
    refine ⟨eG.symm y, (hstab (eG.symm y)).mpr ?_, eG.apply_symm_apply y⟩
    simpa using hy

/-- Ambient place transport intertwines conjugation.  Equality is stated on
valuation subrings so a downstream bundled-place type can consume it by its
extensionality theorem. -/
@[simp]
theorem ambientAbsoluteFinitePlaceEquiv_conjugate_val
    {K Ω G : Type*} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [Group G] [MulSemiringAction G Ω]
    (eΩ : AlgebraicClosure K ≃ₐ[K] Ω)
    (eG : Field.absoluteGaloisGroup K ≃* G)
    (hcompat : ∀ (g : Field.absoluteGaloisGroup K)
        (x : AlgebraicClosure K),
      eΩ ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) x) =
        eG g • eΩ x)
    (g : Field.absoluteGaloisGroup K) (P : AbsoluteFinitePlaceOf K) :
    (ambientAbsoluteFinitePlaceEquiv K Ω eΩ
      (conjugateAbsoluteFinitePlace K g P)).1 =
        eG g • (ambientAbsoluteFinitePlaceEquiv K Ω eΩ P).1 := by
  have hinv (x : Ω) :
      eΩ.symm ((eG g)⁻¹ • x) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (eΩ.symm x) := by
    apply eΩ.injective
    rw [eΩ.apply_symm_apply]
    symm
    calc
      eΩ ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (eΩ.symm x)) = eG (g⁻¹) • eΩ (eΩ.symm x) :=
        hcompat g⁻¹ (eΩ.symm x)
      _ = (eG g)⁻¹ • x := by simp
  have hinvR (x : Ω) :
      eΩ.toRingEquiv.symm ((eG g)⁻¹ • x) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹)
          (eΩ.toRingEquiv.symm x) := by
    exact hinv x
  change transportValuationSubring eΩ.toRingEquiv
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) • P.1) =
    eG g • transportValuationSubring eΩ.toRingEquiv P.1
  have hg_inv :
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)⁻¹ =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g⁻¹) := rfl
  ext x
  rw [mem_transportValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    mem_transportValuationSubring, hinvR, hg_inv]
  rfl

/-- Direct decomposition-group wrapper for the common-ambient/lower-base
adapter.  Taking the lower base to be `ℚ` matches the NU campaign's ambient
`AbsolutePrime` representation. -/
theorem map_absoluteDecompositionGroup_ambientOfFiniteExtension
    (K L Ω G : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    [Group G] [MulSemiringAction G Ω]
    (eΩ : AlgebraicClosure L ≃ₐ[L] Ω)
    (eG : Field.absoluteGaloisGroup L ≃* G)
    (hcompat : ∀ (g : Field.absoluteGaloisGroup L)
        (x : AlgebraicClosure L),
      eΩ ((show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g) x) =
        eG g • eΩ x)
    (P : AbsoluteFinitePlaceOf L) :
    Subgroup.map eG.toMonoidHom (absoluteDecompositionGroup L P.1) =
      ambientDecompositionGroup
        (ambientAbsoluteFinitePlaceEquivOfFiniteExtension K L Ω eΩ P).1 := by
  rw [ambientAbsoluteFinitePlaceEquivOfFiniteExtension_val]
  exact map_absoluteDecompositionGroup_ambient eΩ eG hcompat P

/-- Direct conjugation wrapper after transport to a lower-base ambient place.
It has the exact value-level conclusion needed for `AbsolutePrime.ext`. -/
@[simp]
theorem ambientAbsoluteFinitePlaceEquivOfFiniteExtension_conjugate_val
    (K L Ω G : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [FiniteDimensional K L]
    [Group G] [MulSemiringAction G Ω]
    (eΩ : AlgebraicClosure L ≃ₐ[L] Ω)
    (eG : Field.absoluteGaloisGroup L ≃* G)
    (hcompat : ∀ (g : Field.absoluteGaloisGroup L)
        (x : AlgebraicClosure L),
      eΩ ((show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g) x) =
        eG g • eΩ x)
    (g : Field.absoluteGaloisGroup L) (P : AbsoluteFinitePlaceOf L) :
    (ambientAbsoluteFinitePlaceEquivOfFiniteExtension K L Ω eΩ
      (conjugateAbsoluteFinitePlace L g P)).1 =
        eG g •
          (ambientAbsoluteFinitePlaceEquivOfFiniteExtension K L Ω eΩ P).1 := by
  simpa only [ambientAbsoluteFinitePlaceEquivOfFiniteExtension_val,
    ambientAbsoluteFinitePlaceEquiv_val] using
      ambientAbsoluteFinitePlaceEquiv_conjugate_val eΩ eG hcompat g P

/-- Interface (L1), orientation-free.  Any profinite-group isomorphism gives
a bijection of absolute finite places characterized by equality of
corresponding decomposition groups; the displayed iff states uniqueness,
and the final equation states equivariance. -/
theorem orientation_free_local_interface
    {K K' : Type*} [Field K] [Field K']
    [NumberField K] [NumberField K']
    (α : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup K') :
    ∃ e : AbsoluteFinitePlaceOf K ≃ AbsoluteFinitePlaceOf K',
      (∀ P : AbsoluteFinitePlaceOf K,
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          absoluteDecompositionGroup K' (e P).1) ∧
      (∀ (P : AbsoluteFinitePlaceOf K)
          (Q : AbsoluteFinitePlaceOf K'),
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          absoluteDecompositionGroup K' Q.1 ↔ Q = e P) ∧
      ∀ (g : Field.absoluteGaloisGroup K)
          (P : AbsoluteFinitePlaceOf K),
        e (conjugateAbsoluteFinitePlace K g P) =
          conjugateAbsoluteFinitePlace K' (α g) (e P) := by
  classical
  have hcollections :
      Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
          (absoluteDecompositionCollection K) =
        absoluteDecompositionCollection K' := by
    rw [← bare_reconstruction K, ← bare_reconstruction K']
    exact bareRecovered_functorial α
  have hexists (P : AbsoluteFinitePlaceOf K) :
      ∃ Q : AbsoluteFinitePlaceOf K',
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          absoluteDecompositionGroup K' Q.1 := by
    have hm : Subgroup.map α.toMulEquiv.toMonoidHom
          (absoluteDecompositionGroup K P.1) ∈
        absoluteDecompositionCollection K' := by
      rw [← hcollections]
      exact ⟨absoluteDecompositionGroup K P.1,
        ⟨P.1, P.2, rfl⟩, rfl⟩
    obtain ⟨W, hW, hWmap⟩ := hm
    exact ⟨⟨W, hW⟩, hWmap⟩
  let f : AbsoluteFinitePlaceOf K → AbsoluteFinitePlaceOf K' :=
    fun P => (hexists P).choose
  have hf_spec (P : AbsoluteFinitePlaceOf K) :
      Subgroup.map α.toMulEquiv.toMonoidHom
          (absoluteDecompositionGroup K P.1) =
        absoluteDecompositionGroup K' (f P).1 := by
    simpa [f] using (hexists P).choose_spec
  have hf_injective : Function.Injective f := by
    intro P Q hPQ
    have hmap :
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K Q.1) := by
      rw [hf_spec P, hf_spec Q, hPQ]
    have hgroups : absoluteDecompositionGroup K P.1 =
        absoluteDecompositionGroup K Q.1 :=
      subgroupMap_mulEquiv_injective α.toMulEquiv hmap
    by_contra hne
    have hvals : P.1 ≠ Q.1 := by
      intro h
      exact hne (Subtype.ext h)
    exact absoluteDecompositionGroup_ne_of_ne K P.1 Q.1 P.2 Q.2
      hvals hgroups
  have hf_surjective : Function.Surjective f := by
    intro Q
    have hQmem : absoluteDecompositionGroup K' Q.1 ∈
        absoluteDecompositionCollection K' :=
      ⟨Q.1, Q.2, rfl⟩
    have himage : absoluteDecompositionGroup K' Q.1 ∈
        Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
          (absoluteDecompositionCollection K) := by
      rw [hcollections]
      exact hQmem
    obtain ⟨D, ⟨W, hW, rfl⟩, hDmap⟩ := himage
    let P : AbsoluteFinitePlaceOf K := ⟨W, hW⟩
    refine ⟨P, ?_⟩
    apply Subtype.ext
    by_contra hne
    have hgroups : absoluteDecompositionGroup K' (f P).1 =
        absoluteDecompositionGroup K' Q.1 :=
      (hf_spec P).symm.trans hDmap
    exact absoluteDecompositionGroup_ne_of_ne K' (f P).1 Q.1
      (f P).2 Q.2 hne hgroups
  let e : AbsoluteFinitePlaceOf K ≃ AbsoluteFinitePlaceOf K' :=
    Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  have he_spec (P : AbsoluteFinitePlaceOf K) :
      Subgroup.map α.toMulEquiv.toMonoidHom
          (absoluteDecompositionGroup K P.1) =
        absoluteDecompositionGroup K' (e P).1 := by
    simpa [e] using hf_spec P
  refine ⟨e, he_spec, ?_, ?_⟩
  · intro P Q
    constructor
    · intro hQ
      apply Subtype.ext
      by_contra hne
      have hgroups : absoluteDecompositionGroup K' Q.1 =
          absoluteDecompositionGroup K' (e P).1 :=
        hQ.symm.trans (he_spec P)
      exact absoluteDecompositionGroup_ne_of_ne K' Q.1 (e P).1
        Q.2 (e P).2 hne hgroups
    · rintro rfl
      exact he_spec P
  · intro g P
    let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
    let τ : AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K' := α g
    have hsource :
        absoluteDecompositionGroup K
            (conjugateAbsoluteFinitePlace K g P).1 =
          Subgroup.map (MulAut.conj g).toMonoidHom
            (absoluteDecompositionGroup K P.1) := by
      change MulAction.stabilizer
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (σ • P.1) = _
      exact MulAction.stabilizer_smul_eq_stabilizer_map_conj σ P.1
    have htarget :
        absoluteDecompositionGroup K'
            (conjugateAbsoluteFinitePlace K' (α g) (e P)).1 =
          Subgroup.map (MulAut.conj (α g)).toMonoidHom
            (absoluteDecompositionGroup K' (e P).1) := by
      change MulAction.stabilizer
          (AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K')
            (τ • (e P).1) = _
      exact MulAction.stabilizer_smul_eq_stabilizer_map_conj τ (e P).1
    have hconjhom :
        α.toMulEquiv.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (α g)).toMonoidHom.comp
            α.toMulEquiv.toMonoidHom := by
      ext x
      change α (g * x * g⁻¹) = α g * α x * (α g)⁻¹
      simp
    have hgroups :
        absoluteDecompositionGroup K'
            (e (conjugateAbsoluteFinitePlace K g P)).1 =
          absoluteDecompositionGroup K'
            (conjugateAbsoluteFinitePlace K' (α g) (e P)).1 := by
      calc
        _ = Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K
              (conjugateAbsoluteFinitePlace K g P).1) :=
          (he_spec (conjugateAbsoluteFinitePlace K g P)).symm
        _ = Subgroup.map α.toMulEquiv.toMonoidHom
            (Subgroup.map (MulAut.conj g).toMonoidHom
              (absoluteDecompositionGroup K P.1)) := by rw [hsource]
        _ = Subgroup.map (MulAut.conj (α g)).toMonoidHom
            (Subgroup.map α.toMulEquiv.toMonoidHom
              (absoluteDecompositionGroup K P.1)) := by
          rw [Subgroup.map_map, Subgroup.map_map, hconjhom]
        _ = Subgroup.map (MulAut.conj (α g)).toMonoidHom
            (absoluteDecompositionGroup K' (e P).1) := by rw [he_spec P]
        _ = _ := htarget.symm
    apply Subtype.ext
    by_contra hne
    exact absoluteDecompositionGroup_ne_of_ne K'
      (e (conjugateAbsoluteFinitePlace K g P)).1
      (conjugateAbsoluteFinitePlace K' (α g) (e P)).1
      (e (conjugateAbsoluteFinitePlace K g P)).2
      (conjugateAbsoluteFinitePlace K' (α g) (e P)).2 hne hgroups

end

end NU.LocalTheory
