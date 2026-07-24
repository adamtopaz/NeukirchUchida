import Submission.NU.LCFT.Cohomology.InfRes
import Mathlib.GroupTheory.Nilpotent

/-!
# Tate's abstract reciprocity theorem

This module contains the splitting-module and cohomological-triviality interfaces, the concrete
row-sum calculation, the dimension-shift reciprocity equivalence, and a named package for the
three naturality squares.  The latter package deliberately exposes all vertical maps: later field
specializations do not need to unfold bar-resolution chain maps.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AbstractReciprocity

variable {G : Type} [Group G]

private lemma groupCohomology_map_congr
    {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} {f g : G →* H}
    {φ : Rep.res f A ⟶ B} {ψ : Rep.res g A ⟶ B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℕ) :
    groupCohomology.map f φ n = groupCohomology.map g ψ n := by
  subst hfg
  congr
  ext
  simp [hφψ]

private noncomputable def groupCohomology_mapIso
    {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
    (he : ∀ g, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e') (n : ℕ) :
    groupCohomology B n ≅ groupCohomology A n where
  hom := groupCohomology.map e.symm (Rep.ofHom ⟨e', fun h ↦ by simp [he]⟩) n
  inv := groupCohomology.map e (Rep.ofHom ⟨e'.symm, fun g ↦ by
    rw [e'.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology_map_congr (by simp) e'.symm_comp n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology_map_congr (by simp) e'.comp_symm n

/-- The additive augmentation map on the integral group ring. -/
def augmentationMap : (G →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)

/-- The augmentation ideal `I_G` as an additive subgroup. -/
def augmentationIdeal : AddSubgroup (G →₀ ℤ) :=
  (augmentationMap (G := G)).ker

/-- Concrete data of the splitting module `A(α)`. -/
structure SplittingModuleData (M : Rep.{0, 0, 0} ℤ G) (α : Inhomogeneous.H2 M) where
  /-- A normalized cocycle chosen to represent `α`. -/
  cocycle : Inhomogeneous.C2 M
  /-- The chosen cochain is a normalized two-cocycle. -/
  cocycle_mem : cocycle ∈ Inhomogeneous.cocycles2 M
  /-- The chosen cocycle represents the prescribed class. -/
  cocycle_class_eq :
    QuotientAddGroup.mk' (Inhomogeneous.coboundaries2 M) ⟨cocycle, cocycle_mem⟩ = α
  /-- The middle representation `A(α)`. -/
  middle : Rep.{0, 0, 0} ℤ G
  /-- The `G`-equivariant inclusion of coefficients. -/
  inclusion : M ⟶ middle
  /-- The `G`-equivariant projection to the augmentation ideal. -/
  projection : middle ⟶ barAugmentationIdeal G
  /-- The two displayed equivariant maps form a complex. -/
  sequence_zero : inclusion ≫ projection = 0
  /-- Exactness of `0 → A → A(α) → I_G → 0`. -/
  exact : (ShortComplex.mk inclusion projection sequence_zero).ShortExact
  /-- The defining sequence is the explicit cocycle pushout, not an unrelated extension. -/
  definingSequence_eq_pushout :
    ShortComplex.mk inclusion projection sequence_zero =
      cocyclePushoutSequence M cocycle cocycle_mem
  /-- The inclusion is injective. -/
  inclusion_injective : Function.Injective inclusion.hom
  /-- The projection is onto. -/
  projection_surjective : Function.Surjective projection.hom
  /-- The extension class represented by this construction. -/
  extensionClass : Inhomogeneous.H2 M
  /-- It is the prescribed class. -/
  extensionClass_eq : extensionClass = α
  /-- The extension class is the class of the cocycle defining the displayed pushout. -/
  extensionClass_eq_defining_cocycle : extensionClass =
    QuotientAddGroup.mk' (Inhomogeneous.coboundaries2 M) ⟨cocycle, cocycle_mem⟩
  /-- The prescribed class becomes zero through the constructed equivariant embedding. -/
  inclusion_kills_extensionClass :
    groupCohomology.map (.id G) inclusion 2 (comparisonH2 M extensionClass) = 0

/--
**C05**, proof of Theorem `thm:tate-reciprocity`: construct `A(α)` from a normalized cocycle and
obtain the exact extension by `I_G`.
-/
theorem splittingModule_exists (M : Rep ℤ G) (α : Inhomogeneous.H2 M) :
    Nonempty (SplittingModuleData M α) := by
  induction α using QuotientAddGroup.induction_on with
  | H z =>
      let a : Inhomogeneous.C2 M := z.1
      let ha : a ∈ Inhomogeneous.cocycles2 M := z.2
      refine ⟨{
        cocycle := a
        cocycle_mem := ha
        cocycle_class_eq := rfl
        middle := cocyclePushout M a ha
        inclusion := cocyclePushoutInclusion M a ha
        projection := cocyclePushoutProjection M a ha
        sequence_zero := (cocyclePushoutSequence M a ha).zero
        exact := cocyclePushoutSequence_shortExact M a ha
        definingSequence_eq_pushout := rfl
        inclusion_injective := ?_
        projection_surjective := ?_
        extensionClass := QuotientAddGroup.mk'
          (Inhomogeneous.coboundaries2 M) ⟨a, ha⟩
        extensionClass_eq := rfl
        extensionClass_eq_defining_cocycle := rfl
        inclusion_kills_extensionClass :=
          cocyclePushoutInclusion_kills_class M a ha }⟩
      · intro x y h
        exact congrArg Prod.fst h
      · intro x
        exact ⟨(0, x), rfl⟩

/-- A representation whose Tate cohomology vanishes after restriction to every subgroup. -/
def CohomologicallyTrivial (M : Rep ℤ G) : Prop :=
  ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
    Subsingleton (tateCohomology (Rep.res S.subtype M) n)

private def TateAcyclic {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : Prop :=
  ∀ n : ℤ, Subsingleton (tateCohomology M n)

private theorem rep_shortExact_of_function
    {G : Type} [Group G] {A B C : Rep ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (hzero : f ≫ g = 0)
    (hexact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    (ShortComplex.mk f g hzero).ShortExact := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  letI : Module ℤ C := C.hV2
  letI : Mono f := (Rep.mono_iff_injective f).2 hf
  have f_is_kernel : IsLimit (KernelFork.ofι f hzero) := by
    let lift (s : KernelFork g) : s.pt ⟶ A := by
      letI : Module ℤ s.pt := s.pt.hV2
      let pre (z : s.pt) : A := Classical.choose ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
      have hpre (z : s.pt) : f (pre z) = s.ι z :=
        Classical.choose_spec ((hexact (s.ι z)).1 (by
          have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
          exact hs))
      let add : s.pt →+ A :=
        { toFun := pre
          map_zero' := hf (by rw [map_zero, hpre, map_zero])
          map_add' := fun x y => hf (by rw [map_add, hpre, hpre, map_add, hpre]) }
      let l : s.pt →ₗ[ℤ] A :=
        { toFun := add
          map_add' := add.map_add
          map_smul' := fun n x => by
            change add (s.pt.hV2.smul n x) = A.hV2.smul n (add x)
            rw [int_smul_eq_zsmul s.pt.hV2, int_smul_eq_zsmul A.hV2]
            exact add.map_zsmul n x }
      exact Rep.ofHom ⟨l, fun σ => by
        apply LinearMap.ext
        intro z
        apply hf
        dsimp [l, add]
        calc
          f (pre (s.pt.ρ σ z)) = s.ι (s.pt.ρ σ z) := hpre _
          _ = B.ρ σ (s.ι z) := Rep.hom_comm_apply s.ι σ z
          _ = B.ρ σ (f (pre z)) := by rw [hpre]
          _ = f (A.ρ σ (pre z)) := (Rep.hom_comm_apply f σ (pre z)).symm⟩
    have lift_fac (s : KernelFork g) : lift s ≫ f = s.ι := by
      letI : Module ℤ s.pt := s.pt.hV2
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      change f ((lift s).hom z) = s.ι z
      simp only [lift]
      exact Classical.choose_spec ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
    exact Fork.IsLimit.mk _ lift lift_fac
      (fun s m hm => by
        apply (cancel_mono f).1
        exact hm.trans (lift_fac s).symm)
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ f_is_kernel
  · exact (Rep.mono_iff_injective f).2 hf
  · exact (Rep.epi_iff_surjective g).2 hg

private abbrev shiftInduced {G : Type} [Group G] (M : Rep ℤ G) : Rep ℤ G :=
  Rep.ind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype M)

private theorem shiftInduced_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    Subsingleton (tateCohomology (Rep.res S.subtype (shiftInduced M)) n) := by
  letI : Module ℤ M := M.hV2
  let e0 : Rep.res (⊥ : Subgroup G).subtype M ≅
      Rep.trivial ℤ (⊥ : Subgroup G) M := by
    apply Rep.mkIso
    exact Representation.Equiv.mk (LinearEquiv.refl ℤ M) (fun g => by
      apply LinearMap.ext
      intro x
      have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
      simp [Rep.res, hg])
  let eI := (Rep.indFunctor ℤ (⊥ : Subgroup G).subtype).mapIso e0
  let eS := (Rep.resFunctor S.subtype).mapIso eI
  let eT := (tateCohomologyFunctor n).mapIso eS
  have h := inducedFromTrivial_tateAcyclic G M S n
  exact ⟨fun x y => (ModuleCat.mono_iff_injective eT.hom).1 inferInstance (h.elim _ _)⟩

private abbrev shiftCoinduced {G : Type} [Group G] (M : Rep ℤ G) : Rep ℤ G :=
  Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype M)

private def shiftCoindPointMass {G : Type} [Group G] (M : Rep ℤ G)
    (b : Rep.res (⊥ : Subgroup G).subtype M) : shiftCoinduced M := by
  classical
  exact ⟨fun t => if t = 1 then b else 0, by
    intro x t
    have hx : x = 1 := by
      apply Subtype.ext
      exact (Subgroup.mem_bot (G := G)).mp x.2
    subst x
    simp⟩

private lemma shiftCoind_norm_pointMass
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (b : Rep.res (⊥ : Subgroup G).subtype M) (t : G) :
    ((shiftCoinduced M).norm.hom (shiftCoindPointMass M b)).1 t = b := by
  classical
  letI : Module ℤ (shiftCoinduced M) := (shiftCoinduced M).hV2
  rw [Rep.norm_apply, Representation.norm]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
    Representation.coind_apply, LinearMap.restrict_apply, LinearMap.funLeft_apply]
  change (∑ g : G, if t * g = 1 then b else 0) = b
  rw [Finset.sum_eq_single t⁻¹]
  · simp
  · intro g _ hg
    simp only [ite_eq_right_iff]
    intro h
    exact (hg (eq_inv_of_mul_eq_one_right h)).elim
  · simp

private lemma shiftCoind_invariant_eq_norm_pointMass
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (x : Inhomogeneous.invariants0 (shiftCoinduced M)) :
    (shiftCoinduced M).norm.hom
      (shiftCoindPointMass M (x.1.1 1)) = x.1 := by
  apply Subtype.ext
  apply funext
  intro t
  rw [shiftCoind_norm_pointMass]
  have h := congrArg (fun z : shiftCoinduced M => z.1 1) (x.2 t)
  simpa only [Representation.coind_apply, LinearMap.restrict_apply,
    LinearMap.funLeft_apply, one_mul] using h.symm

private theorem shiftCoind_H0_subsingleton
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) :
    Subsingleton (TateLowDegree.H0 (shiftCoinduced M)) := by
  constructor
  intro x y
  apply sub_eq_zero.mp
  induction x - y using QuotientAddGroup.induction_on with
  | H z =>
    apply (QuotientAddGroup.eq_zero_iff z).2
    change z ∈ TateLowDegree.normRangeInInvariants (shiftCoinduced M)
    exact ⟨shiftCoindPointMass M (z.1.1 1),
      shiftCoind_invariant_eq_norm_pointMass M z⟩

private lemma shiftCoind_normKernel_mem_augmentation
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (x : TateLowDegree.normKernel (shiftCoinduced M)) :
    x.1 ∈ TateLowDegree.augmentation (shiftCoinduced M) := by
  classical
  letI : Module ℤ (shiftCoinduced M) := (shiftCoinduced M).hV2
  have hsum := congrArg (fun z : shiftCoinduced M => z.1 1) x.2
  change (((shiftCoinduced M).norm.hom x.1).1 1) = 0 at hsum
  rw [Rep.norm_apply, Representation.norm] at hsum
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
    Representation.coind_apply, LinearMap.restrict_apply, LinearMap.funLeft_apply,
    one_mul] at hsum
  change (∑ g : G, x.1.1 g) = 0 at hsum
  have heq : (∑ t : G, ((shiftCoinduced M).ρ t⁻¹
      (shiftCoindPointMass M (x.1.1 t)) - shiftCoindPointMass M (x.1.1 t))) = x.1 := by
    apply Subtype.ext
    apply funext
    intro y
    simp only [Submodule.coe_sum, Finset.sum_apply, map_sub,
      Representation.coind_apply, LinearMap.restrict_apply, LinearMap.funLeft_apply]
    change (∑ t : G, ((if y * t⁻¹ = 1 then x.1.1 t else 0) -
      if y = 1 then x.1.1 t else 0)) = x.1.1 y
    rw [Finset.sum_sub_distrib, Finset.sum_eq_single y]
    · by_cases hy : y = 1
      · subst y
        simp [hsum]
      · simp [hy]
    · intro t _ hty
      simp only [ite_eq_right_iff]
      intro h
      exact (hty (inv_injective (eq_inv_of_mul_eq_one_right h))).elim
    · simp
  rw [← heq]
  apply AddSubgroup.sum_mem
  intro t _
  apply AddSubgroup.subset_closure
  exact ⟨t⁻¹, shiftCoindPointMass M (x.1.1 t), rfl⟩

private theorem shiftCoind_HMinusOne_subsingleton
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) :
    Subsingleton (TateLowDegree.HMinusOne (shiftCoinduced M)) := by
  constructor
  intro x y
  apply sub_eq_zero.mp
  induction x - y using QuotientAddGroup.induction_on with
  | H z =>
    apply (QuotientAddGroup.eq_zero_iff z).2
    exact shiftCoind_normKernel_mem_augmentation M z

private theorem shiftCoind_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) :
    TateAcyclic (shiftCoinduced M) := by
  classical
  intro n
  cases n with
  | ofNat n =>
      cases n with
      | zero =>
          let e := TateLowDegree.comparisonH0Tate (shiftCoinduced M)
          let h := shiftCoind_H0_subsingleton M
          exact ⟨fun x y => e.symm.injective (h.elim _ _)⟩
      | succ n =>
          let e := (TateCohomology.isoGroupCohomology (n + 1)).app
              (shiftCoinduced M) ≪≫
            groupCohomology.coindIso (Rep.res (⊥ : Subgroup G).subtype M) (n + 1)
          exact ModuleCat.isZero_iff_subsingleton.mp
            ((isZero_groupCohomology_succ_of_subsingleton
              (Rep.res (⊥ : Subgroup G).subtype M) n).of_iso e)
  | negSucc n =>
      cases n with
      | zero =>
          let e := (TateLowDegree.HMinusOne_equiv_tate (shiftCoinduced M)).some
          let h := shiftCoind_HMinusOne_subsingleton M
          exact ⟨fun x y => e.symm.injective (h.elim _ _)⟩
      | succ n =>
          let e := (TateCohomology.isoGroupHomology (-(n + 2 : ℤ)) (n + 1)
              (by omega)).app
              (Rep.ind (⊥ : Subgroup G).subtype
                (Rep.res (⊥ : Subgroup G).subtype M)) ≪≫
            groupHomology.indIso (⊥ : Subgroup G)
              (Rep.res (⊥ : Subgroup G).subtype M) (n + 1)
          have hz := isZero_groupHomology_succ_of_subsingleton
            (Rep.res (⊥ : Subgroup G).subtype M) n
          have hInd : IsZero
              (tateCohomology (Rep.ind (⊥ : Subgroup G).subtype
                (Rep.res (⊥ : Subgroup G).subtype M)) (-(n + 2 : ℤ))) :=
            hz.of_iso e
          exact ModuleCat.isZero_iff_subsingleton.mp <| hInd.of_iso
            ((tateCohomologyFunctor (-(n + 2 : ℤ))).mapIso
              (Rep.indCoindIso (Rep.res (⊥ : Subgroup G).subtype M))).symm

private theorem shiftInduced_tateAcyclic_self
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : TateAcyclic (shiftInduced M) := by
  classical
  intro n
  let ei := (tateCohomologyFunctor n).mapIso
    (Rep.indCoindIso (Rep.res (⊥ : Subgroup G).subtype M))
  let h := shiftCoind_tateAcyclic M n
  exact ⟨fun x y => (ModuleCat.mono_iff_injective ei.hom).1 inferInstance (h.elim _ _)⟩

private structure UpShiftData {G : Type} [Group G] (M : Rep ℤ G) where
  shifted : Rep ℤ G
  inclusion : M ⟶ shiftInduced M
  projection : shiftInduced M ⟶ shifted
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact
  inclusion_injective : Function.Injective inclusion.hom
  projection_surjective : Function.Surjective projection.hom
  function_exact : Function.Exact inclusion.hom projection.hom

private noncomputable def upShiftData
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : UpShiftData M := by
  classical
  letI : Module ℤ M := M.hV2
  letI : Module ℤ (shiftInduced M) := (shiftInduced M).hV2
  let T : Subgroup G := ⊥
  let C := Rep.coind T.subtype (Rep.res T.subtype M)
  let e := Rep.indCoindIso (Rep.res T.subtype M)
  let u : M ⟶ C := Rep.resCoindToHom T.subtype M (Rep.res T.subtype M) (𝟙 _)
  let f : M ⟶ shiftInduced M := u ≫ e.inv
  have hf : Function.Injective f := by
    intro x y hxy
    have hu : u.hom x = u.hom y := by
      have heq := congrArg (fun z : shiftInduced M => e.hom z) hxy
      simpa [f] using heq
    have heq := congrArg (fun z : C => z.1 1) hu
    simpa [u] using heq
  let W : Submodule ℤ (shiftInduced M) := LinearMap.range f.hom.toLinearMap
  have hW : ∀ g, W ≤ W.comap ((shiftInduced M).ρ g) := by
    intro g x hx
    obtain ⟨m, rfl⟩ := hx
    exact ⟨M.ρ g m, Rep.hom_comm_apply f g m⟩
  let Q := Rep.quotient (shiftInduced M) W hW
  let q : shiftInduced M ⟶ Q := Rep.mkQ (shiftInduced M) W hW
  have hzero : f ≫ q = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change Submodule.Quotient.mk (f.hom x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  have hexact : Function.Exact f q := by
    intro x
    rw [show q.hom x = 0 ↔ x ∈ W from Submodule.Quotient.mk_eq_zero W]
    change x ∈ LinearMap.range f.hom.toLinearMap ↔ ∃ a, f.hom a = x
    rfl
  have hq : Function.Surjective q := W.mkQ_surjective
  exact {
    shifted := Q
    inclusion := f
    projection := q
    zero := hzero
    exact := rep_shortExact_of_function f q hzero hexact hf hq
    inclusion_injective := hf
    projection_surjective := hq
    function_exact := hexact }

private structure DownShiftData {G : Type} [Group G] (M : Rep ℤ G) where
  shifted : Rep ℤ G
  inclusion : shifted ⟶ shiftInduced M
  projection : shiftInduced M ⟶ M
  zero : inclusion ≫ projection = 0
  exact : (ShortComplex.mk inclusion projection zero).ShortExact
  inclusion_injective : Function.Injective inclusion.hom
  projection_surjective : Function.Surjective projection.hom
  function_exact : Function.Exact inclusion.hom projection.hom

private noncomputable def downShiftData
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : DownShiftData M := by
  classical
  letI : Module ℤ M := M.hV2
  letI : Module ℤ (shiftInduced M) := (shiftInduced M).hV2
  let T : Subgroup G := ⊥
  let g : shiftInduced M ⟶ M :=
    (Rep.indResAdjunction ℤ T.subtype).counit.app M
  have hg : Function.Surjective g := by
    intro x
    refine ⟨Representation.IndV.mk T.subtype (Rep.res T.subtype M).ρ 1 x, ?_⟩
    have he : Rep.indResHomEquiv T.subtype (Rep.res T.subtype M) M g = 𝟙 _ := by
      change (Rep.indResHomEquiv T.subtype (Rep.res T.subtype M) M)
        ((Rep.indResHomEquiv T.subtype (Rep.res T.subtype M) M).symm (𝟙 _)) = _
      exact (Rep.indResHomEquiv T.subtype (Rep.res T.subtype M) M).apply_symm_apply _
    exact congrArg (fun q : Rep.res T.subtype M ⟶ Rep.res T.subtype M => q.hom x) he
  let W : Submodule ℤ (shiftInduced M) := LinearMap.ker g.hom.toLinearMap
  have hW : ∀ s, W ≤ W.comap ((shiftInduced M).ρ s) := by
    intro s x hx
    change g.hom x = 0 at hx
    change g.hom ((shiftInduced M).ρ s x) = 0
    calc
      g.hom ((shiftInduced M).ρ s x) = M.ρ s (g.hom x) :=
        Rep.hom_comm_apply g s x
      _ = 0 := by rw [hx, map_zero]
  let K := (shiftInduced M).subrepresentation W hW
  let f : K ⟶ shiftInduced M := Rep.subtype (shiftInduced M) W hW
  have hzero : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact x.2
  have hexact : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hxW : x ∈ W := hx
      exact ⟨⟨x, hxW⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  have hf : Function.Injective f := fun x y hxy => Subtype.ext hxy
  exact {
    shifted := K
    inclusion := f
    projection := g
    zero := hzero
    exact := rep_shortExact_of_function f g hzero hexact hf hg
    inclusion_injective := hf
    projection_surjective := hg
    function_exact := hexact }

private theorem tateAcyclic_iff_of_middle
    {G : Type} [Group G] [Fintype G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (hmid : TateAcyclic X.X₂) : TateAcyclic X.X₁ ↔ TateAcyclic X.X₃ := by
  constructor
  · intro hleft n
    have hzmid : IsZero (tateCohomology X.X₂ n) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hmid n)
    have hzmid' : IsZero (tateCohomology X.X₂ (n + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hmid (n + 1))
    letI : IsIso (TateCohomology.δ hX n) :=
      (TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ
        n (n + 1) rfl hzmid hzmid'
    have hzleft : IsZero (tateCohomology X.X₁ (n + 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hleft (n + 1))
    exact ModuleCat.isZero_iff_subsingleton.mp
      (hzleft.of_iso (asIso (TateCohomology.δ hX n)))
  · intro hright n
    have hzmid : IsZero (tateCohomology X.X₂ (n - 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hmid (n - 1))
    have hzmid' : IsZero (tateCohomology X.X₂ n) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hmid n)
    have hrel : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
    letI : IsIso ((TateCohomology.map_tateComplexFunctor_shortExact hX).δ
        (n - 1) n hrel) :=
      (TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ
        (n - 1) n hrel hzmid hzmid'
    have hzright : IsZero (tateCohomology X.X₃ (n - 1)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hright (n - 1))
    exact ModuleCat.isZero_iff_subsingleton.mp
      (hzright.of_iso
        (asIso ((TateCohomology.map_tateComplexFunctor_shortExact hX).δ
          (n - 1) n hrel)).symm)

private theorem tate_subsingleton_target_of_delta
    {G : Type} [Group G] [Fintype G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (n : ℤ)
    (hmid : TateAcyclic X.X₂)
    (hsource : Subsingleton (tateCohomology X.X₃ n)) :
    Subsingleton (tateCohomology X.X₁ (n + 1)) := by
  have hzmid : IsZero (tateCohomology X.X₂ n) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hmid n)
  have hzmid' : IsZero (tateCohomology X.X₂ (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hmid (n + 1))
  letI : IsIso (TateCohomology.δ hX n) :=
    (TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ
      n (n + 1) rfl hzmid hzmid'
  have hzsource : IsZero (tateCohomology X.X₃ n) :=
    ModuleCat.isZero_iff_subsingleton.mpr hsource
  exact ModuleCat.isZero_iff_subsingleton.mp
    (hzsource.of_iso (asIso (TateCohomology.δ hX n)).symm)

private theorem tate_subsingleton_source_of_delta
    {G : Type} [Group G] [Fintype G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (n : ℤ)
    (hmid : TateAcyclic X.X₂)
    (htarget : Subsingleton (tateCohomology X.X₁ (n + 1))) :
    Subsingleton (tateCohomology X.X₃ n) := by
  have hzmid : IsZero (tateCohomology X.X₂ n) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hmid n)
  have hzmid' : IsZero (tateCohomology X.X₂ (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hmid (n + 1))
  letI : IsIso (TateCohomology.δ hX n) :=
    (TateCohomology.map_tateComplexFunctor_shortExact hX).isIso_δ
      n (n + 1) rfl hzmid hzmid'
  have hztarget : IsZero (tateCohomology X.X₁ (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr htarget
  exact ModuleCat.isZero_iff_subsingleton.mp
    (hztarget.of_iso (asIso (TateCohomology.δ hX n)))

private theorem tateAcyclic_of_shift_stable
    {G : Type} [Group G] [Fintype G]
    (Good : Rep ℤ G → Prop) (M : Rep ℤ G)
    (hlow : ∀ X, Good X →
      Subsingleton (groupCohomology.H1 X) ∧ Subsingleton (groupCohomology.H2 X))
    (hup : ∀ X, Good X → Good (upShiftData X).shifted)
    (hdown : ∀ X, Good X → Good (downShiftData X).shifted)
    (hM : Good M) : TateAcyclic M := by
  classical
  have hpos : ∀ k : ℕ, ∀ X : Rep ℤ G, Good X →
      Subsingleton (tateCohomology X ((k : ℤ) + 1)) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro X hX
        let e := (TateCohomology.isoGroupCohomology 1).app X
        have h := (hlow X hX).1
        simpa using (show Subsingleton (tateCohomology X 1) from
          ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
            (h.elim _ _)⟩)
    | one =>
        intro X hX
        let e := (TateCohomology.isoGroupCohomology 2).app X
        have h := (hlow X hX).2
        simpa using (show Subsingleton (tateCohomology X 2) from
          ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
            (h.elim _ _)⟩)
    | more k hk hk1 =>
        intro X hX
        let U := upShiftData X
        let C := ShortComplex.mk U.inclusion U.projection U.zero
        have hs0 := hk1 U.shifted (hup X hX)
        have hs : Subsingleton (tateCohomology U.shifted ((k : ℤ) + 2)) := by
          rw [show (k : ℤ) + 2 = ((k + 1 : ℕ) : ℤ) + 1 by
            push_cast
            ring]
          exact hs0
        have ht := tate_subsingleton_target_of_delta U.exact ((k : ℤ) + 2)
          (shiftInduced_tateAcyclic_self X) hs
        simpa [C] using ht
  have hneg : ∀ k : ℕ, ∀ X : Rep ℤ G, Good X →
      Subsingleton (tateCohomology X (-(k : ℤ))) := by
    intro k
    induction k with
    | zero =>
        intro X hX
        let D := downShiftData X
        let C := ShortComplex.mk D.inclusion D.projection D.zero
        have ht0 := hpos 0 D.shifted (hdown X hX)
        have ht : Subsingleton (tateCohomology D.shifted (0 + 1)) := by
          simpa using ht0
        have hs := tate_subsingleton_source_of_delta D.exact 0
          (shiftInduced_tateAcyclic_self X) ht
        simpa [C] using hs
    | succ k hk =>
        intro X hX
        let D := downShiftData X
        let C := ShortComplex.mk D.inclusion D.projection D.zero
        have ht0 := hk D.shifted (hdown X hX)
        have ht : Subsingleton
            (tateCohomology D.shifted (-((k + 1 : ℕ) : ℤ) + 1)) := by
          simpa using ht0
        have hs := tate_subsingleton_source_of_delta D.exact
          (-((k + 1 : ℕ) : ℤ)) (shiftInduced_tateAcyclic_self X) ht
        simpa [C] using hs
  intro n
  cases n with
  | ofNat k =>
      cases k with
      | zero => simpa using hneg 0 M hM
      | succ k => simpa using hpos k M hM
  | negSucc k =>
      rw [show Int.negSucc k = -((k + 1 : ℕ) : ℤ) by omega]
      exact hneg (k + 1) M hM

private theorem concreteH1_subsingleton_of_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (hM : TateAcyclic M) :
    Subsingleton (Inhomogeneous.H1 M) := by
  let e := (TateCohomology.isoGroupCohomology 1).app M
  have ht := hM 1
  have hg : Subsingleton (groupCohomology.H1 M) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective e.inv).1 inferInstance (ht.elim _ _)⟩
  exact ⟨fun x y => (comparisonH1 M).injective (hg.elim _ _)⟩

private theorem concreteH2_subsingleton_of_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (hM : TateAcyclic M) :
    Subsingleton (Inhomogeneous.H2 M) := by
  let e := (TateCohomology.isoGroupCohomology 2).app M
  have ht := hM 2
  have hg : Subsingleton (groupCohomology.H2 M) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective e.inv).1 inferInstance (ht.elim _ _)⟩
  exact ⟨fun x y => (comparisonH2 M).injective (hg.elim _ _)⟩

private noncomputable instance quotientToInvariants_preservesZeroMorphisms
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    (Rep.quotientToInvariantsFunctor ℤ N).PreservesZeroMorphisms := by
  constructor
  intro A B
  ext
  rfl

private theorem quotientToInvariants_shortExact_of_H1_zero
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {X : ShortComplex (Rep ℤ G)}
    (hexact : Function.Exact X.f.hom X.g.hom)
    (hf : Function.Injective X.f.hom) (hg : Function.Surjective X.g.hom)
    (hH1 : Subsingleton (Inhomogeneous.H1 (Rep.res N.subtype X.X₁))) :
    (X.map (Rep.quotientToInvariantsFunctor ℤ N)).ShortExact := by
  letI : Module ℤ X.X₁ := X.X₁.hV2
  letI : Module ℤ X.X₂ := X.X₂.hV2
  letI : Module ℤ X.X₃ := X.X₃.hV2
  let F := Rep.quotientToInvariantsFunctor ℤ N
  have hsurj : Function.Surjective (F.map X.g).hom := by
    intro y
    change Representation.invariants (X.X₃.ρ.comp N.subtype) at y
    obtain ⟨b, hb⟩ := hg y.1
    have hlift (n : N) : ∃ a : X.X₁,
        X.f.hom a = (Rep.res N.subtype X.X₂).ρ n b - b := by
      apply (hexact _).1
      change X.g.hom (X.X₂.ρ n b - b) = 0
      rw [map_sub, Rep.hom_comm_apply, hb]
      change X.X₃.ρ n y.1 - y.1 = 0
      exact sub_eq_zero.mpr (y.2 n)
    choose c hc using hlift
    let z0 : Inhomogeneous.C1 (Rep.res N.subtype X.X₁) := fun n => c n
    have hzCocycle : Inhomogeneous.d1 (Rep.res N.subtype X.X₁) z0 = 0 := by
      ext n m
      change X.X₁.ρ n (c m) - c (n * m) + c n = 0
      apply hf
      rw [map_zero, map_add, map_sub, Rep.hom_comm_apply, hc, hc, hc]
      change X.X₂.ρ n (X.X₂.ρ m b - b) -
          (X.X₂.ρ (n * m) b - b) + (X.X₂.ρ n b - b) = 0
      rw [map_sub]
      letI : Module ℤ X.X₂ := X.X₂.hV2
      rw [← Module.End.mul_apply, ← map_mul]
      abel
    have hzNorm : z0 1 = 0 := by
      change c 1 = 0
      apply hf
      rw [map_zero, hc]
      simp
    let z : Inhomogeneous.cocycles1 (Rep.res N.subtype X.X₁) :=
      ⟨z0, hzCocycle, hzNorm⟩
    have hz : (QuotientAddGroup.mk'
        (Inhomogeneous.coboundaries1 (Rep.res N.subtype X.X₁)) z :
        Inhomogeneous.H1 (Rep.res N.subtype X.X₁)) = 0 := hH1.elim _ _
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff z).mp hz
    let b' : X.X₂ := b - X.f.hom a
    have hb'inv : ∀ n : N, X.X₂.ρ n b' = b' := by
      intro n
      apply sub_eq_zero.mp
      change X.X₂.ρ n (b - X.f.hom a) - (b - X.f.hom a) = 0
      rw [map_sub, ← Rep.hom_comm_apply]
      have han := congrFun ha n
      change X.X₁.ρ n a - a = c n at han
      have hcn := hc n
      rw [← han] at hcn
      change X.f.hom (X.X₁.ρ n a - a) = X.X₂.ρ n b - b at hcn
      calc
        (X.X₂.ρ n b - X.f.hom (X.X₁.ρ n a)) - (b - X.f.hom a) =
            (X.X₂.ρ n b - b) -
              X.f.hom (X.X₁.ρ n a - a) := by rw [map_sub]; abel
        _ = 0 := by rw [hcn, sub_self]
    let b'' : Representation.invariants (X.X₂.ρ.comp N.subtype) := ⟨b', hb'inv⟩
    refine ⟨b'', ?_⟩
    apply Subtype.ext
    change X.g.hom (b - X.f.hom a) = y.1
    rw [map_sub, hb]
    have hzero : X.g.hom (X.f.hom a) = 0 := (hexact _).2 ⟨a, rfl⟩
    rw [hzero, sub_zero]
  have hfY : Function.Injective (F.map X.f).hom := by
    intro x y hxy
    change Representation.invariants (X.X₁.ρ.comp N.subtype) at x y
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hxy
  have hexactY : Function.Exact (F.map X.f).hom (F.map X.g).hom := by
    intro x
    change Representation.invariants (X.X₂.ρ.comp N.subtype) at x
    constructor
    · intro hx
      have hx0 : X.g.hom x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨a, ha⟩ := (hexact x.1).1 hx0
      have hainv : ∀ n : N, X.X₁.ρ n a = a := by
        intro n
        apply hf
        rw [Rep.hom_comm_apply, ha]
        exact x.2 n
      exact ⟨⟨a, hainv⟩, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      exact (hexact _).2 ⟨a.1, rfl⟩
  exact rep_shortExact_of_function (F.map X.f) (F.map X.g)
    (by rw [← F.map_comp, X.zero, F.map_zero]) hexactY hfY hsurj

private noncomputable def reciprocitySubgroupTransversal
    {G : Type} [Group G] (S : Subgroup G) :
    Inhomogeneous.Transfer.ExplicitTransversal S
      (Quotient (QuotientGroup.rightRel S)) where
  rep q := Quotient.out q
  decomposition :=
    { toFun := fun p => (p.2 : G) * Quotient.out p.1
      invFun := fun g =>
        (Quotient.mk'' g,
          ⟨g * (Quotient.out (Quotient.mk'' g :
              Quotient (QuotientGroup.rightRel S)))⁻¹, by
            apply QuotientGroup.rightRel_apply.mp
            apply Quotient.exact'
            exact Quotient.out_eq (Quotient.mk'' g :
              Quotient (QuotientGroup.rightRel S))⟩)
      left_inv := by
        rintro ⟨q, s⟩
        have hq : Quotient.mk'' ((s : G) * Quotient.out q) = q := by
          rw [← Quotient.out_eq q]
          symm
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          simp [mul_assoc]
        apply Prod.ext
        · exact hq
        · apply Subtype.ext
          change (s : G) * Quotient.out q *
            (Quotient.out (Quotient.mk'' ((s : G) * Quotient.out q) :
              Quotient (QuotientGroup.rightRel S)))⁻¹ = s
          rw [hq]
          simp
      right_inv := by
        intro g
        simp [mul_assoc] }
  decomposition_apply := fun _ _ => rfl

private theorem H1_index_smul_eq_zero_of_restriction_zero
    {G : Type} [Group G] [Fintype G] (S : Subgroup G) (M : Rep ℤ G)
    (hS : Subsingleton (Inhomogeneous.H1 (Rep.res S.subtype M)))
    (x : Inhomogeneous.H1 M) : S.index • x = 0 := by
  classical
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
  let T := reciprocitySubgroupTransversal S
  have hr : Inhomogeneous.restrictionH1 S.subtype M x = 0 := hS.elim _ _
  rw [← Inhomogeneous.Transfer.corH1_restriction T M x, hr, map_zero]

private theorem H2_index_smul_eq_zero_of_restriction_zero
    {G : Type} [Group G] [Fintype G] (S : Subgroup G) (M : Rep ℤ G)
    (hS : Subsingleton (Inhomogeneous.H2 (Rep.res S.subtype M)))
    (x : Inhomogeneous.H2 M) : S.index • x = 0 := by
  classical
  letI : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
  let T := reciprocitySubgroupTransversal S
  have hr : Inhomogeneous.restrictionH2 S.subtype M x = 0 := hS.elim _ _
  rw [← Inhomogeneous.Transfer.corH2_restriction T M x, hr, map_zero]

private theorem eq_zero_of_sylow_index_smul_eq_zero
    {G : Type} [Group G] [Fintype G] {A : Type} [AddCommGroup A] (x : A)
    (hcard : Nat.card G • x = 0)
    (hSylow : ∀ (p : ℕ) [Fact (Nat.Prime p)] (P : Sylow p G), P.index • x = 0) :
    x = 0 := by
  by_contra hx
  have hord1 : addOrderOf x ≠ 1 := by
    intro h
    exact hx (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpord⟩ := Nat.exists_prime_and_dvd hord1
  have hordcard : addOrderOf x ∣ Nat.card G :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hcard
  have hpcard : p ∣ Nat.card G := hpord.trans hordcard
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let P : Sylow p G := Classical.choice (Sylow.nonempty (p := p) (G := G))
  have hordindex : addOrderOf x ∣ P.index :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr (hSylow p P)
  exact P.not_dvd_index (hpord.trans hordindex)

private theorem lowCohomology_of_proper_subgroups_acyclic
    {G : Type} [Group G] [Fintype G]
    (hcard : 1 < Nat.card G)
    (hnp : ∀ (p : ℕ), Nat.Prime p → ¬ IsPGroup p G)
    (M : Rep ℤ G)
    (hproper : ∀ (S : Subgroup G) [Fintype S],
      Nat.card S < Nat.card G → TateAcyclic (Rep.res S.subtype M)) :
    Subsingleton (groupCohomology.H1 M) ∧
      Subsingleton (groupCohomology.H2 M) := by
  classical
  have hbotlt : Nat.card (⊥ : Subgroup G) < Nat.card G := by
    simpa using hcard
  have hbot := hproper (⊥ : Subgroup G) hbotlt
  have hbot1 := concreteH1_subsingleton_of_tateAcyclic _ hbot
  have hbot2 := concreteH2_subsingleton_of_tateAcyclic _ hbot
  have hc1zero : ∀ x : Inhomogeneous.H1 M, x = 0 := by
    intro x
    have hcardx : Nat.card G • x = 0 := by
      rw [← Subgroup.index_bot]
      exact H1_index_smul_eq_zero_of_restriction_zero (⊥ : Subgroup G) M hbot1 x
    apply eq_zero_of_sylow_index_smul_eq_zero x hcardx
    intro p hp P
    have hPdiv : Nat.card P ∣ Nat.card G :=
      ⟨P.index, P.card_mul_index.symm⟩
    have hPle : Nat.card P ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos hPdiv
    have hPne : Nat.card P ≠ Nat.card G := by
      intro heq
      exact (hnp p hp.out)
        (IsPGroup.of_card (heq.symm.trans P.card_eq_multiplicity))
    have hPlt : Nat.card P < Nat.card G := lt_of_le_of_ne hPle hPne
    have hP := hproper P hPlt
    have hP1 := concreteH1_subsingleton_of_tateAcyclic _ hP
    exact H1_index_smul_eq_zero_of_restriction_zero (G := G)
      (P : Subgroup G) M hP1 x
  have hc2zero : ∀ x : Inhomogeneous.H2 M, x = 0 := by
    intro x
    have hcardx : Nat.card G • x = 0 := by
      rw [← Subgroup.index_bot]
      exact H2_index_smul_eq_zero_of_restriction_zero (⊥ : Subgroup G) M hbot2 x
    apply eq_zero_of_sylow_index_smul_eq_zero x hcardx
    intro p hp P
    have hPdiv : Nat.card P ∣ Nat.card G :=
      ⟨P.index, P.card_mul_index.symm⟩
    have hPle : Nat.card P ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos hPdiv
    have hPne : Nat.card P ≠ Nat.card G := by
      intro heq
      exact (hnp p hp.out)
        (IsPGroup.of_card (heq.symm.trans P.card_eq_multiplicity))
    have hPlt : Nat.card P < Nat.card G := lt_of_le_of_ne hPle hPne
    have hP := hproper P hPlt
    have hP2 := concreteH2_subsingleton_of_tateAcyclic _ hP
    exact H2_index_smul_eq_zero_of_restriction_zero (G := G)
      (P : Subgroup G) M hP2 x
  have hc1 : Subsingleton (Inhomogeneous.H1 M) :=
    ⟨fun x y => (hc1zero x).trans (hc1zero y).symm⟩
  have hc2 : Subsingleton (Inhomogeneous.H2 M) :=
    ⟨fun x y => (hc2zero x).trans (hc2zero y).symm⟩
  exact
    ⟨⟨fun x y => (comparisonH1 M).symm.injective (hc1.elim _ _)⟩,
      ⟨fun x y => (comparisonH2 M).symm.injective (hc2.elim _ _)⟩⟩

private theorem quotient_lowCohomology_of_ambient_zero
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] (M : Rep ℤ G)
    (hN : TateAcyclic (Rep.res N.subtype M))
    (h1M : Subsingleton (groupCohomology.H1 M))
    (h2M : Subsingleton (groupCohomology.H2 M)) :
    Subsingleton (groupCohomology.H1 (M.quotientToInvariants N)) ∧
      Subsingleton (groupCohomology.H2 (M.quotientToInvariants N)) := by
  have hN1 := concreteH1_subsingleton_of_tateAcyclic _ hN
  have hc1M : Subsingleton (Inhomogeneous.H1 M) :=
    ⟨fun x y => (comparisonH1 M).injective (h1M.elim _ _)⟩
  have hc2M : Subsingleton (Inhomogeneous.H2 M) :=
    ⟨fun x y => (comparisonH2 M).injective (h2M.elim _ _)⟩
  have hinj1 := Inhomogeneous.InfRes.inflationH1_injective N M
  have hc1Q : Subsingleton (Inhomogeneous.H1 (M.quotientToInvariants N)) := by
    constructor
    intro x y
    apply hinj1
    exact hc1M.elim _ _
  have hinj2 : Function.Injective (Inhomogeneous.InfRes.inflationH2 N M) := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : Inhomogeneous.InfRes.inflationH2 N M (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ :=
      ((Inhomogeneous.InfRes.fiveTerm_exact N M).exact_at_H2Q (x - y)).1 hz
    have ha0 : a = 0 := by
      apply Subtype.ext
      exact hN1.elim _ _
    rw [← ha, ha0, map_zero]
  have hc2Q : Subsingleton (Inhomogeneous.H2 (M.quotientToInvariants N)) := by
    constructor
    intro x y
    apply hinj2
    exact hc2M.elim _ _
  exact
    ⟨⟨fun x y => (comparisonH1 (M.quotientToInvariants N)).symm.injective
        (hc1Q.elim _ _)⟩,
      ⟨fun x y => (comparisonH2 (M.quotientToInvariants N)).symm.injective
        (hc2Q.elim _ _)⟩⟩

private theorem lowCohomology_subsingleton_of_edge_acyclic
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] (M : Rep ℤ G)
    (hN : TateAcyclic (Rep.res N.subtype M))
    (hQ : TateAcyclic (M.quotientToInvariants N)) :
    Subsingleton (groupCohomology.H1 M) ∧
      Subsingleton (groupCohomology.H2 M) := by
  have hN1 := concreteH1_subsingleton_of_tateAcyclic _ hN
  have hN2 := concreteH2_subsingleton_of_tateAcyclic _ hN
  have hQ1 := concreteH1_subsingleton_of_tateAcyclic _ hQ
  have hQ2 := concreteH2_subsingleton_of_tateAcyclic _ hQ
  have hc1zero : ∀ x : Inhomogeneous.H1 M, x = 0 := by
    intro x
    have hr : Inhomogeneous.InfRes.fixedRestrictionH1 N M x = 0 := by
      apply Subtype.ext
      exact hN1.elim _ _
    obtain ⟨y, hy⟩ :=
      ((Inhomogeneous.InfRes.fiveTerm_exact N M).exact_at_H1G x).1 hr
    calc
      x = Inhomogeneous.InfRes.inflationH1 N M y := hy.symm
      _ = Inhomogeneous.InfRes.inflationH1 N M 0 :=
        congrArg _ (hQ1.elim y 0)
      _ = 0 := map_zero _
  have hc2zero : ∀ x : Inhomogeneous.H2 M, x = 0 := by
    intro x
    have hr : Inhomogeneous.restrictionH2 N.subtype M x = 0 := hN2.elim _ _
    obtain ⟨y, hy⟩ :=
      (Inhomogeneous.InfRes.inflation_restrictionH2_exact_of_H1_zero N M
        (fun z => hN1.elim z 0) x).1 hr
    calc
      x = Inhomogeneous.InfRes.inflationH2 N M y := hy.symm
      _ = Inhomogeneous.InfRes.inflationH2 N M 0 :=
        congrArg _ (hQ2.elim y 0)
      _ = 0 := map_zero _
  have hc1 : Subsingleton (Inhomogeneous.H1 M) :=
    ⟨fun x y => (hc1zero x).trans (hc1zero y).symm⟩
  have hc2 : Subsingleton (Inhomogeneous.H2 M) :=
    ⟨fun x y => (hc2zero x).trans (hc2zero y).symm⟩
  exact
    ⟨⟨fun x y => (comparisonH1 M).symm.injective (hc1.elim _ _)⟩,
      ⟨fun x y => (comparisonH2 M).symm.injective (hc2.elim _ _)⟩⟩

private theorem cyclic_tateAcyclic
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G)
    (h1 : Subsingleton (groupCohomology.H1 M))
    (h2 : Subsingleton (groupCohomology.H2 M)) : TateAcyclic M := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let gen := (IsCyclic.exists_generator (α := G)).choose
  have hgen := (IsCyclic.exists_generator (α := G)).choose_spec
  have ht0 : Subsingleton (tateCohomology M 0) := by
    have hc0 : Subsingleton (TateLowDegree.H0 M) := by
      constructor
      intro x y
      apply sub_eq_zero.mp
      induction x - y using QuotientAddGroup.induction_on with
      | H z =>
        apply (QuotientAddGroup.eq_zero_iff z).2
        let e : Inhomogeneous.invariants0 M →
            LinearMap.ker (Rep.applyAsHom M gen - 𝟙 M).hom.toLinearMap :=
          fun a => ⟨a, by
            rw [LinearMap.mem_ker]
            simpa [Rep.sub_hom, Rep.applyAsHom_apply, sub_eq_zero] using
              (Representation.mem_invariants_iff_of_forall_mem_zpowers
                M.ρ gen hgen a).1 a.2⟩
        have hz : Rep.FiniteCyclicGroup.groupCohomologyπEven
            M gen hgen 2 (by simp) (e z) = 0 := h2.elim _ _
        rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff] at hz
        obtain ⟨a, ha⟩ := hz
        exact ⟨a, ha⟩
    exact ⟨fun x y => (TateLowDegree.comparisonH0Tate M).symm.injective
      (hc0.elim _ _)⟩
  have htm : Subsingleton (tateCohomology M (-1)) := by
    have hcm : Subsingleton (TateLowDegree.HMinusOne M) := by
      constructor
      intro x y
      apply sub_eq_zero.mp
      induction x - y using QuotientAddGroup.induction_on with
      | H z =>
        apply (QuotientAddGroup.eq_zero_iff z).2
        let e : TateLowDegree.normKernel M →
            LinearMap.ker M.norm.hom.toLinearMap := fun a => ⟨a, a.2⟩
        have hz : Rep.FiniteCyclicGroup.groupCohomologyπOdd
            M gen hgen 1 (by simp) (e z) = 0 := h1.elim _ _
        rw [Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff] at hz
        obtain ⟨a, ha⟩ := hz
        change (z : M) ∈ TateLowDegree.augmentation M
        apply AddSubgroup.subset_closure
        refine ⟨gen, a, ?_⟩
        simpa [Rep.sub_hom, Rep.applyAsHom_apply] using ha.symm
    let e := (TateLowDegree.HMinusOne_equiv_tate M).some
    exact ⟨fun x y => e.symm.injective (hcm.elim _ _)⟩
  intro n
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact ht0
      | succ k =>
          let d := k + 1
          letI : NeZero d := ⟨by omega⟩
          let et := (TateCohomology.isoGroupCohomology d).app M
          by_cases he : Even d
          · let ep := Rep.FiniteCyclicGroup.groupCohomologyIsoEven M gen hgen d he
            let e2 := Rep.FiniteCyclicGroup.groupCohomologyIsoEven M gen hgen 2 (by simp)
            let e := et ≪≫ ep ≪≫ e2.symm
            exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
              (h2.elim _ _)⟩
          · have ho : Odd d := Nat.not_even_iff_odd.mp he
            let ep := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M gen hgen d ho
            let e1 := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M gen hgen 1 (by simp)
            let e := et ≪≫ ep ≪≫ e1.symm
            exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
              (h1.elim _ _)⟩
  | negSucc k =>
      cases k with
      | zero => exact htm
      | succ k =>
          let d := k + 1
          letI : NeZero d := ⟨by omega⟩
          let et := (TateCohomology.isoGroupHomology (-(d + 1 : ℤ)) d rfl).app M
          by_cases he : Even d
          · let ep := Rep.FiniteCyclicGroup.groupHomologyIsoEven M gen hgen d he
            let e1 := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M gen hgen 1 (by simp)
            let e := et ≪≫ ep ≪≫ e1.symm
            exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
              (h1.elim _ _)⟩
          · have ho : Odd d := Nat.not_even_iff_odd.mp he
            let ep := Rep.FiniteCyclicGroup.groupHomologyIsoOdd M gen hgen d ho
            let e2 := Rep.FiniteCyclicGroup.groupCohomologyIsoEven M gen hgen 2 (by simp)
            let e := et ≪≫ ep ≪≫ e2.symm
            exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
              (h2.elim _ _)⟩

private theorem groupCohomology_subsingleton_res_of_injective
    {G : Type} [Group G] (M : Rep ℤ G) (n : ℕ)
    (h : ∀ (S : Subgroup G) [Fintype S],
      Subsingleton (groupCohomology (Rep.res S.subtype M) n))
    {H : Type} [Group H] [Fintype H] (f : H →* G) (hf : Function.Injective f) :
    Subsingleton (groupCohomology (Rep.res f M) n) := by
  classical
  letI : Module ℤ M := M.hV2
  let R := f.range
  let eG : H ≃* R := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy => hf (congrArg Subtype.val hxy), f.rangeRestrict_surjective⟩
  let eL : (Rep.res f M).V ≃ₗ[ℤ] (Rep.res R.subtype M).V := LinearEquiv.refl ℤ M
  let e := groupCohomology_mapIso eG eL (fun g => by
    apply LinearMap.ext
    intro x
    rfl) n
  have hR := h R
  exact ⟨fun x y => (ModuleCat.mono_iff_injective e.hom).1 inferInstance
    (hR.elim _ _)⟩

private theorem lowCohomology_subsingleton_of_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (hM : TateAcyclic M) :
    Subsingleton (groupCohomology.H1 M) ∧
      Subsingleton (groupCohomology.H2 M) := by
  let e1 := (TateCohomology.isoGroupCohomology 1).app M
  let e2 := (TateCohomology.isoGroupCohomology 2).app M
  exact
    ⟨⟨fun x y => (ModuleCat.mono_iff_injective e1.inv).1 inferInstance
        ((hM 1).elim _ _)⟩,
      ⟨fun x y => (ModuleCat.mono_iff_injective e2.inv).1 inferInstance
        ((hM 2).elim _ _)⟩⟩

private theorem quotient_isCyclic_of_coatom
    {G : Type} [Group G] (N : Subgroup G) [N.Normal] (hN : IsCoatom N) :
    IsCyclic (G ⧸ N) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hN.lt_top
  let q : G ⧸ N := QuotientGroup.mk' N g
  refine ⟨q, ?_⟩
  let P : Subgroup G := Subgroup.comap (QuotientGroup.mk' N) (Subgroup.zpowers q)
  have hNP : N ≤ P := by
    intro x hx
    change QuotientGroup.mk' N x ∈ Subgroup.zpowers q
    have hx1 : QuotientGroup.mk' N x = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hgP : g ∈ P := Subgroup.mem_zpowers q
  have hPne : P ≠ N := fun h => hg (h ▸ hgP)
  have hNPlt : N < P := lt_of_le_of_ne hNP (Ne.symm hPne)
  have hPtop : P = ⊤ := hN.2 P hNPlt
  apply top_unique
  intro x _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  change a ∈ P
  rw [hPtop]
  trivial

private theorem upShift_restriction_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (S : Subgroup G) [Fintype S]
    (hM : TateAcyclic (Rep.res S.subtype M)) :
    TateAcyclic (Rep.res S.subtype (upShiftData M).shifted) := by
  let U := upShiftData M
  let C := ShortComplex.mk U.inclusion U.projection U.zero
  have hC := (Rep.shortExact_res S.subtype).2 U.exact
  have hmid : TateAcyclic (Rep.res S.subtype (shiftInduced M)) :=
    fun n => shiftInduced_tateAcyclic M S n
  exact (tateAcyclic_iff_of_middle hC hmid).mp hM

private theorem downShift_restriction_tateAcyclic
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (S : Subgroup G) [Fintype S]
    (hM : TateAcyclic (Rep.res S.subtype M)) :
    TateAcyclic (Rep.res S.subtype (downShiftData M).shifted) := by
  let D := downShiftData M
  let C := ShortComplex.mk D.inclusion D.projection D.zero
  have hC := (Rep.shortExact_res S.subtype).2 D.exact
  have hmid : TateAcyclic (Rep.res S.subtype (shiftInduced M)) :=
    fun n => shiftInduced_tateAcyclic M S n
  exact (tateAcyclic_iff_of_middle hC hmid).mpr hM

private theorem shiftInduced_quotient_tateAcyclic
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] [IsCyclic (G ⧸ N)] (M : Rep ℤ G) :
    TateAcyclic ((shiftInduced M).quotientToInvariants N) := by
  have hI := shiftInduced_tateAcyclic_self M
  have hIN : TateAcyclic (Rep.res N.subtype (shiftInduced M)) :=
    fun n => shiftInduced_tateAcyclic M N n
  have hlowI := lowCohomology_subsingleton_of_tateAcyclic _ hI
  have hlowQ := quotient_lowCohomology_of_ambient_zero N (shiftInduced M)
    hIN hlowI.1 hlowI.2
  exact cyclic_tateAcyclic _ hlowQ.1 hlowQ.2

private theorem upShift_edge_good
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] [IsCyclic (G ⧸ N)] (M : Rep ℤ G)
    (hN : TateAcyclic (Rep.res N.subtype M))
    (hQ : TateAcyclic (M.quotientToInvariants N)) :
    TateAcyclic (Rep.res N.subtype (upShiftData M).shifted) ∧
      TateAcyclic ((upShiftData M).shifted.quotientToInvariants N) := by
  let U := upShiftData M
  have hUN := upShift_restriction_tateAcyclic M N hN
  let C := ShortComplex.mk U.inclusion U.projection U.zero
  have hH1 := concreteH1_subsingleton_of_tateAcyclic _ hN
  have hCQ := quotientToInvariants_shortExact_of_H1_zero N (X := C)
    U.function_exact U.inclusion_injective U.projection_surjective hH1
  have hIQ := shiftInduced_quotient_tateAcyclic N M
  exact ⟨hUN, (tateAcyclic_iff_of_middle hCQ hIQ).mp hQ⟩

private theorem downShift_edge_good
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] [IsCyclic (G ⧸ N)] (M : Rep ℤ G)
    (hN : TateAcyclic (Rep.res N.subtype M))
    (hQ : TateAcyclic (M.quotientToInvariants N)) :
    TateAcyclic (Rep.res N.subtype (downShiftData M).shifted) ∧
      TateAcyclic ((downShiftData M).shifted.quotientToInvariants N) := by
  let D := downShiftData M
  have hDN := downShift_restriction_tateAcyclic M N hN
  let C := ShortComplex.mk D.inclusion D.projection D.zero
  have hH1 := concreteH1_subsingleton_of_tateAcyclic _ hDN
  have hCQ := quotientToInvariants_shortExact_of_H1_zero N (X := C)
    D.function_exact D.inclusion_injective D.projection_surjective hH1
  have hIQ := shiftInduced_quotient_tateAcyclic N M
  exact ⟨hDN, (tateAcyclic_iff_of_middle hCQ hIQ).mpr hQ⟩

private theorem finiteGroup_tateAcyclic_of_lowCohomology
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (h1 : ∀ {H : Type} [Group H] [Fintype H] (f : H →* G),
      Function.Injective f → Subsingleton (groupCohomology.H1 (Rep.res f M)))
    (h2 : ∀ {H : Type} [Group H] [Fintype H] (f : H →* G),
      Function.Injective f → Subsingleton (groupCohomology.H2 (Rep.res f M))) :
    TateAcyclic M := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (H : Type) [Group H] [Fintype H], Nat.card H = n →
      ∀ X : Rep ℤ H,
        (∀ {K : Type} [Group K] [Fintype K] (f : K →* H),
          Function.Injective f →
            Subsingleton (groupCohomology.H1 (Rep.res f X))) →
        (∀ {K : Type} [Group K] [Fintype K] (f : K →* H),
          Function.Injective f →
            Subsingleton (groupCohomology.H2 (Rep.res f X))) →
        TateAcyclic X
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro H _ _ hcardEq X h1X h2X
      by_cases hcyc : IsCyclic H
      · letI : IsCyclic H := hcyc
        have hX1 := h1X (MonoidHom.id H) Function.injective_id
        have hX2 := h2X (MonoidHom.id H) Function.injective_id
        change Subsingleton (groupCohomology.H1 X) at hX1
        change Subsingleton (groupCohomology.H2 X) at hX2
        exact cyclic_tateAcyclic X hX1 hX2
      · have hcardH : 1 < Nat.card H := by
          rw [Nat.card_eq_fintype_card]
          by_contra hn
          haveI : Subsingleton H :=
            Fintype.card_le_one_iff_subsingleton.mp (Nat.le_of_not_gt hn)
          exact hcyc isCyclic_of_subsingleton
        have hproper (S : Subgroup H) [Fintype S]
            (hS : Nat.card S < Nat.card H) :
            TateAcyclic (Rep.res S.subtype X) := by
          have hSn : Nat.card S < n := by simpa [← hcardEq] using hS
          refine ih (Nat.card S) hSn S rfl (Rep.res S.subtype X) ?_ ?_
          · intro K _ _ f hf
            exact h1X (S.subtype.comp f) (S.subtype_injective.comp hf)
          · intro K _ _ f hf
            exact h2X (S.subtype.comp f) (S.subtype_injective.comp hf)
        by_cases hpg : ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p H
        · obtain ⟨p, hp, hpG⟩ := hpg
          letI : Fact (Nat.Prime p) := ⟨hp⟩
          letI : IsPGroup p H := hpG
          letI : Group.IsNilpotent H := hpG.isNilpotent
          have hbotne : (⊥ : Subgroup H) ≠ ⊤ := by
            intro hb
            have hc := congrArg (fun S : Subgroup H => Nat.card S) hb
            have : Nat.card H = 1 := by simpa using hc.symm
            omega
          obtain hbot | ⟨N, hNcoat, -⟩ :=
            eq_top_or_exists_le_coatom (⊥ : Subgroup H)
          · exact (hbotne hbot).elim
          · have hnall : ∀ K : Subgroup H, IsCoatom K → K.Normal :=
              (Group.isNilpotent_of_finite_tfae.out 0 2 rfl rfl).mp inferInstance
            letI : N.Normal := hnall N hNcoat
            letI : Fintype N := Fintype.ofFinite N
            letI : Fintype (H ⧸ N) := Fintype.ofFinite (H ⧸ N)
            letI : IsCyclic (H ⧸ N) := quotient_isCyclic_of_coatom N hNcoat
            have hNdiv : Nat.card N ∣ Nat.card H :=
              ⟨N.index, N.card_mul_index.symm⟩
            have hNle : Nat.card N ≤ Nat.card H :=
              Nat.le_of_dvd Nat.card_pos hNdiv
            have hNne : Nat.card N ≠ Nat.card H := by
              intro heq
              exact hNcoat.ne_top (Subgroup.eq_top_of_card_eq N heq)
            have hNlt : Nat.card N < Nat.card H := lt_of_le_of_ne hNle hNne
            have hNX := hproper N hNlt
            have hX1 := h1X (MonoidHom.id H) Function.injective_id
            have hX2 := h2X (MonoidHom.id H) Function.injective_id
            change Subsingleton (groupCohomology.H1 X) at hX1
            change Subsingleton (groupCohomology.H2 X) at hX2
            have hlowQ := quotient_lowCohomology_of_ambient_zero N X hNX hX1 hX2
            have hQX := cyclic_tateAcyclic (X.quotientToInvariants N)
              hlowQ.1 hlowQ.2
            let Good : Rep ℤ H → Prop := fun Y =>
              TateAcyclic (Rep.res N.subtype Y) ∧
                TateAcyclic (Y.quotientToInvariants N)
            refine tateAcyclic_of_shift_stable Good X ?_ ?_ ?_ ⟨hNX, hQX⟩
            · intro Y hY
              exact lowCohomology_subsingleton_of_edge_acyclic N Y hY.1 hY.2
            · intro Y hY
              exact upShift_edge_good N Y hY.1 hY.2
            · intro Y hY
              exact downShift_edge_good N Y hY.1 hY.2
        · have hnp : ∀ (p : ℕ), Nat.Prime p → ¬ IsPGroup p H := by
            intro p hp hpG
            exact hpg ⟨p, hp, hpG⟩
          let Good : Rep ℤ H → Prop := fun Y =>
            ∀ (S : Subgroup H) [Fintype S], Nat.card S < Nat.card H →
              TateAcyclic (Rep.res S.subtype Y)
          have hGoodX : Good X := fun S _ hS => hproper S hS
          refine tateAcyclic_of_shift_stable Good X ?_ ?_ ?_ hGoodX
          · intro Y hY
            exact lowCohomology_of_proper_subgroups_acyclic hcardH hnp Y hY
          · intro Y hY S _ hS
            exact upShift_restriction_tateAcyclic Y S (hY S hS)
          · intro Y hY S _ hS
            exact downShift_restriction_tateAcyclic Y S (hY S hS)
  exact hP (Nat.card G) G rfl M h1 h2

/--
**C06**, proof of Theorem `thm:tate-reciprocity`: the cohomological-triviality criterion, with no
finiteness hypothesis on the coefficient module.
-/
theorem cohomologicallyTrivial_of_H1_H2_zero (M : Rep ℤ G)
    (h1 : ∀ (S : Subgroup G) [Fintype S],
      Subsingleton (groupCohomology.H1 (Rep.res S.subtype M)))
    (h2 : ∀ (S : Subgroup G) [Fintype S],
      Subsingleton (groupCohomology.H2 (Rep.res S.subtype M))) :
    CohomologicallyTrivial M := by
  intro S _ n
  have hS := finiteGroup_tateAcyclic_of_lowCohomology (Rep.res S.subtype M)
    (fun f hf => groupCohomology_subsingleton_res_of_injective M 1 h1
      (S.subtype.comp f) (S.subtype_injective.comp hf))
    (fun f hf => groupCohomology_subsingleton_res_of_injective M 2 h2
      (S.subtype.comp f) (S.subtype_injective.comp hf))
  exact hS n

/-- A normalized cocycle condition in the concrete complex. -/
def IsNormalizedCocycle2 (M : Rep ℤ G) (a : Inhomogeneous.C2 M) : Prop :=
  a ∈ Inhomogeneous.cocycles2 M

/-- The class of a normalized concrete two-cocycle. -/
def cocycleClass2 (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) : Inhomogeneous.H2 M :=
  QuotientAddGroup.mk ⟨a, ha⟩

variable [Fintype G]

/-- The row sum `Σₓ a(x,g)`. -/
def rowSum (M : Rep ℤ G) (a : Inhomogeneous.C2 M) (g : G) : M :=
  ∑ x : G, a x g

/--
**C08**, final calculation in Theorem `thm:tate-reciprocity`: row sums of a normalized cocycle
are invariant.
-/
theorem rowSum_invariant (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) (g : G) :
    rowSum M a g ∈ Inhomogeneous.invariants0 M := by
  intro y
  change M.ρ y (∑ x : G, a x g) = ∑ x : G, a x g
  rw [map_sum]
  have hc (x : G) :
      M.ρ y (a x g) = a (y * x) g - a y (x * g) + a y x := by
    have hmem := ha.1
    change Inhomogeneous.d2 M a = 0 at hmem
    have h := congrFun (congrFun (congrFun hmem y) x) g
    change M.ρ y (a x g) - a (y * x) g + a y (x * g) - a y x = 0 at h
    calc
      M.ρ y (a x g) =
          (M.ρ y (a x g) - a (y * x) g + a y (x * g) - a y x) +
            a (y * x) g - a y (x * g) + a y x := by abel
      _ = a (y * x) g - a y (x * g) + a y x := by rw [h]; abel
  calc
    (∑ x : G, M.ρ y (a x g)) =
        ∑ x : G, (a (y * x) g - a y (x * g) + a y x) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hc x
    _ = (∑ x : G, a (y * x) g) - (∑ x : G, a y (x * g)) +
          ∑ x : G, a y x := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ x : G, a x g) - (∑ x : G, a y x) + ∑ x : G, a y x := by
          have hleft : (∑ x : G, a (y * x) g) = ∑ x : G, a x g := by
            simpa using Equiv.sum_comp (Equiv.mulLeft y) (fun x => a x g)
          have hright : (∑ x : G, a y (x * g)) = ∑ x : G, a y x := by
            simpa using Equiv.sum_comp (Equiv.mulRight g) (fun x => a y x)
          rw [hleft, hright]
    _ = ∑ x : G, a x g := by abel

/-- A row sum as an invariant element. -/
def rowSumInvariant (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) (g : G) : Inhomogeneous.invariants0 M :=
  ⟨rowSum M a g, rowSum_invariant M a ha g⟩

/-- The row sum modulo representation norms. -/
def rowSumClass (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) (g : G) : TateLowDegree.H0 M :=
  QuotientAddGroup.mk (rowSumInvariant M a ha g)

/-- Two concrete cocycles differ by a coboundary. -/
def Cohomologous2 (M : Rep ℤ G) (a b : Inhomogeneous.C2 M) : Prop :=
  ∃ c : Inhomogeneous.C1 M, b - a = Inhomogeneous.d1 M c

/--
**C08**, final calculation in Theorem `thm:tate-reciprocity`: row sums are additive modulo norms.
-/
theorem rowSumClass_mul (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) (g h : G) :
    rowSumClass M a ha (g * h) = rowSumClass M a ha g + rowSumClass M a ha h := by
  letI : Module ℤ M := M.hV2
  change (↑(rowSumInvariant M a ha (g * h)) : TateLowDegree.H0 M) =
    (↑(rowSumInvariant M a ha g) : TateLowDegree.H0 M) +
      (↑(rowSumInvariant M a ha h) : TateLowDegree.H0 M)
  rw [← QuotientAddGroup.mk_add]
  apply QuotientAddGroup.eq.mpr
  change -rowSumInvariant M a ha (g * h) +
      (rowSumInvariant M a ha g + rowSumInvariant M a ha h) ∈
    TateLowDegree.normRangeInInvariants M
  refine ⟨a g h, ?_⟩
  change M.norm.hom (a g h) =
    -(∑ x : G, a x (g * h)) + ((∑ x : G, a x g) + ∑ x : G, a x h)
  rw [Rep.norm_apply, Representation.norm]
  simp only [LinearMap.sum_apply]
  have hc (x : G) :
      M.ρ x (a g h) = a (x * g) h - a x (g * h) + a x g := by
    have hmem := ha.1
    change Inhomogeneous.d2 M a = 0 at hmem
    have hx := congrFun (congrFun (congrFun hmem x) g) h
    change M.ρ x (a g h) - a (x * g) h + a x (g * h) - a x g = 0 at hx
    calc
      M.ρ x (a g h) =
          (M.ρ x (a g h) - a (x * g) h + a x (g * h) - a x g) +
            a (x * g) h - a x (g * h) + a x g := by abel
      _ = a (x * g) h - a x (g * h) + a x g := by rw [hx]; abel
  calc
    (∑ x : G, M.ρ x (a g h)) =
        ∑ x : G, (a (x * g) h - a x (g * h) + a x g) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hc x
    _ = (∑ x : G, a (x * g) h) - (∑ x : G, a x (g * h)) +
          ∑ x : G, a x g := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ x : G, a x h) - (∑ x : G, a x (g * h)) +
          ∑ x : G, a x g := by
          have hr : (∑ x : G, a (x * g) h) = ∑ x : G, a x h := by
            simpa using Equiv.sum_comp (Equiv.mulRight g) (fun x => a x h)
          rw [hr]
    _ = -(∑ x : G, a x (g * h)) + ((∑ x : G, a x g) + ∑ x : G, a x h) := by
          abel

/--
**C08**, final calculation in Theorem `thm:tate-reciprocity`: changing a cocycle by a coboundary
does not change its row-sum map.
-/
theorem rowSumClass_coboundary_independent (M : Rep ℤ G)
    (a b : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hb : IsNormalizedCocycle2 M b) (hab : Cohomologous2 M a b) :
    ∀ g, rowSumClass M a ha g = rowSumClass M b hb g := by
  letI : Module ℤ M := M.hV2
  rcases hab with ⟨c, hc⟩
  intro g
  change (↑(rowSumInvariant M a ha g) : TateLowDegree.H0 M) =
    (↑(rowSumInvariant M b hb g) : TateLowDegree.H0 M)
  apply QuotientAddGroup.eq.mpr
  change -rowSumInvariant M a ha g + rowSumInvariant M b hb g ∈
    TateLowDegree.normRangeInInvariants M
  refine ⟨c g, ?_⟩
  change M.norm.hom (c g) = -(∑ x : G, a x g) + ∑ x : G, b x g
  rw [Rep.norm_apply, Representation.norm]
  simp only [LinearMap.sum_apply]
  have hρ (x : G) :
      M.ρ x (c g) = (b x g - a x g) + c (x * g) - c x := by
    have hx := congrFun (congrFun hc x) g
    change b x g - a x g = M.ρ x (c g) - c (x * g) + c x at hx
    calc
      M.ρ x (c g) =
          (M.ρ x (c g) - c (x * g) + c x) + c (x * g) - c x := by abel
      _ = (b x g - a x g) + c (x * g) - c x := by rw [← hx]
  calc
    (∑ x : G, M.ρ x (c g)) =
        ∑ x : G, ((b x g - a x g) + c (x * g) - c x) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hρ x
    _ = ((∑ x : G, b x g) - ∑ x : G, a x g) +
          (∑ x : G, c (x * g)) - ∑ x : G, c x := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_sub_distrib]
    _ = ((∑ x : G, b x g) - ∑ x : G, a x g) +
          (∑ x : G, c x) - ∑ x : G, c x := by
          have hr : (∑ x : G, c (x * g)) = ∑ x : G, c x := by
            simpa using Equiv.sum_comp (Equiv.mulRight g) c
          rw [hr]
    _ = -(∑ x : G, a x g) + ∑ x : G, b x g := by abel

/--
**C08**, final calculation in Theorem `thm:tate-reciprocity`: the row-sum map kills commutators
and therefore factors through `Gᵃᵇ`.
-/
theorem rowSum_factors_abelianization (M : Rep ℤ G) (a : Inhomogeneous.C2 M)
    (ha : IsNormalizedCocycle2 M a) :
    ∃ f : Additive (Abelianization G) →+ TateLowDegree.H0 M,
      ∀ g, f (Additive.ofMul (Abelianization.of g)) = rowSumClass M a ha g := by
  let φ : G →* Multiplicative (TateLowDegree.H0 M) :=
    { toFun := fun g => Multiplicative.ofAdd (rowSumClass M a ha g)
      map_one' := by
        apply Multiplicative.toAdd.injective
        change rowSumClass M a ha 1 = 0
        have h := rowSumClass_mul M a ha 1 1
        rw [one_mul] at h
        apply add_left_cancel (a := rowSumClass M a ha 1)
        simpa using h.symm
      map_mul' := fun g h => by
        apply Multiplicative.toAdd.injective
        exact rowSumClass_mul M a ha g h }
  let f : Additive (Abelianization G) →+ TateLowDegree.H0 M :=
    MonoidHom.toAdditiveLeft (Abelianization.lift φ)
  refine ⟨f, ?_⟩
  intro g
  change Multiplicative.toAdd (Abelianization.lift φ (Abelianization.of g)) = _
  rw [Abelianization.lift_apply_of]
  rfl

/-- The hypotheses of Tate's abstract reciprocity theorem, uniformly on subgroups. -/
structure Hypotheses (M : Rep ℤ G) : Prop where
  /-- `H¹(S,M)=0` for every subgroup. -/
  h1_zero : ∀ (S : Subgroup G) [Fintype S],
    Subsingleton (groupCohomology.H1 (Rep.res S.subtype M))
  /-- `H²(S,M)` contains an element of exact order `|S|`. -/
  h2_generator : ∀ (S : Subgroup G) [Fintype S],
    ∃ α : groupCohomology.H2 (Rep.res S.subtype M),
      addOrderOf α = Nat.card S ∧ ∀ β, ∃ n : ℤ, n • α = β

private abbrev trivialBottomInteger : Rep ℤ (↥(⊥ : Subgroup G)) :=
  Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ

private def barRegularInducedSeed :
    trivialBottomInteger (G := G) ⟶
      Rep.res (⊥ : Subgroup G).subtype (barRegular G) := by
  let L : ℤ →ₗ[ℤ] barRegular G :=
    { toFun := fun n => n • (MonoidAlgebra.single 1 1 : MonoidAlgebra ℤ G)
      map_add' := by intros; exact add_smul ..
      map_smul' := by
        intros m x
        change (m * x) • (MonoidAlgebra.single 1 1 : MonoidAlgebra ℤ G) =
          m • x • (MonoidAlgebra.single 1 1 : MonoidAlgebra ℤ G)
        exact mul_smul .. }
  exact Rep.ofHom ⟨L, fun g => by
    apply LinearMap.ext
    intro n
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.2)
    subst g
    simp [L]⟩

private def inducedToBarRegular : InducedFromTrivial G ℤ ⟶ barRegular G :=
  (Rep.indResHomEquiv (⊥ : Subgroup G).subtype
      (trivialBottomInteger (G := G)) (barRegular G)).symm
    (barRegularInducedSeed (G := G))

private lemma inducedToBarRegular_mk (h : G) (n : ℤ) :
    (inducedToBarRegular (G := G)).hom
      (Representation.IndV.mk (⊥ : Subgroup G).subtype
        (trivialBottomInteger (G := G)).ρ h n) =
      MonoidAlgebra.single h⁻¹ n := by
  let e := Rep.indResHomEquiv (⊥ : Subgroup G).subtype
    (trivialBottomInteger (G := G)) (barRegular G)
  have he : e (inducedToBarRegular (G := G)) = barRegularInducedSeed (G := G) :=
    e.apply_symm_apply _
  have he1 := congrArg (fun q : trivialBottomInteger (G := G) ⟶
      Rep.res (⊥ : Subgroup G).subtype (barRegular G) => q.hom n) he
  change (inducedToBarRegular (G := G)).hom
    (Representation.IndV.mk (⊥ : Subgroup G).subtype
      (trivialBottomInteger (G := G)).ρ 1 n) =
        (barRegularInducedSeed (G := G)).hom n at he1
  calc
    _ = (inducedToBarRegular (G := G)).hom ((InducedFromTrivial G ℤ).ρ h⁻¹
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (trivialBottomInteger (G := G)).ρ 1 n)) := by
      rw [Representation.ind_mk]
      simp
    _ = (barRegular G).ρ h⁻¹ ((inducedToBarRegular (G := G)).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (trivialBottomInteger (G := G)).ρ 1 n)) :=
      Rep.hom_comm_apply _ _ _
    _ = (barRegular G).ρ h⁻¹ ((barRegularInducedSeed (G := G)).hom n) := by
      rw [he1]
    _ = _ := by
      change Representation.ofMulAction ℤ G G h⁻¹
        (n • (Finsupp.single 1 1 : G →₀ ℤ)) = Finsupp.single h⁻¹ n
      rw [map_smul, Representation.ofMulAction_single]
      simp

private def barRegularToInducedAdd : barRegular G →+ InducedFromTrivial G ℤ :=
  (Finsupp.liftAddHom fun g : G =>
      (Representation.IndV.mk (⊥ : Subgroup G).subtype
        (trivialBottomInteger (G := G)).ρ g⁻¹).toAddMonoidHom).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

private def barRegularToInducedLinear : barRegular G →ₗ[ℤ] InducedFromTrivial G ℤ :=
  (barRegularToInducedAdd (G := G)).toIntLinearMap

private lemma barRegularToInducedLinear_single (g : G) (n : ℤ) :
    barRegularToInducedLinear (G := G) (MonoidAlgebra.single g n) =
      Representation.IndV.mk (⊥ : Subgroup G).subtype
        (trivialBottomInteger (G := G)).ρ g⁻¹ n := by
  change (Finsupp.single g n).sum (fun x n =>
    Representation.IndV.mk (⊥ : Subgroup G).subtype
      (trivialBottomInteger (G := G)).ρ x⁻¹ n) = _
  rw [Finsupp.sum_single_index]
  exact LinearMap.map_zero _

private def barRegularToInduced : barRegular G ⟶ InducedFromTrivial G ℤ :=
  Rep.ofHom ⟨barRegularToInducedLinear (G := G), fun g => by
    apply LinearMap.ext
    intro z
    change barRegularToInducedLinear (G := G) ((barRegular G).ρ g z) =
      (InducedFromTrivial G ℤ).ρ g (barRegularToInducedLinear (G := G) z)
    induction z using MonoidAlgebra.induction_on with
    | hM h =>
        rw [MonoidAlgebra.of_apply, Representation.ofMulAction_single,
          barRegularToInducedLinear_single, barRegularToInducedLinear_single,
          Representation.ind_mk]
        simp [smul_eq_mul]
    | hadd x y hx hy =>
        calc
          _ = barRegularToInducedLinear (G := G)
              ((barRegular G).ρ g x + (barRegular G).ρ g y) :=
            congrArg _ (((barRegular G).ρ g).map_add x y)
          _ = barRegularToInducedLinear (G := G) ((barRegular G).ρ g x) +
              barRegularToInducedLinear (G := G) ((barRegular G).ρ g y) :=
            (barRegularToInducedLinear (G := G)).map_add _ _
          _ = (InducedFromTrivial G ℤ).ρ g (barRegularToInducedLinear (G := G) x) +
              (InducedFromTrivial G ℤ).ρ g (barRegularToInducedLinear (G := G) y) :=
            congrArg₂ (· + ·) hx hy
          _ = (InducedFromTrivial G ℤ).ρ g
              (barRegularToInducedLinear (G := G) x +
                barRegularToInducedLinear (G := G) y) :=
            (((InducedFromTrivial G ℤ).ρ g).map_add _ _).symm
          _ = _ := congrArg _ ((barRegularToInducedLinear (G := G)).map_add x y).symm
    | hsmul n x hx =>
        change (barRegularToInducedAdd (G := G))
            ((barRegular G).ρ g
              ((inferInstance : Module ℤ (MonoidAlgebra ℤ G)).smul n x)) =
          (InducedFromTrivial G ℤ).ρ g
            ((barRegularToInducedAdd (G := G))
              ((inferInstance : Module ℤ (MonoidAlgebra ℤ G)).smul n x))
        rw [int_smul_eq_zsmul]
        have hx' := hx
        change (barRegularToInducedAdd (G := G)) ((barRegular G).ρ g x) =
          (InducedFromTrivial G ℤ).ρ g ((barRegularToInducedAdd (G := G)) x) at hx'
        calc
          _ = (barRegularToInducedAdd (G := G)) (n • (barRegular G).ρ g x) :=
            congrArg _ (map_zsmul ((barRegular G).ρ g) n x)
          _ = n • (barRegularToInducedAdd (G := G)) ((barRegular G).ρ g x) :=
            map_zsmul (barRegularToInducedAdd (G := G)) n _
          _ = n • (InducedFromTrivial G ℤ).ρ g
              ((barRegularToInducedAdd (G := G)) x) := congrArg (n • ·) hx'
          _ = (InducedFromTrivial G ℤ).ρ g
              (n • (barRegularToInducedAdd (G := G)) x) :=
            (map_zsmul ((InducedFromTrivial G ℤ).ρ g) n _).symm
          _ = _ := congrArg _ (map_zsmul (barRegularToInducedAdd (G := G)) n x).symm⟩

private def barRegularIsoInducedFromTrivial : InducedFromTrivial G ℤ ≅ barRegular G where
  hom := inducedToBarRegular (G := G)
  inv := barRegularToInduced (G := G)
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Representation.IndV.hom_ext (⊥ : Subgroup G).subtype
      (trivialBottomInteger (G := G)).ρ
    intro h
    apply LinearMap.ext
    intro n
    change (barRegularToInduced (G := G)).hom
        ((inducedToBarRegular (G := G)).hom
          (Representation.IndV.mk (⊥ : Subgroup G).subtype
            (trivialBottomInteger (G := G)).ρ h n)) = _
    rw [inducedToBarRegular_mk]
    change barRegularToInducedLinear (G := G) (MonoidAlgebra.single h⁻¹ n) = _
    rw [barRegularToInducedLinear_single]
    change Representation.IndV.mk (⊥ : Subgroup G).subtype
      (trivialBottomInteger (G := G)).ρ h⁻¹⁻¹ n =
        Representation.IndV.mk (⊥ : Subgroup G).subtype
          (trivialBottomInteger (G := G)).ρ h n
    rw [inv_inv]
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro h
    apply LinearMap.ext
    intro n
    change (inducedToBarRegular (G := G)).hom
        ((barRegularToInduced (G := G)).hom (MonoidAlgebra.single h n)) = _
    change (inducedToBarRegular (G := G)).hom
        (barRegularToInducedLinear (G := G) (MonoidAlgebra.single h n)) = _
    rw [barRegularToInducedLinear_single, inducedToBarRegular_mk, inv_inv]
    change MonoidAlgebra.single h n =
      (LinearMap.id (R := ℤ) (M := MonoidAlgebra ℤ G)) (MonoidAlgebra.single h n)
    rw [LinearMap.id_apply]

private theorem barRegular_tateAcyclic (S : Subgroup G) [Fintype S] (n : ℤ) :
    Subsingleton (tateCohomology (Rep.res S.subtype (barRegular G)) n) := by
  let e := (tateCohomologyFunctor n).mapIso
    ((Rep.resFunctor S.subtype).mapIso (barRegularIsoInducedFromTrivial (G := G)))
  have h := inducedFromTrivial_tateAcyclic G ℤ S n
  exact ⟨fun x y => (ModuleCat.mono_iff_injective e.inv).1 inferInstance (h.elim _ _)⟩

private theorem barRegular_tateAcyclic_self : TateAcyclic (barRegular G) := by
  let e0 : Rep.res (⊥ : Subgroup G).subtype (Rep.trivial ℤ G ℤ) ≅
      Rep.trivial ℤ (⊥ : Subgroup G) ℤ := by
    apply Rep.mkIso
    exact Representation.Equiv.mk (LinearEquiv.refl ℤ ℤ) (fun g => by
      apply LinearMap.ext
      intro n
      have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
      simp [Rep.res, hg])
  let eI := (Rep.indFunctor ℤ (⊥ : Subgroup G).subtype).mapIso e0
  intro n
  let e := (tateCohomologyFunctor n).mapIso
    (eI ≪≫ barRegularIsoInducedFromTrivial (G := G))
  have h := shiftInduced_tateAcyclic_self (Rep.trivial ℤ G ℤ) n
  exact ⟨fun x y => (ModuleCat.mono_iff_injective e.inv).1 inferInstance (h.elim _ _)⟩

private theorem restrictedClass_is_generator
    (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (S : Subgroup G) [Fintype S] :
    let αS := Inhomogeneous.restrictionH2 S.subtype M α
    addOrderOf αS = Nat.card S ∧ ∀ β, ∃ n : ℤ, n • αS = β := by
  let αS := Inhomogeneous.restrictionH2 S.subtype M α
  obtain ⟨γ, hγorder, hγgen⟩ := hM.h2_generator S
  have horder_dvd : addOrderOf αS ∣ Nat.card S := by
    have hmem : comparisonH2 (Rep.res S.subtype M) αS ∈
        AddSubgroup.zmultiples γ :=
      AddSubgroup.mem_zmultiples_iff.mpr
        (hγgen (comparisonH2 (Rep.res S.subtype M) αS))
    have hd := addOrderOf_dvd_of_mem_zmultiples hmem
    rw [(comparisonH2 (Rep.res S.subtype M)).addOrderOf_eq, hγorder] at hd
    exact hd
  have hcard_dvd_of_nsmul_eq_zero (n : ℕ) (hn : n • αS = 0) :
      Nat.card S ∣ n := by
    letI : Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _
    let T := reciprocitySubgroupTransversal S
    have hcor := Inhomogeneous.Transfer.corH2_restriction T M α
    have hncor : n • (S.index • α) = 0 := by
      rw [← hcor, ← map_nsmul, hn, map_zero]
    have hd : addOrderOf α ∣ n * S.index :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        simpa only [smul_smul] using hncor)
    rw [hα, ← S.card_mul_index] at hd
    exact (Nat.mul_dvd_mul_iff_right
      (Nat.pos_of_ne_zero S.index_ne_zero_of_finite)).mp hd
  have hcard_dvd_order : Nat.card S ∣ addOrderOf αS :=
    hcard_dvd_of_nsmul_eq_zero (addOrderOf αS)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd_rfl)
  have horder : addOrderOf αS = Nat.card S :=
    Nat.dvd_antisymm horder_dvd hcard_dvd_order
  have hcardMathlib :
      Nat.card (groupCohomology.H2 (Rep.res S.subtype M)) = Nat.card S := by
    have hγcard := addOrderOf_eq_card_of_forall_mem_zmultiples
      (g := γ) (fun β => AddSubgroup.mem_zmultiples_iff.mpr (hγgen β))
    exact hγcard.symm.trans hγorder
  have hcardConcrete :
      Nat.card (Inhomogeneous.H2 (Rep.res S.subtype M)) = Nat.card S :=
    (Nat.card_congr (comparisonH2 (Rep.res S.subtype M)).toEquiv).trans hcardMathlib
  letI : Finite (Inhomogeneous.H2 (Rep.res S.subtype M)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardConcrete]; exact Nat.card_pos.ne')
  have htop : AddSubgroup.zmultiples αS = ⊤ := by
    apply (AddSubgroup.card_eq_iff_eq_top (AddSubgroup.zmultiples αS)).mp
    rw [Nat.card_zmultiples, horder, hcardConcrete]
  refine ⟨horder, fun β => ?_⟩
  apply AddSubgroup.mem_zmultiples_iff.mp
  rw [htop]
  trivial

private theorem H1_card_nsmul_eq_zero
    {H : Type} [Group H] [Fintype H] (N : Rep ℤ H)
    (x : groupCohomology.H1 N) : Nat.card H • x = 0 := by
  let B : Subgroup H := ⊥
  have hz : IsZero (groupCohomology.H1 (Rep.res B.subtype N)) :=
    isZero_groupCohomology_succ_of_subsingleton (Rep.res B.subtype N) 0
  have hbMath : Subsingleton (groupCohomology.H1 (Rep.res B.subtype N)) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have hb : Subsingleton (Inhomogeneous.H1 (Rep.res B.subtype N)) :=
    ⟨fun u v => (comparisonH1 (Rep.res B.subtype N)).injective (hbMath.elim _ _)⟩
  have hx0 := H1_index_smul_eq_zero_of_restriction_zero B N hb
    ((comparisonH1 N).symm x)
  rw [show B.index = Nat.card H from Subgroup.index_bot] at hx0
  have := congrArg (comparisonH1 N) hx0
  simpa using this

private theorem restrictedAugmentationIdeal_H1_isCyclic
    (S : Subgroup G) [Fintype S] :
    ∃ u : groupCohomology.H1 (Rep.res S.subtype (barAugmentationIdeal G)),
      ∀ x, ∃ n : ℤ, n • u = x := by
  let A := (barAugmentationSequence G).map (Rep.resFunctor S.subtype)
  have hA : A.ShortExact :=
    (Rep.shortExact_res S.subtype).2 (barAugmentationSequence_shortExact (G := G))
  have hmidTate :
      Subsingleton (tateCohomology (Rep.res S.subtype (barRegular G)) 1) :=
    barRegular_tateAcyclic (G := G) S 1
  let e1 := (TateCohomology.isoGroupCohomology 1).app
    (Rep.res S.subtype (barRegular G))
  have hmid : Subsingleton
      (groupCohomology.H1 (Rep.res S.subtype (barRegular G))) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective e1.inv).1 inferInstance
      (hmidTate.elim _ _)⟩
  let Z := Rep.res S.subtype (Rep.trivial ℤ G ℤ)
  let oneInv : Z.ρ.invariants := ⟨1, by intro s; rfl⟩
  let e0 := groupCohomology.H0Iso Z
  let one0 : groupCohomology.H0 Z := e0.inv oneInv
  let u : groupCohomology.H1 (Rep.res S.subtype (barAugmentationIdeal G)) :=
    groupCohomology.δ hA 0 1 rfl one0
  have hexact : Function.Exact
      (groupCohomology.mapShortComplex₁ hA (i := 0) (j := 1) rfl).f
      (groupCohomology.mapShortComplex₁ hA (i := 0) (j := 1) rfl).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (groupCohomology.mapShortComplex₁ hA (i := 0) (j := 1) rfl)).mp
        (groupCohomology.mapShortComplex₁_exact hA (i := 0) (j := 1) rfl)
  refine ⟨u, fun x => ?_⟩
  have hx0 : (groupCohomology.mapShortComplex₁ hA
      (i := 0) (j := 1) rfl).g x = 0 :=
    hmid.elim _ _
  obtain ⟨z, hz⟩ := (hexact x).mp hx0
  let n : ℤ := (e0.hom z).1
  have hzn : z = n • one0 := by
    apply (ModuleCat.mono_iff_injective e0.hom).1 inferInstance
    apply Subtype.ext
    simp [n, one0, oneInv]
  refine ⟨n, ?_⟩
  change n • groupCohomology.δ hA 0 1 rfl one0 = x
  rw [← map_zsmul]
  rw [hzn] at hz
  exact hz

private theorem restrictedCocyclePushoutInclusion_kills_class
    (M : Rep ℤ G) (α : Inhomogeneous.H2 M)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α)
    (S : Subgroup G) [Fintype S] :
    groupCohomology.map (.id S)
        ((Rep.resFunctor S.subtype).map (cocyclePushoutInclusion M a ha)) 2
      (comparisonH2 (Rep.res S.subtype M)
        (Inhomogeneous.restrictionH2 S.subtype M α)) = 0 := by
  have hkill : groupCohomology.map (.id G) (cocyclePushoutInclusion M a ha) 2
      (comparisonH2 M α) = 0 := by
    rw [← hrep]
    exact cocyclePushoutInclusion_kills_class M a ha
  have hcomp := (restrictionComparison S.subtype M).commutes2 α
  rw [hcomp]
  change groupCohomology.map (.id S)
      ((Rep.resFunctor S.subtype).map (cocyclePushoutInclusion M a ha)) 2
        (groupCohomology.map S.subtype (𝟙 _) 2 (comparisonH2 M α)) = 0
  have hsquare :
      groupCohomology.map S.subtype (𝟙 _) 2 ≫
          groupCohomology.map (.id S)
            ((Rep.resFunctor S.subtype).map (cocyclePushoutInclusion M a ha)) 2 =
        groupCohomology.map (.id G) (cocyclePushoutInclusion M a ha) 2 ≫
          groupCohomology.map S.subtype (𝟙 _) 2 := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology_map_congr rfl
    simp
  calc
    _ = (groupCohomology.map S.subtype (𝟙 _) 2 ≫
          groupCohomology.map (.id S)
            ((Rep.resFunctor S.subtype).map (cocyclePushoutInclusion M a ha)) 2)
        (comparisonH2 M α) := rfl
    _ = (groupCohomology.map (.id G) (cocyclePushoutInclusion M a ha) 2 ≫
          groupCohomology.map S.subtype (𝟙 _) 2) (comparisonH2 M α) :=
      ConcreteCategory.congr_hom hsquare _
    _ = 0 := by rw [ConcreteCategory.comp_apply, hkill, map_zero]

private theorem restrictedTrivialInteger_H1_subsingleton
    (S : Subgroup G) [Fintype S] :
    Subsingleton
      (groupCohomology.H1 (Rep.res S.subtype (Rep.trivial ℤ G ℤ))) := by
  let Z := Rep.res S.subtype (Rep.trivial ℤ G ℤ)
  letI : Z.IsTrivial := ⟨fun _ => rfl⟩
  let e := groupCohomology.H1IsoOfIsTrivial Z
  constructor
  intro x y
  apply sub_eq_zero.mp
  let z := x - y
  apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
  apply AddMonoidHom.ext
  intro g
  have hzkill : Nat.card S • z = 0 := H1_card_nsmul_eq_zero Z z
  have he := congrArg (fun q => e.hom q) hzkill
  have hg := DFunLike.congr_fun he g
  have hmul : (Nat.card S : ℤ) * (e.hom z) g = 0 := by
    simpa [nsmul_eq_mul] using hg
  have hzval := (mul_eq_zero.mp hmul).resolve_left
    (Int.ofNat_ne_zero.mpr Nat.card_pos.ne')
  simpa [z] using hzval

private theorem restrictedAugmentationIdeal_H2_subsingleton
    (S : Subgroup G) [Fintype S] :
    Subsingleton
      (groupCohomology.H2 (Rep.res S.subtype (barAugmentationIdeal G))) := by
  let A := (barAugmentationSequence G).map (Rep.resFunctor S.subtype)
  have hA : A.ShortExact :=
    (Rep.shortExact_res S.subtype).2 (barAugmentationSequence_shortExact (G := G))
  have hmid : TateAcyclic A.X₂ := by
    intro n
    exact barRegular_tateAcyclic (G := G) S n
  have hsourceGroup : Subsingleton (groupCohomology.H1 A.X₃) :=
    restrictedTrivialInteger_H1_subsingleton (G := G) S
  let e1 := (TateCohomology.isoGroupCohomology 1).app A.X₃
  have hsource : Subsingleton (tateCohomology A.X₃ 1) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective e1.hom).1 inferInstance
      (hsourceGroup.elim _ _)⟩
  have htarget := tate_subsingleton_target_of_delta hA 1 hmid hsource
  let e2 := (TateCohomology.isoGroupCohomology 2).app A.X₁
  exact ⟨fun x y => (ModuleCat.mono_iff_injective e2.inv).1 inferInstance
    (htarget.elim _ _)⟩

private theorem restrictedCocycleConnecting_isIso
    (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α)
    (S : Subgroup G) [Fintype S] :
    let X := (cocyclePushoutSequence M a ha).map (Rep.resFunctor S.subtype)
    let hX : X.ShortExact :=
      (Rep.shortExact_res S.subtype).2 (cocyclePushoutSequence_shortExact M a ha)
    IsIso (groupCohomology.δ hX 1 2 rfl) := by
  let X := (cocyclePushoutSequence M a ha).map (Rep.resFunctor S.subtype)
  have hX : X.ShortExact :=
    (Rep.shortExact_res S.subtype).2 (cocyclePushoutSequence_shortExact M a ha)
  let αS := Inhomogeneous.restrictionH2 S.subtype M α
  let eS : Inhomogeneous.H2 (Rep.res S.subtype M) ≃+
      groupCohomology.H2 X.X₁ := comparisonH2 (Rep.res S.subtype M)
  let αm : groupCohomology.H2 X.X₁ := eS αS
  have hgen := restrictedClass_is_generator M hM α hα S
  have hαm : addOrderOf αm = Nat.card S :=
    (eS.addOrderOf_eq αS).trans hgen.1
  have hspanM : ∀ β : groupCohomology.H2 X.X₁,
      ∃ n : ℤ, n • αm = β := by
    intro β
    obtain ⟨n, hn⟩ := hgen.2 (eS.symm β)
    refine ⟨n, ?_⟩
    calc
      n • αm = eS (n • αS) := (map_zsmul eS n αS).symm
      _ = eS (eS.symm β) := congrArg eS hn
      _ = β := eS.apply_symm_apply β
  let K := groupCohomology.mapShortComplex₁ hX (i := 1) (j := 2) rfl
  have hKexact : Function.Exact
      (groupCohomology.δ hX 1 2 rfl)
      (groupCohomology.map (.id S) X.f 2) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact K).mp
      (groupCohomology.mapShortComplex₁_exact hX (i := 1) (j := 2) rfl)
  have hαker : groupCohomology.map (.id S) X.f 2 αm = 0 := by
    change groupCohomology.map (.id S)
        ((Rep.resFunctor S.subtype).map (cocyclePushoutInclusion M a ha)) 2
          (comparisonH2 (Rep.res S.subtype M) αS) = 0
    exact restrictedCocyclePushoutInclusion_kills_class M α a ha hrep S
  obtain ⟨v, hv⟩ := (hKexact αm).mp hαker
  have hsurj : Function.Surjective (groupCohomology.δ hX 1 2 rfl) := by
    intro β
    obtain ⟨n, hn⟩ := hspanM β
    refine ⟨n • v, ?_⟩
    rw [map_zsmul, hv, hn]
  obtain ⟨u0, hugen0⟩ := restrictedAugmentationIdeal_H1_isCyclic (G := G) S
  let u : groupCohomology.H1 X.X₃ := u0
  have hugen : ∀ x : groupCohomology.H1 X.X₃, ∃ n : ℤ, n • u = x := by
    intro x
    exact hugen0 x
  let du := groupCohomology.δ hX 1 2 rfl u
  obtain ⟨w, hw⟩ := hsurj αm
  obtain ⟨q, hq⟩ := hugen w
  have hαmem : αm ∈ AddSubgroup.zmultiples du := by
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨q, ?_⟩
    change q • groupCohomology.δ hX 1 2 rfl u = αm
    rw [← map_zsmul, hq, hw]
  have hlower : Nat.card S ∣ addOrderOf du := by
    have hd := addOrderOf_dvd_of_mem_zmultiples hαmem
    rwa [hαm] at hd
  have hkillu : Nat.card S • u = 0 := H1_card_nsmul_eq_zero X.X₃ u
  have hkilldu : Nat.card S • du = 0 := by
    change Nat.card S • groupCohomology.δ hX 1 2 rfl u = 0
    rw [← map_nsmul, hkillu, map_zero]
  have hupper : addOrderOf du ∣ Nat.card S :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkilldu
  have hdu : addOrderOf du = Nat.card S := Nat.dvd_antisymm hupper hlower
  have hinj : Function.Injective (groupCohomology.δ hX 1 2 rfl) := by
    intro x y hxy
    apply sub_eq_zero.mp
    let z := x - y
    have hz0 : groupCohomology.δ hX 1 2 rfl z = 0 := by
      dsimp only [z]
      rw [map_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := hugen z
    have hndu : n • du = 0 := by
      change n • groupCohomology.δ hX 1 2 rfl u = 0
      rw [← map_zsmul, hn, hz0]
    have hdiv : (addOrderOf du : ℤ) ∣ n :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr hndu
    rw [hdu] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hkilluz : (Nat.card S : ℤ) • u = 0 := by simpa using hkillu
    have hz : z = 0 := by
      rw [← hn, hk, mul_comm, mul_smul, hkilluz]
      exact zsmul_zero k
    exact hz
  exact (ConcreteCategory.isIso_iff_bijective
    (groupCohomology.δ hX 1 2 rfl)).mpr ⟨hinj, hsurj⟩

private theorem cocyclePushout_lowCohomology
    (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α)
    (S : Subgroup G) [Fintype S] :
    Subsingleton (groupCohomology.H1
        (Rep.res S.subtype (cocyclePushout M a ha))) ∧
      Subsingleton (groupCohomology.H2
        (Rep.res S.subtype (cocyclePushout M a ha))) := by
  let X := (cocyclePushoutSequence M a ha).map (Rep.resFunctor S.subtype)
  let hX : X.ShortExact :=
    (Rep.shortExact_res S.subtype).2 (cocyclePushoutSequence_shortExact M a ha)
  letI : IsIso (groupCohomology.δ hX 1 2 rfl) :=
    restrictedCocycleConnecting_isIso M hM α hα a ha hrep S
  let L1 := groupCohomology.mapShortComplex₂ X 1
  let L2 := groupCohomology.mapShortComplex₂ X 2
  have hM1 : Subsingleton L1.X₁ := hM.h1_zero S
  have hI2 : Subsingleton L2.X₃ :=
    restrictedAugmentationIdeal_H2_subsingleton (G := G) S
  have hL1 : Function.Exact L1.f L1.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact L1).mp
      (groupCohomology.mapShortComplex₂_exact hX 1)
  have hL2 : Function.Exact L2.f L2.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact L2).mp
      (groupCohomology.mapShortComplex₂_exact hX 2)
  change Subsingleton L1.X₂ ∧ Subsingleton L2.X₂
  constructor
  · constructor
    intro x y
    apply sub_eq_zero.mp
    let z := x - y
    have hδg : groupCohomology.δ hX 1 2 rfl (L1.g z) = 0 :=
      (groupCohomology.mapShortComplex₃ hX
        (i := 1) (j := 2) rfl).zero_apply z
    have hg0 : L1.g z = 0 := by
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.δ hX 1 2 rfl)).mp inferInstance
      have hzmap : groupCohomology.δ hX 1 2 rfl 0 = 0 :=
        map_zero (ConcreteCategory.hom (groupCohomology.δ hX 1 2 rfl))
      exact hδg.trans hzmap.symm
    obtain ⟨m, hm⟩ := (hL1 z).mp hg0
    have hm0 : m = 0 := hM1.elim _ _
    rw [hm0] at hm
    simpa using hm.symm
  · constructor
    intro x y
    apply sub_eq_zero.mp
    let z := x - y
    have hg0 : L2.g z = 0 := hI2.elim _ _
    obtain ⟨m, hm⟩ := (hL2 z).mp hg0
    obtain ⟨w, hw⟩ :=
      (ModuleCat.epi_iff_surjective (groupCohomology.δ hX 1 2 rfl)).mp
        inferInstance m
    have hzero : L2.f (groupCohomology.δ hX 1 2 rfl w) = 0 :=
      (groupCohomology.mapShortComplex₁ hX
        (i := 1) (j := 2) rfl).zero_apply w
    calc
      z = L2.f m := hm.symm
      _ = L2.f (groupCohomology.δ hX 1 2 rfl w) :=
        congrArg (ConcreteCategory.hom L2.f) hw.symm
      _ = 0 := hzero

private theorem cocyclePushout_tateAcyclic
    (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α) :
    TateAcyclic (cocyclePushout M a ha) := by
  let P := cocyclePushout M a ha
  have hlow : ∀ (S : Subgroup G) [Fintype S],
      Subsingleton (groupCohomology.H1 (Rep.res S.subtype P)) ∧
        Subsingleton (groupCohomology.H2 (Rep.res S.subtype P)) :=
    fun S _ => cocyclePushout_lowCohomology M hM α hα a ha hrep S
  exact finiteGroup_tateAcyclic_of_lowCohomology P
    (fun f hf => groupCohomology_subsingleton_res_of_injective P 1
      (fun S _ => (hlow S).1) f hf)
    (fun f hf => groupCohomology_subsingleton_res_of_injective P 2
      (fun S _ => (hlow S).2) f hf)

private theorem twoConnectingMap_isIso_of_middle_acyclic
    {M : Rep ℤ G} {a : Inhomogeneous.C2 M}
    {ha : IsNormalizedCocycle2 M a} (D : BarDimensionShiftData G M a ha)
    (hAugmentation : TateAcyclic D.augmentationSequence.X₂)
    (hCocycle : TateAcyclic D.cocycleSequence.X₂) :
    IsIso (twoConnectingMap G D) := by
  have hzAug₁ : IsZero
      (tateCohomology D.augmentationSequence.X₂ (-2)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hAugmentation (-2))
  have hzAug₂ : IsZero
      (tateCohomology D.augmentationSequence.X₂ ((-2) + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hAugmentation ((-2) + 1))
  let dAug := TateCohomology.δ D.augmentationExact (-2)
  letI : IsIso dAug :=
    (TateCohomology.map_tateComplexFunctor_shortExact D.augmentationExact).isIso_δ
      (-2) ((-2) + 1) rfl hzAug₁ hzAug₂
  have hzCocycle₁ : IsZero (tateCohomology D.cocycleSequence.X₂ (-1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hCocycle (-1))
  have hzCocycle₂ : IsZero
      (tateCohomology D.cocycleSequence.X₂ ((-1) + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hCocycle ((-1) + 1))
  let dCocycle := TateCohomology.δ D.cocycleExact (-1)
  letI : IsIso dCocycle :=
    (TateCohomology.map_tateComplexFunctor_shortExact D.cocycleExact).isIso_δ
      (-1) ((-1) + 1) rfl hzCocycle₁ hzCocycle₂
  let fSource := (tateCohomologyFunctor (-2)).map D.sourceIso.hom
  let fMiddle := (tateCohomologyFunctor (-1)).map D.augmentationIdealIso.hom
  let fTarget := (tateCohomologyFunctor 0).map D.targetIso.hom
  letI : IsIso fSource := by infer_instance
  letI : IsIso fMiddle := by infer_instance
  letI : IsIso fTarget := by infer_instance
  let iSource := inv fSource
  let iAug := inv dAug
  let iMiddle := inv fMiddle
  let iCocycle := inv dCocycle
  let iTarget := inv fTarget
  change IsIso (fSource ≫ dAug ≫ fMiddle ≫ dCocycle ≫ fTarget)
  refine ⟨⟨iTarget ≫ iCocycle ≫ iMiddle ≫ iAug ≫ iSource, ?_, ?_⟩⟩ <;>
    simp [iTarget, iCocycle, iMiddle, iAug, iSource]

private theorem twoConnectingMap_isIso
    (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α) :
    IsIso (twoConnectingMap G (barDimensionShiftData G M a ha)) := by
  apply twoConnectingMap_isIso_of_middle_acyclic
  · exact barRegular_tateAcyclic_self (G := G)
  · exact cocyclePushout_tateAcyclic M hM α hα a ha hrep

private theorem abstractReciprocity_of_twoConnecting_isIso
    (M : Rep ℤ G) (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    [IsIso (twoConnectingMap G (barDimensionShiftData G M a ha))] :
    ∃ e : Additive (Abelianization G) ≃+ TateLowDegree.H0 M,
      ∀ g, e (Additive.ofMul (Abelianization.of g)) = rowSumClass M a ha g := by
  let D := barDimensionShiftData G M a ha
  let E : TateLowDegree.HMinusTwo (Rep.trivial ℤ G ℤ) ≅ tateCohomology M 0 :=
    asIso (twoConnectingMap G D)
  let e : Additive (Abelianization G) ≃+ TateLowDegree.H0 M :=
    (tateMinusTwoComparison G).symm.trans
      (E.toLinearEquiv.toAddEquiv.trans
        ((TateLowDegree.comparisonH0Tate M).symm.trans
          (AddEquiv.neg (TateLowDegree.H0 M))))
  refine ⟨e, ?_⟩
  intro g
  have hbar : (tateMinusTwoComparison G).symm
      (Additive.ofMul (Abelianization.of g)) = tateBarGenerator G g := by
    apply (tateMinusTwoComparison G).injective
    rw [(tateMinusTwoComparison G).apply_symm_apply]
    exact (tateMinusTwoComparison_barGenerator G g).symm
  change -(TateLowDegree.comparisonH0Tate M).symm
      (E.hom ((tateMinusTwoComparison G).symm
        (Additive.ofMul (Abelianization.of g)))) = rowSumClass M a ha g
  rw [hbar]
  change -(TateLowDegree.comparisonH0Tate M).symm
      (twoConnectingMap G D (tateBarGenerator G g)) = rowSumClass M a ha g
  rw [tateMinusTwo_barGenerator G M a ha (fun x => rowSum_invariant M a ha x) g]
  change -(TateLowDegree.comparisonH0Tate M).symm
      (-TateLowDegree.comparisonH0Tate M (rowSumClass M a ha g)) =
    rowSumClass M a ha g
  simp

/--
**C07–C08**, Theorem `thm:tate-reciprocity`: the two dimension shifts give the reciprocity
isomorphism, with the explicit row-sum formula.
-/
theorem abstractReciprocity_exists (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α) :
    ∃ e : Additive (Abelianization G) ≃+ TateLowDegree.H0 M,
      ∀ g, e (Additive.ofMul (Abelianization.of g)) = rowSumClass M a ha g := by
  letI : IsIso (twoConnectingMap G (barDimensionShiftData G M a ha)) :=
    twoConnectingMap_isIso M hM α hα a ha hrep
  exact abstractReciprocity_of_twoConnecting_isIso M a ha

/-- The chosen Tate reciprocity equivalence. -/
noncomputable def abstractReciprocity (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α) :
    Additive (Abelianization G) ≃+ TateLowDegree.H0 M :=
  (abstractReciprocity_exists M hM α hα a ha hrep).choose

/-- The row-sum formula for `abstractReciprocity`. -/
theorem abstractReciprocity_apply (M : Rep ℤ G) (hM : Hypotheses M)
    (α : Inhomogeneous.H2 M) (hα : addOrderOf α = Nat.card G)
    (a : Inhomogeneous.C2 M) (ha : IsNormalizedCocycle2 M a)
    (hrep : cocycleClass2 M a ha = α) (g : G) :
    abstractReciprocity M hM α hα a ha hrep
        (Additive.ofMul (Abelianization.of g)) = rowSumClass M a ha g :=
  (abstractReciprocity_exists M hM α hα a ha hrep).choose_spec g

/--
A named package for the quotient, inclusion/corestriction, and transfer/restriction naturality
squares of the Tate map.
-/
structure NaturalitySquares
    {G Q S : Type} [Group G] [Group Q] [Group S]
    {TG TQ TS : Type} [AddCommGroup TG] [AddCommGroup TQ] [AddCommGroup TS]
    (rG : Additive (Abelianization G) ≃+ TG)
    (rQ : Additive (Abelianization Q) ≃+ TQ)
    (rS : Additive (Abelianization S) ≃+ TS)
    (quotientAbMap : Additive (Abelianization G) →+ Additive (Abelianization Q))
    (inflationTateMap : TG →+ TQ)
    (inclusionAbMap : Additive (Abelianization S) →+ Additive (Abelianization G))
    (corestrictionTateMap : TS →+ TG)
    (transferAbMap : Additive (Abelianization G) →+ Additive (Abelianization S))
    (restrictionTateMap : TG →+ TS) where
  /-- Quotient on abelianizations. -/
  quotientAb : Additive (Abelianization G) →+ Additive (Abelianization Q)
  /-- This is the supplied bar-resolution quotient map. -/
  quotientAb_eq_actual : quotientAb = quotientAbMap
  /-- Inflation/quotient on degree-zero Tate groups. -/
  quotientTate : TG →+ TQ
  /-- This is the supplied inflation map, not an arbitrary replacement. -/
  quotientTate_eq_actual : quotientTate = inflationTateMap
  /-- Subgroup inclusion on abelianizations. -/
  inclusionAb : Additive (Abelianization S) →+ Additive (Abelianization G)
  /-- This is the map induced by the actual subgroup inclusion. -/
  inclusionAb_eq_actual : inclusionAb = inclusionAbMap
  /-- Module norm/corestriction on degree-zero Tate groups. -/
  normTate : TS →+ TG
  /-- This is the supplied corestriction/norm map. -/
  normTate_eq_actual : normTate = corestrictionTateMap
  /-- Transfer on abelianizations. -/
  transferAb : Additive (Abelianization G) →+ Additive (Abelianization S)
  /-- This is the supplied bar-resolution transfer. -/
  transferAb_eq_actual : transferAb = transferAbMap
  /-- Inclusion/restriction on degree-zero Tate groups. -/
  inclusionTate : TG →+ TS
  /-- This is the supplied restriction map. -/
  inclusionTate_eq_actual : inclusionTate = restrictionTateMap
  /-- Diagram (3.2). -/
  projection_square : quotientTate.comp rG.toAddMonoidHom =
    rQ.toAddMonoidHom.comp quotientAb
  /-- Diagram (3.3). -/
  norm_square : normTate.comp rS.toAddMonoidHom =
    rG.toAddMonoidHom.comp inclusionAb
  /-- Diagram (3.4). -/
  transfer_square : inclusionTate.comp rG.toAddMonoidHom =
    rS.toAddMonoidHom.comp transferAb

/--
**C09**, Remark `rem:tate-naturality` and Proposition `prop:tate-chain-naturality`: bar-resolution
quotient, subgroup, and transfer maps produce all three named commuting squares.
-/
theorem naturalitySquares_exists
    {G Q S : Type} [Group G] [Group Q] [Group S]
    {TG TQ TS : Type} [AddCommGroup TG] [AddCommGroup TQ] [AddCommGroup TS]
    (rG : Additive (Abelianization G) ≃+ TG)
    (rQ : Additive (Abelianization Q) ≃+ TQ)
    (rS : Additive (Abelianization S) ≃+ TS)
    (quotientAbMap : Additive (Abelianization G) →+ Additive (Abelianization Q))
    (inflationTateMap : TG →+ TQ)
    (inclusionAbMap : Additive (Abelianization S) →+ Additive (Abelianization G))
    (corestrictionTateMap : TS →+ TG)
    (transferAbMap : Additive (Abelianization G) →+ Additive (Abelianization S))
    (restrictionTateMap : TG →+ TS)
    (projection_square : inflationTateMap.comp rG.toAddMonoidHom =
      rQ.toAddMonoidHom.comp quotientAbMap)
    (norm_square : corestrictionTateMap.comp rS.toAddMonoidHom =
      rG.toAddMonoidHom.comp inclusionAbMap)
    (transfer_square : restrictionTateMap.comp rG.toAddMonoidHom =
      rS.toAddMonoidHom.comp transferAbMap) :
    Nonempty (NaturalitySquares rG rQ rS quotientAbMap inflationTateMap
      inclusionAbMap corestrictionTateMap transferAbMap restrictionTateMap) := by
  exact ⟨{
    quotientAb := quotientAbMap
    quotientAb_eq_actual := rfl
    quotientTate := inflationTateMap
    quotientTate_eq_actual := rfl
    inclusionAb := inclusionAbMap
    inclusionAb_eq_actual := rfl
    normTate := corestrictionTateMap
    normTate_eq_actual := rfl
    transferAb := transferAbMap
    transferAb_eq_actual := rfl
    inclusionTate := restrictionTateMap
    inclusionTate_eq_actual := rfl
    projection_square := projection_square
    norm_square := norm_square
    transfer_square := transfer_square }⟩

end AbstractReciprocity

end

end NU.LCFT
