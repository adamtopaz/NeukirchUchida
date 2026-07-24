import Submission.NU.LCFT.FundamentalClass.DeepUnits

/-!
# Herbrand quotients and the cyclic local calculation

All local declarations in this file use the same valued/local-field bundle as
`Basic/LocalField.lean`, including `ValuativeExtension K L`.  Finiteness of both Tate groups is
never hidden behind `Nat.card`: every rule that divides cardinalities assumes explicit `Finite`
instances (or, for the fixed trivial module, records positive-cardinality guards).
-/

namespace NU.LCFT

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ValuativeRel

/--
**F04**, Lemma `lem:herbrand-rules`: the quotient `|Ĥ⁰| / |Ĥ⁻¹|` in `ℚ`.

The finiteness instances are deliberately arguments of the definition.  Thus `Nat.card` is never
silently applied to an infinite Tate group (where its value would be zero).
-/
noncomputable def herbrandQuotient {G : Type} [Group G] [Fintype G]
    (M : Rep ℤ G) [Finite (TateLowDegree.H0 M)]
    [Finite (TateLowDegree.HMinusOne M)] : ℚ :=
  (Nat.card (TateLowDegree.H0 M) : ℚ) /
    (Nat.card (TateLowDegree.HMinusOne M) : ℚ)

/-- **F04**, Lemma `lem:herbrand-rules`: finiteness required by the quotient. -/
structure HerbrandFinite {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : Prop where
  /-- Finiteness of degree-zero Tate cohomology. -/
  h0 : Finite (TateLowDegree.H0 M)
  /-- Finiteness of degree-minus-one Tate cohomology. -/
  h1 : Finite (TateLowDegree.HMinusOne M)

/--
**F04**, Lemma `lem:herbrand-rules`: if both Tate groups occurring in the definition are
trivial, their guarded Herbrand quotient is one.
-/
theorem herbrandQuotient_eq_one_of_subsingleton
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    [Finite (TateLowDegree.H0 M)] [Finite (TateLowDegree.HMinusOne M)]
    [Subsingleton (TateLowDegree.H0 M)] [Subsingleton (TateLowDegree.HMinusOne M)] :
    herbrandQuotient M = 1 := by
  rw [herbrandQuotient, Nat.card_unique, Nat.card_unique]
  norm_num

private noncomputable def cyclicH2EquivH0
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G) :
    Inhomogeneous.H2 M ≃+ TateLowDegree.H0 M := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let g := (IsCyclic.exists_generator (α := G)).choose
  have hg := (IsCyclic.exists_generator (α := G)).choose_spec
  let e : Inhomogeneous.invariants0 M ≃+
      LinearMap.ker (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap :=
    { toFun := fun x => ⟨x, by
          rw [LinearMap.mem_ker]
          simpa [Rep.sub_hom, Rep.applyAsHom_apply, sub_eq_zero] using
            (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x).1 x.2⟩
      invFun := fun x => ⟨x, by
          apply (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x).2
          have hx : ((M.applyAsHom g).hom - (𝟙 M : M ⟶ M).hom) (x : M) = 0 := by
            rw [← Rep.sub_hom]
            exact x.2
          change M.ρ g (x : M) - x = 0 at hx
          exact sub_eq_zero.mp hx⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let p := Rep.FiniteCyclicGroup.groupCohomologyπEven M g hg 2 (by simp)
  let q : Inhomogeneous.invariants0 M →+ Inhomogeneous.H2 M :=
    (comparisonH2 M).symm.toAddMonoidHom.comp
      (p.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective p).1 inferInstance
  have hq : Function.Surjective q :=
    (comparisonH2 M).symm.surjective.comp (hp.comp e.surjective)
  have hker : q.ker = TateLowDegree.normRangeInInvariants M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change (comparisonH2 M).symm (p (e x)) = 0 ↔ _
    rw [(comparisonH2 M).symm.map_eq_zero_iff,
      Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [e, TateLowDegree.normAddHom] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [e, TateLowDegree.normAddHom] using hy⟩
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : Inhomogeneous.invariants0 M ⧸ q.ker →+
      TateLowDegree.H0 M :=
    QuotientAddGroup.map q.ker (TateLowDegree.normRangeInInvariants M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.H0 M →+
        Inhomogeneous.invariants0 M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

private noncomputable def cyclicH1EquivHMinusOne
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G) :
    Inhomogeneous.H1 M ≃+ TateLowDegree.HMinusOne M := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let g := (IsCyclic.exists_generator (α := G)).choose
  have hg := (IsCyclic.exists_generator (α := G)).choose_spec
  let e : TateLowDegree.normKernel M ≃+
      LinearMap.ker M.norm.hom.toLinearMap :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let p := Rep.FiniteCyclicGroup.groupCohomologyπOdd M g hg 1 (by simp)
  let q : TateLowDegree.normKernel M →+ Inhomogeneous.H1 M :=
    (comparisonH1 M).symm.toAddMonoidHom.comp
      (p.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective p).1 inferInstance
  have hq : Function.Surjective q :=
    (comparisonH1 M).symm.surjective.comp (hp.comp e.surjective)
  have hker : q.ker = TateLowDegree.augmentationInNormKernel M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change (comparisonH1 M).symm (p (e x)) = 0 ↔ _
    rw [(comparisonH1 M).symm.map_eq_zero_iff,
      Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff]
    change (x : M) ∈ LinearMap.range (M.applyAsHom g - 𝟙 M).hom.toLinearMap ↔
      (x : M) ∈ TateLowDegree.augmentation M
    constructor
    · rintro ⟨y, hy⟩
      apply AddSubgroup.subset_closure
      refine ⟨g, y, ?_⟩
      change (x : M) = M.ρ g y - y
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy.symm
    · intro hx
      have hcoin : (x : M) ∈ Representation.Coinvariants.ker M.ρ := by
        refine AddSubgroup.closure_induction (p := fun z _ =>
          z ∈ Representation.Coinvariants.ker M.ρ) ?_ ?_ ?_ ?_ hx
        · rintro z ⟨s, a, rfl⟩
          exact Representation.Coinvariants.sub_mem_ker s a
        · exact Submodule.zero_mem _
        · exact fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb
        · exact fun _ _ ha => Submodule.neg_mem _ ha
      rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg] at hcoin
      rcases hcoin with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : TateLowDegree.normKernel M ⧸ q.ker →+
      TateLowDegree.HMinusOne M :=
    QuotientAddGroup.map q.ker (TateLowDegree.augmentationInNormKernel M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.HMinusOne M →+
        TateLowDegree.normKernel M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.augmentationInNormKernel M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

private theorem trivialHMinusOne_subsingleton
    {G : Type} [Group G] [Fintype G] :
    Subsingleton (TateLowDegree.HMinusOne (Rep.trivial ℤ G ℤ)) := by
  have hk : Subsingleton (TateLowDegree.normKernel (Rep.trivial ℤ G ℤ)) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : (x : ℤ) = 0 := by
      have h := x.2
      simp [TateLowDegree.normKernel, TateLowDegree.normAddHom,
        Rep.norm, Representation.norm] at h
      exact congr_arg Subtype.val h
    have hy : (y : ℤ) = 0 := by
      have h := y.2
      simp [TateLowDegree.normKernel, TateLowDegree.normAddHom,
        Rep.norm, Representation.norm] at h
      exact congr_arg Subtype.val h
    rw [hx, hy]
  constructor
  intro a b
  induction a using QuotientAddGroup.induction_on with
  | H x =>
    induction b using QuotientAddGroup.induction_on with
    | H y => exact congr_arg _ (hk.elim x y)

set_option maxRecDepth 10000 in
private noncomputable def trivialH0EquivZMod
    {G : Type} [Group G] [Fintype G] :
    TateLowDegree.H0 (Rep.trivial ℤ G ℤ) ≃+ ZMod (Nat.card G) := by
  let M := Rep.trivial ℤ G ℤ
  let e : Inhomogeneous.invariants0 M ≃+ ℤ :=
    { toFun := fun x => x
      invFun := fun x => ⟨x, fun _ => rfl⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hmem (x : Inhomogeneous.invariants0 M) :
      x ∈ TateLowDegree.normRangeInInvariants M ↔
        e x ∈ AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y * (Nat.card G : ℤ) = x
      have hcard : Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
      dsimp [TateLowDegree.normAddHom, M] at hy
      rw [Rep.norm_apply] at hy
      simp only [Representation.norm, LinearMap.sum_apply] at hy
      simp only [Representation.trivial_apply, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] at hy
      rw [hcard] at hy
      simpa [mul_comm] using hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have hcard : Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
      dsimp [TateLowDegree.normAddHom, M]
      rw [Rep.norm_apply]
      simp only [Representation.norm, LinearMap.sum_apply]
      change y * (Nat.card G : ℤ) = (x : ℤ) at hy
      simp only [Representation.trivial_apply, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      simpa [mul_comm] using hy
  let r : TateLowDegree.H0 M →+ ℤ ⧸ AddSubgroup.zmultiples (Nat.card G : ℤ) :=
    QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M)
      (AddSubgroup.zmultiples (Nat.card G : ℤ)) e.toAddMonoidHom (by
        intro x hx
        exact (hmem x).1 hx)
  have hr : Function.Bijective r := by
    let s : (ℤ ⧸ AddSubgroup.zmultiples (Nat.card G : ℤ)) →+
        TateLowDegree.H0 M :=
      QuotientAddGroup.map (AddSubgroup.zmultiples (Nat.card G : ℤ))
        (TateLowDegree.normRangeInInvariants M) e.symm.toAddMonoidHom (by
          intro x hx
          exact (hmem (e.symm x)).2 (by simpa using hx))
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact (AddEquiv.ofBijective r hr).trans (Int.quotientZMultiplesNatEquivZMod _)

private noncomputable def periodicOddEquivHMinusOne
    {G : Type} [CommGroup G] [Fintype G] (M : Rep.{u} ℤ G)
    (gen : G) (hgen : ∀ x, x ∈ Subgroup.zpowers gen) :
    (Rep.FiniteCyclicGroup.subCompNormHom M gen).homology ≃+
      TateLowDegree.HMinusOne M := by
  letI : Module ℤ M := M.hV2
  let SC := Rep.FiniteCyclicGroup.subCompNormHom M gen
  letI : Module ℤ (LinearMap.ker SC.g.hom) := (LinearMap.ker SC.g.hom).module
  let e : TateLowDegree.normKernel M ≃+
      LinearMap.ker M.norm.hom.toLinearMap :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let q : TateLowDegree.normKernel M →+ SC.homology :=
    (ShortComplex.homologyπ SC).hom.toAddMonoidHom.comp
      ((ShortComplex.moduleCatCyclesIso SC).inv.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hq : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (ShortComplex.homologyπ SC)).1 inferInstance |>.comp
      ((ModuleCat.epi_iff_surjective (ShortComplex.moduleCatCyclesIso SC).inv).1 inferInstance |>.comp
        e.surjective)
  have hker : q.ker = TateLowDegree.augmentationInNormKernel M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change q x = 0 ↔ _
    have hzero : q x = 0 ↔
        (x : M) ∈ LinearMap.range (M.applyAsHom gen - 𝟙 M).hom.toLinearMap := by
      change SC.homologyπ (SC.moduleCatCyclesIso.inv (e x)) = 0 ↔ _
      rw [SC.moduleCatCyclesIso_inv_π_apply]
      rw [map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)]
      change Submodule.Quotient.mk (e x) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, ?_⟩
        exact congrArg Subtype.val hy
      · rintro ⟨y, hy⟩
        refine ⟨y, ?_⟩
        apply Subtype.ext
        exact hy
    rw [hzero]
    change (x : M) ∈ LinearMap.range (M.applyAsHom gen - 𝟙 M).hom.toLinearMap ↔
      (x : M) ∈ TateLowDegree.augmentation M
    constructor
    · rintro ⟨y, hy⟩
      apply AddSubgroup.subset_closure
      refine ⟨gen, y, ?_⟩
      change (x : M) = M.ρ gen y - y
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy.symm
    · intro hx
      have hcoin : (x : M) ∈ Representation.Coinvariants.ker M.ρ := by
        refine AddSubgroup.closure_induction (p := fun z _ =>
          z ∈ Representation.Coinvariants.ker M.ρ) ?_ ?_ ?_ ?_ hx
        · rintro z ⟨s, a, rfl⟩
          exact Representation.Coinvariants.sub_mem_ker s a
        · exact Submodule.zero_mem _
        · exact fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb
        · exact fun _ _ ha => Submodule.neg_mem _ ha
      rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ gen hgen] at hcoin
      rcases hcoin with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : TateLowDegree.normKernel M ⧸ q.ker →+
      TateLowDegree.HMinusOne M :=
    QuotientAddGroup.map q.ker (TateLowDegree.augmentationInNormKernel M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.HMinusOne M →+
        TateLowDegree.normKernel M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.augmentationInNormKernel M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

private noncomputable def periodicEvenEquivH0
    {G : Type} [CommGroup G] [Fintype G] (M : Rep.{u} ℤ G)
    (gen : G) (hgen : ∀ x, x ∈ Subgroup.zpowers gen) :
    (Rep.FiniteCyclicGroup.normHomCompSub M gen).homology ≃+
      TateLowDegree.H0 M := by
  letI : Module ℤ M := M.hV2
  let SC := Rep.FiniteCyclicGroup.normHomCompSub M gen
  letI : Module ℤ (LinearMap.ker SC.g.hom) := (LinearMap.ker SC.g.hom).module
  let e : Inhomogeneous.invariants0 M ≃+
      LinearMap.ker (M.applyAsHom gen - 𝟙 M).hom.toLinearMap :=
    { toFun := fun x => ⟨x, by
          rw [LinearMap.mem_ker]
          simpa [Rep.sub_hom, Rep.applyAsHom_apply, sub_eq_zero] using
            (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ gen hgen x).1 x.2⟩
      invFun := fun x => ⟨x, by
          apply (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ gen hgen x).2
          have hx : ((M.applyAsHom gen).hom - (𝟙 M : M ⟶ M).hom) (x : M) = 0 := by
            rw [← Rep.sub_hom]
            exact x.2
          change M.ρ gen (x : M) - x = 0 at hx
          exact sub_eq_zero.mp hx⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let q : Inhomogeneous.invariants0 M →+ SC.homology :=
    (ShortComplex.homologyπ SC).hom.toAddMonoidHom.comp
      ((ShortComplex.moduleCatCyclesIso SC).inv.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hq : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (ShortComplex.homologyπ SC)).1 inferInstance |>.comp
      ((ModuleCat.epi_iff_surjective (ShortComplex.moduleCatCyclesIso SC).inv).1
        inferInstance |>.comp e.surjective)
  have hker : q.ker = TateLowDegree.normRangeInInvariants M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change q x = 0 ↔ _
    have hzero : q x = 0 ↔ (x : M) ∈ LinearMap.range M.norm.hom.toLinearMap := by
      change SC.homologyπ (SC.moduleCatCyclesIso.inv (e x)) = 0 ↔ _
      rw [SC.moduleCatCyclesIso_inv_π_apply]
      rw [map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)]
      change Submodule.Quotient.mk (e x) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, ?_⟩
        exact congrArg Subtype.val hy
      · rintro ⟨y, hy⟩
        refine ⟨y, ?_⟩
        apply Subtype.ext
        exact hy
    rw [hzero]
    rfl
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : Inhomogeneous.invariants0 M ⧸ q.ker →+ TateLowDegree.H0 M :=
    QuotientAddGroup.map q.ker (TateLowDegree.normRangeInInvariants M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.H0 M →+ Inhomogeneous.invariants0 M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

private noncomputable def cyclicPeriodicHom
    {G : Type} [CommGroup G] [Fintype G]
    {A B : Rep ℤ G} (g : G) (f : A ⟶ B) :
    Rep.FiniteCyclicGroup.moduleCatCochainComplex A g ⟶
      Rep.FiniteCyclicGroup.moduleCatCochainComplex B g := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  exact {
    f := fun _ => ModuleCat.ofHom f.hom.toLinearMap
    comm' := by
      rintro i j ⟨rfl⟩
      by_cases hi : Even i
      · simp only [Rep.FiniteCyclicGroup.moduleCatCochainComplex,
          HomologicalComplex.alternatingConst, if_pos (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl), hi, ↓reduceIte, dite_eq_ite]
        ext x
        change B.ρ g (f.hom x) - f.hom x = f.hom (A.ρ g x - x)
        rw [map_sub, Rep.hom_comm_apply]
      · simp only [Rep.FiniteCyclicGroup.moduleCatCochainComplex,
          HomologicalComplex.alternatingConst, if_pos (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl), hi, ↓reduceIte, dite_eq_ite]
        ext x
        exact Rep.norm_comm_apply f x }

private noncomputable def cyclicPeriodicSCMap
    {G : Type} [CommGroup G] [Fintype G]
    {A B : Rep ℤ G} (g : G) (f : A ⟶ B) :
    Rep.FiniteCyclicGroup.subCompNormHom A g ⟶
      Rep.FiniteCyclicGroup.subCompNormHom B g := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  exact {
    τ₁ := ModuleCat.ofHom f.hom.toLinearMap
    τ₂ := ModuleCat.ofHom f.hom.toLinearMap
    τ₃ := ModuleCat.ofHom f.hom.toLinearMap
    comm₁₂ := by
      dsimp [Rep.FiniteCyclicGroup.subCompNormHom]
      ext x
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using
        congrArg (fun z => z - f.hom x) (Rep.hom_comm_apply f g x).symm
    comm₂₃ := by
      dsimp [Rep.FiniteCyclicGroup.subCompNormHom]
      ext x
      exact Rep.norm_comm_apply f x }

private noncomputable def cyclicOddIsoOne
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (g : G) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 1 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
  letI : Module ℤ A := A.hV2
  exact HomologicalComplex.alternatingConstHomologyIsoOdd
    (ModuleCat.of ℤ A) (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.up_nat_odd_add) (by simp) (by simp) (by norm_num)

private noncomputable def cyclicOddIsoThree
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (g : G) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 3 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
  letI : Module ℤ A := A.hV2
  exact HomologicalComplex.alternatingConstHomologyIsoOdd
    (ModuleCat.of ℤ A) (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.up_nat_odd_add) (by simp) (by simp) (by norm_num)

private noncomputable def cyclicEvenIsoTwo
    {G : Type} [CommGroup G] [Fintype G] (A : Rep ℤ G) (g : G) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology 2 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology := by
  letI : Module ℤ A := A.hV2
  exact HomologicalComplex.alternatingConstHomologyIsoEven
    (ModuleCat.of ℤ A) (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.up_nat_odd_add) (by simp) (by simp) (by norm_num)

private theorem cyclicPeriodicHom_naturality_one
    {G : Type} [CommGroup G] [Fintype G]
    {A B : Rep ℤ G} (g : G) (f : A ⟶ B) :
    HomologicalComplex.homologyMap (cyclicPeriodicHom g f) 1 ≫
        (cyclicOddIsoOne B g).hom =
      (cyclicOddIsoOne A g).hom ≫
        ShortComplex.homologyMap (cyclicPeriodicSCMap g f) := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1

private theorem cyclicPeriodicHom_naturality_three
    {G : Type} [CommGroup G] [Fintype G]
    {A B : Rep ℤ G} (g : G) (f : A ⟶ B) :
    HomologicalComplex.homologyMap (cyclicPeriodicHom g f) 3 ≫
        (cyclicOddIsoThree B g).hom =
      (cyclicOddIsoThree A g).hom ≫
        ShortComplex.homologyMap (cyclicPeriodicSCMap g f) := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1


private def rangeEquivOfCommute
    {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y']
    (f : X →+ Y) (g : X' →+ Y') (ex : X ≃+ X') (ey : Y ≃+ Y')
    (h : ∀ x, ey (f x) = g (ex x)) : f.range ≃ g.range where
  toFun z := ⟨ey z.1, by
    obtain ⟨x, hx⟩ := z.2
    exact ⟨ex x, by rw [← h x, hx]⟩⟩
  invFun z := ⟨ey.symm z.1, by
    obtain ⟨x, hx⟩ := z.2
    refine ⟨ex.symm x, ?_⟩
    apply ey.injective
    rw [h, ey.apply_symm_apply, ex.apply_symm_apply, hx]⟩
  left_inv z := by apply Subtype.ext; exact ey.symm_apply_apply z.1
  right_inv z := by apply Subtype.ext; exact ey.apply_symm_apply z.1

private def rangeCodRestrictEquiv {R X Y : Type*} [Ring R]
    [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (K : Submodule R Y) (h : ∀ x, f x ∈ K) :
    LinearMap.range (f.codRestrict K h) ≃+ LinearMap.range f where
  toFun z := ⟨(z.1 : K), by
    obtain ⟨x, hx⟩ := z.2
    exact ⟨x, congrArg Subtype.val hx⟩⟩
  invFun z := ⟨⟨z.1, by
      obtain ⟨x, hx⟩ := z.2
      rw [← hx]
      exact h x⟩, by
    obtain ⟨x, hx⟩ := z.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl

private theorem card_eq_ker_mul_range
    {X Y : Type*} [AddGroup X] [AddGroup Y] [Finite X]
    (f : X →+ Y) : Nat.card X = Nat.card f.ker * Nat.card f.range := by
  rw [← f.ker.card_mul_index, AddSubgroup.index_ker]

private theorem finite_middle_of_range_eq_ker
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C] (p : A →+ B) (q : B →+ C)
    (h : p.range = q.ker) : Finite B := by
  letI : Finite p.range := Finite.of_surjective
    (fun x : A => (⟨p x, x, rfl⟩ : p.range)) (fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩)
  letI : Finite q.ker := Finite.of_injective (fun x : q.ker =>
    (⟨x, by rw [h]; exact x.2⟩ : p.range)) (fun x y hxy => by
      apply Subtype.ext
      exact congrArg (fun z : p.range => (z : B)) hxy)
  letI : Finite q.range := Finite.of_injective (fun x : q.range => (x : C))
    Subtype.val_injective
  exact (q.finite_iff_finite_ker_range).2 ⟨inferInstance, inferInstance⟩

private theorem card_cycle
    {X0 X1 X2 X3 X4 X5 X6 X7 : Type*}
    [AddGroup X0] [AddGroup X1] [AddGroup X2] [AddGroup X3]
    [AddGroup X4] [AddGroup X5] [AddGroup X6] [AddGroup X7]
    [Finite X0] [Finite X1] [Finite X2] [Finite X3]
    [Finite X4] [Finite X5] [Finite X6] [Finite X7]
    (f0 : X0 →+ X1) (f1 : X1 →+ X2) (f2 : X2 →+ X3)
    (f3 : X3 →+ X4) (f4 : X4 →+ X5) (f5 : X5 →+ X6)
    (f6 : X6 →+ X7)
    (h1 : f0.range = f1.ker) (h2 : f1.range = f2.ker)
    (h3 : f2.range = f3.ker) (h4 : f3.range = f4.ker)
    (h5 : f4.range = f5.ker) (h6 : f5.range = f6.ker)
    (h06 : Nat.card X0 = Nat.card X6)
    (hr : Nat.card f0.range = Nat.card f6.range) :
    Nat.card X4 * Nat.card X0 * Nat.card X2 =
      Nat.card X1 * Nat.card X3 * Nat.card X5 := by
  rw [h06]
  rw [card_eq_ker_mul_range f1, card_eq_ker_mul_range f2,
    card_eq_ker_mul_range f3, card_eq_ker_mul_range f4,
    card_eq_ker_mul_range f5, card_eq_ker_mul_range f6]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  rw [hr]
  ac_rfl

private theorem topRes_norm_eq {G : Type} [Group G] [Fintype G]
    [Fintype (⊤ : Subgroup G)] (M : Rep ℤ G) (x : M) :
    (Rep.res (⊤ : Subgroup G).subtype M).norm.hom x = M.norm.hom x := by
  rw [Rep.norm_apply, Rep.norm_apply]
  simp only [Representation.norm, LinearMap.sum_apply]
  simpa using Equiv.sum_comp Subgroup.topEquiv.toEquiv (fun g : G => M.ρ g x)

private noncomputable def topResH0Equiv {G : Type} [Group G] [Fintype G]
    [Fintype (⊤ : Subgroup G)] (M : Rep ℤ G) :
    TateLowDegree.H0 M ≃+
      TateLowDegree.H0 (Rep.res (⊤ : Subgroup G).subtype M) := by
  let N := Rep.res (⊤ : Subgroup G).subtype M
  let e : Inhomogeneous.invariants0 M ≃+ Inhomogeneous.invariants0 N :=
    { toFun := fun x => ⟨x, fun g => x.2 g.1⟩
      invFun := fun x => ⟨x, fun g => x.2 ⟨g, Subgroup.mem_top g⟩⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  have hmem (x : Inhomogeneous.invariants0 M) :
      x ∈ TateLowDegree.normRangeInInvariants M ↔
        e x ∈ TateLowDegree.normRangeInInvariants N := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change N.norm.hom y = (x : M)
      rw [topRes_norm_eq M]
      exact hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change M.norm.hom y = (x : M)
      rw [← topRes_norm_eq M]
      exact hy
  let r : TateLowDegree.H0 M →+ TateLowDegree.H0 N :=
    QuotientAddGroup.map _ _ e.toAddMonoidHom (fun x hx => (hmem x).1 hx)
  let s : TateLowDegree.H0 N →+ TateLowDegree.H0 M :=
    QuotientAddGroup.map _ _ e.symm.toAddMonoidHom (by
      intro x hx
      exact (hmem (e.symm x)).2 (by simpa using hx))
  have hleft : Function.LeftInverse s r := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [r, s]
  have hright : Function.RightInverse s r := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [r, s]
  exact AddEquiv.ofBijective r ⟨hleft.injective, hright.surjective⟩

private theorem topRes_augmentation_eq {G : Type} [Group G] [Fintype G]
    [Fintype (⊤ : Subgroup G)] (M : Rep ℤ G) :
    TateLowDegree.augmentation (Rep.res (⊤ : Subgroup G).subtype M) =
      TateLowDegree.augmentation M := by
  apply le_antisymm
  · rw [TateLowDegree.augmentation, AddSubgroup.closure_le]
    rintro z ⟨g, x, rfl⟩
    apply AddSubgroup.subset_closure
    exact ⟨g.1, x, rfl⟩
  · rw [TateLowDegree.augmentation, AddSubgroup.closure_le]
    rintro z ⟨g, x, rfl⟩
    apply AddSubgroup.subset_closure
    exact ⟨⟨g, Subgroup.mem_top g⟩, x, rfl⟩

private noncomputable def topResHMinusOneEquiv {G : Type} [Group G] [Fintype G]
    [Fintype (⊤ : Subgroup G)] (M : Rep ℤ G) :
    TateLowDegree.HMinusOne M ≃+
      TateLowDegree.HMinusOne (Rep.res (⊤ : Subgroup G).subtype M) := by
  let N := Rep.res (⊤ : Subgroup G).subtype M
  let e : TateLowDegree.normKernel M ≃+ TateLowDegree.normKernel N :=
    { toFun := fun x => ⟨x, by
          change N.norm.hom (x : M) = 0
          rw [topRes_norm_eq M]
          exact x.2⟩
      invFun := fun x => ⟨x, by
          change M.norm.hom (x : M) = 0
          rw [← topRes_norm_eq M]
          exact x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  have hmem (x : TateLowDegree.normKernel M) :
      x ∈ TateLowDegree.augmentationInNormKernel M ↔
        e x ∈ TateLowDegree.augmentationInNormKernel N := by
    change (x : M) ∈ TateLowDegree.augmentation M ↔
      (x : M) ∈ TateLowDegree.augmentation N
    rw [topRes_augmentation_eq M]
  let r : TateLowDegree.HMinusOne M →+ TateLowDegree.HMinusOne N :=
    QuotientAddGroup.map _ _ e.toAddMonoidHom (fun x hx => (hmem x).1 hx)
  let s : TateLowDegree.HMinusOne N →+ TateLowDegree.HMinusOne M :=
    QuotientAddGroup.map _ _ e.symm.toAddMonoidHom (by
      intro x hx
      exact (hmem (e.symm x)).2 (by simpa using hx))
  have hleft : Function.LeftInverse s r := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [r, s]
  have hright : Function.RightInverse s r := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [r, s]
  exact AddEquiv.ofBijective r ⟨hleft.injective, hright.surjective⟩


private theorem herbrandQuotient_finite
    {G : Type} [Group G] [Fintype G] [IsCyclic G]
    (M : Rep.{u} ℤ G) [Finite M]
    [Finite (TateLowDegree.H0 M)] [Finite (TateLowDegree.HMinusOne M)] :
    herbrandQuotient M = 1 := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let gen := (IsCyclic.exists_generator (α := G)).choose
  have hgen := (IsCyclic.exists_generator (α := G)).choose_spec
  let O := Rep.FiniteCyclicGroup.subCompNormHom M gen
  let E := Rep.FiniteCyclicGroup.normHomCompSub M gen
  letI : Module ℤ (LinearMap.ker O.g.hom) := (LinearMap.ker O.g.hom).module
  letI : Module ℤ (LinearMap.ker E.g.hom) := (LinearMap.ker E.g.hom).module
  let eo := periodicOddEquivHMinusOne M gen hgen
  let ee := periodicEvenEquivH0 M gen hgen
  letI : Finite O.homology :=
    Finite.of_equiv (TateLowDegree.HMinusOne M) eo.symm.toEquiv
  letI : Finite E.homology := Finite.of_equiv (TateLowDegree.H0 M) ee.symm.toEquiv
  let d := O.f.hom.toAddMonoidHom
  let n := O.g.hom.toAddMonoidHom
  have hd : Nat.card M = Nat.card d.ker * Nat.card d.range :=
    card_eq_ker_mul_range d
  have hn : Nat.card M = Nat.card n.ker * Nat.card n.range :=
    card_eq_ker_mul_range n
  have ho' : Nat.card (LinearMap.ker O.g.hom) =
      Nat.card O.homology * Nat.card d.range := by
    calc
      Nat.card (LinearMap.ker O.g.hom) = Nat.card (LinearMap.range O.moduleCatToCycles) *
          Nat.card (LinearMap.ker O.g.hom ⧸ LinearMap.range O.moduleCatToCycles) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card d.range * Nat.card O.homology := by
        rw [Nat.card_congr O.moduleCatHomologyIso.toLinearEquiv.toAddEquiv.toEquiv]
        rw [Nat.card_congr (rangeCodRestrictEquiv O.f.hom
          (LinearMap.ker O.g.hom) O.moduleCat_zero_apply).toEquiv]
        rfl
      _ = Nat.card O.homology * Nat.card d.range := mul_comm _ _
  have ho : Nat.card n.ker = Nat.card O.homology * Nat.card d.range := by
    simpa [n] using ho'
  have he' : Nat.card (LinearMap.ker E.g.hom) =
      Nat.card E.homology * Nat.card n.range := by
    calc
      Nat.card (LinearMap.ker E.g.hom) = Nat.card (LinearMap.range E.moduleCatToCycles) *
          Nat.card (LinearMap.ker E.g.hom ⧸ LinearMap.range E.moduleCatToCycles) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card n.range * Nat.card E.homology := by
        rw [Nat.card_congr E.moduleCatHomologyIso.toLinearEquiv.toAddEquiv.toEquiv]
        rw [Nat.card_congr (rangeCodRestrictEquiv E.f.hom
          (LinearMap.ker E.g.hom) E.moduleCat_zero_apply).toEquiv]
        rfl
      _ = Nat.card E.homology * Nat.card n.range := mul_comm _ _
  have he : Nat.card d.ker = Nat.card E.homology * Nat.card n.range := by
    simpa [d, E, O] using he'
  have hrangeD : 0 < Nat.card d.range := Nat.card_pos
  have hrangeN : 0 < Nat.card n.range := Nat.card_pos
  have hcard : Nat.card E.homology = Nat.card O.homology := by
    nlinarith [hd, hn, ho, he]
  rw [Nat.card_congr ee.toEquiv, Nat.card_congr eo.toEquiv] at hcard
  rw [herbrandQuotient, hcard]
  field_simp [Nat.card_pos.ne']

private theorem rep_shortExact_of_function
    {G : Type} [Group G] {A B C : Rep.{u} ℤ G}
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
      refine Representation.IntertwiningMap.ext ?_
      apply LinearMap.ext
      intro z
      change f ((lift s).hom z) = s.ι z
      simp only [lift]
      exact Classical.choose_spec ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
    exact Fork.IsLimit.mk _ lift lift_fac
      (fun s m hm => by
        have hm' : m ≫ f = s.ι := hm
        apply (cancel_mono f).1
        exact hm'.trans (lift_fac s).symm)
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ f_is_kernel
  · exact (Rep.mono_iff_injective f).2 hf
  · exact (Rep.epi_iff_surjective g).2 hg

private theorem herbrandQuotient_mul
    {G : Type} [Group G] [Fintype G] [IsCyclic G]
    (A B C : Rep.{u} ℤ G)
    [Finite (TateLowDegree.H0 A)] [Finite (TateLowDegree.HMinusOne A)]
    [Finite (TateLowDegree.H0 B)] [Finite (TateLowDegree.HMinusOne B)]
    [Finite (TateLowDegree.H0 C)] [Finite (TateLowDegree.HMinusOne C)]
    (f : A ⟶ B) (g : B ⟶ C)
    (hexact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    herbrandQuotient B = herbrandQuotient A * herbrandQuotient C := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  letI : Module ℤ C := C.hV2
  let gen := (IsCyclic.exists_generator (α := G)).choose
  have hgen := (IsCyclic.exists_generator (α := G)).choose_spec
  have hzero : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx : g (f x) = 0 := (hexact (f x)).2 ⟨x, rfl⟩
    exact hx
  let S : ShortComplex (Rep.{u} ℤ G) := ShortComplex.mk f g hzero
  letI : Mono f := (Rep.mono_iff_injective f).2 hf
  have f_is_kernel :
      IsLimit (KernelFork.ofι f hzero) := by
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
      refine Representation.IntertwiningMap.ext ?_
      apply LinearMap.ext
      intro z
      change f ((lift s).hom z) = s.ι z
      simp only [lift]
      exact Classical.choose_spec ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
    exact Fork.IsLimit.mk _ lift lift_fac
      (fun s m hm => by
        have hm' : m ≫ f = s.ι := by
          exact hm
        apply (cancel_mono f).1
        exact hm'.trans (lift_fac s).symm)
  have hS : S.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_of_f_is_kernel S f_is_kernel
    · exact (Rep.mono_iff_injective f).2 hf
    · exact (Rep.epi_iff_surjective g).2 hg
  let P (M : Rep.{u} ℤ G) := Rep.FiniteCyclicGroup.moduleCatCochainComplex M gen
  let PF : P A ⟶ P B := cyclicPeriodicHom gen f
  let PG : P B ⟶ P C := cyclicPeriodicHom gen g
  have hPFPG : PF ≫ PG = 0 := by
    ext i x
    exact congrArg (fun q : A ⟶ C => q.hom x) hzero
  let PS : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk PF PG hPFPG
  have hPS : PS.ShortExact := by
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
    intro i
    apply ShortComplex.ShortExact.mk'
    · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      ext x
      change (∃ y, f y = x) ↔ g x = 0
      exact (hexact x).symm
    · exact (ModuleCat.mono_iff_injective _).2 hf
    · exact (ModuleCat.epi_iff_surjective _).2 hg
  let e1 (M : Rep.{u} ℤ G) : (P M).homology 1 ≃+ TateLowDegree.HMinusOne M :=
    (cyclicOddIsoOne M gen).toLinearEquiv.toAddEquiv |>.trans
      (periodicOddEquivHMinusOne M gen hgen)
  let e2 (M : Rep.{u} ℤ G) : (P M).homology 2 ≃+ TateLowDegree.H0 M :=
    (cyclicEvenIsoTwo M gen).toLinearEquiv.toAddEquiv |>.trans
      (periodicEvenEquivH0 M gen hgen)
  let e3 (M : Rep.{u} ℤ G) : (P M).homology 3 ≃+ TateLowDegree.HMinusOne M :=
    (cyclicOddIsoThree M gen).toLinearEquiv.toAddEquiv |>.trans
      (periodicOddEquivHMinusOne M gen hgen)
  letI : Finite ((P A).homology 1) :=
    Finite.of_equiv (TateLowDegree.HMinusOne A) (e1 A).symm.toEquiv
  letI : Finite ((P B).homology 1) :=
    Finite.of_equiv (TateLowDegree.HMinusOne B) (e1 B).symm.toEquiv
  letI : Finite ((P C).homology 1) :=
    Finite.of_equiv (TateLowDegree.HMinusOne C) (e1 C).symm.toEquiv
  letI : Finite ((P A).homology 2) :=
    Finite.of_equiv (TateLowDegree.H0 A) (e2 A).symm.toEquiv
  letI : Finite ((P B).homology 2) :=
    Finite.of_equiv (TateLowDegree.H0 B) (e2 B).symm.toEquiv
  letI : Finite ((P C).homology 2) :=
    Finite.of_equiv (TateLowDegree.H0 C) (e2 C).symm.toEquiv
  letI : Finite ((P A).homology 3) :=
    Finite.of_equiv (TateLowDegree.HMinusOne A) (e3 A).symm.toEquiv
  letI : Finite ((P B).homology 3) :=
    Finite.of_equiv (TateLowDegree.HMinusOne B) (e3 B).symm.toEquiv
  let p1 := (HomologicalComplex.homologyMap PS.f 1).hom.toAddMonoidHom
  let q1 := (HomologicalComplex.homologyMap PS.g 1).hom.toAddMonoidHom
  let d1 := (hPS.δ 1 2 rfl).hom.toAddMonoidHom
  let p2 := (HomologicalComplex.homologyMap PS.f 2).hom.toAddMonoidHom
  let q2 := (HomologicalComplex.homologyMap PS.g 2).hom.toAddMonoidHom
  let d2 := (hPS.δ 2 3 rfl).hom.toAddMonoidHom
  let p3 := (HomologicalComplex.homologyMap PS.f 3).hom.toAddMonoidHom
  have hp1q1 : p1.range = q1.ker := by
    ext x
    change (∃ y, p1 y = x) ↔ q1 x = 0
    change (∃ y, (HomologicalComplex.homologyMap PS.f 1).hom y = x) ↔
      (HomologicalComplex.homologyMap PS.g 1).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₂ 1).moduleCat_range_eq_ker]
  have hq1d1 : q1.range = d1.ker := by
    ext x
    change (∃ y, q1 y = x) ↔ d1 x = 0
    change (∃ y, (HomologicalComplex.homologyMap PS.g 1).hom y = x) ↔
      (hPS.δ 1 2 rfl).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₃ 1 2 rfl).moduleCat_range_eq_ker]
  have hd1p2 : d1.range = p2.ker := by
    ext x
    change (∃ y, d1 y = x) ↔ p2 x = 0
    change (∃ y, (hPS.δ 1 2 rfl).hom y = x) ↔
      (HomologicalComplex.homologyMap PS.f 2).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₁ 1 2 rfl).moduleCat_range_eq_ker]
  have hp2q2 : p2.range = q2.ker := by
    ext x
    change (∃ y, p2 y = x) ↔ q2 x = 0
    change (∃ y, (HomologicalComplex.homologyMap PS.f 2).hom y = x) ↔
      (HomologicalComplex.homologyMap PS.g 2).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₂ 2).moduleCat_range_eq_ker]
  have hq2d2 : q2.range = d2.ker := by
    ext x
    change (∃ y, q2 y = x) ↔ d2 x = 0
    change (∃ y, (HomologicalComplex.homologyMap PS.g 2).hom y = x) ↔
      (hPS.δ 2 3 rfl).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₃ 2 3 rfl).moduleCat_range_eq_ker]
  have hd2p3 : d2.range = p3.ker := by
    ext x
    change (∃ y, d2 y = x) ↔ p3 x = 0
    change (∃ y, (hPS.δ 2 3 rfl).hom y = x) ↔
      (HomologicalComplex.homologyMap PS.f 3).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hPS.homology_exact₁ 2 3 rfl).moduleCat_range_eq_ker]
  let oddPeriod (M : Rep.{u} ℤ G) : (P M).homology 1 ≃+ (P M).homology 3 :=
    (cyclicOddIsoOne M gen).toLinearEquiv.toAddEquiv |>.trans
      (cyclicOddIsoThree M gen).symm.toLinearEquiv.toAddEquiv
  have hp13 (x : (P A).homology 1) : oddPeriod B (p1 x) = p3 (oddPeriod A x) := by
    apply (ModuleCat.mono_iff_injective (cyclicOddIsoThree B gen).hom).1 inferInstance
    calc
      _ = (cyclicOddIsoOne B gen).hom (p1 x) := by simp [oddPeriod]
      _ = (ShortComplex.homologyMap (cyclicPeriodicSCMap gen f))
          ((cyclicOddIsoOne A gen).hom x) := by
        have h := ConcreteCategory.congr_hom
          (cyclicPeriodicHom_naturality_one gen f) x
        simpa [p1, PS, PF] using h
      _ = (ShortComplex.homologyMap (cyclicPeriodicSCMap gen f))
          ((cyclicOddIsoThree A gen).hom (oddPeriod A x)) := by simp [oddPeriod]
      _ = (cyclicOddIsoThree B gen).hom (p3 (oddPeriod A x)) := by
        have h := ConcreteCategory.congr_hom
          (cyclicPeriodicHom_naturality_three gen f) (oddPeriod A x)
        simpa [p3, PS, PF] using h.symm
  have hrange : Nat.card p1.range = Nat.card p3.range := by
    rw [Nat.card_congr (rangeEquivOfCommute p1 p3 (oddPeriod A) (oddPeriod B) hp13)]
  have hcard := card_cycle p1 q1 d1 p2 q2 d2 p3 hp1q1 hq1d1 hd1p2 hp2q2
    hq2d2 hd2p3 (Nat.card_congr (oddPeriod A).toEquiv) hrange
  rw [Nat.card_congr (e2 B).toEquiv, Nat.card_congr (e1 A).toEquiv,
    Nat.card_congr (e1 C).toEquiv, Nat.card_congr (e1 B).toEquiv,
    Nat.card_congr (e2 A).toEquiv, Nat.card_congr (e2 C).toEquiv] at hcard
  unfold herbrandQuotient
  field_simp [Nat.card_pos.ne']
  exact_mod_cast hcard

/--
**F04**, Lemma `lem:herbrand-rules`: finite modules and induced modules have Herbrand quotient
one, the trivial integer module has quotient `|G|`, and the quotient is multiplicative in a short
exact sequence.  The explicit `Finite` binders are part of the theorem: without them, `Nat.card`
turns an infinite Tate group into zero and the division/multiplicativity statements are false.
-/
theorem herbrandQuotient_rules
    {G : Type} [Group G] [Fintype G] [IsCyclic G] :
    (∀ (M : Rep ℤ G) [Finite M]
      [Finite (TateLowDegree.H0 M)] [Finite (TateLowDegree.HMinusOne M)],
        herbrandQuotient M = 1) ∧
    (∀ [Finite (TateLowDegree.H0 (Rep.trivial ℤ G ℤ))]
      [Finite (TateLowDegree.HMinusOne (Rep.trivial ℤ G ℤ))],
      0 < Nat.card (TateLowDegree.H0 (Rep.trivial ℤ G ℤ)) ∧
        0 < Nat.card (TateLowDegree.HMinusOne (Rep.trivial ℤ G ℤ)) ∧
        herbrandQuotient (Rep.trivial ℤ G ℤ) = Nat.card G) ∧
    (∀ (A : Type) [AddCommGroup A] [Module ℤ A]
      [Finite (TateLowDegree.H0 (InducedFromTrivial G A))]
      [Finite (TateLowDegree.HMinusOne (InducedFromTrivial G A))],
        herbrandQuotient (InducedFromTrivial G A) = 1) ∧
    (∀ (A B C : Rep ℤ G)
      [Finite (TateLowDegree.H0 A)] [Finite (TateLowDegree.HMinusOne A)]
      [Finite (TateLowDegree.H0 B)] [Finite (TateLowDegree.HMinusOne B)]
      [Finite (TateLowDegree.H0 C)] [Finite (TateLowDegree.HMinusOne C)]
      (f : A ⟶ B) (g : B ⟶ C),
      Function.Exact f g → Function.Injective f → Function.Surjective g →
        herbrandQuotient B = herbrandQuotient A * herbrandQuotient C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M _ _ _
    exact herbrandQuotient_finite M
  · intros
    let T := Rep.trivial ℤ G ℤ
    have h0card : Nat.card (TateLowDegree.H0 T) = Nat.card G := by
      rw [Nat.card_congr trivialH0EquivZMod.toEquiv, Nat.card_zmod]
    have hmcard : Nat.card (TateLowDegree.HMinusOne T) = 1 := by
      letI : Subsingleton (TateLowDegree.HMinusOne T) :=
        trivialHMinusOne_subsingleton
      exact Nat.card_unique
    refine ⟨h0card ▸ Nat.card_pos, hmcard ▸ Nat.zero_lt_one, ?_⟩
    rw [herbrandQuotient, h0card, hmcard]
    norm_num
  · intro A _ _ _ _
    let I := InducedFromTrivial G A
    let T : Subgroup G := ⊤
    letI : Fintype T := Fintype.ofFinite T
    let N := Rep.res T.subtype I
    have ht0 : Subsingleton (tateCohomology N 0) :=
      inducedFromTrivial_tateAcyclic G A T 0
    have htm : Subsingleton (tateCohomology N (-1)) :=
      inducedFromTrivial_tateAcyclic G A T (-1)
    have hn0 : Subsingleton (TateLowDegree.H0 N) :=
      ⟨fun x y => (TateLowDegree.comparisonH0Tate N).injective (ht0.elim _ _)⟩
    have hnm : Subsingleton (TateLowDegree.HMinusOne N) := by
      let e := (TateLowDegree.HMinusOne_equiv_tate N).some
      exact ⟨fun x y => e.injective (htm.elim _ _)⟩
    let e0 := topResH0Equiv I
    let em := topResHMinusOneEquiv I
    letI : Subsingleton (TateLowDegree.H0 I) :=
      ⟨fun x y => e0.injective (hn0.elim _ _)⟩
    letI : Subsingleton (TateLowDegree.HMinusOne I) :=
      ⟨fun x y => em.injective (hnm.elim _ _)⟩
    exact herbrandQuotient_eq_one_of_subsingleton I
  · intro A B C _ _ _ _ _ _ f g hexact hf hg
    exact herbrandQuotient_mul A B C f g hexact hf hg


variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

private theorem normalizedValuation_algEquiv_cyclic
    (σ : L ≃ₐ[K] L) (x : Units L) :
    normalizedValuation L (Units.map σ.toRingEquiv.toRingHom x) =
      normalizedValuation L x := by
  have hnorm : normUnitsHom K L (Units.map σ.toRingEquiv.toRingHom x) =
      normUnitsHom K L x := by
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv σ (x : L)
  have h₁ := normalizedValuation_norm K L (Units.map σ.toRingEquiv.toRingHom x)
  have h₂ := normalizedValuation_norm K L x
  rw [hnorm, h₂] at h₁
  have hf : 0 < residueDegree K L := by
    dsimp [residueDegree]
    exact (ramificationInvariants_exists K L).choose_spec.choose_spec.2.1
  nlinarith

private theorem mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic
    (x : Units L) :
    x ∈ unitSubgroup L ↔ normalizedValuation L x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hnonneg : 0 ≤ normalizedValuation L (ringUnitsToFieldUnits L u) :=
      (exists_normalizedValuationHom L).choose_spec.2 _ |>.2 ⟨u, rfl⟩
    have hinvnonneg : 0 ≤ normalizedValuation L ((ringUnitsToFieldUnits L u)⁻¹) :=
      (exists_normalizedValuationHom L).choose_spec.2 _ |>.2 ⟨↑u⁻¹, rfl⟩
    have hneg : normalizedValuation L ((ringUnitsToFieldUnits L u)⁻¹) =
        -normalizedValuation L (ringUnitsToFieldUnits L u) := by
      simp [normalizedValuation]
    omega
  · intro hx
    have hxi : 0 ≤ normalizedValuation L x := hx.ge
    have hxinv : normalizedValuation L x⁻¹ = 0 := by
      have h := normalizedValuation_mul L x x⁻¹
      have hzero : normalizedValuation L 1 = 0 := by simp [normalizedValuation]
      rw [mul_inv_cancel, hzero, hx, zero_add] at h
      exact h.symm
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom L).choose_spec.2 x |>.1 hxi
    obtain ⟨b, hb⟩ := (exists_normalizedValuationHom L).choose_spec.2 x⁻¹ |>.1 hxinv.ge
    let u : Units (RingOfIntegers L) :=
      { val := a
        inv := b
        val_inv := by apply Subtype.ext; dsimp; rw [ha, hb]; simp
        inv_val := by apply Subtype.ext; dsimp; rw [ha, hb]; simp }
    refine ⟨u, ?_⟩
    apply Units.ext
    exact ha

/--
**F04**, Proposition `prop:herbrand-local-units`: the actual integral-unit subgroup is stable
under every `K`-automorphism of `L`.
-/
theorem localUnitSubgroup_stable (σ : L ≃ₐ[K] L) (x : Units L)
    (hx : x ∈ unitSubgroup L) :
    Units.map σ.toRingEquiv.toRingHom x ∈ unitSubgroup L := by
  rw [mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic (L := L),
    normalizedValuation_algEquiv_cyclic K L]
  exact (mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic (L := L) x).1 hx

/--
**F04**, Proposition `prop:herbrand-local-units`: the actual representation on `𝒪_Lˣ`.
-/
noncomputable def localUnitRep : Rep ℤ (L ≃ₐ[K] L) :=
  stableUnitSubgroupRep K L (unitSubgroup L) (localUnitSubgroup_stable K L)

private noncomputable def localUnitInclusion :
    localUnitRep K L ⟶ MulRep K L :=
  (MulRep K L).subtype (unitSubgroup L).toAddSubgroup.toIntSubmodule (by
    intro σ x hx
    change Units.map σ.toRingEquiv.toRingHom (Additive.toMul x) ∈ unitSubgroup L
    exact localUnitSubgroup_stable K L σ _ hx)

private noncomputable def normalizedValuationAddHom_cyclic : Additive (Units L) →+ ℤ where
  toFun x := normalizedValuation L x.toMul
  map_zero' := by simp [normalizedValuation]
  map_add' x y := normalizedValuation_mul L x.toMul y.toMul

private noncomputable def valuationCoefficient_cyclic :
    MulRep K L ⟶ Rep.trivial ℤ (L ≃ₐ[K] L) ℤ :=
  Rep.ofHom ⟨(normalizedValuationAddHom_cyclic L).toIntLinearMap, fun σ => by
    apply LinearMap.ext
    intro x
    change normalizedValuation L
        (Units.map σ.toRingEquiv.toRingHom.toMonoidHom x.toMul) =
      normalizedValuation L x.toMul
    exact normalizedValuation_algEquiv_cyclic K L σ x.toMul⟩

private noncomputable def valuationSequence_cyclic :
    ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (localUnitInclusion K L) (valuationCoefficient_cyclic K L) (by
    ext x
    change normalizedValuation L (Additive.toMul (x.1 : Additive (Units L))) = 0
    exact (mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic
      (L := L) (Additive.toMul x.1)).1 x.2)

private noncomputable def valuationKernelLift_cyclic
    (s : KernelFork (valuationCoefficient_cyclic K L)) :
    s.pt ⟶ localUnitRep K L := by
  letI : Module ℤ s.pt := s.pt.hV2
  let W := (unitSubgroup L).toAddSubgroup.toIntSubmodule
  let lift : s.pt →ₗ[ℤ] W :=
    s.ι.hom.toLinearMap.codRestrict W fun z => by
      have hcond : s.ι ≫ valuationCoefficient_cyclic K L = 0 := KernelFork.condition s
      have hz := congrArg (fun q : s.pt ⟶ Rep.trivial ℤ (L ≃ₐ[K] L) ℤ => q.hom z) hcond
      change normalizedValuation L (Additive.toMul (s.ι.hom z)) = 0 at hz
      exact (mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic
        (L := L) (Additive.toMul (s.ι.hom z))).2 hz
  exact Rep.ofHom ⟨lift, fun g => by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact Rep.hom_comm_apply s.ι g z⟩

private noncomputable def valuationInclusionIsKernel_cyclic :
    IsLimit (KernelFork.ofι (localUnitInclusion K L) (valuationSequence_cyclic K L).zero) :=
  Fork.IsLimit.mk _ (valuationKernelLift_cyclic K L)
    (fun s => by
      letI : Module ℤ s.pt := s.pt.hV2
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      rfl)
    (fun s m hm => by
      letI : Module ℤ s.pt := s.pt.hV2
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact congrArg (fun q : s.pt ⟶ MulRep K L => q.hom z) hm)

private theorem valuationSequence_cyclic_shortExact :
    (valuationSequence_cyclic K L).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ (valuationInclusionIsKernel_cyclic K L)
  · exact (Rep.mono_iff_injective _).2 fun x y h => Subtype.ext h
  · apply (Rep.epi_iff_surjective _).2
    intro n
    obtain ⟨x, hx⟩ := normalizedValuation_surjective L n
    exact ⟨Additive.ofMul x, hx⟩

variable [IsCyclic (L ≃ₐ[K] L)]

private theorem deepUnitQuotient_finite (π : Uniformizer K) (D : DeepUnitFiltrationData K L π) :
    Finite ((unitSubgroup L) ⧸ (D.V 0).comap (unitSubgroup L).subtype) := by
  let U := unitSubgroup L
  let V : Subgroup U := (D.V 0).comap U.subtype
  let rinj : Function.Injective (ringUnitsToFieldUnits L) := by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val h
  let e : Units (RingOfIntegers L) ≃* U :=
    MulEquiv.ofBijective (ringUnitsToFieldUnits L).rangeRestrict ⟨
      (fun x y h => rinj (congrArg Subtype.val h)), fun x => by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨y, Subtype.ext hy⟩⟩
  obtain ⟨r, hr⟩ := D.V_cofinal_principal_right 0
  let red : U →* Units (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)) :=
    (integralUnitReduction L (r + 1)).comp e.symm.toMonoidHom
  haveI : Finite (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)) :=
    (IsLocalRing.finite_quotient_iff).2 ⟨r + 1, le_rfl⟩
  let P : Subgroup U := (principalUnitSubgroup L (r + 1)).comap U.subtype
  have hP : P = red.ker := by
    ext x
    change (x : Units L) ∈ principalUnitSubgroup L (r + 1) ↔ red x = 1
    constructor
    · rintro ⟨y, hy, heq⟩
      change integralUnitReduction L (r + 1) (e.symm x) = 1
      have hey : e y = x := by
        apply Subtype.ext
        exact heq
      rw [← hey, e.symm_apply_apply]
      exact hy
    · intro hx
      refine ⟨e.symm x, hx, ?_⟩
      change ringUnitsToFieldUnits L (e.symm x) = (x : Units L)
      exact congrArg Subtype.val (e.apply_symm_apply x)
  haveI : Finite red.range := Finite.of_injective (fun x : red.range => (x :
    Units (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)))) Subtype.val_injective
  haveI : Finite (U ⧸ red.ker) :=
    Finite.of_equiv red.range (QuotientGroup.quotientKerEquivRange red).symm.toEquiv
  letI : P.FiniteIndex := by rw [hP]; exact Subgroup.finiteIndex_of_finite_quotient
  have hPV : P ≤ V := by
    intro x hx
    exact hr hx
  letI : V.FiniteIndex := Subgroup.finiteIndex_of_le hPV
  exact Subgroup.finite_quotient_of_finiteIndex


/--
**F04**, Proposition `prop:herbrand-local-units`: both Tate groups used in the quotient are finite
and `h_G(𝒪_Lˣ)=1` for the actual integral-unit representation.
-/
theorem cyclic_local_units_herbrand :
    ∃ h : HerbrandFinite (localUnitRep K L),
      @herbrandQuotient _ _ _ (localUnitRep K L) h.h0 h.h1 = 1 := by
  let π := defaultUniformizer K
  obtain ⟨D, hD⟩ := deepUnitFiltration_exists K L π
  let U := unitSubgroup L
  let V := D.V 0
  let VU : Subgroup U := V.comap U.subtype
  let base : localUnitRep K L ≃+ Additive U :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul x.1, x.2⟩
      invFun := fun x => ⟨Additive.ofMul (x.toMul : Units L), x.toMul.2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl }
  let W : Submodule ℤ (localUnitRep K L) :=
    VU.toAddSubgroup.toIntSubmodule.comap base.toAddMonoidHom.toIntLinearMap
  have W_stable : ∀ σ, W ≤ W.comap ((localUnitRep K L).ρ σ) := by
    intro σ x hx
    change Units.map σ.toRingEquiv.toRingHom (Additive.toMul x.1) ∈ V
    exact D.V_stable 0 σ _ hx
  let Q : Rep.{0, 0, 0} ℤ (L ≃ₐ[K] L) :=
    Rep.quotient (localUnitRep K L) W W_stable
  let deep : Rep.{0, 0, 0} ℤ (L ≃ₐ[K] L) :=
    stableUnitSubgroupRep K L V (D.V_stable 0)
  let incLinear : deep →ₗ[ℤ] localUnitRep K L :=
    { toFun := fun x => ⟨x.1, D.V_le_integralUnits 0 x.2⟩
      map_add' := fun x y => by apply Subtype.ext; rfl
      map_smul' := fun n x => by apply Subtype.ext; rfl }
  let inc : deep ⟶ localUnitRep K L := Rep.ofHom ⟨incLinear, fun σ => by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl⟩
  let proj : localUnitRep K L ⟶ Q := Rep.mkQ (localUnitRep K L) W W_stable
  have hzero : inc ≫ proj = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change Submodule.Quotient.mk (incLinear x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact x.2
  let S : ShortComplex (Rep.{0, 0, 0} ℤ (L ≃ₐ[K] L)) :=
    ShortComplex.mk inc proj hzero
  have hexact : Function.Exact inc proj := by
    intro x
    rw [show proj x = 0 ↔ x ∈ W by
      exact Submodule.Quotient.mk_eq_zero W]
    constructor
    · intro hx
      refine ⟨⟨x.1, hx⟩, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨y, rfl⟩
      exact y.2
  have hinc : Function.Injective inc := fun x y h => by
    apply Subtype.ext
    exact congrArg (fun z : localUnitRep K L => (z.1 : Additive (Units L))) h
  have hproj : Function.Surjective proj := W.mkQ_surjective
  have hS : S.ShortExact :=
    rep_shortExact_of_function inc proj hzero hexact hinc hproj
  letI : Finite (U ⧸ VU) := deepUnitQuotient_finite K L π D
  have base_mem (x : localUnitRep K L) :
      x ∈ W ↔ base x ∈ VU.toAddSubgroup := Iff.rfl
  let qb : (localUnitRep K L ⧸ W.toAddSubgroup) →+
      (Additive U ⧸ VU.toAddSubgroup) :=
    QuotientAddGroup.map _ _ base.toAddMonoidHom (fun x hx => (base_mem x).1 hx)
  let qbi : (Additive U ⧸ VU.toAddSubgroup) →+
      (localUnitRep K L ⧸ W.toAddSubgroup) :=
    QuotientAddGroup.map _ _ base.symm.toAddMonoidHom (by
      intro x hx
      exact (base_mem (base.symm x)).2 (by simpa using hx))
  have hqleft : Function.LeftInverse qbi qb := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [qb, qbi]
  have hqright : Function.RightInverse qbi qb := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [qb, qbi]
  let eqQ : (localUnitRep K L ⧸ W.toAddSubgroup) ≃+
      (Additive U ⧸ VU.toAddSubgroup) :=
    AddEquiv.ofBijective qb ⟨hqleft.injective, hqright.surjective⟩
  letI : Finite Q := Finite.of_equiv (Additive (U ⧸ VU)) eqQ.symm.toEquiv
  let T : Subgroup (L ≃ₐ[K] L) := ⊤
  letI : Fintype T := Fintype.ofFinite T
  let deepTop := Rep.res T.subtype deep
  have hdt0 : Subsingleton (tateCohomology deepTop 0) := hD T 0
  have hdtm : Subsingleton (tateCohomology deepTop (-1)) := hD T (-1)
  have hdtop0 : Subsingleton (TateLowDegree.H0 deepTop) :=
    ⟨fun x y => (TateLowDegree.comparisonH0Tate deepTop).injective (hdt0.elim _ _)⟩
  have hdtopm : Subsingleton (TateLowDegree.HMinusOne deepTop) := by
    let e := (TateLowDegree.HMinusOne_equiv_tate deepTop).some
    exact ⟨fun x y => e.injective (hdtm.elim _ _)⟩
  let ed0 := topResH0Equiv deep
  let edm := topResHMinusOneEquiv deep
  letI : Subsingleton (TateLowDegree.H0 deep) :=
    ⟨fun x y => ed0.injective (hdtop0.elim _ _)⟩
  letI : Subsingleton (TateLowDegree.HMinusOne deep) :=
    ⟨fun x y => edm.injective (hdtopm.elim _ _)⟩
  letI : Finite (TateLowDegree.H0 deep) := Finite.of_subsingleton
  letI : Finite (TateLowDegree.HMinusOne deep) := Finite.of_subsingleton
  letI : Finite (TateLowDegree.H0 Q) := inferInstance
  letI : Finite (TateLowDegree.HMinusOne Q) := inferInstance
  let TS := S.map (tateComplexFunctor ℤ (L ≃ₐ[K] L))
  have hTS : TS.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact hS
  let tD0 := TS.X₁.homology 0
  let tU0 := TS.X₂.homology 0
  let tQ0 := TS.X₃.homology 0
  letI : Finite tD0 := Finite.of_equiv (TateLowDegree.H0 deep)
    (TateLowDegree.comparisonH0Tate deep).toEquiv
  letI : Finite tQ0 := Finite.of_equiv (TateLowDegree.H0 Q)
    (TateLowDegree.comparisonH0Tate Q).toEquiv
  let p0 : tD0 →+ tU0 :=
    (HomologicalComplex.homologyMap TS.f 0).hom.toAddMonoidHom
  let q0 : tU0 →+ tQ0 :=
    (HomologicalComplex.homologyMap TS.g 0).hom.toAddMonoidHom
  have hpq0 : p0.range = q0.ker := by
    ext x
    change (∃ y, p0 y = x) ↔ q0 x = 0
    change (∃ y, (HomologicalComplex.homologyMap TS.f 0).hom y = x) ↔
      (HomologicalComplex.homologyMap TS.g 0).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hTS.homology_exact₂ 0).moduleCat_range_eq_ker]
  letI : Finite tU0 := finite_middle_of_range_eq_ker p0 q0 hpq0
  letI : Finite (TateLowDegree.H0 (localUnitRep K L)) :=
    Finite.of_equiv tU0
      (TateLowDegree.comparisonH0Tate (localUnitRep K L)).symm.toEquiv
  let tDm := TS.X₁.homology (-1)
  let tUm := TS.X₂.homology (-1)
  let tQm := TS.X₃.homology (-1)
  let emD := (TateLowDegree.HMinusOne_equiv_tate deep).some
  let emQ := (TateLowDegree.HMinusOne_equiv_tate Q).some
  letI : Finite tDm := Finite.of_equiv (TateLowDegree.HMinusOne deep) emD.toEquiv
  letI : Finite tQm := Finite.of_equiv (TateLowDegree.HMinusOne Q) emQ.toEquiv
  let pm : tDm →+ tUm :=
    (HomologicalComplex.homologyMap TS.f (-1)).hom.toAddMonoidHom
  let qm : tUm →+ tQm :=
    (HomologicalComplex.homologyMap TS.g (-1)).hom.toAddMonoidHom
  have hpqm : pm.range = qm.ker := by
    ext x
    change (∃ y, pm y = x) ↔ qm x = 0
    change (∃ y, (HomologicalComplex.homologyMap TS.f (-1)).hom y = x) ↔
      (HomologicalComplex.homologyMap TS.g (-1)).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hTS.homology_exact₂ (-1)).moduleCat_range_eq_ker]
  letI : Finite tUm := finite_middle_of_range_eq_ker pm qm hpqm
  let emU := (TateLowDegree.HMinusOne_equiv_tate (localUnitRep K L)).some
  letI : Finite (TateLowDegree.HMinusOne (localUnitRep K L)) :=
    Finite.of_equiv tUm emU.symm.toEquiv
  let h : HerbrandFinite (localUnitRep K L) := ⟨inferInstance, inferInstance⟩
  refine ⟨h, ?_⟩
  have hdq := herbrandQuotient_eq_one_of_subsingleton deep
  have hqq := (herbrandQuotient_rules.{0, 0} (G := L ≃ₐ[K] L)).1 Q
  have hmul := (herbrandQuotient_rules.{0, 0} (G := L ≃ₐ[K] L)).2.2.2
    deep (localUnitRep K L) Q inc proj hexact hinc hproj
  rw [hmul, hdq, hqq, mul_one]

/--
**F04**, Proposition `prop:cyclic-H2`: the valuation exact sequence gives finite Tate groups and
`h_G(Lˣ)=[L:K]`.
-/
theorem cyclic_local_herbrand :
    ∃ h : HerbrandFinite (MulRep K L),
      @herbrandQuotient _ _ _ (MulRep K L) h.h0 h.h1 = Module.finrank K L := by
  obtain ⟨hU, hUq⟩ := cyclic_local_units_herbrand K L
  letI : Finite (TateLowDegree.H0 (localUnitRep K L)) := hU.h0
  letI : Finite (TateLowDegree.HMinusOne (localUnitRep K L)) := hU.h1
  let T := Rep.trivial ℤ (L ≃ₐ[K] L) ℤ
  letI : Subsingleton (TateLowDegree.HMinusOne T) :=
    trivialHMinusOne_subsingleton
  letI : Finite (TateLowDegree.HMinusOne T) := Finite.of_subsingleton
  letI : NeZero (Nat.card (L ≃ₐ[K] L)) := ⟨Nat.card_pos.ne'⟩
  letI : Finite (TateLowDegree.H0 T) :=
    Finite.of_equiv (ZMod (Nat.card (L ≃ₐ[K] L)))
      trivialH0EquivZMod.symm.toEquiv
  have hH1 : Subsingleton (Inhomogeneous.H1 (MulRep K L)) :=
    hilbert90_mulRep_inhomogeneous K L
  letI : Subsingleton (TateLowDegree.HMinusOne (MulRep K L)) :=
    ⟨fun x y => (cyclicH1EquivHMinusOne (MulRep K L)).symm.injective
      (hH1.elim _ _)⟩
  letI : Finite (TateLowDegree.HMinusOne (MulRep K L)) := Finite.of_subsingleton
  let S := valuationSequence_cyclic K L
  have hS : S.ShortExact := valuationSequence_cyclic_shortExact K L
  let TS := S.map (tateComplexFunctor ℤ (L ≃ₐ[K] L))
  let tU := TS.X₁.homology 0
  let tM := TS.X₂.homology 0
  let tT := TS.X₃.homology 0
  letI : Finite tU := Finite.of_equiv (TateLowDegree.H0 (localUnitRep K L))
    (TateLowDegree.comparisonH0Tate (localUnitRep K L)).toEquiv
  letI : Finite tT := Finite.of_equiv (TateLowDegree.H0 T)
    (TateLowDegree.comparisonH0Tate T).toEquiv
  let p : tU →+ tM :=
    (HomologicalComplex.homologyMap TS.f 0).hom.toAddMonoidHom
  let q : tM →+ tT :=
    (HomologicalComplex.homologyMap TS.g 0).hom.toAddMonoidHom
  have hex := (TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ 0
  have hrk : p.range = q.ker := by
    ext x
    change (∃ y, p y = x) ↔ q x = 0
    change (∃ y, (HomologicalComplex.homologyMap TS.f 0).hom y = x) ↔
      (HomologicalComplex.homologyMap TS.g 0).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      hex.moduleCat_range_eq_ker]
  letI : Finite p.range := Finite.of_surjective
    (fun x : tU => (⟨p x, x, rfl⟩ : p.range)) (fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩)
  letI : Finite q.ker := Finite.of_injective (fun x : q.ker =>
    (⟨x, by rw [hrk]; exact x.2⟩ : p.range)) (fun x y h => by
      apply @Subtype.ext tM (fun z => q z = 0) x y
      have hv := congrArg (fun z : p.range => (z : tM)) h
      exact hv)
  letI : Finite q.range := Finite.of_injective (fun x : q.range => (x : tT))
    Subtype.val_injective
  letI : Finite tM := (q.finite_iff_finite_ker_range).2 ⟨inferInstance, inferInstance⟩
  letI : Finite (TateLowDegree.H0 (MulRep K L)) :=
    Finite.of_equiv tM (TateLowDegree.comparisonH0Tate (MulRep K L)).symm.toEquiv
  let h : HerbrandFinite (MulRep K L) := ⟨inferInstance, inferInstance⟩
  refine ⟨h, ?_⟩
  have htriv := (herbrandQuotient_rules.{0, 0} (G := L ≃ₐ[K] L)).2.1
  have hexact : Function.Exact (localUnitInclusion K L) (valuationCoefficient_cyclic K L) := by
    intro x
    constructor
    · intro hx
      change normalizedValuation L (Additive.toMul x) = 0 at hx
      exact ⟨⟨x, (mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic
        (L := L) (Additive.toMul x)).2 hx⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      change normalizedValuation L (Additive.toMul (u.1 : Additive (Units L))) = 0
      exact (mem_unitSubgroup_iff_normalizedValuation_eq_zero_cyclic
        (L := L) (Additive.toMul u.1)).1 u.2
  have hmul := (herbrandQuotient_rules.{0, 0} (G := L ≃ₐ[K] L)).2.2.2
    (localUnitRep K L) (MulRep K L) T (localUnitInclusion K L)
      (valuationCoefficient_cyclic K L) hexact
      (fun x y hxy => Subtype.ext hxy) (by
        intro n
        obtain ⟨x, hx⟩ := normalizedValuation_surjective L n
        exact ⟨Additive.ofMul x, hx⟩)
  rw [hmul, hUq, one_mul, htriv.2.2, IsGalois.card_aut_eq_finrank]

/--
**F04**, Proposition `prop:cyclic-H2`: cyclic local `H²` is finite.  This declaration is separate
from the cardinality formula so later arguments can install the `Finite` instance explicitly.
-/
theorem cyclic_local_H2_finite :
    Finite (Inhomogeneous.H2 (MulRep K L)) := by
  obtain ⟨h, _⟩ := cyclic_local_herbrand K L
  letI : Finite (TateLowDegree.H0 (MulRep K L)) := h.h0
  exact Finite.of_equiv (TateLowDegree.H0 (MulRep K L))
    (cyclicH2EquivH0 (MulRep K L)).symm

/--
**F04**, Proposition `prop:cyclic-H2`: for a cyclic local extension,
`|H²(G,Lˣ)|=[L:K]`.
-/
theorem cyclic_local_H2_card :
    Nat.card (Inhomogeneous.H2 (MulRep K L)) = Module.finrank K L := by
  obtain ⟨h, hq⟩ := cyclic_local_herbrand K L
  letI : Finite (TateLowDegree.H0 (MulRep K L)) := h.h0
  letI : Finite (TateLowDegree.HMinusOne (MulRep K L)) := h.h1
  have hH1 : Subsingleton (Inhomogeneous.H1 (MulRep K L)) :=
    hilbert90_mulRep_inhomogeneous K L
  have hminus : Subsingleton (TateLowDegree.HMinusOne (MulRep K L)) :=
    ⟨fun x y => (cyclicH1EquivHMinusOne (MulRep K L)).symm.injective
      (hH1.elim _ _)⟩
  letI := hminus
  have hmcard : Nat.card (TateLowDegree.HMinusOne (MulRep K L)) = 1 :=
    Nat.card_unique
  rw [herbrandQuotient, hmcard] at hq
  norm_num at hq
  rw [Nat.card_congr (cyclicH2EquivH0 (MulRep K L)).toEquiv]
  exact_mod_cast hq

end

end NU.LCFT
