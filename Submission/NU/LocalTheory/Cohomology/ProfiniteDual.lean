import Mathlib
import Submission.NU.LocalTheory.Cohomology.CupZero

/-!
# Profinite evaluation duality

This file proves reflexivity of the explicit elementary quotient against
continuous `ZMod`-valued characters.  It also supplies compactness of the
absolute Galois group over imperfect fields by comparing with the Galois
group of the separable closure.
-/

namespace NU.LocalTheory
noncomputable section

private noncomputable def testRestrictSep
    {M : Type*} [Field M] :
    Field.absoluteGaloisGroup M →*
      (separableClosure M (AlgebraicClosure M) ≃ₐ[M]
        separableClosure M (AlgebraicClosure M)) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  exact AlgEquiv.restrictNormalHom S

private theorem testRestrictSep_bijective
    {M : Type*} [Field M] : Function.Bijective (testRestrictSep (M := M)) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  constructor
  · intro σ τ h
    apply AlgEquiv.ext
    intro y
    have heq : σ.toRingEquiv.toRingHom = τ.toRingEquiv.toRingHom := by
      apply IsPurelyInseparable.injective_comp_algebraMap S A A
      ext x
      change AlgEquiv.restrictNormalHom S
          (show A ≃ₐ[M] A from σ) =
        AlgEquiv.restrictNormalHom S (show A ≃ₐ[M] A from τ) at h
      have hx := DFunLike.congr_fun h x
      have hxv := congrArg Subtype.val hx
      change (show A ≃ₐ[M] A from σ) (x : A) =
        (show A ≃ₐ[M] A from τ) (x : A)
      simpa only [AlgEquiv.restrictNormalHom_apply] using hxv
    exact DFunLike.congr_fun heq y
  · exact AlgEquiv.restrictNormalHom_surjective (F := M) (K₁ := S) A

private noncomputable def testRestrictSepEquiv
    {M : Type*} [Field M] :
    Field.absoluteGaloisGroup M ≃*
      (separableClosure M (AlgebraicClosure M) ≃ₐ[M]
        separableClosure M (AlgebraicClosure M)) :=
  MulEquiv.ofBijective testRestrictSep testRestrictSep_bijective

private theorem testRestrictSep_continuous
    {M : Type*} [Field M] : Continuous (testRestrictSep (M := M)) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  exact InfiniteGalois.restrictNormalHom_continuous S

private theorem testRestrictSepEquiv_symm_continuous
    {M : Type*} [Field M] : Continuous (testRestrictSepEquiv (M := M)).symm := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  apply continuous_of_continuousAt_one (testRestrictSepEquiv (M := M)).symm.toMonoidHom
  rw [continuousAt_def]
  intro U hU
  have hU1 : U ∈ nhds (1 : Field.absoluteGaloisGroup M) := by
    simpa only [map_one] using hU
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff M A U).mp hU1
  let Esep := separableClosure M E
  let iEA : E →ₐ[M] A := E.val
  let iES : Esep →ₐ[M] S :=
    { toFun := fun x => ⟨(x.1.1 : A),
        (map_mem_separableClosure_iff iEA).2 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let L : IntermediateField M S := iES.fieldRange
  let eEL : Esep ≃ₐ[M] L := AlgEquiv.ofInjectiveField iES
  letI : FiniteDimensional M E := hEfin
  letI : FiniteDimensional M Esep := FiniteDimensional.of_injective
    Esep.val.toLinearMap Esep.val.injective
  letI : FiniteDimensional M L := eEL.toLinearEquiv.finiteDimensional
  have hfix : ∀ ρ : S ≃ₐ[M] S, ρ ∈ L.fixingSubgroup →
      (testRestrictSepEquiv (M := M)).symm ρ ∈ E.fixingSubgroup := by
    intro ρ hρ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hρ
    apply (IntermediateField.mem_fixingSubgroup_iff E _).2
    intro x hx
    let σ : A ≃ₐ[M] A := (testRestrictSepEquiv (M := M)).symm ρ
    let f : E →ₐ[M] A := σ.toAlgHom.comp E.val
    let g : E →ₐ[M] A := E.val
    have hfg : f = g := by
      apply AlgHom.coe_ringHom_injective
      apply IsPurelyInseparable.injective_comp_algebraMap Esep E A
      ext y
      change σ (y.1.1 : A) = (y.1.1 : A)
      have hyL : iES y ∈ L := (AlgHom.mem_fieldRange).2 ⟨y, rfl⟩
      have hrho : ρ (iES y) = iES y := hρ _ hyL
      have hrs : testRestrictSep (M := M) σ = ρ := by
        exact (testRestrictSepEquiv (M := M)).apply_symm_apply ρ
      change AlgEquiv.restrictNormalHom S σ = ρ at hrs
      have hrsfun := DFunLike.congr_fun hrs (iES y)
      have hrsfunv := congrArg Subtype.val hrsfun
      have hrhov := congrArg Subtype.val hrho
      rw [hrhov] at hrsfunv
      rw [AlgEquiv.restrictNormalHom_apply] at hrsfunv
      change σ (y.1.1 : A) = (y.1.1 : A) at hrsfunv
      exact hrsfunv
    exact DFunLike.congr_fun hfg ⟨x, hx⟩
  apply Filter.mem_of_superset (L.fixingSubgroup_isOpen.mem_nhds L.fixingSubgroup.one_mem)
  intro ρ hρ
  exact hEU (hfix ρ hρ)

private noncomputable def testAbsoluteContinuousEquiv
    {M : Type*} [Field M] :
    Field.absoluteGaloisGroup M ≃ₜ*
      (separableClosure M (AlgebraicClosure M) ≃ₐ[M]
        separableClosure M (AlgebraicClosure M)) where
  toMulEquiv := testRestrictSepEquiv
  continuous_toFun := testRestrictSep_continuous
  continuous_invFun := testRestrictSepEquiv_symm_continuous

/-- The absolute Galois group is compact, including over imperfect fields. -/
theorem absoluteGaloisGroup_compactSpace
    {M : Type*} [Field M] : CompactSpace (Field.absoluteGaloisGroup M) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  exact (testAbsoluteContinuousEquiv (M := M)).symm.compactSpace

/-- The Krull topology on the absolute Galois group is totally disconnected. -/
theorem absoluteGaloisGroup_totallyDisconnectedSpace
    {M : Type*} [Field M] :
    TotallyDisconnectedSpace (Field.absoluteGaloisGroup M) := by
  change TotallyDisconnectedSpace
    (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M)
  infer_instance

private theorem testElementaryClass_surjective
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

private def testElementaryClassHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : G →* Multiplicative (ElementaryQuotient G n) :=
  AddMonoidHom.toMultiplicativeRight <|
    (ModN.mkQ n).comp <| MonoidHom.toAdditiveLeft <|
      QuotientGroup.mk' (Subgroup.topologicalClosure (commutator G))

@[simp]
private theorem testElementaryClassHom_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (g : G) :
    (testElementaryClassHom n g).toAdd = elementaryClass n g := by
  rfl

private theorem testEvaluationLinear_injective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {n : ℕ} [Fact n.Prime] :
    Function.Injective (evaluationLinear (G := G) n) := by
  classical
  intro x y hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let z := x - y
  have hzEval : evaluationLinear n z = 0 := by
    dsimp [z]
    rw [map_sub, hxy, sub_self]
  by_contra hz
  obtain ⟨g, hg⟩ := testElementaryClass_surjective (G := G) n z
  let C : Subgroup G := Subgroup.topologicalClosure (commutator G)
  let A := TopologicalAbelianization G
  let q : G →* A := QuotientGroup.mk' C
  let nrange : AddSubgroup (Additive A) := (nsmulAddMonoidHom n).range
  letI : IsClosed (C : Set G) := Subgroup.isClosed_topologicalClosure _
  letI : T2Space A := inferInstance
  letI : T2Space (Additive A) := inferInstanceAs (T2Space A)
  have hnrangeClosed : IsClosed (nrange : Set (Additive A)) := by
    have hc : IsCompact (Set.range (fun a : Additive A => n • a)) := by
      rw [← Set.image_univ]
      exact isCompact_univ.image (continuous_nsmul n)
    have hrange : Set.range (fun a : Additive A => n • a) = nrange := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, rfl⟩
      · rintro ⟨b, hb⟩
        exact ⟨b, hb⟩
    rw [hrange] at hc
    exact hc.isClosed
  let H : Subgroup G := (testElementaryClassHom n).ker
  have hHclosed : IsClosed (H : Set G) := by
    have hH : (H : Set G) = q ⁻¹' (nrange : Set (Additive A)) := by
      ext a
      change testElementaryClassHom n a = 1 ↔ Additive.ofMul (q a) ∈ nrange
      rw [show testElementaryClassHom n a = 1 ↔
          elementaryClass n a = 0 by
        change Multiplicative.ofAdd (elementaryClass n a) = 1 ↔ _
        rfl]
      change (LinearMap.range
          (LinearMap.lsmul ℤ (Additive A) (n : ℤ))).mkQ
            (Additive.ofMul (q a)) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change (Additive.ofMul (q a) ∈
        LinearMap.range (LinearMap.lsmul ℤ (Additive A) (n : ℤ))) ↔ _
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        change (n : ℤ) • b = Additive.ofMul (q a) at hb
        change n • b = Additive.ofMul (q a)
        rw [← Nat.cast_smul_eq_nsmul ℤ]
        exact hb
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        change n • b = Additive.ofMul (q a) at hb
        change (n : ℤ) • b = Additive.ofMul (q a)
        rw [Nat.cast_smul_eq_nsmul]
        exact hb
    rw [hH]
    exact hnrangeClosed.preimage QuotientGroup.continuous_mk
  have hgnot : g ∉ H := by
    intro hgH
    have hzero : elementaryClass n g = 0 := by
      change (testElementaryClassHom n g).toAdd = 0
      rw [MonoidHom.mem_ker.mp hgH]
      rfl
    exact hz (hg.symm.trans hzero)
  let HC : ClosedSubgroup G := ⟨H, hHclosed⟩
  have hexists : ∃ N : Subgroup G,
      IsOpen (N : Set G) ∧ H ≤ N ∧ g ∉ N := by
    by_contra hnone
    push Not at hnone
    have hgInf : g ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := by
      rw [Subgroup.mem_sInf]
      intro N hN
      exact hnone N hN.1 hN.2
    have hclosedEq := ProfiniteGrp.closedSubgroup_eq_sInf_open HC
    have : g ∈ H := by
      have hclosedEq' : H =
          sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := hclosedEq
      rw [hclosedEq']
      exact hgInf
    exact hgnot this
  obtain ⟨N, hNopen, hHN, hgN⟩ := hexists
  let classOnN : Additive N →+ ElementaryQuotient G n :=
    MonoidHom.toAdditiveLeft ((testElementaryClassHom n).comp N.subtype)
  let Padd : AddSubgroup (ElementaryQuotient G n) := classOnN.range
  let P : Submodule (ZMod n) (ElementaryQuotient G n) :=
    AddSubgroup.toZModSubmodule n Padd
  have hzP : z ∉ P := by
    intro hzmem
    have hzPadd : z ∈ Padd := by
      exact hzmem
    obtain ⟨u, hu⟩ := hzPadd
    let uG : G := (Additive.toMul u : N)
    have hclass : elementaryClass n uG = z := by
      exact hu
    have hker : g * uG⁻¹ ∈ H := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change elementaryClass n (g * uG⁻¹) = 0
      rw [show elementaryClass n (g * uG⁻¹) =
          elementaryClass n g - elementaryClass n uG by
        change (testElementaryClassHom n (g * uG⁻¹)).toAdd = _
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
          testElementaryClassHom_apply, testElementaryClassHom_apply]
        rw [sub_eq_add_neg],
        hg, hclass, sub_self]
    have hginN : g ∈ N := by
      have hkN := hHN hker
      have huN : uG ∈ N := (Additive.toMul u).prop
      have := N.mul_mem hkN huN
      simpa [mul_assoc] using this
    exact hgN hginN
  obtain ⟨f, hfz, hfP⟩ := Submodule.exists_le_ker_of_notMem hzP
  let χadd : Additive G →+ ZMod n :=
    f.toAddMonoidHom.comp (MonoidHom.toAdditiveLeft (testElementaryClassHom n))
  have hχcontinuous : Continuous χadd := by
    apply continuous_of_continuousAt_zero χadd
    rw [continuousAt_def]
    intro s hs
    have hs0 : (0 : ZMod n) ∈ s := by
      simpa only [map_zero] using mem_of_mem_nhds hs
    have hNzero : ∀ u : N, χadd (Additive.ofMul (u : G)) = 0 := by
      intro u
      apply hfP
      change elementaryClass n (u : G) ∈ Padd
      exact ⟨Additive.ofMul u, rfl⟩
    apply Filter.mem_of_superset (hNopen.mem_nhds N.one_mem)
    intro a ha
    change χadd (Additive.ofMul a) ∈ s
    have hzχ : χadd (Additive.ofMul a) = 0 :=
      hNzero ⟨a, ha⟩
    rw [hzχ]
    exact hs0
  let χ : ContinuousCharacter G n := ⟨χadd, hχcontinuous⟩
  have hevalzero := DFunLike.congr_fun hzEval χ
  have heval : evaluation n z χ = f z := by
    rw [← hg, evaluation_elementaryClass]
    rfl
  have : f z = 0 := by
    rw [← heval]
    exact hevalzero
  exact hfz this

private theorem testEvaluationLinear_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {n : ℕ} [Fact n.Prime] :
    Function.Surjective (evaluationLinear (G := G) n) := by
  classical
  intro L
  let t : ContinuousCharacter G n → Set G := fun χ =>
    {g | continuousCharacterValue χ g = L χ}
  have htclosed (χ : ContinuousCharacter G n) : IsClosed (t χ) := by
    change IsClosed ((fun g : G => χ (Additive.ofMul g)) ⁻¹' {L χ})
    exact isClosed_singleton.preimage χ.continuous
  have hsolve (u : Finset (ContinuousCharacter G n)) :
      ∃ g : G, ∀ χ ∈ u, continuousCharacterValue χ g = L χ := by
    let W : Submodule (ZMod n) (ContinuousCharacter G n) :=
      Submodule.span (ZMod n) (u : Set (ContinuousCharacter G n))
    letI : Module.Finite (ZMod n) W :=
      Module.Finite.span_of_finite (ZMod n) u.finite_toSet
    let evW : Additive G →+ Module.Dual (ZMod n) W :=
      { toFun := fun g =>
          (evaluationLinear n (elementaryClass n (Additive.toMul g))).comp
            (show W →ₗ[ZMod n] ContinuousCharacter G n from W.subtype)
        map_zero' := by
          apply LinearMap.ext
          intro χ
          rw [LinearMap.comp_apply]
          change evaluation n (elementaryClass n (1 : G))
            (χ : ContinuousCharacter G n) = 0
          rw [evaluation_elementaryClass]
          simp
        map_add' := by
          intro g h
          apply LinearMap.ext
          intro χ
          rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
            LinearMap.comp_apply]
          change evaluation n (elementaryClass n
              (Additive.toMul g * Additive.toMul h))
              (χ : ContinuousCharacter G n) =
            evaluation n (elementaryClass n (Additive.toMul g)) χ +
              evaluation n (elementaryClass n (Additive.toMul h)) χ
          rw [evaluation_elementaryClass, evaluation_elementaryClass,
            evaluation_elementaryClass]
          exact (χ : ContinuousCharacter G n).map_add g h }
    let Padd : AddSubgroup (Module.Dual (ZMod n) W) := evW.range
    let P : Submodule (ZMod n) (Module.Dual (ZMod n) W) :=
      AddSubgroup.toZModSubmodule n Padd
    have hPtop : P = ⊤ := by
      by_contra hP
      obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hP)
      obtain ⟨F, hFv, hFP⟩ := Submodule.exists_le_ker_of_notMem hv
      let w : W := (Module.evalEquiv (ZMod n) W).symm F
      have hw : w = 0 := by
        apply Subtype.ext
        apply ContinuousAddMonoidHom.ext
        intro g
        have hev_mem : evW g ∈ P := by
          change evW g ∈ Padd
          exact ⟨g, rfl⟩
        have hzero : F (evW g) = 0 := hFP hev_mem
        have happ := Module.apply_evalEquiv_symm_apply
          (ZMod n) W (evW g) F
        change evaluation n (elementaryClass n (Additive.toMul g))
            (w : ContinuousCharacter G n) = F (evW g) at happ
        rw [evaluation_elementaryClass] at happ
        change (w : ContinuousCharacter G n) g = 0
        exact happ.trans hzero
      have hFzero : F = 0 := by
        rw [← (Module.evalEquiv (ZMod n) W).apply_symm_apply F,
          show (Module.evalEquiv (ZMod n) W).symm F = 0 from hw, map_zero]
      exact hFv (by rw [hFzero]; rfl)
    let LW : Module.Dual (ZMod n) W := L.comp W.subtype
    have hLW : LW ∈ P := by rw [hPtop]; exact Submodule.mem_top
    have hLW' : LW ∈ Padd := hLW
    obtain ⟨g, hg⟩ := hLW'
    refine ⟨Additive.toMul g, ?_⟩
    intro χ hχ
    let χW : W := ⟨χ, Submodule.subset_span hχ⟩
    have happ := congrArg (fun f : Module.Dual (ZMod n) W => f χW) hg
    change evaluation n (elementaryClass n (Additive.toMul g)) χ = L χ at happ
    rw [evaluation_elementaryClass] at happ
    exact happ
  have hfinite (u : Finset (ContinuousCharacter G n)) :
      (Set.univ ∩ ⋂ χ ∈ u, t χ).Nonempty := by
    obtain ⟨g, hg⟩ := hsolve u
    refine ⟨g, Set.mem_inter (Set.mem_univ g) ?_⟩
    rw [Set.mem_iInter]
    intro χ
    rw [Set.mem_iInter]
    intro hχ
    exact hg χ hχ
  have hall := isCompact_univ.inter_iInter_nonempty t htclosed hfinite
  obtain ⟨g, _, hg⟩ := hall
  refine ⟨elementaryClass n g, ?_⟩
  apply LinearMap.ext
  intro χ
  change evaluation n (elementaryClass n g) χ = L χ
  rw [evaluation_elementaryClass]
  exact Set.mem_iInter.mp hg χ

/-- Evaluation identifies a compact totally disconnected group's elementary
quotient with the algebraic dual of its continuous character space. -/
theorem evaluationLinear_bijective_of_compact_totallyDisconnected
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {n : ℕ} [Fact n.Prime] :
    Function.Bijective (evaluationLinear (G := G) n) :=
  ⟨testEvaluationLinear_injective, testEvaluationLinear_surjective⟩

end
end NU.LocalTheory
