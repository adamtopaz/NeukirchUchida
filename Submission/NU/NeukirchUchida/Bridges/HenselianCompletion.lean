import Submission.NU.LocalTheory.Main

/-!
# Henselian fields and their completions

This file isolates the standard completion bridge used by the local-invariant
recovery argument.  It is deliberately independent of
`NU.NeukirchUchida.LocalInvariants`, so the valuation-theoretic theorem can be
proved in a separate worktree.
-/

open scoped IntermediateField NNReal NumberField Pointwise

namespace NU.NeukirchUchida.Bridges

noncomputable section

private abbrev DecompositionField (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) : Type _ :=
  NU.LocalTheory.decompositionField K P.1

/-- Compare the chosen algebraic closure of an intermediate field with the
ambient algebraic closure. -/
private noncomputable def intermediateFieldClosureEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    AlgebraicClosure E ≃ₐ[E] AlgebraicClosure F := by
  letI : IsAlgClosure E (AlgebraicClosure F) :=
    ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equiv E (AlgebraicClosure E) (AlgebraicClosure F)

/-- Algebraically, the absolute Galois group of an intermediate field is its
fixing subgroup in the absolute Galois group of the base. -/
private noncomputable def intermediateFieldGaloisMulEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E ≃* E.fixingSubgroup := by
  let e := intermediateFieldClosureEquiv F E
  let toFun : Field.absoluteGaloisGroup E → E.fixingSubgroup := fun sigma =>
    let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
    ⟨((e.symm.trans sigma').trans e).restrictScalars F, by
      apply (IntermediateField.mem_fixingSubgroup_iff E _).2
      intro x hx
      change e (sigma' (e.symm x)) = x
      have hxe : e.symm x =
          algebraMap E (AlgebraicClosure E) ⟨x, hx⟩ := by
        apply e.injective
        simp
      rw [hxe, sigma'.commutes]
      simp⟩
  let invFun : E.fixingSubgroup → Field.absoluteGaloisGroup E := fun tau =>
    let tauE : AlgebraicClosure F ≃ₐ[E] AlgebraicClosure F :=
      { tau.1 with
        commutes' := fun x => by
          exact (IntermediateField.mem_fixingSubgroup_iff E tau.1).1
            tau.2 x x.2 }
    (e.trans tauE).trans e.symm
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro sigma
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      right_inv := by
        intro tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      map_mul' := by
        intro sigma tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, e]
        rfl }

/-- Restriction from the absolute Galois group of an intermediate field into
the absolute Galois group of its base. -/
private noncomputable def intermediateFieldRestrictionHom
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E →* Field.absoluteGaloisGroup F :=
  E.fixingSubgroup.subtype.comp
    (intermediateFieldGaloisMulEquiv F E).toMonoidHom

private theorem intermediateFieldRestrictionHom_apply
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F))
    (sigma : Field.absoluteGaloisGroup E) (x : AlgebraicClosure F) :
    (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
      intermediateFieldRestrictionHom F E sigma) x =
      intermediateFieldClosureEquiv F E
        ((show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma)
          ((intermediateFieldClosureEquiv F E).symm x)) := by
  rfl

/-- Restriction along the chosen closure comparison is continuous in the two
Krull topologies. -/
private theorem intermediateFieldRestrictionHom_continuous
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Continuous (intermediateFieldRestrictionHom F E) := by
  let r : (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →*
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
    intermediateFieldRestrictionHom F E
  change @Continuous
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (krullTopology E (AlgebraicClosure E))
    (krullTopology F (AlgebraicClosure F)) r
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [r.map_one] at hN
  have hN' : N ∈ nhds
      (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := hN
  rw [krullTopology_mem_nhds_one_iff] at hN'
  obtain ⟨L, hLfin, hLN⟩ := hN'
  letI : FiniteDimensional F L := hLfin
  let e := intermediateFieldClosureEquiv F E
  let b := Module.Free.chooseBasis F L
  letI : Fintype (Module.Free.ChooseBasisIndex F L) := Fintype.ofFinite _
  let S : Set (AlgebraicClosure E) := Set.range
    (fun i : Module.Free.ChooseBasisIndex F L =>
      e.symm (((b i : L) : AlgebraicClosure F)))
  letI : Fintype S := (Set.finite_range _).fintype
  let L' : IntermediateField E (AlgebraicClosure E) :=
    IntermediateField.adjoin E S
  haveI : FiniteDimensional E L' := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x _
    exact Algebra.IsIntegral.isIntegral x
  apply mem_nhds_iff.mpr
  refine ⟨L'.fixingSubgroup, ?_,
    ⟨IntermediateField.fixingSubgroup_isOpen L',
      L'.fixingSubgroup.one_mem⟩⟩
  intro sigma hsigma
  apply hLN
  apply (IntermediateField.mem_fixingSubgroup_iff L _).2
  intro x hx
  have hsigma' :=
    (IntermediateField.mem_fixingSubgroup_iff L' sigma).1 hsigma
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
    intermediateFieldRestrictionHom F E sigma) x = x
  rw [intermediateFieldRestrictionHom_apply]
  let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
  let incl : L →ₐ[F] AlgebraicClosure F := L.val
  let pull : AlgebraicClosure F →ₐ[F] AlgebraicClosure E :=
    e.symm.restrictScalars F
  let f : L →ₗ[F] AlgebraicClosure E :=
    pull.toLinearMap.comp incl.toLinearMap
  let sigmaF : AlgebraicClosure E →ₐ[F] AlgebraicClosure E :=
    sigma'.restrictScalars F
  have heq : sigmaF.toLinearMap.comp f = f := by
    apply b.ext
    intro i
    change sigma' (e.symm (((b i : L) : AlgebraicClosure F))) =
      e.symm (((b i : L) : AlgebraicClosure F))
    apply hsigma'
    apply IntermediateField.subset_adjoin
    exact ⟨i, rfl⟩
  have hxfix := DFunLike.congr_fun heq (⟨x, hx⟩ : L)
  change sigma' (e.symm x) = e.symm x at hxfix
  rw [hxfix]
  exact e.apply_symm_apply x

/-- Topological fixed-field comparison for an arbitrary intermediate field.
Compactness upgrades the continuous algebraic equivalence to a
homeomorphism. -/
private noncomputable def intermediateFieldGaloisContinuousMulEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E ≃ₜ* E.fixingSubgroup := by
  let e := intermediateFieldGaloisMulEquiv F E
  have he : Continuous e := by
    exact Continuous.subtype_mk
      (intermediateFieldRestrictionHom_continuous F E) _
  letI : CompactSpace (Field.absoluteGaloisGroup E) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  let h := he.homeoOfEquivCompactToT2
  exact ContinuousMulEquiv.mk' h (by
    intro x y
    change e (x * y) = e x * e y
    exact e.map_mul x y)

/-- The absolute Galois group of the decomposition field is its absolute
decomposition subgroup, with the induced Krull topology. -/
private noncomputable def decompositionFieldGaloisEquiv
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    Field.absoluteGaloisGroup (DecompositionField K P) ≃ₜ*
      NU.LocalTheory.absoluteDecompositionGroup K P.1 := by
  let e := intermediateFieldGaloisContinuousMulEquiv K
    (NU.LocalTheory.decompositionField K P.1)
  rw [NU.LocalTheory.decompositionField_fixingSubgroup K P.1] at e
  exact e

/-- A valuation on an algebraic extension of `ℚ` has Archimedean value
group.  The proof descends two values to a number field and uses its discrete
valuation representing the restricted valuation ring. -/
private theorem algebraicValuation_valueGroup_mulArchimedean
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
    have hbL : bL ∈ C := by
      rw [htop]
      exact ValuationSubring.mem_top _
    change L.val bL ∈ A at hbL
    have hbval : L.val bL = b := rfl
    rwa [hbval] at hbL
  obtain ⟨p, hp, _⟩ := NU.LocalTheory.numberField_valuations C hC
  let w := p.valuation L
  have hvalring :
      (A.valuation.comap L.val.toRingHom).valuationSubring = C := by
    apply ValuationSubring.ext
    intro z
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      A.valuation_le_one_iff]
    rfl
  have hwvalring : w.valuationSubring = C := by
    rw [hp, NU.LocalTheory.primeValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
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
  have harch : MulArchimedean
      (MonoidWithZeroHom.ValueGroup₀ (.ofClass w)) :=
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

/-- Completion is unchanged if the base valuation is replaced by an
equivalent one and then embedded in a valued overfield.  The target is the
closure of the base field in the completion of that overfield. -/
private noncomputable def valuedCompletionEquivClosure
    {K Ω Γ Δ : Type*} [Field K] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ]
    [LinearOrderedCommGroupWithZero Δ]
    [Valued Ω Γ] [(Valued.v : Valuation Ω Γ).RankOne]
    (v : Valuation K Δ) (i : K →+* Ω)
    (heq : v.IsEquiv (Valued.v.comap i)) :
    v.Completion ≃+*
      ((UniformSpace.Completion.coeRingHom.comp i).fieldRange.topologicalClosure :
        Subfield (UniformSpace.Completion Ω)) := by
  letI : NontriviallyNormedField Ω :=
    Valued.toNontriviallyNormedField Ω Γ
  letI : IsUltrametricDist Ω := Valued.instIsUltrametricDist Ω Γ
  let C := UniformSpace.Completion Ω
  let iC : K →+* C := UniformSpace.Completion.coeRingHom.comp i
  let D : Subfield C := iC.fieldRange.topologicalClosure
  let kToD : K →+* D := iC.codRestrict D fun x =>
    Subfield.le_topologicalClosure iC.fieldRange ⟨x, rfl⟩
  letI : IsClosed (D : Set C) := Subfield.isClosed_topologicalClosure _
  letI : CompleteSpace D := IsClosed.completeSpace_coe
  letI : NormedField K := NormedField.induced K D kToD kToD.injective
  have hk_isometry : Isometry kToD := by
    apply Isometry.of_dist_eq
    intro x y
    rfl
  letI : IsUltrametricDist K := ⟨fun x y z => by
    rw [← hk_isometry.dist_eq x z, ← hk_isometry.dist_eq x y,
      ← hk_isometry.dist_eq y z]
    change dist (i x : C) (i z : C) ≤
      max (dist (i x : C) (i y : C)) (dist (i y : C) (i z : C))
    rw [UniformSpace.Completion.dist_eq,
      UniformSpace.Completion.dist_eq,
      UniformSpace.Completion.dist_eq]
    exact dist_triangle_max _ _ _⟩
  have hdense : DenseRange kToD := by
    rw [denseRange_iff_closure_range]
    ext y
    constructor
    · intro _
      exact Set.mem_univ y
    · intro _
      rw [closure_subtype]
      change (y : C) ∈ closure (((↑) : D → C) '' Set.range kToD)
      have hrange : ((↑) : D → C) '' Set.range kToD = iC.fieldRange := by
        ext z
        constructor
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨kToD x, ⟨x, rfl⟩, rfl⟩
      rw [hrange]
      exact y.property
  have hw_norm : (Valued.v.comap i).IsEquiv
      (NormedField.valuation (K := K)) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    apply ValuationSubring.ext
    intro x
    rw [Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      NormedField.valuation_apply]
    change Valued.v (i x) ≤ 1 ↔ ‖x‖₊ ≤ 1
    have hnorm : ‖x‖ = ‖i x‖ := by
      change ‖(kToD x : D)‖ = ‖i x‖
      exact UniformSpace.Completion.norm_coe (i x)
    rw [← Valued.toNormedField.norm_le_one_iff]
    rw [← hnorm]
    norm_cast
  let eBase : WithVal v ≃ᵤ K := by
    letI : Valued K ℝ≥0 := NormedField.toValued
    exact WithVal.uniformEquiv rfl (heq.trans hw_norm)
  let pkgD : AbstractCompletion K :=
    { space := D
      coe := kToD
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hk_isometry.isUniformInducing
      dense := hdense }
  let eU : v.Completion ≃ᵤ D :=
    UniformSpace.Completion.cPkg.mapEquiv pkgD eBase
  refine
    { eU with
      map_add' := ?_
      map_mul' := ?_ }
  · intro x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          (eU.continuous.comp (continuous_fst.mul continuous_snd))
          ((eU.continuous.comp continuous_fst).mul
            (eU.continuous.comp continuous_snd))
    | ih x y =>
      rw [← UniformSpace.Completion.coe_mul]
      have hmap (z : WithVal v) :
          eU (z : v.Completion) = kToD (eBase z) :=
        AbstractCompletion.mapEquiv_coe _ _ _ _
      have heBase : eBase (x * y) = eBase x * eBase y := rfl
      calc
        eU.toFun (↑(x * y)) = kToD (eBase (x * y)) := hmap _
        _ = kToD (eBase x) * kToD (eBase y) := by
          rw [heBase, map_mul]
        _ = eU.toFun (↑x) * eU.toFun (↑y) :=
          congrArg₂ (· * ·) (hmap x).symm (hmap y).symm
  · intro x y
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          (eU.continuous.comp (continuous_fst.add continuous_snd))
          ((eU.continuous.comp continuous_fst).add
            (eU.continuous.comp continuous_snd))
    | ih x y =>
      rw [← UniformSpace.Completion.coe_add]
      have hmap (z : WithVal v) :
          eU (z : v.Completion) = kToD (eBase z) :=
        AbstractCompletion.mapEquiv_coe _ _ _ _
      have heBase : eBase (x + y) = eBase x + eBase y := rfl
      calc
        eU.toFun (↑(x + y)) = kToD (eBase (x + y)) := hmap _
        _ = kToD (eBase x) + kToD (eBase y) := by
          rw [heBase, map_add]
        _ = eU.toFun (↑x) + eU.toFun (↑y) :=
          congrArg₂ (· + ·) (hmap x).symm (hmap y).symm

set_option maxHeartbeats 800000 in
/-- Replacing the chosen algebraic closure does not change the topological
absolute Galois group. -/
private noncomputable def absoluteGaloisOfAlgClosure
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [IsAlgClosure F E] :
    Field.absoluteGaloisGroup F ≃ₜ* (E ≃ₐ[F] E) := by
  change (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≃ₜ* (E ≃ₐ[F] E)
  let e : AlgebraicClosure F ≃ₐ[F] E :=
    IsAlgClosure.equiv F (AlgebraicClosure F) E
  let m : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≃*
      (E ≃ₐ[F] E) := AlgEquiv.autCongr e
  have hm : Continuous m := by
    change @Continuous
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (E ≃ₐ[F] E)
      (krullTopology F (AlgebraicClosure F)) (krullTopology F E) m
    apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
    intro N hN
    rw [m.map_one] at hN
    have hN' : N ∈ nhds (1 : E ≃ₐ[F] E) := hN
    rw [krullTopology_mem_nhds_one_iff] at hN'
    obtain ⟨L, hLfin, hLN⟩ := hN'
    let L' : IntermediateField F (AlgebraicClosure F) :=
      L.map e.symm.toAlgHom
    haveI : FiniteDimensional F L := hLfin
    haveI : FiniteDimensional F L' := by
      exact (L.equivMap e.symm.toAlgHom).toLinearEquiv.finiteDimensional
    apply mem_nhds_iff.mpr
    refine ⟨L'.fixingSubgroup, ?_,
      ⟨IntermediateField.fixingSubgroup_isOpen L',
        L'.fixingSubgroup.one_mem⟩⟩
    intro sigma hsigma
    apply hLN
    apply (IntermediateField.mem_fixingSubgroup_iff L _).2
    intro x hx
    let sigma' :=
      show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from sigma
    have hsigma' :=
      (IntermediateField.mem_fixingSubgroup_iff L' sigma').1 hsigma
    change e (sigma' (e.symm x)) = x
    rw [hsigma' (e.symm x) ⟨x, hx, rfl⟩]
    exact e.apply_symm_apply x
  letI : CompactSpace
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := by
    change CompactSpace (Field.absoluteGaloisGroup F)
    exact NU.LocalTheory.absoluteGaloisGroup_compactSpace
  let h := hm.homeoOfEquivCompactToT2
  exact ContinuousMulEquiv.mk' h m.map_mul

set_option maxHeartbeats 1000000 in
/-- A field equivalence induces a topological equivalence of absolute Galois
groups. -/
private noncomputable def absoluteGaloisCongr
    {F D : Type*} [Field F] [Field D] (e : F ≃+* D) :
    Field.absoluteGaloisGroup F ≃ₜ* Field.absoluteGaloisGroup D := by
  change (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≃ₜ*
    (AlgebraicClosure D ≃ₐ[D] AlgebraicClosure D)
  let c : AlgebraicClosure F ≃+* AlgebraicClosure D :=
    IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure D) e
  let forward : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →
      (AlgebraicClosure D ≃ₐ[D] AlgebraicClosure D) := fun sigma =>
    { c.symm.trans (sigma.toRingEquiv.trans c) with
      commutes' := fun d => by
        change c (sigma (c.symm (algebraMap D (AlgebraicClosure D) d))) =
          algebraMap D (AlgebraicClosure D) d
        rw [show c.symm (algebraMap D (AlgebraicClosure D) d) =
            algebraMap F (AlgebraicClosure F) (e.symm d) by
          exact IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ _,
          sigma.commutes,
          show c (algebraMap F (AlgebraicClosure F) (e.symm d)) =
            algebraMap D (AlgebraicClosure D) (e (e.symm d)) by
          exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _ _,
          e.apply_symm_apply] }
  let backward : (AlgebraicClosure D ≃ₐ[D] AlgebraicClosure D) →
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := fun tau =>
    { c.trans (tau.toRingEquiv.trans c.symm) with
      commutes' := fun f => by
        change c.symm (tau (c (algebraMap F (AlgebraicClosure F) f))) =
          algebraMap F (AlgebraicClosure F) f
        rw [show c (algebraMap F (AlgebraicClosure F) f) =
            algebraMap D (AlgebraicClosure D) (e f) by
          exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _ _,
          tau.commutes,
          show c.symm (algebraMap D (AlgebraicClosure D) (e f)) =
            algebraMap F (AlgebraicClosure F) (e.symm (e f)) by
          exact IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ _,
          e.symm_apply_apply] }
  let m : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≃*
      (AlgebraicClosure D ≃ₐ[D] AlgebraicClosure D) :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro sigma
        apply AlgEquiv.ext
        intro x
        simp [forward, backward, c]
      right_inv := by
        intro tau
        apply AlgEquiv.ext
        intro x
        simp [forward, backward, c]
      map_mul' := by
        intro sigma tau
        apply AlgEquiv.ext
        intro x
        simp [forward, c] }
  have hm : Continuous m := by
    apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
    intro N hN
    rw [m.map_one] at hN
    have hN' : N ∈ nhds
        (1 : AlgebraicClosure D ≃ₐ[D] AlgebraicClosure D) := hN
    rw [krullTopology_mem_nhds_one_iff] at hN'
    obtain ⟨L, hLfin, hLN⟩ := hN'
    letI : FiniteDimensional D L := hLfin
    let b := Module.Free.chooseBasis D L
    letI : Fintype (Module.Free.ChooseBasisIndex D L) := Fintype.ofFinite _
    let S : Set (AlgebraicClosure F) := Set.range
      (fun i : Module.Free.ChooseBasisIndex D L =>
        c.symm (((b i : L) : AlgebraicClosure D)))
    let L' : IntermediateField F (AlgebraicClosure F) :=
      IntermediateField.adjoin F S
    haveI : FiniteDimensional F L' := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _
      exact Algebra.IsIntegral.isIntegral x
    apply mem_nhds_iff.mpr
    refine ⟨L'.fixingSubgroup, ?_,
      ⟨IntermediateField.fixingSubgroup_isOpen L',
        L'.fixingSubgroup.one_mem⟩⟩
    intro sigma hsigma
    apply hLN
    apply (IntermediateField.mem_fixingSubgroup_iff L _).2
    intro x hx
    have hsigma' :=
      (IntermediateField.mem_fixingSubgroup_iff L' sigma).1 hsigma
    let tau := m sigma
    let incl : L →ₐ[D] AlgebraicClosure D := L.val
    let tauD : AlgebraicClosure D →ₐ[D] AlgebraicClosure D := tau
    have heq : tauD.toLinearMap.comp incl.toLinearMap = incl.toLinearMap := by
      apply b.ext
      intro i
      change c (sigma (c.symm (((b i : L) : AlgebraicClosure D)))) =
        ((b i : L) : AlgebraicClosure D)
      rw [hsigma' _ (IntermediateField.subset_adjoin F S ⟨i, rfl⟩)]
      exact c.apply_symm_apply _
    exact DFunLike.congr_fun heq (⟨x, hx⟩ : L)
  letI : CompactSpace
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := by
    change CompactSpace (Field.absoluteGaloisGroup F)
    exact NU.LocalTheory.absoluteGaloisGroup_compactSpace
  let h := hm.homeoOfEquivCompactToT2
  exact ContinuousMulEquiv.mk' h m.map_mul

/-- An automorphism is uniformly continuous when it preserves the equivalence
class of the distinguished valuation. -/
private theorem valuationEquivComap_uniformContinuous
    {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    [Valued F Γ] (σ : F ≃+* F)
    (hσ : (Valued.v : Valuation F Γ).IsEquiv
      ((Valued.v : Valuation F Γ).comap σ.toRingHom)) :
    UniformContinuous σ := by
  apply uniformContinuous_of_continuousAt_zero σ.toRingHom
  rw [ContinuousAt, map_zero]
  apply (Valued.hasBasis_nhds_zero F Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero F Γ) |>.2
  intro γ _
  obtain ⟨a, ha⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation F Γ)) γ.1
  change (Valued.v : Valuation F Γ).restrict a = γ.1 at ha
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    have hγ0 : (γ.1 : MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation F Γ))) ≠ 0 := Units.ne_zero γ
    apply hγ0
    simpa using ha.symm
  let b := σ.symm a
  have hb0 : b ≠ 0 := by simp [b, ha0]
  let δ : (MonoidWithZeroHom.ValueGroup₀
      (.ofClass (Valued.v : Valuation F Γ)))ˣ :=
    Units.mk0 ((Valued.v : Valuation F Γ).restrict b) (by
      simpa [Valuation.restrict_def, hb0])
  refine ⟨δ, trivial, ?_⟩
  intro x hx
  change (Valued.v : Valuation F Γ).restrict (σ x) < γ.1
  have hx' : (Valued.v : Valuation F Γ) x < Valued.v b := by
    rw [← Valuation.restrict_lt_iff]
    simpa [δ] using hx
  have hmap := hσ.lt_iff_lt.mp hx'
  change (Valued.v : Valuation F Γ) (σ x) < Valued.v (σ b) at hmap
  rw [show σ b = a by simp [b]] at hmap
  rw [← Valuation.restrict_lt_iff] at hmap
  rwa [ha] at hmap

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The completion's absolute Galois group is the decomposition group of an
absolute extension of the defining finite place. -/
private theorem completionGaloisEquivDecomposition
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (v : NU.LocalTheory.FinitePlace K)
    (hv : NU.LocalTheory.primeValuationSubring v =
      P.1.comap (algebraMap K (AlgebraicClosure K))) :
    Nonempty (Field.absoluteGaloisGroup (v.adicCompletion K) ≃ₜ*
      NU.LocalTheory.absoluteDecompositionGroup K P.1) := by
  classical
  let Ω := AlgebraicClosure K
  letI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  let W : ValuationSubring Ω := P.1
  have hW : W ≠ ⊤ := by
    intro htop
    apply NU.LocalTheory.primeValuationSubring_ne_top v
    rw [hv]
    change W.comap (algebraMap K Ω) = ⊤
    rw [htop]
    rfl
  letI : W.valuation.IsNontrivial :=
    not_not.mp ((not_congr W.eq_top_iff).mp hW)
  letI : MulArchimedean W.ValueGroup :=
    algebraicValuation_valueGroup_mulArchimedean W
  letI : W.valuation.RankOne :=
    (W.valuation.nonempty_rankOne_iff_mulArchimedean.mpr inferInstance).some
  letI : Valued Ω W.ValueGroup := Valued.mk' W.valuation
  letI : NontriviallyNormedField Ω :=
    Valued.toNontriviallyNormedField Ω W.ValueGroup
  letI : IsUltrametricDist Ω :=
    Valued.instIsUltrametricDist Ω W.ValueGroup
  letI : UniformContinuousConstSMul K Ω :=
    uniformContinuousConstSMul_of_continuousConstSMul K Ω
  let wK := W.valuation.comap (algebraMap K Ω)
  have hwKring : wK.valuationSubring =
      NU.LocalTheory.primeValuationSubring v := by
    apply ValuationSubring.ext
    intro x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      W.valuation_le_one_iff]
    exact (ValuationSubring.ext_iff.mp hv x).symm
  have hvKring : (v.valuation K).valuationSubring =
      NU.LocalTheory.primeValuationSubring v := by
    rw [NU.LocalTheory.primeValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hequiv : (v.valuation K).IsEquiv wK :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2
      (hvKring.trans hwKring.symm)
  let C := UniformSpace.Completion Ω
  letI : NormedField C := inferInstance
  letI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra Ω
  letI : NontriviallyNormedField C :=
    { non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := Ω)
        exact ⟨(x : C), by
          change 1 < ‖(x : C)‖
          rw [UniformSpace.Completion.norm_coe]
          exact hx⟩ }
  letI : CharZero C :=
    (RingHom.charZero_iff (algebraMap Ω C).injective).mp inferInstance
  letI : IsAlgClosed C :=
    IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe
  let iC : K →+* C :=
    UniformSpace.Completion.coeRingHom.comp (algebraMap K Ω)
  let D : Subfield C := iC.fieldRange.topologicalClosure
  let eD0 : (v.valuation K).Completion ≃+* D :=
    valuedCompletionEquivClosure (v.valuation K) (algebraMap K Ω) hequiv
  let eD : v.adicCompletion K ≃+* D := eD0
  let kToD : K →+* D := iC.codRestrict D fun x =>
    Subfield.le_topologicalClosure iC.fieldRange ⟨x, rfl⟩
  letI : IsClosed (D : Set C) := Subfield.isClosed_topologicalClosure _
  letI : CompleteSpace D := IsClosed.completeSpace_coe
  letI : Algebra K D :=
    { toSMul := ⟨fun k x => kToD k * x⟩
      algebraMap := kToD
      commutes' := fun _ _ => mul_comm _ _
      smul_def' := fun _ _ => rfl }
  letI : Algebra K C := inferInstance
  letI : IsScalarTower K D C :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := D) (A := C) fun x => by
      change iC x = (kToD x : C)
      rfl
  let E : IntermediateField D C := algebraicClosure D C
  letI : Algebra K E :=
    ((algebraMap D E).comp (algebraMap K D)).toAlgebra
  letI : IsScalarTower K D E :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := D) (A := E) fun _ => rfl
  let omegaToC : Ω →ₐ[K] C :=
    { UniformSpace.Completion.coeRingHom with
      commutes' := fun _ => rfl }
  have homegaE (x : Ω) : omegaToC x ∈ E := by
    rw [mem_algebraicClosure_iff']
    exact IsIntegral.tower_top
      ((Algebra.IsIntegral.isIntegral (R := K) x).map omegaToC)
  let omegaToE : Ω →ₐ[K] E :=
    { toRingHom := omegaToC.toRingHom.codRestrict E homegaE
      commutes' := fun _ => rfl }
  let O : IntermediateField K E := omegaToE.fieldRange
  let omegaEquiv : Ω ≃ₐ[K] O := AlgEquiv.ofInjectiveField omegaToE
  let normalO : Normal K O := by
    letI : Normal K Ω := IsAlgClosure.normal K Ω
    exact Normal.of_algEquiv omegaEquiv
  letI normalOInst : Normal K O := normalO
  let restrictScalarsHom : (E ≃ₐ[D] E) →* (E ≃ₐ[K] E) :=
    { toFun := fun τ => τ.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let restrictO : (E ≃ₐ[D] E) →* (O ≃ₐ[K] O) :=
    (AlgEquiv.restrictNormalHom O).comp restrictScalarsHom
  let restrictOmega : (E ≃ₐ[D] E) →*
      (Ω ≃ₐ[K] Ω) :=
    (AlgEquiv.autCongr omegaEquiv).symm.toMonoidHom.comp restrictO
  have restrictOmega_apply (τ : E ≃ₐ[D] E) (x : Ω) :
      omegaToE (restrictOmega τ x) = τ (omegaToE x) := by
    change omegaToE (omegaEquiv.symm (restrictO τ (omegaEquiv x))) =
      τ (omegaToE x)
    calc
      omegaToE (omegaEquiv.symm (restrictO τ (omegaEquiv x))) =
          ((restrictO τ) (omegaEquiv x) : E) := by
            exact congrArg Subtype.val
              (omegaEquiv.apply_symm_apply (restrictO τ (omegaEquiv x)))
      _ = τ (omegaToE x) := by
        exact @AlgEquiv.restrictNormalHom_apply K _ E _ _ O normalOInst
          (restrictScalarsHom τ) (omegaEquiv x)
  letI : NontriviallyNormedField D :=
    { non_trivial := by
        obtain ⟨a, ha0, ha1⟩ :=
          Valuation.IsNontrivial.exists_val_nontrivial
            (v := v.valuation K)
        rcases lt_or_gt_of_ne ha1 with ha | ha
        · have ha' : (v.valuation K) a < (v.valuation K) 1 := by
            simpa only [map_one] using ha
          have hwa : wK a < 1 := by
            simpa only [map_one] using hequiv.lt_iff_lt.mp ha'
          refine ⟨kToD a⁻¹, ?_⟩
          change 1 < ‖((algebraMap K Ω a⁻¹ : Ω) : C)‖
          rw [UniformSpace.Completion.norm_coe,
            Valued.toNormedField.one_lt_norm_iff]
          have hinv : 1 < (wK a)⁻¹ :=
            (one_lt_inv₀
              (zero_lt_iff.mpr ((wK.ne_zero_iff).2
                ((v.valuation K).ne_zero_iff.mp ha0)))).2 hwa
          change 1 < (Valued.v : Valuation Ω W.ValueGroup)
            ((algebraMap K Ω) a⁻¹)
          rw [show (Valued.v : Valuation Ω W.ValueGroup) = W.valuation by
            rfl, map_inv₀]
          exact hinv
        · have ha' : (v.valuation K) 1 < (v.valuation K) a := by
            simpa only [map_one] using ha
          have hwa : 1 < wK a := by
            simpa only [map_one] using hequiv.lt_iff_lt.mp ha'
          refine ⟨kToD a, ?_⟩
          change 1 < ‖((algebraMap K Ω a : Ω) : C)‖
          rw [UniformSpace.Completion.norm_coe,
            Valued.toNormedField.one_lt_norm_iff]
          exact hwa }
  letI : NormedAlgebra D E :=
    { norm_smul_le := fun r x => by
        change ‖(r : C) * (x : C)‖ ≤ ‖(r : C)‖ * ‖(x : C)‖
        exact norm_mul_le _ _ }
  have tau_norm (τ : E ≃ₐ[D] E) (x : E) : ‖τ x‖ = ‖x‖ := by
    rw [NormedAlgebra.norm_eq_spectralNorm D,
      NormedAlgebra.norm_eq_spectralNorm D]
    exact (spectralNorm_eq_of_equiv τ x).symm
  have omegaToE_norm (x : Ω) : ‖omegaToE x‖ = ‖x‖ := by
    change ‖(x : C)‖ = ‖x‖
    exact UniformSpace.Completion.norm_coe x
  have restrictOmega_norm (τ : E ≃ₐ[D] E) (x : Ω) :
      ‖restrictOmega τ x‖ = ‖x‖ := by
    rw [← omegaToE_norm, ← omegaToE_norm, restrictOmega_apply, tau_norm]
  have mem_W_iff_norm (x : Ω) : x ∈ W ↔ ‖x‖ ≤ 1 := by
    rw [← W.valuation_le_one_iff]
    change (Valued.v : Valuation Ω W.ValueGroup) x ≤ 1 ↔ ‖x‖ ≤ 1
    exact Valued.toNormedField.norm_le_one_iff.symm
  have restrictOmega_stabilizes (τ : E ≃ₐ[D] E) :
      restrictOmega τ • W = W := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      mem_W_iff_norm, mem_W_iff_norm, AlgEquiv.smul_def]
    have hinv : (restrictOmega τ)⁻¹ = restrictOmega τ⁻¹ := by
      rw [map_inv]
    rw [hinv, restrictOmega_norm]
  let r : (E ≃ₐ[D] E) →*
      NU.LocalTheory.absoluteDecompositionGroup K W :=
    { toFun := fun τ => ⟨restrictOmega τ, restrictOmega_stabilizes τ⟩
      map_one' := Subtype.ext (map_one restrictOmega)
      map_mul' := fun τ υ => Subtype.ext (map_mul restrictOmega τ υ) }
  have homegaDense : DenseRange omegaToE := by
    rw [DenseRange, Subtype.dense_iff]
    intro y _
    have hrange : ((↑) : E → C) '' Set.range omegaToE =
        Set.range ((↑) : Ω → C) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨omegaToE x, ⟨x, rfl⟩, rfl⟩
    have hy : y ∈ closure (Set.range ((↑) : Ω → C)) := by
      rw [(UniformSpace.Completion.denseRange_coe :
        DenseRange ((↑) : Ω → C)).closure_range]
      trivial
    exact (congrArg closure hrange).symm ▸ hy
  have tau_isometry (τ : E ≃ₐ[D] E) : Isometry τ := by
    apply Isometry.of_dist_eq
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, tau_norm]
  have r_injective : Function.Injective r := by
    intro τ υ hτυ
    have hrestrict : restrictOmega τ = restrictOmega υ :=
      congrArg Subtype.val hτυ
    apply AlgEquiv.ext
    intro y
    apply homegaDense.induction_on (p := fun y => τ y = υ y) y
      (isClosed_eq (tau_isometry τ).continuous
        (tau_isometry υ).continuous)
    intro x
    rw [← restrictOmega_apply τ x, ← restrictOmega_apply υ x,
      hrestrict]
  have stabilizer_uniformContinuous
      (g : NU.LocalTheory.absoluteDecompositionGroup K W) :
      UniformContinuous g.1.toRingEquiv := by
    let σ : Ω ≃ₐ[K] Ω := g.1
    have hmem (x : Ω) : σ x ∈ W ↔ x ∈ W := by
      calc
        σ x ∈ W ↔ σ x ∈ σ • W := by rw [g.2]
        _ ↔ σ⁻¹ • σ x ∈ W :=
          ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
        _ ↔ x ∈ W := by simp [AlgEquiv.smul_def]
    have hring : W.valuation.valuationSubring =
        (W.valuation.comap σ.toRingHom).valuationSubring := by
      apply ValuationSubring.ext
      intro x
      rw [Valuation.mem_valuationSubring_iff,
        Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
        W.valuation_le_one_iff, W.valuation_le_one_iff]
      change x ∈ W ↔ σ x ∈ W
      exact (hmem x).symm
    apply valuationEquivComap_uniformContinuous σ.toRingEquiv
    exact (Valuation.isEquiv_iff_valuationSubring _ _).2 hring
  have r_surjective : Function.Surjective r := by
    intro g
    let σ : Ω ≃ₐ[K] Ω := g.1
    have hσ : UniformContinuous σ.toRingEquiv :=
      stabilizer_uniformContinuous g
    have hσinv : Continuous σ.toRingEquiv.symm := by
      have h := stabilizer_uniformContinuous (g⁻¹)
      have heq : (g⁻¹).1.toRingEquiv = σ.toRingEquiv.symm := by
        rfl
      rw [heq] at h
      exact h.continuous
    let sigmaC : C ≃+* C :=
      UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
        hσ.continuous hσinv
    have sigmaC_coe (x : Ω) : sigmaC (x : C) = (σ x : C) := by
      rw [UniformSpace.Completion.mapRingEquiv_apply,
        UniformSpace.Completion.map_coe hσ]
      change (σ x : C) = (σ x : C)
      rfl
    have sigmaC_cont : Continuous sigmaC := by
      change Continuous (UniformSpace.Completion.map σ)
      exact UniformSpace.Completion.continuous_map
    have sigmaC_fix_D (d : D) : sigmaC (d : C) = (d : C) := by
      apply closure_minimal (s := iC.fieldRange)
        (t := {z : C | sigmaC z = z})
      · rintro _ ⟨k, rfl⟩
        change sigmaC ((algebraMap K Ω k : Ω) : C) =
          ((algebraMap K Ω k : Ω) : C)
        rw [sigmaC_coe, σ.commutes]
      · exact isClosed_eq sigmaC_cont continuous_id
      · exact d.2
    let sigmaAlg : C ≃ₐ[D] C :=
      { sigmaC with commutes' := sigmaC_fix_D }
    letI : IsAlgClosure D E := by
      dsimp [E]
      infer_instance
    let normalE : Normal D E := IsAlgClosure.normal D E
    letI normalEInst : Normal D E := normalE
    let tau : E ≃ₐ[D] E := sigmaAlg.restrictNormal E
    refine ⟨tau, ?_⟩
    apply Subtype.ext
    change restrictOmega tau = σ
    apply AlgEquiv.ext
    intro x
    apply omegaToE.injective
    change omegaToE (restrictOmega tau x) = omegaToE (σ x)
    rw [restrictOmega_apply]
    apply Subtype.ext
    change (tau (omegaToE x) : C) = (σ x : C)
    rw [show (tau (omegaToE x) : C) =
        sigmaAlg (omegaToE x : C) by
      exact AlgEquiv.restrictNormal_commutes sigmaAlg E (omegaToE x)]
    change sigmaC (x : C) = (σ x : C)
    exact sigmaC_coe x
  letI closureE : IsAlgClosure D E := by
    dsimp [E]
    infer_instance
  have hrestrict_cont : Continuous restrictOmega := by
    apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
    intro N hN
    rw [map_one] at hN
    have hN' : N ∈ nhds (1 : Ω ≃ₐ[K] Ω) := hN
    rw [krullTopology_mem_nhds_one_iff] at hN'
    obtain ⟨L, hLfin, hLN⟩ := hN'
    letI : FiniteDimensional K L := hLfin
    obtain ⟨s, hs⟩ := IntermediateField.fg_top K L
    let S : Set E := (fun z : L => omegaToE (z : Ω)) '' (s : Set L)
    letI : Fintype S :=
      (s.finite_toSet.image (fun z : L => omegaToE (z : Ω))).fintype
    let L' : IntermediateField D E := IntermediateField.adjoin D S
    haveI : FiniteDimensional D L' := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _
      exact Algebra.IsIntegral.isIntegral x
    apply mem_nhds_iff.mpr
    refine ⟨L'.fixingSubgroup, ?_,
      ⟨IntermediateField.fixingSubgroup_isOpen L',
        L'.fixingSubgroup.one_mem⟩⟩
    intro τ hτ
    apply hLN
    apply (IntermediateField.mem_fixingSubgroup_iff L _).2
    intro x hx
    have hτ' :=
      (IntermediateField.mem_fixingSubgroup_iff L' τ).1 hτ
    let incl : L →ₐ[K] E := omegaToE.comp L.val
    let tauK : E →ₐ[K] E := τ.restrictScalars K
    have hsAlg : Algebra.adjoin K (s : Set L) = ⊤ :=
      IntermediateField.adjoin_eq_top_iff.mp hs
    have heq : tauK.comp incl = incl := by
      apply AlgHom.ext_of_adjoin_eq_top hsAlg
      intro z hz
      change τ (omegaToE (z : Ω)) = omegaToE (z : Ω)
      exact hτ' _ (IntermediateField.subset_adjoin D S ⟨z, hz, rfl⟩)
    apply omegaToE.injective
    change omegaToE (restrictOmega τ x) = omegaToE x
    rw [restrictOmega_apply]
    exact DFunLike.congr_fun heq (⟨x, hx⟩ : L)
  have hr_cont : Continuous r := by
    change Continuous (fun τ =>
      (⟨restrictOmega τ, restrictOmega_stabilizes τ⟩ :
        NU.LocalTheory.absoluteDecompositionGroup K W))
    exact hrestrict_cont.subtype_mk _
  let m : (E ≃ₐ[D] E) ≃*
      NU.LocalTheory.absoluteDecompositionGroup K W :=
    MulEquiv.ofBijective r ⟨r_injective, r_surjective⟩
  have hm : Continuous m := hr_cont
  letI : CompactSpace (Field.absoluteGaloisGroup D) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  letI : CompactSpace (E ≃ₐ[D] E) :=
    (absoluteGaloisOfAlgClosure D E).toHomeomorph.compactSpace
  letI : T2Space (Field.absoluteGaloisGroup K) := krullTopology_t2
  letI : T2Space
      (NU.LocalTheory.absoluteDecompositionGroup K W) := inferInstance
  let h := hm.homeoOfEquivCompactToT2
  let er : (E ≃ₐ[D] E) ≃ₜ*
      NU.LocalTheory.absoluteDecompositionGroup K W :=
    ContinuousMulEquiv.mk' h m.map_mul
  exact ⟨(absoluteGaloisCongr eD).trans
    ((absoluteGaloisOfAlgClosure D E).trans er)⟩

/-- **Henselian completion bridge (Blueprint T5; nu-inv12 blocker report:
"the remaining standard completion theorem").**  Finite separable extensions
of a rank-one Henselian valued field correspond to finite separable extensions
of its completion.  Applied to the decomposition field selected by an
absolute place, that correspondence induces the displayed topological
absolute-Galois equivalence.

This is the standalone form of the blocked core formerly called
`henselianCompletion_absoluteGaloisEquiv` in `LocalInvariants.lean`.  The
hypothesis `hv` pins the number-field completion to the restriction of the
same ambient valuation; `hhens` and `hrank` use exactly the Henselian and
rank-one vocabulary of `NU.LocalTheory`.  See
`local_invariants_recovery.tex`, T5, and the nu-inv12 blocker report. -/
theorem henselianCompletion_absoluteGaloisEquiv
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (v : NU.LocalTheory.FinitePlace K)
    (hv : NU.LocalTheory.primeValuationSubring v =
      P.1.comap (algebraMap K (AlgebraicClosure K)))
    (hhens : NU.LocalTheory.IsHenselianValuationIn
      (NU.LocalTheory.decompositionField K P.1) (AlgebraicClosure K)
      (P.1.comap
        (NU.LocalTheory.decompositionField K P.1).val.toRingHom))
    (hrank : NU.LocalTheory.IsRankOneValuationSubring
      (P.1.comap
        (NU.LocalTheory.decompositionField K P.1).val.toRingHom)) :
    Nonempty
      (Field.absoluteGaloisGroup (v.adicCompletion K) ≃ₜ*
        Field.absoluteGaloisGroup
          (NU.LocalTheory.decompositionField K P.1)) := by
  obtain ⟨e⟩ := completionGaloisEquivDecomposition K P v hv
  exact ⟨e.trans (decompositionFieldGaloisEquiv K P).symm⟩

end

end NU.NeukirchUchida.Bridges
