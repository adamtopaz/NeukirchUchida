import Submission.NU.LCFT.Cohomology.InfRes
import Submission.NU.LCFT.FundamentalClass.Unramified

/-!
# The local fundamental class for a general finite Galois extension

The public class lives in the concrete `H²`, and every map used to characterize it is the actual
map transported through `comparisonH2`.  The unramified-envelope package records a literal
compositum, its intersection degree, both unramified ends, the inflated carry class, its zero
restriction, and the injective descent map.  Thus the descent and functoriality declarations cannot
be witnessed by zero or otherwise unrelated homomorphisms.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

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

private theorem groupCohomology_mapIso_hom
    {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
    (he : ∀ g, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e') (n : ℕ) :
    (groupCohomology_mapIso e e' he n).hom =
      groupCohomology.map e.symm (Rep.ofHom ⟨e', fun h ↦ by simp [he]⟩) n := rfl

private theorem normalizedGeneratorPackage
    {A : Type*} [AddCommGroup A] [Finite A]
    (n : ℕ) (a : A) (ha : addOrderOf a = n) (hcard : Nat.card A ≤ n) :
    (∀ b : A, ∃ m : ℤ, m • a = b) ∧
      ∃ e : A ≃+ ZMod n,
        e a = 1 ∧ ∀ f : A ≃+ ZMod n, f a = 1 → f = e := by
  have hcardpos : 0 < Nat.card A := Nat.card_pos
  have hna : n ∣ Nat.card A := ha ▸ addOrderOf_dvd_natCard a
  have hcardeq : Nat.card A = n :=
    Nat.le_antisymm hcard (Nat.le_of_dvd hcardpos hna)
  let H := AddSubgroup.zmultiples a
  letI : Finite H := Finite.of_injective H.subtype H.subtype_injective
  have hHcard : Nat.card H = Nat.card A := by
    rw [Nat.card_zmultiples, ha, hcardeq]
  have hHtop : H = ⊤ := AddSubgroup.eq_top_of_card_eq H hHcard
  have hgen : ∀ b : A, b ∈ AddSubgroup.zmultiples a := by
    intro b
    change b ∈ H
    rw [hHtop]
    exact AddSubgroup.mem_top b
  have generates : ∀ b : A, ∃ m : ℤ, m • a = b := by
    intro b
    exact AddSubgroup.mem_zmultiples_iff.mp (hgen b)
  let e : A ≃+ ZMod n := (zmodAddEquivOfGenerator hgen hcardeq).symm
  have hea : e a = 1 :=
    zmodAddEquivOfGenerator_symm_apply_generator hgen hcardeq
  refine ⟨generates, e, hea, ?_⟩
  intro f hf
  apply AddEquiv.ext
  intro b
  obtain ⟨m, rfl⟩ := generates b
  rw [map_zsmul, hf, map_zsmul, hea]

private noncomputable def bottomTransversal (G : Type) [Group G] :
    Inhomogeneous.Transfer.ExplicitTransversal (⊥ : Subgroup G) G where
  rep := id
  decomposition :=
    { toFun := fun p => (p.2 : G) * p.1
      invFun := fun g => (g, (1 : (⊥ : Subgroup G)))
      left_inv := fun p => by
        apply Prod.ext
        · change (p.2 : G) * p.1 = p.1
          rw [show (p.2 : G) = 1 by exact Subgroup.mem_bot.mp p.2.2]
          exact one_mul _
        · exact Subsingleton.elim _ _
      right_inv := fun g => by simp }
  decomposition_apply := fun _ _ => rfl

private noncomputable def subgroupTransversal
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

private theorem bottom_H2_subsingleton
    {G : Type} [Group G] (M : Rep ℤ G) :
    Subsingleton (Inhomogeneous.H2 (Rep.res (⊥ : Subgroup G).subtype M)) := by
  constructor
  intro x y
  suffices hz : ∀ z : Inhomogeneous.H2 (Rep.res (⊥ : Subgroup G).subtype M), z = 0 by
    rw [hz x, hz y]
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

/-- Restriction to the trivial subgroup and corestriction show that `H²(G,M)` is killed by
`|G|`. -/
private theorem H2_card_smul_eq_zero
    {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    (x : Inhomogeneous.H2 M) :
    Fintype.card G • x = 0 := by
  let T := bottomTransversal G
  have hres : Inhomogeneous.restrictionH2 (⊥ : Subgroup G).subtype M x = 0 :=
    (bottom_H2_subsingleton M).elim _ _
  rw [T.card_index]
  rw [← Inhomogeneous.Transfer.corH2_restriction T M x, hres, map_zero]

private theorem local_H2_finrank_smul_eq_zero
    (x : Inhomogeneous.H2 (MulRep K L)) :
    Module.finrank K L • x = 0 := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact H2_card_smul_eq_zero (MulRep K L) x

private noncomputable def restrictedH1Equiv
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
    ((groupCohomology_mapIso eG eM he 1).toLinearEquiv.toAddEquiv.trans
      (comparisonH1 _).symm)

private noncomputable def restrictedH2Equiv
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
    ((groupCohomology_mapIso eG eM he 2).toLinearEquiv.toAddEquiv.trans
      (comparisonH2 _).symm)

private noncomputable def quotientCoefficientEquiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] :
    (MulRep K L).quotientToInvariants H ≃+
      (MulRep K (IntermediateField.fixedField H)).V := by
  let E := IntermediateField.fixedField H
  let toE : (MulRep K L).quotientToInvariants H → Additive (Units E) := fun x =>
    Additive.ofMul
      { val := ⟨((Additive.toMul x.1 : Units L) : L), by
          intro s
          have hx := x.2 s
          exact congrArg
            (fun z : Additive (Units L) => ((Additive.toMul z : Units L) : L)) hx⟩
        inv := ⟨↑(Additive.toMul x.1 : Units L)⁻¹, by
          intro s
          have hx := x.2 s
          have hxval := congrArg
            (fun z : Additive (Units L) => ((Additive.toMul z : Units L) : L)) hx
          change s.1 ((↑(Additive.toMul x.1 : Units L)⁻¹ : Units L) : L) =
            ((↑(Additive.toMul x.1 : Units L)⁻¹ : Units L) : L)
          simp only [Units.val_inv_eq_inv_val, map_inv₀]
          exact congrArg Inv.inv hxval⟩
        val_inv := by
          apply Subtype.ext
          exact (Additive.toMul x.1 : Units L).val_inv
        inv_val := by
          apply Subtype.ext
          exact (Additive.toMul x.1 : Units L).inv_val }
  let fromE : Additive (Units E) → (MulRep K L).quotientToInvariants H := fun y =>
    ⟨Additive.ofMul (Units.map (algebraMap E L) (Additive.toMul y)), by
      intro s
      apply Additive.toMul.injective
      apply Units.ext
      change s.1 ((Additive.toMul y : Units E).1 : L) =
        ((Additive.toMul y : Units E).1 : L)
      exact (Additive.toMul y : Units E).1.2 s⟩
  exact
    { toFun := toE
      invFun := fromE
      left_inv := fun x => by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Units.ext
        rfl
      right_inv := fun y => by
        apply Additive.toMul.injective
        apply Units.ext
        rfl
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Units.ext
        rfl }

set_option linter.tacticCheckInstances false in
private noncomputable def quotientH2Equiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] :
    Inhomogeneous.H2 ((MulRep K L).quotientToInvariants H) ≃+
      Inhomogeneous.H2 (MulRep K (IntermediateField.fixedField H)) := by
  let eG : (L ≃ₐ[K] L) ⧸ H ≃*
      (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H) :=
    IsGalois.normalAutEquivQuotient H
  let eA := quotientCoefficientEquiv H
  let eM : ((MulRep K L).quotientToInvariants H).V ≃ₗ[ℤ]
      (MulRep K (IntermediateField.fixedField H)).V :=
    { eA with
      map_smul' := fun n x => by
        change eA.toAddMonoidHom (n • x) = n • eA.toAddMonoidHom x
        exact eA.toAddMonoidHom.map_zsmul n x }
  have heM_apply (x : ((MulRep K L).quotientToInvariants H).V) :
      eM x = quotientCoefficientEquiv H x := rfl
  have heM_symm_apply (y : (MulRep K (IntermediateField.fixedField H)).V) :
      eM.symm y = (quotientCoefficientEquiv H).symm y := rfl
  have he : ∀ g, eM.toLinearMap ∘ₗ ((MulRep K L).quotientToInvariants H).ρ g =
      (MulRep K (IntermediateField.fixedField H)).ρ (eG g) ∘ₗ eM.toLinearMap := by
    intro g
    induction g using QuotientGroup.induction_on with
    | _ σ =>
      ext x
      change eM (((MulRep K L).quotientToInvariants H).ρ
          (σ : (L ≃ₐ[K] L) ⧸ H) x) =
        (MulRep K (IntermediateField.fixedField H)).ρ
          (eG (σ : (L ≃ₐ[K] L) ⧸ H)) (eM x)
      apply eM.symm.injective
      rw [eM.symm_apply_apply, heM_symm_apply, heM_apply]
      apply Subtype.ext
      change (MulRep K L).ρ σ x.1 =
        Additive.ofMul (Units.map
          (algebraMap (IntermediateField.fixedField H) L)
          (Additive.toMul ((MulRep K (IntermediateField.fixedField H)).ρ
            (eG (σ : (L ≃ₐ[K] L) ⧸ H)) (quotientCoefficientEquiv H x))))
      change Additive.ofMul
          (σ • Additive.toMul (show Additive (Units L) from x.1)) =
        Additive.ofMul (Units.map
          (algebraMap (IntermediateField.fixedField H) L).toMonoidHom
          (Units.map (eG (σ : (L ≃ₐ[K] L) ⧸ H)).toRingEquiv.toRingHom.toMonoidHom
            (Additive.toMul (show Additive
              (Units (IntermediateField.fixedField H)) from
                quotientCoefficientEquiv H x))))
      apply Additive.toMul.injective
      apply Units.ext
      dsimp [quotientCoefficientEquiv, eG]
      rw [IsGalois.normalAutEquivQuotient_apply,
        AlgEquiv.restrictNormalHom_apply]
  exact (comparisonH2 _).trans
    ((groupCohomology_mapIso eG eM he 2).toLinearEquiv.toAddEquiv.trans
      (comparisonH2 _).symm)

/-- Local-field structures on a fixed field, compatible with both sides of the tower. -/
private structure FixedFieldLocalData
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

private noncomputable def fixedFieldLocalData
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (H : Subgroup (L ≃ₐ[K] L)) : FixedFieldLocalData H := by
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
  letI : Valued E NNReal := normValuedE
  haveI : (Valued.v : Valuation E NNReal).Compatible := by
    rw [show (Valued.v : Valuation E NNReal) = vE from rfl]
    infer_instance
  have htop : IsValuativeTopology E := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using
      (Valued.v : Valuation E NNReal).exists_setOf_restrict_le_iff 0 s
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

/-- Hilbert 90 for the restriction of the unit representation to an arbitrary subgroup. -/
private theorem restricted_H1_subsingleton
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    Subsingleton (Inhomogeneous.H1 (Rep.res H.subtype (MulRep K L))) := by
  let E := IntermediateField.fixedField H
  have h : Subsingleton (Inhomogeneous.H1 (MulRep E L)) :=
    hilbert90_mulRep_inhomogeneous E L
  exact ⟨fun x y => (restrictedH1Equiv H).injective (h.elim _ _)⟩

private theorem local_H2_inflation_restriction_exact
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] :
    Function.Exact
      (Inhomogeneous.InfRes.inflationH2 H (MulRep K L))
      (Inhomogeneous.restrictionH2 H.subtype (MulRep K L)) :=
  Inhomogeneous.InfRes.inflation_restrictionH2_exact_of_H1_zero H (MulRep K L)
    (fun x => (restricted_H1_subsingleton H).elim x 0)

/-- Finite outer terms in an exact `A → B → C` bound the middle cardinal by
`|A|·|C|`; this is the counting step used at each index-`p` stage. -/
private theorem finite_and_card_le_of_exact
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C] (p : A →+ B) (q : B →+ C)
    (hexact : Function.Exact p q) :
    Finite B ∧ Nat.card B ≤ Nat.card A * Nat.card C := by
  have h : p.range = q.ker := by
    ext x
    exact (hexact x).symm
  letI : Finite p.range := Finite.of_surjective p.rangeRestrict fun y => by
    obtain ⟨a, ha⟩ := y.2
    exact ⟨a, Subtype.ext ha⟩
  letI : Finite q.ker := Finite.of_injective (fun x : q.ker =>
    (⟨x, by rw [h]; exact x.2⟩ : p.range)) (fun x y hxy => by
      apply Subtype.ext
      exact congrArg (fun z : p.range => (z : B)) hxy)
  letI : Finite q.range := Finite.of_injective (fun x : q.range => (x : C))
    Subtype.val_injective
  have hB : Finite B :=
    (q.finite_iff_finite_ker_range).2 ⟨inferInstance, inferInstance⟩
  letI : Finite B := hB
  refine ⟨hB, ?_⟩
  have hcard : Nat.card B = Nat.card q.ker * Nat.card q.range := by
    rw [← q.ker.card_mul_index, AddSubgroup.index_ker]
  rw [hcard]
  apply Nat.mul_le_mul
  · exact Nat.card_le_card_of_injective (fun x : q.ker =>
      (⟨x, by rw [h]; exact x.2⟩ : p.range)) (fun x y hxy => by
        apply Subtype.ext
        exact congrArg (fun z : p.range => (z : B)) hxy) |>.trans
        (Nat.card_le_card_of_surjective p.rangeRestrict fun y => by
          obtain ⟨a, ha⟩ := y.2
          exact ⟨a, Subtype.ext ha⟩)
  · exact Nat.card_le_card_of_injective (fun x : q.range => (x : C))
      Subtype.val_injective

/-- The local `H²` bound when the full Galois group is a `p`-group. -/
private theorem local_H2_upperBound_of_isPGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (p : ℕ) [Fact p.Prime]
    (hP : IsPGroup p (L ≃ₐ[K] L)) :
    Finite (Inhomogeneous.H2 (MulRep K L)) ∧
      Nat.card (Inhomogeneous.H2 (MulRep K L)) ≤ Module.finrank K L := by
  classical
  by_cases hcyc : IsCyclic (L ≃ₐ[K] L)
  · letI : IsCyclic (L ≃ₐ[K] L) := hcyc
    exact ⟨cyclic_local_H2_finite K L, (cyclic_local_H2_card K L).le⟩
  · let G := L ≃ₐ[K] L
    haveI : Nontrivial G := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hG
      letI : Subsingleton G := hG
      exact hcyc isCyclic_of_subsingleton
    have hcenterP : IsPGroup p (Subgroup.center G) := hP.to_subgroup _
    letI : Nontrivial (Subgroup.center G) := hP.center_nontrivial
    have hpCenter : p ∣ Nat.card (Subgroup.center G) :=
      hcenterP.card_eq_or_dvd.resolve_left (by
        intro hcard
        have : 1 < Nat.card (Subgroup.center G) :=
          Finite.one_lt_card_iff_nontrivial.mpr inferInstance
        omega)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpCenter
    let N : Subgroup G := Subgroup.zpowers (z : G)
    have hNcenter : N ≤ Subgroup.center G := by
      exact Subgroup.zpowers_le.mpr z.2
    letI : N.Normal := ⟨by
      intro n hn g
      have hn' := (Subgroup.mem_center_iff.mp (hNcenter hn)) g
      have heq : g * n * g⁻¹ = n := by
        calc
          g * n * g⁻¹ = n * g * g⁻¹ := by rw [hn']
          _ = n := by simp
      simpa [heq] using hn⟩
    have hzG : orderOf (z : G) = p := by
      rw [← Subgroup.orderOf_mk (z : G) z.2]
      exact hz
    have hcardN : Nat.card N = p := by
      exact (Nat.card_zpowers (z : G)).trans hzG
    let E := IntermediateField.fixedField N
    let D := fixedFieldLocalData (K := K) (L := L) N
    letI : ValuativeRel E := D.valuativeRel
    letI : IsNonarchimedeanLocalField E := D.localField
    letI : ValuativeExtension K E := D.lowerExtension
    letI : ValuativeExtension E L := D.upperExtension
    let eQG : G ⧸ N ≃* (E ≃ₐ[K] E) := IsGalois.normalAutEquivQuotient N
    have hPE : IsPGroup p (E ≃ₐ[K] E) := (hP.to_quotient N).of_equiv eQG
    have hquot_lt : Nat.card (G ⧸ N) < Nat.card G := by
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hcardN] at hprod
      have hqpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hpgt : 1 < p := (Fact.out : Nat.Prime p).one_lt
      nlinarith
    have hAutE_lt : Nat.card (E ≃ₐ[K] E) < Nat.card G := by
      rw [← Nat.card_congr eQG.toEquiv]
      exact hquot_lt
    have hLower := local_H2_upperBound_of_isPGroup K E p hPE
    letI : IsCyclic (L ≃ₐ[E] L) :=
      (IntermediateField.subgroupEquivAlgEquiv N).isCyclic.mp
        (Subgroup.isCyclic_zpowers (z : G))
    let eQ := quotientH2Equiv N
    let eN := restrictedH2Equiv N
    letI : Finite (Inhomogeneous.H2 (MulRep K E)) := hLower.1
    letI : Finite (Inhomogeneous.H2 ((MulRep K L).quotientToInvariants N)) :=
      Finite.of_equiv _ eQ.symm.toEquiv
    letI : Finite (Inhomogeneous.H2 (MulRep E L)) :=
      cyclic_local_H2_finite E L
    letI : Finite
        (Inhomogeneous.H2 (Rep.res N.subtype (MulRep K L))) :=
      Finite.of_equiv _ eN.symm.toEquiv
    have hcount := finite_and_card_le_of_exact
      (Inhomogeneous.InfRes.inflationH2 N (MulRep K L))
      (Inhomogeneous.restrictionH2 N.subtype (MulRep K L))
      (local_H2_inflation_restriction_exact K L N)
    refine ⟨hcount.1, ?_⟩
    calc
      Nat.card (Inhomogeneous.H2 (MulRep K L)) ≤
          Nat.card (Inhomogeneous.H2 ((MulRep K L).quotientToInvariants N)) *
            Nat.card (Inhomogeneous.H2 (Rep.res N.subtype (MulRep K L))) := hcount.2
      _ = Nat.card (Inhomogeneous.H2 (MulRep K E)) *
            Nat.card (Inhomogeneous.H2 (MulRep E L)) := by
          rw [Nat.card_congr eQ.toEquiv, Nat.card_congr eN.toEquiv]
      _ ≤ Module.finrank K E * Module.finrank E L :=
        Nat.mul_le_mul hLower.2 (cyclic_local_H2_card E L).le
      _ = Module.finrank K L := Module.finrank_mul_finrank K E L
termination_by Nat.card (L ≃ₐ[K] L)
decreasing_by exact hAutE_lt

/-- The restricted local `H²` over a Sylow subgroup has at most the Sylow order. -/
private theorem sylow_restricted_H2_bound
    (p : ℕ) [Fact p.Prime] (P : Sylow p (L ≃ₐ[K] L)) :
    Finite (Inhomogeneous.H2
      (Rep.res (P : Subgroup (L ≃ₐ[K] L)).subtype (MulRep K L))) ∧
    Nat.card (Inhomogeneous.H2
      (Rep.res (P : Subgroup (L ≃ₐ[K] L)).subtype (MulRep K L))) ≤ Nat.card P := by
  let E := IntermediateField.fixedField (P : Subgroup (L ≃ₐ[K] L))
  let D := fixedFieldLocalData (K := K) (L := L)
    (P : Subgroup (L ≃ₐ[K] L))
  letI : ValuativeRel E := D.valuativeRel
  letI : IsNonarchimedeanLocalField E := D.localField
  letI : ValuativeExtension K E := D.lowerExtension
  letI : ValuativeExtension E L := D.upperExtension
  let eG := IntermediateField.subgroupEquivAlgEquiv
    (P : Subgroup (L ≃ₐ[K] L))
  have hPG : IsPGroup p (L ≃ₐ[E] L) := P.isPGroup'.of_equiv eG
  have hlocal := local_H2_upperBound_of_isPGroup E L p hPG
  let eH := restrictedH2Equiv (P : Subgroup (L ≃ₐ[K] L))
  letI : Finite (Inhomogeneous.H2 (MulRep E L)) := hlocal.1
  have hfin : Finite (Inhomogeneous.H2
      (Rep.res (P : Subgroup (L ≃ₐ[K] L)).subtype (MulRep K L))) :=
    Finite.of_equiv _ eH.symm.toEquiv
  letI := hfin
  refine ⟨hfin, ?_⟩
  calc
    Nat.card (Inhomogeneous.H2
        (Rep.res (P : Subgroup (L ≃ₐ[K] L)).subtype (MulRep K L))) =
      Nat.card (Inhomogeneous.H2 (MulRep E L)) := Nat.card_congr eH.toEquiv
    _ ≤ Module.finrank E L := hlocal.2
    _ = Nat.card P := by
      rw [← IsGalois.card_aut_eq_finrank]
      exact (Nat.card_congr eG.toEquiv).symm

/--
The remaining F05 arithmetic induction: apply the six-term edge along normal index-`p`
fixed-field towers, transport the restricted and invariant unit representations to those towers,
and use restriction/corestriction on Sylow subgroups to assemble the primary bounds.
-/
private theorem local_H2_upperBound_sylow_induction :
    Finite (Inhomogeneous.H2 (MulRep K L)) ∧
      Nat.card (Inhomogeneous.H2 (MulRep K L)) ≤ Module.finrank K L := by
  classical
  let G := L ≃ₐ[K] L
  let M := MulRep K L
  let A := Inhomogeneous.H2 M
  let primes := (Nat.card G).primeFactors
  letI primeFact (r : primes) : Fact (Nat.Prime (r : ℕ)) :=
    ⟨(Nat.mem_primeFactors.mp r.2).1⟩
  let P (r : primes) : Sylow (r : ℕ) G := default
  let B (r : primes) := Inhomogeneous.H2
    (Rep.res ((P r : Sylow (r : ℕ) G) : Subgroup G).subtype M)
  letI finiteB (r : primes) : Finite (B r) :=
    (sylow_restricted_H2_bound (K := K) (L := L) (r : ℕ) (P r)).1
  let resProd : A → (∀ r : primes, B r) := fun x r =>
    Inhomogeneous.restrictionH2
      ((P r : Sylow (r : ℕ) G) : Subgroup G).subtype M x
  have hresProd : Function.Injective resProd := by
    intro x y hxy
    apply sub_eq_zero.mp
    let d : A := x - y
    have hd0 : d = 0 := by
      by_contra hd
      have hord : addOrderOf d ≠ 1 := by
        intro h
        exact hd (AddMonoid.addOrderOf_eq_one_iff.mp h)
      obtain ⟨q, hq, hqord⟩ := Nat.exists_prime_and_dvd hord
      have hkillG : Nat.card G • d = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact H2_card_smul_eq_zero M d
      have hordG : addOrderOf d ∣ Nat.card G :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkillG
      have hqG : q ∣ Nat.card G := hqord.trans hordG
      let r : primes := ⟨q, Nat.mem_primeFactors.mpr
        ⟨hq, hqG, Nat.card_pos.ne'⟩⟩
      have hresd : Inhomogeneous.restrictionH2
          ((P r : Sylow q G) : Subgroup G).subtype M d = 0 := by
        have hr := congrFun hxy r
        change Inhomogeneous.restrictionH2
            ((P r : Sylow q G) : Subgroup G).subtype M x =
          Inhomogeneous.restrictionH2
            ((P r : Sylow q G) : Subgroup G).subtype M y at hr
        change Inhomogeneous.restrictionH2
            ((P r : Sylow q G) : Subgroup G).subtype M (x - y) = 0
        rw [map_sub, hr, sub_self]
      let ι := Quotient (QuotientGroup.rightRel
        ((P r : Sylow q G) : Subgroup G))
      letI : Fintype ι := Fintype.ofFinite ι
      let T := subgroupTransversal ((P r : Sylow q G) : Subgroup G)
      have hindex : ((P r : Sylow q G) : Subgroup G).index • d = 0 := by
        rw [← Inhomogeneous.Transfer.corH2_restriction T M d, hresd, map_zero]
      have hordIndex : addOrderOf d ∣
          ((P r : Sylow q G) : Subgroup G).index :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hindex
      exact (P r).not_dvd_index (hqord.trans hordIndex)
    exact hd0
  have hfinite : Finite A := Finite.of_injective resProd hresProd
  letI : Finite A := hfinite
  have hfactor : (Nat.card A).factorization ≤ (Nat.card G).factorization := by
    rw [Finsupp.le_def]
    intro q
    by_cases hq : Nat.Prime q
    · letI : Fact (Nat.Prime q) := ⟨hq⟩
      let PA : Sylow q (Multiplicative A) := default
      let PG : Sylow q G := default
      let C := Inhomogeneous.H2
        (Rep.res ((PG : Sylow q G) : Subgroup G).subtype M)
      letI : Finite C :=
        (sylow_restricted_H2_bound (K := K) (L := L) q PG).1
      let ι := Quotient (QuotientGroup.rightRel
        ((PG : Sylow q G) : Subgroup G))
      letI : Fintype ι := Fintype.ofFinite ι
      let T := subgroupTransversal ((PG : Sylow q G) : Subgroup G)
      have hresPA : Function.Injective (fun x : PA =>
          Inhomogeneous.restrictionH2
            ((PG : Sylow q G) : Subgroup G).subtype M x.1.toAdd) := by
        intro x y hxy
        have hindex : ((PG : Sylow q G) : Subgroup G).index • x.1.toAdd =
            ((PG : Sylow q G) : Subgroup G).index • y.1.toAdd := by
          calc
            ((PG : Sylow q G) : Subgroup G).index • x.1.toAdd =
                Inhomogeneous.Transfer.corH2 T M
                  (Inhomogeneous.restrictionH2
                    ((PG : Sylow q G) : Subgroup G).subtype M x.1.toAdd) :=
              (Inhomogeneous.Transfer.corH2_restriction T M x.1.toAdd).symm
            _ = Inhomogeneous.Transfer.corH2 T M
                  (Inhomogeneous.restrictionH2
                    ((PG : Sylow q G) : Subgroup G).subtype M y.1.toAdd) := by
              change Inhomogeneous.restrictionH2
                  ((PG : Sylow q G) : Subgroup G).subtype M x.1.toAdd =
                Inhomogeneous.restrictionH2
                  ((PG : Sylow q G) : Subgroup G).subtype M y.1.toAdd at hxy
              exact congrArg (Inhomogeneous.Transfer.corH2 T M) hxy
            _ = ((PG : Sylow q G) : Subgroup G).index • y.1.toAdd :=
              Inhomogeneous.Transfer.corH2_restriction T M y.1.toAdd
        have hpow : x ^ ((PG : Sylow q G) : Subgroup G).index =
            y ^ ((PG : Sylow q G) : Subgroup G).index := by
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          change ((PG : Sylow q G) : Subgroup G).index • x.1.toAdd =
            ((PG : Sylow q G) : Subgroup G).index • y.1.toAdd
          exact hindex
        exact (PA.isPGroup'.powEquiv' PG.not_dvd_index).injective hpow
      have hcardPA : Nat.card PA ≤ Nat.card C :=
        Nat.card_le_card_of_injective _ hresPA
      have hcardC : Nat.card C ≤ Nat.card PG :=
        (sylow_restricted_H2_bound (K := K) (L := L) q PG).2
      have hmulCard : Nat.card (Multiplicative A) = Nat.card A :=
        Nat.card_congr (Multiplicative.toAdd : Multiplicative A ≃ A)
      have hpows : q ^ (Nat.card A).factorization q ≤
          q ^ (Nat.card G).factorization q := by
        calc
          q ^ (Nat.card A).factorization q = Nat.card PA := by
            simpa [hmulCard] using (Sylow.card_eq_multiplicity PA).symm
          _ ≤ Nat.card C := hcardPA
          _ ≤ Nat.card PG := hcardC
          _ = q ^ (Nat.card G).factorization q := Sylow.card_eq_multiplicity PG
      exact (Nat.pow_le_pow_iff_right hq.one_lt).mp hpows
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  have hcardDvd : Nat.card A ∣ Nat.card G :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp hfactor
  refine ⟨hfinite, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank K L]
  exact Nat.le_of_dvd Nat.card_pos hcardDvd

/--
**F05**, Theorem `thm:H2-upper-bound`: for every finite Galois local extension, `H²(G,Lˣ)` is
finite and has cardinality at most `|G|=[L:K]`.  Finiteness is part of the statement, rather than
being hidden by the convention `Nat.card X = 0` for infinite `X`.
-/
theorem local_H2_upperBound :
    Finite (Inhomogeneous.H2 (MulRep K L)) ∧
      Nat.card (Inhomogeneous.H2 (MulRep K L)) ≤ Module.finrank K L :=
  local_H2_upperBound_sylow_induction K L

/--
**F05**, Theorem `thm:H2-upper-bound`: its finiteness component as an installable instance.
-/
theorem local_H2_finite : Finite (Inhomogeneous.H2 (MulRep K L)) :=
  (local_H2_upperBound K L).1

section Envelope

variable (U M : Type) [Field U] [Field M]
  [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
  [IsScalarTower K L M] [IsScalarTower K U M]
  [FiniteDimensional K U] [FiniteDimensional K M]
  [FiniteDimensional L M] [FiniteDimensional U M]
  [IsGalois K U] [IsGalois K M] [IsGalois L M]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension K U] [ValuativeExtension K M]
  [ValuativeExtension L M] [ValuativeExtension U M]
  [ContinuousSMul K U] [ContinuousSMul K M]
  [ContinuousSMul L M] [ContinuousSMul U M]

/--
**F08**, Lemma `lem:psi-restricts-zero` and Theorem `thm:local-fundamental-class`: the full
unramified-envelope and descent data for `M = L K_n`, where `n=[L:K]`.

All three cohomology maps below are `transportedH2` applied to pointwise-pinned group and
coefficient morphisms.  The fields `psi_eq_inflated`, `psi_restricts_zero`, and
`descent_unique` are therefore substantive equations about the carry class.
-/
structure UnramifiedEnvelopeData (π : Uniformizer K) where
  /-- The unramified degree-`n` source `U/K`. -/
  source : UnramifiedCyclicExtensionData K U
  /-- The source has degree `n=[L:K]`. -/
  source_degree : Module.finrank K U = Module.finrank K L
  /-- The unramified extension `M/L`. -/
  upper : UnramifiedCyclicExtensionData L M
  /-- `M` is generated over `K` by the displayed copies of `L` and `U`. -/
  compositum_eq_top :
    Algebra.adjoin K (Set.range (algebraMap L M) ∪ Set.range (algebraMap U M)) = ⊤
  /-- The intersection of the two displayed subfields inside `M`. -/
  intersection : IntermediateField K M
  /-- Its carrier is literally the intersection of the images of `L` and `U`. -/
  mem_intersection_iff : ∀ x : M, x ∈ intersection ↔
    (∃ l : L, algebraMap L M l = x) ∧ (∃ u : U, algebraMap U M u = x)
  /-- `L ∩ U` is the maximal unramified part, of degree `f(L/K)`. -/
  intersection_degree : Module.finrank K intersection = residueDegree K L
  /-- Consequently `[M:L]=e(L/K)`. -/
  envelope_degree_over_L : Module.finrank L M = ramificationIndex K L
  /-- The pinned carry class on `U/K`. -/
  sourceClass : UnramifiedClassData K U source π
  /-- Restriction `Gal(M/K) → Gal(U/K)` used to inflate the source class. -/
  sourceQuotient : (M ≃ₐ[K] M) →* (U ≃ₐ[K] U)
  /-- The source quotient is literal restriction along `U ↪ M`. -/
  sourceQuotient_apply : ∀ (σ : M ≃ₐ[K] M) (x : U),
    algebraMap U M (sourceQuotient σ x) = σ (algebraMap U M x)
  /-- The corresponding coefficient inclusion `Uˣ → Mˣ`. -/
  sourceCoefficient : Rep.res sourceQuotient (MulRep K U) ⟶ MulRep K M
  /-- The coefficient morphism is the actual field embedding. -/
  sourceCoefficient_apply : ∀ x : Units U,
    Additive.toMul (sourceCoefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap U M) x
  /-- The inflated unramified class `ψ`. -/
  psi : Inhomogeneous.H2 (MulRep K M)
  /-- Defining equation for `ψ`. -/
  psi_eq_inflated : psi =
    transportedH2 sourceQuotient sourceCoefficient sourceClass.class
  /-- Inflation is injective (the Hilbert-90 kernel is zero). -/
  source_inflation_injective :
    Function.Injective (transportedH2 sourceQuotient sourceCoefficient)
  /-- Hence `ψ` retains exact order `n`. -/
  psi_order : addOrderOf psi = Module.finrank K L
  /-- Inclusion `Gal(M/L) → Gal(M/K)` for the restriction calculation. -/
  upperSubgroup : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)
  /-- It is the identity on the underlying automorphism of `M`. -/
  upperSubgroup_apply : ∀ (σ : M ≃ₐ[L] M) (x : M), upperSubgroup σ x = σ x
  /-- Identity coefficient morphism for restriction to `Gal(M/L)`. -/
  upperCoefficient : Rep.res upperSubgroup (MulRep K M) ⟶ MulRep L M
  /-- It leaves every unit of `M` unchanged. -/
  upperCoefficient_apply : ∀ x : Units M,
    upperCoefficient.hom (Additive.ofMul x) = Additive.ofMul x
  /-- **F08**, Lemma `lem:psi-restricts-zero`: the restricted carry class is zero. -/
  psi_restricts_zero : transportedH2 upperSubgroup upperCoefficient psi = 0
  /-- Restriction `Gal(M/K) → Gal(L/K)` used for descent. -/
  descentQuotient : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)
  /-- The descent quotient is literal restriction along `L ↪ M`. -/
  descentQuotient_apply : ∀ (σ : M ≃ₐ[K] M) (x : L),
    algebraMap L M (descentQuotient σ x) = σ (algebraMap L M x)
  /-- Coefficient inclusion `Lˣ → Mˣ` for descent inflation. -/
  descentCoefficient : Rep.res descentQuotient (MulRep K L) ⟶ MulRep K M
  /-- It is the actual field embedding. -/
  descentCoefficient_apply : ∀ x : Units L,
    Additive.toMul (descentCoefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap L M) x
  /-- Inflation from `L/K` into the envelope is injective. -/
  descent_injective :
    Function.Injective (transportedH2 descentQuotient descentCoefficient)
  /-- The zero-restriction calculation puts `ψ` in the actual inflation range. -/
  psi_in_descent_range :
    psi ∈ Set.range (transportedH2 descentQuotient descentCoefficient)
  /-- The preimage of `ψ` is unique. -/
  descent_unique : ∀ α β : Inhomogeneous.H2 (MulRep K L),
    transportedH2 descentQuotient descentCoefficient α = psi →
      transportedH2 descentQuotient descentCoefficient β = psi → α = β

private theorem envelope_preimage_existsUnique (π : Uniformizer K)
    (D : UnramifiedEnvelopeData K L U M π) :
    ∃! α : Inhomogeneous.H2 (MulRep K L),
      transportedH2 D.descentQuotient D.descentCoefficient α = D.psi := by
  obtain ⟨α, hα⟩ := D.psi_in_descent_range
  refine ⟨α, hα, ?_⟩
  intro β hβ
  exact D.descent_unique β α hβ hα

/-- The unique class descending to the inflated carry class in a pinned envelope. -/
noncomputable def unramifiedEnvelopePreimage (π : Uniformizer K)
    (D : UnramifiedEnvelopeData K L U M π) :
    Inhomogeneous.H2 (MulRep K L) :=
  (envelope_preimage_existsUnique K L U M π D).choose

/-- The chosen envelope preimage has the required inflated image. -/
theorem unramifiedEnvelopePreimage_spec (π : Uniformizer K)
    (D : UnramifiedEnvelopeData K L U M π) :
    transportedH2 D.descentQuotient D.descentCoefficient
        (unramifiedEnvelopePreimage K L U M π D) = D.psi :=
  (envelope_preimage_existsUnique K L U M π D).choose_spec.1

private theorem envelope_preimage_order (π : Uniformizer K)
    (D : UnramifiedEnvelopeData K L U M π)
    (α : Inhomogeneous.H2 (MulRep K L))
    (hα : transportedH2 D.descentQuotient D.descentCoefficient α = D.psi) :
    addOrderOf α = Module.finrank K L := by
  rw [← addOrderOf_injective
    (transportedH2 D.descentQuotient D.descentCoefficient)
    D.descent_injective α, hα, D.psi_order]

end Envelope

/--
**F08**, Theorem `thm:local-fundamental-class`: a class descends from every pinned unramified
envelope.  Quantifying over the full envelope data
makes the characterization independent of all auxiliary choices, including the uniformizer.
-/
def DescendsFromUnramifiedEnvelopes
    (α : Inhomogeneous.H2 (MulRep K L)) : Prop :=
  ∀ (π : Uniformizer K) (U M : Type)
    [Field U] [Field M]
    [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
    [IsScalarTower K L M] [IsScalarTower K U M]
    [FiniteDimensional K U] [FiniteDimensional K M]
    [FiniteDimensional L M] [FiniteDimensional U M]
    [IsGalois K U] [IsGalois K M] [IsGalois L M]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension K U] [ValuativeExtension K M]
    [ValuativeExtension L M] [ValuativeExtension U M]
    [ContinuousSMul K U] [ContinuousSMul K M]
    [ContinuousSMul L M] [ContinuousSMul U M]
    (D : UnramifiedEnvelopeData K L U M π),
      transportedH2 D.descentQuotient D.descentCoefficient α = D.psi

/--
The field-theoretic output of the unramified-tower construction, before any cohomology class is
chosen.  Keeping this package separate is what makes the proof order explicit: geometry first,
then carry inflation and inf--res descent.
-/
private structure UnramifiedEnvelopeGeometry
    (K L U M : Type)
    [Field K] [Field L] [Field U] [Field M]
    [Algebra K L] [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
    [IsScalarTower K L M] [IsScalarTower K U M]
    [FiniteDimensional K L] [FiniteDimensional K U] [FiniteDimensional K M]
    [FiniteDimensional L M] [FiniteDimensional U M]
    [IsGalois K L] [IsGalois K U] [IsGalois K M] [IsGalois L M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension K L] [ValuativeExtension K U] [ValuativeExtension K M]
    [ValuativeExtension L M] [ValuativeExtension U M]
    [ContinuousSMul K L] [ContinuousSMul K U] [ContinuousSMul K M]
    [ContinuousSMul L M] [ContinuousSMul U M] where
  source : UnramifiedCyclicExtensionData K U
  source_degree : Module.finrank K U = Module.finrank K L
  upper : UnramifiedCyclicExtensionData L M
  compositum_eq_top :
    Algebra.adjoin K (Set.range (algebraMap L M) ∪ Set.range (algebraMap U M)) = ⊤
  intersection : IntermediateField K M
  mem_intersection_iff : ∀ x : M, x ∈ intersection ↔
    (∃ l : L, algebraMap L M l = x) ∧ (∃ u : U, algebraMap U M u = x)
  intersection_degree : Module.finrank K intersection = residueDegree K L
  envelope_degree_over_L : Module.finrank L M = ramificationIndex K L

/-- Literal restriction from a Galois tower to its normal intermediate field. -/
private noncomputable def towerQuotientHom
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    (M ≃ₐ[K] M) →* (E ≃ₐ[K] E) :=
  AlgEquiv.restrictNormalHom E

/-- Coefficient inclusion accompanying `towerQuotientHom`. -/
private noncomputable def towerInflationCoefficient
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    Rep.res (towerQuotientHom K E M) (MulRep K E) ⟶ MulRep K M := by
  let i : Additive (Units E) →+ Additive (Units M) :=
    (Units.map (algebraMap E M)).toAdditive
  exact Rep.ofHom ⟨i.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes σ E
      ((Additive.toMul x : Units E) : E)⟩

/-- Literal inclusion of the upper Galois group in a field tower. -/
private noncomputable def towerSubgroupHom
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M] :
    (M ≃ₐ[E] M) →* (M ≃ₐ[K] M) :=
  AlgEquiv.restrictScalarsHom K

/-- Identity coefficient map accompanying `towerSubgroupHom`. -/
private noncomputable def towerRestrictionCoefficient
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M] :
    Rep.res (towerSubgroupHom K E M) (MulRep K M) ⟶ MulRep E M := by
  exact Rep.ofHom ⟨(AddMonoidHom.id (Additive (Units M))).toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    rfl⟩

/-- Functoriality of the concrete comparison-layer `H²` transport. -/
private theorem transportedH2_comp
    {G H J : Type} [Group G] [Group H] [Group J]
    {A : Rep ℤ G} {B : Rep ℤ H} {C : Rep ℤ J}
    (f : H →* G) (g : J →* H)
    (φ : Rep.res f A ⟶ B) (ψ : Rep.res g B ⟶ C)
    (x : Inhomogeneous.H2 A) :
    transportedH2 g ψ (transportedH2 f φ x) =
      transportedH2 (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) x := by
  apply (comparisonH2 C).injective
  simp only [transportedH2, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply]
  change (groupCohomology.map g ψ 2).hom
      ((groupCohomology.map f φ 2).hom (comparisonH2 A x)) =
    (groupCohomology.map (f.comp g) ((Rep.resFunctor g).map φ ≫ ψ) 2).hom
      (comparisonH2 A x)
  rw [groupCohomology.map_comp]
  rfl

/-- The tautological valuative extension used for the degree-one carry class. -/
private theorem selfValuativeExtension
    (F : Type) [Field F] [ValuativeRel F] : ValuativeExtension F F :=
  ⟨fun _ _ => Iff.rfl⟩

private theorem self_ramificationIndex
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [ValuativeExtension F F] :
    ramificationIndex F F = 1 := by
  have h := normalizedValuation_algebraMap F F (defaultUniformizer F).val
  have hval := (defaultUniformizer F).valuation_eq_one
  simp [hval] at h
  exact_mod_cast h.symm

/-- Arithmetic Frobenius data for the degree-one unramified extension. -/
private noncomputable def selfUnramifiedCyclicExtensionData
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
  let e : Multiplicative (ZMod (Module.finrank F F)) ≃* (F ≃ₐ[F] F) :=
    zmodMulEquivOfGenerator hmem (IsGalois.card_aut_eq_finrank F F)
  refine {
    unramified := ⟨self_ramificationIndex F⟩
    frobenius := frob
    frobenius_preserves_integral := ?_
    frobenius_residue := ?_
    frobenius_generates := hgen
    frobeniusEquiv := e
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

private theorem unramifiedClassData_transport_class
    {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension F E] [ContinuousSMul F E]
    {D₁ D₂ : UnramifiedCyclicExtensionData F E} (h : D₁ = D₂)
    (π : Uniformizer F) (C : UnramifiedClassData F E D₁ π) :
    (h ▸ C).class = C.class := by
  subst h
  rfl

private theorem towerQuotient_ker_eq_fixing
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    (towerQuotientHom K E M).ker =
      (IsScalarTower.toAlgHom K E M).fieldRange.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    have hc := AlgEquiv.restrictNormal_commutes σ E y
    change σ.restrictNormal E = 1 at h
    rw [h] at hc
    exact hc.symm
  · intro h
    apply AlgEquiv.ext
    intro y
    apply (algebraMap E M).injective
    have hc := AlgEquiv.restrictNormal_commutes σ E y
    change algebraMap E M (σ.restrictNormal E y) = algebraMap E M y
    exact hc.trans (h (algebraMap E M y) ⟨y, rfl⟩)

private noncomputable def towerKernelEquiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    (towerQuotientHom K E M).ker ≃* (M ≃ₐ[E] M) where
  toFun n :=
    { n.1 with
      commutes' := fun x => by
        have hc := AlgEquiv.restrictNormal_commutes n.1 E x
        have hn : n.1.restrictNormal E = 1 := n.2
        rw [hn] at hc
        exact hc.symm }
  invFun σ := ⟨towerSubgroupHom K E M σ, by
    rw [towerQuotient_ker_eq_fixing K E M,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact σ.commutes y⟩
  left_inv n := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    rfl
  map_mul' x y := by
    apply AlgEquiv.ext
    intro z
    rfl

private theorem towerInvariant_mem_fieldRange
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M]
    (x : (MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker) :
    ((Additive.toMul x.1 : Units M) : M) ∈
      (IsScalarTower.toAlgHom K E M).fieldRange := by
  rw [← IsGalois.fixedField_fixingSubgroup
    (IsScalarTower.toAlgHom K E M).fieldRange]
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  let n : (towerQuotientHom K E M).ker := ⟨σ, by
    rw [towerQuotient_ker_eq_fixing K E M]
    exact hσ⟩
  have hx := x.2 n
  exact congrArg
    (fun z : Additive (Units M) => ((Additive.toMul z : Units M) : M)) hx

private noncomputable def towerQuotientCoefficientEquiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    (MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker ≃+
      (MulRep K E).V := by
  let i : E →ₐ[K] M := IsScalarTower.toAlgHom K E M
  let e : E ≃ₐ[K] i.fieldRange := i.equivFieldRange
  let toE : (MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker →
      Additive (Units E) := fun x =>
    let ux : Units i.fieldRange :=
      { val := ⟨(Additive.toMul x.1 : Units M).val,
          towerInvariant_mem_fieldRange K E M x⟩
        inv := ⟨(Additive.toMul x.1 : Units M).inv, by
          rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val]
          exact (IsScalarTower.toAlgHom K E M).fieldRange.inv_mem
            (towerInvariant_mem_fieldRange K E M x)⟩
        val_inv := by
          apply Subtype.ext
          exact (Additive.toMul x.1 : Units M).val_inv
        inv_val := by
          apply Subtype.ext
          exact (Additive.toMul x.1 : Units M).inv_val }
    Additive.ofMul (Units.map e.symm.toRingEquiv.toRingHom ux)
  let fromE : Additive (Units E) →
      (MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker := fun y =>
    ⟨Additive.ofMul (Units.map (algebraMap E M) (Additive.toMul y)), by
      intro n
      apply Additive.toMul.injective
      apply Units.ext
      have hc := AlgEquiv.restrictNormal_commutes n.1 E
        ((Additive.toMul y : Units E) : E)
      have hn : n.1.restrictNormal E = 1 := n.2
      rw [hn] at hc
      exact hc.symm⟩
  exact
    { toFun := toE
      invFun := fromE
      left_inv := fun x => by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Units.ext
        change i (e.symm ⟨((Additive.toMul x.1 : Units M) : M), _⟩) =
          ((Additive.toMul x.1 : Units M) : M)
        exact congrArg Subtype.val (e.apply_symm_apply
          ⟨((Additive.toMul x.1 : Units M) : M),
            towerInvariant_mem_fieldRange K E M x⟩)
      right_inv := fun y => by
        apply Additive.toMul.injective
        apply Units.ext
        change e.symm ⟨i ((Additive.toMul y : Units E) : E), _⟩ =
          ((Additive.toMul y : Units E) : E)
        apply e.injective
        rw [e.apply_symm_apply]
        apply Subtype.ext
        rfl
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Units.ext
        change e.symm ⟨((Additive.toMul x.1 : Units M) : M) *
            ((Additive.toMul y.1 : Units M) : M), _⟩ =
          e.symm ⟨((Additive.toMul x.1 : Units M) : M), _⟩ *
            e.symm ⟨((Additive.toMul y.1 : Units M) : M), _⟩
        rw [← map_mul]
        congr 1 }

private noncomputable def towerQuotientGroupEquiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    (M ≃ₐ[K] M) ⧸ (towerQuotientHom K E M).ker ≃* (E ≃ₐ[K] E) :=
  QuotientGroup.quotientKerEquivOfSurjective (towerQuotientHom K E M)
    (AlgEquiv.restrictNormalHom_surjective M)

private noncomputable def towerQuotientLinearEquiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    ((MulRep K M).quotientToInvariants
      (towerQuotientHom K E M).ker).V ≃ₗ[ℤ] (MulRep K E).V :=
  { towerQuotientCoefficientEquiv K E M with
    map_smul' := fun n x => by
      change (towerQuotientCoefficientEquiv K E M).toAddMonoidHom (n • x) =
        n • (towerQuotientCoefficientEquiv K E M).toAddMonoidHom x
      exact (towerQuotientCoefficientEquiv K E M).toAddMonoidHom.map_zsmul n x }

private theorem towerQuotientLinearEquiv_equivariant
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    ∀ g, (towerQuotientLinearEquiv K E M).toLinearMap ∘ₗ
      ((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker).ρ g =
      (MulRep K E).ρ (towerQuotientGroupEquiv K E M g) ∘ₗ
        (towerQuotientLinearEquiv K E M).toLinearMap := by
  intro g
  induction g using QuotientGroup.induction_on with
  | _ σ =>
    ext x
    change towerQuotientLinearEquiv K E M
        (((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker).ρ
          (σ : (M ≃ₐ[K] M) ⧸ (towerQuotientHom K E M).ker) x) =
      (MulRep K E).ρ
        (towerQuotientGroupEquiv K E M
          (σ : (M ≃ₐ[K] M) ⧸ (towerQuotientHom K E M).ker))
        (towerQuotientLinearEquiv K E M x)
    apply (towerQuotientLinearEquiv K E M).symm.injective
    rw [(towerQuotientLinearEquiv K E M).symm_apply_apply]
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    change σ (((Additive.toMul x.1 : Units M) : M)) =
      algebraMap E M
        ((towerQuotientGroupEquiv K E M
            (QuotientGroup.mk' (towerQuotientHom K E M).ker σ))
          ((Additive.toMul
            (towerQuotientCoefficientEquiv K E M x) : Units E) : E))
    rw [show towerQuotientGroupEquiv K E M
      (QuotientGroup.mk' (towerQuotientHom K E M).ker σ) =
        towerQuotientHom K E M σ from rfl]
    have hx := (towerQuotientCoefficientEquiv K E M).symm_apply_apply x
    have hx' := congrArg (fun z :
        ((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker).V =>
      ((Additive.toMul z.1 : Units M) : M)) hx
    rw [← hx']
    have hc := AlgEquiv.restrictNormal_commutes σ E
      ((Additive.toMul
        (towerQuotientCoefficientEquiv K E M x) : Units E) : E)
    exact hc.symm

private noncomputable def towerQuotientH2Equiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    Inhomogeneous.H2
        ((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker) ≃+
      Inhomogeneous.H2 (MulRep K E) :=
  (comparisonH2 _).trans
    ((groupCohomology_mapIso (towerQuotientGroupEquiv K E M)
      (towerQuotientLinearEquiv K E M)
      (towerQuotientLinearEquiv_equivariant K E M) 2).toLinearEquiv.toAddEquiv.trans
        (comparisonH2 _).symm)

private noncomputable def towerKernelH2Equiv
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M] :
    Inhomogeneous.H2
        (Rep.res (towerQuotientHom K E M).ker.subtype (MulRep K M)) ≃+
      Inhomogeneous.H2 (MulRep E M) := by
  let eG := towerKernelEquiv K E M
  let eM : (Rep.res (towerQuotientHom K E M).ker.subtype
      (MulRep K M)).V ≃ₗ[ℤ] (MulRep E M).V := LinearEquiv.refl ℤ _
  have he : ∀ g, eM.toLinearMap ∘ₗ
      (Rep.res (towerQuotientHom K E M).ker.subtype (MulRep K M)).ρ g =
      (MulRep E M).ρ (eG g) ∘ₗ eM.toLinearMap := by
    intro g
    ext x
    rfl
  exact (comparisonH2 _).trans
    ((groupCohomology_mapIso eG eM he 2).toLinearEquiv.toAddEquiv.trans
      (comparisonH2 _).symm)

set_option maxHeartbeats 800000 in
private theorem towerQuotientH2Equiv_inflation
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M]
    (x : Inhomogeneous.H2
      ((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker)) :
    transportedH2 (towerQuotientHom K E M) (towerInflationCoefficient K E M)
        (towerQuotientH2Equiv K E M x) =
      Inhomogeneous.InfRes.inflationH2
        (towerQuotientHom K E M).ker (MulRep K M) x := by
  let eG := towerQuotientGroupEquiv K E M
  let eM := towerQuotientLinearEquiv K E M
  have he := towerQuotientLinearEquiv_equivariant K E M
  let φ : Rep.res eG.symm
      ((MulRep K M).quotientToInvariants
        (towerQuotientHom K E M).ker) ⟶ MulRep K E :=
    Rep.ofHom ⟨eM.toLinearMap, fun h => by
      change eM.toLinearMap ∘ₗ
          ((MulRep K M).quotientToInvariants
            (towerQuotientHom K E M).ker).ρ (eG.symm h) =
        (MulRep K E).ρ h ∘ₗ eM.toLinearMap
      have hh := he (eG.symm h)
      rw [eG.apply_symm_apply] at hh
      exact hh⟩
  have hmap :
      (groupCohomology_mapIso eG eM he 2).hom ≫
          groupCohomology.map (towerQuotientHom K E M)
            (towerInflationCoefficient K E M) 2 =
        groupCohomology.map (QuotientGroup.mk' (towerQuotientHom K E M).ker)
          (Rep.ofHom <| (MulRep K M).ρ.quotientToInvariants_lift
            (towerQuotientHom K E M).ker) 2 := by
    rw [show (groupCohomology_mapIso eG eM he 2).hom =
      groupCohomology.map eG.symm φ 2 from rfl]
    rw [← groupCohomology.map_comp]
    apply groupCohomology_map_congr
    · ext σ
      apply eG.injective
      change eG (eG.symm (towerQuotientHom K E M σ)) =
        eG (QuotientGroup.mk' (towerQuotientHom K E M).ker σ)
      rw [eG.apply_symm_apply]
      rfl
    · apply LinearMap.ext
      intro z
      change (towerInflationCoefficient K E M).hom (eM z) = z.1
      have hz := (towerQuotientCoefficientEquiv K E M).symm_apply_apply z
      have hz' := congrArg Subtype.val hz
      exact hz'
  apply (comparisonH2 (MulRep K M)).injective
  rw [Inhomogeneous.InfRes.comparisonH2_inflation]
  simp only [transportedH2, towerQuotientH2Equiv, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, AddMonoidHom.coe_comp,
    AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  exact ConcreteCategory.congr_hom hmap
    ((comparisonH2
      ((MulRep K M).quotientToInvariants (towerQuotientHom K E M).ker)) x)

set_option maxHeartbeats 800000 in
private theorem towerKernelH2Equiv_restriction
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M]
    [IsGalois K E] [IsGalois K M]
    (x : Inhomogeneous.H2 (MulRep K M)) :
    towerKernelH2Equiv K E M
        (Inhomogeneous.restrictionH2
          (towerQuotientHom K E M).ker.subtype (MulRep K M) x) =
      transportedH2 (towerSubgroupHom K E M)
        (towerRestrictionCoefficient K E M) x := by
  let eG := towerKernelEquiv K E M
  let eM : (Rep.res (towerQuotientHom K E M).ker.subtype
      (MulRep K M)).V ≃ₗ[ℤ] (MulRep E M).V := LinearEquiv.refl ℤ _
  have he : ∀ g, eM.toLinearMap ∘ₗ
      (Rep.res (towerQuotientHom K E M).ker.subtype (MulRep K M)).ρ g =
      (MulRep E M).ρ (eG g) ∘ₗ eM.toLinearMap := by
    intro g
    ext z
    rfl
  have hmap :
      groupCohomology.map (towerQuotientHom K E M).ker.subtype (𝟙 _) 2 ≫
          (groupCohomology_mapIso eG eM he 2).hom =
        groupCohomology.map (towerSubgroupHom K E M)
          (towerRestrictionCoefficient K E M) 2 := by
    rw [groupCohomology_mapIso_hom]
    rw [← groupCohomology.map_comp]
    apply groupCohomology_map_congr
    · ext σ
      rfl
    · apply LinearMap.ext
      intro z
      rfl
  apply (comparisonH2 (MulRep E M)).injective
  have hres := (restrictionComparison
    (towerQuotientHom K E M).ker.subtype (MulRep K M)).commutes2 x
  simp only [towerKernelH2Equiv, AddEquiv.trans_apply, transportedH2,
    AddEquiv.apply_symm_apply, AddMonoidHom.coe_comp,
    AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  rw [hres]
  exact ConcreteCategory.congr_hom hmap (comparisonH2 (MulRep K M) x)

set_option maxHeartbeats 1200000 in
/--
The comparison-layer form of inflation--restriction for a literal field tower.  This is the only
bridge between `InfRes.lean` and `transportedH2` needed by envelope descent.
-/
private theorem towerTransportedH2_infRes
    (K E M : Type) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M] [FiniteDimensional E M]
    [IsGalois K E] [IsGalois K M] :
    Function.Injective
        (transportedH2 (towerQuotientHom K E M)
          (towerInflationCoefficient K E M)) ∧
      Function.Exact
        (transportedH2 (towerQuotientHom K E M)
          (towerInflationCoefficient K E M))
        (transportedH2 (towerSubgroupHom K E M)
          (towerRestrictionCoefficient K E M)) := by
  classical
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  let N := (towerQuotientHom K E M).ker
  letI : N.Normal := (towerQuotientHom K E M).normal_ker
  let qE := towerQuotientH2Equiv K E M
  let kE := towerKernelH2Equiv K E M
  have hH1 : Subsingleton
      (Inhomogeneous.H1 (Rep.res N.subtype (MulRep K M))) :=
    restricted_H1_subsingleton (K := K) (L := M) N
  have hinf : Function.Injective
      (Inhomogeneous.InfRes.inflationH2 N (MulRep K M)) := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : Inhomogeneous.InfRes.inflationH2 N (MulRep K M) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ :=
      ((Inhomogeneous.InfRes.fiveTerm_exact N (MulRep K M)).exact_at_H2Q
        (x - y)).1 hz
    have ha0 : a = 0 := by
      apply Subtype.ext
      exact hH1.elim _ _
    rw [← ha, ha0, map_zero]
  have hexact :=
    Inhomogeneous.InfRes.inflation_restrictionH2_exact_of_H1_zero
      N (MulRep K M) (fun x => hH1.elim x 0)
  constructor
  · intro x y hxy
    apply qE.symm.injective
    apply hinf
    have hxcomp :
        transportedH2 (towerQuotientHom K E M)
            (towerInflationCoefficient K E M) x =
          Inhomogeneous.InfRes.inflationH2 N (MulRep K M) (qE.symm x) := by
      simpa [qE, N] using towerQuotientH2Equiv_inflation K E M (qE.symm x)
    have hycomp :
        transportedH2 (towerQuotientHom K E M)
            (towerInflationCoefficient K E M) y =
          Inhomogeneous.InfRes.inflationH2 N (MulRep K M) (qE.symm y) := by
      simpa [qE, N] using towerQuotientH2Equiv_inflation K E M (qE.symm y)
    rw [← hxcomp, ← hycomp]
    exact hxy
  · intro x
    constructor
    · intro hx
      have hr : Inhomogeneous.restrictionH2 N.subtype (MulRep K M) x = 0 := by
        apply kE.injective
        rw [map_zero, towerKernelH2Equiv_restriction K E M, hx]
      obtain ⟨y, hy⟩ := (hexact x).1 hr
      refine ⟨qE y, ?_⟩
      rw [towerQuotientH2Equiv_inflation K E M]
      exact hy
    · rintro ⟨a, rfl⟩
      let y := qE.symm a
      have hp :
          transportedH2 (towerQuotientHom K E M)
              (towerInflationCoefficient K E M) a =
            Inhomogeneous.InfRes.inflationH2 N (MulRep K M) y := by
        simpa [qE, N, y] using
          towerQuotientH2Equiv_inflation K E M (qE.symm a)
      have hr : Inhomogeneous.restrictionH2 N.subtype (MulRep K M)
          (Inhomogeneous.InfRes.inflationH2 N (MulRep K M) y) = 0 :=
        (hexact _).2 ⟨y, rfl⟩
      rw [hp, ← towerKernelH2Equiv_restriction K E M, hr, map_zero]

private structure EnvelopeFiniteLocalFieldData
    (K E : Type) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] where
  valuativeRel : ValuativeRel E
  topology : TopologicalSpace E
  localField :
    letI : ValuativeRel E := valuativeRel
    letI : TopologicalSpace E := topology
    IsNonarchimedeanLocalField E
  valuativeExtension :
    letI : ValuativeRel E := valuativeRel
    letI : TopologicalSpace E := topology
    letI : IsNonarchimedeanLocalField E := localField
    ValuativeExtension K E
  continuousSMul :
    letI : ValuativeRel E := valuativeRel
    letI : TopologicalSpace E := topology
    ContinuousSMul K E

private noncomputable def envelopeFiniteLocalFieldData
    (K E : Type) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    EnvelopeFiniteLocalFieldData K E := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  let nE : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NontriviallyNormedField E := nE
  letI : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := E))
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  let tE : TopologicalSpace E := inferInstance
  let vE : ValuativeRel E :=
    ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel E := vE
  letI : (NormedField.valuation (K := E)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : TopologicalSpace E := tE
  letI : Valued E NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation E NNReal).Compatible := by
    rw [show (Valued.v : Valuation E NNReal) = NormedField.valuation from rfl]
    infer_instance
  have htop : IsValuativeTopology E := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using
      (Valued.v : Valuation E NNReal).exists_setOf_restrict_le_iff 0 s
  have hloc : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K E
  have hnontriv : ValuativeRel.IsNontrivial E := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := E))]
    infer_instance
  let hlocal : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hloc
      toIsNontrivial := hnontriv }
  letI : IsNonarchimedeanLocalField E := hlocal
  let hKE : ValuativeExtension K E := by
    constructor
    intro a b
    change NormedField.valuation (algebraMap K E a) ≤
        NormedField.valuation (algebraMap K E b) ↔ a ≤ᵥ b
    rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    change spectralNorm K E (algebraMap K E a) ≤
        spectralNorm K E (algebraMap K E b) ↔ a ≤ᵥ b
    rw [spectralNorm_extends, spectralNorm_extends,
      Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
    exact Valued.toNormedField.norm_le_iff
  letI : ValuativeExtension K E := hKE
  exact ⟨vE, tE, hlocal, hKE, inferInstance⟩

private theorem envelopeValuativeExtension_of_algEquiv
    (K L E : Type) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [FiniteDimensional K L] [FiniteDimensional K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K L] [ValuativeExtension K E]
    (e : L ≃ₐ[K] E) :
    letI : Algebra L E := e.toRingEquiv.toRingHom.toAlgebra
    ValuativeExtension L E := by
  letI : Algebra L E := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
    ringOfIntegers_module_finite K L
  letI : Module.Finite (RingOfIntegers K) (RingOfIntegers E) :=
    ringOfIntegers_module_finite K E
  have hmemL (x : L) :
      x ∈ (ValuativeRel.valuation L).integer ↔ IsIntegral (RingOfIntegers K) x := by
    constructor
    · intro hx
      let ox : RingOfIntegers L := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers K) (RingOfIntegers L) L)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation L)).mem_of_integral
        hx.tower_top
  have hmemE (x : E) :
      x ∈ (ValuativeRel.valuation E).integer ↔ IsIntegral (RingOfIntegers K) x := by
    constructor
    · intro hx
      let ox : RingOfIntegers E := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers K) (RingOfIntegers E) E)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation E)).mem_of_integral
        hx.tower_top
  have hinteger : (ValuativeRel.valuation E).integer.comap (algebraMap L E) =
      (ValuativeRel.valuation L).integer := by
    ext x
    change algebraMap L E x ∈ (ValuativeRel.valuation E).integer ↔
      x ∈ (ValuativeRel.valuation L).integer
    rw [hmemE, hmemL]
    exact isIntegral_algHom_iff (e.toAlgHom.restrictScalars (RingOfIntegers K)) e.injective
  letI : (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation E) :=
    Valuation.HasExtension.ofComapInteger hinteger
  constructor
  intro x y
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E),
    Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation L)
      (ValuativeRel.valuation E),
    ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L)]

private theorem envelopeAlgEquiv_continuous
    (F L E : Type) [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E]
    [FiniteDimensional F L] [FiniteDimensional F E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (e : L ≃ₐ[F] E) (halg : ∀ x : L, algebraMap L E x = e x)
    [ValuativeExtension L E] : Continuous e := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  rw [IsValuativeTopology.mem_nhds_iff'] at hs ⊢
  obtain ⟨γ, hγ⟩ := hs
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ.val
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz : ValuativeRel.valuation L z ≠ 0 := by
    intro hz
    have := congrArg (ValuativeExtension.mapValueGroupWithZero L E) hz
    rw [map_zero, ValuativeExtension.mapValueGroupWithZero_valuation, halg, hy] at this
    exact γ.ne_zero this
  refine ⟨Units.mk0 (ValuativeRel.valuation L z) hz, ?_⟩
  intro w hw
  apply hγ
  change ValuativeRel.valuation E (e w - e x) < γ.val
  rw [← map_sub, ← halg, ← ValuativeExtension.mapValueGroupWithZero_valuation]
  have hmapz : ValuativeExtension.mapValueGroupWithZero L E
      (ValuativeRel.valuation L z) = γ.val := by
    rw [ValuativeExtension.mapValueGroupWithZero_valuation, halg, hy]
  rw [← hmapz]
  exact ValuativeExtension.mapValueGroupWithZero_strictMono hw

set_option maxHeartbeats 800000 in
private noncomputable def envelopeUnramifiedCyclicDataTransport
    (K L E : Type) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [FiniteDimensional K L] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K L] [ValuativeExtension K E]
    [ContinuousSMul K L] [ContinuousSMul K E]
    (D : UnramifiedCyclicExtensionData K L) (e : L ≃ₐ[K] E)
    (hunr : IsUnramifiedLocalExtension K E) :
    UnramifiedCyclicExtensionData K E := by
  letI : Algebra L E := e.toRingEquiv.toRingHom.toAlgebra
  letI : Algebra E L := e.symm.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun x => (e.symm.commutes x).symm
  letI : ValuativeExtension L E := envelopeValuativeExtension_of_algEquiv K L E e
  letI : ValuativeExtension E L := envelopeValuativeExtension_of_algEquiv K E L e.symm
  letI : (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let eO : RingOfIntegers L ≃+* RingOfIntegers E :=
    { toFun := algebraMap (RingOfIntegers L) (RingOfIntegers E)
      invFun := algebraMap (RingOfIntegers E) (RingOfIntegers L)
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x
      right_inv := by
        intro x
        apply Subtype.ext
        exact e.apply_symm_apply x
      map_mul' := map_mul _
      map_add' := map_add _ }
  let er : LocalResidueField L ≃+* LocalResidueField E :=
    IsLocalRing.ResidueField.mapEquiv eO
  let conj : (L ≃ₐ[K] L) ≃* (E ≃ₐ[K] E) :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      invFun := fun τ => e.trans (τ.trans e.symm)
      left_inv := by
        intro σ
        apply AlgEquiv.ext
        intro x
        simp
      right_inv := by
        intro τ
        apply AlgEquiv.ext
        intro x
        simp
      map_mul' := by
        intro σ τ
        apply AlgEquiv.ext
        intro x
        simp [AlgEquiv.mul_apply] }
  have eO_apply (x : RingOfIntegers L) : (eO x : E) = e (x : L) := rfl
  have eO_symm_apply (x : RingOfIntegers E) : (eO.symm x : L) = e.symm (x : E) := rfl
  let frob : E ≃ₐ[K] E := conj D.frobenius
  have hfrob_integral : ∀ x : RingOfIntegers E,
      ∃ y : RingOfIntegers E, (y : E) = frob (x : E) := by
    intro x
    obtain ⟨y, hy⟩ := D.frobenius_preserves_integral (eO.symm x)
    refine ⟨eO y, ?_⟩
    change e (y : L) = e (D.frobenius (e.symm (x : E)))
    rw [hy, eO_symm_apply]
  have hfrob_residue : ∀ (x y : RingOfIntegers E),
      (y : E) = frob (x : E) →
        Ideal.Quotient.mk (LocalMaximalIdeal E) y =
          (Ideal.Quotient.mk (LocalMaximalIdeal E) x) ^ residueCard K := by
    intro x y hxy
    let xL := eO.symm x
    let yL := eO.symm y
    have hxyL : (yL : L) = D.frobenius (xL : L) := by
      calc
        (yL : L) = e.symm (y : E) := eO_symm_apply y
        _ = e.symm (frob (x : E)) := congrArg e.symm hxy
        _ = D.frobenius (e.symm (x : E)) := by simp [frob, conj]
        _ = D.frobenius (xL : L) := congrArg D.frobenius (eO_symm_apply x).symm
    have hD := D.frobenius_residue xL yL hxyL
    have hmapped := congrArg er hD
    change er (IsLocalRing.residue (RingOfIntegers L) (eO.symm y)) =
      er ((IsLocalRing.residue (RingOfIntegers L) (eO.symm x)) ^ residueCard K) at hmapped
    change IsLocalRing.residue (RingOfIntegers E) y =
      (IsLocalRing.residue (RingOfIntegers E) x) ^ residueCard K
    simpa [er] using hmapped
  have hgen : Subgroup.zpowers frob = ⊤ := by
    change Subgroup.zpowers (conj D.frobenius) = ⊤
    calc
      Subgroup.zpowers (conj D.frobenius) =
          Subgroup.map conj.toMonoidHom (Subgroup.zpowers D.frobenius) :=
        (MonoidHom.map_zpowers conj.toMonoidHom D.frobenius).symm
      _ = Subgroup.map conj.toMonoidHom ⊤ := congrArg _ D.frobenius_generates
      _ = ⊤ := Subgroup.map_top_of_surjective conj.toMonoidHom conj.surjective
  have hdegree : Module.finrank K L = Module.finrank K E :=
    e.toLinearEquiv.finrank_eq
  let zchange : Multiplicative (ZMod (Module.finrank K E)) ≃*
      Multiplicative (ZMod (Module.finrank K L)) :=
    AddEquiv.toMultiplicative (ZMod.ringEquivCongr hdegree.symm).toAddEquiv
  exact {
    unramified := hunr
    frobenius := frob
    frobenius_preserves_integral := hfrob_integral
    frobenius_residue := hfrob_residue
    frobenius_generates := hgen
    frobeniusEquiv := zchange.trans (D.frobeniusEquiv.trans conj)
    frobeniusEquiv_apply := by
      intro r
      change conj (D.frobeniusEquiv (zchange (Multiplicative.ofAdd r))) =
        (conj D.frobenius) ^ r.val
      change conj (D.frobeniusEquiv
        (Multiplicative.ofAdd (ZMod.ringEquivCongr hdegree.symm r))) = _
      rw [D.frobeniusEquiv_apply, map_pow, ZMod.ringEquivCongr_val] }

set_option maxHeartbeats 1200000 in
private noncomputable def envelopeUnramifiedCyclicDataBaseTransport
    (F K E M : Type) [Field F] [Field K] [Field E] [Field M]
    [Algebra F K] [Algebra F E] [Algebra F M]
    [Algebra K M] [Algebra E M] [IsScalarTower F K M] [IsScalarTower F E M]
    [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K M] [FiniteDimensional E M]
    [IsGalois K M] [IsGalois E M]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension F K] [ValuativeExtension F E]
    [ValuativeExtension K M] [ValuativeExtension E M]
    [ContinuousSMul F K] [ContinuousSMul F E]
    [ContinuousSMul K M] [ContinuousSMul E M]
    (D : UnramifiedCyclicExtensionData E M) (e : K ≃ₐ[F] E)
    (halg : ∀ x : K, algebraMap E M (e x) = algebraMap K M x) :
    UnramifiedCyclicExtensionData K M := by
  -- The slightly unusual base of `e` is harmless here: only its ring equivalence and the
  -- displayed compatibility with the two embeddings into `M` are used.
  letI : Algebra K E := e.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun x => (halg x).symm
  letI : ValuativeExtension K E := envelopeValuativeExtension_of_algEquiv F K E e
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let eO : RingOfIntegers K ≃+* RingOfIntegers E := by
    letI : Algebra E K := e.symm.toRingEquiv.toRingHom.toAlgebra
    letI : IsScalarTower F E K := IsScalarTower.of_algebraMap_eq fun x =>
      (e.symm.commutes x).symm
    letI : ValuativeExtension E K := envelopeValuativeExtension_of_algEquiv F E K e.symm
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation K) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    exact {
      toFun := algebraMap (RingOfIntegers K) (RingOfIntegers E)
      invFun := algebraMap (RingOfIntegers E) (RingOfIntegers K)
      left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x
      right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x
      map_mul' := map_mul _
      map_add' := map_add _ }
  let er : LocalResidueField K ≃+* LocalResidueField E :=
    IsLocalRing.ResidueField.mapEquiv eO
  have hcard : residueCard K = residueCard E :=
    Nat.card_congr er.toEquiv
  let changeBase : (M ≃ₐ[E] M) ≃* (M ≃ₐ[K] M) :=
    { toFun := fun σ => σ.restrictScalars K
      invFun := fun τ =>
        { τ with
          commutes' := by
            intro y
            obtain ⟨x, rfl⟩ := e.surjective y
            rw [halg]
            exact τ.commutes x }
      left_inv := by intro σ; apply AlgEquiv.ext; intro x; rfl
      right_inv := by intro τ; apply AlgEquiv.ext; intro x; rfl
      map_mul' := by intro σ τ; apply AlgEquiv.ext; intro x; rfl }
  let frob : M ≃ₐ[K] M := changeBase D.frobenius
  have hgen : Subgroup.zpowers frob = ⊤ := by
    change Subgroup.zpowers (changeBase D.frobenius) = ⊤
    calc
      Subgroup.zpowers (changeBase D.frobenius) =
          Subgroup.map changeBase.toMonoidHom (Subgroup.zpowers D.frobenius) :=
        (MonoidHom.map_zpowers changeBase.toMonoidHom D.frobenius).symm
      _ = Subgroup.map changeBase.toMonoidHom ⊤ := congrArg _ D.frobenius_generates
      _ = ⊤ := Subgroup.map_top_of_surjective changeBase.toMonoidHom changeBase.surjective
  have hdegree : Module.finrank K M = Module.finrank E M := by
    apply Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl M)
    ext x
    exact halg x
  have hunr : IsUnramifiedLocalExtension K M := by
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    let kK := LocalResidueField K
    let kE := LocalResidueField E
    let kM := LocalResidueField M
    letI : Algebra kK kM := Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers M))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
    letI : Algebra kE kM := Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers M))
      (IsLocalRing.maximalIdeal (RingOfIntegers E))
    have hresK : Module.finrank kK kM = residueDegree K M :=
      residueFinrank_eq_residueDegree_of_localFields (K := K) (L := M)
    have hresE : Module.finrank kE kM = residueDegree E M :=
      residueFinrank_eq_residueDegree_of_localFields (K := E) (L := M)
    have hresEq : Module.finrank kK kM = Module.finrank kE kM := by
      apply Algebra.finrank_eq_of_equiv_equiv er (RingEquiv.refl kM)
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      change IsLocalRing.residue (RingOfIntegers M)
          (algebraMap (RingOfIntegers E) (RingOfIntegers M) (eO x)) =
        IsLocalRing.residue (RingOfIntegers M)
          (algebraMap (RingOfIntegers K) (RingOfIntegers M) x)
      apply congrArg (IsLocalRing.residue (RingOfIntegers M))
      apply Subtype.ext
      exact halg x
    have hresidue : residueDegree K M = residueDegree E M := by
      rw [← hresK, ← hresE]
      exact hresEq
    have hformulaK := finrank_eq_ramificationIndex_mul_residueDegree K M
    have hformulaE := finrank_eq_ramificationIndex_mul_residueDegree E M
    rw [D.unramified.ramificationIndex_eq_one, one_mul] at hformulaE
    have hmul : ramificationIndex K M * residueDegree K M = residueDegree K M := by
      calc
        _ = Module.finrank K M := hformulaK.symm
        _ = Module.finrank E M := hdegree
        _ = residueDegree E M := hformulaE
        _ = residueDegree K M := hresidue.symm
    have hrespos : 0 < residueDegree K M := by
      rw [← hresK]
      exact Module.finrank_pos
    refine ⟨Nat.mul_right_cancel hrespos ?_⟩
    exact hmul.trans (one_mul _).symm
  let zchange : Multiplicative (ZMod (Module.finrank K M)) ≃*
      Multiplicative (ZMod (Module.finrank E M)) :=
    AddEquiv.toMultiplicative (ZMod.ringEquivCongr hdegree).toAddEquiv
  exact {
    unramified := hunr
    frobenius := frob
    frobenius_preserves_integral := D.frobenius_preserves_integral
    frobenius_residue := by
      intro x y hxy
      rw [hcard]
      exact D.frobenius_residue x y hxy
    frobenius_generates := hgen
    frobeniusEquiv := zchange.trans (D.frobeniusEquiv.trans changeBase)
    frobeniusEquiv_apply := by
      intro r
      change changeBase (D.frobeniusEquiv
        (Multiplicative.ofAdd (ZMod.ringEquivCongr hdegree r))) =
          (changeBase D.frobenius) ^ r.val
      rw [D.frobeniusEquiv_apply, map_pow, ZMod.ringEquivCongr_val] }

private noncomputable def envelopeTowerUnramifiedCyclicData
    (K Ksep : Type) [Field K] [Field Ksep] [Algebra K Ksep]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [IsSepClosure K Ksep] (T : UnramifiedTower K Ksep) (i : ℕ) :
    letI : FiniteDimensional K (T.field i) := T.finiteDimensional i
    letI : IsGalois K (T.field i) := T.isGalois i
    letI : ValuativeRel (T.field i) :=
      unramifiedIntermediateFieldValuativeRel K Ksep (T.field i) (T.unramified i)
    letI : TopologicalSpace (T.field i) :=
      unramifiedIntermediateFieldTopology K Ksep (T.field i) (T.unramified i)
    letI : IsNonarchimedeanLocalField (T.field i) :=
      unramifiedIntermediateFieldLocalField K Ksep (T.field i) (T.unramified i)
    letI : ValuativeExtension K (T.field i) :=
      unramifiedIntermediateFieldValuativeExtension K Ksep (T.field i) (T.unramified i)
    letI : ContinuousSMul K (T.field i) :=
      unramifiedIntermediateFieldContinuousSMul K Ksep (T.field i) (T.unramified i)
    UnramifiedCyclicExtensionData K (T.field i) := by
  letI : FiniteDimensional K (T.field i) := T.finiteDimensional i
  letI : IsGalois K (T.field i) := T.isGalois i
  letI : ValuativeRel (T.field i) :=
    unramifiedIntermediateFieldValuativeRel K Ksep (T.field i) (T.unramified i)
  letI : TopologicalSpace (T.field i) :=
    unramifiedIntermediateFieldTopology K Ksep (T.field i) (T.unramified i)
  letI : IsNonarchimedeanLocalField (T.field i) :=
    unramifiedIntermediateFieldLocalField K Ksep (T.field i) (T.unramified i)
  letI : ValuativeExtension K (T.field i) :=
    unramifiedIntermediateFieldValuativeExtension K Ksep (T.field i) (T.unramified i)
  letI : ContinuousSMul K (T.field i) :=
    unramifiedIntermediateFieldContinuousSMul K Ksep (T.field i) (T.unramified i)
  let n := Module.finrank K (T.field i)
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
  have hmem : ∀ σ : T.field i ≃ₐ[K] T.field i,
      σ ∈ Subgroup.zpowers (T.frobenius i) := by
    intro σ
    rw [T.frobenius_generates i]
    exact Subgroup.mem_top σ
  let ez : Multiplicative (ZMod n) ≃* (T.field i ≃ₐ[K] T.field i) :=
    zmodMulEquivOfGenerator hmem (IsGalois.card_aut_eq_finrank K (T.field i))
  exact {
    unramified := unramifiedIntermediateFieldIsUnramified K Ksep (T.field i) (T.unramified i)
    frobenius := T.frobenius i
    frobenius_preserves_integral := T.frobenius_preserves_integral i
    frobenius_residue := T.frobenius_residue i
    frobenius_generates := T.frobenius_generates i
    frobeniusEquiv := ez
    frobeniusEquiv_apply := by
      intro r
      have h := zmodMulEquivOfGenerator_apply_ofAdd_intCast hmem
        (IsGalois.card_aut_eq_finrank K (T.field i)) (r.val : ℤ)
      rw [zpow_natCast] at h
      simpa [ez, n] using h }

set_option maxHeartbeats 1200000 in
private theorem envelopeUnramifiedCyclicDataExists
    (E C Esep : Type) [Field E] [Field C] [Field Esep]
    [Algebra E C] [Algebra E Esep] [Algebra C Esep] [IsScalarTower E C Esep]
    [FiniteDimensional E C] [IsGalois E C]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel C] [TopologicalSpace C] [IsNonarchimedeanLocalField C]
    [ValuativeExtension E C] [ContinuousSMul E C]
    [IsSepClosure E Esep] (hunr : IsUnramifiedLocalExtension E C) :
    Nonempty (UnramifiedCyclicExtensionData E C) := by
  let T : UnramifiedTower E Esep := unramifiedTower E Esep
  let m := Module.finrank E C
  have hmpos : 0 < m := Module.finrank_pos
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
  let W := T.field (m - 1)
  letI : FiniteDimensional E W := T.finiteDimensional (m - 1)
  letI : IsGalois E W := T.isGalois (m - 1)
  letI : ValuativeRel W :=
    unramifiedIntermediateFieldValuativeRel E Esep W (T.unramified (m - 1))
  letI : TopologicalSpace W :=
    unramifiedIntermediateFieldTopology E Esep W (T.unramified (m - 1))
  letI : IsNonarchimedeanLocalField W :=
    unramifiedIntermediateFieldLocalField E Esep W (T.unramified (m - 1))
  letI : ValuativeExtension E W :=
    unramifiedIntermediateFieldValuativeExtension E Esep W (T.unramified (m - 1))
  letI : ContinuousSMul E W :=
    unramifiedIntermediateFieldContinuousSMul E Esep W (T.unramified (m - 1))
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation C) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let kE := LocalResidueField E
  let kC := LocalResidueField C
  letI : Algebra kE kC :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers C))
      (IsLocalRing.maximalIdeal (RingOfIntegers E))
  have hres : Module.finrank kE kC = residueDegree E C :=
    residueFinrank_eq_residueDegree_of_localFields (K := E) (L := C)
  have hresdeg : residueDegree E C = m := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree E C
    rw [hunr.ramificationIndex_eq_one, one_mul] at hdegree
    exact hdegree.symm
  let j : C →ₐ[E] Esep := IsScalarTower.toAlgHom E C Esep
  have hWle : W ≤ j.fieldRange := by
    apply UnramifiedTower.field_le_fieldRange_of_dvd_residueFinrank
      (K := E) (Ksep := Esep) T C j (m - 1)
    rw [hm, hres, hresdeg]
  letI : FiniteDimensional E j.fieldRange :=
    j.equivFieldRange.toLinearEquiv.finiteDimensional
  have hrange : Module.finrank E j.fieldRange = m := by
    rw [← j.equivFieldRange.toLinearEquiv.finrank_eq]
  have hWrange : W = j.fieldRange :=
    IntermediateField.eq_of_le_of_finrank_eq hWle
      ((T.finrank (m - 1)).trans (hm.trans hrange.symm))
  let eWC : W ≃ₐ[E] C :=
    (IntermediateField.equivOfEq hWrange).trans j.equivFieldRange.symm
  let DW : UnramifiedCyclicExtensionData E W :=
    envelopeTowerUnramifiedCyclicData E Esep T (m - 1)
  exact ⟨envelopeUnramifiedCyclicDataTransport E W C DW eWC hunr⟩

private theorem envelope_zpowers_pow_eq_gcd
    {G : Type} [Group G] [Finite G] (g : G) (a : ℕ) :
    Subgroup.zpowers (g ^ a) = Subgroup.zpowers (g ^ Nat.gcd (Nat.card G) a) := by
  let N := Nat.card G
  let d := Nat.gcd N a
  change Subgroup.zpowers (g ^ a) = Subgroup.zpowers (g ^ d)
  apply le_antisymm
  · apply Subgroup.zpowers_le_of_mem
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right N a
    have heq : g ^ a = (g ^ d) ^ c := by rw [hc, pow_mul]
    rw [heq]
    exact (Subgroup.zpowers (g ^ d)).pow_mem (Subgroup.mem_zpowers (g ^ d)) c
  · apply Subgroup.zpowers_le_of_mem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨Nat.gcdB N a, ?_⟩
    symm
    calc
      g ^ d = g ^ (d : ℤ) := (zpow_natCast g d).symm
      _ = g ^ ((N : ℤ) * Nat.gcdA N a + (a : ℤ) * Nat.gcdB N a) := by
        rw [show (d : ℤ) =
          (N : ℤ) * Nat.gcdA N a + (a : ℤ) * Nat.gcdB N a by
            exact Nat.gcd_eq_gcd_ab N a]
      _ = (g ^ (N : ℤ)) ^ Nat.gcdA N a *
          (g ^ (a : ℤ)) ^ Nat.gcdB N a := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (g ^ a) ^ Nat.gcdB N a := by
        rw [zpow_natCast, pow_card_eq_one', one_zpow, one_mul, zpow_natCast]

private theorem envelope_subgroup_eq_of_isCyclic_of_index_eq
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    (H J : Subgroup G) (hindex : H.index = J.index) : H = J := by
  letI : CommGroup G := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  obtain ⟨a, rfl⟩ := (Subgroup.le_zpowers_iff g H).mp (by rw [hg]; exact le_top)
  obtain ⟨b, rfl⟩ := (Subgroup.le_zpowers_iff g J).mp (by rw [hg]; exact le_top)
  rw [envelope_zpowers_pow_eq_gcd g a, envelope_zpowers_pow_eq_gcd g b]
  congr 2
  -- The index of the range of the power map is the relevant gcd.
  have hrange (m : ℕ) :
      (powMonoidHom m : G →* G).range = Subgroup.zpowers (g ^ m) := by
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    rfl
  have ha := IsCyclic.index_powMonoidHom_range (G := G) a
  have hb := IsCyclic.index_powMonoidHom_range (G := G) b
  rw [hrange a] at ha
  rw [hrange b] at hb
  omega

private theorem envelope_intermediateField_eq_of_cyclic_of_finrank_eq
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (U A B : IntermediateField K Ω)
    [FiniteDimensional K U] [IsGalois K U]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (hcyc : IsCyclic (U ≃ₐ[K] U)) (hA : A ≤ U) (hB : B ≤ U)
    (hrank : Module.finrank K A = Module.finrank K B) : A = B := by
  let A' : IntermediateField K U := A.restrict hA
  let B' : IntermediateField K U := B.restrict hB
  letI : IsCyclic (U ≃ₐ[K] U) := hcyc
  have hAfin : Module.finrank K A' = Module.finrank K A := by
    calc
      Module.finrank K A' = Module.finrank K (IntermediateField.lift A') :=
        (IntermediateField.liftAlgEquiv A').toLinearEquiv.finrank_eq
      _ = Module.finrank K A := by rw [IntermediateField.lift_restrict]
  have hBfin : Module.finrank K B' = Module.finrank K B := by
    calc
      Module.finrank K B' = Module.finrank K (IntermediateField.lift B') :=
        (IntermediateField.liftAlgEquiv B').toLinearEquiv.finrank_eq
      _ = Module.finrank K B := by rw [IntermediateField.lift_restrict]
  have hfix : A'.fixingSubgroup = B'.fixingSubgroup := by
    apply envelope_subgroup_eq_of_isCyclic_of_index_eq
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index,
      ← IntermediateField.finrank_eq_fixingSubgroup_index, hAfin, hBfin, hrank]
  have hAB' : A' = B' := by
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    exact hfix
  calc
    A = IntermediateField.lift A' := (IntermediateField.lift_restrict hA).symm
    _ = IntermediateField.lift B' := congrArg IntermediateField.lift hAB'
    _ = B := IntermediateField.lift_restrict hB

set_option maxHeartbeats 800000 in
private theorem envelope_compositum_relative_finrank
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E U : IntermediateField K Ω)
    [FiniteDimensional K E] [FiniteDimensional K U]
    [IsGalois K E] :
    let C : IntermediateField K Ω := E ⊔ U
    letI : Algebra E C := intermediateFieldInclusionAlgebra K Ω le_sup_left
    letI : Algebra U C := intermediateFieldInclusionAlgebra K Ω le_sup_right
    Module.finrank E C = Module.finrank (E ⊓ U : IntermediateField K Ω) U := by
  let I : IntermediateField K Ω := E ⊓ U
  let C : IntermediateField K Ω := E ⊔ U
  letI : Algebra E C := intermediateFieldInclusionAlgebra K Ω le_sup_left
  letI : Algebra U C := intermediateFieldInclusionAlgebra K Ω le_sup_right
  letI : IsScalarTower K E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K U C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K C := IntermediateField.finiteDimensional_sup E U
  letI : FiniteDimensional E C := FiniteDimensional.right K E C
  let EC : IntermediateField K C := E.restrict le_sup_left
  let UC : IntermediateField K C := U.restrict le_sup_right
  have hIC : I ≤ C := inf_le_left.trans le_sup_left
  let IC : IntermediateField K C := I.restrict hIC
  have hIC_EC : IC ≤ EC := by
    intro x hx
    have hxI : x.1 ∈ I := (IntermediateField.mem_restrict hIC x).1 hx
    exact (IntermediateField.mem_restrict le_sup_left x).2 hxI.1
  have hIC_UC : IC ≤ UC := by
    intro x hx
    have hxI : x.1 ∈ I := (IntermediateField.mem_restrict hIC x).1 hx
    exact (IntermediateField.mem_restrict le_sup_right x).2 hxI.2
  let A : IntermediateField IC C := IntermediateField.extendScalars hIC_EC
  let B : IntermediateField IC C := IntermediateField.extendScalars hIC_UC
  have hECsupUC : EC ⊔ UC = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  have hECinfUC : EC ⊓ UC = IC := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_inf, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_restrict]
  have hsup : A ⊔ B = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [← IntermediateField.restrictScalars_sup,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_top, hECsupUC]
  have hinf : A ⊓ B = ⊥ := by
    apply IntermediateField.restrictScalars_injective K
    rw [← IntermediateField.restrictScalars_inf,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_bot_eq_self, hECinfUC]
  letI : Algebra I E := intermediateFieldInclusionAlgebra K Ω inf_le_left
  letI : IsScalarTower K I E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional I E := FiniteDimensional.right K I E
  have hIE : IsGalois I E := IsGalois.tower_top_of_isGalois K I E
  let eI : I ≃+* IC :=
    { toFun := fun x =>
        let xc : C := ⟨x.1, hIC x.2⟩
        ⟨xc, (IntermediateField.mem_restrict hIC xc).2 x.2⟩
      invFun := fun x =>
        ⟨x.1.1, (IntermediateField.mem_restrict hIC x.1).1 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let eE : E ≃+* A :=
    { toFun := fun x =>
        let xc : C := ⟨x.1, (show E ≤ C from le_sup_left) x.2⟩
        ⟨xc, (IntermediateField.mem_extendScalars hIC_EC).2
          ((IntermediateField.mem_restrict (show E ≤ C from le_sup_left) xc).2 x.2)⟩
      invFun := fun x =>
        ⟨x.1.1, (IntermediateField.mem_restrict (show E ≤ C from le_sup_left) x.1).1
          ((IntermediateField.mem_extendScalars hIC_EC).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let eU : U ≃+* B :=
    { toFun := fun x =>
        let xc : C := ⟨x.1, (show U ≤ C from le_sup_right) x.2⟩
        ⟨xc, (IntermediateField.mem_extendScalars hIC_UC).2
          ((IntermediateField.mem_restrict (show U ≤ C from le_sup_right) xc).2 x.2)⟩
      invFun := fun x =>
        ⟨x.1.1, (IntermediateField.mem_restrict (show U ≤ C from le_sup_right) x.1).1
          ((IntermediateField.mem_extendScalars hIC_UC).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hcompIE : (algebraMap IC A).comp eI.toRingHom =
      eE.toRingHom.comp (algebraMap I E) := by
    ext x
    rfl
  letI : IsGalois IC A := IsGalois.of_equiv_equiv
    (F := I) (E := E) (M := IC) (N := A) (f := eI) (g := eE) (h := hIE) hcompIE
  letI : FiniteDimensional IC C := FiniteDimensional.right K IC C
  letI : FiniteDimensional IC A := by
    apply FiniteDimensional.of_injective A.val.toLinearMap
    exact A.val.injective
  letI : FiniteDimensional IC B := by
    apply FiniteDimensional.of_injective B.val.toLinearMap
    exact B.val.injective
  have hlin : A.LinearDisjoint B :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
  have hdegree : Module.finrank A C = Module.finrank IC B :=
    hlin.finrank_left_eq_finrank hsup
  have hleft : Module.finrank E C = Module.finrank A C := by
    apply Algebra.finrank_eq_of_equiv_equiv eE (RingEquiv.refl C)
    ext x
    rfl
  have hright : Module.finrank I U = Module.finrank IC B := by
    apply Algebra.finrank_eq_of_equiv_equiv eI eU
    ext x
    rfl
  change Module.finrank E C = Module.finrank I U
  exact hleft.trans (hdegree.trans hright.symm)

private theorem envelope_tower_intersection_finrank
    (K L Ksep : Type) [Field K] [Field L] [Field Ksep]
    [Algebra K L] [Algebra K Ksep] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [IsSepClosure K Ksep]
    (T : UnramifiedTower K Ksep) (j : L →ₐ[K] Ksep) :
    Module.finrank K
      (j.fieldRange ⊓ T.field (Module.finrank K L - 1) : IntermediateField K Ksep) =
        residueDegree K L := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kL := LocalResidueField L
  letI : Algebra k kL :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let n := Module.finrank K L
  let f := residueDegree K L
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel Module.finrank_pos
  have hres : Module.finrank k kL = f :=
    residueFinrank_eq_residueDegree_of_localFields (K := K) (L := L)
  have hfpos : 0 < f := by rw [← hres]; exact Module.finrank_pos
  have hf : f - 1 + 1 = f := Nat.sub_add_cancel hfpos
  let E := j.fieldRange
  let U := T.field (n - 1)
  let I : IntermediateField K Ksep := E ⊓ U
  letI : FiniteDimensional K E := j.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K U := T.finiteDimensional (n - 1)
  letI : IsGalois K U := T.isGalois (n - 1)
  letI : FiniteDimensional K I :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (show I ≤ U from inf_le_right)).toLinearMap
      (IntermediateField.inclusion_injective (show I ≤ U from inf_le_right))
  let d := Module.finrank K I
  have hdpos : 0 < d := Module.finrank_pos
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
  have hdn : d ∣ n := by
    have hdiv := IntermediateField.finrank_dvd_of_le_right (show I ≤ U from inf_le_right)
    rw [T.finrank (n - 1), hn] at hdiv
    exact hdiv
  let V := T.field (d - 1)
  letI : FiniteDimensional K V := T.finiteDimensional (d - 1)
  have hVU : V ≤ U := T.le_of_dvd (by simpa [hd, hn] using hdn)
  have hcyc : IsCyclic (U ≃ₐ[K] U) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨T.frobenius (n - 1), T.frobenius_generates (n - 1)⟩
  have hIV : I = V := by
    apply envelope_intermediateField_eq_of_cyclic_of_finrank_eq U I V hcyc inf_le_right hVU
    rw [T.finrank (d - 1), hd]
  have hVleE : V ≤ E := by
    rw [← hIV]
    exact inf_le_left
  have hdf : d ∣ f := by
    have hdiv := UnramifiedTower.degree_dvd_residueFinrank_of_field_le_fieldRange
      (K := K) (Ksep := Ksep) T L j (d - 1) hVleE
    rw [hd, show Module.finrank (LocalResidueField K) (LocalResidueField L) = f from hres] at hdiv
    exact hdiv
  have hfn : f ∣ n := by
    change residueDegree K L ∣ Module.finrank K L
    rw [finrank_eq_ramificationIndex_mul_residueDegree K L]
    exact dvd_mul_left (residueDegree K L) (ramificationIndex K L)
  have hFleE : T.field (f - 1) ≤ E := by
    apply UnramifiedTower.field_le_fieldRange_of_dvd_residueFinrank
      (K := K) (Ksep := Ksep) T L j (f - 1)
    rw [hf, show Module.finrank (LocalResidueField K) (LocalResidueField L) = f from hres]
  have hFleU : T.field (f - 1) ≤ U :=
    T.le_of_dvd (by simpa [hf, hn] using hfn)
  have hFleI : T.field (f - 1) ≤ I := le_inf hFleE hFleU
  have hfd : f ∣ d := by
    have hdiv := IntermediateField.finrank_dvd_of_le_right hFleI
    rw [T.finrank (f - 1), hf] at hdiv
    exact hdiv
  change d = f
  exact Nat.dvd_antisymm hdf hfd


set_option maxHeartbeats 1200000 in
/--
The remaining field-embedding bridge from A05: place `L` and the degree-`[L:K]` tower level in one
separable closure and identify their intersection with the maximal unramified part of `L/K`.
-/
private theorem unramifiedEnvelopeGeometry_exists
    (Ksep : Type) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (T : UnramifiedTower K Ksep) :
    ∃ (U M : Type) (_ : Field U) (_ : Field M)
      (_ : Algebra K U) (_ : Algebra K M) (_ : Algebra L M) (_ : Algebra U M)
      (_ : IsScalarTower K L M) (_ : IsScalarTower K U M)
      (_ : FiniteDimensional K U) (_ : FiniteDimensional K M)
      (_ : FiniteDimensional L M) (_ : FiniteDimensional U M)
      (_ : IsGalois K U) (_ : IsGalois K M) (_ : IsGalois L M)
      (_ : ValuativeRel U) (_ : TopologicalSpace U) (_ : IsNonarchimedeanLocalField U)
      (_ : ValuativeRel M) (_ : TopologicalSpace M) (_ : IsNonarchimedeanLocalField M)
      (_ : ValuativeExtension K U) (_ : ValuativeExtension K M)
      (_ : ValuativeExtension L M) (_ : ValuativeExtension U M)
      (_ : ContinuousSMul K U) (_ : ContinuousSMul K M)
      (_ : ContinuousSMul L M) (_ : ContinuousSMul U M),
      Nonempty (UnramifiedEnvelopeGeometry K L U M) := by
  classical
  let n := Module.finrank K L
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel Module.finrank_pos
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let j : L →ₐ[K] Ksep := IsSepClosed.lift
  let E : IntermediateField K Ksep := j.fieldRange
  let eLE : L ≃ₐ[K] E := j.equivFieldRange
  letI : FiniteDimensional K E := eLE.toLinearEquiv.finiteDimensional
  letI : IsGalois K E := IsGalois.of_algEquiv eLE
  let DE := envelopeFiniteLocalFieldData K E
  letI : ValuativeRel E := DE.valuativeRel
  letI : TopologicalSpace E := DE.topology
  letI : IsNonarchimedeanLocalField E := DE.localField
  letI : ValuativeExtension K E := DE.valuativeExtension
  letI : ContinuousSMul K E := DE.continuousSMul
  letI : Algebra L E := eLE.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq fun x => (eLE.commutes x).symm
  letI : ValuativeExtension L E := envelopeValuativeExtension_of_algEquiv K L E eLE
  let U := T.field (n - 1)
  letI : FiniteDimensional K U := T.finiteDimensional (n - 1)
  letI : IsGalois K U := T.isGalois (n - 1)
  letI : ValuativeRel U :=
    unramifiedIntermediateFieldValuativeRel K Ksep U (T.unramified (n - 1))
  letI : TopologicalSpace U :=
    unramifiedIntermediateFieldTopology K Ksep U (T.unramified (n - 1))
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U (T.unramified (n - 1))
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U (T.unramified (n - 1))
  letI : ContinuousSMul K U :=
    unramifiedIntermediateFieldContinuousSMul K Ksep U (T.unramified (n - 1))
  let C : IntermediateField K Ksep := E ⊔ U
  let DC := (T.compositum_localField E (inferInstance : IsGalois K E) (n - 1)).some
  letI : Algebra E C := intermediateFieldInclusionAlgebra K Ksep le_sup_left
  letI : Algebra U C := intermediateFieldInclusionAlgebra K Ksep le_sup_right
  letI : IsScalarTower K E C := DC.scalarTower_left
  letI : IsScalarTower K U C := DC.scalarTower_right
  letI : FiniteDimensional E C := DC.finiteDimensional_left
  letI : FiniteDimensional U C := DC.finiteDimensional_right
  letI : FiniteDimensional K C := FiniteDimensional.trans K E C
  letI : IsGalois K C := DC.isGalois_base
  letI : IsGalois E C := DC.isGalois_left
  letI : ValuativeRel C := DC.compositumValuativeRel
  letI : TopologicalSpace C := DC.compositumTopology
  letI : IsNonarchimedeanLocalField C := DC.compositumLocalField
  letI : ValuativeExtension K C := DC.valuativeExtension_base
  letI : ValuativeExtension E C := DC.valuativeExtension_left
  letI : ValuativeExtension U C := DC.valuativeExtension_right
  letI : ContinuousSMul K C := DC.continuousSMul_base
  letI : ContinuousSMul E C := DC.continuousSMul_left
  letI : ContinuousSMul U C := DC.continuousSMul_right
  letI : Algebra L C :=
    ((algebraMap E C).comp eLE.toRingEquiv.toRingHom).toAlgebra
  letI : IsScalarTower L E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap K C x = algebraMap E C (algebraMap K E x) :=
        (IsScalarTower.algebraMap_apply K E C x).symm
      _ = algebraMap E C (eLE (algebraMap K L x)) :=
        congrArg (algebraMap E C) (eLE.commutes x).symm
  letI : FiniteDimensional L C := FiniteDimensional.right K L C
  letI : IsGalois L C := IsGalois.tower_top_of_isGalois K L C
  let hLC : ValuativeExtension L C := by
    constructor
    intro x y
    change algebraMap E C (eLE x) ≤ᵥ algebraMap E C (eLE y) ↔ x ≤ᵥ y
    rw [ValuativeExtension.vle_iff_vle (A := E) (B := C)]
    change algebraMap L E x ≤ᵥ algebraMap L E y ↔ x ≤ᵥ y
    exact ValuativeExtension.vle_iff_vle (A := L) (B := E) x y
  letI : ValuativeExtension L C := hLC
  let hcontLE : Continuous eLE :=
    envelopeAlgEquiv_continuous K L E eLE (fun _ => rfl)
  letI : ContinuousSMul L C := by
    constructor
    change Continuous (fun p : L × C => algebraMap E C (eLE p.1) * p.2)
    have hs : Continuous (fun p : E × C => p.1 • p.2) := continuous_smul
    have hp : Continuous (fun p : L × C => (eLE p.1, p.2)) :=
      (hcontLE.comp continuous_fst).prodMk continuous_snd
    simpa only [Algebra.smul_def, Function.comp_def] using hs.comp hp
  let I : IntermediateField K Ksep := E ⊓ U
  letI : Algebra I U := intermediateFieldInclusionAlgebra K Ksep inf_le_right
  letI : IsScalarTower K I U := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Free I U := Module.Free.of_divisionRing I U
  letI : FiniteDimensional I U := FiniteDimensional.right K I U
  have hIC : I ≤ C := inf_le_left.trans le_sup_left
  let IC : IntermediateField K C := I.restrict hIC
  let source : UnramifiedCyclicExtensionData K U :=
    envelopeTowerUnramifiedCyclicData K Ksep T (n - 1)
  have hunrEC : IsUnramifiedLocalExtension E C := DC.unramified_left
  letI : Algebra C Ksep := C.val.toRingHom.toAlgebra
  letI : Algebra E Ksep := E.val.toRingHom.toAlgebra
  let hECT : IsScalarTower E C Ksep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower E C Ksep := hECT
  letI : IsSepClosure E Ksep :=
    { sep_closed := IsSepClosure.sep_closed K
      separable := ⟨fun x =>
        IsSeparable.tower_top E (Algebra.IsSeparable.isSeparable K x)⟩ }
  let upperE : UnramifiedCyclicExtensionData E C :=
    (@envelopeUnramifiedCyclicDataExists E C Ksep
      (inferInstance : Field E) (inferInstance : Field C) (inferInstance : Field Ksep)
      (inferInstance : Algebra E C) (inferInstance : Algebra E Ksep)
      (inferInstance : Algebra C Ksep) hECT
      (inferInstance : FiniteDimensional E C) (inferInstance : IsGalois E C)
      (inferInstance : ValuativeRel E) (inferInstance : TopologicalSpace E)
      (inferInstance : IsNonarchimedeanLocalField E)
      (inferInstance : ValuativeRel C) (inferInstance : TopologicalSpace C)
      (inferInstance : IsNonarchimedeanLocalField C)
      (inferInstance : ValuativeExtension E C) (inferInstance : ContinuousSMul E C)
      (inferInstance : IsSepClosure E Ksep) hunrEC).some
  let upper : UnramifiedCyclicExtensionData L C :=
    envelopeUnramifiedCyclicDataBaseTransport K L E C upperE eLE (fun _ => rfl)
  have hintersection : Module.finrank K I = residueDegree K L :=
    envelope_tower_intersection_finrank K L Ksep T j
  have hsourceDegree : Module.finrank K U = Module.finrank K L := by
    rw [T.finrank (n - 1), hn]
  have hrelative : Module.finrank E C = Module.finrank I U :=
    envelope_compositum_relative_finrank K Ksep E U
  have henvelopeE : Module.finrank E C = ramificationIndex K L := by
    have hfpos : 0 < residueDegree K L := by
      rw [← hintersection]
      exact Module.finrank_pos
    apply Nat.eq_of_mul_eq_mul_right hfpos
    calc
      Module.finrank E C * residueDegree K L =
          Module.finrank I U * Module.finrank K I := by
        rw [hrelative, hintersection]
      _ = Module.finrank K U := by
        rw [mul_comm]
        exact Module.finrank_mul_finrank K I U
      _ = Module.finrank K L := hsourceDegree
      _ = ramificationIndex K L * residueDegree K L :=
        finrank_eq_ramificationIndex_mul_residueDegree K L
  have henvelope : Module.finrank L C = ramificationIndex K L := by
    rw [show Module.finrank L C = Module.finrank E C by
      apply Algebra.finrank_eq_of_equiv_equiv eLE.toRingEquiv (RingEquiv.refl C)
      ext x
      rfl]
    exact henvelopeE
  have hcompositum :
      Algebra.adjoin K (Set.range (algebraMap L C) ∪ Set.range (algebraMap U C)) = ⊤ := by
    let EL : IntermediateField K C := E.restrict le_sup_left
    let UC : IntermediateField K C := U.restrict le_sup_right
    let A := IntermediateField.adjoin K
      (Set.range (algebraMap L C) ∪ Set.range (algebraMap U C))
    have hEL : EL ≤ A := by
      intro x hx
      let xe : E := ⟨x.1,
        (IntermediateField.mem_restrict (show E ≤ C from le_sup_left) x).1 hx⟩
      obtain ⟨l, hl⟩ := eLE.surjective xe
      apply IntermediateField.subset_adjoin K
      left
      refine ⟨l, ?_⟩
      apply Subtype.ext
      change (eLE l : Ksep) = x.1
      simpa [xe] using congrArg Subtype.val hl
    have hUC : UC ≤ A := by
      intro x hx
      let xu : U := ⟨x.1,
        (IntermediateField.mem_restrict (show U ≤ C from le_sup_right) x).1 hx⟩
      apply IntermediateField.subset_adjoin K
      right
      refine ⟨xu, ?_⟩
      apply Subtype.ext
      rfl
    have hsup : EL ⊔ UC = ⊤ := by
      apply IntermediateField.lift_injective C
      rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
        IntermediateField.lift_restrict, IntermediateField.lift_top]
    have hA : A = ⊤ := by
      apply top_unique
      rw [← hsup]
      exact sup_le hEL hUC
    exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)).mp hA
  have hmem : ∀ x : C, x ∈ IC ↔
      (∃ l : L, algebraMap L C l = x) ∧ (∃ u : U, algebraMap U C u = x) := by
    intro x
    constructor
    · intro hx
      have hxI : x.1 ∈ I := (IntermediateField.mem_restrict hIC x).1 hx
      let xe : E := ⟨x.1, hxI.1⟩
      obtain ⟨l, hl⟩ := eLE.surjective xe
      refine ⟨⟨l, ?_⟩, ⟨⟨x.1, hxI.2⟩, ?_⟩⟩
      · apply Subtype.ext
        change (eLE l : Ksep) = x.1
        simpa [xe] using congrArg Subtype.val hl
      · apply Subtype.ext
        rfl
    · rintro ⟨⟨l, hl⟩, ⟨u, hu⟩⟩
      apply (IntermediateField.mem_restrict hIC x).2
      constructor
      · have hval := congrArg Subtype.val hl
        change x.1 ∈ E
        rw [← hval]
        exact (eLE l).2
      · have hval := congrArg Subtype.val hu
        change x.1 ∈ U
        rw [← hval]
        exact u.2
  have hintersectionC : Module.finrank K IC = residueDegree K L := by
    calc
      Module.finrank K IC = Module.finrank K (IntermediateField.lift IC) :=
        (IntermediateField.liftAlgEquiv IC).toLinearEquiv.finrank_eq
      _ = Module.finrank K I := by rw [IntermediateField.lift_restrict]
      _ = residueDegree K L := hintersection
  let G : UnramifiedEnvelopeGeometry K L U C :=
    { source := source
      source_degree := hsourceDegree
      upper := upper
      compositum_eq_top := hcompositum
      intersection := IC
      mem_intersection_iff := hmem
      intersection_degree := hintersectionC
      envelope_degree_over_L := henvelope }
  exact ⟨U, C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Nonempty.intro G⟩

/-- The explicit carry calculation of `lem:psi-restricts-zero` in the geometric envelope. -/
private theorem inflatedCarry_restricts_zero
    (U M : Type) [Field U] [Field M]
    [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
    [IsScalarTower K L M] [IsScalarTower K U M]
    [FiniteDimensional K U] [FiniteDimensional K M]
    [FiniteDimensional L M] [FiniteDimensional U M]
    [IsGalois K U] [IsGalois K M] [IsGalois L M]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension K U] [ValuativeExtension K M]
    [ValuativeExtension L M] [ValuativeExtension U M]
    [ContinuousSMul K U] [ContinuousSMul K M]
    [ContinuousSMul L M] [ContinuousSMul U M]
    (G : UnramifiedEnvelopeGeometry K L U M) (π : Uniformizer K)
    (C : UnramifiedClassData K U G.source π) :
    transportedH2 (towerSubgroupHom K L M) (towerRestrictionCoefficient K L M)
      (transportedH2 (towerQuotientHom K U M) (towerInflationCoefficient K U M)
        C.class) = 0 := by
  letI : ValuativeExtension L L := selfValuativeExtension L
  let target : UnramifiedCyclicExtensionData L L :=
    selfUnramifiedCyclicExtensionData L
  have hsourceDegree : Module.finrank K U =
      Module.finrank L L * Module.finrank K L := by
    simpa using G.source_degree
  have hcommonDegree : Module.finrank L M * Module.finrank K G.intersection =
      Module.finrank K U := by
    rw [G.envelope_degree_over_L, G.intersection_degree, G.source_degree,
      finrank_eq_ramificationIndex_mul_residueDegree K L]
  have htargetDegree : Module.finrank L L ∣ Module.finrank L M := by simp
  obtain ⟨B, hBsource, hBcommon, hBtarget, _⟩ :=
    carryBaseChangeData_exists K L U L M G.source G.upper target
      G.compositum_eq_top G.intersection G.mem_intersection_iff
      G.intersection_degree hsourceDegree hcommonDegree htargetDegree
  let πL := defaultUniformizer L
  obtain ⟨CT⟩ := carryCocycle_isGenerator L L target πL
  let CB : UnramifiedClassData K U B.source π := hBsource.symm ▸ C
  let CTB : UnramifiedClassData L L B.target πL := hBtarget.symm ▸ CT
  have hCBclass : CB.class = C.class :=
    unramifiedClassData_transport_class hBsource.symm π C
  have htargetZero : CTB.class = 0 := by
    apply AddMonoid.addOrderOf_eq_one_iff.mp
    simpa using CTB.order_class
  have hbase := (carryClass_baseChange K L U L M B π πL CB CTB).2
  have hBzeroC : transportedH2 B.sourceGroupHom B.sourceCoefficient C.class = 0 := by
    rw [← hCBclass, hbase, htargetZero, map_zero]
  rw [transportedH2_comp]
  let f := (towerQuotientHom K U M).comp (towerSubgroupHom K L M)
  let c := (Rep.resFunctor (towerSubgroupHom K L M)).map
      (towerInflationCoefficient K U M) ≫ towerRestrictionCoefficient K L M
  have hf : f = B.sourceGroupHom := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U M).injective
    calc
      algebraMap U M (f σ x) = σ (algebraMap U M x) := by
        exact AlgEquiv.restrictNormal_commutes
          ((towerSubgroupHom K L M) σ) U x
      _ = algebraMap U M (B.sourceGroupHom σ x) :=
        (B.sourceGroupHom_apply σ x).symm
  change transportedH2 f c C.class = 0
  have hc : c.hom.toLinearMap = B.sourceCoefficient.hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    change Additive.ofMul (Units.map (algebraMap U M) (Additive.toMul x)) =
      B.sourceCoefficient.hom (Additive.ofMul (Additive.toMul x))
    apply Additive.toMul.injective
    exact (B.sourceCoefficient_apply (Additive.toMul x)).symm
  have hmaps := groupCohomology_map_congr
    (A := MulRep K U) (B := MulRep L M) hf hc 2
  apply (comparisonH2 (MulRep L M)).injective
  simp only [transportedH2, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply]
  rw [hmaps]
  have hbcomp := congrArg (comparisonH2 (MulRep L M)) hBzeroC
  simpa only [transportedH2, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply, map_zero] using hbcomp

/-- Assemble all cohomological envelope fields from geometry, carries, and inf--res. -/
private theorem unramifiedEnvelopeData_of_geometry
    (U M : Type) [Field U] [Field M]
    [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
    [IsScalarTower K L M] [IsScalarTower K U M]
    [FiniteDimensional K U] [FiniteDimensional K M]
    [FiniteDimensional L M] [FiniteDimensional U M]
    [IsGalois K U] [IsGalois K M] [IsGalois L M]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension K U] [ValuativeExtension K M]
    [ValuativeExtension L M] [ValuativeExtension U M]
    [ContinuousSMul K U] [ContinuousSMul K M]
    [ContinuousSMul L M] [ContinuousSMul U M]
    (π : Uniformizer K) (G : UnramifiedEnvelopeGeometry K L U M) :
    Nonempty (UnramifiedEnvelopeData K L U M π) := by
  obtain ⟨C⟩ := carryCocycle_isGenerator K U G.source π
  let sourceQ := towerQuotientHom K U M
  let sourceC := towerInflationCoefficient K U M
  let upperS := towerSubgroupHom K L M
  let upperC := towerRestrictionCoefficient K L M
  let descentQ := towerQuotientHom K L M
  let descentC := towerInflationCoefficient K L M
  let ψ := transportedH2 sourceQ sourceC C.class
  have hsource := towerTransportedH2_infRes K U M
  have hdescent := towerTransportedH2_infRes K L M
  have hzero : transportedH2 upperS upperC ψ = 0 :=
    inflatedCarry_restricts_zero K L U M G π C
  have hrange : ψ ∈ Set.range (transportedH2 descentQ descentC) :=
    (hdescent.2 ψ).1 hzero
  have horder : addOrderOf ψ = Module.finrank K L := by
    change addOrderOf (transportedH2 sourceQ sourceC C.class) = Module.finrank K L
    rw [addOrderOf_injective (transportedH2 sourceQ sourceC) hsource.1 C.class,
      C.order_class, G.source_degree]
  refine ⟨{
    source := G.source
    source_degree := G.source_degree
    upper := G.upper
    compositum_eq_top := G.compositum_eq_top
    intersection := G.intersection
    mem_intersection_iff := G.mem_intersection_iff
    intersection_degree := G.intersection_degree
    envelope_degree_over_L := G.envelope_degree_over_L
    sourceClass := C
    sourceQuotient := sourceQ
    sourceQuotient_apply := ?_
    sourceCoefficient := sourceC
    sourceCoefficient_apply := fun _ => rfl
    psi := ψ
    psi_eq_inflated := rfl
    source_inflation_injective := hsource.1
    psi_order := horder
    upperSubgroup := upperS
    upperSubgroup_apply := fun _ _ => rfl
    upperCoefficient := upperC
    upperCoefficient_apply := fun _ => rfl
    psi_restricts_zero := hzero
    descentQuotient := descentQ
    descentQuotient_apply := ?_
    descentCoefficient := descentC
    descentCoefficient_apply := fun _ => rfl
    descent_injective := hdescent.1
    psi_in_descent_range := hrange
    descent_unique := ?_ }⟩
  · intro σ x
    exact AlgEquiv.restrictNormal_commutes σ U x
  · intro σ x
    exact AlgEquiv.restrictNormal_commutes σ L x
  · intro α β hα hβ
    exact hdescent.1 (hα.trans hβ.symm)

/--
The final aggregate is assembled only after envelope descent and both F09 compatibilities have
been proved.  It is deliberately not used to prove any of those inputs.
-/
private structure FundamentalClassSystem where
  value : ∀ (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L],
      Inhomogeneous.H2 (MulRep K L)
  envelope_exists : ∀ (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (π : Uniformizer K),
    ∃ (U M : Type) (_ : Field U) (_ : Field M)
      (_ : Algebra K U) (_ : Algebra K M) (_ : Algebra L M) (_ : Algebra U M)
      (_ : IsScalarTower K L M) (_ : IsScalarTower K U M)
      (_ : FiniteDimensional K U) (_ : FiniteDimensional K M)
      (_ : FiniteDimensional L M) (_ : FiniteDimensional U M)
      (_ : IsGalois K U) (_ : IsGalois K M) (_ : IsGalois L M)
      (_ : ValuativeRel U) (_ : TopologicalSpace U) (_ : IsNonarchimedeanLocalField U)
      (_ : ValuativeRel M) (_ : TopologicalSpace M) (_ : IsNonarchimedeanLocalField M)
      (_ : ValuativeExtension K U) (_ : ValuativeExtension K M)
      (_ : ValuativeExtension L M) (_ : ValuativeExtension U M)
      (_ : ContinuousSMul K U) (_ : ContinuousSMul K M)
      (_ : ContinuousSMul L M) (_ : ContinuousSMul U M),
      Nonempty (UnramifiedEnvelopeData K L U M π)
  descends : ∀ (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L],
      DescendsFromUnramifiedEnvelopes K L (value K L)
  descends_unique : ∀ (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (α : Inhomogeneous.H2 (MulRep K L)),
      DescendsFromUnramifiedEnvelopes K L α → α = value K L
  order_value : ∀ (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L],
      addOrderOf (value K L) = Module.finrank K L
  inflation : ∀ (K L E : Type)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional K L] [FiniteDimensional L E] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K L] [ValuativeExtension L E] [ValuativeExtension K E]
    [ContinuousSMul K L] [ContinuousSMul L E] [ContinuousSMul K E],
    ∃ (q : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L))
      (c : Rep.res q (MulRep K L) ⟶ MulRep K E),
      (∀ (σ : E ≃ₐ[K] E) (x : L),
        algebraMap L E (q σ x) = σ (algebraMap L E x)) ∧
      (∀ x : Units L,
        Additive.toMul (c.hom (Additive.ofMul x)) = Units.map (algebraMap L E) x) ∧
      transportedH2 q c (value K L) =
        (Module.finrank L E : ℤ) • value K E
  restriction : ∀ (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L] [FiniteDimensional K L]
    [IsGalois K L] [IsGalois E L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K E] [ValuativeExtension E L] [ValuativeExtension K L]
    [ContinuousSMul K E] [ContinuousSMul E L] [ContinuousSMul K L],
    ∃ (s : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))
      (c : Rep.res s (MulRep K L) ⟶ MulRep E L),
      (∀ (σ : L ≃ₐ[E] L) (x : L), s σ x = σ x) ∧
      (∀ x : Units L, c.hom (Additive.ofMul x) = Additive.ofMul x) ∧
      transportedH2 s c (value K L) = value E L

/--
**F08**, Lemma `lem:psi-restricts-zero` and construction preceding
`thm:local-fundamental-class`: an actual unramified source `U=K_n` and compositum `M=L U` carry
all the pinned inflation, restriction, and unique-descent data above.
-/
theorem unramifiedEnvelope_descentData (π : Uniformizer K) :
    ∃ (U M : Type) (_ : Field U) (_ : Field M)
      (_ : Algebra K U) (_ : Algebra K M) (_ : Algebra L M) (_ : Algebra U M)
      (_ : IsScalarTower K L M) (_ : IsScalarTower K U M)
      (_ : FiniteDimensional K U) (_ : FiniteDimensional K M)
      (_ : FiniteDimensional L M) (_ : FiniteDimensional U M)
      (_ : IsGalois K U) (_ : IsGalois K M) (_ : IsGalois L M)
      (_ : ValuativeRel U) (_ : TopologicalSpace U) (_ : IsNonarchimedeanLocalField U)
      (_ : ValuativeRel M) (_ : TopologicalSpace M) (_ : IsNonarchimedeanLocalField M)
      (_ : ValuativeExtension K U) (_ : ValuativeExtension K M)
      (_ : ValuativeExtension L M) (_ : ValuativeExtension U M)
      (_ : ContinuousSMul K U) (_ : ContinuousSMul K M)
      (_ : ContinuousSMul L M) (_ : ContinuousSMul U M),
      Nonempty (UnramifiedEnvelopeData K L U M π) := by
  let Ksep := SeparableClosure K
  let T : UnramifiedTower K Ksep := unramifiedTower K Ksep
  obtain ⟨U, M, fU, fM, aKU, aKM, aLM, aUM, stKLM, stKUM,
      fdKU, fdKM, fdLM, fdUM, galKU, galKM, galLM,
      vU, tU, locU, vM, tM, locM, veKU, veKM, veLM, veUM,
      csKU, csKM, csLM, csUM, hG⟩ := unramifiedEnvelopeGeometry_exists K L Ksep T
  refine ⟨U, M, fU, fM, aKU, aKM, aLM, aUM, stKLM, stKUM,
    fdKU, fdKM, fdLM, fdUM, galKU, galKM, galLM,
    vU, tU, locU, vM, tM, locM, veKU, veKM, veLM, veUM,
    csKU, csKM, csLM, csUM, ?_⟩
  letI : Field U := fU
  letI : Field M := fM
  letI : Algebra K U := aKU
  letI : Algebra K M := aKM
  letI : Algebra L M := aLM
  letI : Algebra U M := aUM
  letI : IsScalarTower K L M := stKLM
  letI : IsScalarTower K U M := stKUM
  letI : FiniteDimensional K U := fdKU
  letI : FiniteDimensional K M := fdKM
  letI : FiniteDimensional L M := fdLM
  letI : FiniteDimensional U M := fdUM
  letI : IsGalois K U := galKU
  letI : IsGalois K M := galKM
  letI : IsGalois L M := galLM
  letI : ValuativeRel U := vU
  letI : TopologicalSpace U := tU
  letI : IsNonarchimedeanLocalField U := locU
  letI : ValuativeRel M := vM
  letI : TopologicalSpace M := tM
  letI : IsNonarchimedeanLocalField M := locM
  letI : ValuativeExtension K U := veKU
  letI : ValuativeExtension K M := veKM
  letI : ValuativeExtension L M := veLM
  letI : ValuativeExtension U M := veUM
  letI : ContinuousSMul K U := csKU
  letI : ContinuousSMul K M := csKM
  letI : ContinuousSMul L M := csLM
  letI : ContinuousSMul U M := csUM
  obtain ⟨G⟩ := hG
  exact unramifiedEnvelopeData_of_geometry K L U M π G

section EnvelopeCoherence

variable (Ksep : Type) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
variable (U₁ M₁ U₂ M₂ : Type)
  [Field U₁] [Field M₁] [Field U₂] [Field M₂]
  [Algebra K U₁] [Algebra K M₁] [Algebra L M₁] [Algebra U₁ M₁]
  [Algebra K U₂] [Algebra K M₂] [Algebra L M₂] [Algebra U₂ M₂]
  [IsScalarTower K L M₁] [IsScalarTower K U₁ M₁]
  [IsScalarTower K L M₂] [IsScalarTower K U₂ M₂]
  [FiniteDimensional K U₁] [FiniteDimensional K M₁]
  [FiniteDimensional L M₁] [FiniteDimensional U₁ M₁]
  [FiniteDimensional K U₂] [FiniteDimensional K M₂]
  [FiniteDimensional L M₂] [FiniteDimensional U₂ M₂]
  [IsGalois K U₁] [IsGalois K M₁] [IsGalois L M₁]
  [IsGalois K U₂] [IsGalois K M₂] [IsGalois L M₂]
  [ValuativeRel U₁] [TopologicalSpace U₁] [IsNonarchimedeanLocalField U₁]
  [ValuativeRel M₁] [TopologicalSpace M₁] [IsNonarchimedeanLocalField M₁]
  [ValuativeRel U₂] [TopologicalSpace U₂] [IsNonarchimedeanLocalField U₂]
  [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
  [ValuativeExtension K U₁] [ValuativeExtension K M₁]
  [ValuativeExtension L M₁] [ValuativeExtension U₁ M₁]
  [ValuativeExtension K U₂] [ValuativeExtension K M₂]
  [ValuativeExtension L M₂] [ValuativeExtension U₂ M₂]
  [ContinuousSMul K U₁] [ContinuousSMul K M₁]
  [ContinuousSMul L M₁] [ContinuousSMul U₁ M₁]
  [ContinuousSMul K U₂] [ContinuousSMul K M₂]
  [ContinuousSMul L M₂] [ContinuousSMul U₂ M₂]

private theorem envelopeSourceRange_eq_tower
    (K U Ksep : Type) [Field K] [Field U] [Field Ksep]
    [Algebra K U] [Algebra K Ksep] [FiniteDimensional K U]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeExtension K U] [IsSepClosure K Ksep]
    (T : UnramifiedTower K Ksep) (D : UnramifiedCyclicExtensionData K U)
    (j : U →ₐ[K] Ksep) :
    j.fieldRange = T.field (Module.finrank K U - 1) := by
  let n := Module.finrank K U
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel Module.finrank_pos
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let kK := LocalResidueField K
  let kU := LocalResidueField U
  letI : Algebra kK kU :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers U))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  have hres : Module.finrank kK kU = residueDegree K U :=
    residueFinrank_eq_residueDegree_of_localFields (K := K) (L := U)
  have hresdeg : residueDegree K U = n := by
    have hdegree := finrank_eq_ramificationIndex_mul_residueDegree K U
    rw [D.unramified.ramificationIndex_eq_one, one_mul] at hdegree
    exact hdegree.symm
  have hle : T.field (n - 1) ≤ j.fieldRange := by
    apply UnramifiedTower.field_le_fieldRange_of_dvd_residueFinrank
      (K := K) (Ksep := Ksep) T U j (n - 1)
    rw [hn, hres, hresdeg]
  letI : FiniteDimensional K j.fieldRange :=
    j.equivFieldRange.toLinearEquiv.finiteDimensional
  apply (IntermediateField.eq_of_le_of_finrank_eq hle ?_).symm
  rw [T.finrank (n - 1), hn]
  exact j.equivFieldRange.toLinearEquiv.finrank_eq

private theorem envelopeRange_eq
    (K L U M Ksep : Type)
    [Field K] [Field L] [Field U] [Field M] [Field Ksep]
    [Algebra K L] [Algebra K U] [Algebra K M] [Algebra L M] [Algebra U M]
    [Algebra K Ksep] [Algebra L Ksep]
    [IsScalarTower K L M] [IsScalarTower K U M] [IsScalarTower K L Ksep]
    (jL : L →ₐ[K] Ksep) (jM : M →ₐ[L] Ksep)
    (hLM : ∀ l : L, (jM.restrictScalars K) (algebraMap L M l) = jL l)
    (hcomp : Algebra.adjoin K
      (Set.range (algebraMap L M) ∪ Set.range (algebraMap U M)) = ⊤)
    (V : IntermediateField K Ksep)
    (hU : ((jM.restrictScalars K).comp
      (IsScalarTower.toAlgHom K U M)).fieldRange = V) :
    (jM.restrictScalars K).fieldRange = jL.fieldRange ⊔ V := by
  let jMK : M →ₐ[K] Ksep := jM.restrictScalars K
  let jU : U →ₐ[K] Ksep := jMK.comp (IsScalarTower.toAlgHom K U M)
  let S : IntermediateField K Ksep := jL.fieldRange ⊔ V
  have hSle : S ≤ jMK.fieldRange := by
    apply sup_le
    · intro x hx
      obtain ⟨l, rfl⟩ := hx
      exact ⟨algebraMap L M l, hLM l⟩
    · rw [← hU]
      intro x hx
      obtain ⟨u, rfl⟩ := hx
      exact ⟨algebraMap U M u, rfl⟩
  have hrangeS : jMK.fieldRange ≤ S := by
    intro x hx
    obtain ⟨m, hm⟩ := hx
    rw [← hm]
    let A : Subalgebra K M := S.toSubalgebra.comap jMK
    have hgen : Algebra.adjoin K
        (Set.range (algebraMap L M) ∪ Set.range (algebraMap U M)) ≤ A := by
      apply Algebra.adjoin_le
      intro y hy
      rcases hy with hy | hy
      · obtain ⟨l, rfl⟩ := hy
        change jMK (algebraMap L M l) ∈ S
        rw [hLM]
        exact (show jL.fieldRange ≤ S from le_sup_left) ⟨l, rfl⟩
      · obtain ⟨u, rfl⟩ := hy
        change jU u ∈ S
        apply (show V ≤ S from le_sup_right)
        rw [← hU]
        exact ⟨u, rfl⟩
    have htop : (⊤ : Subalgebra K M) ≤ A := by
      rw [← hcomp]
      exact hgen
    exact htop (by trivial)
  exact le_antisymm hrangeS hSle

private noncomputable def envelopeConjHom
    (K E₁ E₂ : Type) [Field K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] (e : E₁ ≃ₐ[K] E₂) :
    (E₂ ≃ₐ[K] E₂) →* (E₁ ≃ₐ[K] E₁) where
  toFun σ := e.trans (σ.trans e.symm)
  map_one' := by ext x; simp
  map_mul' σ τ := by ext x; simp [AlgEquiv.mul_apply]

private noncomputable def envelopeConjCoefficient
    (K E₁ E₂ : Type) [Field K] [Field E₁] [Field E₂]
    [Algebra K E₁] [Algebra K E₂] (e : E₁ ≃ₐ[K] E₂) :
    Rep.res (envelopeConjHom K E₁ E₂ e) (MulRep K E₁) ⟶ MulRep K E₂ := by
  let f : Additive (Units E₁) →+ Additive (Units E₂) :=
    (Units.map e.toRingEquiv.toRingHom).toAdditive
  exact Rep.ofHom ⟨f.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    change e ((envelopeConjHom K E₁ E₂ e σ)
      ((Additive.toMul x : Units E₁) : E₁)) =
        σ (e ((Additive.toMul x : Units E₁) : E₁))
    simp [envelopeConjHom]⟩

private noncomputable def envelopeIdCoefficient
    {G : Type} [Group G] (A : Rep ℤ G) :
    Rep.res (MonoidHom.id G) A ⟶ A := 𝟙 A

set_option linter.tacticCheckInstances false in
set_option backward.isDefEq.respectTransparency false in
private theorem envelopeTransportedH2_congr
    {G H : Type} [Group G] [Group H]
    {A : Rep ℤ G} {B : Rep ℤ H}
    {f g : H →* G} (φ : Rep.res f A ⟶ B) (ψ : Rep.res g A ⟶ B)
    (hfg : f = g) (hφ : ∀ x : A.V, φ.hom x = ψ.hom x)
    (x : Inhomogeneous.H2 A) :
    transportedH2 f φ x = transportedH2 g ψ x := by
  subst g
  have hinter : φ.hom = ψ.hom := by
    apply DFunLike.ext _ _
    intro z
    exact hφ z
  have hmaps : φ = ψ := Rep.hom_ext hinter
  cases hmaps
  rfl


private theorem envelopeTransportedH2_id
    {G : Type} [Group G] (A : Rep ℤ G) (x : Inhomogeneous.H2 A) :
    transportedH2 (MonoidHom.id G) (envelopeIdCoefficient A) x = x := by
  apply (comparisonH2 A).injective
  simp [transportedH2, envelopeIdCoefficient]

set_option maxHeartbeats 800000 in
private theorem unramifiedEnvelope_equivs
    (K L Ksep U₁ M₁ U₂ M₂ : Type)
    [Field K] [Field L] [Field Ksep]
    [Field U₁] [Field M₁] [Field U₂] [Field M₂]
    [Algebra K L] [Algebra K Ksep] [IsSepClosure K Ksep]
    [Algebra K U₁] [Algebra K M₁] [Algebra L M₁] [Algebra U₁ M₁]
    [Algebra K U₂] [Algebra K M₂] [Algebra L M₂] [Algebra U₂ M₂]
    [IsScalarTower K L M₁] [IsScalarTower K U₁ M₁]
    [IsScalarTower K L M₂] [IsScalarTower K U₂ M₂]
    [FiniteDimensional K L] [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [IsGalois K L] [IsGalois K U₁] [IsGalois K U₂]
    [IsGalois K M₁] [IsGalois K M₂]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel U₁] [TopologicalSpace U₁] [IsNonarchimedeanLocalField U₁]
    [ValuativeRel U₂] [TopologicalSpace U₂] [IsNonarchimedeanLocalField U₂]
    [ValuativeExtension K U₁] [ValuativeExtension K U₂]
    (T : UnramifiedTower K Ksep)
    (S₁ : UnramifiedCyclicExtensionData K U₁)
    (S₂ : UnramifiedCyclicExtensionData K U₂)
    (hdeg : Module.finrank K U₁ = Module.finrank K U₂)
    (hcomp₁ : Algebra.adjoin K
      (Set.range (algebraMap L M₁) ∪ Set.range (algebraMap U₁ M₁)) = ⊤)
    (hcomp₂ : Algebra.adjoin K
      (Set.range (algebraMap L M₂) ∪ Set.range (algebraMap U₂ M₂)) = ⊤) :
    ∃ (eU : U₁ ≃ₐ[K] U₂) (eM : M₁ ≃ₐ[K] M₂),
      (∀ l : L, eM (algebraMap L M₁ l) = algebraMap L M₂ l) ∧
      (∀ u : U₁, eM (algebraMap U₁ M₁ u) = algebraMap U₂ M₂ (eU u)) := by
  classical
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let jL : L →ₐ[K] Ksep := IsSepClosed.lift
  letI : Algebra L Ksep := jL.toRingHom.toAlgebra
  letI : IsScalarTower K L Ksep :=
    IsScalarTower.of_algebraMap_eq fun x => (jL.commutes x).symm
  letI : IsSepClosure L Ksep :=
    { sep_closed := IsSepClosure.sep_closed K
      separable := ⟨fun x =>
        IsSeparable.tower_top L (Algebra.IsSeparable.isSeparable K x)⟩ }
  letI : Algebra.IsSeparable L M₁ :=
    ⟨fun x => IsSeparable.tower_top L (Algebra.IsSeparable.isSeparable K x)⟩
  letI : Algebra.IsSeparable L M₂ :=
    ⟨fun x => IsSeparable.tower_top L (Algebra.IsSeparable.isSeparable K x)⟩
  let jM₁L : M₁ →ₐ[L] Ksep := IsSepClosed.lift
  let jM₂L : M₂ →ₐ[L] Ksep := IsSepClosed.lift
  let jM₁ : M₁ →ₐ[K] Ksep := jM₁L.restrictScalars K
  let jM₂ : M₂ →ₐ[K] Ksep := jM₂L.restrictScalars K
  let jU₁ : U₁ →ₐ[K] Ksep := jM₁.comp (IsScalarTower.toAlgHom K U₁ M₁)
  let jU₂ : U₂ →ₐ[K] Ksep := jM₂.comp (IsScalarTower.toAlgHom K U₂ M₂)
  let n := Module.finrank K U₁
  have hU₁ : jU₁.fieldRange = T.field (n - 1) :=
    envelopeSourceRange_eq_tower K U₁ Ksep T S₁ jU₁
  have hU₂' : jU₂.fieldRange = T.field (Module.finrank K U₂ - 1) :=
    envelopeSourceRange_eq_tower K U₂ Ksep T S₂ jU₂
  have hU₂ : jU₂.fieldRange = T.field (n - 1) := by simpa [n, hdeg] using hU₂'
  have hM₁ : jM₁.fieldRange = jL.fieldRange ⊔ T.field (n - 1) :=
    envelopeRange_eq K L U₁ M₁ Ksep jL jM₁L
      (fun l => jM₁L.commutes l) hcomp₁ _ hU₁
  have hM₂ : jM₂.fieldRange = jL.fieldRange ⊔ T.field (n - 1) :=
    envelopeRange_eq K L U₂ M₂ Ksep jL jM₂L
      (fun l => jM₂L.commutes l) hcomp₂ _ hU₂
  have hUr : jU₁.fieldRange = jU₂.fieldRange := hU₁.trans hU₂.symm
  have hMr : jM₁.fieldRange = jM₂.fieldRange := hM₁.trans hM₂.symm
  let eU : U₁ ≃ₐ[K] U₂ :=
    jU₁.equivFieldRange.trans
      ((IntermediateField.equivOfEq hUr).trans jU₂.equivFieldRange.symm)
  let eM : M₁ ≃ₐ[K] M₂ :=
    jM₁.equivFieldRange.trans
      ((IntermediateField.equivOfEq hMr).trans jM₂.equivFieldRange.symm)
  have heU (u : U₁) : jU₂ (eU u) = jU₁ u := by
    change jU₂ (jU₂.equivFieldRange.symm
      ((IntermediateField.equivOfEq hUr) (jU₁.equivFieldRange u))) = jU₁ u
    exact congrArg Subtype.val (jU₂.equivFieldRange.apply_symm_apply
      ((IntermediateField.equivOfEq hUr) (jU₁.equivFieldRange u)))
  have heM (m : M₁) : jM₂ (eM m) = jM₁ m := by
    change jM₂ (jM₂.equivFieldRange.symm
      ((IntermediateField.equivOfEq hMr) (jM₁.equivFieldRange m))) = jM₁ m
    exact congrArg Subtype.val (jM₂.equivFieldRange.apply_symm_apply
      ((IntermediateField.equivOfEq hMr) (jM₁.equivFieldRange m)))
  refine ⟨eU, eM, ?_, ?_⟩
  · intro l
    apply jM₂.injective
    calc
      jM₂ (eM (algebraMap L M₁ l)) = jM₁ (algebraMap L M₁ l) := heM _
      _ = jL l := jM₁L.commutes l
      _ = jM₂ (algebraMap L M₂ l) := (jM₂L.commutes l).symm
  · intro u
    apply jM₂.injective
    calc
      jM₂ (eM (algebraMap U₁ M₁ u)) = jM₁ (algebraMap U₁ M₁ u) := heM _
      _ = jU₁ u := rfl
      _ = jU₂ (eU u) := (heU u).symm
      _ = jM₂ (algebraMap U₂ M₂ (eU u)) := rfl


set_option maxHeartbeats 800000 in
set_option linter.tacticCheckInstances false in
set_option backward.isDefEq.respectTransparency false in
private theorem unramifiedSourceClass_transport
    (K U₁ U₂ : Type) [Field K] [Field U₁] [Field U₂]
    [Algebra K U₁] [Algebra K U₂]
    [FiniteDimensional K U₁] [FiniteDimensional K U₂]
    [IsGalois K U₁] [IsGalois K U₂]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel U₁] [TopologicalSpace U₁] [IsNonarchimedeanLocalField U₁]
    [ValuativeRel U₂] [TopologicalSpace U₂] [IsNonarchimedeanLocalField U₂]
    [ValuativeExtension K U₁] [ValuativeExtension K U₂]
    [ContinuousSMul K U₁] [ContinuousSMul K U₂]
    (S₁ : UnramifiedCyclicExtensionData K U₁)
    (S₂ : UnramifiedCyclicExtensionData K U₂)
    (π₁ π₂ : Uniformizer K)
    (C₁ : UnramifiedClassData K U₁ S₁ π₁)
    (C₂ : UnramifiedClassData K U₂ S₂ π₂)
    (e : U₁ ≃ₐ[K] U₂)
    (hdeg : Module.finrank K U₁ = Module.finrank K U₂)
    [Algebra U₁ U₂] [IsScalarTower K U₁ U₂]
    [FiniteDimensional U₁ U₂] [ValuativeExtension U₁ U₂]
    [ContinuousSMul U₁ U₂]
    (he : ∀ x : U₁, algebraMap U₁ U₂ x = e x) :
    transportedH2 (envelopeConjHom K U₁ U₂ e)
      (envelopeConjCoefficient K U₁ U₂ e) C₁.class = C₂.class := by
  letI : ValuativeExtension K K := ⟨fun _ _ => Iff.rfl⟩
  letI : ContinuousSMul K K := inferInstance
  letI : ValuativeExtension U₂ U₂ := ⟨fun _ _ => Iff.rfl⟩
  letI : ContinuousSMul U₂ U₂ := inferInstance
  letI : IsScalarTower K K U₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K U₂ U₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hresKK : residueDegree K K = 1 := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree K K
    rw [Module.finrank_self, self_ramificationIndex K, one_mul] at h
    exact h.symm
  have hcomp : Algebra.adjoin K
      (Set.range (algebraMap K U₂) ∪ Set.range (algebraMap U₁ U₂)) = ⊤ := by
    apply top_unique
    intro x _
    apply Algebra.subset_adjoin
    right
    obtain ⟨u, rfl⟩ := e.surjective x
    exact ⟨u, he u⟩
  let I : IntermediateField K U₂ := ⊥
  have hmem : ∀ x : U₂, x ∈ I ↔
      (∃ k : K, algebraMap K U₂ k = x) ∧
        (∃ u : U₁, algebraMap U₁ U₂ u = x) := by
    intro x
    constructor
    · intro hx
      rw [show I = ⊥ from rfl, IntermediateField.mem_bot] at hx
      obtain ⟨k, rfl⟩ := hx
      refine ⟨⟨k, rfl⟩, ?_⟩
      obtain ⟨u, hu⟩ := e.surjective (algebraMap K U₂ k)
      exact ⟨u, he u |>.trans hu⟩
    · rintro ⟨⟨k, hk⟩, -⟩
      rw [show I = ⊥ from rfl, IntermediateField.mem_bot]
      exact ⟨k, hk⟩
  have hI : Module.finrank K I = residueDegree K K := by
    rw [hresKK]
    simp [I]
  have hsource : Module.finrank K U₁ = Module.finrank K U₂ * Module.finrank K K := by
    simpa using hdeg
  have hcommon : Module.finrank K U₂ * Module.finrank K I = Module.finrank K U₁ := by
    rw [show Module.finrank K I = 1 by simp [I], mul_one]
    exact hdeg.symm
  obtain ⟨B, hBS, -, hBT, -⟩ := carryBaseChangeData_exists K K U₁ U₂ U₂
    S₁ S₂ S₂ hcomp I hmem hI hsource hcommon (dvd_refl _)
  let C₁B : UnramifiedClassData K U₁ B.source π₁ := hBS.symm ▸ C₁
  let C₂B : UnramifiedClassData K U₂ B.target π₂ := hBT.symm ▸ C₂
  have hclasses := (carryClass_baseChange K K U₁ U₂ U₂ B π₁ π₂ C₁B C₂B).2
  have hsourceHom : B.sourceGroupHom = envelopeConjHom K U₁ U₂ e := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply e.injective
    rw [← he]
    calc
      algebraMap U₁ U₂ (B.sourceGroupHom σ x) =
          σ (algebraMap U₁ U₂ x) := B.sourceGroupHom_apply σ x
      _ = σ (e x) := congrArg σ (he x)
      _ = e (envelopeConjHom K U₁ U₂ e σ x) := by simp [envelopeConjHom]
  have htargetHom : B.targetGroupHom = MonoidHom.id (U₂ ≃ₐ[K] U₂) := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    exact B.targetGroupHom_apply σ x
  have hsourceCoeff : ∀ x : (MulRep K U₁).V,
      B.sourceCoefficient.hom x = (envelopeConjCoefficient K U₁ U₂ e).hom x := by
    intro x
    change Additive (Units U₁) at x
    apply (Additive.toMul : Additive (Units U₂) ≃ Units U₂).injective
    have hx := B.sourceCoefficient_apply (Additive.toMul x : Units U₁)
    change (Additive.toMul (B.sourceCoefficient.hom
      (Additive.ofMul (Additive.toMul x : Units U₁))) : Units U₂) =
        Units.map (algebraMap U₁ U₂) (Additive.toMul x : Units U₁) at hx
    have hx' : (Additive.toMul (B.sourceCoefficient.hom x) : Units U₂) =
        Units.map (algebraMap U₁ U₂) (Additive.toMul x : Units U₁) := by
      exact hx
    calc
      (Additive.toMul (B.sourceCoefficient.hom x) : Units U₂) =
          Units.map (algebraMap U₁ U₂) (Additive.toMul x : Units U₁) := hx'
      _ = Units.map e.toRingEquiv.toRingHom (Additive.toMul x : Units U₁) := by
        apply Units.ext
        exact he _
      _ = (Additive.toMul ((envelopeConjCoefficient K U₁ U₂ e).hom x) : Units U₂) := rfl
  have htargetCoeff : ∀ x : (MulRep K U₂).V,
      B.targetCoefficient.hom x = (envelopeIdCoefficient (MulRep K U₂)).hom x := by
    intro x
    change Additive (Units U₂) at x
    apply (Additive.toMul : Additive (Units U₂) ≃ Units U₂).injective
    have hx := B.targetCoefficient_apply (Additive.toMul x : Units U₂)
    change (Additive.toMul (B.targetCoefficient.hom
      (Additive.ofMul (Additive.toMul x : Units U₂))) : Units U₂) =
        (Additive.toMul x : Units U₂) at hx
    have hx' : (Additive.toMul (B.targetCoefficient.hom x) : Units U₂) =
        (Additive.toMul x : Units U₂) := by
      exact hx
    calc
      (Additive.toMul (B.targetCoefficient.hom x) : Units U₂) =
          (Additive.toMul x : Units U₂) := hx'
      _ = (Additive.toMul ((envelopeIdCoefficient (MulRep K U₂)).hom x) : Units U₂) := rfl
  have hleft := envelopeTransportedH2_congr B.sourceCoefficient
    (envelopeConjCoefficient K U₁ U₂ e) hsourceHom hsourceCoeff C₁B.class
  have hright := envelopeTransportedH2_congr B.targetCoefficient
    (envelopeIdCoefficient (MulRep K U₂)) htargetHom htargetCoeff C₂B.class
  have hC₁ : C₁B.class = C₁.class := by cases hBS; rfl
  have hC₂ : C₂B.class = C₂.class := by cases hBT; rfl
  rw [hleft, hright, envelopeTransportedH2_id, hC₁, hC₂] at hclasses
  exact hclasses


set_option maxHeartbeats 2000000 in
set_option linter.tacticCheckInstances false in
set_option backward.isDefEq.respectTransparency false in
private theorem unramifiedEnvelopePreimage_eq_of_equivs
    (K L U₁ M₁ U₂ M₂ : Type)
    [Field K] [Field L] [Field U₁] [Field M₁] [Field U₂] [Field M₂]
    [Algebra K L]
    [Algebra K U₁] [Algebra K M₁] [Algebra L M₁] [Algebra U₁ M₁]
    [Algebra K U₂] [Algebra K M₂] [Algebra L M₂] [Algebra U₂ M₂]
    [IsScalarTower K L M₁] [IsScalarTower K U₁ M₁]
    [IsScalarTower K L M₂] [IsScalarTower K U₂ M₂]
    [FiniteDimensional K L]
    [FiniteDimensional K U₁] [FiniteDimensional K M₁]
    [FiniteDimensional L M₁] [FiniteDimensional U₁ M₁]
    [FiniteDimensional K U₂] [FiniteDimensional K M₂]
    [FiniteDimensional L M₂] [FiniteDimensional U₂ M₂]
    [IsGalois K L]
    [IsGalois K U₁] [IsGalois K M₁] [IsGalois L M₁]
    [IsGalois K U₂] [IsGalois K M₂] [IsGalois L M₂]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel U₁] [TopologicalSpace U₁] [IsNonarchimedeanLocalField U₁]
    [ValuativeRel M₁] [TopologicalSpace M₁] [IsNonarchimedeanLocalField M₁]
    [ValuativeRel U₂] [TopologicalSpace U₂] [IsNonarchimedeanLocalField U₂]
    [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [ValuativeExtension K L]
    [ValuativeExtension K U₁] [ValuativeExtension K M₁]
    [ValuativeExtension L M₁] [ValuativeExtension U₁ M₁]
    [ValuativeExtension K U₂] [ValuativeExtension K M₂]
    [ValuativeExtension L M₂] [ValuativeExtension U₂ M₂]
    [ContinuousSMul K L]
    [ContinuousSMul K U₁] [ContinuousSMul K M₁]
    [ContinuousSMul L M₁] [ContinuousSMul U₁ M₁]
    [ContinuousSMul K U₂] [ContinuousSMul K M₂]
    [ContinuousSMul L M₂] [ContinuousSMul U₂ M₂]
    (π₁ π₂ : Uniformizer K)
    (D₁ : UnramifiedEnvelopeData K L U₁ M₁ π₁)
    (D₂ : UnramifiedEnvelopeData K L U₂ M₂ π₂)
    (eU : U₁ ≃ₐ[K] U₂) (eM : M₁ ≃ₐ[K] M₂)
    (hLM : ∀ l : L, eM (algebraMap L M₁ l) = algebraMap L M₂ l)
    (hUM : ∀ u : U₁, eM (algebraMap U₁ M₁ u) = algebraMap U₂ M₂ (eU u))
    [Algebra U₁ U₂] [IsScalarTower K U₁ U₂]
    [FiniteDimensional U₁ U₂] [ValuativeExtension U₁ U₂]
    [ContinuousSMul U₁ U₂]
    (heU : ∀ x : U₁, algebraMap U₁ U₂ x = eU x) :
    unramifiedEnvelopePreimage K L U₁ M₁ π₁ D₁ =
      unramifiedEnvelopePreimage K L U₂ M₂ π₂ D₂ := by
  let qU := envelopeConjHom K U₁ U₂ eU
  let cU := envelopeConjCoefficient K U₁ U₂ eU
  let qM := envelopeConjHom K M₁ M₂ eM
  let cM := envelopeConjCoefficient K M₁ M₂ eM
  have hsourceClass : transportedH2 qU cU D₁.sourceClass.class =
      D₂.sourceClass.class :=
    unramifiedSourceClass_transport K U₁ U₂ D₁.source D₂.source π₁ π₂
      D₁.sourceClass D₂.sourceClass eU
      (D₁.source_degree.trans D₂.source_degree.symm) heU
  have hsourceGroup : D₁.sourceQuotient.comp qM = qU.comp D₂.sourceQuotient := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply eU.injective
    apply (algebraMap U₂ M₂).injective
    calc
      algebraMap U₂ M₂ (eU (D₁.sourceQuotient (qM σ) x)) =
          eM (algebraMap U₁ M₁ (D₁.sourceQuotient (qM σ) x)) := (hUM _).symm
      _ = eM ((qM σ) (algebraMap U₁ M₁ x)) :=
        congrArg eM (D₁.sourceQuotient_apply (qM σ) x)
      _ = σ (eM (algebraMap U₁ M₁ x)) := by simp [qM, envelopeConjHom]
      _ = σ (algebraMap U₂ M₂ (eU x)) := congrArg σ (hUM x)
      _ = algebraMap U₂ M₂ (D₂.sourceQuotient σ (eU x)) :=
        (D₂.sourceQuotient_apply σ (eU x)).symm
      _ = algebraMap U₂ M₂ (eU (qU (D₂.sourceQuotient σ) x)) := by
        congr 1
        simp [qU, envelopeConjHom]
  let sourceLeft := (Rep.resFunctor qM).map D₁.sourceCoefficient ≫ cM
  let sourceRight := (Rep.resFunctor D₂.sourceQuotient).map cU ≫ D₂.sourceCoefficient
  have hsourceCoeff : ∀ x : (MulRep K U₁).V,
      sourceLeft.hom x = sourceRight.hom x := by
    intro x
    change Additive (Units U₁) at x
    apply (Additive.toMul : Additive (Units M₂) ≃ Units M₂).injective
    have hx₁ := D₁.sourceCoefficient_apply (Additive.toMul x)
    have hx₂ := D₂.sourceCoefficient_apply
      (Units.map eU.toRingEquiv.toRingHom.toMonoidHom (Additive.toMul x))
    change Additive.toMul (D₁.sourceCoefficient.hom
      (Additive.ofMul (Additive.toMul x))) =
        Units.map (algebraMap U₁ M₁) (Additive.toMul x) at hx₁
    change Additive.toMul (D₂.sourceCoefficient.hom
      (Additive.ofMul (Units.map eU.toRingEquiv.toRingHom.toMonoidHom
        (Additive.toMul x)))) =
        Units.map (algebraMap U₂ M₂)
          (Units.map eU.toRingEquiv.toRingHom.toMonoidHom (Additive.toMul x)) at hx₂
    change Units.map eM.toRingEquiv.toRingHom.toMonoidHom
        (Additive.toMul (D₁.sourceCoefficient.hom x)) =
      Additive.toMul (D₂.sourceCoefficient.hom
        (cU.hom x))
    have hx₁' : Additive.toMul (D₁.sourceCoefficient.hom x) =
        Units.map (algebraMap U₁ M₁) (Additive.toMul x) := by
      exact hx₁
    have hx₂' : Additive.toMul (D₂.sourceCoefficient.hom (cU.hom x)) =
        Units.map (algebraMap U₂ M₂)
          (Units.map eU.toRingEquiv.toRingHom.toMonoidHom (Additive.toMul x)) := by
      exact hx₂
    calc
      Units.map eM.toRingEquiv.toRingHom.toMonoidHom
          (Additive.toMul (D₁.sourceCoefficient.hom x)) =
        Units.map eM.toRingEquiv.toRingHom.toMonoidHom
          (Units.map (algebraMap U₁ M₁) (Additive.toMul x)) := congrArg _ hx₁'
      _ = Units.map (algebraMap U₂ M₂)
          (Units.map eU.toRingEquiv.toRingHom.toMonoidHom (Additive.toMul x)) := by
        apply Units.ext
        exact hUM _
      _ = Additive.toMul (D₂.sourceCoefficient.hom (cU.hom x)) := hx₂'.symm
  have hsourceMaps : transportedH2 (D₁.sourceQuotient.comp qM) sourceLeft
      D₁.sourceClass.class =
      transportedH2 (qU.comp D₂.sourceQuotient) sourceRight
        D₁.sourceClass.class :=
    envelopeTransportedH2_congr
      (f := D₁.sourceQuotient.comp qM)
      (g := qU.comp D₂.sourceQuotient)
      sourceLeft sourceRight hsourceGroup hsourceCoeff _
  have hpsi : transportedH2 qM cM D₁.psi = D₂.psi := by
    rw [D₁.psi_eq_inflated, D₂.psi_eq_inflated, transportedH2_comp]
    rw [hsourceMaps]
    rw [← transportedH2_comp, hsourceClass]
  have hdescentGroup : D₁.descentQuotient.comp qM = D₂.descentQuotient := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M₂).injective
    calc
      algebraMap L M₂ (D₁.descentQuotient (qM σ) x) =
          eM (algebraMap L M₁ (D₁.descentQuotient (qM σ) x)) := (hLM _).symm
      _ = eM ((qM σ) (algebraMap L M₁ x)) :=
        congrArg eM (D₁.descentQuotient_apply (qM σ) x)
      _ = σ (eM (algebraMap L M₁ x)) := by simp [qM, envelopeConjHom]
      _ = σ (algebraMap L M₂ x) := congrArg σ (hLM x)
      _ = algebraMap L M₂ (D₂.descentQuotient σ x) :=
        (D₂.descentQuotient_apply σ x).symm
  let descentLeft := (Rep.resFunctor qM).map D₁.descentCoefficient ≫ cM
  have hdescentCoeff : ∀ x : (MulRep K L).V,
      descentLeft.hom x = D₂.descentCoefficient.hom x := by
    intro x
    change Additive (Units L) at x
    apply (Additive.toMul : Additive (Units M₂) ≃ Units M₂).injective
    have hx₁ := D₁.descentCoefficient_apply (Additive.toMul x)
    have hx₂ := D₂.descentCoefficient_apply (Additive.toMul x)
    change Additive.toMul (D₁.descentCoefficient.hom
      (Additive.ofMul (Additive.toMul x))) =
        Units.map (algebraMap L M₁) (Additive.toMul x) at hx₁
    change Additive.toMul (D₂.descentCoefficient.hom
      (Additive.ofMul (Additive.toMul x))) =
        Units.map (algebraMap L M₂) (Additive.toMul x) at hx₂
    change Units.map eM.toRingEquiv.toRingHom.toMonoidHom
        (Additive.toMul (D₁.descentCoefficient.hom x)) =
      Additive.toMul (D₂.descentCoefficient.hom x)
    have hx₁' : Additive.toMul (D₁.descentCoefficient.hom x) =
        Units.map (algebraMap L M₁) (Additive.toMul x) := by
      exact hx₁
    have hx₂' : Additive.toMul (D₂.descentCoefficient.hom x) =
        Units.map (algebraMap L M₂) (Additive.toMul x) := by
      exact hx₂
    calc
      Units.map eM.toRingEquiv.toRingHom.toMonoidHom
          (Additive.toMul (D₁.descentCoefficient.hom x)) =
        Units.map eM.toRingEquiv.toRingHom.toMonoidHom
          (Units.map (algebraMap L M₁) (Additive.toMul x)) := congrArg _ hx₁'
      _ = Units.map (algebraMap L M₂) (Additive.toMul x) := by
        apply Units.ext
        exact hLM _
      _ = Additive.toMul (D₂.descentCoefficient.hom x) := hx₂'.symm
  let α₁ := unramifiedEnvelopePreimage K L U₁ M₁ π₁ D₁
  let α₂ := unramifiedEnvelopePreimage K L U₂ M₂ π₂ D₂
  have hα₁ : transportedH2 D₂.descentQuotient D₂.descentCoefficient α₁ = D₂.psi := by
    rw [← hpsi, ← unramifiedEnvelopePreimage_spec K L U₁ M₁ π₁ D₁,
      transportedH2_comp]
    exact (envelopeTransportedH2_congr
      (f := D₁.descentQuotient.comp qM) (g := D₂.descentQuotient)
      descentLeft D₂.descentCoefficient hdescentGroup hdescentCoeff α₁).symm
  exact D₂.descent_unique α₁ α₂ hα₁
    (unramifiedEnvelopePreimage_spec K L U₂ M₂ π₂ D₂)



/--
**F08**, Theorem `thm:local-fundamental-class` (envelope coherence): the unique preimages
obtained from two pinned unramified envelopes agree.  The comparison is made in a common
refinement supplied by `T`: Frobenius compatibility along divisibility inclusions, compatible
local-field structures on composita, and the gcd intersection formula are exactly the tower
interfaces used to identify the two refined inflated carry classes.
-/
theorem unramifiedEnvelopePreimage_commonRefinement
    (T : UnramifiedTower K Ksep)
    (π₁ π₂ : Uniformizer K)
    (D₁ : UnramifiedEnvelopeData K L U₁ M₁ π₁)
    (D₂ : UnramifiedEnvelopeData K L U₂ M₂ π₂) :
    unramifiedEnvelopePreimage K L U₁ M₁ π₁ D₁ =
      unramifiedEnvelopePreimage K L U₂ M₂ π₂ D₂ := by
  obtain ⟨eU, eM, hLM, hUM⟩ :=
    unramifiedEnvelope_equivs K L Ksep U₁ M₁ U₂ M₂ T
      D₁.source D₂.source (D₁.source_degree.trans D₂.source_degree.symm)
      D₁.compositum_eq_top D₂.compositum_eq_top
  letI : Algebra U₁ U₂ := eU.toRingEquiv.toRingHom.toAlgebra
  letI : IsScalarTower K U₁ U₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (eU.commutes x).symm
  letI : FiniteDimensional U₁ U₂ := by
    apply FiniteDimensional.of_surjective (Algebra.linearMap U₁ U₂)
    intro y
    obtain ⟨x, hx⟩ := eU.surjective y
    refine ⟨x, ?_⟩
    change eU x = y
    exact hx
  letI : ValuativeExtension U₁ U₂ :=
    envelopeValuativeExtension_of_algEquiv K U₁ U₂ eU
  let hcont : Continuous eU :=
    envelopeAlgEquiv_continuous K U₁ U₂ eU (fun _ => rfl)
  letI : ContinuousSMul U₁ U₂ := by
    constructor
    change Continuous (fun p : U₁ × U₂ => eU p.1 * p.2)
    exact (hcont.comp continuous_fst).mul continuous_snd
  exact unramifiedEnvelopePreimage_eq_of_equivs K L U₁ M₁ U₂ M₂
    π₁ π₂ D₁ D₂ eU eM hLM hUM (fun _ => rfl)

/-- Envelope coherence and the unique-preimage specification give descent from every envelope. -/
theorem unramifiedEnvelopePreimage_descends
    (T : UnramifiedTower K Ksep)
    (π₁ : Uniformizer K)
    (D₁ : UnramifiedEnvelopeData K L U₁ M₁ π₁) :
    DescendsFromUnramifiedEnvelopes K L
      (unramifiedEnvelopePreimage K L U₁ M₁ π₁ D₁) := by
  intro π₂ U₂' M₂'
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D₂
  rw [unramifiedEnvelopePreimage_commonRefinement
    (K := K) (L := L) (Ksep := Ksep) (U₁ := U₁) (M₁ := M₁)
    (U₂ := U₂') (M₂ := M₂') T π₁ π₂ D₁ D₂]
  exact unramifiedEnvelopePreimage_spec K L U₂' M₂' π₂ D₂

end EnvelopeCoherence

/--
**F08**, Theorem `thm:local-fundamental-class`: a normalized local fundamental class, pinned
both by unramified descent and by its normalized
invariant.  Exact order and generation rule out the old trivial-model bundles.
-/
structure LocalFundamentalClass where
  /-- The concrete normalized `H²` class. -/
  «class» : Inhomogeneous.H2 (MulRep K L)
  /-- It is the unique descent of the inflated unramified carry class. -/
  descends : DescendsFromUnramifiedEnvelopes K L «class»
  /-- Its exact order is the extension degree. -/
  order_class : addOrderOf «class» = Module.finrank K L
  /-- It generates all of `H²`. -/
  generates : ∀ β : Inhomogeneous.H2 (MulRep K L), ∃ n : ℤ, n • «class» = β
  /-- The normalized invariant. -/
  invariant : Inhomogeneous.H2 (MulRep K L) ≃+ ZMod (Module.finrank K L)
  /-- Defining normalization of the invariant. -/
  invariant_class : invariant «class» = 1
  /-- The normalization uniquely determines the invariant map. -/
  invariant_unique : ∀ e : Inhomogeneous.H2 (MulRep K L) ≃+
      ZMod (Module.finrank K L), e «class» = 1 → e = invariant

private theorem localFundamentalClass_of_descent
    (α : Inhomogeneous.H2 (MulRep K L))
    (hdesc : DescendsFromUnramifiedEnvelopes K L α)
    (horder : addOrderOf α = Module.finrank K L)
    (hfinite : Finite (Inhomogeneous.H2 (MulRep K L)))
    (hcard : Nat.card (Inhomogeneous.H2 (MulRep K L)) ≤ Module.finrank K L) :
    Nonempty (LocalFundamentalClass K L) := by
  letI : Finite (Inhomogeneous.H2 (MulRep K L)) := hfinite
  obtain ⟨hgen, e, he, heuniq⟩ :=
    normalizedGeneratorPackage (Module.finrank K L) α horder hcard
  exact ⟨{
    «class» := α
    descends := hdesc
    order_class := horder
    generates := hgen
    invariant := e
    invariant_class := he
    invariant_unique := heuniq }⟩

/--
**F08**, Theorem `thm:local-fundamental-class`: unique descent from the unramified envelope,
together with the finite upper bound, produces the normalized generator of order `[L:K]`.
-/
theorem localFundamentalClass_exists : Nonempty (LocalFundamentalClass K L) := by
  classical
  let π := defaultUniformizer K
  obtain ⟨U, M, fU, fM, aKU, aKM, aLM, aUM, stKLM, stKUM,
      fdKU, fdKM, fdLM, fdUM, galKU, galKM, galLM,
      vU, tU, locU, vM, tM, locM, veKU, veKM, veLM, veUM,
      csKU, csKM, csLM, csUM, hD⟩ :=
    unramifiedEnvelope_descentData K L π
  letI : Field U := fU
  letI : Field M := fM
  letI : Algebra K U := aKU
  letI : Algebra K M := aKM
  letI : Algebra L M := aLM
  letI : Algebra U M := aUM
  letI : IsScalarTower K L M := stKLM
  letI : IsScalarTower K U M := stKUM
  letI : FiniteDimensional K U := fdKU
  letI : FiniteDimensional K M := fdKM
  letI : FiniteDimensional L M := fdLM
  letI : FiniteDimensional U M := fdUM
  letI : IsGalois K U := galKU
  letI : IsGalois K M := galKM
  letI : IsGalois L M := galLM
  letI : ValuativeRel U := vU
  letI : TopologicalSpace U := tU
  letI : IsNonarchimedeanLocalField U := locU
  letI : ValuativeRel M := vM
  letI : TopologicalSpace M := tM
  letI : IsNonarchimedeanLocalField M := locM
  letI : ValuativeExtension K U := veKU
  letI : ValuativeExtension K M := veKM
  letI : ValuativeExtension L M := veLM
  letI : ValuativeExtension U M := veUM
  letI : ContinuousSMul K U := csKU
  letI : ContinuousSMul K M := csKM
  letI : ContinuousSMul L M := csLM
  letI : ContinuousSMul U M := csUM
  obtain ⟨D⟩ := hD
  let Ksep := SeparableClosure K
  let T : UnramifiedTower K Ksep := unramifiedTower K Ksep
  let α := unramifiedEnvelopePreimage K L U M π D
  have hdesc : DescendsFromUnramifiedEnvelopes K L α :=
    unramifiedEnvelopePreimage_descends
      (K := K) (L := L) (Ksep := Ksep) (U₁ := U) (M₁ := M) T π D
  have horder : addOrderOf α = Module.finrank K L :=
    envelope_preimage_order K L U M π D α
      (unramifiedEnvelopePreimage_spec K L U M π D)
  exact localFundamentalClass_of_descent K L α hdesc horder
    (local_H2_finite K L) (local_H2_upperBound K L).2

/-- **F08**, Theorem `thm:local-fundamental-class`: the canonical class. -/
noncomputable def fundamentalClass : LocalFundamentalClass K L :=
  (localFundamentalClass_exists K L).some

/-- **F08**, Theorem `thm:local-fundamental-class`: the underlying concrete class. -/
abbrev fundamentalClassValue : Inhomogeneous.H2 (MulRep K L) :=
  (fundamentalClass K L).class

/--
**F08**, Theorem `thm:local-fundamental-class`: Hilbert 90 supplies the degree-one vanishing in
the same local-field instance bundle.
-/
theorem localFundamentalClass_H1 :
    Subsingleton (Inhomogeneous.H1 (MulRep K L)) :=
  hilbert90_mulRep_inhomogeneous K L

/--
**F08**, Definition `def:normalized-invariant`: the normalized invariant identifies local `H²`
with the
cyclic group of order `[L:K]` and sends the fundamental class to `1`.
-/
theorem normalizedInvariant_exists :
    ∃ e : Inhomogeneous.H2 (MulRep K L) ≃+ ZMod (Module.finrank K L),
      e (fundamentalClassValue K L) = 1 := by
  exact ⟨(fundamentalClass K L).invariant,
    (fundamentalClass K L).invariant_class⟩

/-- **F08**, Definition `def:normalized-invariant`: the canonical invariant. -/
noncomputable def normalizedInvariant :
    Inhomogeneous.H2 (MulRep K L) ≃+ ZMod (Module.finrank K L) :=
  (fundamentalClass K L).invariant

/-- The selected valuations on a finite scalar tower are compatible on the middle field. -/
private theorem envelopeValuativeExtension_of_tower
    (F A B : Type) [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B] [Algebra A B]
    [IsScalarTower F A B]
    [FiniteDimensional F A] [FiniteDimensional F B]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeExtension F A] [ValuativeExtension F B] :
    ValuativeExtension A B := by
  letI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation A) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation B) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Module.Finite (RingOfIntegers F) (RingOfIntegers A) :=
    ringOfIntegers_module_finite F A
  letI : Module.Finite (RingOfIntegers F) (RingOfIntegers B) :=
    ringOfIntegers_module_finite F B
  have hmemA (x : A) :
      x ∈ (ValuativeRel.valuation A).integer ↔ IsIntegral (RingOfIntegers F) x := by
    constructor
    · intro hx
      let ox : RingOfIntegers A := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers F) (RingOfIntegers A) A)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation A)).mem_of_integral
        hx.tower_top
  have hmemB (x : B) :
      x ∈ (ValuativeRel.valuation B).integer ↔ IsIntegral (RingOfIntegers F) x := by
    constructor
    · intro hx
      let ox : RingOfIntegers B := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers F) (RingOfIntegers B) B)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation B)).mem_of_integral
        hx.tower_top
  have hinteger : (ValuativeRel.valuation B).integer.comap (algebraMap A B) =
      (ValuativeRel.valuation A).integer := by
    ext x
    change algebraMap A B x ∈ (ValuativeRel.valuation B).integer ↔
      x ∈ (ValuativeRel.valuation A).integer
    rw [hmemB, hmemA]
    exact isIntegral_algHom_iff
      ((IsScalarTower.toAlgHom F A B).restrictScalars (RingOfIntegers F))
      (algebraMap A B).injective
  letI : (ValuativeRel.valuation A).HasExtension (ValuativeRel.valuation B) :=
    Valuation.HasExtension.ofComapInteger hinteger
  constructor
  intro x y
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B),
    Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation A)
      (ValuativeRel.valuation B),
    ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A)]

set_option maxHeartbeats 2000000 in
/-- Put two nested envelopes in one separable closure, respecting both displayed composita. -/
private theorem unramifiedEnvelope_inflation_embeddings
    (F A B Fsep U₁ M₁ U₂ M₂ : Type)
    [Field F] [Field A] [Field B] [Field Fsep]
    [Field U₁] [Field M₁] [Field U₂] [Field M₂]
    [Algebra F A] [Algebra F B] [Algebra A B] [IsScalarTower F A B]
    [Algebra F Fsep] [IsSepClosure F Fsep]
    [Algebra F U₁] [Algebra F M₁] [Algebra A M₁] [Algebra U₁ M₁]
    [Algebra F U₂] [Algebra F M₂] [Algebra B M₂] [Algebra U₂ M₂]
    [IsScalarTower F A M₁] [IsScalarTower F U₁ M₁]
    [IsScalarTower F B M₂] [IsScalarTower F U₂ M₂]
    [FiniteDimensional F A] [FiniteDimensional F B]
    [FiniteDimensional F U₁] [FiniteDimensional F M₁]
    [FiniteDimensional A M₁] [FiniteDimensional U₁ M₁]
    [FiniteDimensional F U₂] [FiniteDimensional F M₂]
    [FiniteDimensional B M₂] [FiniteDimensional U₂ M₂]
    [IsGalois F A] [IsGalois F B]
    [IsGalois F U₁] [IsGalois F M₁] [IsGalois A M₁]
    [IsGalois F U₂] [IsGalois F M₂] [IsGalois B M₂]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]
    [ValuativeRel B] [TopologicalSpace B] [IsNonarchimedeanLocalField B]
    [ValuativeRel U₁] [TopologicalSpace U₁] [IsNonarchimedeanLocalField U₁]
    [ValuativeRel M₁] [TopologicalSpace M₁] [IsNonarchimedeanLocalField M₁]
    [ValuativeRel U₂] [TopologicalSpace U₂] [IsNonarchimedeanLocalField U₂]
    [ValuativeRel M₂] [TopologicalSpace M₂] [IsNonarchimedeanLocalField M₂]
    [ValuativeExtension F A] [ValuativeExtension F B]
    [ValuativeExtension F U₁] [ValuativeExtension F M₁]
    [ValuativeExtension A M₁] [ValuativeExtension U₁ M₁]
    [ValuativeExtension F U₂] [ValuativeExtension F M₂]
    [ValuativeExtension B M₂] [ValuativeExtension U₂ M₂]
    [ContinuousSMul F A] [ContinuousSMul F B]
    [ContinuousSMul F U₁] [ContinuousSMul F M₁]
    [ContinuousSMul A M₁] [ContinuousSMul U₁ M₁]
    [ContinuousSMul F U₂] [ContinuousSMul F M₂]
    [ContinuousSMul B M₂] [ContinuousSMul U₂ M₂]
    (T : UnramifiedTower F Fsep)
    {π : Uniformizer F}
    (D₁ : UnramifiedEnvelopeData F A U₁ M₁ π)
    (D₂ : UnramifiedEnvelopeData F B U₂ M₂ π) :
    ∃ (eU : U₁ →ₐ[F] U₂) (eM : M₁ →ₐ[F] M₂),
      (∀ a : A, eM (algebraMap A M₁ a) =
        algebraMap B M₂ (algebraMap A B a)) ∧
      (∀ u : U₁, eM (algebraMap U₁ M₁ u) = algebraMap U₂ M₂ (eU u)) := by
  classical
  letI : IsSepClosed Fsep := IsSepClosure.sep_closed F
  let jB : B →ₐ[F] Fsep := IsSepClosed.lift
  let jA : A →ₐ[F] Fsep := jB.comp (IsScalarTower.toAlgHom F A B)
  letI : Algebra A Fsep := jA.toRingHom.toAlgebra
  letI : IsScalarTower F A Fsep :=
    IsScalarTower.of_algebraMap_eq fun x => (jA.commutes x).symm
  letI : IsSepClosure A Fsep :=
    { sep_closed := IsSepClosure.sep_closed F
      separable := ⟨fun x =>
        IsSeparable.tower_top A (Algebra.IsSeparable.isSeparable F x)⟩ }
  letI : Algebra.IsSeparable A M₁ :=
    ⟨fun x => IsSeparable.tower_top A (Algebra.IsSeparable.isSeparable F x)⟩
  let jM₁A : M₁ →ₐ[A] Fsep := IsSepClosed.lift
  let jM₁ : M₁ →ₐ[F] Fsep := jM₁A.restrictScalars F
  let jU₁ : U₁ →ₐ[F] Fsep :=
    jM₁.comp (IsScalarTower.toAlgHom F U₁ M₁)
  letI : Algebra B Fsep := jB.toRingHom.toAlgebra
  letI : IsScalarTower F B Fsep :=
    IsScalarTower.of_algebraMap_eq fun x => (jB.commutes x).symm
  letI : IsSepClosure B Fsep :=
    { sep_closed := IsSepClosure.sep_closed F
      separable := ⟨fun x =>
        IsSeparable.tower_top B (Algebra.IsSeparable.isSeparable F x)⟩ }
  letI : Algebra.IsSeparable B M₂ :=
    ⟨fun x => IsSeparable.tower_top B (Algebra.IsSeparable.isSeparable F x)⟩
  let jM₂B : M₂ →ₐ[B] Fsep := IsSepClosed.lift
  let jM₂ : M₂ →ₐ[F] Fsep := jM₂B.restrictScalars F
  let jU₂ : U₂ →ₐ[F] Fsep :=
    jM₂.comp (IsScalarTower.toAlgHom F U₂ M₂)
  let n₁ := Module.finrank F U₁
  let n₂ := Module.finrank F U₂
  have hn₁ : n₁ - 1 + 1 = n₁ := Nat.sub_add_cancel Module.finrank_pos
  have hn₂ : n₂ - 1 + 1 = n₂ := Nat.sub_add_cancel Module.finrank_pos
  have hU₁ : jU₁.fieldRange = T.field (n₁ - 1) :=
    envelopeSourceRange_eq_tower F U₁ Fsep T D₁.source jU₁
  have hU₂ : jU₂.fieldRange = T.field (n₂ - 1) :=
    envelopeSourceRange_eq_tower F U₂ Fsep T D₂.source jU₂
  have hn_div : n₁ ∣ n₂ := by
    change Module.finrank F U₁ ∣ Module.finrank F U₂
    rw [D₁.source_degree, D₂.source_degree]
    exact ⟨Module.finrank A B, (Module.finrank_mul_finrank F A B).symm⟩
  have hlevel : T.field (n₁ - 1) ≤ T.field (n₂ - 1) := by
    apply T.le_of_dvd
    simpa only [hn₁, hn₂] using hn_div
  have hUr : jU₁.fieldRange ≤ jU₂.fieldRange := by
    rw [hU₁, hU₂]
    exact hlevel
  have hM₁ : jM₁.fieldRange = jA.fieldRange ⊔ T.field (n₁ - 1) :=
    envelopeRange_eq F A U₁ M₁ Fsep jA jM₁A
      (fun a => jM₁A.commutes a) D₁.compositum_eq_top _ hU₁
  have hM₂ : jM₂.fieldRange = jB.fieldRange ⊔ T.field (n₂ - 1) :=
    envelopeRange_eq F B U₂ M₂ Fsep jB jM₂B
      (fun b => jM₂B.commutes b) D₂.compositum_eq_top _ hU₂
  have hAB : jA.fieldRange ≤ jB.fieldRange := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨algebraMap A B a, rfl⟩
  have hMr : jM₁.fieldRange ≤ jM₂.fieldRange := by
    rw [hM₁, hM₂]
    exact sup_le (hAB.trans le_sup_left) (hlevel.trans le_sup_right)
  let eU : U₁ →ₐ[F] U₂ :=
    (jU₂.equivFieldRange.symm.toAlgHom).comp
      ((IntermediateField.inclusion hUr).comp jU₁.equivFieldRange.toAlgHom)
  let eM : M₁ →ₐ[F] M₂ :=
    (jM₂.equivFieldRange.symm.toAlgHom).comp
      ((IntermediateField.inclusion hMr).comp jM₁.equivFieldRange.toAlgHom)
  have heU (u : U₁) : jU₂ (eU u) = jU₁ u := by
    change jU₂ (jU₂.equivFieldRange.symm
      ((IntermediateField.inclusion hUr) (jU₁.equivFieldRange u))) = jU₁ u
    exact congrArg Subtype.val (jU₂.equivFieldRange.apply_symm_apply
      ((IntermediateField.inclusion hUr) (jU₁.equivFieldRange u)))
  have heM (m : M₁) : jM₂ (eM m) = jM₁ m := by
    change jM₂ (jM₂.equivFieldRange.symm
      ((IntermediateField.inclusion hMr) (jM₁.equivFieldRange m))) = jM₁ m
    exact congrArg Subtype.val (jM₂.equivFieldRange.apply_symm_apply
      ((IntermediateField.inclusion hMr) (jM₁.equivFieldRange m)))
  refine ⟨eU, eM, ?_, ?_⟩
  · intro a
    apply jM₂.injective
    calc
      jM₂ (eM (algebraMap A M₁ a)) = jM₁ (algebraMap A M₁ a) := heM _
      _ = jA a := jM₁A.commutes a
      _ = jB (algebraMap A B a) := rfl
      _ = jM₂ (algebraMap B M₂ (algebraMap A B a)) :=
        (jM₂B.commutes _).symm
  · intro u
    apply jM₂.injective
    calc
      jM₂ (eM (algebraMap U₁ M₁ u)) = jM₁ (algebraMap U₁ M₁ u) := heM _
      _ = jU₁ u := rfl
      _ = jU₂ (eU u) := (heU u).symm
      _ = jM₂ (algebraMap U₂ M₂ (eU u)) := rfl

set_option maxHeartbeats 10000000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
/-- Inflation to the top of a commuting field diamond is independent of the middle field. -/
private theorem towerInflation_diamond
    (F A B C D : Type) [Field F] [Field A] [Field B] [Field C] [Field D]
    [Algebra F A] [Algebra F B] [Algebra F C] [Algebra F D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower F A B] [IsScalarTower F A C] [IsScalarTower F A D]
    [IsScalarTower F B D] [IsScalarTower F C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    [FiniteDimensional F A] [FiniteDimensional F B]
    [FiniteDimensional F C] [FiniteDimensional F D]
    [IsGalois F A] [IsGalois F B] [IsGalois F C] [IsGalois F D]
    (x : Inhomogeneous.H2 (MulRep F A)) :
    transportedH2 (towerQuotientHom F B D) (towerInflationCoefficient F B D)
        (transportedH2 (towerQuotientHom F A B)
          (towerInflationCoefficient F A B) x) =
      transportedH2 (towerQuotientHom F C D) (towerInflationCoefficient F C D)
        (transportedH2 (towerQuotientHom F A C)
          (towerInflationCoefficient F A C) x) := by
  let qB := (towerQuotientHom F A B).comp (towerQuotientHom F B D)
  let cB := (Rep.resFunctor (towerQuotientHom F B D)).map
      (towerInflationCoefficient F A B) ≫ towerInflationCoefficient F B D
  let qC := (towerQuotientHom F A C).comp (towerQuotientHom F C D)
  let cC := (Rep.resFunctor (towerQuotientHom F C D)).map
      (towerInflationCoefficient F A C) ≫ towerInflationCoefficient F C D
  have hq : qB = qC := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro a
    apply (algebraMap A D).injective
    calc
      algebraMap A D (qB σ a) =
          algebraMap B D (algebraMap A B (qB σ a)) :=
        IsScalarTower.algebraMap_apply A B D _
      _ = algebraMap B D
          ((towerQuotientHom F B D σ) (algebraMap A B a)) := by
        apply congrArg (algebraMap B D)
        exact AlgEquiv.restrictNormal_commutes (towerQuotientHom F B D σ) A a
      _ = σ (algebraMap B D (algebraMap A B a)) :=
        AlgEquiv.restrictNormal_commutes σ B _
      _ = σ (algebraMap A D a) := by
        rw [IsScalarTower.algebraMap_apply A B D]
      _ = σ (algebraMap C D (algebraMap A C a)) := by
        rw [IsScalarTower.algebraMap_apply A C D]
      _ = algebraMap C D
          ((towerQuotientHom F C D σ) (algebraMap A C a)) :=
        (AlgEquiv.restrictNormal_commutes σ C _).symm
      _ = algebraMap C D (algebraMap A C (qC σ a)) := by
        apply congrArg (algebraMap C D)
        exact (AlgEquiv.restrictNormal_commutes (towerQuotientHom F C D σ) A a).symm
      _ = algebraMap A D (qC σ a) :=
        (IsScalarTower.algebraMap_apply A C D _).symm
  have hc : ∀ a : (MulRep F A).V, cB.hom a = cC.hom a := by
    intro a
    apply Additive.toMul.injective
    apply Units.ext
    change algebraMap B D (algebraMap A B ((Additive.toMul a : Units A) : A)) =
      algebraMap C D (algebraMap A C ((Additive.toMul a : Units A) : A))
    rw [← IsScalarTower.algebraMap_apply A B D,
      ← IsScalarTower.algebraMap_apply A C D]
  have hB :
      transportedH2 (towerQuotientHom F B D) (towerInflationCoefficient F B D)
          (transportedH2 (towerQuotientHom F A B)
            (towerInflationCoefficient F A B) x) =
        transportedH2 qB cB x :=
    transportedH2_comp (towerQuotientHom F A B) (towerQuotientHom F B D)
      (towerInflationCoefficient F A B) (towerInflationCoefficient F B D) x
  have hC :
      transportedH2 (towerQuotientHom F C D) (towerInflationCoefficient F C D)
          (transportedH2 (towerQuotientHom F A C)
            (towerInflationCoefficient F A C) x) =
        transportedH2 qC cC x :=
    transportedH2_comp (towerQuotientHom F A C) (towerQuotientHom F C D)
      (towerInflationCoefficient F A C) (towerInflationCoefficient F C D) x
  have hcLinear : cB.hom.toLinearMap = cC.hom.toLinearMap := by
    apply LinearMap.ext
    exact hc
  have hmaps := groupCohomology_map_congr
    (A := MulRep F A) (B := MulRep F D) hq hcLinear 2
  have hmiddle : transportedH2 qB cB x = transportedH2 qC cC x := by
    apply (comparisonH2 (MulRep F D)).injective
    simp only [transportedH2, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
      Function.comp_apply, AddEquiv.apply_symm_apply]
    rw [hmaps]
  exact hB.trans (hmiddle.trans hC.symm)

section Inflation

variable (E : Type) [Field E] [Algebra K E] [Algebra L E]
  [IsScalarTower K L E]
  [FiniteDimensional L E] [FiniteDimensional K E] [IsGalois K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension L E] [ValuativeExtension K E]
  [ContinuousSMul L E] [ContinuousSMul K E]

/-- **F09**, Proposition `prop:fundamental-inflation`: its actual quotient/coefficient maps. -/
structure FundamentalInflationData where
  /-- Restriction `Gal(E/K) → Gal(L/K)`. -/
  quotientHom : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L)
  /-- It is literal restriction on `L`. -/
  quotientHom_apply : ∀ (σ : E ≃ₐ[K] E) (x : L),
    algebraMap L E (quotientHom σ x) = σ (algebraMap L E x)
  /-- Coefficient inclusion `Lˣ → Eˣ`. -/
  coefficient : Rep.res quotientHom (MulRep K L) ⟶ MulRep K E
  /-- It is the actual field embedding. -/
  coefficient_apply : ∀ x : Units L,
    Additive.toMul (coefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap L E) x

private noncomputable def actualFundamentalInflationData :
    FundamentalInflationData K L E := by
  let q : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let i : Additive (Units L) →+ Additive (Units E) :=
    (Units.map (algebraMap L E)).toAdditive
  let c : Rep.res q (MulRep K L) ⟶ MulRep K E :=
    Rep.ofHom ⟨i.toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      refine Units.ext ?_
      exact AlgEquiv.restrictNormal_commutes σ L
        ((Additive.toMul x : Units L) : L)⟩
  exact {
    quotientHom := q
    quotientHom_apply := by
      intro σ x
      exact AlgEquiv.restrictNormal_commutes σ L x
    coefficient := c
    coefficient_apply := by
      intro x
      rfl }

set_option maxHeartbeats 5000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual F09 inflation square after refining both descents to the degree-`[E:K]` envelope. -/
private theorem actualFundamentalInflation_square :
    transportedH2 (actualFundamentalInflationData K L E).quotientHom
        (actualFundamentalInflationData K L E).coefficient (fundamentalClassValue K L) =
      (Module.finrank L E : ℤ) • fundamentalClassValue K E := by
  classical
  let π := defaultUniformizer K
  obtain ⟨U₁, M₁, fU₁, fM₁, aKU₁, aKM₁, aLM₁, aU₁M₁, stKLM₁, stKU₁M₁,
      fdKU₁, fdKM₁, fdLM₁, fdU₁M₁, galKU₁, galKM₁, galLM₁,
      vU₁, tU₁, locU₁, vM₁, tM₁, locM₁, veKU₁, veKM₁, veLM₁, veU₁M₁,
      csKU₁, csKM₁, csLM₁, csU₁M₁, hD₁⟩ :=
    unramifiedEnvelope_descentData K L π
  letI : Field U₁ := fU₁
  letI : Field M₁ := fM₁
  letI : Algebra K U₁ := aKU₁
  letI : Algebra K M₁ := aKM₁
  letI : Algebra L M₁ := aLM₁
  letI : Algebra U₁ M₁ := aU₁M₁
  letI : IsScalarTower K L M₁ := stKLM₁
  letI : IsScalarTower K U₁ M₁ := stKU₁M₁
  letI : FiniteDimensional K U₁ := fdKU₁
  letI : FiniteDimensional K M₁ := fdKM₁
  letI : FiniteDimensional L M₁ := fdLM₁
  letI : FiniteDimensional U₁ M₁ := fdU₁M₁
  letI : IsGalois K U₁ := galKU₁
  letI : IsGalois K M₁ := galKM₁
  letI : IsGalois L M₁ := galLM₁
  letI : ValuativeRel U₁ := vU₁
  letI : TopologicalSpace U₁ := tU₁
  letI : IsNonarchimedeanLocalField U₁ := locU₁
  letI : ValuativeRel M₁ := vM₁
  letI : TopologicalSpace M₁ := tM₁
  letI : IsNonarchimedeanLocalField M₁ := locM₁
  letI : ValuativeExtension K U₁ := veKU₁
  letI : ValuativeExtension K M₁ := veKM₁
  letI : ValuativeExtension L M₁ := veLM₁
  letI : ValuativeExtension U₁ M₁ := veU₁M₁
  letI : ContinuousSMul K U₁ := csKU₁
  letI : ContinuousSMul K M₁ := csKM₁
  letI : ContinuousSMul L M₁ := csLM₁
  letI : ContinuousSMul U₁ M₁ := csU₁M₁
  obtain ⟨D₁⟩ := hD₁
  obtain ⟨U₂, M₂, fU₂, fM₂, aKU₂, aKM₂, aEM₂, aU₂M₂, stKEM₂, stKU₂M₂,
      fdKU₂, fdKM₂, fdEM₂, fdU₂M₂, galKU₂, galKM₂, galEM₂,
      vU₂, tU₂, locU₂, vM₂, tM₂, locM₂, veKU₂, veKM₂, veEM₂, veU₂M₂,
      csKU₂, csKM₂, csEM₂, csU₂M₂, hD₂⟩ :=
    unramifiedEnvelope_descentData K E π
  letI : Field U₂ := fU₂
  letI : Field M₂ := fM₂
  letI : Algebra K U₂ := aKU₂
  letI : Algebra K M₂ := aKM₂
  letI : Algebra E M₂ := aEM₂
  letI : Algebra U₂ M₂ := aU₂M₂
  letI : IsScalarTower K E M₂ := stKEM₂
  letI : IsScalarTower K U₂ M₂ := stKU₂M₂
  letI : FiniteDimensional K U₂ := fdKU₂
  letI : FiniteDimensional K M₂ := fdKM₂
  letI : FiniteDimensional E M₂ := fdEM₂
  letI : FiniteDimensional U₂ M₂ := fdU₂M₂
  letI : IsGalois K U₂ := galKU₂
  letI : IsGalois K M₂ := galKM₂
  letI : IsGalois E M₂ := galEM₂
  letI : ValuativeRel U₂ := vU₂
  letI : TopologicalSpace U₂ := tU₂
  letI : IsNonarchimedeanLocalField U₂ := locU₂
  letI : ValuativeRel M₂ := vM₂
  letI : TopologicalSpace M₂ := tM₂
  letI : IsNonarchimedeanLocalField M₂ := locM₂
  letI : ValuativeExtension K U₂ := veKU₂
  letI : ValuativeExtension K M₂ := veKM₂
  letI : ValuativeExtension E M₂ := veEM₂
  letI : ValuativeExtension U₂ M₂ := veU₂M₂
  letI : ContinuousSMul K U₂ := csKU₂
  letI : ContinuousSMul K M₂ := csKM₂
  letI : ContinuousSMul E M₂ := csEM₂
  letI : ContinuousSMul U₂ M₂ := csU₂M₂
  obtain ⟨D₂⟩ := hD₂
  let Ksep := SeparableClosure K
  let T : UnramifiedTower K Ksep := unramifiedTower K Ksep
  obtain ⟨eU, eM, hLM, hUM⟩ :=
    unramifiedEnvelope_inflation_embeddings K L E Ksep U₁ M₁ U₂ M₂ T D₁ D₂
  letI : Algebra U₁ U₂ := eU.toRingHom.toAlgebra
  letI : IsScalarTower K U₁ U₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (eU.commutes x).symm
  letI : FiniteDimensional U₁ U₂ := FiniteDimensional.right K U₁ U₂
  letI : IsGalois U₁ U₂ := IsGalois.tower_top_of_isGalois K U₁ U₂
  letI : ValuativeExtension U₁ U₂ := envelopeValuativeExtension_of_tower K U₁ U₂
  let hcontU : Continuous eU := by
    letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
    letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
    letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
    letI : UniformSpace U₁ := IsTopologicalAddGroup.rightUniformSpace U₁
    letI : IsUniformAddGroup U₁ := isUniformAddGroup_of_addCommGroup
    letI : ValuativeRel.IsNontrivial U₁ :=
      IsNonarchimedeanLocalField.toIsNontrivial
    exact LinearMap.continuous_of_finiteDimensional (𝕜 := K) eU.toLinearMap
  letI : ContinuousSMul U₁ U₂ := by
    constructor
    change Continuous (fun p : U₁ × U₂ => eU p.1 * p.2)
    exact (hcontU.comp continuous_fst).mul continuous_snd
  letI : IsUnramifiedLocalExtension U₁ U₂ := by
    constructor
    let ϖ := defaultUniformizer K
    let x : Units U₁ := Units.map (algebraMap K U₁) ϖ.val
    have h₁₂ := normalizedValuation_algebraMap U₁ U₂ x
    have hK₁ := normalizedValuation_algebraMap K U₁ ϖ.val
    have hK₂ := normalizedValuation_algebraMap K U₂ ϖ.val
    have hx : Units.map (algebraMap U₁ U₂).toMonoidHom x =
        Units.map (algebraMap K U₂).toMonoidHom ϖ.val := by
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply K U₁ U₂ (ϖ.val : K)).symm
    have hleft : normalizedValuation U₂
        (Units.map (algebraMap U₁ U₂).toMonoidHom x) = 1 := by
      calc
        _ = normalizedValuation U₂
            (Units.map (algebraMap K U₂).toMonoidHom ϖ.val) :=
          congrArg (normalizedValuation U₂) hx
        _ = (ramificationIndex K U₂ : ℤ) * normalizedValuation K ϖ.val := hK₂
        _ = 1 := by
          rw [D₂.source.unramified.ramificationIndex_eq_one,
            ϖ.valuation_eq_one]
          norm_num
    have hright : normalizedValuation U₁ x = 1 := by
      dsimp only [x]
      rw [hK₁, D₁.source.unramified.ramificationIndex_eq_one,
        ϖ.valuation_eq_one]
      norm_num
    have heq : (1 : ℤ) = (ramificationIndex U₁ U₂ : ℤ) * 1 :=
      hleft.symm.trans (h₁₂.trans
        (congrArg (fun z : ℤ => (ramificationIndex U₁ U₂ : ℤ) * z) hright))
    norm_num at heq
    exact_mod_cast heq.symm
  let U₁sep := SeparableClosure U₁
  letI : IsSepClosed U₁sep := IsSepClosure.sep_closed U₁
  let jU₂ : U₂ →ₐ[U₁] U₁sep := IsSepClosed.lift
  letI : Algebra U₂ U₁sep := jU₂.toRingHom.toAlgebra
  letI : IsScalarTower U₁ U₂ U₁sep :=
    IsScalarTower.of_algebraMap_eq fun x => (jU₂.commutes x).symm
  obtain ⟨upper⟩ := envelopeUnramifiedCyclicDataExists U₁ U₂ U₁sep inferInstance
  obtain ⟨C, hClower, hCtotal, -⟩ :=
    unramifiedCarryTowerData_exists K U₁ U₂ D₁.source D₂.source upper
  let C₁ : UnramifiedClassData K U₁ C.lower π := hClower.symm ▸ D₁.sourceClass
  let C₂ : UnramifiedClassData K U₂ C.total π := hCtotal.symm ▸ D₂.sourceClass
  have hC₁ : C₁.class = D₁.sourceClass.class :=
    unramifiedClassData_transport_class hClower.symm π D₁.sourceClass
  have hC₂ : C₂.class = D₂.sourceClass.class :=
    unramifiedClassData_transport_class hCtotal.symm π D₂.sourceClass
  have hcarryC := (carryClass_inflation K U₁ U₂ C π C₁ C₂).2
  have hdegree : Module.finrank U₁ U₂ = Module.finrank L E := by
    have hU := Module.finrank_mul_finrank K U₁ U₂
    rw [D₁.source_degree, D₂.source_degree] at hU
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos
      (hU.trans (Module.finrank_mul_finrank K L E).symm)
  have hCq : C.quotientHom = towerQuotientHom K U₁ U₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro u
    apply (algebraMap U₁ U₂).injective
    exact (C.quotientHom_apply σ u).trans
      (AlgEquiv.restrictNormal_commutes σ U₁ u).symm
  have hCc : ∀ u : (MulRep K U₁).V,
      C.inflationCoefficient.hom u = (towerInflationCoefficient K U₁ U₂).hom u := by
    intro u
    rw [show u = Additive.ofMul (Additive.toMul u) from rfl]
    apply Additive.toMul.injective
    exact C.inflationCoefficient_apply (Additive.toMul u)
  have hcarryMap := envelopeTransportedH2_congr C.inflationCoefficient
    (towerInflationCoefficient K U₁ U₂) hCq hCc C₁.class
  have hcarry :
      transportedH2 (towerQuotientHom K U₁ U₂)
          (towerInflationCoefficient K U₁ U₂) D₁.sourceClass.class =
        (Module.finrank L E : ℤ) • D₂.sourceClass.class := by
    rw [← hC₁, ← hC₂, ← hdegree]
    exact hcarryMap.symm.trans hcarryC
  letI : Algebra L M₂ :=
    ((algebraMap E M₂).comp (algebraMap L E)).toAlgebra
  letI : IsScalarTower L E M₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K L M₂ := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap K M₂ x = algebraMap E M₂ (algebraMap K E x) :=
        IsScalarTower.algebraMap_apply K E M₂ x
      _ = algebraMap E M₂ (algebraMap L E (algebraMap K L x)) := by
        rw [IsScalarTower.algebraMap_apply K L E]
      _ = algebraMap L M₂ (algebraMap K L x) := rfl
  letI : Algebra U₁ M₂ :=
    ((algebraMap U₂ M₂).comp eU.toRingHom).toAlgebra
  letI : IsScalarTower U₁ U₂ M₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K U₁ M₂ := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap K M₂ x = algebraMap U₂ M₂ (algebraMap K U₂ x) :=
        IsScalarTower.algebraMap_apply K U₂ M₂ x
      _ = algebraMap U₂ M₂ (eU (algebraMap K U₁ x)) := by
        rw [eU.commutes]
      _ = algebraMap U₁ M₂ (algebraMap K U₁ x) := rfl
  letI : Algebra M₁ M₂ := eM.toRingHom.toAlgebra
  letI : IsScalarTower K M₁ M₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (eM.commutes x).symm
  letI : IsScalarTower L M₁ M₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (hLM x).symm
  letI : IsScalarTower U₁ M₁ M₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (hUM x).symm
  letI : FiniteDimensional M₁ M₂ := FiniteDimensional.right K M₁ M₂
  have hD₁descentQ : D₁.descentQuotient = towerQuotientHom K L M₁ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M₁).injective
    exact (D₁.descentQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ L x).symm
  have hD₁descentC : ∀ x : (MulRep K L).V,
      D₁.descentCoefficient.hom x = (towerInflationCoefficient K L M₁).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₁.descentCoefficient_apply (Additive.toMul x)
  have hD₁descentMap (x : Inhomogeneous.H2 (MulRep K L)) :
      transportedH2 D₁.descentQuotient D₁.descentCoefficient x =
        transportedH2 (towerQuotientHom K L M₁)
          (towerInflationCoefficient K L M₁) x :=
    envelopeTransportedH2_congr D₁.descentCoefficient
      (towerInflationCoefficient K L M₁) hD₁descentQ hD₁descentC x
  have hD₁sourceQ : D₁.sourceQuotient = towerQuotientHom K U₁ M₁ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U₁ M₁).injective
    exact (D₁.sourceQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ U₁ x).symm
  have hD₁sourceC : ∀ x : (MulRep K U₁).V,
      D₁.sourceCoefficient.hom x = (towerInflationCoefficient K U₁ M₁).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₁.sourceCoefficient_apply (Additive.toMul x)
  have hD₁sourceMap :
      transportedH2 D₁.sourceQuotient D₁.sourceCoefficient D₁.sourceClass.class =
        transportedH2 (towerQuotientHom K U₁ M₁)
          (towerInflationCoefficient K U₁ M₁) D₁.sourceClass.class :=
    envelopeTransportedH2_congr D₁.sourceCoefficient
      (towerInflationCoefficient K U₁ M₁) hD₁sourceQ hD₁sourceC _
  have hdesc₁ :
      transportedH2 (towerQuotientHom K L M₁) (towerInflationCoefficient K L M₁)
          (fundamentalClassValue K L) =
        transportedH2 (towerQuotientHom K U₁ M₁) (towerInflationCoefficient K U₁ M₁)
          D₁.sourceClass.class := by
    calc
      _ = transportedH2 D₁.descentQuotient D₁.descentCoefficient
          (fundamentalClassValue K L) := (hD₁descentMap _).symm
      _ = D₁.psi := (fundamentalClass K L).descends π U₁ M₁ D₁
      _ = transportedH2 D₁.sourceQuotient D₁.sourceCoefficient
          D₁.sourceClass.class := D₁.psi_eq_inflated
      _ = _ := hD₁sourceMap
  have hD₂descentQ : D₂.descentQuotient = towerQuotientHom K E M₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E M₂).injective
    exact (D₂.descentQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ E x).symm
  have hD₂descentC : ∀ x : (MulRep K E).V,
      D₂.descentCoefficient.hom x = (towerInflationCoefficient K E M₂).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₂.descentCoefficient_apply (Additive.toMul x)
  have hD₂descentMap (x : Inhomogeneous.H2 (MulRep K E)) :
      transportedH2 D₂.descentQuotient D₂.descentCoefficient x =
        transportedH2 (towerQuotientHom K E M₂)
          (towerInflationCoefficient K E M₂) x :=
    envelopeTransportedH2_congr D₂.descentCoefficient
      (towerInflationCoefficient K E M₂) hD₂descentQ hD₂descentC x
  have hD₂sourceQ : D₂.sourceQuotient = towerQuotientHom K U₂ M₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U₂ M₂).injective
    exact (D₂.sourceQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ U₂ x).symm
  have hD₂sourceC : ∀ x : (MulRep K U₂).V,
      D₂.sourceCoefficient.hom x = (towerInflationCoefficient K U₂ M₂).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₂.sourceCoefficient_apply (Additive.toMul x)
  have hD₂sourceMap :
      transportedH2 D₂.sourceQuotient D₂.sourceCoefficient D₂.sourceClass.class =
        transportedH2 (towerQuotientHom K U₂ M₂)
          (towerInflationCoefficient K U₂ M₂) D₂.sourceClass.class :=
    envelopeTransportedH2_congr D₂.sourceCoefficient
      (towerInflationCoefficient K U₂ M₂) hD₂sourceQ hD₂sourceC _
  have hdesc₂ :
      transportedH2 (towerQuotientHom K E M₂) (towerInflationCoefficient K E M₂)
          (fundamentalClassValue K E) =
        transportedH2 (towerQuotientHom K U₂ M₂) (towerInflationCoefficient K U₂ M₂)
          D₂.sourceClass.class := by
    calc
      _ = transportedH2 D₂.descentQuotient D₂.descentCoefficient
          (fundamentalClassValue K E) := (hD₂descentMap _).symm
      _ = D₂.psi := (fundamentalClass K E).descends π U₂ M₂ D₂
      _ = transportedH2 D₂.sourceQuotient D₂.sourceCoefficient
          D₂.sourceClass.class := D₂.psi_eq_inflated
      _ = _ := hD₂sourceMap
  have hactual :
      transportedH2 (actualFundamentalInflationData K L E).quotientHom
          (actualFundamentalInflationData K L E).coefficient
          (fundamentalClassValue K L) =
        transportedH2 (towerQuotientHom K L E) (towerInflationCoefficient K L E)
          (fundamentalClassValue K L) := by
    rfl
  apply (towerTransportedH2_infRes K E M₂).1
  rw [map_zsmul]
  calc
    transportedH2 (towerQuotientHom K E M₂) (towerInflationCoefficient K E M₂)
        (transportedH2 (actualFundamentalInflationData K L E).quotientHom
          (actualFundamentalInflationData K L E).coefficient
          (fundamentalClassValue K L)) =
      transportedH2 (towerQuotientHom K E M₂) (towerInflationCoefficient K E M₂)
        (transportedH2 (towerQuotientHom K L E) (towerInflationCoefficient K L E)
          (fundamentalClassValue K L)) := congrArg _ hactual
    _ = transportedH2 (towerQuotientHom K M₁ M₂) (towerInflationCoefficient K M₁ M₂)
        (transportedH2 (towerQuotientHom K L M₁) (towerInflationCoefficient K L M₁)
          (fundamentalClassValue K L)) :=
      towerInflation_diamond K L E M₁ M₂ (fundamentalClassValue K L)
    _ = transportedH2 (towerQuotientHom K M₁ M₂) (towerInflationCoefficient K M₁ M₂)
        (transportedH2 (towerQuotientHom K U₁ M₁) (towerInflationCoefficient K U₁ M₁)
          D₁.sourceClass.class) := congrArg _ hdesc₁
    _ = transportedH2 (towerQuotientHom K U₂ M₂) (towerInflationCoefficient K U₂ M₂)
        (transportedH2 (towerQuotientHom K U₁ U₂) (towerInflationCoefficient K U₁ U₂)
          D₁.sourceClass.class) :=
      towerInflation_diamond K U₁ M₁ U₂ M₂ D₁.sourceClass.class
    _ = transportedH2 (towerQuotientHom K U₂ M₂) (towerInflationCoefficient K U₂ M₂)
        ((Module.finrank L E : ℤ) • D₂.sourceClass.class) := congrArg _ hcarry
    _ = (Module.finrank L E : ℤ) •
        transportedH2 (towerQuotientHom K U₂ M₂) (towerInflationCoefficient K U₂ M₂)
          D₂.sourceClass.class := map_zsmul _ _ _
    _ = (Module.finrank L E : ℤ) •
        transportedH2 (towerQuotientHom K E M₂) (towerInflationCoefficient K E M₂)
          (fundamentalClassValue K E) := congrArg _ hdesc₂.symm

/--
**F09**, Proposition `prop:fundamental-inflation`: for `L ⊆ E`, the actual inflation map sends
`α_{L/K}` to `[E:L] α_{E/K}`.  The existential object contains only pointwise-pinned maps, so a
zero-map witness is impossible.
-/
theorem fundamentalClass_inflation :
    ∃ D : FundamentalInflationData K L E,
      transportedH2 D.quotientHom D.coefficient (fundamentalClassValue K L) =
        (Module.finrank L E : ℤ) • fundamentalClassValue K E := by
  exact ⟨actualFundamentalInflationData K L E,
    actualFundamentalInflation_square K L E⟩

private theorem fundamentalClass_inflation_systemField :
    ∃ (q : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L))
      (c : Rep.res q (MulRep K L) ⟶ MulRep K E),
      (∀ (σ : E ≃ₐ[K] E) (x : L),
        algebraMap L E (q σ x) = σ (algebraMap L E x)) ∧
      (∀ x : Units L,
        Additive.toMul (c.hom (Additive.ofMul x)) = Units.map (algebraMap L E) x) ∧
      transportedH2 q c (fundamentalClassValue K L) =
        (Module.finrank L E : ℤ) • fundamentalClassValue K E := by
  obtain ⟨D, hD⟩ := fundamentalClass_inflation K L E
  exact ⟨D.quotientHom, D.coefficient, D.quotientHom_apply,
    D.coefficient_apply, hD⟩

end Inflation

set_option maxHeartbeats 1200000 in
/-- Intersecting an unramified level whose degree is a multiple of `[E:F]` with `E`
finds the same maximal unramified subfield as the degree-`[E:F]` level. -/
private theorem envelope_tower_intersection_finrank_of_dvd
    (F E Fsep : Type) [Field F] [Field E] [Field Fsep]
    [Algebra F E] [Algebra F Fsep] [FiniteDimensional F E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension F E] [IsSepClosure F Fsep]
    (T : UnramifiedTower F Fsep) (j : E →ₐ[F] Fsep) (m : ℕ)
    (hdiv : Module.finrank F E ∣ m + 1) :
    Module.finrank F
        (j.fieldRange ⊓ T.field m : IntermediateField F Fsep) =
      residueDegree F E := by
  let n := Module.finrank F E
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel Module.finrank_pos
  have hnm : T.field (n - 1) ≤ T.field m := by
    apply T.le_of_dvd
    simpa only [hn] using hdiv
  let I : IntermediateField F Fsep := j.fieldRange ⊓ T.field m
  letI : FiniteDimensional F (T.field m) := T.finiteDimensional m
  letI : FiniteDimensional F I :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (show I ≤ T.field m from inf_le_right)).toLinearMap
      (IntermediateField.inclusion_injective (show I ≤ T.field m from inf_le_right))
  let d := Module.finrank F I
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel Module.finrank_pos
  have hdm : d ∣ m + 1 := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (show I ≤ T.field m from inf_le_right)
    rwa [T.finrank m] at h
  have hdn : d ∣ n := by
    letI : FiniteDimensional F j.fieldRange :=
      j.equivFieldRange.toLinearEquiv.finiteDimensional
    have h := IntermediateField.finrank_dvd_of_le_right
      (show I ≤ j.fieldRange from inf_le_left)
    rw [← j.equivFieldRange.toLinearEquiv.finrank_eq] at h
    exact h
  letI : IsGalois F (T.field m) := T.isGalois m
  let V := T.field (d - 1)
  letI : FiniteDimensional F V := T.finiteDimensional (d - 1)
  have hVm : V ≤ T.field m := T.le_of_dvd (by simpa only [hd] using hdm)
  have hcyc : IsCyclic (T.field m ≃ₐ[F] T.field m) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨T.frobenius m, T.frobenius_generates m⟩
  have hIV : I = V := by
    apply envelope_intermediateField_eq_of_cyclic_of_finrank_eq
      (T.field m) I V hcyc inf_le_right hVm
    rw [T.finrank (d - 1), hd]
  have hIn : I ≤ T.field (n - 1) := by
    rw [hIV]
    exact T.le_of_dvd (by simpa only [hd, hn] using hdn)
  have hintersection :
      j.fieldRange ⊓ T.field m = j.fieldRange ⊓ T.field (n - 1) := by
    apply le_antisymm
    · exact le_inf inf_le_left hIn
    · exact le_inf inf_le_left (inf_le_right.trans hnm)
  rw [hintersection]
  exact envelope_tower_intersection_finrank F E Fsep T j

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
/-- Restriction of coefficients and inflation along a field tower form the literal mixed square. -/
private theorem towerRestriction_inflation_square
    (F E A B : Type) [Field F] [Field E] [Field A] [Field B]
    [Algebra F E] [Algebra F A] [Algebra F B]
    [Algebra E A] [Algebra E B] [Algebra A B]
    [IsScalarTower F E A] [IsScalarTower F E B]
    [IsScalarTower F A B] [IsScalarTower E A B]
    [FiniteDimensional F E] [FiniteDimensional F A] [FiniteDimensional F B]
    [FiniteDimensional E A] [FiniteDimensional E B]
    [IsGalois F A] [IsGalois F B] [IsGalois E A] [IsGalois E B]
    (x : Inhomogeneous.H2 (MulRep F A)) :
    transportedH2 (towerQuotientHom E A B) (towerInflationCoefficient E A B)
        (transportedH2 (towerSubgroupHom F E A)
          (towerRestrictionCoefficient F E A) x) =
      transportedH2 (towerSubgroupHom F E B) (towerRestrictionCoefficient F E B)
        (transportedH2 (towerQuotientHom F A B)
          (towerInflationCoefficient F A B) x) := by
  let qL := (towerSubgroupHom F E A).comp (towerQuotientHom E A B)
  let cL := (Rep.resFunctor (towerQuotientHom E A B)).map
      (towerRestrictionCoefficient F E A) ≫ towerInflationCoefficient E A B
  let qR := (towerQuotientHom F A B).comp (towerSubgroupHom F E B)
  let cR := (Rep.resFunctor (towerSubgroupHom F E B)).map
      (towerInflationCoefficient F A B) ≫ towerRestrictionCoefficient F E B
  have hq : qL = qR := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro a
    apply (algebraMap A B).injective
    calc
      algebraMap A B (qL σ a) = σ (algebraMap A B a) :=
        AlgEquiv.restrictNormal_commutes σ A a
      _ = (towerSubgroupHom F E B σ) (algebraMap A B a) := rfl
      _ = algebraMap A B (qR σ a) :=
        (AlgEquiv.restrictNormal_commutes (towerSubgroupHom F E B σ) A a).symm
  have hc : ∀ a : (MulRep F A).V, cL.hom a = cR.hom a := by
    intro a
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hL := transportedH2_comp (towerSubgroupHom F E A)
    (towerQuotientHom E A B) (towerRestrictionCoefficient F E A)
    (towerInflationCoefficient E A B) x
  have hR := transportedH2_comp (towerQuotientHom F A B)
    (towerSubgroupHom F E B) (towerInflationCoefficient F A B)
    (towerRestrictionCoefficient F E B) x
  have hcLinear : cL.hom.toLinearMap = cR.hom.toLinearMap := by
    apply LinearMap.ext
    exact hc
  have hmaps := groupCohomology_map_congr
    (A := MulRep F A) (B := MulRep E B) hq hcLinear 2
  have hmiddle : transportedH2 qL cL x = transportedH2 qR cR x := by
    apply (comparisonH2 (MulRep E B)).injective
    simp only [transportedH2, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
      Function.comp_apply, AddEquiv.apply_symm_apply]
    rw [hmaps]
  exact hL.trans (hmiddle.trans hR.symm)

section Restriction

variable (E : Type) [Field E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L]
  [FiniteDimensional K E] [FiniteDimensional E L] [IsGalois E L]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension K E] [ValuativeExtension E L]
  [ContinuousSMul K E] [ContinuousSMul E L]

/-- **F09**, Proposition `prop:fundamental-restriction`: its actual subgroup/coefficient maps. -/
structure FundamentalRestrictionData where
  /-- Inclusion `Gal(L/E) → Gal(L/K)`. -/
  subgroupHom : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L)
  /-- It leaves the underlying automorphism of `L` unchanged. -/
  subgroupHom_apply : ∀ (σ : L ≃ₐ[E] L) (x : L), subgroupHom σ x = σ x
  /-- Identity coefficient morphism on `Lˣ`. -/
  coefficient : Rep.res subgroupHom (MulRep K L) ⟶ MulRep E L
  /-- It is pointwise the identity. -/
  coefficient_apply : ∀ x : Units L,
    coefficient.hom (Additive.ofMul x) = Additive.ofMul x

private noncomputable def actualFundamentalRestrictionData :
    FundamentalRestrictionData K L E := by
  let s : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  let c : Rep.res s (MulRep K L) ⟶ MulRep E L :=
    Rep.ofHom ⟨(AddMonoidHom.id (Additive (Units L))).toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      rfl⟩
  exact {
    subgroupHom := s
    subgroupHom_apply := by
      intro σ x
      rfl
    coefficient := c
    coefficient_apply := by
      intro x
      rfl }

set_option maxHeartbeats 10000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Private common-refinement construction for the descended F07 base-change face. -/
private theorem fundamentalRestriction_descended_baseChange_face_aux :
    transportedH2 (towerSubgroupHom K E L) (towerRestrictionCoefficient K E L)
        (fundamentalClassValue K L) = fundamentalClassValue E L := by
  classical
  let πK := defaultUniformizer K
  let πE := defaultUniformizer E
  obtain ⟨U₁, M₁, fU₁, fM₁, aKU₁, aKM₁, aLM₁, aU₁M₁, stKLM₁, stKU₁M₁,
      fdKU₁, fdKM₁, fdLM₁, fdU₁M₁, galKU₁, galKM₁, galLM₁,
      vU₁, tU₁, locU₁, vM₁, tM₁, locM₁, veKU₁, veKM₁, veLM₁, veU₁M₁,
      csKU₁, csKM₁, csLM₁, csU₁M₁, hD₁⟩ :=
    unramifiedEnvelope_descentData K L πK
  letI : Field U₁ := fU₁
  letI : Field M₁ := fM₁
  letI : Algebra K U₁ := aKU₁
  letI : Algebra K M₁ := aKM₁
  letI : Algebra L M₁ := aLM₁
  letI : Algebra U₁ M₁ := aU₁M₁
  letI : IsScalarTower K L M₁ := stKLM₁
  letI : IsScalarTower K U₁ M₁ := stKU₁M₁
  letI : FiniteDimensional K U₁ := fdKU₁
  letI : FiniteDimensional K M₁ := fdKM₁
  letI : FiniteDimensional L M₁ := fdLM₁
  letI : FiniteDimensional U₁ M₁ := fdU₁M₁
  letI : IsGalois K U₁ := galKU₁
  letI : IsGalois K M₁ := galKM₁
  letI : IsGalois L M₁ := galLM₁
  letI : ValuativeRel U₁ := vU₁
  letI : TopologicalSpace U₁ := tU₁
  letI : IsNonarchimedeanLocalField U₁ := locU₁
  letI : ValuativeRel M₁ := vM₁
  letI : TopologicalSpace M₁ := tM₁
  letI : IsNonarchimedeanLocalField M₁ := locM₁
  letI : ValuativeExtension K U₁ := veKU₁
  letI : ValuativeExtension K M₁ := veKM₁
  letI : ValuativeExtension L M₁ := veLM₁
  letI : ValuativeExtension U₁ M₁ := veU₁M₁
  letI : ContinuousSMul K U₁ := csKU₁
  letI : ContinuousSMul K M₁ := csKM₁
  letI : ContinuousSMul L M₁ := csLM₁
  letI : ContinuousSMul U₁ M₁ := csU₁M₁
  obtain ⟨D₁⟩ := hD₁
  obtain ⟨U₂, M₂, fU₂, fM₂, aEU₂, aEM₂, aLM₂, aU₂M₂, stELM₂, stEU₂M₂,
      fdEU₂, fdEM₂, fdLM₂, fdU₂M₂, galEU₂, galEM₂, galLM₂,
      vU₂, tU₂, locU₂, vM₂, tM₂, locM₂, veEU₂, veEM₂, veLM₂, veU₂M₂,
      csEU₂, csEM₂, csLM₂, csU₂M₂, hD₂⟩ :=
    unramifiedEnvelope_descentData E L πE
  letI : Field U₂ := fU₂
  letI : Field M₂ := fM₂
  letI : Algebra E U₂ := aEU₂
  letI : Algebra E M₂ := aEM₂
  letI : Algebra L M₂ := aLM₂
  letI : Algebra U₂ M₂ := aU₂M₂
  letI : IsScalarTower E L M₂ := stELM₂
  letI : IsScalarTower E U₂ M₂ := stEU₂M₂
  letI : FiniteDimensional E U₂ := fdEU₂
  letI : FiniteDimensional E M₂ := fdEM₂
  letI : FiniteDimensional L M₂ := fdLM₂
  letI : FiniteDimensional U₂ M₂ := fdU₂M₂
  letI : IsGalois E U₂ := galEU₂
  letI : IsGalois E M₂ := galEM₂
  letI : IsGalois L M₂ := galLM₂
  letI : ValuativeRel U₂ := vU₂
  letI : TopologicalSpace U₂ := tU₂
  letI : IsNonarchimedeanLocalField U₂ := locU₂
  letI : ValuativeRel M₂ := vM₂
  letI : TopologicalSpace M₂ := tM₂
  letI : IsNonarchimedeanLocalField M₂ := locM₂
  letI : ValuativeExtension E U₂ := veEU₂
  letI : ValuativeExtension E M₂ := veEM₂
  letI : ValuativeExtension L M₂ := veLM₂
  letI : ValuativeExtension U₂ M₂ := veU₂M₂
  letI : ContinuousSMul E U₂ := csEU₂
  letI : ContinuousSMul E M₂ := csEM₂
  letI : ContinuousSMul L M₂ := csLM₂
  letI : ContinuousSMul U₂ M₂ := csU₂M₂
  obtain ⟨D₂⟩ := hD₂
  let Ksep := SeparableClosure K
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let jL : L →ₐ[K] Ksep := IsSepClosed.lift
  letI : Algebra L Ksep := jL.toRingHom.toAlgebra
  letI : IsScalarTower K L Ksep :=
    IsScalarTower.of_algebraMap_eq fun x => (jL.commutes x).symm
  let jM₁ : M₁ →ₐ[L] Ksep := IsSepClosed.lift
  let jM₂ : M₂ →ₐ[L] Ksep := IsSepClosed.lift
  let jU₁ : U₁ →ₐ[K] Ksep :=
    (jM₁.restrictScalars K).comp (IsScalarTower.toAlgHom K U₁ M₁)
  let jE : E →ₐ[K] Ksep := jL.comp (IsScalarTower.toAlgHom K E L)
  letI : Algebra E Ksep := jE.toRingHom.toAlgebra
  letI : IsScalarTower K E Ksep :=
    IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm
  letI : IsScalarTower E L Ksep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let jU₂ : U₂ →ₐ[E] Ksep :=
    (jM₂.restrictScalars E).comp (IsScalarTower.toAlgHom E U₂ M₂)
  letI : IsSepClosure E Ksep :=
    { sep_closed := IsSepClosure.sep_closed K
      separable := ⟨fun x =>
        IsSeparable.tower_top E (Algebra.IsSeparable.isSeparable K x)⟩ }
  let TK : UnramifiedTower K Ksep := unramifiedTower K Ksep
  let TE : UnramifiedTower E Ksep := unramifiedTower E Ksep
  have hU₁range : jU₁.fieldRange = TK.field (Module.finrank K U₁ - 1) :=
    envelopeSourceRange_eq_tower K U₁ Ksep TK D₁.source jU₁
  have hU₂range : jU₂.fieldRange = TE.field (Module.finrank E U₂ - 1) :=
    envelopeSourceRange_eq_tower E U₂ Ksep TE D₂.source jU₂
  let n := Module.finrank K U₁
  let r := Module.finrank E U₂
  let f := residueDegree K E
  let e := ramificationIndex K E
  let m := r * e
  have hn : n = Module.finrank K L := D₁.source_degree
  have hr : r = Module.finrank E L := D₂.source_degree
  have hEf : Module.finrank K E = e * f :=
    finrank_eq_ramificationIndex_mul_residueDegree K E
  have hmf : m * f = n := by
    calc
      m * f = (e * f) * r := by
        simp only [m, mul_comm, mul_left_comm, mul_assoc]
      _ = Module.finrank K E * Module.finrank E L := by rw [← hEf, hr]
      _ = Module.finrank K L := Module.finrank_mul_finrank K E L
      _ = n := hn.symm
  have hmpos : 0 < m := by
    have hnpos : 0 < n := Module.finrank_pos
    have hprod : 0 < m * f := hmf.symm ▸ hnpos
    exact Nat.pos_of_mul_pos_right hprod
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
  let W : IntermediateField E Ksep := TE.field (m - 1)
  letI : FiniteDimensional E W := TE.finiteDimensional (m - 1)
  letI : IsGalois E W := TE.isGalois (m - 1)
  letI : ValuativeRel W :=
    unramifiedIntermediateFieldValuativeRel E Ksep W (TE.unramified (m - 1))
  letI : TopologicalSpace W :=
    unramifiedIntermediateFieldTopology E Ksep W (TE.unramified (m - 1))
  letI : IsNonarchimedeanLocalField W :=
    unramifiedIntermediateFieldLocalField E Ksep W (TE.unramified (m - 1))
  letI : ValuativeExtension E W :=
    unramifiedIntermediateFieldValuativeExtension E Ksep W (TE.unramified (m - 1))
  letI : ContinuousSMul E W :=
    unramifiedIntermediateFieldContinuousSMul E Ksep W (TE.unramified (m - 1))
  let aKW : Algebra K W :=
    ((algebraMap E W).comp (algebraMap K E)).toAlgebra
  letI : Algebra K W := aKW
  letI : Module K W := aKW.toModule
  letI : IsScalarTower K E W := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fdKW : FiniteDimensional K W := FiniteDimensional.trans K E W
  letI : FiniteDimensional K W := fdKW
  let hveKW : ValuativeExtension K W := by
    constructor
    intro x y
    change algebraMap E W (algebraMap K E x) ≤ᵥ
        algebraMap E W (algebraMap K E y) ↔ x ≤ᵥ y
    rw [ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]
  letI : ValuativeExtension K W := hveKW
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation W) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation W) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  have hepos : 0 < e := by
    have hKE : 0 < Module.finrank K E := Module.finrank_pos
    have hprod : 0 < e * f := hEf.symm ▸ hKE
    exact Nat.pos_of_mul_pos_right hprod
  have hramKW : ramificationIndex K W = e := by
    let ϖ := defaultUniformizer K
    let x : Units E := Units.map (algebraMap K E) ϖ.val
    have hKW := normalizedValuation_algebraMap K W ϖ.val
    have hKE := normalizedValuation_algebraMap K E ϖ.val
    have hEW := normalizedValuation_algebraMap E W x
    have hx : Units.map (algebraMap E W).toMonoidHom x =
        Units.map (algebraMap K W).toMonoidHom ϖ.val := by
      apply Units.ext
      rfl
    have hz : (ramificationIndex K W : ℤ) = (e : ℤ) := by
      calc
        (ramificationIndex K W : ℤ) = normalizedValuation W
            (Units.map (algebraMap K W).toMonoidHom ϖ.val) := by
          symm
          calc
            _ = (ramificationIndex K W : ℤ) * normalizedValuation K ϖ.val := hKW
            _ = (ramificationIndex K W : ℤ) := by
              rw [ϖ.valuation_eq_one]
              norm_num
        _ = normalizedValuation W
            (Units.map (algebraMap E W).toMonoidHom x) :=
          congrArg (normalizedValuation W) hx.symm
        _ = (ramificationIndex E W : ℤ) * normalizedValuation E x := hEW
        _ = normalizedValuation E x := by
          rw [(unramifiedIntermediateFieldIsUnramified E Ksep W
            (TE.unramified (m - 1))).ramificationIndex_eq_one]
          norm_num
        _ = (ramificationIndex K E : ℤ) := by
          dsimp only [x]
          rw [hKE, ϖ.valuation_eq_one]
          norm_num
        _ = (e : ℤ) := rfl
    exact_mod_cast hz
  have hresDegree : residueDegree K W = n := by
    apply Nat.eq_of_mul_eq_mul_left hepos
    calc
      e * residueDegree K W = Module.finrank K W := by
        rw [finrank_eq_ramificationIndex_mul_residueDegree K W, hramKW]
      _ = Module.finrank K E * Module.finrank E W :=
        (Module.finrank_mul_finrank K E W).symm
      _ = (e * f) * m := by rw [hEf, TE.finrank (m - 1), hm]
      _ = e * n := by rw [← hmf]; ac_rfl
  let kK := LocalResidueField K
  let kW := LocalResidueField W
  letI : Algebra kK kW :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers W))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  have hresKW : Module.finrank kK kW = n :=
    (residueFinrank_eq_residueDegree_of_localFields (K := K) (L := W)).trans hresDegree
  let jW : W →ₐ[K] Ksep := W.val.restrictScalars K
  have hTKWraw : TK.field (n - 1) ≤ jW.fieldRange := by
    refine @UnramifiedTower.field_le_fieldRange_of_dvd_residueFinrank
      K Ksep _ _ _ _ _ _ _ TK W W.toField aKW fdKW
      (inferInstance : ValuativeRel W)
      (inferInstance : TopologicalSpace W) (inferInstance : IsNonarchimedeanLocalField W)
      (inferInstance : ValuativeExtension K W) jW (n - 1) ?_
    have hnpos : 0 < n := Module.finrank_pos
    rw [Nat.sub_add_cancel hnpos, hresKW]
  have hjW : jW.fieldRange = W.restrictScalars K := by
    ext x
    simp only [AlgHom.mem_fieldRange, IntermediateField.mem_restrictScalars]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hTKW : TK.field (n - 1) ≤ W.restrictScalars K := hjW ▸ hTKWraw
  have hU₁W : jU₁.fieldRange ≤ W.restrictScalars K := by
    rw [hU₁range]
    exact hTKW
  have hEW : jE.fieldRange ≤ W.restrictScalars K := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact (algebraMap E W y).2
  let C₀ : IntermediateField K Ksep := jU₁.fieldRange ⊔ jE.fieldRange
  have hC₀W : C₀ ≤ W.restrictScalars K := sup_le hU₁W hEW
  have hdivEn : Module.finrank K E ∣ n := by
    refine ⟨Module.finrank E L, ?_⟩
    rw [hn, Module.finrank_mul_finrank K E L]
  have hintersection₀ : Module.finrank K
      (jE.fieldRange ⊓ jU₁.fieldRange : IntermediateField K Ksep) = f := by
    rw [hU₁range]
    apply envelope_tower_intersection_finrank_of_dvd K E Ksep TK jE (n - 1)
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel Module.finrank_pos
    simpa only [hnsub] using hdivEn
  let I₀ : IntermediateField K Ksep := jU₁.fieldRange ⊓ jE.fieldRange
  have hintersectionI : Module.finrank K I₀ = f := by
    change Module.finrank K
      (jU₁.fieldRange ⊓ jE.fieldRange : IntermediateField K Ksep) = f
    rw [inf_comm]
    exact hintersection₀
  letI : FiniteDimensional K jE.fieldRange :=
    jE.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K jU₁.fieldRange :=
    jU₁.equivFieldRange.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional K I₀ :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (show I₀ ≤ jU₁.fieldRange from inf_le_left)).toLinearMap
      (IntermediateField.inclusion_injective
        (show I₀ ≤ jU₁.fieldRange from inf_le_left))
  letI : FiniteDimensional K C₀ :=
    IntermediateField.finiteDimensional_sup jU₁.fieldRange jE.fieldRange
  letI : IsGalois K jU₁.fieldRange := IsGalois.of_algEquiv jU₁.equivFieldRange
  letI : Algebra jU₁.fieldRange C₀ :=
    intermediateFieldInclusionAlgebra K Ksep le_sup_left
  letI : IsScalarTower K jU₁.fieldRange C₀ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional jU₁.fieldRange C₀ := FiniteDimensional.right K _ _
  letI : Algebra I₀ jE.fieldRange :=
    intermediateFieldInclusionAlgebra K Ksep inf_le_right
  letI : IsScalarTower K I₀ jE.fieldRange :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional I₀ jE.fieldRange := FiniteDimensional.right K _ _
  have hrelative : Module.finrank jU₁.fieldRange C₀ =
      Module.finrank I₀ jE.fieldRange := by
    exact envelope_compositum_relative_finrank K Ksep jU₁.fieldRange jE.fieldRange
  have hfpos : 0 < f := by
    have hKE : 0 < Module.finrank K E := Module.finrank_pos
    have hprod : 0 < e * f := hEf.symm ▸ hKE
    exact Nat.pos_of_mul_pos_left hprod
  have hC₀mul : Module.finrank K C₀ * f = Module.finrank K W * f := by
    calc
      Module.finrank K C₀ * f =
          (Module.finrank K jU₁.fieldRange *
            Module.finrank jU₁.fieldRange C₀) * Module.finrank K I₀ := by
        rw [Module.finrank_mul_finrank K jU₁.fieldRange C₀, hintersectionI]
      _ = n * (Module.finrank I₀ jE.fieldRange * Module.finrank K I₀) := by
        rw [hrelative, ← jU₁.equivFieldRange.toLinearEquiv.finrank_eq]
        dsimp only [n]
        ac_rfl
      _ = n * Module.finrank K jE.fieldRange := by
        rw [mul_comm (Module.finrank I₀ jE.fieldRange),
          Module.finrank_mul_finrank K I₀ jE.fieldRange]
      _ = n * Module.finrank K E := by
        rw [← jE.equivFieldRange.toLinearEquiv.finrank_eq]
      _ = Module.finrank K W * f := by
        rw [← Module.finrank_mul_finrank K E W, TE.finrank (m - 1), hm]
        calc
          n * Module.finrank K E = Module.finrank K E * n := mul_comm _ _
          _ = Module.finrank K E * (m * f) := by rw [hmf]
          _ = (Module.finrank K E * m) * f := by ac_rfl
  have hC₀rankW : Module.finrank K C₀ = Module.finrank K W :=
    Nat.eq_of_mul_eq_mul_right hfpos hC₀mul
  let eWW : W ≃ₐ[K] W.restrictScalars K :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun x => by
        apply Subtype.ext
        exact jE.commutes x }
  letI : FiniteDimensional K (W.restrictScalars K) :=
    eWW.toLinearEquiv.finiteDimensional
  have hC₀rank : Module.finrank K C₀ = Module.finrank K (W.restrictScalars K) :=
    hC₀rankW.trans eWW.toLinearEquiv.finrank_eq
  have hC₀eq : C₀ = W.restrictScalars K :=
    IntermediateField.eq_of_le_of_finrank_eq hC₀W hC₀rank
  have hU₂W : jU₂.fieldRange ≤ W := by
    rw [hU₂range]
    apply TE.le_of_dvd
    have hre : r ∣ m := by exact dvd_mul_right r e
    simpa only [Nat.sub_add_cancel (Module.finrank_pos : 0 < r), hm] using hre
  let eU₁' : U₁ →ₐ[K] W.restrictScalars K :=
    jU₁.codRestrict (W.restrictScalars K).toSubalgebra (fun x => hU₁W ⟨x, rfl⟩)
  let eU₁ : U₁ →ₐ[K] W := eWW.symm.toAlgHom.comp eU₁'
  let eU₂ : U₂ →ₐ[E] W :=
    jU₂.codRestrict W.toSubalgebra (fun x => hU₂W ⟨x, rfl⟩)
  letI : Algebra U₁ W := eU₁.toRingHom.toAlgebra
  letI : IsScalarTower K U₁ W :=
    IsScalarTower.of_algebraMap_eq fun x => (eU₁.commutes x).symm
  letI : FiniteDimensional U₁ W := FiniteDimensional.right K U₁ W
  letI : ValuativeExtension U₁ W := envelopeValuativeExtension_of_tower K U₁ W
  letI : ContinuousSMul K W := by
    constructor
    have hKE : Continuous (algebraMap K E) := by
      have h := (continuous_smul : Continuous (fun p : K × E => p.1 • p.2)).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : K => (1 : E))))
      convert h using 1
      ext x
      simp only [Function.comp_apply, id_eq, Algebra.smul_def, mul_one]
    have hEW : Continuous (algebraMap E W) := by
      have h := (continuous_smul : Continuous (fun p : E × W => p.1 • p.2)).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : E => (1 : W))))
      convert h using 1
      ext x
      simp only [Function.comp_apply, id_eq, Algebra.smul_def, mul_one]
    have hKW : Continuous (algebraMap K W) := by
      convert hEW.comp hKE using 1
      ext x
      have hscalar : algebraMap K W x = algebraMap E W (algebraMap K E x) :=
        IsScalarTower.algebraMap_apply K E W x
      have hscalarAmbient :
          ((((algebraMap K W x : W) : Ksep) : AlgebraicClosure K)) =
            ((((algebraMap E W (algebraMap K E x) : W) : Ksep) : AlgebraicClosure K)) :=
        congrArg (fun z : W => (((z : Ksep) : AlgebraicClosure K))) hscalar
      exact hscalarAmbient
    have hcont : Continuous (fun p : K × W => algebraMap K W p.1 * p.2) :=
      (hKW.comp continuous_fst).mul continuous_snd
    simpa only [Algebra.smul_def] using hcont
  let hcontU₁ : Continuous eU₁ := by
    letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
    letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
    letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
    letI : UniformSpace U₁ := IsTopologicalAddGroup.rightUniformSpace U₁
    letI : IsUniformAddGroup U₁ := isUniformAddGroup_of_addCommGroup
    letI : ValuativeRel.IsNontrivial U₁ := IsNonarchimedeanLocalField.toIsNontrivial
    exact LinearMap.continuous_of_finiteDimensional (𝕜 := K) eU₁.toLinearMap
  letI : ContinuousSMul U₁ W := by
    constructor
    change Continuous (fun p : U₁ × W => eU₁ p.1 * p.2)
    exact (hcontU₁.comp continuous_fst).mul continuous_snd
  letI : Algebra U₂ W := eU₂.toRingHom.toAlgebra
  letI : IsScalarTower E U₂ W :=
    IsScalarTower.of_algebraMap_eq fun x => (eU₂.commutes x).symm
  letI : FiniteDimensional U₂ W := FiniteDimensional.right E U₂ W
  letI : ValuativeExtension U₂ W := envelopeValuativeExtension_of_tower E U₂ W
  let hcontU₂ : Continuous eU₂ := by
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    letI : (Valued.v (R := E) (Γ₀ := ValuativeRel.ValueGroupWithZero E)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := E).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField E :=
      Valued.toNontriviallyNormedField E (ValuativeRel.ValueGroupWithZero E)
    letI : UniformSpace U₂ := IsTopologicalAddGroup.rightUniformSpace U₂
    letI : IsUniformAddGroup U₂ := isUniformAddGroup_of_addCommGroup
    letI : ValuativeRel.IsNontrivial U₂ := IsNonarchimedeanLocalField.toIsNontrivial
    exact LinearMap.continuous_of_finiteDimensional (𝕜 := E) eU₂.toLinearMap
  letI : ContinuousSMul U₂ W := by
    constructor
    change Continuous (fun p : U₂ × W => eU₂ p.1 * p.2)
    exact (hcontU₂.comp continuous_fst).mul continuous_snd
  let EW : IntermediateField K W :=
    (IsScalarTower.toAlgHom K E W).fieldRange
  let UW : IntermediateField K W := eU₁.fieldRange
  let J : IntermediateField K W := UW ⊓ EW
  have heU₁ (u : U₁) : (eWW (eU₁ u) : W.restrictScalars K).1 = jU₁ u := by
    change (eWW (eWW.symm (eU₁' u)) : W.restrictScalars K).1 = jU₁ u
    rw [eWW.apply_symm_apply]
    rfl
  have hmapU : UW.map eWW.toAlgHom = jU₁.fieldRange.restrict hU₁W := by
    ext x
    simp only [IntermediateField.mem_map, UW, AlgHom.mem_fieldRange,
      IntermediateField.mem_restrict]
    constructor
    · rintro ⟨y, ⟨u, hu⟩, rfl⟩
      refine ⟨u, ?_⟩
      subst y
      exact (heU₁ u).symm
    · rintro ⟨u, hu⟩
      refine ⟨eU₁ u, ⟨u, rfl⟩, ?_⟩
      apply Subtype.ext
      exact (heU₁ u).trans hu
  have hmapE : EW.map eWW.toAlgHom = jE.fieldRange.restrict hEW := by
    ext x
    simp only [IntermediateField.mem_map, EW, AlgHom.mem_fieldRange,
      IntermediateField.mem_restrict]
    constructor
    · rintro ⟨y, ⟨z, hz⟩, rfl⟩
      refine ⟨z, ?_⟩
      subst y
      rfl
    · rintro ⟨z, hz⟩
      refine ⟨algebraMap E W z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hz
  have hmapTop : IntermediateField.map eWW.toAlgHom
      (⊤ : IntermediateField K W) = ⊤ := by
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_top, iff_true]
    exact ⟨eWW.symm x, trivial, eWW.apply_symm_apply x⟩
  have hsupW : UW ⊔ EW = ⊤ := by
    apply (IntermediateField.map_injective eWW.toAlgHom)
    rw [IntermediateField.map_sup, hmapU, hmapE, hmapTop]
    apply IntermediateField.lift_injective (W.restrictScalars K)
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
    exact hC₀eq
  have hmapJ : J.map eWW.toAlgHom =
      (jU₁.fieldRange.restrict hU₁W ⊓ jE.fieldRange.restrict hEW) := by
    change IntermediateField.map eWW.toAlgHom (UW ⊓ EW) = _
    rw [IntermediateField.map_inf, hmapU, hmapE]
  let J' : IntermediateField K (W.restrictScalars K) :=
    jU₁.fieldRange.restrict hU₁W ⊓ jE.fieldRange.restrict hEW
  have hliftJ' : IntermediateField.lift J' = I₀ := by
    change IntermediateField.lift
      (jU₁.fieldRange.restrict hU₁W ⊓ jE.fieldRange.restrict hEW) = I₀
    rw [IntermediateField.lift_inf, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict]
  have hJdegree : Module.finrank K J = f := by
    calc
      Module.finrank K J = Module.finrank K (J.map eWW.toAlgHom) :=
        (IntermediateField.equivMap J eWW.toAlgHom).toLinearEquiv.finrank_eq
      _ = Module.finrank K J' := by rw [hmapJ]
      _ = Module.finrank K (IntermediateField.lift J') :=
        (IntermediateField.liftAlgEquiv J').toLinearEquiv.finrank_eq
      _ = Module.finrank K I₀ := by rw [hliftJ']
      _ = f := hintersectionI
  have hcompositum :
      Algebra.adjoin K (Set.range (algebraMap E W) ∪ Set.range (algebraMap U₁ W)) = ⊤ := by
    apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)).mp
    change EW ⊔ UW = ⊤
    rw [sup_comm]
    exact hsupW
  have hmemJ : ∀ x : W, x ∈ J ↔
      (∃ z : E, algebraMap E W z = x) ∧
        (∃ u : U₁, algebraMap U₁ W u = x) := by
    intro x
    change (x ∈ UW ∧ x ∈ EW) ↔ _
    simp only [UW, EW, AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨z, hz⟩⟩
      exact ⟨⟨z, hz⟩, ⟨u, hu⟩⟩
    · rintro ⟨⟨z, hz⟩, ⟨u, hu⟩⟩
      exact ⟨⟨u, hu⟩, ⟨z, hz⟩⟩
  let common : UnramifiedCyclicExtensionData E W :=
    envelopeTowerUnramifiedCyclicData E Ksep TE (m - 1)
  have hsourceDegree : Module.finrank K U₁ =
      Module.finrank E U₂ * Module.finrank K E := by
    rw [D₁.source_degree, D₂.source_degree, mul_comm,
      Module.finrank_mul_finrank K E L]
  have hcommonDegree : Module.finrank E W * Module.finrank K J =
      Module.finrank K U₁ := by
    rw [TE.finrank (m - 1), hm, hJdegree]
    exact hmf.trans rfl
  have htargetDegree : Module.finrank E U₂ ∣ Module.finrank E W := by
    rw [TE.finrank (m - 1), hm]
    exact dvd_mul_right r e
  obtain ⟨B, hBS, hBW, hBT, hBI⟩ := carryBaseChangeData_exists
    K E U₁ U₂ W D₁.source common D₂.source hcompositum J hmemJ hJdegree
      hsourceDegree hcommonDegree htargetDegree
  let C₁ : UnramifiedClassData K U₁ B.source πK := hBS.symm ▸ D₁.sourceClass
  let C₂ : UnramifiedClassData E U₂ B.target πE := hBT.symm ▸ D₂.sourceClass
  letI : Algebra E M₁ :=
    ((algebraMap L M₁).comp (algebraMap E L)).toAlgebra
  letI : IsScalarTower E L M₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K E M₁ := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap K M₁ x = algebraMap L M₁ (algebraMap K L x) :=
        IsScalarTower.algebraMap_apply K L M₁ x
      _ = algebraMap L M₁ (algebraMap E L (algebraMap K E x)) := by
        rw [IsScalarTower.algebraMap_apply K E L]
      _ = algebraMap E M₁ (algebraMap K E x) := rfl
  letI : FiniteDimensional E M₁ := FiniteDimensional.right K E M₁
  letI : IsGalois E M₁ := IsGalois.tower_top_of_isGalois K E M₁
  let jM₁K : M₁ →ₐ[K] Ksep := jM₁.restrictScalars K
  let jM₁E : M₁ →ₐ[E] Ksep := jM₁.restrictScalars E
  have hU₁M₁range : jU₁.fieldRange ≤ jM₁K.fieldRange := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact ⟨algebraMap U₁ M₁ u, rfl⟩
  have hEM₁range : jE.fieldRange ≤ jM₁K.fieldRange := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨algebraMap L M₁ (algebraMap E L z), ?_⟩
    exact jM₁.commutes (algebraMap E L z)
  have hC₀M₁ : C₀ ≤ jM₁K.fieldRange :=
    sup_le hU₁M₁range hEM₁range
  have hWM₁range : W ≤ jM₁E.fieldRange := by
    intro x hx
    have hxW : (x : Ksep) ∈ W.restrictScalars K := hx
    have hxC₀ : (x : Ksep) ∈ C₀ := by
      rw [hC₀eq]
      exact hxW
    obtain ⟨y, hy⟩ := hC₀M₁ hxC₀
    exact ⟨y, hy⟩
  let eW : W →ₐ[E] M₁ :=
    (jM₁E.equivFieldRange.symm.toAlgHom).comp
      (IntermediateField.inclusion hWM₁range)
  have heW (w : W) : jM₁E (eW w) = (w : Ksep) := by
    change jM₁E (jM₁E.equivFieldRange.symm
      ((IntermediateField.inclusion hWM₁range) w)) = (w : Ksep)
    exact congrArg Subtype.val (jM₁E.equivFieldRange.apply_symm_apply
      ((IntermediateField.inclusion hWM₁range) w))
  letI : Algebra W M₁ := eW.toRingHom.toAlgebra
  letI : IsScalarTower E W M₁ :=
    IsScalarTower.of_algebraMap_eq fun x => (eW.commutes x).symm
  letI : FiniteDimensional W M₁ := FiniteDimensional.right E W M₁
  letI : IsGalois W M₁ := IsGalois.tower_top_of_isGalois E W M₁
  have heU₁Ksep (u : U₁) : ((eU₁ u : W) : Ksep) = jU₁ u := heU₁ u
  letI : IsScalarTower U₁ W M₁ := IsScalarTower.of_algebraMap_eq fun u => by
    apply jM₁E.injective
    have hleft : jM₁E (algebraMap U₁ M₁ u) = jU₁ u := rfl
    have hright : jM₁E (algebraMap W M₁ (algebraMap U₁ W u)) =
        ((eU₁ u : W) : Ksep) := heW (eU₁ u)
    exact hleft.trans ((heU₁Ksep u).symm.trans hright.symm)
  let jLE : L →ₐ[E] Ksep :=
    { jL.toRingHom with
      commutes' := fun _ => rfl }
  let jM₂E : M₂ →ₐ[E] Ksep := jM₂.restrictScalars E
  have hjLE (l : L) : jLE l = jL l := rfl
  have hM₂range_eq : jM₂E.fieldRange = jLE.fieldRange ⊔ jU₂.fieldRange := by
    apply envelopeRange_eq E L U₂ M₂ Ksep jLE jM₂
      (fun l => (jM₂.commutes l).trans (hjLE l).symm)
      D₂.compositum_eq_top jU₂.fieldRange
    rfl
  have hLM₁range : jLE.fieldRange ≤ jM₁E.fieldRange := by
    intro x hx
    obtain ⟨l, rfl⟩ := hx
    refine ⟨algebraMap L M₁ l, ?_⟩
    exact (jM₁.commutes l).trans (hjLE l).symm
  have hU₂M₁range : jU₂.fieldRange ≤ jM₁E.fieldRange :=
    hU₂W.trans hWM₁range
  have hM₂M₁range : jM₂E.fieldRange ≤ jM₁E.fieldRange := by
    rw [hM₂range_eq]
    exact sup_le hLM₁range hU₂M₁range
  let eM : M₂ →ₐ[E] M₁ :=
    (jM₁E.equivFieldRange.symm.toAlgHom).comp
      ((IntermediateField.inclusion hM₂M₁range).comp
        jM₂E.equivFieldRange.toAlgHom)
  have heM (x : M₂) : jM₁E (eM x) = jM₂E x := by
    change jM₁E (jM₁E.equivFieldRange.symm
      ((IntermediateField.inclusion hM₂M₁range) (jM₂E.equivFieldRange x))) = jM₂E x
    exact congrArg Subtype.val (jM₁E.equivFieldRange.apply_symm_apply
      ((IntermediateField.inclusion hM₂M₁range) (jM₂E.equivFieldRange x)))
  letI : Algebra M₂ M₁ := eM.toRingHom.toAlgebra
  letI : IsScalarTower E M₂ M₁ :=
    IsScalarTower.of_algebraMap_eq fun x => (eM.commutes x).symm
  letI : FiniteDimensional M₂ M₁ := FiniteDimensional.right E M₂ M₁
  letI : IsGalois M₂ M₁ := IsGalois.tower_top_of_isGalois E M₂ M₁
  have hLM (l : L) : eM (algebraMap L M₂ l) = algebraMap L M₁ l := by
    apply jM₁E.injective
    calc
      jM₁E (eM (algebraMap L M₂ l)) = jM₂E (algebraMap L M₂ l) := heM _
      _ = jLE l := (jM₂.commutes l).trans (hjLE l).symm
      _ = jM₁E (algebraMap L M₁ l) :=
        ((jM₁.commutes l).trans (hjLE l).symm).symm
  letI : IsScalarTower L M₂ M₁ :=
    IsScalarTower.of_algebraMap_eq fun l => (hLM l).symm
  letI : Algebra U₂ M₁ :=
    ((algebraMap W M₁).comp (algebraMap U₂ W)).toAlgebra
  letI : IsScalarTower U₂ W M₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower E U₂ M₁ := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap E M₁ x = algebraMap W M₁ (algebraMap E W x) :=
        IsScalarTower.algebraMap_apply E W M₁ x
      _ = algebraMap W M₁ (algebraMap U₂ W (algebraMap E U₂ x)) := by
        rw [IsScalarTower.algebraMap_apply E U₂ W]
      _ = algebraMap U₂ M₁ (algebraMap E U₂ x) := rfl
  have hU₂M₁Ksep (u : U₂) : jM₁E (algebraMap U₂ M₁ u) = jU₂ u := by
    calc
      jM₁E (algebraMap U₂ M₁ u) = ((eU₂ u : W) : Ksep) := heW (eU₂ u)
      _ = jU₂ u := rfl
  have hUM (u : U₂) : eM (algebraMap U₂ M₂ u) = algebraMap U₂ M₁ u := by
    apply jM₁E.injective
    calc
      jM₁E (eM (algebraMap U₂ M₂ u)) = jM₂E (algebraMap U₂ M₂ u) := heM _
      _ = jU₂ u := rfl
      _ = jM₁E (algebraMap U₂ M₁ u) := (hU₂M₁Ksep u).symm
  letI : IsScalarTower U₂ M₂ M₁ :=
    IsScalarTower.of_algebraMap_eq fun u => (hUM u).symm
  have hC₁class : C₁.class = D₁.sourceClass.class :=
    unramifiedClassData_transport_class hBS.symm πK D₁.sourceClass
  have hC₂class : C₂.class = D₂.sourceClass.class :=
    unramifiedClassData_transport_class hBT.symm πE D₂.sourceClass
  have hbase :
      transportedH2 B.sourceGroupHom B.sourceCoefficient C₁.class =
        transportedH2 B.targetGroupHom B.targetCoefficient C₂.class :=
    (carryClass_baseChange K E U₁ U₂ W B πK πE C₁ C₂).2
  have hD₁descentQ : D₁.descentQuotient = towerQuotientHom K L M₁ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M₁).injective
    exact (D₁.descentQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ L x).symm
  have hD₁descentC : ∀ x : (MulRep K L).V,
      D₁.descentCoefficient.hom x = (towerInflationCoefficient K L M₁).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₁.descentCoefficient_apply (Additive.toMul x)
  have hD₁descentMap (x : Inhomogeneous.H2 (MulRep K L)) :
      transportedH2 D₁.descentQuotient D₁.descentCoefficient x =
        transportedH2 (towerQuotientHom K L M₁)
          (towerInflationCoefficient K L M₁) x :=
    envelopeTransportedH2_congr D₁.descentCoefficient
      (towerInflationCoefficient K L M₁) hD₁descentQ hD₁descentC x
  have hD₁sourceQ : D₁.sourceQuotient = towerQuotientHom K U₁ M₁ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U₁ M₁).injective
    exact (D₁.sourceQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ U₁ x).symm
  have hD₁sourceC : ∀ x : (MulRep K U₁).V,
      D₁.sourceCoefficient.hom x = (towerInflationCoefficient K U₁ M₁).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₁.sourceCoefficient_apply (Additive.toMul x)
  have hD₁sourceMap :
      transportedH2 D₁.sourceQuotient D₁.sourceCoefficient D₁.sourceClass.class =
        transportedH2 (towerQuotientHom K U₁ M₁)
          (towerInflationCoefficient K U₁ M₁) D₁.sourceClass.class :=
    envelopeTransportedH2_congr D₁.sourceCoefficient
      (towerInflationCoefficient K U₁ M₁) hD₁sourceQ hD₁sourceC _
  have hdesc₁ :
      transportedH2 (towerQuotientHom K L M₁) (towerInflationCoefficient K L M₁)
          (fundamentalClassValue K L) =
        transportedH2 (towerQuotientHom K U₁ M₁) (towerInflationCoefficient K U₁ M₁)
          D₁.sourceClass.class := by
    calc
      _ = transportedH2 D₁.descentQuotient D₁.descentCoefficient
          (fundamentalClassValue K L) := (hD₁descentMap _).symm
      _ = D₁.psi := (fundamentalClass K L).descends πK U₁ M₁ D₁
      _ = transportedH2 D₁.sourceQuotient D₁.sourceCoefficient
          D₁.sourceClass.class := D₁.psi_eq_inflated
      _ = _ := hD₁sourceMap
  have hD₂descentQ : D₂.descentQuotient = towerQuotientHom E L M₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M₂).injective
    exact (D₂.descentQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ L x).symm
  have hD₂descentC : ∀ x : (MulRep E L).V,
      D₂.descentCoefficient.hom x = (towerInflationCoefficient E L M₂).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₂.descentCoefficient_apply (Additive.toMul x)
  have hD₂descentMap (x : Inhomogeneous.H2 (MulRep E L)) :
      transportedH2 D₂.descentQuotient D₂.descentCoefficient x =
        transportedH2 (towerQuotientHom E L M₂)
          (towerInflationCoefficient E L M₂) x :=
    envelopeTransportedH2_congr D₂.descentCoefficient
      (towerInflationCoefficient E L M₂) hD₂descentQ hD₂descentC x
  have hD₂sourceQ : D₂.sourceQuotient = towerQuotientHom E U₂ M₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U₂ M₂).injective
    exact (D₂.sourceQuotient_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ U₂ x).symm
  have hD₂sourceC : ∀ x : (MulRep E U₂).V,
      D₂.sourceCoefficient.hom x = (towerInflationCoefficient E U₂ M₂).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact D₂.sourceCoefficient_apply (Additive.toMul x)
  have hD₂sourceMap :
      transportedH2 D₂.sourceQuotient D₂.sourceCoefficient D₂.sourceClass.class =
        transportedH2 (towerQuotientHom E U₂ M₂)
          (towerInflationCoefficient E U₂ M₂) D₂.sourceClass.class :=
    envelopeTransportedH2_congr D₂.sourceCoefficient
      (towerInflationCoefficient E U₂ M₂) hD₂sourceQ hD₂sourceC _
  have hdesc₂ :
      transportedH2 (towerQuotientHom E L M₂) (towerInflationCoefficient E L M₂)
          (fundamentalClassValue E L) =
        transportedH2 (towerQuotientHom E U₂ M₂) (towerInflationCoefficient E U₂ M₂)
          D₂.sourceClass.class := by
    calc
      _ = transportedH2 D₂.descentQuotient D₂.descentCoefficient
          (fundamentalClassValue E L) := (hD₂descentMap _).symm
      _ = D₂.psi := (fundamentalClass E L).descends πE U₂ M₂ D₂
      _ = transportedH2 D₂.sourceQuotient D₂.sourceCoefficient
          D₂.sourceClass.class := D₂.psi_eq_inflated
      _ = _ := hD₂sourceMap
  have hBtargetQ : B.targetGroupHom = towerQuotientHom E U₂ W := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply (algebraMap U₂ W).injective
    exact (B.targetGroupHom_apply σ x).trans
      (AlgEquiv.restrictNormal_commutes σ U₂ x).symm
  have hBtargetC : ∀ x : (MulRep E U₂).V,
      B.targetCoefficient.hom x = (towerInflationCoefficient E U₂ W).hom x := by
    intro x
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
    apply Additive.toMul.injective
    exact B.targetCoefficient_apply (Additive.toMul x)
  have htargetW :
      transportedH2 B.targetGroupHom B.targetCoefficient C₂.class =
        transportedH2 (towerQuotientHom E U₂ W)
          (towerInflationCoefficient E U₂ W) C₂.class :=
    envelopeTransportedH2_congr B.targetCoefficient
      (towerInflationCoefficient E U₂ W) hBtargetQ hBtargetC C₂.class
  let qS₁ := (towerQuotientHom K U₁ M₁).comp (towerSubgroupHom K E M₁)
  let cS₁ := (Rep.resFunctor (towerSubgroupHom K E M₁)).map
      (towerInflationCoefficient K U₁ M₁) ≫ towerRestrictionCoefficient K E M₁
  let qS₂ := B.sourceGroupHom.comp (towerQuotientHom E W M₁)
  let cS₂ := (Rep.resFunctor (towerQuotientHom E W M₁)).map
      B.sourceCoefficient ≫ towerInflationCoefficient E W M₁
  have hqS : qS₁ = qS₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro u
    apply (algebraMap U₁ M₁).injective
    calc
      algebraMap U₁ M₁ (qS₁ σ u) = σ (algebraMap U₁ M₁ u) :=
        AlgEquiv.restrictNormal_commutes (towerSubgroupHom K E M₁ σ) U₁ u
      _ = σ (algebraMap W M₁ (algebraMap U₁ W u)) := by
        rw [← IsScalarTower.algebraMap_apply U₁ W M₁]
      _ = algebraMap W M₁
          ((towerQuotientHom E W M₁ σ) (algebraMap U₁ W u)) :=
        (AlgEquiv.restrictNormal_commutes σ W (algebraMap U₁ W u)).symm
      _ = algebraMap W M₁
          (algebraMap U₁ W (B.sourceGroupHom (towerQuotientHom E W M₁ σ) u)) :=
        congrArg (algebraMap W M₁)
          (B.sourceGroupHom_apply (towerQuotientHom E W M₁ σ) u).symm
      _ = algebraMap U₁ M₁ (qS₂ σ u) :=
        (IsScalarTower.algebraMap_apply U₁ W M₁ _).symm
  have hcS : ∀ x : (MulRep K U₁).V, cS₁.hom x = cS₂.hom x := by
    intro x
    have hleft : Additive.toMul (cS₁.hom x) =
        Units.map (algebraMap U₁ M₁) (Additive.toMul x) := rfl
    have hsource : Additive.toMul (B.sourceCoefficient.hom x) =
        Units.map (algebraMap U₁ W) (Additive.toMul x) := by
      rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
      exact B.sourceCoefficient_apply (Additive.toMul x)
    have hright : Additive.toMul (cS₂.hom x) =
        Units.map (algebraMap W M₁) (Additive.toMul (B.sourceCoefficient.hom x)) := rfl
    apply Additive.toMul.injective
    calc
      Additive.toMul (cS₁.hom x) =
          Units.map (algebraMap U₁ M₁) (Additive.toMul x) := hleft
      _ = Units.map (algebraMap W M₁)
          (Units.map (algebraMap U₁ W) (Additive.toMul x)) := by
        apply Units.ext
        exact IsScalarTower.algebraMap_apply U₁ W M₁ _
      _ = Units.map (algebraMap W M₁)
          (Additive.toMul (B.sourceCoefficient.hom x)) := by
        have hmapped :
            Units.map (algebraMap W M₁).toMonoidHom
                (Units.map (algebraMap U₁ W) (Additive.toMul x)) =
              Units.map (algebraMap W M₁).toMonoidHom
                (Additive.toMul (B.sourceCoefficient.hom x)) :=
          congrArg (Units.map (algebraMap W M₁).toMonoidHom) hsource.symm
        exact hmapped
      _ = Additive.toMul (cS₂.hom x) := hright.symm
  have hsourceTop (x : Inhomogeneous.H2 (MulRep K U₁)) :
      transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K U₁ M₁)
            (towerInflationCoefficient K U₁ M₁) x) =
        transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 B.sourceGroupHom B.sourceCoefficient x) := by
    have hleft :
        transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
            (transportedH2 (towerQuotientHom K U₁ M₁)
              (towerInflationCoefficient K U₁ M₁) x) =
          transportedH2 qS₁ cS₁ x :=
      transportedH2_comp (towerQuotientHom K U₁ M₁) (towerSubgroupHom K E M₁)
        (towerInflationCoefficient K U₁ M₁) (towerRestrictionCoefficient K E M₁) x
    have hmiddle : transportedH2 qS₁ cS₁ x = transportedH2 qS₂ cS₂ x :=
      envelopeTransportedH2_congr
        (G := U₁ ≃ₐ[K] U₁) (H := M₁ ≃ₐ[E] M₁)
        (A := MulRep K U₁) (B := MulRep E M₁)
        (f := qS₁) (g := qS₂) cS₁ cS₂ hqS hcS x
    have hright :
        transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
            (transportedH2 B.sourceGroupHom B.sourceCoefficient x) =
          transportedH2 qS₂ cS₂ x :=
      transportedH2_comp B.sourceGroupHom (towerQuotientHom E W M₁)
        B.sourceCoefficient (towerInflationCoefficient E W M₁) x
    exact hleft.trans (hmiddle.trans hright.symm)
  let qL₁ := (towerQuotientHom E L M₂).comp (towerQuotientHom E M₂ M₁)
  let cL₁ := (Rep.resFunctor (towerQuotientHom E M₂ M₁)).map
      (towerInflationCoefficient E L M₂) ≫ towerInflationCoefficient E M₂ M₁
  let qL₂ := towerQuotientHom E L M₁
  let cL₂ := towerInflationCoefficient E L M₁
  have hqL : qL₁ = qL₂ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro l
    apply (algebraMap L M₁).injective
    calc
      algebraMap L M₁ (qL₁ σ l) =
          algebraMap M₂ M₁ (algebraMap L M₂ (qL₁ σ l)) :=
        IsScalarTower.algebraMap_apply L M₂ M₁ _
      _ = algebraMap M₂ M₁
          ((towerQuotientHom E M₂ M₁ σ) (algebraMap L M₂ l)) :=
        congrArg (algebraMap M₂ M₁)
          (AlgEquiv.restrictNormal_commutes (towerQuotientHom E M₂ M₁ σ) L l)
      _ = σ (algebraMap M₂ M₁ (algebraMap L M₂ l)) :=
        AlgEquiv.restrictNormal_commutes σ M₂ (algebraMap L M₂ l)
      _ = σ (algebraMap L M₁ l) := by
        rw [← IsScalarTower.algebraMap_apply L M₂ M₁]
      _ = algebraMap L M₁ (qL₂ σ l) :=
        (AlgEquiv.restrictNormal_commutes σ L l).symm
  have hcL : ∀ x : (MulRep E L).V, cL₁.hom x = cL₂.hom x := by
    intro x
    have hleft : Additive.toMul (cL₁.hom x) =
        Units.map (algebraMap M₂ M₁).toMonoidHom
          (Units.map (algebraMap L M₂).toMonoidHom (Additive.toMul x)) := rfl
    have hright : Additive.toMul (cL₂.hom x) =
        Units.map (algebraMap L M₁).toMonoidHom (Additive.toMul x) := rfl
    apply Additive.toMul.injective
    calc
      Additive.toMul (cL₁.hom x) =
          Units.map (algebraMap M₂ M₁)
            (Units.map (algebraMap L M₂) (Additive.toMul x)) := hleft
      _ = Units.map (algebraMap L M₁) (Additive.toMul x) := by
        apply Units.ext
        exact (IsScalarTower.algebraMap_apply L M₂ M₁ _).symm
      _ = Additive.toMul (cL₂.hom x) := hright.symm
  have hLtop (x : Inhomogeneous.H2 (MulRep E L)) :
      transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E L M₂)
            (towerInflationCoefficient E L M₂) x) =
        transportedH2 (towerQuotientHom E L M₁)
          (towerInflationCoefficient E L M₁) x := by
    have hcomp :
        transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
            (transportedH2 (towerQuotientHom E L M₂)
              (towerInflationCoefficient E L M₂) x) =
          transportedH2 qL₁ cL₁ x :=
      transportedH2_comp (towerQuotientHom E L M₂) (towerQuotientHom E M₂ M₁)
        (towerInflationCoefficient E L M₂) (towerInflationCoefficient E M₂ M₁) x
    have hcongr : transportedH2 qL₁ cL₁ x = transportedH2 qL₂ cL₂ x :=
      envelopeTransportedH2_congr
        (G := L ≃ₐ[E] L) (H := M₁ ≃ₐ[E] M₁)
        (A := MulRep E L) (B := MulRep E M₁)
        (f := qL₁) (g := qL₂) cL₁ cL₂ hqL hcL x
    exact hcomp.trans hcongr
  have htargetDiamond :
      transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E U₂ M₂)
            (towerInflationCoefficient E U₂ M₂) C₂.class) =
        transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 (towerQuotientHom E U₂ W)
            (towerInflationCoefficient E U₂ W) C₂.class) :=
    towerInflation_diamond E U₂ M₂ W M₁ C₂.class
  have hdesc₁Top :
      transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K L M₁)
            (towerInflationCoefficient K L M₁) (fundamentalClassValue K L)) =
        transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K U₁ M₁)
            (towerInflationCoefficient K U₁ M₁) D₁.sourceClass.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep K M₁) =>
        transportedH2 (towerSubgroupHom K E M₁)
          (towerRestrictionCoefficient K E M₁) z) hdesc₁
  have hC₁Top :
      transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K U₁ M₁)
            (towerInflationCoefficient K U₁ M₁) C₁.class) =
        transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K U₁ M₁)
            (towerInflationCoefficient K U₁ M₁) D₁.sourceClass.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep K U₁) =>
        transportedH2 (towerSubgroupHom K E M₁)
          (towerRestrictionCoefficient K E M₁)
          (transportedH2 (towerQuotientHom K U₁ M₁)
            (towerInflationCoefficient K U₁ M₁) z)) hC₁class
  have hbaseTop :
      transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 B.sourceGroupHom B.sourceCoefficient C₁.class) =
        transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 B.targetGroupHom B.targetCoefficient C₂.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep E W) =>
        transportedH2 (towerQuotientHom E W M₁)
          (towerInflationCoefficient E W M₁) z) hbase
  have htargetWTop :
      transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 B.targetGroupHom B.targetCoefficient C₂.class) =
        transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
          (transportedH2 (towerQuotientHom E U₂ W)
            (towerInflationCoefficient E U₂ W) C₂.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep E W) =>
        transportedH2 (towerQuotientHom E W M₁)
          (towerInflationCoefficient E W M₁) z) htargetW
  have hC₂Top :
      transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E U₂ M₂)
            (towerInflationCoefficient E U₂ M₂) C₂.class) =
        transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E U₂ M₂)
            (towerInflationCoefficient E U₂ M₂) D₂.sourceClass.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep E U₂) =>
        transportedH2 (towerQuotientHom E M₂ M₁)
          (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E U₂ M₂)
            (towerInflationCoefficient E U₂ M₂) z)) hC₂class
  have hdesc₂Top :
      transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E L M₂)
            (towerInflationCoefficient E L M₂) (fundamentalClassValue E L)) =
        transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
          (transportedH2 (towerQuotientHom E U₂ M₂)
            (towerInflationCoefficient E U₂ M₂) D₂.sourceClass.class) :=
    congrArg
      (fun z : Inhomogeneous.H2 (MulRep E M₂) =>
        transportedH2 (towerQuotientHom E M₂ M₁)
          (towerInflationCoefficient E M₂ M₁) z) hdesc₂
  apply (towerTransportedH2_infRes E L M₁).1
  calc
    transportedH2 (towerQuotientHom E L M₁) (towerInflationCoefficient E L M₁)
        (transportedH2 (towerSubgroupHom K E L) (towerRestrictionCoefficient K E L)
          (fundamentalClassValue K L)) =
      transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
        (transportedH2 (towerQuotientHom K L M₁) (towerInflationCoefficient K L M₁)
          (fundamentalClassValue K L)) :=
      towerRestriction_inflation_square K E L M₁ (fundamentalClassValue K L)
    _ = transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
        (transportedH2 (towerQuotientHom K U₁ M₁) (towerInflationCoefficient K U₁ M₁)
          D₁.sourceClass.class) := hdesc₁Top
    _ = transportedH2 (towerSubgroupHom K E M₁) (towerRestrictionCoefficient K E M₁)
        (transportedH2 (towerQuotientHom K U₁ M₁) (towerInflationCoefficient K U₁ M₁)
          C₁.class) := hC₁Top.symm
    _ = transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
        (transportedH2 B.sourceGroupHom B.sourceCoefficient C₁.class) :=
      hsourceTop C₁.class
    _ = transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
        (transportedH2 B.targetGroupHom B.targetCoefficient C₂.class) := hbaseTop
    _ = transportedH2 (towerQuotientHom E W M₁) (towerInflationCoefficient E W M₁)
        (transportedH2 (towerQuotientHom E U₂ W)
          (towerInflationCoefficient E U₂ W) C₂.class) := htargetWTop
    _ = transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
        (transportedH2 (towerQuotientHom E U₂ M₂)
          (towerInflationCoefficient E U₂ M₂) C₂.class) := htargetDiamond.symm
    _ = transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
        (transportedH2 (towerQuotientHom E U₂ M₂)
          (towerInflationCoefficient E U₂ M₂) D₂.sourceClass.class) := hC₂Top
    _ = transportedH2 (towerQuotientHom E M₂ M₁) (towerInflationCoefficient E M₂ M₁)
        (transportedH2 (towerQuotientHom E L M₂) (towerInflationCoefficient E L M₂)
          (fundamentalClassValue E L)) := hdesc₂Top.symm
    _ = transportedH2 (towerQuotientHom E L M₁) (towerInflationCoefficient E L M₁)
        (fundamentalClassValue E L) := hLtop (fundamentalClassValue E L)

/-- The remaining descended F07 base-change face, stated with the literal tower maps. -/
private theorem fundamentalRestriction_descended_baseChange_face :
    transportedH2 (towerSubgroupHom K E L) (towerRestrictionCoefficient K E L)
        (fundamentalClassValue K L) = fundamentalClassValue E L := by
  exact fundamentalRestriction_descended_baseChange_face_aux K L E

/-- The actual F09 restriction square obtained from the F07 base-change carry identity. -/
private theorem actualFundamentalRestriction_square :
    transportedH2 (actualFundamentalRestrictionData K L E).subgroupHom
        (actualFundamentalRestrictionData K L E).coefficient (fundamentalClassValue K L) =
      fundamentalClassValue E L := by
  change transportedH2 (towerSubgroupHom K E L) (towerRestrictionCoefficient K E L)
      (fundamentalClassValue K L) = fundamentalClassValue E L
  exact fundamentalRestriction_descended_baseChange_face K L E

/--
**F09**, Proposition `prop:fundamental-restriction`: actual subgroup restriction sends
`α_{L/K}` to `α_{L/E}`.  This is the descended form of the **F07** base-change carry formula.
-/
theorem fundamentalClass_restriction :
    ∃ D : FundamentalRestrictionData K L E,
      transportedH2 D.subgroupHom D.coefficient (fundamentalClassValue K L) =
        fundamentalClassValue E L := by
  exact ⟨actualFundamentalRestrictionData K L E,
    actualFundamentalRestriction_square K L E⟩

private theorem fundamentalClass_restriction_systemField :
    ∃ (s : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))
      (c : Rep.res s (MulRep K L) ⟶ MulRep E L),
      (∀ (σ : L ≃ₐ[E] L) (x : L), s σ x = σ x) ∧
      (∀ x : Units L, c.hom (Additive.ofMul x) = Additive.ofMul x) ∧
      transportedH2 s c (fundamentalClassValue K L) = fundamentalClassValue E L := by
  obtain ⟨D, hD⟩ := fundamentalClass_restriction K L E
  exact ⟨D.subgroupHom, D.coefficient, D.subgroupHom_apply,
    D.coefficient_apply, hD⟩

end Restriction

private theorem descendsFromUnramifiedEnvelopes_unique
    (α β : Inhomogeneous.H2 (MulRep K L))
    (hα : DescendsFromUnramifiedEnvelopes K L α)
    (hβ : DescendsFromUnramifiedEnvelopes K L β) : α = β := by
  classical
  let π := defaultUniformizer K
  obtain ⟨U, M, fU, fM, aKU, aKM, aLM, aUM, stKLM, stKUM,
      fdKU, fdKM, fdLM, fdUM, galKU, galKM, galLM,
      vU, tU, locU, vM, tM, locM, veKU, veKM, veLM, veUM,
      csKU, csKM, csLM, csUM, hD⟩ :=
    unramifiedEnvelope_descentData K L π
  letI : Field U := fU
  letI : Field M := fM
  letI : Algebra K U := aKU
  letI : Algebra K M := aKM
  letI : Algebra L M := aLM
  letI : Algebra U M := aUM
  letI : IsScalarTower K L M := stKLM
  letI : IsScalarTower K U M := stKUM
  letI : FiniteDimensional K U := fdKU
  letI : FiniteDimensional K M := fdKM
  letI : FiniteDimensional L M := fdLM
  letI : FiniteDimensional U M := fdUM
  letI : IsGalois K U := galKU
  letI : IsGalois K M := galKM
  letI : IsGalois L M := galLM
  letI : ValuativeRel U := vU
  letI : TopologicalSpace U := tU
  letI : IsNonarchimedeanLocalField U := locU
  letI : ValuativeRel M := vM
  letI : TopologicalSpace M := tM
  letI : IsNonarchimedeanLocalField M := locM
  letI : ValuativeExtension K U := veKU
  letI : ValuativeExtension K M := veKM
  letI : ValuativeExtension L M := veLM
  letI : ValuativeExtension U M := veUM
  letI : ContinuousSMul K U := csKU
  letI : ContinuousSMul K M := csKM
  letI : ContinuousSMul L M := csLM
  letI : ContinuousSMul U M := csUM
  obtain ⟨D⟩ := hD
  apply D.descent_injective
  exact (hα π U M D).trans (hβ π U M D).symm

/-- The system is a final aggregate of independently constructed envelope and F09 data. -/
private theorem fundamentalClassSystem_exists : Nonempty FundamentalClassSystem := by
  refine ⟨{
    value := fundamentalClassValue
    envelope_exists := unramifiedEnvelope_descentData
    descends := ?_
    descends_unique := ?_
    order_value := ?_
    inflation := ?_
    restriction := ?_ }⟩
  · intro K L _ _ _ _ _ _ _ _ _ _ _ _ _
    exact (fundamentalClass K L).descends
  · intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ α hα
    exact descendsFromUnramifiedEnvelopes_unique K L α (fundamentalClassValue K L)
      hα (fundamentalClass K L).descends
  · intro K L _ _ _ _ _ _ _ _ _ _ _ _ _
    exact (fundamentalClass K L).order_class
  · intro K L E
    intros
    exact fundamentalClass_inflation_systemField K L E
  · intro K E L
    intros
    exact fundamentalClass_restriction_systemField K L E

end

end NU.LCFT
