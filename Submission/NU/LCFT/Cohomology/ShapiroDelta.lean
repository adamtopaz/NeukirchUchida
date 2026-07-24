import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Compatibility of Shapiro's isomorphism with connecting morphisms

This file proves that Mathlib's concrete `groupCohomology.coindIso` intertwines the connecting
morphisms of a short exact sequence with those of its coinduction.  The proof identifies
Shapiro's inverse with the map on homology induced by a natural cochain map.  The only delicate
step unfolds `ProjectiveResolution.isoExt` and uses naturality of the chosen comparison between
projective resolutions.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- Compatibility shim for the restriction exactness API added after the pinned Mathlib commit. -/
lemma _root_.Rep.shortExact_res
    {H G : Type} [Group H] [Group G] (φ : H →* G)
    {X : ShortComplex (Rep ℤ G)} :
    (X.map (Rep.resFunctor φ)).ShortExact ↔ X.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, Rep.mono_iff_injective, ShortComplex.map_g,
      Rep.epi_iff_surjective] at h₂ h₃
    exact { exact := h₁
            mono_f := (Rep.mono_iff_injective _).2 h₂
            epi_g := (Rep.epi_iff_surjective _).2 h₃ }
  · rintro @⟨_, mono_f, epi_g⟩
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa [Rep.mono_iff_injective] using! mono_f
      epi_g := by simpa [Rep.epi_iff_surjective] using! epi_g
    }

private noncomputable def precompLinearYonedaObj
    {k : Type u} {C : Type v} [Ring k] [Category C] [Abelian C] [Linear k C]
    {P Q : ChainComplex C ℕ} (q : P ⟶ Q) (A : C) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    ((((((CategoryTheory.linearYoneda k C).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map q)).op)

private noncomputable def postcompLinearYonedaObj
    {k : Type u} {C : Type v} [Ring k] [Category C] [Abelian C] [Linear k C]
    (P : ChainComplex C ℕ) {A B : C} (f : A ⟶ B) :
    P.linearYonedaObj k A ⟶ P.linearYonedaObj k B :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    (((NatTrans.mapHomologicalComplex
      ((CategoryTheory.linearYoneda k C).map f).rightOp (ComplexShape.down ℕ)).app P).op)

private abbrev repLinearYonedaObj
    {H : Type} [Group H] (P : ChainComplex (Rep ℤ H) ℕ) (A : Rep ℤ H) :=
  @ChainComplex.linearYonedaObj (Rep ℤ H) _ _ ℕ _ _ P ℤ _ Rep.instLinear A

private noncomputable abbrev repIsoExt
    {H : Type} [Group H] {X : Rep ℤ H} (P : ProjectiveResolution X)
    (n : ℕ) (A : Rep ℤ H) :=
  @ProjectiveResolution.isoExt ℤ _ (Rep ℤ H) _ _ Rep.instLinear _ X P n A

private noncomputable def repPrecompLinearYonedaObj
    {H : Type} [Group H] {P Q : ChainComplex (Rep ℤ H) ℕ} (q : P ⟶ Q)
    (A : Rep ℤ H) : repLinearYonedaObj Q A ⟶ repLinearYonedaObj P A where
  f n := (@precompLinearYonedaObj ℤ (Rep ℤ H) _ _ _ Rep.instLinear P Q q A).f n
  comm' i j _ :=
    (@precompLinearYonedaObj ℤ (Rep ℤ H) _ _ _ Rep.instLinear P Q q A).comm i j

private noncomputable def repPostcompLinearYonedaObj
    {H : Type} [Group H] (P : ChainComplex (Rep ℤ H) ℕ) {A B : Rep ℤ H}
    (f : A ⟶ B) : repLinearYonedaObj P A ⟶ repLinearYonedaObj P B where
  f n := (@postcompLinearYonedaObj ℤ (Rep ℤ H) _ _ _ Rep.instLinear P A B f).f n
  comm' i j _ :=
    (@postcompLinearYonedaObj ℤ (Rep ℤ H) _ _ _ Rep.instLinear P A B f).comm i j

private noncomputable def barPostcompLinearYonedaObj
    {H : Type} [Group H] {A B : Rep ℤ H} (f : A ⟶ B) :
    repLinearYonedaObj (Rep.barComplex ℤ H) A ⟶
      repLinearYonedaObj (Rep.barComplex ℤ H) B :=
  repPostcompLinearYonedaObj (Rep.barComplex ℤ H) f

variable {G : Type} [Group G] (S : Subgroup G)

@[reassoc]
private theorem inhomogeneousCochainsIso_naturality
    {H : Type} [Group H] {A B : Rep ℤ H} (f : A ⟶ B) :
    groupCohomology.cochainsMap (.id H) f ≫
        (groupCohomology.inhomogeneousCochainsIso B).hom =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        barPostcompLinearYonedaObj f := by
  ext n
  apply DFunLike.ext'
  funext x
  apply (Rep.freeLiftLEquiv ℤ H (Fin n → H) B).injective
  ext i
  change
    (Rep.freeLiftLEquiv ℤ H (Fin n → H) B)
        ((Rep.freeLiftLEquiv ℤ H (Fin n → H) B).symm
          (fun j => f.hom (x j))) i =
      f.hom ((Rep.freeLiftLEquiv ℤ H (Fin n → H) A)
        ((Rep.freeLiftLEquiv ℤ H (Fin n → H) A).symm x) i)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

@[reassoc]
private theorem inhomogeneousCochainsIso_inv_naturality
    {H : Type} [Group H] {A B : Rep ℤ H} (f : A ⟶ B) :
    (groupCohomology.inhomogeneousCochainsIso A).inv ≫
        groupCohomology.cochainsMap (.id H) f =
      barPostcompLinearYonedaObj f ≫
        (groupCohomology.inhomogeneousCochainsIso B).inv := by
  ext n
  rfl

private noncomputable def shapiroResolution :
    CategoryTheory.ProjectiveResolution (Rep.trivial ℤ S ℤ) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)

private noncomputable def shapiroResolutionComparison :
    (shapiroResolution S).complex ⟶ (Rep.barResolution ℤ S).complex :=
  CategoryTheory.ProjectiveResolution.lift (𝟙 _) (shapiroResolution S)
    (Rep.barResolution ℤ S)

private noncomputable def shapiroResolutionComparison' :
    ((Rep.resFunctor S.subtype).mapProjectiveResolution
      (Rep.barResolution ℤ G)).complex ⟶ Rep.barComplex ℤ S where
  f n := (shapiroResolutionComparison S).f n
  comm' i j _ := (shapiroResolutionComparison S).comm i j

private abbrev shapiroLinearYonedaObj (A : Rep ℤ S) :=
  repLinearYonedaObj
    ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).complex A

private noncomputable def shapiroPrecompLinearYonedaObj (A : Rep ℤ S) :
    repLinearYonedaObj (Rep.barComplex ℤ S) A ⟶ shapiroLinearYonedaObj S A :=
  repPrecompLinearYonedaObj (shapiroResolutionComparison' S) A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shapiroPrecompLinearYonedaObj_eq (A : Rep ℤ S) :
    shapiroPrecompLinearYonedaObj S A =
      @precompLinearYonedaObj ℤ (Rep ℤ S) _ _ _ Rep.instLinear _ _
        (shapiroResolutionComparison S) A := by
  ext n
  rfl

private noncomputable def shapiroPostcompLinearYonedaObj
    {A B : Rep ℤ S} (f : A ⟶ B) : shapiroLinearYonedaObj S A ⟶
      shapiroLinearYonedaObj S B :=
  repPostcompLinearYonedaObj
    ((Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).complex f

@[reassoc]
private theorem shapiroResolutionComparison_naturality
    {A B : Rep ℤ S} (f : A ⟶ B) :
    shapiroPrecompLinearYonedaObj S A ≫
        shapiroPostcompLinearYonedaObj S f =
      barPostcompLinearYonedaObj f ≫
        shapiroPrecompLinearYonedaObj S B := by
  ext n
  rfl

private noncomputable def linearYonedaObjResIsoHom (A : Rep ℤ S) :
    shapiroLinearYonedaObj S A ⟶
      repLinearYonedaObj (Rep.barComplex ℤ G)
        ((Rep.coindFunctor ℤ S.subtype).obj A) where
  f n := (groupCohomology.linearYonedaObjResProjectiveResolutionIso
    (Rep.barResolution ℤ G) A).hom.f n
  comm' i j _ := (groupCohomology.linearYonedaObjResProjectiveResolutionIso
    (Rep.barResolution ℤ G) A).hom.comm i j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem linearYonedaObjResIsoHom_eq (A : Rep ℤ S) :
    linearYonedaObjResIsoHom S A =
      (groupCohomology.linearYonedaObjResProjectiveResolutionIso
        (Rep.barResolution ℤ G) A).hom := by
  ext n
  rfl

@[reassoc]
private theorem linearYonedaObjResIso_naturality
    {A B : Rep ℤ S} (f : A ⟶ B) :
    shapiroPostcompLinearYonedaObj S f ≫ linearYonedaObjResIsoHom S B =
      linearYonedaObjResIsoHom S A ≫
        barPostcompLinearYonedaObj ((Rep.coindFunctor ℤ S.subtype).map f) := by
  ext n
  rfl

private noncomputable def shapiroCochainsMap (A : Rep ℤ S) :
    groupCohomology.inhomogeneousCochains A ⟶
      groupCohomology.inhomogeneousCochains (Rep.coind S.subtype A) :=
  (groupCohomology.inhomogeneousCochainsIso A).hom ≫
    shapiroPrecompLinearYonedaObj S A ≫
    linearYonedaObjResIsoHom S A ≫
    (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).inv

private theorem shapiroCochainsMap_naturality {A B : Rep ℤ S} (f : A ⟶ B) :
    shapiroCochainsMap S A ≫
        groupCohomology.cochainsMap (.id G) ((Rep.coindFunctor ℤ S.subtype).map f) =
      groupCohomology.cochainsMap (.id S) f ≫ shapiroCochainsMap S B := by
  simp only [shapiroCochainsMap]
  slice_lhs 4 5 =>
    erw [inhomogeneousCochainsIso_inv_naturality
      (H := G) ((Rep.coindFunctor ℤ S.subtype).map f)]
  slice_lhs 3 5 =>
    erw [← linearYonedaObjResIso_naturality_assoc S f]
  slice_lhs 2 3 => erw [shapiroResolutionComparison_naturality S f]
  slice_lhs 1 2 =>
    erw [← inhomogeneousCochainsIso_naturality (H := S) f]
  simp only [Category.assoc]
  rfl

private theorem homologyUnop_naturality
    {V : Type w} {ι : Type*} [Category V] [Abelian V] {c : ComplexShape ι}
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i]
    [K.unop.HasHomology i] [L.unop.HasHomology i] :
    (L.homologyUnop i).hom ≫ (HomologicalComplex.homologyMap φ i).unop =
      HomologicalComplex.homologyMap
          ((HomologicalComplex.unopFunctor V c).map φ.op) i ≫
        (K.homologyUnop i).hom := by
  apply Quiver.Hom.op_inj
  convert (HomologicalComplex.homologyOp_hom_naturality
    ((HomologicalComplex.unopFunctor V c).map φ.op) i) using 1 <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem isoExt_shapiroResolutionComparison (A : Rep ℤ S) (n : ℕ) :
    (repIsoExt (Rep.barResolution ℤ S) n A).inv ≫
        (repIsoExt (X := Rep.trivial ℤ S ℤ)
          ((Rep.resFunctor S.subtype).mapProjectiveResolution
            (Rep.barResolution ℤ G)) n A).hom =
      HomologicalComplex.homologyMap
        (@precompLinearYonedaObj ℤ (Rep ℤ S) _ _ _ Rep.instLinear _ _
          (shapiroResolutionComparison S) A) n := by
  let F := ((@linearYoneda ℤ _ (Rep ℤ S) _ _ Rep.instLinear).obj A).rightOp
  let P : ProjectiveResolution (Rep.trivial ℤ S ℤ) :=
    (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)
  let Q := Rep.barResolution ℤ S
  let q : P.complex ⟶ Q.complex := shapiroResolutionComparison S
  change
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homologyUnop n).hom ≫
      (Q.isoLeftDerivedObj F n).hom.unop ≫
      (P.isoLeftDerivedObj F n).inv.unop ≫
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyUnop n).inv =
        HomologicalComplex.homologyMap
          (@precompLinearYonedaObj ℤ (Rep ℤ S) _ _ _ Rep.instLinear _ _ q A) n
  have hcomm : q.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ 𝟙 _ := by
    change (ProjectiveResolution.lift (𝟙 _) P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ 𝟙 _
    exact ProjectiveResolution.lift_commutes_zero (𝟙 _) P Q
  let φ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map q
  have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 _) P Q q hcomm F n
  rw [show (F.leftDerived n).map (𝟙 _) = 𝟙 _ from (F.leftDerived n).map_id _,
    Category.id_comp] at hnat
  have h := (Iso.inv_comp_eq (P.isoLeftDerivedObj F n)).2 hnat
  change (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom =
    HomologicalComplex.homologyMap φ n at h
  have hu := congrArg Quiver.Hom.unop h
  rw [unop_comp] at hu
  slice_lhs 2 3 => rw [hu]
  have hφ := homologyUnop_naturality φ n
  slice_lhs 1 2 => rw [hφ]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyMap_shapiroCochainsMap (A : Rep ℤ S) (n : ℕ) :
    HomologicalComplex.homologyMap (shapiroCochainsMap S A) n =
      (groupCohomology.coindIso A n).inv := by
  simp only [shapiroCochainsMap, HomologicalComplex.homologyMap_comp]
  rw [shapiroPrecompLinearYonedaObj_eq S A,
    linearYonedaObjResIsoHom_eq S A]
  simp only [groupCohomology.coindIso, groupCohomologyIso,
    groupCohomologyIsoExt, Rep.barResolution_complex,
    Functor.mapProjectiveResolution_complex, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
    isoOfQuasiIsoAt_hom, Category.assoc]
  slice_rhs 2 3 =>
    erw [isoExt_shapiroResolutionComparison S A n]
  simp only [Functor.map_comp]
  rfl

private noncomputable def shapiroCochainsShortComplexMap
    (Y : ShortComplex (Rep ℤ S)) :
    Y.map (groupCohomology.cochainsFunctor ℤ S) ⟶
      (Y.map (Rep.coindFunctor ℤ S.subtype)).map
        (groupCohomology.cochainsFunctor ℤ G) where
  τ₁ := shapiroCochainsMap S Y.X₁
  τ₂ := shapiroCochainsMap S Y.X₂
  τ₃ := shapiroCochainsMap S Y.X₃
  comm₁₂ := shapiroCochainsMap_naturality S Y.f
  comm₂₃ := shapiroCochainsMap_naturality S Y.g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Shapiro's inverse commutes with the connecting morphism of a short exact sequence. -/
theorem _root_.groupCohomology.coindIso_inv_δ (S : Subgroup G) [S.FiniteIndex]
    {Y : ShortComplex (Rep ℤ S)}
    (hY : Y.ShortExact) :
    groupCohomology.δ hY 1 2 rfl ≫ (groupCohomology.coindIso Y.X₁ 2).inv =
      (groupCohomology.coindIso Y.X₃ 1).inv ≫
        groupCohomology.δ (hY.map_of_exact (Rep.coindFunctor ℤ S.subtype)) 1 2 rfl := by
  let hcoind := hY.map_of_exact (Rep.coindFunctor ℤ S.subtype)
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (shapiroCochainsShortComplexMap S Y)
    (groupCohomology.map_cochainsFunctor_shortExact hY)
    (groupCohomology.map_cochainsFunctor_shortExact hcoind) 1 2 rfl
  dsimp [shapiroCochainsShortComplexMap] at h
  erw [homologyMap_shapiroCochainsMap, homologyMap_shapiroCochainsMap] at h
  simpa only [hcoind] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Shapiro connecting square specialized to a restricted short exact sequence. -/
theorem _root_.groupCohomology.coindIso_inv_δ_res (S : Subgroup G) [S.FiniteIndex]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) :
    groupCohomology.δ ((Rep.shortExact_res S.subtype).2 hX) 1 2 rfl ≫
        (groupCohomology.coindIso (Rep.res S.subtype X.X₁) 2).inv =
      (groupCohomology.coindIso (Rep.res S.subtype X.X₃) 1).inv ≫
        groupCohomology.δ
          (((Rep.shortExact_res S.subtype).2 hX).map_of_exact
            (Rep.coindFunctor ℤ S.subtype)) 1 2 rfl := by
  simpa using groupCohomology.coindIso_inv_δ S ((Rep.shortExact_res S.subtype).2 hX)

end

end NU.LCFT
