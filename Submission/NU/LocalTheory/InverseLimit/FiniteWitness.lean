import Submission.NU.LocalTheory.FiniteLevel.Recover

/-!
# Finite witnesses in a cofinal Galois system

This file formalizes the first half of Blueprint §8: a non-procyclic closed
subgroup has a noncyclic finite anchor; noncyclic decomposition groups lie
over the finite ramification locus; hence all witness sets above the anchor
are finite.  It ends with the compactness theorem for finite inverse systems,
without a surjectivity hypothesis.
-/

open IsDedekindDomain
open scoped NumberField

namespace NU.LocalTheory

noncomputable section

/-- Procyclicity expressed by a topological generator of the subgroup. -/
def IsProcyclic {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) : Prop :=
  ∃ h : H, (Subgroup.zpowers h).topologicalClosure = ⊤

private noncomputable def finiteLevelImageMap
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    H →* finiteLevelImage L H where
  toFun h := ⟨absoluteRestriction L h.1, ⟨h.1, h.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (absoluteRestriction L)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (absoluteRestriction L) x.1 y.1

private theorem finiteLevelImageMap_surjective
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Function.Surjective (finiteLevelImageMap L H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem finiteLevelImageMap_continuous
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Continuous (finiteLevelImageMap L H) := by
  apply Continuous.subtype_mk
  have hr : Continuous (absoluteRestriction L) := by
    change Continuous (AlgEquiv.restrictNormalHom L.field)
    exact InfiniteGalois.restrictNormalHom_continuous L.field
  exact hr.comp continuous_subtype_val

private def finiteLevelGenerators
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    Set H :=
  {h | ∀ y : finiteLevelImage L H,
    y ∈ Subgroup.zpowers (finiteLevelImageMap L H h)}

private theorem finiteLevelGenerators_nonempty
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K))
    (hcyclic : IsCyclic (finiteLevelImage L H)) :
    (finiteLevelGenerators L H).Nonempty := by
  letI : IsCyclic (finiteLevelImage L H) := hcyclic
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator
    (α := finiteLevelImage L H)
  obtain ⟨h, rfl⟩ := finiteLevelImageMap_surjective L H y
  exact ⟨h, hy⟩

private theorem finiteLevelGenerators_isClosed
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (H : Subgroup (Field.absoluteGaloisGroup K)) :
    IsClosed (finiteLevelGenerators L H) := by
  let T : Set (finiteLevelImage L H) :=
    {x | ∀ y : finiteLevelImage L H, y ∈ Subgroup.zpowers x}
  have hT : IsClosed T := Set.toFinite T |>.isClosed
  change IsClosed ((finiteLevelImageMap L H) ⁻¹' T)
  exact hT.preimage (finiteLevelImageMap_continuous L H)

private theorem absoluteRestriction_eq_of_le
    {K : Type*} [Field K] [NumberField K]
    {L M : GaloisLevel K} (hLM : L.LE M)
    {g k : Field.absoluteGaloisGroup K}
    (h : absoluteRestriction M g = absoluteRestriction M k) :
    absoluteRestriction L g = absoluteRestriction L k := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [absoluteRestriction_apply, absoluteRestriction_apply]
  have he := DFunLike.congr_fun h
    (IntermediateField.inclusion hLM x)
  have hev := congrArg Subtype.val he
  rw [absoluteRestriction_apply, absoluteRestriction_apply] at hev
  exact hev

private theorem finiteLevelGenerators_antitone
    {K : Type*} [Field K] [NumberField K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    {L M : GaloisLevel K} (hLM : L.LE M) :
    finiteLevelGenerators M H ⊆ finiteLevelGenerators L H := by
  intro h hh y
  obtain ⟨x, hx, hy⟩ := y.property
  let xH : H := ⟨x, hx⟩
  have hm := hh (finiteLevelImageMap M H xH)
  rw [Subgroup.mem_zpowers_iff] at hm ⊢
  obtain ⟨z, hz⟩ := hm
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change absoluteRestriction L h.1 ^ z = y.1
  rw [← map_zpow]
  rw [← hy]
  apply absoluteRestriction_eq_of_le hLM
  have hz' := congrArg Subtype.val hz
  change absoluteRestriction M h.1 ^ z = absoluteRestriction M x at hz'
  rw [map_zpow]
  exact hz'

/-- Blueprint Lemma 8.1 (`lem:cyclic-images`): cyclic images throughout a
cofinal system force a closed subgroup to be procyclic. -/
theorem cyclic_finite_images_imply_procyclic
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (hcyclic : ∀ i, IsCyclic (finiteLevelImage (Λ i) H)) :
    IsProcyclic H := by
  let C : ι → Set H := fun i => finiteLevelGenerators (Λ i) H
  have hCnonempty (i : ι) : (C i).Nonempty :=
    finiteLevelGenerators_nonempty (Λ i) H (hcyclic i)
  have hCclosed (i : ι) : IsClosed (C i) :=
    finiteLevelGenerators_isClosed (Λ i) H
  have hCdirected : Directed (fun A B : Set H => A ⊇ B) C := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hΛ.2.1 i j
    exact ⟨k, finiteLevelGenerators_antitone H hik,
      finiteLevelGenerators_antitone H hjk⟩
  letI : Nonempty ι := hΛ.1
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    absoluteGaloisGroup_compactSpace
  letI : CompactSpace H :=
    hclosed.isClosedEmbedding_subtypeVal.compactSpace
  obtain ⟨h, hh⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hCdirected hCnonempty
      (fun i => (hCclosed i).isCompact) hCclosed
  refine ⟨h, ?_⟩
  apply top_unique
  intro x _
  change x ∈ closure (Subgroup.zpowers h : Set H)
  rw [mem_closure_iff_nhds_one]
  intro U hU
  obtain ⟨V, hV, hVU⟩ :=
    (mem_nhds_induced (f := fun z : H =>
      (z : Field.absoluteGaloisGroup K)) (a := (1 : H)) U).mp hU
  obtain ⟨E, hEfin, hEnormal, hEV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K (AlgebraicClosure K) V).mp hV
  letI : FiniteDimensional K E := hEfin
  letI : Normal K E := hEnormal
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsGalois K E := ⟨⟩
  let LE : GaloisLevel K :=
    { field := E
      finiteDimensional := hEfin
      numberField := inferInstance
      isGalois := inferInstance }
  obtain ⟨i, hi⟩ := hΛ.2.2 LE
  have hgen : h ∈ C i := Set.mem_iInter.mp hh i
  have hpower := hgen (finiteLevelImageMap (Λ i) H x)
  rw [Subgroup.mem_zpowers_iff] at hpower
  obtain ⟨z, hz⟩ := hpower
  refine ⟨h ^ z, ?_, ?_⟩
  · exact (Subgroup.zpowers h).zpow_mem (Subgroup.mem_zpowers h) z
  · apply hVU
    let d : Field.absoluteGaloisGroup K := ((h ^ z) / x : H)
    have hdker : absoluteRestriction (Λ i) d = 1 := by
      dsimp [d]
      rw [map_div, map_zpow]
      have hz' := congrArg Subtype.val hz
      change absoluteRestriction (Λ i) h.1 ^ z =
        absoluteRestriction (Λ i) x.1 at hz'
      rw [hz']
      simp
    have hdfix : d ∈ E.fixingSubgroup := by
      apply E.fixingSubgroup_antitone hi
      rw [← IntermediateField.restrictNormalHom_ker]
      exact hdker
    exact hEV hdfix

/-- Ramification of the restricted base prime, expressed by the usual
ramification index. -/
def IsRamifiedAtBase {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : FinitePlace L) : Prop :=
  1 < w.asIdeal.ramificationIdx (𝓞 K)

/-- Blueprint Lemma 8.2 (`lem:noncyclic-ramified`): a noncyclic finite
decomposition group lies over a ramified base prime. -/
theorem noncyclic_decompositionGroup_ramified
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : FinitePlace L)
    (hnoncyclic : ¬IsCyclic (decompositionGroup K w)) :
    IsRamifiedAtBase (K := K) (L := L) w := by
  open scoped Pointwise in
  by_contra hunramified
  apply hnoncyclic
  rw [IsRamifiedAtBase, not_lt] at hunramified
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    apply Nat.le_antisymm hunramified
    exact Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)
  let G := L ≃ₐ[K] L
  let R := 𝓞 K
  let S := 𝓞 L
  let p : Ideal R := w.asIdeal.under R
  letI : p.IsPrime := inferInstance
  letI : p.IsMaximal := inferInstance
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (R ⧸ p) := Fintype.ofFinite (R ⧸ p)
  letI : Fintype (S ⧸ w.asIdeal) := Fintype.ofFinite (S ⧸ w.asIdeal)
  letI : w.asIdeal.LiesOver p := ⟨rfl⟩
  let ρ := Ideal.Quotient.stabilizerHom w.asIdeal p G
  have hIcard : Nat.card (w.asIdeal.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p w.asIdeal G]
    exact he
  have hIcard' :
      Nat.card (w.asIdeal.inertia (MulAction.stabilizer G w.asIdeal)) = 1 := by
    change Nat.card
      (w.asIdeal.toAddSubgroup.inertia (MulAction.stabilizer G w.asIdeal)) = 1
    rw [← AddSubgroup.subgroupOf_inertia]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) w.asIdeal)).toEquiv]
    exact hIcard
  have hker : ρ.ker = ⊥ := by
    rw [Ideal.Quotient.ker_stabilizerHom]
    exact Subgroup.card_eq_one.mp hIcard'
  have hρinj : Function.Injective ρ :=
    (MonoidHom.ker_eq_bot_iff ρ).mp hker
  letI := finitePlaceAction K L
  let f0 : decompositionGroup K w →
      MulAction.stabilizer G w.asIdeal := fun σ => by
    refine ⟨σ.1, ?_⟩
    have hσ := σ.2
    change σ.1 • w = w at hσ
    exact congrArg HeightOneSpectrum.asIdeal hσ
  let f : decompositionGroup K w →* MulAction.stabilizer G w.asIdeal :=
    { toFun := f0
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply isCyclic_of_injective (ρ.comp f)
  apply hρinj.comp
  intro x y hxy
  have hval := congrArg
    (fun z : MulAction.stabilizer G w.asIdeal => z.1) hxy
  apply Subtype.ext
  simpa [f, f0] using hval

/-- Only finitely many base primes ramify in a fixed finite extension. -/
theorem ramified_base_places_finite
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    {v : FinitePlace K | ∃ w : FinitePlace L,
      restrictFinitePlace K w = v ∧
        IsRamifiedAtBase (K := K) (L := L) w}.Finite := by
  let I := differentIdeal (𝓞 K) (𝓞 L)
  have hI : I ≠ ⊥ := differentIdeal_ne_bot
  have hfinite : {w : FinitePlace L | w.asIdeal ∣ I}.Finite :=
    Ideal.finite_factors hI
  apply (hfinite.image (restrictFinitePlace K)).subset
  rintro v ⟨w, hwv, hwram⟩
  refine ⟨w, ?_, hwv⟩
  change w.asIdeal ∣ I
  apply dvd_differentIdeal_iff.mpr
  intro hunramified
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one_iff.mpr hunramified
  rw [IsRamifiedAtBase, he] at hwram
  exact (Nat.lt_irrefl 1) hwram

/-- Blueprint (8.3): prime witnesses whose decomposition group equals the
fixed finite image of `H`. -/
def finiteWitnesses {K : Type*} [Field K] [NumberField K]
    (H : Subgroup (Field.absoluteGaloisGroup K)) (L : GaloisLevel K) :
    Set (FinitePlace L.field) :=
  {w | decompositionGroup K w = finiteLevelImage L H}

/-- Restriction of a place between two nested Galois levels. -/
noncomputable def restrictLevelPlace {K : Type*} [Field K] [NumberField K]
    {L M : GaloisLevel K} (hLM : L.LE M)
    (w : FinitePlace M.field) : FinitePlace L.field := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  exact restrictFinitePlace L.field w

/-- Restriction preserves witness sets. -/
theorem restrictLevelPlace_mem_finiteWitnesses
    {K : Type*} [Field K] [NumberField K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    {L M : GaloisLevel K} (hLM : L.LE M)
    {w : FinitePlace M.field} (hw : w ∈ finiteWitnesses H M) :
    restrictLevelPlace hLM w ∈ finiteWitnesses H L := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower K L.field M.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change decompositionGroup K (restrictLevelPlace hLM w) = finiteLevelImage L H
  rw [restrictLevelPlace]
  calc
    decompositionGroup K (restrictFinitePlace L.field w) =
        Subgroup.map (galoisRestriction K L.field M.field)
          (decompositionGroup K w) :=
      (tower_surjectivity K L.field M.field w).symm
    _ = Subgroup.map (galoisRestriction K L.field M.field)
          (finiteLevelImage M H) := by rw [hw]
    _ = finiteLevelImage L H := by
      have hcomp :
          (galoisRestriction K L.field M.field).comp
              (absoluteRestriction M) = absoluteRestriction L := by
        ext g x
        have hr := galoisRestriction_apply K L.field M.field
          (absoluteRestriction M g) x
        have hr' := congrArg M.field.val hr
        calc
          (((galoisRestriction K L.field M.field
              (absoluteRestriction M g)) x : L.field) :
                AlgebraicClosure K) =
              ((algebraMap L.field M.field
                ((galoisRestriction K L.field M.field
                  (absoluteRestriction M g)) x) : M.field) :
                    AlgebraicClosure K) := rfl
          _ = ((absoluteRestriction M g
                (algebraMap L.field M.field x) : M.field) :
                  AlgebraicClosure K) := hr'
          _ = (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
                (x : AlgebraicClosure K) := by
            rw [absoluteRestriction_apply]
            rfl
          _ = ((absoluteRestriction L g x : L.field) :
                AlgebraicClosure K) := by
            rw [absoluteRestriction_apply]
      rw [finiteLevelImage, finiteLevelImage, Subgroup.map_map, hcomp]

private theorem finitePlaces_over_finitePlace
    (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (v : FinitePlace K) :
    Set.Finite {w : FinitePlace L | restrictFinitePlace K w = v} := by
  let f : {w : FinitePlace L | restrictFinitePlace K w = v} →
      v.asIdeal.primesOver (𝓞 L) := fun w =>
    ⟨w.1.asIdeal, w.1.isPrime, by
      rw [Ideal.liesOver_iff]
      have hw := congrArg HeightOneSpectrum.asIdeal w.2
      exact hw.symm⟩
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    exact congrArg Subtype.val hwz
  letI : Fintype (v.asIdeal.primesOver (𝓞 L)) :=
    (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  letI : Finite {w : FinitePlace L |
      restrictFinitePlace K w = v} := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp inferInstance

private theorem restrictFinitePlace_restrictLevelPlace
    {K : Type*} [Field K] [NumberField K]
    {L M : GaloisLevel K} (hLM : L.LE M)
    (w : FinitePlace M.field) :
    restrictFinitePlace K (restrictLevelPlace hLM w) =
      restrictFinitePlace K w := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower K L.field M.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply HeightOneSpectrum.ext
  rw [restrictLevelPlace, restrictFinitePlace_asIdeal,
    restrictFinitePlace_asIdeal, restrictFinitePlace_asIdeal]
  ext x
  change algebraMap (𝓞 L.field) (𝓞 M.field)
      (algebraMap (𝓞 K) (𝓞 L.field) x) ∈ w.asIdeal ↔
    algebraMap (𝓞 K) (𝓞 M.field) x ∈ w.asIdeal
  have hx : algebraMap (𝓞 L.field) (𝓞 M.field)
      (algebraMap (𝓞 K) (𝓞 L.field) x) =
        algebraMap (𝓞 K) (𝓞 M.field) x := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K L.field M.field x
  rw [hx]

/-- Blueprint Lemma 8.3 (`lem:finite-witness`): above a noncyclic anchor,
witness sets are nonempty and finite, and restriction supplies the transition
map. -/
theorem finite_witness_system
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (H : Subgroup (Field.absoluteGaloisGroup K)) (i₀ : ι)
    (hanchor : ¬IsCyclic (finiteLevelImage (Λ i₀) H))
    (hdecomp : ∀ i, finiteLevelImage (Λ i) H ∈
      decompositionCollection K (Λ i).field)
    (i : ι) (hi : (Λ i₀).LE (Λ i)) :
    (finiteWitnesses H (Λ i)).Nonempty ∧
      (finiteWitnesses H (Λ i)).Finite := by
  constructor
  · obtain ⟨w, hw⟩ := hdecomp i
    exact ⟨w, hw⟩
  · let R : Set (FinitePlace K) :=
      {v | ∃ w : FinitePlace (Λ i₀).field,
        restrictFinitePlace K w = v ∧
          IsRamifiedAtBase (K := K) (L := (Λ i₀).field) w}
    have hR : R.Finite :=
      ramified_base_places_finite K (Λ i₀).field
    let f : FinitePlace (Λ i).field → FinitePlace K :=
      restrictFinitePlace K
    have hpre : (f ⁻¹' R).Finite := hR.preimage' (fun v _ => by
      change Set.Finite {w : FinitePlace (Λ i).field |
        restrictFinitePlace K w = v}
      exact finitePlaces_over_finitePlace K (Λ i).field v)
    apply hpre.subset
    intro w hw
    change f w ∈ R
    let w₀ := restrictLevelPlace hi w
    have hw₀ : w₀ ∈ finiteWitnesses H (Λ i₀) :=
      restrictLevelPlace_mem_finiteWitnesses H hi hw
    have hnoncyclic : ¬IsCyclic (decompositionGroup K w₀) := by
      rw [hw₀]
      exact hanchor
    have hram := noncyclic_decompositionGroup_ramified
      K (Λ i₀).field w₀ hnoncyclic
    refine ⟨w₀, ?_, hram⟩
    exact restrictFinitePlace_restrictLevelPlace hi w

/-- Blueprint Lemma 8.4 (`lem:finite-inverse-compactness`): a directed
inverse system of nonempty finite sets has a compatible point.  No
surjectivity of transition maps is assumed. -/
theorem finite_inverse_system_compactness
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type*) [∀ i, Finite (S i)] [∀ i, Nonempty (S i)]
    (r : ∀ {i j : ι}, i ≤ j → S j → S i)
    (r_id : ∀ i (x : S i), r (le_refl i) x = x)
    (r_comp : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      r hij (r hjk x) = r (hij.trans hjk) x) :
    ∃ x : ∀ i, S i, ∀ {i j : ι} (hij : i ≤ j), r hij (x j) = x i := by
  open CategoryTheory in
  let F : ιᵒᵖ ⥤ Type _ :=
    { obj := fun i => S i.unop
      map := fun {i j} f => ↾(r (leOfHom f.unop))
      map_id := by
        intro i
        ext x
        exact r_id i.unop x
      map_comp := by
        intro i j k f g
        ext x
        exact (r_comp (leOfHom g.unop) (leOfHom f.unop) x).symm }
  letI (i : ιᵒᵖ) : Finite (F.obj i) := inferInstance
  letI (i : ιᵒᵖ) : Nonempty (F.obj i) := inferInstance
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  let x : ∀ i, S i := fun i => u (Opposite.op i)
  refine ⟨x, ?_⟩
  intro i j hij
  have hsection := hu ((homOfLE hij).op)
  change r (leOfHom ((homOfLE hij).op).unop)
      (u (Opposite.op j)) = u (Opposite.op i) at hsection
  simpa [x] using hsection

end

end NU.LocalTheory
