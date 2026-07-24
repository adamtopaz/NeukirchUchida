import Mathlib

/-!
# Local fields: normalized valuations, units, lattices, and unramified towers

This file fixes the Stage A conventions used throughout the development.  A local field is a
Mathlib `IsNonarchimedeanLocalField`; its multiplicative group is `Units K`, its ring of integers
is `𝒪[K]`, and its maximal ideal is `𝓂[K]`.

The project-facing integer valuation is a normalized additive exponent packaged as a homomorphism
`Units K →* Multiplicative ℤ`.  This is a small adapter around Mathlib's value group.  Principal
units are defined by reduction of `𝒪[K]ˣ`, not by a choice of uniformizer.
-/

namespace NU.LCFT

noncomputable section

open scoped Pointwise ValuativeRel

universe u v w

/-- The ring of integers of a Mathlib nonarchimedean local field. -/
abbrev RingOfIntegers (K : Type u) [Field K] [ValuativeRel K] := 𝒪[K]

/-- The maximal ideal of the ring of integers. -/
abbrev LocalMaximalIdeal (K : Type u) [Field K] [ValuativeRel K] := 𝓂[K]

/-- The residue field of a valued field. -/
abbrev LocalResidueField (K : Type u) [Field K] [ValuativeRel K] := 𝓀[K]

/-- The cardinality of the residue field. -/
noncomputable def residueCard (K : Type u) [Field K] [ValuativeRel K] : ℕ :=
  Nat.card (LocalResidueField K)

section NormalizedValuation

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/--
**A01**, foundational result (F3): Mathlib's discrete value group admits the unique orientation
for which the ring of integers consists of elements of nonnegative integer valuation.
-/
theorem exists_normalizedValuationHom :
    ∃ v : Units K →* Multiplicative ℤ,
      Function.Surjective v ∧
      ∀ x : Units K, 0 ≤ Multiplicative.toAdd (v x) ↔
        ∃ a : RingOfIntegers K, (a : K) = (x : K) := by
  let e : ValuativeRel.ValueGroupWithZero K ≃*o WithZero (Multiplicative ℤ) :=
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let v₀ : Units K →* Units (ValuativeRel.ValueGroupWithZero K) :=
    Units.map (ValuativeRel.valuation K)
  let v₁ : Units K →* Units (WithZero (Multiplicative ℤ)) :=
    (Units.mapEquiv e.toMulEquiv).toMonoidHom.comp v₀
  let v : Units K →* Multiplicative ℤ :=
    (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom.comp
      (WithZero.unitsWithZeroEquiv.toMonoidHom.comp v₁)
  refine ⟨v, ?_, ?_⟩
  · have hv₀ : Function.Surjective v₀ := by
      intro δ
      obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective
        (K := K) (δ : ValuativeRel.ValueGroupWithZero K)
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, map_zero] at ha
        exact δ.ne_zero ha.symm
      refine ⟨Units.mk0 a ha0, ?_⟩
      apply Units.ext
      exact ha
    exact (MulEquiv.inv (Multiplicative ℤ)).surjective.comp
      (WithZero.unitsWithZeroEquiv.surjective.comp
        ((Units.mapEquiv e.toMulEquiv).surjective.comp hv₀))
  · intro x
    change 0 ≤ -Multiplicative.toAdd (WithZero.unitsWithZeroEquiv
      (Units.mapEquiv e.toMulEquiv (Units.map (ValuativeRel.valuation K) x))) ↔ _
    rw [le_neg]
    change Multiplicative.toAdd (WithZero.unitsWithZeroEquiv
      (Units.mapEquiv e.toMulEquiv (Units.map (ValuativeRel.valuation K) x))) ≤ 0 ↔ _
    change WithZero.unitsWithZeroEquiv
      (Units.mapEquiv e.toMulEquiv (Units.map (ValuativeRel.valuation K) x)) ≤ 1 ↔ _
    rw [← WithZero.coe_le_coe]
    simp only [WithZero.coe_unitsWithZeroEquiv_eq_units_val, Units.coe_mapEquiv,
      Units.coe_map]
    constructor
    · intro h
      have h' : ValuativeRel.valuation K (x : K) ≤ 1 :=
        e.toOrderIso.le_iff_le.mp ((e.map_one).symm ▸ h)
      have hxmem : (x : K) ∈ (ValuativeRel.valuation K).integer :=
        (Valuation.mem_integer_iff (ValuativeRel.valuation K) (x : K)).mpr h'
      exact ⟨⟨x, hxmem⟩, rfl⟩
    · intro h
      rcases h with ⟨a, ha⟩
      have hxmem : (x : K) ∈ (ValuativeRel.valuation K).integer := ha ▸ a.prop
      have h' : ValuativeRel.valuation K (x : K) ≤ 1 :=
        (Valuation.mem_integer_iff (ValuativeRel.valuation K) (x : K)).mp hxmem
      calc
        e.toMulEquiv (ValuativeRel.valuation K (x : K)) ≤ e.toMulEquiv 1 :=
          e.toOrderIso.le_iff_le.mpr h'
        _ = (↑(1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by simp

/-- The normalized integer valuation on `Kˣ`, in multiplicative-homomorphism form. -/
noncomputable def normalizedValuationHom : Units K →* Multiplicative ℤ :=
  (exists_normalizedValuationHom K).choose

/-- The normalized integer valuation on a nonzero field element. -/
noncomputable def normalizedValuation (x : Units K) : ℤ :=
  Multiplicative.toAdd (normalizedValuationHom K x)

/-- Normalized valuation is additive on products. -/
theorem normalizedValuation_mul (x y : Units K) :
    normalizedValuation K (x * y) = normalizedValuation K x + normalizedValuation K y := by
  simp [normalizedValuation]

/-- The normalized valuation is onto `ℤ`. -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  exact Multiplicative.toAdd.surjective.comp
    (exists_normalizedValuationHom K).choose_spec.1

/-- A project-local uniformizer, with arithmetic normalization `v(π) = 1`. -/
structure Uniformizer where
  /-- The underlying nonzero field element. -/
  val : Units K
  /-- Its normalized valuation. -/
  valuation_eq_one : normalizedValuation K val = 1

instance : Coe (Uniformizer K) (Units K) := ⟨Uniformizer.val⟩

/-- Uniformizers exist in every nonarchimedean local field. -/
noncomputable def defaultUniformizer : Uniformizer K :=
  ⟨(normalizedValuation_surjective K 1).choose,
    (normalizedValuation_surjective K 1).choose_spec⟩

end NormalizedValuation

section Ramification

open ValuativeRel

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

private theorem normalizedValuation_inv_aux
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem normalizedValuation_zpow_aux
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) (n : ℤ) :
    normalizedValuation K (x ^ n) = n * normalizedValuation K x := by
  simp [normalizedValuation]

private theorem normalizedValuation_map_nonneg_iff
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (x : Units K) :
    0 ≤ normalizedValuation L (Units.map (algebraMap K L) x) ↔
      0 ≤ normalizedValuation K x := by
  letI : (valuation K).HasExtension (valuation L) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  unfold normalizedValuation normalizedValuationHom
  rw [(exists_normalizedValuationHom L).choose_spec.2,
    (exists_normalizedValuationHom K).choose_spec.2]
  simp only [Units.coe_map]
  constructor
  · rintro ⟨a, ha⟩
    have hleL : valuation L (algebraMap K L (x : K)) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    have hleK : valuation K (x : K) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mp hleL
    exact ⟨⟨x, (Valuation.mem_integer_iff _ _).mpr hleK⟩, rfl⟩
  · rintro ⟨a, ha⟩
    have hleK : valuation K (x : K) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    have hleL : valuation L (algebraMap K L (x : K)) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr hleK
    exact ⟨⟨algebraMap K L x, (Valuation.mem_integer_iff _ _).mpr hleL⟩, rfl⟩

private theorem normalizedValuation_map_eq_mul
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] :
    let e := normalizedValuation L
      (Units.map (algebraMap K L) (defaultUniformizer K).val)
    0 < e ∧ ∀ x : Units K,
      normalizedValuation L (Units.map (algebraMap K L) x) =
        e * normalizedValuation K x := by
  dsimp only
  let π := (defaultUniformizer K).val
  let e := normalizedValuation L (Units.map (algebraMap K L) π)
  have he0 : 0 ≤ e := by
    exact (normalizedValuation_map_nonneg_iff K L π).2 (by
      dsimp [π]
      rw [(defaultUniformizer K).valuation_eq_one]
      omega)
  have he : 0 < e := by
    refine he0.lt_of_ne ?_
    intro heq
    have hmapinv : normalizedValuation L
        (Units.map (algebraMap K L) π⁻¹) = 0 := by
      rw [map_inv, normalizedValuation_inv_aux, show normalizedValuation L
        (Units.map (algebraMap K L) π) = e from rfl, ← heq, neg_zero]
    have hinvnonneg : 0 ≤ normalizedValuation K π⁻¹ :=
      (normalizedValuation_map_nonneg_iff K L π⁻¹).1 hmapinv.ge
    rw [normalizedValuation_inv_aux, (defaultUniformizer K).valuation_eq_one] at hinvnonneg
    omega
  refine ⟨he, ?_⟩
  intro x
  let n := normalizedValuation K x
  let z := x * π ^ (-n)
  have hz : normalizedValuation K z = 0 := by
    rw [normalizedValuation_mul, normalizedValuation_zpow_aux]
    dsimp [n, π]
    rw [(defaultUniformizer K).valuation_eq_one]
    simp
  have hzmap_nonneg := (normalizedValuation_map_nonneg_iff K L z).2 hz.ge
  have hzinvmap_nonneg := (normalizedValuation_map_nonneg_iff K L z⁻¹).2 (by
    rw [normalizedValuation_inv_aux, hz, neg_zero])
  have hzmap : normalizedValuation L (Units.map (algebraMap K L) z) = 0 := by
    have hi : normalizedValuation L (Units.map (algebraMap K L) z)⁻¹ =
        -normalizedValuation L (Units.map (algebraMap K L) z) :=
      normalizedValuation_inv_aux L _
    rw [map_inv] at hzinvmap_nonneg
    omega
  rw [show z = x * π ^ (-n) from rfl, map_mul, map_zpow,
    normalizedValuation_mul, normalizedValuation_zpow_aux] at hzmap
  dsimp [n, e, π] at hzmap ⊢
  linear_combination hzmap

private theorem normalizedValuation_le_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    normalizedValuation K x ≤ normalizedValuation K y ↔
      valuation K (y : K) ≤ valuation K (x : K) := by
  have hnonneg : 0 ≤ normalizedValuation K (y * x⁻¹) ↔
      valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 := by
    unfold normalizedValuation normalizedValuationHom
    rw [(exists_normalizedValuationHom K).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  rw [normalizedValuation_mul, normalizedValuation_inv_aux] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation K y - normalizedValuation K x ↔
      valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change valuation K (y : K) / valuation K (x : K) ≤ 1 ↔ _
  rw [div_le_one₀ ((valuation K).pos_iff.mpr x.ne_zero)]

private theorem normalizedValuation_lt_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    normalizedValuation K x < normalizedValuation K y ↔
      valuation K (y : K) < valuation K (x : K) := by
  simpa only [not_le] using (normalizedValuation_le_iff K y x).not

private theorem continuous_algebraMap_of_valuativeExtension
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] : Continuous (algebraMap K L) := by
  obtain ⟨he, hscale⟩ := normalizedValuation_map_eq_mul K L
  let π := (defaultUniformizer K).val
  apply continuous_of_continuousAt_zero (algebraMap K L)
  rw [ContinuousAt, map_zero]
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  intro γL _
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (K := L) (γL : ValueGroupWithZero L)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact γL.ne_zero ha.symm
  let y : Units L := Units.mk0 a ha0
  let t := normalizedValuation L y
  let N : ℤ := |t| + 1
  let γK : Units (ValueGroupWithZero K) := Units.map (valuation K) (π ^ N)
  refine ⟨γK, trivial, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  let xu : Units K := Units.mk0 x hx0
  have hxN : normalizedValuation K (π ^ N) < normalizedValuation K xu := by
    apply (normalizedValuation_lt_iff K (π ^ N) xu).2
    simpa [xu, γK] using hx
  have hπN : normalizedValuation K (π ^ N) = N := by
    rw [normalizedValuation_zpow_aux]
    simp [π, (defaultUniformizer K).valuation_eq_one]
  have htN : t < N := by
    have habs := le_abs_self t
    dsimp [N]
    omega
  have hteN : t <
      normalizedValuation L (Units.map (algebraMap K L) xu) := by
    rw [hscale]
    rw [hπN] at hxN
    have hN0 : 0 ≤ N := by
      have habs := abs_nonneg t
      dsimp [N]
      omega
    have he1 : 1 ≤ normalizedValuation L
        (Units.map (algebraMap K L) (defaultUniformizer K).val) := by omega
    nlinarith
  have hlt : valuation L ((Units.map (algebraMap K L) xu : Units L) : L) <
      valuation L (y : L) :=
    (normalizedValuation_lt_iff L y (Units.map (algebraMap K L) xu)).1 hteN
  simpa [xu, y, ha] using hlt

/-- The ring of integers of a finite local-field extension is finite over the base ring of
integers. -/
theorem ringOfIntegers_module_finite
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    [(valuation K).HasExtension (valuation L)] : Module.Finite 𝒪[K] 𝒪[L] := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := IsTopologicalAddGroup.rightUniformSpace L
  letI := isUniformAddGroup_of_addCommGroup (G := L)
  letI : ContinuousSMul K L := ⟨by
    have h : Continuous (fun p : K × L => algebraMap K L p.1 * p.2) :=
      (((continuous_algebraMap_of_valuativeExtension K L).comp continuous_fst).mul
        continuous_snd).congr (fun _ => rfl)
    simpa only [Algebra.smul_def] using h⟩
  letI : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  let b := Module.Free.chooseBasis K L
  let coord (i) : L →ₗ[K] K :=
    { toFun := fun x => b.repr x i
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hcoord (i) : Continuous (fun x : L => b.repr x i) := by
    exact LinearMap.continuous_of_finiteDimensional (coord i)
  have hcompact (i) : IsCompact (Set.range fun x : 𝒪[L] => b.repr (x : L) i) := by
    simpa only [Set.image_univ, Function.comp_apply] using
      isCompact_univ.image ((hcoord i).comp continuous_subtype_val)
  have hbounded (i) : Bornology.IsBounded
      (Set.range fun x : 𝒪[L] => b.repr (x : L) i) := (hcompact i).isBounded
  choose C hC using fun i => (Metric.isBounded_iff_subset_closedBall (0 : K)).1 (hbounded i)
  let D : ℝ := ∑ i, max (C i) 0
  have hC_nonneg (i) : 0 ≤ C i := by
    have hzero : (0 : K) ∈ Set.range (fun x : 𝒪[L] => b.repr (x : L) i) :=
      ⟨0, by simp⟩
    have := hC i hzero
    simpa using this
  have hCiD (i) : C i ≤ D := by
    dsimp [D]
    apply Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i) |>.trans'
    exact le_max_left _ _
  obtain ⟨q : K, hq0, hq1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨n : ℕ, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1 : ℝ) / (D + 1) by positivity) hq1
  let c : K := q ^ n
  have hc0 : c ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp hq0)
  have hcD : ‖c‖ * D ≤ 1 := by
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hnormc : ‖c‖ < 1 / (D + 1) := by simpa [c, norm_pow] using hn
    have hDlt : D < D + 1 := by linarith
    have hmul : ‖c‖ * D < (1 / (D + 1)) * (D + 1) := by
      gcongr
    have hD1 : D + 1 ≠ 0 := by linarith
    rw [one_div, inv_mul_cancel₀ hD1] at hmul
    exact hmul.le
  let g (i) : L := c⁻¹ • b i
  let lattice : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range g)
  letI : Module.Finite 𝒪[K] lattice :=
    Module.Finite.span_of_finite 𝒪[K] (Set.finite_range g)
  let toL : 𝒪[L] →ₗ[𝒪[K]] L :=
    (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap
  have hmem (x : 𝒪[L]) : toL x ∈ lattice := by
    apply (Submodule.mem_span_range_iff_exists_fun 𝒪[K]).2
    let a (i) : 𝒪[K] := ⟨c * b.repr (x : L) i, by
      apply (Valuation.mem_integer_iff _ _).mpr
      apply Valued.toNormedField.norm_le_one_iff.mp
      calc
        ‖c * b.repr (x : L) i‖ = ‖c‖ * ‖b.repr (x : L) i‖ := norm_mul _ _
        _ ≤ ‖c‖ * C i := by
          gcongr
          have hi := hC i ⟨x, rfl⟩
          simpa [Metric.mem_closedBall, dist_zero_right] using hi
        _ ≤ ‖c‖ * D := mul_le_mul_of_nonneg_left (hCiD i) (norm_nonneg _)
        _ ≤ 1 := hcD⟩
    refine ⟨a, ?_⟩
    change ∑ i, ((a i : 𝒪[K]) : K) • g i = (x : L)
    calc
      ∑ i, ((a i : 𝒪[K]) : K) • g i =
          ∑ i, b.repr (x : L) i • b i := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [a, g, smul_smul]
            congr 1
            field_simp
      _ = (x : L) := b.sum_repr (x : L)
  let f : 𝒪[L] →ₗ[𝒪[K]] lattice := LinearMap.codRestrict lattice toL hmem
  exact Module.Finite.of_injective f (fun x y h => by
    apply Subtype.ext
    exact congr_arg (fun z : lattice => (z : L)) h)

private theorem isUnit_of_normalizedValuation_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (a : 𝒪[K]) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [normalizedValuation_inv_aux, hval, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units 𝒪[K] :=
    { val := a
      inv := b
      val_inv := by
        apply Subtype.ext
        change (a : K) * (b : K) = 1
        rw [hb]
        exact mul_inv_cancel₀ ha
      inv_val := by
        apply Subtype.ext
        change (b : K) * (a : K) = 1
        rw [hb]
        exact inv_mul_cancel₀ ha }
  exact ⟨u, rfl⟩

/-- A normalized uniformizer represented in the valuation ring; it is irreducible there. -/
theorem integral_normalizedUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ ϖ : 𝒪[K], (ϖ : K) = ((defaultUniformizer K).val : K) ∧ Irreducible ϖ := by
  let π := (defaultUniformizer K).val
  have hπnonneg : 0 ≤ normalizedValuation K π := by
    dsimp [π]
    rw [(defaultUniformizer K).valuation_eq_one]
    omega
  obtain ⟨ϖ, hϖ⟩ := (exists_normalizedValuationHom K).choose_spec.2 π |>.1 hπnonneg
  refine ⟨ϖ, hϖ, (irreducible_iff.mpr ⟨?_, ?_⟩)⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation K
        (Units.map (algebraMap 𝒪[K] K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap 𝒪[K] K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap 𝒪[K] K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units 𝒪[K]), rfl⟩
      rw [normalizedValuation_inv_aux] at hinvnonneg
      omega
    have heq : Units.map (algebraMap 𝒪[K] K) u = π := by
      apply Units.ext
      change (((u : Units 𝒪[K]) : 𝒪[K]) : K) = (π : K)
      rw [hu, hϖ]
    rw [heq, (defaultUniformizer K).valuation_eq_one] at huval
    omega
  · intro a b hab
    have ha0 : (a : K) ≠ 0 := by
      intro ha
      have : (ϖ : K) = 0 := by rw [hab]; simp [ha]
      apply π.ne_zero
      rw [← hϖ]
      exact this
    have hb0 : (b : K) ≠ 0 := by
      intro hb
      have : (ϖ : K) = 0 := by rw [hab]; simp [hb]
      apply π.ne_zero
      rw [← hϖ]
      exact this
    let ua : Units K := Units.mk0 (a : K) ha0
    let ub : Units K := Units.mk0 (b : K) hb0
    have hva : 0 ≤ normalizedValuation K ua :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨a, rfl⟩
    have hvb : 0 ≤ normalizedValuation K ub :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨b, rfl⟩
    have huv : ua * ub = π := by
      apply Units.ext
      simpa [ua, ub, ← hϖ] using congr_arg Subtype.val hab.symm
    have hvsum : normalizedValuation K ua + normalizedValuation K ub = 1 := by
      rw [← normalizedValuation_mul, huv, (defaultUniformizer K).valuation_eq_one]
    rcases (show normalizedValuation K ua = 0 ∨ normalizedValuation K ub = 0 by omega) with ha | hb
    · exact Or.inl (isUnit_of_normalizedValuation_eq_zero K a ha0 ha)
    · exact Or.inr (isUnit_of_normalizedValuation_eq_zero K b hb0 hb)

/-- An integral unit has normalized valuation zero. -/
theorem normalizedValuation_ringUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : Units 𝒪[K]) :
    normalizedValuation K (Units.map (algebraMap 𝒪[K] K) u) = 0 := by
  have hnonneg : 0 ≤ normalizedValuation K
      (Units.map (algebraMap 𝒪[K] K) u) :=
    (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
  have hinvnonneg : 0 ≤ normalizedValuation K
      (Units.map (algebraMap 𝒪[K] K) u)⁻¹ :=
    (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
      ⟨(u⁻¹ : Units 𝒪[K]), rfl⟩
  rw [normalizedValuation_inv_aux] at hinvnonneg
  omega

/--
**A01**, foundational result (F3): existence of the ramification index and residue degree, the
extension formula for normalized valuations, and the identity `[L:K] = e f`.
-/
theorem ramificationInvariants_exists :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
      (∀ x : Units K,
        normalizedValuation L (Units.map (algebraMap K L) x) =
          (e : ℤ) * normalizedValuation K x) ∧
      Module.finrank K L = e * f := by
  letI : (valuation K).HasExtension (valuation L) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  letI : Module.Finite 𝒪[K] 𝒪[L] := ringOfIntegers_module_finite K L
  obtain ⟨heZ, hscale⟩ := normalizedValuation_map_eq_mul K L
  let eZ : ℤ := normalizedValuation L
    (Units.map (algebraMap K L) (defaultUniformizer K).val)
  let e : ℕ := eZ.toNat
  have hecast : (e : ℤ) = eZ := by
    rw [Int.toNat_of_nonneg heZ.le]
  have he : 0 < e := by omega
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer K
  obtain ⟨ϖL, hϖL, hϖLirr⟩ := integral_normalizedUniformizer L
  let mϖ : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : 𝒪[L] => (z : L)) h
    have : algebraMap K L (ϖK : K) = 0 := by simpa [mϖ] using h'
    apply hϖKirr.ne_zero
    apply Subtype.ext
    exact (algebraMap K L).injective (by simpa using this)
  obtain ⟨n, u, hfac⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmϖ0 hϖLirr
  let xu : Units L := Units.map (algebraMap 𝒪[L] L) u
  have hfacUnits : Units.map (algebraMap K L) (defaultUniformizer K).val =
      xu * (defaultUniformizer L).val ^ n := by
    apply Units.ext
    change algebraMap K L (((defaultUniformizer K).val : Units K) : K) =
      algebraMap 𝒪[L] L (u : 𝒪[L]) * (((defaultUniformizer L).val : Units L) : L) ^ n
    rw [show algebraMap 𝒪[L] L (u : 𝒪[L]) = (((u : Units 𝒪[L]) : 𝒪[L]) : L) from rfl,
      ← hϖK]
    simpa [mϖ, hϖL] using congr_arg (fun z : 𝒪[L] => (z : L)) hfac
  have hnZ : (n : ℤ) = eZ := by
    have hval := congr_arg (normalizedValuation L) hfacUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit] at hval
    have hpow : normalizedValuation L ((defaultUniformizer L).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom L ((defaultUniformizer L).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation L (defaultUniformizer L).val = _
      rw [(defaultUniformizer L).valuation_eq_one, mul_one]
    rw [hpow] at hval
    change eZ = 0 + (n : ℤ) at hval
    omega
  have hn : n = e := by exact_mod_cast hnZ.trans hecast.symm
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let P : Ideal 𝒪[L] := IsLocalRing.maximalIdeal 𝒪[L]
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖL} := hϖLirr.maximalIdeal_eq
  have hmap : Ideal.map (algebraMap 𝒪[K] 𝒪[L]) p = P ^ e := by
    rw [hp, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {mϖ} = P ^ e
    rw [hfac, Ideal.span_singleton_mul_left_unit u.isUnit, hn, hP,
      Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map (algebraMap 𝒪[K] 𝒪[L]) p ≤ P ^ (e + 1) := by
    rw [hmap]
    intro hle
    have heq : P ^ e = P ^ (e + 1) :=
      le_antisymm hle (Ideal.pow_le_pow_right (Nat.le_succ e))
    have hc := congr_arg Order.coheight heq
    rw [show P = IsLocalRing.maximalIdeal 𝒪[L] from rfl,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
    have : e = e + 1 := by exact_mod_cast hc
    omega
  have hram : p.ramificationIdx P = e := Ideal.ramificationIdx_spec hmap.le hnot
  have hp0 : p ≠ ⊥ := by
    rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
    exact hϖKirr.ne_zero
  have hdegree := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (S := 𝒪[L]) K L (p := p) hp0
  let f := p.inertiaDeg P
  have hf : 0 < f := Ideal.inertiaDeg_pos p P
  refine ⟨e, f, he, hf, ?_, ?_⟩
  · intro x
    rw [hecast]
    exact hscale x
  · rw [← hdegree, show IsLocalRing.maximalIdeal 𝒪[L] = P from rfl, hram]

/-- The ramification index selected by `ramificationInvariants_exists`. -/
noncomputable def ramificationIndex : ℕ :=
  (ramificationInvariants_exists K L).choose

/-- The residue degree selected compatibly with `ramificationIndex`. -/
noncomputable def residueDegree : ℕ :=
  (ramificationInvariants_exists K L).choose_spec.choose

/-- **A01**, foundational result (F3): the extension valuation is multiplied by `e(L/K)`. -/
theorem normalizedValuation_algebraMap (x : Units K) :
    normalizedValuation L (Units.map (algebraMap K L) x) =
      (ramificationIndex K L : ℤ) * normalizedValuation K x := by
  dsimp [ramificationIndex]
  exact (ramificationInvariants_exists K L).choose_spec.choose_spec.2.2.1 x

/-- **A01**, foundational result (F3): `[L:K] = e(L/K) f(L/K)`. -/
theorem finrank_eq_ramificationIndex_mul_residueDegree :
    Module.finrank K L = ramificationIndex K L * residueDegree K L := by
  dsimp [ramificationIndex, residueDegree]
  exact (ramificationInvariants_exists K L).choose_spec.choose_spec.2.2.2

/-- Valuation-theoretic unramifiedness for an extension of local fields. -/
class IsUnramifiedLocalExtension : Prop where
  /-- The ramification index is one. -/
  ramificationIndex_eq_one : ramificationIndex K L = 1

end Ramification

section UnitFiltration

variable (K : Type u) [Field K] [ValuativeRel K]

/-- The homomorphism from integral units to field units. -/
def ringUnitsToFieldUnits : Units (RingOfIntegers K) →* Units K :=
  Units.map (algebraMap (RingOfIntegers K) K)

/-- The subgroup `𝒪_Kˣ ≤ Kˣ`. -/
def unitSubgroup : Subgroup (Units K) :=
  (ringUnitsToFieldUnits K).range

/-- Reduction of integral units modulo `𝔪_K^r`. -/
def integralUnitReduction (r : ℕ) :
    Units (RingOfIntegers K) →* Units (RingOfIntegers K ⧸ LocalMaximalIdeal K ^ r) :=
  Units.map (Ideal.Quotient.mk (LocalMaximalIdeal K ^ r))

/--
The principal-unit subgroup `U_K^r`, defined as the image in `Kˣ` of integral units reducing to
one modulo `𝔪_K^r`.
-/
def principalUnitSubgroup (r : ℕ) : Subgroup (Units K) :=
  (integralUnitReduction K r).ker.map (ringUnitsToFieldUnits K)

/-- The filtration `U_K^{r+1} ≤ U_K^r`. -/
theorem principalUnitSubgroup_antitone {r s : ℕ} (h : r ≤ s) :
    principalUnitSubgroup K s ≤ principalUnitSubgroup K r := by
  rintro x ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  change integralUnitReduction K r u = 1
  apply Units.ext
  change Ideal.Quotient.mk (LocalMaximalIdeal K ^ r) (u : RingOfIntegers K) =
    Ideal.Quotient.mk (LocalMaximalIdeal K ^ r) 1
  rw [Ideal.Quotient.eq]
  apply Ideal.pow_le_pow_right h
  apply Ideal.Quotient.eq.mp
  exact congr_arg Units.val hu

/-- The subgroup `U_K^r`, viewed inside `U_K^1`. -/
def principalUnitFiltrationWithin (r : ℕ) : Subgroup (principalUnitSubgroup K 1) :=
  (principalUnitSubgroup K (r + 1)).comap (principalUnitSubgroup K 1).subtype

/-- Successive terms of the filtration inside `U_K^1` decrease. -/
theorem principalUnitFiltrationWithin_succ_le (r : ℕ) :
    principalUnitFiltrationWithin K (r + 1) ≤ principalUnitFiltrationWithin K r := by
  intro x hx
  exact principalUnitSubgroup_antitone K (Nat.le_succ (r + 1)) hx

end UnitFiltration

/-- Compatible residue classes in the `I`-adic inverse system `R/I^n`. -/
structure AdicCompatibleFamily (R : Type u) [CommRing R] (I : Ideal R) where
  /-- The residue class at level `n`. -/
  value : (n : ℕ) → R ⧸ I ^ n
  /-- Compatibility under `R/I^(n+1) → R/I^n`. -/
  compatible : ∀ n,
    Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (value (n + 1)) = value n

/-- The natural projection between quotients by nested subgroups. -/
noncomputable def quotientProjection {G : Type u} [CommGroup G]
    {H N : Subgroup G} (h : H ≤ N) : G ⧸ H →* G ⧸ N :=
  QuotientGroup.map H N (MonoidHom.id G) (by simpa using h)

/-- A concrete inverse limit of quotients by a decreasing sequence of subgroups. -/
structure SubgroupInverseLimit {G : Type u} [CommGroup G]
    (F : ℕ → Subgroup G) (hF : ∀ n, F (n + 1) ≤ F n) where
  /-- The quotient class at level `n`. -/
  value : (n : ℕ) → G ⧸ F n
  /-- Compatibility under quotient projection. -/
  compatible : ∀ n, quotientProjection (hF n) (value (n + 1)) = value n

section Lattices

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (V : Type v) [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul K V] [FiniteDimensional K V]

/-- A compact open `𝒪_K`-lattice in a finite-dimensional `K`-vector space. -/
structure IsCompactOpenLattice (Λ : Submodule (RingOfIntegers K) V) : Prop where
  /-- Compactness of the underlying subset. -/
  isCompact : IsCompact (Λ : Set V)
  /-- Openness of the underlying subset. -/
  isOpen : IsOpen (Λ : Set V)

/--
**A03**, Lemma `lem:lattices` (Commensurability of lattices): two compact open lattices have
finite quotients by their intersection.
-/
theorem compactOpenLattices_commensurable
    (Λ Γ : Submodule (RingOfIntegers K) V)
    (hΛ : IsCompactOpenLattice K V Λ) (hΓ : IsCompactOpenLattice K V Γ) :
    Finite (Λ ⧸ (Λ ⊓ Γ).comap Λ.subtype) ∧
      Finite (Γ ⧸ (Λ ⊓ Γ).comap Γ.subtype) := by
  constructor
  · letI : CompactSpace Λ := isCompact_iff_compactSpace.mp hΛ.isCompact
    apply AddSubgroup.quotient_finite_of_isOpen
    change IsOpen {x : Λ | (x : V) ∈ Λ ∧ (x : V) ∈ Γ}
    convert hΓ.isOpen.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    exact and_iff_right x.prop
  · letI : CompactSpace Γ := isCompact_iff_compactSpace.mp hΓ.isCompact
    apply AddSubgroup.quotient_finite_of_isOpen
    change IsOpen {x : Γ | (x : V) ∈ Λ ∧ (x : V) ∈ Γ}
    convert hΛ.isOpen.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    exact and_iff_left x.prop

end Lattices

section Completeness

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K]
  [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/--
**A04**, Lemma `lem:unit-separated`: `𝒪_K` is the inverse limit of its quotients by powers of
`𝔪_K`; the equivalence records the canonical residue maps.
-/
theorem ringOfIntegers_inverseLimit :
    ∃ e : RingOfIntegers K ≃
        AdicCompatibleFamily (RingOfIntegers K) (LocalMaximalIdeal K),
      ∀ (x : RingOfIntegers K) n,
        (e x).value n = Ideal.Quotient.mk (LocalMaximalIdeal K ^ n) x := by
  let R := RingOfIntegers K
  have family_ext {R : Type u} [CommRing R] {I : Ideal R}
      (a b : AdicCompatibleFamily R I) (h : a.value = b.value) : a = b := by
    cases a
    cases b
    simp_all
  let I : Ideal R := LocalMaximalIdeal K
  have hLift (c : AdicCompatibleFamily R I) : ∃ L : R, ∀ n,
      Ideal.Quotient.mk (I ^ n) L = c.value n := by
    choose f hf using fun n => Ideal.Quotient.mk_surjective (c.value n)
    have hc : ∀ {m n : ℕ} (h : m ≤ n),
        c.value m = Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c.value n) := by
      intro m n h
      exact Ideal.Quotient.eq_factor_of_eq_factor_succ
        (fun _ _ h => Ideal.pow_le_pow_right h) c.value
        (fun k => (c.compatible k).symm) h
    have hfCauchy : ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro m n h
      have hq : Ideal.Quotient.mk (I ^ m) (f m) =
          Ideal.Quotient.mk (I ^ m) (f n) := by
        calc
          _ = c.value m := hf m
          _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c.value n) := hc h
          _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
                (Ideal.Quotient.mk (I ^ n) (f n)) := congrArg _ (hf n).symm
          _ = _ := Ideal.Quotient.factor_mk _ _
      rw [SModEq.sub_mem]
      simpa [Ideal.smul_top_eq_map] using Ideal.Quotient.eq.mp hq
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete I R).prec hfCauchy
    refine ⟨L, fun n => ?_⟩
    rw [← hf n, Ideal.Quotient.eq]
    simpa [Ideal.smul_top_eq_map, SModEq.sub_mem] using (hL n).symm
  let liftFamily : AdicCompatibleFamily R I → R := fun c => (hLift c).choose
  have liftFamily_spec (c : AdicCompatibleFamily R I) (n : ℕ) :
      Ideal.Quotient.mk (I ^ n) (liftFamily c) = c.value n := (hLift c).choose_spec n
  let toFamily : R → AdicCompatibleFamily R I := fun x =>
    { value := fun n => Ideal.Quotient.mk (I ^ n) x
      compatible := fun n => by rfl }
  let e : R ≃ AdicCompatibleFamily R I :=
    { toFun := toFamily
      invFun := liftFamily
      left_inv := fun x => by
        rw [IsHausdorff.eq_iff_smodEq (I := I)]
        intro n
        simpa [Ideal.smul_top_eq_map, Ideal.Quotient.eq, SModEq.sub_mem] using
          Ideal.Quotient.eq.mp (liftFamily_spec (toFamily x) n)
      right_inv := fun c => family_ext _ _ (funext fun n => liftFamily_spec c n) }
  exact ⟨e, fun x n => rfl⟩

/--
**A04**, Lemma `lem:unit-separated`: `U_K^1` is the inverse limit of
`U_K^1/U_K^{r+1}`.
-/
theorem principalUnits_inverseLimit :
    ∃ e : (principalUnitSubgroup K 1) ≃
        SubgroupInverseLimit (principalUnitFiltrationWithin K)
          (principalUnitFiltrationWithin_succ_le K),
      ∀ (x : principalUnitSubgroup K 1) n,
        (e x).value n =
          (QuotientGroup.mk x :
            (principalUnitSubgroup K 1) ⧸ principalUnitFiltrationWithin K n) := by
  let R := RingOfIntegers K
  let I : Ideal R := LocalMaximalIdeal K
  let G := principalUnitSubgroup K 1
  let F : ℕ → Subgroup G := principalUnitFiltrationWithin K
  let hF : ∀ n, F (n + 1) ≤ F n := principalUnitFiltrationWithin_succ_le K
  have limit_ext (a b : SubgroupInverseLimit F hF) (h : a.value = b.value) : a = b := by
    cases a
    cases b
    simp_all
  have hMapInj : Function.Injective (ringUnitsToFieldUnits K) :=
    Units.map_injective (fun _ _ h => Subtype.ext h)
  have hRep (x : G) : ∃ u : Units R,
      u ∈ (integralUnitReduction K 1).ker ∧ ringUnitsToFieldUnits K u = x := by
    exact x.prop
  let rep (x : G) : Units R := (hRep x).choose
  have rep_mem (x : G) : rep x ∈ (integralUnitReduction K 1).ker :=
    (hRep x).choose_spec.1
  have rep_map (x : G) : ringUnitsToFieldUnits K (rep x) = x :=
    (hRep x).choose_spec.2
  have rep_smodEq_of_mk_eq {x y : G} (n : ℕ)
      (hxy : (QuotientGroup.mk x : G ⧸ F n) = QuotientGroup.mk y) :
      (rep x : R) ≡ (rep y : R) [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    have hdiv : x / y ∈ F n := QuotientGroup.eq_iff_div_mem.mp hxy
    obtain ⟨w, hw, hwmap⟩ := hdiv
    have hwEq : w = rep x / rep y := by
      apply hMapInj
      rw [map_div, rep_map, rep_map]
      exact hwmap
    have hqw : Ideal.Quotient.mk (I ^ (n + 1)) (w : R) =
        Ideal.Quotient.mk (I ^ (n + 1)) 1 := by
      exact congr_arg Units.val hw
    have hqrep : Ideal.Quotient.mk (I ^ (n + 1)) (rep x : R) =
        Ideal.Quotient.mk (I ^ (n + 1)) (rep y : R) := by
      calc
        _ = Ideal.Quotient.mk (I ^ (n + 1)) ((w * rep y : Units R) : R) := by
          rw [hwEq]
          simp
        _ = Ideal.Quotient.mk (I ^ (n + 1)) (w : R) *
              Ideal.Quotient.mk (I ^ (n + 1)) (rep y : R) := by
          simp only [Units.val_mul, map_mul]
        _ = Ideal.Quotient.mk (I ^ (n + 1)) 1 *
              Ideal.Quotient.mk (I ^ (n + 1)) (rep y : R) := by rw [hqw]
        _ = _ := by simp
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_top_eq_map] using
      Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.mp hqrep)
  let toLimit : G → SubgroupInverseLimit F hF := fun x =>
    { value := fun n => (QuotientGroup.mk x : G ⧸ F n)
      compatible := fun n => by simp [quotientProjection] }
  have toLimit_injective : Function.Injective toLimit := by
    intro x y hxy
    have hsmod : ∀ n : ℕ, (rep x : R) ≡ (rep y : R)
        [SMOD (I ^ n • ⊤ : Submodule R R)] := by
      intro n
      apply rep_smodEq_of_mk_eq
      exact congr_arg (fun c => c.value n) hxy
    have hrepEq : rep x = rep y := by
      apply Units.ext
      exact IsHausdorff.eq_iff_smodEq.mpr hsmod
    apply Subtype.ext
    rw [← rep_map x, ← rep_map y, hrepEq]
  have toLimit_surjective : Function.Surjective toLimit := by
    intro c
    let x : ℕ → G := fun n => Quotient.out (c.value n)
    have hxout (n : ℕ) : (QuotientGroup.mk (x n) : G ⧸ F n) = c.value n :=
      Quotient.out_eq _
    have hxstep (n : ℕ) :
        (QuotientGroup.mk (x (n + 1)) : G ⧸ F n) = QuotientGroup.mk (x n) := by
      calc
        _ = quotientProjection (hF n)
              (QuotientGroup.mk (x (n + 1)) : G ⧸ F (n + 1)) := by
            simp [quotientProjection]
        _ = quotientProjection (hF n) (c.value (n + 1)) := by rw [hxout]
        _ = c.value n := c.compatible n
        _ = _ := (hxout n).symm
    have hstep (n : ℕ) :
        (rep (x n) : R) ≡ (rep (x (n + 1)) : R)
          [SMOD (I ^ n • ⊤ : Submodule R R)] := by
      exact rep_smodEq_of_mk_eq n (hxstep n).symm
    have hCauchy : ∀ {m n : ℕ}, m ≤ n →
        (rep (x m) : R) ≡ (rep (x n) : R)
          [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      induction hmn with
      | refl => exact SModEq.rfl
      | @step n hmn ih =>
          exact ih.trans ((hstep n).mono (by
            simpa [Ideal.smul_top_eq_map] using Ideal.pow_le_pow_right hmn))
    obtain ⟨a, ha⟩ := (inferInstance : IsPrecomplete I R).prec hCauchy
    have haUnit : IsUnit a := by
      by_contra h
      have haM : a ∈ I := (IsLocalRing.mem_maximalIdeal a).mpr
        ((mem_nonunits_iff).mpr h)
      have hadiff : a - (rep (x 1) : R) ∈ I := by
        have := (ha 1).symm
        simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using this
      have huM : (rep (x 1) : R) ∈ I := by
        have := I.sub_mem haM hadiff
        simpa using this
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp huM))
        (rep (x 1)).isUnit
    let ua : Units R := haUnit.unit
    have huaVal : (ua : R) = a := haUnit.unit_spec
    have huaKer : ua ∈ (integralUnitReduction K 1).ker := by
      change integralUnitReduction K 1 ua = 1
      have hq : Ideal.Quotient.mk (I ^ 1) (ua : R) =
          Ideal.Quotient.mk (I ^ 1) 1 := by
        calc
          _ = Ideal.Quotient.mk (I ^ 1) a := by rw [huaVal]
          _ = Ideal.Quotient.mk (I ^ 1) (rep (x 1) : R) := by
            rw [Ideal.Quotient.eq]
            have := (ha 1).symm
            simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using this
          _ = Ideal.Quotient.mk (I ^ 1) 1 := by
            have := congr_arg Units.val (rep_mem (x 1))
            simpa [I, integralUnitReduction] using this
      apply Units.ext
      simpa [I, integralUnitReduction] using hq
    let z : G := ⟨ringUnitsToFieldUnits K ua, ⟨ua, huaKer, rfl⟩⟩
    have hzmem (n : ℕ) : z / x (n + 1) ∈ F n := by
      let w : Units R := ua / rep (x (n + 1))
      have hwker : w ∈ (integralUnitReduction K (n + 1)).ker := by
        change integralUnitReduction K (n + 1) w = 1
        have hqa : Ideal.Quotient.mk (I ^ (n + 1)) (ua : R) =
            Ideal.Quotient.mk (I ^ (n + 1)) (rep (x (n + 1)) : R) := by
          rw [Ideal.Quotient.eq, huaVal]
          have := (ha (n + 1)).symm
          simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using this
        have hqaU : Units.map (Ideal.Quotient.mk (I ^ (n + 1))).toMonoidHom ua =
            Units.map (Ideal.Quotient.mk (I ^ (n + 1))).toMonoidHom
              (rep (x (n + 1))) := by
          apply Units.ext
          change Ideal.Quotient.mk (I ^ (n + 1)) (ua : R) =
            Ideal.Quotient.mk (I ^ (n + 1)) (rep (x (n + 1)) : R)
          exact hqa
        change Units.map (Ideal.Quotient.mk (I ^ (n + 1))).toMonoidHom w = 1
        rw [show w = ua / rep (x (n + 1)) from rfl, map_div, hqaU]
        simp
      refine ⟨w, hwker, ?_⟩
      change ringUnitsToFieldUnits K w = (z : G) / x (n + 1)
      simp [w, z, rep_map]
    have hzc : toLimit z = c := by
      apply limit_ext
      funext n
      exact (QuotientGroup.eq_iff_div_mem.mpr (hzmem n)).trans (hxstep n) |>.trans (hxout n)
    exact ⟨z, hzc⟩
  let e : G ≃ SubgroupInverseLimit F hF := Equiv.ofBijective toLimit
    ⟨toLimit_injective, toLimit_surjective⟩
  refine ⟨e, ?_⟩
  intro x n
  rfl

set_option linter.unusedSectionVars false in
/--
**A04**, Lemma `lem:unit-separated`: the principal-unit filtration is separated.
-/
theorem iInf_principalUnitSubgroup :
    (⨅ r : ℕ, principalUnitSubgroup K (r + 1)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxall : ∀ r : ℕ, x ∈ principalUnitSubgroup K (r + 1) := by
    simpa only [Subgroup.mem_iInf] using hx
  obtain ⟨u, hu, hux⟩ := hxall 0
  have hmapinj : Function.Injective (ringUnitsToFieldUnits K) :=
    Units.map_injective (fun _ _ h => Subtype.ext h)
  have huCongr : ∀ n : ℕ, (u : RingOfIntegers K) ≡ 1
      [SMOD (LocalMaximalIdeal K ^ n • ⊤ :
        Submodule (RingOfIntegers K) (RingOfIntegers K))] := by
    intro n
    obtain ⟨w, hw, hwx⟩ := hxall n
    have hwu : w = u := hmapinj (hwx.trans hux.symm)
    subst w
    rw [SModEq.sub_mem]
    have hq : Ideal.Quotient.mk (LocalMaximalIdeal K ^ (n + 1))
        (u : RingOfIntegers K) = Ideal.Quotient.mk (LocalMaximalIdeal K ^ (n + 1)) 1 := by
      exact congr_arg Units.val hw
    have hm : (u : RingOfIntegers K) - 1 ∈ LocalMaximalIdeal K ^ (n + 1) :=
      Ideal.Quotient.eq.mp hq
    simpa [Ideal.smul_top_eq_map] using
      (Ideal.pow_le_pow_right (Nat.le_succ n) hm)
  have hu1 : (u : RingOfIntegers K) = 1 :=
    IsHausdorff.eq_iff_smodEq.mpr huCongr
  have : u = 1 := Units.ext hu1
  rw [← hux, this, map_one]
  exact Subgroup.one_mem _

end Completeness

section UnramifiedTower

variable (K : Type u) (Ksep : Type v) [Field K] [Field Ksep] [Algebra K Ksep]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/--
Valuation-theoretic unramifiedness for a finite intermediate field.  Mathlib does not install
local-field structures on an arbitrary finite `IntermediateField`, so this proposition includes a
choice of such structures, compatibility of scalar multiplication, and ramification index one.
The choice projections below expose one coherent instance bundle to tower and compositum clients.
-/
def IsUnramifiedIntermediateField (E : IntermediateField K Ksep)
    [FiniteDimensional K E] : Prop :=
  ∃ vE : ValuativeRel E, ∃ tE : TopologicalSpace E,
    letI : ValuativeRel E := vE
    letI : TopologicalSpace E := tE
    ∃ hE : IsNonarchimedeanLocalField E,
      letI : IsNonarchimedeanLocalField E := hE
      ∃ hKE : ValuativeExtension K E,
        letI : ValuativeExtension K E := hKE
        ContinuousSMul K E ∧ IsUnramifiedLocalExtension K E

/-- The valuation relation selected by unramified intermediate-field evidence. -/
noncomputable def unramifiedIntermediateFieldValuativeRel
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) : ValuativeRel E :=
  hE.choose

/-- The topology selected compatibly with the unramified intermediate-field valuation. -/
noncomputable def unramifiedIntermediateFieldTopology
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) : TopologicalSpace E :=
  hE.choose_spec.choose

/-- The selected intermediate field is a nonarchimedean local field. -/
noncomputable def unramifiedIntermediateFieldLocalField
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    IsNonarchimedeanLocalField E :=
  hE.choose_spec.choose_spec.choose

/-- The selected valuation on an unramified intermediate field extends the base valuation. -/
noncomputable def unramifiedIntermediateFieldValuativeExtension
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    ValuativeExtension K E :=
  hE.choose_spec.choose_spec.choose_spec.choose

/-- Scalar multiplication is continuous for the selected intermediate-field topology. -/
noncomputable def unramifiedIntermediateFieldContinuousSMul
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    letI : ValuativeExtension K E :=
      unramifiedIntermediateFieldValuativeExtension K Ksep E hE
    ContinuousSMul K E :=
  hE.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- The selected local-field extension has ramification index one. -/
noncomputable def unramifiedIntermediateFieldIsUnramified
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    letI : ValuativeExtension K E :=
      unramifiedIntermediateFieldValuativeExtension K Ksep E hE
    IsUnramifiedLocalExtension K E :=
  hE.choose_spec.choose_spec.choose_spec.choose_spec.2

/-- The canonical algebra structure attached to an inclusion of intermediate fields. -/
def intermediateFieldInclusionAlgebra {E F : IntermediateField K Ksep} (h : E ≤ F) :
    Algebra E F :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/--
Local-field and scalar-tower data on the compositum `E ⊔ U`.  The structure on `U` is the one
selected by its `IsUnramifiedIntermediateField` evidence, while the given structure on `E` is
left unchanged.  This is the transport package needed to use a tower level in the compositum
`E U`: it exposes all finite-dimensional, Galois, valuation, topology, and unramified-over-`E`
instances required by descent.
-/
structure UnramifiedCompositumLocalFieldData
    (E U : IntermediateField K Ksep)
    [FiniteDimensional K E] [FiniteDimensional K U]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K E] [ContinuousSMul K E]
    (hE : IsGalois K E) (hU : IsGalois K U)
    (hunr : IsUnramifiedIntermediateField K Ksep U) where
  /-- The valuation relation on the compositum. -/
  compositumValuativeRel : ValuativeRel (E ⊔ U : IntermediateField K Ksep)
  /-- The compatible topology on the compositum. -/
  compositumTopology : TopologicalSpace (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is a nonarchimedean local field. -/
  compositumLocalField :
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    IsNonarchimedeanLocalField (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is finite over the left field. -/
  finiteDimensional_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    FiniteDimensional E (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is finite over the unramified tower level. -/
  finiteDimensional_right :
    letI : Algebra U (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_right
    FiniteDimensional U (E ⊔ U : IntermediateField K Ksep)
  /-- The displayed `K/E/(E ⊔ U)` algebra structures form a scalar tower. -/
  scalarTower_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    IsScalarTower K E (E ⊔ U : IntermediateField K Ksep)
  /-- The displayed `K/U/(E ⊔ U)` algebra structures form a scalar tower. -/
  scalarTower_right :
    letI : Algebra U (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_right
    IsScalarTower K U (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is Galois over `K`. -/
  isGalois_base : IsGalois K (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is Galois over `E`. -/
  isGalois_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    IsGalois E (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum valuation extends the base valuation. -/
  valuativeExtension_base :
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    letI : IsNonarchimedeanLocalField (E ⊔ U : IntermediateField K Ksep) := compositumLocalField
    ValuativeExtension K (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum valuation extends the valuation on `E`. -/
  valuativeExtension_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    letI : IsNonarchimedeanLocalField (E ⊔ U : IntermediateField K Ksep) := compositumLocalField
    ValuativeExtension E (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum valuation extends the selected valuation on `U`. -/
  valuativeExtension_right :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hunr
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hunr
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hunr
    letI : Algebra U (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_right
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    letI : IsNonarchimedeanLocalField (E ⊔ U : IntermediateField K Ksep) := compositumLocalField
    ValuativeExtension U (E ⊔ U : IntermediateField K Ksep)
  /-- Scalar multiplication by `K` on the compositum is continuous. -/
  continuousSMul_base :
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    ContinuousSMul K (E ⊔ U : IntermediateField K Ksep)
  /-- Scalar multiplication by `E` on the compositum is continuous. -/
  continuousSMul_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    ContinuousSMul E (E ⊔ U : IntermediateField K Ksep)
  /-- Scalar multiplication by `U` on the compositum is continuous. -/
  continuousSMul_right :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hunr
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hunr
    letI : Algebra U (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_right
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    ContinuousSMul U (E ⊔ U : IntermediateField K Ksep)
  /-- The compositum is unramified over `E`. -/
  unramified_left :
    letI : Algebra E (E ⊔ U : IntermediateField K Ksep) :=
      intermediateFieldInclusionAlgebra K Ksep le_sup_left
    letI : ValuativeRel (E ⊔ U : IntermediateField K Ksep) := compositumValuativeRel
    letI : TopologicalSpace (E ⊔ U : IntermediateField K Ksep) := compositumTopology
    letI : IsNonarchimedeanLocalField (E ⊔ U : IntermediateField K Ksep) := compositumLocalField
    letI : ValuativeExtension E (E ⊔ U : IntermediateField K Ksep) := valuativeExtension_left
    IsUnramifiedLocalExtension E (E ⊔ U : IntermediateField K Ksep)

/--
An unramified tower in one fixed ambient separable closure.  The field at index `n` has degree
`n+1`; every level carries an exposed local-field instance bundle, arithmetic Frobenius is pinned
by its residue action, divisibility inclusions commute with Frobenius, and composita with finite
Galois intermediate fields carry the structures used in unramified-envelope descent.  The gcd
formula makes intersections of tower levels available without a separate classification argument.
-/
structure UnramifiedTower where
  /-- The degree-`n+1` intermediate field. -/
  field : ℕ → IntermediateField K Ksep
  /-- Finiteness of every level. -/
  finiteDimensional : ∀ n, FiniteDimensional K (field n)
  /-- Every level is unramified over the base local field. -/
  unramified : ∀ n, IsUnramifiedIntermediateField K Ksep (field n)
  /-- Every level is Galois. -/
  isGalois : ∀ n, IsGalois K (field n)
  /-- The prescribed degree. -/
  finrank : ∀ n, Module.finrank K (field n) = n + 1
  /-- Arithmetic Frobenius at every finite level. -/
  frobenius : ∀ n, (field n ≃ₐ[K] field n)
  /-- Frobenius preserves the valuation ring for the selected level structure. -/
  frobenius_preserves_integral : ∀ n,
    letI : ValuativeRel (field n) :=
      unramifiedIntermediateFieldValuativeRel K Ksep (field n) (unramified n)
    letI : TopologicalSpace (field n) :=
      unramifiedIntermediateFieldTopology K Ksep (field n) (unramified n)
    letI : IsNonarchimedeanLocalField (field n) :=
      unramifiedIntermediateFieldLocalField K Ksep (field n) (unramified n)
    ∀ x : RingOfIntegers (field n),
      ∃ y : RingOfIntegers (field n), (y : field n) = frobenius n (x : field n)
  /-- Arithmetic Frobenius induces `x ↦ x^|k_K|` on the residue field. -/
  frobenius_residue : ∀ n,
    letI : ValuativeRel (field n) :=
      unramifiedIntermediateFieldValuativeRel K Ksep (field n) (unramified n)
    letI : TopologicalSpace (field n) :=
      unramifiedIntermediateFieldTopology K Ksep (field n) (unramified n)
    letI : IsNonarchimedeanLocalField (field n) :=
      unramifiedIntermediateFieldLocalField K Ksep (field n) (unramified n)
    ∀ (x y : RingOfIntegers (field n)),
      (y : field n) = frobenius n (x : field n) →
        Ideal.Quotient.mk (LocalMaximalIdeal (field n)) y =
          (Ideal.Quotient.mk (LocalMaximalIdeal (field n)) x) ^ residueCard K
  /-- Frobenius generates the finite Galois group. -/
  frobenius_generates : ∀ n, Subgroup.zpowers (frobenius n) = ⊤
  /-- Divisibility of degrees gives literal containment in the ambient closure. -/
  le_of_dvd : ∀ {a b : ℕ}, a + 1 ∣ b + 1 → field a ≤ field b
  /-- Frobenius commutes with every divisibility inclusion of tower levels. -/
  frobenius_compatible : ∀ {a b : ℕ} (h : a + 1 ∣ b + 1) (x : field a),
    IntermediateField.inclusion (le_of_dvd h) (frobenius a x) =
      frobenius b (IntermediateField.inclusion (le_of_dvd h) x)
  /-- Local-field structures on a tower-level compositum, compatible with both inclusions. -/
  compositum_localField : ∀ (E : IntermediateField K Ksep)
    [FiniteDimensional K E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [ContinuousSMul K E]
    (hE : IsGalois K E) (n : ℕ),
      Nonempty (UnramifiedCompositumLocalFieldData K Ksep E (field n)
        hE (isGalois n) (unramified n))
  /-- Intersections of tower levels have the degree prescribed by the gcd. -/
  intersection_finrank : ∀ a b : ℕ,
    Module.finrank K (field a ⊓ field b : IntermediateField K Ksep) = Nat.gcd (a + 1) (b + 1)

/-- The canonical spectral norm supplies the local-field structures on a finite extension. -/
private theorem finiteExtension_localFieldData_exists
    (F : Type u) (L : Type w)
    [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ vL : ValuativeRel L, ∃ tL : TopologicalSpace L,
      letI : ValuativeRel L := vL
      letI : TopologicalSpace L := tL
      ∃ hL : IsNonarchimedeanLocalField L,
        letI : IsNonarchimedeanLocalField L := hL
        ∃ hFL : ValuativeExtension F L,
          letI : ValuativeExtension F L := hFL
          ContinuousSMul F L := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := F) (Γ₀ := ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
  let nL : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField F L
  letI : NontriviallyNormedField L := nL
  letI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := F) (L := L))
  letI : NormedAlgebra F L := spectralNorm.normedAlgebra F L
  let tL : TopologicalSpace L := inferInstance
  let vL : ValuativeRel L :=
    ValuativeRel.ofValuation (NormedField.valuation (K := L))
  refine ⟨vL, tL, ?_⟩
  letI : ValuativeRel L := vL
  letI : (NormedField.valuation (K := L)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : TopologicalSpace L := tL
  letI : Valued L NNReal := NormedField.toValued
  haveI : (Valued.v : Valuation L NNReal).Compatible := by
    rw [show (Valued.v : Valuation L NNReal) = NormedField.valuation from rfl]
    infer_instance
  haveI htop : IsValuativeTopology L := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [Valued.is_topological_valuation s]
    simpa using
      (Valued.v : Valuation L NNReal).exists_setOf_restrict_le_iff 0 s
  haveI hloc : LocallyCompactSpace L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete F L
  haveI hnontriv : ValuativeRel.IsNontrivial L := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance
  let hL : IsNonarchimedeanLocalField L :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hloc
      toIsNontrivial := hnontriv }
  refine ⟨hL, ?_⟩
  letI : IsNonarchimedeanLocalField L := hL
  let hFL : ValuativeExtension F L := by
    constructor
    intro a b
    change NormedField.valuation (algebraMap F L a) ≤
        NormedField.valuation (algebraMap F L b) ↔ a ≤ᵥ b
    rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    change spectralNorm F L (algebraMap F L a) ≤
        spectralNorm F L (algebraMap F L b) ↔ a ≤ᵥ b
    rw [spectralNorm_extends, spectralNorm_extends,
      Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]
    exact Valued.toNormedField.norm_le_iff
  refine ⟨hFL, ?_⟩
  letI : ValuativeExtension F L := hFL
  exact inferInstance

/-- A monic lift of an irreducible degree-`d` residue polynomial. -/
private structure UnramifiedLiftPolynomial
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (d : ℕ) where
  poly : Polynomial (RingOfIntegers F)
  monic : poly.Monic
  natDegree : poly.natDegree = d
  reduction_irreducible :
    Irreducible (poly.map (IsLocalRing.residue (RingOfIntegers F)))

/-- Finite-field theory and coefficientwise lifting give an unramified polynomial in every
positive degree. -/
private theorem unramifiedLiftPolynomial_exists
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (d : ℕ) (hd : 0 < d) :
    Nonempty (UnramifiedLiftPolynomial F d) := by
  let k := LocalResidueField F
  let p := ringChar k
  letI : Fact p.Prime := ⟨CharP.prime_ringChar k⟩
  letI : CharP k p := ringChar.charP k
  letI : NeZero d := ⟨hd.ne'⟩
  let l := FiniteField.Extension k p d
  let α : l := (Field.exists_primitive_element k l).choose
  have hα : IntermediateField.adjoin k {α} = ⊤ :=
    (Field.exists_primitive_element k l).choose_spec
  let fbar : Polynomial k := minpoly k α
  have hfbar_monic : fbar.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral α)
  have hfbar_irred : Irreducible fbar :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral α)
  have hfbar_deg : fbar.natDegree = d := by
    calc
      fbar.natDegree = Module.finrank k (IntermediateField.adjoin k {α}) :=
        (IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)).symm
      _ = Module.finrank k l := by rw [hα]; simp
      _ = d := FiniteField.finrank_extension k p d
  obtain ⟨f, hfred, hfdeg, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective fbar) hfbar_monic
  exact ⟨⟨f, hfmonic, hfdeg.trans hfbar_deg, hfred.symm ▸ hfbar_irred⟩⟩

/-- A degree-`d` residue lift together with one of its roots in the fixed separable closure. -/
private structure UnramifiedLevelSeed
    (F : Type u) (Fsep : Type v) [Field F] [Field Fsep] [Algebra F Fsep]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (d : ℕ) where
  lift : UnramifiedLiftPolynomial F d
  root : Fsep
  minpoly_eq : minpoly F root = lift.poly.map (algebraMap (RingOfIntegers F) F)

/-- A lifted residue polynomial is irreducible and separable over the local field, hence has a
root in its fixed separable closure. -/
private theorem unramifiedLevelSeed_exists [IsSepClosure K Ksep]
    (d : ℕ) (hd : 0 < d) : Nonempty (UnramifiedLevelSeed K Ksep d) := by
  let D := (unramifiedLiftPolynomial_exists K d hd).some
  let fK := D.poly.map (algebraMap (RingOfIntegers K) K)
  have hfR : Irreducible D.poly :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (IsLocalRing.residue (RingOfIntegers K)) D.poly D.monic D.reduction_irreducible
  have hfK : Irreducible fK :=
    (D.monic.irreducible_iff_irreducible_map_fraction_map).1 hfR
  have hfred_sep : (D.poly.map (IsLocalRing.residue (RingOfIntegers K))).Separable :=
    PerfectField.separable_of_irreducible D.reduction_irreducible
  have hfred_deriv :
      (D.poly.map (IsLocalRing.residue (RingOfIntegers K))).derivative ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero D.reduction_irreducible).1 hfred_sep
  have hfR_deriv : D.poly.derivative ≠ 0 := by
    intro h
    apply hfred_deriv
    rw [Polynomial.derivative_map, h, Polynomial.map_zero]
  have hfK_deriv : fK.derivative ≠ 0 := by
    intro h
    apply hfR_deriv
    apply Polynomial.map_injective (algebraMap (RingOfIntegers K) K)
      (IsFractionRing.injective (RingOfIntegers K) K)
    rw [Polynomial.map_zero, ← Polynomial.derivative_map]
    exact h
  have hfK_sep : fK.Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hfK).2 hfK_deriv
  have hfK_degree : fK.degree ≠ 0 := by
    apply Polynomial.degree_ne_of_natDegree_ne
    rw [D.monic.natDegree_map, D.natDegree]
    exact hd.ne'
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  obtain ⟨z, hz⟩ := IsSepClosed.exists_aeval_eq_zero Ksep fK hfK_degree hfK_sep
  refine ⟨⟨D, z, ?_⟩⟩
  exact (minpoly.eq_of_irreducible_of_monic hfK hz (D.monic.map _)).symm

/-- The field generated by a level seed has the residue polynomial's prescribed degree. -/
private theorem unramifiedLevelSeed_finrank [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    Module.finrank K (IntermediateField.adjoin K {S.root}) = d := by
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral S.root), S.minpoly_eq,
    S.lift.monic.natDegree_map, S.lift.natDegree]

set_option maxHeartbeats 800000 in
private theorem unramifiedLevelSeed_isUnramified [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    letI : FiniteDimensional K (IntermediateField.adjoin K {S.root}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
    IsUnramifiedIntermediateField K Ksep (IntermediateField.adjoin K {S.root}) := by
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  obtain ⟨vU, tU, hU, hKU, hsmul⟩ := finiteExtension_localFieldData_exists K U
  refine ⟨vU, tU, ?_⟩
  letI : ValuativeRel U := vU
  letI : TopologicalSpace U := tU
  refine ⟨hU, ?_⟩
  letI : IsNonarchimedeanLocalField U := hU
  refine ⟨hKU, ?_⟩
  letI : ValuativeExtension K U := hKU
  refine ⟨hsmul, ?_⟩
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  letI : Module.Finite 𝒪[K] 𝒪[U] := ringOfIntegers_module_finite K U
  let g : U := IntermediateField.AdjoinSimple.gen K S.root
  have hgpoly : Polynomial.aeval g S.lift.poly = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, ← S.minpoly_eq,
      ← IntermediateField.minpoly_gen K S.root]
    exact minpoly.aeval K g
  have hgK : IsIntegral 𝒪[K] g :=
    ⟨S.lift.poly, S.lift.monic, by simpa only [Polynomial.aeval_def] using hgpoly⟩
  have hgU : IsIntegral 𝒪[U] g := hgK.tower_top
  have hgmem : (g : U) ∈ (ValuativeRel.valuation U).integer :=
    (Valuation.integer.integers (ValuativeRel.valuation U)).mem_of_integral hgU
  let og : 𝒪[U] := ⟨g, hgmem⟩
  let k := LocalResidueField K
  let kU := LocalResidueField U
  let gbar : kU := IsLocalRing.residue 𝒪[U] og
  have hrootbar : Polynomial.aeval gbar
      (S.lift.poly.map (IsLocalRing.residue 𝒪[K])) = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map
      (ψ := IsLocalRing.residue 𝒪[U]) (φ := IsLocalRing.residue 𝒪[K]) rfl]
    rw [show Polynomial.aeval og S.lift.poly = 0 from ?_, map_zero]
    apply Subtype.ext
    have hcoe : ((Polynomial.aeval og S.lift.poly : 𝒪[U]) : U) =
        Polynomial.aeval g S.lift.poly := by
      change algebraMap 𝒪[U] U (Polynomial.aeval og S.lift.poly) =
        Polynomial.aeval (algebraMap 𝒪[U] U og) S.lift.poly
      simpa only [Polynomial.map_id] using Polynomial.map_aeval_eq_aeval_map
        (φ := RingHom.id 𝒪[K]) (ψ := algebraMap 𝒪[U] U) (by
          apply RingHom.ext
          intro x
          simp only [RingHom.comp_apply, RingHom.id_apply]
          change algebraMap 𝒪[K] U x =
            algebraMap 𝒪[U] U (algebraMap 𝒪[K] 𝒪[U] x)
          rw [show algebraMap 𝒪[U] U (algebraMap 𝒪[K] 𝒪[U] x) =
            algebraMap K U (x : K) from
              Valuation.HasExtension.val_algebraMap
                (vR := ValuativeRel.valuation K) (vA := ValuativeRel.valuation U) x]
          rfl)
        S.lift.poly og
    rw [hcoe]
    exact hgpoly
  have hminbar : minpoly k gbar =
      S.lift.poly.map (IsLocalRing.residue 𝒪[K]) := by
    exact (minpoly.eq_of_irreducible_of_monic S.lift.reduction_irreducible
      hrootbar (S.lift.monic.map _)).symm
  have hd : 0 < d := by
    rw [← S.lift.natDegree, ← S.lift.monic.natDegree_map
      (IsLocalRing.residue 𝒪[K])]
    exact S.lift.reduction_irreducible.natDegree_pos
  have hlower : d ≤ Module.finrank k kU := by
    let A := IntermediateField.adjoin k {gbar}
    haveI : FiniteDimensional k A :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral gbar)
    calc
      d = Module.finrank k A := by
        rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral gbar),
          hminbar, S.lift.monic.natDegree_map, S.lift.natDegree]
      _ ≤ Module.finrank k (⊤ : IntermediateField k kU) :=
        IntermediateField.finrank_le_of_le_right le_top
      _ = Module.finrank k kU := by simp
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let P : Ideal 𝒪[U] := IsLocalRing.maximalIdeal 𝒪[U]
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer K
  have hp0 : p ≠ ⊥ := by
    rw [show p = Ideal.span {ϖK} from hϖKirr.maximalIdeal_eq,
      ne_eq, Ideal.span_singleton_eq_bot]
    exact hϖKirr.ne_zero
  letI : Module.IsTorsionFree 𝒪[K] 𝒪[U] :=
    Valuation.HasExtension.instIsTorsionFreeInteger
  letI : NoZeroSMulDivisors 𝒪[K] 𝒪[U] :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := by
        intro c x hcx
        by_cases hc : c = 0
        · exact Or.inl hc
        · refine Or.inr ?_
          apply Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hc)
          simpa using hcx }
  have hupper : Module.finrank k kU ≤ Module.finrank K U := by
    have h := Ideal.inertiaDeg_le_finrank (S := 𝒪[U]) K U P hp0
    rw [Ideal.inertiaDeg_algebraMap] at h
    exact h
  have hres : Module.finrank k kU = d := by
    apply le_antisymm
    · exact hupper.trans_eq (unramifiedLevelSeed_finrank K Ksep S)
    · exact hlower
  have hinertia : p.inertiaDeg P = d := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact hres
  have hdegree := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (S := 𝒪[U]) K U (p := p) hp0
  have hramification : p.ramificationIdx P = 1 := by
    rw [hinertia, unramifiedLevelSeed_finrank K Ksep S] at hdegree
    apply Nat.eq_of_mul_eq_mul_right hd
    simpa using hdegree
  obtain ⟨ϖU, hϖU, hϖUirr⟩ := integral_normalizedUniformizer U
  let mϖ : 𝒪[U] := algebraMap 𝒪[K] 𝒪[U] ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : 𝒪[U] => (z : U)) h
    have hz : algebraMap K U (ϖK : K) = 0 := by simpa [mϖ] using h'
    exact hϖKirr.ne_zero (Subtype.ext ((algebraMap K U).injective (by simpa using hz)))
  obtain ⟨n, unit, hfac⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmϖ0 hϖUirr
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖU} := hϖUirr.maximalIdeal_eq
  have hmap : Ideal.map (algebraMap 𝒪[K] 𝒪[U]) p = P ^ n := by
    rw [hp, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {mϖ} = P ^ n
    rw [hfac, Ideal.span_singleton_mul_left_unit unit.isUnit, hP,
      Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map (algebraMap 𝒪[K] 𝒪[U]) p ≤ P ^ (n + 1) := by
    rw [hmap]
    intro hle
    have heq : P ^ n = P ^ (n + 1) :=
      le_antisymm hle (Ideal.pow_le_pow_right (Nat.le_succ n))
    have hc := congr_arg Order.coheight heq
    rw [show P = IsLocalRing.maximalIdeal 𝒪[U] from rfl,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
    have : n = n + 1 := by exact_mod_cast hc
    omega
  have hnram : p.ramificationIdx P = n :=
    Ideal.ramificationIdx_spec hmap.le hnot
  have hn : n = 1 := hnram ▸ hramification
  let xu : Units U := Units.map (algebraMap 𝒪[U] U) unit
  have hfacUnits : Units.map (algebraMap K U) (defaultUniformizer K).val =
      xu * (defaultUniformizer U).val ^ n := by
    apply Units.ext
    change algebraMap K U (((defaultUniformizer K).val : Units K) : K) =
      algebraMap 𝒪[U] U (unit : 𝒪[U]) *
        (((defaultUniformizer U).val : Units U) : U) ^ n
    rw [show algebraMap 𝒪[U] U (unit : 𝒪[U]) =
      (((unit : Units 𝒪[U]) : 𝒪[U]) : U) from rfl, ← hϖK]
    simpa [mϖ, hϖU] using congr_arg (fun z : 𝒪[U] => (z : U)) hfac
  have hval : normalizedValuation U
      (Units.map (algebraMap K U) (defaultUniformizer K).val) = 1 := by
    rw [hfacUnits, normalizedValuation_mul, normalizedValuation_ringUnit]
    have hpow : normalizedValuation U ((defaultUniformizer U).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom U ((defaultUniformizer U).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation U (defaultUniformizer U).val = _
      rw [(defaultUniformizer U).valuation_eq_one, mul_one]
    rw [hpow, hn]
    norm_num
  refine ⟨?_⟩
  have hscale := normalizedValuation_algebraMap K U (defaultUniformizer K).val
  rw [hval, (defaultUniformizer K).valuation_eq_one, mul_one] at hscale
  exact_mod_cast hscale.symm

/-- A simple residue root lifts, with its residue fixed, over a Henselian local ring. -/
private theorem hensel_lift_residue_root
    (R : Type w) [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    (f : Polynomial R) (hf : f.Monic) (a₀ : IsLocalRing.ResidueField R)
    (hroot : Polynomial.aeval a₀ f = 0)
    (hderiv : Polynomial.aeval a₀ f.derivative ≠ 0) :
    ∃ a : R, f.IsRoot a ∧ IsLocalRing.residue R a = a₀ := by
  obtain ⟨a₀', ha₀'⟩ := IsLocalRing.residue_surjective a₀
  have heval : f.eval a₀' ∈ IsLocalRing.maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    calc
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.eval a₀') =
          Polynomial.eval₂ (IsLocalRing.residue R)
            (IsLocalRing.residue R a₀') f := by
              exact (Polynomial.eval₂_at_apply (IsLocalRing.residue R) a₀').symm
      _ = Polynomial.eval₂ (IsLocalRing.residue R) a₀ f := by rw [ha₀']
      _ = 0 := by
        simpa only [Polynomial.aeval_def,
          IsLocalRing.ResidueField.algebraMap_eq] using hroot
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      (f.derivative.eval a₀')) := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply hderiv
    change Polynomial.eval₂ (IsLocalRing.residue R) a₀ f.derivative = 0
    rw [← ha₀']
    exact (Polynomial.eval₂_at_apply (p := f.derivative)
      (IsLocalRing.residue R) a₀').trans hzero
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian f hf a₀' heval hunit
  refine ⟨a, ha, ?_⟩
  rw [← ha₀', ← sub_eq_zero, ← map_sub]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a - a₀') = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha'

/-- An irreducible finite-field polynomial has a root in every extension whose degree is a
multiple of its degree. -/
private theorem finiteField_irreducible_root_of_natDegree_dvd_finrank
    {k l : Type*} [Field k] [Field l] [Finite k] [Finite l] [Algebra k l]
    (f : Polynomial k) (hf : Irreducible f)
    (h : f.natDegree ∣ Module.finrank k l) :
    ∃ x : l, Polynomial.aeval x f = 0 := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  let A := AdjoinRoot f
  have hfin : Module.finrank k A = f.natDegree := by
    exact finrank_quotient_span_eq_natDegree
  have hdiv : Module.finrank k A ∣ Module.finrank k l := by
    rw [hfin]
    exact h
  let emb : A →ₐ[k] l := (FiniteField.nonempty_algHom_of_finrank_dvd hdiv).some
  refine ⟨emb (AdjoinRoot.root f), ?_⟩
  change f.eval₂ (algebraMap k l) (emb (AdjoinRoot.root f)) = 0
  calc
    f.eval₂ (algebraMap k l) (emb (AdjoinRoot.root f)) =
        emb (f.eval₂ (algebraMap k A) (AdjoinRoot.root f)) := by
      symm
      have he :=
        Polynomial.hom_eval₂ f (algebraMap k A) emb.toRingHom (AdjoinRoot.root f)
      have hcomp : emb.toRingHom.comp (algebraMap k A) = algebraMap k l :=
        emb.comp_algebraMap
      rw [hcomp] at he
      exact he
    _ = 0 := by
      have hroot : f.eval₂ (algebraMap k A) (AdjoinRoot.root f) = 0 := by
        simpa [A] using AdjoinRoot.eval₂_root f
      rw [hroot, map_zero]

set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- An unramified intermediate field has residue degree equal to its field degree. -/
private theorem residue_finrank_eq_finrank_of_unramified
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    letI : ValuativeExtension K E :=
      unramifiedIntermediateFieldValuativeExtension K Ksep E hE
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField E) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[E])
        (IsLocalRing.maximalIdeal 𝒪[K])
    Module.finrank (LocalResidueField K) (LocalResidueField E) = Module.finrank K E := by
  letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
  letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
  letI : IsNonarchimedeanLocalField E :=
    unramifiedIntermediateFieldLocalField K Ksep E hE
  letI : ValuativeExtension K E :=
    unramifiedIntermediateFieldValuativeExtension K Ksep E hE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField E) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[E])
      (IsLocalRing.maximalIdeal 𝒪[K])
  letI : Module.Finite 𝒪[K] 𝒪[E] := ringOfIntegers_module_finite K E
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let P : Ideal 𝒪[E] := IsLocalRing.maximalIdeal 𝒪[E]
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer K
  obtain ⟨ϖE, hϖE, hϖEirr⟩ := integral_normalizedUniformizer E
  let mϖ : 𝒪[E] := algebraMap 𝒪[K] 𝒪[E] ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : 𝒪[E] => (z : E)) h
    have hz : algebraMap K E (ϖK : K) = 0 := by simpa [mϖ] using h'
    exact hϖKirr.ne_zero (Subtype.ext ((algebraMap K E).injective (by simpa using hz)))
  obtain ⟨n, unit, hfac⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmϖ0 hϖEirr
  let xu : Units E := Units.map (algebraMap 𝒪[E] E) unit
  have hfacUnits : Units.map (algebraMap K E) (defaultUniformizer K).val =
      xu * (defaultUniformizer E).val ^ n := by
    apply Units.ext
    change algebraMap K E (((defaultUniformizer K).val : Units K) : K) =
      algebraMap 𝒪[E] E (unit : 𝒪[E]) *
        (((defaultUniformizer E).val : Units E) : E) ^ n
    rw [show algebraMap 𝒪[E] E (unit : 𝒪[E]) =
      (((unit : Units 𝒪[E]) : 𝒪[E]) : E) from rfl, ← hϖK]
    simpa [mϖ, hϖE] using congr_arg (fun z : 𝒪[E] => (z : E)) hfac
  have hn : n = 1 := by
    have hval := congr_arg (normalizedValuation E) hfacUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit] at hval
    have hpow : normalizedValuation E ((defaultUniformizer E).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom E ((defaultUniformizer E).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation E (defaultUniformizer E).val = _
      rw [(defaultUniformizer E).valuation_eq_one, mul_one]
    rw [hpow] at hval
    have hbase := normalizedValuation_algebraMap K E (defaultUniformizer K).val
    rw [(unramifiedIntermediateFieldIsUnramified K Ksep E hE).ramificationIndex_eq_one,
      (defaultUniformizer K).valuation_eq_one] at hbase
    norm_num at hbase
    rw [hbase] at hval
    norm_num at hval
    exact_mod_cast hval.symm
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖE} := hϖEirr.maximalIdeal_eq
  have hmap : Ideal.map (algebraMap 𝒪[K] 𝒪[E]) p = P := by
    rw [hp, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {mϖ} = P
    rw [hfac, hn, pow_one, Ideal.span_singleton_mul_left_unit unit.isUnit, hP]
  have hnot : ¬ Ideal.map (algebraMap 𝒪[K] 𝒪[E]) p ≤ P ^ 2 := by
    rw [hmap]
    intro hle
    have heq : P = P ^ 2 :=
      le_antisymm hle (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0))
    have heq' : P ^ 1 = P ^ 2 := by simpa using heq
    have hc := congr_arg Order.coheight heq'
    rw [show P = IsLocalRing.maximalIdeal 𝒪[E] from rfl,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
    norm_num at hc
  have hram : p.ramificationIdx P = 1 := by
    apply Ideal.ramificationIdx_spec (by simpa using hmap.le)
    simpa only [one_add_one_eq_two] using hnot
  have hdegree := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (S := 𝒪[E]) K E (p := p) (by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact hϖKirr.ne_zero)
  rw [hram, one_mul] at hdegree
  calc
    Module.finrank (LocalResidueField K) (LocalResidueField E) = p.inertiaDeg P := by
      rw [Ideal.inertiaDeg_algebraMap]
      rfl
    _ = Module.finrank K E := hdegree

/-- A residue root of a lifted unramified polynomial lifts inside every unramified extension whose
residue degree is a multiple of the polynomial's degree. -/
private theorem unramifiedLevelSeed_liftedRoot
    [IsSepClosure K Ksep] {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E)
    (hdiv : d ∣ Module.finrank K E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    letI : ValuativeExtension K E :=
      unramifiedIntermediateFieldValuativeExtension K Ksep E hE
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    ∃ a : RingOfIntegers E,
      (S.lift.poly.map (algebraMap (RingOfIntegers K) (RingOfIntegers E))).IsRoot a := by
  letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
  letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
  letI : IsNonarchimedeanLocalField E :=
    unramifiedIntermediateFieldLocalField K Ksep E hE
  letI : ValuativeExtension K E :=
    unramifiedIntermediateFieldValuativeExtension K Ksep E hE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kE := LocalResidueField E
  letI : Algebra k kE :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[E])
      (IsLocalRing.maximalIdeal 𝒪[K])
  let fbar := S.lift.poly.map (IsLocalRing.residue 𝒪[K])
  have hfdeg : fbar.natDegree = d := by
    rw [S.lift.monic.natDegree_map, S.lift.natDegree]
  have hresdeg : Module.finrank k kE = Module.finrank K E :=
    residue_finrank_eq_finrank_of_unramified K Ksep E hE
  have hrootdiv : fbar.natDegree ∣ Module.finrank k kE := by
    rw [hfdeg, hresdeg]
    exact hdiv
  obtain ⟨a₀, ha₀⟩ := finiteField_irreducible_root_of_natDegree_dvd_finrank
    fbar S.lift.reduction_irreducible hrootdiv
  let fE := S.lift.poly.map (algebraMap 𝒪[K] 𝒪[E])
  have hfE : fE.Monic := S.lift.monic.map _
  have hsep : fbar.Separable :=
    PerfectField.separable_of_irreducible S.lift.reduction_irreducible
  have hderiv₀ : Polynomial.aeval a₀ fbar.derivative ≠ 0 :=
    hsep.aeval_derivative_ne_zero ha₀
  have hcomm :
      (algebraMap k kE).comp (IsLocalRing.residue 𝒪[K]) =
        (IsLocalRing.residue 𝒪[E]).comp (algebraMap 𝒪[K] 𝒪[E]) := rfl
  have hrootE : Polynomial.aeval a₀ fE = 0 := by
    change Polynomial.eval₂ (IsLocalRing.residue 𝒪[E]) a₀
      (S.lift.poly.map (algebraMap 𝒪[K] 𝒪[E])) = 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have ha₀' := ha₀
    rw [Polynomial.aeval_def, show fbar =
      S.lift.poly.map (IsLocalRing.residue 𝒪[K]) from rfl,
      Polynomial.eval₂_map] at ha₀'
    exact ha₀'
  have hderivE : Polynomial.aeval a₀ fE.derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    change Polynomial.eval₂ (IsLocalRing.residue 𝒪[E]) a₀
      (S.lift.poly.derivative.map (algebraMap 𝒪[K] 𝒪[E])) ≠ 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have hderiv₀' := hderiv₀
    rw [Polynomial.aeval_def, show fbar.derivative =
      S.lift.poly.derivative.map (IsLocalRing.residue 𝒪[K]) by
        rw [Polynomial.derivative_map],
      Polynomial.eval₂_map] at hderiv₀'
    exact hderiv₀'
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  obtain ⟨a, ha, _⟩ := hensel_lift_residue_root 𝒪[E] fE hfE a₀ hrootE hderivE
  exact ⟨a, ha⟩

set_option maxHeartbeats 800000 in
/-- A level generated by an unramified seed is normal: all residue roots lift into the same
level, so its defining polynomial already splits there. -/
private theorem unramifiedLevelSeed_isGalois [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    letI : FiniteDimensional K (IntermediateField.adjoin K {S.root}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
    IsGalois K (IntermediateField.adjoin K {S.root}) := by
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  have hunr : IsUnramifiedIntermediateField K Ksep U :=
    unramifiedLevelSeed_isUnramified K Ksep S
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hunr
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hunr
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hunr
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hunr
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : UniformSpace U := IsTopologicalAddGroup.rightUniformSpace U
  letI : IsUniformAddGroup U := isUniformAddGroup_of_addCommGroup
  let k := LocalResidueField K
  let kU := LocalResidueField U
  letI : Algebra k kU :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
      (IsLocalRing.maximalIdeal 𝒪[K])
  let fbar := S.lift.poly.map (IsLocalRing.residue 𝒪[K])
  have hfbar_deg : fbar.natDegree = d := by
    rw [S.lift.monic.natDegree_map, S.lift.natDegree]
  have hkU_deg : Module.finrank k kU = d := by
    rw [residue_finrank_eq_finrank_of_unramified K Ksep U hunr,
      unramifiedLevelSeed_finrank K Ksep S]
  have hdiv : fbar.natDegree ∣ Module.finrank k kU := by
    rw [hfbar_deg, hkU_deg]
  obtain ⟨r, hr⟩ := finiteField_irreducible_root_of_natDegree_dvd_finrank
    fbar S.lift.reduction_irreducible hdiv
  have hminr : minpoly k r = fbar :=
    (minpoly.eq_of_irreducible_of_monic S.lift.reduction_irreducible hr
      (S.lift.monic.map _)).symm
  have hfbar_splits : (fbar.map (algebraMap k kU)).Splits := by
    rw [← hminr]
    exact IsGalois.splits k r
  have hfbar_sep : fbar.Separable :=
    PerfectField.separable_of_irreducible S.lift.reduction_irreducible
  let fOU := S.lift.poly.map (algebraMap 𝒪[K] 𝒪[U])
  have hfOU : fOU.Monic := S.lift.monic.map _
  have hcomm :
      (algebraMap k kU).comp (IsLocalRing.residue 𝒪[K]) =
        (IsLocalRing.residue 𝒪[U]).comp (algebraMap 𝒪[K] 𝒪[U]) := rfl
  have hlift (x : fbar.rootSet kU) :
      ∃ a : 𝒪[U], fOU.IsRoot a ∧ IsLocalRing.residue 𝒪[U] a = (x : kU) := by
    have hx : Polynomial.aeval (x : kU) fbar = 0 :=
      (Polynomial.mem_rootSet.mp x.prop).2
    have hxderiv : Polynomial.aeval (x : kU) fbar.derivative ≠ 0 :=
      hfbar_sep.aeval_derivative_ne_zero hx
    have hxOU : Polynomial.aeval (x : kU) fOU = 0 := by
      change Polynomial.eval₂ (IsLocalRing.residue 𝒪[U]) (x : kU)
        (S.lift.poly.map (algebraMap 𝒪[K] 𝒪[U])) = 0
      rw [Polynomial.eval₂_map, ← hcomm]
      have hx' := hx
      rw [Polynomial.aeval_def] at hx'
      change Polynomial.eval₂ (algebraMap k kU) (x : kU)
        (S.lift.poly.map (IsLocalRing.residue 𝒪[K])) = 0 at hx'
      rw [Polynomial.eval₂_map] at hx'
      exact hx'
    have hxderivOU : Polynomial.aeval (x : kU) fOU.derivative ≠ 0 := by
      rw [Polynomial.derivative_map]
      change Polynomial.eval₂ (IsLocalRing.residue 𝒪[U]) (x : kU)
        (S.lift.poly.derivative.map (algebraMap 𝒪[K] 𝒪[U])) ≠ 0
      rw [Polynomial.eval₂_map, ← hcomm]
      have hderiv_eq : fbar.derivative =
          S.lift.poly.derivative.map (IsLocalRing.residue 𝒪[K]) := by
        dsimp only [fbar]
        rw [Polynomial.derivative_map]
      have hxderiv' := hxderiv
      rw [Polynomial.aeval_def, hderiv_eq, Polynomial.eval₂_map] at hxderiv'
      exact hxderiv'
    exact hensel_lift_residue_root 𝒪[U] fOU hfOU (x : kU) hxOU hxderivOU
  choose lift hlift_root hlift_residue using hlift
  let fK := S.lift.poly.map (algebraMap 𝒪[K] K)
  let fKU := fK.map (algebraMap K U)
  have hpoly : fOU.map (algebraMap 𝒪[U] U) = fKU := by
    dsimp only [fOU, fKU, fK]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hfK_monic : fK.Monic := S.lift.monic.map _
  let rootMap : fbar.rootSet kU → fK.rootSet U := fun x =>
    ⟨(lift x : U), by
      rw [Polynomial.mem_rootSet]
      refine ⟨?_, ?_⟩
      · exact hfK_monic.ne_zero
      · rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        change fKU.IsRoot (lift x : U)
        rw [← hpoly]
        exact (hlift_root x).map⟩
  have hrootMap_injective : Function.Injective rootMap := by
    intro x y hxy
    apply Subtype.ext
    have hcoe : (lift x : U) = (lift y : U) :=
      congr_arg (fun z : fK.rootSet U => (z : U)) hxy
    have hliftxy : lift x = lift y := Subtype.ext hcoe
    exact (hlift_residue x).symm.trans
      ((congr_arg (IsLocalRing.residue 𝒪[U]) hliftxy).trans (hlift_residue y))
  have hdomain_card : Fintype.card (fbar.rootSet kU) = d := by
    rw [Polynomial.card_rootSet_eq_natDegree hfbar_sep hfbar_splits, hfbar_deg]
  have hlower : d ≤ Fintype.card (fK.rootSet U) := by
    rw [← hdomain_card]
    exact Fintype.card_le_of_injective rootMap hrootMap_injective
  have hfK_sep : fK.Separable := by
    rw [show fK = minpoly K S.root from S.minpoly_eq.symm]
    exact Algebra.IsSeparable.isSeparable K S.root
  have hfKU_sep : fKU.Separable := by
    dsimp only [fKU]
    exact hfK_sep.map
  have hrootSet_card : fKU.roots.card = Fintype.card (fK.rootSet U) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    classical
    unfold Polynomial.rootSet
    rw [Set.ncard_coe_finset]
    have haroots : fK.aroots U = fKU.roots := by rfl
    rw [haroots]
    exact (@Multiset.toFinset_card_of_nodup U (Classical.decEq U) fKU.roots
      (Polynomial.nodup_roots hfKU_sep)).symm
  have hlower' : d ≤ fKU.roots.card := by
    rwa [hrootSet_card]
  have hfKU_deg : fKU.natDegree = d := by
    dsimp only [fKU, fK]
    rw [hfK_monic.natDegree_map, S.lift.monic.natDegree_map, S.lift.natDegree]
  have hupper : fKU.roots.card ≤ d := by
    simpa only [hfKU_deg] using Polynomial.card_roots' fKU
  have hfKU_splits : fKU.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    exact (le_antisymm hupper hlower').trans hfKU_deg.symm
  have hsplits : ((minpoly K S.root).map (algebraMap K U)).Splits := by
    rw [S.minpoly_eq]
    exact hfKU_splits
  letI : Normal K U := by
    constructor
    intro x
    rw [IntermediateField.minpoly_eq]
    apply IntermediateField.splits_of_mem_adjoin K Ksep (L := U) (S := {S.root})
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨Algebra.IsIntegral.isIntegral S.root, hsplits⟩
    · exact x.prop
  exact ⟨⟩

set_option maxHeartbeats 500000 in
/-- If a seed degree divides the degree of an unramified intermediate field, the seed level is
literally contained in that field inside the fixed separable closure. -/
private theorem unramifiedLevelSeed_le_of_dvd [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E)
    (hdiv : d ∣ Module.finrank K E) :
    IntermediateField.adjoin K {S.root} ≤ E := by
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
  letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
  letI : IsNonarchimedeanLocalField E :=
    unramifiedIntermediateFieldLocalField K Ksep E hE
  letI : ValuativeExtension K E :=
    unramifiedIntermediateFieldValuativeExtension K Ksep E hE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  obtain ⟨a, ha⟩ := unramifiedLevelSeed_liftedRoot K Ksep S E hE hdiv
  let fK := S.lift.poly.map (algebraMap 𝒪[K] K)
  have hfR : Irreducible S.lift.poly :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (IsLocalRing.residue 𝒪[K]) S.lift.poly S.lift.monic
        S.lift.reduction_irreducible
  have hfK : Irreducible fK :=
    (S.lift.monic.irreducible_iff_irreducible_map_fraction_map).1 hfR
  have hpolyE :
      (S.lift.poly.map (algebraMap 𝒪[K] 𝒪[E])).map (algebraMap 𝒪[E] E) =
        fK.map (algebraMap K E) := by
    dsimp only [fK]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  have haE : (fK.map (algebraMap K E)).IsRoot (a : E) := by
    rw [← hpolyE]
    exact ha.map
  let z : Ksep := E.val (a : E)
  have hzroot : (fK.map (algebraMap K Ksep)).IsRoot z := by
    have hz := haE.map (f := E.val.toRingHom)
    have hcomp : E.val.toRingHom.comp (algebraMap K E) = algebraMap K Ksep :=
      E.val.comp_algebraMap
    rw [Polynomial.map_map, hcomp] at hz
    exact hz
  have hzaeval : Polynomial.aeval z fK = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hzroot
  have hminz : fK = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hfK hzaeval (S.lift.monic.map _)
  letI : IsGalois K U := unramifiedLevelSeed_isGalois K Ksep S
  have hsplitf : (fK.map (algebraMap K U)).Splits := by
    have hs := IsGalois.splits K (IntermediateField.AdjoinSimple.gen K S.root)
    rw [IntermediateField.minpoly_gen, S.minpoly_eq] at hs
    exact hs
  have hzU : z ∈ U := by
    apply (Algebra.IsIntegral.isIntegral z).mem_intermediateField_of_minpoly_splits
    rw [← hminz]
    exact hsplitf
  let Z := IntermediateField.adjoin K {z}
  have hZleU : Z ≤ U := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzU
  have hzE : z ∈ E := by
    exact (a : E).prop
  have hZleE : Z ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzE
  haveI : FiniteDimensional K Z :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hZrank : Module.finrank K Z = d := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral z), ← hminz]
    exact (S.lift.monic.natDegree_map (algebraMap 𝒪[K] K)).trans S.lift.natDegree
  have hZU : Z = U := IntermediateField.eq_of_le_of_finrank_eq hZleU
    (hZrank.trans (unramifiedLevelSeed_finrank K Ksep S).symm)
  change U ≤ E
  rw [← hZU]
  exact hZleE

/-- A base-field automorphism of an unramified level restricts to an automorphism of its ring of
integers. -/
private noncomputable def unramifiedAlgEquivOnIntegers
    (U : IntermediateField K Ksep) [FiniteDimensional K U]
    (hU : IsUnramifiedIntermediateField K Ksep U) (σ : U ≃ₐ[K] U) :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hU
    letI : ValuativeExtension K U :=
      unramifiedIntermediateFieldValuativeExtension K Ksep U hU
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    RingOfIntegers U ≃ₐ[RingOfIntegers K] RingOfIntegers U := by
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Module.Finite 𝒪[K] 𝒪[U] := ringOfIntegers_module_finite K U
  have map_mem (τ : U ≃ₐ[K] U) (x : 𝒪[U]) :
      τ (x : U) ∈ (ValuativeRel.valuation U).integer := by
    have hxO : IsIntegral 𝒪[K] x := Algebra.IsIntegral.isIntegral x
    have hxU : IsIntegral 𝒪[K] (x : U) :=
      IsIntegral.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[U] U) hxO
    have hτ : IsIntegral 𝒪[K] (τ (x : U)) := IsIntegral.map τ hxU
    exact (Valuation.integer.integers (ValuativeRel.valuation U)).mem_of_integral
      hτ.tower_top
  let mapInt (τ : U ≃ₐ[K] U) (x : 𝒪[U]) : 𝒪[U] := ⟨τ (x : U), map_mem τ x⟩
  refine
    { toFun := mapInt σ
      invFun := mapInt σ.symm
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : U))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : U))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : U) (y : U))
      map_add' := fun x y => Subtype.ext (map_add σ (x : U) (y : U))
      commutes' := fun x => Subtype.ext (σ.commutes (x : K)) }

/-- Simple roots of a lifted unramified polynomial are uniquely determined by their residue. -/
private theorem unramifiedLift_root_unique
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (E : IntermediateField K Ksep) [FiniteDimensional K E]
    (hE : IsUnramifiedIntermediateField K Ksep E) :
    letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
    letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
    letI : IsNonarchimedeanLocalField E :=
      unramifiedIntermediateFieldLocalField K Ksep E hE
    letI : ValuativeExtension K E :=
      unramifiedIntermediateFieldValuativeExtension K Ksep E hE
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    ∀ (a b : RingOfIntegers E),
      (S.lift.poly.map (algebraMap (RingOfIntegers K) (RingOfIntegers E))).IsRoot a →
      (S.lift.poly.map (algebraMap (RingOfIntegers K) (RingOfIntegers E))).IsRoot b →
      IsLocalRing.residue (RingOfIntegers E) a =
        IsLocalRing.residue (RingOfIntegers E) b → a = b := by
  letI : ValuativeRel E := unramifiedIntermediateFieldValuativeRel K Ksep E hE
  letI : TopologicalSpace E := unramifiedIntermediateFieldTopology K Ksep E hE
  letI : IsNonarchimedeanLocalField E :=
    unramifiedIntermediateFieldLocalField K Ksep E hE
  letI : ValuativeExtension K E :=
    unramifiedIntermediateFieldValuativeExtension K Ksep E hE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kE := LocalResidueField E
  letI : Algebra k kE :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[E])
      (IsLocalRing.maximalIdeal 𝒪[K])
  let fE := S.lift.poly.map (algebraMap 𝒪[K] 𝒪[E])
  let fbar := S.lift.poly.map (IsLocalRing.residue 𝒪[K])
  have hfbar_sep : fbar.Separable :=
    PerfectField.separable_of_irreducible S.lift.reduction_irreducible
  have hredpoly : fE.map (IsLocalRing.residue 𝒪[E]) =
      fbar.map (algebraMap k kE) := by
    dsimp only [fE, fbar]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  intro a b ha hb hab
  have hunit : IsUnit (fE.derivative.eval a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hrootred : (fE.map (IsLocalRing.residue 𝒪[E])).IsRoot
        (IsLocalRing.residue 𝒪[E] a) := by
      exact ha.map
    have hsepred : (fE.map (IsLocalRing.residue 𝒪[E])).Separable := by
      rw [hredpoly]
      exact hfbar_sep.map
    have hrootred' : Polynomial.eval₂ (RingHom.id kE)
        (IsLocalRing.residue 𝒪[E] a) (fE.map (IsLocalRing.residue 𝒪[E])) = 0 := by
      rw [Polynomial.eval₂_id]
      exact hrootred
    have hderivred :
        (fE.map (IsLocalRing.residue 𝒪[E])).derivative.eval
          (IsLocalRing.residue 𝒪[E] a) ≠ 0 := by
      exact hsepred.eval₂_derivative_ne_zero (RingHom.id kE) hrootred'
    simpa only [Polynomial.derivative_map, Polynomial.eval_map,
      Polynomial.eval₂_at_apply] using hderivred
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub ha hb
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      ← IsLocalRing.residue_eq_zero_iff, map_sub, hab, sub_self]
  · exact hunit

/-- Reduction of a level automorphism to the corresponding residue-field automorphism. -/
private noncomputable def unramifiedResidueRingEquiv
    (U : IntermediateField K Ksep) [FiniteDimensional K U]
    (hU : IsUnramifiedIntermediateField K Ksep U) (σ : U ≃ₐ[K] U) :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hU
    letI : ValuativeExtension K U :=
      unramifiedIntermediateFieldValuativeExtension K Ksep U hU
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    LocalResidueField U ≃+* LocalResidueField U := by
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  exact IsLocalRing.ResidueField.mapEquiv
    (unramifiedAlgEquivOnIntegers K Ksep U hU σ).toRingEquiv

/-- Reduction of a level automorphism, as an automorphism over the base residue field. -/
private noncomputable def unramifiedResidueAlgEquiv
    (U : IntermediateField K Ksep) [FiniteDimensional K U]
    (hU : IsUnramifiedIntermediateField K Ksep U) (σ : U ≃ₐ[K] U) :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hU
    letI : ValuativeExtension K U :=
      unramifiedIntermediateFieldValuativeExtension K Ksep U hU
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField U) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
        (IsLocalRing.maximalIdeal 𝒪[K])
    LocalResidueField U ≃ₐ[LocalResidueField K] LocalResidueField U := by
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField U) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
      (IsLocalRing.maximalIdeal 𝒪[K])
  let σO := unramifiedAlgEquivOnIntegers K Ksep U hU σ
  refine { IsLocalRing.ResidueField.mapEquiv σO.toRingEquiv with commutes' := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.ResidueField.mapEquiv σO.toRingEquiv
      (IsLocalRing.residue 𝒪[U] (algebraMap 𝒪[K] 𝒪[U] r)) =
    IsLocalRing.residue 𝒪[U] (algebraMap 𝒪[K] 𝒪[U] r)
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  exact congr_arg (IsLocalRing.residue 𝒪[U]) (σO.commutes r)

/-- Reduction is a homomorphism from level automorphisms to residue-field automorphisms. -/
private noncomputable def unramifiedResidueAlgEquivHom
    (U : IntermediateField K Ksep) [FiniteDimensional K U]
    (hU : IsUnramifiedIntermediateField K Ksep U) :
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hU
    letI : ValuativeExtension K U :=
      unramifiedIntermediateFieldValuativeExtension K Ksep U hU
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField U) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
        (IsLocalRing.maximalIdeal 𝒪[K])
    (U ≃ₐ[K] U) →* (LocalResidueField U ≃ₐ[LocalResidueField K] LocalResidueField U) := by
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField U) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
      (IsLocalRing.maximalIdeal 𝒪[K])
  refine
    { toFun := unramifiedResidueAlgEquiv K Ksep U hU
      map_one' := ?_
      map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  · intro σ τ
    apply AlgEquiv.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rfl

set_option maxHeartbeats 500000 in
/-- Reduction is faithful on the automorphism group of a seeded unramified level. -/
private theorem unramifiedLevelSeed_residueRingEquiv_injective [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    let U := IntermediateField.adjoin K {S.root}
    letI : FiniteDimensional K U :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
    let hU : IsUnramifiedIntermediateField K Ksep U :=
      unramifiedLevelSeed_isUnramified K Ksep S
    letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
    letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
    letI : IsNonarchimedeanLocalField U :=
      unramifiedIntermediateFieldLocalField K Ksep U hU
    letI : ValuativeExtension K U :=
      unramifiedIntermediateFieldValuativeExtension K Ksep U hU
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    Function.Injective (unramifiedResidueRingEquiv K Ksep U hU) := by
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  let hU : IsUnramifiedIntermediateField K Ksep U :=
    unramifiedLevelSeed_isUnramified K Ksep S
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let g : U := IntermediateField.AdjoinSimple.gen K S.root
  have hgpoly : Polynomial.aeval g S.lift.poly = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, ← S.minpoly_eq,
      ← IntermediateField.minpoly_gen K S.root]
    exact minpoly.aeval K g
  have hgK : IsIntegral 𝒪[K] g :=
    ⟨S.lift.poly, S.lift.monic, by simpa only [Polynomial.aeval_def] using hgpoly⟩
  have hgmem : (g : U) ∈ (ValuativeRel.valuation U).integer :=
    (Valuation.integer.integers (ValuativeRel.valuation U)).mem_of_integral
      hgK.tower_top
  let og : 𝒪[U] := ⟨g, hgmem⟩
  let fU := S.lift.poly.map (algebraMap 𝒪[K] 𝒪[U])
  have hpolyU : fU.map (algebraMap 𝒪[U] U) =
      S.lift.poly.map (algebraMap 𝒪[K] U) := by
    dsimp only [fU]
    rw [Polynomial.map_map]
    congr 1
  have hogroot : fU.IsRoot og := by
    apply Polynomial.IsRoot.of_map (f := algebraMap 𝒪[U] U) _
      (fun _ _ h => Subtype.ext h)
    rw [hpolyU]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hgpoly
    exact hgpoly
  change Function.Injective (unramifiedResidueRingEquiv K Ksep U hU)
  intro σ τ hστ
  let σO := unramifiedAlgEquivOnIntegers K Ksep U hU σ
  let τO := unramifiedAlgEquivOnIntegers K Ksep U hU τ
  have hmap (ρ : U ≃ₐ[K] U) :
      fU.map (unramifiedAlgEquivOnIntegers K Ksep U hU ρ).toRingHom = fU := by
    dsimp only [fU]
    rw [Polynomial.map_map]
    have hcomp :
        (unramifiedAlgEquivOnIntegers K Ksep U hU ρ).toRingHom.comp
          (algebraMap 𝒪[K] 𝒪[U]) = algebraMap 𝒪[K] 𝒪[U] :=
      (unramifiedAlgEquivOnIntegers K Ksep U hU ρ).toAlgHom.comp_algebraMap
    rw [hcomp]
  have hσroot : fU.IsRoot (σO og) := by
    have h := hogroot.map (f := σO.toRingHom)
    rw [hmap σ] at h
    exact h
  have hτroot : fU.IsRoot (τO og) := by
    have h := hogroot.map (f := τO.toRingHom)
    rw [hmap τ] at h
    exact h
  have hres : IsLocalRing.residue 𝒪[U] (σO og) =
      IsLocalRing.residue 𝒪[U] (τO og) := by
    have h := DFunLike.congr_fun hστ (IsLocalRing.residue 𝒪[U] og)
    calc
      IsLocalRing.residue 𝒪[U] (σO og) =
          unramifiedResidueRingEquiv K Ksep U hU σ
            (IsLocalRing.residue 𝒪[U] og) := by rfl
      _ = unramifiedResidueRingEquiv K Ksep U hU τ
            (IsLocalRing.residue 𝒪[U] og) := h
      _ = IsLocalRing.residue 𝒪[U] (τO og) := by rfl
  have hO : σO og = τO og :=
    unramifiedLift_root_unique K Ksep S U hU (σO og) (τO og)
      hσroot hτroot hres
  apply AlgEquiv.coe_algHom_injective
  apply (IntermediateField.adjoin.powerBasis
    (Algebra.IsIntegral.isIntegral S.root)).algHom_ext
  exact congr_arg Subtype.val hO

/-- The intermediate field cut out by one lifted unramified seed. -/
private abbrev unramifiedLevelField {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    IntermediateField K Ksep :=
  IntermediateField.adjoin K {S.root}

/-- The canonical finite-dimensional instance for a seeded level. -/
private noncomputable def unramifiedLevelFieldFiniteDimensional [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    FiniteDimensional K (unramifiedLevelField K Ksep S) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)

/-- The seeded level is unramified. -/
private theorem unramifiedLevelField_isUnramified [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    letI : FiniteDimensional K (unramifiedLevelField K Ksep S) :=
      unramifiedLevelFieldFiniteDimensional K Ksep S
    IsUnramifiedIntermediateField K Ksep (unramifiedLevelField K Ksep S) :=
  unramifiedLevelSeed_isUnramified K Ksep S

/-- The seeded level is Galois. -/
private theorem unramifiedLevelField_isGalois [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    letI : FiniteDimensional K (unramifiedLevelField K Ksep S) :=
      unramifiedLevelFieldFiniteDimensional K Ksep S
    IsGalois K (unramifiedLevelField K Ksep S) :=
  unramifiedLevelSeed_isGalois K Ksep S

/-- The seeded level has the seed's prescribed degree. -/
private theorem unramifiedLevelField_finrank [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    Module.finrank K (unramifiedLevelField K Ksep S) = d :=
  unramifiedLevelSeed_finrank K Ksep S

/-- Divisibility gives the canonical inclusion between members of a family of seeded levels. -/
private theorem unramifiedLevelFields_le_of_dvd [IsSepClosure K Ksep]
    (S : ∀ n : ℕ, UnramifiedLevelSeed K Ksep (n + 1))
    {a b : ℕ} (h : a + 1 ∣ b + 1) :
    unramifiedLevelField K Ksep (S a) ≤ unramifiedLevelField K Ksep (S b) := by
  letI : FiniteDimensional K (unramifiedLevelField K Ksep (S b)) :=
    unramifiedLevelFieldFiniteDimensional K Ksep (S b)
  apply unramifiedLevelSeed_le_of_dvd K Ksep (S a)
    (unramifiedLevelField K Ksep (S b))
    (unramifiedLevelField_isUnramified K Ksep (S b))
  rw [unramifiedLevelField_finrank K Ksep (S b)]
  exact h

/-- Arithmetic-Frobenius data on one already constructed seeded level. -/
private structure UnramifiedLevelFrobeniusDatum [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) where
  frobenius : unramifiedLevelField K Ksep S ≃ₐ[K] unramifiedLevelField K Ksep S
  preserves_integral :
    letI : FiniteDimensional K (unramifiedLevelField K Ksep S) :=
      unramifiedLevelFieldFiniteDimensional K Ksep S
    let hU : IsUnramifiedIntermediateField K Ksep (unramifiedLevelField K Ksep S) :=
      unramifiedLevelField_isUnramified K Ksep S
    letI : ValuativeRel (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldValuativeRel K Ksep _ hU
    letI : TopologicalSpace (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldTopology K Ksep _ hU
    letI : IsNonarchimedeanLocalField (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldLocalField K Ksep _ hU
    ∀ x : RingOfIntegers (unramifiedLevelField K Ksep S),
      ∃ y : RingOfIntegers (unramifiedLevelField K Ksep S),
        (y : unramifiedLevelField K Ksep S) =
          frobenius (x : unramifiedLevelField K Ksep S)
  residue_action :
    letI : FiniteDimensional K (unramifiedLevelField K Ksep S) :=
      unramifiedLevelFieldFiniteDimensional K Ksep S
    let hU : IsUnramifiedIntermediateField K Ksep (unramifiedLevelField K Ksep S) :=
      unramifiedLevelField_isUnramified K Ksep S
    letI : ValuativeRel (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldValuativeRel K Ksep _ hU
    letI : TopologicalSpace (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldTopology K Ksep _ hU
    letI : IsNonarchimedeanLocalField (unramifiedLevelField K Ksep S) :=
      unramifiedIntermediateFieldLocalField K Ksep _ hU
    ∀ (x y : RingOfIntegers (unramifiedLevelField K Ksep S)),
      (y : unramifiedLevelField K Ksep S) =
          frobenius (x : unramifiedLevelField K Ksep S) →
        Ideal.Quotient.mk (LocalMaximalIdeal (unramifiedLevelField K Ksep S)) y =
          (Ideal.Quotient.mk (LocalMaximalIdeal (unramifiedLevelField K Ksep S)) x) ^
            residueCard K
  generates : Subgroup.zpowers frobenius = ⊤

set_option maxHeartbeats 500000 in
/-- Arithmetic Frobenius on a seeded level is the unique lift of finite-field Frobenius. -/
private theorem unramifiedLevelFrobeniusDatum_exists [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d) :
    Nonempty (UnramifiedLevelFrobeniusDatum K Ksep S) := by
  let U := unramifiedLevelField K Ksep S
  letI : FiniteDimensional K U := unramifiedLevelFieldFiniteDimensional K Ksep S
  let hU : IsUnramifiedIntermediateField K Ksep U :=
    unramifiedLevelField_isUnramified K Ksep S
  letI : IsGalois K U := unramifiedLevelField_isGalois K Ksep S
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kU := LocalResidueField U
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra k kU :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[U])
      (IsLocalRing.maximalIdeal 𝒪[K])
  let red := unramifiedResidueAlgEquivHom K Ksep U hU
  have hred_injective : Function.Injective red := by
    intro σ τ hστ
    apply unramifiedLevelSeed_residueRingEquiv_injective K Ksep S
    exact congr_arg AlgEquiv.toRingEquiv hστ
  letI : Fintype (kU ≃ₐ[k] kU) := AlgEquiv.fintype k kU
  letI : Fintype (U ≃ₐ[K] U) := AlgEquiv.fintype K U
  letI : Finite (kU ≃ₐ[k] kU) := Finite.of_fintype _
  letI : Finite (U ≃ₐ[K] U) := Finite.of_fintype _
  have hcard : Nat.card (kU ≃ₐ[k] kU) = Nat.card (U ≃ₐ[K] U) := by
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
      residue_finrank_eq_finrank_of_unramified K Ksep U hU]
  have hred_bijective : Function.Bijective red :=
    hred_injective.bijective_of_nat_card_le hcard.le
  let φbar : kU ≃ₐ[k] kU := FiniteField.frobeniusAlgEquivOfAlgebraic k kU
  obtain ⟨φ, hφ⟩ := hred_bijective.2 φbar
  refine ⟨⟨φ, ?_, ?_, ?_⟩⟩
  · change ∀ x : RingOfIntegers U,
      ∃ y : RingOfIntegers U, (y : U) = φ (x : U)
    intro x
    let φO := unramifiedAlgEquivOnIntegers K Ksep U hU φ
    exact ⟨φO x, rfl⟩
  · change ∀ (x y : RingOfIntegers U),
      (y : U) = φ (x : U) →
        IsLocalRing.residue 𝒪[U] y =
          (IsLocalRing.residue 𝒪[U] x) ^ residueCard K
    intro x y hy
    let φO := unramifiedAlgEquivOnIntegers K Ksep U hU φ
    have hyO : y = φO x := Subtype.ext hy
    subst y
    calc
      IsLocalRing.residue 𝒪[U] (φO x) = red φ (IsLocalRing.residue 𝒪[U] x) := by
        rfl
      _ = φbar (IsLocalRing.residue 𝒪[U] x) :=
        DFunLike.congr_fun hφ (IsLocalRing.residue 𝒪[U] x)
      _ = (IsLocalRing.residue 𝒪[U] x) ^ residueCard K := by
        have hkcard : Fintype.card k = residueCard K := by
          change Fintype.card k = Nat.card k
          exact (Nat.card_eq_fintype_card (α := k)).symm
        rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hkcard]
  · rw [Subgroup.eq_top_iff']
    intro τ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k kU).2 (red τ)
    have hpow : φ ^ i.1 = τ := by
      apply hred_injective
      rw [map_pow, hφ]
      exact hi
    rw [← hpow]
    exact Subgroup.pow_mem (Subgroup.zpowers φ) (Subgroup.mem_zpowers φ) i.1

/-- The arithmetic-Frobenius data still needed on a family of already constructed seeded levels. -/
private structure UnramifiedLevelFrobeniusData [IsSepClosure K Ksep]
    (S : ∀ n : ℕ, UnramifiedLevelSeed K Ksep (n + 1)) where
  frobenius : ∀ n,
    unramifiedLevelField K Ksep (S n) ≃ₐ[K] unramifiedLevelField K Ksep (S n)
  preserves_integral : ∀ n,
    letI : FiniteDimensional K (unramifiedLevelField K Ksep (S n)) :=
      unramifiedLevelFieldFiniteDimensional K Ksep (S n)
    let hU : IsUnramifiedIntermediateField K Ksep (unramifiedLevelField K Ksep (S n)) :=
      unramifiedLevelField_isUnramified K Ksep (S n)
    letI : ValuativeRel (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldValuativeRel K Ksep _ hU
    letI : TopologicalSpace (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldTopology K Ksep _ hU
    letI : IsNonarchimedeanLocalField (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldLocalField K Ksep _ hU
    ∀ x : RingOfIntegers (unramifiedLevelField K Ksep (S n)),
      ∃ y : RingOfIntegers (unramifiedLevelField K Ksep (S n)),
        (y : unramifiedLevelField K Ksep (S n)) =
          frobenius n (x : unramifiedLevelField K Ksep (S n))
  residue_action : ∀ n,
    letI : FiniteDimensional K (unramifiedLevelField K Ksep (S n)) :=
      unramifiedLevelFieldFiniteDimensional K Ksep (S n)
    let hU : IsUnramifiedIntermediateField K Ksep (unramifiedLevelField K Ksep (S n)) :=
      unramifiedLevelField_isUnramified K Ksep (S n)
    letI : ValuativeRel (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldValuativeRel K Ksep _ hU
    letI : TopologicalSpace (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldTopology K Ksep _ hU
    letI : IsNonarchimedeanLocalField (unramifiedLevelField K Ksep (S n)) :=
      unramifiedIntermediateFieldLocalField K Ksep _ hU
    ∀ (x y : RingOfIntegers (unramifiedLevelField K Ksep (S n))),
      (y : unramifiedLevelField K Ksep (S n)) =
          frobenius n (x : unramifiedLevelField K Ksep (S n)) →
        Ideal.Quotient.mk (LocalMaximalIdeal (unramifiedLevelField K Ksep (S n))) y =
          (Ideal.Quotient.mk
            (LocalMaximalIdeal (unramifiedLevelField K Ksep (S n))) x) ^ residueCard K
  generates : ∀ n, Subgroup.zpowers (frobenius n) = ⊤
  compatible : ∀ {a b : ℕ} (h : a + 1 ∣ b + 1)
      (x : unramifiedLevelField K Ksep (S a)),
    IntermediateField.inclusion (unramifiedLevelFields_le_of_dvd K Ksep S h)
        (frobenius a x) =
      frobenius b
        (IntermediateField.inclusion (unramifiedLevelFields_le_of_dvd K Ksep S h) x)

/-- Residual 1: arithmetic Frobenius exists on all seeded levels, generates each Galois group,
and is compatible with the canonical divisibility inclusions. -/
private theorem unramifiedLevelFrobeniusData_exists [IsSepClosure K Ksep]
    (S : ∀ n : ℕ, UnramifiedLevelSeed K Ksep (n + 1)) :
    Nonempty (UnramifiedLevelFrobeniusData K Ksep S) := by
  let D (n : ℕ) : UnramifiedLevelFrobeniusDatum K Ksep (S n) :=
    (unramifiedLevelFrobeniusDatum_exists K Ksep (S n)).some
  refine ⟨
    { frobenius := fun n => (D n).frobenius
      preserves_integral := fun n => (D n).preserves_integral
      residue_action := fun n => (D n).residue_action
      generates := fun n => (D n).generates
      compatible := ?_ }⟩
  intro a b h
  let Ua := unramifiedLevelField K Ksep (S a)
  let Ub := unramifiedLevelField K Ksep (S b)
  letI : FiniteDimensional K Ua :=
    unramifiedLevelFieldFiniteDimensional K Ksep (S a)
  letI : FiniteDimensional K Ub :=
    unramifiedLevelFieldFiniteDimensional K Ksep (S b)
  let hUa : IsUnramifiedIntermediateField K Ksep Ua :=
    unramifiedLevelField_isUnramified K Ksep (S a)
  let hUb : IsUnramifiedIntermediateField K Ksep Ub :=
    unramifiedLevelField_isUnramified K Ksep (S b)
  letI : ValuativeRel Ua := unramifiedIntermediateFieldValuativeRel K Ksep Ua hUa
  letI : TopologicalSpace Ua := unramifiedIntermediateFieldTopology K Ksep Ua hUa
  letI : IsNonarchimedeanLocalField Ua :=
    unramifiedIntermediateFieldLocalField K Ksep Ua hUa
  letI : ValuativeExtension K Ua :=
    unramifiedIntermediateFieldValuativeExtension K Ksep Ua hUa
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation Ua) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : ValuativeRel Ub := unramifiedIntermediateFieldValuativeRel K Ksep Ub hUb
  letI : TopologicalSpace Ub := unramifiedIntermediateFieldTopology K Ksep Ub hUb
  letI : IsNonarchimedeanLocalField Ub :=
    unramifiedIntermediateFieldLocalField K Ksep Ub hUb
  letI : ValuativeExtension K Ub :=
    unramifiedIntermediateFieldValuativeExtension K Ksep Ub hUb
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation Ub) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let hab : Ua ≤ Ub := unramifiedLevelFields_le_of_dvd K Ksep S h
  let inc : Ua →ₐ[K] Ub := IntermediateField.inclusion hab
  letI : Algebra Ua Ub := intermediateFieldInclusionAlgebra K Ksep hab
  letI : Module.Finite 𝒪[K] 𝒪[Ua] := ringOfIntegers_module_finite K Ua
  letI : Module.Finite 𝒪[K] 𝒪[Ub] := ringOfIntegers_module_finite K Ub
  have inc_mem (z : 𝒪[Ua]) :
      inc (z : Ua) ∈ (ValuativeRel.valuation Ub).integer := by
    have hzO : IsIntegral 𝒪[K] z := Algebra.IsIntegral.isIntegral z
    have hzUa : IsIntegral 𝒪[K] (z : Ua) :=
      IsIntegral.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[Ua] Ua) hzO
    have hzUb : IsIntegral 𝒪[K] (inc (z : Ua)) := IsIntegral.map inc hzUa
    exact (Valuation.integer.integers (ValuativeRel.valuation Ub)).mem_of_integral
      hzUb.tower_top
  let incO : 𝒪[Ua] →ₐ[𝒪[K]] 𝒪[Ub] :=
    { toFun := fun z => ⟨inc (z : Ua), inc_mem z⟩
      map_one' := Subtype.ext (map_one inc)
      map_mul' := fun x y => Subtype.ext (map_mul inc (x : Ua) (y : Ua))
      map_zero' := Subtype.ext (map_zero inc)
      map_add' := fun x y => Subtype.ext (map_add inc (x : Ua) (y : Ua))
      commutes' := fun x => Subtype.ext (inc.commutes (x : K)) }
  have hincO_injective : Function.Injective incO := by
    intro x y hxy
    apply Subtype.ext
    exact inc.injective (congr_arg Subtype.val hxy)
  letI : Algebra 𝒪[Ua] 𝒪[Ub] := incO.toRingHom.toAlgebra
  letI : IsScalarTower 𝒪[K] 𝒪[Ua] 𝒪[Ub] :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hincO_integral : incO.toRingHom.IsIntegral := by
    intro z
    exact (Algebra.IsIntegral.isIntegral (R := 𝒪[K]) z).tower_top
  letI : IsLocalHom incO.toRingHom :=
    hincO_integral.isLocalHom hincO_injective
  let φa := (D a).frobenius
  let φb := (D b).frobenius
  let φaO := unramifiedAlgEquivOnIntegers K Ksep Ua hUa φa
  let φbO := unramifiedAlgEquivOnIntegers K Ksep Ub hUb φb
  let g : Ua := IntermediateField.AdjoinSimple.gen K (S a).root
  have hgpoly : Polynomial.aeval g (S a).lift.poly = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, ← (S a).minpoly_eq,
      ← IntermediateField.minpoly_gen K (S a).root]
    exact minpoly.aeval K g
  have hgK : IsIntegral 𝒪[K] g :=
    ⟨(S a).lift.poly, (S a).lift.monic,
      by simpa only [Polynomial.aeval_def] using hgpoly⟩
  have hgmem : (g : Ua) ∈ (ValuativeRel.valuation Ua).integer :=
    (Valuation.integer.integers (ValuativeRel.valuation Ua)).mem_of_integral
      hgK.tower_top
  let og : 𝒪[Ua] := ⟨g, hgmem⟩
  let fUa := (S a).lift.poly.map (algebraMap 𝒪[K] 𝒪[Ua])
  let fUb := (S a).lift.poly.map (algebraMap 𝒪[K] 𝒪[Ub])
  have hpolyUa : fUa.map (algebraMap 𝒪[Ua] Ua) =
      (S a).lift.poly.map (algebraMap 𝒪[K] Ua) := by
    dsimp only [fUa]
    rw [Polynomial.map_map]
    congr 1
  have hogroot : fUa.IsRoot og := by
    apply Polynomial.IsRoot.of_map (f := algebraMap 𝒪[Ua] Ua) _
      (fun _ _ hz => Subtype.ext hz)
    rw [hpolyUa]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hgpoly
    exact hgpoly
  have hmapφa : fUa.map φaO.toRingHom = fUa := by
    dsimp only [fUa]
    rw [Polynomial.map_map]
    congr 1
    exact φaO.toAlgHom.comp_algebraMap
  have hmapφb : fUb.map φbO.toRingHom = fUb := by
    dsimp only [fUb]
    rw [Polynomial.map_map]
    congr 1
    exact φbO.toAlgHom.comp_algebraMap
  have hmapinc : fUa.map incO.toRingHom = fUb := by
    dsimp only [fUa, fUb]
    rw [Polynomial.map_map]
    congr 1
  let z₁ : 𝒪[Ub] := incO (φaO og)
  let z₂ : 𝒪[Ub] := φbO (incO og)
  have hz₁root : fUb.IsRoot z₁ := by
    have hz := (hogroot.map (f := φaO.toRingHom)).map (f := incO.toRingHom)
    rw [hmapφa, hmapinc] at hz
    exact hz
  have hz₂root : fUb.IsRoot z₂ := by
    have hz := (hogroot.map (f := incO.toRingHom)).map (f := φbO.toRingHom)
    rw [hmapinc, hmapφb] at hz
    exact hz
  let resMap : LocalResidueField Ua →+* LocalResidueField Ub :=
    IsLocalRing.ResidueField.map incO.toRingHom
  have hresMap (z : 𝒪[Ua]) :
      IsLocalRing.residue 𝒪[Ub] (incO z) =
        resMap (IsLocalRing.residue 𝒪[Ua] z) := by
    exact (IsLocalRing.ResidueField.map_residue incO.toRingHom z).symm
  have hresa : IsLocalRing.residue 𝒪[Ua] (φaO og) =
      (IsLocalRing.residue 𝒪[Ua] og) ^ residueCard K :=
    (D a).residue_action og (φaO og) rfl
  have hresb : IsLocalRing.residue 𝒪[Ub] (φbO (incO og)) =
      (IsLocalRing.residue 𝒪[Ub] (incO og)) ^ residueCard K :=
    (D b).residue_action (incO og) (φbO (incO og)) rfl
  have hres : IsLocalRing.residue 𝒪[Ub] z₁ =
      IsLocalRing.residue 𝒪[Ub] z₂ := by
    calc
      IsLocalRing.residue 𝒪[Ub] z₁ =
          resMap (IsLocalRing.residue 𝒪[Ua] (φaO og)) := hresMap (φaO og)
      _ = resMap ((IsLocalRing.residue 𝒪[Ua] og) ^ residueCard K) := by
        rw [hresa]
      _ = (resMap (IsLocalRing.residue 𝒪[Ua] og)) ^ residueCard K :=
        map_pow resMap (IsLocalRing.residue 𝒪[Ua] og) (residueCard K)
      _ = (IsLocalRing.residue 𝒪[Ub] (incO og)) ^ residueCard K := by
        rw [hresMap]
      _ = IsLocalRing.residue 𝒪[Ub] z₂ := hresb.symm
  have hz : z₁ = z₂ :=
    unramifiedLift_root_unique K Ksep (S a) Ub hUb z₁ z₂ hz₁root hz₂root hres
  have hgen : inc (φa g) = φb (inc g) := congr_arg Subtype.val hz
  have hhom : inc.comp φa.toAlgHom = φb.toAlgHom.comp inc := by
    apply (IntermediateField.adjoin.powerBasis
      (Algebra.IsIntegral.isIntegral (S a).root)).algHom_ext
    exact hgen
  intro x
  exact DFunLike.congr_fun hhom x

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Residual 2: composita of a finite Galois intermediate field with a seeded unramified level
carry the required compatible local-field data and remain unramified over the left field. -/
private theorem unramifiedLevelField_compositumData_exists [IsSepClosure K Ksep]
    {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (E : IntermediateField K Ksep)
    [FiniteDimensional K E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] [ContinuousSMul K E]
    (hE : IsGalois K E) :
    letI : FiniteDimensional K (unramifiedLevelField K Ksep S) :=
      unramifiedLevelFieldFiniteDimensional K Ksep S
    Nonempty (UnramifiedCompositumLocalFieldData K Ksep E
      (unramifiedLevelField K Ksep S) hE
      (unramifiedLevelField_isGalois K Ksep S)
      (unramifiedLevelField_isUnramified K Ksep S)) := by
  let U := unramifiedLevelField K Ksep S
  letI : FiniteDimensional K U := unramifiedLevelFieldFiniteDimensional K Ksep S
  let hU : IsUnramifiedIntermediateField K Ksep U :=
    unramifiedLevelField_isUnramified K Ksep S
  letI : IsGalois K U := unramifiedLevelField_isGalois K Ksep S
  letI : IsGalois K E := hE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  have hd : 0 < d := by
    rw [← S.lift.natDegree, ← S.lift.monic.natDegree_map
      (IsLocalRing.residue 𝒪[K])]
    exact S.lift.reduction_irreducible.natDegree_pos
  letI : IsSepClosure E Ksep :=
    { sep_closed := IsSepClosure.sep_closed K
      separable := ⟨fun x =>
        IsSeparable.tower_top E (Algebra.IsSeparable.isSeparable K x)⟩ }
  let SE : UnramifiedLevelSeed E Ksep d :=
    (unramifiedLevelSeed_exists E Ksep d hd).some
  let W := unramifiedLevelField E Ksep SE
  letI : FiniteDimensional E W := unramifiedLevelFieldFiniteDimensional E Ksep SE
  let hW : IsUnramifiedIntermediateField E Ksep W :=
    unramifiedLevelField_isUnramified E Ksep SE
  letI : ValuativeRel W := unramifiedIntermediateFieldValuativeRel E Ksep W hW
  letI : TopologicalSpace W := unramifiedIntermediateFieldTopology E Ksep W hW
  letI : IsNonarchimedeanLocalField W :=
    unramifiedIntermediateFieldLocalField E Ksep W hW
  letI : ValuativeExtension E W :=
    unramifiedIntermediateFieldValuativeExtension E Ksep W hW
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation W) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra K W :=
    ((algebraMap E W).comp (algebraMap K E)).toAlgebra
  letI : IsScalarTower K E W := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let hKW : ValuativeExtension K W := by
    constructor
    intro x y
    change algebraMap K W x ≤ᵥ algebraMap K W y ↔ x ≤ᵥ y
    rw [show algebraMap K W x = algebraMap E W (algebraMap K E x) from rfl,
      show algebraMap K W y = algebraMap E W (algebraMap K E y) from rfl,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]
  letI : ValuativeExtension K W := hKW
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation W) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kE := LocalResidueField E
  let kW := LocalResidueField W
  letI : Algebra k kE :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[E])
      (IsLocalRing.maximalIdeal 𝒪[K])
  letI : Algebra kE kW :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[W])
      (IsLocalRing.maximalIdeal 𝒪[E])
  letI : Algebra k kW :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal 𝒪[W])
      (IsLocalRing.maximalIdeal 𝒪[K])
  letI : IsScalarTower k kE kW := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hresW : Module.finrank kE kW = d := by
    rw [residue_finrank_eq_finrank_of_unramified E Ksep W hW,
      unramifiedLevelField_finrank E Ksep SE]
  have hdiv : d ∣ Module.finrank k kW := by
    rw [← Module.finrank_mul_finrank k kE kW, hresW]
    exact dvd_mul_left d (Module.finrank k kE)
  let fbar := S.lift.poly.map (IsLocalRing.residue 𝒪[K])
  obtain ⟨a₀, ha₀⟩ := finiteField_irreducible_root_of_natDegree_dvd_finrank
    fbar S.lift.reduction_irreducible (by
      rw [S.lift.monic.natDegree_map, S.lift.natDegree]
      exact hdiv)
  let fW := S.lift.poly.map (algebraMap 𝒪[K] 𝒪[W])
  have hfW : fW.Monic := S.lift.monic.map _
  have hsep : fbar.Separable :=
    PerfectField.separable_of_irreducible S.lift.reduction_irreducible
  have hderiv₀ : Polynomial.aeval a₀ fbar.derivative ≠ 0 :=
    hsep.aeval_derivative_ne_zero ha₀
  have hcomm :
      (algebraMap k kW).comp (IsLocalRing.residue 𝒪[K]) =
        (IsLocalRing.residue 𝒪[W]).comp (algebraMap 𝒪[K] 𝒪[W]) := rfl
  have hrootW : Polynomial.aeval a₀ fW = 0 := by
    change Polynomial.eval₂ (IsLocalRing.residue 𝒪[W]) a₀
      (S.lift.poly.map (algebraMap 𝒪[K] 𝒪[W])) = 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have ha₀' := ha₀
    rw [Polynomial.aeval_def, show fbar =
      S.lift.poly.map (IsLocalRing.residue 𝒪[K]) from rfl,
      Polynomial.eval₂_map] at ha₀'
    exact ha₀'
  have hderivW : Polynomial.aeval a₀ fW.derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    change Polynomial.eval₂ (IsLocalRing.residue 𝒪[W]) a₀
      (S.lift.poly.derivative.map (algebraMap 𝒪[K] 𝒪[W])) ≠ 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have hderiv₀' := hderiv₀
    rw [Polynomial.aeval_def, show fbar.derivative =
      S.lift.poly.derivative.map (IsLocalRing.residue 𝒪[K]) by
        rw [Polynomial.derivative_map],
      Polynomial.eval₂_map] at hderiv₀'
    exact hderiv₀'
  letI : UniformSpace W := IsTopologicalAddGroup.rightUniformSpace W
  letI : IsUniformAddGroup W := isUniformAddGroup_of_addCommGroup
  obtain ⟨zO, hzO, _⟩ :=
    hensel_lift_residue_root 𝒪[W] fW hfW a₀ hrootW hderivW
  let fK := S.lift.poly.map (algebraMap 𝒪[K] K)
  have hfR : Irreducible S.lift.poly :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (IsLocalRing.residue 𝒪[K]) S.lift.poly S.lift.monic
        S.lift.reduction_irreducible
  have hfK : Irreducible fK :=
    (S.lift.monic.irreducible_iff_irreducible_map_fraction_map).1 hfR
  have hpolyW : fW.map (algebraMap 𝒪[W] W) = fK.map (algebraMap K W) := by
    dsimp only [fW, fK]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hzW : (fK.map (algebraMap K W)).IsRoot (zO : W) := by
    rw [← hpolyW]
    exact hzO.map
  let z : Ksep := W.val (zO : W)
  have hzaeval : Polynomial.aeval z fK = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hz := hzW.map (f := W.val.toRingHom)
    have hcomp : W.val.toRingHom.comp (algebraMap K W) = algebraMap K Ksep := by
      apply RingHom.ext
      intro x
      rfl
    rw [Polynomial.map_map, hcomp] at hz
    exact hz
  have hminz : fK = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hfK hzaeval (S.lift.monic.map _)
  have hsplitf : (fK.map (algebraMap K U)).Splits := by
    have hs := IsGalois.splits K (IntermediateField.AdjoinSimple.gen K S.root)
    rw [IntermediateField.minpoly_gen, S.minpoly_eq] at hs
    exact hs
  have hzU : z ∈ U := by
    apply (Algebra.IsIntegral.isIntegral z).mem_intermediateField_of_minpoly_splits
    rw [← hminz]
    exact hsplitf
  let Z := IntermediateField.adjoin K {z}
  have hZleU : Z ≤ U := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzU
  let WK := W.restrictScalars K
  have hzWK : z ∈ WK := (zO : W).prop
  have hZleWK : Z ≤ WK := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzWK
  haveI : FiniteDimensional K Z :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hZrank : Module.finrank K Z = d := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral z), ← hminz]
    exact (S.lift.monic.natDegree_map (algebraMap 𝒪[K] K)).trans S.lift.natDegree
  have hZU : Z = U := IntermediateField.eq_of_le_of_finrank_eq hZleU
    (hZrank.trans (unramifiedLevelField_finrank K Ksep S).symm)
  have hUleWK : U ≤ WK := hZU ▸ hZleWK
  have hEleWK : E ≤ WK := by
    intro x hx
    exact W.algebraMap_mem ⟨x, hx⟩
  let C := E ⊔ U
  have hCleWK : C ≤ WK := sup_le hEleWK hUleWK
  letI : FiniteDimensional K C := IntermediateField.finiteDimensional_sup E U
  letI : Algebra E C := intermediateFieldInclusionAlgebra K Ksep le_sup_left
  letI : IsScalarTower K E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional E C := FiniteDimensional.right K E C
  obtain ⟨vC, tC, hC, hEC, hsmulE⟩ := finiteExtension_localFieldData_exists E C
  letI : ValuativeRel C := vC
  letI : TopologicalSpace C := tC
  letI : IsNonarchimedeanLocalField C := hC
  letI : ValuativeExtension E C := hEC
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation C) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let hKC : ValuativeExtension K C := by
    constructor
    intro x y
    change algebraMap K C x ≤ᵥ algebraMap K C y ↔ x ≤ᵥ y
    rw [show algebraMap K C x = algebraMap E C (algebraMap K E x) from rfl,
      show algebraMap K C y = algebraMap E C (algebraMap K E y) from rfl,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]
  letI : ValuativeExtension K C := hKC
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation C) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let CE : IntermediateField E Ksep :=
    IntermediateField.extendScalars (show E ≤ C from le_sup_left)
  have hCEleW : CE ≤ W := by
    intro x hx
    exact hCleWK hx
  let j : C →ₐ[E] W := IntermediateField.inclusion hCEleW
  letI : Algebra C W := j.toRingHom.toAlgebra
  letI : IsScalarTower E C W := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional C W := FiniteDimensional.right E C W
  letI : Module.Finite 𝒪[E] 𝒪[C] := ringOfIntegers_module_finite E C
  letI : Module.Finite 𝒪[E] 𝒪[W] := ringOfIntegers_module_finite E W
  have hmemC (x : C) :
      x ∈ (ValuativeRel.valuation C).integer ↔ IsIntegral 𝒪[E] x := by
    constructor
    · intro hx
      let ox : 𝒪[C] := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom 𝒪[E] 𝒪[C] C)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation C)).mem_of_integral
        hx.tower_top
  have hmemW (x : W) :
      x ∈ (ValuativeRel.valuation W).integer ↔ IsIntegral 𝒪[E] x := by
    constructor
    · intro hx
      let ox : 𝒪[W] := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom 𝒪[E] 𝒪[W] W)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation W)).mem_of_integral
        hx.tower_top
  have hinteger : (ValuativeRel.valuation W).integer.comap (algebraMap C W) =
      (ValuativeRel.valuation C).integer := by
    ext x
    change algebraMap C W x ∈ (ValuativeRel.valuation W).integer ↔
      x ∈ (ValuativeRel.valuation C).integer
    rw [hmemW, hmemC]
    exact isIntegral_algHom_iff (j.restrictScalars 𝒪[E]) j.injective
  letI : (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation W) :=
    Valuation.HasExtension.ofComapInteger hinteger
  let hCW : ValuativeExtension C W := by
    constructor
    intro x y
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation W),
      Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation C)
        (ValuativeRel.valuation W),
      ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation C)]
  letI : ValuativeExtension C W := hCW
  let πE := (defaultUniformizer E).val
  have hEW := normalizedValuation_algebraMap E W πE
  rw [(unramifiedIntermediateFieldIsUnramified E Ksep W hW).ramificationIndex_eq_one,
    (defaultUniformizer E).valuation_eq_one] at hEW
  norm_num at hEW
  have hECval := normalizedValuation_algebraMap E C πE
  rw [(defaultUniformizer E).valuation_eq_one, mul_one] at hECval
  let πC : Units C := Units.map (algebraMap E C) πE
  have hCWval := normalizedValuation_algebraMap C W πC
  have hπcomp : Units.map (algebraMap C W).toMonoidHom πC =
      Units.map (algebraMap E W).toMonoidHom πE := by
    apply Units.ext
    rfl
  have hram : ramificationIndex E C = 1 := by
    have hleft : normalizedValuation W
        (Units.map (algebraMap C W).toMonoidHom πC) = 1 :=
      (congr_arg (normalizedValuation W) hπcomp).trans hEW
    have hπC : normalizedValuation C πC = (ramificationIndex E C : ℤ) := hECval
    have heq : (1 : ℤ) =
        (ramificationIndex C W : ℤ) * (ramificationIndex E C : ℤ) := by
      calc
        (1 : ℤ) = normalizedValuation W
            (Units.map (algebraMap C W).toMonoidHom πC) := hleft.symm
        _ = (ramificationIndex C W : ℤ) * normalizedValuation C πC := hCWval
        _ = (ramificationIndex C W : ℤ) * (ramificationIndex E C : ℤ) := by
          rw [hπC]
    have hn : 1 = ramificationIndex C W * ramificationIndex E C := by
      exact_mod_cast heq
    apply Nat.eq_one_of_dvd_one
    rw [hn]
    exact dvd_mul_left (ramificationIndex E C) (ramificationIndex C W)
  let hCEunr : IsUnramifiedLocalExtension E C := ⟨hram⟩
  letI : ValuativeRel U := unramifiedIntermediateFieldValuativeRel K Ksep U hU
  letI : TopologicalSpace U := unramifiedIntermediateFieldTopology K Ksep U hU
  letI : IsNonarchimedeanLocalField U :=
    unramifiedIntermediateFieldLocalField K Ksep U hU
  letI : ValuativeExtension K U :=
    unramifiedIntermediateFieldValuativeExtension K Ksep U hU
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let q : U →ₐ[K] C := IntermediateField.inclusion le_sup_right
  letI : Algebra U C := q.toRingHom.toAlgebra
  letI : IsScalarTower K U C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional U C := FiniteDimensional.right K U C
  letI : Module.Finite 𝒪[K] 𝒪[U] := ringOfIntegers_module_finite K U
  letI : Module.Finite 𝒪[K] 𝒪[C] := ringOfIntegers_module_finite K C
  have hmemU (x : U) :
      x ∈ (ValuativeRel.valuation U).integer ↔ IsIntegral 𝒪[K] x := by
    constructor
    · intro hx
      let ox : 𝒪[U] := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[U] U)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation U)).mem_of_integral
        hx.tower_top
  have hmemCK (x : C) :
      x ∈ (ValuativeRel.valuation C).integer ↔ IsIntegral 𝒪[K] x := by
    constructor
    · intro hx
      let ox : 𝒪[C] := ⟨x, hx⟩
      exact IsIntegral.map (IsScalarTower.toAlgHom 𝒪[K] 𝒪[C] C)
        (Algebra.IsIntegral.isIntegral ox)
    · intro hx
      exact (Valuation.integer.integers (ValuativeRel.valuation C)).mem_of_integral
        hx.tower_top
  have hintegerUC : (ValuativeRel.valuation C).integer.comap (algebraMap U C) =
      (ValuativeRel.valuation U).integer := by
    ext x
    change algebraMap U C x ∈ (ValuativeRel.valuation C).integer ↔
      x ∈ (ValuativeRel.valuation U).integer
    rw [hmemCK, hmemU]
    exact isIntegral_algHom_iff (q.restrictScalars 𝒪[K]) q.injective
  letI : (ValuativeRel.valuation U).HasExtension (ValuativeRel.valuation C) :=
    Valuation.HasExtension.ofComapInteger hintegerUC
  let hUC : ValuativeExtension U C := by
    constructor
    intro x y
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation C),
      Valuation.HasExtension.val_map_le_iff (ValuativeRel.valuation U)
        (ValuativeRel.valuation C),
      ← Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation U)]
  letI : ValuativeExtension U C := hUC
  let hsmulK : ContinuousSMul K C := by
    constructor
    have hcont : Continuous (fun p : K × C => algebraMap K C p.1 * p.2) :=
      ((continuous_algebraMap_of_valuativeExtension K C).comp continuous_fst).mul
        continuous_snd
    simpa only [Algebra.smul_def] using hcont
  let hsmulU : ContinuousSMul U C := by
    constructor
    have hcont : Continuous (fun p : U × C => algebraMap U C p.1 * p.2) :=
      ((continuous_algebraMap_of_valuativeExtension U C).comp continuous_fst).mul
        continuous_snd
    simpa only [Algebra.smul_def] using hcont
  let hGC : IsGalois K C := by infer_instance
  letI : IsGalois K C := hGC
  let hGEC : IsGalois E C := IsGalois.tower_top_of_isGalois K E C
  refine ⟨
    { compositumValuativeRel := vC
      compositumTopology := tC
      compositumLocalField := hC
      finiteDimensional_left := inferInstance
      finiteDimensional_right := by
        letI : Algebra U C := intermediateFieldInclusionAlgebra K Ksep le_sup_right
        letI : IsScalarTower K U C := IsScalarTower.of_algebraMap_eq fun _ => rfl
        exact FiniteDimensional.right K U C
      scalarTower_left := inferInstance
      scalarTower_right := by
        exact IsScalarTower.of_algebraMap_eq fun _ => rfl
      isGalois_base := hGC
      isGalois_left := hGEC
      valuativeExtension_base := hKC
      valuativeExtension_left := hEC
      valuativeExtension_right := hUC
      continuousSMul_base := hsmulK
      continuousSMul_left := hsmulE
      continuousSMul_right := hsmulU
      unramified_left := hCEunr }⟩

/-- Residual 3: intersections of seeded levels have the degree prescribed by the gcd. -/
private theorem unramifiedLevelFields_intersection_finrank [IsSepClosure K Ksep]
    (S : ∀ n : ℕ, UnramifiedLevelSeed K Ksep (n + 1)) (a b : ℕ) :
    Module.finrank K
      (unramifiedLevelField K Ksep (S a) ⊓ unramifiedLevelField K Ksep (S b) :
        IntermediateField K Ksep) = Nat.gcd (a + 1) (b + 1) := by
  let U := unramifiedLevelField K Ksep (S a)
  let V := unramifiedLevelField K Ksep (S b)
  let I := U ⊓ V
  letI : FiniteDimensional K U :=
    unramifiedLevelFieldFiniteDimensional K Ksep (S a)
  letI : FiniteDimensional K V :=
    unramifiedLevelFieldFiniteDimensional K Ksep (S b)
  letI : FiniteDimensional K I :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (show I ≤ U from inf_le_left)).toLinearMap
      (IntermediateField.inclusion_injective (show I ≤ U from inf_le_left))
  let g := Nat.gcd (a + 1) (b + 1)
  let c := g - 1
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left (b + 1) (Nat.succ_pos a)
  have hc : c + 1 = g := by
    dsimp only [c]
    omega
  have hca : c + 1 ∣ a + 1 := by
    rw [hc]
    exact Nat.gcd_dvd_left (a + 1) (b + 1)
  have hcb : c + 1 ∣ b + 1 := by
    rw [hc]
    exact Nat.gcd_dvd_right (a + 1) (b + 1)
  have hlevel : unramifiedLevelField K Ksep (S c) ≤ I := by
    apply le_inf
    · exact unramifiedLevelFields_le_of_dvd K Ksep S hca
    · exact unramifiedLevelFields_le_of_dvd K Ksep S hcb
  have hlower : g ≤ Module.finrank K I := by
    rw [← hc, ← unramifiedLevelField_finrank K Ksep (S c)]
    exact IntermediateField.finrank_le_of_le_right hlevel
  have hdivU : Module.finrank K I ∣ a + 1 := by
    rw [← unramifiedLevelField_finrank K Ksep (S a)]
    exact IntermediateField.finrank_dvd_of_le_right (show I ≤ U from inf_le_left)
  have hdivV : Module.finrank K I ∣ b + 1 := by
    rw [← unramifiedLevelField_finrank K Ksep (S b)]
    exact IntermediateField.finrank_dvd_of_le_right (show I ≤ V from inf_le_right)
  have hupper : Module.finrank K I ≤ g :=
    Nat.le_of_dvd hgpos (Nat.dvd_gcd hdivU hdivV)
  exact le_antisymm hupper hlower

private theorem unramifiedTower_lifting_classification [IsSepClosure K Ksep] :
    ∃ T : UnramifiedTower K Ksep,
      ∀ (n : ℕ) (E : IntermediateField K Ksep) [FiniteDimensional K E],
        IsUnramifiedIntermediateField K Ksep E →
          Module.finrank K E = n + 1 → E = T.field n := by
  let S : ∀ n : ℕ, UnramifiedLevelSeed K Ksep (n + 1) := fun n =>
    (unramifiedLevelSeed_exists K Ksep (n + 1) (Nat.succ_pos n)).some
  let F : UnramifiedLevelFrobeniusData K Ksep S :=
    (unramifiedLevelFrobeniusData_exists K Ksep S).some
  let T : UnramifiedTower K Ksep :=
    { field := fun n => unramifiedLevelField K Ksep (S n)
      finiteDimensional := fun n => unramifiedLevelFieldFiniteDimensional K Ksep (S n)
      unramified := fun n => unramifiedLevelField_isUnramified K Ksep (S n)
      isGalois := fun n => unramifiedLevelField_isGalois K Ksep (S n)
      finrank := fun n => unramifiedLevelField_finrank K Ksep (S n)
      frobenius := F.frobenius
      frobenius_preserves_integral := F.preserves_integral
      frobenius_residue := F.residue_action
      frobenius_generates := F.generates
      le_of_dvd := fun h => unramifiedLevelFields_le_of_dvd K Ksep S h
      frobenius_compatible := F.compatible
      compositum_localField := by
        intro E _ _ _ _ _ _ hE n
        exact unramifiedLevelField_compositumData_exists K Ksep (S n) E hE
      intersection_finrank :=
        unramifiedLevelFields_intersection_finrank K Ksep S }
  refine ⟨T, ?_⟩
  intro n E _ hE hdegree
  have hle : unramifiedLevelField K Ksep (S n) ≤ E := by
    apply unramifiedLevelSeed_le_of_dvd K Ksep (S n) E hE
    rw [hdegree]
  have heq : unramifiedLevelField K Ksep (S n) = E :=
    IntermediateField.eq_of_le_of_finrank_eq hle
      ((unramifiedLevelField_finrank K Ksep (S n)).trans hdegree.symm)
  exact heq.symm

private theorem unramifiedLevelSeed_liftedRoot_of_residueFinrank
    [IsSepClosure K Ksep] {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (hdiv :
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
        ⟨ValuativeRel.isEquiv _ _⟩
      letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
        Ideal.Quotient.algebraOfLiesOver
          (IsLocalRing.maximalIdeal (RingOfIntegers L))
          (IsLocalRing.maximalIdeal (RingOfIntegers K))
      d ∣ Module.finrank (LocalResidueField K) (LocalResidueField L)) :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    ∃ a : RingOfIntegers L,
      (S.lift.poly.map
        (algebraMap (RingOfIntegers K) (RingOfIntegers L))).IsRoot a := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kL := LocalResidueField L
  letI : Algebra k kL :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let fbar := S.lift.poly.map (IsLocalRing.residue (RingOfIntegers K))
  have hfdeg : fbar.natDegree = d := by
    rw [S.lift.monic.natDegree_map, S.lift.natDegree]
  have hrootdiv : fbar.natDegree ∣ Module.finrank k kL := by
    rw [hfdeg]
    exact hdiv
  obtain ⟨a₀, ha₀⟩ := finiteField_irreducible_root_of_natDegree_dvd_finrank
    fbar S.lift.reduction_irreducible hrootdiv
  let fL := S.lift.poly.map (algebraMap (RingOfIntegers K) (RingOfIntegers L))
  have hfL : fL.Monic := S.lift.monic.map _
  have hsep : fbar.Separable :=
    PerfectField.separable_of_irreducible S.lift.reduction_irreducible
  have hderiv₀ : Polynomial.aeval a₀ fbar.derivative ≠ 0 :=
    hsep.aeval_derivative_ne_zero ha₀
  have hcomm :
      (algebraMap k kL).comp (IsLocalRing.residue (RingOfIntegers K)) =
        (IsLocalRing.residue (RingOfIntegers L)).comp
          (algebraMap (RingOfIntegers K) (RingOfIntegers L)) := rfl
  have hrootL : Polynomial.aeval a₀ fL = 0 := by
    change Polynomial.eval₂ (IsLocalRing.residue (RingOfIntegers L)) a₀
      (S.lift.poly.map
        (algebraMap (RingOfIntegers K) (RingOfIntegers L))) = 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have ha₀' := ha₀
    rw [Polynomial.aeval_def, show fbar =
      S.lift.poly.map (IsLocalRing.residue (RingOfIntegers K)) from rfl,
      Polynomial.eval₂_map] at ha₀'
    exact ha₀'
  have hderivL : Polynomial.aeval a₀ fL.derivative ≠ 0 := by
    rw [Polynomial.derivative_map]
    change Polynomial.eval₂ (IsLocalRing.residue (RingOfIntegers L)) a₀
      (S.lift.poly.derivative.map
        (algebraMap (RingOfIntegers K) (RingOfIntegers L))) ≠ 0
    rw [Polynomial.eval₂_map, ← hcomm]
    have hderiv₀' := hderiv₀
    rw [Polynomial.aeval_def, show fbar.derivative =
      S.lift.poly.derivative.map (IsLocalRing.residue (RingOfIntegers K)) by
        rw [Polynomial.derivative_map],
      Polynomial.eval₂_map] at hderiv₀'
    exact hderiv₀'
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  obtain ⟨a, ha, _⟩ :=
    hensel_lift_residue_root (RingOfIntegers L) fL hfL a₀ hrootL hderivL
  exact ⟨a, ha⟩

set_option maxHeartbeats 500000 in
private theorem unramifiedLevelSeed_le_fieldRange_of_residueFinrank
    [IsSepClosure K Ksep] {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (j : L →ₐ[K] Ksep)
    (hdiv :
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
        ⟨ValuativeRel.isEquiv _ _⟩
      letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
        Ideal.Quotient.algebraOfLiesOver
          (IsLocalRing.maximalIdeal (RingOfIntegers L))
          (IsLocalRing.maximalIdeal (RingOfIntegers K))
      d ∣ Module.finrank (LocalResidueField K) (LocalResidueField L)) :
    IntermediateField.adjoin K {S.root} ≤ j.fieldRange := by
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  obtain ⟨a, ha⟩ :=
    unramifiedLevelSeed_liftedRoot_of_residueFinrank K Ksep S L hdiv
  let fK := S.lift.poly.map (algebraMap (RingOfIntegers K) K)
  have hfR : Irreducible S.lift.poly :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (IsLocalRing.residue (RingOfIntegers K)) S.lift.poly S.lift.monic
        S.lift.reduction_irreducible
  have hfK : Irreducible fK :=
    (S.lift.monic.irreducible_iff_irreducible_map_fraction_map).1 hfR
  have hpolyL :
      (S.lift.poly.map
        (algebraMap (RingOfIntegers K) (RingOfIntegers L))).map
          (algebraMap (RingOfIntegers L) L) =
        fK.map (algebraMap K L) := by
    dsimp only [fK]
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
  have haL : (fK.map (algebraMap K L)).IsRoot (a : L) := by
    rw [← hpolyL]
    exact ha.map (f := algebraMap (RingOfIntegers L) L)
  let z : Ksep := j (a : L)
  have hzroot : (fK.map (algebraMap K Ksep)).IsRoot z := by
    have hz := haL.map (f := j.toRingHom)
    have hcomp : j.toRingHom.comp (algebraMap K L) = algebraMap K Ksep :=
      j.comp_algebraMap
    rw [Polynomial.map_map, hcomp] at hz
    exact hz
  have hzaeval : Polynomial.aeval z fK = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hzroot
  have hminz : fK = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hfK hzaeval (S.lift.monic.map _)
  letI : IsGalois K U := unramifiedLevelSeed_isGalois K Ksep S
  have hsplitf : (fK.map (algebraMap K U)).Splits := by
    have hs := IsGalois.splits K (IntermediateField.AdjoinSimple.gen K S.root)
    rw [IntermediateField.minpoly_gen, S.minpoly_eq] at hs
    exact hs
  have hzU : z ∈ U := by
    apply (Algebra.IsIntegral.isIntegral z).mem_intermediateField_of_minpoly_splits
    rw [← hminz]
    exact hsplitf
  let Z := IntermediateField.adjoin K {z}
  have hZleU : Z ≤ U := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzU
  have hzRange : z ∈ j.fieldRange := ⟨a, rfl⟩
  have hZleRange : Z ≤ j.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hzRange
  haveI : FiniteDimensional K Z :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hZrank : Module.finrank K Z = d := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral z), ← hminz]
    exact (S.lift.monic.natDegree_map
      (algebraMap (RingOfIntegers K) K)).trans S.lift.natDegree
  have hZU : Z = U := IntermediateField.eq_of_le_of_finrank_eq hZleU
    (hZrank.trans (unramifiedLevelSeed_finrank K Ksep S).symm)
  change U ≤ j.fieldRange
  rw [← hZU]
  exact hZleRange

set_option maxHeartbeats 500000 in
private theorem unramifiedLevelSeed_residueFinrank_dvd_of_le_fieldRange
    [IsSepClosure K Ksep] {d : ℕ} (S : UnramifiedLevelSeed K Ksep d)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (j : L →ₐ[K] Ksep)
    (hle : IntermediateField.adjoin K {S.root} ≤ j.fieldRange) :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver
        (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    d ∣ Module.finrank (LocalResidueField K) (LocalResidueField L) := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  let k := LocalResidueField K
  let kL := LocalResidueField L
  letI : Algebra k kL :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  have hrootmem : S.root ∈ j.fieldRange := hle
    (IntermediateField.subset_adjoin K {S.root} (Set.mem_singleton S.root))
  obtain ⟨a, ha⟩ := hrootmem
  have hmina : minpoly K a =
      S.lift.poly.map (algebraMap (RingOfIntegers K) K) := by
    calc
      minpoly K a = minpoly K (j a) := (minpoly.algHom_eq j j.injective a).symm
      _ = minpoly K S.root := congrArg (minpoly K) ha
      _ = S.lift.poly.map (algebraMap (RingOfIntegers K) K) := S.minpoly_eq
  have hapoly : Polynomial.aeval a S.lift.poly = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K, ← hmina]
    exact minpoly.aeval K a
  have haIntK : IsIntegral (RingOfIntegers K) a :=
    ⟨S.lift.poly, S.lift.monic,
      by simpa only [Polynomial.aeval_def] using hapoly⟩
  have haIntL : IsIntegral (RingOfIntegers L) a := haIntK.tower_top
  have hamem : a ∈ (ValuativeRel.valuation L).integer :=
    (Valuation.integer.integers (ValuativeRel.valuation L)).mem_of_integral haIntL
  let oa : RingOfIntegers L := ⟨a, hamem⟩
  let a₀ : kL := IsLocalRing.residue (RingOfIntegers L) oa
  let fbar := S.lift.poly.map (IsLocalRing.residue (RingOfIntegers K))
  have hrootbar : Polynomial.aeval a₀ fbar = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map
      (ψ := IsLocalRing.residue (RingOfIntegers L))
      (φ := IsLocalRing.residue (RingOfIntegers K)) rfl]
    rw [show Polynomial.aeval oa S.lift.poly = 0 from ?_, map_zero]
    apply Subtype.ext
    have hcoe : ((Polynomial.aeval oa S.lift.poly : RingOfIntegers L) : L) =
        Polynomial.aeval a S.lift.poly := by
      change algebraMap (RingOfIntegers L) L
          (Polynomial.aeval oa S.lift.poly) =
        Polynomial.aeval (algebraMap (RingOfIntegers L) L oa) S.lift.poly
      simpa only [Polynomial.map_id] using Polynomial.map_aeval_eq_aeval_map
        (φ := RingHom.id (RingOfIntegers K))
        (ψ := algebraMap (RingOfIntegers L) L) (by
          apply RingHom.ext
          intro x
          simp only [RingHom.comp_apply, RingHom.id_apply]
          change algebraMap (RingOfIntegers K) L x =
            algebraMap (RingOfIntegers L) L
              (algebraMap (RingOfIntegers K) (RingOfIntegers L) x)
          rw [show algebraMap (RingOfIntegers L) L
              (algebraMap (RingOfIntegers K) (RingOfIntegers L) x) =
            algebraMap K L (x : K) from
              Valuation.HasExtension.val_algebraMap
                (vR := ValuativeRel.valuation K)
                (vA := ValuativeRel.valuation L) x]
          rfl)
        S.lift.poly oa
    rw [hcoe]
    exact hapoly
  have hminbar : minpoly k a₀ = fbar :=
    (minpoly.eq_of_irreducible_of_monic S.lift.reduction_irreducible
      hrootbar (S.lift.monic.map _)).symm
  let A := IntermediateField.adjoin k {a₀}
  haveI : FiniteDimensional k A :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a₀)
  have hdegree : Module.finrank k A = d := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a₀),
      hminbar, S.lift.monic.natDegree_map, S.lift.natDegree]
  rw [← hdegree]
  calc
    Module.finrank k A ∣ Module.finrank k (⊤ : IntermediateField k kL) :=
      IntermediateField.finrank_dvd_of_le_right le_top
    _ = Module.finrank k kL := by simp

/-- A tower level embeds into a finite local extension whenever its degree divides the residue
field degree. -/
theorem UnramifiedTower.field_le_fieldRange_of_dvd_residueFinrank
    [IsSepClosure K Ksep] (T : UnramifiedTower K Ksep)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (j : L →ₐ[K] Ksep) (n : ℕ)
    (hdiv :
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
        ⟨ValuativeRel.isEquiv _ _⟩
      letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
        Ideal.Quotient.algebraOfLiesOver
          (IsLocalRing.maximalIdeal (RingOfIntegers L))
          (IsLocalRing.maximalIdeal (RingOfIntegers K))
      n + 1 ∣ Module.finrank (LocalResidueField K) (LocalResidueField L)) :
    T.field n ≤ j.fieldRange := by
  let S : UnramifiedLevelSeed K Ksep (n + 1) :=
    (unramifiedLevelSeed_exists K Ksep (n + 1) (Nat.succ_pos n)).some
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  have hUle : U ≤ j.fieldRange :=
    unramifiedLevelSeed_le_fieldRange_of_residueFinrank K Ksep S L j hdiv
  obtain ⟨T₀, hT₀⟩ := unramifiedTower_lifting_classification K Ksep
  have hUeq : U = T₀.field n :=
    hT₀ n U (unramifiedLevelSeed_isUnramified K Ksep S)
      (unramifiedLevelSeed_finrank K Ksep S)
  letI : FiniteDimensional K (T.field n) := T.finiteDimensional n
  have hTeq : T.field n = T₀.field n :=
    hT₀ n (T.field n) (T.unramified n) (T.finrank n)
  rw [hTeq, ← hUeq]
  exact hUle

/-- Conversely, containment of a tower level forces its degree to divide the residue-field
degree. -/
theorem UnramifiedTower.degree_dvd_residueFinrank_of_field_le_fieldRange
    [IsSepClosure K Ksep] (T : UnramifiedTower K Ksep)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (j : L →ₐ[K] Ksep) (n : ℕ)
    (hle : T.field n ≤ j.fieldRange) :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver
        (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    n + 1 ∣ Module.finrank (LocalResidueField K) (LocalResidueField L) := by
  let S : UnramifiedLevelSeed K Ksep (n + 1) :=
    (unramifiedLevelSeed_exists K Ksep (n + 1) (Nat.succ_pos n)).some
  let U := IntermediateField.adjoin K {S.root}
  letI : FiniteDimensional K U :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral S.root)
  obtain ⟨T₀, hT₀⟩ := unramifiedTower_lifting_classification K Ksep
  have hUeq : U = T₀.field n :=
    hT₀ n U (unramifiedLevelSeed_isUnramified K Ksep S)
      (unramifiedLevelSeed_finrank K Ksep S)
  letI : FiniteDimensional K (T.field n) := T.finiteDimensional n
  have hTeq : T.field n = T₀.field n :=
    hT₀ n (T.field n) (T.unramified n) (T.finrank n)
  apply unramifiedLevelSeed_residueFinrank_dvd_of_le_fieldRange K Ksep S L j
  change U ≤ j.fieldRange
  rw [hUeq, ← hTeq]
  exact hle

/--
**A05**, Lemma `lem:unramified-tower`: existence of a compatible unramified tower, unique at the
level of its intermediate fields in the fixed separable closure.  Arithmetic Frobenius is pinned
on residue fields and along divisibility inclusions; the tower also carries compositum local-field
transport and the gcd formula for intersections.
-/
theorem unramifiedTower_existsUnique [IsSepClosure K Ksep] :
    ∃ T : UnramifiedTower K Ksep,
      ∀ T' : UnramifiedTower K Ksep, ∀ n, T'.field n = T.field n := by
  obtain ⟨T, hT⟩ := unramifiedTower_lifting_classification K Ksep
  refine ⟨T, fun T' n => ?_⟩
  letI : FiniteDimensional K (T'.field n) := T'.finiteDimensional n
  exact hT n (T'.field n) (T'.unramified n) (T'.finrank n)

/-- The chosen unramified tower in the fixed separable closure. -/
noncomputable def unramifiedTower [IsSepClosure K Ksep] : UnramifiedTower K Ksep :=
  (unramifiedTower_existsUnique K Ksep).choose

end UnramifiedTower

section RectangularSubgroups

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The subgroup `π^(aℤ) U_K^b`. -/
def rectangularSubgroup (π : Uniformizer K) (a b : ℕ) : Subgroup (Units K) :=
  Subgroup.zpowers (π.val ^ a) ⊔ principalUnitSubgroup K b

/-- The subgroup `π^(aℤ) 𝒪_Kˣ`, used for unramified norm groups. -/
def unramifiedRectangularSubgroup (π : Uniformizer K) (a : ℕ) : Subgroup (Units K) :=
  Subgroup.zpowers (π.val ^ a) ⊔ unitSubgroup K

/-- An open finite-index subgroup, with topology and algebraic finite index stored separately. -/
structure OpenFiniteIndexSubgroup (G : Type v) [Group G] [TopologicalSpace G]
    extends OpenSubgroup G where
  /-- The underlying subgroup has finite index. -/
  finiteIndex' : toSubgroup.FiniteIndex

instance {G : Type v} [Group G] [TopologicalSpace G]
    (H : OpenFiniteIndexSubgroup G) : H.toSubgroup.FiniteIndex := H.finiteIndex'

end RectangularSubgroups

end

end NU.LCFT
