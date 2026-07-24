import Submission.NU.LCFT.Basic.LocalField

/-!
# Norms of local-field extensions

The algebraic norm is restricted to unit groups and bundled as a continuous monoid homomorphism.
The algebraic subgroup `normSubgroup` is literally its range; openness is deliberately a separate
theorem proved only after finite reciprocity.
-/

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel

universe u v w

section NormMap

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The field norm on multiplicative groups. -/
def normUnitsHom : Units L →* Units K :=
  Units.map (Algebra.norm K)

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ContinuousSMul K L]

/-- **A02**, Lemma `lem:norm-valuation`: the field norm is continuous on multiplicative groups. -/
theorem continuous_normUnitsHom : Continuous (normUnitsHom K L) := by
  classical
  apply Units.continuous_map
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := IsTopologicalAddGroup.rightUniformSpace L
  letI := isUniformAddGroup_of_addCommGroup (G := L)
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let hnorm : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  let b := Module.Free.chooseBasis K L
  let coord (i) : L →ₗ[K] K :=
    { toFun := fun x => b.repr x i
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hcoord (i) : Continuous (fun x : L => b.repr x i) := by
    exact LinearMap.continuous_of_finiteDimensional
      (𝕜 := K) (hnorm := hnorm) (coord i)
  have hmatrix : Continuous (fun x : L => fun i j => b.repr (x * b j) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (hcoord i).comp (continuous_id.mul continuous_const)
  rw [show (Algebra.norm K : L → K) =
      fun x => Matrix.det (fun i j => b.repr (x * b j) i) from by
    funext x
    rw [Algebra.norm_eq_matrix_det b, Algebra.leftMulMatrix_apply]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl]
  exact hmatrix.matrix_det

/-- The field norm bundled as a continuous homomorphism. -/
def normUnitsContinuousHom : Units L →ₜ* Units K :=
  { normUnitsHom K L with
    continuous_toFun := continuous_normUnitsHom K L }

/-- The algebraic norm subgroup, definitionally the range of the field norm. -/
def normSubgroup : Subgroup (Units K) :=
  (normUnitsHom K L).range

omit [FiniteDimensional K L] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ContinuousSMul K L] in
/-- Membership in the norm subgroup is existence of a field-unit norm preimage. -/
theorem mem_normSubgroup_iff (x : Units K) :
    x ∈ normSubgroup K L ↔ ∃ y : Units L, normUnitsHom K L y = x := by
  rfl

end NormMap

section NormAlgebra

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/--
**A02**, Lemma `lem:norm-valuation`: for a finite Galois extension, `Algebra.norm` agrees with
the product over all Galois automorphisms.
-/
theorem algebraNorm_eq_galoisProduct [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : (L ≃ₐ[K] L), σ x := by
  exact Algebra.norm_eq_prod_automorphisms K x

/-- The unit-group norm agrees with the product over Galois automorphisms. -/
theorem normUnitsHom_eq_galoisProduct [IsGalois K L] (x : Units L) :
    algebraMap K L ((normUnitsHom K L x : Units K) : K) =
      ∏ σ : (L ≃ₐ[K] L), σ (x : L) := by
  exact algebraNorm_eq_galoisProduct K L (x : L)

variable (M : Type w) [Field M] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [FiniteDimensional L M]

/-- The norm in a finite tower is the composite of the two norms. -/
theorem normUnitsHom_tower (x : Units M) :
    normUnitsHom K M x = normUnitsHom K L (normUnitsHom L M x) := by
  apply Units.ext
  exact (Algebra.norm_norm (R := K) (S := L)).symm

end NormAlgebra

section NormValuation

open ValuativeRel

private theorem normalizedValuation_inv_aux_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem normalizedValuation_zpow_aux_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) (n : ℤ) :
    normalizedValuation K (x ^ n) = n * normalizedValuation K x := by
  simp [normalizedValuation]

private theorem normalizedValuation_le_iff_norm
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
  rw [normalizedValuation_mul, normalizedValuation_inv_aux_norm] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation K y - normalizedValuation K x ↔
      valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change valuation K (y : K) / valuation K (x : K) ≤ 1 ↔ _
  rw [div_le_one₀ ((valuation K).pos_iff.mpr x.ne_zero)]

private theorem normalizedValuation_lt_iff_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    normalizedValuation K x < normalizedValuation K y ↔
      valuation K (y : K) < valuation K (x : K) := by
  simpa only [not_le] using (normalizedValuation_le_iff_norm K y x).not

private theorem continuous_algebraMap_of_valuativeExtension_norm
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] : Continuous (algebraMap K L) := by
  have he : 0 < ramificationIndex K L := by
    dsimp [ramificationIndex]
    exact (ramificationInvariants_exists K L).choose_spec.choose_spec.1
  have hscale := normalizedValuation_algebraMap K L
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
    apply (normalizedValuation_lt_iff_norm K (π ^ N) xu).2
    simpa [xu, γK] using hx
  have hπN : normalizedValuation K (π ^ N) = N := by
    rw [normalizedValuation_zpow_aux_norm]
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
    have he1 : 1 ≤ (ramificationIndex K L : ℤ) := by omega
    nlinarith
  have hlt : valuation L ((Units.map (algebraMap K L) xu : Units L) : L) <
      valuation L (y : L) :=
    (normalizedValuation_lt_iff_norm L y (Units.map (algebraMap K L) xu)).1 hteN
  simpa [xu, y, ha] using hlt

private theorem ringOfIntegers_module_finite_norm
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
      (((continuous_algebraMap_of_valuativeExtension_norm K L).comp continuous_fst).mul
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

private theorem isUnit_of_normalizedValuation_eq_zero_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (a : 𝒪[K]) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [normalizedValuation_inv_aux_norm, hval, neg_zero]
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

private theorem integral_normalizedUniformizer_norm
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
      rw [normalizedValuation_inv_aux_norm] at hinvnonneg
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
    · exact Or.inl (isUnit_of_normalizedValuation_eq_zero_norm K a ha0 ha)
    · exact Or.inr (isUnit_of_normalizedValuation_eq_zero_norm K b hb0 hb)

private theorem normalizedValuation_ringUnit_norm
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
  rw [normalizedValuation_inv_aux_norm] at hinvnonneg
  omega

private theorem integralUnit_of_normalizedValuation_eq_zero_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K)
    (hx : normalizedValuation K x = 0) :
    ∃ u : Units 𝒪[K], Units.map (algebraMap 𝒪[K] K) u = x := by
  obtain ⟨a, ha⟩ := (exists_normalizedValuationHom K).choose_spec.2 x |>.1 hx.ge
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [normalizedValuation_inv_aux_norm, hx, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units 𝒪[K] :=
    { val := a
      inv := b
      val_inv := by apply Subtype.ext; dsimp; rw [ha, hb]; simp
      inv_val := by apply Subtype.ext; dsimp; rw [ha, hb]; simp }
  refine ⟨u, ?_⟩
  apply Units.ext
  exact ha

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

/--
**A02**, Lemma `lem:norm-valuation` (Valuation of a norm):
`v_K(N_{L/K} x) = f(L/K) v_L(x)`.
-/
theorem normalizedValuation_norm (x : Units L) :
    normalizedValuation K (normUnitsHom K L x) =
      (residueDegree K L : ℤ) * normalizedValuation L x := by
  letI : (valuation K).HasExtension (valuation L) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  letI : Module.Finite 𝒪[K] 𝒪[L] := ringOfIntegers_module_finite_norm K L
  let e := ramificationIndex K L
  let f := residueDegree K L
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer_norm K
  obtain ⟨ϖL, hϖL, hϖLirr⟩ := integral_normalizedUniformizer_norm L
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let P : Ideal 𝒪[L] := IsLocalRing.maximalIdeal 𝒪[L]
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖL} := hϖLirr.maximalIdeal_eq
  let mϖ : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : 𝒪[L] => (z : L)) h
    have hz : algebraMap K L (ϖK : K) = 0 := by simpa [mϖ] using h'
    apply hϖKirr.ne_zero
    apply Subtype.ext
    exact (algebraMap K L).injective (by simpa using hz)
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
  have hn : n = e := by
    have hval := congr_arg (normalizedValuation L) hfacUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit_norm] at hval
    have hpow : normalizedValuation L ((defaultUniformizer L).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom L ((defaultUniformizer L).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation L (defaultUniformizer L).val = _
      rw [(defaultUniformizer L).valuation_eq_one, mul_one]
    rw [hpow, normalizedValuation_algebraMap,
      (defaultUniformizer K).valuation_eq_one, mul_one] at hval
    have hne : (n : ℤ) = (e : ℤ) := by simpa [e] using hval.symm
    exact_mod_cast hne
  have hmap : Ideal.map (algebraMap 𝒪[K] 𝒪[L]) p = P ^ e := by
    rw [hp, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {mϖ} = P ^ e
    rw [hfac, Ideal.span_singleton_mul_left_unit u.isUnit, hn, hP,
      Ideal.span_singleton_pow]
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime P p
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing 𝒪[L])
  have hfrac : Module.finrank (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) =
      Module.finrank K L := by
    rw [Algebra.IsAlgebraic.finrank_of_isFractionRing 𝒪[K] (FractionRing 𝒪[K]) 𝒪[L]
      (FractionRing 𝒪[L]),
      Algebra.IsAlgebraic.finrank_of_isFractionRing 𝒪[K] K 𝒪[L] L]
  have hrn := Ideal.relNorm_algebraMap (R := 𝒪[K]) 𝒪[L] p
  rw [hmap, map_pow, hs, ← pow_mul, hfrac] at hrn
  have hp0 : p ≠ ⊥ := by
    rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
    exact hϖKirr.ne_zero
  have hp1 : p ≠ 1 := by
    rw [Ideal.one_eq_top]
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
  have hse : s * e = Module.finrank K L :=
    (IsMulTorsionFree.pow_right_inj₀ hp1 hp0).mp hrn
  have hdegree := finrank_eq_ramificationIndex_mul_residueDegree K L
  have hsf : s = f := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < e by
      dsimp [e, ramificationIndex]
      exact (ramificationInvariants_exists K L).choose_spec.choose_spec.1)
    simpa [e, f, mul_comm] using hse.trans hdegree
  have hnormIdeal : Ideal.span {(Algebra.intNorm 𝒪[K] 𝒪[L]) ϖL} =
      Ideal.span {ϖK ^ f} := by
    rw [← Ideal.relNorm_singleton 𝒪[K] ϖL, ← hP, hs, hsf, hp,
      Ideal.span_singleton_pow]
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hnormIdeal
  let aK : 𝒪[K] := (Algebra.intNorm 𝒪[K] 𝒪[L]) ϖL
  have haK0 : (aK : K) ≠ 0 := by
    intro ha
    have hwK := congr_arg (fun z : 𝒪[K] => (z : K)) hw
    change (aK : K) * (((w : Units 𝒪[K]) : 𝒪[K]) : K) = (ϖK : K) ^ f at hwK
    rw [ha, zero_mul] at hwK
    have hϖK0 : (ϖK : K) ≠ 0 := fun h => hϖKirr.ne_zero (Subtype.ext h)
    exact (pow_ne_zero f hϖK0) hwK.symm
  let aKU : Units K := Units.mk0 (aK : K) haK0
  have haKUval : normalizedValuation K aKU = (f : ℤ) := by
    have hUnits : aKU * Units.map (algebraMap 𝒪[K] K) w =
        (defaultUniformizer K).val ^ f := by
      apply Units.ext
      change (aK : K) * (((w : Units 𝒪[K]) : 𝒪[K]) : K) =
        (((defaultUniformizer K).val : Units K) : K) ^ f
      have hwK := congr_arg (fun z : 𝒪[K] => (z : K)) hw
      change (aK : K) * (((w : Units 𝒪[K]) : 𝒪[K]) : K) = (ϖK : K) ^ f at hwK
      simpa [hϖK] using hwK
    have hv := congr_arg (normalizedValuation K) hUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit_norm] at hv
    have hpow : normalizedValuation K ((defaultUniformizer K).val ^ f) = (f : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom K ((defaultUniformizer K).val ^ f)) = _
      rw [map_pow, toAdd_pow]
      change (f : ℤ) * normalizedValuation K (defaultUniformizer K).val = _
      rw [(defaultUniformizer K).valuation_eq_one, mul_one]
    omega
  have haKnorm : (aK : K) = Algebra.norm K (ϖL : L) := by
    have hint :=
      Algebra.algebraMap_intNorm (A := 𝒪[K]) (K := K) (L := L) (B := 𝒪[L]) ϖL
    rw [show algebraMap 𝒪[K] K ((Algebra.intNorm 𝒪[K] 𝒪[L]) ϖL) =
        (((Algebra.intNorm 𝒪[K] 𝒪[L]) ϖL : 𝒪[K]) : K) from rfl,
      show algebraMap 𝒪[L] L ϖL = (ϖL : L) from rfl] at hint
    exact hint
  have hπnorm : normUnitsHom K L (defaultUniformizer L).val = aKU := by
    apply Units.ext
    exact (congr_arg (Algebra.norm K) hϖL).symm.trans haKnorm.symm
  have hnormπ : normalizedValuation K
      (normUnitsHom K L (defaultUniformizer L).val) = (f : ℤ) := by
    rw [hπnorm, haKUval]
  let m := normalizedValuation L x
  let z := x * (defaultUniformizer L).val ^ (-m)
  have hzval : normalizedValuation L z = 0 := by
    rw [normalizedValuation_mul, normalizedValuation_zpow_aux_norm]
    dsimp [m]
    rw [(defaultUniformizer L).valuation_eq_one]
    simp
  obtain ⟨uz, huz⟩ := integralUnit_of_normalizedValuation_eq_zero_norm L z hzval
  let intNz : Units 𝒪[K] := Units.map (Algebra.intNorm 𝒪[K] 𝒪[L]) uz
  have hnormz : normUnitsHom K L z = Units.map (algebraMap 𝒪[K] K) intNz := by
    apply Units.ext
    have hint :=
      Algebra.algebraMap_intNorm (A := 𝒪[K]) (K := K) (L := L) (B := 𝒪[L]) (uz : 𝒪[L])
    change Algebra.norm K (z : L) =
      algebraMap 𝒪[K] K ((Algebra.intNorm 𝒪[K] 𝒪[L]) (uz : 𝒪[L]))
    exact (congr_arg (Algebra.norm K) (congr_arg Units.val huz)).symm.trans hint.symm
  have hnormzval : normalizedValuation K (normUnitsHom K L z) = 0 := by
    rw [hnormz, normalizedValuation_ringUnit_norm]
  rw [show z = x * (defaultUniformizer L).val ^ (-m) from rfl,
    map_mul, map_zpow, normalizedValuation_mul,
    normalizedValuation_zpow_aux_norm, hnormπ] at hnormzval
  dsimp [m, f] at hnormzval ⊢
  linear_combination hnormzval

/-- The valuation image of the norm subgroup is `f(L/K)ℤ`. -/
theorem valuation_mem_normSubgroup_iff (z : ℤ) :
    (∃ x : normSubgroup K L, normalizedValuation K x = z) ↔
      ∃ m : ℤ, z = (residueDegree K L : ℤ) * m := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := x.prop
    refine ⟨normalizedValuation L y, ?_⟩
    rw [← hx, ← hy]
    exact normalizedValuation_norm K L y
  · rintro ⟨m, rfl⟩
    obtain ⟨y, hy⟩ := normalizedValuation_surjective L m
    refine ⟨⟨normUnitsHom K L y, ⟨y, rfl⟩⟩, ?_⟩
    rw [normalizedValuation_norm, hy]

end NormValuation

private theorem mem_unitSubgroup_iff_normalizedValuation_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) :
    x ∈ unitSubgroup K ↔ normalizedValuation K x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hnonneg : 0 ≤ normalizedValuation K (ringUnitsToFieldUnits K u) :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
    have hinvnonneg : 0 ≤ normalizedValuation K ((ringUnitsToFieldUnits K u)⁻¹) :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨↑u⁻¹, rfl⟩
    have hneg : normalizedValuation K ((ringUnitsToFieldUnits K u)⁻¹) =
        -normalizedValuation K (ringUnitsToFieldUnits K u) := by
      simp [normalizedValuation]
    omega
  · intro hx
    have hxi : 0 ≤ normalizedValuation K x := hx.ge
    have hxinv : normalizedValuation K x⁻¹ = 0 := by
      have h := normalizedValuation_mul K x x⁻¹
      have hzero : normalizedValuation K 1 = 0 := by simp [normalizedValuation]
      rw [mul_inv_cancel, hzero, hx, zero_add] at h
      exact h.symm
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom K).choose_spec.2 x |>.1 hxi
    obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
    let u : Units (RingOfIntegers K) :=
      { val := a
        inv := b
        val_inv := by apply Subtype.ext; dsimp; rw [ha, hb]; simp
        inv_val := by apply Subtype.ext; dsimp; rw [ha, hb]; simp }
    refine ⟨u, ?_⟩
    apply Units.ext
    exact ha

private theorem norm_mod_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [Module.Finite A B] [Module.Free A B] (x : B) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (Algebra.norm A x) =
      Algebra.norm (A ⧸ IsLocalRing.maximalIdeal A)
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) x) := by
  classical
  let b := Module.Free.chooseBasis A B
  rw [Algebra.norm_eq_matrix_det b,
    Algebra.norm_eq_matrix_det (IsLocalRing.basisQuotient b), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_apply,
    LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
    IsLocalRing.basisQuotient_apply]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (b.repr (x * b j) i) =
    (IsLocalRing.basisQuotient b).repr
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) (x * b j)) i
  rw [IsLocalRing.basisQuotient_repr]

private theorem trace_mod_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [Module.Finite A B] [Module.Free A B] (x : B) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (Algebra.trace A B x) =
      Algebra.trace (A ⧸ IsLocalRing.maximalIdeal A)
        (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) x) := by
  classical
  let b := Module.Free.chooseBasis A B
  rw [Algebra.trace_eq_matrix_trace b,
    Algebra.trace_eq_matrix_trace (IsLocalRing.basisQuotient b)]
  rw [Matrix.trace, Matrix.trace, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', IsLocalRing.basisQuotient_apply]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (b.repr (x * b i) i) =
    (IsLocalRing.basisQuotient b).repr
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) (x * b i)) i
  rw [IsLocalRing.basisQuotient_repr]

private theorem unramified_map_maximalIdeal_eq
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [IsUnramifiedLocalExtension K L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (IsLocalRing.maximalIdeal 𝒪[K]) =
      IsLocalRing.maximalIdeal 𝒪[L] := by
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer_norm K
  obtain ⟨ϖL, hϖL, hϖLirr⟩ := integral_normalizedUniformizer_norm L
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let P : Ideal 𝒪[L] := IsLocalRing.maximalIdeal 𝒪[L]
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖL} := hϖLirr.maximalIdeal_eq
  let mϖ : 𝒪[L] := algebraMap 𝒪[K] 𝒪[L] ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : 𝒪[L] => (z : L)) h
    have hz : algebraMap K L (ϖK : K) = 0 := by simpa [mϖ] using h'
    apply hϖKirr.ne_zero
    apply Subtype.ext
    exact (algebraMap K L).injective (by simpa using hz)
  obtain ⟨n, w, hfac⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmϖ0 hϖLirr
  let xw : Units L := Units.map (algebraMap 𝒪[L] L) w
  have hfacUnits : Units.map (algebraMap K L) (defaultUniformizer K).val =
      xw * (defaultUniformizer L).val ^ n := by
    apply Units.ext
    change algebraMap K L (((defaultUniformizer K).val : Units K) : K) =
      algebraMap 𝒪[L] L (w : 𝒪[L]) * (((defaultUniformizer L).val : Units L) : L) ^ n
    rw [show algebraMap 𝒪[L] L (w : 𝒪[L]) = (((w : Units 𝒪[L]) : 𝒪[L]) : L) from rfl,
      ← hϖK]
    simpa [mϖ, hϖL] using congr_arg (fun z : 𝒪[L] => (z : L)) hfac
  have hn : n = ramificationIndex K L := by
    have hval := congr_arg (normalizedValuation L) hfacUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit_norm] at hval
    have hpow : normalizedValuation L ((defaultUniformizer L).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom L ((defaultUniformizer L).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation L (defaultUniformizer L).val = _
      rw [(defaultUniformizer L).valuation_eq_one, mul_one]
    rw [hpow, normalizedValuation_algebraMap,
      (defaultUniformizer K).valuation_eq_one, mul_one] at hval
    have hne : (n : ℤ) = (ramificationIndex K L : ℤ) := by simpa using hval.symm
    exact_mod_cast hne
  change Ideal.map (algebraMap 𝒪[K] 𝒪[L]) p = P
  rw [hp, Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span {mϖ} = P
  rw [hfac, Ideal.span_singleton_mul_left_unit w.isUnit, hn,
    IsUnramifiedLocalExtension.ramificationIndex_eq_one, pow_one, hP]

private theorem hensel_norm_correction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [IsLocalRing A] [IsLocalRing B] [Module.Finite A B] [Module.Free A B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmap : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (d : Units A)
    (hd : Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toMonoidHom d = 1)
    (a : Units B) (ha : IsUnit (Algebra.trace A B (a : B))) :
    ∃ w : Units B, Units.map (Algebra.norm A) w = d := by
  classical
  let b := Module.Free.chooseBasis A B
  let M := Algebra.leftMulMatrix b (a : B)
  let c : Units A := Units.map (Algebra.norm A) a
  let g : Polynomial A := Matrix.det (1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C)
  let f : Polynomial A := Polynomial.C ((c⁻¹ : Units A) : A) *
    (g - Polynomial.C (d : A))
  have hcard : 0 < Fintype.card (Module.Free.ChooseBasisIndex A B) := Fintype.card_pos
  have hcoeff : g.coeff (Fintype.card (Module.Free.ChooseBasisIndex A B)) = (c : A) := by
    dsimp [g, c, M]
    rw [show 1 + (Polynomial.X : Polynomial A) •
          (Algebra.leftMulMatrix b (a : B)).map Polynomial.C =
        (Polynomial.X : Polynomial A) • (Algebra.leftMulMatrix b (a : B)).map Polynomial.C +
          (1 : Matrix _ _ A).map Polynomial.C by simp [add_comm],
      Polynomial.coeff_det_X_add_C_card, ← Algebra.norm_eq_matrix_det b]
  have hgdeg : g.natDegree = Fintype.card (Module.Free.ChooseBasisIndex A B) := by
    apply le_antisymm
    · change (Matrix.det (1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C)).natDegree ≤ _
      rw [show 1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C =
        (Polynomial.X : Polynomial A) • M.map Polynomial.C +
          (1 : Matrix _ _ A).map Polynomial.C by simp [add_comm]]
      exact Polynomial.natDegree_det_X_add_C_le M (1 : Matrix _ _ A)
    · exact Polynomial.le_natDegree_of_ne_zero (hcoeff.trans_ne c.ne_zero)
  have hsublead : (g - Polynomial.C (d : A)).leadingCoeff = (c : A) := by
    rw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C, hgdeg,
      Polynomial.coeff_sub, hcoeff, Polynomial.coeff_C]
    simp [hcard.ne']
  have hfmonic : f.Monic := by
    rw [Polynomial.Monic.def]
    simp only [f, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hsublead]
    exact c.inv_val
  have hfzero : f.eval 0 ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hdval := congr_arg Units.val hd
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (d : A) = 1 at hdval
    simp only [f, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    have hgzero : g.eval 0 = 1 := by
      change Polynomial.evalRingHom 0
        (Matrix.det (1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C)) = 1
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      have hone : Matrix.det (1 : Matrix (Module.Free.ChooseBasisIndex A B)
          (Module.Free.ChooseBasisIndex A B) A) = 1 := Matrix.det_one
      rw [← hone]
      apply congrArg (fun N : Matrix (Module.Free.ChooseBasisIndex A B)
        (Module.Free.ChooseBasisIndex A B) A => Matrix.det N)
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hgzero, map_mul, map_sub, map_one, hdval]
    simp
  have hfderiv : f.derivative.eval 0 =
      ((c⁻¹ : Units A) : A) * Algebra.trace A B (a : B) := by
    simp only [f, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_sub, sub_zero, Polynomial.eval_mul, Polynomial.eval_C]
    rw [show g.derivative.eval 0 = M.trace from Matrix.derivative_det_one_add_X_smul M,
      Algebra.trace_eq_matrix_trace b]
  have hfderivunit : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (f.derivative.eval 0)) := by
    rw [hfderiv]
    exact (c⁻¹).isUnit.mul ha |>.map _
  obtain ⟨t, htroot, ht⟩ := HenselianRing.is_henselian f hfmonic 0 hfzero hfderivunit
  have htmem : t ∈ IsLocalRing.maximalIdeal A := by simpa using ht
  let y : B := 1 + algebraMap A B t * (a : B)
  have hymem : algebraMap A B t * (a : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [← hmap]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (algebraMap A B) htmem)
  have hyunit : IsUnit y := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hy
    have hone := (IsLocalRing.maximalIdeal B).sub_mem hy hymem
    simpa [y] using hone
  have hgeval (s : A) :
      g.eval s = Algebra.norm A (1 + algebraMap A B s * (a : B)) := by
    rw [Algebra.norm_eq_matrix_det b]
    change Polynomial.evalRingHom s
      (Matrix.det (1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C)) =
        Matrix.det (Algebra.leftMulMatrix b (1 + algebraMap A B s * (a : B)))
    rw [RingHom.map_det]
    have hmapmat :
        (Polynomial.evalRingHom s).mapMatrix
            (1 + (Polynomial.X : Polynomial A) • M.map Polynomial.C) = 1 + s • M := by
      rw [RingHom.mapMatrix_apply]
      ext i j
      by_cases hij : i = j <;> simp [hij] <;> ring
    rw [hmapmat]
    apply congrArg (fun N : Matrix (Module.Free.ChooseBasisIndex A B)
      (Module.Free.ChooseBasisIndex A B) A => Matrix.det N)
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, M, Algebra.leftMulMatrix_apply,
      LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [add_mul, one_mul, map_add]
    simp only [smul_eq_mul, Finsupp.add_apply]
    rw [mul_assoc, ← Algebra.smul_def]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hgtd : g.eval t = (d : A) := by
    change f.eval t = 0 at htroot
    simp only [f, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub] at htroot
    have hc0 : ((c⁻¹ : Units A) : A) ≠ 0 := (c⁻¹).ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp htroot).resolve_left hc0)
  have hnormy : Algebra.norm A y = (d : A) := (hgeval t).symm.trans hgtd
  let w : Units B := hyunit.unit
  have hw : (w : B) = y := hyunit.unit_spec
  refine ⟨w, ?_⟩
  apply Units.ext
  change Algebra.norm A (w : B) = (d : A)
  rw [hw, hnormy]

section UnramifiedNorm

variable (K : Type u) (L : Type v)
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [IsUnramifiedLocalExtension K L]

private theorem unramified_norm_lifts_integral_units :
    ∀ u : Units (RingOfIntegers K), ∃ v : Units (RingOfIntegers L),
      normUnitsHom K L (ringUnitsToFieldUnits L v) = ringUnitsToFieldUnits K u := by
  intro u
  classical
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  letI : Module.Finite 𝒪[K] 𝒪[L] := ringOfIntegers_module_finite_norm K L
  letI : Module.Free 𝒪[K] 𝒪[L] := Module.free_of_finite_type_torsion_free'
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  let p : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]
  let q : Ideal 𝒪[L] := Ideal.map (algebraMap 𝒪[K] 𝒪[L]) p
  let P : Ideal 𝒪[L] := IsLocalRing.maximalIdeal 𝒪[L]
  have hqP : q = P := unramified_map_maximalIdeal_eq K L
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal 𝒪[K]
  letI : q.IsMaximal := hqP ▸ IsLocalRing.maximalIdeal.isMaximal 𝒪[L]
  letI : Field (𝒪[K] ⧸ p) := Ideal.Quotient.field p
  letI : Field (𝒪[L] ⧸ q) := Ideal.Quotient.field q
  letI : Finite (𝒪[L] ⧸ P) := by
    dsimp [P]
    change Finite (LocalResidueField L)
    infer_instance
  letI : Finite (𝒪[L] ⧸ q) := hqP ▸ (inferInstance : Finite (𝒪[L] ⧸ P))
  let ubar : Units (𝒪[K] ⧸ p) := Units.map (Ideal.Quotient.mk p).toMonoidHom u
  obtain ⟨zbar, hzbar⟩ :=
    FiniteField.unitsMap_norm_surjective (𝒪[K] ⧸ p) (𝒪[L] ⧸ q) ubar
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (zbar : 𝒪[L] ⧸ q)
  have hznotq : z ∉ q := by
    intro h
    have hz0 : Ideal.Quotient.mk q z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [hz] at hz0
    exact zbar.ne_zero hz0
  have hznotP : z ∉ P := by simpa [hqP] using hznotq
  have hzunit : IsUnit z := IsLocalRing.notMem_maximalIdeal.mp hznotP
  let zU : Units 𝒪[L] := hzunit.unit
  have hzU : (zU : 𝒪[L]) = z := hzunit.unit_spec
  have hnormmod : Ideal.Quotient.mk p (Algebra.norm 𝒪[K] z) =
      Ideal.Quotient.mk p (u : 𝒪[K]) := by
    calc
      _ = Algebra.norm (𝒪[K] ⧸ p) (Ideal.Quotient.mk q z) := by
        simpa [p, q] using norm_mod_maximalIdeal z
      _ = Algebra.norm (𝒪[K] ⧸ p) (zbar : 𝒪[L] ⧸ q) := by rw [hz]
      _ = (ubar : 𝒪[K] ⧸ p) := congr_arg Units.val hzbar
      _ = Ideal.Quotient.mk p (u : 𝒪[K]) := rfl
  let nz : Units 𝒪[K] := Units.map (Algebra.norm 𝒪[K]) zU
  have hnormmodU : Ideal.Quotient.mk p (nz : 𝒪[K]) =
      Ideal.Quotient.mk p (u : 𝒪[K]) := by
    change Ideal.Quotient.mk p (Algebra.norm 𝒪[K] (zU : 𝒪[L])) = _
    rw [hzU]
    exact hnormmod
  let d : Units 𝒪[K] := u / nz
  have hd : Units.map (Ideal.Quotient.mk p).toMonoidHom d = 1 := by
    change Units.map (Ideal.Quotient.mk p).toMonoidHom (u / nz) = 1
    rw [map_div]
    have hmaps : Units.map (Ideal.Quotient.mk p).toMonoidHom nz =
        Units.map (Ideal.Quotient.mk p).toMonoidHom u := by
      apply Units.ext
      exact hnormmodU
    rw [hmaps]
    simp
  obtain ⟨abar, habar⟩ :=
    Algebra.trace_surjective (𝒪[K] ⧸ p) (𝒪[L] ⧸ q) (1 : 𝒪[K] ⧸ p)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective abar
  have htrace : Ideal.Quotient.mk p (Algebra.trace 𝒪[K] 𝒪[L] a) = 1 := by
    calc
      _ = Algebra.trace (𝒪[K] ⧸ p) (𝒪[L] ⧸ q) (Ideal.Quotient.mk q a) := by
        simpa [p, q] using trace_mod_maximalIdeal a
      _ = Algebra.trace (𝒪[K] ⧸ p) (𝒪[L] ⧸ q) abar := by rw [ha]
      _ = 1 := habar
  have hanotq : a ∉ q := by
    intro h
    have ha0 : Ideal.Quotient.mk q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [ha] at ha0
    have htr0 := congr_arg (Algebra.trace (𝒪[K] ⧸ p) (𝒪[L] ⧸ q)) ha0
    rw [habar, map_zero] at htr0
    exact one_ne_zero htr0
  have hanotP : a ∉ P := by simpa [hqP] using hanotq
  have haunit : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp hanotP
  let aU : Units 𝒪[L] := haunit.unit
  have haU : (aU : 𝒪[L]) = a := haunit.unit_spec
  have htraceunit : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] (aU : 𝒪[L])) := by
    rw [haU, ← IsLocalRing.notMem_maximalIdeal]
    intro h
    have hzero : Ideal.Quotient.mk p (Algebra.trace 𝒪[K] 𝒪[L] a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [htrace] at hzero
    exact one_ne_zero hzero
  obtain ⟨wU, hwU⟩ := hensel_norm_correction hqP d hd aU htraceunit
  let v : Units 𝒪[L] := zU * wU
  have hvnorm : Units.map (Algebra.norm 𝒪[K]) v = u := by
    rw [show v = zU * wU from rfl, map_mul, hwU]
    simp [d, nz]
  refine ⟨v, ?_⟩
  apply Units.ext
  have hint := Algebra.algebraMap_intNorm
    (A := 𝒪[K]) (K := K) (L := L) (B := 𝒪[L]) (v : 𝒪[L])
  rw [Algebra.intNorm_eq_norm,
    show algebraMap 𝒪[L] L (v : 𝒪[L]) = (((v : Units 𝒪[L]) : 𝒪[L]) : L) from rfl] at hint
  have hvnorm' := congr_arg Units.val hvnorm
  change Algebra.norm 𝒪[K] (v : 𝒪[L]) = (u : 𝒪[K]) at hvnorm'
  change Algebra.norm K (((v : Units 𝒪[L]) : 𝒪[L]) : L) =
    algebraMap 𝒪[K] K (u : 𝒪[K])
  rw [← hint, hvnorm']

/--
**A06**, Lemma `lem:unramified-norm`: the norm from an unramified extension is onto on integral
units.  This statement includes the convergence of the successive trace corrections.
-/
theorem unramified_norm_surjective_on_units :
    ∀ x : unitSubgroup K, ∃ y : unitSubgroup L,
      normUnitsHom K L y = x := by
  rintro ⟨x, u, rfl⟩
  obtain ⟨v, hv⟩ := unramified_norm_lifts_integral_units K L u
  exact ⟨⟨ringUnitsToFieldUnits L v, ⟨v, rfl⟩⟩, hv⟩

/--
**A06**, Lemma `lem:unramified-norm`: the full unramified norm group is
`π^[L:K]ℤ 𝒪_Kˣ`.
-/
theorem normSubgroup_eq_unramifiedRectangular (π : Uniformizer K) :
    normSubgroup K L =
      unramifiedRectangularSubgroup K π (Module.finrank K L) := by
  have hunit : ∀ x : Units K,
      x ∈ unitSubgroup K ↔ normalizedValuation K x = 0 :=
    mem_unitSubgroup_iff_normalizedValuation_eq_zero K
  have hdegree : residueDegree K L = Module.finrank K L := by
    have h := finrank_eq_ramificationIndex_mul_residueDegree K L
    rw [IsUnramifiedLocalExtension.ramificationIndex_eq_one, one_mul] at h
    exact h.symm
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let a : Units K := (π.val ^ Module.finrank K L) ^ normalizedValuation L y
    let u : Units K := a⁻¹ * normUnitsHom K L y
    have ha : a ∈ Subgroup.zpowers (π.val ^ Module.finrank K L) :=
      Subgroup.mem_zpowers_iff.mpr ⟨normalizedValuation L y, rfl⟩
    have hvbase : normalizedValuation K (π.val ^ Module.finrank K L) =
        Module.finrank K L := by
      change Multiplicative.toAdd
        (normalizedValuationHom K (π.val ^ Module.finrank K L)) = _
      rw [map_pow, toAdd_pow]
      change (Module.finrank K L : ℤ) * normalizedValuation K π.val = _
      rw [π.valuation_eq_one, mul_one]
    have hva : normalizedValuation K a =
        (Module.finrank K L : ℤ) * normalizedValuation L y := by
      change Multiplicative.toAdd (normalizedValuationHom K
        ((π.val ^ Module.finrank K L) ^ normalizedValuation L y)) = _
      rw [map_zpow, toAdd_zpow, zsmul_eq_mul]
      change normalizedValuation L y *
        normalizedValuation K (π.val ^ Module.finrank K L) = _
      rw [hvbase, mul_comm]
    have hvainv : normalizedValuation K a⁻¹ = -normalizedValuation K a := by
      simp [normalizedValuation]
    have hvu : normalizedValuation K u = 0 := by
      rw [normalizedValuation_mul, normalizedValuation_norm, hdegree, hvainv, hva]
      simp
    have hu : u ∈ unitSubgroup K := (hunit u).2 hvu
    have hau := Subgroup.mul_mem_sup ha hu
    have heq : a * u = normUnitsHom K L y := by simp [u]
    exact heq ▸ hau
  · unfold unramifiedRectangularSubgroup
    rw [Subgroup.mem_sup]
    rintro ⟨a, ha, u, hu, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hπnorm : π.val ^ Module.finrank K L ∈ normSubgroup K L := by
      refine ⟨Units.map (algebraMap K L) π.val, ?_⟩
      change normUnitsHom K L (Units.map (algebraMap K L) π.val) = _
      apply Units.ext
      change Algebra.norm K (algebraMap K L (π.val : K)) =
        ((π.val ^ Module.finrank K L : Units K) : K)
      rw [Algebra.norm_algebraMap]
      rfl
    have hpow : (π.val ^ Module.finrank K L) ^ m ∈ normSubgroup K L :=
      (normSubgroup K L).zpow_mem hπnorm m
    obtain ⟨y, hy⟩ := unramified_norm_surjective_on_units K L ⟨u, hu⟩
    exact (normSubgroup K L).mul_mem hpow ⟨y, hy⟩

end UnramifiedNorm

end

end NU.LCFT
