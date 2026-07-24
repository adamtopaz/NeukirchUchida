import Submission.NU.LCFT.FundamentalClass.Approximation

/-!
# A cohomologically trivial open subgroup of local units

This file follows the normal-basis construction in `lem:deep-acyclic-units`.  In particular, the
lattice package below does not merely name two additive subgroups: it records the normal-basis
generator, denominator clearing, the regular `𝒪_K[G]` coordinates of both lattices, and the exact
relation `B = π_K^(N+1) A`.  The multiplicative package then records the literal filtration
`V_i = 1 + π_K^i B`, its inverse-limit completeness, its intersection, and equivariant regular
residue coordinates on every graded quotient.
-/

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel

/-- **F02–F03**, Lemma `lem:deep-acyclic-units`: left translation on the regular module. -/
def regularFinsuppTranslate {G A : Type} [Group G] [AddCommGroup A] (g : G) :
    (G →₀ A) →+ (G →₀ A) :=
  (Finsupp.domCongr (Equiv.mulLeft g)).toAddMonoidHom

/--
**F03**, Lemma `lem:deep-acyclic-units`: the actual subrepresentation of `MulRep K L` carried
by a Galois-stable subgroup of `Lˣ`.
Using this definition in the conclusion prevents replacing the deep units by an unrelated
representation with vanishing cohomology.
-/
def stableUnitSubgroupRep (K L : Type) [Field K] [Field L] [Algebra K L]
    (V : Subgroup (Units L))
    (stable : ∀ (σ : L ≃ₐ[K] L) x, x ∈ V →
      Units.map σ.toRingEquiv.toRingHom x ∈ V) : Rep ℤ (L ≃ₐ[K] L) :=
  (MulRep K L).subrepresentation V.toAddSubgroup.toIntSubmodule (by
    intro σ x hx
    change Additive.toMul ((MulRep K L).ρ σ x) ∈ V
    change Units.map σ.toRingEquiv.toRingHom (Additive.toMul x) ∈ V
    exact stable σ (Additive.toMul x) hx)

/-- **F03**, Lemma `lem:deep-acyclic-units`: the additive quotient `V_i/V_{i+1}`. -/
abbrev DeepUnitGradedQuotient {L : Type} [Field L]
    (V : ℕ → Subgroup (Units L)) (i : ℕ) :=
  Additive (V i ⧸ (V (i + 1)).comap (V i).subtype)

private theorem normalizedValuation_inv_deep
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem normalizedValuation_le_iff_deep
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    normalizedValuation K x ≤ normalizedValuation K y ↔
      ValuativeRel.valuation K (y : K) ≤ ValuativeRel.valuation K (x : K) := by
  have hnonneg : 0 ≤ normalizedValuation K (y * x⁻¹) ↔
      ValuativeRel.valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 := by
    unfold normalizedValuation normalizedValuationHom
    rw [(exists_normalizedValuationHom K).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  rw [normalizedValuation_mul, normalizedValuation_inv_deep] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation K y - normalizedValuation K x ↔
      ValuativeRel.valuation K ((y * x⁻¹ : Units K) : K) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change ValuativeRel.valuation K (y : K) / ValuativeRel.valuation K (x : K) ≤ 1 ↔ _
  rw [div_le_one₀ ((ValuativeRel.valuation K).pos_iff.mpr x.ne_zero)]

private theorem normalizedValuation_lt_iff_deep
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Units K) :
    normalizedValuation K x < normalizedValuation K y ↔
      ValuativeRel.valuation K (y : K) < ValuativeRel.valuation K (x : K) := by
  simpa only [not_le] using (normalizedValuation_le_iff_deep K y x).not

private theorem normalizedValuation_algEquiv_deep
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
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

private theorem isUnit_of_normalizedValuation_eq_zero_deep
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (a : RingOfIntegers K) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [normalizedValuation_inv_deep, hval, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers K) :=
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

private theorem integral_uniformizer_deep
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K) :
    ∃ ϖ : RingOfIntegers K, (ϖ : K) = (π.val : K) ∧ Irreducible ϖ := by
  have hπnonneg : 0 ≤ normalizedValuation K π.val := by rw [π.valuation_eq_one]; omega
  obtain ⟨ϖ, hϖ⟩ := (exists_normalizedValuationHom K).choose_spec.2 π.val |>.1 hπnonneg
  refine ⟨ϖ, hϖ, (irreducible_iff.mpr ⟨?_, ?_⟩)⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation K
        (Units.map (algebraMap (RingOfIntegers K) K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
      rw [normalizedValuation_inv_deep] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers K) K) u = π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
      rw [hu, hϖ]
    rw [heq, π.valuation_eq_one] at huval
    omega
  · intro a b hab
    have ha0 : (a : K) ≠ 0 := by
      intro ha
      have : (ϖ : K) = 0 := by rw [hab]; simp [ha]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    have hb0 : (b : K) ≠ 0 := by
      intro hb
      have : (ϖ : K) = 0 := by rw [hab]; simp [hb]
      apply π.val.ne_zero
      rw [← hϖ]
      exact this
    let ua : Units K := Units.mk0 (a : K) ha0
    let ub : Units K := Units.mk0 (b : K) hb0
    have hva : 0 ≤ normalizedValuation K ua :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨a, rfl⟩
    have hvb : 0 ≤ normalizedValuation K ub :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨b, rfl⟩
    have huv : ua * ub = π.val := by
      apply Units.ext
      simpa [ua, ub, ← hϖ] using congr_arg Subtype.val hab.symm
    have hvsum : normalizedValuation K ua + normalizedValuation K ub = 1 := by
      rw [← normalizedValuation_mul, huv, π.valuation_eq_one]
    rcases (show normalizedValuation K ua = 0 ∨ normalizedValuation K ub = 0 by omega) with ha | hb
    · exact Or.inl (isUnit_of_normalizedValuation_eq_zero_deep K a ha0 ha)
    · exact Or.inr (isUnit_of_normalizedValuation_eq_zero_deep K b hb0 hb)

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

/--
**F02**, Lemma `lem:deep-acyclic-units`: the two integral regular lattices in its proof.

`A` is freely generated over `𝒪_K` by the orbit of the denominator-cleared normal-basis element.
The deeper lattice is *definitionally specified by membership* as
`B = π_K^(N+1) A`; it is also supplied with its own pinned regular coordinates.  Thus neither
`A` nor `B` can be replaced by the zero lattice.
-/
structure DeepUnitLatticeData (π : Uniformizer K) where
  /-- A normal-basis generator before denominators are cleared. -/
  rawGenerator : L
  /-- Its normal basis. -/
  rawNormalBasis : Module.Basis (L ≃ₐ[K] L) K L
  /-- The basis is the Galois orbit of `rawGenerator`. -/
  rawNormalBasis_eq_orbit : ∀ σ, rawNormalBasis σ = σ rawGenerator
  /-- Power of the base uniformizer used to clear denominators. -/
  denominatorExponent : ℕ
  /-- The integral, denominator-cleared normal-basis generator. -/
  generator : L
  /-- Defining equation for the cleared generator. -/
  generator_eq_cleared :
    generator = algebraMap K L ((π.val : K) ^ denominatorExponent) * rawGenerator
  /-- The cleared generator is integral. -/
  generator_integral : ∃ a : RingOfIntegers L, (a : L) = generator
  /-- The scaled orbit is still a `K`-basis. -/
  normalBasis : Module.Basis (L ≃ₐ[K] L) K L
  /-- The scaled normal basis is exactly the orbit of `generator`. -/
  normalBasis_eq_orbit : ∀ σ, normalBasis σ = σ generator
  /-- The integral normal-basis lattice `A`. -/
  A : Submodule (RingOfIntegers K) L
  /-- Pinned free rank-one `𝒪_K[G]` coordinates on `A`. -/
  A_regularEquiv :
    ((L ≃ₐ[K] L) →₀ RingOfIntegers K) ≃ₗ[RingOfIntegers K] A
  /-- A basis vector is sent to the corresponding Galois conjugate. -/
  A_regularEquiv_single : ∀ (σ : L ≃ₐ[K] L) (c : RingOfIntegers K),
    ((A_regularEquiv (Finsupp.single σ c) : A) : L) =
      algebraMap K L (c : K) * σ generator
  /-- The coordinate equivalence intertwines left translation and Galois action. -/
  A_regularEquiv_equivariant : ∀ (τ : L ≃ₐ[K] L)
      (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K),
    ((A_regularEquiv (regularFinsuppTranslate τ c) : A) : L) =
      τ ((A_regularEquiv c : A) : L)
  /-- Galois stability of `A`. -/
  A_stable : ∀ (σ : L ≃ₐ[K] L) x, x ∈ A → σ x ∈ A
  /-- `A` consists of integral elements. -/
  A_integral : ∀ x, x ∈ A → ∃ a : RingOfIntegers L, (a : L) = x
  /-- `A` is compact. -/
  A_compact : IsCompact (A : Set L)
  /-- `A` is open. -/
  A_open : IsOpen (A : Set L)
  /-- Exponent with `π_K^N 𝒪_L ⊆ A`. -/
  integralContainmentExponent : ℕ
  /-- The denominator-clearing containment `π_K^N 𝒪_L ⊆ A`. -/
  pi_pow_integral_le_A : ∀ x : RingOfIntegers L,
    algebraMap K L ((π.val : K) ^ integralContainmentExponent) * (x : L) ∈ A
  /-- The deeper normal-basis lattice `B`. -/
  B : Submodule (RingOfIntegers K) L
  /-- Defining equation `B = π_K^(N+1) A`, stated without a hidden coercion map. -/
  mem_B_iff : ∀ x : L, x ∈ B ↔ ∃ a : A,
    x = algebraMap K L ((π.val : K) ^ (integralContainmentExponent + 1)) * (a : L)
  /-- Pinned free rank-one `𝒪_K[G]` coordinates on `B`. -/
  B_regularEquiv :
    ((L ≃ₐ[K] L) →₀ RingOfIntegers K) ≃ₗ[RingOfIntegers K] B
  /-- The regular generator of `B` is the prescribed scaling of the generator of `A`. -/
  B_regularEquiv_single : ∀ (σ : L ≃ₐ[K] L) (c : RingOfIntegers K),
    ((B_regularEquiv (Finsupp.single σ c) : B) : L) =
      algebraMap K L (c : K) *
        (algebraMap K L ((π.val : K) ^ (integralContainmentExponent + 1)) *
          σ generator)
  /-- The `B` coordinates intertwine left translation and Galois action. -/
  B_regularEquiv_equivariant : ∀ (τ : L ≃ₐ[K] L)
      (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K),
    ((B_regularEquiv (regularFinsuppTranslate τ c) : B) : L) =
      τ ((B_regularEquiv c : B) : L)
  /-- Galois stability of `B`. -/
  B_stable : ∀ (σ : L ≃ₐ[K] L) x, x ∈ B → σ x ∈ B
  /-- `B` consists of integral elements. -/
  B_integral : ∀ x, x ∈ B → ∃ b : RingOfIntegers L, (b : L) = x
  /-- `B` is a compact additive lattice. -/
  B_compact : IsCompact (B : Set L)
  /-- `B` is an open additive lattice. -/
  B_open : IsOpen (B : Set L)
  /-- The key multiplicative estimate `B² ⊆ π_K B`. -/
  mul_mem_pi : ∀ x ∈ B, ∀ y ∈ B,
    ∃ z ∈ B, x * y = algebraMap K L (π.val : K) * z
  /-- Reduction of regular coordinates modulo `π_K`. -/
  residueCoordinates : B →+ ((L ≃ₐ[K] L) →₀ LocalResidueField K)
  /-- Reduction is the canonical residue map on every regular basis vector. -/
  residueCoordinates_single : ∀ (σ : L ≃ₐ[K] L) (c : RingOfIntegers K),
    residueCoordinates (B_regularEquiv (Finsupp.single σ c)) =
      Finsupp.single σ (Ideal.Quotient.mk (LocalMaximalIdeal K) c)
  /-- Reduction is onto the additive regular residue module. -/
  residueCoordinates_surjective : Function.Surjective residueCoordinates
  /-- Its kernel is exactly `π_K B`. -/
  residueCoordinates_eq_zero_iff : ∀ b : B, residueCoordinates b = 0 ↔
    ∃ b' : B, (b : L) = algebraMap K L (π.val : K) * (b' : L)
  /-- Reduction intertwines Galois action with regular left translation. -/
  residueCoordinates_equivariant : ∀ (σ : L ≃ₐ[K] L) (b : B),
    residueCoordinates ⟨σ (b : L), B_stable σ b b.2⟩ =
      regularFinsuppTranslate σ (residueCoordinates b)

/--
**F02**, Lemma `lem:deep-acyclic-units`: clear denominators in a normal basis, construct the
literal regular lattices `A` and `B = π_K^(N+1)A`, and prove `B² ⊆ π_K B`.
-/
theorem deepUnitLattice_exists (π : Uniformizer K) :
    Nonempty (DeepUnitLatticeData K L π) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := IsTopologicalAddGroup.rightUniformSpace L
  letI := isUniformAddGroup_of_addCommGroup (G := L)
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  have algebraMap_OK (c : RingOfIntegers K) :
      algebraMap (RingOfIntegers K) K c = (c : K) := rfl
  let rawBasis := IsGalois.normalBasis K L
  let rawGen : L := rawBasis 1
  have rawGen_ne : rawGen ≠ 0 := rawBasis.ne_zero 1
  let rawUnit : Units L := Units.mk0 rawGen rawGen_ne
  let d : ℕ := (-normalizedValuation L rawUnit).toNat
  let scale : Units K := π.val ^ d
  let gen : L := algebraMap K L (scale : K) * rawGen
  let basis : Module.Basis (L ≃ₐ[K] L) K L := rawBasis.unitsSMul (fun _ => scale)
  have basis_eq (σ : L ≃ₐ[K] L) : basis σ = σ gen := by
    rw [show basis σ = (scale : K) • rawBasis σ from Module.Basis.unitsSMul_apply σ]
    rw [IsGalois.normalBasis_apply]
    simp [gen, rawGen, rawBasis, Algebra.smul_def]
  have gen_ne : gen ≠ 0 := by simp [gen, rawGen_ne]
  have gen_integral : ∃ a : RingOfIntegers L, (a : L) = gen := by
    let mappedScale : Units L := Units.map (algebraMap K L) scale
    have hscale : normalizedValuation L mappedScale =
        (ramificationIndex K L : ℤ) * (d : ℤ) := by
      rw [normalizedValuation_algebraMap, show normalizedValuation K scale = (d : ℤ) by
        dsimp [scale]
        change Multiplicative.toAdd (normalizedValuationHom K (π.val ^ d)) = _
        rw [map_pow, toAdd_pow]
        change (d : ℤ) * normalizedValuation K π.val = (d : ℤ)
        rw [π.valuation_eq_one, mul_one]]
    have he : 0 < ramificationIndex K L :=
      (ramificationInvariants_exists K L).choose_spec.choose_spec.1
    have hd : -normalizedValuation L rawUnit ≤ (d : ℤ) := by
      dsimp [d]
      omega
    have hnonneg : 0 ≤ normalizedValuation L (mappedScale * rawUnit) := by
      rw [normalizedValuation_mul, hscale]
      nlinarith
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom L).choose_spec.2
      (mappedScale * rawUnit) |>.1 hnonneg
    refine ⟨a, ?_⟩
    simpa [mappedScale, scale, gen, rawUnit] using ha
  let A : Submodule (RingOfIntegers K) L :=
    Submodule.span (RingOfIntegers K) (Set.range fun σ => basis σ)
  have basis_li : LinearIndependent (RingOfIntegers K) (fun σ => basis σ) :=
    basis.linearIndependent.restrict_scalars' (RingOfIntegers K)
  let Ae : ((L ≃ₐ[K] L) →₀ RingOfIntegers K) ≃ₗ[RingOfIntegers K] A :=
    basis_li.linearCombinationEquiv
  have Ae_coe (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K) :
      ((Ae c : A) : L) = Finsupp.linearCombination (RingOfIntegers K) (fun σ => basis σ) c :=
    rfl
  have Ae_single (σ : L ≃ₐ[K] L) (c : RingOfIntegers K) :
      ((Ae (Finsupp.single σ c) : A) : L) =
        algebraMap K L (c : K) * σ gen := by
    rw [Ae_coe, Finsupp.linearCombination_single, basis_eq]
    change (c : K) • σ gen = _
    simp [Algebra.smul_def]
  have basis_action (τ σ : L ≃ₐ[K] L) : τ (basis σ) = basis (τ * σ) := by
    rw [basis_eq, basis_eq]
    rfl
  have Ae_equivariant (τ : L ≃ₐ[K] L)
      (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K) :
      ((Ae (regularFinsuppTranslate τ c) : A) : L) = τ ((Ae c : A) : L) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | single σ a =>
        have htrans : regularFinsuppTranslate τ (Finsupp.single σ a) =
            Finsupp.single (τ * σ) a := by
          ext u
          simp [regularFinsuppTranslate, Finsupp.domCongr_apply]
        rw [htrans, Ae_single, Ae_single]
        simp
  have A_stable (τ : L ≃ₐ[K] L) (x : L) (hx : x ∈ A) : τ x ∈ A := by
    obtain ⟨c, hc⟩ := Ae.surjective ⟨x, hx⟩
    have hcx : ((Ae c : A) : L) = x := congrArg Subtype.val hc
    rw [← hcx, ← Ae_equivariant]
    exact (Ae (regularFinsuppTranslate τ c)).2
  have basis_integral (σ : L ≃ₐ[K] L) :
      ∃ a : RingOfIntegers L, (a : L) = basis σ := by
    obtain ⟨a, ha⟩ := gen_integral
    have hvalgen : 0 ≤ normalizedValuation L (Units.mk0 gen gen_ne) :=
      (exists_normalizedValuationHom L).choose_spec.2 _ |>.2 ⟨a, ha⟩
    let σgen : Units L := Units.mk0 (σ gen) (by simpa using σ.injective.ne gen_ne)
    have hval : 0 ≤ normalizedValuation L σgen := by
      rw [show σgen = Units.map σ.toRingEquiv.toRingHom (Units.mk0 gen gen_ne) by
        apply Units.ext; rfl, normalizedValuation_algEquiv_deep K L]
      exact hvalgen
    obtain ⟨a', ha'⟩ := (exists_normalizedValuationHom L).choose_spec.2 σgen |>.1 hval
    exact ⟨a', by simpa [σgen, basis_eq] using ha'⟩
  have A_integral (x : L) (hx : x ∈ A) : ∃ a : RingOfIntegers L, (a : L) = x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨σ, rfl⟩ := hx
        exact basis_integral σ
    | zero => exact ⟨0, rfl⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, rfl⟩
    | smul c x _ hx =>
        obtain ⟨a, rfl⟩ := hx
        exact ⟨algebraMap (RingOfIntegers K) (RingOfIntegers L) c * a, by
          change algebraMap K L (c : K) * (a : L) = c • (a : L)
          simp only [Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]⟩
  have A_compact : IsCompact (A : Set L) := by
    let f : ((L ≃ₐ[K] L) → RingOfIntegers K) → L := fun c =>
      ∑ σ, algebraMap K L ((c σ : RingOfIntegers K) : K) * basis σ
    have halg : Continuous (algebraMap K L) := by
      have ht := continuous_smul.comp
        (continuous_id.prodMk (show Continuous (fun _ : K => (1 : L)) from continuous_const))
      convert ht using 1
      funext x
      simp [Algebra.smul_def]
    have hf : Continuous f := by
      apply continuous_finset_sum
      intro σ _
      exact (halg.comp (continuous_subtype_val.comp (continuous_apply σ))).mul continuous_const
    have hrange : Set.range f = (A : Set L) := by
      ext x
      rw [Set.mem_range]
      constructor
      · rintro ⟨c, rfl⟩
        apply (Submodule.mem_span_range_iff_exists_fun (RingOfIntegers K)).2
        refine ⟨c, ?_⟩
        simp only [f, Algebra.smul_def,
          IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
      · intro hx
        obtain ⟨c, hc⟩ :=
          (Submodule.mem_span_range_iff_exists_fun (RingOfIntegers K)).1 hx
        refine ⟨c, ?_⟩
        simpa only [f, Algebra.smul_def,
          IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK] using hc
    rw [← hrange]
    simpa only [Set.image_univ] using isCompact_univ.image hf
  have A_open : IsOpen (A : Set L) := by
    have hset : (A : Set L) =
        ⋂ σ, (basis.coord σ : L → K) ⁻¹' (RingOfIntegers K : Set K) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro hx σ
        obtain ⟨c, hc⟩ :=
          (Submodule.mem_span_range_iff_exists_fun (RingOfIntegers K)).1 hx
        have hcK : (∑ i, (c i : K) • basis i) = x := by
          simpa only [Algebra.smul_def,
            IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK] using hc
        have h := congrArg (fun y : L => basis.repr y σ) hcK
        have heval : basis.repr x σ =
            (∑ i, Finsupp.single i (c i : K)) σ := by
          simpa using h.symm
        let ck : (L ≃ₐ[K] L) →₀ K :=
          Finsupp.equivFunOnFinite.symm (fun i => (c i : K))
        have hsum : (∑ i, Finsupp.single i (c i : K)) = ck := by
          convert Finsupp.univ_sum_single ck using 1 <;> simp [ck]
        have heq : basis.coord σ x = (c σ : K) := by
          change basis.repr x σ = _
          rw [heval, hsum]
          simp [ck]
        rw [heq]
        exact (c σ).prop
      · intro hx
        let c : (L ≃ₐ[K] L) → RingOfIntegers K := fun σ =>
          ⟨basis.repr x σ, by simpa using hx σ⟩
        apply (Submodule.mem_span_range_iff_exists_fun (RingOfIntegers K)).2
        refine ⟨c, ?_⟩
        simpa only [c, Algebra.smul_def,
          IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK] using basis.sum_repr x
    rw [hset]
    apply isOpen_iInter_of_finite
    intro σ
    apply IsOpen.preimage (LinearMap.continuous_of_finiteDimensional (basis.coord σ))
    exact Valued.isOpen_integer K
  have compactOL : IsCompact (RingOfIntegers L : Set L) := by
    have hrange : Set.range (fun x : RingOfIntegers L => (x : L)) =
        (RingOfIntegers L : Set L) := Subtype.range_val
    rw [← hrange]
    simpa only [Set.image_univ] using
      (isCompact_univ : IsCompact (Set.univ : Set (RingOfIntegers L))).image
        continuous_subtype_val
  have hcontain_eventually : ∀ᶠ a : L in nhds 0,
      ∀ x : L, x ∈ (RingOfIntegers L : Set L) → a * x ∈ A := by
    apply compactOL.eventually_forall_of_forall_eventually
    intro x hx
    have hnhds : (A : Set L) ∈ nhds ((0 : L) * x) := by
      simpa using A_open.mem_nhds A.zero_mem
    exact (continuous_mul.tendsto (0, x)) hnhds
  let mappedπ : Units L := Units.map (algebraMap K L) π.val
  have hmappedπ_val : 0 < normalizedValuation L mappedπ := by
    rw [normalizedValuation_algebraMap, π.valuation_eq_one, mul_one]
    exact_mod_cast (ramificationInvariants_exists K L).choose_spec.choose_spec.1
  have hmappedπ_lt : ValuativeRel.valuation L (mappedπ : L) < 1 := by
    have := (normalizedValuation_lt_iff_deep L 1 mappedπ).1 (by
      simpa [normalizedValuation] using hmappedπ_val)
    simpa using this
  have hpow : Filter.Tendsto (fun n : ℕ => algebraMap K L ((π.val : K) ^ n))
      Filter.atTop (nhds 0) := by
    simpa [mappedπ] using Valued.tendsto_zero_pow_of_v_lt_one hmappedπ_lt
  have hNevent := hpow.eventually hcontain_eventually
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hNevent)
  have piN_integral (x : RingOfIntegers L) :
      algebraMap K L ((π.val : K) ^ N) * (x : L) ∈ A := hN N le_rfl x x.2
  let p : K := (π.val : K) ^ (N + 1)
  have hp : p ≠ 0 := pow_ne_zero _ π.val.ne_zero
  let scaleA : A →ₗ[RingOfIntegers K] L :=
    { toFun := fun a => algebraMap K L p * (a : L)
      map_add' := fun a b => by simp [mul_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
        simp only [RingHom.id_apply]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
        ring }
  have scaleA_inj : Function.Injective scaleA := by
    intro a b h
    apply Subtype.ext
    exact mul_left_cancel₀ ((map_ne_zero (algebraMap K L)).2 hp) h
  let B : Submodule (RingOfIntegers K) L := LinearMap.range scaleA
  let scaleAe : A ≃ₗ[RingOfIntegers K] B := LinearEquiv.ofInjective scaleA scaleA_inj
  let Be : ((L ≃ₐ[K] L) →₀ RingOfIntegers K) ≃ₗ[RingOfIntegers K] B := Ae.trans scaleAe
  have memB (x : L) : x ∈ B ↔ ∃ a : A, x = algebraMap K L p * (a : L) := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  have Be_coe (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K) :
      ((Be c : B) : L) = algebraMap K L p * ((Ae c : A) : L) := by
    rfl
  have Be_single (σ : L ≃ₐ[K] L) (c : RingOfIntegers K) :
      ((Be (Finsupp.single σ c) : B) : L) =
        algebraMap K L (c : K) *
          (algebraMap K L ((π.val : K) ^ (N + 1)) * σ gen) := by
    rw [Be_coe, Ae_single]
    dsimp [p]
    ring
  have Be_equivariant (τ : L ≃ₐ[K] L)
      (c : (L ≃ₐ[K] L) →₀ RingOfIntegers K) :
      ((Be (regularFinsuppTranslate τ c) : B) : L) = τ ((Be c : B) : L) := by
    rw [Be_coe, Be_coe, Ae_equivariant]
    simp [p]
  have B_stable (τ : L ≃ₐ[K] L) (x : L) (hx : x ∈ B) : τ x ∈ B := by
    obtain ⟨c, hc⟩ := Be.surjective ⟨x, hx⟩
    have hcx : ((Be c : B) : L) = x := congrArg Subtype.val hc
    rw [← hcx, ← Be_equivariant]
    exact (Be (regularFinsuppTranslate τ c)).2
  have B_integral (x : L) (hx : x ∈ B) : ∃ b : RingOfIntegers L, (b : L) = x := by
    obtain ⟨a, rfl⟩ := (memB x).1 hx
    obtain ⟨a', ha'⟩ := A_integral a a.2
    have hpint : 0 ≤ normalizedValuation K (π.val ^ (N + 1)) := by
      change 0 ≤ Multiplicative.toAdd (normalizedValuationHom K (π.val ^ (N + 1)))
      rw [map_pow, toAdd_pow]
      change 0 ≤ (N + 1 : ℤ) * normalizedValuation K π.val
      rw [π.valuation_eq_one, mul_one]
      omega
    obtain ⟨q, hq⟩ := (exists_normalizedValuationHom K).choose_spec.2 (π.val ^ (N + 1)) |>.1 hpint
    refine ⟨algebraMap (RingOfIntegers K) (RingOfIntegers L) q * a', ?_⟩
    change algebraMap K L (q : K) * (a' : L) = _
    rw [hq, ha']
    rfl
  have B_compact : IsCompact (B : Set L) := by
    have himage : (B : Set L) = (fun x : L => algebraMap K L p * x) '' (A : Set L) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_image]
      constructor
      · intro hx
        obtain ⟨a, rfl⟩ := (memB x).1 hx
        exact ⟨a, a.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact (memB _).2 ⟨⟨a, ha⟩, rfl⟩
    rw [himage]
    exact A_compact.image (continuous_const.mul continuous_id)
  have B_open : IsOpen (B : Set L) := by
    have himage : (B : Set L) = (Homeomorph.mulLeft₀ (algebraMap K L p)
        ((map_ne_zero (algebraMap K L)).2 hp)) '' (A : Set L) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_image]
      constructor
      · intro hx
        obtain ⟨a, rfl⟩ := (memB x).1 hx
        exact ⟨a, a.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact (memB _).2 ⟨⟨a, ha⟩, rfl⟩
    rw [himage, (Homeomorph.mulLeft₀ _ _).isOpen_image]
    exact A_open
  have mul_mem_pi (x : L) (hx : x ∈ B) (y : L) (hy : y ∈ B) :
      ∃ z ∈ B, x * y = algebraMap K L (π.val : K) * z := by
    obtain ⟨a, rfl⟩ := (memB x).1 hx
    obtain ⟨b, rfl⟩ := (memB y).1 hy
    obtain ⟨ai, hai⟩ := A_integral a a.2
    obtain ⟨bi, hbi⟩ := A_integral b b.2
    let ci : RingOfIntegers L := ai * bi
    let cL : L := algebraMap K L ((π.val : K) ^ N) * (ci : L)
    have hcA : cL ∈ A := piN_integral ci
    let z : L := algebraMap K L p * cL
    refine ⟨z, (memB z).2 ⟨⟨cL, hcA⟩, rfl⟩, ?_⟩
    dsimp [z, cL, p, ci]
    rw [hai, hbi]
    push_cast
    ring
  let red : RingOfIntegers K →+ LocalResidueField K :=
    (Ideal.Quotient.mk (LocalMaximalIdeal K)).toAddMonoidHom
  let redF : ((L ≃ₐ[K] L) →₀ RingOfIntegers K) →+
      ((L ≃ₐ[K] L) →₀ LocalResidueField K) := Finsupp.mapRange.addMonoidHom red
  let res : B →+ ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
    redF.comp Be.symm.toLinearMap.toAddMonoidHom
  have res_single (σ : L ≃ₐ[K] L) (c : RingOfIntegers K) :
      res (Be (Finsupp.single σ c)) =
        Finsupp.single σ (Ideal.Quotient.mk (LocalMaximalIdeal K) c) := by
    change res (Be (Finsupp.single σ c)) = Finsupp.single σ (red c)
    simp [res, redF]
  have res_surj : Function.Surjective res := by
    intro c
    have hred : Function.Surjective red := Ideal.Quotient.mk_surjective
    obtain ⟨d, hd⟩ := Finsupp.mapRange_surjective red (map_zero red) hred c
    refine ⟨Be d, ?_⟩
    simpa [res, redF] using hd
  obtain ⟨ϖ, hϖ, hϖirr⟩ := integral_uniformizer_deep K π
  have red_varpi (a : RingOfIntegers K) : red (ϖ * a) = 0 := by
    change Ideal.Quotient.mk (LocalMaximalIdeal K) (ϖ * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem,
      show LocalMaximalIdeal K = Ideal.span {ϖ} from hϖirr.maximalIdeal_eq,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have res_zero (b : B) : res b = 0 ↔
      ∃ b' : B, (b : L) = algebraMap K L (π.val : K) * (b' : L) := by
    let c := Be.symm b
    constructor
    · intro hb
      have hcoord (σ : L ≃ₐ[K] L) : c σ ∈ LocalMaximalIdeal K := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have happ := DFunLike.congr_fun hb σ
        change red (c σ) = 0 at happ
        change Ideal.Quotient.mk (LocalMaximalIdeal K) (c σ) = 0
        exact happ
      have hmax : LocalMaximalIdeal K = Ideal.span {ϖ} := by
        exact hϖirr.maximalIdeal_eq
      have hdiv (σ : L ≃ₐ[K] L) : ∃ d : RingOfIntegers K, c σ = ϖ * d := by
        have hc := hcoord σ
        rw [hmax, Ideal.mem_span_singleton] at hc
        obtain ⟨d, hd⟩ := hc
        exact ⟨d, hd⟩
      let d : (L ≃ₐ[K] L) → RingOfIntegers K := fun σ => (hdiv σ).choose
      let d' : (L ≃ₐ[K] L) →₀ RingOfIntegers K :=
        Finsupp.equivFunOnFinite.symm d
      let b' : B := Be d'
      refine ⟨b', ?_⟩
      have hc : c = ϖ • d' := by
        apply Finsupp.ext
        intro σ
        change c σ = ϖ * d σ
        exact (hdiv σ).choose_spec
      have hbBe : b = Be c := by simp [c]
      rw [hbBe, hc, map_smul]
      have hcoe : (((ϖ • Be d' : B) : B) : L) =
          algebraMap K L (ϖ : K) * ((Be d' : B) : L) := by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
      rw [hcoe, hϖ]
    · rintro ⟨b', hb'⟩
      apply Finsupp.ext
      intro σ
      have hbsub : b = ϖ • b' := by
        apply Subtype.ext
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
        change (b : L) = algebraMap K L (ϖ : K) * (b' : L)
        simpa [hϖ] using hb'
      rw [hbsub]
      change red ((Be.symm (ϖ • b')) σ) = 0
      rw [map_smul]
      change red (ϖ * (Be.symm b') σ) = 0
      exact red_varpi _
  have res_equivariant (σ : L ≃ₐ[K] L) (b : B) :
      res ⟨σ (b : L), B_stable σ b b.2⟩ =
        regularFinsuppTranslate σ (res b) := by
    let c := Be.symm b
    have hb : b = Be c := by simp [c]
    have hsub : (⟨σ (b : L), B_stable σ b b.2⟩ : B) =
        Be (regularFinsuppTranslate σ c) := by
      apply Subtype.ext
      rw [hb]
      exact (Be_equivariant σ c).symm
    rw [hsub, hb]
    simp only [res, AddMonoidHom.comp_apply, LinearEquiv.symm_apply_apply, redF]
    ext τ
    simp [red, regularFinsuppTranslate, Finsupp.domCongr_apply]
  exact ⟨{
    rawGenerator := rawGen
    rawNormalBasis := rawBasis
    rawNormalBasis_eq_orbit := IsGalois.normalBasis_apply
    denominatorExponent := d
    generator := gen
    generator_eq_cleared := rfl
    generator_integral := gen_integral
    normalBasis := basis
    normalBasis_eq_orbit := basis_eq
    A := A
    A_regularEquiv := Ae
    A_regularEquiv_single := Ae_single
    A_regularEquiv_equivariant := Ae_equivariant
    A_stable := A_stable
    A_integral := A_integral
    A_compact := A_compact
    A_open := A_open
    integralContainmentExponent := N
    pi_pow_integral_le_A := piN_integral
    B := B
    mem_B_iff := by simpa [p] using memB
    B_regularEquiv := Be
    B_regularEquiv_single := Be_single
    B_regularEquiv_equivariant := Be_equivariant
    B_stable := B_stable
    B_integral := B_integral
    B_compact := B_compact
    B_open := B_open
    mul_mem_pi := mul_mem_pi
    residueCoordinates := res
    residueCoordinates_single := res_single
    residueCoordinates_surjective := res_surj
    residueCoordinates_eq_zero_iff := res_zero
    residueCoordinates_equivariant := res_equivariant }⟩

/--
**F03**, Lemma `lem:deep-acyclic-units`: the multiplicative filtration used in its proof.
Besides the equations defining
`V_i`, this package records the canonical inverse-limit map and the actual Galois action on each
graded quotient.  The graded coordinate formula is the blueprint map
`1 + π_K^i b ↦ b mod π_K B`.
-/
structure DeepUnitFiltrationData (π : Uniformizer K) where
  /-- The chosen normal-basis lattice data. -/
  lattice : DeepUnitLatticeData K L π
  /-- The groups in the filtration. -/
  V : ℕ → Subgroup (Units L)
  /-- Literal defining equation `V_i = 1 + π_K^i B`. -/
  mem_V_iff : ∀ (i : ℕ) (x : Units L), x ∈ V i ↔ ∃ b : lattice.B,
    (x : L) = 1 + algebraMap K L ((π.val : K) ^ i) * (b : L)
  /-- Every displayed `1 + π_K^i b` is a unit, so the defining equation loses no elements. -/
  one_add_isUnit : ∀ (i : ℕ) (b : lattice.B),
    IsUnit (1 + algebraMap K L ((π.val : K) ^ i) * (b : L))
  /-- The filtration decreases. -/
  V_antitone : Antitone V
  /-- A named successor inclusion used by the inverse system. -/
  V_succ_le : ∀ i, V (i + 1) ≤ V i
  /-- Every term consists of integral units. -/
  V_le_integralUnits : ∀ i, V i ≤ unitSubgroup L
  /-- In fact every term lies in the proved principal-unit group `U_L^1`. -/
  V_le_principalUnits : ∀ i, V i ≤ principalUnitSubgroup L 1
  /-- The `V_i` eventually lie in every term of the Stage-A principal-unit filtration. -/
  V_cofinal_principal_left : ∀ r, ∃ i,
    V i ≤ principalUnitSubgroup L (r + 1)
  /-- Conversely, every `V_i` contains a sufficiently deep standard principal-unit group. -/
  V_cofinal_principal_right : ∀ i, ∃ r,
    principalUnitSubgroup L (r + 1) ≤ V i
  /-- The first deep group is open. -/
  V_open : IsOpen (V 0 : Set (Units L))
  /-- Galois stability of every term. -/
  V_stable : ∀ i (σ : L ≃ₐ[K] L) x, x ∈ V i →
    Units.map σ.toRingEquiv.toRingHom x ∈ V i
  /-- The filtration terms viewed inside `V_0`. -/
  within : ℕ → Subgroup (V 0)
  /-- The within-filtration is the literal comap of `V_i`. -/
  within_eq_comap : ∀ i, within i = (V i).comap (V 0).subtype
  /-- Its level zero is all of `V_0`. -/
  within_zero : within 0 = ⊤
  /-- Successor maps for the inverse system. -/
  within_succ_le : ∀ i, within (i + 1) ≤ within i
  /-- Separatedness: the intersection of all `V_i` inside `V_0` is trivial. -/
  within_separated : (⨅ i, within i) = ⊥
  /-- The canonical inverse-limit equivalence. -/
  inverseLimitEquiv :
    (V 0) ≃ SubgroupInverseLimit within within_succ_le
  /-- The equivalence is the canonical system of quotient maps, not an arbitrary bijection. -/
  inverseLimitEquiv_apply : ∀ (x : V 0) i,
    (inverseLimitEquiv x).value i =
      (QuotientGroup.mk x : (V 0) ⧸ within i)
  /-- Actual Galois action on each multiplicative graded quotient. -/
  gradedAction : ∀ i (σ : L ≃ₐ[K] L),
    DeepUnitGradedQuotient V i →+ DeepUnitGradedQuotient V i
  /-- The action is induced by applying `σ` to representatives. -/
  gradedAction_mk : ∀ i (σ : L ≃ₐ[K] L) (x : V i),
    gradedAction i σ (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk
        (⟨Units.map σ.toRingEquiv.toRingHom (x : Units L),
          V_stable i σ x x.2⟩ : V i))
  /-- A representation whose carrier is identified with the actual graded quotient. -/
  gradedRep : ℕ → Rep ℤ (L ≃ₐ[K] L)
  /-- Carrier identification for the graded representation. -/
  gradedRepEquiv : ∀ i, gradedRep i ≃+ DeepUnitGradedQuotient V i
  /-- The carrier identification transports the representation action to `gradedAction`. -/
  gradedRepEquiv_equivariant : ∀ i (σ : L ≃ₐ[K] L) (x : gradedRep i),
    gradedRepEquiv i ((gradedRep i).ρ σ x) =
      gradedAction i σ (gradedRepEquiv i x)
  /-- The graded representation is the **C04** induced module from the trivial subgroup. -/
  gradedInducedIso : ∀ i,
    gradedRep i ≅ InducedFromTrivial (L ≃ₐ[K] L) (LocalResidueField K)
  /-- Equivariant regular residue coordinates on `V_i/V_{i+1}`. -/
  gradedCoordinates : ∀ i,
    DeepUnitGradedQuotient V i ≃+
      ((L ≃ₐ[K] L) →₀ LocalResidueField K)
  /-- Defining formula `1 + π_K^i b ↦ b mod π_K B`. -/
  gradedCoordinates_formula : ∀ i (x : V i) (b : lattice.B),
    ((x : Units L) : L) =
        1 + algebraMap K L ((π.val : K) ^ i) * (b : L) →
      gradedCoordinates i (Additive.ofMul (QuotientGroup.mk x)) =
        lattice.residueCoordinates b
  /-- The coordinates identify the actual action with regular left translation. -/
  gradedCoordinates_equivariant : ∀ i (σ : L ≃ₐ[K] L)
      (x : DeepUnitGradedQuotient V i),
    gradedCoordinates i (gradedAction i σ x) =
      regularFinsuppTranslate σ (gradedCoordinates i x)

/--
**F03**, Lemma `lem:deep-acyclic-units`: construct `V_i = 1 + π_K^iB`, identify every graded
piece equivariantly with the induced additive module `k_K[G]`, and apply **F01** and **C04**.
The conclusion is stated for the actual subrepresentation carried by `V_0` and is uniform after
restriction to every subgroup, exactly the cohomological-triviality shape used later.
-/
private abbrev botRep {G A : Type} [Group G] [AddCommGroup A] [Module ℤ A] :
    Rep ℤ (↥(⊥ : Subgroup G)) := Rep.trivial ℤ _ A
private abbrev coindBot {G A : Type} [Group G] [AddCommGroup A] [Module ℤ A] :
    Rep ℤ G := Rep.coind (⊥ : Subgroup G).subtype (botRep (G := G) (A := A))

private def coindBotEquivFun {G A : Type} [Group G] [AddCommGroup A] [Module ℤ A] :
    (coindBot (G := G) (A := A)) ≃ₗ[ℤ] (G → A) where
  toFun f := f.1
  invFun f := ⟨f, by
    intro x g
    have hx : x = 1 := by
      apply Subtype.ext
      exact (Subgroup.mem_bot (G := G)).mp x.2
    subst x
    simp⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def invPrecompEquiv {G A : Type} [Group G] [AddCommGroup A] [Module ℤ A] :
    (G → A) ≃ₗ[ℤ] (G → A) where
  toFun f g := f g⁻¹
  invFun f g := f g⁻¹
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def inducedRegularEquiv {G A : Type} [Group G] [AddCommGroup A]
    [Module ℤ A] [Fintype G] :
    InducedFromTrivial G A ≃+ (G →₀ A) := by
  classical
  let hmod : (inferInstance : Module ℤ A) = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  cases hmod
  exact ((Representation.equivOfIso
    (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv.trans
      coindBotEquivFun |>.trans invPrecompEquiv).trans
        (Finsupp.linearEquivFunOnFinite ℤ A G).symm |>.toAddEquiv

private theorem inducedRegularEquiv_equivariant {G A : Type} [Group G] [AddCommGroup A]
    [Module ℤ A] [Fintype G] (g : G) (x : InducedFromTrivial G A) :
    inducedRegularEquiv (G := G) (A := A) ((InducedFromTrivial G A).ρ g x) =
      regularFinsuppTranslate g (inducedRegularEquiv (G := G) (A := A) x) := by
  classical
  let hmod : (inferInstance : Module ℤ A) = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  cases hmod
  apply Finsupp.ext
  intro t
  change (((Representation.equivOfIso
      (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv
        ((InducedFromTrivial G A).ρ g x) : coindBot).1 t⁻¹) = _
  rw [show (Representation.equivOfIso
      (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv
        ((InducedFromTrivial G A).ρ g x) =
      (coindBot (G := G) (A := A)).ρ g
        ((Representation.equivOfIso
          (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv x) by
    exact Rep.hom_comm_apply
      (Rep.indCoindIso (botRep (G := G) (A := A))).hom g x]
  change ((Representation.equivOfIso
      (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv x : coindBot).1
        (t⁻¹ * g) =
    ((Representation.equivOfIso
      (Rep.indCoindIso (botRep (G := G) (A := A)))).toLinearEquiv x : coindBot).1
        ((g⁻¹ * t)⁻¹)
  rw [mul_inv_rev]
  simp

set_option maxHeartbeats 800000 in
-- The explicit quotient-coordinate construction is large enough to exceed the default budget.
private theorem deepUnitFiltrationData_exists (π : Uniformizer K) :
    Nonempty (DeepUnitFiltrationData K L π) := by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI := IsTopologicalAddGroup.rightUniformSpace L
    letI := isUniformAddGroup_of_addCommGroup (G := L)
    letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
    letI : (Valued.v (R := L) (Γ₀ := ValuativeRel.ValueGroupWithZero L)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := L).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField L :=
      Valued.toNontriviallyNormedField L (ValuativeRel.ValueGroupWithZero L)
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) := by
      constructor
      exact ValuativeRel.isEquiv _ _
    have algebraMap_OK (c : RingOfIntegers K) :
        algebraMap (RingOfIntegers K) K c = (c : K) := rfl
    obtain ⟨lat⟩ := deepUnitLattice_exists K L π
    obtain ⟨ϖ, hϖ, hϖirr⟩ := integral_uniformizer_deep K π
    let mappedπ : Units L := Units.map (algebraMap K L) π.val
    have hmappedπ_val : 0 < normalizedValuation L mappedπ := by
      rw [normalizedValuation_algebraMap, π.valuation_eq_one, mul_one]
      exact_mod_cast (ramificationInvariants_exists K L).choose_spec.choose_spec.1
    have hmappedπ_vlt : ValuativeRel.valuation L (mappedπ : L) < 1 := by
      have := (normalizedValuation_lt_iff_deep L 1 mappedπ).1 (by
        simpa [normalizedValuation] using hmappedπ_val)
      simpa using this
    have hmappedπ_norm : ‖(mappedπ : L)‖ < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mpr hmappedπ_vlt
    let scaleB (i : ℕ) : lat.B →ₗ[RingOfIntegers K] L :=
      { toFun := fun b => algebraMap K L ((π.val : K) ^ i) * (b : L)
        map_add' := fun a b => by simp [mul_add]
        map_smul' := fun c b => by
          simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
          simp only [RingHom.id_apply]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
          ring }
    have scaleB_inj (i : ℕ) : Function.Injective (scaleB i) := by
      intro a b h
      apply Subtype.ext
      exact mul_left_cancel₀ ((map_ne_zero (algebraMap K L)).2
        (pow_ne_zero i π.val.ne_zero)) h
    let C (i : ℕ) : Submodule (RingOfIntegers K) L := LinearMap.range (scaleB i)
    have memC (i : ℕ) (x : L) : x ∈ C i ↔ ∃ b : lat.B,
        x = algebraMap K L ((π.val : K) ^ i) * (b : L) := by
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨b, hb.symm⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, rfl⟩
    have C_succ_le (i : ℕ) : C (i + 1) ≤ C i := by
      intro x hx
      obtain ⟨b, rfl⟩ := (memC (i + 1) x).1 hx
      let b' : lat.B := ϖ • b
      apply (memC i _).2
      refine ⟨b', ?_⟩
      simp only [b', Submodule.coe_smul_of_tower, Algebra.smul_def]
      rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK, hϖ]
      push_cast
      ring
    have C_antitone : Antitone C := antitone_nat_of_succ_le C_succ_le
    have C_le_B (i : ℕ) : C i ≤ lat.B := by
      intro x hx
      obtain ⟨b, rfl⟩ := (memC i x).1 hx
      let b' : lat.B := (ϖ ^ i) • b
      have hb' := b'.2
      simp only [b', Submodule.coe_smul_of_tower, Algebra.smul_def] at hb'
      rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK] at hb'
      change algebraMap K L ((ϖ : K) ^ i) * (b : L) ∈ lat.B at hb'
      rw [hϖ] at hb'
      simpa only [map_pow] using hb'
    have B_norm_lt_one (b : lat.B) : ‖(b : L)‖ < 1 := by
      obtain ⟨a, ha⟩ := (lat.mem_B_iff b).1 b.2
      obtain ⟨ai, hai⟩ := lat.A_integral a a.2
      have hainorm : ‖(a : L)‖ ≤ 1 := by
        rw [← hai]
        apply Valued.toNormedField.norm_le_one_iff.mpr
        exact (Valuation.mem_integer_iff _ _).mp ai.prop
      have hpownorm : ‖(mappedπ : L) ^ (lat.integralContainmentExponent + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hmappedπ_norm (by omega)
      rw [ha, norm_mul]
      have hmap : algebraMap K L ((π.val : K) ^ (lat.integralContainmentExponent + 1)) =
          (mappedπ : L) ^ (lat.integralContainmentExponent + 1) := by simp [mappedπ]
      rw [hmap]
      nlinarith [norm_nonneg ((mappedπ : L) ^ (lat.integralContainmentExponent + 1))]
    have C_norm_lt_one (i : ℕ) (x : L) (hx : x ∈ C i) : ‖x‖ < 1 := by
      exact B_norm_lt_one ⟨x, C_le_B i hx⟩
    have C_mul (i : ℕ) (x : L) (hx : x ∈ C i) (y : L) (hy : y ∈ C i) :
        x * y ∈ C i := by
      obtain ⟨a, rfl⟩ := (memC i x).1 hx
      obtain ⟨b, rfl⟩ := (memC i y).1 hy
      obtain ⟨z, hz, hab⟩ := lat.mul_mem_pi a a.2 b b.2
      let z' : lat.B := (ϖ ^ (i + 1)) • ⟨z, hz⟩
      apply (memC i _).2
      refine ⟨z', ?_⟩
      have hz' : (z' : L) =
          algebraMap K L ((π.val : K) ^ (i + 1)) * z := by
        simp only [z', Submodule.coe_smul_of_tower, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
        change algebraMap K L ((ϖ : K) ^ (i + 1)) * z = _
        rw [hϖ]
      rw [hz']
      calc
        _ = algebraMap K L ((π.val : K) ^ (2 * i)) * ((a : L) * (b : L)) := by
          push_cast
          ring
        _ = algebraMap K L ((π.val : K) ^ (2 * i)) *
            (algebraMap K L (π.val : K) * z) := by rw [hab]
        _ = _ := by
          push_cast
          ring
    have C_compact (i : ℕ) : IsCompact (C i : Set L) := by
      have himage : (C i : Set L) =
          (fun x : L => algebraMap K L ((π.val : K) ^ i) * x) '' (lat.B : Set L) := by
        ext x
        simp only [SetLike.mem_coe, Set.mem_image]
        constructor
        · intro hx
          obtain ⟨b, rfl⟩ := (memC i x).1 hx
          exact ⟨b, b.2, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          exact (memC i _).2 ⟨⟨b, hb⟩, rfl⟩
      rw [himage]
      exact lat.B_compact.image (continuous_const.mul continuous_id)
    have C_closed (i : ℕ) : IsClosed (C i : Set L) := (C_compact i).isClosed
    have one_add_unit (i : ℕ) (b : lat.B) :
        IsUnit (1 + algebraMap K L ((π.val : K) ^ i) * (b : L)) := by
      rw [isUnit_iff_ne_zero]
      intro hzero
      have hc : algebraMap K L ((π.val : K) ^ i) * (b : L) = -1 :=
        eq_neg_of_add_eq_zero_right hzero
      have hmem : algebraMap K L ((π.val : K) ^ i) * (b : L) ∈ C i :=
        (memC i _).2 ⟨b, rfl⟩
      have hn := C_norm_lt_one i _ hmem
      rw [hc, norm_neg, norm_one] at hn
      exact lt_irrefl 1 hn
    let V : ℕ → Subgroup (Units L) := fun i =>
      { carrier := {x | (x : L) - 1 ∈ C i}
        one_mem' := by simp
        mul_mem' := by
          intro x y hx hy
          change ((x : L) * (y : L) - 1) ∈ C i
          have hmul := C_mul i ((x : L) - 1) hx ((y : L) - 1) hy
          have hadd := (C i).add_mem ((C i).add_mem hx hy) hmul
          convert hadd using 1
          ring
        inv_mem' := by
          intro x hx
          let c : L := (x : L) - 1
          have hcx : (x : L) = 1 + c := by simp [c]
          have hcC : c ∈ C i := by simpa [c] using hx
          have hcnorm : ‖-c‖ < 1 := by
            rw [norm_neg]
            exact C_norm_lt_one i _ hcC
          have hgeo := hasSum_geometric_of_norm_lt_one hcnorm
          let s : ℕ → L := fun n => -c * ∑ k ∈ Finset.range n, (-c) ^ k
          have hpowmem (n : ℕ) : (-c) ^ (n + 1) ∈ C i := by
            induction n with
            | zero => simpa using (C i).neg_mem hcC
            | succ n hn =>
                rw [pow_succ]
                exact C_mul i _ hn _ ((C i).neg_mem hcC)
          have hsmem (n : ℕ) : s n ∈ C i := by
            dsimp [s]
            rw [Finset.mul_sum]
            apply Submodule.sum_mem
            intro k hk
            rw [show -c * (-c) ^ k = (-c) ^ (k + 1) by rw [pow_succ']]
            exact hpowmem k
          have htend : Filter.Tendsto s Filter.atTop
              (nhds (-c * (1 - -c)⁻¹)) := by
            exact Filter.Tendsto.const_mul (-c) hgeo.tendsto_sum_nat
          have hlimit : -c * (1 - -c)⁻¹ = ((x⁻¹ : Units L) : L) - 1 := by
            rw [Units.val_inv_eq_inv_val]
            have hcne : (1 + c : L) ≠ 0 := by
              rw [← hcx]
              exact x.ne_zero
            rw [show (1 - -c) = (1 + c : L) by ring, hcx]
            calc
              -c * (1 + c)⁻¹ = (1 + c)⁻¹ * (1 - (1 + c)) := by ring
              _ = (1 + c)⁻¹ - 1 := by rw [mul_sub, mul_one, inv_mul_cancel₀ hcne]
          rw [hlimit] at htend
          exact C_closed i |>.mem_of_tendsto htend (Filter.Eventually.of_forall hsmem) }
    have memV (i : ℕ) (x : Units L) : x ∈ V i ↔ ∃ b : lat.B,
        (x : L) = 1 + algebraMap K L ((π.val : K) ^ i) * (b : L) := by
      change (x : L) - 1 ∈ C i ↔ _
      rw [memC]
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        calc
          (x : L) = ((x : L) - 1) + 1 := by ring
          _ = algebraMap K L ((π.val : K) ^ i) * (b : L) + 1 := by rw [hb]
          _ = _ := by ring
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [hb]
        ring
    have V_antitone : Antitone V := by
      intro i j hij x hx
      exact C_antitone hij hx
    have V_stable (i : ℕ) (σ : L ≃ₐ[K] L) (x : Units L) (hx : x ∈ V i) :
        Units.map σ.toRingEquiv.toRingHom x ∈ V i := by
      obtain ⟨b, hb⟩ := (memV i x).1 hx
      apply (memV i _).2
      refine ⟨⟨σ (b : L), lat.B_stable σ b b.2⟩, ?_⟩
      change σ (x : L) = _
      rw [hb]
      simp
    have C_open (i : ℕ) : IsOpen (C i : Set L) := by
      have himage : (C i : Set L) =
          (Homeomorph.mulLeft₀ (algebraMap K L ((π.val : K) ^ i))
            ((map_ne_zero (algebraMap K L)).2 (pow_ne_zero i π.val.ne_zero))) ''
              (lat.B : Set L) := by
        ext x
        simp only [SetLike.mem_coe, Set.mem_image]
        constructor
        · intro hx
          obtain ⟨b, rfl⟩ := (memC i x).1 hx
          exact ⟨b, b.2, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          exact (memC i _).2 ⟨⟨b, hb⟩, rfl⟩
      rw [himage, (Homeomorph.mulLeft₀ _ _).isOpen_image]
      exact lat.B_open
    have V_open : IsOpen (V 0 : Set (Units L)) := by
      let f : Units L → L := fun x => (x : L) - 1
      change IsOpen (f ⁻¹' (C 0 : Set L))
      have hf : Continuous f :=
        (show Continuous (fun x : Units L => (x : L)) from Units.continuous_val).sub
          (show Continuous (fun _ : Units L => (1 : L)) from continuous_const)
      exact (C_open 0).preimage hf
    have integralRep (i : ℕ) (x : Units L) (hx : x ∈ V i) :
        ∃ u : Units (RingOfIntegers L), ringUnitsToFieldUnits L u = x := by
      have hxi : x⁻¹ ∈ V i := (V i).inv_mem hx
      obtain ⟨ci, hci⟩ := lat.B_integral ((x : L) - 1) (C_le_B i hx)
      obtain ⟨di, hdi⟩ := lat.B_integral (((x⁻¹ : Units L) : L) - 1) (C_le_B i hxi)
      let ux : RingOfIntegers L := 1 + ci
      let vx : RingOfIntegers L := 1 + di
      have hux : (ux : L) = (x : L) := by dsimp [ux]; rw [hci]; ring
      have hvx : (vx : L) = ((x⁻¹ : Units L) : L) := by dsimp [vx]; rw [hdi]; ring
      let u : Units (RingOfIntegers L) :=
        { val := ux
          inv := vx
          val_inv := by
            apply Subtype.ext
            change (ux : L) * (vx : L) = 1
            rw [hux, hvx]
            simp
          inv_val := by
            apply Subtype.ext
            change (vx : L) * (ux : L) = 1
            rw [hux, hvx]
            simp }
      refine ⟨u, ?_⟩
      apply Units.ext
      exact hux
    have integral_norm_le (a : RingOfIntegers L) : ‖(a : L)‖ ≤ 1 := by
      apply Valued.toNormedField.norm_le_one_iff.mpr
      exact (Valuation.mem_integer_iff _ _).mp a.prop
    have integral_norm_eq_one_of_isUnit (a : RingOfIntegers L) (ha : IsUnit a) :
        ‖(a : L)‖ = 1 := by
      let u := ha.unit
      have hua : (u : RingOfIntegers L) = a := ha.unit_spec
      have h₁ := integral_norm_le a
      have h₂ := integral_norm_le (u⁻¹ : Units (RingOfIntegers L))
      have hprod : ‖(a : L)‖ * ‖(((u⁻¹ : Units (RingOfIntegers L)) :
          RingOfIntegers L) : L)‖ = 1 := by
        rw [← norm_mul]
        have heq : (a : L) * (((u⁻¹ : Units (RingOfIntegers L)) :
            RingOfIntegers L) : L) = 1 := by
          have hv := congrArg (fun z : RingOfIntegers L => (z : L)) u.val_inv
          simpa [hua] using hv
        rw [heq, norm_one]
      nlinarith [norm_nonneg (a : L),
        norm_nonneg ((((u⁻¹ : Units (RingOfIntegers L)) : RingOfIntegers L) : L))]
    have diff_mem_maximal (i : ℕ) (x : Units L) (hx : x ∈ V i)
        (u : Units (RingOfIntegers L)) (hu : ringUnitsToFieldUnits L u = x) :
        (u : RingOfIntegers L) - 1 ∈ LocalMaximalIdeal L := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      have hnorm := integral_norm_eq_one_of_isUnit ((u : RingOfIntegers L) - 1) hunit
      have hcoe : (((u : RingOfIntegers L) - 1 : RingOfIntegers L) : L) = (x : L) - 1 := by
        have huv := congrArg (fun z : Units L => (z : L)) hu
        change (((u : RingOfIntegers L) : L)) = (x : L) at huv
        exact congrArg (fun z : L => z - 1) huv
      rw [hcoe] at hnorm
      exact (ne_of_lt (C_norm_lt_one i _ hx)) hnorm
    have V_le_integral (i : ℕ) : V i ≤ unitSubgroup L := by
      intro x hx
      obtain ⟨u, hu⟩ := integralRep i x hx
      exact ⟨u, hu⟩
    have V_le_principal (i : ℕ) : V i ≤ principalUnitSubgroup L 1 := by
      intro x hx
      obtain ⟨u, hu⟩ := integralRep i x hx
      refine ⟨u, ?_, hu⟩
      change integralUnitReduction L 1 u = 1
      apply Units.ext
      change Ideal.Quotient.mk (LocalMaximalIdeal L ^ 1) (u : RingOfIntegers L) =
        Ideal.Quotient.mk (LocalMaximalIdeal L ^ 1) 1
      rw [Ideal.Quotient.eq, pow_one]
      exact diff_mem_maximal i x hx u hu
    obtain ⟨ϖL, hϖL, hϖLirr⟩ := integral_uniformizer_deep L (defaultUniformizer L)
    have maximal_pow_mem_iff (n : ℕ) (x : RingOfIntegers L) :
        x ∈ LocalMaximalIdeal L ^ n ↔ ∃ y : RingOfIntegers L, x = ϖL ^ n * y := by
      rw [show LocalMaximalIdeal L = Ideal.span {ϖL} from hϖLirr.maximalIdeal_eq,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, hy⟩
      · rintro ⟨y, rfl⟩
        exact dvd_mul_right _ _
    have hpowπ : Filter.Tendsto (fun n : ℕ => algebraMap K L ((π.val : K) ^ n))
        Filter.atTop (nhds 0) := by
      simpa [mappedπ] using Valued.tendsto_zero_pow_of_v_lt_one hmappedπ_vlt
    have hpowL : Filter.Tendsto (fun n : ℕ => ((ϖL : L) ^ n))
        Filter.atTop (nhds 0) := by
      have hvlt : ValuativeRel.valuation L (ϖL : L) < 1 := by
        have := (normalizedValuation_lt_iff_deep L 1 (defaultUniformizer L).val).1 (by
          rw [(defaultUniformizer L).valuation_eq_one]
          simp [normalizedValuation])
        simpa [hϖL] using this
      exact Valued.tendsto_zero_pow_of_v_lt_one hvlt
    have idealPow_open (n : ℕ) : IsOpen
        {x : L | ∃ y : RingOfIntegers L, x = (ϖL : L) ^ n * (y : L)} := by
      have heq : {x : L | ∃ y : RingOfIntegers L, x = (ϖL : L) ^ n * (y : L)} =
          (Homeomorph.mulLeft₀ ((ϖL : L) ^ n)
            (pow_ne_zero n (by simpa [hϖL] using (defaultUniformizer L).val.ne_zero))) ''
              (RingOfIntegers L : Set L) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨y, y.2, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
      rw [heq, (Homeomorph.mulLeft₀ _ _).isOpen_image]
      exact Valued.isOpen_integer L
    have V_cofinal_left (r : ℕ) : ∃ i, V i ≤ principalUnitSubgroup L (r + 1) := by
      let T : Set L := {x | ∃ y : RingOfIntegers L,
        x = (ϖL : L) ^ (r + 1) * (y : L)}
      have hTopen : IsOpen T := idealPow_open (r + 1)
      have hTev : ∀ᶠ a : L in nhds 0, ∀ b : L, b ∈ (lat.B : Set L) → a * b ∈ T := by
        apply lat.B_compact.eventually_forall_of_forall_eventually
        intro b hb
        have hzero : (0 : L) ∈ T := ⟨0, by simp⟩
        exact (continuous_mul.tendsto (0, b)) (by simpa using hTopen.mem_nhds hzero)
      have hev := hpowπ.eventually hTev
      obtain ⟨i, hi⟩ := Filter.eventually_atTop.1 hev
      refine ⟨i, ?_⟩
      intro x hx
      obtain ⟨u, hu⟩ := integralRep i x hx
      refine ⟨u, ?_, hu⟩
      change integralUnitReduction L (r + 1) u = 1
      apply Units.ext
      change Ideal.Quotient.mk (LocalMaximalIdeal L ^ (r + 1)) (u : RingOfIntegers L) =
        Ideal.Quotient.mk (LocalMaximalIdeal L ^ (r + 1)) 1
      rw [Ideal.Quotient.eq]
      rw [maximal_pow_mem_iff]
      have hdiff : (x : L) - 1 ∈ C i := hx
      obtain ⟨b, hb⟩ := (memC i _).1 hdiff
      obtain ⟨y, hy⟩ := hi i le_rfl b b.2
      refine ⟨y, ?_⟩
      apply Subtype.ext
      have huv := congrArg (fun z : Units L => (z : L)) hu
      change (((u : RingOfIntegers L) : L)) = (x : L) at huv
      change ((u : RingOfIntegers L) : L) - 1 = (ϖL : L) ^ (r + 1) * (y : L)
      rw [huv, hb, hy]
    have compactOL : IsCompact (RingOfIntegers L : Set L) := by
      have hrange : Set.range (fun x : RingOfIntegers L => (x : L)) =
          (RingOfIntegers L : Set L) := Subtype.range_val
      rw [← hrange]
      simpa only [Set.image_univ] using
        (isCompact_univ : IsCompact (Set.univ : Set (RingOfIntegers L))).image
          continuous_subtype_val
    have V_cofinal_right (i : ℕ) : ∃ r,
        principalUnitSubgroup L (r + 1) ≤ V i := by
      have hCev : ∀ᶠ a : L in nhds 0, ∀ y : L,
          y ∈ (RingOfIntegers L : Set L) → a * y ∈ C i := by
        apply compactOL.eventually_forall_of_forall_eventually
        intro y hy
        exact (continuous_mul.tendsto (0, y)) (by
          simpa using (C_open i).mem_nhds (C i).zero_mem)
      have hev := hpowL.eventually hCev
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
      refine ⟨n, ?_⟩
      rintro x ⟨u, hu, hux⟩
      have hq : (u : RingOfIntegers L) - 1 ∈ LocalMaximalIdeal L ^ (n + 1) := by
        apply Ideal.Quotient.eq.mp
        exact congrArg Units.val hu
      obtain ⟨y, hy⟩ := (maximal_pow_mem_iff (n + 1) _).1 hq
      have hmem : (ϖL : L) ^ (n + 1) * (y : L) ∈ C i := hn (n + 1) (by omega) y y.2
      change (x : L) - 1 ∈ C i
      have huxv := congrArg (fun z : Units L => (z : L)) hux.symm
      change (x : L) = (((u : RingOfIntegers L) : L)) at huxv
      rw [huxv]
      convert hmem using 1
      exact congrArg (fun z : RingOfIntegers L => (z : L)) hy
    let within (i : ℕ) : Subgroup (V 0) := (V i).comap (V 0).subtype
    have within_eq (i : ℕ) : within i = (V i).comap (V 0).subtype := rfl
    have within_zero : within 0 = ⊤ := by
      ext x
      simp [within]
    have within_succ (i : ℕ) : within (i + 1) ≤ within i := by
      intro x hx
      exact C_succ_le i hx
    have within_sep : (⨅ i, within i) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxV (i : ℕ) : (x : Units L) ∈ V i := by
        have hi : x ∈ within i := by
          exact Subgroup.mem_iInf.mp hx i
        exact hi
      have hxP (r : ℕ) : (x : Units L) ∈ principalUnitSubgroup L (r + 1) := by
        obtain ⟨i, hi⟩ := V_cofinal_left r
        exact hi (hxV i)
      have hxinf : (x : Units L) ∈ ⨅ r, principalUnitSubgroup L (r + 1) := by
        exact Subgroup.mem_iInf.mpr hxP
      rw [iInf_principalUnitSubgroup L] at hxinf
      have hxone : (x : Units L) = 1 := hxinf
      apply Subtype.ext
      exact hxone
    let oneAddToV0 (b : lat.B) : V 0 :=
      ⟨(one_add_unit 0 b).unit, by
        apply (memV 0 _).2
        refine ⟨b, ?_⟩
        simpa using (one_add_unit 0 b).unit_spec⟩
    have oneAddToV0_cont : Continuous oneAddToV0 := by
      apply Continuous.subtype_mk
      apply Units.continuous_iff.mpr
      constructor
      · have hval : Continuous (fun b : lat.B => (1 + (b : L))) :=
          continuous_const.add continuous_subtype_val
        convert hval using 1
        funext b
        simpa only [Function.comp_apply, pow_zero, map_one, one_mul] using
          (one_add_unit 0 b).unit_spec
      · have hval : Continuous (fun b : lat.B => (1 + (b : L))) :=
          continuous_const.add continuous_subtype_val
        have hne (b : lat.B) : (1 + (b : L)) ≠ 0 := by
          have hspec : ((one_add_unit 0 b).unit : L) = 1 + (b : L) := by
            simpa only [pow_zero, map_one, one_mul] using (one_add_unit 0 b).unit_spec
          rw [← hspec]
          exact (one_add_unit 0 b).unit.ne_zero
        have hinv := hval.inv₀ hne
        convert hinv using 1
        funext b
        have hspec : ((one_add_unit 0 b).unit : L) = 1 + (b : L) := by
          simpa only [pow_zero, map_one, one_mul] using (one_add_unit 0 b).unit_spec
        calc
          (((one_add_unit 0 b).unit⁻¹ : Units L) : L) =
              ((one_add_unit 0 b).unit : L)⁻¹ := Units.val_inv_eq_inv_val _
          _ = (1 + (b : L))⁻¹ := congrArg Inv.inv hspec
    have oneAddToV0_surj : Function.Surjective oneAddToV0 := by
      intro x
      obtain ⟨b, hb⟩ := (memV 0 (x : Units L)).1 x.2
      refine ⟨b, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rw [(one_add_unit 0 b).unit_spec]
      simpa using hb.symm
    have compactV0 : IsCompact (Set.univ : Set (V 0)) := by
      letI : CompactSpace lat.B := isCompact_iff_compactSpace.mp lat.B_compact
      have hrange : Set.range oneAddToV0 = Set.univ :=
        Set.range_eq_univ.mpr oneAddToV0_surj
      rw [← hrange]
      simpa only [Set.image_univ] using
        (isCompact_univ.image oneAddToV0_cont : IsCompact (oneAddToV0 '' Set.univ))
    let toLimit : (V 0) → SubgroupInverseLimit within within_succ := fun x =>
      { value := fun n => (QuotientGroup.mk x : (V 0) ⧸ within n)
        compatible := fun n => by simp [quotientProjection] }
    have toLimit_inj : Function.Injective toLimit := by
      intro x y hxy
      have hdiv (n : ℕ) : x / y ∈ within n := by
        apply QuotientGroup.eq_iff_div_mem.mp
        exact congrArg (fun z => z.value n) hxy
      have hall : x / y ∈ ⨅ n, within n := Subgroup.mem_iInf.mpr hdiv
      rw [within_sep] at hall
      exact div_eq_one.mp hall
    have toLimit_surj : Function.Surjective toLimit := by
      intro c
      let rep (n : ℕ) : V 0 := Quotient.out (c.value n)
      have rep_mk (n : ℕ) : (QuotientGroup.mk (rep n) : (V 0) ⧸ within n) = c.value n :=
        Quotient.out_eq _
      let T (n : ℕ) : Set (V 0) :=
        {x | (QuotientGroup.mk x : (V 0) ⧸ within n) = c.value n}
      have T_nonempty (n : ℕ) : (T n).Nonempty := ⟨rep n, rep_mk n⟩
      have within_closed (n : ℕ) : IsClosed (within n : Set (V 0)) := by
        change IsClosed {x : V 0 | (((x : V 0) : Units L) : L) - 1 ∈ C n}
        let f : V 0 → L := fun x => (((x : V 0) : Units L) : L) - 1
        change IsClosed (f ⁻¹' (C n : Set L))
        have hf : Continuous f :=
          (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
        exact (C_closed n).preimage hf
      have T_closed (n : ℕ) : IsClosed (T n) := by
        have hset : T n = {x : V 0 | x / rep n ∈ within n} := by
          ext x
          change ((QuotientGroup.mk x : (V 0) ⧸ within n) = c.value n) ↔ _
          rw [← rep_mk n, QuotientGroup.eq_iff_div_mem]
          rfl
        rw [hset]
        let f : V 0 → V 0 := fun x => x / rep n
        change IsClosed (f ⁻¹' (within n : Set (V 0)))
        exact (within_closed n).preimage (continuous_id.div_const (rep n))
      have T_succ (n : ℕ) : T (n + 1) ⊆ T n := by
        intro x hx
        change (QuotientGroup.mk x : (V 0) ⧸ within n) = c.value n
        calc
          _ = quotientProjection (within_succ n)
              (QuotientGroup.mk x : (V 0) ⧸ within (n + 1)) := by
                simp [quotientProjection]
          _ = quotientProjection (within_succ n) (c.value (n + 1)) := by rw [hx]
          _ = c.value n := c.compatible n
      have T0_compact : IsCompact (T 0) :=
        compactV0.of_isClosed_subset (T_closed 0) (fun _ _ => Set.mem_univ _)
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        T T_succ T_nonempty T0_compact T_closed
      refine ⟨x, ?_⟩
      have hv : (toLimit x).value = c.value := by
        funext n
        exact Set.mem_iInter.mp hx n
      cases h₁ : toLimit x with
      | mk v hvcomp =>
        cases h₂ : c with
        | mk w hwcomp =>
          have hvw : v = w := by simpa [h₁, h₂] using hv
          cases hvw
          rfl
    let invEquiv : (V 0) ≃ SubgroupInverseLimit within within_succ :=
      Equiv.ofBijective toLimit ⟨toLimit_inj, toLimit_surj⟩
    have invEquiv_apply (x : V 0) (i : ℕ) :
        (invEquiv x).value i = (QuotientGroup.mk x : (V 0) ⧸ within i) := rfl
    let coord (i : ℕ) (x : V i) : lat.B :=
      Classical.choose ((memV i (x : Units L)).1 x.2)
    have coord_spec (i : ℕ) (x : V i) :
        ((x : Units L) : L) = 1 + algebraMap K L ((π.val : K) ^ i) * (coord i x : L) :=
      Classical.choose_spec ((memV i (x : Units L)).1 x.2)
    have coord_unique (i : ℕ) (x : V i) (b : lat.B)
        (hb : ((x : Units L) : L) =
          1 + algebraMap K L ((π.val : K) ^ i) * (b : L)) : coord i x = b := by
      apply Subtype.ext
      apply mul_left_cancel₀ ((map_ne_zero (algebraMap K L)).2 (pow_ne_zero i π.val.ne_zero))
      have hs := coord_spec i x
      rw [hb] at hs
      exact add_left_cancel hs.symm
    let residueFun (i : ℕ) (x : Additive (V i)) :
        ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
      lat.residueCoordinates (coord i (Additive.toMul x))
    have residueFun_zero (i : ℕ) : residueFun i 0 = 0 := by
      change lat.residueCoordinates (coord i (Additive.toMul 0)) = 0
      rw [coord_unique i (Additive.toMul 0) 0 (by simp), map_zero]
    have residueFun_add (i : ℕ) (x y : Additive (V i)) :
        residueFun i (x + y) = residueFun i x + residueFun i y := by
        let a := coord i (Additive.toMul x)
        let b := coord i (Additive.toMul y)
        obtain ⟨z, hzB, hab⟩ := lat.mul_mem_pi (a : L) a.2 (b : L) b.2
        let zB : lat.B := ⟨z, hzB⟩
        have habB : (a : L) * (b : L) ∈ lat.B := by
          rw [hab]
          have hzsmul := lat.B.smul_mem ϖ zB.2
          simp only [Algebra.smul_def] at hzsmul
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK] at hzsmul
          change algebraMap K L (ϖ : K) * z ∈ lat.B at hzsmul
          rw [hϖ] at hzsmul
          exact hzsmul
        let abB : lat.B := ⟨(a : L) * (b : L), habB⟩
        let e : lat.B := ϖ ^ i • abB
        have he : (e : L) = algebraMap K L ((π.val : K) ^ i) *
            ((a : L) * (b : L)) := by
          simp only [e, Submodule.coe_smul_of_tower, Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
          change algebraMap K L ((ϖ : K) ^ i) * ((a : L) * (b : L)) = _
          rw [hϖ]
        have hezero : lat.residueCoordinates e = 0 := by
          rw [lat.residueCoordinates_eq_zero_iff]
          refine ⟨ϖ ^ i • zB, ?_⟩
          simp only [e, Submodule.coe_smul_of_tower, Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
          change algebraMap K L ((ϖ : K) ^ i) * ((a : L) * (b : L)) = _
          rw [hab]
          change algebraMap K L ((ϖ : K) ^ i) *
            (algebraMap K L (π.val : K) * (zB : L)) =
            algebraMap K L (π.val : K) *
              (algebraMap K L (((ϖ ^ i : RingOfIntegers K) : K)) * (zB : L))
          push_cast
          ring
        have hprod : (((Additive.toMul (x + y) : V i) : Units L) : L) =
            1 + algebraMap K L ((π.val : K) ^ i) * ((a + b + e : lat.B) : L) := by
          change (((Additive.toMul x : V i) : Units L) : L) *
              (((Additive.toMul y : V i) : Units L) : L) = _
          rw [coord_spec i (Additive.toMul x), coord_spec i (Additive.toMul y)]
          change (1 + algebraMap K L ((π.val : K) ^ i) * (a : L)) *
            (1 + algebraMap K L ((π.val : K) ^ i) * (b : L)) = _
          push_cast
          rw [he]
          simp only [map_pow]
          ring
        change lat.residueCoordinates (coord i (Additive.toMul (x + y))) =
          lat.residueCoordinates (coord i (Additive.toMul x)) +
            lat.residueCoordinates (coord i (Additive.toMul y))
        rw [coord_unique i (Additive.toMul (x + y)) (a + b + e) hprod]
        simp [hezero]
        rfl
    let residueOnV (i : ℕ) : Additive (V i) →+
        ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
      { toFun := residueFun i
        map_zero' := residueFun_zero i
        map_add' := residueFun_add i }
    have residueOnV_eq_zero_iff (i : ℕ) (x : Additive (V i)) :
        residueOnV i x = 0 ↔
          Additive.toMul x ∈ (V (i + 1)).comap (V i).subtype := by
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := (lat.residueCoordinates_eq_zero_iff (coord i (Additive.toMul x))).1 hx
        apply (memV (i + 1) _).2
        refine ⟨b, ?_⟩
        change (((Additive.toMul x : V i) : Units L) : L) = _
        rw [coord_spec i (Additive.toMul x), hb]
        push_cast
        ring
      · intro hx
        obtain ⟨b, hb⟩ := (memV (i + 1) ((Additive.toMul x : V i) : Units L)).1 hx
        have hc : coord i (Additive.toMul x) = ϖ • b := by
          apply coord_unique i
          rw [hb]
          simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK]
          change 1 + algebraMap K L ((π.val : K) ^ (i + 1)) * (b : L) =
            1 + algebraMap K L ((π.val : K) ^ i) *
              (algebraMap K L (ϖ : K) * (b : L))
          rw [hϖ]
          push_cast
          ring
        change lat.residueCoordinates (coord i (Additive.toMul x)) = 0
        rw [hc, lat.residueCoordinates_eq_zero_iff]
        refine ⟨b, ?_⟩
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L, algebraMap_OK, hϖ]
    let residueMul (i : ℕ) : V i →* Multiplicative
        ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
      { toFun x := Multiplicative.ofAdd (residueOnV i (Additive.ofMul x))
        map_one' := (residueOnV i).map_zero
        map_mul' x y := (residueOnV i).map_add (Additive.ofMul x) (Additive.ofMul y) }
    have residueMul_kernel (i : ℕ) :
        (V (i + 1)).comap (V i).subtype ≤ (residueMul i).ker := by
      intro x hx
      change residueOnV i (Additive.ofMul x) = 0
      exact (residueOnV_eq_zero_iff i (Additive.ofMul x)).2 hx
    let gradedMap (i : ℕ) : DeepUnitGradedQuotient V i →+
        ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
      (QuotientGroup.lift ((V (i + 1)).comap (V i).subtype)
        (residueMul i) (residueMul_kernel i)).toAdditive
    have gradedMap_mk (i : ℕ) (x : V i) :
        gradedMap i (Additive.ofMul (QuotientGroup.mk x)) =
          lat.residueCoordinates (coord i x) := by
      change (QuotientGroup.lift ((V (i + 1)).comap (V i).subtype)
        (residueMul i) (residueMul_kernel i)) (QuotientGroup.mk x) = _
      rw [QuotientGroup.lift_mk]
      rfl
    have gradedMap_surj (i : ℕ) : Function.Surjective (gradedMap i) := by
      intro c
      obtain ⟨b, hb⟩ := lat.residueCoordinates_surjective c
      let x : V i := ⟨(one_add_unit i b).unit, by
        apply (memV i _).2
        exact ⟨b, (one_add_unit i b).unit_spec⟩⟩
      refine ⟨Additive.ofMul (QuotientGroup.mk x), ?_⟩
      rw [gradedMap_mk, coord_unique i x b]
      · exact hb
      · exact (one_add_unit i b).unit_spec
    have residueMul_ker (i : ℕ) : (residueMul i).ker =
        (V (i + 1)).comap (V i).subtype := by
      ext x
      change residueOnV i (Additive.ofMul x) = 0 ↔ _
      exact residueOnV_eq_zero_iff i (Additive.ofMul x)
    have gradedLift_inj (i : ℕ) : Function.Injective
        (QuotientGroup.lift ((V (i + 1)).comap (V i).subtype)
          (residueMul i) (residueMul_kernel i)) := by
      apply (MonoidHom.ker_eq_bot_iff _).1
      rw [QuotientGroup.ker_lift, residueMul_ker]
      apply (Subgroup.map_eq_bot_iff _).2
      intro x hx
      change (QuotientGroup.mk x : V i ⧸ (V (i + 1)).comap (V i).subtype) = 1
      exact (QuotientGroup.eq_one_iff x).2 hx
    have gradedMap_inj (i : ℕ) : Function.Injective (gradedMap i) := by
      intro q r hqr
      apply Additive.toMul.injective
      apply gradedLift_inj i
      exact hqr
    let gradedCoordinates (i : ℕ) : DeepUnitGradedQuotient V i ≃+
        ((L ≃ₐ[K] L) →₀ LocalResidueField K) :=
      AddEquiv.ofBijective (gradedMap i) ⟨gradedMap_inj i, gradedMap_surj i⟩
    have gradedCoordinates_formula (i : ℕ) (x : V i) (b : lat.B)
        (hb : ((x : Units L) : L) =
          1 + algebraMap K L ((π.val : K) ^ i) * (b : L)) :
        gradedCoordinates i (Additive.ofMul (QuotientGroup.mk x)) =
          lat.residueCoordinates b := by
      change gradedMap i (Additive.ofMul (QuotientGroup.mk x)) = _
      rw [gradedMap_mk, coord_unique i x b hb]
    let gradedAction (i : ℕ) (σ : L ≃ₐ[K] L) :
        DeepUnitGradedQuotient V i →+ DeepUnitGradedQuotient V i :=
      (gradedCoordinates i).symm.toAddMonoidHom.comp
        ((regularFinsuppTranslate σ).comp (gradedCoordinates i).toAddMonoidHom)
    have coordinates_sigma_mk (i : ℕ) (σ : L ≃ₐ[K] L) (x : V i) :
        gradedCoordinates i (Additive.ofMul (QuotientGroup.mk
          (⟨Units.map σ.toRingEquiv.toRingHom (x : Units L),
            V_stable i σ x x.2⟩ : V i))) =
          regularFinsuppTranslate σ
            (gradedCoordinates i (Additive.ofMul (QuotientGroup.mk x))) := by
      let b := coord i x
      let sb : lat.B := ⟨σ (b : L), lat.B_stable σ b b.2⟩
      rw [gradedCoordinates_formula i x b (coord_spec i x)]
      rw [gradedCoordinates_formula i _ sb]
      · exact lat.residueCoordinates_equivariant σ b
      · change σ (((x : Units L) : L)) = _
        rw [coord_spec i x]
        simp [b, sb]
    have gradedAction_mk (i : ℕ) (σ : L ≃ₐ[K] L) (x : V i) :
        gradedAction i σ (Additive.ofMul (QuotientGroup.mk x)) =
          Additive.ofMul (QuotientGroup.mk
            (⟨Units.map σ.toRingEquiv.toRingHom (x : Units L),
              V_stable i σ x x.2⟩ : V i)) := by
      apply (gradedCoordinates i).injective
      change gradedCoordinates i ((gradedCoordinates i).symm
        (regularFinsuppTranslate σ
          (gradedCoordinates i (Additive.ofMul (QuotientGroup.mk x))))) = _
      rw [AddEquiv.apply_symm_apply]
      exact (coordinates_sigma_mk i σ x).symm
    have gradedCoordinates_equivariant (i : ℕ) (σ : L ≃ₐ[K] L)
        (x : DeepUnitGradedQuotient V i) :
        gradedCoordinates i (gradedAction i σ x) =
          regularFinsuppTranslate σ (gradedCoordinates i x) := by
      simp [gradedAction]
    let gradedRep (_i : ℕ) : Rep ℤ (L ≃ₐ[K] L) :=
      InducedFromTrivial (L ≃ₐ[K] L) (LocalResidueField K)
    let gradedRepEquiv (i : ℕ) : gradedRep i ≃+ DeepUnitGradedQuotient V i :=
      (inducedRegularEquiv (G := L ≃ₐ[K] L) (A := LocalResidueField K)).trans
        (gradedCoordinates i).symm
    have gradedRepEquiv_equivariant (i : ℕ) (σ : L ≃ₐ[K] L) (x : gradedRep i) :
        gradedRepEquiv i ((gradedRep i).ρ σ x) =
          gradedAction i σ (gradedRepEquiv i x) := by
      apply (gradedCoordinates i).injective
      rw [gradedCoordinates_equivariant]
      simpa only [gradedRepEquiv, gradedRep, AddEquiv.trans_apply,
        AddEquiv.apply_symm_apply] using
          inducedRegularEquiv_equivariant (G := L ≃ₐ[K] L)
            (A := LocalResidueField K) σ x
    let gradedInducedIso (_i : ℕ) : gradedRep _i ≅
        InducedFromTrivial (L ≃ₐ[K] L) (LocalResidueField K) := CategoryTheory.Iso.refl _
    let D : DeepUnitFiltrationData K L π :=
      { lattice := lat
        V := V
        mem_V_iff := memV
        one_add_isUnit := one_add_unit
        V_antitone := V_antitone
        V_succ_le := fun i => V_antitone (Nat.le_succ i)
        V_le_integralUnits := V_le_integral
        V_le_principalUnits := V_le_principal
        V_cofinal_principal_left := V_cofinal_left
        V_cofinal_principal_right := V_cofinal_right
        V_open := V_open
        V_stable := V_stable
        within := within
        within_eq_comap := within_eq
        within_zero := within_zero
        within_succ_le := within_succ
        within_separated := within_sep
        inverseLimitEquiv := invEquiv
        inverseLimitEquiv_apply := invEquiv_apply
        gradedAction := gradedAction
        gradedAction_mk := gradedAction_mk
        gradedRep := gradedRep
        gradedRepEquiv := gradedRepEquiv
        gradedRepEquiv_equivariant := gradedRepEquiv_equivariant
        gradedInducedIso := gradedInducedIso
        gradedCoordinates := gradedCoordinates
        gradedCoordinates_formula := gradedCoordinates_formula
        gradedCoordinates_equivariant := gradedCoordinates_equivariant }
    exact ⟨D⟩

section DeepUnitFiltrationAssembly

variable (π : Uniformizer K) (D : DeepUnitFiltrationData K L π)

private def deepRepEquiv :
    stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0) ≃+ Additive (D.V 0) where
  toFun x := Additive.ofMul ⟨Additive.toMul x.1, x.2⟩
  invFun x := ⟨Additive.ofMul (((Additive.toMul x : D.V 0) : Units L)),
    (Additive.toMul x : D.V 0).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Additive.toMul.injective; apply Subtype.ext; rfl
  map_add' _ _ := rfl

private theorem deepRepEquiv_equivariant
    (g : L ≃ₐ[K] L) (x : stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)) :
    deepRepEquiv K L π D
        ((stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)).ρ g x) =
      Additive.ofMul
        (⟨Units.map g.toRingEquiv.toRingHom
          ((Additive.toMul (deepRepEquiv K L π D x) : D.V 0) : Units L),
          D.V_stable 0 g _ (Additive.toMul (deepRepEquiv K L π D x) : D.V 0).2⟩ : D.V 0) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change Additive.toMul (((stableUnitSubgroupRep K L (D.V 0)
    (D.V_stable 0)).ρ g) x).1 = _
  rfl


private def filtrationFromInverseLimit
    {H : Type} [CommGroup H]
    (F : ℕ → Subgroup H) (Fzero : F 0 = ⊤)
    (Fsucc : ∀ n, F (n + 1) ≤ F n) (Fsep : (⨅ n, F n) = ⊥)
    (e : H ≃ SubgroupInverseLimit F Fsucc)
    (e_apply : ∀ (x : H) n, (e x).value n = (QuotientGroup.mk x : H ⧸ F n)) :
    CompleteSeparatedFiltration (Additive H) where
  F n := (F n).toAddSubgroup
  F_zero := by rw [Fzero]; rfl
  antitone := by exact antitone_nat_of_succ_le (fun n => Fsucc n)
  separated := by
    ext x
    constructor
    · intro hx
      have hall : Additive.toMul x ∈ ⨅ n, F n := by
        apply Subgroup.mem_iInf.mpr
        intro n
        exact AddSubgroup.mem_iInf.mp hx n
      rw [Fsep] at hall
      exact hall
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      exact (⨅ n, (F n).toAddSubgroup).zero_mem
  complete := by
    intro x hx
    let c : SubgroupInverseLimit F Fsucc :=
      { value := fun n => (QuotientGroup.mk (Additive.toMul (x n)) : H ⧸ F n)
        compatible := fun n => by
          rw [show quotientProjection (Fsucc n)
              (QuotientGroup.mk (Additive.toMul (x (n + 1)))) =
              (QuotientGroup.mk (Additive.toMul (x (n + 1))) : H ⧸ F n) by
            simp [quotientProjection]]
          apply QuotientGroup.eq_iff_div_mem.mpr
          exact hx n }
    refine ⟨Additive.ofMul (e.symm c), ?_⟩
    intro n
    change e.symm c / Additive.toMul (x n) ∈ F n
    apply QuotientGroup.eq_iff_div_mem.mp
    rw [← e_apply, e.apply_symm_apply]

private def filtrationComap
    {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (Φ : CompleteSeparatedFiltration A) (e : B ≃+ A) :
    CompleteSeparatedFiltration B where
  F n := (Φ.F n).comap e.toAddMonoidHom
  F_zero := by ext x; simp [Φ.F_zero]
  antitone _ _ h := AddSubgroup.comap_mono (Φ.antitone h)
  separated := by
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
    change (∀ i, e x ∈ Φ.F i) ↔ x = 0
    rw [← AddSubgroup.mem_iInf, Φ.separated]
    simp
  complete := by
    intro x hx
    have hx' : ∀ n, e (x (n + 1)) - e (x n) ∈ Φ.F n := by
      intro n
      rw [← map_sub]
      exact hx n
    obtain ⟨a, ha⟩ := Φ.complete (fun n => e (x n)) hx'
    refine ⟨e.symm a, ?_⟩
    intro n
    change e (e.symm a - x n) ∈ Φ.F n
    rw [map_sub, e.apply_symm_apply]
    exact ha n

private theorem gradeMapData :
    let M := stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)
    let Ψ := filtrationFromInverseLimit D.within D.within_zero D.within_succ_le
      D.within_separated D.inverseLimitEquiv D.inverseLimitEquiv_apply
    let Φ := filtrationComap Ψ (deepRepEquiv K L π D)
    ∀ n, ∃ q : Φ.F n →+ D.gradedRep n,
      Function.Surjective q ∧
      (∀ x, q x = 0 ↔ (x : M) ∈ Φ.F (n + 1)) ∧
      ∀ g (x : Φ.F n),
        q ⟨M.ρ g x, by
          change deepRepEquiv K L π D (M.ρ g x) ∈
            (D.within n).toAddSubgroup
          rw [deepRepEquiv_equivariant K L π D]
          change (⟨Units.map g.toRingEquiv.toRingHom
            ((Additive.toMul (deepRepEquiv K L π D x) : D.V 0) : Units L), _⟩ : D.V 0) ∈
              D.within n
          rw [D.within_eq_comap]
          apply D.V_stable n g
          have hx : deepRepEquiv K L π D x ∈ (D.within n).toAddSubgroup := x.2
          change Additive.toMul (deepRepEquiv K L π D x) ∈ D.within n at hx
          rw [D.within_eq_comap] at hx
          exact hx⟩ = (D.gradedRep n).ρ g (q x) := by
  dsimp only
  intro n
  let toLevel (x : (filtrationComap
      (filtrationFromInverseLimit D.within D.within_zero D.within_succ_le
        D.within_separated D.inverseLimitEquiv D.inverseLimitEquiv_apply)
      (deepRepEquiv K L π D)).F n) : D.V n :=
    ⟨((Additive.toMul (deepRepEquiv K L π D x) : D.V 0) : Units L), by
      have hx : Additive.toMul (deepRepEquiv K L π D x) ∈ D.within n := x.2
      rw [D.within_eq_comap] at hx
      exact hx⟩
  let q : (filtrationComap
      (filtrationFromInverseLimit D.within D.within_zero D.within_succ_le
        D.within_separated D.inverseLimitEquiv D.inverseLimitEquiv_apply)
      (deepRepEquiv K L π D)).F n →+ D.gradedRep n :=
    { toFun := fun x => (D.gradedRepEquiv n).symm
          (Additive.ofMul (QuotientGroup.mk (toLevel x)))
      map_zero' := by
        apply (D.gradedRepEquiv n).injective
        rw [AddEquiv.apply_symm_apply, map_zero]
        apply Additive.toMul.injective
        change (QuotientGroup.mk (toLevel 0) : D.V n ⧸
          (D.V (n + 1)).comap (D.V n).subtype) = 1
        rw [QuotientGroup.eq_one_iff]
        change ((toLevel 0 : D.V n) : Units L) ∈ D.V (n + 1)
        rw [show ((toLevel 0 : D.V n) : Units L) = 1 by rfl]
        exact (D.V (n + 1)).one_mem
      map_add' := by
        intro x y
        apply (D.gradedRepEquiv n).injective
        simp only [AddEquiv.apply_symm_apply, map_add]
        rfl }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro y
    let c := D.gradedRepEquiv n y
    let r : D.V n := Quotient.out (Additive.toMul c)
    have hr : Additive.ofMul (QuotientGroup.mk r) = c := by
      apply Additive.toMul.injective
      exact Quotient.out_eq _
    let x0 : D.V 0 := ⟨(r : Units L), D.V_antitone (Nat.zero_le n) r.2⟩
    let xm : stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0) :=
      (deepRepEquiv K L π D).symm (Additive.ofMul x0)
    have hxm : xm ∈ (filtrationComap
        (filtrationFromInverseLimit D.within D.within_zero D.within_succ_le
          D.within_separated D.inverseLimitEquiv D.inverseLimitEquiv_apply)
        (deepRepEquiv K L π D)).F n := by
      change Additive.ofMul x0 ∈ (D.within n).toAddSubgroup
      change x0 ∈ D.within n
      rw [D.within_eq_comap]
      exact r.2
    refine ⟨⟨xm, hxm⟩, ?_⟩
    apply (D.gradedRepEquiv n).injective
    change D.gradedRepEquiv n ((D.gradedRepEquiv n).symm
        (Additive.ofMul (QuotientGroup.mk (toLevel ⟨xm, hxm⟩)))) =
      D.gradedRepEquiv n y
    rw [AddEquiv.apply_symm_apply]
    change Additive.ofMul (QuotientGroup.mk (toLevel ⟨xm, hxm⟩)) = c
    rw [← hr]
    apply Additive.toMul.injective
    change QuotientGroup.mk (toLevel ⟨xm, hxm⟩) = QuotientGroup.mk r
    congr 1
  · intro x
    change (D.gradedRepEquiv n).symm
        (Additive.ofMul (QuotientGroup.mk (toLevel x))) = 0 ↔ _
    rw [AddEquiv.symm_apply_eq, map_zero]
    change (QuotientGroup.mk (toLevel x) : D.V n ⧸
      (D.V (n + 1)).comap (D.V n).subtype) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change ((toLevel x : D.V n) : Units L) ∈ D.V (n + 1) ↔ _
    change ((Additive.toMul (deepRepEquiv K L π D x) : D.V 0) : Units L) ∈
        D.V (n + 1) ↔
      deepRepEquiv K L π D x ∈ (D.within (n + 1)).toAddSubgroup
    rw [D.within_eq_comap]
    rfl
  · intro g x
    apply (D.gradedRepEquiv n).injective
    rw [D.gradedRepEquiv_equivariant]
    change D.gradedRepEquiv n ((D.gradedRepEquiv n).symm
        (Additive.ofMul (QuotientGroup.mk (toLevel ⟨_, _⟩)))) =
      D.gradedAction n g (D.gradedRepEquiv n ((D.gradedRepEquiv n).symm
        (Additive.ofMul (QuotientGroup.mk (toLevel x)))))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [D.gradedAction_mk]
    apply Additive.toMul.injective
    change QuotientGroup.mk (toLevel ⟨_, _⟩) =
      QuotientGroup.mk (⟨Units.map g.toRingEquiv.toRingHom (toLevel x : Units L), _⟩ : D.V n)
    congr 1



private theorem gradedStepH1
    {G : Type} [Group G] [Fintype G]
    {M N : Rep ℤ G} (Φ : CompleteSeparatedFiltration M)
    (stable : ∀ n g x, x ∈ Φ.F n → M.ρ g x ∈ Φ.F n)
    (n : ℕ) (q : Φ.F n →+ N)
    (qeq : ∀ g (x : Φ.F n),
      q ⟨M.ρ g x, stable n g x x.2⟩ = N.ρ g (q x))
    (qker : ∀ x : Φ.F n, q x = 0 ↔ (x : M) ∈ Φ.F (n + 1))
    (qsurj : Function.Surjective q)
    (hN : Subsingleton (Inhomogeneous.H1 N))
    (z : Inhomogeneous.C1 M) (hz : z ∈ Inhomogeneous.cocycles1 M)
    (hzF : ∀ g, z g ∈ Φ.F n) :
    ∃ b : M, b ∈ Φ.F n ∧
      ∀ g, (z - Inhomogeneous.d0 M b) g ∈ Φ.F (n + 1) := by
  let zN : Inhomogeneous.C1 N := fun g => q ⟨z g, hzF g⟩
  have hzN : zN ∈ Inhomogeneous.cocycles1 N := by
    constructor
    · change Inhomogeneous.d1 N zN = 0
      ext g h
      have hmem : M.ρ g (z h) - z (g * h) + z g ∈ Φ.F n :=
        (Φ.F n).add_mem ((Φ.F n).sub_mem (stable n g _ (hzF h)) (hzF (g * h))) (hzF g)
      calc
        Inhomogeneous.d1 N zN g h =
            q ⟨M.ρ g (z h) - z (g * h) + z g, hmem⟩ := by
              change N.ρ g (q ⟨z h, hzF h⟩) - q ⟨z (g * h), hzF (g * h)⟩ +
                q ⟨z g, hzF g⟩ = _
              rw [← qeq]
              rw [← map_sub, ← map_add]
              rfl
        _ = 0 := by
          have hh : M.ρ g (z h) - z (g * h) + z g = 0 :=
            congr_fun (congr_fun hz.1 g) h
          rw [show (⟨M.ρ g (z h) - z (g * h) + z g, hmem⟩ : Φ.F n) = 0 by
            apply Subtype.ext
            exact hh]
          exact q.map_zero
    · change zN 1 = 0
      change q ⟨z 1, hzF 1⟩ = 0
      rw [show (⟨z 1, hzF 1⟩ : Φ.F n) = 0 by
        apply Subtype.ext
        exact hz.2]
      exact q.map_zero
  let zNc : Inhomogeneous.cocycles1 N := ⟨zN, hzN⟩
  have hclass : (QuotientAddGroup.mk zNc : Inhomogeneous.H1 N) = 0 := hN.elim _ _
  obtain ⟨bN, hbN⟩ := (QuotientAddGroup.eq_zero_iff zNc).1 hclass
  obtain ⟨bF, hbF⟩ := qsurj bN
  refine ⟨bF, bF.2, ?_⟩
  intro g
  have hresmem : (z - Inhomogeneous.d0 M (bF : M)) g ∈ Φ.F n := by
    change z g - (M.ρ g bF - bF) ∈ Φ.F n
    exact (Φ.F n).sub_mem (hzF g) ((Φ.F n).sub_mem (stable n g _ bF.2) bF.2)
  apply (qker ⟨_, hresmem⟩).1
  change q ⟨z g - (M.ρ g bF - bF), hresmem⟩ = 0
  have hsub : (⟨z g - (M.ρ g bF - bF), hresmem⟩ : Φ.F n) =
      ⟨z g, hzF g⟩ -
        ⟨M.ρ g bF - bF, (Φ.F n).sub_mem (stable n g _ bF.2) bF.2⟩ := by rfl
  rw [hsub, map_sub]
  have hact : q ⟨M.ρ g bF, stable n g bF bF.2⟩ = N.ρ g bN := by
    rw [qeq, hbF]
  have hqb : q bF = bN := hbF
  rw [show q ⟨M.ρ g bF - bF, (Φ.F n).sub_mem (stable n g _ bF.2) bF.2⟩ =
      N.ρ g bN - bN by
        have heq : (⟨M.ρ g bF - bF,
            (Φ.F n).sub_mem (stable n g _ bF.2) bF.2⟩ : Φ.F n) =
            ⟨M.ρ g bF, stable n g _ bF.2⟩ - bF := by rfl
        rw [heq, map_sub, hact, hqb]]
  change zN g - Inhomogeneous.d0 N bN g = 0
  rw [congr_fun hbN g]
  change zN g - zN g = 0
  simp

private theorem gradedStepH2
    {G : Type} [Group G] [Fintype G]
    {M N : Rep ℤ G} (Φ : CompleteSeparatedFiltration M)
    (stable : ∀ n g x, x ∈ Φ.F n → M.ρ g x ∈ Φ.F n)
    (n : ℕ) (q : Φ.F n →+ N)
    (qeq : ∀ g (x : Φ.F n),
      q ⟨M.ρ g x, stable n g x x.2⟩ = N.ρ g (q x))
    (qker : ∀ x : Φ.F n, q x = 0 ↔ (x : M) ∈ Φ.F (n + 1))
    (qsurj : Function.Surjective q)
    (hN : Subsingleton (Inhomogeneous.H2 N))
    (z : Inhomogeneous.C2 M) (hz : z ∈ Inhomogeneous.cocycles2 M)
    (hzF : ∀ g h, z g h ∈ Φ.F n) :
    ∃ b : Inhomogeneous.C1 M, (∀ g, b g ∈ Φ.F n) ∧
      ∀ g h, (z - Inhomogeneous.d1 M b) g h ∈ Φ.F (n + 1) := by
  let zN : Inhomogeneous.C2 N := fun g h => q ⟨z g h, hzF g h⟩
  have hzN : zN ∈ Inhomogeneous.cocycles2 N := by
    constructor
    · change Inhomogeneous.d2 N zN = 0
      ext g h t
      have hmem : M.ρ g (z h t) - z (g * h) t + z g (h * t) - z g h ∈ Φ.F n :=
        (Φ.F n).sub_mem
          ((Φ.F n).add_mem
            ((Φ.F n).sub_mem (stable n g _ (hzF h t)) (hzF (g * h) t))
            (hzF g (h * t))) (hzF g h)
      calc
        Inhomogeneous.d2 N zN g h t =
            q ⟨M.ρ g (z h t) - z (g * h) t + z g (h * t) - z g h, hmem⟩ := by
              change N.ρ g (q ⟨z h t, hzF h t⟩) - q ⟨z (g * h) t, hzF (g * h) t⟩ +
                q ⟨z g (h * t), hzF g (h * t)⟩ - q ⟨z g h, hzF g h⟩ = _
              rw [← qeq]
              rw [← map_sub, ← map_add, ← map_sub]
              rfl
        _ = 0 := by
          have hh : M.ρ g (z h t) - z (g * h) t + z g (h * t) - z g h = 0 :=
            congr_fun (congr_fun (congr_fun hz.1 g) h) t
          rw [show (⟨M.ρ g (z h t) - z (g * h) t + z g (h * t) - z g h,
              hmem⟩ : Φ.F n) = 0 by
            apply Subtype.ext
            exact hh]
          exact q.map_zero
    · constructor
      · intro g
        change q ⟨z 1 g, hzF 1 g⟩ = 0
        rw [show (⟨z 1 g, hzF 1 g⟩ : Φ.F n) = 0 by
          apply Subtype.ext
          exact hz.2.1 g]
        exact q.map_zero
      · intro g
        change q ⟨z g 1, hzF g 1⟩ = 0
        rw [show (⟨z g 1, hzF g 1⟩ : Φ.F n) = 0 by
          apply Subtype.ext
          exact hz.2.2 g]
        exact q.map_zero
  let zNc : Inhomogeneous.cocycles2 N := ⟨zN, hzN⟩
  have hclass : (QuotientAddGroup.mk zNc : Inhomogeneous.H2 N) = 0 := hN.elim _ _
  obtain ⟨bN, hbN⟩ := (QuotientAddGroup.eq_zero_iff zNc).1 hclass
  choose bF hbF using fun g => qsurj (bN g)
  let b : Inhomogeneous.C1 M := fun g => bF g
  refine ⟨b, fun g => (bF g).2, ?_⟩
  intro g h
  have hd1mem : Inhomogeneous.d1 M b g h ∈ Φ.F n := by
    change M.ρ g (bF h : M) - bF (g * h) + bF g ∈ Φ.F n
    exact (Φ.F n).add_mem
      ((Φ.F n).sub_mem (stable n g _ (bF h).2) (bF (g * h)).2) (bF g).2
  have hresmem : (z - Inhomogeneous.d1 M b) g h ∈ Φ.F n :=
    (Φ.F n).sub_mem (hzF g h) hd1mem
  apply (qker ⟨_, hresmem⟩).1
  change q ⟨z g h - Inhomogeneous.d1 M b g h, hresmem⟩ = 0
  have hsub : (⟨z g h - Inhomogeneous.d1 M b g h, hresmem⟩ : Φ.F n) =
      ⟨z g h, hzF g h⟩ - ⟨Inhomogeneous.d1 M b g h, hd1mem⟩ := by rfl
  rw [hsub, map_sub]
  have hact : q ⟨M.ρ g (bF h : M), stable n g _ (bF h).2⟩ = N.ρ g (bN h) := by
    rw [qeq, hbF]
  have hd1q : q ⟨Inhomogeneous.d1 M b g h, hd1mem⟩ = Inhomogeneous.d1 N bN g h := by
    change q ⟨M.ρ g (bF h : M) - bF (g * h) + bF g, hd1mem⟩ = _
    have heq : (⟨M.ρ g (bF h : M) - bF (g * h) + bF g, hd1mem⟩ : Φ.F n) =
        (⟨M.ρ g (bF h : M), stable n g _ (bF h).2⟩ - bF (g * h)) + bF g := by rfl
    rw [heq, map_add, map_sub, hact, hbF, hbF]
    rfl
  rw [hd1q]
  change zN g h - Inhomogeneous.d1 N bN g h = 0
  rw [congr_fun (congr_fun hbN g) h]
  change zN g h - zN g h = 0
  simp


private theorem gradedH1Subsingleton (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] (n : ℕ) :
    Subsingleton (Inhomogeneous.H1 (Rep.res S.subtype (D.gradedRep n))) := by
  let ei := (Rep.resFunctor S.subtype).mapIso (D.gradedInducedIso n)
  let et := (tateCohomologyFunctor (1 : ℤ)).mapIso ei
  have hi := inducedFromTrivial_tateAcyclic (L ≃ₐ[K] L) (LocalResidueField K) S 1
  have ht : Subsingleton
      (tateCohomology (Rep.res S.subtype (D.gradedRep n)) 1) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective et.hom).1 inferInstance (hi.elim _ _)⟩
  let ec := (TateCohomology.isoGroupCohomology 1).app
    (Rep.res S.subtype (D.gradedRep n))
  have hc : Subsingleton
      (groupCohomology.H1 (Rep.res S.subtype (D.gradedRep n))) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective ec.inv).1 inferInstance (ht.elim _ _)⟩
  exact ⟨fun x y => (comparisonH1 _).injective (hc.elim _ _)⟩

private theorem gradedH2Subsingleton (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] (n : ℕ) :
    Subsingleton (Inhomogeneous.H2 (Rep.res S.subtype (D.gradedRep n))) := by
  let ei := (Rep.resFunctor S.subtype).mapIso (D.gradedInducedIso n)
  let et := (tateCohomologyFunctor (2 : ℤ)).mapIso ei
  have hi := inducedFromTrivial_tateAcyclic (L ≃ₐ[K] L) (LocalResidueField K) S 2
  have ht : Subsingleton
      (tateCohomology (Rep.res S.subtype (D.gradedRep n)) 2) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective et.hom).1 inferInstance (hi.elim _ _)⟩
  let ec := (TateCohomology.isoGroupCohomology 2).app
    (Rep.res S.subtype (D.gradedRep n))
  have hc : Subsingleton
      (groupCohomology.H2 (Rep.res S.subtype (D.gradedRep n))) :=
    ⟨fun x y => (ModuleCat.mono_iff_injective ec.inv).1 inferInstance (ht.elim _ _)⟩
  exact ⟨fun x y => (comparisonH2 _).injective (hc.elim _ _)⟩


private theorem assembleDeep (D : DeepUnitFiltrationData K L π) :
    AbstractReciprocity.CohomologicallyTrivial
      (stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)) := by
  let M := stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)
  let Ψ := filtrationFromInverseLimit D.within D.within_zero D.within_succ_le
    D.within_separated D.inverseLimitEquiv D.inverseLimitEquiv_apply
  let Φ := filtrationComap Ψ (deepRepEquiv K L π D)
  have stableFull : ∀ n g x, x ∈ Φ.F n → M.ρ g x ∈ Φ.F n := by
    intro n g x hx
    change deepRepEquiv K L π D (M.ρ g x) ∈ (D.within n).toAddSubgroup
    rw [deepRepEquiv_equivariant K L π D]
    change (⟨Units.map g.toRingEquiv.toRingHom
      ((Additive.toMul (deepRepEquiv K L π D x) : D.V 0) : Units L), _⟩ : D.V 0) ∈
        D.within n
    rw [D.within_eq_comap]
    apply D.V_stable n g
    have hx' : deepRepEquiv K L π D x ∈ (D.within n).toAddSubgroup := hx
    change Additive.toMul (deepRepEquiv K L π D x) ∈ D.within n at hx'
    rw [D.within_eq_comap] at hx'
    exact hx'
  apply AbstractReciprocity.cohomologicallyTrivial_of_H1_H2_zero M
  · intro S _
    have stableS : ∀ n g x, x ∈ Φ.F n → (Rep.res S.subtype M).ρ g x ∈ Φ.F n := by
      intro n g x hx
      exact stableFull n g x hx
    have hi : Subsingleton (Inhomogeneous.H1 (Rep.res S.subtype M)) :=
      CompleteSeparatedFiltration.serreApproximation_H1 Φ stableS (by
        intro n z hz hzF
        obtain ⟨q, hsurj, hker, heq⟩ := gradeMapData K L π D n
        apply gradedStepH1 (M := Rep.res S.subtype M)
          (N := Rep.res S.subtype (D.gradedRep n)) Φ stableS n q
        · intro g x
          exact heq g x
        · exact hker
        · exact hsurj
        · exact gradedH1Subsingleton K L π D S n
        · exact hz
        · exact hzF)
    exact ⟨fun x y => (comparisonH1 _).symm.injective (hi.elim _ _)⟩
  · intro S _
    have stableS : ∀ n g x, x ∈ Φ.F n → (Rep.res S.subtype M).ρ g x ∈ Φ.F n := by
      intro n g x hx
      exact stableFull n g x hx
    have hi : Subsingleton (Inhomogeneous.H2 (Rep.res S.subtype M)) :=
      CompleteSeparatedFiltration.serreApproximation_H2 Φ stableS (by
        intro n z hz hzF
        obtain ⟨q, hsurj, hker, heq⟩ := gradeMapData K L π D n
        apply gradedStepH2 (M := Rep.res S.subtype M)
          (N := Rep.res S.subtype (D.gradedRep n)) Φ stableS n q
        · intro g x
          exact heq g x
        · exact hker
        · exact hsurj
        · exact gradedH2Subsingleton K L π D S n
        · exact hz
        · exact hzF)
    exact ⟨fun x y => (comparisonH2 _).symm.injective (hi.elim _ _)⟩

end DeepUnitFiltrationAssembly

theorem deepUnitFiltration_exists (π : Uniformizer K) :
    ∃ D : DeepUnitFiltrationData K L π,
      AbstractReciprocity.CohomologicallyTrivial
        (stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)) := by
  obtain ⟨D⟩ := deepUnitFiltrationData_exists K L π
  exact ⟨D, assembleDeep K L π D⟩

end

end NU.LCFT
