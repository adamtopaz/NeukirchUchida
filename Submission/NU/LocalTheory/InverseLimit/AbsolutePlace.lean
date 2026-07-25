import Submission.NU.LocalTheory.InverseLimit.FiniteWitness

/-!
# Absolute places and the inverse-limit characterization

Compatible finite prime-ideal places are glued to a valuation subring of the
fixed algebraic closure.  Absolute decomposition groups are stabilizers of
that valuation subring.  The terminal theorem is Blueprint Theorem 8.7.
-/

open scoped NumberField Pointwise

namespace NU.LocalTheory

noncomputable section

/-- An absolute finite place: a nontrivial valuation subring of the fixed
algebraic closure whose restriction to `K` is one of the prime-ideal
valuation subrings. -/
def IsAbsoluteFinitePlace (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) : Prop :=
  W ≠ ⊤ ∧ ∃ v : FinitePlace K,
    W.comap (algebraMap K (AlgebraicClosure K)) = primeValuationSubring v

/-- The absolute decomposition group is definitionally the stabilizer of an
absolute valuation under `G_K`. -/
noncomputable def absoluteDecompositionGroup (K : Type*) [Field K]
    [NumberField K] (W : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) := by
  change Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
  exact MulAction.stabilizer
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W

/-- The collection of all absolute decomposition groups of finite places. -/
def absoluteDecompositionCollection (K : Type*) [Field K] [NumberField K] :
    Set (Subgroup (Field.absoluteGaloisGroup K)) :=
  {H | ∃ W : ValuationSubring (AlgebraicClosure K),
    IsAbsoluteFinitePlace K W ∧ H = absoluteDecompositionGroup K W}

/-- Compatibility of a family of finite prime-ideal places over nested
levels. -/
def IsCompatiblePlaceFamily {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (w : ∀ i, FinitePlace (Λ i).field) : Prop :=
  ∀ i j (hij : (Λ i).LE (Λ j)),
    restrictLevelPlace hij (w j) = w i

private theorem primeValuationSubring_comap_restrict
    (K : Type*) {L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : FinitePlace L) :
    (primeValuationSubring w).comap (algebraMap K L) =
      primeValuationSubring (restrictFinitePlace K w) := by
  let v := restrictFinitePlace K w
  have hle : primeValuationSubring v ≤
      (primeValuationSubring w).comap (algebraMap K L) := by
    intro x hx
    rw [mem_primeValuationSubring_iff] at hx
    rw [ValuationSubring.mem_comap, mem_primeValuationSubring_iff]
    obtain ⟨a, b, hb, hab⟩ := hx
    refine ⟨algebraMap (𝓞 K) (𝓞 L) a,
      algebraMap (𝓞 K) (𝓞 L) b, ?_, ?_⟩
    · intro hbw
      apply hb
      change b ∈ (restrictFinitePlace K w).asIdeal
      exact hbw
    · have hcoe (c : 𝓞 K) :
          ((algebraMap (𝓞 K) (𝓞 L) c : 𝓞 L) : L) =
            algebraMap K L (c : K) := by
        calc
          _ = algebraMap (𝓞 K) L c :=
            (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L c).symm
          _ = algebraMap K L (c : K) :=
            IsScalarTower.algebraMap_apply (𝓞 K) K L c
      rw [hcoe, hcoe, ← map_mul, hab]
  have hne : (primeValuationSubring w).comap (algebraMap K L) ≠ ⊤ := by
    obtain ⟨a, ha, ha0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have haw : algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal := ha
    have hlt : w.valuation L
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) < 1 :=
      (w.valuation_lt_one_iff_mem
        (algebraMap (𝓞 K) (𝓞 L) a)).2 haw
    have hmap0 : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).2 (by exact_mod_cast ha0)
    have hpos : 0 < w.valuation L (algebraMap K L (a : K)) :=
      (w.valuation L).pos_iff.mpr hmap0
    have hcoe :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) =
          algebraMap K L (a : K) := by
      calc
        _ = algebraMap (𝓞 K) L a :=
          (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a).symm
        _ = algebraMap K L (a : K) :=
          IsScalarTower.algebraMap_apply (𝓞 K) K L a
    rw [hcoe] at hlt
    have hinv : 1 < (w.valuation L (algebraMap K L (a : K)))⁻¹ :=
      (one_lt_inv₀ hpos).2 hlt
    intro htop
    have hz : (a : K)⁻¹ ∈
        (primeValuationSubring w).comap (algebraMap K L) := by
      rw [htop]
      trivial
    rw [ValuationSubring.mem_comap, primeValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hz
    rw [map_inv₀, Valuation.map_inv] at hz
    exact (not_le_of_gt hinv) hz
  letI : Ring.KrullDimLE 1 (primeValuationSubring v) := by
    change Ring.KrullDimLE 1
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  exact (ValuationSubring.eq_of_le_of_ne_top
    (primeValuationSubring v) hle hne).symm

private theorem exists_galoisLevel_mem
    {K : Type*} [Field K] [NumberField K]
    (x : AlgebraicClosure K) : ∃ L : GaloisLevel K, x ∈ L.field := by
  let A : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {x}
  letI : FiniteDimensional K A :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
  let Nfield : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.normalClosure K A (AlgebraicClosure K)
  letI : IsGalois K (AlgebraicClosure K) := by infer_instance
  let N : GaloisLevel K :=
    { field := Nfield
      finiteDimensional := normalClosure.is_finiteDimensional K A
        (AlgebraicClosure K)
      numberField := NumberField.of_module_finite K _
      isGalois := IsGalois.normalClosure K A (AlgebraicClosure K) }
  refine ⟨N, IntermediateField.le_normalClosure A ?_⟩
  exact IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)

/-- Blueprint (8.4), `eq:union-valuation-ring`: a compatible cofinal family
of localizations glues to a valuation subring of the algebraic closure, with
the displayed restriction equations. -/
theorem exists_union_valuationSubring
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (w : ∀ i, FinitePlace (Λ i).field)
    (hw : IsCompatiblePlaceFamily Λ w) :
    ∃ W : ValuationSubring (AlgebraicClosure K),
      ∀ i,
        W.comap (Λ i).field.val.toRingHom =
          primeValuationSubring (w i) := by
  have hmem_iff_of_le {i j : ι} (hij : (Λ i).LE (Λ j))
      (x : AlgebraicClosure K) (hxi : x ∈ (Λ i).field) :
      (⟨x, hxi⟩ : (Λ i).field) ∈ primeValuationSubring (w i) ↔
        (⟨x, hij hxi⟩ : (Λ j).field) ∈
          primeValuationSubring (w j) := by
    letI : Algebra (Λ i).field (Λ j).field :=
      (IntermediateField.inclusion hij).toAlgebra
    have hcomap := primeValuationSubring_comap_restrict
      (Λ i).field (w j)
    rw [show restrictFinitePlace (Λ i).field (w j) =
      restrictLevelPlace hij (w j) from rfl, hw i j hij] at hcomap
    have hiff := ValuationSubring.ext_iff.mp hcomap ⟨x, hxi⟩
    rw [ValuationSubring.mem_comap] at hiff
    have heq : algebraMap (Λ i).field (Λ j).field ⟨x, hxi⟩ =
        (⟨x, hij hxi⟩ : (Λ j).field) := by
      apply Subtype.ext
      rfl
    rw [heq] at hiff
    exact hiff.symm
  let U : Set (AlgebraicClosure K) :=
    {x | ∃ i, ∃ hxi : x ∈ (Λ i).field,
      (⟨x, hxi⟩ : (Λ i).field) ∈ primeValuationSubring (w i)}
  let R : Subring (AlgebraicClosure K) :=
    { carrier := U
      zero_mem' := by
        let i := Classical.choice hΛ.1
        exact ⟨i, (Λ i).field.zero_mem, zero_mem _⟩
      one_mem' := by
        let i := Classical.choice hΛ.1
        exact ⟨i, (Λ i).field.one_mem, one_mem _⟩
      add_mem' := by
        rintro x y ⟨i, hxi, hx⟩ ⟨j, hyj, hy⟩
        obtain ⟨k, hik, hjk⟩ := hΛ.2.1 i j
        have hxk := (hmem_iff_of_le hik x hxi).mp hx
        have hyk := (hmem_iff_of_le hjk y hyj).mp hy
        refine ⟨k, (Λ k).field.add_mem (hik hxi) (hjk hyj), ?_⟩
        simpa using add_mem hxk hyk
      mul_mem' := by
        rintro x y ⟨i, hxi, hx⟩ ⟨j, hyj, hy⟩
        obtain ⟨k, hik, hjk⟩ := hΛ.2.1 i j
        have hxk := (hmem_iff_of_le hik x hxi).mp hx
        have hyk := (hmem_iff_of_le hjk y hyj).mp hy
        refine ⟨k, (Λ k).field.mul_mem (hik hxi) (hjk hyj), ?_⟩
        simpa using mul_mem hxk hyk
      neg_mem' := by
        rintro x ⟨i, hxi, hx⟩
        refine ⟨i, (Λ i).field.neg_mem hxi, ?_⟩
        have hneg := (primeValuationSubring (w i)).neg_mem
          (⟨x, hxi⟩ : (Λ i).field) hx
        have heq : -(⟨x, hxi⟩ : (Λ i).field) =
            (⟨-x, (Λ i).field.neg_mem hxi⟩ : (Λ i).field) := by
          apply Subtype.ext
          rfl
        rwa [heq] at hneg }
  let W : ValuationSubring (AlgebraicClosure K) :=
    { toSubring := R
      mem_or_inv_mem' := by
        intro x
        obtain ⟨N, hxN⟩ := exists_galoisLevel_mem x
        obtain ⟨i, hNi⟩ := hΛ.2.2 N
        let xi : (Λ i).field := ⟨x, hNi hxN⟩
        rcases (primeValuationSubring (w i)).mem_or_inv_mem xi with hx | hx
        · exact Or.inl ⟨i, hNi hxN, hx⟩
        · refine Or.inr ⟨i, (Λ i).field.inv_mem (hNi hxN), ?_⟩
          have heq : xi⁻¹ =
              (⟨x⁻¹, (Λ i).field.inv_mem (hNi hxN)⟩ : (Λ i).field) := by
            apply Subtype.ext
            rfl
          rwa [← heq] }
  refine ⟨W, ?_⟩
  intro i
  apply ValuationSubring.ext
  intro x
  change (x : AlgebraicClosure K) ∈ U ↔
    x ∈ primeValuationSubring (w i)
  constructor
  · rintro ⟨j, hxj, hx⟩
    obtain ⟨k, hik, hjk⟩ := hΛ.2.1 i j
    have hxk := (hmem_iff_of_le hjk (x : AlgebraicClosure K) hxj).mp hx
    have hxi : (x : AlgebraicClosure K) ∈ (Λ i).field := x.property
    exact (hmem_iff_of_le hik (x : AlgebraicClosure K) hxi).mpr hxk
  · intro hx
    exact ⟨i, x.property, hx⟩

/-- The union valuation ring selected from the preceding existence theorem. -/
noncomputable def unionValuationSubring
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (w : ∀ i, FinitePlace (Λ i).field)
    (hw : IsCompatiblePlaceFamily Λ w) :
    ValuationSubring (AlgebraicClosure K) :=
  (exists_union_valuationSubring Λ hΛ w hw).choose

@[simp]
theorem unionValuationSubring_restrict
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (w : ∀ i, FinitePlace (Λ i).field)
    (hw : IsCompatiblePlaceFamily Λ w) (i : ι) :
    (unionValuationSubring Λ hΛ w hw).comap
        (Λ i).field.val.toRingHom = primeValuationSubring (w i) :=
  (exists_union_valuationSubring Λ hΛ w hw).choose_spec i

/-- Restricting an absolute finite place to any finite Galois level remains
a nontrivial valuation. -/
theorem absolutePlace_comap_nontrivial
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) (L : GaloisLevel K) :
    IsNontrivialValuation (W.comap L.field.val.toRingHom) := by
  obtain ⟨_, v, hbase⟩ := hW
  intro htop
  apply primeValuationSubring_ne_top v
  rw [← hbase]
  have hcomp : W.comap (algebraMap K (AlgebraicClosure K)) =
      (W.comap L.field.val.toRingHom).comap (algebraMap K L.field) := by
    apply ValuationSubring.ext
    intro x
    rfl
  rw [hcomp, htop]
  rfl

/-- The prime-ideal place obtained by restricting an absolute place to a
finite Galois level. -/
noncomputable def absolutePlaceAtLevel
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) (L : GaloisLevel K) :
    FinitePlace L.field :=
  centerFinitePlace (W.comap L.field.val.toRingHom)
    (absolutePlace_comap_nontrivial W hW L)

private theorem absolutePlaceAtLevel_restrict_base
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) (L : GaloisLevel K)
    (v : FinitePlace K)
    (hbase : W.comap (algebraMap K (AlgebraicClosure K)) =
      primeValuationSubring v) :
    restrictFinitePlace K (absolutePlaceAtLevel W hW L) = v := by
  let w := absolutePlaceAtLevel W hW L
  have hw : primeValuationSubring w =
      W.comap L.field.val.toRingHom :=
    primeValuationSubring_centerFinitePlace _ _
  have hrest : primeValuationSubring (restrictFinitePlace K w) =
      primeValuationSubring v := by
    calc
      primeValuationSubring (restrictFinitePlace K w) =
          (primeValuationSubring w).comap (algebraMap K L.field) :=
        (primeValuationSubring_comap_restrict K w).symm
      _ = (W.comap L.field.val.toRingHom).comap
          (algebraMap K L.field) := by rw [hw]
      _ = W.comap (algebraMap K (AlgebraicClosure K)) := by
        apply ValuationSubring.ext
        intro x
        rfl
      _ = primeValuationSubring v := hbase
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
    (K := K)
  apply (Valuation.isEquiv_iff_valuationSubring _ _).2
  simpa only [w, primeValuationSubring,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    using hrest

private theorem ringOfIntegers_le_valuationSubring
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    ∀ a : 𝓞 F, (a : F) ∈ A := by
  intro a
  apply (Subring.isIntegrallyClosed_iff.mp
    (inferInstance : IsIntegrallyClosed A))
  exact a.2.tower_top

private def valuationIntegralCenter
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal A).comap
    ((algebraMap (𝓞 F) F).codRestrict A
      (ringOfIntegers_le_valuationSubring A))

private instance valuationIntegralCenter_isPrime
    {F : Type*} [Field F] [CharZero F] (A : ValuationSubring F) :
    (valuationIntegralCenter A).IsPrime :=
  (IsLocalRing.maximalIdeal A).comap_isPrime _

private theorem valuationIntegralCenter_primeValuationSubring
    {F : Type*} [Field F] [NumberField F] (v : FinitePlace F) :
    valuationIntegralCenter (primeValuationSubring v) = v.asIdeal := by
  change valuationIntegralCenter
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) = v.asIdeal
  apply Ideal.ext
  intro x
  change (⟨(x : F), ringOfIntegers_le_valuationSubring
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) x⟩ :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) ∈
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) ↔
          x ∈ v.asIdeal
  rw [show (⟨(x : F), ringOfIntegers_le_valuationSubring
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) x⟩ :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) =
      algebraMap (𝓞 F)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v) x by
    apply Subtype.ext
    rfl]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v)
      v.asIdeal x

private def valuationComapMap
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : A.comap f →+* A where
  toFun x := ⟨f x, x.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

private theorem valuationComapMap_isLocal
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : IsLocalHom (valuationComapMap f A) := by
  apply IsLocalHom.mk
  intro x hx
  have hfx0 : f (x : F) ≠ 0 := by
    intro hzero
    apply IsUnit.ne_zero hx
    apply Subtype.ext
    exact hzero
  have hx0 : (x : F) ≠ 0 := (map_ne_zero f).mp hfx0
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hyval : (y : E) = (f (x : F))⁻¹ := by
    apply (mul_left_cancel₀ hfx0)
    have hy' := congrArg Subtype.val hy
    change f (x : F) * (y : E) = 1 at hy'
    rw [hy', mul_inv_cancel₀ hfx0]
  let y' : A.comap f := ⟨(x : F)⁻¹, by
    change f ((x : F)⁻¹) ∈ A
    rw [map_inv₀, ← hyval]
    exact y.property⟩
  exact isUnit_iff_exists_inv.mpr ⟨y', by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0⟩

private theorem valuationIntegralCenter_comap
    {F E : Type*} [Field F] [Field E] [CharZero F] [CharZero E]
    (f : F →+* E) (A : ValuationSubring E) :
    valuationIntegralCenter (A.comap f) =
      (valuationIntegralCenter A).comap
        (NumberField.RingOfIntegers.mapRingHom f) := by
  letI : IsLocalHom (valuationComapMap f A) :=
    valuationComapMap_isLocal f A
  apply Ideal.ext
  intro x
  change (⟨(x : F), ringOfIntegers_le_valuationSubring
      (A.comap f) x⟩ : A.comap f) ∈
        IsLocalRing.maximalIdeal (A.comap f) ↔
    (⟨f (x : F), ringOfIntegers_le_valuationSubring A
      (NumberField.RingOfIntegers.mapRingHom f x)⟩ : A) ∈
        IsLocalRing.maximalIdeal A
  have hm := IsLocalRing.maximalIdeal_comap (valuationComapMap f A)
  have hx := (Ideal.ext_iff.mp hm
    ⟨(x : F), ringOfIntegers_le_valuationSubring (A.comap f) x⟩).symm
  change _ ↔ valuationComapMap f A
    ⟨(x : F), ringOfIntegers_le_valuationSubring (A.comap f) x⟩ ∈
      IsLocalRing.maximalIdeal A at hx
  exact hx

private def valuationSubringSmulEquiv
    {G F : Type*} [Group G] [Field F] [MulSemiringAction G F]
    (g : G) (A : ValuationSubring F) : A ≃+* (g • A : ValuationSubring F) where
  toFun x := ⟨g • (x : F),
    ValuationSubring.smul_mem_pointwise_smul g (x : F) A x.property⟩
  invFun x := ⟨g⁻¹ • (x : F),
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)
  map_mul' x y := by ext; exact MulSemiringAction.smul_mul g (x : F) (y : F)

private theorem valuationIntegralCenter_smul
    {G F : Type*} [Group G] [Field F] [CharZero F]
    [MulSemiringAction G F] (g : G) (A : ValuationSubring F) :
    valuationIntegralCenter (g • A) = g • valuationIntegralCenter A := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change (⟨(x : F), ringOfIntegers_le_valuationSubring (g • A) x⟩ :
      (g • A : ValuationSubring F)) ∈
        IsLocalRing.maximalIdeal (g • A : ValuationSubring F) ↔
    (⟨((g⁻¹ • x : 𝓞 F) : F),
      ringOfIntegers_le_valuationSubring A (g⁻¹ • x)⟩ : A) ∈
        IsLocalRing.maximalIdeal A
  simp only [IsLocalRing.mem_maximalIdeal]
  apply not_congr
  let e := valuationSubringSmulEquiv g A
  let y : A := ⟨((g⁻¹ • x : 𝓞 F) : F),
    ringOfIntegers_le_valuationSubring A (g⁻¹ • x)⟩
  have he := isUnit_map_iff e y
  have hey : e y = (⟨(x : F),
      ringOfIntegers_le_valuationSubring (g • A) x⟩ :
        (g • A : ValuationSubring F)) := by
    apply Subtype.ext
    change g • (g⁻¹ • (x : F)) = (x : F)
    simp
  rw [← hey]
  exact he

private theorem isUnit_mk_valuationSubring_iff
    {F : Type*} [Field F] (A : ValuationSubring F) (x : F) (hx : x ∈ A) :
    IsUnit (⟨x, hx⟩ : A) ↔ x ≠ 0 ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have hy' := congrArg Subtype.val hy
    change x * (y : F) = 1 at hy'
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hy'
      exact zero_ne_one hy'
    refine ⟨hx0, ?_⟩
    have heq : (y : F) = x⁻¹ := by
      apply (mul_left_cancel₀ hx0)
      rw [hy', mul_inv_cancel₀ hx0]
    rw [← heq]
    exact y.property
  · rintro ⟨hx0, hinv⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

private theorem valuationSubring_eq_of_integralCenter_eq
    (K : Type*) {F : Type*} [Field K] [NumberField K]
    [Field F] [CharZero F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (A B : ValuationSubring F)
    (hA : A.comap (algebraMap K F) ≠ ⊤)
    (hB : B.comap (algebraMap K F) ≠ ⊤)
    (hcenter : valuationIntegralCenter A = valuationIntegralCenter B) :
    A = B := by
  apply ValuationSubring.ext
  intro x
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  letI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin (S := {x})
      (fun y _ => Algebra.IsIntegral.isIntegral y)
  letI : NumberField L := NumberField.of_module_finite K L
  let AL : ValuationSubring L := A.comap L.val.toRingHom
  let BL : ValuationSubring L := B.comap L.val.toRingHom
  have hAL : AL ≠ ⊤ := by
    intro htop
    apply hA
    apply ValuationSubring.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      have hy : algebraMap K L y ∈ AL := by rw [htop]; trivial
      exact hy
  have hBL : BL ≠ ⊤ := by
    intro htop
    apply hB
    apply ValuationSubring.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      have hy : algebraMap K L y ∈ BL := by rw [htop]; trivial
      exact hy
  obtain ⟨v, hv, _⟩ := numberField_valuations AL hAL
  obtain ⟨w, hw, _⟩ := numberField_valuations BL hBL
  have hcenterL : valuationIntegralCenter AL = valuationIntegralCenter BL := by
    dsimp only [AL, BL]
    rw [valuationIntegralCenter_comap,
      valuationIntegralCenter_comap, hcenter]
  have hvw : v = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [← valuationIntegralCenter_primeValuationSubring v,
      ← valuationIntegralCenter_primeValuationSubring w,
      ← hv, ← hw, hcenterL]
  have hAB : AL = BL := by rw [hv, hw, hvw]
  let y : L := ⟨x, IntermediateField.subset_adjoin K {x}
    (Set.mem_singleton x)⟩
  have hy := ValuationSubring.ext_iff.mp hAB y
  exact hy

private theorem exists_smul_of_valuationSubring_comap_eq
    (K : Type*) {F : Type*} [Field K] [NumberField K]
    [Field F] [CharZero F] [Algebra K F] [Algebra.IsAlgebraic K F]
    [IsAlgClosed F] (Z : IntermediateField K F)
    (A B : ValuationSubring F)
    (hA : A.comap (algebraMap K F) ≠ ⊤)
    (hB : B.comap (algebraMap K F) ≠ ⊤)
    (hcomap : A.comap Z.val.toRingHom = B.comap Z.val.toRingHom) :
    ∃ σ : Gal(F / Z), B = σ • A := by
  letI : IsAlgClosure Z F := IsAlgClosure.mk inferInstance inferInstance
  letI : Normal Z F := IsAlgClosure.normal Z F
  letI : IsGalois Z F := IsGalois.mk
  let R := 𝓞 F
  let G := Gal(F / Z)
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : ContinuousSMul G R :=
    continuousSMul_iff_stabilizer_isOpen.mpr fun x => by
      have hx := stabilizer_isOpen_of_isIntegral (K := Z) (x : F)
      have heq : (MulAction.stabilizer G x : Set G) =
          (MulAction.stabilizer Gal(F / Z) (x : F) : Set Gal(F / Z)) := by
        ext g
        change (g • x = x) ↔ (g • (x : F) = (x : F))
        constructor
        · exact fun h => congrArg Subtype.val h
        · intro h
          apply Subtype.ext
          exact h
      rw [heq]
      exact hx
  let R₀ := FixedPoints.subring R G
  letI : Algebra R₀ R := (Subring.subtype R₀).toAlgebra
  letI : SMulCommClass G R₀ R :=
    { smul_comm := fun g a x => by
        change g • ((a : R) * x) = (a : R) * (g • x)
        calc
          _ = (g • (a : R)) * (g • x) :=
            MulSemiringAction.smul_mul g (a : R) x
          _ = _ := by rw [a.property g] }
  letI : Algebra.IsInvariant R₀ R G :=
    { isInvariant := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }
  let P : Ideal R := valuationIntegralCenter A
  let Q : Ideal R := valuationIntegralCenter B
  have hunder : P.under R₀ = Q.under R₀ := by
    apply Ideal.ext
    intro x
    let xf : F := ((x : R) : F)
    have hfixed : ∀ g : G, g xf = xf := by
      intro g
      have hx := congrArg Subtype.val (x.property g)
      exact hx
    obtain ⟨z, hz⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed xf).mpr hfixed
    have hinv := ValuationSubring.ext_iff.mp hcomap z⁻¹
    change algebraMap Z F z⁻¹ ∈ A ↔ algebraMap Z F z⁻¹ ∈ B at hinv
    rw [map_inv₀, hz] at hinv
    change (⟨xf, ringOfIntegers_le_valuationSubring A (x : R)⟩ : A) ∈
        IsLocalRing.maximalIdeal A ↔
      (⟨xf, ringOfIntegers_le_valuationSubring B (x : R)⟩ : B) ∈
        IsLocalRing.maximalIdeal B
    simp only [IsLocalRing.mem_maximalIdeal]
    apply not_congr
    rw [isUnit_mk_valuationSubring_iff,
      isUnit_mk_valuationSubring_iff]
    exact and_congr_right (fun _ => hinv)
  obtain ⟨σ, hσ⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (G := G) (A := R₀) (B := R) P Q hunder
  have hcenter : valuationIntegralCenter (σ • A) =
      valuationIntegralCenter B := by
    rw [valuationIntegralCenter_smul, ← hσ]
  have hσA : (σ • A).comap (algebraMap K F) ≠ ⊤ := by
    have heq : (σ • A).comap (algebraMap K F) =
        A.comap (algebraMap K F) := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hfix : σ⁻¹ (algebraMap K F x) = algebraMap K F x := by
        calc
          σ⁻¹ (algebraMap K F x) =
              σ⁻¹ (algebraMap Z F (algebraMap K Z x)) := by rfl
          _ = algebraMap Z F (algebraMap K Z x) := σ⁻¹.commutes _
          _ = algebraMap K F x := by rfl
      rw [AlgEquiv.smul_def, hfix]
    rwa [heq]
  have heq := valuationSubring_eq_of_integralCenter_eq K (σ • A) B
    hσA hB hcenter
  exact ⟨σ, heq.symm⟩

private theorem mem_primeValuationSubring_automorphism
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (σ : M ≃ₐ[K] M) (w : FinitePlace M) (x : M) :
    x ∈ primeValuationSubring w ↔
      σ x ∈ primeValuationSubring (conjugateFinitePlace K σ w) := by
  rw [mem_primeValuationSubring_iff, mem_primeValuationSubring_iff]
  constructor
  · rintro ⟨a, b, hb, h⟩
    refine ⟨σ • a, σ • b, ?_, ?_⟩
    · simpa [conjugateFinitePlace_asIdeal] using hb
    · change σ x * σ (b : M) = σ (a : M)
      simpa only [map_mul] using congrArg σ h
  · rintro ⟨a, b, hb, h⟩
    refine ⟨σ⁻¹ • a, σ⁻¹ • b, ?_, ?_⟩
    · intro hmem
      apply hb
      rw [conjugateFinitePlace_asIdeal,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact hmem
    · have hh := congrArg σ.symm h
      change x * σ.symm (b : M) = σ.symm (a : M)
      simpa only [map_mul, AlgEquiv.symm_apply_apply] using hh

/-- An absolute decomposition group maps onto the finite decomposition group
of its restricted place. -/
theorem absoluteDecompositionGroup_finiteImage
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) (L : GaloisLevel K) :
    finiteLevelImage L (absoluteDecompositionGroup K W) =
      decompositionGroup K (absolutePlaceAtLevel W hW L) := by
  let A := W.comap L.field.val.toRingHom
  let v := absolutePlaceAtLevel W hW L
  have hA : IsNontrivialValuation A :=
    absolutePlace_comap_nontrivial W hW L
  have hlevel : primeValuationSubring v = A :=
    primeValuationSubring_centerFinitePlace A hA
  apply le_antisymm
  · rintro σ ⟨g, hg, rfl⟩
    letI := finitePlaceAction K L.field
    change conjugateFinitePlace K (absoluteRestriction L g) v = v
    have hgW :
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) • W = W := by
      exact (MulAction.mem_stabilizer_iff.mp hg)
    have hpres (x : L.field) : x ∈ A ↔ absoluteRestriction L g x ∈ A := by
      change (x : AlgebraicClosure K) ∈ W ↔
        ((absoluteRestriction L g x : L.field) : AlgebraicClosure K) ∈ W
      rw [absoluteRestriction_apply]
      have hs := ValuationSubring.smul_mem_pointwise_smul_iff
        (g := (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g))
        (S := W) (x := (x : AlgebraicClosure K))
      rw [hgW] at hs
      exact hs.symm
    have hconjlevel :
        primeValuationSubring
          (conjugateFinitePlace K (absoluteRestriction L g) v) = A := by
      apply ValuationSubring.ext
      intro x
      have hm := mem_primeValuationSubring_automorphism
        K L.field (absoluteRestriction L g) v
          ((absoluteRestriction L g)⁻¹ x)
      have hm' :
          (absoluteRestriction L g)⁻¹ x ∈ primeValuationSubring v ↔
            x ∈ primeValuationSubring
              (conjugateFinitePlace K (absoluteRestriction L g) v) := by
        simpa using hm
      have hp : (absoluteRestriction L g)⁻¹ x ∈ A ↔ x ∈ A := by
        simpa using hpres ((absoluteRestriction L g)⁻¹ x)
      constructor
      · intro hx
        have hxv := hm'.mpr hx
        rw [hlevel] at hxv
        exact hp.mp hxv
      · intro hx
        apply hm'.mp
        rw [hlevel]
        exact hp.mpr hx
    have hu := numberField_valuations A hA
    exact (hu.choose_spec.2 _ hconjlevel.symm).trans
      (hu.choose_spec.2 v hlevel.symm).symm
  · intro σ hσ
    letI := finitePlaceAction K L.field
    change conjugateFinitePlace K σ v = v at hσ
    obtain ⟨τE, hτE⟩ := AlgEquiv.restrictNormalHom_surjective
      (AlgebraicClosure K) σ
    let τ : Field.absoluteGaloisGroup K := τE
    have hτ : absoluteRestriction L τ = σ := hτE
    have hpres (x : L.field) : x ∈ A ↔ σ x ∈ A := by
      have hm := mem_primeValuationSubring_automorphism K L.field σ v x
      rw [hσ, hlevel] at hm
      exact hm
    have hτcomap : (τE • W).comap L.field.val.toRingHom = A := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_comap,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      have hinv : absoluteRestriction L τ⁻¹ = σ⁻¹ := by
        rw [map_inv, hτ]
      have he := DFunLike.congr_fun hinv x
      have he' := congrArg Subtype.val he
      rw [absoluteRestriction_apply] at he'
      have hleft :
          (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from τ⁻¹)
              (x : AlgebraicClosure K) ∈ W ↔ (σ⁻¹ x) ∈ A := by
        change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from τ⁻¹)
              (x : AlgebraicClosure K) ∈ W ↔
          ((σ⁻¹ x : L.field) : AlgebraicClosure K) ∈ W
        exact iff_of_eq (congrArg (fun z => z ∈ W) he')
      exact hleft.trans ((hpres (σ⁻¹ x)).trans (by simp))
    obtain ⟨vK, hvK⟩ := hW.2
    have hWbase : W.comap (algebraMap K (AlgebraicClosure K)) ≠ ⊤ := by
      rw [hvK]
      exact primeValuationSubring_ne_top vK
    have hτbase : (τE • W).comap
        (algebraMap K (AlgebraicClosure K)) =
          W.comap (algebraMap K (AlgebraicClosure K)) := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change τE⁻¹ (algebraMap K (AlgebraicClosure K) x) ∈ W ↔
        algebraMap K (AlgebraicClosure K) x ∈ W
      rw [show τE⁻¹ (algebraMap K (AlgebraicClosure K) x) =
        algebraMap K (AlgebraicClosure K) x from τE⁻¹.commutes x]
    have hτnontrivial : (τE • W).comap
        (algebraMap K (AlgebraicClosure K)) ≠ ⊤ := by
      rwa [hτbase]
    obtain ⟨δ, hδ⟩ := exists_smul_of_valuationSubring_comap_eq
      K L.field W (τE • W) hWbase hτnontrivial
        (show W.comap L.field.val.toRingHom =
          (τE • W).comap L.field.val.toRingHom from hτcomap.symm)
    let δK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
      δ.restrictScalars K
    have hδK : τE • W = δK • W := hδ
    let d : Field.absoluteGaloisGroup K := δK
    let g : Field.absoluteGaloisGroup K := d⁻¹ * τ
    have hg : g ∈ absoluteDecompositionGroup K W := by
      change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) ∈
        MulAction.stabilizer
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W
      rw [MulAction.mem_stabilizer_iff]
      change (δK⁻¹ *
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from τ)) • W = W
      rw [mul_smul, hδK]
      simp
    refine ⟨g, hg, ?_⟩
    have hδres : absoluteRestriction L d = 1 := by
      ext x
      rw [absoluteRestriction_apply]
      exact δ.commutes x
    change absoluteRestriction L g = σ
    rw [show g = d⁻¹ * τ by rfl, map_mul, map_inv, hδres, hτ]
    simp

private theorem subgroup_le_of_cofinal_images
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (A B : Subgroup (Field.absoluteGaloisGroup K))
    (hB : IsClosed (B : Set (Field.absoluteGaloisGroup K)))
    (himages : ∀ i, finiteLevelImage (Λ i) A ≤ finiteLevelImage (Λ i) B) :
    A ≤ B := by
  intro g hg
  change g ∈ (B : Set (Field.absoluteGaloisGroup K))
  rw [← hB.closure_eq]
  rw [mem_closure_iff_nhds_one]
  intro U hU
  obtain ⟨E, hEfin, hEnormal, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K
      (AlgebraicClosure K) U).mp hU
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
  have hgimage : absoluteRestriction (Λ i) g ∈ finiteLevelImage (Λ i) A :=
    ⟨g, hg, rfl⟩
  obtain ⟨b, hb, hbg⟩ := himages i hgimage
  refine ⟨b, hb, hEU ?_⟩
  apply E.fixingSubgroup_antitone hi
  rw [← IntermediateField.restrictNormalHom_ker]
  change absoluteRestriction (Λ i) (b / g) = 1
  rw [map_div, hbg]
  simp

/-- Blueprint Lemma 8.5 (`lem:closed-images`): closed subgroups of a
profinite group are determined by their images in a cofinal family of finite
Galois quotients. -/
theorem closed_subgroups_eq_of_cofinal_images
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (A B : Subgroup (Field.absoluteGaloisGroup K))
    (hA : IsClosed (A : Set (Field.absoluteGaloisGroup K)))
    (hB : IsClosed (B : Set (Field.absoluteGaloisGroup K)))
    (himages : ∀ i, finiteLevelImage (Λ i) A = finiteLevelImage (Λ i) B) :
    A = B := by
  apply le_antisymm
  · exact subgroup_le_of_cofinal_images Λ hΛ A B hB
      (fun i => (himages i).le)
  · exact subgroup_le_of_cofinal_images Λ hΛ B A hA
      (fun i => (himages i).ge)

open Polynomial in
private theorem monic_natDegree_two_eq
    {F : Type*} [Field F] (q : F[X]) (hq : q.Monic)
    (hdeg : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  ext n
  by_cases h0 : n = 0
  · subst n; simp
  by_cases h1 : n = 1
  · subst n; simp
  by_cases h2 : n = 2
  · subst n; simpa [hdeg] using hq.coeff_natDegree
  have hn : q.natDegree < n := by omega
  rw [q.coeff_eq_zero_of_natDegree_lt hn]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C,
    h0, h1, h2, show 1 ≠ n by omega]

open Polynomial in
private theorem exists_irreducible_quadratic
    (F : Type*) [Field F] [Finite F] :
    ∃ q : F[X], q.Monic ∧ Irreducible q ∧ q.natDegree = 2 := by
  let ⟨p, hp⟩ := CharP.exists F
  letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let E := FiniteField.Extension F p 2
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F E
  refine ⟨minpoly F x, minpoly.monic (IsIntegral.of_finite F x),
    minpoly.irreducible (IsIntegral.of_finite F x), ?_⟩
  have hfin := IntermediateField.adjoin.finrank (IsIntegral.of_finite F x)
  rw [hx] at hfin
  calc
    (minpoly F x).natDegree = Module.finrank F ↥(⊤ : IntermediateField F E) := hfin.symm
    _ = Module.finrank F E := by simp
    _ = 2 := FiniteField.finrank_extension F p 2

open Polynomial in
private theorem quadratic_monic_natDegree
    {F : Type*} [Semiring F] [Nontrivial F] (a b : F) :
    (X ^ 2 + C a * X + C b : F[X]).Monic ∧
      (X ^ 2 + C a * X + C b : F[X]).natDegree = 2 := by
  have hlo : (C a * X + C b : F[X]).degree < (2 : WithBot ℕ) := by
    calc
      (C a * X + C b : F[X]).degree ≤
          max (C a * X : F[X]).degree (C b).degree := degree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · exact degree_C_mul_X_le a
        · exact degree_C_le.trans (by norm_num)
      _ < 2 := by norm_num
  have hmon : (X ^ 2 + (C a * X + C b) : F[X]).Monic :=
    monic_X_pow_add hlo
  have hdegree : (X ^ 2 + (C a * X + C b) : F[X]).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hlo
  have hnat := natDegree_eq_of_degree_eq_some hdegree
  simpa only [add_assoc] using And.intro hmon hnat

private theorem decompositionGroup_eq_idealStabilizer
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : FinitePlace L) :
    decompositionGroup K w =
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  letI := finitePlaceAction K L
  ext σ
  change σ • w = w ↔ σ • w.asIdeal = w.asIdeal
  constructor
  · intro h
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change (conjugateFinitePlace K σ w).asIdeal = w.asIdeal
    rw [conjugateFinitePlace_asIdeal]
    exact h

private theorem square_ne_exp_neg_one
    (x : WithZero (Multiplicative ℤ)) : x ^ 2 ≠ WithZero.exp (-1 : ℤ) := by
  intro h
  have hh := congrArg WithZero.log h
  simp [WithZero.log_pow] at hh
  omega

open Polynomial in
private theorem quadratic_residue_root
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    (A B : R) (β : S)
    (hβ : β ^ 2 + algebraMap R S A * β + algebraMap R S B = 0) :
    let q : (R ⧸ p)[X] :=
      X ^ 2 + C (Ideal.Quotient.mk p A) * X + C (Ideal.Quotient.mk p B)
    (aeval (Ideal.Quotient.mk P β)) q = 0 := by
  dsimp
  simp only [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul]
  change (Ideal.Quotient.mk P)
    (β ^ 2 + algebraMap R S A * β + algebraMap R S B) = 0
  rw [hβ, map_zero]

open Polynomial in
private theorem exists_local_klein_level
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) :
    ∃ L : GaloisLevel K,
      IsKleinFour (L.field ≃ₐ[K] L.field) ∧
      decompositionGroup K (absolutePlaceAtLevel W hW L) = ⊤ := by
  obtain ⟨hWne, v, hWbase⟩ := hW
  let p : Ideal (𝓞 K) := v.asIdeal
  let πK : K := Classical.choose (v.valuation_exists_uniformizer K)
  have hπK : v.valuation K πK = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec (v.valuation_exists_uniformizer K)
  let k := (𝓞 K) ⧸ p
  letI : Field k := Ideal.Quotient.field p
  letI : Finite k := by dsimp [k, p]; infer_instance
  obtain ⟨q, hqmon, hqirr, hqdeg⟩ := exists_irreducible_quadratic k
  obtain ⟨A, hA⟩ := Ideal.Quotient.mk_surjective (I := p) (q.coeff 1)
  obtain ⟨B, hB⟩ := Ideal.Quotient.mk_surjective (I := p) (q.coeff 0)
  let pa : K[X] := X ^ 2 - C πK
  obtain ⟨α, hαroot⟩ := IsAlgClosed.exists_root
      (pa.map (algebraMap K (AlgebraicClosure K))) (by
    simp only [pa, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rw [degree_X_pow_sub_C (R := AlgebraicClosure K) (n := 2) (by omega)]
    norm_num)
  let aK : K := (A : K)
  let bK : K := (B : K)
  let pb : K[X] := X ^ 2 + C aK * X + C bK
  obtain ⟨β, hβroot⟩ := IsAlgClosed.exists_root
      (pb.map (algebraMap K (AlgebraicClosure K))) (by
    intro hd
    have hz := coeff_eq_zero_of_degree_lt
      (p := pb.map (algebraMap K (AlgebraicClosure K))) (n := 2)
      (by rw [hd]; norm_num)
    simp [pb] at hz)
  have hαeq : α ^ 2 = algebraMap K (AlgebraicClosure K) πK :=
    sub_eq_zero.mp (by simpa [pa, Polynomial.IsRoot] using hαroot)
  have hβeq : β ^ 2 + algebraMap K (AlgebraicClosure K) aK * β +
      algebraMap K (AlgebraicClosure K) bK = 0 := by
    simpa [pb, Polynomial.IsRoot] using hβroot
  have hpmon : pa.Monic := monic_X_pow_sub_C πK (by omega)
  have hpdeg : pa.natDegree = 2 := by
    apply natDegree_eq_of_degree_eq_some
    exact degree_X_pow_sub_C (by omega) πK
  obtain ⟨hpbmon, hpbdeg⟩ := quadratic_monic_natDegree aK bK
  have hαint : IsIntegral K α := ⟨pa, hpmon, by
    simpa [pa, hαeq]⟩
  have hβint : IsIntegral K β := ⟨pb, by simpa [pb] using hpbmon, by
    simpa [pb] using hβroot⟩
  let Eα : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {α}
  let Eβ : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {β}
  let E : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {α, β}
  letI : FiniteDimensional K Eα := IntermediateField.adjoin.finiteDimensional hαint
  letI : FiniteDimensional K Eβ := IntermediateField.adjoin.finiteDimensional hβint
  have hEeq : E = Eα ⊔ Eβ := by
    change IntermediateField.adjoin K {α, β} =
      IntermediateField.adjoin K {α} ⊔ IntermediateField.adjoin K {β}
    rw [show ({α, β} : Set (AlgebraicClosure K)) = {α} ∪ {β} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union],
      IntermediateField.adjoin_union]
  letI : FiniteDimensional K E := hEeq ▸ inferInstance
  have hαfin : Module.finrank K Eα ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hαint]
    have hdvd : minpoly K α ∣ pa := minpoly.dvd K α (by
      simpa [pa, hαeq])
    simpa [hpdeg] using Polynomial.natDegree_le_of_dvd hdvd hpmon.ne_zero
  have hβfin : Module.finrank K Eβ ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hβint]
    have hdvd : minpoly K β ∣ pb := minpoly.dvd K β (by
      simpa [pb] using hβroot)
    have := Polynomial.natDegree_le_of_dvd hdvd (by
      exact (by simpa [pb] using hpbmon.ne_zero))
    simpa [pb, hpbdeg] using this
  have hEfin : Module.finrank K E ≤ 4 := by
    rw [hEeq]
    exact (IntermediateField.finrank_sup_le Eα Eβ).trans
      (Nat.mul_le_mul hαfin hβfin)
  have hnormal : Normal K E := by
    apply IntermediateField.normal_iff_forall_map_le.mpr
    intro σ
    rw [IntermediateField.map_le_iff_le_comap]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x (hx : x ∈ ({α, β} : Set (AlgebraicClosure K)))
    change σ x ∈ E
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      have hs : (σ α) ^ 2 = algebraMap K (AlgebraicClosure K) πK := by
        rw [← map_pow, hαeq, σ.commutes]
      have hprod : (σ α - α) * (σ α + α) = 0 := by
        calc
          _ = (σ α) ^ 2 - α ^ 2 := by ring
          _ = 0 := by rw [hs, hαeq, sub_self]
      rcases mul_eq_zero.mp hprod with h | h
      · rw [sub_eq_zero.mp h]
        exact IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)
      · rw [add_eq_zero_iff_eq_neg.mp h]
        exact E.neg_mem (IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp))
    · subst x
      have hs : (σ β) ^ 2 + algebraMap K (AlgebraicClosure K) aK * σ β +
          algebraMap K (AlgebraicClosure K) bK = 0 := by
        calc
          _ = σ (β ^ 2 + algebraMap K (AlgebraicClosure K) aK * β +
              algebraMap K (AlgebraicClosure K) bK) := by simp [σ.commutes]
          _ = 0 := by rw [hβeq, map_zero]
      have hprod : (σ β - β) *
          (σ β + β + algebraMap K (AlgebraicClosure K) aK) = 0 := by
        calc
          _ = ((σ β) ^ 2 + algebraMap K (AlgebraicClosure K) aK * σ β +
              algebraMap K (AlgebraicClosure K) bK) -
              (β ^ 2 + algebraMap K (AlgebraicClosure K) aK * β +
              algebraMap K (AlgebraicClosure K) bK) := by ring
          _ = 0 := by rw [hs, hβeq, sub_self]
      rcases mul_eq_zero.mp hprod with h | h
      · rw [sub_eq_zero.mp h]
        exact IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)
      · have heq : σ β = -β - algebraMap K (AlgebraicClosure K) aK := by
          linear_combination h
        rw [heq]
        exact E.sub_mem (E.neg_mem
          (IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)))
          (E.algebraMap_mem aK)
  letI : Normal K E := hnormal
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsGalois K E := ⟨⟩
  let L : GaloisLevel K :=
    { field := E
      finiteDimensional := inferInstance
      numberField := inferInstance
      isGalois := inferInstance }
  have hpow2 : ∀ g : E ≃ₐ[K] E, g ^ 2 = 1 := by
    intro g
    apply AlgEquiv.ext
    have heq : (g ^ 2).toAlgHom = (1 : E ≃ₐ[K] E).toAlgHom := by
      apply IntermediateField.adjoin_algHom_ext K
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · subst x
        let αE : E := ⟨α, IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)⟩
        have hαE : αE ^ 2 = algebraMap K E πK := by
          apply Subtype.ext
          exact hαeq
        have hgα : g αE = αE ∨ g αE = -αE := by
          have hs : (g αE) ^ 2 = algebraMap K E πK := by
            rw [← map_pow, hαE, g.commutes]
          have hp : (g αE - αE) * (g αE + αE) = 0 := by
            calc
              _ = (g αE) ^ 2 - αE ^ 2 := by ring
              _ = 0 := by rw [hs, hαE, sub_self]
          rcases mul_eq_zero.mp hp with h | h
          · exact Or.inl (sub_eq_zero.mp h)
          · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
        change g (g αE) = αE
        rcases hgα with h | h
        · rw [h, h]
        · rw [h, map_neg, h, neg_neg]
      · subst x
        let βE : E := ⟨β, IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)⟩
        have hβE : βE ^ 2 + algebraMap K E aK * βE + algebraMap K E bK = 0 := by
          apply Subtype.ext
          exact hβeq
        have hgβ : g βE = βE ∨ g βE = -βE - algebraMap K E aK := by
          have hs : (g βE) ^ 2 + algebraMap K E aK * g βE +
              algebraMap K E bK = 0 := by
            calc
              _ = g (βE ^ 2 + algebraMap K E aK * βE + algebraMap K E bK) := by
                simp [g.commutes]
              _ = 0 := by rw [hβE, map_zero]
          have hp : (g βE - βE) * (g βE + βE + algebraMap K E aK) = 0 := by
            calc
              _ = ((g βE) ^ 2 + algebraMap K E aK * g βE + algebraMap K E bK) -
                  (βE ^ 2 + algebraMap K E aK * βE + algebraMap K E bK) := by ring
              _ = 0 := by rw [hs, hβE, sub_self]
          rcases mul_eq_zero.mp hp with h | h
          · exact Or.inl (sub_eq_zero.mp h)
          · right; linear_combination h
        change g (g βE) = βE
        rcases hgβ with h | h
        · rw [h, h]
        · rw [h, map_sub, map_neg, g.commutes, h]
          ring
    intro z
    exact DFunLike.congr_fun heq z
  let w : FinitePlace E := absolutePlaceAtLevel W
    (⟨hWne, v, hWbase⟩ : IsAbsoluteFinitePlace K W) L
  have hwrest : restrictFinitePlace K w = v :=
    absolutePlaceAtLevel_restrict_base W
      (⟨hWne, v, hWbase⟩ : IsAbsoluteFinitePlace K W) L v hWbase
  letI : w.asIdeal.LiesOver p := by
    have h : w.asIdeal.LiesOver (restrictFinitePlace K w).asIdeal := ⟨rfl⟩
    simpa [p, hwrest] using h
  let αE : E :=
    ⟨α, IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)⟩
  have hαE : αE ^ 2 = algebraMap K E πK := by
    apply Subtype.ext
    exact hαeq
  have he_ne_one : w.asIdeal.ramificationIdx' (𝓞 K) ≠ 1 := by
    intro he
    have hlie := v.valuation_liesOver E w πK
    have he' : p.ramificationIdx w.asIdeal = 1 := by
      rw [Ideal.ramificationIdx_eq_ramificationIdx' p w.asIdeal v.ne_bot]
      exact he
    have hπw : w.valuation E (algebraMap K E πK) =
        WithZero.exp (-1 : ℤ) := by
      rw [he', pow_one, hπK] at hlie
      exact hlie.symm
    have hαval : (w.valuation E αE) ^ 2 = WithZero.exp (-1 : ℤ) := by
      rw [← hπw, ← hαE]
      exact (map_pow (w.valuation E) αE 2).symm
    exact square_ne_exp_neg_one (w.valuation E αE) hαval
  have he_pos : 0 < w.asIdeal.ramificationIdx' (𝓞 K) :=
    Ideal.ramificationIdx'_pos w.asIdeal (𝓞 K)
  have he : 2 ≤ w.asIdeal.ramificationIdx' (𝓞 K) := by
    omega
  let βE : E :=
    ⟨β, IntermediateField.subset_adjoin K ({α, β} : Set _) (by simp)⟩
  have hβOE : βE ^ 2 + algebraMap (𝓞 K) E A * βE +
      algebraMap (𝓞 K) E B = 0 := by
    apply Subtype.ext
    simpa [aK, bK, IsScalarTower.algebraMap_apply (𝓞 K) K E] using hβeq
  have hβintOK : IsIntegral (𝓞 K) βE := by
    refine ⟨X ^ 2 + C A * X + C B, (quadratic_monic_natDegree A B).1, ?_⟩
    simpa using hβOE
  letI : IsScalarTower ℤ (𝓞 K) E :=
    IsScalarTower.of_algebraMap_eq (fun z => by
      apply Subtype.ext
      simp)
  have hβintZ : IsIntegral ℤ βE := isIntegral_trans βE hβintOK
  let βO : 𝓞 E := ⟨βE, hβintZ⟩
  let kE := (𝓞 E) ⧸ w.asIdeal
  letI : Field kE := Ideal.Quotient.field w.asIdeal
  have hβOeq : βO ^ 2 + algebraMap (𝓞 K) (𝓞 E) A * βO +
      algebraMap (𝓞 K) (𝓞 E) B = 0 := by
    apply Subtype.ext
    exact hβOE
  let βbar : kE := Ideal.Quotient.mk w.asIdeal βO
  have hqshape : q = X ^ 2 + C (Ideal.Quotient.mk p A) * X +
      C (Ideal.Quotient.mk p B) := by
    rw [monic_natDegree_two_eq q hqmon hqdeg, hA, hB]
  have hβbar : aeval βbar q = 0 := by
    rw [hqshape]
    exact quadratic_residue_root p w.asIdeal A B βO hβOeq
  have hminDvd : minpoly k βbar ∣ q := minpoly.dvd k βbar hβbar
  have hassoc : Associated (minpoly k βbar) q :=
    (minpoly.irreducible (IsIntegral.of_finite k βbar)).associated_of_dvd hqirr hminDvd
  have hmineq : minpoly k βbar = q :=
    Polynomial.eq_of_monic_of_associated
      (minpoly.monic (IsIntegral.of_finite k βbar)) hqmon hassoc
  have hmindeq : (minpoly k βbar).natDegree = 2 := by
    rw [hmineq, hqdeg]
  let kres : IntermediateField k kE := IntermediateField.adjoin k {βbar}
  letI : FiniteDimensional k kres :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.of_finite k βbar)
  have hkres : Module.finrank k kres = 2 := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite k βbar), hmindeq]
  have hktower := Module.finrank_mul_finrank k kres kE
  have hkpos : 0 < Module.finrank kres kE := Module.finrank_pos
  have hfres : 2 ≤ Module.finrank k kE := by
    rw [hkres] at hktower
    omega
  have hf : 2 ≤ w.asIdeal.inertiaDeg' (𝓞 K) := by
    rw [← Ideal.inertiaDeg_eq_inertiaDeg' p w.asIdeal,
      Ideal.inertiaDeg_algebraMap]
    exact hfres
  let G := E ≃ₐ[K] E
  have hcardstab :
      Nat.card (MulAction.stabilizer G w.asIdeal) =
        w.asIdeal.ramificationIdx' (𝓞 K) *
          w.asIdeal.inertiaDeg' (𝓞 K) := by
    rw [Ideal.card_stabilizer_eq p w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p w.asIdeal G,
      Ideal.inertiaDegIn_eq_inertiaDeg p w.asIdeal G]
  have hdecomp : decompositionGroup K w =
      MulAction.stabilizer G w.asIdeal :=
    decompositionGroup_eq_idealStabilizer K E w
  have hcardlower : 4 ≤ Nat.card (decompositionGroup K w) := by
    rw [hdecomp, hcardstab]
    exact (show 4 = 2 * 2 by norm_num) ▸ Nat.mul_le_mul he hf
  have hGupper : Nat.card G ≤ 4 := by
    rw [IsGalois.card_aut_eq_finrank K E]
    exact hEfin
  have hdecompTop : decompositionGroup K w = ⊤ :=
    Subgroup.eq_top_of_le_card _ (hGupper.trans hcardlower)
  have hGcard : Nat.card G = 4 := by
    apply le_antisymm hGupper
    simpa [hdecompTop] using hcardlower
  have hnsub : ¬Subsingleton G := by
    intro hs
    have hc : Nat.card G = 1 :=
      (Nat.card_eq_one_iff_unique).2 ⟨hs, inferInstance⟩
    omega
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hnsub
  have hexp_le : Monoid.exponent G ≤ 2 :=
    Monoid.exponent_min' 2 (by omega) hpow2
  have hexp_gt : 1 < Monoid.exponent G := Monoid.one_lt_exponent
  have hexp : Monoid.exponent G = 2 := by omega
  let hklein : IsKleinFour G := ⟨hGcard, hexp⟩
  exact ⟨L, hklein, hdecompTop⟩

/-- Blueprint Lemma 8.6 (`lem:decomp-not-procyclic`), strengthened to its
explicit local biquadratic quotient. -/
theorem absoluteDecompositionGroup_has_biquadratic_quotient
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) :
    ∃ f : (absoluteDecompositionGroup K W) →ₜ*
        Multiplicative (ZMod 2 × ZMod 2),
      Function.Surjective f := by
  obtain ⟨L, hklein, hdecomp⟩ := exists_local_klein_level W hW
  letI : IsKleinFour (L.field ≃ₐ[K] L.field) := hklein
  let e : (L.field ≃ₐ[K] L.field) ≃*
      Multiplicative (ZMod 2 × ZMod 2) :=
    Classical.choice IsKleinFour.nonempty_mulEquiv
  let r : absoluteDecompositionGroup K W →*
      (L.field ≃ₐ[K] L.field) :=
    (absoluteRestriction L).comp (absoluteDecompositionGroup K W).subtype
  have hrcont : Continuous r := by
    have hres : Continuous (absoluteRestriction L) := by
      change Continuous (AlgEquiv.restrictNormalHom L.field)
      exact InfiniteGalois.restrictNormalHom_continuous L.field
    exact hres.comp continuous_subtype_val
  have hecont : Continuous e := continuous_of_discreteTopology
  let f : (absoluteDecompositionGroup K W) →ₜ*
      Multiplicative (ZMod 2 × ZMod 2) :=
    ContinuousMonoidHom.mk (e.toMonoidHom.comp r) (hecont.comp hrcont)
  refine ⟨f, ?_⟩
  have hrsurj : Function.Surjective r := by
    intro σ
    have hσ : σ ∈ finiteLevelImage L (absoluteDecompositionGroup K W) := by
      rw [absoluteDecompositionGroup_finiteImage W hW L, hdecomp]
      trivial
    obtain ⟨g, hg, hgres⟩ := hσ
    exact ⟨⟨g, hg⟩, hgres⟩
  intro y
  obtain ⟨g, hg⟩ := hrsurj (e.symm y)
  refine ⟨g, ?_⟩
  change e (r g) = y
  rw [hg]
  simp
/-- In particular an absolute finite-place decomposition group is not
procyclic. -/
theorem absoluteDecompositionGroup_not_procyclic
    {K : Type*} [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K))
    (hW : IsAbsoluteFinitePlace K W) :
    ¬IsProcyclic (absoluteDecompositionGroup K W) := by
  rintro ⟨h, hh⟩
  obtain ⟨f, hf⟩ := absoluteDecompositionGroup_has_biquadratic_quotient W hW
  apply (IsKleinFour.not_isCyclic :
    ¬IsCyclic (Multiplicative (ZMod 2 × ZMod 2)))
  let y := f h
  refine ⟨y, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := hf z
  have hx : x ∈ closure (Subgroup.zpowers h : Set
      (absoluteDecompositionGroup K W)) := by
    change x ∈ (Subgroup.zpowers h).topologicalClosure
    rw [hh]
    trivial
  rw [mem_closure_iff] at hx
  let O : Set (absoluteDecompositionGroup K W) := f ⁻¹' {f x}
  have hOopen : IsOpen O :=
    f.continuous.isOpen_preimage _ (isOpen_discrete _)
  have hxO : x ∈ O := Set.mem_preimage.mpr (Set.mem_singleton _)
  obtain ⟨a, haO, ha⟩ := hx O hOopen hxO
  change a ∈ Subgroup.zpowers h at ha
  rw [Subgroup.mem_zpowers_iff] at ha
  obtain ⟨n, rfl⟩ := ha
  refine ⟨n, ?_⟩
  change y ^ n = f x
  dsimp [y]
  rw [← map_zpow]
  exact haO

private theorem algEquiv_fiber_isOpen
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x y : Ω) :
    IsOpen {g : Ω ≃ₐ[K] Ω | g x = y} := by
  by_cases h : ∃ g : Ω ≃ₐ[K] Ω, g x = y
  · obtain ⟨g₀, hg₀⟩ := h
    have heq : {g : Ω ≃ₐ[K] Ω | g x = y} =
        g₀ • (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)) := by
      ext g
      rw [mem_leftCoset_iff, Set.mem_setOf_eq]
      change (g x = y) ↔ (g₀⁻¹ * g) x = x
      constructor
      · intro hg
        change g₀.symm (g x) = x
        rw [hg, ← hg₀]
        exact g₀.symm_apply_apply x
      · intro hg
        have := congrArg g₀ hg
        simpa [hg₀] using this
    rw [heq]
    exact (stabilizer_isOpen_of_isIntegral x).leftCoset g₀
  · have heq : {g : Ω ≃ₐ[K] Ω | g x = y} = ∅ := by
      ext g
      constructor
      · intro hg
        exact (h ⟨g, hg⟩).elim
      · intro hg
        exact hg.elim
    rw [heq]
    exact isOpen_empty

private theorem algEquiv_eval_preimage_isClopen
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x : Ω) (S : Set Ω) :
    IsClopen {g : Ω ≃ₐ[K] Ω | g x ∈ S} := by
  have heq : {g : Ω ≃ₐ[K] Ω | g x ∈ S} =
      ⋃ y ∈ S, {g : Ω ≃ₐ[K] Ω | g x = y} := by
    ext g
    simp
  have hopen : IsOpen {g : Ω ≃ₐ[K] Ω | g x ∈ S} := by
    rw [heq]
    exact isOpen_biUnion fun y _ => algEquiv_fiber_isOpen x y
  have hcompl : {g : Ω ≃ₐ[K] Ω | g x ∈ S}ᶜ =
      {g : Ω ≃ₐ[K] Ω | g x ∈ Sᶜ} := by
    ext g
    simp
  refine ⟨?_, hopen⟩
  apply isOpen_compl_iff.mp
  rw [hcompl]
  rw [show {g : Ω ≃ₐ[K] Ω | g x ∈ Sᶜ} =
      ⋃ y ∈ Sᶜ, {g : Ω ≃ₐ[K] Ω | g x = y} by
        ext g
        simp]
  exact isOpen_biUnion fun y _ => algEquiv_fiber_isOpen x y

private theorem mem_stabilizer_valuationSubring_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (W : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) :
    g ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) W ↔
      ∀ x : Ω, x ∈ W ↔ g x ∈ W := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg x
    have hmem := ValuationSubring.smul_mem_pointwise_smul_iff
      (g := g) (S := W) (x := x)
    rw [hg] at hmem
    simpa [AlgEquiv.smul_def] using hmem.symm
  · intro hg
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := g) (S := W) (x := x)]
    change (g⁻¹ x ∈ W) ↔ x ∈ W
    simpa using hg (g⁻¹ x)

private theorem absoluteDecompositionGroup_isClosed
    (K : Type*) [Field K] [NumberField K]
    (W : ValuationSubring (AlgebraicClosure K)) :
    IsClosed (absoluteDecompositionGroup K W :
      Set (Field.absoluteGaloisGroup K)) := by
  change IsClosed ((MulAction.stabilizer
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W) :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  have heq : ((MulAction.stabilizer
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W) :
        Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) =
      ⋂ x : AlgebraicClosure K,
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          x ∈ W ↔ g x ∈ W} := by
    ext g
    constructor
    · intro hg
      have hs := (mem_stabilizer_valuationSubring_iff W g).mp hg
      rw [Set.mem_iInter]
      exact hs
    · intro hg
      apply (mem_stabilizer_valuationSubring_iff W g).mpr
      rw [Set.mem_iInter] at hg
      exact hg
  rw [heq]
  apply isClosed_iInter
  intro x
  by_cases hx : x ∈ W
  · have hset : {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        x ∈ W ↔ g x ∈ W} =
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          g x ∈ (W : Set _)} := by
      ext g
      simp [hx]
    rw [hset]
    exact (algEquiv_eval_preimage_isClopen
      (K := K) (Ω := AlgebraicClosure K) x (W : Set _)).1
  · have hset : {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
        x ∈ W ↔ g x ∈ W} =
        {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
          g x ∈ (W : Set _)}ᶜ := by
      ext g
      simp [hx]
    rw [hset]
    exact (algEquiv_eval_preimage_isClopen
      (K := K) (Ω := AlgebraicClosure K) x (W : Set _)).2.isClosed_compl

private theorem restrictLevelPlace_refl
    {K : Type*} [Field K] [NumberField K]
    (L : GaloisLevel K) (w : FinitePlace L.field) :
    restrictLevelPlace (L := L) (M := L) le_rfl w = w := by
  letI : Algebra L.field L.field :=
    (IntermediateField.inclusion
      (show L.field ≤ L.field from le_rfl)).toAlgebra
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [restrictLevelPlace, restrictFinitePlace_asIdeal]
  ext x
  change algebraMap (𝓞 L.field) (𝓞 L.field) x ∈ w.asIdeal ↔ _
  have hx : algebraMap (𝓞 L.field) (𝓞 L.field) x = x := by
    apply Subtype.ext
    rfl
  rw [hx]

private theorem restrictLevelPlace_trans
    {K : Type*} [Field K] [NumberField K]
    {L M N : GaloisLevel K} (hLM : L.LE M) (hMN : M.LE N)
    (w : FinitePlace N.field) :
    restrictLevelPlace hLM (restrictLevelPlace hMN w) =
      restrictLevelPlace (hLM.trans hMN) w := by
  letI : Algebra L.field M.field := (IntermediateField.inclusion hLM).toAlgebra
  letI : Algebra M.field N.field := (IntermediateField.inclusion hMN).toAlgebra
  letI : Algebra L.field N.field :=
    (IntermediateField.inclusion (hLM.trans hMN)).toAlgebra
  letI : IsScalarTower L.field M.field N.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [restrictLevelPlace, restrictLevelPlace, restrictLevelPlace,
    restrictFinitePlace_asIdeal, restrictFinitePlace_asIdeal,
    restrictFinitePlace_asIdeal]
  ext x
  change algebraMap (𝓞 M.field) (𝓞 N.field)
      (algebraMap (𝓞 L.field) (𝓞 M.field) x) ∈ w.asIdeal ↔
    algebraMap (𝓞 L.field) (𝓞 N.field) x ∈ w.asIdeal
  have hx : algebraMap (𝓞 M.field) (𝓞 N.field)
      (algebraMap (𝓞 L.field) (𝓞 M.field) x) =
        algebraMap (𝓞 L.field) (𝓞 N.field) x := by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply L.field M.field N.field x
  rw [hx]

/-- Blueprint Theorem 8.7 (`thm:limit`): a closed subgroup is an absolute
finite-place decomposition group exactly when it is not procyclic and every
cofinal finite image is a finite-level decomposition group. -/
theorem inverse_limit_characterization
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ)
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup K))) :
    H ∈ absoluteDecompositionCollection K ↔
      ¬IsProcyclic H ∧
        ∀ i, finiteLevelImage (Λ i) H ∈
          decompositionCollection K (Λ i).field := by
  constructor
  · rintro ⟨W, hW, rfl⟩
    refine ⟨absoluteDecompositionGroup_not_procyclic W hW, ?_⟩
    intro i
    rw [absoluteDecompositionGroup_finiteImage W hW (Λ i)]
    exact ⟨absolutePlaceAtLevel W hW (Λ i), rfl⟩
  · rintro ⟨hnonprocyclic, hdecomp⟩
    have hanchor_exists :
        ∃ i₀, ¬IsCyclic (finiteLevelImage (Λ i₀) H) := by
      by_contra h
      push Not at h
      exact hnonprocyclic
        (cyclic_finite_images_imply_procyclic Λ hΛ H hclosed h)
    obtain ⟨i₀, hanchor⟩ := hanchor_exists
    let J := {i : ι // (Λ i₀).LE (Λ i)}
    let Λ' : J → GaloisLevel K := fun i => Λ i.1
    letI : Preorder J :=
      { le := fun i j => (Λ i.1).LE (Λ j.1)
        le_refl := fun _ => le_rfl
        le_trans := fun _ _ _ hij hjk => hij.trans hjk }
    letI : IsDirected J (· ≤ ·) := IsDirected.mk fun i j => by
      obtain ⟨k, hik, hjk⟩ := hΛ.2.1 i.1 j.1
      exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩
    let S : J → Type _ := fun i =>
      {v : FinitePlace (Λ' i).field // v ∈ finiteWitnesses H (Λ' i)}
    letI (i : J) : Finite (S i) :=
      Set.finite_coe_iff.mpr
        (finite_witness_system Λ H i₀ hanchor hdecomp i.1 i.2).2
    letI (i : J) : Nonempty (S i) := by
      obtain ⟨v, hv⟩ :=
        (finite_witness_system Λ H i₀ hanchor hdecomp i.1 i.2).1
      exact ⟨⟨v, hv⟩⟩
    let r : ∀ {i j : J}, i ≤ j → S j → S i := fun {i j} hij v =>
      ⟨restrictLevelPlace hij v.1,
        restrictLevelPlace_mem_finiteWitnesses H hij v.2⟩
    have rid : ∀ i (v : S i), r (le_refl i) v = v := by
      intro i v
      apply Subtype.ext
      exact restrictLevelPlace_refl (Λ' i) v.1
    have rcomp : ∀ {i j k : J} (hij : i ≤ j) (hjk : j ≤ k)
        (v : S k), r hij (r hjk v) = r (hij.trans hjk) v := by
      intro i j k hij hjk v
      apply Subtype.ext
      exact restrictLevelPlace_trans hij hjk v.1
    obtain ⟨x, hx⟩ := finite_inverse_system_compactness S r rid rcomp
    have hΛ' : IsCofinalGaloisSystem Λ' := by
      refine ⟨⟨⟨i₀, le_rfl⟩⟩, ?_, ?_⟩
      · intro i j
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        exact ⟨k, hik, hjk⟩
      · intro L
        obtain ⟨j, hj⟩ := hΛ.2.2 L
        obtain ⟨k, hi₀k, hjk⟩ := hΛ.2.1 i₀ j
        exact ⟨⟨k, hi₀k⟩, hj.trans hjk⟩
    have hcompat : IsCompatiblePlaceFamily Λ' (fun i => (x i).1) := by
      intro i j hij
      exact congrArg Subtype.val (hx hij)
    obtain ⟨W, hWlevels⟩ := exists_union_valuationSubring Λ' hΛ'
      (fun i => (x i).1) hcompat
    let j₀ : J := ⟨i₀, le_rfl⟩
    let w₀ : FinitePlace (Λ' j₀).field := (x j₀).1
    have hW₀ : W.comap (Λ' j₀).field.val.toRingHom =
        primeValuationSubring w₀ := hWlevels j₀
    have hbase : W.comap (algebraMap K (AlgebraicClosure K)) =
        primeValuationSubring (restrictFinitePlace K w₀) := by
      calc
        W.comap (algebraMap K (AlgebraicClosure K)) =
            (W.comap (Λ' j₀).field.val.toRingHom).comap
              (algebraMap K (Λ' j₀).field) := by
          apply ValuationSubring.ext
          intro y
          rfl
        _ = (primeValuationSubring w₀).comap
            (algebraMap K (Λ' j₀).field) := by rw [hW₀]
        _ = primeValuationSubring (restrictFinitePlace K w₀) :=
          primeValuationSubring_comap_restrict K w₀
    have hWne : W ≠ ⊤ := by
      intro htop
      apply primeValuationSubring_ne_top w₀
      rw [← hW₀, htop]
      ext y
      simp
    have hWabs : IsAbsoluteFinitePlace K W :=
      ⟨hWne, restrictFinitePlace K w₀, hbase⟩
    refine ⟨W, hWabs, ?_⟩
    apply closed_subgroups_eq_of_cofinal_images Λ' hΛ' H
      (absoluteDecompositionGroup K W) hclosed
      (absoluteDecompositionGroup_isClosed K W)
    intro j
    have hplace : absolutePlaceAtLevel W hWabs (Λ' j) = (x j).1 := by
      let A := W.comap (Λ' j).field.val.toRingHom
      have hA : IsNontrivialValuation A :=
        absolutePlace_comap_nontrivial W hWabs (Λ' j)
      simpa [absolutePlaceAtLevel, centerFinitePlace, A] using
        ((numberField_valuations A hA).choose_spec.2 (x j).1
          (hWlevels j)).symm
    rw [absoluteDecompositionGroup_finiteImage W hWabs (Λ' j), hplace]
    exact (x j).2.symm

end

end NU.LocalTheory
