import Submission.NU.NeukirchUchida.FiniteConjugacy

/-!
# Compactness and completion of the pointed theorem

Blueprint §2.2 and §7.  This file proves the two elementary global group
lemmas, defines finite-level solution sets as literal finite-quotient
cylinders, records their finite-intersection property, and states global
existence and uniqueness.
-/

open scoped NumberField Pointwise

namespace NU.NeukirchUchida

noncomputable section

/-! ## Prime transitivity and the virtual center -/

/-- Blueprint Lemma `lem:prime-transitivity`: `G_ℚ` acts transitively on
absolute primes above one rational prime. -/
theorem absolutePrime_transitive
    (P Q : AbsolutePrime)
    (hPQ : finitePrime rationalNumberField P =
      finitePrime rationalNumberField Q) :
    ∃ alpha : RationalAbsoluteGaloisGroup, alpha • P = Q := by
  obtain ⟨alpha, halpha⟩ :=
    exists_smul_of_finitePrime_eq rationalNumberField P Q hPQ
  exact ⟨alpha.1, halpha⟩

/-- An ambient automorphism centralizes the open subgroup `G_F`. -/
def CentralizesAbsoluteGaloisGroup
    (F : NumberFieldInOmega) (c : RationalAbsoluteGaloisGroup) : Prop :=
  ∀ g : absoluteGaloisGroup F, c * g.1 = g.1 * c

/-- Blueprint Lemma `lem:virtual-center`: the centralizer in `G_ℚ` of every
open subgroup `G_F` is trivial.  The statement has the needed open-subgroup
strength, not merely trivial center of `G_ℚ`. -/
theorem centralizer_absoluteGaloisGroup_eq_one
    (F : NumberFieldInOmega) (c : RationalAbsoluteGaloisGroup)
    (hc : CentralizesAbsoluteGaloisGroup F c) :
    c = 1 := by
  have hfixPrime (P : AbsolutePrime) : c • P = P := by
    have hD : decompositionGroup F P = decompositionGroup F (c • P) := by
      ext g
      constructor
      · intro hg
        change g.1 • (c • P) = c • P
        calc
          g.1 • (c • P) = (g.1 * c) • P := (mul_smul _ _ _).symm
          _ = (c * g.1) • P := by rw [(hc g).symm]
          _ = c • (g.1 • P) := mul_smul _ _ _
          _ = c • P := congrArg (fun Q : AbsolutePrime => c • Q) hg
      · intro hg
        change g.1 • P = P
        calc
          g.1 • P = c⁻¹ • (c • (g.1 • P)) :=
            (inv_smul_smul c (g.1 • P)).symm
          _ = c⁻¹ • ((c * g.1) • P) := by rw [mul_smul]
          _ = c⁻¹ • ((g.1 * c) • P) := by rw [hc g]
          _ = c⁻¹ • (g.1 • (c • P)) := by rw [mul_smul]
          _ = c⁻¹ • (c • P) :=
            congrArg (fun Q : AbsolutePrime => c⁻¹ • Q) hg
          _ = P := inv_smul_smul c P
    let e : absoluteGaloisGroup F ≃ₜ* absoluteGaloisGroup F :=
      ContinuousMulEquiv.refl _
    have hmapP : Subgroup.map e.toMulEquiv.toMonoidHom
        (decompositionGroup F P) = decompositionGroup F P := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hg
        exact ⟨g, hg, rfl⟩
    have hmapcP : Subgroup.map e.toMulEquiv.toMonoidHom
        (decompositionGroup F P) = decompositionGroup F (c • P) := by
      rw [hmapP]
      exact hD
    have hcorrP := eq_primeCorrespondence_of_map_decompositionGroup
      e P P hmapP
    have hcorrCP := eq_primeCorrespondence_of_map_decompositionGroup
      e P (c • P) hmapcP
    exact hcorrCP.trans hcorrP.symm
  have finitePrime_surj (K : NumberFieldInOmega) :
      Function.Surjective (finitePrime K) := by
    intro v
    let A := NU.LocalTheory.primeValuationSubring v
    let i : K.field →+* Omega := K.field.val.toRingHom
    let f : A →+* Omega := i.comp A.toSubring.subtype
    obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
    have hcomap_ne : W.comap i ≠ ⊤ := by
      have hA : A ≠ ⊤ :=
        NU.LocalTheory.primeValuationSubring_ne_top v
      obtain ⟨x, _, hx⟩ :=
        SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hA)
      have hx0 : x ≠ 0 := by
        intro h
        apply hx
        simp [h]
      have hxinv : x⁻¹ ∈ A.nonunits :=
        A.inv_mem_nonunits_iff.mpr (Or.inr hx)
      let a : A := ⟨x⁻¹, A.nonunits_subset hxinv⟩
      have ha0 : a ≠ 0 := by
        intro h
        exact inv_ne_zero hx0 (congrArg Subtype.val h)
      intro htop
      have ha_nonunit : ¬IsUnit a := by
        simpa [IsLocalRing.mem_maximalIdeal] using
          A.coe_mem_nonunits_iff.mp hxinv
      let fW : A →+* W :=
        (i.comp A.toSubring.subtype).codRestrict W.toSubring hW
      letI : IsLocalHom fW := hlocal
      have hfa_nonunit : ¬IsUnit (fW a) := by
        intro h
        exact ha_nonunit (IsUnit.of_map fW a h)
      apply hfa_nonunit
      have hinvW : i (a.1⁻¹) ∈ W := by
        have : a.1⁻¹ ∈ W.comap i := by
          rw [htop]
          trivial
        exact this
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨i (a.1⁻¹), hinvW⟩, ?_⟩
      apply Subtype.ext
      dsimp [fW, a]
      rw [← map_mul]
      rw [show A.toSubring.subtype
        (⟨x⁻¹, A.nonunits_subset hxinv⟩ : A) = x⁻¹ from rfl,
        inv_inv, inv_mul_cancel₀ hx0, map_one]
    have hle : A ≤ W.comap i := by
      intro x hx
      exact hW ⟨x, hx⟩
    letI : Ring.KrullDimLE 1 A := by
      change Ring.KrullDimLE 1
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K.field v)
      infer_instance
    have hcomap : W.comap i = A := by
      exact (ValuationSubring.eq_of_le_of_ne_top A hle hcomap_ne).symm
    have hWtop : W ≠ ⊤ := by
      intro h
      apply hcomap_ne
      rw [h]
      rfl
    let j : ℚ →+* Omega := algebraMap ℚ Omega
    have hQcomap : W.comap j ≠ ⊤ := by
      intro htop
      apply hWtop
      apply top_unique
      intro x _
      have hj (r : ℚ) : j r ∈ W := by
        have : r ∈ W.comap j := by
          rw [htop]
          trivial
        exact this
      let jW : ℚ →+* W := j.codRestrict W.toSubring hj
      letI : Algebra ℚ W := jW.toAlgebra
      letI : IsScalarTower ℚ W Omega := by
        apply IsScalarTower.of_algebraMap_eq
        intro r
        rfl
      have hxQ : IsIntegral ℚ x := by
        letI : Algebra.IsAlgebraic ℚ Omega :=
          AlgebraicClosure.isAlgebraic ℚ
        letI : Algebra.IsIntegral ℚ Omega :=
          Algebra.IsAlgebraic.isIntegral
        exact Algebra.IsIntegral.isIntegral x
      have hxW : IsIntegral W x := hxQ.tower_top
      exact (Subring.isIntegrallyClosed_iff.mp
        (inferInstance : IsIntegrallyClosed W)) hxW
    obtain ⟨q, hq, _⟩ :=
      NU.LocalTheory.numberField_valuations (W.comap j) hQcomap
    let P : AbsolutePrime := ⟨W, hWtop, q, hq⟩
    refine ⟨P, ?_⟩
    apply (NU.LocalTheory.numberField_valuations A
      (NU.LocalTheory.primeValuationSubring_ne_top v)).unique
    · rw [primeValuationSubring_finitePrime, hcomap]
    · rfl
  have primeValuationSubring_conjugate
      (K : NumberFieldInOmega) (sigma : K.field ≃ₐ[ℚ] K.field)
      (v : NU.LocalTheory.FinitePlace K.field) :
      NU.LocalTheory.primeValuationSubring
          (NU.LocalTheory.conjugateFinitePlace ℚ sigma v) =
        sigma • NU.LocalTheory.primeValuationSubring v := by
    ext x
    rw [NU.LocalTheory.mem_primeValuationSubring_iff,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.aut_inv,
      NU.LocalTheory.mem_primeValuationSubring_iff]
    constructor
    · rintro ⟨a, b, hb, hab⟩
      refine ⟨sigma.symm • a, sigma.symm • b, ?_, ?_⟩
      · intro hbmem
        apply hb
        rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
          Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact hbmem
      · rw [show ((sigma.symm • b : 𝓞 K.field) : K.field) =
            sigma.symm (b : K.field) by rfl,
          show ((sigma.symm • a : 𝓞 K.field) : K.field) =
            sigma.symm (a : K.field) by rfl]
        calc
          sigma.symm x * sigma.symm (b : K.field) =
              sigma.symm (x * (b : K.field)) :=
            (map_mul sigma.symm x (b : K.field)).symm
          _ = sigma.symm (a : K.field) := congrArg sigma.symm hab
    · rintro ⟨a, b, hb, hab⟩
      refine ⟨sigma • a, sigma • b, ?_, ?_⟩
      · rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
          Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        simpa only [inv_smul_smul] using hb
      · rw [show ((sigma • b : 𝓞 K.field) : K.field) =
            sigma (b : K.field) by rfl,
          show ((sigma • a : 𝓞 K.field) : K.field) =
            sigma (a : K.field) by rfl]
        have hact : sigma.symm x * (b : K.field) = (a : K.field) := by
          simpa only [AlgEquiv.smul_def] using hab
        calc
          x * sigma (b : K.field) =
              sigma (sigma.symm x) * sigma (b : K.field) := by
            rw [sigma.apply_symm_apply]
          _ = sigma (sigma.symm x * (b : K.field)) :=
            (map_mul sigma (sigma.symm x) (b : K.field)).symm
          _ = sigma (a : K.field) := congrArg sigma hact
  have finitePrime_ambient_smul
      (K : NumberFieldInOmega) [IsGalois ℚ K.field]
      (g : RationalAbsoluteGaloisGroup) (P : AbsolutePrime) :
      finitePrime K (g • P) =
        NU.LocalTheory.conjugateFinitePlace ℚ
          (AlgEquiv.restrictNormalHom K.field g) (finitePrime K P) := by
    let sigma : K.field ≃ₐ[ℚ] K.field :=
      AlgEquiv.restrictNormalHom K.field g
    have hvals : NU.LocalTheory.primeValuationSubring
        (finitePrime K (g • P)) =
        NU.LocalTheory.primeValuationSubring
          (NU.LocalTheory.conjugateFinitePlace ℚ sigma (finitePrime K P)) := by
      rw [primeValuationSubring_finitePrime,
        primeValuationSubring_conjugate,
        primeValuationSubring_finitePrime]
      ext x
      change K.field.val x ∈ g • P.valuationSubring ↔
        x ∈ sigma • P.valuationSubring.comap K.field.val.toRingHom
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change g⁻¹ (K.field.val x) ∈ P.valuationSubring ↔
        K.field.val (sigma⁻¹ x) ∈ P.valuationSubring
      rw [show K.field.val (sigma⁻¹ x) = g⁻¹ (K.field.val x) by
        rw [show sigma⁻¹ = AlgEquiv.restrictNormalHom K.field g⁻¹ by
          dsimp only [sigma]
          exact (map_inv (AlgEquiv.restrictNormalHom K.field) g).symm]
        exact AlgEquiv.restrictNormal_commutes g⁻¹ K.field x]
    apply (NU.LocalTheory.numberField_valuations
      (NU.LocalTheory.primeValuationSubring (finitePrime K (g • P)))
      (NU.LocalTheory.primeValuationSubring_ne_top
        (finitePrime K (g • P)))).unique
    · rfl
    · exact hvals
  have restriction_eq_one
      (K : NumberFieldInOmega) [IsGalois ℚ K.field] :
      ambientRestriction K c = 1 := by
    let S := NU.Chebotarev.frobeniusPrimeSet
      (K := ℚ) (L := K.field)
      (ConjClasses.mk (1 : K.field ≃ₐ[ℚ] K.field))
    have hden := NU.Chebotarev.chebotarev_dirichletDensity
      (K := ℚ) (L := K.field)
      (ConjClasses.mk (1 : K.field ≃ₐ[ℚ] K.field))
    have hnum : (0 : ℝ) <
        ((ConjClasses.mk (1 : K.field ≃ₐ[ℚ] K.field)).carrier.ncard : ℝ) := by
      exact_mod_cast ((Set.ncard_pos
        (s := (ConjClasses.mk (1 : K.field ≃ₐ[ℚ] K.field)).carrier)).2
          (show (ConjClasses.mk
            (1 : K.field ≃ₐ[ℚ] K.field)).carrier.Nonempty from
              ⟨1, ConjClasses.mem_carrier_mk⟩))
    have hdenom : (0 : ℝ) < Nat.card (K.field ≃ₐ[ℚ] K.field) := by
      exact_mod_cast Nat.card_pos (α := K.field ≃ₐ[ℚ] K.field)
    have hpositive : (0 : ℝ) <
        ((ConjClasses.mk (1 : K.field ≃ₐ[ℚ] K.field)).carrier.ncard : ℝ) /
          (Nat.card (K.field ≃ₐ[ℚ] K.field) : ℝ) :=
      div_pos hnum hdenom
    have hnonempty : S.Nonempty := by
      by_contra hempty
      have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
      have hfin : S.Finite := by
        rw [hSempty]
        exact Set.finite_empty
      have hzero : NU.Chebotarev.HasDirichletDensity S 0 :=
        NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfin
      have heq :
          ((ConjClasses.mk
            (1 : K.field ≃ₐ[ℚ] K.field)).carrier.ncard : ℝ) /
              (Nat.card (K.field ≃ₐ[ℚ] K.field) : ℝ) = 0 :=
        tendsto_nhds_unique hden hzero
      exact (ne_of_gt hpositive) heq
    obtain ⟨q, hq⟩ := hnonempty
    rcases hq with ⟨hunramified, w, hwq, hclass⟩
    let f : K.field ≃ₐ[ℚ] K.field :=
      NU.Chebotarev.arithFrobeniusAt (K := ℚ) (L := K.field) w
    have hconj : IsConj f 1 := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mp
      exact hclass
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    have hf : f = 1 := by
      calc
        f = a⁻¹ * (a * f * a⁻¹) * a := by group
        _ = 1 := by rw [ha]; group
    have hwunr : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
      hunramified w hwq
    have hgen := NU.Chebotarev.arithFrobAt_generates_decomposition
      (K := ℚ) (L := K.field) w hwunr
    rw [show NU.Chebotarev.arithFrobeniusAt
      (K := ℚ) (L := K.field) w = 1 from hf] at hgen
    obtain ⟨P, hPw⟩ := finitePrime_surj K w
    have hplace : NU.LocalTheory.conjugateFinitePlace ℚ
        (ambientRestriction K c) w = w := by
      change NU.LocalTheory.conjugateFinitePlace ℚ
        (AlgEquiv.restrictNormalHom K.field c) w = w
      rw [← hPw, ← finitePrime_ambient_smul K c P, hfixPrime P]
    have hstab : ambientRestriction K c • w.asIdeal = w.asIdeal := by
      have hi := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hplace
      rw [NU.LocalTheory.conjugateFinitePlace_asIdeal] at hi
      exact hi
    have hmem : ambientRestriction K c ∈
        NU.Chebotarev.decompositionSubgroup (K := ℚ) (L := K.field) w :=
      hstab
    rw [hgen, Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    simpa using hn.symm
  apply AlgEquiv.ext
  intro x
  let A : IntermediateField ℚ Omega :=
    IntermediateField.adjoin ℚ ({x} : Set Omega)
  let Nfield : IntermediateField ℚ Omega :=
    IntermediateField.normalClosure ℚ A Omega
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Omega := Algebra.IsAlgebraic.isIntegral
  letI : FiniteDimensional ℚ A :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
  let N : NumberFieldInOmega :=
    { field := Nfield
      finite := normalClosure.is_finiteDimensional ℚ A Omega }
  have hxA : x ∈ A :=
    IntermediateField.subset_adjoin ℚ ({x} : Set Omega) (Set.mem_singleton x)
  have hxN : x ∈ N.field := IntermediateField.le_normalClosure A hxA
  have hOmega : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  letI : IsGalois ℚ Omega := hOmega
  have hNgal : IsGalois ℚ N.field := IsGalois.normalClosure ℚ A Omega
  letI : IsGalois ℚ N.field := hNgal
  have hcN := restriction_eq_one N
  let y : N.field := ⟨x, hxN⟩
  have hy := ambientRestriction_apply N c y
  rw [hcN] at hy
  simpa using hy.symm

/-! ## Common normal levels -/

/-- A finite Galois `N/ℚ` containing both base fields.  Every field is still
literally an intermediate field of the one `Omega`. -/
structure CommonNormalLevel (F₁ F₂ : NumberFieldInOmega) where
  /-- The common finite normal field. -/
  field : NumberFieldInOmega
  /-- Literal inclusion of the source base. -/
  left_le : F₁.field ≤ field.field
  /-- Literal inclusion of the target base. -/
  right_le : F₂.field ≤ field.field
  /-- Normality over `ℚ`. -/
  isGalois : IsGalois ℚ field.field

attribute [instance] CommonNormalLevel.isGalois

/-- A common finite normal overfield exists (take the normal closure of the
compositum).  This is the inhabitation sanity check for `CommonNormalLevel`.
-/
theorem commonNormalLevel_nonempty (F₁ F₂ : NumberFieldInOmega) :
    Nonempty (CommonNormalLevel F₁ F₂) := by
  let K : IntermediateField ℚ Omega := F₁.field ⊔ F₂.field
  let Nfield := IntermediateField.normalClosure ℚ K Omega
  let N : NumberFieldInOmega :=
    { field := Nfield
      finite := normalClosure.is_finiteDimensional ℚ K Omega }
  have hKN : K ≤ N.field := IntermediateField.le_normalClosure K
  have h₁ : F₁.field ≤ N.field := le_sup_left.trans hKN
  have h₂ : F₂.field ≤ N.field := le_sup_right.trans hKN
  have hOmega : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  letI : IsGalois ℚ Omega := hOmega
  have hN : IsGalois ℚ N.field := IsGalois.normalClosure ℚ K Omega
  exact ⟨⟨N, h₁, h₂, hN⟩⟩

noncomputable instance (F₁ F₂ : NumberFieldInOmega) :
    Nonempty (CommonNormalLevel F₁ F₂) :=
  commonNormalLevel_nonempty F₁ F₂

/-- Inclusion of common normal levels. -/
def CommonNormalLevel.LE
    {F₁ F₂ : NumberFieldInOmega}
    (N M : CommonNormalLevel F₁ F₂) : Prop :=
  N.field.field ≤ M.field.field

/-- Common normal levels are directed. -/
theorem commonNormalLevel_directed
    {F₁ F₂ : NumberFieldInOmega}
    (N M : CommonNormalLevel F₁ F₂) :
    ∃ L : CommonNormalLevel F₁ F₂, N.LE L ∧ M.LE L := by
  let K : IntermediateField ℚ Omega := N.field.field ⊔ M.field.field
  let Lfield := IntermediateField.normalClosure ℚ K Omega
  let L : NumberFieldInOmega :=
    { field := Lfield
      finite := normalClosure.is_finiteDimensional ℚ K Omega }
  have hKL : K ≤ L.field := IntermediateField.le_normalClosure K
  have hNL : N.field.field ≤ L.field := le_sup_left.trans hKL
  have hML : M.field.field ≤ L.field := le_sup_right.trans hKL
  have hOmega : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  letI : IsGalois ℚ Omega := hOmega
  have hL : IsGalois ℚ L.field := IsGalois.normalClosure ℚ K Omega
  let level : CommonNormalLevel F₁ F₂ :=
    { field := L
      left_le := N.left_le.trans hNL
      right_le := N.right_le.trans hNL
      isGalois := hL }
  exact ⟨level, hNL, hML⟩

/-- The copy of `F` inside a finite level `N`, obtained by literal preimage
along `N ↪ Omega`. -/
def fieldAtLevel
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field) :
    IntermediateField ℚ N.field :=
  IntermediateField.comap N.field.val F.field

/-- Defining membership equation for the copy of a base field at a level. -/
@[simp]
theorem mem_fieldAtLevel_iff
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    (x : N.field) :
    x ∈ fieldAtLevel F N hFN ↔ (x.1 : Omega) ∈ F.field :=
  Iff.rfl

/-- The finite predicate defining `C_N`.  Its first conjunct is literal field
transport inside `N`; its second is equality with the named quotient map.
Thus it is a genuine predicate on the finite group `Gal(N/ℚ)`. -/
def FiniteSolutionPredicate
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : CommonNormalLevel F₁ F₂)
    (a : N.field.field ≃ₐ[ℚ] N.field.field) : Prop :=
  IntermediateField.map a.toAlgHom
      (fieldAtLevel F₂ N.field N.right_le) =
      fieldAtLevel F₁ N.field N.left_le ∧
    ∀ g : relativeGaloisGroup F₁ N.field N.left_le,
      (normalLevelQuotientIso theta N.field N.left_le N.right_le g).1 =
        a⁻¹ * g.1 * a

/-- Blueprint equation `eq:C-N`: the finite-level solution set is the
preimage of `FiniteSolutionPredicate` under restriction to `Gal(N/ℚ)`.
Closedness is therefore a finite-cylinder fact, not a separate arithmetic
argument. -/
def finiteLevelSolutionSet
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : CommonNormalLevel F₁ F₂) :
    Set RationalAbsoluteGaloisGroup :=
  (ambientRestriction N.field) ⁻¹'
    {a | FiniteSolutionPredicate theta N a}

/-- Blueprint Lemma `lem:solution-sets`: every `C_N` is nonempty and clopen.
-/
theorem finiteLevelSolutionSet_nonempty_clopen
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : CommonNormalLevel F₁ F₂) :
    Set.Nonempty (finiteLevelSolutionSet theta N) ∧
      IsClopen (finiteLevelSolutionSet theta N) := by
  constructor
  · obtain ⟨alpha, hfield, hiso⟩ :=
      exists_finiteLevel_inducingAutomorphism F₁ F₂ N.field theta
        N.left_le N.right_le
    refine ⟨alpha, ?_⟩
    change FiniteSolutionPredicate theta N (ambientRestriction N.field alpha)
    constructor
    · ext y
      rw [IntermediateField.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_fieldAtLevel_iff] at hx ⊢
        rw [← hfield, mem_conjugateField_iff]
        have ha := ambientRestriction_apply N.field alpha x
        change alpha.symm
          (N.field.field.val (ambientRestriction N.field alpha x)) ∈ F₂.field
        rw [ha, alpha.symm_apply_apply]
        exact hx
      · intro hy
        rw [mem_fieldAtLevel_iff] at hy
        have hy' : alpha.symm y.1 ∈ F₂.field := by
          rw [← hfield, mem_conjugateField_iff] at hy
          exact hy
        let x := (ambientRestriction N.field alpha).symm y
        refine ⟨x, ?_, ?_⟩
        · rw [mem_fieldAtLevel_iff]
          have ha_inv : (ambientRestriction N.field alpha).symm =
              ambientRestriction N.field alpha.symm := by
            change (ambientRestriction N.field alpha)⁻¹ = _
            rw [← map_inv]
            rfl
          have hxval : N.field.field.val x = alpha.symm y.1 := by
            dsimp [x]
            rw [ha_inv]
            exact ambientRestriction_apply N.field alpha.symm y
          change N.field.field.val x ∈ F₂.field
          rw [hxval]
          exact hy'
        · exact (ambientRestriction N.field alpha).apply_symm_apply y
    · intro g
      have h := DFunLike.congr_fun hiso g
      have hval := congrArg Subtype.val h
      rw [finiteConjugationIso_apply] at hval
      exact hval.symm
  · apply (isClopen_discrete
      {a | FiniteSolutionPredicate theta N a}).preimage
    exact @InfiniteGalois.restrictNormalHom_continuous
      ℚ Omega inferInstance inferInstance inferInstance N.field.field
        N.isGalois.to_normal

/-- Restriction from a finer common level gives the nesting
`C_{N'} ⊆ C_N` in `lem:solution-sets`. -/
theorem finiteLevelSolutionSet_anti
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N M : CommonNormalLevel F₁ F₂) (hNM : N.LE M) :
    finiteLevelSolutionSet theta M ⊆ finiteLevelSolutionSet theta N := by
  intro alpha halpha
  change FiniteSolutionPredicate theta M
    (ambientRestriction M.field alpha) at halpha
  change FiniteSolutionPredicate theta N
    (ambientRestriction N.field alpha)
  let i : N.field.field →ₐ[ℚ] M.field.field :=
    IntermediateField.inclusion hNM
  letI : Algebra N.field.field M.field.field := i.toRingHom.toAlgebra
  letI : IsScalarTower ℚ N.field.field M.field.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let r : (M.field.field ≃ₐ[ℚ] M.field.field) →*
      (N.field.field ≃ₐ[ℚ] N.field.field) :=
    AlgEquiv.restrictNormalHom N.field.field
  have hrestrict (beta : RationalAbsoluteGaloisGroup) :
      r (ambientRestriction M.field beta) = ambientRestriction N.field beta := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap N.field.field M.field.field).injective
    calc
      algebraMap N.field.field M.field.field
          (r (ambientRestriction M.field beta) x) =
          ambientRestriction M.field beta
            (algebraMap N.field.field M.field.field x) := by
        change algebraMap N.field.field M.field.field
            ((ambientRestriction M.field beta).restrictNormal N.field.field x) = _
        exact AlgEquiv.restrictNormal_commutes
          (ambientRestriction M.field beta) N.field.field x
      _ = algebraMap N.field.field M.field.field
          (ambientRestriction N.field beta x) := by
        apply M.field.field.val.injective
        calc
          M.field.field.val
              (ambientRestriction M.field beta
                (algebraMap N.field.field M.field.field x)) = beta x.1 :=
            ambientRestriction_apply M.field beta
              (algebraMap N.field.field M.field.field x)
          _ = N.field.field.val (ambientRestriction N.field beta x) :=
            (ambientRestriction_apply N.field beta x).symm
  let aM := ambientRestriction M.field alpha
  let aN := ambientRestriction N.field alpha
  have ha : r aM = aN := hrestrict alpha
  constructor
  · rcases halpha with ⟨hfieldM, hmapM⟩
    ext y
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fieldAtLevel_iff] at hx ⊢
      let xM : M.field.field := algebraMap N.field.field M.field.field x
      have hxM : xM ∈ fieldAtLevel F₂ M.field M.right_le := by
        rw [mem_fieldAtLevel_iff]
        exact hx
      have hcomm : aM xM =
          algebraMap N.field.field M.field.field (aN x) := by
        calc
          aM xM = algebraMap N.field.field M.field.field ((r aM) x) := by
            change aM (algebraMap N.field.field M.field.field x) =
              algebraMap N.field.field M.field.field
                (aM.restrictNormal N.field.field x)
            exact (AlgEquiv.restrictNormal_commutes aM N.field.field x).symm
          _ = algebraMap N.field.field M.field.field (aN x) := by
            rw [ha]
      have hyM : algebraMap N.field.field M.field.field (aN x) ∈
          fieldAtLevel F₁ M.field M.left_le := by
        rw [← hfieldM, IntermediateField.mem_map]
        exact ⟨xM, hxM, hcomm⟩
      rw [mem_fieldAtLevel_iff] at hyM
      exact hyM
    · intro hy
      rw [mem_fieldAtLevel_iff] at hy
      let yM : M.field.field := algebraMap N.field.field M.field.field y
      have hyM : yM ∈ fieldAtLevel F₁ M.field M.left_le := by
        rw [mem_fieldAtLevel_iff]
        exact hy
      rw [← hfieldM, IntermediateField.mem_map] at hyM
      obtain ⟨zM, hzM, hz⟩ := hyM
      let x : N.field.field := aN.symm y
      have hcomm : aM (algebraMap N.field.field M.field.field x) = yM := by
        calc
          aM (algebraMap N.field.field M.field.field x) =
              algebraMap N.field.field M.field.field ((r aM) x) := by
            change aM (algebraMap N.field.field M.field.field x) =
              algebraMap N.field.field M.field.field
                (aM.restrictNormal N.field.field x)
            exact (AlgEquiv.restrictNormal_commutes aM N.field.field x).symm
          _ = algebraMap N.field.field M.field.field (aN x) := by rw [ha]
          _ = yM := by simp [x, yM]
      have hz_eq : zM = algebraMap N.field.field M.field.field x := by
        apply aM.injective
        change aM zM = yM at hz
        rw [hz, hcomm]
      refine ⟨x, ?_, aN.apply_symm_apply y⟩
      rw [mem_fieldAtLevel_iff]
      change N.field.field.val x ∈ F₂.field
      have hzval := congrArg M.field.field.val hz_eq
      have hzval' : N.field.field.val x = M.field.field.val zM := hzval.symm
      rw [hzval']
      rw [mem_fieldAtLevel_iff] at hzM
      exact hzM
  · rcases halpha with ⟨hfieldM, hmapM⟩
    intro g
    obtain ⟨gamma, hgamma⟩ :=
      finiteQuotientMap_surjective F₁ N.field N.left_le g
    let gM := finiteQuotientMap F₁ M.field M.left_le gamma
    have hM := hmapM gM
    have hsigmaM :
        (normalLevelQuotientIso theta M.field M.left_le M.right_le gM).1 =
          (finiteQuotientMap F₂ M.field M.right_le (theta gamma)).1 := by
      have h := normalLevelQuotientIso_comp_restriction
        theta M.field M.left_le M.right_le gamma
      exact congrArg Subtype.val h
    rw [hsigmaM] at hM
    have hrF (F : NumberFieldInOmega) (hF : F.field ≤ N.field.field)
        (hFM : F.field ≤ M.field.field) (beta : absoluteGaloisGroup F) :
        r (finiteQuotientMap F M.field hFM beta).1 =
          (finiteQuotientMap F N.field hF beta).1 := by
      exact hrestrict beta.1
    have hMr := congrArg r hM
    rw [map_mul, map_mul, map_inv, ha,
      hrF F₁ N.left_le M.left_le gamma,
      hrF F₂ N.right_le M.right_le (theta gamma)] at hMr
    have hsigmaN := normalLevelQuotientIso_comp_restriction
      theta N.field N.left_le N.right_le gamma
    rw [hgamma] at hsigmaN
    rw [hgamma] at hMr
    exact (congrArg Subtype.val hsigmaN).trans hMr

/-- Every finite family of solution cylinders has nonempty intersection,
using one common normal overfield. -/
theorem finiteLevelSolutionSet_finiteIntersection
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (S : Finset (CommonNormalLevel F₁ F₂)) :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∀ N ∈ S, alpha ∈ finiteLevelSolutionSet theta N := by
  classical
  have hupper (T : Finset (CommonNormalLevel F₁ F₂)) :
      ∃ L : CommonNormalLevel F₁ F₂, ∀ N ∈ T, N.LE L := by
    induction T using Finset.induction_on with
    | empty =>
        let L := Classical.choice (inferInstance :
          Nonempty (CommonNormalLevel F₁ F₂))
        exact ⟨L, by simp⟩
    | @insert N T hN ih =>
        obtain ⟨M, hM⟩ := ih
        obtain ⟨L, hNL, hML⟩ := commonNormalLevel_directed N M
        refine ⟨L, ?_⟩
        intro K hK
        rw [Finset.mem_insert] at hK
        rcases hK with rfl | hK
        · exact hNL
        · exact (hM K hK).trans hML
  obtain ⟨L, hL⟩ := hupper S
  obtain ⟨alpha, halpha⟩ :=
    (finiteLevelSolutionSet_nonempty_clopen theta L).1
  refine ⟨alpha, ?_⟩
  intro N hNS
  exact finiteLevelSolutionSet_anti theta N L (hL N hNS) halpha

/-- Compactness of `G_ℚ` supplies one point in every finite-level solution
set. -/
theorem exists_mem_all_finiteLevelSolutionSets
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∀ N : CommonNormalLevel F₁ F₂,
        alpha ∈ finiteLevelSolutionSet theta N := by
  classical
  letI : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  have hclosed (N : CommonNormalLevel F₁ F₂) :
      IsClosed (finiteLevelSolutionSet theta N) :=
    (finiteLevelSolutionSet_nonempty_clopen theta N).2.isClosed
  have hfip (S : Finset (CommonNormalLevel F₁ F₂)) :
      (Set.univ ∩ ⋂ N ∈ S, finiteLevelSolutionSet theta N).Nonempty := by
    obtain ⟨alpha, halpha⟩ :=
      finiteLevelSolutionSet_finiteIntersection theta S
    refine ⟨alpha, Set.mem_inter (Set.mem_univ alpha) ?_⟩
    simp only [Set.mem_iInter]
    exact halpha
  obtain ⟨alpha, _, halpha⟩ := isCompact_univ.inter_iInter_nonempty
    (fun N : CommonNormalLevel F₁ F₂ => finiteLevelSolutionSet theta N)
    hclosed hfip
  exact ⟨alpha, Set.mem_iInter.mp halpha⟩

/-! ## Global conjugation, existence, and uniqueness -/

/-- Contravariant conjugation by `alpha`, provided `alpha(F₂)=F₁`. -/
noncomputable def ambientConjugationIso
    (F₁ F₂ : NumberFieldInOmega)
    (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field) :
    absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂ := by
  let forward : absoluteGaloisGroup F₁ → absoluteGaloisGroup F₂ := fun g =>
    ⟨alpha⁻¹ * g.1 * alpha, by
      intro x
      have hax : alpha x.1 ∈ F₁.field := by
        rw [← hfield, mem_conjugateField_iff]
        simp
      let y : F₁.field := ⟨alpha x.1, hax⟩
      change alpha.symm (g.1 (alpha x.1)) = x.1
      rw [show g.1 (alpha x.1) = alpha x.1 from g.2 y,
        alpha.symm_apply_apply]⟩
  have hsymmfield : conjugateField alpha.symm F₁.field = F₂.field := by
    ext x
    rw [mem_conjugateField_iff, ← hfield, mem_conjugateField_iff]
    simp
  let backward : absoluteGaloisGroup F₂ → absoluteGaloisGroup F₁ := fun g =>
    ⟨alpha * g.1 * alpha⁻¹, by
      intro x
      have hax : alpha.symm x.1 ∈ F₂.field := by
        rw [← hsymmfield, mem_conjugateField_iff]
        simp
      let y : F₂.field := ⟨alpha.symm x.1, hax⟩
      change alpha (g.1 (alpha.symm x.1)) = x.1
      rw [show g.1 (alpha.symm x.1) = alpha.symm x.1 from g.2 y,
        alpha.apply_symm_apply]⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro g
        apply Subtype.ext
        change alpha * (alpha⁻¹ * g.1 * alpha) * alpha⁻¹ = g.1
        group
      right_inv := by
        intro g
        apply Subtype.ext
        change alpha⁻¹ * (alpha * g.1 * alpha⁻¹) * alpha = g.1
        group
      map_mul' := by
        intro g h
        apply Subtype.ext
        change alpha⁻¹ * (g.1 * h.1) * alpha =
          (alpha⁻¹ * g.1 * alpha) * (alpha⁻¹ * h.1 * alpha)
        group
      continuous_toFun := by
        change Continuous (fun g : absoluteGaloisGroup F₁ =>
          (⟨alpha⁻¹ * g.1 * alpha, _⟩ : absoluteGaloisGroup F₂))
        fun_prop
      continuous_invFun := by
        change Continuous (fun g : absoluteGaloisGroup F₂ =>
          (⟨alpha * g.1 * alpha⁻¹, _⟩ : absoluteGaloisGroup F₁))
        fun_prop }

/-- Defining equation `alpha_*(g) = alpha⁻¹ g alpha`. -/
@[simp]
theorem ambientConjugationIso_apply
    (F₁ F₂ : NumberFieldInOmega)
    (alpha : RationalAbsoluteGaloisGroup)
    (hfield : conjugateField alpha F₂.field = F₁.field)
    (g : absoluteGaloisGroup F₁) :
    (ambientConjugationIso F₁ F₂ alpha hfield g).1 =
      alpha⁻¹ * g.1 * alpha := by
  rfl

/-- Blueprint Proposition `prop:global-existence`: one ambient automorphism
carries `F₂` to `F₁` and induces `theta` on the full profinite groups. -/
theorem exists_global_inducingAutomorphism
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂) :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∃ hfield : conjugateField alpha F₂.field = F₁.field,
        ambientConjugationIso F₁ F₂ alpha hfield = theta := by
  letI : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  obtain ⟨alpha, hall⟩ := exists_mem_all_finiteLevelSolutionSets theta
  let N₀ := Classical.choice (inferInstance :
    Nonempty (CommonNormalLevel F₁ F₂))
  have hsol₀ : FiniteSolutionPredicate theta N₀
      (ambientRestriction N₀.field alpha) := hall N₀
  have hfield : conjugateField alpha F₂.field = F₁.field := by
    ext x
    rw [mem_conjugateField_iff]
    constructor
    · intro hx
      let z : N₀.field.field := ⟨alpha.symm x, N₀.right_le hx⟩
      have hz : z ∈ fieldAtLevel F₂ N₀.field N₀.right_le := hx
      have hza : ambientRestriction N₀.field alpha z ∈
          fieldAtLevel F₁ N₀.field N₀.left_le := by
        rw [← hsol₀.1, IntermediateField.mem_map]
        exact ⟨z, hz, rfl⟩
      rw [mem_fieldAtLevel_iff] at hza
      have hval := ambientRestriction_apply N₀.field alpha z
      change N₀.field.field.val
        (ambientRestriction N₀.field alpha z) ∈ F₁.field at hza
      rw [hval] at hza
      change alpha (alpha.symm x) ∈ F₁.field at hza
      simpa using hza
    · intro hx
      let y : N₀.field.field := ⟨x, N₀.left_le hx⟩
      have hy : y ∈ fieldAtLevel F₁ N₀.field N₀.left_le := hx
      rw [← hsol₀.1, IntermediateField.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [mem_fieldAtLevel_iff] at hz
      have hval := ambientRestriction_apply N₀.field alpha z
      change alpha.symm x ∈ F₂.field
      have hzx : alpha z.1 = x := by
        calc
          alpha z.1 = N₀.field.field.val
              (ambientRestriction N₀.field alpha z) := hval.symm
          _ = x := congrArg Subtype.val hzy
      rw [← hzx, alpha.symm_apply_apply]
      exact hz
  refine ⟨alpha, hfield, ?_⟩
  apply ContinuousMulEquiv.ext
  intro g
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  let A := IntermediateField.adjoin ℚ ({x} : Set Omega)
  letI : FiniteDimensional ℚ A := by
    letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
    letI : Algebra.IsIntegral ℚ Omega := Algebra.IsAlgebraic.isIntegral
    exact IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
  let K : IntermediateField ℚ Omega := (F₁.field ⊔ F₂.field) ⊔ A
  let Lfield := IntermediateField.normalClosure ℚ K Omega
  let L : NumberFieldInOmega :=
    { field := Lfield
      finite := normalClosure.is_finiteDimensional ℚ K Omega }
  have hKL : K ≤ L.field := IntermediateField.le_normalClosure K
  have h₁L : F₁.field ≤ L.field :=
    (le_sup_left.trans le_sup_left).trans hKL
  have h₂L : F₂.field ≤ L.field :=
    (le_sup_right.trans le_sup_left).trans hKL
  have hLgal : IsGalois ℚ L.field := IsGalois.normalClosure ℚ K Omega
  let level : CommonNormalLevel F₁ F₂ :=
    { field := L
      left_le := h₁L
      right_le := h₂L
      isGalois := hLgal }
  have hxA : x ∈ A :=
    IntermediateField.subset_adjoin ℚ ({x} : Set Omega) (Set.mem_singleton x)
  have hxL : x ∈ L.field := hKL ((show A ≤ K from le_sup_right) hxA)
  let xL : L.field := ⟨x, hxL⟩
  have hsol : FiniteSolutionPredicate theta level
      (ambientRestriction L alpha) := hall level
  let q₁ := finiteQuotientMap F₁ L h₁L g
  let q₂ := finiteQuotientMap F₂ L h₂L (theta g)
  have hsigma := normalLevelQuotientIso_comp_restriction
    theta L h₁L h₂L g
  have hq : q₂.1 = (ambientRestriction L alpha)⁻¹ * q₁.1 *
      ambientRestriction L alpha := by
    exact (congrArg Subtype.val hsigma).symm.trans (hsol.2 q₁)
  rw [ambientConjugationIso_apply]
  let beta : RationalAbsoluteGaloisGroup := alpha⁻¹ * g.1 * alpha
  have hres : ambientRestriction L beta =
      (ambientRestriction L alpha)⁻¹ * q₁.1 * ambientRestriction L alpha := by
    dsimp [beta, q₁]
    rw [map_mul, map_mul, map_inv]
    rfl
  calc
    beta x = L.field.val (ambientRestriction L beta xL) :=
      (ambientRestriction_apply L beta xL).symm
    _ = L.field.val
        (((ambientRestriction L alpha)⁻¹ * q₁.1 *
          ambientRestriction L alpha) xL) := by rw [hres]
    _ = L.field.val (q₂.1 xL) := by rw [hq]
    _ = (theta g).1 x := finiteQuotientMap_apply F₂ L h₂L (theta g) xL

/-- Blueprint Proposition `prop:global-uniqueness`: two ambient
automorphisms inducing the same profinite isomorphism are equal. -/
theorem global_inducingAutomorphism_unique
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (alpha beta : RationalAbsoluteGaloisGroup)
    (halpha : conjugateField alpha F₂.field = F₁.field)
    (hbeta : conjugateField beta F₂.field = F₁.field)
    (ha : ambientConjugationIso F₁ F₂ alpha halpha = theta)
    (hb : ambientConjugationIso F₁ F₂ beta hbeta = theta) :
    alpha = beta := by
  let c : RationalAbsoluteGaloisGroup := beta * alpha⁻¹
  have hc : CentralizesAbsoluteGaloisGroup F₁ c := by
    intro g
    have hmaps : ambientConjugationIso F₁ F₂ alpha halpha g =
        ambientConjugationIso F₁ F₂ beta hbeta g := by
      rw [ha, hb]
    have hval := congrArg Subtype.val hmaps
    rw [ambientConjugationIso_apply, ambientConjugationIso_apply] at hval
    calc
      c * g.1 = beta * (alpha⁻¹ * g.1 * alpha) * alpha⁻¹ := by
        dsimp [c]
        group
      _ = beta * (beta⁻¹ * g.1 * beta) * alpha⁻¹ := by rw [hval]
      _ = g.1 * c := by
        dsimp [c]
        group
  have hc1 : c = 1 := centralizer_absoluteGaloisGroup_eq_one F₁ c hc
  calc
    alpha = 1 * alpha := by group
    _ = c * alpha := by rw [hc1]
    _ = beta := by
      dsimp [c]
      group

end

end NU.NeukirchUchida
