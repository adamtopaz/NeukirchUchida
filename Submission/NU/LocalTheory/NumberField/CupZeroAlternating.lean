import Submission.NU.LocalTheory.NumberField.LocalPlane
import Submission.NU.LocalTheory.NumberField.TameNorm

/-!
# Cup-zero pairs versus alternating pairs over number fields

This file assembles the independent dependency chains from the alternating
and norm calculations.  Its terminal theorem is Blueprint Theorem 5.5.
-/

namespace NU.LocalTheory

noncomputable section

/-- Blueprint (5.6): every cup-zero pair of Kummer characters has zero
determinant under `p,q`. -/
def KummerCupDeterminantCondition {M : Type*} [Field M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (p q : MulCharacter M ℓ) : Prop :=
  ∀ a b : Mˣ,
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) →
      characterDet p q a b = 0

/-- Steinberg cup-zero immediately turns the determinant condition into the
alternating relation. -/
theorem alternatingPair_of_kummerCupDeterminant {M : Type*} [Field M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (p q : MulCharacter M ℓ)
    (hdet : KummerCupDeterminantCondition ζ hζ p q) :
    AlternatingPair ℓ p q := by
  intro a b hab
  exact sub_eq_zero.mp (hdet a b (steinberg_cupZero ζ hζ a b hab))

/-- The span of an independent ordered pair has dimension two. -/
theorem pairSpan_finrank_eq_two {F : Type*} [Field F]
    {ℓ : ℕ} [Fact ℓ.Prime] (p q : MulCharacter F ℓ)
    (hind : PairIndependent (k := ZMod ℓ) p q) :
    Module.finrank (ZMod ℓ) (pairSpan (k := ZMod ℓ) p q) = 2 := by
  have hrange : Set.range (pairVector p q) = {p, q} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [pairVector]
    · intro hx
      rcases hx with (rfl | hx)
      · exact ⟨0, rfl⟩
      · have : x = q := by simpa using hx
        subst x
        exact ⟨1, rfl⟩
  rw [pairSpan, ← hrange, finrank_span_eq_card hind]
  rfl

private theorem valuation_ne_top_of_independent_conclusion
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime]
    (p q : MulCharacter F ℓ)
    (hind : PairIndependent (k := ZMod ℓ) p q)
    (A : ValuationSubring F)
    (hA : SatisfiesValuationConclusion ℓ A p q) : A ≠ ⊤ := by
  intro htop
  subst A
  have hlocalI : localI ℓ (⊤ : ValuationSubring F) = ⊥ := by
    ext r
    constructor
    · intro hr
      rw [Submodule.mem_bot]
      apply AddMonoidHom.ext
      intro z
      cases z with
      | ofMul x =>
        apply hr x
        rw [ValuationSubring.mem_unitGroup_iff]
        let u : (⊤ : ValuationSubring F)ˣ :=
          { val := ⟨(x : F), ValuationSubring.mem_top _⟩
            inv := ⟨(x⁻¹ : Fˣ), ValuationSubring.mem_top _⟩
            val_inv := by ext; simp
            inv_val := by ext; simp }
        simpa [u] using (⊤ : ValuationSubring F).valuation_unit u
    · intro hr
      rw [Submodule.mem_bot] at hr
      subst r
      exact Submodule.zero_mem _
  have hcodim := hA.2
  rw [relativeCodim, hlocalI] at hcodim
  have hcomap :
      Submodule.comap (pairSpan (k := ZMod ℓ) p q).subtype
        (⊥ : Submodule (ZMod ℓ) (MulCharacter F ℓ)) = ⊥ := by
    ext x
    simp
  rw [hcomap] at hcodim
  have hquot : Module.finrank (ZMod ℓ)
      ((pairSpan (k := ZMod ℓ) p q) ⧸
        (⊥ : Submodule (ZMod ℓ) (pairSpan (k := ZMod ℓ) p q))) =
      Module.finrank (ZMod ℓ) (pairSpan (k := ZMod ℓ) p q) :=
    (Submodule.quotEquivOfEqBot
      (⊥ : Submodule (ZMod ℓ) (pairSpan (k := ZMod ℓ) p q)) rfl).finrank_eq
  rw [hquot, pairSpan_finrank_eq_two p q hind] at hcodim
  omega

/-- An independent alternating pair spans a tame finite-place local plane. -/
theorem exists_tame_local_plane_of_alternating
    {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (p q : MulCharacter M ℓ)
    (hind : PairIndependent (k := ZMod ℓ) p q)
    (halt : AlternatingPair ℓ p q) :
    ∃ v : FinitePlace M,
      residueCharacteristic v ≠ ℓ ∧
        pairSpan (k := ZMod ℓ) p q =
          localD ℓ (primeValuationSubring v) := by
  have hchar : ringChar M ≠ ℓ := by
    rw [ringChar.eq_zero (R := M)]
    exact (Fact.out : ℓ.Prime).ne_zero.symm
  obtain ⟨A, hA⟩ :=
    (alternatingPair_iff_exists_valuation hℓodd hchar ζ hζ p q hind).mp halt
  have hAne : A ≠ ⊤ :=
    valuation_ne_top_of_independent_conclusion p q hind A hA
  obtain ⟨v, hAv, _⟩ := numberField_valuations A hAne
  rw [hAv] at hA
  have hv : residueCharacteristic v ≠ ℓ := by
    intro hv
    have hrankD := localD_finrank_eq_one_of_residueChar v hv
    letI : Module.Finite (ZMod ℓ)
        (localD ℓ (primeValuationSubring v)) :=
      Module.finite_of_finrank_pos (by rw [hrankD]; exact Nat.zero_lt_one)
    have hle := Submodule.finrank_mono hA.1
    rw [pairSpan_finrank_eq_two p q hind, hrankD] at hle
    omega
  refine ⟨v, hv, ?_⟩
  have hrankD := localD_finrank_eq_two ζ hζ v hv
  letI : Module.Finite (ZMod ℓ)
      (localD ℓ (primeValuationSubring v)) :=
    Module.finite_of_finrank_pos (by rw [hrankD]; omega)
  exact Submodule.eq_of_le_of_finrank_eq hA.1
    ((pairSpan_finrank_eq_two p q hind).trans hrankD.symm)

private def localDQuotientCharacter
    {F : Type*} [Field F] {n : ℕ} (A : ValuationSubring F)
    (p : localD n A) :
    Additive (Fˣ ⧸ A.principalUnitGroup) →+ ZMod n := by
  let pmul : Fˣ →* Multiplicative (ZMod n) :=
    { toFun := fun x => Multiplicative.ofAdd
        ((p : MulCharacter F n) (Additive.ofMul x))
      map_one' := by simp
      map_mul' := by
        intro x y
        simpa using (p : MulCharacter F n).map_add
          (Additive.ofMul x) (Additive.ofMul y) }
  let qmul : (Fˣ ⧸ A.principalUnitGroup) →* Multiplicative (ZMod n) :=
    QuotientGroup.lift A.principalUnitGroup pmul (by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change (p : MulCharacter F n) (Additive.ofMul x) = 0
      exact p.prop x hx)
  exact
    { toFun := fun x => (qmul x.toMul).toAdd
      map_zero' := by
        change (qmul 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro x y
        change (qmul (x.toMul * y.toMul)).toAdd =
          (qmul x.toMul).toAdd + (qmul y.toMul).toAdd
        rw [map_mul]
        rfl }

private def localDToPrincipalUnitDual
    {F : Type*} [Field F] {n : ℕ} (A : ValuationSubring F)
    (p : localD n A) :
    PrincipalUnitModEll A n →ₗ[ZMod n] ZMod n :=
  (ModN.liftEquiv').symm
    ⟨localDQuotientCharacter A p, by
      intro x
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), CharP.cast_eq_zero,
        zero_smul]⟩

@[simp]
private theorem localDToPrincipalUnitDual_class
    {F : Type*} [Field F] {n : ℕ} (A : ValuationSubring F)
    (p : localD n A) (x : Fˣ) :
    localDToPrincipalUnitDual A p (principalUnitModEllClass A n x) =
      (p : MulCharacter F n) (Additive.ofMul x) := by
  rfl

private theorem characterDet_eq_zero_of_local_classes_dependent
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring F) (p q : MulCharacter F ℓ)
    (hp : p ∈ localD ℓ A) (hq : q ∈ localD ℓ A)
    (a b : Fˣ)
    (hdep : ¬ PairIndependent (k := ZMod ℓ)
      (principalUnitModEllClass A ℓ a)
      (principalUnitModEllClass A ℓ b)) :
    characterDet p q a b = 0 := by
  let P : PrincipalUnitModEll A ℓ →ₗ[ZMod ℓ] ZMod ℓ :=
    localDToPrincipalUnitDual A ⟨p, hp⟩
  let Q : PrincipalUnitModEll A ℓ →ₗ[ZMod ℓ] ZMod ℓ :=
    localDToPrincipalUnitDual A ⟨q, hq⟩
  let x := principalUnitModEllClass A ℓ a
  let y := principalUnitModEllClass A ℓ b
  have hcases : y = 0 ∨ ∃ c : ZMod ℓ, c • y = x := by
    by_cases hy : y = 0
    · exact Or.inl hy
    · right
      rw [PairIndependent, linearIndependent_fin2] at hdep
      simp only [pairVector] at hdep
      push Not at hdep
      exact hdep hy
  rcases hcases with hy | ⟨c, hc⟩
  · have hPy : P y = 0 := by rw [hy, map_zero]
    have hQy : Q y = 0 := by rw [hy, map_zero]
    change P x * Q y - P y * Q x = 0
    rw [hPy, hQy]
    ring
  · have hPx : P x = c * P y := by
      rw [← hc, map_smul]
      rfl
    have hQx : Q x = c * Q y := by
      rw [← hc, map_smul]
      rfl
    change P x * Q y - P y * Q x = 0
    rw [hPx, hQx]
    ring

private theorem character_eq_zero_of_kummerClass_eq_zero
    {F : Type*} [Field F] {ℓ : ℕ}
    (p : MulCharacter F ℓ) (a : Fˣ)
    (ha : kummerQuotientClass ℓ a = 0) :
    p (Additive.ofMul a) = 0 := by
  change (LinearMap.range
    (LinearMap.lsmul ℤ (Additive Fˣ) (ℓ : ℤ))).mkQ
      (Additive.ofMul a) = 0 at ha
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
  obtain ⟨x, hx⟩ := ha
  change (ℓ : ℤ) • x = Additive.ofMul a at hx
  rw [← hx, map_zsmul]
  simpa [← Nat.cast_smul_eq_nsmul (ZMod ℓ), CharP.cast_eq_zero]

private theorem kummerQuotientClass_eq_zero_of_pow
    {M : Type*} [Field M] (n : ℕ) (a u : Mˣ) (hu : u ^ n = a) :
    kummerQuotientClass n a = 0 := by
  rw [← hu]
  change ModN.mkQ n (n • Additive.ofMul u) = 0
  rw [map_nsmul]
  change (LinearMap.range (LinearMap.lsmul ℤ (Additive Mˣ) (n : ℤ))).mkQ
    (n • Additive.ofMul u) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Additive.ofMul u, by simp⟩

/-- Blueprint Theorem 5.5 (`thm:cupzero-alternating`): for an independent
pair over a number field containing `μ_ℓ`, alternating is equivalent to
determinant vanishing on every explicit cup-zero pair. -/
theorem cupZero_alternating_iff {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (p q : MulCharacter M ℓ)
    (hind : PairIndependent (k := ZMod ℓ) p q) :
    AlternatingPair ℓ p q ↔
      KummerCupDeterminantCondition ζ hζ p q := by
  constructor
  · intro halt a b hcup
    obtain ⟨v, hv, hplane⟩ :=
      exists_tame_local_plane_of_alternating hℓodd ζ hζ p q hind halt
    have hp : p ∈ localD ℓ (primeValuationSubring v) := by
      rw [← hplane]
      apply Submodule.subset_span
      simp
    have hq : q ∈ localD ℓ (primeValuationSubring v) := by
      rw [← hplane]
      apply Submodule.subset_span
      simp
    by_cases ha : kummerQuotientClass ℓ a = 0
    · have hpa := character_eq_zero_of_kummerClass_eq_zero p a ha
      have hqa := character_eq_zero_of_kummerClass_eq_zero q a ha
      simp [characterDet, hpa, hqa]
    · have hpow : ∀ x : M, x ^ ℓ ≠ (a : M) := by
        intro x hx
        apply ha
        by_cases hx0 : x = 0
        · subst x
          exact (a.ne_zero (by
            simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
        · exact kummerQuotientClass_eq_zero_of_pow ℓ a (Units.mk0 x hx0)
            (Units.ext (by simpa using hx))
      let f : Polynomial M := Polynomial.X ^ ℓ - Polynomial.C (a : M)
      have hf : Irreducible f :=
        X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime) hpow
      letI : Fact (Irreducible f) := ⟨hf⟩
      let E := AdjoinRoot f
      letI : Field E := inferInstance
      letI : Algebra M E := inferInstance
      letI : FiniteDimensional M E :=
        (AdjoinRoot.powerBasis (Irreducible.ne_zero hf)).finite
      have hroot : (AdjoinRoot.root f : E) ^ ℓ =
          algebraMap M E (a : M) := by
        simpa [E, f] using root_X_pow_sub_C_pow ℓ (a : M)
      have hE : IsKummerRadicalExtension M E ℓ a := by
        refine ⟨AdjoinRoot.root f, hroot, AdjoinRoot.adjoinRoot_eq_top, ?_⟩
        rw [(AdjoinRoot.powerBasis (Irreducible.ne_zero hf)).finrank]
        simp [f]
      have hNorm : IsUnitNorm M E b :=
        (cyclic_norm_criterion ζ hζ a b ha hE).mp hcup
      have hdep :=
        global_norm_local_line hℓodd ζ hζ a b hE hNorm v hv
      exact characterDet_eq_zero_of_local_classes_dependent
        (primeValuationSubring v) p q hp hq a b hdep
  · exact alternatingPair_of_kummerCupDeterminant ζ hζ p q

end

end NU.LocalTheory
