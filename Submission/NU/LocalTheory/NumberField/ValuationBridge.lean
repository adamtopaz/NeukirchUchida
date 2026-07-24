import Submission.NU.LocalTheory.Alternating.FromAEJ
import Submission.NU.LocalTheory.NumberField.Place

/-!
# Number-field valuations as prime-ideal places

Finite places are represented first by nonzero prime ideals of the ring of
integers, exactly as required by Blueprint §10.1(1).  The associated
valuation subring is Mathlib's localization at that prime.  The terminal
lemma identifies every nontrivial AEJ valuation subring with a unique such
prime-ideal place.
-/

open IsDedekindDomain
open scoped NumberField

namespace NU.LocalTheory

noncomputable section

private theorem ringOfIntegers_le_valuationSubring
    {K : Type*} [Field K] [NumberField K] (A : ValuationSubring K) :
    ∀ a : 𝓞 K, (a : K) ∈ A := by
  intro a
  apply (Subring.isIntegrallyClosed_iff.mp
    (inferInstance : IsIntegrallyClosed A))
  exact (NumberField.RingOfIntegers.isIntegral_coe a).tower_top

private def valuationCenterIdeal
    {K : Type*} [Field K] [NumberField K] (A : ValuationSubring K) :
    Ideal (𝓞 K) :=
  (IsLocalRing.maximalIdeal A).comap
    ((algebraMap (𝓞 K) K).codRestrict A
      (ringOfIntegers_le_valuationSubring A))

private theorem valuationCenterIdeal_ne_bot
    {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : A ≠ ⊤) :
    valuationCenterIdeal A ≠ ⊥ := by
  let f : 𝓞 K →+* A :=
    (algebraMap (𝓞 K) K).codRestrict A
      (ringOfIntegers_le_valuationSubring A)
  intro hp
  apply hA
  apply top_unique
  intro x _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hfb_not : f b ∉ IsLocalRing.maximalIdeal A := by
    intro hfb
    have hbp : b ∈ valuationCenterIdeal A := by
      exact hfb
    rw [hp] at hbp
    exact hb0 (Ideal.mem_bot.mp hbp)
  have hfb_unit : IsUnit (f b) := by
    simpa [IsLocalRing.mem_maximalIdeal] using hfb_not
  have hbval : A.valuation (algebraMap (𝓞 K) K b) = 1 := by
    simpa [f] using (A.valuation_eq_one_iff (f b)).mp hfb_unit
  have hbinv : (algebraMap (𝓞 K) K b)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, hbval, inv_one]
  rw [← hab]
  simpa [div_eq_mul_inv] using
    A.mul_mem _ _ (ringOfIntegers_le_valuationSubring A a) hbinv

private def valuationCenterPlace
    {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : A ≠ ⊤) : FinitePlace K :=
  HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime (valuationCenterIdeal_ne_bot A hA) (by
      unfold valuationCenterIdeal
      infer_instance))

private theorem primeValuationSubring_valuationCenterPlace_le
    {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : A ≠ ⊤) :
    primeValuationSubring (valuationCenterPlace A hA) ≤ A := by
  let f : 𝓞 K →+* A :=
    (algebraMap (𝓞 K) K).codRestrict A
      (ringOfIntegers_le_valuationSubring A)
  intro x hx
  change x ∈ HeightOneSpectrum.valuationSubringAtPrime K
    (valuationCenterPlace A hA) at hx
  change x ∈ (Localization.subalgebra.ofField K _
    (valuationCenterPlace A hA).asIdeal.primeCompl_le_nonZeroDivisors).toSubring at hx
  rcases hx with ⟨a, b, hb, rfl⟩
  have hfb_not : f b ∉ IsLocalRing.maximalIdeal A := by
    intro hfb
    have hbp : b ∈ valuationCenterIdeal A := by
      exact hfb
    exact hb hbp
  have hfb_unit : IsUnit (f b) := by
    simpa [IsLocalRing.mem_maximalIdeal] using hfb_not
  have hbval : A.valuation (b : K) = 1 := by
    simpa [f] using (A.valuation_eq_one_iff (f b)).mp hfb_unit
  have hbinv : (b : K)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, hbval, inv_one]
  exact A.mul_mem _ _ (ringOfIntegers_le_valuationSubring A a) hbinv

/-- Blueprint Lemma 4.1 (`lem:number-field-valuations`): every nontrivial
Krull valuation of a number field is the localization at a unique nonzero
prime ideal. -/
theorem numberField_valuations {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : IsNontrivialValuation A) :
    ∃! v : FinitePlace K, A = primeValuationSubring v := by
  let v := valuationCenterPlace A hA
  have hle : primeValuationSubring v ≤ A :=
    primeValuationSubring_valuationCenterPlace_le A hA
  letI : Ring.KrullDimLE 1 (primeValuationSubring v) := by
    change Ring.KrullDimLE 1
      (HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  have heq : primeValuationSubring v = A :=
    ValuationSubring.eq_of_le_of_ne_top (primeValuationSubring v) hle hA
  refine ⟨v, heq.symm, ?_⟩
  intro w hw
  have hvw : primeValuationSubring v = primeValuationSubring w := by
    rw [heq, ← hw]
  apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
  apply (Valuation.isEquiv_iff_valuationSubring _ _).2
  simpa only [primeValuationSubring,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] using
      hvw.symm

/-- The center prime of a nontrivial valuation, defined from the uniqueness
part of `numberField_valuations`. -/
noncomputable def centerFinitePlace {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : IsNontrivialValuation A) :
    FinitePlace K :=
  (numberField_valuations A hA).choose

@[simp]
theorem primeValuationSubring_centerFinitePlace
    {K : Type*} [Field K] [NumberField K]
    (A : ValuationSubring K) (hA : IsNontrivialValuation A) :
    primeValuationSubring (centerFinitePlace A hA) = A := by
  simpa [centerFinitePlace] using (numberField_valuations A hA).choose_spec.1.symm

end

end NU.LocalTheory
