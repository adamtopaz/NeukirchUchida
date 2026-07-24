import Mathlib

/-!
# Primitive number-field places and local multiplicative quotients

This file contains only Mathlib-based definitions shared by the independent
alternating and cohomological/norm branches.  In particular it has no AEJ or
local-theory import.
-/

open IsDedekindDomain
open scoped NumberField

namespace NU.LocalTheory

noncomputable section

/-- A finite place of a number field, represented by a nonzero prime ideal of
its ring of integers. -/
abbrev FinitePlace (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K)

/-- The localized DVR `𝓞_{K,𝔭}` as a valuation subring of `K`. -/
def primeValuationSubring {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : ValuationSubring K :=
  HeightOneSpectrum.valuationSubringAtPrime K v

/-- The localization has the expected denominator description. -/
theorem mem_primeValuationSubring_iff {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (x : K) :
    x ∈ primeValuationSubring v ↔
      ∃ a b : 𝓞 K, b ∉ v.asIdeal ∧ x * (b : K) = (a : K) := by
  change x ∈ (HeightOneSpectrum.valuationSubringAtPrime K v).toSubring ↔ _
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    have hb' : b ≠ 0 := fun h ↦ hb (h ▸ v.asIdeal.zero_mem)
    have hb0 : (b : K) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb'
    refine ⟨a, b, hb, ?_⟩
    field_simp
  · rintro ⟨a, b, hb, hxb⟩
    have hb' : b ≠ 0 := fun h ↦ hb (h ▸ v.asIdeal.zero_mem)
    have hb0 : (b : K) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb'
    refine ⟨a, b, hb, ?_⟩
    rw [← div_eq_mul_inv, eq_div_iff hb0]
    exact hxb

/-- A prime localization is a nontrivial valuation subring. -/
theorem primeValuationSubring_ne_top {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : primeValuationSubring v ≠ ⊤ := by
  rw [primeValuationSubring,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

/-- The residue field attached to a prime-ideal place. -/
abbrev ResidueFieldAt {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) :=
  IsLocalRing.ResidueField (primeValuationSubring v)

/-- The residue characteristic of a finite place. -/
def residueCharacteristic {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : ℕ :=
  ringChar (ResidueFieldAt v)

/-- A valuation subring is nontrivial precisely when it is not the full
field. -/
def IsNontrivialValuation {K : Type*} [Field K]
    (A : ValuationSubring K) : Prop :=
  A ≠ ⊤

/-- The quotient `Fˣ/(U_A¹ Fˣⁿ)`, presented explicitly by first quotienting
by principal units and then by `n`-multiples. -/
abbrev PrincipalUnitModEll {F : Type*} [Field F]
    (A : ValuationSubring F) (n : ℕ) :=
  ModN (Additive (Fˣ ⧸ A.principalUnitGroup)) n

/-- The class of `x` in `Fˣ/(U_A¹ Fˣⁿ)`. -/
def principalUnitModEllClass {F : Type*} [Field F]
    (A : ValuationSubring F) (n : ℕ) (x : Fˣ) :
    PrincipalUnitModEll A n :=
  ModN.mkQ n (Additive.ofMul (QuotientGroup.mk x))

/-- The residue-unit summand modulo `n`-th powers. -/
abbrev ResidueUnitModEll {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (n : ℕ) :=
  ModN (Additive (ResidueFieldAt v)ˣ) n

end

end NU.LocalTheory
