import Submission.NU.AEJ

/-!
# Alternating pairs: algebraic primitives

This file implements the statement-level primitives from Blueprint §§2–3:
the multiplicative mod-`ℓ` quotient, its additive characters, annihilators,
the alternating determinant relation, and the two valuation subspaces
`𝔇_v^ℓ` and `𝕀_v^ℓ`.

Only Mathlib and `NU.AEJ` are imported, as required by the campaign trust
contract.
-/

open scoped Pointwise

namespace NU.LocalTheory

noncomputable section

/-- The multiplicative Kummer quotient `Fˣ / Fˣⁿ`, presented as the explicit
additive quotient `ModN (Additive Fˣ) n`.  This is the coefficient-correct
version of Blueprint (2.1); it is not an `ℓ`-adic quotient. -/
abbrev KummerQuotient (F : Type*) [Field F] (n : ℕ) :=
  ModN (Additive Fˣ) n

/-- The class of a nonzero field element in `Fˣ / Fˣⁿ`. -/
def kummerQuotientClass {F : Type*} [Field F] (n : ℕ) (x : Fˣ) :
    KummerQuotient F n :=
  ModN.mkQ n (Additive.ofMul x)

/-- Multiplicative characters `Fˣ / Fˣⁿ → ZMod n`, represented before
quotienting as additive homomorphisms from `Additive Fˣ`.  Every such map
kills `n`-th powers automatically. -/
abbrev MulCharacter (F : Type*) [Field F] (n : ℕ) :=
  Additive Fˣ →+ ZMod n

/-- Pull a multiplicative character back along a field homomorphism. -/
def pullbackCharacter {F E : Type*} [Field F] [Field E] (n : ℕ)
    (f : F →+* E) (p : MulCharacter E n) : MulCharacter F n where
  toFun x := p (Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul x)))
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
theorem pullbackCharacter_apply {F E : Type*} [Field F] [Field E] (n : ℕ)
    (f : F →+* E) (p : MulCharacter E n) (x : Fˣ) :
    pullbackCharacter n f p (Additive.ofMul x) =
      p (Additive.ofMul (Units.map f.toMonoidHom x)) :=
  rfl

/-- The common kernel of two multiplicative characters, as a subgroup of
`Fˣ`. -/
def commonKernelSubgroup {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) : Subgroup Fˣ where
  carrier := {x | p (Additive.ofMul x) = 0 ∧ q (Additive.ofMul x) = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    constructor
    · simp [map_add, hx.1, hy.1]
    · simp [map_add, hx.2, hy.2]
  inv_mem' := by
    intro x hx
    constructor
    · simp [map_neg, hx.1]
    · simp [map_neg, hx.2]

/-- The common kernel, transported to the AEJ convention of a subset of the
ambient field with zero omitted. -/
def commonKernelCarrier {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) : Set F :=
  (fun x : Fˣ => (x : F)) '' (commonKernelSubgroup p q : Set Fˣ)

/-- The common kernel is an AEJ multiplicative subgroup. -/
theorem commonKernelCarrier_isMulSubgroup {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) :
    NU.AEJ.IsMulSubgroup (commonKernelCarrier p q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨1, (commonKernelSubgroup p q).one_mem, by simp⟩
  · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, (commonKernelSubgroup p q).mul_mem hu hv, by simp⟩
  · rintro a ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, (commonKernelSubgroup p q).inv_mem hu, by simp⟩
  · rintro ⟨u, hu, hzero⟩
    exact Units.ne_zero u hzero

/-- The annihilator of a multiplicative subgroup. -/
def annihilator {F : Type*} [Field F] (n : ℕ) (S : Subgroup Fˣ) :
    Submodule (ZMod n) (MulCharacter F n) where
  carrier := {p | ∀ x : Fˣ, x ∈ S → p (Additive.ofMul x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq x hx
    simp [hp x hx, hq x hx]
  smul_mem' := by
    intro c p hp x hx
    change c • p (Additive.ofMul x) = 0
    simp [hp x hx]

/-- Blueprint (3.2), `𝔇_v^ℓ`: characters annihilating principal units. -/
def localD {F : Type*} [Field F] (n : ℕ) (A : ValuationSubring F) :
    Submodule (ZMod n) (MulCharacter F n) :=
  annihilator n A.principalUnitGroup

/-- Blueprint (3.3), `𝕀_v^ℓ`: characters annihilating all valuation units. -/
def localI {F : Type*} [Field F] (n : ℕ) (A : ValuationSubring F) :
    Submodule (ZMod n) (MulCharacter F n) :=
  annihilator n A.unitGroup

/-- Principal-unit annihilators contain unit annihilators. -/
theorem localI_le_localD {F : Type*} [Field F] (n : ℕ)
    (A : ValuationSubring F) : localI n A ≤ localD n A := by
  intro p hp x hx
  exact hp x (A.principal_units_le_units hx)

/-- Blueprint Definition (3.4): the alternating-pair predicate. -/
def AlternatingPair {F : Type*} [Field F] (n : ℕ)
    (p q : MulCharacter F n) : Prop :=
  ∀ x y : Fˣ, (x : F) + (y : F) = 1 →
    p (Additive.ofMul x) * q (Additive.ofMul y) =
      p (Additive.ofMul y) * q (Additive.ofMul x)

/-- The determinant associated with two characters. -/
def characterDet {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) (x y : Fˣ) : ZMod n :=
  p (Additive.ofMul x) * q (Additive.ofMul y) -
    p (Additive.ofMul y) * q (Additive.ofMul x)

/-- The ordered two-vector used to express linear independence. -/
def pairVector {V : Type*} (p q : V) : Fin 2 → V
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q

/-- Linear independence of an ordered pair. -/
def PairIndependent {k V : Type*} [DivisionRing k] [AddCommGroup V]
    [Module k V] (p q : V) : Prop :=
  LinearIndependent k (pairVector p q)

/-- The span `⟨p,q⟩`. -/
def pairSpan {k V : Type*} [Semiring k] [AddCommMonoid V]
    [Module k V] (p q : V) : Submodule k V :=
  Submodule.span k {p, q}

/-- Codimension of `W ∩ J` inside `W`, written using an explicit quotient.
This is the codimension convention in Blueprint (3.5). -/
def relativeCodim {k V : Type*} [DivisionRing k] [AddCommGroup V]
    [Module k V] (W J : Submodule k V) : ℕ :=
  Module.finrank k (W ⧸ Submodule.comap W.subtype J)

/-- The valuation-side conclusion in Blueprint (3.5). -/
def SatisfiesValuationConclusion {F : Type*} [Field F] (n : ℕ)
    [Fact n.Prime] (A : ValuationSubring F) (p q : MulCharacter F n) : Prop :=
  pairSpan p q ≤ localD n A ∧
    relativeCodim (pairSpan p q) (localI n A) ≤ 1

private theorem character_kills_neg_one
    {F : Type*} [Field F] {ℓ : ℕ} (hℓodd : Odd ℓ)
    (p : MulCharacter F ℓ) :
    p (Additive.ofMul (-1 : Fˣ)) = 0 := by
  apply (ZMod.add_self_eq_zero_iff_eq_zero hℓodd).mp
  rw [← p.map_add]
  have ha : Additive.ofMul (-1 : Fˣ) + Additive.ofMul (-1 : Fˣ) = 0 := by
    ext
    simp
  rw [ha, p.map_zero]

private theorem principalUnit_of_valuation_lt_one
    {F : Type*} [Field F] (A : ValuationSubring F) (x y : Fˣ)
    (hxy : (x : F) + (y : F) = 1)
    (hx : A.valuation (x : F) < 1) :
    y ∈ A.principalUnitGroup := by
  rw [A.mem_principalUnitGroup_iff]
  have hyfield : (y : F) - 1 = -(x : F) := by
    linear_combination hxy
  rw [hyfield, A.valuation.map_neg]
  exact hx

private theorem principalUnit_neg_mul_inv_of_one_lt_valuation
    {F : Type*} [Field F] (A : ValuationSubring F) (x y : Fˣ)
    (hxy : (x : F) + (y : F) = 1)
    (hx : 1 < A.valuation (x : F)) :
    let u : Fˣ := (-1 : Fˣ) * x * y⁻¹
    u ∈ A.principalUnitGroup := by
  dsimp only
  rw [A.mem_principalUnitGroup_iff]
  have hyval : A.valuation (y : F) = A.valuation (x : F) := by
    have hyfield : (y : F) = 1 - (x : F) := by
      linear_combination hxy
    rw [hyfield, A.valuation.map_sub_eq_of_lt_right]
    simpa using hx
  have hfield : ((((-1 : Fˣ) * x * y⁻¹ : Fˣ) : F) - 1) =
      -((y : F)⁻¹) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_neg_one]
    have hy0 : (y : F) ≠ 0 := Units.ne_zero y
    field_simp
    linear_combination -hxy
  rw [hfield, A.valuation.map_neg, map_inv₀, hyval]
  exact inv_lt_one_of_one_lt₀ hx

private theorem character_eq_of_one_lt_valuation
    {F : Type*} [Field F] {ℓ : ℕ} (hℓodd : Odd ℓ)
    (A : ValuationSubring F) (p : MulCharacter F ℓ)
    (hpD : p ∈ localD ℓ A) (x y : Fˣ)
    (hxy : (x : F) + (y : F) = 1)
    (hx : 1 < A.valuation (x : F)) :
    p (Additive.ofMul x) = p (Additive.ofMul y) := by
  let u : Fˣ := (-1 : Fˣ) * x * y⁻¹
  have hu : u ∈ A.principalUnitGroup :=
    principalUnit_neg_mul_inv_of_one_lt_valuation A x y hxy hx
  have hpu : p (Additive.ofMul u) = 0 := hpD u hu
  have hneg := character_kills_neg_one hℓodd p
  have hudom : Additive.ofMul u =
      Additive.ofMul (-1 : Fˣ) + Additive.ofMul x - Additive.ofMul y := by
    rfl
  have hrel : p (Additive.ofMul (-1 : Fˣ)) + p (Additive.ofMul x) -
      p (Additive.ofMul y) = 0 := by
    rw [hudom, map_sub, map_add] at hpu
    exact hpu
  rw [hneg, zero_add, sub_eq_zero] at hrel
  exact hrel

private theorem character_det_on_units_of_relativeCodim_le_one
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring F) (p q : MulCharacter F ℓ)
    (hcodim : relativeCodim (pairSpan p q) (localI ℓ A) ≤ 1)
    {x y : Fˣ} (hx : x ∈ A.unitGroup) (hy : y ∈ A.unitGroup) :
    p (Additive.ofMul x) * q (Additive.ofMul y) =
      p (Additive.ofMul y) * q (Additive.ofMul x) := by
  let W : Submodule (ZMod ℓ) (MulCharacter F ℓ) := pairSpan p q
  let N : Submodule (ZMod ℓ) W := Submodule.comap W.subtype (localI ℓ A)
  letI : Module.Finite (ZMod ℓ) W :=
    Module.Finite.span_of_finite (ZMod ℓ) (by simp)
  have hfin : Module.finrank (ZMod ℓ) (W ⧸ N) ≤ 1 := by
    simpa [relativeCodim, W, N] using hcodim
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hfin
  obtain ⟨r, hr⟩ := N.mkQ_surjective v
  have hpW : p ∈ W := by
    apply Submodule.subset_span
    simp
  have hqW : q ∈ W := by
    apply Submodule.subset_span
    simp
  obtain ⟨c, hc⟩ := hv (N.mkQ ⟨p, hpW⟩)
  obtain ⟨d, hd⟩ := hv (N.mkQ ⟨q, hqW⟩)
  rw [← hr] at hc hd
  have hcp : c • r - (⟨p, hpW⟩ : W) ∈ N := by
    apply (Submodule.Quotient.eq N).mp
    simpa using hc
  have hdq : d • r - (⟨q, hqW⟩ : W) ∈ N := by
    apply (Submodule.Quotient.eq N).mp
    simpa using hd
  have hcpI :
      ((c • r - (⟨p, hpW⟩ : W) : W) : MulCharacter F ℓ) ∈ localI ℓ A := hcp
  have hdqI :
      ((d • r - (⟨q, hqW⟩ : W) : W) : MulCharacter F ℓ) ∈ localI ℓ A := hdq
  have hcpx := hcpI x hx
  have hcpy := hcpI y hy
  have hdqx := hdqI x hx
  have hdqy := hdqI y hy
  change c * (r : MulCharacter F ℓ) (Additive.ofMul x) -
      p (Additive.ofMul x) = 0 at hcpx
  change c * (r : MulCharacter F ℓ) (Additive.ofMul y) -
      p (Additive.ofMul y) = 0 at hcpy
  change d * (r : MulCharacter F ℓ) (Additive.ofMul x) -
      q (Additive.ofMul x) = 0 at hdqx
  change d * (r : MulCharacter F ℓ) (Additive.ofMul y) -
      q (Additive.ofMul y) = 0 at hdqy
  have hpx : p (Additive.ofMul x) =
      c * (r : MulCharacter F ℓ) (Additive.ofMul x) :=
    (sub_eq_zero.mp hcpx).symm
  have hpy : p (Additive.ofMul y) =
      c * (r : MulCharacter F ℓ) (Additive.ofMul y) :=
    (sub_eq_zero.mp hcpy).symm
  have hqx : q (Additive.ofMul x) =
      d * (r : MulCharacter F ℓ) (Additive.ofMul x) :=
    (sub_eq_zero.mp hdqx).symm
  have hqy : q (Additive.ofMul y) =
      d * (r : MulCharacter F ℓ) (Additive.ofMul y) :=
    (sub_eq_zero.mp hdqy).symm
  rw [hpx, hpy, hqx, hqy]
  ring

/-- Blueprint Theorem 3.2, reverse implication: a two-space contained in
`𝔇_v^ℓ` with unit-annihilator codimension at most one is alternating.
Oddness is used to kill `-1`. -/
theorem alternatingPair_of_valuation {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓodd : Odd ℓ) (A : ValuationSubring F)
    (p q : MulCharacter F ℓ)
    (hA : SatisfiesValuationConclusion ℓ A p q) :
    AlternatingPair ℓ p q := by
  have hpW : p ∈ pairSpan (k := ZMod ℓ) p q := by
    apply Submodule.subset_span
    simp
  have hqW : q ∈ pairSpan (k := ZMod ℓ) p q := by
    apply Submodule.subset_span
    simp
  have hpD : p ∈ localD ℓ A := hA.1 hpW
  have hqD : q ∈ localD ℓ A := hA.1 hqW
  intro x y hxy
  by_cases hxsmall : A.valuation (x : F) < 1
  · have hyP := principalUnit_of_valuation_lt_one A x y hxy hxsmall
    have hp0 := hpD y hyP
    have hq0 := hqD y hyP
    rw [hp0, hq0, mul_zero, zero_mul]
  by_cases hysmall : A.valuation (y : F) < 1
  · have hxP := principalUnit_of_valuation_lt_one A y x
      (by simpa [add_comm] using hxy) hysmall
    have hp0 := hpD x hxP
    have hq0 := hqD x hxP
    rw [hp0, hq0, zero_mul, mul_zero]
  by_cases hxlarge : 1 < A.valuation (x : F)
  · have hp_eq := character_eq_of_one_lt_valuation hℓodd A p hpD x y hxy hxlarge
    have hq_eq := character_eq_of_one_lt_valuation hℓodd A q hqD x y hxy hxlarge
    rw [hp_eq, hq_eq]
  by_cases hylarge : 1 < A.valuation (y : F)
  · have hp_eq := character_eq_of_one_lt_valuation hℓodd A p hpD y x
      (by simpa [add_comm] using hxy) hylarge
    have hq_eq := character_eq_of_one_lt_valuation hℓodd A q hqD y x
      (by simpa [add_comm] using hxy) hylarge
    rw [hp_eq, hq_eq]
  have hxunit : x ∈ A.unitGroup := by
    rw [A.mem_unitGroup_iff]
    exact le_antisymm (not_lt.mp hxlarge) (not_lt.mp hxsmall)
  have hyunit : y ∈ A.unitGroup := by
    rw [A.mem_unitGroup_iff]
    exact le_antisymm (not_lt.mp hylarge) (not_lt.mp hysmall)
  exact character_det_on_units_of_relativeCodim_le_one A p q hA.2 hxunit hyunit

end

end NU.LocalTheory
