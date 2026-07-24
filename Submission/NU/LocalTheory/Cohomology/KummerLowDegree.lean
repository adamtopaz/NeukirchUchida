import Submission.NU.LocalTheory.Alternating.Basic
import Submission.NU.LocalTheory.Cohomology.CupZero
import Submission.NU.LocalTheory.Cohomology.ProfiniteDual
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Low-degree Kummer theory and the cyclic norm criterion

This file exposes the exact low-degree interface required by packets.  It
contains the Kummer equivalence, its compatibility with evaluation, the
cyclic norm criterion of Blueprint Lemma 5.1, and Steinberg cup-zero.  No
Merkurjev–Suslin theorem is assumed.
-/

namespace NU.LocalTheory

noncomputable section

open scoped Pointwise

/-- The defining root-action equations for a candidate degree-one Kummer
equivalence.  Including these equations prevents choosing an unrelated
linear equivalence. -/
def IsKummerEquiv {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M)
    (e : KummerQuotient M ℓ ≃ₗ[ZMod ℓ]
      ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ) : Prop :=
  ∀ a : Mˣ, ∃ α : AlgebraicClosure M,
    α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
    ∀ σ : Field.absoluteGaloisGroup M,
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
        (algebraMap M (AlgebraicClosure M) ζ) ^
            (continuousCharacterValue (e (kummerQuotientClass ℓ a)) σ).val * α

private theorem primitiveRoot_natCast_ne_zero'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    {ζ : M} (hζ : IsPrimitiveRoot ζ ℓ) : (ℓ : M) ≠ 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : ℓ.Prime).ne_zero
  subst ℓ
  have hp : (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) =
      (n : M) + 1 := hζ.prod_one_sub_pow_eq_order
  rw [show (n.succ : M) = (n : M) + 1 by simp, ← hp,
    Finset.prod_ne_zero_iff]
  intro i hi
  simp only [Finset.mem_range] at hi
  apply sub_ne_zero.mpr
  exact (hζ.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero i) (Nat.succ_lt_succ hi)).symm

private noncomputable def kummerRoot'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) : AlgebraicClosure M := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  have hcast : (ℓ : S) ≠ 0 := by
    rw [← map_natCast (algebraMap M S)]
    simpa only [map_zero] using
      (algebraMap M S).injective.ne (primitiveRoot_natCast_ne_zero' hζ)
  letI : NeZero (ℓ : S) := ⟨hcast⟩
  exact (IsSepClosed.exists_pow_nat_eq
    (algebraMap M S (a : M)) ℓ).choose.1

private theorem kummerRoot_pow'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    kummerRoot' ζ hζ a ^ ℓ =
      algebraMap M (AlgebraicClosure M) (a : M) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  have hcast : (ℓ : S) ≠ 0 := by
    rw [← map_natCast (algebraMap M S)]
    simpa only [map_zero] using
      (algebraMap M S).injective.ne (primitiveRoot_natCast_ne_zero' hζ)
  letI : NeZero (ℓ : S) := ⟨hcast⟩
  unfold kummerRoot'
  dsimp only
  let r : S := (IsSepClosed.exists_pow_nat_eq
    (algebraMap M S (a : M)) ℓ).choose
  change (r.1 : A) ^ ℓ = algebraMap M A (a : M)
  calc
    (r.1 : A) ^ ℓ = ((r ^ ℓ : S) : A) := rfl
    _ = algebraMap M A (a : M) := congrArg (fun x : S => (x : A))
      (IsSepClosed.exists_pow_nat_eq
        (algebraMap M S (a : M)) ℓ).choose_spec

private theorem kummerRoot_ne_zero'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    kummerRoot' ζ hζ a ≠ 0 := by
  intro h
  have hmap : algebraMap M (AlgebraicClosure M) (a : M) ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap M (AlgebraicClosure M)).injective.ne (Units.ne_zero a)
  apply hmap
  rw [← kummerRoot_pow' ζ hζ a, h,
    zero_pow (Fact.out : ℓ.Prime).ne_zero]

private theorem kummerActionRatio_pow'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ : Field.absoluteGaloisGroup M) :
    ((show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
      (kummerRoot' ζ hζ a) / kummerRoot' ζ hζ a) ^ ℓ =
      (1 : AlgebraicClosure M) := by
  let A := AlgebraicClosure M
  let σe : A ≃ₐ[M] A := σ
  let α : A := kummerRoot' ζ hζ a
  have hα : α ^ ℓ = algebraMap M A (a : M) := kummerRoot_pow' ζ hζ a
  change (σe α / α) ^ ℓ = 1
  calc
    (σe α / α) ^ ℓ = σe (α ^ ℓ) / α ^ ℓ := by rw [div_pow, map_pow]
    _ = σe (algebraMap M A (a : M)) / algebraMap M A (a : M) := by rw [hα]
    _ = algebraMap M A (a : M) / algebraMap M A (a : M) := by
      rw [σe.commutes]
    _ = 1 := div_self ((map_ne_zero (algebraMap M A)).2 (Units.ne_zero a))

private noncomputable def kummerActionIndex'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ : Field.absoluteGaloisGroup M) : Fin ℓ := by
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  let ratio : A := (show A ≃ₐ[M] A from σ)
    (kummerRoot' ζ hζ a) / kummerRoot' ζ hζ a
  have hratio : ratio ^ ℓ = 1 := kummerActionRatio_pow' ζ hζ a σ
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact ⟨(hζA.eq_pow_of_pow_eq_one hratio).choose,
    (hζA.eq_pow_of_pow_eq_one hratio).choose_spec.1⟩

private theorem kummerActionIndex_spec'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ : Field.absoluteGaloisGroup M) :
    (algebraMap M (AlgebraicClosure M) ζ) ^
        (kummerActionIndex' ζ hζ a σ).val =
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
        (kummerRoot' ζ hζ a) / kummerRoot' ζ hζ a := by
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  let ratio : A := (show A ≃ₐ[M] A from σ)
    (kummerRoot' ζ hζ a) / kummerRoot' ζ hζ a
  have hratio : ratio ^ ℓ = 1 := kummerActionRatio_pow' ζ hζ a σ
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact (hζA.eq_pow_of_pow_eq_one hratio).choose_spec.2

private theorem kummerActionEquation'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ : Field.absoluteGaloisGroup M) :
    (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
        (kummerRoot' ζ hζ a) =
      (algebraMap M (AlgebraicClosure M) ζ) ^
          (kummerActionIndex' ζ hζ a σ).val * kummerRoot' ζ hζ a := by
  rw [kummerActionIndex_spec']
  exact (div_mul_cancel₀ _ (kummerRoot_ne_zero' ζ hζ a)).symm

private theorem kummerActionIndex_mul'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ τ : Field.absoluteGaloisGroup M) :
    ((kummerActionIndex' ζ hζ a (σ * τ)).val : ZMod ℓ) =
      (kummerActionIndex' ζ hζ a σ).val +
        (kummerActionIndex' ζ hζ a τ).val := by
  let A := AlgebraicClosure M
  let α : A := kummerRoot' ζ hζ a
  let ζA : A := algebraMap M A ζ
  let σe : A ≃ₐ[M] A := σ
  let τe : A ≃ₐ[M] A := τ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  have hα0 : α ≠ 0 := kummerRoot_ne_zero' ζ hζ a
  have hσ := kummerActionEquation' ζ hζ a σ
  have hτ := kummerActionEquation' ζ hζ a τ
  have hστ := kummerActionEquation' ζ hζ a (σ * τ)
  have hp : ζA ^ (kummerActionIndex' ζ hζ a (σ * τ)).val =
      ζA ^ ((kummerActionIndex' ζ hζ a σ).val +
        (kummerActionIndex' ζ hζ a τ).val) := by
    apply mul_right_cancel₀ hα0
    rw [← hστ]
    change σe (τe α) = _
    rw [hτ, map_mul, map_pow]
    have hfix : σe ζA = ζA := by simp [σe, ζA, A]
    rw [hfix, hσ]
    simp only [pow_add]
    ring
  rw [← Nat.cast_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ ℓ).2
  let ζu : Aˣ := Units.mk0 ζA
    (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero)
  have hζu : IsPrimitiveRoot ζu ℓ := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [ζu] using hζA
  have hpu : ζu ^ (kummerActionIndex' ζ hζ a (σ * τ)).val =
      ζu ^ ((kummerActionIndex' ζ hζ a σ).val +
        (kummerActionIndex' ζ hζ a τ).val) := by
    apply Units.ext
    simpa [ζu] using hp
  have hm := (pow_eq_pow_iff_modEq
    (x := ζu)
    (n := (kummerActionIndex' ζ hζ a (σ * τ)).val)
    (m := (kummerActionIndex' ζ hζ a σ).val +
      (kummerActionIndex' ζ hζ a τ).val)).mp hpu
  simpa only [← hζu.eq_orderOf] using hm

private def rawKummerAddHom'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    Additive (Field.absoluteGaloisGroup M) →+ ZMod ℓ where
  toFun x := ((kummerActionIndex' ζ hζ a (Additive.toMul x)).val : ZMod ℓ)
  map_zero' := by
    let e : ZMod ℓ :=
      ((kummerActionIndex' ζ hζ a (1 : Field.absoluteGaloisGroup M)).val : ZMod ℓ)
    have he : e = e + e := by
      simpa [e] using kummerActionIndex_mul' ζ hζ a
        (1 : Field.absoluteGaloisGroup M) 1
    apply add_left_cancel (a := e)
    simpa [e] using he.symm
  map_add' x y := by
    exact kummerActionIndex_mul' ζ hζ a (Additive.toMul x) (Additive.toMul y)

private theorem rawKummerAddHom_eq_zero_of_fix'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (σ : Field.absoluteGaloisGroup M)
    (hfix : (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
      (kummerRoot' ζ hζ a) = kummerRoot' ζ hζ a) :
    rawKummerAddHom' ζ hζ a (Additive.ofMul σ) = 0 := by
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  have hact := kummerActionEquation' ζ hζ a σ
  rw [hfix] at hact
  have hp : ζA ^ (kummerActionIndex' ζ hζ a σ).val = 1 := by
    apply mul_right_cancel₀ (kummerRoot_ne_zero' ζ hζ a)
    simpa [A, ζA] using hact.symm
  have hi : (kummerActionIndex' ζ hζ a σ).val = 0 := by
    by_contra hi0
    exact hζA.pow_ne_one_of_pos_of_lt hi0
      (kummerActionIndex' ζ hζ a σ).isLt hp
  change ((kummerActionIndex' ζ hζ a σ).val : ZMod ℓ) = 0
  rw [hi]
  simp

private theorem rawKummerAddHom_continuous'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    Continuous (rawKummerAddHom' ζ hζ a) := by
  let A := AlgebraicClosure M
  let α : A := kummerRoot' ζ hζ a
  letI : Algebra.IsIntegral M A := Algebra.IsAlgebraic.isIntegral
  apply continuous_of_continuousAt_zero (rawKummerAddHom' ζ hζ a)
  rw [continuousAt_def]
  intro s hs
  have hs0 : (0 : ZMod ℓ) ∈ s := by
    simpa only [map_zero] using mem_of_mem_nhds hs
  let U : Set (Additive (Field.absoluteGaloisGroup M)) :=
    {x | (show A ≃ₐ[M] A from Additive.toMul x) α = α}
  have hUopen : IsOpen U := by
    change IsOpen {σ : A ≃ₐ[M] A | σ α = α}
    rw [show {σ : A ≃ₐ[M] A | σ α = α} =
      (MulAction.stabilizer (A ≃ₐ[M] A) α : Set (A ≃ₐ[M] A)) by
        ext σ
        change (σ α = α) ↔ σ ∈ MulAction.stabilizer (A ≃ₐ[M] A) α
        simp only [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]]
    exact @stabilizer_isOpen_of_isIntegral M A _ _ _ this α
  have hUzero : (0 : Additive (Field.absoluteGaloisGroup M)) ∈ U := by
    change (show A ≃ₐ[M] A from (1 : Field.absoluteGaloisGroup M)) α = α
    rfl
  apply Filter.mem_of_superset (hUopen.mem_nhds hUzero)
  intro x hx
  change rawKummerAddHom' ζ hζ a x ∈ s
  have hz : rawKummerAddHom' ζ hζ a x = 0 := by
    simpa using rawKummerAddHom_eq_zero_of_fix' ζ hζ a
      (Additive.toMul x) hx
  rw [hz]
  exact hs0

private def rawKummerCharacter'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ :=
  ⟨rawKummerAddHom' ζ hζ a, rawKummerAddHom_continuous' ζ hζ a⟩

private theorem rawKummerCharacter_definingEquation'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    ∃ α : AlgebraicClosure M,
      α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
      ∀ σ : Field.absoluteGaloisGroup M,
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
          (algebraMap M (AlgebraicClosure M) ζ) ^
              (continuousCharacterValue
                (rawKummerCharacter' ζ hζ a) σ).val * α := by
  refine ⟨kummerRoot' ζ hζ a, kummerRoot_pow' ζ hζ a, ?_⟩
  intro σ
  have hv : continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ =
      ((kummerActionIndex' ζ hζ a σ).val : ZMod ℓ) := rfl
  rw [hv, ZMod.val_natCast,
    Nat.mod_eq_of_lt (kummerActionIndex' ζ hζ a σ).isLt]
  exact kummerActionEquation' ζ hζ a σ

private theorem rawKummerCharacter_eq_of_definingEquation'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (χ : ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ)
    (hχ : ∃ α : AlgebraicClosure M,
      α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
      ∀ σ : Field.absoluteGaloisGroup M,
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
          (algebraMap M (AlgebraicClosure M) ζ) ^
              (continuousCharacterValue χ σ).val * α) :
    χ = rawKummerCharacter' ζ hζ a := by
  obtain ⟨α, hαpow, hαeq⟩ := hχ
  obtain ⟨β, hβpow, hβeq⟩ := rawKummerCharacter_definingEquation' ζ hζ a
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hmapa : algebraMap M A (a : M) ≠ 0 :=
    (map_ne_zero (algebraMap M A)).2 (Units.ne_zero a)
  have hα0 : α ≠ 0 := by
    intro hα
    apply hmapa
    rw [← hαpow, hα, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hratio : (β / α) ^ ℓ = (1 : A) := by
    rw [div_pow, hβpow, hαpow, div_self hmapa]
  obtain ⟨j, _, hj⟩ := hζA.eq_pow_of_pow_eq_one hratio
  have hβα : β = ζA ^ j * α := by
    rw [hj, div_mul_cancel₀ β hα0]
  apply ContinuousAddMonoidHom.ext
  intro x
  let σ : Field.absoluteGaloisGroup M := Additive.toMul x
  let σe : A ≃ₐ[M] A := σ
  change continuousCharacterValue χ σ =
    continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ
  have heq :
      ζA ^ (continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ j * (ζA ^ (continuousCharacterValue χ σ).val * α) := by
    calc
      ζA ^ (continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ (continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ).val * β := by
          rw [hβα]
      _ = σe β := (hβeq σ).symm
      _ = σe (ζA ^ j * α) := congrArg (fun y => σe y) hβα
      _ = ζA ^ j * σe α := by
        have hsζ : σe ζA = ζA := by simp [σe, ζA, A]
        rw [map_mul, map_pow, hsζ]
      _ = ζA ^ j * (ζA ^ (continuousCharacterValue χ σ).val * α) := by
        have hsα : σe α = ζA ^ (continuousCharacterValue χ σ).val * α := by
          simpa [σe, ζA, A] using hαeq σ
        rw [hsα]
  have hpowequal :
      ζA ^ (continuousCharacterValue χ σ).val =
        ζA ^ (continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ).val := by
    apply mul_left_cancel₀
      (pow_ne_zero j (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero))
    apply mul_right_cancel₀ hα0
    simpa [mul_assoc, mul_left_comm, mul_comm] using heq.symm
  apply ZMod.val_injective ℓ
  exact hζA.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpowequal

private theorem primitiveRoot_pow_val_add'
    {A : Type*} [Field A] {ℓ : ℕ} [Fact ℓ.Prime]
    {ζ : A} (hζ : IsPrimitiveRoot ζ ℓ) (x y : ZMod ℓ) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [ZMod.val_add]
  calc
    ζ ^ ((x.val + y.val) % ℓ) = ζ ^ (x.val + y.val) :=
      pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hζ.pow_eq_one
    _ = ζ ^ x.val * ζ ^ y.val := pow_add ζ x.val y.val

private theorem rawKummerCharacter_mul'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ) :
    rawKummerCharacter' ζ hζ (a * b) =
      rawKummerCharacter' ζ hζ a + rawKummerCharacter' ζ hζ b := by
  symm
  apply rawKummerCharacter_eq_of_definingEquation' ζ hζ (a * b)
    (rawKummerCharacter' ζ hζ a + rawKummerCharacter' ζ hζ b)
  let A := AlgebraicClosure M
  let α : A := kummerRoot' ζ hζ a
  let β : A := kummerRoot' ζ hζ b
  let ζA : A := algebraMap M A ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  refine ⟨α * β, ?_, ?_⟩
  · rw [mul_pow, kummerRoot_pow' ζ hζ a, kummerRoot_pow' ζ hζ b,
      ← map_mul]
    rfl
  · intro σ
    let σe : A ≃ₐ[M] A := σ
    let va : ZMod ℓ := continuousCharacterValue
      (rawKummerCharacter' ζ hζ a) σ
    let vb : ZMod ℓ := continuousCharacterValue
      (rawKummerCharacter' ζ hζ b) σ
    have hva : va = ((kummerActionIndex' ζ hζ a σ).val : ZMod ℓ) := rfl
    have hvaval : va.val = (kummerActionIndex' ζ hζ a σ).val := by
      rw [hva, ZMod.val_natCast,
        Nat.mod_eq_of_lt (kummerActionIndex' ζ hζ a σ).isLt]
    have hvb : vb = ((kummerActionIndex' ζ hζ b σ).val : ZMod ℓ) := rfl
    have hvbval : vb.val = (kummerActionIndex' ζ hζ b σ).val := by
      rw [hvb, ZMod.val_natCast,
        Nat.mod_eq_of_lt (kummerActionIndex' ζ hζ b σ).isLt]
    have ha : σe α = ζA ^ va.val * α := by
      simpa [σe, α, ζA, A, hvaval] using
        kummerActionEquation' ζ hζ a σ
    have hb : σe β = ζA ^ vb.val * β := by
      simpa [σe, β, ζA, A, hvbval] using
        kummerActionEquation' ζ hζ b σ
    have hv : continuousCharacterValue
        (rawKummerCharacter' ζ hζ a + rawKummerCharacter' ζ hζ b) σ = va + vb := by
      rfl
    rw [map_mul, ha, hb, hv, primitiveRoot_pow_val_add' hζA]
    ring

private theorem rawKummerCharacter_one'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    rawKummerCharacter' ζ hζ (1 : Mˣ) = 0 := by
  symm
  apply rawKummerCharacter_eq_of_definingEquation' ζ hζ (1 : Mˣ) 0
  refine ⟨1, by simp, ?_⟩
  intro σ
  simp [continuousCharacterValue]

private def rawKummerUnitsHom'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    Additive Mˣ →+ ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ where
  toFun x := rawKummerCharacter' ζ hζ (Additive.toMul x)
  map_zero' := rawKummerCharacter_one' ζ hζ
  map_add' x y := rawKummerCharacter_mul' ζ hζ
    (Additive.toMul x) (Additive.toMul y)

private def rawKummerLinear'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    KummerQuotient M ℓ →ₗ[ZMod ℓ]
      ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ :=
  (ModN.liftEquiv').symm ⟨rawKummerUnitsHom' ζ hζ, by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), CharP.cast_eq_zero, zero_smul]⟩

@[simp]
private theorem rawKummerLinear_class'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    rawKummerLinear' ζ hζ (kummerQuotientClass ℓ a) =
      rawKummerCharacter' ζ hζ a := by
  rfl

private theorem kummerRoot_mem_separableClosure'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    kummerRoot' ζ hζ a ∈ separableClosure M (AlgebraicClosure M) := by
  let A := AlgebraicClosure M
  let S := separableClosure M A
  letI : Normal M A := inferInstance
  letI : IsGalois M S := separableClosure.isGalois M A
  have hcast : (ℓ : S) ≠ 0 := by
    rw [← map_natCast (algebraMap M S)]
    simpa only [map_zero] using
      (algebraMap M S).injective.ne (primitiveRoot_natCast_ne_zero' hζ)
  letI : NeZero (ℓ : S) := ⟨hcast⟩
  unfold kummerRoot'
  dsimp only
  exact (IsSepClosed.exists_pow_nat_eq
    (algebraMap M S (a : M)) ℓ).choose.2

private theorem kummerQuotientClass_eq_zero_of_pow'
    {M : Type*} [Field M] (n : ℕ) (a u : Mˣ) (hu : u ^ n = a) :
    kummerQuotientClass n a = 0 := by
  rw [← hu]
  change ModN.mkQ n (n • Additive.ofMul u) = 0
  rw [map_nsmul]
  change (LinearMap.range (LinearMap.lsmul ℤ (Additive Mˣ) (n : ℤ))).mkQ
    (n • Additive.ofMul u) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Additive.ofMul u, by simp⟩

private theorem rawKummerLinear_injective'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (rawKummerLinear' ζ hζ) := by
  intro x₁ x₂ h₁₂
  suffices x₁ - x₂ = 0 by exact sub_eq_zero.mp this
  let x := x₁ - x₂
  change x = 0
  have hx : rawKummerLinear' ζ hζ x = 0 := by
    dsimp [x]
    rw [map_sub, h₁₂, sub_self]
  obtain ⟨g, hg⟩ :=
    (LinearMap.range (LinearMap.lsmul ℤ (Additive Mˣ) (ℓ : ℤ))).mkQ_surjective x
  rw [← hg] at hx ⊢
  cases g with
  | ofMul a =>
    change kummerQuotientClass ℓ a = 0
    have hchar : rawKummerCharacter' ζ hζ a = 0 := by
      change rawKummerLinear' ζ hζ (kummerQuotientClass ℓ a) = 0 at hx
      simpa only [rawKummerLinear_class'] using hx
    let A := AlgebraicClosure M
    let S := separableClosure M A
    letI : Normal M A := inferInstance
    letI : IsGalois M S := separableClosure.isGalois M A
    let αS : S := ⟨kummerRoot' ζ hζ a,
      kummerRoot_mem_separableClosure' ζ hζ a⟩
    have hfixedA (σ : Field.absoluteGaloisGroup M) :
        (show A ≃ₐ[M] A from σ) (αS : A) = αS := by
      have hv := congrArg (fun χ => continuousCharacterValue χ σ) hchar
      have hact := kummerActionEquation' ζ hζ a σ
      have hz : continuousCharacterValue (rawKummerCharacter' ζ hζ a) σ = 0 := by
        have hz0 : continuousCharacterValue
            (0 : ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ) σ = 0 := rfl
        exact hv.trans hz0
      have hindex : (kummerActionIndex' ζ hζ a σ).val = 0 := by
        have hcast : ((kummerActionIndex' ζ hζ a σ).val : ZMod ℓ) = 0 := by
          exact hz
        have hval := congrArg ZMod.val hcast
        simpa [ZMod.val_zero, ZMod.val_natCast,
          Nat.mod_eq_of_lt (kummerActionIndex' ζ hζ a σ).isLt] using hval
      simpa [A, αS, hindex] using hact
    have hfixedS (ρ : S ≃ₐ[M] S) : ρ αS = αS := by
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
        (F := M) (K₁ := S) A ρ
      have hr := DFunLike.congr_fun hσ αS
      have hrestr : (AlgEquiv.restrictNormalHom S σ) αS = αS := by
        apply Subtype.ext
        rw [AlgEquiv.restrictNormalHom_apply]
        exact hfixedA σ
      exact hr.symm.trans hrestr
    have hbase : (αS : S) ∈ Set.range (algebraMap M S) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed αS).2 hfixedS
    obtain ⟨u, hu⟩ := hbase
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      apply kummerRoot_ne_zero' ζ hζ a
      change ((αS : S) : A) = 0
      simpa using congrArg Subtype.val hu.symm
    let uu : Mˣ := Units.mk0 u hu0
    apply kummerQuotientClass_eq_zero_of_pow' ℓ a uu
    apply Units.ext
    apply (algebraMap M A).injective
    change algebraMap M A (u ^ ℓ) = algebraMap M A (a : M)
    rw [map_pow]
    have huA : algebraMap M A u = kummerRoot' ζ hζ a := by
      exact congrArg Subtype.val hu
    rw [huA, kummerRoot_pow' ζ hζ a]

private theorem rawKummerLinear_surjective'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Surjective (rawKummerLinear' ζ hζ) := by
  intro χ
  classical
  let A := AlgebraicClosure M
  letI : Normal M A := inferInstance
  letI : Algebra.IsIntegral M A := Algebra.IsAlgebraic.isIntegral
  let kerSet : Set (Field.absoluteGaloisGroup M) :=
    {σ | continuousCharacterValue χ σ = 0}
  have hkerOpen : IsOpen kerSet := by
    let kerAdd : Set (Additive (Field.absoluteGaloisGroup M)) :=
      {x | χ x = 0}
    have hopenAdd : IsOpen kerAdd := by
      exact (isOpen_discrete ({0} : Set (ZMod ℓ))).preimage χ.continuous
    exact hopenAdd
  have hkerOne : (1 : Field.absoluteGaloisGroup M) ∈ kerSet := by
    simp [kerSet, continuousCharacterValue]
  have hkerNhd : kerSet ∈ nhds (1 : Field.absoluteGaloisGroup M) :=
    hkerOpen.mem_nhds hkerOne
  obtain ⟨E, hEfin, hEnormal, hEker⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal M A kerSet).mp hkerNhd
  letI : FiniteDimensional M E := hEfin
  letI : Normal M E := hEnormal
  let Esep := separableClosure M E
  letI : IsGalois M Esep := separableClosure.isGalois M E
  let L : IntermediateField M A := IntermediateField.lift Esep
  let eL : Esep ≃ₐ[M] L := IntermediateField.liftAlgEquiv Esep
  letI : FiniteDimensional M L := eL.toLinearEquiv.finiteDimensional
  letI : Normal M L := Normal.of_algEquiv eL
  letI : Algebra.IsSeparable M L := ⟨fun x => by
    have hs := Algebra.IsSeparable.isSeparable M (eL.symm x)
    have hm := hs.map eL.toAlgHom eL.injective
    simpa using hm⟩
  letI : IsGalois M L := ⟨⟩
  have hfixE_of_fixL (σ : Field.absoluteGaloisGroup M)
      (hσL : σ ∈ L.fixingSubgroup) : σ ∈ E.fixingSubgroup := by
    let σE : E ≃ₐ[M] E := AlgEquiv.restrictNormalHom E σ
    have hfixL : ∀ x ∈ L, (show A ≃ₐ[M] A from σ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσL
    have hσEcomm (x : Esep) : σE (algebraMap Esep E x) =
        algebraMap Esep E x := by
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      have hxL : ((eL x : L) : A) ∈ L := (eL x).prop
      have hxfix := hfixL ((eL x : L) : A) hxL
      simpa [eL, L, Esep, IntermediateField.liftAlgEquiv_apply] using hxfix
    let σEhom : E →ₐ[Esep] E :=
      { σE.toAlgHom with commutes' := hσEcomm }
    have heq : σEhom = AlgHom.id Esep E := Subsingleton.elim _ _
    apply (IntermediateField.mem_fixingSubgroup_iff E σ).2
    intro x hx
    have happ := DFunLike.congr_fun heq ⟨x, hx⟩
    have happ' := congrArg Subtype.val happ
    simpa [σEhom, σE, AlgEquiv.restrictNormalHom_apply] using happ'
  let rL : Field.absoluteGaloisGroup M →* (L ≃ₐ[M] L) :=
    AlgEquiv.restrictNormalHom L
  have hrLsurj : Function.Surjective rL :=
    AlgEquiv.restrictNormalHom_surjective (F := M) (K₁ := L) A
  let χmul : Field.absoluteGaloisGroup M →* Multiplicative (ZMod ℓ) :=
    AddMonoidHom.toMultiplicativeRight χ.toAddMonoidHom
  have hrker : rL.ker ≤ χmul.ker := by
    intro σ hσ
    have hσL : σ ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker L]
      exact hσ
    have hσE := hfixE_of_fixL σ hσL
    have hzero : continuousCharacterValue χ σ = 0 := hEker hσE
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    exact hzero
  let ψmul : (L ≃ₐ[M] L) →* Multiplicative (ZMod ℓ) :=
    rL.liftOfSurjective hrLsurj ⟨χmul, hrker⟩
  have hψ (σ : Field.absoluteGaloisGroup M) :
      (ψmul (rL σ)).toAdd = continuousCharacterValue χ σ := by
    change (ψmul (rL σ)).toAdd = χ (Additive.ofMul σ)
    have hcomp : ψmul.comp rL = χmul := by
      exact congrArg Subtype.val
        ((rL.liftOfSurjective hrLsurj).symm_apply_apply ⟨χmul, hrker⟩)
    have happ := DFunLike.congr_fun hcomp σ
    exact congrArg Multiplicative.toAdd happ
  let ψv : (L ≃ₐ[M] L) → ZMod ℓ := fun g => (ψmul g).toAdd
  have hψone : ψv 1 = 0 := by simp [ψv]
  have hψmul (g h : L ≃ₐ[M] L) : ψv (g * h) = ψv g + ψv h := by
    change (ψmul (g * h)).toAdd = (ψmul g).toAdd + (ψmul h).toAdd
    rw [map_mul]
    rfl
  have hψinv (g : L ≃ₐ[M] L) : ψv g⁻¹ = -ψv g := by
    change (ψmul g⁻¹).toAdd = -(ψmul g).toAdd
    rw [map_inv]
    rfl
  let nb : Module.Basis (L ≃ₐ[M] L) M L := IsGalois.normalBasis M L
  let coeff : (L ≃ₐ[M] L) → M := fun g => ζ ^ (-ψv g).val
  let αL : L := ∑ g : (L ≃ₐ[M] L), coeff g • nb g
  have hcoord : nb.repr αL 1 = coeff 1 := by
    simp [αL, coeff, nb]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply]
      simp [hb]
    · simp
  have hcoeff_one : coeff 1 = 1 := by
    simp [coeff, hψone]
  have hαL0 : αL ≠ 0 := by
    intro hzero
    have hz := congrArg (fun x : L => nb.repr x 1) hzero
    rw [hcoord, map_zero, Finsupp.zero_apply, hcoeff_one] at hz
    exact one_ne_zero hz
  have hcoeff (h k : L ≃ₐ[M] L) :
      coeff (h⁻¹ * k) = ζ ^ (ψv h).val * coeff k := by
    have hv : -(ψv (h⁻¹ * k)) = ψv h + -(ψv k) := by
      rw [hψmul, hψinv]
      abel
    dsimp [coeff]
    rw [hv, primitiveRoot_pow_val_add' hζ]
  have hnb (h g : L ≃ₐ[M] L) : h (nb g) = nb (h * g) := by
    have hg : nb g = g (nb 1) := by
      simpa [nb] using IsGalois.normalBasis_apply (K := M) (L := L) g
    have hhg : nb (h * g) = (h * g) (nb 1) := by
      simpa [nb] using IsGalois.normalBasis_apply (K := M) (L := L) (h * g)
    rw [hg, hhg]
    rfl
  have heigen (h : L ≃ₐ[M] L) :
      h αL = algebraMap M L (ζ ^ (ψv h).val) * αL := by
    calc
      h αL = ∑ g : (L ≃ₐ[M] L), coeff g • h (nb g) := by
        simp only [αL, map_sum, map_smul]
      _ = ∑ g : (L ≃ₐ[M] L), coeff g • nb (h * g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [hnb]
      _ = ∑ k : (L ≃ₐ[M] L), coeff (h⁻¹ * k) • nb k := by
        apply Fintype.sum_equiv (Equiv.mulLeft h)
        intro g
        change coeff g • nb (h * g) = coeff (h⁻¹ * (h * g)) • nb (h * g)
        rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = ∑ k : (L ≃ₐ[M] L), (ζ ^ (ψv h).val * coeff k) • nb k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hcoeff]
      _ = (ζ ^ (ψv h).val) • αL := by
        simp only [αL, mul_smul, Finset.smul_sum]
      _ = algebraMap M L (ζ ^ (ψv h).val) * αL := by
        rw [Algebra.smul_def]
  have hpowfixed (h : L ≃ₐ[M] L) : h (αL ^ ℓ) = αL ^ ℓ := by
    rw [map_pow, heigen, mul_pow]
    have hrootpow : (algebraMap M L (ζ ^ (ψv h).val)) ^ ℓ = 1 := by
      rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
        one_pow, map_one]
    rw [hrootpow, one_mul]
  have hbase : αL ^ ℓ ∈ Set.range (algebraMap M L) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (αL ^ ℓ)).2 hpowfixed
  obtain ⟨c, hc⟩ := hbase
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    have hpzero : αL ^ ℓ = 0 := by simpa using hc.symm
    exact (pow_ne_zero ℓ hαL0) hpzero
  let a0 : Mˣ := Units.mk0 c hc0
  have hrootA : ((αL : L) : A) ^ ℓ = algebraMap M A (a0 : M) := by
    have hcA := congrArg Subtype.val hc
    simpa [a0] using hcA.symm
  have hactionA (σ : Field.absoluteGaloisGroup M) :
      (show A ≃ₐ[M] A from σ) ((αL : L) : A) =
        (algebraMap M A ζ) ^ (continuousCharacterValue χ σ).val *
          ((αL : L) : A) := by
    have he := heigen (rL σ)
    have heA := congrArg Subtype.val he
    have hrapply : (((rL σ) αL : L) : A) =
        (show A ≃ₐ[M] A from σ) (αL : A) := by
      dsimp [rL]
      exact AlgEquiv.restrictNormalHom_apply L σ αL
    rw [hrapply] at heA
    have hval : (ψv (rL σ)).val = (continuousCharacterValue χ σ).val :=
      congrArg ZMod.val (hψ σ)
    simpa [hval] using heA
  have hχraw : χ = rawKummerCharacter' ζ hζ a0 :=
    rawKummerCharacter_eq_of_definingEquation' ζ hζ a0 χ
      ⟨((αL : L) : A), hrootA, hactionA⟩
  refine ⟨kummerQuotientClass ℓ a0, ?_⟩
  rw [rawKummerLinear_class', ← hχraw]

private theorem exists_rawKummerEquiv'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ e : KummerQuotient M ℓ ≃ₗ[ZMod ℓ]
        ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ,
      IsKummerEquiv ζ e := by
  let e : KummerQuotient M ℓ ≃ₗ[ZMod ℓ]
      ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ :=
    LinearEquiv.ofBijective (rawKummerLinear' ζ hζ)
      ⟨rawKummerLinear_injective' ζ hζ,
        rawKummerLinear_surjective' ζ hζ⟩
  refine ⟨e, ?_⟩
  intro a
  obtain ⟨α, hpow, hact⟩ := rawKummerCharacter_definingEquation' ζ hζ a
  refine ⟨α, hpow, ?_⟩
  intro σ
  simpa [e] using hact σ

/-- Existence of the degree-one Kummer equivalence with its defining
equations, Blueprint (2.2). -/
theorem exists_kummerEquiv {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ e : KummerQuotient M ℓ ≃ₗ[ZMod ℓ]
        ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ,
      IsKummerEquiv ζ e := by
  exact exists_rawKummerEquiv' ζ hζ

/-- The Kummer equivalence associated with a chosen primitive root. -/
noncomputable def kummerEquiv {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    KummerQuotient M ℓ ≃ₗ[ZMod ℓ]
      ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ :=
  (exists_kummerEquiv ζ hζ).choose

private theorem finEquiv_apply {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      change i = Fin.ofNat (n + 1) i.val
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt i.isLt).symm

private theorem kummerQuotientClass_eq_zero_iff_exists_pow
    {M : Type*} [Field M] (n : ℕ) (a : Mˣ) :
    kummerQuotientClass n a = 0 ↔ ∃ u : Mˣ, u ^ n = a := by
  unfold kummerQuotientClass ModN.mkQ
  change ((Additive.ofMul a : Additive Mˣ) :
      (Additive Mˣ) ⧸
        (LinearMap.range (LinearMap.lsmul ℤ (Additive Mˣ) n)).toAddSubgroup) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  change (Additive.ofMul a : Additive Mˣ) ∈
      LinearMap.range (LinearMap.lsmul ℤ (Additive Mˣ) n) ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Additive.toMul u, ?_⟩
    have hu' : n • u = Additive.ofMul a := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact hu
    exact congrArg Additive.toMul hu'
  · rintro ⟨u, hu⟩
    refine ⟨Additive.ofMul u, ?_⟩
    change Additive.ofMul (u ^ n) = Additive.ofMul a
    rw [hu]

/-- The Kummer character of a nonzero element. -/
def kummerCharacter {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ :=
  kummerEquiv ζ hζ (kummerQuotientClass ℓ a)

/-- Defining equation for the Kummer character: after choosing an
`ℓ`-th root `α`, Galois acts through the power of `ζ` represented by the
`ZMod ℓ` value. -/
theorem kummerCharacter_definingEquation {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ) :
    ∃ α : AlgebraicClosure M,
      α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
      ∀ σ : Field.absoluteGaloisGroup M,
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
          (algebraMap M (AlgebraicClosure M) ζ) ^
              (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * α :=
  (exists_kummerEquiv ζ hζ).choose_spec a

/-- The Kummer-character value is characterized by the action on any chosen
root of the Kummer equation. -/
theorem kummerCharacterValue_eq_of_action
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (α : AlgebraicClosure M)
    (hαpow : α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M))
    (σ : Field.absoluteGaloisGroup M) (r : ZMod ℓ)
    (hαact : (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
      (algebraMap M (AlgebraicClosure M) ζ) ^ r.val * α) :
    continuousCharacterValue (kummerCharacter ζ hζ a) σ = r := by
  obtain ⟨β, hβpow, hβact⟩ := kummerCharacter_definingEquation ζ hζ a
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hmapa : algebraMap M A (a : M) ≠ 0 :=
    (map_ne_zero (algebraMap M A)).2 (Units.ne_zero a)
  have hα0 : α ≠ 0 := by
    intro hα
    apply hmapa
    rw [← hαpow, hα, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hratio : (β / α) ^ ℓ = (1 : A) := by
    rw [div_pow, hβpow, hαpow, div_self hmapa]
  obtain ⟨j, _, hj⟩ := hζA.eq_pow_of_pow_eq_one hratio
  have hβα : β = ζA ^ j * α := by
    rw [hj, div_mul_cancel₀ β hα0]
  have heq :
      ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ j * (ζA ^ r.val * α) := by
    calc
      ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * β := by
          rw [hβα]
      _ = (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) β :=
        (hβact σ).symm
      _ = (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
          (ζA ^ j * α) := congrArg _ hβα
      _ = ζA ^ j *
          (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α := by
        rw [map_mul, map_pow]
        congr 2
        exact (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ).commutes ζ
      _ = ζA ^ j * (ζA ^ r.val * α) := by rw [hαact]
  have hpowequal : ζA ^
      (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val =
      ζA ^ r.val := by
    apply mul_left_cancel₀
      (pow_ne_zero j (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero))
    apply mul_right_cancel₀ hα0
    simpa [mul_assoc, mul_left_comm, mul_comm] using heq
  apply ZMod.val_injective ℓ
  exact hζA.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpowequal

private theorem continuousCharacter_smul_value
    {G : Type*} [Group G] [TopologicalSpace G] (n : ℕ)
    (r : ZMod n) (χ : ContinuousCharacter G n) (g : G) :
    continuousCharacterValue (r • χ) g =
      r * continuousCharacterValue χ g := by
  change (r • χ) (Additive.ofMul g) = r • χ (Additive.ofMul g)
  let ev : ContinuousCharacter G n →+ ZMod n :=
    { toFun := fun b => b (Additive.ofMul g)
      map_zero' := by simp
      map_add' := fun _ _ => by simp }
  simpa [ev] using ZMod.map_smul ev r χ

private theorem kummerCharacter_eq_of_definingEquation
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (χ : ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ)
    (hχ : ∃ α : AlgebraicClosure M,
      α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
      ∀ σ : Field.absoluteGaloisGroup M,
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
          (algebraMap M (AlgebraicClosure M) ζ) ^
              (continuousCharacterValue χ σ).val * α) :
    χ = kummerCharacter ζ hζ a := by
  obtain ⟨α, hαpow, hαeq⟩ := hχ
  obtain ⟨β, hβpow, hβeq⟩ := kummerCharacter_definingEquation ζ hζ a
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  have hmapa : algebraMap M A (a : M) ≠ 0 :=
    (map_ne_zero (algebraMap M A)).2 (Units.ne_zero a)
  have hα0 : α ≠ 0 := by
    intro hα
    apply hmapa
    rw [← hαpow, hα, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hratio : (β / α) ^ ℓ = (1 : A) := by
    rw [div_pow, hβpow, hαpow, div_self hmapa]
  obtain ⟨j, _, hj⟩ := hζA.eq_pow_of_pow_eq_one hratio
  have hβα : β = ζA ^ j * α := by
    rw [hj, div_mul_cancel₀ β hα0]
  apply ContinuousAddMonoidHom.ext
  intro x
  let σ : Field.absoluteGaloisGroup M := Additive.toMul x
  let σe : A ≃ₐ[M] A := σ
  change continuousCharacterValue χ σ =
    continuousCharacterValue (kummerCharacter ζ hζ a) σ
  have heq :
      ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ j * (ζA ^ (continuousCharacterValue χ σ).val * α) := by
    calc
      ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val *
          (ζA ^ j * α) =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * β := by
          rw [hβα]
      _ = σe β := (hβeq σ).symm
      _ = σe (ζA ^ j * α) := congrArg (fun y => σe y) hβα
      _ = ζA ^ j * σe α := by
        have hsζ : σe ζA = ζA := by simp [σe, ζA, A]
        rw [map_mul, map_pow, hsζ]
      _ = ζA ^ j * (ζA ^ (continuousCharacterValue χ σ).val * α) := by
        have hsα : σe α = ζA ^ (continuousCharacterValue χ σ).val * α := by
          simpa [σe, ζA, A] using hαeq σ
        rw [hsα]
  have hpowequal :
      ζA ^ (continuousCharacterValue χ σ).val =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val := by
    apply mul_left_cancel₀
      (pow_ne_zero j (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero))
    apply mul_right_cancel₀ hα0
    simpa [mul_assoc, mul_left_comm, mul_comm] using heq.symm
  apply ZMod.val_injective ℓ
  exact hζA.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpowequal

private def kummerDualLinear'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ →ₗ[ZMod ℓ]
      MulCharacter M ℓ where
  toFun x := (evaluationLinear ℓ x).toAddMonoidHom.comp <|
    (kummerEquiv ζ hζ).toLinearMap.toAddMonoidHom.comp (ModN.mkQ ℓ)
  map_add' x y := by
    apply AddMonoidHom.ext
    intro u
    change (evaluationLinear ℓ (x + y)) _ =
      evaluationLinear ℓ x _ + evaluationLinear ℓ y _
    rw [map_add, LinearMap.add_apply]
  map_smul' c x := by
    apply AddMonoidHom.ext
    intro u
    change (evaluationLinear ℓ (c • x)) _ =
      c • evaluationLinear ℓ x _
    rw [map_smul, LinearMap.smul_apply]

@[simp]
private theorem kummerDualLinear_apply'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (x : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) (u : Mˣ) :
    kummerDualLinear' ζ hζ x (Additive.ofMul u) =
      evaluation ℓ x (kummerCharacter ζ hζ u) := by
  rfl

private theorem kummerDualLinear_bijective'
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Bijective (kummerDualLinear' ζ hζ) := by
  letI : CompactSpace (Field.absoluteGaloisGroup M) :=
    absoluteGaloisGroup_compactSpace
  letI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup M) :=
    absoluteGaloisGroup_totallyDisconnectedSpace
  have heval :=
    evaluationLinear_bijective_of_compact_totallyDisconnected
      (G := Field.absoluteGaloisGroup M) (n := ℓ)
  constructor
  · intro x y hxy
    apply heval.1
    apply LinearMap.ext
    intro χ
    obtain ⟨q, rfl⟩ := (kummerEquiv ζ hζ).surjective χ
    obtain ⟨u, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (Additive Mˣ) (ℓ : ℤ))).mkQ_surjective q
    exact DFunLike.congr_fun hxy u
  · intro p
    let pLift : KummerQuotient M ℓ →ₗ[ZMod ℓ] ZMod ℓ :=
      (ModN.liftEquiv').symm ⟨p, by
        intro u
        rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), CharP.cast_eq_zero,
          zero_smul]⟩
    let L : Module.Dual (ZMod ℓ)
        (ContinuousCharacter (Field.absoluteGaloisGroup M) ℓ) :=
      pLift.comp (kummerEquiv ζ hζ).symm.toLinearMap
    obtain ⟨x, hx⟩ := heval.2 L
    refine ⟨x, ?_⟩
    apply AddMonoidHom.ext
    intro u
    change evaluation ℓ x
      (kummerEquiv ζ hζ (ModN.mkQ ℓ u)) = p u
    have happ := DFunLike.congr_fun hx
      (kummerEquiv ζ hζ (ModN.mkQ ℓ u))
    have happ' : evaluation ℓ x
        (kummerEquiv ζ hζ (ModN.mkQ ℓ u)) =
          pLift (ModN.mkQ ℓ u) := by
      simpa [evaluation, L] using happ
    rw [happ']
    rfl

/-- Existence of the dual Kummer identification used to transport local
annihilator planes into the group quotient.  Its equation fixes the map and
prevents a trivial implementation. -/
theorem exists_kummerDualEquiv {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ e : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
        MulCharacter M ℓ,
      ∀ x u,
        e x (Additive.ofMul u) =
          evaluation ℓ x (kummerCharacter ζ hζ u) := by
  let e : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
      MulCharacter M ℓ :=
    LinearEquiv.ofBijective (kummerDualLinear' ζ hζ)
      (kummerDualLinear_bijective' ζ hζ)
  refine ⟨e, ?_⟩
  intro x u
  exact kummerDualLinear_apply' ζ hζ x u

/-- The dual Kummer equivalence, characterized by evaluation. -/
noncomputable def kummerDualEquiv {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
      MulCharacter M ℓ :=
  (exists_kummerDualEquiv ζ hζ).choose

@[simp]
theorem kummerDualEquiv_apply {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (x : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) (u : Mˣ) :
    kummerDualEquiv ζ hζ x (Additive.ofMul u) =
      evaluation ℓ x (kummerCharacter ζ hζ u) :=
  (exists_kummerDualEquiv ζ hζ).choose_spec x u

/-- A concrete `ℓ`-Kummer radical extension generated by an `ℓ`-th root of
`a`.  The generation and degree equations are included explicitly, so this
predicate cannot be met by an unrelated or trivial extension. -/
def IsKummerRadicalExtension (M E : Type*) [Field M] [Field E]
    [Algebra M E] (ℓ : ℕ) (a : Mˣ) : Prop :=
  ∃ α : E,
    α ^ ℓ = algebraMap M E (a : M) ∧
      Algebra.adjoin M ({α} : Set E) = ⊤ ∧
      Module.finrank M E = ℓ

/-- Membership in the norm image on nonzero elements. -/
def IsUnitNorm (M E : Type*) [Field M] [Field E] [Algebra M E]
    (b : Mˣ) : Prop :=
  ∃ z : Eˣ, Algebra.norm M (z : E) = (b : M)

/-- Evaluation at an algebraic element is locally constant on the absolute
Galois group. -/
private theorem absoluteGalois_apply_isLocallyConstant
    {M : Type*} [Field M] (v : AlgebraicClosure M) :
    IsLocallyConstant (fun σ : Field.absoluteGaloisGroup M =>
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) v) := by
  change IsLocallyConstant (fun σ : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M => σ v)
  let U : Subgroup (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M) :=
    MulAction.stabilizer (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M) v
  have hU : IsOpen (U : Set (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M)) := by
    letI : Algebra.IsIntegral M (AlgebraicClosure M) := Algebra.IsAlgebraic.isIntegral
    exact stabilizer_isOpen_of_isIntegral v
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro σ
  change IsOpen {τ : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M | τ v = σ v}
  rw [show {τ : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M | τ v = σ v} =
      σ • (U : Set (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M)) by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem,
      SetLike.mem_coe, U, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    constructor
    · intro h
      change (σ⁻¹ * τ) v = v
      change σ⁻¹ (τ v) = v
      rw [h]
      simp
    · intro h
      calc
        τ v = σ ((σ⁻¹ * τ) v) := by simp
        _ = σ v := congrArg σ h]
  exact hU.leftCoset σ

/-- The exponent of an `ℓ`-th root of unity relative to a fixed primitive
root (with an arbitrary fallback away from the roots of unity). -/
private noncomputable def cupPrimitiveRootIndex
    {A : Type*} [Field A] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : A) (hζ : IsPrimitiveRoot ζ ℓ) (x : A) : Fin ℓ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  by_cases hx : x ^ ℓ = 1
  · exact ⟨(hζ.eq_pow_of_pow_eq_one hx).choose,
      (hζ.eq_pow_of_pow_eq_one hx).choose_spec.1⟩
  · exact ⟨0, (Fact.out : ℓ.Prime).pos⟩

private theorem cupPrimitiveRootIndex_spec
    {A : Type*} [Field A] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : A) (hζ : IsPrimitiveRoot ζ ℓ) (x : A) (hx : x ^ ℓ = 1) :
    ζ ^ (cupPrimitiveRootIndex ζ hζ x).val = x := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [cupPrimitiveRootIndex, dif_pos hx]
  exact (hζ.eq_pow_of_pow_eq_one hx).choose_spec.2

private theorem primitiveRoot_pow_val_sub
    {A : Type*} [Field A] {ℓ : ℕ} [Fact ℓ.Prime]
    {ζ : A} (hζ : IsPrimitiveRoot ζ ℓ) (x y : ZMod ℓ) :
    ζ ^ (x - y).val = ζ ^ x.val / ζ ^ y.val := by
  apply (eq_div_iff (pow_ne_zero y.val
    (hζ.ne_zero (Fact.out : ℓ.Prime).ne_zero))).2
  rw [← primitiveRoot_pow_val_add' hζ, sub_add_cancel]

private theorem primitiveRoot_pow_val_mul
    {A : Type*} [Field A] {ℓ : ℕ} [Fact ℓ.Prime]
    {ζ : A} (hζ : IsPrimitiveRoot ζ ℓ) (x y : ZMod ℓ) :
    ζ ^ (x * y).val = ζ ^ (x.val * y.val) := by
  rw [ZMod.val_mul]
  exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hζ.pow_eq_one

/-- The explicit `CupZero` convention is symmetric up to the usual
pointwise-product cochain. -/
private theorem cupZero_symm
    {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} {a b : ContinuousCharacter G n}
    (h : CupZero n a b) : CupZero n b a := by
  obtain ⟨c, hc⟩ := h
  have hacont : Continuous (fun g : G => continuousCharacterValue a g) := by
    change Continuous (a ∘ Additive.ofMul)
    exact a.continuous.comp continuous_ofMul
  have hbcont : Continuous (fun g : G => continuousCharacterValue b g) := by
    change Continuous (b ∘ Additive.ofMul)
    exact b.continuous.comp continuous_ofMul
  let d : C(G, ZMod n) :=
    ⟨fun g => -(continuousCharacterValue a g * continuousCharacterValue b g) - c g,
      (hacont.mul hbcont).neg.sub c.continuous⟩
  refine ⟨d, ?_⟩
  intro σ τ
  have ha_mul : continuousCharacterValue a (σ * τ) =
      continuousCharacterValue a σ + continuousCharacterValue a τ := by
    change a (Additive.ofMul (σ * τ)) =
      a (Additive.ofMul σ) + a (Additive.ofMul τ)
    exact map_add a (Additive.ofMul σ) (Additive.ofMul τ)
  have hb_mul : continuousCharacterValue b (σ * τ) =
      continuousCharacterValue b σ + continuousCharacterValue b τ := by
    change b (Additive.ofMul (σ * τ)) =
      b (Additive.ofMul σ) + b (Additive.ofMul τ)
    exact map_add b (Additive.ofMul σ) (Additive.ofMul τ)
  dsimp [d]
  rw [ha_mul, hb_mul]
  have hc' : c (σ * τ) = c σ + c τ -
      continuousCharacterValue a σ * continuousCharacterValue b τ := by
    linear_combination (hc σ τ)
  rw [hc']
  ring

/-- The partial conjugate product along a chosen cyclic generator. -/
private def partialConjugateProduct
    {M L : Type*} [Field M] [Field L] [Algebra M L]
    (s : L ≃ₐ[M] L) (z : L) (n : ℕ) : L :=
  ∏ j ∈ Finset.range n, (s ^ j) z

private theorem partialConjugateProduct_add
    {M L : Type*} [Field M] [Field L] [Algebra M L]
    (s : L ≃ₐ[M] L) (z : L) (i j : ℕ) :
    partialConjugateProduct s z (i + j) =
      partialConjugateProduct s z i *
        (s ^ i) (partialConjugateProduct s z j) := by
  rw [partialConjugateProduct, Finset.prod_range_add,
    partialConjugateProduct, partialConjugateProduct, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [pow_add]
  rfl

/-- The defining Kummer action equation holds for every chosen root, not
only the root selected in `kummerCharacter_definingEquation`. -/
private theorem kummerCharacter_action_of_root
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (r : AlgebraicClosure M)
    (hrpow : r ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M))
    (σ : Field.absoluteGaloisGroup M) :
    (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) r =
      (algebraMap M (AlgebraicClosure M) ζ) ^
          (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * r := by
  obtain ⟨β, hβpow, hβeq⟩ := kummerCharacter_definingEquation ζ hζ a
  let A := AlgebraicClosure M
  let ζA : A := algebraMap M A ζ
  let σe : A ≃ₐ[M] A := σ
  have hmapa : algebraMap M A (a : M) ≠ 0 :=
    (map_ne_zero (algebraMap M A)).2 (Units.ne_zero a)
  have hr0 : r ≠ 0 := by
    intro hr
    apply hmapa
    rw [← hrpow, hr, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M A).injective
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hratio : (β / r) ^ ℓ = (1 : A) := by
    rw [div_pow, hβpow, hrpow, div_self hmapa]
  obtain ⟨j, _, hj⟩ := hζA.eq_pow_of_pow_eq_one hratio
  have hβr : β = ζA ^ j * r := by
    rw [hj, div_mul_cancel₀ β hr0]
  have hfixζ : σe (ζA ^ j) = ζA ^ j := by simp [σe, ζA, A]
  apply mul_left_cancel₀ (pow_ne_zero j
    (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero))
  calc
    ζA ^ j * σe r = σe (ζA ^ j * r) := by rw [map_mul, hfixζ]
    _ = σe β := by rw [← hβr]
    _ = ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * β := by
      simpa [σe, ζA, A] using hβeq σ
    _ = ζA ^ j *
        (ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val * r) := by
      rw [hβr]
      ring

/-- A nonzero Kummer class has an absolute Galois element on which its
character takes the value one. -/
private theorem exists_kummerCharacter_value_one
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a : Mˣ)
    (ha : kummerQuotientClass ℓ a ≠ 0) :
    ∃ σ : Field.absoluteGaloisGroup M,
      continuousCharacterValue (kummerCharacter ζ hζ a) σ = 1 := by
  let χ := kummerCharacter ζ hζ a
  have hχ : χ ≠ 0 := by
    intro hzero
    apply ha
    apply (kummerEquiv ζ hζ).injective
    simpa [χ, kummerCharacter] using hzero
  have hex : ∃ x : Additive (Field.absoluteGaloisGroup M), χ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hχ
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hex
  let k : ℕ := (χ x)⁻¹ |>.val
  let y : Additive (Field.absoluteGaloisGroup M) := k • x
  refine ⟨Additive.toMul y, ?_⟩
  change χ y = 1
  rw [show χ y = k • χ x by exact map_nsmul χ k x]
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ)]
  change (k : ZMod ℓ) * χ x = 1
  rw [show (k : ZMod ℓ) = (χ x)⁻¹ by
    exact ZMod.natCast_zmod_val (χ x)⁻¹]
  exact inv_mul_cancel₀ hx

/-- The explicit inhomogeneous cocycle used by `CupZero` for two
Kummer characters. -/
private def kummerCupValue {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (σ τ : Field.absoluteGaloisGroup M) : ZMod ℓ :=
  continuousCharacterValue (kummerCharacter ζ hζ a) σ *
    continuousCharacterValue (kummerCharacter ζ hζ b) τ

/-- Unfold `CupZero` while retaining a name for its precise coboundary
convention. -/
private theorem kummerCupZero_iff_coboundary
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) ↔
      ∃ c : C(Field.absoluteGaloisGroup M, ZMod ℓ),
        ∀ σ τ, kummerCupValue ζ hζ a b σ τ =
          c σ + c τ - c (σ * τ) := by
  rfl

/-- Norms trivialize the explicit Kummer cup cocycle. -/
private theorem cyclic_norm_criterion_of_norm
    {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] {ℓ : ℕ} [Fact ℓ.Prime]
    [IsGalois M E] [IsCyclic (E ≃ₐ[M] E)]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (ha : kummerQuotientClass ℓ a ≠ 0)
    (α : E) (hαpow : α ^ ℓ = algebraMap M E (a : M))
    (hαgen : Algebra.adjoin M ({α} : Set E) = ⊤)
    (hdegree : Module.finrank M E = ℓ)
    (hb : IsUnitNorm M E b) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) := by
  classical
  obtain ⟨z, hz⟩ := hb
  let ι : E →ₐ[M] AlgebraicClosure M := IsAlgClosed.lift
  let L : IntermediateField M (AlgebraicClosure M) := ι.fieldRange
  let e : E ≃ₐ[M] L := AlgHom.equivFieldRange ι
  letI : FiniteDimensional M L := e.toLinearEquiv.finiteDimensional
  letI : IsGalois M L := IsGalois.of_algEquiv e
  have hfinrank : Module.finrank M L = ℓ := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact hdegree
  have hcard : Nat.card (L ≃ₐ[M] L) = ℓ := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  letI : IsCyclic (L ≃ₐ[M] L) := isCyclic_of_prime_card hcard
  let r : L := e α
  have hrpowL : r ^ ℓ = algebraMap M L (a : M) := by
    dsimp [r]
    rw [← map_pow, hαpow, e.commutes]
  have hrpowA : (r : AlgebraicClosure M) ^ ℓ =
      algebraMap M (AlgebraicClosure M) (a : M) := by
    have h := congrArg Subtype.val hrpowL
    simpa [L] using h
  have hr0 : r ≠ 0 := by
    intro hr
    have ha0 : algebraMap M L (a : M) ≠ 0 :=
      (map_ne_zero (algebraMap M L)).2 (Units.ne_zero a)
    apply ha0
    rw [← hrpowL, hr, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hLgen : Algebra.adjoin M ({r} : Set L) = ⊤ := by
    calc
      Algebra.adjoin M ({r} : Set L) =
          (Algebra.adjoin M ({α} : Set E)).map e.toAlgHom := by
        rw [AlgHom.map_adjoin, Set.image_singleton]
        rfl
      _ = ⊤ := by
        rw [hαgen, Algebra.map_top]
        exact (AlgHom.range_eq_top e.toAlgHom).2 e.surjective
  obtain ⟨ρ, hρ⟩ := exists_kummerCharacter_value_one ζ hζ a ha
  let s : L ≃ₐ[M] L := AlgEquiv.restrictNormalHom L ρ
  have hsr : s r = algebraMap M L ζ * r := by
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    have hact := kummerCharacter_action_of_root ζ hζ a
      (r : AlgebraicClosure M) hrpowA ρ
    rw [hρ, ZMod.val_one] at hact
    simpa [s, L] using hact
  have hsne : s ≠ 1 := by
    intro hs
    have heq : algebraMap M L ζ * r = r := by
      rw [← hsr, hs]
      rfl
    have hζmap : algebraMap M L ζ = 1 := by
      apply mul_right_cancel₀ hr0
      simpa using heq
    have hζone : ζ = 1 := by
      apply (algebraMap M L).injective
      simpa using hζmap
    exact hζ.ne_one (Fact.out : ℓ.Prime).one_lt hζone
  have hsgen : ∀ t : L ≃ₐ[M] L, t ∈ Subgroup.zpowers s :=
    fun t => mem_zpowers_of_prime_card hcard hsne
  let zL : L := e (z : E)
  have hzL0 : zL ≠ 0 := by
    intro h
    apply Units.ne_zero z
    apply e.injective
    simpa [zL] using h
  have hnormzL : Algebra.norm M zL = (b : M) := by
    rw [show zL = e (z : E) by rfl, Algebra.norm_eq_of_algEquiv e, hz]
  have hnormprod : (∏ t : L ≃ₐ[M] L, t zL) = algebraMap M L (b : M) := by
    rw [← Algebra.norm_eq_prod_automorphisms, hnormzL]
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let autFromFin : Fin ℓ ≃ (L ≃ₐ[M] L) :=
    (ZMod.finEquiv ℓ).toEquiv.trans <|
      Multiplicative.ofAdd.trans (zmodMulEquivOfGenerator hsgen hcard).toEquiv
  have haut (i : Fin ℓ) : autFromFin i = s ^ i.val := by
    change zmodMulEquivOfGenerator hsgen hcard
      (Multiplicative.ofAdd (ZMod.finEquiv ℓ i)) = s ^ i.val
    rw [show ZMod.finEquiv ℓ i = (i.val : ZMod ℓ) by
      cases ℓ with
      | zero => exact Fin.elim0 i
      | succ n =>
        change i = Fin.ofNat (n + 1) i.val
        apply Fin.ext
        exact (Nat.mod_eq_of_lt i.isLt).symm]
    simpa using zmodMulEquivOfGenerator_apply_ofAdd_intCast hsgen hcard (i.val : ℤ)
  have hcycle : partialConjugateProduct s zL ℓ =
      algebraMap M L (b : M) := by
    calc
      partialConjugateProduct s zL ℓ =
          ∏ i : Fin ℓ, (s ^ i.val) zL := by
        rw [partialConjugateProduct]
        simpa using (Fin.prod_univ_eq_prod_range
          (fun i : ℕ => (s ^ i) zL) ℓ).symm
      _ = ∏ i : Fin ℓ, autFromFin i zL := by
        apply Fintype.prod_congr
        intro i
        rw [haut]
      _ = ∏ t : L ≃ₐ[M] L, t zL :=
        Fintype.prod_equiv autFromFin _ _ (fun _ => rfl)
      _ = algebraMap M L (b : M) := hnormprod
  have hs_pow_r (n : ℕ) :
      (s ^ n) r = (algebraMap M L ζ) ^ n * r := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ, AlgEquiv.mul_apply, hsr, map_mul,
        (s ^ n).commutes, hn, pow_succ]
      ring
  have hrestrict (σ : Field.absoluteGaloisGroup M) :
      AlgEquiv.restrictNormalHom L
          (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) =
        s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    change AlgEquiv.restrictNormalHom L σA = _
    apply AlgEquiv.ext
    have heq : (AlgEquiv.restrictNormalHom L σA).toAlgHom =
        (s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hLgen
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change (AlgEquiv.restrictNormalHom L σA) r =
        (s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val) r
      apply Subtype.ext
      have hlhs : (((AlgEquiv.restrictNormalHom L σA) r : L) :
          AlgebraicClosure M) = σA (r : AlgebraicClosure M) :=
        AlgEquiv.restrictNormalHom_apply L σA r
      have hrhs := congrArg Subtype.val
        (hs_pow_r (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val)
      have hact := kummerCharacter_action_of_root ζ hζ a
        (r : AlgebraicClosure M) hrpowA σ
      rw [hlhs]
      simpa [L] using hact.trans (by simpa [L] using hrhs.symm)
    intro x
    exact DFunLike.congr_fun heq x
  obtain ⟨β, hβpow, hβact⟩ := kummerCharacter_definingEquation ζ hζ b
  have hβ0 : β ≠ 0 := by
    intro hβ
    have hb0 : algebraMap M (AlgebraicClosure M) (b : M) ≠ 0 :=
      (map_ne_zero (algebraMap M (AlgebraicClosure M))).2 (Units.ne_zero b)
    apply hb0
    rw [← hβpow, hβ, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  let P : ℕ → L := partialConjugateProduct s zL
  let R : ℕ → AlgebraicClosure M := fun n => β ^ n / (P n : AlgebraicClosure M)
  have hP0 (n : ℕ) : P n ≠ 0 := by
    dsimp [P, partialConjugateProduct]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero (s ^ i)).2 hzL0
  have hPadd (i j : ℕ) : P (i + j) = P i * (s ^ i) (P j) :=
    partialConjugateProduct_add s zL i j
  have hPperiod (n : ℕ) :
      P (n + ℓ) = P n * algebraMap M L (b : M) := by
    rw [hPadd, show P ℓ = algebraMap M L (b : M) from hcycle]
    simp
  have hRperiod : Function.Periodic R ℓ := by
    intro n
    dsimp [R]
    rw [hPperiod, pow_add, hβpow]
    have hmapb : algebraMap M (AlgebraicClosure M) (b : M) =
        ((algebraMap M L (b : M) : L) : AlgebraicClosure M) := by rfl
    rw [hmapb]
    have hPn0 : ((P n : L) : AlgebraicClosure M) ≠ 0 :=
      Subtype.coe_ne_coe.mpr (hP0 n)
    have hB0 : (((algebraMap M L (b : M) : L) : AlgebraicClosure M)) ≠ 0 := by
      exact Subtype.coe_ne_coe.mpr
        ((map_ne_zero (algebraMap M L)).2 (Units.ne_zero b))
    field_simp [hPn0, hB0]
    norm_cast
    exact mul_comm _ _
  have hRmod (n : ℕ) : R (n % ℓ) = R n := hRperiod.map_mod_nat n
  let wL : L := algebraMap M L (b : M) / zL ^ ℓ
  have hnormwL : Algebra.norm M wL = 1 := by
    dsimp [wL]
    change Algebra.norm M
      (algebraMap M L (b : M) * (zL ^ ℓ)⁻¹) = 1
    rw [map_mul, Algebra.norm_inv, map_pow, hnormzL,
      Algebra.norm_algebraMap, hfinrank]
    simp
  let Q : ℕ → L := partialConjugateProduct s wL
  have hQ0 (n : ℕ) : Q n ≠ 0 := by
    dsimp [Q, partialConjugateProduct]
    have hwL0 : wL ≠ 0 := by
      dsimp [wL]
      exact div_ne_zero ((map_ne_zero (algebraMap M L)).2 (Units.ne_zero b))
        (pow_ne_zero ℓ hzL0)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero (s ^ i)).2 hwL0
  have hQcycle : Q ℓ = 1 := by
    have hnormprodw : (∏ t : L ≃ₐ[M] L, t wL) = 1 := by
      rw [← Algebra.norm_eq_prod_automorphisms, hnormwL, map_one]
    calc
      Q ℓ = ∏ i : Fin ℓ, (s ^ i.val) wL := by
        dsimp [Q, partialConjugateProduct]
        simpa using (Fin.prod_univ_eq_prod_range
          (fun i : ℕ => (s ^ i) wL) ℓ).symm
      _ = ∏ i : Fin ℓ, autFromFin i wL := by
        apply Fintype.prod_congr
        intro i
        rw [haut]
      _ = ∏ t : L ≃ₐ[M] L, t wL :=
        Fintype.prod_equiv autFromFin _ _ (fun _ => rfl)
      _ = 1 := hnormprodw
  have hQadd (i j : ℕ) : Q (i + j) = Q i * (s ^ i) (Q j) :=
    partialConjugateProduct_add s wL i j
  have hQperiod : Function.Periodic Q ℓ := by
    intro n
    rw [hQadd, hQcycle, map_one, mul_one]
  have hQmod (n : ℕ) : Q (n % ℓ) = Q n := hQperiod.map_mod_nat n
  let cyc : Multiplicative (ZMod ℓ) ≃* (L ≃ₐ[M] L) :=
    zmodMulEquivOfGenerator hsgen hcard
  let coord : (L ≃ₐ[M] L) → ZMod ℓ := fun t => (cyc.symm t).toAdd
  have hcoord (t : L ≃ₐ[M] L) : t = s ^ (coord t).val := by
    calc
      t = cyc (cyc.symm t) := (cyc.apply_symm_apply t).symm
      _ = cyc (Multiplicative.ofAdd (coord t)) := rfl
      _ = cyc (Multiplicative.ofAdd ((coord t).val : ZMod ℓ)) := by
        rw [ZMod.natCast_zmod_val]
      _ = s ^ ((coord t).val : ℤ) := by
        change zmodMulEquivOfGenerator hsgen hcard
          (Multiplicative.ofAdd ((coord t).val : ZMod ℓ)) = _
        simpa only [Int.cast_natCast] using
          (zmodMulEquivOfGenerator_apply_ofAdd_intCast hsgen hcard
            ((coord t).val : ℤ))
      _ = s ^ (coord t).val := zpow_natCast s (coord t).val
  have hcoord_mul (g h : L ≃ₐ[M] L) :
      coord (g * h) = coord g + coord h := by
    exact congrArg Multiplicative.toAdd (map_mul cyc.symm g h)
  let f : (L ≃ₐ[M] L) → Lˣ := fun t =>
    Units.mk0 (Q (coord t).val) (hQ0 (coord t).val)
  letI : SMul (L ≃ₐ[M] L) Lˣ :=
    AlgEquiv.instMulDistribMulActionUnits.toSMul
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    apply Units.ext
    change Q (coord (g * h)).val = g (Q (coord h).val) * Q (coord g).val
    rw [hcoord_mul, ZMod.val_add, hQmod, hQadd]
    conv_rhs =>
      lhs
      rw [hcoord g]
    exact mul_comm (Q (coord g).val) ((s ^ (coord g).val) (Q (coord h).val))
  obtain ⟨u, hu⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have hu0 : (u : L) ≠ 0 := Units.ne_zero u
  have hcoords : coord s = 1 := by
    change (cyc.symm s).toAdd = 1
    rw [show cyc = zmodMulEquivOfGenerator hsgen hcard by rfl,
      zmodMulEquivOfGenerator_symm_apply_generator]
    rfl
  have hQone : Q 1 = wL := by
    simp [Q, partialConjugateProduct]
  have hsu : s (u : L) / (u : L) =
      algebraMap M L (b : M) / zL ^ ℓ := by
    have hus := hu s
    have hus' : s (u : L) / (u : L) = Q (coord s).val := by
      simpa [AlgEquiv.smul_units_def, f] using
        congrArg (fun x : Lˣ => (x : L)) hus
    rw [hcoords, ZMod.val_one, hQone] at hus'
    simpa [wL] using hus'
  obtain ⟨v, hvpow⟩ : ∃ v : AlgebraicClosure M,
      v ^ ℓ = ((u : L) : AlgebraicClosure M) :=
    IsAlgClosed.exists_pow_nat_eq _ (Fact.out : ℓ.Prime).pos
  have hv0 : v ≠ 0 := by
    intro hv
    have huA0 : (((u : L) : L) : AlgebraicClosure M) ≠ 0 :=
      Subtype.coe_ne_coe.mpr hu0
    apply huA0
    rw [← hvpow, hv, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hsu_pow (n : ℕ) :
      (s ^ n) (u : L) / (u : L) =
        (algebraMap M L (b : M)) ^ n / (P n) ^ ℓ := by
    induction n with
    | zero =>
      simp [P, partialConjugateProduct, hu0]
    | succ n hn =>
      have hsnu0 : (s ^ n) (u : L) ≠ 0 := (map_ne_zero (s ^ n)).2 hu0
      have hPn0 : P n ≠ 0 := hP0 n
      have hsnz0 : (s ^ n) zL ≠ 0 := (map_ne_zero (s ^ n)).2 hzL0
      calc
        (s ^ (n + 1)) (u : L) / (u : L) =
            (s ^ n) (s (u : L)) / (u : L) := by
          rw [pow_succ]
          rfl
        _ = ((s ^ n) (s (u : L)) / (s ^ n) (u : L)) *
            ((s ^ n) (u : L) / (u : L)) := by
          field_simp
        _ = (s ^ n) (s (u : L) / (u : L)) *
            ((s ^ n) (u : L) / (u : L)) := by
          congr 1
          exact (map_div₀ (s ^ n) (s (u : L)) (u : L)).symm
        _ = ((algebraMap M L (b : M)) / ((s ^ n) zL) ^ ℓ) *
            ((algebraMap M L (b : M)) ^ n / (P n) ^ ℓ) := by
          rw [hsu, hn]
          congr 1
          rw [map_div₀, map_pow, (s ^ n).commutes]
        _ = (algebraMap M L (b : M)) ^ (n + 1) /
            (P (n + 1)) ^ ℓ := by
          have hPsucc : P (n + 1) = P n * (s ^ n) zL := by
            rw [hPadd n 1]
            simp [P, partialConjugateProduct]
          rw [hPsucc, mul_pow, pow_succ]
          field_simp [hPn0, hsnz0,
            (map_ne_zero (algebraMap M L)).2 (Units.ne_zero b)]
  have hRpow (n : ℕ) : (R n) ^ ℓ =
      (((s ^ n) (u : L) : L) : AlgebraicClosure M) /
        ((u : L) : AlgebraicClosure M) := by
    have h := congrArg Subtype.val (hsu_pow n)
    dsimp [R]
    rw [div_pow, ← pow_mul, Nat.mul_comm n ℓ, pow_mul, hβpow]
    simpa [L] using h.symm
  have hactionL (σ : Field.absoluteGaloisGroup M) (x : L) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
          (x : AlgebraicClosure M) =
        ((s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val) x : L) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    have hres := AlgEquiv.restrictNormalHom_apply L σA x
    rw [hrestrict σ] at hres
    exact hres.symm
  have hRaction (σ : Field.absoluteGaloisGroup M) (j : ℕ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (R j) *
          R (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val =
        (algebraMap M (AlgebraicClosure M) ζ) ^
            ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val * j) *
          R ((continuousCharacterValue (kummerCharacter ζ hζ a) σ).val + j) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    let i := (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
    let y := (continuousCharacterValue (kummerCharacter ζ hζ b) σ).val
    change σA (R j) * R i =
      (algebraMap M (AlgebraicClosure M) ζ) ^ (y * j) * R (i + j)
    have hσβ : σA β = (algebraMap M (AlgebraicClosure M) ζ) ^ y * β := by
      simpa [σA, y] using hβact σ
    have hσP : σA (P j : AlgebraicClosure M) =
        ((s ^ i) (P j) : L) := by
      simpa [σA, i] using hactionL σ (P j)
    have hPi0 : ((P i : L) : AlgebraicClosure M) ≠ 0 :=
      Subtype.coe_ne_coe.mpr (hP0 i)
    have hPj0 : ((P j : L) : AlgebraicClosure M) ≠ 0 :=
      Subtype.coe_ne_coe.mpr (hP0 j)
    have hsPj0 : (((s ^ i) (P j) : L) : AlgebraicClosure M) ≠ 0 :=
      Subtype.coe_ne_coe.mpr ((map_ne_zero (s ^ i)).2 (hP0 j))
    dsimp [R]
    rw [map_div₀, map_pow, hσβ, mul_pow, ← pow_mul, hσP, hPadd]
    rw [show (((P i * (s ^ i) (P j) : L)) : AlgebraicClosure M) =
      (P i : AlgebraicClosure M) * ((s ^ i) (P j) : L) by rfl]
    field_simp [hPi0, hPj0, hsPj0]
    ring
  let V : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ =>
    (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) v / v
  let T : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ =>
    R (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val / V σ
  have hV0 (σ : Field.absoluteGaloisGroup M) : V σ ≠ 0 := by
    dsimp [V]
    exact div_ne_zero
      ((map_ne_zero (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)).2 hv0) hv0
  have hR0 (n : ℕ) : R n ≠ 0 := by
    dsimp [R]
    exact div_ne_zero (pow_ne_zero n hβ0)
      (Subtype.coe_ne_coe.mpr (hP0 n))
  have hVpow (σ : Field.absoluteGaloisGroup M) : (V σ) ^ ℓ =
      (((s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val)
          (u : L) : L) : AlgebraicClosure M) /
        ((u : L) : AlgebraicClosure M) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    dsimp [V]
    rw [div_pow, ← map_pow, hvpow]
    have huact := hactionL σ (u : L)
    simpa [σA] using congrArg (fun x => x / ((u : L) : AlgebraicClosure M)) huact
  have hTpow (σ : Field.absoluteGaloisGroup M) : (T σ) ^ ℓ = 1 := by
    dsimp [T]
    rw [div_pow, hRpow, hVpow, div_self]
    exact div_ne_zero
      (Subtype.coe_ne_coe.mpr
        ((map_ne_zero (s ^
          (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val)).2 hu0))
      (Subtype.coe_ne_coe.mpr hu0)
  let ζA : AlgebraicClosure M := algebraMap M (AlgebraicClosure M) ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M (AlgebraicClosure M)).injective
  let c0 : Field.absoluteGaloisGroup M → ZMod ℓ := fun σ =>
    ((cupPrimitiveRootIndex ζA hζA (T σ)).val : ZMod ℓ)
  have hc0val (σ : Field.absoluteGaloisGroup M) :
      (c0 σ).val = (cupPrimitiveRootIndex ζA hζA (T σ)).val := by
    dsimp [c0]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt
      (cupPrimitiveRootIndex ζA hζA (T σ)).isLt]
  have hc0root (σ : Field.absoluteGaloisGroup M) :
      ζA ^ (c0 σ).val = T σ := by
    rw [hc0val]
    exact cupPrimitiveRootIndex_spec ζA hζA (T σ) (hTpow σ)
  have hxloc : IsLocallyConstant (fun σ : Field.absoluteGaloisGroup M =>
      (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val) := by
    apply IsLocallyConstant.comp
      (f := fun σ : Field.absoluteGaloisGroup M =>
        continuousCharacterValue (kummerCharacter ζ hζ a) σ)
      ((IsLocallyConstant.iff_continuous _).2 ?_)
      ZMod.val
    change Continuous ((kummerCharacter ζ hζ a) ∘ Additive.ofMul)
    exact (kummerCharacter ζ hζ a).continuous.comp continuous_ofMul
  have hvloc : IsLocallyConstant (fun σ : Field.absoluteGaloisGroup M =>
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) v) :=
    absoluteGalois_apply_isLocallyConstant v
  have hTloc : IsLocallyConstant T := by
    exact hxloc.comp₂ hvloc (fun i w => R i / (w / v))
  have hc0loc : IsLocallyConstant c0 :=
    hTloc.comp (fun x =>
      ((cupPrimitiveRootIndex ζA hζA x).val : ZMod ℓ))
  let cRev : C(Field.absoluteGaloisGroup M, ZMod ℓ) :=
    ⟨c0, hc0loc.continuous⟩
  have hVmul (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (V τ) * V σ =
        V (σ * τ) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    let τA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := τ
    change σA (τA v / v) * (σA v / v) = σA (τA v) / v
    rw [map_div₀]
    field_simp [hv0, (map_ne_zero σA).2 hv0]
  have hRstandard (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)
          (R (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val) *
          R (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val /
          R (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val =
        ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val *
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val) := by
    let i := (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
    let j := (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val
    have hxmul : continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ) =
        continuousCharacterValue (kummerCharacter ζ hζ a) σ +
          continuousCharacterValue (kummerCharacter ζ hζ a) τ := by
      change (kummerCharacter ζ hζ a)
        (Additive.ofMul (σ * τ)) =
          (kummerCharacter ζ hζ a) (Additive.ofMul σ) +
            (kummerCharacter ζ hζ a) (Additive.ofMul τ)
      exact map_add (kummerCharacter ζ hζ a) (Additive.ofMul σ) (Additive.ofMul τ)
    have hk : (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val =
        (i + j) % ℓ := by rw [hxmul, ZMod.val_add]
    have hRk : R (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val =
        R (i + j) := by
      rw [hk]
      exact hRmod (i + j)
    rw [hRk]
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    change σA (R j) * R i / R (i + j) =
      ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val * j)
    have hr := hRaction σ j
    change σA (R j) * R i =
      ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val * j) *
        R (i + j) at hr
    rw [hr]
    exact mul_div_cancel_right₀ _ (hR0 (i + j))
  have hTstandard (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (T τ) *
          T σ / T (σ * τ) =
        ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val *
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    let i := (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
    let j := (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val
    let k := (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val
    have hσV0 : σA (V τ) ≠ 0 := (map_ne_zero σA).2 (hV0 τ)
    have hσR0 : σA (R j) ≠ 0 := (map_ne_zero σA).2 (hR0 j)
    have hTk0 : T (σ * τ) ≠ 0 := by
      dsimp [T]
      exact div_ne_zero (hR0 k) (hV0 (σ * τ))
    change σA (R j / V τ) * (R i / V σ) / (R k / V (σ * τ)) = _
    calc
      σA (R j / V τ) * (R i / V σ) / (R k / V (σ * τ)) =
          (σA (R j) * R i / R k) /
            (σA (V τ) * V σ / V (σ * τ)) := by
        rw [map_div₀]
        field_simp [hσV0, hσR0, hV0 σ, hV0 τ, hV0 (σ * τ),
          hR0 i, hR0 j, hR0 k, hTk0]
      _ = _ := by rw [hRstandard, hVmul, div_self (hV0 (σ * τ)), div_one]
  have hTfixed (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (T τ) = T τ := by
    rw [← hc0root τ]
    dsimp [ζA]
    simp
  have hTordinary (σ τ : Field.absoluteGaloisGroup M) :
      T σ * T τ / T (σ * τ) =
        ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val *
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val) := by
    rw [← hTfixed σ τ, mul_comm]
    exact hTstandard σ τ
  have hrev (σ τ : Field.absoluteGaloisGroup M) :
      continuousCharacterValue (kummerCharacter ζ hζ b) σ *
          continuousCharacterValue (kummerCharacter ζ hζ a) τ =
        cRev σ + cRev τ - cRev (σ * τ) := by
    change continuousCharacterValue (kummerCharacter ζ hζ b) σ *
          continuousCharacterValue (kummerCharacter ζ hζ a) τ =
        c0 σ + c0 τ - c0 (σ * τ)
    apply ZMod.val_injective ℓ
    apply hζA.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [primitiveRoot_pow_val_mul hζA,
      primitiveRoot_pow_val_sub hζA,
      primitiveRoot_pow_val_add' hζA,
      hc0root, hc0root, hc0root]
    exact (hTordinary σ τ).symm
  apply cupZero_symm
  exact ⟨cRev, hrev⟩

-- The explicit finite-level descent below is elaboration-heavy.
set_option maxHeartbeats 1000000

/-- A trivialization of the explicit Kummer cup cocycle makes the second
Kummer parameter a norm. -/
private theorem cyclic_norm_criterion_to_norm
    {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] {ℓ : ℕ} [Fact ℓ.Prime]
    [IsGalois M E] [IsCyclic (E ≃ₐ[M] E)]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (ha : kummerQuotientClass ℓ a ≠ 0)
    (α : E) (hαpow : α ^ ℓ = algebraMap M E (a : M))
    (hαgen : Algebra.adjoin M ({α} : Set E) = ⊤)
    (hdegree : Module.finrank M E = ℓ)
    (hcup : CupZero ℓ (kummerCharacter ζ hζ a)
      (kummerCharacter ζ hζ b)) :
    IsUnitNorm M E b := by
  classical
  obtain ⟨c, hc⟩ := cupZero_symm hcup
  let ι : E →ₐ[M] AlgebraicClosure M := IsAlgClosed.lift
  let L : IntermediateField M (AlgebraicClosure M) := ι.fieldRange
  let e : E ≃ₐ[M] L := AlgHom.equivFieldRange ι
  letI : FiniteDimensional M L := e.toLinearEquiv.finiteDimensional
  letI : IsGalois M L := IsGalois.of_algEquiv e
  have hfinrank : Module.finrank M L = ℓ := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact hdegree
  have hcard : Nat.card (L ≃ₐ[M] L) = ℓ := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  letI : IsCyclic (L ≃ₐ[M] L) := isCyclic_of_prime_card hcard
  let r : L := e α
  have hrpowL : r ^ ℓ = algebraMap M L (a : M) := by
    dsimp [r]
    rw [← map_pow, hαpow, e.commutes]
  have hrpowA : (r : AlgebraicClosure M) ^ ℓ =
      algebraMap M (AlgebraicClosure M) (a : M) := by
    have h := congrArg Subtype.val hrpowL
    simpa [L] using h
  have hr0 : r ≠ 0 := by
    intro hr
    have ha0 : algebraMap M L (a : M) ≠ 0 :=
      (map_ne_zero (algebraMap M L)).2 (Units.ne_zero a)
    apply ha0
    rw [← hrpowL, hr, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  have hLgen : Algebra.adjoin M ({r} : Set L) = ⊤ := by
    calc
      Algebra.adjoin M ({r} : Set L) =
          (Algebra.adjoin M ({α} : Set E)).map e.toAlgHom := by
        rw [AlgHom.map_adjoin, Set.image_singleton]
        rfl
      _ = ⊤ := by
        rw [hαgen, Algebra.map_top]
        exact (AlgHom.range_eq_top e.toAlgHom).2 e.surjective
  obtain ⟨ρ, hρ⟩ := exists_kummerCharacter_value_one ζ hζ a ha
  let s : L ≃ₐ[M] L := AlgEquiv.restrictNormalHom L ρ
  have hsr : s r = algebraMap M L ζ * r := by
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    have hact := kummerCharacter_action_of_root ζ hζ a
      (r : AlgebraicClosure M) hrpowA ρ
    rw [hρ, ZMod.val_one] at hact
    simpa [s, L] using hact
  have hsne : s ≠ 1 := by
    intro hs
    have heq : algebraMap M L ζ * r = r := by
      rw [← hsr, hs]
      rfl
    have hζmap : algebraMap M L ζ = 1 := by
      apply mul_right_cancel₀ hr0
      simpa using heq
    have hζone : ζ = 1 := by
      apply (algebraMap M L).injective
      simpa using hζmap
    exact hζ.ne_one (Fact.out : ℓ.Prime).one_lt hζone
  have hsgen : ∀ t : L ≃ₐ[M] L, t ∈ Subgroup.zpowers s :=
    fun t => mem_zpowers_of_prime_card hcard hsne
  have hs_pow_r (n : ℕ) :
      (s ^ n) r = (algebraMap M L ζ) ^ n * r := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ, AlgEquiv.mul_apply, hsr, map_mul,
        (s ^ n).commutes, hn, pow_succ]
      ring
  have hrestrict (σ : Field.absoluteGaloisGroup M) :
      AlgEquiv.restrictNormalHom L
          (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) =
        s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    change AlgEquiv.restrictNormalHom L σA = _
    apply AlgEquiv.ext
    have heq : (AlgEquiv.restrictNormalHom L σA).toAlgHom =
        (s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hLgen
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change (AlgEquiv.restrictNormalHom L σA) r =
        (s ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val) r
      apply Subtype.ext
      have hlhs : (((AlgEquiv.restrictNormalHom L σA) r : L) :
          AlgebraicClosure M) = σA (r : AlgebraicClosure M) :=
        AlgEquiv.restrictNormalHom_apply L σA r
      have hrhs := congrArg Subtype.val
        (hs_pow_r (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val)
      have hact := kummerCharacter_action_of_root ζ hζ a
        (r : AlgebraicClosure M) hrpowA σ
      rw [hlhs]
      simpa [L] using hact.trans (by simpa [L] using hrhs.symm)
    intro x
    exact DFunLike.congr_fun heq x
  have hfixL_iff (σ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) ∈ L.fixingSubgroup ↔
        continuousCharacterValue (kummerCharacter ζ hζ a) σ = 0 := by
    rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker,
      hrestrict]
    constructor
    · intro hp
      have hpr := DFunLike.congr_fun (congrArg (fun t : L ≃ₐ[M] L => t) hp) r
      rw [hs_pow_r] at hpr
      have hpζ : (algebraMap M L ζ) ^
          (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val = 1 := by
        apply mul_right_cancel₀ hr0
        simpa using hpr
      apply ZMod.val_injective ℓ
      simp only [ZMod.val_zero]
      exact (hζ.map_of_injective (algebraMap M L).injective).pow_inj
        (ZMod.val_lt _) (Fact.out : ℓ.Prime).pos hpζ
    · intro hx
      rw [hx, ZMod.val_zero, pow_zero]
  obtain ⟨β, hβpow, hβact⟩ := kummerCharacter_definingEquation ζ hζ b
  have hβ0 : β ≠ 0 := by
    intro hβ
    have hb0 : algebraMap M (AlgebraicClosure M) (b : M) ≠ 0 :=
      (map_ne_zero (algebraMap M (AlgebraicClosure M))).2 (Units.ne_zero b)
    apply hb0
    rw [← hβpow, hβ, zero_pow (Fact.out : ℓ.Prime).ne_zero]
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let ζA : AlgebraicClosure M := algebraMap M (AlgebraicClosure M) ζ
  have hζA : IsPrimitiveRoot ζA ℓ :=
    hζ.map_of_injective (algebraMap M (AlgebraicClosure M)).injective
  let m : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ =>
    ζA ^ (c σ).val
  let q : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ =>
    β ^ (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
  let t : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ => q σ / m σ
  have hm0 (σ : Field.absoluteGaloisGroup M) : m σ ≠ 0 :=
    pow_ne_zero _ (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero)
  have hq0 (σ : Field.absoluteGaloisGroup M) : q σ ≠ 0 :=
    pow_ne_zero _ hβ0
  have ht0 (σ : Field.absoluteGaloisGroup M) : t σ ≠ 0 :=
    div_ne_zero (hq0 σ) (hm0 σ)
  have hmdiff (σ τ : Field.absoluteGaloisGroup M) :
      m σ * m τ / m (σ * τ) =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ b) σ *
          continuousCharacterValue (kummerCharacter ζ hζ a) τ).val := by
    dsimp [m]
    rw [← primitiveRoot_pow_val_add' hζA,
      ← primitiveRoot_pow_val_sub hζA, hc σ τ]
  have hc_one : c (1 : Field.absoluteGaloisGroup M) = 0 := by
    have h := hc 1 1
    simpa [continuousCharacterValue] using h.symm
  let H : Subgroup (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M) := L.fixingSubgroup
  let cH : H →* Multiplicative (ZMod ℓ) :=
    { toFun := fun σ => Multiplicative.ofAdd
        (c (show Field.absoluteGaloisGroup M from σ.1))
      map_one' := congrArg Multiplicative.ofAdd hc_one
      map_mul' := fun σ τ => by
        apply Multiplicative.toAdd.injective
        change c (show Field.absoluteGaloisGroup M from σ.1 * τ.1) =
          c (show Field.absoluteGaloisGroup M from σ.1) +
            c (show Field.absoluteGaloisGroup M from τ.1)
        have hxτ : continuousCharacterValue (kummerCharacter ζ hζ a)
            (show Field.absoluteGaloisGroup M from τ.1) = 0 :=
          (hfixL_iff (show Field.absoluteGaloisGroup M from τ.1)).1 τ.2
        have hmul : (show Field.absoluteGaloisGroup M from σ.1 * τ.1) =
            (show Field.absoluteGaloisGroup M from σ.1) *
              (show Field.absoluteGaloisGroup M from τ.1) := rfl
        rw [hmul]
        have h := hc (show Field.absoluteGaloisGroup M from σ.1)
          (show Field.absoluteGaloisGroup M from τ.1)
        rw [hxτ, mul_zero] at h
        linear_combination h }
  let kerSet : Set (Field.absoluteGaloisGroup M) :=
    {σ | (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) ∈
        L.fixingSubgroup ∧ c σ = 0}
  have hkerOpen : IsOpen kerSet := by
    have hfixOpen : IsOpen
        (L.fixingSubgroup : Set (AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M)) :=
      L.fixingSubgroup_isOpen
    have hcOpen : IsOpen {σ : Field.absoluteGaloisGroup M | c σ = 0} := by
      exact (isOpen_discrete ({0} : Set (ZMod ℓ))).preimage c.continuous
    exact hfixOpen.inter hcOpen
  have hkerOne : (1 : Field.absoluteGaloisGroup M) ∈ kerSet := by
    exact ⟨L.fixingSubgroup.one_mem, hc_one⟩
  have hkerNhd : kerSet ∈ nhds (1 : Field.absoluteGaloisGroup M) :=
    hkerOpen.mem_nhds hkerOne
  obtain ⟨F, hFfin, hFnormal, hFker⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal M (AlgebraicClosure M) kerSet).mp hkerNhd
  letI : FiniteDimensional M F := hFfin
  letI : Normal M F := hFnormal
  let Fsep := separableClosure M F
  letI : IsGalois M Fsep := separableClosure.isGalois M F
  let F' : IntermediateField M (AlgebraicClosure M) := IntermediateField.lift Fsep
  let eF : Fsep ≃ₐ[M] F' := IntermediateField.liftAlgEquiv Fsep
  letI : FiniteDimensional M F' := eF.toLinearEquiv.finiteDimensional
  letI : Normal M F' := Normal.of_algEquiv eF
  letI : Algebra.IsSeparable M F' := ⟨fun x => by
    have hs := Algebra.IsSeparable.isSeparable M (eF.symm x)
    have hm := hs.map eF.toAlgHom eF.injective
    simpa using hm⟩
  letI : IsGalois M F' := ⟨⟩
  have hF'ker : ∀ σ : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M,
      σ ∈ F'.fixingSubgroup →
        (show Field.absoluteGaloisGroup M from σ) ∈ kerSet := by
    intro σ hσ
    apply hFker
    apply (IntermediateField.mem_fixingSubgroup_iff F σ).2
    intro x hx
    let σF : F ≃ₐ[M] F := AlgEquiv.restrictNormalHom F σ
    have hσFcomm (y : Fsep) : σF (algebraMap Fsep F y) = algebraMap Fsep F y := by
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      have hyF' : ((eF y : F') : AlgebraicClosure M) ∈ F' := (eF y).prop
      have hyfix := (IntermediateField.mem_fixingSubgroup_iff F' σ).1 hσ
        ((eF y : F') : AlgebraicClosure M) hyF'
      simpa [eF, F', Fsep, IntermediateField.liftAlgEquiv_apply] using hyfix
    let σFhom : F →ₐ[Fsep] F :=
      { σF.toAlgHom with commutes' := hσFcomm }
    have heq : σFhom = AlgHom.id Fsep F := Subsingleton.elim _ _
    have happ := DFunLike.congr_fun heq ⟨x, hx⟩
    have happ' := congrArg Subtype.val happ
    simpa [σFhom, σF, AlgEquiv.restrictNormalHom_apply] using happ'
  let U : IntermediateField M (AlgebraicClosure M) := L ⊔ F'
  letI : FiniteDimensional M U := IntermediateField.finiteDimensional_sup L F'
  letI : Normal M U :=
    IntermediateField.normal_sup M (AlgebraicClosure M) L F'
  letI : Algebra.IsSeparable M U :=
    IntermediateField.isSeparable_sup M (AlgebraicClosure M) L F'
  letI : IsGalois M U := ⟨⟩
  have hUker : ∀ σ : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M,
      σ ∈ U.fixingSubgroup →
        (show Field.absoluteGaloisGroup M from σ) ∈ kerSet := by
    intro σ hσ
    apply hF'ker σ
    exact IntermediateField.fixingSubgroup_le le_sup_right hσ
  have hLU : L ≤ U := le_sup_left
  letI : Algebra L U := (IntermediateField.inclusion hLU).toAlgebra
  letI : IsScalarTower M L U :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional L U := FiniteDimensional.right M L U
  letI : IsGalois L U := IsGalois.tower_top_of_isGalois M L U
  have hLU_apply (x : L) :
      algebraMap L U x = ⟨(x : AlgebraicClosure M), hLU x.2⟩ := rfl
  let rU : H →* (U ≃ₐ[L] U) :=
    { toFun := fun σ =>
        { AlgEquiv.restrictNormalHom U σ.1 with
          commutes' := fun x => by
            rw [hLU_apply]
            apply Subtype.ext
            have hres := AlgEquiv.restrictNormalHom_apply U σ.1
              (⟨(x : AlgebraicClosure M), hLU x.2⟩ : U)
            have hfix := (IntermediateField.mem_fixingSubgroup_iff L σ.1).1 σ.2
              (x : AlgebraicClosure M) x.2
            exact hres.trans hfix }
      map_one' := by
        apply AlgEquiv.ext
        intro x
        apply Subtype.ext
        exact AlgEquiv.restrictNormalHom_apply U (1 : H).1 x
      map_mul' := fun σ τ => by
        apply AlgEquiv.ext
        intro x
        apply Subtype.ext
        calc
          ((AlgEquiv.restrictNormalHom U (σ * τ).1) x : U) =
              (σ * τ).1 (x : AlgebraicClosure M) :=
            AlgEquiv.restrictNormalHom_apply U (σ * τ).1 x
          _ = σ.1 (τ.1 (x : AlgebraicClosure M)) := rfl
          _ = σ.1 ((AlgEquiv.restrictNormalHom U τ.1 x : U) :
              AlgebraicClosure M) :=
            congrArg σ.1 (AlgEquiv.restrictNormalHom_apply U τ.1 x).symm
          _ = ((AlgEquiv.restrictNormalHom U σ.1)
                ((AlgEquiv.restrictNormalHom U τ.1) x) : U) :=
            (AlgEquiv.restrictNormalHom_apply U σ.1
              ((AlgEquiv.restrictNormalHom U τ.1) x)).symm }
  have hrUsurj : Function.Surjective rU := by
    intro g
    let gM : U ≃ₐ[M] U := g.restrictScalars M
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := M) (K₁ := U) (AlgebraicClosure M) gM
    have hσL : σ ∈ L.fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff L σ).2
      intro x hx
      let xL : L := ⟨x, hx⟩
      have happ := DFunLike.congr_fun hσ (algebraMap L U xL)
      have happ' := congrArg Subtype.val happ
      have hgfix := congrArg Subtype.val (g.commutes xL)
      have happ'' : σ x = ((g (algebraMap L U xL) : U) : AlgebraicClosure M) := by
        simpa [gM, hLU_apply, AlgEquiv.restrictNormalHom_apply] using happ'
      have hgfix' : ((g (algebraMap L U xL) : U) : AlgebraicClosure M) = x := by
        simpa [hLU_apply] using hgfix
      exact happ''.trans hgfix'
    refine ⟨⟨σ, hσL⟩, ?_⟩
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hσ x
  have hrUker : rU.ker ≤ cH.ker := by
    intro σ hσ
    have hσU : σ.1 ∈ U.fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff U σ.1).2
      intro x hx
      let xU : U := ⟨x, hx⟩
      have happ := DFunLike.congr_fun hσ xU
      have happ' := congrArg Subtype.val happ
      simpa [rU, AlgEquiv.restrictNormalHom_apply] using happ'
    have hcσ : c (show Field.absoluteGaloisGroup M from σ.1) = 0 :=
      (hUker σ.1 hσU).2
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    exact hcσ
  let ψ : (U ≃ₐ[L] U) →* Multiplicative (ZMod ℓ) :=
    rU.liftOfSurjective hrUsurj ⟨cH, hrUker⟩
  have hψ (σ : H) :
      (ψ (rU σ)).toAdd = c (show Field.absoluteGaloisGroup M from σ.1) := by
    have hcomp : ψ.comp rU = cH := by
      exact congrArg Subtype.val
        ((rU.liftOfSurjective hrUsurj).symm_apply_apply ⟨cH, hrUker⟩)
    have happ := DFunLike.congr_fun hcomp σ
    exact congrArg Multiplicative.toAdd happ
  let ζU : U := algebraMap M U ζ
  have hζU : IsPrimitiveRoot ζU ℓ :=
    hζ.map_of_injective (algebraMap M U).injective
  let fU : (U ≃ₐ[L] U) → Uˣ := fun g =>
    Units.mk0 (ζU ^ (-(ψ g).toAdd).val)
      (pow_ne_zero _ (hζU.ne_zero (Fact.out : ℓ.Prime).ne_zero))
  letI : SMul (U ≃ₐ[L] U) Uˣ :=
    AlgEquiv.instMulDistribMulActionUnits.toSMul
  have hfU : groupCohomology.IsMulCocycle₁ fU := by
    intro g h
    apply Units.ext
    have hψmul : (ψ (g * h)).toAdd = (ψ g).toAdd + (ψ h).toAdd := by
      rw [map_mul]
      rfl
    change ζU ^ (-(ψ (g * h)).toAdd).val =
      g (ζU ^ (-(ψ h).toAdd).val) * ζU ^ (-(ψ g).toAdd).val
    have hgζ : g ζU = ζU := by
      dsimp [ζU]
      rw [show algebraMap M U ζ = algebraMap L U (algebraMap M L ζ) by
        exact IsScalarTower.algebraMap_apply M L U ζ,
        g.commutes]
    rw [hψmul, neg_add_rev, primitiveRoot_pow_val_add' hζU,
      map_pow, hgζ]
  obtain ⟨w, hw⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units fU hfU
  have hw0 : (w : U) ≠ 0 := Units.ne_zero w
  have hwH (σ : H) : σ.1 ((w : U) : AlgebraicClosure M) /
      ((w : U) : AlgebraicClosure M) =
        ζA ^ (-c (show Field.absoluteGaloisGroup M from σ.1)).val := by
    have hwu := hw (rU σ)
    rw [AlgEquiv.smul_units_def] at hwu
    have hwu' := congrArg (fun x : Uˣ => (x : U)) hwu
    have hwu'' : (rU σ) (w : U) / (w : U) =
        ζU ^ (-(ψ (rU σ)).toAdd).val := by
      simpa [fU] using hwu'
    rw [hψ σ] at hwu''
    have hact := AlgEquiv.restrictNormalHom_apply U σ.1 (w : U)
    rw [← hact]
    exact congrArg Subtype.val hwu''
  have hχa_mul (σ τ : Field.absoluteGaloisGroup M) :
      continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ) =
        continuousCharacterValue (kummerCharacter ζ hζ a) σ +
          continuousCharacterValue (kummerCharacter ζ hζ a) τ := by
    change (kummerCharacter ζ hζ a) (Additive.ofMul (σ * τ)) =
      (kummerCharacter ζ hζ a) (Additive.ofMul σ) +
        (kummerCharacter ζ hζ a) (Additive.ofMul τ)
    exact map_add (kummerCharacter ζ hζ a) (Additive.ofMul σ) (Additive.ofMul τ)
  have hmfixed (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (m τ) = m τ := by
    dsimp [m, ζA]
    simp
  have htdiff_quotient (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (t τ) * t σ /
          t (σ * τ) =
        ((show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (q τ) * q σ /
          q (σ * τ)) / (m σ * m τ / m (σ * τ)) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    change σA (q τ / m τ) * (q σ / m σ) / (q (σ * τ) / m (σ * τ)) = _
    rw [map_div₀, hmfixed σ τ]
    field_simp [hq0 σ, hq0 τ, hq0 (σ * τ), hm0 σ, hm0 τ,
      hm0 (σ * τ), (map_ne_zero σA).2 (hq0 τ)]
    ring
  have hqdiff_of_val_add_lt (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val < ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (q τ) * q σ /
          q (σ * τ) =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ b) σ *
          continuousCharacterValue (kummerCharacter ζ hζ a) τ).val := by
    let i := (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
    let j := (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val
    have hk : (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val =
        i + j := by
      rw [hχa_mul, ZMod.val_add, Nat.mod_eq_of_lt hsum]
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    dsimp [q]
    rw [hk]
    change σA (β ^ j) * β ^ i / β ^ (i + j) = _
    rw [map_pow, hβact, mul_pow, primitiveRoot_pow_val_mul hζA, pow_add]
    field_simp [pow_ne_zero i hβ0, pow_ne_zero j hβ0]
    ring
  have hqdiff_of_val_add_eq (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val = ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (q τ) * q σ /
          q (σ * τ) =
        ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ b) σ *
          continuousCharacterValue (kummerCharacter ζ hζ a) τ).val *
          algebraMap M (AlgebraicClosure M) (b : M) := by
    let i := (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val
    let j := (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val
    have hk : (continuousCharacterValue (kummerCharacter ζ hζ a) (σ * τ)).val = 0 := by
      rw [hχa_mul, ZMod.val_add, hsum, Nat.mod_self]
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    dsimp [q]
    rw [hk]
    change σA (β ^ j) * β ^ i / β ^ 0 = _
    rw [map_pow, hβact, mul_pow, pow_zero, div_one,
      primitiveRoot_pow_val_mul hζA]
    calc
      (ζA ^ (continuousCharacterValue (kummerCharacter ζ hζ b) σ).val) ^ j *
            β ^ j * β ^ i =
          ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val * j) *
            β ^ (i + j) := by rw [pow_mul, pow_add]; ring
      _ = ζA ^ ((continuousCharacterValue (kummerCharacter ζ hζ b) σ).val * j) *
            β ^ ℓ := by rw [hsum]
      _ = _ := by rw [hβpow]
  have htdiff_of_val_add_lt (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val < ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (t τ) * t σ /
          t (σ * τ) = 1 := by
    rw [htdiff_quotient, hqdiff_of_val_add_lt σ τ hsum, hmdiff,
      div_self]
    exact pow_ne_zero _ (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero)
  have htdiff_of_val_add_eq (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val = ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (t τ) * t σ /
          t (σ * τ) = algebraMap M (AlgebraicClosure M) (b : M) := by
    rw [htdiff_quotient, hqdiff_of_val_add_eq σ τ hsum, hmdiff]
    field_simp [pow_ne_zero _ (hζA.ne_zero (Fact.out : ℓ.Prime).ne_zero)]
  let wA : AlgebraicClosure M := ((w : U) : AlgebraicClosure M)
  have hwA0 : wA ≠ 0 := by
    intro hwz
    apply hw0
    apply Subtype.ext
    exact hwz
  let d : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ =>
    (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) wA / wA
  have hd0 (σ : Field.absoluteGaloisGroup M) : d σ ≠ 0 := by
    exact div_ne_zero
      ((map_ne_zero (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ)).2 hwA0)
      hwA0
  have hddiff (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (d τ) * d σ /
          d (σ * τ) = 1 := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    let τA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := τ
    change σA (τA wA / wA) * (σA wA / wA) /
      (σA (τA wA) / wA) = 1
    rw [map_div₀]
    field_simp [hwA0, (map_ne_zero σA).2 hwA0,
      (map_ne_zero τA).2 hwA0, (map_ne_zero σA).2 ((map_ne_zero τA).2 hwA0)]
  let T : Field.absoluteGaloisGroup M → AlgebraicClosure M := fun σ => t σ / d σ
  have hT0 (σ : Field.absoluteGaloisGroup M) : T σ ≠ 0 :=
    div_ne_zero (ht0 σ) (hd0 σ)
  have hTdiff_eq_tdiff (σ τ : Field.absoluteGaloisGroup M) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (T τ) * T σ /
          T (σ * τ) =
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (t τ) * t σ /
          t (σ * τ) := by
    let σA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := σ
    change σA (t τ / d τ) * (t σ / d σ) / (t (σ * τ) / d (σ * τ)) = _
    rw [map_div₀]
    calc
      (σA (t τ) / σA (d τ)) * (t σ / d σ) /
          (t (σ * τ) / d (σ * τ)) =
        (σA (t τ) * t σ / t (σ * τ)) /
          (σA (d τ) * d σ / d (σ * τ)) := by
        field_simp [ht0 σ, ht0 τ, ht0 (σ * τ), hd0 σ, hd0 τ,
          hd0 (σ * τ), (map_ne_zero σA).2 (ht0 τ),
          (map_ne_zero σA).2 (hd0 τ)]
      _ = _ := by rw [hddiff, div_one]
  have hTdiff_of_val_add_lt (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val < ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (T τ) * T σ /
          T (σ * τ) = 1 := by
    rw [hTdiff_eq_tdiff, htdiff_of_val_add_lt σ τ hsum]
  have hTdiff_of_val_add_eq (σ τ : Field.absoluteGaloisGroup M)
      (hsum : (continuousCharacterValue (kummerCharacter ζ hζ a) σ).val +
          (continuousCharacterValue (kummerCharacter ζ hζ a) τ).val = ℓ) :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) (T τ) * T σ /
          T (σ * τ) = algebraMap M (AlgebraicClosure M) (b : M) := by
    rw [hTdiff_eq_tdiff, htdiff_of_val_add_eq σ τ hsum]
  have hd_eq_t_of_mem_H (σ : H) :
      d (show Field.absoluteGaloisGroup M from σ.1) =
        t (show Field.absoluteGaloisGroup M from σ.1) := by
    let σG : Field.absoluteGaloisGroup M := σ.1
    have hx : continuousCharacterValue (kummerCharacter ζ hζ a) σG = 0 :=
      (hfixL_iff σG).1 σ.2
    have hneg := primitiveRoot_pow_val_sub hζA (0 : ZMod ℓ) (c σG)
    simp only [zero_sub, ZMod.val_zero, pow_zero] at hneg
    calc
      d σG = ζA ^ (-c σG).val := by
        exact hwH σ
      _ = 1 / ζA ^ (c σG).val := hneg
      _ = q σG / m σG := by
        dsimp [q, m]
        rw [hx, ZMod.val_zero, pow_zero]
      _ = t σG := rfl
  have hT_eq_one_of_mem_H (σ : H) :
      T (show Field.absoluteGaloisGroup M from σ.1) = 1 := by
    dsimp [T]
    rw [hd_eq_t_of_mem_H σ, div_self (ht0 _)]
  have hχa_rho_pow (n : ℕ) :
      continuousCharacterValue (kummerCharacter ζ hζ a) (ρ ^ n) =
        (n : ZMod ℓ) := by
    induction n with
    | zero => simp [continuousCharacterValue]
    | succ n ih =>
      rw [pow_succ, hχa_mul, ih, hρ, Nat.cast_succ]
  have hχa_rho_pow_val {n : ℕ} (hn : n < ℓ) :
      (continuousCharacterValue (kummerCharacter ζ hζ a) (ρ ^ n)).val = n := by
    rw [hχa_rho_pow, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  let zA : AlgebraicClosure M := T ρ
  let P : ℕ → AlgebraicClosure M := fun n =>
    partialConjugateProduct
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ) zA n
  have hTpow_succ (n : ℕ) (hn : n + 1 < ℓ) :
      T (ρ ^ (n + 1)) =
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ n) zA *
          T (ρ ^ n) := by
    have hsum :
        (continuousCharacterValue (kummerCharacter ζ hζ a) (ρ ^ n)).val +
            (continuousCharacterValue (kummerCharacter ζ hζ a) ρ).val < ℓ := by
      rw [hχa_rho_pow_val (Nat.lt_trans (Nat.lt_succ_self n) hn), hρ,
        ZMod.val_one]
      exact hn
    have hd := hTdiff_of_val_add_lt (ρ ^ n) ρ hsum
    have heq := (div_eq_one_iff_eq (hT0 ((ρ ^ n) * ρ))).1 hd
    rw [← pow_succ] at heq
    exact heq.symm
  have hPzero : P 0 = 1 := by
    simp [P, partialConjugateProduct]
  have hPsucc (n : ℕ) :
      P (n + 1) = P n *
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ n) zA := by
    dsimp [P, partialConjugateProduct]
    rw [Finset.prod_range_succ]
    congr 1
  have hTpow_eq_P (n : ℕ) (hn : n < ℓ) : T (ρ ^ n) = P n := by
    induction n with
    | zero =>
      have h1 : (1 : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M) ∈
          L.fixingSubgroup := L.fixingSubgroup.one_mem
      have hT1 := hT_eq_one_of_mem_H (⟨1, h1⟩ : H)
      rw [pow_zero, hPzero]
      exact hT1
    | succ n ih =>
      have hn' : n < ℓ := Nat.lt_trans (Nat.lt_succ_self n) hn
      rw [show n + 1 = Nat.succ n by omega, hTpow_succ n (by omega), ih hn',
        hPsucc]
      exact mul_comm _ _
  have hρpowℓ_H :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ ℓ) ∈
        L.fixingSubgroup := by
    apply (hfixL_iff (ρ ^ ℓ)).2
    rw [hχa_rho_pow, ZMod.natCast_self]
  have hTρpowℓ : T (ρ ^ ℓ) = 1 :=
    hT_eq_one_of_mem_H (⟨ρ ^ ℓ, hρpowℓ_H⟩ : H)
  have hPcycle : P ℓ = algebraMap M (AlgebraicClosure M) (b : M) := by
    let n := ℓ - 1
    have hn : n < ℓ := Nat.sub_lt (Fact.out : ℓ.Prime).pos Nat.zero_lt_one
    have hnadd : n + 1 = ℓ := Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_le
    have hsum :
        (continuousCharacterValue (kummerCharacter ζ hζ a) (ρ ^ n)).val +
            (continuousCharacterValue (kummerCharacter ζ hζ a) ρ).val = ℓ := by
      rw [hχa_rho_pow_val hn, hρ, ZMod.val_one]
      exact hnadd
    have hd := hTdiff_of_val_add_eq (ρ ^ n) ρ hsum
    rw [← pow_succ, hnadd, hTρpowℓ, div_one, hTpow_eq_P n hn] at hd
    rw [← hnadd, hPsucc]
    simpa [zA, mul_comm] using hd
  have hT_right_H (γ : Field.absoluteGaloisGroup M) (σ : H) :
      T (γ * (show Field.absoluteGaloisGroup M from σ.1)) = T γ := by
    let σG : Field.absoluteGaloisGroup M := σ.1
    have hxσ : continuousCharacterValue (kummerCharacter ζ hζ a) σG = 0 :=
      (hfixL_iff σG).1 σ.2
    have hsum :
        (continuousCharacterValue (kummerCharacter ζ hζ a) γ).val +
            (continuousCharacterValue (kummerCharacter ζ hζ a) σG).val < ℓ := by
      rw [hxσ, ZMod.val_zero, add_zero]
      exact ZMod.val_lt _
    have hd := hTdiff_of_val_add_lt γ σG hsum
    rw [hT_eq_one_of_mem_H σ, map_one, one_mul] at hd
    exact ((div_eq_one_iff_eq (hT0 (γ * σG))).1 hd).symm
  have hT_eq_of_char_eq (γ δ : Field.absoluteGaloisGroup M)
      (hγδ : continuousCharacterValue (kummerCharacter ζ hζ a) γ =
        continuousCharacterValue (kummerCharacter ζ hζ a) δ) :
      T γ = T δ := by
    let κ : Field.absoluteGaloisGroup M := γ⁻¹ * δ
    have hχinv : continuousCharacterValue (kummerCharacter ζ hζ a) γ⁻¹ =
        -continuousCharacterValue (kummerCharacter ζ hζ a) γ := by
      change (kummerCharacter ζ hζ a) (-Additive.ofMul γ) =
        -(kummerCharacter ζ hζ a) (Additive.ofMul γ)
      exact map_neg (kummerCharacter ζ hζ a) (Additive.ofMul γ)
    have hκzero : continuousCharacterValue (kummerCharacter ζ hζ a) κ = 0 := by
      dsimp [κ]
      rw [hχa_mul, hχinv, hγδ, neg_add_cancel]
    have hκH :
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from κ) ∈
          L.fixingSubgroup := (hfixL_iff κ).2 hκzero
    have hright := hT_right_H γ (⟨κ, hκH⟩ : H)
    have hγκ : γ * κ = δ := by simp [κ]
    rw [hγκ] at hright
    exact hright.symm
  have hzA_fixed (σ : H) :
      σ.1 zA = zA := by
    let σG : Field.absoluteGaloisGroup M := σ.1
    have hxσ : continuousCharacterValue (kummerCharacter ζ hζ a) σG = 0 :=
      (hfixL_iff σG).1 σ.2
    have hsum :
        (continuousCharacterValue (kummerCharacter ζ hζ a) σG).val +
            (continuousCharacterValue (kummerCharacter ζ hζ a) ρ).val < ℓ := by
      rw [hxσ, ZMod.val_zero, zero_add, hρ, ZMod.val_one]
      exact (Fact.out : ℓ.Prime).one_lt
    have hd := hTdiff_of_val_add_lt σG ρ hsum
    rw [hT_eq_one_of_mem_H σ, mul_one] at hd
    have heq := (div_eq_one_iff_eq (hT0 (σG * ρ))).1 hd
    have hchar : continuousCharacterValue (kummerCharacter ζ hζ a) (σG * ρ) =
        continuousCharacterValue (kummerCharacter ζ hζ a) ρ := by
      rw [hχa_mul, hxσ, zero_add]
    have hcoset := hT_eq_of_char_eq (σG * ρ) ρ hchar
    dsimp [zA]
    exact heq.trans hcoset
  let pβ : Polynomial M := Polynomial.X ^ ℓ - Polynomial.C (b : M)
  have hpβsep : pβ.Separable := by
    rw [← Polynomial.separable_map (algebraMap M (AlgebraicClosure M))]
    dsimp [pβ]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      X_pow_sub_C_eq_prod hζA (Fact.out : ℓ.Prime).pos hβpow,
      Polynomial.separable_prod_X_sub_C_iff']
    exact hζA.injOn_pow_mul hβ0
  have hβsep : IsSeparable M β := by
    apply hpβsep.of_dvd
    apply minpoly.dvd M β
    simp [pβ, hβpow]
  let S : IntermediateField M (AlgebraicClosure M) :=
    separableClosure M (AlgebraicClosure M)
  have hUS : U ≤ S :=
    (le_separableClosure_iff M (AlgebraicClosure M) U).2 inferInstance
  have hwS : wA ∈ S := by
    apply hUS
    exact (w : U).2
  have hρwS :
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ) wA ∈ S := by
    let ρA : AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M := ρ
    exact (map_mem_separableClosure_iff ρA.toAlgHom).2 hwS
  have hβS : β ∈ S := (mem_separableClosure_iff).2 hβsep
  have hzS : zA ∈ S := by
    dsimp [zA, T, t, q, m, d, ζA]
    rw [hρ, ZMod.val_one, pow_one]
    exact S.div_mem
      (S.div_mem hβS (S.toSubalgebra.pow_mem (S.algebraMap_mem ζ) (c ρ).val))
      (S.div_mem hρwS hwS)
  letI : IsGalois M S := separableClosure.isGalois M (AlgebraicClosure M)
  have hLS : L ≤ S :=
    (le_separableClosure_iff M (AlgebraicClosure M) L).2 inferInstance
  letI : Algebra L S := (IntermediateField.inclusion hLS).toAlgebra
  letI : IsScalarTower M L S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsGalois L S := IsGalois.tower_top_of_isGalois M L S
  have hLS_apply (x : L) :
      algebraMap L S x = ⟨(x : AlgebraicClosure M), hLS x.2⟩ := rfl
  let zS : S := ⟨zA, hzS⟩
  have hzSfixed (g : S ≃ₐ[L] S) : g zS = zS := by
    let gM : S ≃ₐ[M] S := g.restrictScalars M
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := M) (K₁ := S) (AlgebraicClosure M) gM
    have hσL : σ ∈ L.fixingSubgroup := by
      apply (IntermediateField.mem_fixingSubgroup_iff L σ).2
      intro x hx
      let xL : L := ⟨x, hx⟩
      have happ := DFunLike.congr_fun hσ (algebraMap L S xL)
      have happ' := congrArg Subtype.val happ
      have hgfix := congrArg Subtype.val (g.commutes xL)
      have happ'' : σ x = ((g (algebraMap L S xL) : S) :
          AlgebraicClosure M) := by
        simpa [gM, hLS_apply, AlgEquiv.restrictNormalHom_apply] using happ'
      have hgfix' : ((g (algebraMap L S xL) : S) : AlgebraicClosure M) = x := by
        simpa [hLS_apply] using hgfix
      exact happ''.trans hgfix'
    apply Subtype.ext
    have hres := AlgEquiv.restrictNormalHom_apply S σ zS
    have happ := congrArg Subtype.val (DFunLike.congr_fun hσ zS)
    calc
      ((g zS : S) : AlgebraicClosure M) = (gM zS : S) := rfl
      _ = ((AlgEquiv.restrictNormalHom S σ) zS : S) := happ.symm
      _ = σ zA := hres
      _ = zA := hzA_fixed (⟨σ, hσL⟩ : H)
  have hzSrange : zS ∈ Set.range (algebraMap L S) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed zS).2 hzSfixed
  obtain ⟨zL, hzL⟩ := hzSrange
  have hzLA : (zL : AlgebraicClosure M) = zA := by
    have hzLv := congrArg Subtype.val hzL
    simpa [hLS_apply, zS] using hzLv
  have hrestrict_pow (n : ℕ) :
      AlgEquiv.restrictNormalHom L
          (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ n) = s ^ n := by
    change AlgEquiv.restrictNormalHom L
        ((show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ) ^ n) = s ^ n
    rw [map_pow]
  have hterm (n : ℕ) :
      (((s ^ n) zL : L) : AlgebraicClosure M) =
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ n)
          (zL : AlgebraicClosure M) := by
    rw [← hrestrict_pow n]
    exact AlgEquiv.restrictNormalHom_apply L
      (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ n) zL
  have hcycleL : partialConjugateProduct s zL ℓ =
      algebraMap M L (b : M) := by
    apply Subtype.ext
    change L.val (partialConjugateProduct s zL ℓ) =
      L.val (algebraMap M L (b : M))
    rw [partialConjugateProduct, map_prod]
    calc
      (∏ j ∈ Finset.range ℓ, L.val ((s ^ j) zL)) =
          ∏ j ∈ Finset.range ℓ,
            (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from ρ ^ j)
              (zL : AlgebraicClosure M) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hterm j
      _ = P ℓ := by
        dsimp [P, partialConjugateProduct]
        apply Finset.prod_congr rfl
        intro j hj
        rw [hzLA]
        congr 1
      _ = algebraMap M (AlgebraicClosure M) (b : M) := hPcycle
      _ = L.val (algebraMap M L (b : M)) := rfl
  let autFromFin : Fin ℓ ≃ (L ≃ₐ[M] L) :=
    (ZMod.finEquiv ℓ).toEquiv.trans <|
      Multiplicative.ofAdd.trans (zmodMulEquivOfGenerator hsgen hcard).toEquiv
  have haut (i : Fin ℓ) : autFromFin i = s ^ i.val := by
    change zmodMulEquivOfGenerator hsgen hcard
      (Multiplicative.ofAdd (ZMod.finEquiv ℓ i)) = s ^ i.val
    rw [show ZMod.finEquiv ℓ i = (i.val : ZMod ℓ) by
      cases ℓ with
      | zero => exact Fin.elim0 i
      | succ n =>
        change i = Fin.ofNat (n + 1) i.val
        apply Fin.ext
        exact (Nat.mod_eq_of_lt i.isLt).symm]
    simpa using zmodMulEquivOfGenerator_apply_ofAdd_intCast hsgen hcard (i.val : ℤ)
  have hnormzL : Algebra.norm M zL = (b : M) := by
    apply (algebraMap M L).injective
    rw [Algebra.norm_eq_prod_automorphisms]
    calc
      (∏ τ : L ≃ₐ[M] L, τ zL) =
          ∏ i : Fin ℓ, autFromFin i zL :=
        (autFromFin.prod_comp (fun τ => τ zL)).symm
      _ = ∏ i : Fin ℓ, (s ^ i.val) zL := by
        apply Fintype.prod_congr
        intro i
        rw [haut]
      _ = partialConjugateProduct s zL ℓ := by
        rw [partialConjugateProduct]
        simpa using Fin.prod_univ_eq_prod_range
          (fun i : ℕ => (s ^ i) zL) ℓ
      _ = algebraMap M L (b : M) := hcycleL
  have hzL0 : zL ≠ 0 := by
    intro hz
    apply hT0 ρ
    change zA = 0
    rw [← hzLA, hz]
    rfl
  let zE : E := e.symm zL
  have hzE0 : zE ≠ 0 := by
    intro hz
    apply hzL0
    have := congrArg e hz
    simpa [zE] using this
  have hnormzE : Algebra.norm M zE = (b : M) := by
    calc
      Algebra.norm M zE = Algebra.norm M (e zE) :=
        (Algebra.norm_eq_of_algEquiv e zE).symm
      _ = Algebra.norm M zL := by rw [show e zE = zL by simp [zE]]
      _ = (b : M) := hnormzL
  exact ⟨Units.mk0 zE hzE0, hnormzE⟩

set_option maxHeartbeats 200000

/-- Residual cyclic-cohomology calculation: for a cyclic Kummer extension,
the explicit inhomogeneous cup cocycle is a coboundary exactly when the
second Kummer parameter is a norm. -/
private theorem cyclic_norm_criterion_core
    {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] {ℓ : ℕ} [Fact ℓ.Prime]
    [IsGalois M E] [IsCyclic (E ≃ₐ[M] E)]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (ha : kummerQuotientClass ℓ a ≠ 0)
    (α : E) (hαpow : α ^ ℓ = algebraMap M E (a : M))
    (hαgen : Algebra.adjoin M ({α} : Set E) = ⊤)
    (hdegree : Module.finrank M E = ℓ) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) ↔
      IsUnitNorm M E b := by
  constructor
  · exact cyclic_norm_criterion_to_norm ζ hζ a b ha α hαpow hαgen hdegree
  · exact cyclic_norm_criterion_of_norm ζ hζ a b ha α hαpow hαgen hdegree

/-- Blueprint Lemma 5.1 (`lem:cyclic-norm`): for a nonzero Kummer class,
explicit cup-zero is equivalent to membership in the norm group of the
cyclic Kummer extension. -/
theorem cyclic_norm_criterion {M E : Type*} [Field M] [Field E]
    [Algebra M E] [FiniteDimensional M E] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (a b : Mˣ)
    (ha : kummerQuotientClass ℓ a ≠ 0)
    (hE : IsKummerRadicalExtension M E ℓ a) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) ↔
      IsUnitNorm M E b := by
  obtain ⟨α, hαpow, hαgen, hdegree⟩ := hE
  have hpow : ∀ x : M, x ^ ℓ ≠ (a : M) := by
    intro x hx
    apply ha
    rw [kummerQuotientClass_eq_zero_iff_exists_pow]
    by_cases hx0 : x = 0
    · subst x
      exact (Units.ne_zero a (by
        simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
    · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  let f : Polynomial M := Polynomial.X ^ ℓ - Polynomial.C (a : M)
  have hf : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : ℓ.Prime) hpow
  letI : Fact (Irreducible f) := ⟨hf⟩
  have hprim : (primitiveRoots ℓ M).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (Fact.out : ℓ.Prime).pos).2 hζ⟩
  letI : Polynomial.IsSplittingField M E f := by
    constructor
    · change (Polynomial.X ^ ℓ - Polynomial.C (a : M)).map
          (algebraMap M E) |>.Splits
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot
        (hζ.map_of_injective (algebraMap M E).injective) hαpow
    · apply top_unique
      rw [← hαgen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff]
      change α ∈ f.rootSet E
      rw [Polynomial.mem_rootSet_of_ne (Irreducible.ne_zero hf)]
      simp [f, hαpow]
  letI : IsGalois M E :=
    isGalois_of_isSplittingField_X_pow_sub_C hprim hf E
  letI : IsCyclic (E ≃ₐ[M] E) :=
    isCyclic_of_isSplittingField_X_pow_sub_C hprim hf E
  exact cyclic_norm_criterion_core ζ hζ a b ha α hαpow hαgen hdegree

/-- The zero-class clause of Blueprint Lemma 5.1. -/
theorem cupZero_of_kummerClass_eq_zero {M : Type*} [Field M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (a b : Mˣ) (ha : kummerQuotientClass ℓ a = 0) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) := by
  have hchar : kummerCharacter ζ hζ a = 0 := by
    rw [kummerCharacter, ha, map_zero]
  rw [hchar]
  exact cupZero_zero_left ℓ _

/-- Blueprint Corollary 5.2 (`cor:steinberg`): Kummer classes of `a` and
`1-a` are cup-zero.  The equation on the two units is the division-free
form of `b = 1-a`. -/
theorem steinberg_cupZero {M : Type*} [Field M] {ℓ : ℕ}
    [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (a b : Mˣ) (hab : (a : M) + (b : M) = 1) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) := by
  by_cases ha : kummerQuotientClass ℓ a = 0
  · exact cupZero_of_kummerClass_eq_zero ζ hζ a b ha
  have hpow : ∀ x : M, x ^ ℓ ≠ (a : M) := by
    intro x hx
    apply ha
    rw [kummerQuotientClass_eq_zero_iff_exists_pow]
    by_cases hx0 : x = 0
    · subst x
      exact (Units.ne_zero a (by
        simpa [zero_pow (Fact.out : ℓ.Prime).ne_zero] using hx.symm)).elim
    · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
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
  apply (cyclic_norm_criterion ζ hζ a b ha hE).2
  have hprim : (primitiveRoots ℓ M).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (Fact.out : ℓ.Prime).pos).2 hζ⟩
  letI : Polynomial.IsSplittingField M E f := by
    simpa [E, f] using isSplittingField_AdjoinRoot_X_pow_sub_C hprim hf
  letI : IsGalois M E :=
    isGalois_of_isSplittingField_X_pow_sub_C hprim hf E
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let autFromFin : Fin ℓ ≃ (E ≃ₐ[M] E) :=
    (ZMod.finEquiv ℓ).toEquiv.trans <|
      Multiplicative.ofAdd.trans (autEquivZmod hf E hζ).symm.toEquiv
  have hact (i : Fin ℓ) :
      autFromFin i (AdjoinRoot.root f) =
        algebraMap M E (ζ ^ i.val) * AdjoinRoot.root f := by
    simpa [autFromFin, finEquiv_apply, Algebra.smul_def] using
      autEquivZmod_symm_apply_natCast hf E hroot hζ i.val
  have hprod :
      (∏ i : Fin ℓ,
          (1 - algebraMap M E (ζ ^ i.val) * AdjoinRoot.root f)) =
        algebraMap M E (1 - (a : M)) := by
    rw [show (∏ i : Fin ℓ,
        (1 - algebraMap M E (ζ ^ i.val) * AdjoinRoot.root f)) =
        ∏ i ∈ Finset.range ℓ,
          (1 - algebraMap M E (ζ ^ i) * AdjoinRoot.root f) by
      simpa using Fin.prod_univ_eq_prod_range
        (fun i : ℕ =>
          1 - algebraMap M E (ζ ^ i) * AdjoinRoot.root f) ℓ]
    have hpoly := X_pow_sub_C_eq_prod
      (hζ.map_of_injective (algebraMap M E).injective)
      (Fact.out : ℓ.Prime).pos hroot
    have heval := congrArg (Polynomial.eval (1 : E)) hpoly
    simpa only [map_sub, map_pow, map_one, one_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_prod] using heval.symm
  have hnorm : Algebra.norm M (1 - AdjoinRoot.root f : E) =
      1 - (a : M) := by
    apply (algebraMap M E).injective
    rw [Algebra.norm_eq_prod_automorphisms]
    calc
      (∏ σ : E ≃ₐ[M] E, σ (1 - AdjoinRoot.root f)) =
          ∏ i : Fin ℓ, autFromFin i (1 - AdjoinRoot.root f) :=
        (autFromFin.prod_comp
          (fun σ => σ (1 - AdjoinRoot.root f))).symm
      _ = ∏ i : Fin ℓ,
          (1 - algebraMap M E (ζ ^ i.val) * AdjoinRoot.root f) := by
        apply Fintype.prod_congr
        intro i
        rw [map_sub, map_one, hact]
      _ = algebraMap M E (1 - (a : M)) := hprod
  let zval : E := 1 - AdjoinRoot.root f
  have hzval : zval ≠ 0 := by
    intro hz
    have hone : (AdjoinRoot.root f : E) = 1 := by
      dsimp [zval] at hz
      exact (sub_eq_zero.mp hz).symm
    rw [hone, one_pow] at hroot
    have hamap : algebraMap M E (a : M) = algebraMap M E 1 :=
      hroot.symm.trans (map_one (algebraMap M E)).symm
    have haone : (a : M) = 1 := (algebraMap M E).injective hamap
    apply Units.ne_zero b
    have hab' : (1 : M) + (b : M) = 1 + 0 := by
      simpa [haone] using hab
    exact add_left_cancel hab'
  refine ⟨Units.mk0 zval hzval, ?_⟩
  change Algebra.norm M zval = (b : M)
  rw [show zval = 1 - AdjoinRoot.root f by rfl, hnorm]
  exact (sub_eq_iff_eq_add').2 hab.symm

/-- Changing the primitive root scales all Kummer characters by one common
nonzero scalar, so all zero and determinant conditions are unchanged. -/
theorem kummerCharacter_change_primitiveRoot {M : Type*} [Field M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ ζ' : M)
    (hζ : IsPrimitiveRoot ζ ℓ) (hζ' : IsPrimitiveRoot ζ' ℓ) :
    ∃ c : ZMod ℓ, c ≠ 0 ∧
      ∀ a : Mˣ, kummerCharacter ζ' hζ' a = c • kummerCharacter ζ hζ a := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨i, _, hicoprime, hζ'pow⟩ := (hζ.isPrimitiveRoot_iff).mp hζ'
  let d : ZMod ℓ := i
  have hdunit : IsUnit d := (ZMod.isUnit_iff_coprime i ℓ).2 hicoprime
  have hd0 : d ≠ 0 := hdunit.ne_zero
  refine ⟨d⁻¹, inv_ne_zero hd0, ?_⟩
  intro a
  obtain ⟨β, hβpow, hβeq⟩ := kummerCharacter_definingEquation ζ' hζ' a
  have hscaled : ∃ α : AlgebraicClosure M,
      α ^ ℓ = algebraMap M (AlgebraicClosure M) (a : M) ∧
      ∀ σ : Field.absoluteGaloisGroup M,
        (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from σ) α =
          (algebraMap M (AlgebraicClosure M) ζ) ^
              (continuousCharacterValue
                (d • kummerCharacter ζ' hζ' a) σ).val * α := by
    refine ⟨β, hβpow, ?_⟩
    intro σ
    rw [hβeq σ]
    congr 1
    let A := AlgebraicClosure M
    let ζA : A := algebraMap M A ζ
    let v : ZMod ℓ :=
      continuousCharacterValue (kummerCharacter ζ' hζ' a) σ
    have hvalue :
        continuousCharacterValue (d • kummerCharacter ζ' hζ' a) σ =
          d * v := continuousCharacter_smul_value ℓ d _ σ
    have hzmod : (((d * v).val : ℕ) : ZMod ℓ) =
        ((i * v.val : ℕ) : ZMod ℓ) := by
      rw [ZMod.natCast_zmod_val]
      simp [d, v, Nat.cast_mul]
    have hmod : (d * v).val ≡ i * v.val [MOD ℓ] :=
      (ZMod.natCast_eq_natCast_iff _ _ ℓ).mp hzmod
    have hpowers : ζA ^ (d * v).val = ζA ^ (i * v.val) :=
      pow_eq_pow_of_modEq hmod
        (hζ.map_of_injective (algebraMap M A).injective).pow_eq_one
    rw [hvalue]
    have hmapζ : algebraMap M A ζ' = ζA ^ i := by
      simpa [ζA] using (congrArg (algebraMap M A) hζ'pow).symm
    calc
      (algebraMap M A ζ') ^ v.val = (ζA ^ i) ^ v.val := by rw [hmapζ]
      _ = ζA ^ (i * v.val) := (pow_mul ζA i v.val).symm
      _ = ζA ^ (d * v).val := hpowers.symm
      _ = (algebraMap M (AlgebraicClosure M) ζ) ^ (d * v).val := by rfl
  have hscale : d • kummerCharacter ζ' hζ' a =
      kummerCharacter ζ hζ a :=
    kummerCharacter_eq_of_definingEquation ζ hζ a _ hscaled
  calc
    kummerCharacter ζ' hζ' a =
        (d⁻¹ * d) • kummerCharacter ζ' hζ' a := by
      rw [inv_mul_cancel₀ hd0, one_smul]
    _ = d⁻¹ • (d • kummerCharacter ζ' hζ' a) := by rw [mul_smul]
    _ = d⁻¹ • kummerCharacter ζ hζ a := by rw [hscale]

/-- Cup-zero on Kummer characters is independent of the primitive root. -/
theorem cupZero_kummer_primitiveRoot_iff {M : Type*} [Field M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ ζ' : M)
    (hζ : IsPrimitiveRoot ζ ℓ) (hζ' : IsPrimitiveRoot ζ' ℓ)
    (a b : Mˣ) :
    CupZero ℓ (kummerCharacter ζ hζ a) (kummerCharacter ζ hζ b) ↔
      CupZero ℓ (kummerCharacter ζ' hζ' a) (kummerCharacter ζ' hζ' b) := by
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ :=
      kummerCharacter_change_primitiveRoot ζ ζ' hζ hζ'
    rw [hc a, hc b]
    exact h.smul c c
  · intro h
    obtain ⟨c, _, hc⟩ :=
      kummerCharacter_change_primitiveRoot ζ' ζ hζ' hζ
    rw [hc a, hc b]
    exact h.smul c c

end

end NU.LocalTheory
