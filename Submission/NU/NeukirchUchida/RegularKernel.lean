import Submission.NU.NeukirchUchida.ChebotarevContainment
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The regular-kernel auxiliary extension

Blueprint §4.  The file records the cyclotomic Kummer projector, the
cyclotomic-eigenspace descent lemma, the asymmetric cyclic extension, and
`prop:regular-kernel`.  Finite normal fields remain literal intermediate
fields of the one ambient `Omega`; the regular representation is
`MonoidAlgebra (ZMod p) G`, as required by blueprint §9.1(4).
-/

open scoped NumberField Pointwise BigOperators
open IsDedekindDomain
open WithZero Valuation.IsRankOneDiscrete

namespace NU.NeukirchUchida

noncomputable section

/-! ## Cyclotomic and Kummer primitives in the common closure -/

/-- A chosen primitive `p`-th root of unity in `Omega`. -/
noncomputable def primitiveRootInOmega (p : NU.LocalTheory.OddPrime) : Omega :=
  Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot Omega (p : ℕ))

/-- The chosen root is genuinely primitive; this defining theorem prevents a
choice of `1` when `p > 1`. -/
theorem primitiveRootInOmega_spec (p : NU.LocalTheory.OddPrime) :
    IsPrimitiveRoot (primitiveRootInOmega p) (p : ℕ) :=
  Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot Omega (p : ℕ))

/-- The cyclotomic field `ℚ(mu_p)` inside the fixed `Omega`. -/
def cyclotomicFieldInOmega (p : NU.LocalTheory.OddPrime) :
    IntermediateField ℚ Omega :=
  IntermediateField.adjoin ℚ {primitiveRootInOmega p}

/-- The literal compositum `N(mu_p)` in `Omega`. -/
noncomputable def cyclotomicCompositum
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    NumberFieldInOmega where
  field := N.field ⊔ cyclotomicFieldInOmega p
  finite := by
    letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
    letI : Algebra.IsIntegral ℚ Omega := Algebra.IsAlgebraic.isIntegral
    let A := IntermediateField.adjoin ℚ
      ({primitiveRootInOmega p} : Set Omega)
    letI : FiniteDimensional ℚ A :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (primitiveRootInOmega p))
    exact IntermediateField.finiteDimensional_sup N.field A

/-- The inclusion `N ≤ N(mu_p)`. -/
theorem le_cyclotomicCompositum
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    N.field ≤ (cyclotomicCompositum N p).field :=
  le_sup_left

/-- The chosen primitive root as an element of `N(mu_p)`. -/
def cyclotomicRoot
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    (cyclotomicCompositum N p).field :=
  ⟨primitiveRootInOmega p,
    (show cyclotomicFieldInOmega p ≤
        N.field ⊔ cyclotomicFieldInOmega p from le_sup_right)
      ((IntermediateField.subset_adjoin ℚ
        {primitiveRootInOmega p})
          (Set.mem_singleton (primitiveRootInOmega p)))⟩

/-- `Delta = Gal(N(mu_p)/N)` in the literal ambient model. -/
abbrev CyclotomicDelta
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :=
  relativeGaloisGroup N (cyclotomicCompositum N p)
    (le_cyclotomicCompositum N p)

/-- The mod-`p` cyclotomic character on `Delta`. -/
noncomputable def cyclotomicCharacter
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    CyclotomicDelta N p →* (ZMod (p : ℕ))ˣ := by
  let E := cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion
      (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
  have hroot : IsPrimitiveRoot (cyclotomicRoot N p) (p : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := E.field.val)
    · exact primitiveRootInOmega_spec p
    · exact E.field.val.injective
  let toAut : CyclotomicDelta N p →* (E.field ≃ₐ[N.field] E.field) :=
    { toFun := fun delta =>
        { delta.1 with
          commutes' := fun x => delta.2 x }
      map_one' := by
        apply AlgEquiv.ext
        intro x
        rfl
      map_mul' := by
        intro delta epsilon
        apply AlgEquiv.ext
        intro x
        rfl }
  exact (hroot.autToPow N.field).comp toAut

/-- Defining root-action equation for the cyclotomic character. -/
theorem cyclotomicCharacter_spec
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (delta : CyclotomicDelta N p) :
    delta.1 (cyclotomicRoot N p) =
      cyclotomicRoot N p ^ ((cyclotomicCharacter N p delta :
        ZMod (p : ℕ)).val) := by
  let E := cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion
      (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
  have hroot : IsPrimitiveRoot (cyclotomicRoot N p) (p : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := E.field.val)
    · exact primitiveRootInOmega_spec p
    · exact E.field.val.injective
  let toAut : CyclotomicDelta N p →* (E.field ≃ₐ[N.field] E.field) :=
    { toFun := fun delta =>
        { delta.1 with commutes' := fun x => delta.2 x }
      map_one' := by ext; rfl
      map_mul' := by intro d e; ext; rfl }
  have h := hroot.autToPow_spec N.field (toAut delta)
  rw [show cyclotomicCharacter N p delta =
    hroot.autToPow N.field (toAut delta) from rfl]
  exact h.symm

/-- The subgroup of `p`-th powers in a field's unit group. -/
def pthPowerSubgroup (F : NumberFieldInOmega) (p : ℕ) :
    Subgroup F.fieldˣ where
  carrier := {x | ∃ y : F.fieldˣ, y ^ p = x}
  one_mem' := ⟨1, one_pow p⟩
  mul_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, mul_pow a b p⟩
  inv_mem' := by
    rintro x ⟨a, rfl⟩
    exact ⟨a⁻¹, inv_pow a p⟩

instance pthPowerSubgroup_normal (F : NumberFieldInOmega) (p : ℕ) :
    (pthPowerSubgroup F p).Normal := by
  infer_instance

/-- The Kummer group `Fˣ/Fˣᵖ`, written multiplicatively. -/
abbrev KummerClass (F : NumberFieldInOmega) (p : ℕ) :=
  F.fieldˣ ⧸ pthPowerSubgroup F p

/-- The induced action of `Delta` on Kummer classes. -/
noncomputable def kummerAction
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    CyclotomicDelta N p →*
      (KummerClass (cyclotomicCompositum N p) (p : ℕ) ≃*
        KummerClass (cyclotomicCompositum N p) (p : ℕ)) := by
  let E := cyclotomicCompositum N p
  let unitEquiv (delta : CyclotomicDelta N p) : E.fieldˣ ≃* E.fieldˣ :=
    Units.mapEquiv delta.1.toRingEquiv.toMulEquiv
  have hmap (delta : CyclotomicDelta N p) :
      Subgroup.map (unitEquiv delta) (pthPowerSubgroup E (p : ℕ)) =
        pthPowerSubgroup E (p : ℕ) := by
    apply le_antisymm
    · rintro x ⟨y, ⟨z, hz⟩, rfl⟩
      refine ⟨unitEquiv delta z, ?_⟩
      change (unitEquiv delta z) ^ (p : ℕ) = unitEquiv delta y
      rw [← map_pow, hz]
    · intro x hx
      rcases hx with ⟨z, hz⟩
      let y := (unitEquiv delta).symm z ^ (p : ℕ)
      refine ⟨y, ⟨(unitEquiv delta).symm z, rfl⟩, ?_⟩
      dsimp [y]
      rw [map_pow, (unitEquiv delta).apply_symm_apply, hz]
  let action (delta : CyclotomicDelta N p) :
      KummerClass E (p : ℕ) ≃* KummerClass E (p : ℕ) :=
    QuotientGroup.congr (pthPowerSubgroup E (p : ℕ))
      (pthPowerSubgroup E (p : ℕ)) (unitEquiv delta) (hmap delta)
  exact
    { toFun := action
      map_one' := by
        apply MulEquiv.ext
        intro c
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
        rfl
      map_mul' := by
        intro delta epsilon
        apply MulEquiv.ext
        intro c
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
        rfl }

/-- Defining equation for the Kummer action on represented unit classes. -/
@[simp]
theorem kummerAction_mk
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (delta : CyclotomicDelta N p)
    (a : (cyclotomicCompositum N p).fieldˣ) :
    kummerAction N p delta (QuotientGroup.mk a) =
      QuotientGroup.mk
        (Units.map delta.1.toRingEquiv.toMonoidHom a) := by
  rfl

/-- The guarded Kummer averaging idempotent
`e_chi = |Delta|⁻¹ sum_delta chi(delta)⁻¹ [delta]`, blueprint
`eq:chi-idempotent`.

The proof `hcard` is a binding part of the interface: it makes `|Delta|` a
unit in `ZMod p`, so the definition cannot be instantiated at `Delta = C_p`
and silently collapse to zero. -/
noncomputable def kummerProjector
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) :
    MonoidAlgebra (ZMod (p : ℕ)) Delta := by
  letI := Fintype.ofFinite Delta
  exact ∑ delta : Delta,
    MonoidAlgebra.single delta
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
          ZMod (p : ℕ)) * ((chi delta)⁻¹ : ZMod (p : ℕ)))

/-- Defining coefficient equation for the guarded Kummer projector. -/
@[simp]
theorem kummerProjector_apply
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) (delta : Delta) :
    (kummerProjector p hcard chi).coeff delta =
      (Nat.card Delta : ZMod (p : ℕ))⁻¹ *
        ((chi delta)⁻¹ : ZMod (p : ℕ)) := by
  classical
  letI := Fintype.ofFinite Delta
  unfold kummerProjector
  rw [MonoidAlgebra.coeff_sum]
  change Finsupp.applyAddHom delta (∑ d : Delta,
    (MonoidAlgebra.single d
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi d)⁻¹ : ZMod (p : ℕ)))).coeff) = _
  rw [map_sum, Finset.sum_eq_single delta]
  · change (Finsupp.single delta
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi delta)⁻¹ : ZMod (p : ℕ)))) delta = _
    rw [Finsupp.single_eq_same]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  · intro d hd hne
    change (Finsupp.single d
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi d)⁻¹ : ZMod (p : ℕ)))) delta = 0
    rw [Finsupp.single_eq_of_ne hne.symm]
  · intro h
    exact (h (Finset.mem_univ delta)).elim

/-- Every coefficient of the guarded average is nonzero. -/
theorem kummerProjector_coeff_ne_zero
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) (delta : Delta) :
    (kummerProjector p hcard chi).coeff delta ≠ 0 := by
  rw [kummerProjector_apply]
  exact mul_ne_zero (inv_ne_zero hcard)
    (inv_ne_zero (Units.ne_zero (chi delta)))

/-- In particular, the guarded Kummer projector cannot collapse to zero. -/
theorem kummerProjector_ne_zero
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) :
    kummerProjector p hcard chi ≠ 0 := by
  intro h
  have hc := congrArg
    (fun x : MonoidAlgebra (ZMod (p : ℕ)) Delta => x.coeff 1) h
  rw [kummerProjector_apply] at hc
  simp at hc
  exact hcard hc

/-- The guarded Kummer average is the idempotent `e_chi`. -/
theorem kummerProjector_idempotent
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) :
    IsIdempotentElem (kummerProjector p hcard chi) := by
  classical
  letI := Fintype.ofFinite Delta
  let R := ZMod (p : ℕ)
  let P := kummerProjector p hcard chi
  let a : Delta → R := fun d =>
    (Nat.card Delta : R)⁻¹ * ((chi d)⁻¹ : R)
  have hP : P = ∑ d : Delta, MonoidAlgebra.single d (a d) := by
    rfl
  have hsingle (d : Delta) :
      MonoidAlgebra.single d (a d) =
        a d • MonoidAlgebra.single d (1 : R) := by
    ext x
    simp [MonoidAlgebra.coeff, Finsupp.single_apply, smul_eq_mul]
  have htranslate (d : Delta) :
      MonoidAlgebra.single d (1 : R) * P = (chi d : R) • P := by
    dsimp [P, R]
    classical
    ext x
    rw [MonoidAlgebra.single_mul_apply, one_mul]
    change (kummerProjector p hcard chi).coeff (d⁻¹ * x) =
      (chi d : R) * (kummerProjector p hcard chi).coeff x
    rw [kummerProjector_apply, kummerProjector_apply]
    change (Nat.card Delta : ZMod (p : ℕ))⁻¹ *
        (↑(chi (d⁻¹ * x)) : ZMod (p : ℕ))⁻¹ =
      (chi d : ZMod (p : ℕ)) *
        ((Nat.card Delta : ZMod (p : ℕ))⁻¹ *
          (↑(chi x) : ZMod (p : ℕ))⁻¹)
    rw [map_mul, map_inv]
    push_cast
    field_simp
  change P * P = P
  rw [hP]
  rw [Finset.sum_mul]
  calc
    (∑ d : Delta, MonoidAlgebra.single d (a d) * P) =
        ∑ d : Delta, a d • (MonoidAlgebra.single d (1 : R) * P) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hsingle, smul_mul_assoc]
    _ = ∑ d : Delta, a d • ((chi d : R) • P) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [htranslate]
    _ = (∑ d : Delta, a d * (chi d : R)) • P := by
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro d hd
          rw [smul_smul]
    _ = P := by
          have hterm (d : Delta) : a d * (chi d : R) =
              (Nat.card Delta : R)⁻¹ := by
            dsimp [a, R]
            field_simp
          simp_rw [hterm]
          rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_eq_nat_card, nsmul_eq_mul]
          have hc : (Nat.card Delta : R) * (Nat.card Delta : R)⁻¹ = 1 :=
            mul_inv_cancel₀ hcard
          rw [hc, one_smul]

/-- Left translation gives the defining `chi`-eigen equation. -/
theorem kummerProjector_leftTranslate
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) (gamma : Delta) :
    MonoidAlgebra.single gamma 1 * kummerProjector p hcard chi =
      (chi gamma : ZMod (p : ℕ)) • kummerProjector p hcard chi := by
  classical
  letI := Fintype.ofFinite Delta
  ext delta
  rw [MonoidAlgebra.single_mul_apply, one_mul]
  change (kummerProjector p hcard chi).coeff (gamma⁻¹ * delta) =
    (chi gamma : ZMod (p : ℕ)) *
      (kummerProjector p hcard chi).coeff delta
  rw [kummerProjector_apply, kummerProjector_apply]
  change (Nat.card Delta : ZMod (p : ℕ))⁻¹ *
      (↑(chi (gamma⁻¹ * delta)) : ZMod (p : ℕ))⁻¹ =
    (chi gamma : ZMod (p : ℕ)) *
      ((Nat.card Delta : ZMod (p : ℕ))⁻¹ *
        (↑(chi delta) : ZMod (p : ℕ))⁻¹)
  rw [map_mul, map_inv]
  push_cast
  field_simp

/-- The actual cyclotomic group has order dividing `p - 1`.  This is the
arithmetic guard behind the averaging denominator. -/
theorem cyclotomicDelta_card_dvd_p_sub_one
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    Nat.card (CyclotomicDelta N p) ∣ (p : ℕ) - 1 := by
  let E := cyclotomicCompositum N p
  have hNE : N.field ≤ E.field := le_cyclotomicCompositum N p
  letI : Algebra ℚ E.field := E.field.algebra'
  let N' : IntermediateField ℚ E.field := IntermediateField.restrict hNE
  let C : IntermediateField ℚ E.field :=
    IntermediateField.adjoin ℚ ({cyclotomicRoot N p} : Set E.field)
  have htop : N' ⊔ C = ⊤ := by
    apply IntermediateField.lift_injective E.field
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have himage : Subtype.val '' ({cyclotomicRoot N p} : Set E.field) =
        ({primitiveRootInOmega p} : Set Omega) := by
      ext x
      simp [cyclotomicRoot]
    rw [himage]
    rfl
  have hinj : Function.Injective (cyclotomicCharacter N p) := by
    intro delta epsilon hchar
    have hroot : delta.1 (cyclotomicRoot N p) =
        epsilon.1 (cyclotomicRoot N p) := by
      rw [cyclotomicCharacter_spec, cyclotomicCharacter_spec, hchar]
    let deltaQ : E.field ≃ₐ[ℚ] E.field :=
      { delta.1.toRingEquiv with
        commutes' := fun q => map_ratCast delta.1.toRingEquiv q }
    let epsilonQ : E.field ≃ₐ[ℚ] E.field :=
      { epsilon.1.toRingEquiv with
        commutes' := fun q => map_ratCast epsilon.1.toRingEquiv q }
    let g : E.field ≃ₐ[ℚ] E.field := deltaQ⁻¹ * epsilonQ
    have hgroot : g (cyclotomicRoot N p) = cyclotomicRoot N p := by
      dsimp [g, deltaQ, epsilonQ]
      rw [← hroot, AlgEquiv.symm_apply_apply]
    let H : IntermediateField ℚ E.field :=
      IntermediateField.fixedField (Subgroup.zpowers g)
    have hNle : N' ≤ H := by
      intro y hy
      rw [IntermediateField.mem_fixedField_iff]
      intro tau htau
      let yN : N' := ⟨y, hy⟩
      have hgy : g y = y := by
        dsimp [g, deltaQ, epsilonQ]
        have hd : delta.1 y = y := by
          let x : N.field :=
            ⟨y.1, (IntermediateField.mem_restrict hNE y).mp hy⟩
          exact delta.2 x
        have he : epsilon.1 y = y := by
          let x : N.field :=
            ⟨y.1, (IntermediateField.mem_restrict hNE y).mp hy⟩
          exact epsilon.2 x
        rw [he, ← hd, AlgEquiv.symm_apply_apply]
        exact hd.symm
      have hz : Subgroup.zpowers g ≤
          MulAction.stabilizer (E.field ≃ₐ[ℚ] E.field) y :=
        Subgroup.zpowers_le.mpr hgy
      exact hz htau
    have hCle : C ≤ H := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change cyclotomicRoot N p ∈
        IntermediateField.fixedField (Subgroup.zpowers g)
      rw [IntermediateField.mem_fixedField_iff]
      intro tau htau
      have hz : Subgroup.zpowers g ≤
          MulAction.stabilizer (E.field ≃ₐ[ℚ] E.field) (cyclotomicRoot N p) :=
        Subgroup.zpowers_le.mpr hgroot
      exact hz htau
    have htopH : (⊤ : IntermediateField ℚ E.field) ≤ H := by
      rw [← htop]
      exact sup_le hNle hCle
    have hg : g = 1 := by
      apply AlgEquiv.ext
      intro x
      have hx : x ∈ H := htopH trivial
      change x ∈ IntermediateField.fixedField (Subgroup.zpowers g) at hx
      exact (IntermediateField.mem_fixedField_iff
        (H := Subgroup.zpowers g) x).mp hx g (Subgroup.mem_zpowers g)
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun hg x
    dsimp [g] at hx
    have hx' := congrArg deltaQ hx
    change deltaQ x = epsilonQ x
    simpa using hx'.symm
  have hdvd := Subgroup.card_dvd_of_injective
    (cyclotomicCharacter N p) hinj
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.1.2⟩
  calc
    Nat.card (CyclotomicDelta N p) ∣ Nat.card (ZMod (p : ℕ))ˣ := hdvd
    _ = Fintype.card (ZMod (p : ℕ))ˣ := Nat.card_eq_fintype_card
    _ = (p : ℕ) - 1 := ZMod.card_units (p : ℕ)

/-- Exported invertibility guard for the actual cyclotomic `Delta`.
It rules out the `Delta = C_p` collapse at the declaration used below. -/
theorem cyclotomicDelta_card_ne_zero_mod_p
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    (Nat.card (CyclotomicDelta N p) : ZMod (p : ℕ)) ≠ 0 := by
  intro hzero
  have hp_dvd_card : (p : ℕ) ∣ Nat.card (CyclotomicDelta N p) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hp_dvd_sub : (p : ℕ) ∣ (p : ℕ) - 1 :=
    hp_dvd_card.trans (cyclotomicDelta_card_dvd_p_sub_one N p)
  have hle : (p : ℕ) ≤ (p : ℕ) - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt p.1.2.one_lt) hp_dvd_sub
  exact (Nat.not_le_of_lt (Nat.sub_lt p.1.2.pos Nat.zero_lt_one)) hle

/-- The blueprint's actual cyclotomic Kummer idempotent, specialized with the
proved `p ∤ |CyclotomicDelta|` guard. -/
noncomputable def cyclotomicKummerProjector
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    MonoidAlgebra (ZMod (p : ℕ)) (CyclotomicDelta N p) :=
  kummerProjector p (cyclotomicDelta_card_ne_zero_mod_p N p)
    (cyclotomicCharacter N p)

/-- Defining coefficient equation for the actual cyclotomic projector. -/
@[simp]
theorem cyclotomicKummerProjector_apply
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (delta : CyclotomicDelta N p) :
    (cyclotomicKummerProjector N p).coeff delta =
      (Nat.card (CyclotomicDelta N p) : ZMod (p : ℕ))⁻¹ *
        ((cyclotomicCharacter N p delta)⁻¹ : ZMod (p : ℕ)) := by
  exact kummerProjector_apply p
    (cyclotomicDelta_card_ne_zero_mod_p N p)
    (cyclotomicCharacter N p) delta

/-- The specialized cyclotomic projector is an idempotent. -/
theorem cyclotomicKummerProjector_idempotent
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    IsIdempotentElem (cyclotomicKummerProjector N p) := by
  exact kummerProjector_idempotent p
    (cyclotomicDelta_card_ne_zero_mod_p N p)
    (cyclotomicCharacter N p)

/-- The specialized cyclotomic projector is nonzero. -/
theorem cyclotomicKummerProjector_ne_zero
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    cyclotomicKummerProjector N p ≠ 0 := by
  exact kummerProjector_ne_zero p
    (cyclotomicDelta_card_ne_zero_mod_p N p)
    (cyclotomicCharacter N p)

/-- Applying `e_chi` to a Kummer class, in multiplicative notation. -/
noncomputable def projectedKummerClass
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ)) :
    KummerClass (cyclotomicCompositum N p) (p : ℕ) := by
  letI := Fintype.ofFinite (CyclotomicDelta N p)
  exact ∏ delta : CyclotomicDelta N p,
    (kummerAction N p delta c) ^
      ((cyclotomicKummerProjector N p).coeff delta).val

/-- Defining product equation for the projected Kummer class. -/
theorem projectedKummerClass_apply
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ)) :
    projectedKummerClass N p c =
      letI := Fintype.ofFinite (CyclotomicDelta N p)
      ∏ delta : CyclotomicDelta N p,
        (kummerAction N p delta c) ^
          ((cyclotomicKummerProjector N p).coeff delta).val := by
  rfl

/-- The image of the projector lies in the cyclotomic-character eigenspace. -/
theorem projectedKummerClass_eigen
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ))
    (delta : CyclotomicDelta N p) :
    kummerAction N p delta (projectedKummerClass N p c) =
      projectedKummerClass N p c ^
        ((cyclotomicCharacter N p delta : ZMod (p : ℕ)).val) := by
  classical
  letI := Fintype.ofFinite (CyclotomicDelta N p)
  let E := cyclotomicCompositum N p
  let D := CyclotomicDelta N p
  let P := cyclotomicKummerProjector N p
  let r := (cyclotomicCharacter N p delta : ZMod (p : ℕ)).val
  have hexponent (x : KummerClass E (p : ℕ)) : x ^ (p : ℕ) = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    change QuotientGroup.mk (a ^ (p : ℕ)) = 1
    apply (QuotientGroup.eq_one_iff (a ^ (p : ℕ))).mpr
    exact ⟨a, rfl⟩
  have hcoeff (eta : D) :
      P.coeff (delta⁻¹ * eta) =
        (cyclotomicCharacter N p delta : ZMod (p : ℕ)) * P.coeff eta := by
    have h := congrArg (fun z : MonoidAlgebra (ZMod (p : ℕ)) D => z.coeff eta)
      (kummerProjector_leftTranslate p
        (cyclotomicDelta_card_ne_zero_mod_p N p)
        (cyclotomicCharacter N p) delta)
    have hmul : (MonoidAlgebra.single delta 1 * P).coeff eta =
        P.coeff (delta⁻¹ * eta) := by
      simpa only [MonoidAlgebra.coeff, one_mul] using
        (MonoidAlgebra.single_mul_apply P (1 : ZMod (p : ℕ)) delta eta)
    have hsmul :
        ((cyclotomicCharacter N p delta : ZMod (p : ℕ)) • P).coeff eta =
          (cyclotomicCharacter N p delta : ZMod (p : ℕ)) * P.coeff eta := by
      have hs := congrArg (fun z : D →₀ ZMod (p : ℕ) => z eta)
        (MonoidAlgebra.coeff_smul
          (cyclotomicCharacter N p delta : ZMod (p : ℕ)) P)
      simpa only [Finsupp.smul_apply, smul_eq_mul] using hs
    have h' : (MonoidAlgebra.single delta 1 * P).coeff eta =
        ((cyclotomicCharacter N p delta : ZMod (p : ℕ)) • P).coeff eta := by
      change (MonoidAlgebra.single delta 1 * P).coeff eta =
        ((cyclotomicCharacter N p delta : ZMod (p : ℕ)) • P).coeff eta at h
      exact h
    exact hmul.symm.trans (h'.trans hsmul)
  have hpow (eta : D) :
      (kummerAction N p eta c) ^ (P.coeff (delta⁻¹ * eta)).val =
        (kummerAction N p eta c) ^ ((P.coeff eta).val * r) := by
    apply (pow_eq_pow_iff_modEq).mpr
    apply Nat.ModEq.of_dvd
      ((orderOf_dvd_iff_pow_eq_one).mpr (hexponent (kummerAction N p eta c)))
    apply (ZMod.natCast_eq_natCast_iff _ _ (p : ℕ)).mp
    rw [ZMod.natCast_val, Nat.cast_mul, ZMod.natCast_val,
      ZMod.natCast_val]
    simp only [ZMod.cast_id', id]
    exact (hcoeff eta).trans (mul_comm _ _)
  rw [projectedKummerClass_apply]
  rw [map_prod]
  simp_rw [map_pow]
  have haction (gamma : D) :
      kummerAction N p delta (kummerAction N p gamma c) =
        kummerAction N p (delta * gamma) c := by
    have h := DFunLike.congr_fun (map_mul (kummerAction N p) delta gamma) c
    exact h.symm
  simp_rw [haction]
  let shift : D ≃ D := Equiv.mulLeft delta
  calc
    (∏ gamma : D,
        kummerAction N p (delta * gamma) c ^ (P.coeff gamma).val) =
      ∏ eta : D,
        kummerAction N p eta c ^ (P.coeff (delta⁻¹ * eta)).val := by
          let g : D → KummerClass E (p : ℕ) := fun eta =>
            kummerAction N p eta c ^ (P.coeff (delta⁻¹ * eta)).val
          simpa [shift, g, mul_assoc] using shift.prod_comp g
    _ = ∏ eta : D,
        (kummerAction N p eta c ^ (P.coeff eta).val) ^ r := by
          apply Finset.prod_congr rfl
          intro eta heta
          exact (hpow eta).trans (pow_mul _ _ _)
    _ = (∏ eta : D,
        kummerAction N p eta c ^ (P.coeff eta).val) ^ r := by
          exact Finset.prod_pow Finset.univ r _

/-- A chosen `p`-th radical of a nonzero element in the algebraically closed
ambient field. -/
noncomputable def radicalRoot
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) : Omega :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (a.1 : Omega) p.1.2.pos)

/-- Defining radical equation. -/
theorem radicalRoot_spec
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) :
    radicalRoot E p a ^ (p : ℕ) = (a.1 : Omega) :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (a.1 : Omega) p.1.2.pos)

/-- `E(sqrt[p]{a})` inside the common ambient closure. -/
def radicalExtension
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) : IntermediateField ℚ Omega :=
  E.field ⊔ IntermediateField.adjoin ℚ {radicalRoot E p a}

/-! ## The asymmetric cyclic extension -/

/-- Relative ramification index of `w/v` in an ambient extension. -/
noncomputable def relativeRamificationIndex
    {N : NumberFieldInOmega} (L : NumberFieldExtension N)
    (v : NU.LocalTheory.FinitePlace N.field)
    (w : NU.LocalTheory.FinitePlace L.field.field) : ℕ :=
  w.asIdeal.ramificationIdx' (NumberField.RingOfIntegers N.field)

/-- Relative residue degree of `w/v`. -/
noncomputable def relativeResidueDegree
    {N : NumberFieldInOmega} (L : NumberFieldExtension N)
    (v : NU.LocalTheory.FinitePlace N.field)
    (w : NU.LocalTheory.FinitePlace L.field.field) : ℕ :=
  w.asIdeal.inertiaDeg' (NumberField.RingOfIntegers N.field)

/-- An extension is ramified at a specified base prime. -/
def IsRamifiedAt
    {N : NumberFieldInOmega} (L : NumberFieldExtension N)
    (v : NU.LocalTheory.FinitePlace N.field) : Prop :=
  ∃ w : NU.LocalTheory.FinitePlace L.field.field,
    NU.LocalTheory.restrictFinitePlace N.field w = v ∧
      1 < relativeRamificationIndex L v w

/-- A base prime splits completely in an extension. -/
def SplitsCompletelyAbove
    {N : NumberFieldInOmega} (L : NumberFieldExtension N)
    (v : NU.LocalTheory.FinitePlace N.field) : Prop :=
  (∃ w : NU.LocalTheory.FinitePlace L.field.field,
    NU.LocalTheory.restrictFinitePlace N.field w = v) ∧
  ∀ w : NU.LocalTheory.FinitePlace L.field.field,
    NU.LocalTheory.restrictFinitePlace N.field w = v →
      relativeRamificationIndex L v w = 1 ∧
        relativeResidueDegree L v w = 1

/-! ## Conjugates and the regular module -/

/-- A finite Galois overfield of `N` inside `Omega`.  Its Galois property
over `ℚ` is a field, not an unpinned instance choice. -/
structure GaloisOverfield (N : NumberFieldInOmega) where
  /-- The underlying extension of `N`. -/
  toExtension : NumberFieldExtension N
  /-- The upper field is Galois over `ℚ`. -/
  isGaloisQ : IsGalois ℚ toExtension.field.field

attribute [instance] GaloisOverfield.isGaloisQ

/-- A common normal field is its own trivial finite Galois overfield. -/
noncomputable def trivialGaloisOverfield
    (N : NumberFieldInOmega) [IsGalois ℚ N.field] : GaloisOverfield N where
  toExtension := trivialNumberFieldExtension N
  isGaloisQ := by
    change IsGalois ℚ N.field
    infer_instance

/-- Inhabitation sanity check for `GaloisOverfield`. -/
instance galoisOverfieldNonempty
    (N : NumberFieldInOmega) [IsGalois ℚ N.field] :
    Nonempty (GaloisOverfield N) :=
  ⟨trivialGaloisOverfield N⟩

/-- The kernel `Gal(M/N)`. -/
abbrev RegularKernelGroup
    (N : NumberFieldInOmega) (M : GaloisOverfield N) :=
  M.toExtension.field.field ≃ₐ[N.field] M.toExtension.field.field

/-- The commutative group structure certified by a commutativity equation.
Its operations are the existing kernel operations, so this introduces no
alternative group law. -/
@[reducible]
def regularKernelCommGroup
    (N : NumberFieldInOmega) (M : GaloisOverfield N)
    (hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a) :
    CommGroup (RegularKernelGroup N M) :=
  { (inferInstance : Group (RegularKernelGroup N M)) with
    mul_comm := hcomm }

/-- Conjugation of the kernel by `Gal(N/ℚ)`.  The commutativity hypothesis is
what makes conjugation independent of a chosen lift. -/
noncomputable def regularKernelConjugation
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (M : GaloisOverfield N)
    (hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a) :
    (N.field ≃ₐ[ℚ] N.field) →*
      (RegularKernelGroup N M ≃* RegularKernelGroup N M) := by
  let E := M.toExtension.field.field
  let A := RegularKernelGroup N M
  let G := E ≃ₐ[ℚ] E
  let Q := N.field ≃ₐ[ℚ] N.field
  let r : G →* Q := AlgEquiv.restrictNormalHom N.field
  let e : A ≃* r.ker := by
    let toFun : A → r.ker := fun a =>
      ⟨a.restrictScalars ℚ, by
        change r (a.restrictScalars ℚ) = 1
        apply AlgEquiv.ext
        intro x
        apply (algebraMap N.field E).injective
        calc
          algebraMap N.field E (r (a.restrictScalars ℚ) x) =
              (a.restrictScalars ℚ) (algebraMap N.field E x) :=
            AlgEquiv.restrictNormal_commutes (a.restrictScalars ℚ) N.field x
          _ = algebraMap N.field E x := a.commutes x
          _ = algebraMap N.field E x := by rfl⟩
    let invFun : r.ker → A := fun a =>
      { a.1.toRingEquiv with
        commutes' := fun x => by
          have hx := DFunLike.congr_fun a.2 x
          have hx0 : r a.1 x = x := hx.trans rfl
          calc
            a.1 (algebraMap N.field E x) =
                algebraMap N.field E (r a.1 x) :=
              (AlgEquiv.restrictNormal_commutes a.1 N.field x).symm
            _ = algebraMap N.field E x := congrArg (algebraMap N.field E) hx0 }
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by intro a; apply AlgEquiv.ext; intro x; rfl
        right_inv := by intro a; apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
        map_mul' := by intro a b; apply Subtype.ext; rfl }
  let actionG : G →* (A ≃* A) :=
    (MulAut.congr e).symm.toMonoidHom.comp MulAut.conjNormal
  have hker : r.ker ≤ actionG.ker := by
    intro t ht
    obtain ⟨a, ha⟩ := e.surjective ⟨t, ht⟩
    apply DFunLike.ext _ _
    intro b
    apply e.injective
    have hab := congrArg e (hcomm a b)
    have hcomm' : t * (e b : G) = (e b : G) * t := by
      change ((⟨t, ht⟩ : r.ker) * e b : r.ker).1 =
        (e b * ⟨t, ht⟩ : r.ker).1
      rw [← ha]
      exact congrArg Subtype.val hab
    change (⟨t * (e b : G) * t⁻¹, _⟩ : r.ker) = e b
    apply Subtype.ext
    change t * (e b : G) * t⁻¹ = (e b : G)
    calc
      t * (e b : G) * t⁻¹ = (e b : G) * t * t⁻¹ :=
        congrArg (fun z : G => z * t⁻¹) hcomm'
      _ = (e b : G) := mul_inv_cancel_right _ _
  have hr : Function.Surjective r :=
    AlgEquiv.restrictNormalHom_surjective E
  exact r.liftOfSurjective hr ⟨actionG, hker⟩

/-- Defining lift equation for kernel conjugation. -/
theorem regularKernelConjugation_lift
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (M : GaloisOverfield N)
    (hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a)
    (g : N.field ≃ₐ[ℚ] N.field)
    (gtilde : M.toExtension.field.field ≃ₐ[ℚ]
      M.toExtension.field.field)
    (hg : AlgEquiv.restrictNormalHom N.field gtilde = g)
    (a : RegularKernelGroup N M) (x : M.toExtension.field.field) :
    regularKernelConjugation N M hcomm g a x =
      gtilde (a (gtilde.symm x)) := by
  subst g
  simp [regularKernelConjugation, MonoidHom.liftOfSurjective]

/-- Left translation on the regular group algebra. -/
def regularLeftTranslate
    (p : NU.LocalTheory.OddPrime) {G : Type*} [Group G]
    (g : G) (x : MonoidAlgebra (ZMod (p : ℕ)) G) :
    MonoidAlgebra (ZMod (p : ℕ)) G :=
  MonoidAlgebra.single g 1 * x


/-! ## Consolidated fallback seam -/

/-- The remaining field-theoretic descent construction. -/
private def KummerDescentConstruction : Prop :=
  ∀ (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ)),
    c ≠ 1 →
    (∀ delta : CyclotomicDelta N p,
      kummerAction N p delta c =
        c ^ ((cyclotomicCharacter N p delta : ZMod (p : ℕ)).val)) →
    ∀ (a : (cyclotomicCompositum N p).fieldˣ),
    QuotientGroup.mk a = c →
    ∃ L : NumberFieldExtension N,
      IsGalois N.field L.field.field ∧
      Module.finrank N.field L.field.field = (p : ℕ) ∧
      IsCyclic (L.field.field ≃ₐ[N.field] L.field.field) ∧
      (cyclotomicCompositum N p).field ⊔ L.field.field =
        radicalExtension (cyclotomicCompositum N p) p a

/-- The remaining weak-approximation and local Kummer construction. -/
private def AsymmetricCyclicConstruction : Prop :=
  ∀ (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime),
    ∃ q : NU.Chebotarev.PrimeIdeal ℚ,
      NU.Chebotarev.PrimeIdeal.norm q ≠ (p : ℕ) ∧
      SplitsCompletelyAt N q ∧
      ∃ v : (N.field ≃ₐ[ℚ] N.field) →
          NU.LocalTheory.FinitePlace N.field,
        (∀ g, rationalPrime N (v g) = q) ∧
        Function.Injective v ∧
        (∀ w, rationalPrime N w = q → ∃ g, v g = w) ∧
        (∀ g, v g = NU.LocalTheory.conjugateFinitePlace ℚ g (v 1)) ∧
        ∃ b a : (cyclotomicCompositum N p).fieldˣ,
          QuotientGroup.mk a =
              projectedKummerClass N p (QuotientGroup.mk b) ∧
          projectedKummerClass N p (QuotientGroup.mk b) ≠ 1 ∧
          ∃ L : NumberFieldExtension N,
            IsGalois N.field L.field.field ∧
            Module.finrank N.field L.field.field = (p : ℕ) ∧
            IsCyclic (L.field.field ≃ₐ[N.field] L.field.field) ∧
            IsRamifiedAt L (v 1) ∧
            (∀ g ≠ 1, SplitsCompletelyAbove L (v g)) ∧
            (cyclotomicCompositum N p).field ⊔ L.field.field =
              radicalExtension (cyclotomicCompositum N p) p a

/-- The remaining conjugate-compositum construction and its regular-module
identification. -/
private def RegularKernelConstruction : Prop :=
  ∀ (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime),
    ∃ M : GaloisOverfield N,
      ∃ hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a,
      letI : CommGroup (RegularKernelGroup N M) :=
        regularKernelCommGroup N M hcomm
      (∀ a : RegularKernelGroup N M, a ^ (p : ℕ) = 1) ∧
      ∃ moduleA : Module (ZMod (p : ℕ))
          (Additive (RegularKernelGroup N M)),
        letI : Module (ZMod (p : ℕ))
            (Additive (RegularKernelGroup N M)) := moduleA
        (∀ (a : RegularKernelGroup N M) (r : ZMod (p : ℕ)),
          Additive.toMul (r • Additive.ofMul a) = a ^ r.val) ∧
        ∃ e : Additive (RegularKernelGroup N M) ≃ₗ[ZMod (p : ℕ)]
            MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field),
          (∀ (g : N.field ≃ₐ[ℚ] N.field)
              (a : RegularKernelGroup N M),
            e (Additive.ofMul
                (regularKernelConjugation N M hcomm g a)) =
              regularLeftTranslate p g (e (Additive.ofMul a))) ∧
          Fintype.card (RegularKernelGroup N M) =
            (p : ℕ) ^ Fintype.card (N.field ≃ₐ[ℚ] N.field)

/-- The genuinely arithmetic part of the regular-kernel construction:
an additive regular representation with the required conjugation action.
The exponent, `ZMod p`-module structure, linearity, and cardinality are formal
consequences assembled below. -/
private def RegularKernelAdditiveConstruction : Prop :=
  ∀ (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime),
    ∃ M : GaloisOverfield N,
      ∃ hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a,
      letI : CommGroup (RegularKernelGroup N M) :=
        regularKernelCommGroup N M hcomm
      ∃ e : Additive (RegularKernelGroup N M) ≃+
          MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field),
        ∀ (g : N.field ≃ₐ[ℚ] N.field)
            (a : RegularKernelGroup N M),
          e (Additive.ofMul
              (regularKernelConjugation N M hcomm g a)) =
            regularLeftTranslate p g (e (Additive.ofMul a))

/-- Transporting the standard module structure through an additive regular
representation supplies all of `RegularKernelConstruction`'s formal
bookkeeping. -/
private theorem regularKernelConstruction_of_additive
    (h : RegularKernelAdditiveConstruction) :
    RegularKernelConstruction := by
  intro N _ p
  obtain ⟨M, hcomm, eAdd, hequiv⟩ := h N p
  letI : CommGroup (RegularKernelGroup N M) :=
    regularKernelCommGroup N M hcomm
  have hpow (a : RegularKernelGroup N M) : a ^ (p : ℕ) = 1 := by
    apply Additive.ofMul.injective
    apply eAdd.injective
    change eAdd ((p : ℕ) • Additive.ofMul a) = eAdd 0
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul
      (R := ZMod (p : ℕ)), ZMod.natCast_self, zero_smul]
  let moduleA : Module (ZMod (p : ℕ))
      (Additive (RegularKernelGroup N M)) :=
    eAdd.module (ZMod (p : ℕ))
  refine ⟨M, hcomm, hpow, moduleA, ?_, ?_⟩
  · intro a r
    have ha : r • Additive.ofMul a = Additive.ofMul (a ^ r.val) := by
      apply eAdd.injective
      rw [show eAdd (r • Additive.ofMul a) =
          r • eAdd (Additive.ofMul a) by
        change eAdd (eAdd.symm (r • eAdd (Additive.ofMul a))) = _
        exact eAdd.apply_symm_apply _]
      calc
        r • eAdd (Additive.ofMul a) =
            (r.val : ZMod (p : ℕ)) • eAdd (Additive.ofMul a) := by
          rw [ZMod.natCast_zmod_val]
        _ = r.val • eAdd (Additive.ofMul a) :=
          Nat.cast_smul_eq_nsmul (ZMod (p : ℕ)) r.val _
        _ = eAdd (r.val • Additive.ofMul a) :=
          (map_nsmul eAdd r.val (Additive.ofMul a)).symm
        _ = eAdd (Additive.ofMul (a ^ r.val)) := rfl
    exact congrArg Additive.toMul ha
  · let eLinear := eAdd.linearEquiv (ZMod (p : ℕ))
    refine ⟨eLinear, ?_, ?_⟩
    · intro g a
      exact hequiv g a
    · classical
      letI : Fintype
          ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ)) := inferInstance
      letI : Fintype
          (MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field)) :=
        Fintype.ofEquiv ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ))
          MonoidAlgebra.coeffEquiv.symm
      calc
        Fintype.card (RegularKernelGroup N M) =
            Fintype.card (Additive (RegularKernelGroup N M)) :=
          Fintype.card_congr Additive.toMul.symm
        _ = Fintype.card
            (MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field)) :=
          Fintype.card_congr eAdd.toEquiv
        _ = Fintype.card
            ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ)) :=
          Fintype.card_congr MonoidAlgebra.coeffEquiv
        _ = (p : ℕ) ^ Fintype.card (N.field ≃ₐ[ℚ] N.field) := by
          rw [Fintype.card_finsupp, ZMod.card]

/-- One sharply delimited arithmetic fallback: Kummer descent, the asymmetric
weak-approximation extension, and the additive conjugate-compositum
realization.  Everything from the additive realization to the stated linear
regular module is proved above. -/
private def RegularKernelArithmeticResidual : Prop :=
  KummerDescentConstruction ∧
    AsymmetricCyclicConstruction ∧ RegularKernelAdditiveConstruction

/-- The cyclotomic compositum is Galois over the base field. -/
private theorem cyclotomicCompositum_isGaloisOverBase
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime) :
    letI : Algebra N.field (cyclotomicCompositum N p).field :=
      (IntermediateField.inclusion
        (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
    IsGalois N.field (cyclotomicCompositum N p).field := by
  let E := cyclotomicCompositum N p
  let zeta : Omega := primitiveRootInOmega p
  have hNE : N.field ≤ E.field := le_cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion hNE).toRingHom.toAlgebra
  let EN : IntermediateField N.field Omega :=
    IntermediateField.extendScalars hNE
  have hgen : IntermediateField.adjoin N.field {zeta} = EN := by
    apply IntermediateField.restrictScalars_injective ℚ
    change (IntermediateField.adjoin N.field {zeta}).restrictScalars ℚ =
      E.field
    calc
      (IntermediateField.adjoin N.field {zeta}).restrictScalars ℚ =
          N.field ⊔ IntermediateField.adjoin ℚ {zeta} :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ N.field {zeta}
      _ = E.field := rfl
  letI : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsAlgebraic N.field Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (A := Omega) N.field
  letI : Normal N.field Omega :=
    { isAlgebraic := fun x => Algebra.IsAlgebraic.isAlgebraic x
      splits' := fun _ => IsAlgClosed.splits _ }
  have hnormal : Normal N.field EN := by
    rw [IntermediateField.normal_iff_forall_map_eq]
    intro sigma
    let sigmaEquiv : Omega ≃ₐ[N.field] Omega :=
      AlgEquiv.ofBijective sigma
        (AlgHom.normal_bijective N.field Omega Omega sigma)
    have hstable (tau : Omega ≃ₐ[N.field] Omega) :
        ∀ x : Omega, x ∈ EN → tau x ∈ EN := by
      intro x hx
      rw [← hgen] at hx
      refine IntermediateField.adjoin_induction N.field
        (p := fun x _ => tau x ∈ EN) ?_ ?_ ?_ ?_ ?_ hx
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        have hzeta : IsPrimitiveRoot zeta (p : ℕ) :=
          primitiveRootInOmega_spec p
        have hpw : (tau zeta) ^ (p : ℕ) = 1 := by
          rw [← map_pow, hzeta.pow_eq_one, map_one]
        obtain ⟨i, _, htau⟩ := hzeta.eq_pow_of_pow_eq_one hpw
        rw [← htau]
        exact pow_mem (show zeta ∈ EN by
          change zeta ∈ E.field
          exact (show cyclotomicFieldInOmega p ≤ E.field from le_sup_right)
            ((IntermediateField.subset_adjoin ℚ {zeta})
              (Set.mem_singleton zeta))) i
      · intro y
        change tau (algebraMap N.field Omega y) ∈ E.field
        rw [tau.commutes]
        exact hNE y.2
      · intro x y _ _ hx hy
        simpa only [map_add] using EN.add_mem hx hy
      · intro x _ hx
        simpa only [map_inv₀] using EN.inv_mem hx
      · intro x y _ _ hx hy
        simpa only [map_mul] using EN.mul_mem hx hy
    apply le_antisymm
    · rw [IntermediateField.map_le_iff_le_comap]
      intro x hx
      change sigma x ∈ EN
      exact hstable sigmaEquiv x hx
    · intro x hx
      rw [IntermediateField.mem_map]
      exact ⟨sigmaEquiv.symm x, hstable sigmaEquiv.symm x hx,
        sigmaEquiv.apply_symm_apply x⟩
  letI : Normal N.field E.field := hnormal
  exact IsGalois.mk

/-- The eigenclass equation, expressed on representatives. -/
private theorem eigenUnitRelation
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ))
    (heigen : ∀ delta : CyclotomicDelta N p,
      kummerAction N p delta c =
        c ^ ((cyclotomicCharacter N p delta : ZMod (p : ℕ)).val))
    (a : (cyclotomicCompositum N p).fieldˣ)
    (ha : QuotientGroup.mk a = c)
    (delta : CyclotomicDelta N p) :
    ∃ u : (cyclotomicCompositum N p).fieldˣ,
      Units.map delta.1.toRingEquiv.toMonoidHom a =
        u ^ (p : ℕ) * a ^
          ((cyclotomicCharacter N p delta : ZMod (p : ℕ)).val) := by
  let r := (cyclotomicCharacter N p delta : ZMod (p : ℕ)).val
  have hq :
      (QuotientGroup.mk
          (Units.map delta.1.toRingEquiv.toMonoidHom a) :
        KummerClass (cyclotomicCompositum N p) (p : ℕ)) =
      (QuotientGroup.mk (a ^ r) :
        KummerClass (cyclotomicCompositum N p) (p : ℕ)) := by
    calc
      (QuotientGroup.mk
          (Units.map delta.1.toRingEquiv.toMonoidHom a) :
        KummerClass (cyclotomicCompositum N p) (p : ℕ)) =
          kummerAction N p delta (QuotientGroup.mk a) :=
        (kummerAction_mk N p delta a).symm
      _ = kummerAction N p delta c :=
        congrArg (kummerAction N p delta) ha
      _ = c ^ r := heigen delta
      _ = (QuotientGroup.mk a) ^ r :=
        congrArg (fun z => z ^ r) ha.symm
      _ = QuotientGroup.mk (a ^ r) :=
        (QuotientGroup.mk_pow
          (pthPowerSubgroup (cyclotomicCompositum N p) (p : ℕ)) a r).symm
  have hmem : Units.map delta.1.toRingEquiv.toMonoidHom a / a ^ r ∈
      pthPowerSubgroup (cyclotomicCompositum N p) (p : ℕ) :=
    QuotientGroup.eq_iff_div_mem.mp hq
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, ?_⟩
  change Units.map delta.1.toRingEquiv.toMonoidHom a =
    u ^ (p : ℕ) * a ^ r
  calc
    Units.map delta.1.toRingEquiv.toMonoidHom a =
        (Units.map delta.1.toRingEquiv.toMonoidHom a / a ^ r) *
          a ^ r := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = u ^ (p : ℕ) * a ^ r :=
      congrArg (fun z => z * a ^ r) hu.symm

set_option maxHeartbeats 1600000 in
-- Normality, centrality, and the fixed-field complement are elaborated together.
set_option synthInstance.maxHeartbeats 160000 in
/-- Kummer descent from a cyclotomic eigenclass. -/
private theorem kummerDescentConstruction : KummerDescentConstruction := by
  intro N p c hc heigen a ha
  let E := cyclotomicCompositum N p
  let alpha : Omega := radicalRoot E p a
  have halphaOmega : alpha ^ (p : ℕ) = (a.1 : Omega) :=
    radicalRoot_spec E p a
  have hnotpow : ∀ b : E.field, b ^ (p : ℕ) ≠ (a.1 : E.field) := by
    intro b hb
    have hb0 : b ≠ 0 := by
      intro hbzero
      subst b
      apply a.ne_zero
      exact hb.symm.trans (zero_pow p.1.2.ne_zero)
    let bu : E.fieldˣ := Units.mk0 b hb0
    have hbu : bu ^ (p : ℕ) = a := by
      apply Units.ext
      exact hb
    have hmem : a ∈ pthPowerSubgroup E (p : ℕ) := ⟨bu, hbu⟩
    have hmk : QuotientGroup.mk a = 1 :=
      (QuotientGroup.eq_one_iff a).2 hmem
    exact hc (ha.symm.trans hmk)
  let f : Polynomial E.field :=
    Polynomial.X ^ (p : ℕ) - Polynomial.C a.1
  have hirr : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime p.1.2 hnotpow
  let R0 : IntermediateField E.field Omega :=
    IntermediateField.adjoin E.field {alpha}
  let RQ : IntermediateField ℚ Omega := R0.restrictScalars ℚ
  have hRQ : RQ = radicalExtension E p a := by
    change (IntermediateField.adjoin E.field {alpha}).restrictScalars ℚ =
      E.field ⊔ IntermediateField.adjoin ℚ {alpha}
    exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ E.field {alpha}
  let Rfield : NumberFieldInOmega :=
    { field := RQ
      finite := by
        letI : Algebra.IsAlgebraic ℚ Omega :=
          AlgebraicClosure.isAlgebraic ℚ
        letI : Algebra.IsIntegral ℚ Omega :=
          Algebra.IsAlgebraic.isIntegral
        let A := IntermediateField.adjoin ℚ ({alpha} : Set Omega)
        letI : FiniteDimensional ℚ A :=
          IntermediateField.adjoin.finiteDimensional
            (Algebra.IsIntegral.isIntegral alpha)
        rw [hRQ]
        exact IntermediateField.finiteDimensional_sup E.field A }
  have hNE : N.field ≤ E.field := le_cyclotomicCompositum N p
  have hER : E.field ≤ RQ := by
    intro x hx
    change x ∈ R0
    exact R0.algebraMap_mem ⟨x, hx⟩
  have hNR : N.field ≤ RQ := hNE.trans hER
  letI : Algebra ℚ RQ := RQ.algebra'
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion hNE).toRingHom.toAlgebra
  letI : Algebra E.field RQ :=
    (IntermediateField.inclusion hER).toRingHom.toAlgebra
  letI : Algebra N.field RQ :=
    (IntermediateField.inclusion hNR).toRingHom.toAlgebra
  letI : IsScalarTower N.field E.field RQ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : IsScalarTower ℚ N.field RQ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : IsScalarTower ℚ E.field RQ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : Module.Finite ℚ RQ := Rfield.finite
  letI : Module.Finite N.field RQ :=
    Module.Finite.of_restrictScalars_finite ℚ N.field RQ
  letI : Module.Finite E.field RQ :=
    Module.Finite.of_restrictScalars_finite ℚ E.field RQ
  let alphaR : RQ := by
    refine ⟨alpha, ?_⟩
    change alpha ∈ R0
    exact IntermediateField.subset_adjoin E.field {alpha}
      (Set.mem_singleton alpha)
  have halphaR : alphaR ^ (p : ℕ) = algebraMap E.field RQ a.1 := by
    apply Subtype.ext
    exact halphaOmega
  have halpha0 : alpha ≠ 0 := by
    intro hz
    apply a.ne_zero
    apply E.field.val.injective
    change (a.1 : Omega) = 0
    rw [← halphaOmega, hz, zero_pow p.1.2.ne_zero]
  have halphaR0 : alphaR ≠ 0 := by
    intro hz
    apply a.ne_zero
    apply (algebraMap E.field RQ).injective
    calc
      algebraMap E.field RQ a.1 = alphaR ^ (p : ℕ) := halphaR.symm
      _ = 0 := by rw [hz, zero_pow p.1.2.ne_zero]
      _ = algebraMap E.field RQ 0 := (map_zero _).symm
  have hroot : IsPrimitiveRoot (cyclotomicRoot N p) (p : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective (f := E.field.val)
    · exact primitiveRootInOmega_spec p
    · exact E.field.val.injective
  have hroots : (primitiveRoots (p : ℕ) E.field).Nonempty := by
    refine ⟨cyclotomicRoot N p, ?_⟩
    exact (mem_primitiveRoots p.1.2.pos).2 hroot
  have hsplits : (f.map (algebraMap E.field RQ)).Splits := by
    rw [show f = Polynomial.X ^ (p : ℕ) - Polynomial.C a.1 from rfl,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hroot.map_of_injective (algebraMap E.field RQ).injective) halphaR
  have hgen : IntermediateField.adjoin E.field {alphaR} = ⊤ := by
    let RR : IntermediateField E.field Omega :=
      IntermediateField.extendScalars hER
    let i : RQ ≃ₐ[E.field] RR :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    have hgenRR : IntermediateField.adjoin E.field {i alphaR} = ⊤ := by
      apply IntermediateField.lift_injective RR
      rw [IntermediateField.lift_adjoin_simple,
        IntermediateField.lift_top]
      change R0 = RR
      ext x
      rfl
    have himapTop : IntermediateField.map i.toAlgHom
        (⊤ : IntermediateField E.field RQ) = ⊤ := by
      apply top_unique
      intro x _
      rw [IntermediateField.mem_map]
      exact ⟨i.symm x, trivial, i.apply_symm_apply x⟩
    apply (IntermediateField.map_injective i.toAlgHom)
    rw [IntermediateField.adjoin_map, himapTop, Set.image_singleton]
    change IntermediateField.adjoin E.field {i alphaR} = ⊤
    exact hgenRR
  letI : Polynomial.IsSplittingField E.field RQ f :=
    isSplittingField_iff_intermediateField.mpr ⟨hsplits, by
      apply top_unique
      rw [← hgen]
      apply IntermediateField.adjoin.mono E.field
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      have hfmonic : f.Monic :=
        Polynomial.monic_X_pow_sub_C a.1 p.1.2.ne_zero
      rw [hfmonic.mem_rootSet]
      rw [Polynomial.aeval_def,
        show f = Polynomial.X ^ (p : ℕ) - Polynomial.C a.1 from rfl,
        Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, halphaR, sub_self]⟩
  letI : IsGalois E.field RQ :=
    isGalois_of_isSplittingField_X_pow_sub_C hroots hirr RQ
  have hfinER : Module.finrank E.field RQ = (p : ℕ) :=
    finrank_of_isSplittingField_X_pow_sub_C hroots hirr RQ
  letI : IsGalois N.field E.field :=
    cyclotomicCompositum_isGaloisOverBase N p
  letI : IsScalarTower N.field E.field Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let RN : IntermediateField N.field Omega :=
    IntermediateField.extendScalars hNR
  letI : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsAlgebraic N.field Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (A := Omega) N.field
  letI : Normal N.field Omega :=
    { isAlgebraic := fun x => Algebra.IsAlgebraic.isAlgebraic x
      splits' := fun _ => IsAlgClosed.splits _ }
  have hnormalNR : Normal N.field RN := by
    rw [IntermediateField.normal_iff_forall_map_eq]
    intro sigma
    let sigmaEquiv : Omega ≃ₐ[N.field] Omega :=
      AlgEquiv.ofBijective sigma
        (AlgHom.normal_bijective N.field Omega Omega sigma)
    have hstable (tau : Omega ≃ₐ[N.field] Omega) :
        ∀ x : Omega, x ∈ RN → tau x ∈ RN := by
      intro x hx
      change x ∈ R0 at hx
      refine IntermediateField.adjoin_induction E.field
        (p := fun x _ => tau x ∈ RN) ?_ ?_ ?_ ?_ ?_ hx
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        let deltaN : E.field ≃ₐ[N.field] E.field :=
          tau.restrictNormal E.field
        let deltaQ : E.field ≃ₐ[ℚ] E.field :=
          deltaN.restrictScalars ℚ
        let delta : CyclotomicDelta N p :=
          ⟨deltaQ, by
            intro y
            change deltaN (algebraMap N.field E.field y) =
              algebraMap N.field E.field y
            exact deltaN.commutes y⟩
        obtain ⟨u, hu⟩ := eigenUnitRelation N p c heigen a ha delta
        let r :=
          (cyclotomicCharacter N p delta : ZMod (p : ℕ)).val
        let z : Omega := (u.1 : Omega) * alpha ^ r
        have hcomm (y : E.field) :
            (deltaN y : Omega) = tau (y : Omega) :=
          AlgEquiv.restrictNormal_commutes tau E.field y
        have hpow : (tau alpha) ^ (p : ℕ) = z ^ (p : ℕ) := by
          calc
            (tau alpha) ^ (p : ℕ) = tau (alpha ^ (p : ℕ)) :=
              (map_pow tau alpha (p : ℕ)).symm
            _ = tau (a.1 : Omega) := congrArg tau halphaOmega
            _ = (deltaN a.1 : Omega) := (hcomm a.1).symm
            _ = ((Units.map delta.1.toRingEquiv.toMonoidHom a).1 :
                Omega) := by rfl
            _ = ((u ^ (p : ℕ) * a ^ r).1 : Omega) := by
              exact congrArg (fun v : E.fieldˣ => (v.1 : Omega)) hu
            _ = (u.1 : Omega) ^ (p : ℕ) * (a.1 : Omega) ^ r := by
              rfl
            _ = (u.1 : Omega) ^ (p : ℕ) *
                ((alpha ^ r) ^ (p : ℕ)) := by
              congr 1
              rw [← halphaOmega]
              calc
                (alpha ^ (p : ℕ)) ^ r = alpha ^ ((p : ℕ) * r) :=
                  (pow_mul alpha (p : ℕ) r).symm
                _ = alpha ^ (r * (p : ℕ)) := by
                  rw [Nat.mul_comm (p : ℕ) r]
                _ = (alpha ^ r) ^ (p : ℕ) :=
                  pow_mul alpha r (p : ℕ)
            _ = z ^ (p : ℕ) := by
              dsimp [z]
              exact (mul_pow (u.1 : Omega) (alpha ^ r) (p : ℕ)).symm
        have hu0 : (u.1 : Omega) ≠ 0 := by
          intro hz
          apply u.ne_zero
          apply E.field.val.injective
          simpa using hz
        have hz0 : z ≠ 0 :=
          mul_ne_zero hu0 (pow_ne_zero r halpha0)
        let xi : Omega := tau alpha / z
        have hxipow : xi ^ (p : ℕ) = 1 := by
          dsimp [xi]
          rw [div_pow, hpow, div_self (pow_ne_zero (p : ℕ) hz0)]
        have hzeta : IsPrimitiveRoot (primitiveRootInOmega p) (p : ℕ) :=
          primitiveRootInOmega_spec p
        obtain ⟨i, _, hxi⟩ := hzeta.eq_pow_of_pow_eq_one hxipow
        have hzetamem : primitiveRootInOmega p ∈ RN := by
          change primitiveRootInOmega p ∈ R0
          change algebraMap E.field Omega (cyclotomicRoot N p) ∈ R0
          exact R0.algebraMap_mem (cyclotomicRoot N p)
        have humem : (u.1 : Omega) ∈ RN := by
          change (u.1 : Omega) ∈ R0
          exact R0.algebraMap_mem u.1
        have halphamem : alpha ∈ RN := by
          change alpha ∈ R0
          exact IntermediateField.subset_adjoin E.field {alpha}
            (Set.mem_singleton alpha)
        have hximem : xi ∈ RN := by
          rw [← hxi]
          exact RN.toSubfield.pow_mem hzetamem i
        have halpharmem : alpha ^ r ∈ RN :=
          RN.toSubfield.pow_mem halphamem r
        rw [← div_mul_cancel₀ (tau alpha) hz0]
        change xi * z ∈ RN
        exact RN.mul_mem hximem (RN.mul_mem humem halpharmem)
      · intro y
        have hcomm := AlgEquiv.restrictNormal_commutes tau E.field y
        change tau (algebraMap E.field Omega y) ∈ RN
        rw [← hcomm]
        change (tau.restrictNormal E.field y : Omega) ∈ R0
        exact R0.algebraMap_mem (tau.restrictNormal E.field y)
      · intro x y _ _ hx hy
        simpa only [map_add] using RN.add_mem hx hy
      · intro x _ hx
        simpa only [map_inv₀] using RN.inv_mem hx
      · intro x y _ _ hx hy
        simpa only [map_mul] using RN.mul_mem hx hy
    apply le_antisymm
    · rw [IntermediateField.map_le_iff_le_comap]
      intro x hx
      change sigma x ∈ RN
      exact hstable sigmaEquiv x hx
    · intro x hx
      rw [IntermediateField.mem_map]
      exact ⟨sigmaEquiv.symm x, hstable sigmaEquiv.symm x hx,
        sigmaEquiv.apply_symm_apply x⟩
  letI : Normal N.field RQ := hnormalNR
  letI : IsGalois N.field RQ := IsGalois.mk
  let H := RQ ≃ₐ[N.field] RQ
  let D := E.field ≃ₐ[N.field] E.field
  let res : H →* D := AlgEquiv.restrictNormalHom E.field
  let C : Subgroup H := res.ker
  let zetaR : RQ := algebraMap E.field RQ (cyclotomicRoot N p)
  have hzetaR : IsPrimitiveRoot zetaR (p : ℕ) :=
    hroot.map_of_injective (algebraMap E.field RQ).injective
  have hcentral : C ≤ Subgroup.center H := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro t
    have hsone : AlgEquiv.restrictNormalHom E.field s = 1 :=
      MonoidHom.mem_ker.mp hs
    have hfixs (y : E.field) :
        s (algebraMap E.field RQ y) = algebraMap E.field RQ y := by
      have hres := AlgEquiv.restrictNormal_commutes s E.field y
      have hsy := DFunLike.congr_fun hsone y
      change s.restrictNormal E.field y = y at hsy
      calc
        s (algebraMap E.field RQ y) =
            algebraMap E.field RQ (s.restrictNormal E.field y) := hres.symm
        _ = algebraMap E.field RQ y :=
          congrArg (algebraMap E.field RQ) hsy
    let deltaN : E.field ≃ₐ[N.field] E.field := res t
    let deltaQ : E.field ≃ₐ[ℚ] E.field := deltaN.restrictScalars ℚ
    let delta : CyclotomicDelta N p :=
      ⟨deltaQ, by
        intro y
        change deltaN (algebraMap N.field E.field y) =
          algebraMap N.field E.field y
        exact deltaN.commutes y⟩
    let r := (cyclotomicCharacter N p delta : ZMod (p : ℕ)).val
    have hrest (y : E.field) :
        t (algebraMap E.field RQ y) = algebraMap E.field RQ (deltaN y) :=
      (AlgEquiv.restrictNormal_commutes t E.field y).symm
    have htZeta : t zetaR = zetaR ^ r := by
      dsimp [zetaR]
      rw [hrest, ← map_pow]
      exact congrArg (algebraMap E.field RQ)
        (cyclotomicCharacter_spec N p delta)
    obtain ⟨u, hu⟩ := eigenUnitRelation N p c heigen a ha delta
    let z : RQ := algebraMap E.field RQ u.1 * alphaR ^ r
    have htpow : (t alphaR) ^ (p : ℕ) = z ^ (p : ℕ) := by
      calc
        (t alphaR) ^ (p : ℕ) = t (alphaR ^ (p : ℕ)) :=
          (map_pow t alphaR (p : ℕ)).symm
        _ = t (algebraMap E.field RQ a.1) := congrArg t halphaR
        _ = algebraMap E.field RQ (deltaN a.1) := hrest a.1
        _ = algebraMap E.field RQ
            (Units.map delta.1.toRingEquiv.toMonoidHom a).1 := by rfl
        _ = algebraMap E.field RQ (u ^ (p : ℕ) * a ^ r).1 :=
          congrArg (fun v : E.fieldˣ => algebraMap E.field RQ v.1) hu
        _ = (algebraMap E.field RQ u.1) ^ (p : ℕ) *
            (algebraMap E.field RQ a.1) ^ r := by rfl
        _ = (algebraMap E.field RQ u.1) ^ (p : ℕ) *
            ((alphaR ^ r) ^ (p : ℕ)) := by
          congr 1
          rw [← halphaR]
          calc
            (alphaR ^ (p : ℕ)) ^ r = alphaR ^ ((p : ℕ) * r) :=
              (pow_mul alphaR (p : ℕ) r).symm
            _ = alphaR ^ (r * (p : ℕ)) := by
              rw [Nat.mul_comm (p : ℕ) r]
            _ = (alphaR ^ r) ^ (p : ℕ) := pow_mul alphaR r (p : ℕ)
        _ = z ^ (p : ℕ) := by
          dsimp [z]
          exact (mul_pow _ _ _).symm
    have hz0 : z ≠ 0 :=
      mul_ne_zero ((map_ne_zero (algebraMap E.field RQ)).2 u.ne_zero)
        (pow_ne_zero r halphaR0)
    let eta : RQ := t alphaR / z
    have hetapow : eta ^ (p : ℕ) = 1 := by
      dsimp [eta]
      rw [div_pow, htpow, div_self (pow_ne_zero (p : ℕ) hz0)]
    obtain ⟨i, _, heta⟩ := hzetaR.eq_pow_of_pow_eq_one hetapow
    have htalpha : t alphaR = zetaR ^ i * z := by
      rw [heta]
      exact (div_mul_cancel₀ (t alphaR) hz0).symm
    let xi : RQ := s alphaR / alphaR
    have hxipow : xi ^ (p : ℕ) = 1 := by
      dsimp [xi]
      rw [div_pow, ← map_pow s alphaR (p : ℕ), halphaR, hfixs,
        div_self]
      exact (map_ne_zero (algebraMap E.field RQ)).2 a.ne_zero
    obtain ⟨j, _, hxi⟩ := hzetaR.eq_pow_of_pow_eq_one hxipow
    have hsalpha : s alphaR = zetaR ^ j * alphaR := by
      rw [hxi]
      exact (div_mul_cancel₀ (s alphaR) halphaR0).symm
    have hsZeta : s zetaR = zetaR := hfixs (cyclotomicRoot N p)
    have halphaComm : (s * t) alphaR = (t * s) alphaR := by
      change s (t alphaR) = t (s alphaR)
      rw [htalpha, map_mul, map_pow, hsZeta]
      dsimp [z]
      rw [map_mul, hfixs, map_pow, hsalpha]
      rw [map_mul, map_pow, htZeta, htalpha]
      dsimp [z]
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm r j]
      ring
    symm
    apply AlgEquiv.ext
    intro x
    have hx : (x : RQ) ∈ (⊤ : IntermediateField E.field RQ) := trivial
    rw [← hgen] at hx
    refine IntermediateField.adjoin_induction E.field
      (p := fun x _ => (s * t) x = (t * s) x) ?_ ?_ ?_ ?_ ?_ hx
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact halphaComm
    · intro y
      change s (t (algebraMap E.field RQ y)) =
        t (s (algebraMap E.field RQ y))
      rw [hrest, hfixs, hfixs, hrest]
    · intro x y _ _ hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
    · intro x _ hx
      simpa only [map_inv₀] using congrArg Inv.inv hx
    · intro x y _ _ hx hy
      simpa only [map_mul] using congrArg₂ (· * ·) hx hy
  have hresSurj : Function.Surjective res :=
    AlgEquiv.restrictNormalHom_surjective RQ
  let EN : IntermediateField N.field Omega :=
    IntermediateField.extendScalars hNE
  have hglobal :
      IntermediateField.adjoin N.field {primitiveRootInOmega p} = EN := by
    apply IntermediateField.restrictScalars_injective ℚ
    change (IntermediateField.adjoin N.field
      {primitiveRootInOmega p}).restrictScalars ℚ = E.field
    calc
      (IntermediateField.adjoin N.field
          {primitiveRootInOmega p}).restrictScalars ℚ =
          N.field ⊔ IntermediateField.adjoin ℚ {primitiveRootInOmega p} :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ N.field
          {primitiveRootInOmega p}
      _ = E.field := rfl
  have hgenE :
      IntermediateField.adjoin N.field {cyclotomicRoot N p} = ⊤ := by
    let i : E.field ≃ₐ[N.field] EN :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    have hgenEN :
        IntermediateField.adjoin N.field {i (cyclotomicRoot N p)} = ⊤ := by
      apply IntermediateField.lift_injective EN
      rw [IntermediateField.lift_adjoin_simple,
        IntermediateField.lift_top]
      exact hglobal
    have himapTop : IntermediateField.map i.toAlgHom
        (⊤ : IntermediateField N.field E.field) = ⊤ := by
      apply top_unique
      intro x _
      rw [IntermediateField.mem_map]
      exact ⟨i.symm x, trivial, i.apply_symm_apply x⟩
    apply (IntermediateField.map_injective i.toAlgHom)
    rw [IntermediateField.adjoin_map, himapTop, Set.image_singleton]
    change IntermediateField.adjoin N.field
      {i (cyclotomicRoot N p)} = ⊤
    exact hgenEN
  let chiN : D →* (ZMod (p : ℕ))ˣ := hroot.autToPow N.field
  have hchiInj : Function.Injective chiN := by
    intro s t hst
    apply AlgEquiv.ext
    intro x
    have hx : (x : E.field) ∈ (⊤ : IntermediateField N.field E.field) :=
      trivial
    rw [← hgenE] at hx
    refine IntermediateField.adjoin_induction N.field
      (p := fun x _ => s x = t x) ?_ ?_ ?_ ?_ ?_ hx
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      rw [← hroot.autToPow_spec N.field s,
        ← hroot.autToPow_spec N.field t, hst]
    · intro y
      rw [s.commutes, t.commutes]
    · intro x y _ _ hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
    · intro x _ hx
      simpa only [map_inv₀] using congrArg Inv.inv hx
    · intro x y _ _ hx hy
      simpa only [map_mul] using congrArg₂ (· * ·) hx hy
  letI : IsCyclic D := isCyclic_of_injective chiN hchiInj
  letI : IsMulCommutative H :=
    res.isMulCommutative_of_isCyclic_of_ker_le_center hcentral
  have hindexC : C.index = Nat.card D := by
    calc
      C.index = Nat.card res.range := Subgroup.index_ker res
      _ = Nat.card (⊤ : Subgroup D) := by
        rw [MonoidHom.range_eq_top.mpr hresSurj]
      _ = Nat.card D := Nat.card_congr Subgroup.topEquiv.toEquiv
  have hcardC : Nat.card C = (p : ℕ) := by
    apply Nat.eq_of_mul_eq_mul_right
      (show 0 < Module.finrank N.field E.field from Module.finrank_pos)
    calc
      Nat.card C * Module.finrank N.field E.field = Nat.card C * C.index := by
        rw [hindexC, IsGalois.card_aut_eq_finrank]
      _ = Nat.card H := Subgroup.card_mul_index C
      _ = Module.finrank N.field RQ :=
        IsGalois.card_aut_eq_finrank N.field RQ
      _ = Module.finrank N.field E.field * Module.finrank E.field RQ :=
        (Module.finrank_mul_finrank N.field E.field RQ).symm
      _ = Module.finrank N.field E.field * (p : ℕ) := by rw [hfinER]
      _ = (p : ℕ) * Module.finrank N.field E.field := Nat.mul_comm _ _
  have hDdvd : Nat.card D ∣ (p : ℕ) - 1 := by
    have hd := Subgroup.card_dvd_of_injective chiN hchiInj
    letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.1.2⟩
    calc
      Nat.card D ∣ Nat.card (ZMod (p : ℕ))ˣ := hd
      _ = Fintype.card (ZMod (p : ℕ))ˣ := Nat.card_eq_fintype_card
      _ = (p : ℕ) - 1 := ZMod.card_units (p : ℕ)
  have hcopPred : Nat.Coprime (p : ℕ) ((p : ℕ) - 1) := by
    apply p.1.2.coprime_iff_not_dvd.mpr
    intro hd
    have hle : (p : ℕ) ≤ (p : ℕ) - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt p.1.2.one_lt) hd
    exact (Nat.not_le_of_lt
      (Nat.sub_lt p.1.2.pos Nat.zero_lt_one)) hle
  have hcop : Nat.Coprime (Nat.card C) C.index := by
    rw [hcardC, hindexC]
    exact Nat.Coprime.coprime_dvd_right hDdvd hcopPred
  obtain ⟨T, hT⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  letI : T.Normal := Subgroup.normal_of_isMulCommutative T
  let L0 : IntermediateField N.field RQ := IntermediateField.fixedField T
  letI : IsGalois N.field L0 :=
    IsGalois.of_fixedField_normal_subgroup T
  have hfinL0 : Module.finrank N.field L0 = (p : ℕ) := by
    rw [← IsGalois.card_aut_eq_finrank]
    calc
      Nat.card (L0 ≃ₐ[N.field] L0) = Nat.card (H ⧸ T) :=
        Nat.card_congr
          (IsGalois.normalAutEquivQuotient T).symm.toEquiv
      _ = T.index := (Subgroup.index_eq_card T).symm
      _ = Nat.card C := hT.symm.index_eq_card
      _ = (p : ℕ) := hcardC
  let eHom : E.field →ₐ[N.field] RQ :=
    IsScalarTower.toAlgHom N.field E.field RQ
  let ENR : IntermediateField N.field RQ :=
    IntermediateField.map eHom (⊤ : IntermediateField N.field E.field)
  have hCfix : C = ENR.fixingSubgroup := by
    ext s
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hs x hx
      rw [IntermediateField.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      have hres := AlgEquiv.restrictNormal_commutes s E.field y
      have hsy := DFunLike.congr_fun hs y
      change s.restrictNormal E.field y = y at hsy
      calc
        s (eHom y) = algebraMap E.field RQ
            (s.restrictNormal E.field y) := hres.symm
        _ = eHom y := congrArg (algebraMap E.field RQ) hsy
    · intro hs
      apply AlgEquiv.ext
      intro y
      apply (algebraMap E.field RQ).injective
      have hres := AlgEquiv.restrictNormal_commutes s E.field y
      calc
        algebraMap E.field RQ (res s y) =
            s (algebraMap E.field RQ y) := hres
        _ = algebraMap E.field RQ y := hs _ (by
          rw [IntermediateField.mem_map]
          exact ⟨y, trivial, rfl⟩)
  have hfixedE : IntermediateField.fixedField C = ENR := by
    rw [hCfix]
    exact IsGalois.fixedField_fixingSubgroup ENR
  have hsupN : IntermediateField.fixedField C ⊔ L0 = ⊤ := by
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [IsGalois.intermediateFieldEquivSubgroup_apply,
      IsGalois.intermediateFieldEquivSubgroup_apply,
      IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_top]
    exact congrArg OrderDual.toDual hT.disjoint.symm.eq_bot
  let Einside : IntermediateField ℚ RQ :=
    (IntermediateField.fixedField C).restrictScalars ℚ
  let Linside : IntermediateField ℚ RQ := L0.restrictScalars ℚ
  let LQ : IntermediateField ℚ Omega := IntermediateField.lift Linside
  have hElift : IntermediateField.lift Einside = E.field := by
    dsimp [Einside]
    rw [hfixedE]
    ext x
    constructor
    · intro hx
      have hxRQ : x ∈ RQ := IntermediateField.lift_le _ hx
      let xR : RQ := ⟨x, hxRQ⟩
      have hxI : xR ∈ ENR.restrictScalars ℚ :=
        (IntermediateField.mem_lift xR).mp hx
      have hxE : xR ∈ ENR := hxI
      rw [IntermediateField.mem_map] at hxE
      obtain ⟨y, _, hxy⟩ := hxE
      have hv : (y : Omega) = x := congrArg Subtype.val hxy
      rw [← hv]
      exact y.2
    · intro hx
      let xR : RQ := ⟨x, hER hx⟩
      have hxE : xR ∈ ENR := by
        rw [IntermediateField.mem_map]
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
      have hxI : xR ∈ ENR.restrictScalars ℚ := hxE
      exact (IntermediateField.mem_lift xR).2 hxI
  have hsupInside : Einside ⊔ Linside = ⊤ := by
    dsimp [Einside, Linside]
    rw [IntermediateField.restrictScalars_sup, hsupN,
      IntermediateField.restrictScalars_top]
  have hcompositum : E.field ⊔ LQ = RQ := by
    rw [← hElift]
    change IntermediateField.lift Einside ⊔
      IntermediateField.lift Linside = RQ
    calc
      IntermediateField.lift Einside ⊔ IntermediateField.lift Linside =
          IntermediateField.lift (Einside ⊔ Linside) :=
        (IntermediateField.lift_sup ℚ RQ Einside Linside).symm
      _ = IntermediateField.lift (⊤ : IntermediateField ℚ RQ) :=
        congrArg IntermediateField.lift hsupInside
      _ = RQ := IntermediateField.lift_top ℚ RQ
  let eQ : Linside ≃ₐ[ℚ] LQ :=
    IntermediateField.liftAlgEquiv Linside
  have hNL : N.field ≤ LQ := by
    intro x hx
    let xR : RQ := ⟨x, hNR hx⟩
    have hx0 : xR ∈ L0 := L0.algebraMap_mem ⟨x, hx⟩
    have hxi : xR ∈ Linside := hx0
    simpa [xR, LQ] using (IntermediateField.mem_lift xR).mpr hxi
  letI : Algebra N.field LQ :=
    (IntermediateField.inclusion hNL).toRingHom.toAlgebra
  let eL : L0 ≃ₐ[N.field] LQ :=
    { toFun := fun x => eQ ⟨x.1, x.2⟩
      invFun := fun x => (eQ.symm x : Linside)
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg Subtype.val
          (eQ.symm_apply_apply ⟨x.1, x.2⟩)
      right_inv := eQ.apply_symm_apply
      map_mul' := eQ.map_mul
      map_add' := eQ.map_add
      commutes' := fun _ => by apply Subtype.ext; rfl }
  letI : Module.Finite ℚ Linside := by infer_instance
  let Lfield : NumberFieldInOmega :=
    { field := LQ
      finite := Module.Finite.equiv eQ.toLinearEquiv }
  let L : NumberFieldExtension N :=
    { field := Lfield
      le_base := hNL }
  letI : Algebra N.field L.field.field :=
    (IntermediateField.inclusion hNL).toRingHom.toAlgebra
  letI : Module.Finite N.field L.field.field :=
    Module.Finite.equiv eL.toLinearEquiv
  letI : IsGalois N.field L.field.field := IsGalois.of_algEquiv eL
  have hfinL : Module.finrank N.field L.field.field = (p : ℕ) := by
    calc
      Module.finrank N.field L.field.field = Module.finrank N.field L0 :=
        eL.toLinearEquiv.finrank_eq.symm
      _ = (p : ℕ) := hfinL0
  have hcyclicL : IsCyclic (L.field.field ≃ₐ[N.field] L.field.field) := by
    letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.1.2⟩
    apply isCyclic_of_prime_card (p := (p : ℕ))
    rw [IsGalois.card_aut_eq_finrank, hfinL]
  refine ⟨L, inferInstance, hfinL, hcyclicL, ?_⟩
  change E.field ⊔ LQ = radicalExtension E p a
  exact hcompositum.trans hRQ

/-! ### Arithmetic input for the asymmetric extension -/

private theorem asymmetricAbsoluteRamificationIndex
    (L : NumberFieldInOmega)
    (v : NU.LocalTheory.FinitePlace L.field) :
    absoluteRamificationIndex L v =
      v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ) := rfl

private theorem asymmetricAbsoluteResidueDegree
    (L : NumberFieldInOmega)
    (v : NU.LocalTheory.FinitePlace L.field) :
    absoluteResidueDegree L v =
      v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ) := rfl

private theorem cyclotomicCompositum_isGaloisOverQ
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    IsGalois ℚ (cyclotomicCompositum N p).field := by
  let C := cyclotomicFieldInOmega p
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Omega := Algebra.IsAlgebraic.isIntegral
  haveI : IsCyclotomicExtension {(p : ℕ)} ℚ C :=
    (primitiveRootInOmega_spec p).intermediateField_adjoin_isCyclotomicExtension ℚ
  letI : IsGalois ℚ C :=
    IsCyclotomicExtension.isGalois {(p : ℕ)} ℚ C
  have hN : Normal ℚ N.field := IsGalois.to_normal
  have hC : Normal ℚ C := IsGalois.to_normal
  have hsup : Normal ℚ
      ↥(N.field ⊔ C : IntermediateField ℚ Omega) :=
    @IntermediateField.normal_sup ℚ Omega inferInstance inferInstance
      inferInstance N.field C hN hC
  change IsGalois ℚ ↥(N.field ⊔ C : IntermediateField ℚ Omega)
  exact @IsGalois.mk ℚ inferInstance _ inferInstance inferInstance
    inferInstance hsup

private theorem existsIdentityFrobeniusPrimeAway
    (F : NumberFieldInOmega) [IsGalois ℚ F.field] (n : ℕ) :
    ∃ q : NU.Chebotarev.PrimeIdeal ℚ,
      NU.Chebotarev.PrimeIdeal.norm q ≠ n ∧
      q ∈ NU.Chebotarev.frobeniusPrimeSet (K := ℚ) (L := F.field)
        (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)) := by
  let S := NU.Chebotarev.frobeniusPrimeSet (K := ℚ) (L := F.field)
    (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field))
  let B : Set (NU.Chebotarev.PrimeIdeal ℚ) :=
    {q | NU.Chebotarev.PrimeIdeal.norm q = n}
  have hB : B.Finite := by
    apply Set.Finite.of_finite_image
      (f := fun q : NU.Chebotarev.PrimeIdeal ℚ => q.asIdeal)
    · exact (Ideal.finite_setOf_absNorm_eq n).subset (by
        intro I hI
        rcases hI with ⟨q, hqn, rfl⟩
        exact hqn)
    · intro q _ r _ hqr
      exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hqr
  have hden := NU.Chebotarev.chebotarev_dirichletDensity
    (K := ℚ) (L := F.field)
    (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field))
  have hnum : (0 : ℝ) <
      ((ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)).carrier.ncard : ℝ) := by
    exact_mod_cast ((Set.ncard_pos
      (s := (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)).carrier)).2
        (show (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)).carrier.Nonempty
          from ⟨1, ConjClasses.mem_carrier_mk⟩))
  have hdenom : (0 : ℝ) < Nat.card (F.field ≃ₐ[ℚ] F.field) := by
    exact_mod_cast Nat.card_pos (α := F.field ≃ₐ[ℚ] F.field)
  have hpositive : (0 : ℝ) <
      ((ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)).carrier.ncard : ℝ) /
        (Nat.card (F.field ≃ₐ[ℚ] F.field) : ℝ) :=
    div_pos hnum hdenom
  by_contra hex
  have hsub : S ⊆ B := by
    intro q hq
    change NU.Chebotarev.PrimeIdeal.norm q = n
    by_contra hne
    exact hex ⟨q, hne, hq⟩
  have hzero : NU.Chebotarev.HasDirichletDensity S 0 :=
    NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero
      (hB.subset hsub)
  have heq :
      ((ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field)).carrier.ncard : ℝ) /
        (Nat.card (F.field ≃ₐ[ℚ] F.field) : ℝ) = 0 :=
    tendsto_nhds_unique hden hzero
  linarith

set_option maxHeartbeats 800000 in
private theorem splitsCompletelyAt_of_identityFrobenius
    (F : NumberFieldInOmega) [IsGalois ℚ F.field]
    (q : NU.Chebotarev.PrimeIdeal ℚ)
    (hq : q ∈ NU.Chebotarev.frobeniusPrimeSet (K := ℚ) (L := F.field)
      (ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field))) :
    SplitsCompletelyAt F q := by
  rcases hq with ⟨hunr, P, hPq, hclass⟩
  refine ⟨⟨P, ?_⟩, ?_⟩
  · apply HeightOneSpectrum.ext
    rw [rationalPrime, NU.LocalTheory.restrictFinitePlace_asIdeal]
    exact hPq.over.symm
  · intro W hWq
    have hWover : W.asIdeal.LiesOver q.asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
        ← hWq]
      rfl⟩
    letI : W.asIdeal.LiesOver q.asIdeal := hWover
    have hWu : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers ℚ) W.asIdeal := hunr W hWover
    have hclassW : NU.Chebotarev.frobeniusClassAt
        (K := ℚ) (L := F.field) W =
        ConjClasses.mk (1 : F.field ≃ₐ[ℚ] F.field) := by
      calc
        NU.Chebotarev.frobeniusClassAt (K := ℚ) (L := F.field) W =
            NU.Chebotarev.frobeniusClassAt (K := ℚ) (L := F.field) P :=
          NU.Chebotarev.frobeniusClass_wellDefined q W P hWover hPq
        _ = _ := hclass
    have hfrob : NU.Chebotarev.arithFrobeniusAt
        (K := ℚ) (L := F.field) W = 1 := by
      have hc : IsConj (NU.Chebotarev.arithFrobeniusAt
          (K := ℚ) (L := F.field) W)
          (1 : F.field ≃ₐ[ℚ] F.field) :=
        ConjClasses.mk_eq_mk_iff_isConj.mp hclassW
      exact isConj_one_right.mp hc.symm
    constructor
    · rw [asymmetricAbsoluteRamificationIndex,
        ← Ideal.ramificationIdx_eq_ramificationIdx'
          q.asIdeal W.asIdeal q.ne_bot]
      have hu := (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
        W.ne_bot).mp hWu
      simpa [← hWover.over] using hu
    · rw [asymmetricAbsoluteResidueDegree,
        ← Ideal.inertiaDeg_eq_inertiaDeg' q.asIdeal W.asIdeal]
      have hord := NU.Chebotarev.arithFrobAt_order_eq_inertiaDeg W hWu
      rw [hfrob, orderOf_one, ← hWover.over] at hord
      exact hord.symm

private noncomputable def restrictFinitePlaceAlong
    (N E : NumberFieldInOmega) (hNE : N.field ≤ E.field)
    (P : NU.LocalTheory.FinitePlace E.field) :
    NU.LocalTheory.FinitePlace N.field := by
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion hNE).toRingHom.toAlgebra
  exact NU.LocalTheory.restrictFinitePlace N.field P

private theorem restrictSplitPrime
    (N E : NumberFieldInOmega) (hNE : N.field ≤ E.field)
    (q : NU.Chebotarev.PrimeIdeal ℚ)
    (P : NU.LocalTheory.FinitePlace E.field)
    (hPq : rationalPrime E P = q)
    (hPe : absoluteRamificationIndex E P = 1)
    (hPf : absoluteResidueDegree E P = 1) :
    ∃ v : NU.LocalTheory.FinitePlace N.field,
      restrictFinitePlaceAlong N E hNE P = v ∧
      rationalPrime N v = q ∧ absoluteRamificationIndex N v = 1 ∧
        absoluteResidueDegree N v = 1 := by
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion hNE).toRingHom.toAlgebra
  letI : IsScalarTower ℚ N.field E.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let v := restrictFinitePlaceAlong N E hNE P
  have hv_def : v = NU.LocalTheory.restrictFinitePlace N.field P := by
    apply HeightOneSpectrum.ext
    rfl
  have hPv : P.asIdeal.LiesOver v.asIdeal := ⟨by
    rw [hv_def, Ideal.under_def,
      ← NU.LocalTheory.restrictFinitePlace_asIdeal]⟩
  have hPqOver : P.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hPq]
    rfl⟩
  letI : P.asIdeal.LiesOver v.asIdeal := hPv
  have hvq : v.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def]
    calc
      q.asIdeal = Ideal.comap
          (algebraMap (NumberField.RingOfIntegers ℚ)
            (NumberField.RingOfIntegers E.field)) P.asIdeal :=
        hPqOver.over.trans
          (Ideal.under_def (NumberField.RingOfIntegers ℚ) P.asIdeal)
      _ = Ideal.comap
          (algebraMap (NumberField.RingOfIntegers ℚ)
            (NumberField.RingOfIntegers N.field))
          (Ideal.comap (algebraMap (NumberField.RingOfIntegers N.field)
            (NumberField.RingOfIntegers E.field)) P.asIdeal) := by
        rw [Ideal.comap_comap]
        congr 1
      _ = Ideal.comap
          (algebraMap (NumberField.RingOfIntegers ℚ)
            (NumberField.RingOfIntegers N.field)) v.asIdeal := by
        rw [hv_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal]⟩
  letI : v.asIdeal.LiesOver q.asIdeal := hvq
  letI := Localization.AtPrime.algebraOfLiesOver v.asIdeal P.asIdeal
  have heTower := Ideal.ramificationIdx'_tower'
    (R := 𝓞 ℚ) v.asIdeal P.asIdeal
  have hfTower := Ideal.inertiaDeg'_tower
    (R := 𝓞 ℚ) v.asIdeal P.asIdeal
  have hPoldE : P.asIdeal.ramificationIdx' (𝓞 ℚ) = 1 := hPe
  have hPoldF : P.asIdeal.inertiaDeg' (𝓞 ℚ) = 1 := hPf
  have hve : v.asIdeal.ramificationIdx' (𝓞 ℚ) = 1 := by
    rw [hPoldE] at heTower
    exact Nat.eq_one_of_dvd_one ⟨_, heTower⟩
  have hvf : v.asIdeal.inertiaDeg' (𝓞 ℚ) = 1 := by
    rw [hPoldF] at hfTower
    exact Nat.eq_one_of_dvd_one ⟨_, hfTower⟩
  refine ⟨v, rfl, ?_, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    exact hvq.over.symm
  · exact hve
  · exact hvf

private theorem splitsCompletelyAt_of_onePlace
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (q : NU.Chebotarev.PrimeIdeal ℚ)
    (v0 : NU.LocalTheory.FinitePlace N.field)
    (hvq : rationalPrime N v0 = q)
    (he : absoluteRamificationIndex N v0 = 1)
    (hf : absoluteResidueDegree N v0 = 1) :
    SplitsCompletelyAt N q := by
  refine ⟨⟨v0, hvq⟩, ?_⟩
  intro v hv
  have hv0over : v0.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hvq]
    rfl⟩
  have hvover : v.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hv]
    rfl⟩
  letI : v0.asIdeal.LiesOver q.asIdeal := hv0over
  letI : v.asIdeal.LiesOver q.asIdeal := hvover
  have heq_e : v0.asIdeal.ramificationIdx'
      (NumberField.RingOfIntegers ℚ) =
      v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup q.asIdeal
      v0.asIdeal v.asIdeal (N.field ≃ₐ[ℚ] N.field)
  have heq_f : v0.asIdeal.inertiaDeg'
      (NumberField.RingOfIntegers ℚ) =
      v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup q.asIdeal
      v0.asIdeal v.asIdeal (N.field ≃ₐ[ℚ] N.field)
  constructor
  · rw [asymmetricAbsoluteRamificationIndex, ← heq_e,
      ← asymmetricAbsoluteRamificationIndex]
    exact he
  · rw [asymmetricAbsoluteResidueDegree, ← heq_f,
      ← asymmetricAbsoluteResidueDegree]
    exact hf

private theorem splitPrimeOrbitLabel
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (q : NU.Chebotarev.PrimeIdeal ℚ) (hs : SplitsCompletelyAt N q)
    (v1 : NU.LocalTheory.FinitePlace N.field)
    (hv1q : rationalPrime N v1 = q) :
    ∃ v : (N.field ≃ₐ[ℚ] N.field) →
        NU.LocalTheory.FinitePlace N.field,
      (∀ g, rationalPrime N (v g) = q) ∧ Function.Injective v ∧
      (∀ w, rationalPrime N w = q → ∃ g, v g = w) ∧
      (∀ g, v g = NU.LocalTheory.conjugateFinitePlace ℚ g (v 1)) ∧
      v 1 = v1 := by
  let v : (N.field ≃ₐ[ℚ] N.field) →
      NU.LocalTheory.FinitePlace N.field :=
    fun g => NU.LocalTheory.conjugateFinitePlace ℚ g v1
  have hv1over : v1.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hv1q]
    rfl⟩
  letI : v1.asIdeal.LiesOver q.asIdeal := hv1over
  have hstabcard : Nat.card (MulAction.stabilizer
      (N.field ≃ₐ[ℚ] N.field) v1.asIdeal) = 1 := by
    rw [Ideal.card_stabilizer_eq q.asIdeal v1.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal v1.asIdeal
        (N.field ≃ₐ[ℚ] N.field),
      Ideal.inertiaDegIn_eq_inertiaDeg q.asIdeal v1.asIdeal
        (N.field ≃ₐ[ℚ] N.field),
      ← asymmetricAbsoluteRamificationIndex,
      ← asymmetricAbsoluteResidueDegree,
      (hs.2 v1 hv1q).1, (hs.2 v1 hv1q).2, one_mul]
  have hstab : MulAction.stabilizer
      (N.field ≃ₐ[ℚ] N.field) v1.asIdeal = ⊥ :=
    Subgroup.card_eq_one.mp hstabcard
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    apply HeightOneSpectrum.ext
    change (NU.LocalTheory.restrictFinitePlace ℚ
      (NU.LocalTheory.conjugateFinitePlace ℚ g v1)).asIdeal = q.asIdeal
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
      NU.LocalTheory.conjugateFinitePlace_asIdeal]
    change Ideal.under (NumberField.RingOfIntegers ℚ)
      (g • v1.asIdeal) = q.asIdeal
    rw [Ideal.under_smul, ← hv1over.over]
  · intro g h hgh
    have hideal : g • v1.asIdeal = h • v1.asIdeal := by
      simpa [v, NU.LocalTheory.conjugateFinitePlace_asIdeal] using
        congrArg HeightOneSpectrum.asIdeal hgh
    have hmem : h⁻¹ * g ∈ MulAction.stabilizer
        (N.field ≃ₐ[ℚ] N.field) v1.asIdeal := by
      change (h⁻¹ * g) • v1.asIdeal = v1.asIdeal
      rw [mul_smul, hideal, ← mul_smul, inv_mul_cancel, one_smul]
    rw [hstab, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  · intro w hwq
    have hwover : w.asIdeal.LiesOver q.asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
        ← hwq]
      rfl⟩
    letI : w.asIdeal.LiesOver q.asIdeal := hwover
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      q.asIdeal v1.asIdeal w.asIdeal (N.field ≃ₐ[ℚ] N.field)
    refine ⟨g, ?_⟩
    apply HeightOneSpectrum.ext
    change g • v1.asIdeal = w.asIdeal
    exact hg
  · intro g
    change NU.LocalTheory.conjugateFinitePlace ℚ g v1 =
      NU.LocalTheory.conjugateFinitePlace ℚ g
        (NU.LocalTheory.conjugateFinitePlace ℚ 1 v1)
    congr 1
    apply HeightOneSpectrum.ext
    simp [NU.LocalTheory.conjugateFinitePlace_asIdeal]
  · apply HeightOneSpectrum.ext
    simp [v, NU.LocalTheory.conjugateFinitePlace_asIdeal]

private theorem conjugatePlace_ne_of_split
    (F : NumberFieldInOmega) [IsGalois ℚ F.field]
    (q : NU.Chebotarev.PrimeIdeal ℚ) (hs : SplitsCompletelyAt F q)
    (P : NU.LocalTheory.FinitePlace F.field) (hPq : rationalPrime F P = q)
    (g : F.field ≃ₐ[ℚ] F.field) (hg : g ≠ 1) :
    NU.LocalTheory.conjugateFinitePlace ℚ g P ≠ P := by
  have hPover : P.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hPq]
    rfl⟩
  letI : P.asIdeal.LiesOver q.asIdeal := hPover
  have hcard : Nat.card (MulAction.stabilizer
      (F.field ≃ₐ[ℚ] F.field) P.asIdeal) = 1 := by
    rw [Ideal.card_stabilizer_eq q.asIdeal P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal P.asIdeal
        (F.field ≃ₐ[ℚ] F.field),
      Ideal.inertiaDegIn_eq_inertiaDeg q.asIdeal P.asIdeal
        (F.field ≃ₐ[ℚ] F.field),
      ← asymmetricAbsoluteRamificationIndex,
      ← asymmetricAbsoluteResidueDegree,
      (hs.2 P hPq).1, (hs.2 P hPq).2, one_mul]
  have hstab : MulAction.stabilizer
      (F.field ≃ₐ[ℚ] F.field) P.asIdeal = ⊥ :=
    Subgroup.card_eq_one.mp hcard
  intro heq
  have hmem : g ∈ MulAction.stabilizer
      (F.field ≃ₐ[ℚ] F.field) P.asIdeal := by
    change g • P.asIdeal = P.asIdeal
    rw [← NU.LocalTheory.conjugateFinitePlace_asIdeal]
    exact congrArg HeightOneSpectrum.asIdeal heq
  rw [hstab, Subgroup.mem_bot] at hmem
  exact hg hmem

set_option maxHeartbeats 1000000 in
private theorem asymmetricWeakApproximation
    (E : NumberFieldInOmega) (q : NU.Chebotarev.PrimeIdeal ℚ)
    (P : NU.LocalTheory.FinitePlace E.field)
    (hPq : rationalPrime E P = q) :
    ∃ x : NumberField.RingOfIntegers E.field,
      x ∈ P.asIdeal ∧ x ∉ P.asIdeal ^ 2 ∧
      ∀ Q : NU.LocalTheory.FinitePlace E.field,
        rationalPrime E Q = q → Q ≠ P → x - 1 ∈ Q.asIdeal := by
  classical
  have hPover : P.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hPq]
    rfl⟩
  let S : Set (Ideal (NumberField.RingOfIntegers E.field)) :=
    q.asIdeal.primesOver (NumberField.RingOfIntegers E.field)
  have hSfin : S.Finite := by
    dsimp [S]
    rw [← IsDedekindDomain.coe_primesOverFinset q.ne_bot
      (NumberField.RingOfIntegers E.field)]
    exact Finset.finite_toSet _
  letI : Fintype S := hSfin.fintype
  let Ps : S := ⟨P.asIdeal, P.isPrime, hPover⟩
  obtain ⟨t, htP, htP2⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot
      P.isPrime.ne_top 1
  have htP' : t ∈ P.asIdeal := by simpa using htP
  have htP2' : t ∉ P.asIdeal ^ 2 := by simpa using htP2
  let I : S → Ideal (NumberField.RingOfIntegers E.field) :=
    fun Q => Q.1 ^ 2
  let z : S → NumberField.RingOfIntegers E.field :=
    fun Q => if Q = Ps then t else 1
  have hmax (Q : S) : Q.1.IsMaximal :=
    Ideal.primesOver.isMaximal Q
  have hpair : Pairwise (Function.onFun IsCoprime I) := by
    intro Q R hQR
    change IsCoprime (I Q) (I R)
    have hne : Q.1 ≠ R.1 := by
      intro h
      exact hQR (Subtype.ext h)
    haveI : Q.1.IsMaximal := hmax Q
    haveI : R.1.IsMaximal := hmax R
    exact (Ideal.isCoprime_of_isMaximal hne).pow
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hpair z
  have hxP : x - t ∈ P.asIdeal ^ 2 := by
    simpa [I, z, Ps] using hx Ps
  have hxmem : x ∈ P.asIdeal := by
    have hsub : x - t ∈ P.asIdeal :=
      P.asIdeal.pow_le_self (by omega) hxP
    exact sub_add_cancel x t ▸ P.asIdeal.add_mem hsub htP'
  have hxnot : x ∉ P.asIdeal ^ 2 := by
    intro hx2
    apply htP2'
    have hneg : t - x ∈ P.asIdeal ^ 2 := by
      simpa only [neg_sub] using (P.asIdeal ^ 2).neg_mem hxP
    convert (P.asIdeal ^ 2).add_mem hneg hx2 using 1 <;> ring
  refine ⟨x, hxmem, hxnot, ?_⟩
  intro Q hQq hQP
  have hQover : Q.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hQq]
    rfl⟩
  let Qs : S := ⟨Q.asIdeal, Q.isPrime, hQover⟩
  have hQs : Qs ≠ Ps := by
    intro h
    apply hQP
    apply HeightOneSpectrum.ext
    exact congrArg Subtype.val h
  have hle : Q.asIdeal ^ 2 ≤ Q.asIdeal :=
    Ideal.pow_le_self (I := Q.asIdeal) (n := 2) (by norm_num)
  exact hle (by simpa [I, z, hQs] using hx Qs)

set_option maxHeartbeats 1000000 in
private theorem kummerRadicalRamifiedAt
    {E R : Type*} [Field E] [NumberField E] [Field R] [NumberField R]
    [Algebra E R] [FiniteDimensional E R]
    (p : NU.LocalTheory.OddPrime) (a0 : NumberField.RingOfIntegers E)
    (alpha : R)
    (hpow : alpha ^ (p : ℕ) = algebraMap E R (a0 : E))
    (hdegree : Module.finrank E R = (p : ℕ))
    (P : NU.LocalTheory.FinitePlace E) (k : ℕ)
    (hval : P.intValuation a0 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k) :
    ∃ W : NU.LocalTheory.FinitePlace R,
      NU.LocalTheory.restrictFinitePlace E W = P ∧
        1 < W.asIdeal.ramificationIdx' (NumberField.RingOfIntegers E) := by
  let A := NumberField.RingOfIntegers E
  let B := NumberField.RingOfIntegers R
  letI : NoZeroSMulDivisors A B := ⟨by
    intro c x h
    change algebraMap A B c * x = 0 at h
    rcases mul_eq_zero.mp h with hc | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_eq_zero_iff A B).mp hc)
    · exact Or.inr hx⟩
  obtain ⟨J, _, hJprime, hJcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B) (by
      intro x hx
      change algebraMap A B x = 0 at hx
      have hx0 : x = 0 :=
        (FaithfulSMul.algebraMap_eq_zero_iff A B).mp hx
      subst x
      exact P.asIdeal.zero_mem)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [← hJcomap, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact FaithfulSMul.algebraMap_eq_zero_iff A B
  let W : NU.LocalTheory.FinitePlace R := ⟨J, hJprime, hJ0⟩
  have hWover : W.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def]
    exact hJcomap.symm⟩
  letI : W.asIdeal.LiesOver P.asIdeal := hWover
  have hrestrict : NU.LocalTheory.restrictFinitePlace E W = P := by
    apply HeightOneSpectrum.ext
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
    exact hJcomap
  let e := P.asIdeal.ramificationIdx W.asIdeal
  have hlie := P.valuation_liesOver R W (a0 : E)
  have hvalfield : P.valuation E (a0 : E) = exp (-(k : ℤ)) := by
    rw [P.valuation_of_algebraMap, hval]
  have hlie' : (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
      (W.valuation R alpha) ^ (p : ℕ) := by
    calc
      (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
          (P.valuation E (a0 : E)) ^ e := by rw [hvalfield]
      _ = W.valuation R (algebraMap E R (a0 : E)) := hlie
      _ = W.valuation R (alpha ^ (p : ℕ)) :=
        congrArg (W.valuation R) hpow.symm
      _ = (W.valuation R alpha) ^ (p : ℕ) := map_pow _ _ _
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hlie'
  rw [log_pow, log_exp, log_pow, Int.nsmul_eq_mul] at hlog
  have hdZ : (p : ℤ) ∣ ((e : ℕ) : ℤ) * (k : ℤ) := by
    refine ⟨-(W.valuation R alpha).log, ?_⟩
    rw [Int.nsmul_eq_mul] at hlog
    linarith
  have hd : (p : ℕ) ∣ e * k := by exact_mod_cast hdZ
  have hpe : (p : ℕ) ∣ e := (p.1.2.dvd_mul.mp hd).resolve_right hk
  have hepos : 0 < e :=
    Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
        W.asIdeal P.ne_bot)
  have hple : (p : ℕ) ≤ e := Nat.le_of_dvd hepos hpe
  have hele : e ≤ (p : ℕ) := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank B E R W.asIdeal
  have heq : e = (p : ℕ) := Nat.le_antisymm hele hple
  refine ⟨W, hrestrict, ?_⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx'
    P.asIdeal W.asIdeal P.ne_bot,
    show P.asIdeal.ramificationIdx W.asIdeal = e from rfl, heq]
  exact p.1.2.one_lt

/-! ### Rung A: an asymmetric projected Kummer element -/

/-- Restriction from the cyclotomic compositum, with its canonical inclusion
made explicit rather than left to instance search. -/
private noncomputable def restrictCyclotomicPlace
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (P : NU.LocalTheory.FinitePlace (cyclotomicCompositum N p).field) :
    NU.LocalTheory.FinitePlace N.field := by
  letI : Algebra N.field (cyclotomicCompositum N p).field :=
    (IntermediateField.inclusion
      (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
  exact NU.LocalTheory.restrictFinitePlace N.field P

/-- The completely split auxiliary prime, a prime above its identity-labelled
base place, and the simply transitive labelling of all base places. -/
private structure AsymmetricPrimeData
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) where
  q : NU.Chebotarev.PrimeIdeal ℚ
  norm_ne : NU.Chebotarev.PrimeIdeal.norm q ≠ (p : ℕ)
  splitCyclotomic : SplitsCompletelyAt (cyclotomicCompositum N p) q
  splitBase : SplitsCompletelyAt N q
  P : NU.LocalTheory.FinitePlace (cyclotomicCompositum N p).field
  P_over_q : rationalPrime (cyclotomicCompositum N p) P = q
  v : (N.field ≃ₐ[ℚ] N.field) → NU.LocalTheory.FinitePlace N.field
  v_over_q : ∀ g, rationalPrime N (v g) = q
  v_injective : Function.Injective v
  v_surjective : ∀ w, rationalPrime N w = q → ∃ g, v g = w
  v_conjugate :
    ∀ g, v g = NU.LocalTheory.conjugateFinitePlace ℚ g (v 1)
  P_over_identity : restrictCyclotomicPlace N p P = v 1

/-- Chebotarev and the orbit calculation supply the prime package. -/
private theorem asymmetricPrimeData_exists
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    Nonempty (AsymmetricPrimeData N p) := by
  let E := cyclotomicCompositum N p
  letI : IsGalois ℚ E.field := cyclotomicCompositum_isGaloisOverQ N p
  obtain ⟨q, hqne, hqFrob⟩ :=
    existsIdentityFrobeniusPrimeAway E (p : ℕ)
  have hsplitE : SplitsCompletelyAt E q :=
    splitsCompletelyAt_of_identityFrobenius E q hqFrob
  obtain ⟨P, hPq⟩ := hsplitE.1
  have hPsplit := hsplitE.2 P hPq
  obtain ⟨v1, hPv1, hv1q, hv1e, hv1f⟩ :=
    restrictSplitPrime N E (le_cyclotomicCompositum N p) q P hPq
      hPsplit.1 hPsplit.2
  have hsplitN : SplitsCompletelyAt N q :=
    splitsCompletelyAt_of_onePlace N q v1 hv1q hv1e hv1f
  obtain ⟨v, hvq, hvInjective, hvSurjective, hvConjugate, hvOne⟩ :=
    splitPrimeOrbitLabel N q hsplitN v1 hv1q
  have hrestrict : restrictCyclotomicPlace N p P = v1 := by
    calc
      restrictCyclotomicPlace N p P =
          restrictFinitePlaceAlong N E
            (le_cyclotomicCompositum N p) P := by
        apply HeightOneSpectrum.ext
        rfl
      _ = v1 := hPv1
  exact ⟨{
    q := q
    norm_ne := hqne
    splitCyclotomic := hsplitE
    splitBase := hsplitN
    P := P
    P_over_q := hPq
    v := v
    v_over_q := hvq
    v_injective := hvInjective
    v_surjective := hvSurjective
    v_conjugate := hvConjugate
    P_over_identity := hrestrict.trans hvOne.symm }⟩

/-- Integral weak-approximation data before applying the cyclotomic
projector. -/
private structure AsymmetricApproximationData
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p) where
  integer : NumberField.RingOfIntegers (cyclotomicCompositum N p).field
  mem_identity : integer ∈ D.P.asIdeal
  not_mem_identity_sq : integer ∉ D.P.asIdeal ^ 2
  one_mod_other :
    ∀ Q : NU.LocalTheory.FinitePlace (cyclotomicCompositum N p).field,
      rationalPrime (cyclotomicCompositum N p) Q = D.q → Q ≠ D.P →
        integer - 1 ∈ Q.asIdeal

private theorem AsymmetricApproximationData.integer_ne_zero
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D) :
    (A.integer : (cyclotomicCompositum N p).field) ≠ 0 := by
  intro hzero
  apply A.not_mem_identity_sq
  have hzero' : A.integer = 0 := by
    apply Subtype.ext
    exact hzero
  rw [hzero']
  exact (D.P.asIdeal ^ 2).zero_mem

/-- The weak-approximation integer as a field unit. -/
private def AsymmetricApproximationData.unit
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D) :
    (cyclotomicCompositum N p).fieldˣ :=
  Units.mk0 A.integer A.integer_ne_zero

/-- Chinese remaindering gives valuation one at `P` and principal-unit
congruences at every other place over `q`. -/
private theorem asymmetricApproximationData_exists
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p) :
    Nonempty (AsymmetricApproximationData D) := by
  obtain ⟨x, hxP, hxP2, hxOther⟩ :=
    asymmetricWeakApproximation (cyclotomicCompositum N p) D.q D.P
      D.P_over_q
  exact ⟨{
    integer := x
    mem_identity := hxP
    not_mem_identity_sq := hxP2
    one_mod_other := hxOther }⟩

/-- A representative-level version of the cyclotomic Kummer projection. -/
private noncomputable def projectedKummerRepresentative
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (b : (cyclotomicCompositum N p).fieldˣ) :
    (cyclotomicCompositum N p).fieldˣ := by
  letI := Fintype.ofFinite (CyclotomicDelta N p)
  exact ∏ delta : CyclotomicDelta N p,
    (Units.map delta.1.toRingEquiv.toMonoidHom b) ^
      ((cyclotomicKummerProjector N p).coeff delta).val

/-- The explicit representative has exactly the projected Kummer class. -/
private theorem projectedKummerRepresentative_class
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (b : (cyclotomicCompositum N p).fieldˣ) :
    QuotientGroup.mk (projectedKummerRepresentative N p b) =
      projectedKummerClass N p (QuotientGroup.mk b) := by
  classical
  let E := cyclotomicCompositum N p
  let D := CyclotomicDelta N p
  letI := Fintype.ofFinite D
  let u : D → E.fieldˣ := fun delta =>
    Units.map delta.1.toRingEquiv.toMonoidHom b
  let n : D → ℕ := fun delta =>
    ((cyclotomicKummerProjector N p).coeff delta).val
  have hrepresentative :
      projectedKummerRepresentative N p b = ∏ delta : D, u delta ^ n delta :=
    rfl
  rw [projectedKummerClass_apply, hrepresentative]
  calc
    (QuotientGroup.mk (∏ delta : D, u delta ^ n delta) :
        KummerClass E (p : ℕ)) =
        ∏ delta : D,
          (QuotientGroup.mk (u delta ^ n delta) :
            KummerClass E (p : ℕ)) := by
      simpa using
        (map_prod (QuotientGroup.mk' (pthPowerSubgroup E (p : ℕ)))
          (fun delta : D => u delta ^ n delta) Finset.univ)
    _ = ∏ delta : D,
        (kummerAction N p delta (QuotientGroup.mk b)) ^ n delta := by
      apply Finset.prod_congr rfl
      intro delta _
      rw [QuotientGroup.mk_pow, kummerAction_mk]
    _ = ∏ delta : D,
        (kummerAction N p delta (QuotientGroup.mk b)) ^
          ((cyclotomicKummerProjector N p).coeff delta).val := by
      rfl

/-- A normalized projected element.  The source is a power of the weak
approximation unit, its projected class is represented by `a`, and `a` has
exactly valuation one at the identity place. -/
private structure AsymmetricProjectedKummerData
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D) where
  exponent : ℕ
  exponent_ne_zero : ¬(p : ℕ) ∣ exponent
  b : (cyclotomicCompositum N p).fieldˣ
  b_eq : b = A.unit ^ exponent
  a : (cyclotomicCompositum N p).fieldˣ
  class_eq :
    (QuotientGroup.mk a :
      KummerClass (cyclotomicCompositum N p) (p : ℕ)) =
        projectedKummerClass N p (QuotientGroup.mk b)
  valuation_one :
    D.P.valuation (cyclotomicCompositum N p).field a.1 = exp (-1)

private theorem AsymmetricApproximationData.unit_valuation
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D) :
    D.P.valuation (cyclotomicCompositum N p).field A.unit.1 = exp (-1) := by
  let m := multiplicity D.P.asIdeal (Ideal.span {A.integer})
  have hinteger_ne : A.integer ≠ 0 := by
    intro hzero
    apply A.integer_ne_zero
    exact congrArg (fun z : NumberField.RingOfIntegers
      (cyclotomicCompositum N p).field =>
        (z : (cyclotomicCompositum N p).field)) hzero
  have hv : D.P.intValuation A.integer = exp (-(m : ℤ)) := by
    exact D.P.intValuation_eq_exp_neg_multiplicity hinteger_ne
  have hm_lower : 1 ≤ m := by
    have hmem : A.integer ∈ D.P.asIdeal ^ 1 := by
      simpa only [pow_one] using A.mem_identity
    have hle : D.P.intValuation A.integer ≤ exp (-(1 : ℤ)) :=
      (D.P.intValuation_le_pow_iff_mem A.integer 1).mpr hmem
    rw [hv] at hle
    have hneg : -(m : ℤ) ≤ -(1 : ℤ) := WithZero.exp_le_exp.mp hle
    omega
  have hm_upper : m < 2 := by
    have hnle : ¬D.P.intValuation A.integer ≤ exp (-(2 : ℤ)) := by
      intro hle
      exact A.not_mem_identity_sq
        ((D.P.intValuation_le_pow_iff_mem A.integer 2).mp hle)
    have hlt : exp (-(2 : ℤ)) < D.P.intValuation A.integer :=
      lt_of_not_ge hnle
    rw [hv] at hlt
    have hneg : -(2 : ℤ) < -(m : ℤ) := WithZero.exp_lt_exp.mp hlt
    omega
  have hm : m = 1 := by omega
  calc
    D.P.valuation (cyclotomicCompositum N p).field A.unit.1 =
        D.P.intValuation A.integer := by
      exact D.P.valuation_of_algebraMap A.integer
    _ = exp (-1) := by
      rw [hv, hm]
      norm_num

private theorem AsymmetricApproximationData.conjugate_unit_valuation
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D) (delta : CyclotomicDelta N p)
    (hdelta : delta ≠ 1) :
    D.P.valuation (cyclotomicCompositum N p).field
      (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1 = 1 := by
  let E := cyclotomicCompositum N p
  letI : IsGalois ℚ E.field := cyclotomicCompositum_isGaloisOverQ N p
  let sigma : E.field ≃ₐ[ℚ] E.field := delta.1
  have hsigma : sigma ≠ 1 := by
    intro h
    apply hdelta
    apply Subtype.ext
    exact h
  have hsymm : sigma.symm ≠ 1 := by
    exact inv_ne_one.mpr hsigma
  let Q := NU.LocalTheory.conjugateFinitePlace ℚ sigma.symm D.P
  have hPover : D.P.asIdeal.LiesOver D.q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← D.P_over_q]
    rfl⟩
  have hQq : rationalPrime E Q = D.q := by
    apply HeightOneSpectrum.ext
    rw [rationalPrime, NU.LocalTheory.restrictFinitePlace_asIdeal,
      NU.LocalTheory.conjugateFinitePlace_asIdeal]
    have hunder : Ideal.under (NumberField.RingOfIntegers ℚ)
        (sigma.symm • D.P.asIdeal) =
        Ideal.under (NumberField.RingOfIntegers ℚ) D.P.asIdeal :=
      Ideal.under_smul (NumberField.RingOfIntegers ℚ) D.P.asIdeal sigma.symm
    exact hunder.trans hPover.over.symm
  have hQne : Q ≠ D.P :=
    conjugatePlace_ne_of_split E D.q D.splitCyclotomic D.P D.P_over_q
      sigma.symm hsymm
  have hmodQ : A.integer - 1 ∈ Q.asIdeal :=
    A.one_mod_other Q hQq hQne
  have hmodP : sigma • A.integer - 1 ∈ D.P.asIdeal := by
    rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hmodQ
    have hinv : sigma.symm⁻¹ = sigma := inv_inv sigma
    rw [hinv] at hmodQ
    simpa only [smul_sub, smul_one] using hmodQ
  have hnotmem : sigma • A.integer ∉ D.P.asIdeal := by
    intro hmem
    have hone : (1 : NumberField.RingOfIntegers E.field) ∈ D.P.asIdeal := by
      convert D.P.asIdeal.sub_mem hmem hmodP using 1 <;> ring
    exact D.P.isPrime.ne_top
      ((Ideal.eq_top_iff_one D.P.asIdeal).2 hone)
  have hint : D.P.intValuation (sigma • A.integer) = 1 :=
    D.P.intValuation_eq_one_iff.mpr hnotmem
  calc
    D.P.valuation E.field
        (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1 =
        D.P.valuation E.field
          ((sigma • A.integer : NumberField.RingOfIntegers E.field) :
            E.field) := by
      congr 1
    _ = D.P.intValuation (sigma • A.integer) :=
      D.P.valuation_of_algebraMap (sigma • A.integer)
    _ = 1 := hint

private theorem projectedKummerRepresentative_valuation
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p)
    (A : AsymmetricApproximationData D) :
    D.P.valuation (cyclotomicCompositum N p).field
        (projectedKummerRepresentative N p A.unit).1 =
      exp (-(((cyclotomicKummerProjector N p).coeff
        (1 : CyclotomicDelta N p)).val : ℤ)) := by
  classical
  letI := Fintype.ofFinite (CyclotomicDelta N p)
  let c := ((cyclotomicKummerProjector N p).coeff
    (1 : CyclotomicDelta N p)).val
  have hone : D.P.valuation (cyclotomicCompositum N p).field
      (Units.map (1 : CyclotomicDelta N p).1.toRingEquiv.toMonoidHom
        A.unit).1 = exp (-1) := by
    simpa using A.unit_valuation
  have hprod :
      ∏ delta : CyclotomicDelta N p,
        (D.P.valuation (cyclotomicCompositum N p).field
          (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1) ^
            ((cyclotomicKummerProjector N p).coeff delta).val =
        (D.P.valuation (cyclotomicCompositum N p).field
          (Units.map (1 : CyclotomicDelta N p).1.toRingEquiv.toMonoidHom
            A.unit).1) ^ c := by
    apply Finset.prod_eq_single (1 : CyclotomicDelta N p)
    · intro delta _ hdelta
      rw [A.conjugate_unit_valuation delta hdelta]
      exact one_pow _
    · intro honeNotMem
      exact (honeNotMem (Finset.mem_univ 1)).elim
  let u : CyclotomicDelta N p →
      (cyclotomicCompositum N p).fieldˣ := fun delta =>
    (Units.map delta.1.toRingEquiv.toMonoidHom A.unit) ^
      ((cyclotomicKummerProjector N p).coeff delta).val
  have hrepresentative : projectedKummerRepresentative N p A.unit =
      ∏ delta : CyclotomicDelta N p, u delta := rfl
  have hmapProd :
      D.P.valuation (cyclotomicCompositum N p).field
          (∏ delta : CyclotomicDelta N p, u delta).1 =
        ∏ delta : CyclotomicDelta N p,
          D.P.valuation (cyclotomicCompositum N p).field (u delta).1 := by
    have hcoe :
        (∏ delta : CyclotomicDelta N p, u delta).1 =
          ∏ delta : CyclotomicDelta N p, (u delta).1 := by
      exact map_prod
        (Units.coeHom (cyclotomicCompositum N p).field) u Finset.univ
    rw [hcoe]
    exact map_prod (D.P.valuation (cyclotomicCompositum N p).field)
      (fun delta : CyclotomicDelta N p => (u delta).1) Finset.univ
  calc
    D.P.valuation (cyclotomicCompositum N p).field
        (projectedKummerRepresentative N p A.unit).1 =
        D.P.valuation (cyclotomicCompositum N p).field
          (∏ delta : CyclotomicDelta N p, u delta).1 :=
      congrArg (D.P.valuation (cyclotomicCompositum N p).field)
        (congrArg Units.val hrepresentative)
    _ = ∏ delta : CyclotomicDelta N p,
          D.P.valuation (cyclotomicCompositum N p).field (u delta).1 :=
      hmapProd
    _ = ∏ delta : CyclotomicDelta N p,
          (D.P.valuation (cyclotomicCompositum N p).field
            (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1) ^
              ((cyclotomicKummerProjector N p).coeff delta).val := by
      apply Finset.prod_congr rfl
      intro delta _
      exact map_pow (D.P.valuation (cyclotomicCompositum N p).field)
        (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1 _
    _ = (exp (-1 : ℤ) : ℤᵐ⁰) ^ c := by rw [hprod, hone]
    _ = exp (-(c : ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

/-- Identity-place rung: rescale the projector by a nonzero scalar and then
by a global `p`-th power so that the represented eigenclass has valuation
exactly one. -/
private theorem asymmetricProjectedKummerData_exists
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p)
    (A : AsymmetricApproximationData D) :
    Nonempty (AsymmetricProjectedKummerData A) := by
  classical
  letI : NeZero (p : ℕ) := ⟨p.1.2.ne_zero⟩
  let E := cyclotomicCompositum N p
  let coeff : ZMod (p : ℕ) :=
    (cyclotomicKummerProjector N p).coeff (1 : CyclotomicDelta N p)
  let c : ℕ := coeff.val
  have hcoeff : coeff ≠ 0 := by
    dsimp [coeff]
    rw [cyclotomicKummerProjector_apply]
    simpa using inv_ne_zero
      (cyclotomicDelta_card_ne_zero_mod_p N p)
  let inverseCoeff : ZMod (p : ℕ) := coeff⁻¹
  let s : ℕ := inverseCoeff.val
  have hinverseCoeff : inverseCoeff ≠ 0 := inv_ne_zero hcoeff
  have hspos : 0 < s := ZMod.val_pos.mpr hinverseCoeff
  have hslt : s < (p : ℕ) := ZMod.val_lt inverseCoeff
  have hsNotDvd : ¬(p : ℕ) ∣ s :=
    Nat.not_dvd_of_pos_of_lt hspos hslt
  have hcast : (↑(c * s) : ZMod (p : ℕ)) = (1 : ZMod (p : ℕ)) := by
    calc
      (↑(c * s) : ZMod (p : ℕ)) = (c : ZMod (p : ℕ)) *
          (s : ZMod (p : ℕ)) := by rw [Nat.cast_mul]
      _ = coeff * inverseCoeff := by
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = 1 := mul_inv_cancel₀ hcoeff
  have hmodEq : c * s ≡ 1 [MOD (p : ℕ)] :=
    (ZMod.natCast_eq_natCast_iff (c * s) 1 (p : ℕ)).mp (by
      simpa using hcast)
  have hmod : (c * s) % (p : ℕ) = 1 :=
    Nat.mod_eq_of_modEq hmodEq p.1.2.one_lt
  let m : ℕ := (c * s) / (p : ℕ)
  have hdecomp : c * s = 1 + (p : ℕ) * m := by
    calc
      c * s = (c * s) % (p : ℕ) + (p : ℕ) * m :=
        (Nat.mod_add_div (c * s) (p : ℕ)).symm
      _ = 1 + (p : ℕ) * m := by rw [hmod]
  let b : E.fieldˣ := A.unit ^ s
  let r : E.fieldˣ := projectedKummerRepresentative N p b
  let correction : E.fieldˣ := A.unit⁻¹ ^ m
  let a : E.fieldˣ := r * correction ^ (p : ℕ)
  letI := Fintype.ofFinite (CyclotomicDelta N p)
  have hrepresentativePower :
      projectedKummerRepresentative N p b =
        projectedKummerRepresentative N p A.unit ^ s := by
    let n : CyclotomicDelta N p → ℕ := fun delta =>
      ((cyclotomicKummerProjector N p).coeff delta).val
    calc
      projectedKummerRepresentative N p b =
          ∏ delta : CyclotomicDelta N p,
            (Units.map delta.1.toRingEquiv.toMonoidHom b) ^ n delta := rfl
      _ = ∏ delta : CyclotomicDelta N p,
          ((Units.map delta.1.toRingEquiv.toMonoidHom A.unit) ^
            n delta) ^ s := by
        apply Finset.prod_congr rfl
        intro delta _
        dsimp [b]
        rw [map_pow, ← pow_mul, ← pow_mul, Nat.mul_comm s (n delta)]
      _ = (∏ delta : CyclotomicDelta N p,
          (Units.map delta.1.toRingEquiv.toMonoidHom A.unit) ^
            n delta) ^ s := Finset.prod_pow Finset.univ s _
      _ = projectedKummerRepresentative N p A.unit ^ s := rfl
  have hvalr : D.P.valuation E.field r.1 =
      exp (-((c * s : ℕ) : ℤ)) := by
    calc
      D.P.valuation E.field r.1 =
          D.P.valuation E.field
            (projectedKummerRepresentative N p A.unit ^ s).1 := by
        exact congrArg (D.P.valuation E.field)
          (congrArg Units.val hrepresentativePower)
      _ = (D.P.valuation E.field
          (projectedKummerRepresentative N p A.unit).1) ^ s :=
        map_pow (D.P.valuation E.field)
          (projectedKummerRepresentative N p A.unit).1 s
      _ = (exp (-(c : ℤ)) : ℤᵐ⁰) ^ s := by
        rw [projectedKummerRepresentative_valuation D A]
      _ = exp (-((c * s : ℕ) : ℤ)) := by
        rw [← WithZero.exp_nsmul]
        congr 1
        push_cast
        ring
  have hvalCorrection : D.P.valuation E.field correction.1 =
      exp (m : ℤ) := by
    calc
      D.P.valuation E.field correction.1 =
          (D.P.valuation E.field A.unit⁻¹.1) ^ m :=
        map_pow (D.P.valuation E.field) A.unit⁻¹.1 m
      _ = ((D.P.valuation E.field A.unit.1)⁻¹) ^ m := by
        have hcoeInv : A.unit⁻¹.1 = (A.unit.1)⁻¹ := by rfl
        rw [hcoeInv, map_inv₀]
      _ = ((exp (-1 : ℤ) : ℤᵐ⁰)⁻¹) ^ m := by
        rw [A.unit_valuation]
      _ = (exp (1 : ℤ) : ℤᵐ⁰) ^ m := by
        congr 1
      _ = exp (m : ℤ) := by
        rw [← WithZero.exp_nsmul]
        congr 1
        simp
  have hclass : (QuotientGroup.mk a : KummerClass E (p : ℕ)) =
      projectedKummerClass N p (QuotientGroup.mk b) := by
    have hcorrection :
        (QuotientGroup.mk (correction ^ (p : ℕ)) :
          KummerClass E (p : ℕ)) = 1 := by
      apply (QuotientGroup.eq_one_iff (correction ^ (p : ℕ))).mpr
      exact ⟨correction, rfl⟩
    calc
      (QuotientGroup.mk a : KummerClass E (p : ℕ)) =
          QuotientGroup.mk r * QuotientGroup.mk (correction ^ (p : ℕ)) := by
        exact QuotientGroup.mk_mul (pthPowerSubgroup E (p : ℕ))
          r (correction ^ (p : ℕ))
      _ = QuotientGroup.mk r := by rw [hcorrection, mul_one]
      _ = projectedKummerClass N p (QuotientGroup.mk b) :=
        projectedKummerRepresentative_class N p b
  have hvala : D.P.valuation E.field a.1 = exp (-1) := by
    have hcoeMul : a.1 = r.1 * (correction ^ (p : ℕ)).1 := by rfl
    have hcoePow : (correction ^ (p : ℕ)).1 =
        correction.1 ^ (p : ℕ) := by
      exact map_pow (Units.coeHom E.field) correction (p : ℕ)
    calc
      D.P.valuation E.field a.1 =
          D.P.valuation E.field r.1 *
            (D.P.valuation E.field correction.1) ^ (p : ℕ) := by
        rw [hcoeMul, map_mul, hcoePow, map_pow]
      _ = exp (-((c * s : ℕ) : ℤ)) *
          (exp (m : ℤ) : ℤᵐ⁰) ^ (p : ℕ) := by
        rw [hvalr, hvalCorrection]
      _ = exp (-((c * s : ℕ) : ℤ) + ((p : ℕ) : ℤ) * (m : ℤ)) := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
      _ = exp (-1) := by
        congr 1
        rw [hdecomp]
        push_cast
        ring
  exact ⟨{
    exponent := s
    exponent_ne_zero := hsNotDvd
    b := b
    b_eq := rfl
    a := a
    class_eq := hclass
    valuation_one := hvala }⟩

/-- A field element is a `p`-th power in the completion at `P`. -/
private def IsLocalPthPowerAt
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) : Prop :=
  ∃ x : P.adicCompletion E.field,
    x ^ (p : ℕ) = algebraMap E.field (P.adicCompletion E.field) a.1

/-- Valuation nondivisibility prevents a Kummer class from being trivial. -/
private theorem kummerClass_ne_one_of_valuation_not_dvd
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) (k : ℕ)
    (hval : P.valuation E.field a.1 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k) :
    (QuotientGroup.mk a : KummerClass E (p : ℕ)) ≠ 1 := by
  intro htrivial
  have hmem : a ∈ pthPowerSubgroup E (p : ℕ) :=
    (QuotientGroup.eq_one_iff a).mp htrivial
  obtain ⟨u, hu⟩ := hmem
  have hvpow : (P.valuation E.field u.1) ^ (p : ℕ) =
      exp (-(k : ℤ)) := by
    calc
      (P.valuation E.field u.1) ^ (p : ℕ) =
          P.valuation E.field (u.1 ^ (p : ℕ)) :=
        (map_pow (P.valuation E.field) u.1 (p : ℕ)).symm
      _ = P.valuation E.field a.1 := by
        exact congrArg (P.valuation E.field) (congrArg Units.val hu)
      _ = exp (-(k : ℤ)) := hval
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hvpow
  rw [log_pow, log_exp, Int.nsmul_eq_mul] at hlog
  have hdZ : (p : ℤ) ∣ (k : ℤ) := by
    refine ⟨-(P.valuation E.field u.1).log, ?_⟩
    linarith
  have hd : (p : ℕ) ∣ k := by
    exact_mod_cast hdZ
  exact hk hd

/-! ### Rung B: tame local Kummer criteria -/

/-- The radical field, bundled as an extension of its Kummer base. -/
private noncomputable def radicalNumberFieldExtension
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) : NumberFieldExtension E := by
  letI : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsIntegral ℚ Omega := Algebra.IsAlgebraic.isIntegral
  let A := IntermediateField.adjoin ℚ
    ({radicalRoot E p a} : Set Omega)
  letI : FiniteDimensional ℚ A :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (radicalRoot E p a))
  exact {
    field := {
      field := radicalExtension E p a
      finite := IntermediateField.finiteDimensional_sup E.field A }
    le_base := le_sup_left }

private theorem radicalNumberFieldExtension_finrank_of_not_isPow
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ)
    (hnotpow : ∀ b : E.field, b ^ (p : ℕ) ≠ a.1) :
    Module.finrank E.field
      (radicalNumberFieldExtension E p a).field.field = (p : ℕ) := by
  let alpha : Omega := radicalRoot E p a
  let R := radicalNumberFieldExtension E p a
  let R0 : IntermediateField E.field Omega :=
    IntermediateField.adjoin E.field {alpha}
  have hR0 : R0.restrictScalars ℚ = R.field.field := by
    calc
      R0.restrictScalars ℚ =
          E.field ⊔ IntermediateField.adjoin ℚ {alpha} :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ E.field {alpha}
      _ = R.field.field := rfl
  let e : R.field.field ≃ₐ[E.field] R0 :=
    { toFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ R0.restrictScalars ℚ := by
            rw [hR0]
            exact x.2
          exact hx⟩
      invFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ R0.restrictScalars ℚ := x.2
          rw [hR0] at hx
          exact hx⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => by apply Subtype.ext; rfl }
  let alpha0 : R0 := ⟨alpha,
    IntermediateField.subset_adjoin E.field {alpha}
      (Set.mem_singleton alpha)⟩
  have halpha : alpha0 ^ (p : ℕ) = algebraMap E.field R0 a.1 := by
    apply Subtype.ext
    exact radicalRoot_spec E p a
  let f : Polynomial E.field :=
    Polynomial.X ^ (p : ℕ) - Polynomial.C a.1
  have hirr : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime p.1.2 hnotpow
  have hroot : Polynomial.aeval alpha0 f = 0 := by
    rw [Polynomial.aeval_def,
      show f = Polynomial.X ^ (p : ℕ) - Polynomial.C a.1 from rfl,
      Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, halpha, sub_self]
  have hfmonic : f.Monic :=
    Polynomial.monic_X_pow_sub_C a.1 p.1.2.ne_zero
  have halphaIntegral : IsIntegral E.field alpha0 :=
    ⟨f, hfmonic, hroot⟩
  have hmin : f = minpoly E.field alpha0 :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hfmonic
  have hgen : IntermediateField.adjoin E.field {alpha0} = ⊤ := by
    apply (IntermediateField.lift_injective R0)
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have himage : Subtype.val '' ({alpha0} : Set R0) =
        ({alpha} : Set Omega) := by
      ext x
      simp [alpha0]
    rw [himage]
  calc
    Module.finrank E.field R.field.field = Module.finrank E.field R0 :=
      e.toLinearEquiv.finrank_eq
    _ = Module.finrank E.field
        (IntermediateField.adjoin E.field {alpha0}) := by
      rw [hgen]
      exact IntermediateField.finrank_top'.symm
    _ = (minpoly E.field alpha0).natDegree :=
      IntermediateField.adjoin.finrank halphaIntegral
    _ = f.natDegree := congrArg Polynomial.natDegree hmin.symm
    _ = (p : ℕ) := Polynomial.natDegree_X_pow_sub_C

set_option maxHeartbeats 1000000 in
-- The ideal-over-prime construction and two valuation logarithms need room.
private theorem kummerRadicalFieldRamifiedAt
    {E R : Type*} [Field E] [NumberField E] [Field R] [NumberField R]
    [Algebra E R] [FiniteDimensional E R]
    (p : NU.LocalTheory.OddPrime) (a : E) (alpha : R)
    (hpow : alpha ^ (p : ℕ) = algebraMap E R a)
    (hdegree : Module.finrank E R = (p : ℕ))
    (P : NU.LocalTheory.FinitePlace E) (k : ℕ)
    (hval : P.valuation E a = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k) :
    ∃ W : NU.LocalTheory.FinitePlace R,
      NU.LocalTheory.restrictFinitePlace E W = P ∧
        1 < W.asIdeal.ramificationIdx' (NumberField.RingOfIntegers E) := by
  let A := NumberField.RingOfIntegers E
  let B := NumberField.RingOfIntegers R
  letI : NoZeroSMulDivisors A B := ⟨by
    intro c x h
    have hzero : algebraMap A B c * x = 0 := h
    rcases mul_eq_zero.mp hzero with hc | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_eq_zero_iff A B).mp hc)
    · exact Or.inr hx⟩
  obtain ⟨J, _, hJprime, hJcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B) (by
      intro x hx
      have hxmap : algebraMap A B x = 0 := hx
      have hx0 : x = 0 :=
        (FaithfulSMul.algebraMap_eq_zero_iff A B).mp hxmap
      subst x
      exact P.asIdeal.zero_mem)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [← hJcomap, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact FaithfulSMul.algebraMap_eq_zero_iff A B
  let W : NU.LocalTheory.FinitePlace R := ⟨J, hJprime, hJ0⟩
  have hWover : W.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def]
    exact hJcomap.symm⟩
  letI : W.asIdeal.LiesOver P.asIdeal := hWover
  have hrestrict : NU.LocalTheory.restrictFinitePlace E W = P := by
    apply HeightOneSpectrum.ext
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
    exact hJcomap
  let e := P.asIdeal.ramificationIdx W.asIdeal
  have hlie := P.valuation_liesOver R W a
  have hlie' : (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
      (W.valuation R alpha) ^ (p : ℕ) := by
    calc
      (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
          (P.valuation E a) ^ e := by rw [hval]
      _ = W.valuation R (algebraMap E R a) := hlie
      _ = W.valuation R (alpha ^ (p : ℕ)) :=
        congrArg (W.valuation R) hpow.symm
      _ = (W.valuation R alpha) ^ (p : ℕ) := map_pow _ _ _
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hlie'
  rw [log_pow, log_exp, log_pow, Int.nsmul_eq_mul] at hlog
  have hdZ : (p : ℤ) ∣ ((e : ℕ) : ℤ) * (k : ℤ) := by
    refine ⟨-(W.valuation R alpha).log, ?_⟩
    rw [Int.nsmul_eq_mul] at hlog
    linarith
  have hd : (p : ℕ) ∣ e * k := by exact_mod_cast hdZ
  have hpe : (p : ℕ) ∣ e := (p.1.2.dvd_mul.mp hd).resolve_right hk
  have hepos : 0 < e :=
    Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
        W.asIdeal P.ne_bot)
  have hple : (p : ℕ) ≤ e := Nat.le_of_dvd hepos hpe
  have hele : e ≤ (p : ℕ) := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank B E R W.asIdeal
  have heq : e = (p : ℕ) := Nat.le_antisymm hele hple
  refine ⟨W, hrestrict, ?_⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx'
    P.asIdeal W.asIdeal P.ne_bot,
    show P.asIdeal.ramificationIdx W.asIdeal = e from rfl, heq]
  exact p.1.2.one_lt

/-- Ramification is tame when every relative ramification index is coprime
to the residue characteristic. -/
private def IsTamelyRamifiedAt
    {E : NumberFieldInOmega} (R : NumberFieldExtension E)
    (P : NU.LocalTheory.FinitePlace E.field) : Prop :=
  ∀ W : NU.LocalTheory.FinitePlace R.field.field,
    NU.LocalTheory.restrictFinitePlace E.field W = P →
      Nat.Coprime (relativeRamificationIndex R P W)
        (NU.LocalTheory.residueCharacteristic P)

/-- The valuation criterion ramifies the degree-`p` radical at the identity
place. -/
private theorem tameKummerRadical_ramified
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) (k : ℕ)
    (hval : P.valuation E.field a.1 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k) :
    IsRamifiedAt (radicalNumberFieldExtension E p a) P := by
  have hnotpow : ∀ b : E.field, b ^ (p : ℕ) ≠ a.1 := by
    intro b hb
    have hvpow : (P.valuation E.field b) ^ (p : ℕ) =
        exp (-(k : ℤ)) := by
      calc
        (P.valuation E.field b) ^ (p : ℕ) =
            P.valuation E.field (b ^ (p : ℕ)) :=
          (map_pow (P.valuation E.field) b (p : ℕ)).symm
        _ = P.valuation E.field a.1 :=
          congrArg (P.valuation E.field) hb
        _ = exp (-(k : ℤ)) := hval
    have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hvpow
    rw [log_pow, log_exp, Int.nsmul_eq_mul] at hlog
    have hdZ : (p : ℤ) ∣ (k : ℤ) := by
      refine ⟨-(P.valuation E.field b).log, ?_⟩
      linarith
    have hd : (p : ℕ) ∣ k := by exact_mod_cast hdZ
    exact hk hd
  let R := radicalNumberFieldExtension E p a
  let alpha : R.field.field := ⟨radicalRoot E p a, by
    exact (show IntermediateField.adjoin ℚ {radicalRoot E p a} ≤
        radicalExtension E p a from le_sup_right)
      (IntermediateField.subset_adjoin ℚ {radicalRoot E p a}
        (Set.mem_singleton (radicalRoot E p a)))⟩
  have hpow : alpha ^ (p : ℕ) = algebraMap E.field R.field.field a.1 := by
    apply Subtype.ext
    exact radicalRoot_spec E p a
  have hdegree : Module.finrank E.field R.field.field = (p : ℕ) :=
    radicalNumberFieldExtension_finrank_of_not_isPow E p a hnotpow
  obtain ⟨W, hW, he⟩ :=
    kummerRadicalFieldRamifiedAt p a.1 alpha hpow hdegree P k hval hk
  refine ⟨W, hW, ?_⟩
  exact he

section

open NU.LocalTheory

private def regularKernelCompletionIntegerHom
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    primeValuationSubring v →+* v.adicCompletionIntegers M where
  toFun x := ⟨NumberField.FinitePlace.embedding v (x : M), by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [NumberField.FinitePlace.embedding_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    let w := v.valuation M
    have hA : primeValuationSubring v = w.valuationSubring :=
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
    have hx : (x : M) ∈ w.valuationSubring := hA ▸ x.prop
    exact hx⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private instance regularKernelCompletionIntegerHom_isLocal
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    IsLocalHom (regularKernelCompletionIntegerHom v) := by
  apply IsLocalHom.mk
  intro x hx
  let w := v.valuation M
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  rw [B.valuation_eq_one_iff] at hx
  rw [A.valuation_eq_one_iff]
  have hA : A = w.valuationSubring :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
  have hequivGlobal : w.IsEquiv A.valuation := by
    rw [hA]
    exact Valuation.isEquiv_valuation_valuationSubring w
  apply hequivGlobal.eq_one_iff_eq_one.mp
  have hequivLocal :
      (Valued.v : Valuation (v.adicCompletion M) ℤᵐ⁰).IsEquiv B.valuation :=
    Valuation.isEquiv_valuation_valuationSubring _
  have hraw : Valued.v (NumberField.FinitePlace.embedding v (x : M)) = 1 :=
    hequivLocal.eq_one_iff_eq_one.mpr hx
  rw [NumberField.FinitePlace.embedding_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hraw
  exact hraw

private noncomputable def regularKernelCompletionResidueMap
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    IsLocalRing.ResidueField (primeValuationSubring v) →+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers M) :=
  IsLocalRing.ResidueField.map (regularKernelCompletionIntegerHom v)

private theorem regularKernelCompletionResidueMap_surjective
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    Function.Surjective (regularKernelCompletionResidueMap v) := by
  intro y
  obtain ⟨b, rfl⟩ :=
    (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers M)) y
  let K := v.adicCompletion M
  let A := primeValuationSubring v
  let B := v.adicCompletionIntegers M
  have hopen : Metric.ball (b : K) 1 ∈ nhds (b : K) :=
    Metric.ball_mem_nhds _ zero_lt_one
  obtain ⟨x, hxball⟩ :=
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap M v).mem_nhds hopen
  have hxdiffnorm : ‖algebraMap M K x - (b : K)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hxball
  have hxdiff : Valued.v (algebraMap M K x - (b : K)) < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mp hxdiffnorm
  have hbraw : Valued.v (b : K) ≤ 1 := b.prop
  have hxraw : Valued.v (algebraMap M K x) ≤ 1 := by
    rw [show algebraMap M K x = (algebraMap M K x - (b : K)) + b by abel]
    exact (Valued.v.map_add _ _).trans (max_le hxdiff.le hbraw)
  have hembalg : NumberField.FinitePlace.embedding v x = algebraMap M K x := by
    rw [NumberField.FinitePlace.embedding_apply]
    rfl
  have hxglobal : (v.valuation M) x ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
      ← NumberField.FinitePlace.embedding_apply, hembalg]
    exact hxraw
  have hA : A = (v.valuation M).valuationSubring :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
  have hxA : x ∈ A := by
    rw [hA]
    exact hxglobal
  let xa : A := ⟨x, hxA⟩
  refine ⟨IsLocalRing.residue A xa, ?_⟩
  rw [regularKernelCompletionResidueMap, IsLocalRing.ResidueField.map_residue]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    B.valuation_lt_one_iff]
  apply (Valuation.isEquiv_valuation_valuationSubring
    (Valued.v : Valuation K ℤᵐ⁰)).lt_iff_lt.mp
  simpa [regularKernelCompletionIntegerHom, xa, hembalg] using hxdiff

private noncomputable def regularKernelQuotientEquivResidueFieldAt
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    (𝓞 M ⧸ v.asIdeal) ≃+*
      IsLocalRing.ResidueField (primeValuationSubring v) := by
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)

private theorem regularKernelResidueFieldAt_finite
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    Finite (IsLocalRing.ResidueField (primeValuationSubring v)) :=
  Finite.of_equiv (𝓞 M ⧸ v.asIdeal)
    (regularKernelQuotientEquivResidueFieldAt v).toEquiv

private theorem regularKernel_ringChar_eq_of_fieldHom
    {k l : Type*} [Field k] [Field l] (f : k →+* l) :
    ringChar k = ringChar l := by
  apply Nat.dvd_antisymm
  · apply ringChar.dvd
    apply f.injective
    simpa only [map_natCast, map_zero] using
      (CharP.cast_eq_zero l (ringChar l))
  · apply ringChar.dvd
    rw [← map_natCast f, CharP.cast_eq_zero k (ringChar k), map_zero]

private theorem regularKernelCompletion_residueCharacteristic_eq
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers M)) =
      residueCharacteristic v := by
  change ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers M)) =
    ringChar (IsLocalRing.ResidueField (primeValuationSubring v))
  exact (regularKernel_ringChar_eq_of_fieldHom
    (regularKernelCompletionResidueMap v)).symm

open scoped Pointwise in
private theorem regularKernelCompletionIntegers_isAdicComplete
    {M : Type*} [Field M] [NumberField M] (v : FinitePlace M) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers M))
      (v.adicCompletionIntegers M) := by
  letI : CompleteSpace (Valued.integer (v.adicCompletion M)) :=
    (Valued.isClosed_valuationSubring
      (v.adicCompletion M)).completeSpace_coe
  letI : IsDiscreteValuationRing
      (Valued.integer (v.adicCompletion M)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers M)
    infer_instance
  letI : Finite (IsLocalRing.ResidueField
      (primeValuationSubring v)) :=
    regularKernelResidueFieldAt_finite v
  letI : Finite (Valued.ResidueField (v.adicCompletion M)) :=
    Finite.of_surjective (regularKernelCompletionResidueMap v)
      (regularKernelCompletionResidueMap_surjective v)
  letI : CompactSpace (Valued.integer (v.adicCompletion M)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  change IsAdicComplete
    (IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion M)))
      (Valued.integer (v.adicCompletion M))
  refine { prec' := ?_ }
  intro f hf
  let S n : Set (Valued.integer (v.adicCompletion M)) := f n +ᵥ
    (((IsLocalRing.maximalIdeal
      (Valued.integer (v.adicCompletion M))) ^ n :
        Ideal (Valued.integer (v.adicCompletion M))) : Set _)
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr
      (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have hclosed n : IsClosed (S n) :=
    (IsNoetherianRing.isClosed_ideal
      ((IsLocalRing.maximalIdeal
        (Valued.integer (v.adicCompletion M))) ^ n)).vadd (f n)
  obtain ⟨L, hL⟩ := (hclosed 0).isCompact
    |>.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) hclosed
  refine ⟨L, fun n => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
  simpa [SModEq.sub_mem] using hy

private theorem regularKernel_oneModPrime_isLocalPthPower
    {M : Type*} [Field M] [NumberField M]
    (v : FinitePlace M) (p : NU.LocalTheory.OddPrime)
    (u : NumberField.RingOfIntegers M) (hu : u - 1 ∈ v.asIdeal)
    (hchar : residueCharacteristic v ≠ (p : ℕ)) :
    ∃ x : v.adicCompletion M,
      x ^ (p : ℕ) = algebraMap M (v.adicCompletion M) (u : M) := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers M))
      (v.adicCompletionIntegers M) :=
    regularKernelCompletionIntegers_isAdicComplete v
  letI : HenselianRing (v.adicCompletionIntegers M)
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers M)) :=
    IsAdicComplete.henselianRing _ _
  letI : Algebra (NumberField.RingOfIntegers M)
      (primeValuationSubring v) := by
    change Algebra (NumberField.RingOfIntegers M)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)
    infer_instance
  letI : IsLocalization.AtPrime (primeValuationSubring v) v.asIdeal := by
    change IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)
      v.asIdeal
    infer_instance
  let uA : primeValuationSubring v :=
    algebraMap (NumberField.RingOfIntegers M) (primeValuationSubring v) u
  let uB : v.adicCompletionIntegers M :=
    regularKernelCompletionIntegerHom v uA
  have huA : uA - 1 ∈
      IsLocalRing.maximalIdeal (primeValuationSubring v) := by
    have hmap : algebraMap (NumberField.RingOfIntegers M)
        (primeValuationSubring v) (u - 1) ∈
        IsLocalRing.maximalIdeal (primeValuationSubring v) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal
        (primeValuationSubring v)]
      exact Ideal.mem_map_of_mem _ hu
    simpa [uA] using hmap
  have huB : uB - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers M) := by
    have hmap := Ideal.mem_map_of_mem
      (regularKernelCompletionIntegerHom v) huA
    have hle := IsLocalRing.map_maximalIdeal_le
      (regularKernelCompletionIntegerHom v)
    simpa [uB] using hle hmap
  let f : Polynomial (v.adicCompletionIntegers M) :=
    Polynomial.X ^ (p : ℕ) - Polynomial.C uB
  have hf : f.Monic :=
    Polynomial.monic_X_pow_sub_C uB p.1.2.ne_zero
  have heval : f.eval 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers M) := by
    have hneg : 1 - uB ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers M) := by
      simpa only [neg_sub] using
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers M)).neg_mem huB
    have heq : f.eval 1 = 1 - uB := by simp [f]
    rw [heq]
    exact hneg
  have hpunit : IsUnit (p : v.adicCompletionIntegers M) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hpMem
    have hpzero : (p : IsLocalRing.ResidueField
        (v.adicCompletionIntegers M)) = 0 := by
      calc
        (p : IsLocalRing.ResidueField (v.adicCompletionIntegers M)) =
            IsLocalRing.residue (v.adicCompletionIntegers M)
              (p : v.adicCompletionIntegers M) :=
          (map_natCast
            (IsLocalRing.residue (v.adicCompletionIntegers M))
              (p : ℕ)).symm
        _ = 0 := (IsLocalRing.residue_eq_zero_iff
          (p : v.adicCompletionIntegers M)).mpr hpMem
    have hdvd : ringChar (IsLocalRing.ResidueField
        (v.adicCompletionIntegers M)) ∣ (p : ℕ) :=
      (CharP.cast_eq_zero_iff
        (IsLocalRing.ResidueField (v.adicCompletionIntegers M))
        (ringChar (IsLocalRing.ResidueField
          (v.adicCompletionIntegers M))) (p : ℕ)).mp hpzero
    have hprime : Nat.Prime (ringChar (IsLocalRing.ResidueField
        (v.adicCompletionIntegers M))) := by
      apply (CharP.char_is_prime_or_zero
        (IsLocalRing.ResidueField (v.adicCompletionIntegers M)) _).resolve_right
      intro hzero
      have hpzeroNat : (p : ℕ) = 0 := by
        simpa [hzero] using hdvd
      exact p.1.2.ne_zero hpzeroNat
    have heq := (Nat.dvd_prime p.1.2).mp hdvd
    exact heq.elim hprime.ne_one (fun h => hchar
      ((regularKernelCompletion_residueCharacteristic_eq v).symm.trans h))
  have hderiv : IsUnit ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers M)))
      (f.derivative.eval 1)) := by
    have hdeval : f.derivative.eval 1 =
        (p : v.adicCompletionIntegers M) := by
      simp only [f, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, sub_zero, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
    rw [hdeval]
    exact hpunit.map _
  obtain ⟨y, hy, _⟩ :=
    HenselianRing.is_henselian f hf 1 heval hderiv
  refine ⟨(y : v.adicCompletion M), ?_⟩
  have hy' : y ^ (p : ℕ) = uB := by
    have hsub : y ^ (p : ℕ) - uB = 0 := by
      simpa [f, Polynomial.IsRoot] using hy
    exact sub_eq_zero.mp hsub
  calc
    (y : v.adicCompletion M) ^ (p : ℕ) = (uB : v.adicCompletion M) :=
      congrArg Subtype.val hy'
    _ = algebraMap M (v.adicCompletion M) (u : M) := by
      change NumberField.FinitePlace.embedding v (uA : M) = _
      have huAcoe : (uA : M) = (u : M) := rfl
      rw [huAcoe, NumberField.FinitePlace.embedding_apply]
      rfl

private theorem regularKernel_residueCharacteristic_eq_quotient_ringChar
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.residueCharacteristic v =
      ringChar ((NumberField.RingOfIntegers K) ⧸ v.asIdeal) := by
  letI : Algebra (NumberField.RingOfIntegers K)
      (NU.LocalTheory.primeValuationSubring v) :=
    show Algebra (NumberField.RingOfIntegers K)
      (HeightOneSpectrum.valuationSubringAtPrime K v) from inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (HeightOneSpectrum.valuationSubringAtPrime K v) v.asIdeal from
        inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (NU.LocalTheory.primeValuationSubring v)
  rw [NU.LocalTheory.residueCharacteristic, ringChar.eq_iff]
  exact (e.symm.toRingHom.charP_iff_charP _).mpr
    (ringChar.charP ((NumberField.RingOfIntegers K) ⧸ v.asIdeal))

private theorem regularKernel_rational_residueCharacteristic_eq_norm
    (q : NU.Chebotarev.PrimeIdeal ℚ) :
    NU.LocalTheory.residueCharacteristic q =
      NU.Chebotarev.PrimeIdeal.norm q := by
  letI : q.asIdeal.IsMaximal := q.isMaximal
  let J : Ideal ℤ := Ideal.map Rat.ringOfIntegersEquiv q.asIdeal
  letI : J.IsMaximal :=
    Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv
  letI : Field ((NumberField.RingOfIntegers ℚ) ⧸ q.asIdeal) :=
    Ideal.Quotient.field q.asIdeal
  letI : Field (ℤ ⧸ J) := Ideal.Quotient.field J
  let e : ((NumberField.RingOfIntegers ℚ) ⧸ q.asIdeal) ≃+* (ℤ ⧸ J) :=
    Ideal.quotientEquiv q.asIdeal J Rat.ringOfIntegersEquiv rfl
  have hchar :
      ringChar ((NumberField.RingOfIntegers ℚ) ⧸ q.asIdeal) =
        ringChar (ℤ ⧸ J) := by
    rw [ringChar.eq_iff]
    exact (e.toRingHom.charP_iff_charP _).mpr
      (ringChar.charP (ℤ ⧸ J))
  have hJunder : Ideal.under ℤ J = J := by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap]
    rfl
  have hnormJ : ringChar (ℤ ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.ringChar_quot, hJunder]
  have hnorm : Ideal.absNorm J = Ideal.absNorm q.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr e.symm.toEquiv
  calc
    NU.LocalTheory.residueCharacteristic q =
        ringChar ((NumberField.RingOfIntegers ℚ) ⧸ q.asIdeal) :=
      regularKernel_residueCharacteristic_eq_quotient_ringChar q
    _ = ringChar (ℤ ⧸ J) := hchar
    _ = Ideal.absNorm J := hnormJ
    _ = Ideal.absNorm q.asIdeal := hnorm
    _ = NU.Chebotarev.PrimeIdeal.norm q := rfl

private theorem regularKernel_residueCharacteristic_restrictFinitePlace
    (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : NU.LocalTheory.FinitePlace M) :
    NU.LocalTheory.residueCharacteristic
        (NU.LocalTheory.restrictFinitePlace L w) =
      NU.LocalTheory.residueCharacteristic w := by
  rw [regularKernel_residueCharacteristic_eq_quotient_ringChar,
    regularKernel_residueCharacteristic_eq_quotient_ringChar]
  letI : Algebra (NumberField.RingOfIntegers L)
      (NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.restrictFinitePlace L w)) :=
    show Algebra (NumberField.RingOfIntegers L)
      (HeightOneSpectrum.valuationSubringAtPrime L
        (NU.LocalTheory.restrictFinitePlace L w)) from inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.restrictFinitePlace L w))
      (NU.LocalTheory.restrictFinitePlace L w).asIdeal :=
    show IsLocalization.AtPrime
      (HeightOneSpectrum.valuationSubringAtPrime L
        (NU.LocalTheory.restrictFinitePlace L w))
      (NU.LocalTheory.restrictFinitePlace L w).asIdeal from inferInstance
  rw [Ideal.ringChar_quot, Ideal.ringChar_quot,
    NU.LocalTheory.restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

private theorem regularKernel_restrictFinitePlace_tower
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (W : NU.LocalTheory.FinitePlace M) :
    NU.LocalTheory.restrictFinitePlace K
        (NU.LocalTheory.restrictFinitePlace L W) =
      NU.LocalTheory.restrictFinitePlace K W := by
  apply HeightOneSpectrum.ext
  rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
    NU.LocalTheory.restrictFinitePlace_asIdeal,
    NU.LocalTheory.restrictFinitePlace_asIdeal]
  ext x
  have hx : algebraMap (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers M)
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) x) =
      algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers M) x := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply K L M (x : K)).symm
  exact Iff.rfl.trans (congrArg (fun z => z ∈ W.asIdeal) hx).to_iff

private theorem AsymmetricApproximationData.conjugate_integer_one_mod_away
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {D : AsymmetricPrimeData N p}
    (A : AsymmetricApproximationData D)
    (g : N.field ≃ₐ[ℚ] N.field) (hg : g ≠ 1)
    (Q : FinitePlace (cyclotomicCompositum N p).field)
    (hQ : restrictCyclotomicPlace N p Q = D.v g)
    (delta : CyclotomicDelta N p) :
    delta.1 • A.integer - 1 ∈ Q.asIdeal := by
  let E := cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion
      (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
  letI : IsScalarTower ℚ N.field E.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsGalois N.field E.field :=
    cyclotomicCompositum_isGaloisOverBase N p
  letI : IsGalois ℚ E.field := cyclotomicCompositum_isGaloisOverQ N p
  let sigma : E.field ≃ₐ[ℚ] E.field := delta.1
  let sigmaN : E.field ≃ₐ[N.field] E.field :=
    { sigma.toRingEquiv with
      commutes' := by
        intro x
        exact delta.2 x }
  let Q' := NU.LocalTheory.conjugateFinitePlace ℚ sigma.symm Q
  have hQ'N : restrictCyclotomicPlace N p Q' = D.v g := by
    change NU.LocalTheory.restrictFinitePlace N.field Q' = D.v g
    calc
      NU.LocalTheory.restrictFinitePlace N.field Q' =
          NU.LocalTheory.restrictFinitePlace N.field Q := by
        apply HeightOneSpectrum.ext
        rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
          NU.LocalTheory.conjugateFinitePlace_asIdeal]
        change Ideal.under (NumberField.RingOfIntegers N.field)
          (sigmaN.symm • Q.asIdeal) =
            Ideal.under (NumberField.RingOfIntegers N.field) Q.asIdeal
        exact Ideal.under_smul
          (NumberField.RingOfIntegers N.field) Q.asIdeal sigmaN.symm
      _ = D.v g := hQ
  have hQ'q : rationalPrime E Q' = D.q := by
    change NU.LocalTheory.restrictFinitePlace ℚ Q' = D.q
    calc
      NU.LocalTheory.restrictFinitePlace ℚ Q' =
          NU.LocalTheory.restrictFinitePlace ℚ
            (NU.LocalTheory.restrictFinitePlace N.field Q') :=
        (regularKernel_restrictFinitePlace_tower Q').symm
      _ = NU.LocalTheory.restrictFinitePlace ℚ (D.v g) :=
        congrArg (NU.LocalTheory.restrictFinitePlace ℚ) hQ'N
      _ = D.q := D.v_over_q g
  have hQ'ne : Q' ≠ D.P := by
    intro heq
    have hvg : D.v g = D.v 1 := by
      calc
        D.v g = restrictCyclotomicPlace N p Q' := hQ'N.symm
        _ = restrictCyclotomicPlace N p D.P :=
          congrArg (restrictCyclotomicPlace N p) heq
        _ = D.v 1 := D.P_over_identity
    exact hg (D.v_injective hvg)
  have hmod : A.integer - 1 ∈ Q'.asIdeal :=
    A.one_mod_other Q' hQ'q hQ'ne
  rw [NU.LocalTheory.conjugateFinitePlace_asIdeal,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hmod
  have hinv : sigma.symm⁻¹ = sigma := inv_inv sigma
  rw [hinv] at hmod
  simpa only [smul_sub, smul_one] using hmod

/- Other-place rung: principal units are `p`-divisible because the auxiliary
residue characteristic is different from `p`. -/
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem projectedKummerRepresentative_localPowerAway
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p)
    (A : AsymmetricApproximationData D)
    (K : AsymmetricProjectedKummerData A) :
    ∀ g : N.field ≃ₐ[ℚ] N.field, g ≠ 1 →
      ∀ Q : NU.LocalTheory.FinitePlace
          (cyclotomicCompositum N p).field,
        restrictCyclotomicPlace N p Q = D.v g →
        IsLocalPthPowerAt (cyclotomicCompositum N p) p K.a Q := by
  classical
  intro g hg Q hQ
  let E := cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion
      (le_cyclotomicCompositum N p)).toRingHom.toAlgebra
  letI : IsScalarTower ℚ N.field E.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let C := Q.adicCompletion E.field
  letI : Algebra E.field C := by
    dsimp [C, E]
    infer_instance
  have hQq : rationalPrime E Q = D.q := by
    change NU.LocalTheory.restrictFinitePlace ℚ Q = D.q
    calc
      NU.LocalTheory.restrictFinitePlace ℚ Q =
          NU.LocalTheory.restrictFinitePlace ℚ
            (NU.LocalTheory.restrictFinitePlace N.field Q) :=
        (regularKernel_restrictFinitePlace_tower Q).symm
      _ = NU.LocalTheory.restrictFinitePlace ℚ (D.v g) :=
        congrArg (NU.LocalTheory.restrictFinitePlace ℚ) hQ
      _ = D.q := D.v_over_q g
  have hresidue : residueCharacteristic Q =
      NU.Chebotarev.PrimeIdeal.norm D.q := by
    calc
      residueCharacteristic Q =
          residueCharacteristic (rationalPrime E Q) :=
        (regularKernel_residueCharacteristic_restrictFinitePlace ℚ Q).symm
      _ = residueCharacteristic D.q :=
        congrArg residueCharacteristic hQq
      _ = NU.Chebotarev.PrimeIdeal.norm D.q :=
        regularKernel_rational_residueCharacteristic_eq_norm D.q
  have hchar : residueCharacteristic Q ≠ (p : ℕ) := by
    rw [hresidue]
    exact D.norm_ne
  let Delta := CyclotomicDelta N p
  letI := Fintype.ofFinite Delta
  let u : Delta → E.fieldˣ := fun delta =>
    Units.map delta.1.toRingEquiv.toMonoidHom K.b
  let n : Delta → ℕ := fun delta =>
    ((cyclotomicKummerProjector N p).coeff delta).val
  have hdeltaRoot (delta : Delta) :
      ∃ z : C, z ^ (p : ℕ) = algebraMap E.field C (u delta).1 := by
    have hmod := A.conjugate_integer_one_mod_away g hg Q hQ delta
    obtain ⟨z, hz⟩ := regularKernel_oneModPrime_isLocalPthPower
      Q p (delta.1 • A.integer) hmod hchar
    have hzunit : z ^ (p : ℕ) = algebraMap E.field C
        (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1 := by
      calc
        z ^ (p : ℕ) = algebraMap E.field C
            (((delta.1 • A.integer :
              NumberField.RingOfIntegers E.field)) : E.field) := hz
        _ = algebraMap E.field C
            (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1 := by
          rfl
    refine ⟨z ^ K.exponent, ?_⟩
    calc
      (z ^ K.exponent) ^ (p : ℕ) =
          (z ^ (p : ℕ)) ^ K.exponent := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (algebraMap E.field C
          (Units.map delta.1.toRingEquiv.toMonoidHom A.unit).1) ^
            K.exponent := congrArg (fun x : C => x ^ K.exponent) hzunit
      _ = algebraMap E.field C
          ((Units.map delta.1.toRingEquiv.toMonoidHom A.unit) ^
            K.exponent).1 := by simp
      _ = algebraMap E.field C (u delta).1 := by
        dsimp [u]
        rw [K.b_eq]
        congr 1
        exact (map_pow delta.1 A.unit.1 K.exponent).symm
  choose z hz using hdeltaRoot
  let r : C := ∏ delta : Delta, z delta ^ n delta
  have hrepresentative :
      projectedKummerRepresentative N p K.b =
        ∏ delta : Delta, u delta ^ n delta := rfl
  have hr : r ^ (p : ℕ) = algebraMap E.field C
      (projectedKummerRepresentative N p K.b).1 := by
    calc
      r ^ (p : ℕ) =
          ∏ delta : Delta, (z delta ^ n delta) ^ (p : ℕ) := by
        dsimp [r]
        rw [← Finset.prod_pow]
      _ = ∏ delta : Delta, (z delta ^ (p : ℕ)) ^ n delta := by
        apply Finset.prod_congr rfl
        intro delta _
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = ∏ delta : Delta,
          (algebraMap E.field C (u delta).1) ^ n delta := by
        apply Finset.prod_congr rfl
        intro delta _
        exact congrArg (fun x : C => x ^ n delta) (hz delta)
      _ = algebraMap E.field C
          ((∏ delta : Delta, u delta ^ n delta).1) := by
        simp
      _ = algebraMap E.field C
          (projectedKummerRepresentative N p K.b).1 := by
        rw [hrepresentative]
  let rep := projectedKummerRepresentative N p K.b
  have hclass : (QuotientGroup.mk K.a : KummerClass E (p : ℕ)) =
      QuotientGroup.mk rep :=
    K.class_eq.trans (projectedKummerRepresentative_class N p K.b).symm
  have hmem : K.a / rep ∈ pthPowerSubgroup E (p : ℕ) :=
    QuotientGroup.eq_iff_div_mem.mp hclass
  obtain ⟨c, hc⟩ := hmem
  have ha : c ^ (p : ℕ) * rep = K.a := by
    rw [hc]
    simp
  refine ⟨algebraMap E.field C c.1 * r, ?_⟩
  calc
    (algebraMap E.field C c.1 * r) ^ (p : ℕ) =
        (algebraMap E.field C c.1) ^ (p : ℕ) * r ^ (p : ℕ) :=
      mul_pow _ _ _
    _ = algebraMap E.field C (c ^ (p : ℕ)).1 *
        algebraMap E.field C
          (projectedKummerRepresentative N p K.b).1 := by rw [hr]; simp
    _ = algebraMap E.field C (c ^ (p : ℕ)).1 *
        algebraMap E.field C rep.1 := by rfl
    _ = algebraMap E.field C (c ^ (p : ℕ) * rep).1 := by simp
    _ = algebraMap E.field C K.a.1 := by rw [ha]

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
-- Comparing both discrete valuations and their residue fields needs extra synthesis room.
private theorem regularKernel_localEmbedding_place (P : FinitePlace K)
    (j : L →ₐ[K] P.adicCompletion K) :
    ∃ W : FinitePlace L, restrictFinitePlace K W = P ∧
      W.asIdeal.ramificationIdx' (NumberField.RingOfIntegers K) = 1 ∧
      W.asIdeal.inertiaDeg' (NumberField.RingOfIntegers K) = 1 := by
  let C := P.adicCompletion K
  let B := P.adicCompletionIntegers K
  let u : Valuation L ℤᵐ⁰ :=
    (Valued.v : Valuation C ℤᵐ⁰).comap j.toRingHom
  have hmem (x : NumberField.RingOfIntegers L) : j (x : L) ∈ B := by
    have hxZ : IsIntegral ℤ (x : L) := x.2
    have hjZ : IsIntegral ℤ (j (x : L)) := by
      let jZ : L →ₐ[ℤ] C := j.restrictScalars ℤ
      exact hxZ.map jZ
    have hjB : IsIntegral B (j (x : L)) := hjZ.tower_top
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hjB
    exact hb ▸ b.prop
  let f : NumberField.RingOfIntegers L →+* B :=
    { toFun := fun x => ⟨j (x : L), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let J : Ideal (NumberField.RingOfIntegers L) :=
    (IsLocalRing.maximalIdeal B).comap f
  have hJprime : J.IsPrime := by infer_instance
  have hJcomap : J.comap (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)) = P.asIdeal := by
    ext x
    change f (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) x) ∈ IsLocalRing.maximalIdeal B ↔
        x ∈ P.asIdeal
    rw [B.valuation_lt_one_iff]
    have hequiv : (Valued.v : Valuation C ℤᵐ⁰).IsEquiv B.valuation :=
      Valuation.isEquiv_valuation_valuationSubring _
    change B.valuation ↑(f (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) x)) < B.valuation 1 ↔ x ∈ P.asIdeal
    rw [← hequiv.lt_iff_lt, map_one]
    change Valued.v (j ((algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) x : NumberField.RingOfIntegers L) : L)) < 1 ↔
        x ∈ P.asIdeal
    change Valued.v (j (algebraMap K L (x : K))) < 1 ↔ x ∈ P.asIdeal
    rw [j.commutes]
    change Valued.v (algebraMap K C (x : K)) < 1 ↔ x ∈ P.asIdeal
    have hv : Valued.v (algebraMap K C (x : K)) = P.valuation K (x : K) := by
      change Valued.v ((x : K) : P.adicCompletion K) = P.valuation K (x : K)
      exact P.valuedAdicCompletion_eq_valuation' (x : K)
    rw [hv]
    exact P.valuation_lt_one_iff_mem x
  have hJne : J ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [← hJcomap, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact FaithfulSMul.algebraMap_eq_zero_iff _ _
  let W : FinitePlace L := ⟨J, hJprime, hJne⟩
  letI : W.asIdeal.IsMaximal := W.isMaximal
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (NumberField.RingOfIntegers L ⧸ W.asIdeal) :=
    Ideal.Quotient.field W.asIdeal
  letI : Field (NumberField.RingOfIntegers K ⧸ P.asIdeal) :=
    Ideal.Quotient.field P.asIdeal
  have hrestrict : restrictFinitePlace K W = P := by
    apply HeightOneSpectrum.ext
    rw [restrictFinitePlace_asIdeal]
    exact hJcomap
  have hWover : W.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def]
    exact hJcomap.symm⟩
  letI : W.asIdeal.LiesOver P.asIdeal := hWover
  let AW := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L W
  have hAWle : AW ≤ u.valuationSubring := by
    rintro x ⟨b, s, hs, rfl⟩
    have hbraw : Valued.v (j (b : L)) ≤ (1 : ℤᵐ⁰) := hmem b
    have hsnot : f s ∉ IsLocalRing.maximalIdeal B := by
      exact hs
    have hsraw_not_lt : ¬ Valued.v (j (s : L)) < (1 : ℤᵐ⁰) := by
      intro hlt
      apply hsnot
      rw [B.valuation_lt_one_iff]
      have hequiv : (Valued.v : Valuation C ℤᵐ⁰).IsEquiv B.valuation :=
        Valuation.isEquiv_valuation_valuationSubring _
      change B.valuation (f s : C) < B.valuation 1
      rw [← hequiv.lt_iff_lt, map_one]
      exact hlt
    have hsraw : Valued.v (j (s : L)) = (1 : ℤᵐ⁰) :=
      le_antisymm (hmem s) (not_lt.mp hsraw_not_lt)
    change u ((b : L) * (s : L)⁻¹) ≤ 1
    change Valued.v (j ((b : L) * (s : L)⁻¹)) ≤ 1
    rw [map_mul, map_inv₀]
    rw [map_mul, map_inv₀, hsraw, inv_one, mul_one]
    exact hbraw
  obtain ⟨pi, hpi⟩ := P.valuation_exists_uniformizer K
  have hupi : u (algebraMap K L pi) = exp (-1 : ℤ) := by
    change Valued.v (j (algebraMap K L pi)) = exp (-1 : ℤ)
    rw [j.commutes]
    change Valued.v (algebraMap K C pi) = exp (-1 : ℤ)
    change Valued.v ((pi : K) : P.adicCompletion K) = exp (-1 : ℤ)
    rw [P.valuedAdicCompletion_eq_valuation', hpi]
  have huNon : Valuation.IsNontrivial u := ⟨algebraMap K L pi, by
    rw [hupi]
    simp⟩
  have hAW : AW = u.valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top _ hAWle (by
      rw [ne_eq, Valuation.valuationSubring_eq_top_iff]
      exact not_not.mpr huNon)
  have hequiv : (W.valuation L).IsEquiv u := by
    rw [Valuation.isEquiv_iff_valuationSubring,
      ← W.valuationSubringAtPrime_eq_valuationSubring]
    exact hAW
  let e := P.asIdeal.ramificationIdx W.asIdeal
  obtain ⟨tau, htau⟩ := W.valuation_exists_uniformizer L
  have hWpi : W.valuation L (algebraMap K L pi) =
      (exp (-1 : ℤ) : ℤᵐ⁰) ^ e := by
    calc
      W.valuation L (algebraMap K L pi) =
          (P.valuation K pi) ^ e := (P.valuation_liesOver L W pi).symm
      _ = (exp (-1 : ℤ) : ℤᵐ⁰) ^ e := by rw [hpi]
  have hWeq : W.valuation L (tau ^ e) =
      W.valuation L (algebraMap K L pi) := by
    rw [map_pow, htau, hWpi]
  have hueq : u (tau ^ e) = u (algebraMap K L pi) :=
    hequiv.eq_iff.mp hWeq
  have hupow : (u tau) ^ e = exp (-1 : ℤ) := by
    rw [← map_pow, hueq, hupi]
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hupow
  rw [log_pow, log_exp, Int.nsmul_eq_mul] at hlog
  have hedivZ : (e : ℤ) ∣ 1 := by
    refine ⟨-(u tau).log, ?_⟩
    linarith
  have hediv : e ∣ 1 := by exact_mod_cast hedivZ
  have he : e = 1 := Nat.eq_one_of_dvd_one hediv
  let Bres := IsLocalRing.ResidueField B
  let resf : NumberField.RingOfIntegers L →+* Bres :=
    (IsLocalRing.residue B).comp f
  have hresf (x : NumberField.RingOfIntegers L) (hx : x ∈ W.asIdeal) :
      resf x = 0 := by
    change IsLocalRing.residue B (f x) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hx
  let qf : (NumberField.RingOfIntegers L ⧸ W.asIdeal) →+* Bres :=
    Ideal.Quotient.lift W.asIdeal resf hresf
  have hqfinj : Function.Injective qf := qf.injective
  let AP := primeValuationSubring P
  letI : Algebra (NumberField.RingOfIntegers K) AP := by
    change Algebra (NumberField.RingOfIntegers K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K P)
    infer_instance
  letI : IsLocalization.AtPrime AP P.asIdeal := by
    change IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K P) P.asIdeal
    infer_instance
  letI : IsLocalRing AP := by
    change IsLocalRing
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K P)
    infer_instance
  let eP : (NumberField.RingOfIntegers K ⧸ P.asIdeal) ≃+*
      IsLocalRing.ResidueField AP :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K P)
  let qbase : (NumberField.RingOfIntegers K ⧸ P.asIdeal) →+* Bres :=
    (regularKernelCompletionResidueMap P).comp eP.toRingHom
  have hqbasesurj : Function.Surjective qbase :=
    (regularKernelCompletionResidueMap_surjective P).comp eP.surjective
  have hcompat : qf.comp (algebraMap
      (NumberField.RingOfIntegers K ⧸ P.asIdeal)
      (NumberField.RingOfIntegers L ⧸ W.asIdeal)) = qbase := by
    ext x
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [Ideal.Quotient.lift_mk]
    change resf (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) x) =
        regularKernelCompletionResidueMap P (eP (Ideal.Quotient.mk P.asIdeal x))
    have hePapp : eP (Ideal.Quotient.mk P.asIdeal x) =
        IsLocalRing.residue AP
          (algebraMap (NumberField.RingOfIntegers K) AP x) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk P.asIdeal AP x
    rw [hePapp, regularKernelCompletionResidueMap,
      IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue B
        (f (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) x)) = _
    apply congrArg (IsLocalRing.residue B)
    apply Subtype.ext
    change j (algebraMap K L (x : K)) =
      NumberField.FinitePlace.embedding P (x : K)
    rw [j.commutes, NumberField.FinitePlace.embedding_apply]
    rfl
  have hquotSurj : Function.Surjective (algebraMap
      (NumberField.RingOfIntegers K ⧸ P.asIdeal)
      (NumberField.RingOfIntegers L ⧸ W.asIdeal)) := by
    intro z
    obtain ⟨x, hx⟩ := hqbasesurj (qf z)
    refine ⟨x, hqfinj ?_⟩
    rw [← RingHom.comp_apply, hcompat, hx]
  have hf : P.asIdeal.inertiaDeg W.asIdeal = 1 := by
    rw [Ideal.inertiaDeg_algebraMap]
    have haInj : Function.Injective
        (Algebra.ofId (NumberField.RingOfIntegers K ⧸ P.asIdeal)
          (NumberField.RingOfIntegers L ⧸ W.asIdeal)) := by
      intro x y hxy
      exact (Algebra.ofId _ _).toRingHom.injective hxy
    let aeq : (NumberField.RingOfIntegers K ⧸ P.asIdeal) ≃ₐ[(NumberField.RingOfIntegers K ⧸ P.asIdeal)] (NumberField.RingOfIntegers L ⧸ W.asIdeal) :=
      AlgEquiv.ofBijective
        (Algebra.ofId (NumberField.RingOfIntegers K ⧸ P.asIdeal)
          (NumberField.RingOfIntegers L ⧸ W.asIdeal))
        ⟨haInj, hquotSurj⟩
    calc
      Module.finrank (NumberField.RingOfIntegers K ⧸ P.asIdeal)
          (NumberField.RingOfIntegers L ⧸ W.asIdeal) =
          Module.finrank (NumberField.RingOfIntegers K ⧸ P.asIdeal)
            (NumberField.RingOfIntegers K ⧸ P.asIdeal) :=
        aeq.symm.toLinearEquiv.finrank_eq
      _ = 1 := Module.finrank_self _
  have he' : W.asIdeal.ramificationIdx'
      (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.ramificationIdx_eq_ramificationIdx'
      P.asIdeal W.asIdeal P.ne_bot]
    exact he
  have hf' : W.asIdeal.inertiaDeg'
      (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.inertiaDeg_eq_inertiaDeg' P.asIdeal W.asIdeal]
    exact hf
  exact ⟨W, hrestrict, he', hf'⟩

private theorem regularKernel_allIndices_one_of_galois
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : FinitePlace K) (W₀ W : FinitePlace L)
    (h0 : restrictFinitePlace K W₀ = P)
    (he0 : W₀.asIdeal.ramificationIdx' (NumberField.RingOfIntegers K) = 1)
    (hf0 : W₀.asIdeal.inertiaDeg' (NumberField.RingOfIntegers K) = 1)
    (h : restrictFinitePlace K W = P) :
    W.asIdeal.ramificationIdx' (NumberField.RingOfIntegers K) = 1 ∧
      W.asIdeal.inertiaDeg' (NumberField.RingOfIntegers K) = 1 := by
  have ho0 : W₀.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def, ← restrictFinitePlace_asIdeal, h0]⟩
  have ho : W.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def, ← restrictFinitePlace_asIdeal, h]⟩
  letI : W₀.asIdeal.LiesOver P.asIdeal := ho0
  letI : W.asIdeal.LiesOver P.asIdeal := ho
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : W₀.asIdeal.IsMaximal := W₀.isMaximal
  letI : W.asIdeal.IsMaximal := W.isMaximal
  have heq := Ideal.ramificationIdx_eq_of_isGaloisGroup
    P.asIdeal W.asIdeal W₀.asIdeal (L ≃ₐ[K] L)
  have hfeq := Ideal.inertiaDeg_eq_of_isGaloisGroup
    P.asIdeal W.asIdeal W₀.asIdeal (L ≃ₐ[K] L)
  exact ⟨heq.trans he0, hfeq.trans hf0⟩

end

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The two reducible and irreducible radical cases build several transported field instances.
/-- A local `p`-th power makes the local radical algebra trivial, hence the
place splits completely. -/
private theorem tameKummerRadical_splits
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field)
    (hroots : ∃ z : E.field, IsPrimitiveRoot z (p : ℕ))
    (hlocal : IsLocalPthPowerAt E p a P) :
    SplitsCompletelyAbove (radicalNumberFieldExtension E p a) P := by
  let R := radicalNumberFieldExtension E p a
  let alpha : Omega := radicalRoot E p a
  let R0 : IntermediateField E.field Omega :=
    IntermediateField.adjoin E.field {alpha}
  have hR0 : R0.restrictScalars ℚ = R.field.field := by
    calc
      R0.restrictScalars ℚ =
          E.field ⊔ IntermediateField.adjoin ℚ {alpha} :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ E.field {alpha}
      _ = R.field.field := rfl
  let e : R.field.field ≃ₐ[E.field] R0 :=
    { toFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ R0.restrictScalars ℚ := by
            rw [hR0]
            exact x.2
          exact hx⟩
      invFun := fun x => ⟨x.1, by
          have hx : x.1 ∈ R0.restrictScalars ℚ := x.2
          rw [hR0] at hx
          exact hx⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => by apply Subtype.ext; rfl }
  let alpha0 : R0 := ⟨alpha,
    IntermediateField.subset_adjoin E.field {alpha}
      (Set.mem_singleton alpha)⟩
  have halpha : alpha0 ^ (p : ℕ) = algebraMap E.field R0 a.1 := by
    apply Subtype.ext
    exact radicalRoot_spec E p a
  have hgen : IntermediateField.adjoin E.field {alpha0} = ⊤ := by
    apply (IntermediateField.lift_injective R0)
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have himage : Subtype.val '' ({alpha0} : Set R0) =
        ({alpha} : Set Omega) := by
      ext x
      simp [alpha0]
    rw [himage]
  by_cases hpow : ∃ b : E.field, b ^ (p : ℕ) = a.1
  · obtain ⟨b, hb⟩ := hpow
    obtain ⟨z, hz⟩ := hroots
    have hbne : b ≠ 0 := by
      intro hb0
      rw [hb0, zero_pow p.1.2.ne_zero] at hb
      exact a.ne_zero hb.symm
    have hzO : IsPrimitiveRoot (z : Omega) (p : ℕ) :=
      hz.map_of_injective E.field.val.injective
    have hbO : (b : Omega) ^ (p : ℕ) =
        (a.1 : Omega) := congrArg E.field.val hb
    have hxi : (alpha / (b : Omega)) ^ (p : ℕ) = 1 := by
      rw [div_pow, radicalRoot_spec E p a, hbO]
      exact div_self ((map_ne_zero E.field.val).mpr a.ne_zero)
    obtain ⟨i, _, hzi⟩ := hzO.eq_pow_of_pow_eq_one hxi
    let c : E.field := b * z ^ i
    have hc : (c : Omega) = alpha := by
      change (b : Omega) * (z : Omega) ^ i = alpha
      rw [hzi, ← mul_div_assoc]
      exact mul_div_cancel_left₀ alpha ((map_ne_zero E.field.val).mpr hbne)
    let fpoly : Polynomial E.field :=
      Polynomial.X ^ (p : ℕ) - Polynomial.C a.1
    have hroot : Polynomial.aeval alpha0 fpoly = 0 := by
      simp [fpoly, halpha]
    have hmonic : fpoly.Monic :=
      Polynomial.monic_X_pow_sub_C a.1 p.1.2.ne_zero
    have hint : IsIntegral E.field alpha0 := ⟨fpoly, hmonic, hroot⟩
    have hrootOmega : Polynomial.aeval alpha fpoly = 0 := by
      simp only [fpoly, Polynomial.aeval_def, Polynomial.eval₂_sub,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [sub_eq_zero]
      exact radicalRoot_spec E p a
    have hintOmega : IsIntegral E.field alpha :=
      ⟨fpoly, hmonic, hrootOmega⟩
    letI : FiniteDimensional E.field R0 :=
      IntermediateField.adjoin.finiteDimensional hintOmega
    have hgenAlg : Algebra.adjoin E.field {alpha0} = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra]
      exact congrArg IntermediateField.toSubalgebra hgen
    let pb0 : PowerBasis E.field R0 :=
      PowerBasis.ofAdjoinEqTop hint hgenAlg
    let pb : PowerBasis E.field R.field.field := pb0.map e.symm
    have hpgen : pb.gen = e.symm alpha0 := by
      calc
        pb.gen = e.symm pb0.gen := PowerBasis.map_gen pb0 e.symm
        _ = e.symm alpha0 := congrArg e.symm
          (PowerBasis.ofAdjoinEqTop_gen hint hgenAlg)
    have hpbc : pb.gen = algebraMap E.field R.field.field c := by
      rw [hpgen]
      apply Subtype.ext
      exact hc.symm
    let y : P.adicCompletion E.field := algebraMap E.field _ c
    have hpby : Polynomial.aeval y (minpoly E.field pb.gen) = 0 := by
      rw [hpbc, minpoly.eq_X_sub_C]
      simp [y]
    let j : R.field.field →ₐ[E.field] P.adicCompletion E.field :=
      pb.lift y hpby
    letI : Module.Free E.field R.field.field := Module.Free.of_basis pb.basis
    have hfin : Module.finrank E.field R.field.field = 1 := by
      calc
        Module.finrank E.field R.field.field = pb.dim := pb.finrank
        _ = (minpoly E.field pb.gen).natDegree := pb.natDegree_minpoly.symm
        _ = 1 := by
          rw [hpbc, minpoly.eq_X_sub_C, Polynomial.natDegree_X_sub_C]
    have hbij : Function.Bijective (algebraMap E.field R.field.field) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
    let er : E.field ≃ₐ[E.field] R.field.field :=
      AlgEquiv.ofBijective (Algebra.ofId E.field R.field.field) hbij
    letI : IsGalois E.field R.field.field := IsGalois.of_algEquiv er
    obtain ⟨W₀, hW₀, he₀, hf₀⟩ := regularKernel_localEmbedding_place P j
    refine ⟨⟨W₀, hW₀⟩, ?_⟩
    intro W hW
    exact regularKernel_allIndices_one_of_galois P W₀ W hW₀ he₀ hf₀ hW
  · push Not at hpow
    let fpoly : Polynomial E.field :=
      Polynomial.X ^ (p : ℕ) - Polynomial.C a.1
    have hirr : Irreducible fpoly :=
      X_pow_sub_C_irreducible_of_prime p.1.2 hpow
    have hroot : Polynomial.aeval alpha0 fpoly = 0 := by
      simp [fpoly, halpha]
    have hmonic : fpoly.Monic :=
      Polynomial.monic_X_pow_sub_C a.1 p.1.2.ne_zero
    have hmin : fpoly = minpoly E.field alpha0 :=
      minpoly.eq_of_irreducible_of_monic hirr hroot hmonic
    have hint : IsIntegral E.field alpha0 := ⟨fpoly, hmonic, hroot⟩
    have hrootOmega : Polynomial.aeval alpha fpoly = 0 := by
      simp only [fpoly, Polynomial.aeval_def, Polynomial.eval₂_sub,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [sub_eq_zero]
      exact radicalRoot_spec E p a
    have hintOmega : IsIntegral E.field alpha :=
      ⟨fpoly, hmonic, hrootOmega⟩
    letI : FiniteDimensional E.field R0 :=
      IntermediateField.adjoin.finiteDimensional hintOmega
    have hgenAlg : Algebra.adjoin E.field {alpha0} = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra]
      exact congrArg IntermediateField.toSubalgebra hgen
    let pb0 : PowerBasis E.field R0 :=
      PowerBasis.ofAdjoinEqTop hint hgenAlg
    let pb : PowerBasis E.field R.field.field := pb0.map e.symm
    obtain ⟨y, hy⟩ := hlocal
    have hpby : Polynomial.aeval y (minpoly E.field pb.gen) = 0 := by
      have hpgen : pb.gen = e.symm alpha0 := by
        calc
          pb.gen = e.symm pb0.gen := PowerBasis.map_gen pb0 e.symm
          _ = e.symm alpha0 := congrArg e.symm
            (PowerBasis.ofAdjoinEqTop_gen hint hgenAlg)
      have hminpb : minpoly E.field pb.gen = fpoly := by
        calc
          minpoly E.field pb.gen = minpoly E.field alpha0 := by
            rw [hpgen]
            exact minpoly.algEquiv_eq e.symm alpha0
          _ = fpoly := hmin.symm
      rw [hminpb]
      simp [fpoly, hy]
    let j : R.field.field →ₐ[E.field] P.adicCompletion E.field :=
      pb.lift y hpby
    have hpbpow : pb.gen ^ (p : ℕ) =
        algebraMap E.field R.field.field a.1 := by
      have hpgen : pb.gen = e.symm alpha0 := by
        calc
          pb.gen = e.symm pb0.gen := PowerBasis.map_gen pb0 e.symm
          _ = e.symm alpha0 := congrArg e.symm
            (PowerBasis.ofAdjoinEqTop_gen hint hgenAlg)
      rw [hpgen]
      apply e.injective
      rw [map_pow, e.apply_symm_apply, e.commutes, halpha]
    obtain ⟨z, hz⟩ := hroots
    have hprim : (primitiveRoots (p : ℕ) E.field).Nonempty :=
      ⟨z, (mem_primitiveRoots p.1.2.pos).2 hz⟩
    letI : Module.Free E.field R.field.field := Module.Free.of_basis pb.basis
    letI : Polynomial.IsSplittingField E.field R.field.field fpoly := by
      constructor
      · change (Polynomial.X ^ (p : ℕ) - Polynomial.C (a : E.field)).map
            (algebraMap E.field R.field.field) |>.Splits
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
          Polynomial.map_X]
        exact X_pow_sub_C_splits_of_isPrimitiveRoot
          (hz.map_of_injective (algebraMap E.field R.field.field).injective) hpbpow
      · apply top_unique
        rw [← pb.adjoin_gen_eq_top]
        apply Algebra.adjoin_mono
        rw [Set.singleton_subset_iff]
        change pb.gen ∈ fpoly.rootSet R.field.field
        rw [Polynomial.mem_rootSet_of_ne (Irreducible.ne_zero hirr)]
        simp [fpoly, hpbpow]
    letI : IsGalois E.field R.field.field :=
      isGalois_of_isSplittingField_X_pow_sub_C hprim hirr R.field.field
    obtain ⟨W₀, hW₀, he₀, hf₀⟩ := regularKernel_localEmbedding_place P j
    refine ⟨⟨W₀, hW₀⟩, ?_⟩
    intro W hW
    exact regularKernel_allIndices_one_of_galois P W₀ W hW₀ he₀ hf₀ hW

/-- A valuation not divisible by `p` forces the radical field to have
its full prime degree. -/
private theorem radicalNumberFieldExtension_finrank_of_valuation_not_dvd
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) (k : ℕ)
    (hval : P.valuation E.field a.1 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k) :
    Module.finrank E.field
      (radicalNumberFieldExtension E p a).field.field = (p : ℕ) := by
  apply radicalNumberFieldExtension_finrank_of_not_isPow E p a
  intro b hb
  have hvpow : (P.valuation E.field b) ^ (p : ℕ) =
      exp (-(k : ℤ)) := by
    calc
      (P.valuation E.field b) ^ (p : ℕ) =
          P.valuation E.field (b ^ (p : ℕ)) :=
        (map_pow (P.valuation E.field) b (p : ℕ)).symm
      _ = P.valuation E.field a.1 := congrArg (P.valuation E.field) hb
      _ = exp (-(k : ℤ)) := hval
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hvpow
  rw [log_pow, log_exp, Int.nsmul_eq_mul] at hlog
  have hdZ : (p : ℤ) ∣ (k : ℤ) := by
    refine ⟨-(P.valuation E.field b).log, ?_⟩
    linarith
  exact hk (by exact_mod_cast hdZ)

/-- At every prolongation, the same valuation condition forces ramification
index exactly `p`. -/
private theorem kummerRadical_ramificationIndex_eq_prime
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) (k : ℕ)
    (hval : P.valuation E.field a.1 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k)
    (W : NU.LocalTheory.FinitePlace
      (radicalNumberFieldExtension E p a).field.field)
    (hW : NU.LocalTheory.restrictFinitePlace E.field W = P) :
    relativeRamificationIndex (radicalNumberFieldExtension E p a) P W =
      (p : ℕ) := by
  let R := radicalNumberFieldExtension E p a
  let alpha : R.field.field := ⟨radicalRoot E p a, by
    exact (show IntermediateField.adjoin ℚ {radicalRoot E p a} ≤
        radicalExtension E p a from le_sup_right)
      (IntermediateField.subset_adjoin ℚ {radicalRoot E p a}
        (Set.mem_singleton (radicalRoot E p a)))⟩
  have hpow : alpha ^ (p : ℕ) = algebraMap E.field R.field.field a.1 := by
    apply Subtype.ext
    exact radicalRoot_spec E p a
  have hdegree : Module.finrank E.field R.field.field = (p : ℕ) :=
    radicalNumberFieldExtension_finrank_of_valuation_not_dvd
      E p a P k hval hk
  let A := NumberField.RingOfIntegers E.field
  let B := NumberField.RingOfIntegers R.field.field
  letI : NoZeroSMulDivisors A B := ⟨by
    intro c x h
    have hzero : algebraMap A B c * x = 0 := h
    rcases mul_eq_zero.mp hzero with hc | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_eq_zero_iff A B).mp hc)
    · exact Or.inr hx⟩
  have hWover : W.asIdeal.LiesOver P.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal, hW]⟩
  letI : W.asIdeal.LiesOver P.asIdeal := hWover
  let e := P.asIdeal.ramificationIdx W.asIdeal
  have hlie := P.valuation_liesOver R.field.field W a.1
  have hlie' : (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
      (W.valuation R.field.field alpha) ^ (p : ℕ) := by
    calc
      (exp (-(k : ℤ)) : ℤᵐ⁰) ^ e =
          (P.valuation E.field a.1) ^ e := by rw [hval]
      _ = W.valuation R.field.field (algebraMap E.field R.field.field a.1) :=
        hlie
      _ = W.valuation R.field.field (alpha ^ (p : ℕ)) :=
        congrArg (W.valuation R.field.field) hpow.symm
      _ = (W.valuation R.field.field alpha) ^ (p : ℕ) := map_pow _ _ _
  have hlog := congrArg (fun z : ℤᵐ⁰ => z.log) hlie'
  rw [log_pow, log_exp, log_pow, Int.nsmul_eq_mul] at hlog
  have hdZ : (p : ℤ) ∣ ((e : ℕ) : ℤ) * (k : ℤ) := by
    refine ⟨-(W.valuation R.field.field alpha).log, ?_⟩
    rw [Int.nsmul_eq_mul] at hlog
    linarith
  have hd : (p : ℕ) ∣ e * k := by exact_mod_cast hdZ
  have hpe : (p : ℕ) ∣ e := (p.1.2.dvd_mul.mp hd).resolve_right hk
  have hepos : 0 < e :=
    Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
        W.asIdeal P.ne_bot)
  have hple : (p : ℕ) ≤ e := Nat.le_of_dvd hepos hpe
  have hele : e ≤ (p : ℕ) := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank B E.field R.field.field W.asIdeal
  have heq : e = (p : ℕ) := Nat.le_antisymm hele hple
  rw [relativeRamificationIndex,
    ← Ideal.ramificationIdx_eq_ramificationIdx'
      P.asIdeal W.asIdeal P.ne_bot]
  exact heq

/-- A valuation forcing radical degree and ramification index `p` is tame
away from residue characteristic `p`. -/
private theorem tameKummerRadical_isTame
    (E : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (a : E.fieldˣ) (P : NU.LocalTheory.FinitePlace E.field) (k : ℕ)
    (hval : P.valuation E.field a.1 = exp (-(k : ℤ)))
    (hk : ¬(p : ℕ) ∣ k)
    (hq : NU.LocalTheory.residueCharacteristic P ≠ (p : ℕ)) :
    IsTamelyRamifiedAt (radicalNumberFieldExtension E p a) P := by
  intro W hW
  have he := kummerRadical_ramificationIndex_eq_prime
    E p a P k hval hk W hW
  rw [he]
  letI : Algebra (NumberField.RingOfIntegers E.field)
      (NU.LocalTheory.primeValuationSubring P) :=
    show Algebra (NumberField.RingOfIntegers E.field)
      (HeightOneSpectrum.valuationSubringAtPrime E.field P) from inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring P) P.asIdeal :=
    show IsLocalization.AtPrime
      (HeightOneSpectrum.valuationSubringAtPrime E.field P) P.asIdeal from
        inferInstance
  letI : Finite (NU.LocalTheory.ResidueFieldAt P) := by
    exact Finite.of_equiv
      ((NumberField.RingOfIntegers E.field) ⧸ P.asIdeal)
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
        (NU.LocalTheory.primeValuationSubring P)).toEquiv
  have hqprime : Nat.Prime (NU.LocalTheory.residueCharacteristic P) := by
    exact CharP.prime_ringChar (NU.LocalTheory.ResidueFieldAt P)
  exact (Nat.coprime_primes p.1.2 hqprime).mpr hq.symm

/-- At a completely split rational prime, its residue characteristic is its
rational norm. -/
private theorem residueCharacteristic_eq_norm_of_split
    (E : NumberFieldInOmega) (q : NU.Chebotarev.PrimeIdeal ℚ)
    (P : NU.LocalTheory.FinitePlace E.field)
    (hPq : rationalPrime E P = q)
    (he : absoluteRamificationIndex E P = 1)
    (hf : absoluteResidueDegree E P = 1) :
    NU.LocalTheory.residueCharacteristic P =
      NU.Chebotarev.PrimeIdeal.norm q := by
  have hrestrict :
      NU.LocalTheory.residueCharacteristic (rationalPrime E P) =
        NU.LocalTheory.residueCharacteristic P :=
    regularKernel_residueCharacteristic_restrictFinitePlace ℚ P
  calc
    NU.LocalTheory.residueCharacteristic P =
        NU.LocalTheory.residueCharacteristic (rationalPrime E P) :=
      hrestrict.symm
    _ = NU.LocalTheory.residueCharacteristic q := congrArg
      NU.LocalTheory.residueCharacteristic hPq
    _ = NU.Chebotarev.PrimeIdeal.norm q :=
      regularKernel_rational_residueCharacteristic_eq_norm q

/-- The relative cyclotomic degree inherits the `p - 1` bound from the
faithful cyclotomic character. -/
private theorem cyclotomicCompositum_finrank_le_p_sub_one
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    letI : Algebra N.field (cyclotomicCompositum N p).field :=
      (IntermediateField.inclusion (le_cyclotomicCompositum N p)).toAlgebra
    Module.finrank N.field (cyclotomicCompositum N p).field ≤
      (p : ℕ) - 1 := by
  let E := cyclotomicCompositum N p
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion (le_cyclotomicCompositum N p)).toAlgebra
  letI : IsGalois N.field E.field :=
    cyclotomicCompositum_isGaloisOverBase N p
  let equivDelta : CyclotomicDelta N p ≃
      (E.field ≃ₐ[N.field] E.field) :=
    { toFun := fun delta =>
        { delta.1.toRingEquiv with
          commutes' := fun x => delta.2 x }
      invFun := fun sigma =>
        ⟨sigma.restrictScalars ℚ, fun x => sigma.commutes x⟩
      left_inv := by intro delta; apply Subtype.ext; rfl
      right_inv := by intro sigma; apply AlgEquiv.ext; intro x; rfl }
  have hcard : Nat.card (CyclotomicDelta N p) =
      Nat.card (E.field ≃ₐ[N.field] E.field) :=
    Nat.card_congr equivDelta
  have hfin : Nat.card (E.field ≃ₐ[N.field] E.field) =
      Module.finrank N.field E.field :=
    IsGalois.card_aut_eq_finrank N.field E.field
  have hdvd : Module.finrank N.field E.field ∣ (p : ℕ) - 1 := by
    rw [← hfin, ← hcard]
    exact cyclotomicDelta_card_dvd_p_sub_one N p
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt p.1.2.one_lt) hdvd

/-- Equal prime degrees in two sides of a finite field tower cancel from the
remaining relative degrees. -/
private theorem regularKernel_cancel_tower_degrees
    {N E L R : Type*} [Field N] [Field E] [Field L] [Field R]
    [Algebra N E] [Algebra N L] [Algebra E R] [Algebra L R]
    [Algebra N R] [IsScalarTower N E R] [IsScalarTower N L R]
    [FiniteDimensional N E] [FiniteDimensional N L]
    [FiniteDimensional E R] [FiniteDimensional L R]
    (p : ℕ) (hp : 0 < p)
    (hER : Module.finrank E R = p)
    (hNL : Module.finrank N L = p) :
    Module.finrank L R = Module.finrank N E := by
  have hEtower : Module.finrank N E * Module.finrank E R =
      Module.finrank N R := Module.finrank_mul_finrank N E R
  have hLtower : Module.finrank N L * Module.finrank L R =
      Module.finrank N R := Module.finrank_mul_finrank N L R
  rw [hER] at hEtower
  rw [hNL] at hLtower
  have heq : p * Module.finrank L R = Module.finrank N E * p :=
    hLtower.trans hEtower.symm
  apply Nat.eq_of_mul_eq_mul_left hp
  simpa [Nat.mul_comm] using heq

/-! ### Rung C: transport through cyclotomic Kummer descent -/

private theorem regularKernel_liesOver_of_restrict_eq
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (W : NU.LocalTheory.FinitePlace L)
    (P : NU.LocalTheory.FinitePlace K)
    (h : NU.LocalTheory.restrictFinitePlace K W = P) :
    W.asIdeal.LiesOver P.asIdeal := ⟨by
  rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal, h]⟩

private theorem finitePlaceAbove_numberFieldExtension
    {K : NumberFieldInOmega} (L : NumberFieldExtension K)
    (P : NU.LocalTheory.FinitePlace K.field) :
    ∃ W : NU.LocalTheory.FinitePlace L.field.field,
      NU.LocalTheory.restrictFinitePlace K.field W = P := by
  let A := NumberField.RingOfIntegers K.field
  let B := NumberField.RingOfIntegers L.field.field
  letI : NoZeroSMulDivisors A B := ⟨by
    intro c x h
    have hzero : algebraMap A B c * x = 0 := h
    rcases mul_eq_zero.mp hzero with hc | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_eq_zero_iff A B).mp hc)
    · exact Or.inr hx⟩
  obtain ⟨J, _, hJprime, hJcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B) (by
      intro x hx
      have hxmap : algebraMap A B x = 0 := hx
      have hx0 : x = 0 :=
        (FaithfulSMul.algebraMap_eq_zero_iff A B).mp hxmap
      subst x
      exact P.asIdeal.zero_mem)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [← hJcomap, h]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact FaithfulSMul.algebraMap_eq_zero_iff A B
  let W : NU.LocalTheory.FinitePlace L.field.field := ⟨J, hJprime, hJ0⟩
  refine ⟨W, ?_⟩
  apply HeightOneSpectrum.ext
  rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
  exact hJcomap

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
-- The two compositum degree towers require several transported field instances.
/-- Ramification and tameness of the radical transport through
`E L = E(sqrt[p]{a})` to ramification of `L/N`. -/
private theorem transportRadicalRamificationToDescent
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p)
    (a : (cyclotomicCompositum N p).fieldˣ)
    (L : NumberFieldExtension N)
    (hLdegree : Module.finrank N.field L.field.field = (p : ℕ))
    (hval : D.P.valuation (cyclotomicCompositum N p).field a.1 = exp (-1))
    (hcompositum :
      (cyclotomicCompositum N p).field ⊔ L.field.field =
        radicalExtension (cyclotomicCompositum N p) p a)
    (hram : IsRamifiedAt
      (radicalNumberFieldExtension (cyclotomicCompositum N p) p a) D.P)
    (htame : IsTamelyRamifiedAt
      (radicalNumberFieldExtension (cyclotomicCompositum N p) p a) D.P) :
    IsRamifiedAt L (D.v 1) := by
  let E := cyclotomicCompositum N p
  let R := radicalNumberFieldExtension E p a
  obtain ⟨W, hWP, _hWram⟩ := hram
  have hLR : L.field.field ≤ R.field.field := by
    intro x hx
    have hxR : x ∈ radicalExtension (cyclotomicCompositum N p) p a := by
      rw [← hcompositum]
      exact (show L.field.field ≤
        (cyclotomicCompositum N p).field ⊔ L.field.field from le_sup_right) hx
    exact hxR
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  letI : IsScalarTower ℚ N.field E.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra N.field R.field.field :=
    (IntermediateField.inclusion (le_sup_left.trans R.le_base)).toAlgebra
  letI : IsScalarTower N.field E.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra L.field.field R.field.field :=
    (IntermediateField.inclusion hLR).toAlgebra
  letI : IsScalarTower N.field L.field.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℚ E.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℚ N.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hpNotDvdOne : ¬(p : ℕ) ∣ 1 := by
    intro hp
    exact p.1.2.ne_one (Nat.eq_one_of_dvd_one hp)
  have hRdegree : Module.finrank E.field R.field.field = (p : ℕ) := by
    exact radicalNumberFieldExtension_finrank_of_valuation_not_dvd
      (cyclotomicCompositum N p) p a D.P 1 hval hpNotDvdOne
  have heWPRel : relativeRamificationIndex
      (radicalNumberFieldExtension (cyclotomicCompositum N p) p a)
        D.P W = (p : ℕ) :=
    kummerRadical_ramificationIndex_eq_prime
      (cyclotomicCompositum N p) p a D.P 1 hval hpNotDvdOne W hWP
  have heWP : W.asIdeal.ramificationIdx' (𝓞 E.field) = (p : ℕ) :=
    heWPRel
  have _hcoprime : Nat.Coprime (p : ℕ)
      (NU.LocalTheory.residueCharacteristic D.P) := by
    have hcoprime := htame W hWP
    rw [heWPRel] at hcoprime
    exact hcoprime
  have hWoverP : W.asIdeal.LiesOver D.P.asIdeal :=
    regularKernel_liesOver_of_restrict_eq W D.P hWP
  letI : W.asIdeal.LiesOver D.P.asIdeal := hWoverP
  have hPsplit := D.splitCyclotomic.2 D.P D.P_over_q
  have hqPe : D.P.asIdeal.ramificationIdx' (𝓞 ℚ) = 1 :=
    hPsplit.1
  have hvoverq : (D.v 1).asIdeal.LiesOver D.q.asIdeal :=
    regularKernel_liesOver_of_restrict_eq (D.v 1) D.q (D.v_over_q 1)
  have hPoverv : D.P.asIdeal.LiesOver (D.v 1).asIdeal :=
    regularKernel_liesOver_of_restrict_eq D.P (D.v 1) D.P_over_identity
  letI : (D.v 1).asIdeal.LiesOver D.q.asIdeal := hvoverq
  letI : D.P.asIdeal.LiesOver (D.v 1).asIdeal := hPoverv
  letI := Localization.AtPrime.algebraOfLiesOver
    (D.v 1).asIdeal D.P.asIdeal
  have heTowerQP := Ideal.ramificationIdx'_tower'
    (R := 𝓞 ℚ) (D.v 1).asIdeal D.P.asIdeal
  have hvPe : D.P.asIdeal.ramificationIdx' (𝓞 N.field) = 1 := by
    rw [hqPe] at heTowerQP
    exact Nat.eq_one_of_mul_eq_one_left heTowerQP.symm
  have hWoverv : W.asIdeal.LiesOver (D.v 1).asIdeal :=
    regularKernel_liesOver_of_restrict_eq W (D.v 1) (by
      calc
        NU.LocalTheory.restrictFinitePlace N.field W =
            NU.LocalTheory.restrictFinitePlace N.field
              (NU.LocalTheory.restrictFinitePlace E.field W) :=
          (regularKernel_restrictFinitePlace_tower W).symm
        _ = NU.LocalTheory.restrictFinitePlace N.field D.P :=
          congrArg (NU.LocalTheory.restrictFinitePlace N.field) hWP
        _ = D.v 1 := D.P_over_identity)
  letI : W.asIdeal.LiesOver (D.v 1).asIdeal := hWoverv
  letI := Localization.AtPrime.algebraOfLiesOver D.P.asIdeal W.asIdeal
  have heTowerPW := Ideal.ramificationIdx'_tower'
    (R := 𝓞 N.field) D.P.asIdeal W.asIdeal
  have hvWe : W.asIdeal.ramificationIdx' (𝓞 N.field) = (p : ℕ) := by
    rw [hvPe, heWP, one_mul] at heTowerPW
    exact heTowerPW
  let w : NU.LocalTheory.FinitePlace L.field.field :=
    NU.LocalTheory.restrictFinitePlace L.field.field W
  have hWw : NU.LocalTheory.restrictFinitePlace L.field.field W = w := rfl
  have hwv : NU.LocalTheory.restrictFinitePlace N.field w = D.v 1 := by
    calc
      NU.LocalTheory.restrictFinitePlace N.field w =
          NU.LocalTheory.restrictFinitePlace N.field W :=
        regularKernel_restrictFinitePlace_tower W
      _ = D.v 1 := by
        apply HeightOneSpectrum.ext
        exact hWoverv.over.symm
  have hwoverv : w.asIdeal.LiesOver (D.v 1).asIdeal :=
    regularKernel_liesOver_of_restrict_eq w (D.v 1) hwv
  have hWoverw : W.asIdeal.LiesOver w.asIdeal :=
    regularKernel_liesOver_of_restrict_eq W w hWw
  letI : w.asIdeal.LiesOver (D.v 1).asIdeal := hwoverv
  letI : W.asIdeal.LiesOver w.asIdeal := hWoverw
  letI := Localization.AtPrime.algebraOfLiesOver w.asIdeal W.asIdeal
  have heTowerLW := Ideal.ramificationIdx'_tower'
    (R := 𝓞 N.field) w.asIdeal W.asIdeal
  have hEbound : Module.finrank N.field E.field ≤ (p : ℕ) - 1 :=
    cyclotomicCompositum_finrank_le_p_sub_one N p
  have hRLdegree : Module.finrank L.field.field R.field.field =
      Module.finrank N.field E.field :=
    regularKernel_cancel_tower_degrees (p : ℕ) p.1.2.pos
      hRdegree hLdegree
  let ALR := NumberField.RingOfIntegers L.field.field
  let BLR := NumberField.RingOfIntegers R.field.field
  letI : NoZeroSMulDivisors ALR BLR := ⟨by
    intro c x h
    have hzero : algebraMap ALR BLR c * x = 0 := h
    rcases mul_eq_zero.mp hzero with hc | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_eq_zero_iff ALR BLR).mp hc)
    · exact Or.inr hx⟩
  refine ⟨w, hwv, ?_⟩
  have hewpos : 0 < w.asIdeal.ramificationIdx' (𝓞 N.field) :=
    Ideal.ramificationIdx'_pos w.asIdeal (𝓞 N.field)
  by_contra hnotRamified
  have hewle : w.asIdeal.ramificationIdx' (𝓞 N.field) ≤ 1 :=
    Nat.le_of_not_gt hnotRamified
  have hew : w.asIdeal.ramificationIdx' (𝓞 N.field) = 1 := by
    omega
  rw [hvWe, hew, one_mul] at heTowerLW
  have hpLeDegree : (p : ℕ) ≤
      Module.finrank L.field.field R.field.field := by
    rw [heTowerLW]
    rw [← Ideal.ramificationIdx_eq_ramificationIdx'
      w.asIdeal W.asIdeal w.ne_bot]
    exact Ideal.ramificationIdx_le_finrank
      BLR L.field.field R.field.field W.asIdeal
  have hpLeSub : (p : ℕ) ≤ (p : ℕ) - 1 :=
    hpLeDegree.trans (hRLdegree.le.trans hEbound)
  exact (Nat.not_le_of_lt
    (Nat.sub_lt p.1.2.pos Nat.zero_lt_one)) hpLeSub

/-- Complete splitting of every nonidentity radical localization transports
through the same compositum equality to `L/N`. -/
private theorem transportRadicalSplittingToDescent
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} (D : AsymmetricPrimeData N p)
    (a : (cyclotomicCompositum N p).fieldˣ)
    (L : NumberFieldExtension N)
    (hcompositum :
      (cyclotomicCompositum N p).field ⊔ L.field.field =
        radicalExtension (cyclotomicCompositum N p) p a)
    (hsplit : ∀ g : N.field ≃ₐ[ℚ] N.field, g ≠ 1 →
      ∀ Q : NU.LocalTheory.FinitePlace
          (cyclotomicCompositum N p).field,
        restrictCyclotomicPlace N p Q = D.v g →
        SplitsCompletelyAbove
          (radicalNumberFieldExtension (cyclotomicCompositum N p) p a) Q) :
    ∀ g : N.field ≃ₐ[ℚ] N.field, g ≠ 1 →
      SplitsCompletelyAbove L (D.v g) := by
  intro g hg
  let E := cyclotomicCompositum N p
  let R := radicalNumberFieldExtension E p a
  have hLR : L.field.field ≤ R.field.field := by
    intro x hx
    change x ∈ radicalExtension (cyclotomicCompositum N p) p a
    rw [← hcompositum]
    exact (show L.field.field ≤
      (cyclotomicCompositum N p).field ⊔ L.field.field from le_sup_right) hx
  let LR : NumberFieldExtension L.field :=
    { field := R.field
      le_base := hLR }
  letI : Algebra N.field E.field :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  letI : IsScalarTower ℚ N.field E.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra N.field R.field.field :=
    (IntermediateField.inclusion (le_sup_left.trans R.le_base)).toAlgebra
  letI : IsScalarTower N.field E.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra L.field.field R.field.field :=
    (IntermediateField.inclusion hLR).toAlgebra
  letI : IsScalarTower N.field L.field.field R.field.field :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  constructor
  · exact finitePlaceAbove_numberFieldExtension L (D.v g)
  · intro w hw
    obtain ⟨W, hWw⟩ := finitePlaceAbove_numberFieldExtension LR w
    let Q : NU.LocalTheory.FinitePlace E.field :=
      NU.LocalTheory.restrictFinitePlace E.field W
    have hWN : NU.LocalTheory.restrictFinitePlace N.field W = D.v g := by
      calc
        NU.LocalTheory.restrictFinitePlace N.field W =
            NU.LocalTheory.restrictFinitePlace N.field
              (NU.LocalTheory.restrictFinitePlace L.field.field W) :=
          (regularKernel_restrictFinitePlace_tower W).symm
        _ = NU.LocalTheory.restrictFinitePlace N.field w :=
          congrArg (NU.LocalTheory.restrictFinitePlace N.field) hWw
        _ = D.v g := hw
    have hQN : restrictCyclotomicPlace N p Q = D.v g := by
      change NU.LocalTheory.restrictFinitePlace N.field Q = D.v g
      calc
        NU.LocalTheory.restrictFinitePlace N.field Q =
            NU.LocalTheory.restrictFinitePlace N.field W :=
          regularKernel_restrictFinitePlace_tower W
        _ = D.v g := hWN
    have hqQ : rationalPrime E Q = D.q := by
      change NU.LocalTheory.restrictFinitePlace ℚ Q = D.q
      calc
        NU.LocalTheory.restrictFinitePlace ℚ Q =
            NU.LocalTheory.restrictFinitePlace ℚ
              (NU.LocalTheory.restrictFinitePlace N.field Q) :=
          (regularKernel_restrictFinitePlace_tower Q).symm
        _ = NU.LocalTheory.restrictFinitePlace ℚ (D.v g) :=
          congrArg (NU.LocalTheory.restrictFinitePlace ℚ) hQN
        _ = D.q := D.v_over_q g
    have hQsplit := D.splitCyclotomic.2 Q hqQ
    have hWsplit := hsplit g hg Q hQN
    letI : IsScalarTower ℚ E.field R.field.field :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ℚ N.field R.field.field :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hWQ : NU.LocalTheory.restrictFinitePlace E.field W = Q := rfl
    have hQover : Q.asIdeal.LiesOver D.q.asIdeal :=
      regularKernel_liesOver_of_restrict_eq Q D.q hqQ
    have hWoverQ : W.asIdeal.LiesOver Q.asIdeal :=
      regularKernel_liesOver_of_restrict_eq W Q hWQ
    letI : Q.asIdeal.LiesOver D.q.asIdeal := hQover
    letI : W.asIdeal.LiesOver Q.asIdeal := hWoverQ
    have hQe : Q.asIdeal.ramificationIdx' (𝓞 ℚ) = 1 :=
      hQsplit.1
    have hQf : Q.asIdeal.inertiaDeg' (𝓞 ℚ) = 1 :=
      hQsplit.2
    have hWindices := hWsplit.2 W hWQ
    have hWe : W.asIdeal.ramificationIdx' (𝓞 E.field) = 1 :=
      hWindices.1
    have hWf : W.asIdeal.inertiaDeg' (𝓞 E.field) = 1 :=
      hWindices.2
    letI := Localization.AtPrime.algebraOfLiesOver Q.asIdeal W.asIdeal
    have heTowerQW := Ideal.ramificationIdx'_tower'
      (R := 𝓞 ℚ) Q.asIdeal W.asIdeal
    have hfTowerQW := Ideal.inertiaDeg'_tower
      (R := 𝓞 ℚ) Q.asIdeal W.asIdeal
    have hqWe : W.asIdeal.ramificationIdx' (𝓞 ℚ) = 1 := by
      rw [hQe, hWe, one_mul] at heTowerQW
      exact heTowerQW
    have hqWf : W.asIdeal.inertiaDeg' (𝓞 ℚ) = 1 := by
      rw [hQf, hWf, one_mul] at hfTowerQW
      exact hfTowerQW
    have hvover : (D.v g).asIdeal.LiesOver D.q.asIdeal :=
      regularKernel_liesOver_of_restrict_eq (D.v g) D.q (D.v_over_q g)
    have hWoverv : W.asIdeal.LiesOver (D.v g).asIdeal :=
      regularKernel_liesOver_of_restrict_eq W (D.v g) hWN
    letI : (D.v g).asIdeal.LiesOver D.q.asIdeal := hvover
    letI : W.asIdeal.LiesOver (D.v g).asIdeal := hWoverv
    letI := Localization.AtPrime.algebraOfLiesOver
      (D.v g).asIdeal W.asIdeal
    have heTowerNW := Ideal.ramificationIdx'_tower'
      (R := 𝓞 ℚ) (D.v g).asIdeal W.asIdeal
    have hfTowerNW := Ideal.inertiaDeg'_tower
      (R := 𝓞 ℚ) (D.v g).asIdeal W.asIdeal
    have hvWe : W.asIdeal.ramificationIdx' (𝓞 N.field) = 1 := by
      rw [hqWe] at heTowerNW
      exact Nat.eq_one_of_mul_eq_one_left heTowerNW.symm
    have hvWf : W.asIdeal.inertiaDeg' (𝓞 N.field) = 1 := by
      rw [hqWf] at hfTowerNW
      exact Nat.eq_one_of_mul_eq_one_left hfTowerNW.symm
    have hwover : w.asIdeal.LiesOver (D.v g).asIdeal :=
      regularKernel_liesOver_of_restrict_eq w (D.v g) hw
    have hWoverw : W.asIdeal.LiesOver w.asIdeal :=
      regularKernel_liesOver_of_restrict_eq W w hWw
    letI : w.asIdeal.LiesOver (D.v g).asIdeal := hwover
    letI : W.asIdeal.LiesOver w.asIdeal := hWoverw
    letI := Localization.AtPrime.algebraOfLiesOver w.asIdeal W.asIdeal
    have heTowerLW := Ideal.ramificationIdx'_tower'
      (R := 𝓞 N.field) w.asIdeal W.asIdeal
    have hfTowerLW := Ideal.inertiaDeg'_tower
      (R := 𝓞 N.field) w.asIdeal W.asIdeal
    have hwe : w.asIdeal.ramificationIdx' (𝓞 N.field) = 1 := by
      rw [hvWe] at heTowerLW
      exact Nat.eq_one_of_dvd_one ⟨_, heTowerLW⟩
    have hwf : w.asIdeal.inertiaDeg' (𝓞 N.field) = 1 := by
      rw [hvWf] at hfTowerLW
      exact Nat.eq_one_of_dvd_one ⟨_, hfTowerLW⟩
    exact ⟨hwe, hwf⟩

/-- Assembly of rungs A--C into the exact asymmetric-cyclic seam. -/
private theorem asymmetricCyclicConstruction : AsymmetricCyclicConstruction := by
  intro N _ p
  obtain ⟨D⟩ := asymmetricPrimeData_exists N p
  obtain ⟨A⟩ := asymmetricApproximationData_exists D
  obtain ⟨K⟩ := asymmetricProjectedKummerData_exists D A
  let E := cyclotomicCompositum N p
  let b : E.fieldˣ := K.b
  let a : E.fieldˣ := K.a
  have hclass : (QuotientGroup.mk a : KummerClass E (p : ℕ)) =
      projectedKummerClass N p (QuotientGroup.mk b) := K.class_eq
  have hpNotDvdOne : ¬(p : ℕ) ∣ 1 := by
    intro hp
    exact p.1.2.ne_one (Nat.eq_one_of_dvd_one hp)
  have hclassNontrivial :
      projectedKummerClass N p (QuotientGroup.mk b) ≠ 1 := by
    intro htrivial
    exact (kummerClass_ne_one_of_valuation_not_dvd E p a D.P 1
      K.valuation_one hpNotDvdOne) (hclass.trans htrivial)
  have heigen := projectedKummerClass_eigen N p (QuotientGroup.mk b)
  obtain ⟨L, hLgal, hLdegree, hLcyclic, hcompositum⟩ :=
    kummerDescentConstruction N p
      (projectedKummerClass N p (QuotientGroup.mk b))
      hclassNontrivial heigen a hclass
  have hlocal := projectedKummerRepresentative_localPowerAway D A K
  have hradRam : IsRamifiedAt (radicalNumberFieldExtension E p a) D.P :=
    tameKummerRadical_ramified E p a D.P 1 K.valuation_one hpNotDvdOne
  have hPsplit := D.splitCyclotomic.2 D.P D.P_over_q
  have hresidue : NU.LocalTheory.residueCharacteristic D.P =
      NU.Chebotarev.PrimeIdeal.norm D.q :=
    residueCharacteristic_eq_norm_of_split E D.q D.P D.P_over_q
      hPsplit.1 hPsplit.2
  have hresidueNe : NU.LocalTheory.residueCharacteristic D.P ≠ (p : ℕ) := by
    rw [hresidue]
    exact D.norm_ne
  have hradTame : IsTamelyRamifiedAt
      (radicalNumberFieldExtension E p a) D.P :=
    tameKummerRadical_isTame E p a D.P 1 K.valuation_one
      hpNotDvdOne hresidueNe
  have hroot : IsPrimitiveRoot (cyclotomicRoot N p) (p : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective (f := E.field.val)
    · exact primitiveRootInOmega_spec p
    · exact E.field.val.injective
  have hradSplit :
      ∀ g : N.field ≃ₐ[ℚ] N.field, g ≠ 1 →
        ∀ Q : NU.LocalTheory.FinitePlace E.field,
          restrictCyclotomicPlace N p Q = D.v g →
          SplitsCompletelyAbove (radicalNumberFieldExtension E p a) Q := by
    intro g hg Q hQ
    exact tameKummerRadical_splits E p a Q
      ⟨cyclotomicRoot N p, hroot⟩ (hlocal g hg Q hQ)
  have hLram : IsRamifiedAt L (D.v 1) :=
    transportRadicalRamificationToDescent D a L hLdegree K.valuation_one
      hcompositum hradRam hradTame
  have hLsplit : ∀ g : N.field ≃ₐ[ℚ] N.field, g ≠ 1 →
      SplitsCompletelyAbove L (D.v g) :=
    transportRadicalSplittingToDescent D a L hcompositum hradSplit
  exact ⟨D.q, D.norm_ne, D.splitBase, D.v, D.v_over_q,
    D.v_injective, D.v_surjective, D.v_conjugate, b, a, hclass,
    hclassNontrivial, L, hLgal, hLdegree, hLcyclic, hLram, hLsplit,
    hcompositum⟩

/-! ### Rung D: conjugate compositum and regular coordinates -/

/-- A chosen family of Galois conjugates of one cyclic extension and its
literal finite compositum `iSup_g L_g`. -/
private structure RegularConjugateCompositumData
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) where
  seed : NumberFieldExtension N
  q : NU.Chebotarev.PrimeIdeal ℚ
  norm_ne : NU.Chebotarev.PrimeIdeal.norm q ≠ (p : ℕ)
  v : (N.field ≃ₐ[ℚ] N.field) → NU.LocalTheory.FinitePlace N.field
  v_over_q : ∀ g, rationalPrime N (v g) = q
  v_injective : Function.Injective v
  v_conjugate :
    ∀ g, v g = NU.LocalTheory.conjugateFinitePlace ℚ g (v 1)
  lift : (N.field ≃ₐ[ℚ] N.field) → RationalAbsoluteGaloisGroup
  lift_restrict : ∀ g (x : N.field), lift g x.1 = (g x).1
  factor : (N.field ≃ₐ[ℚ] N.field) → NumberFieldExtension N
  factor_one : factor 1 = seed
  factor_eq_conjugate :
    ∀ g, (factor g).field.field =
      conjugateField (lift g) seed.field.field
  factor_isGalois :
    ∀ g, IsGalois N.field (factor g).field.field
  factor_degree :
    ∀ g, Module.finrank N.field (factor g).field.field = (p : ℕ)
  factor_cyclic :
    ∀ g, IsCyclic ((factor g).field.field ≃ₐ[N.field]
      (factor g).field.field)
  factor_ramified : ∀ g, IsRamifiedAt (factor g) (v g)
  factor_split :
    ∀ g h, h ≠ g → SplitsCompletelyAbove (factor g) (v h)
  overfield : GaloisOverfield N
  overfield_lift :
    (g : N.field ≃ₐ[ℚ] N.field) →
      overfield.toExtension.field.field ≃ₐ[ℚ]
        overfield.toExtension.field.field
  overfield_lift_restrict :
    ∀ g, AlgEquiv.restrictNormalHom N.field (overfield_lift g) = g
  overfield_lift_factor :
    ∀ g k (x : overfield.toExtension.field.field),
      (overfield_lift g x).1 ∈ (factor (g * k)).field.field ↔
        x.1 ∈ (factor k).field.field
  field_eq_iSup :
    overfield.toExtension.field.field = ⨆ g, (factor g).field.field

private noncomputable def regularKernelMapFinitePlace
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (e : K ≃+* L) (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.FinitePlace L where
  asIdeal := Ideal.map
    (NumberField.RingOfIntegers.mapRingEquiv e) v.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv
    (NumberField.RingOfIntegers.mapRingEquiv e)
  ne_bot :=
    (Ideal.map_eq_bot_iff_of_injective
      (f := (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom)
      (NumberField.RingOfIntegers.mapRingEquiv e).injective).not.mpr
        v.ne_bot

@[simp]
private theorem regularKernelMapFinitePlace_symm
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (e : K ≃+* L) (v : NU.LocalTheory.FinitePlace K) :
    regularKernelMapFinitePlace e.symm
      (regularKernelMapFinitePlace e v) = v := by
  apply HeightOneSpectrum.ext
  dsimp [regularKernelMapFinitePlace]
  let eO := NumberField.RingOfIntegers.mapRingEquiv e
  change Ideal.map eO.symm.toRingHom
      (Ideal.map eO.toRingHom v.asIdeal) = v.asIdeal
  rw [Ideal.map_map]
  have hcomp : eO.symm.toRingHom.comp eO.toRingHom = RingHom.id _ := by
    ext x
    exact congrArg Subtype.val (eO.symm_apply_apply x)
  rw [hcomp, Ideal.map_id]

private theorem regularKernelMapFinitePlace_injective
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (e : K ≃+* L) :
    Function.Injective (regularKernelMapFinitePlace e) := by
  intro v w h
  have h' := congrArg (regularKernelMapFinitePlace e.symm) h
  simpa using h'

private theorem regularKernelMapFinitePlace_restrict
    {K L K' L' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [NumberField K] [NumberField L] [NumberField K'] [NumberField L']
    [Algebra K L] [Algebra K' L']
    (f : K ≃+* K') (g : L ≃+* L')
    (hcomp : (algebraMap (𝓞 K') (𝓞 L')).comp
        (NumberField.RingOfIntegers.mapRingEquiv f).toRingHom =
      (NumberField.RingOfIntegers.mapRingEquiv g).toRingHom.comp
        (algebraMap (𝓞 K) (𝓞 L)))
    (w : NU.LocalTheory.FinitePlace L) :
    NU.LocalTheory.restrictFinitePlace K'
        (regularKernelMapFinitePlace g w) =
      regularKernelMapFinitePlace f
        (NU.LocalTheory.restrictFinitePlace K w) := by
  apply HeightOneSpectrum.ext
  rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
  dsimp [regularKernelMapFinitePlace]
  rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
  let fO := NumberField.RingOfIntegers.mapRingEquiv f
  let gO := NumberField.RingOfIntegers.mapRingEquiv g
  change Ideal.comap (algebraMap (𝓞 K') (𝓞 L'))
      (Ideal.map gO.toRingHom w.asIdeal) =
    Ideal.map fO.toRingHom
      (Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal)
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective fO.toRingHom fO.surjective]
    refine ⟨fO.symm x, ?_, fO.apply_symm_apply x⟩
    change algebraMap (𝓞 K) (𝓞 L) (fO.symm x) ∈ w.asIdeal
    have hx' : algebraMap (𝓞 K') (𝓞 L') x ∈
        Ideal.map gO.toRingHom w.asIdeal := hx
    rw [Ideal.mem_map_iff_of_surjective gO.toRingHom gO.surjective]
      at hx'
    obtain ⟨z, hz, hzg⟩ := hx'
    have hsq : z = algebraMap (𝓞 K) (𝓞 L) (fO.symm x) := by
      apply gO.injective
      have hzg' : gO z = algebraMap (𝓞 K') (𝓞 L') x := hzg
      rw [hzg']
      have hc := DFunLike.congr_fun hcomp (fO.symm x)
      change algebraMap (𝓞 K') (𝓞 L') (fO (fO.symm x)) =
        gO (algebraMap (𝓞 K) (𝓞 L) (fO.symm x)) at hc
      rwa [fO.apply_symm_apply] at hc
    rwa [← hsq]
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective fO.toRingHom fO.surjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change algebraMap (𝓞 K') (𝓞 L') (fO y) ∈
      Ideal.map gO.toRingHom w.asIdeal
    rw [Ideal.mem_map_iff_of_surjective gO.toRingHom gO.surjective]
    refine ⟨algebraMap (𝓞 K) (𝓞 L) y, hy, ?_⟩
    exact (DFunLike.congr_fun hcomp y).symm

private theorem regularKernel_ramificationIdx_map_equiv
    {R S R' S' : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsDomain R] [IsDomain R'] [IsDedekindDomain S] [IsDedekindDomain S']
    [Algebra R S] [Algebra R' S']
    [Module.IsTorsionFree R S] [Module.IsTorsionFree R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hcomp : (algebraMap R' S').comp f.toRingHom =
      g.toRingHom.comp (algebraMap R S))
    (P : Ideal R) (Q : Ideal S) [Q.LiesOver P] [Q.IsPrime]
    (hP : P ≠ ⊥) :
    (Ideal.map g Q).ramificationIdx' R' =
      Q.ramificationIdx' R := by
  have hover : (Ideal.map g Q).LiesOver (Ideal.map f P) := by
    constructor
    rw [Ideal.under_def]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_map_iff_of_surjective f f.surjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Ideal.mem_comap,
        Ideal.mem_map_iff_of_surjective g g.surjective]
      refine ⟨algebraMap R S y, ?_, ?_⟩
      · change y ∈ Ideal.under R Q
        rw [← Ideal.over_def Q P]
        exact hy
      · exact (DFunLike.congr_fun hcomp y).symm
    · intro x hx
      rw [Ideal.mem_map_iff_of_surjective f f.surjective]
      refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
      have hx' : algebraMap R' S' x ∈ Ideal.map g Q := hx
      rw [Ideal.mem_map_iff_of_surjective g g.surjective] at hx'
      obtain ⟨z, hz, hzg⟩ := hx'
      have hsq : z = algebraMap R S (f.symm x) := by
        apply g.injective
        rw [hzg]
        simpa using DFunLike.congr_fun hcomp (f.symm x)
      rw [hsq] at hz
      change f.symm x ∈ Ideal.under R Q at hz
      rwa [← Ideal.over_def Q P] at hz
  letI : (Ideal.map g Q).LiesOver (Ideal.map f P) := hover
  have hmapP : Ideal.map f P ≠ ⊥ := by
    intro h
    exact hP ((Ideal.map_eq_bot_iff_of_injective f.injective).mp h)
  rw [← Ideal.ramificationIdx_eq_ramificationIdx'
      (Ideal.map f P) (Ideal.map g Q) hmapP,
    ← Ideal.ramificationIdx_eq_ramificationIdx' P Q hP]
  unfold Ideal.ramificationIdx
  congr 1
  ext n
  change Ideal.map (algebraMap R' S') (Ideal.map f.toRingHom P) ≤
      Ideal.map g.toRingHom Q ^ n ↔
        Ideal.map (algebraMap R S) P ≤ Q ^ n
  have hleft :
      Ideal.map (algebraMap R' S') (Ideal.map f.toRingHom P) =
        Ideal.map g.toRingHom (Ideal.map (algebraMap R S) P) := by
    calc
      _ = Ideal.map ((algebraMap R' S').comp f.toRingHom) P :=
        Ideal.map_map f.toRingHom (algebraMap R' S')
      _ = Ideal.map (g.toRingHom.comp (algebraMap R S)) P := by
        rw [hcomp]
      _ = _ := (Ideal.map_map (algebraMap R S) g.toRingHom).symm
  rw [hleft, ← Ideal.map_pow g.toRingHom Q n]
  constructor
  · intro h
    have hh := (Ideal.map_le_iff_le_comap).mp h
    rw [Ideal.comap_map_of_surjective g.toRingHom g.surjective] at hh
    have hker : RingHom.ker g.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp g.injective
    rw [← RingHom.ker_eq_comap_bot, hker] at hh
    simpa using hh
  · exact Ideal.map_mono

private theorem regularKernel_inertiaDeg_map_equiv
    {R S R' S' : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (f : R ≃+* R') (g : S ≃+* S')
    (hcomp : (algebraMap R' S').comp f.toRingHom =
      g.toRingHom.comp (algebraMap R S))
    (P : Ideal R) (Q : Ideal S) [Q.LiesOver P]
    [P.IsMaximal] [Q.IsMaximal] :
    (Ideal.map g Q).inertiaDeg' R' =
      Q.inertiaDeg' R := by
  have hover : (Ideal.map g Q).LiesOver (Ideal.map f P) := by
    constructor
    rw [Ideal.under_def]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_map_iff_of_surjective f f.surjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Ideal.mem_comap,
        Ideal.mem_map_iff_of_surjective g g.surjective]
      refine ⟨algebraMap R S y, ?_, ?_⟩
      · change y ∈ Ideal.under R Q
        rw [← Ideal.over_def Q P]
        exact hy
      · exact (DFunLike.congr_fun hcomp y).symm
    · intro x hx
      rw [Ideal.mem_map_iff_of_surjective f f.surjective]
      refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
      have hx' : algebraMap R' S' x ∈ Ideal.map g Q := hx
      rw [Ideal.mem_map_iff_of_surjective g g.surjective] at hx'
      obtain ⟨z, hz, hzg⟩ := hx'
      have hsq : z = algebraMap R S (f.symm x) := by
        apply g.injective
        rw [hzg]
        simpa using DFunLike.congr_fun hcomp (f.symm x)
      rw [hsq] at hz
      change f.symm x ∈ Ideal.under R Q at hz
      rwa [← Ideal.over_def Q P] at hz
  letI : (Ideal.map g Q).LiesOver (Ideal.map f P) := hover
  letI : (Ideal.map f P).IsMaximal :=
    Ideal.IsMaximal.map_bijective f f.bijective inferInstance
  letI : (Ideal.map g Q).IsMaximal :=
    Ideal.IsMaximal.map_bijective g g.bijective inferInstance
  rw [← Ideal.inertiaDeg_eq_inertiaDeg' (Ideal.map f P) (Ideal.map g Q),
    ← Ideal.inertiaDeg_eq_inertiaDeg' P Q,
    Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap]
  let ef : (R ⧸ P) ≃+* (R' ⧸ Ideal.map f P) :=
    Ideal.quotientEquiv P (Ideal.map f P) f rfl
  let eg : (S ⧸ Q) ≃+* (S' ⧸ Ideal.map g Q) :=
    Ideal.quotientEquiv Q (Ideal.map g Q) g rfl
  refine (Algebra.finrank_eq_of_equiv_equiv ef eg ?_).symm
  apply Ideal.Quotient.ringHom_ext
  ext x
  change Ideal.Quotient.mk (Ideal.map g Q)
      (algebraMap R' S' (f x)) =
    Ideal.Quotient.mk (Ideal.map g Q) (g (algebraMap R S x))
  have hc : algebraMap R' S' (f x) = g (algebraMap R S x) := by
    simpa using DFunLike.congr_fun hcomp x
  rw [hc]

private noncomputable def regularKernelSemilinearAutCongr
    {F E M N : Type*} [Field F] [Field E] [Field M] [Field N]
    [Algebra F E] [Algebra M N]
    (f : F ≃+* M) (g : E ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap F E)) :
    (E ≃ₐ[F] E) ≃* (N ≃ₐ[M] N) := by
  let forward (sigma : E ≃ₐ[F] E) : N ≃ₐ[M] N :=
    { (g.symm.trans sigma.toRingEquiv).trans g with
      commutes' := by
        intro x
        change g (sigma (g.symm (algebraMap M N x))) = algebraMap M N x
        have hsource : g.symm (algebraMap M N x) =
            algebraMap F E (f.symm x) := by
          apply g.injective
          rw [g.apply_symm_apply]
          have hc := DFunLike.congr_fun hcomp (f.symm x)
          simpa using hc
        rw [hsource, sigma.commutes]
        have hc := DFunLike.congr_fun hcomp (f.symm x)
        simpa using hc.symm }
  let backward (tau : N ≃ₐ[M] N) : E ≃ₐ[F] E :=
    { (g.trans tau.toRingEquiv).trans g.symm with
      commutes' := by
        intro x
        change g.symm (tau (g (algebraMap F E x))) = algebraMap F E x
        have htarget : g (algebraMap F E x) =
            algebraMap M N (f x) := by
          have hc := DFunLike.congr_fun hcomp x
          simpa using hc.symm
        rw [htarget, tau.commutes]
        apply g.injective
        rw [g.apply_symm_apply, htarget] }
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro sigma
        apply AlgEquiv.ext
        intro x
        simp [forward, backward]
      right_inv := by
        intro tau
        apply AlgEquiv.ext
        intro x
        simp [forward, backward]
      map_mul' := by
        intro sigma tau
        apply AlgEquiv.ext
        intro x
        simp [forward, AlgEquiv.mul_apply] }

/-- Form the finite Galois compositum of all conjugates of the asymmetric
cyclic extension. -/
private theorem regularConjugateCompositumData_exists
    (hAsymmetric : AsymmetricCyclicConstruction)
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    Nonempty (RegularConjugateCompositumData N p) := by
  classical
  letI : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : Normal ℚ Omega :=
    { isAlgebraic := fun x => Algebra.IsAlgebraic.isAlgebraic x
      splits' := fun _ => IsAlgClosed.splits _ }
  obtain ⟨q, hnorm, _hsplitN, v, hvq, hvinj, _hvsurj, hvconj,
    _b, _a, _hclass, _hne, L, hLgal, hLdegree, hLcyclic,
    hLramified, hLsplit, _hcompositum⟩ := hAsymmetric N p
  let lift : (N.field ≃ₐ[ℚ] N.field) → RationalAbsoluteGaloisGroup :=
    fun g => if hg : g = 1 then 1 else
      Classical.choose (AlgEquiv.restrictNormalHom_surjective Omega g)
  have hlift (g : N.field ≃ₐ[ℚ] N.field) (x : N.field) :
      lift g x.1 = (g x).1 := by
    by_cases hg : g = 1
    · subst g
      simp [lift]
    · let tau := Classical.choose
        (AlgEquiv.restrictNormalHom_surjective Omega g)
      have hs := Classical.choose_spec
        (AlgEquiv.restrictNormalHom_surjective Omega g)
      have hsx := DFunLike.congr_fun hs x
      have hlt : lift g = tau := dif_neg hg
      rw [hlt]
      calc
        tau x.1 = N.field.val
            ((AlgEquiv.restrictNormalHom N.field tau) x) :=
          (AlgEquiv.restrictNormal_commutes tau N.field x).symm
        _ = N.field.val (g x) := congrArg Subtype.val hsx
  let factorField (g : N.field ≃ₐ[ℚ] N.field) :
      IntermediateField ℚ Omega := conjugateField (lift g) L.field.field
  have hfactorFinite (g : N.field ≃ₐ[ℚ] N.field) :
      FiniteDimensional ℚ (factorField g) := by
    let e := IntermediateField.equivMap L.field.field (lift g).toAlgHom
    change FiniteDimensional ℚ
      (IntermediateField.map (lift g).toAlgHom L.field.field)
    exact e.toLinearEquiv.finiteDimensional
  have hfactorLe (g : N.field ≃ₐ[ℚ] N.field) :
      N.field ≤ factorField g := by
    intro x hx
    change x ∈ conjugateField (lift g) L.field.field
    rw [mem_conjugateField_iff]
    let xn : N.field := ⟨x, hx⟩
    have hinv : (lift g).symm x = (g.symm xn).1 := by
      apply (lift g).injective
      rw [(lift g).apply_symm_apply]
      calc
        x = (g (g.symm xn)).1 :=
          congrArg Subtype.val (g.apply_symm_apply xn).symm
        _ = lift g (g.symm xn).1 := (hlift g (g.symm xn)).symm
    rw [hinv]
    exact L.le_base (g.symm xn).2
  let factorNF (g : N.field ≃ₐ[ℚ] N.field) : NumberFieldInOmega :=
    { field := factorField g
      finite := hfactorFinite g }
  let factor (g : N.field ≃ₐ[ℚ] N.field) : NumberFieldExtension N :=
    { field := factorNF g
      le_base := hfactorLe g }
  let eQ (g : N.field ≃ₐ[ℚ] N.field) :
      L.field.field ≃ₐ[ℚ] (factor g).field.field := by
    change L.field.field ≃ₐ[ℚ] factorField g
    exact IntermediateField.equivMap L.field.field (lift g).toAlgHom
  have hcomp (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      (algebraMap N.field (factor g).field.field).comp g.toRingHom =
        (eQ g).toRingEquiv.toRingHom.comp
          (algebraMap N.field L.field.field) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    ext x
    exact (hlift g x).symm
  have hfactorGalois (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      IsGalois N.field (factor g).field.field := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    exact IsGalois.of_equiv_equiv (h := hLgal)
      (f := g.toRingEquiv) (g := (eQ g).toRingEquiv) (hcomp g)
  have hfactorDegree (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      Module.finrank N.field (factor g).field.field = (p : ℕ) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    calc
      Module.finrank N.field (factor g).field.field =
          Module.finrank N.field L.field.field :=
        (Algebra.finrank_eq_of_equiv_equiv g.toRingEquiv
          (eQ g).toRingEquiv (hcomp g)).symm
      _ = (p : ℕ) := hLdegree
  have hfactorCyclic (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      IsCyclic ((factor g).field.field ≃ₐ[N.field]
        (factor g).field.field) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    exact (regularKernelSemilinearAutCongr g.toRingEquiv
      (eQ g).toRingEquiv (hcomp g)).isCyclic.mp hLcyclic
  have hcompO (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      (algebraMap (𝓞 N.field) (𝓞 (factor g).field.field)).comp
          (NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv).toRingHom =
        (NumberField.RingOfIntegers.mapRingEquiv
          (eQ g).toRingEquiv).toRingHom.comp
            (algebraMap (𝓞 N.field) (𝓞 L.field.field)) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    ext x
    have hc := DFunLike.congr_fun (hcomp g) (x : N.field)
    exact congrArg Subtype.val hc
  have hmapV (g k : N.field ≃ₐ[ℚ] N.field) :
      regularKernelMapFinitePlace g.toRingEquiv (v k) = v (g * k) := by
    apply HeightOneSpectrum.ext
    dsimp [regularKernelMapFinitePlace]
    rw [congrArg HeightOneSpectrum.asIdeal (hvconj k),
      congrArg HeightOneSpectrum.asIdeal (hvconj (g * k)),
      NU.LocalTheory.conjugateFinitePlace_asIdeal,
      NU.LocalTheory.conjugateFinitePlace_asIdeal]
    change g • (k • (v 1).asIdeal) = (g * k) • (v 1).asIdeal
    exact (mul_smul g k (v 1).asIdeal).symm
  have hfactorRamified (g : N.field ≃ₐ[ℚ] N.field) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      IsRamifiedAt (factor g) (v g) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    letI : FiniteDimensional ℚ (factor g).field.field := hfactorFinite g
    letI : NumberField (factor g).field.field :=
      NumberField.of_module_finite ℚ (factor g).field.field
    obtain ⟨w, hw, he⟩ := hLramified
    have hover : w.asIdeal.LiesOver (v 1).asIdeal :=
      regularKernel_liesOver_of_restrict_eq w (v 1) hw
    letI : w.asIdeal.LiesOver (v 1).asIdeal := hover
    let w' := regularKernelMapFinitePlace (eQ g).toRingEquiv w
    refine ⟨w', ?_, ?_⟩
    · calc
        NU.LocalTheory.restrictFinitePlace N.field w' =
            regularKernelMapFinitePlace g.toRingEquiv
              (NU.LocalTheory.restrictFinitePlace N.field w) :=
          regularKernelMapFinitePlace_restrict g.toRingEquiv
            (eQ g).toRingEquiv (hcompO g) w
        _ = regularKernelMapFinitePlace g.toRingEquiv (v 1) :=
          congrArg (regularKernelMapFinitePlace g.toRingEquiv) hw
        _ = v (g * 1) := hmapV g 1
        _ = v g := by rw [mul_one]
    · have hidx := regularKernel_ramificationIdx_map_equiv
        (NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv)
        (NumberField.RingOfIntegers.mapRingEquiv (eQ g).toRingEquiv)
        (hcompO g) (v 1).asIdeal w.asIdeal (v 1).ne_bot
      have hidx' : relativeRamificationIndex (factor g)
          (regularKernelMapFinitePlace g.toRingEquiv (v 1)) w' =
          relativeRamificationIndex L (v 1) w := by
        dsimp [relativeRamificationIndex, w', regularKernelMapFinitePlace]
        exact hidx
      change 1 < relativeRamificationIndex (factor g) (v g) w'
      rw [← show regularKernelMapFinitePlace g.toRingEquiv (v 1) = v g by
        simpa using hmapV g 1, hidx']
      exact he
  have hfactorSplit (g h : N.field ≃ₐ[ℚ] N.field) (hneq : h ≠ g) :
      letI : Algebra N.field (factor g).field.field :=
        (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
      SplitsCompletelyAbove (factor g) (v h) := by
    letI : Algebra N.field (factor g).field.field :=
      (IntermediateField.inclusion (factor g).le_base).toRingHom.toAlgebra
    letI : FiniteDimensional ℚ (factor g).field.field := hfactorFinite g
    letI : NumberField (factor g).field.field :=
      NumberField.of_module_finite ℚ (factor g).field.field
    let k : N.field ≃ₐ[ℚ] N.field := g⁻¹ * h
    have hk : k ≠ 1 := by
      intro hkone
      have hgh : g = h := inv_mul_eq_one.mp hkone
      exact hneq hgh.symm
    have hseedSplit := hLsplit k hk
    have hlabel : g * k = h := by
      simp [k, mul_assoc]
    have hbase : regularKernelMapFinitePlace g.toRingEquiv (v k) = v h :=
      (hmapV g k).trans (congrArg v hlabel)
    constructor
    · obtain ⟨w, hw⟩ := hseedSplit.1
      let w' := regularKernelMapFinitePlace (eQ g).toRingEquiv w
      refine ⟨w', ?_⟩
      calc
        NU.LocalTheory.restrictFinitePlace N.field w' =
            regularKernelMapFinitePlace g.toRingEquiv
              (NU.LocalTheory.restrictFinitePlace N.field w) :=
          regularKernelMapFinitePlace_restrict g.toRingEquiv
            (eQ g).toRingEquiv (hcompO g) w
        _ = regularKernelMapFinitePlace g.toRingEquiv (v k) :=
          congrArg (regularKernelMapFinitePlace g.toRingEquiv) hw
        _ = v h := hbase
    · intro w' hw'
      let w := regularKernelMapFinitePlace (eQ g).symm.toRingEquiv w'
      have hforward :
          regularKernelMapFinitePlace (eQ g).toRingEquiv w = w' := by
        exact regularKernelMapFinitePlace_symm (eQ g).symm.toRingEquiv w'
      have hrestForward :
          NU.LocalTheory.restrictFinitePlace N.field w' =
            regularKernelMapFinitePlace g.toRingEquiv
              (NU.LocalTheory.restrictFinitePlace N.field w) := by
        rw [← hforward]
        exact regularKernelMapFinitePlace_restrict g.toRingEquiv
          (eQ g).toRingEquiv (hcompO g) w
      have hrest : NU.LocalTheory.restrictFinitePlace N.field w = v k := by
        have heq : regularKernelMapFinitePlace g.toRingEquiv
            (NU.LocalTheory.restrictFinitePlace N.field w) =
            regularKernelMapFinitePlace g.toRingEquiv (v k) := by
          calc
            _ = NU.LocalTheory.restrictFinitePlace N.field w' :=
              hrestForward.symm
            _ = v h := hw'
            _ = _ := hbase.symm
        exact regularKernelMapFinitePlace_injective g.toRingEquiv heq
      have hindices := hseedSplit.2 w hrest
      have hover : w.asIdeal.LiesOver (v k).asIdeal :=
        regularKernel_liesOver_of_restrict_eq w (v k) hrest
      letI : w.asIdeal.LiesOver (v k).asIdeal := hover
      have hram := regularKernel_ramificationIdx_map_equiv
        (NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv)
        (NumberField.RingOfIntegers.mapRingEquiv (eQ g).toRingEquiv)
        (hcompO g) (v k).asIdeal w.asIdeal (v k).ne_bot
      have hinertia := regularKernel_inertiaDeg_map_equiv
        (NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv)
        (NumberField.RingOfIntegers.mapRingEquiv (eQ g).toRingEquiv)
        (hcompO g) (v k).asIdeal w.asIdeal
      have hram' : relativeRamificationIndex (factor g)
          (regularKernelMapFinitePlace g.toRingEquiv (v k))
          (regularKernelMapFinitePlace (eQ g).toRingEquiv w) =
          relativeRamificationIndex L (v k) w := by
        dsimp [relativeRamificationIndex, regularKernelMapFinitePlace]
        exact hram
      have hinertia' : relativeResidueDegree (factor g)
          (regularKernelMapFinitePlace g.toRingEquiv (v k))
          (regularKernelMapFinitePlace (eQ g).toRingEquiv w) =
          relativeResidueDegree L (v k) w := by
        dsimp [relativeResidueDegree, regularKernelMapFinitePlace]
        exact hinertia
      constructor
      · rw [← hbase, ← hforward, hram']
        exact hindices.1
      · rw [← hbase, ← hforward, hinertia']
        exact hindices.2
  letI : IsScalarTower ℚ N.field Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : Algebra.IsAlgebraic N.field Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (A := Omega) N.field
  letI : Normal N.field Omega :=
    { isAlgebraic := fun x => Algebra.IsAlgebraic.isAlgebraic x
      splits' := fun _ => IsAlgClosed.splits _ }
  letI : IsGalois N.field L.field.field := hLgal
  let LN : IntermediateField N.field Omega :=
    IntermediateField.extendScalars L.le_base
  have hLNnormal : Normal N.field LN := by
    change Normal N.field L.field.field
    infer_instance
  have hLstable (tau : Omega →ₐ[N.field] Omega) :
      IntermediateField.map tau LN = LN :=
    (IntermediateField.normal_iff_forall_map_eq.mp hLNnormal) tau
  have hfactorMapLe (sigma : Omega ≃ₐ[ℚ] Omega)
      (k : N.field ≃ₐ[ℚ] N.field) :
      IntermediateField.map sigma.toAlgHom (factorField k) ≤
        factorField ((sigma.restrictNormal N.field) * k) := by
    let g : N.field ≃ₐ[ℚ] N.field := sigma.restrictNormal N.field
    let tauQ : Omega ≃ₐ[ℚ] Omega :=
      ((lift k).trans sigma).trans (lift (g * k)).symm
    let tauN : Omega ≃ₐ[N.field] Omega :=
      { tauQ.toRingEquiv with
        commutes' := by
          intro x
          change (lift (g * k)).symm (sigma (lift k x.1)) = x.1
          rw [hlift k x]
          have hsigma : sigma (k x).1 = (g (k x)).1 := by
            exact (AlgEquiv.restrictNormal_commutes sigma N.field (k x)).symm
          rw [hsigma]
          have hprod : (g (k x)).1 = lift (g * k) x.1 := by
            exact (hlift (g * k) x).symm
          rw [hprod, (lift (g * k)).symm_apply_apply] }
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change y ∈ conjugateField (lift k) L.field.field at hy
    rw [mem_conjugateField_iff] at hy
    change sigma y ∈ conjugateField (lift (g * k)) L.field.field
    rw [mem_conjugateField_iff]
    let z : Omega := (lift k).symm y
    have hzLN : z ∈ LN := hy
    have hzmap : tauN z ∈ IntermediateField.map tauN LN :=
      ⟨z, hzLN, rfl⟩
    rw [hLstable tauN] at hzmap
    change tauN z ∈ L.field.field at hzmap
    simpa [tauN, tauQ, z] using hzmap
  have hfactorMapEq (sigma : Omega ≃ₐ[ℚ] Omega)
      (k : N.field ≃ₐ[ℚ] N.field) :
      IntermediateField.map sigma.toAlgHom (factorField k) =
        factorField ((sigma.restrictNormal N.field) * k) := by
    apply le_antisymm (hfactorMapLe sigma k)
    let g : N.field ≃ₐ[ℚ] N.field := sigma.restrictNormal N.field
    have hinvLe := hfactorMapLe sigma.symm (g * k)
    have hginv : sigma.symm.restrictNormal N.field = g⁻¹ := by
      exact map_inv (AlgEquiv.restrictNormalHom N.field) sigma
    rw [hginv] at hinvLe
    have hinvLe' :
        IntermediateField.map sigma.symm.toAlgHom (factorField (g * k)) ≤
          factorField k := by
      simpa [mul_assoc] using hinvLe
    intro x hx
    rw [IntermediateField.mem_map]
    refine ⟨sigma.symm x, ?_, sigma.apply_symm_apply x⟩
    apply hinvLe'
    exact ⟨x, hx, rfl⟩
  let Mfield : IntermediateField ℚ Omega :=
    ⨆ g : N.field ≃ₐ[ℚ] N.field, factorField g
  letI (g : N.field ≃ₐ[ℚ] N.field) :
      FiniteDimensional ℚ (factorField g) := hfactorFinite g
  have hMfinite : FiniteDimensional ℚ Mfield := by
    dsimp [Mfield]
    infer_instance
  have hMstable (sigma : Omega ≃ₐ[ℚ] Omega) :
      IntermediateField.map sigma.toAlgHom Mfield = Mfield := by
    dsimp [Mfield]
    rw [IntermediateField.map_iSup]
    let g : N.field ≃ₐ[ℚ] N.field := sigma.restrictNormal N.field
    apply le_antisymm
    · apply iSup_le
      intro k
      rw [hfactorMapEq sigma k]
      exact le_iSup (fun j : N.field ≃ₐ[ℚ] N.field => factorField j)
        (g * k)
    · apply iSup_le
      intro k
      have hle := le_iSup
        (fun j : N.field ≃ₐ[ℚ] N.field =>
          IntermediateField.map sigma.toAlgHom (factorField j)) (g⁻¹ * k)
      rw [hfactorMapEq sigma (g⁻¹ * k)] at hle
      simpa [g, mul_assoc] using hle
  have hMnormal : Normal ℚ Mfield := by
    apply (IntermediateField.normal_iff_forall_map_eq
      (K := Mfield)).mpr
    intro sigmaHom
    let sigma : Omega ≃ₐ[ℚ] Omega :=
      AlgEquiv.ofBijective sigmaHom
        (AlgHom.normal_bijective ℚ Omega Omega sigmaHom)
    simpa [sigma] using hMstable sigma
  letI : FiniteDimensional ℚ Mfield := hMfinite
  letI : Normal ℚ Mfield := hMnormal
  have hMgalois : IsGalois ℚ Mfield :=
    { to_isSeparable := by infer_instance
      to_normal := hMnormal }
  have hMle : N.field ≤ Mfield := by
    exact (hfactorLe 1).trans
      (le_iSup (fun g : N.field ≃ₐ[ℚ] N.field => factorField g) 1)
  let MNF : NumberFieldInOmega :=
    { field := Mfield
      finite := hMfinite }
  let Mext : NumberFieldExtension N :=
    { field := MNF
      le_base := hMle }
  let Mover : GaloisOverfield N :=
    { toExtension := Mext
      isGaloisQ := by
        change IsGalois ℚ Mfield
        exact hMgalois }
  letI : Algebra N.field Mfield :=
    (IntermediateField.inclusion hMle).toAlgebra
  letI : IsScalarTower ℚ N.field Mfield :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let liftM (g : N.field ≃ₐ[ℚ] N.field) : Mfield ≃ₐ[ℚ] Mfield :=
    (IntermediateField.equivMap Mfield (lift g).toAlgHom).trans
      (IntermediateField.equivOfEq (hMstable (lift g)))
  have hliftMRestrict (g : N.field ≃ₐ[ℚ] N.field) :
      AlgEquiv.restrictNormalHom N.field (liftM g) = g := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc
      ((AlgEquiv.restrictNormalHom N.field (liftM g)) x).1 =
          (liftM g (algebraMap N.field Mfield x)).1 := by
        exact congrArg Subtype.val
          (AlgEquiv.restrictNormal_commutes (liftM g) N.field x)
      _ = lift g x.1 := rfl
      _ = (g x).1 := hlift g x
  have hliftMFactor (g k : N.field ≃ₐ[ℚ] N.field) (x : Mfield) :
      (liftM g x).1 ∈ factorField (g * k) ↔
        x.1 ∈ factorField k := by
    have hrestrict : (lift g).restrictNormal N.field = g := by
      apply AlgEquiv.ext
      intro y
      apply Subtype.ext
      calc
        ((lift g).restrictNormal N.field y).1 = lift g y.1 :=
          AlgEquiv.restrictNormal_commutes (lift g) N.field y
        _ = (g y).1 := hlift g y
    have hmap : IntermediateField.map (lift g).toAlgHom (factorField k) =
        factorField (g * k) := by
      simpa [hrestrict] using hfactorMapEq (lift g) k
    constructor
    · intro hx
      have hx' : lift g x.1 ∈ factorField (g * k) := hx
      rw [← hmap, IntermediateField.mem_map] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x.1 := (lift g).injective hyx
      rwa [← hyx']
    · intro hx
      have hxmap : lift g x.1 ∈
          IntermediateField.map (lift g).toAlgHom (factorField k) :=
        ⟨x.1, hx, rfl⟩
      rw [hmap] at hxmap
      exact hxmap
  have hliftOne : lift 1 = 1 := by simp [lift]
  have hfactorFieldOne : factorField 1 = L.field.field := by
    change conjugateField (lift 1) L.field.field = L.field.field
    apply IntermediateField.ext
    intro x
    rw [mem_conjugateField_iff, hliftOne]
    rfl
  have numberFieldInOmega_eq (A B : NumberFieldInOmega)
      (h : A.field = B.field) : A = B := by
    cases A with
    | mk Af Ah =>
      cases B with
      | mk Bf Bh =>
        dsimp at h
        subst Bf
        rfl
  have numberFieldExtension_eq (A B : NumberFieldExtension N)
      (h : A.field = B.field) : A = B := by
    cases A with
    | mk Af Ah =>
      cases B with
      | mk Bf Bh =>
        dsimp at h
        subst Bf
        rfl
  have hfactorNFOne : factorNF 1 = L.field :=
    numberFieldInOmega_eq _ _ hfactorFieldOne
  have hfactorOne : factor 1 = L :=
    numberFieldExtension_eq _ _ hfactorNFOne
  refine ⟨{
    seed := L
    q := q
    norm_ne := hnorm
    v := v
    v_over_q := hvq
    v_injective := hvinj
    v_conjugate := hvconj
    lift := lift
    lift_restrict := hlift
    factor := factor
    factor_one := hfactorOne
    factor_eq_conjugate := by intro g; rfl
    factor_isGalois := hfactorGalois
    factor_degree := hfactorDegree
    factor_cyclic := hfactorCyclic
    factor_ramified := hfactorRamified
    factor_split := hfactorSplit
    overfield := Mover
    overfield_lift := liftM
    overfield_lift_restrict := hliftMRestrict
    overfield_lift_factor := hliftMFactor
    field_eq_iSup := by rfl }⟩

/-- One `ZMod p` coordinate for each conjugate cyclic factor. -/
private structure RegularFactorCoordinateSystem
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) (M : GaloisOverfield N) where
  coordinate : (N.field ≃ₐ[ℚ] N.field) →
    Additive (RegularKernelGroup N M) →+ ZMod (p : ℕ)

/-- Every named factor lies in the chosen compositum. -/
private theorem regularConjugateFactor_le_overfield
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field) :
    (D.factor g).field.field ≤ D.overfield.toExtension.field.field := by
  have hFiSup : (D.factor g).field.field ≤
      ⨆ h, (D.factor h).field.field :=
    le_iSup (fun h => (D.factor h).field.field) g
  exact hFiSup.trans_eq D.field_eq_iSup.symm

/-- Restriction of a kernel automorphism to one normal conjugate factor. -/
private noncomputable def regularConjugateFactorRestriction
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field) :
    RegularKernelGroup N D.overfield →*
      ((D.factor g).field.field ≃ₐ[N.field] (D.factor g).field.field) := by
  let F := (D.factor g).field.field
  let M := D.overfield.toExtension.field.field
  letI : Algebra F M :=
    (IntermediateField.inclusion
      (regularConjugateFactor_le_overfield D g)).toAlgebra
  letI : IsScalarTower N.field F M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsGalois N.field F := D.factor_isGalois g
  exact AlgEquiv.restrictNormalHom F

/-- The chosen cyclic factor isomorphism with additive `ZMod p`. -/
private noncomputable def regularConjugateFactorZModEquiv
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field) :
    ((D.factor g).field.field ≃ₐ[N.field] (D.factor g).field.field) ≃*
      Multiplicative (ZMod (p : ℕ)) := by
  let F := (D.factor g).field.field
  letI : IsGalois N.field F := D.factor_isGalois g
  letI : IsCyclic (F ≃ₐ[N.field] F) := D.factor_cyclic g
  have hcard : Nat.card (F ≃ₐ[N.field] F) = (p : ℕ) := by
    calc
      Nat.card (F ≃ₐ[N.field] F) = Module.finrank N.field F :=
        IsGalois.card_aut_eq_finrank N.field F
      _ = (p : ℕ) := D.factor_degree g
  exact (zmodCyclicMulEquiv (D.factor_cyclic g)).symm.trans
    (ZMod.ringEquivCongr hcard).toAddEquiv.toMultiplicative

@[simp]
private theorem regularConjugateFactorRestriction_apply
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : RegularKernelGroup N D.overfield)
    (x : (D.factor g).field.field) :
    IntermediateField.inclusion
        (regularConjugateFactor_le_overfield D g)
      (regularConjugateFactorRestriction D g a x) =
        a (IntermediateField.inclusion
          (regularConjugateFactor_le_overfield D g) x) := by
  let F := (D.factor g).field.field
  let M := D.overfield.toExtension.field.field
  letI : Algebra F M :=
    (IntermediateField.inclusion
      (regularConjugateFactor_le_overfield D g)).toAlgebra
  letI : IsScalarTower N.field F M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsGalois N.field F := D.factor_isGalois g
  exact AlgEquiv.restrictNormal_commutes a F x

/-- Undoing `Multiplicative` and then `Additive` leaves the original
additive group, with an explicit equivalence to avoid instance ambiguity. -/
private def additiveMultiplicativeZModAddEquiv (n : ℕ) :
    Additive (Multiplicative (ZMod n)) ≃+ ZMod n :=
  AddEquiv.refl _

/-- Raw factor coordinates obtained from arbitrary cyclic generators. -/
private noncomputable def regularConjugateRawFactorCoordinates
    (_hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    RegularFactorCoordinateSystem N p D.overfield :=
  ⟨fun g => (additiveMultiplicativeZModAddEquiv (p : ℕ)).toAddMonoidHom.comp
    (MonoidHom.toAdditive
      ((regularConjugateFactorZModEquiv D g).toMonoidHom.comp
        (regularConjugateFactorRestriction D g)))⟩

@[simp]
private theorem regularConjugateRawFactorCoordinates_apply
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : Additive (RegularKernelGroup N D.overfield)) :
    (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g a =
      additiveMultiplicativeZModAddEquiv (p : ℕ)
        (Additive.ofMul (regularConjugateFactorZModEquiv D g
          (regularConjugateFactorRestriction D g (Additive.toMul a)))) := by
  rfl

/-- Evaluation in all explicitly typed per-conjugate coordinates. -/
private noncomputable def regularFactorEvaluation
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {M : GaloisOverfield N}
    (C : RegularFactorCoordinateSystem N p M) :
    Additive (RegularKernelGroup N M) →+
      ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ)) where
  toFun a := Finsupp.equivFunOnFinite.symm
    (fun g => C.coordinate g a)
  map_zero' := by
    apply Finsupp.equivFunOnFinite.injective
    funext g
    simp
  map_add' a b := by
    apply Finsupp.equivFunOnFinite.injective
    funext g
    simp

@[simp]
private theorem regularFactorEvaluation_apply
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime} {M : GaloisOverfield N}
    (C : RegularFactorCoordinateSystem N p M)
    (a : Additive (RegularKernelGroup N M))
    (g : N.field ≃ₐ[ℚ] N.field) :
    regularFactorEvaluation C a g = C.coordinate g a := by
  rfl

/-- The compositum is generated by its factors, so factor evaluation is
injective. -/
private theorem regularRawFactorEvaluation_injective
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    Function.Injective (regularFactorEvaluation
      (regularConjugateRawFactorCoordinates hAsymmetric D)) := by
  classical
  intro a b hab
  let aM : RegularKernelGroup N D.overfield := Additive.toMul a
  let bM : RegularKernelGroup N D.overfield := Additive.toMul b
  have hres (g : N.field ≃ₐ[ℚ] N.field) :
      regularConjugateFactorRestriction D g aM =
        regularConjugateFactorRestriction D g bM := by
    apply (regularConjugateFactorZModEquiv D g).injective
    have hcoord := congrArg (fun z => z g) hab
    have hcoord' :
        (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g a =
          (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g b := by
      exact hcoord
    rw [regularConjugateRawFactorCoordinates_apply,
      regularConjugateRawFactorCoordinates_apply] at hcoord'
    have hadd := (additiveMultiplicativeZModAddEquiv (p : ℕ)).injective hcoord'
    have hmul := Additive.ofMul.injective hadd
    simpa only [aM, bM] using hmul
  let cK : RegularKernelGroup N D.overfield := aM⁻¹ * bM
  letI : Algebra ℚ D.overfield.toExtension.field.field :=
    D.overfield.toExtension.field.field.algebra'
  let c : D.overfield.toExtension.field.field ≃ₐ[ℚ]
      D.overfield.toExtension.field.field := cK.restrictScalars ℚ
  let S : IntermediateField ℚ D.overfield.toExtension.field.field :=
    IntermediateField.fixedField (Subgroup.zpowers c)
  let T : IntermediateField ℚ D.overfield.toExtension.field.field :=
    ⨆ g, IntermediateField.restrict
      (regularConjugateFactor_le_overfield D g)
  have hfactorS (g : N.field ≃ₐ[ℚ] N.field) :
      IntermediateField.restrict
          (regularConjugateFactor_le_overfield D g) ≤ S := by
    intro x hx
    let F := (D.factor g).field.field
    let y : F := ⟨x.1,
      (IntermediateField.mem_restrict
        (regularConjugateFactor_le_overfield D g) x).mp hx⟩
    have hresC : regularConjugateFactorRestriction D g cK = 1 := by
      dsimp [cK]
      rw [map_mul, map_inv, hres g, inv_mul_cancel]
    have hresCy : regularConjugateFactorRestriction D g cK y = y := by
      have hy := DFunLike.congr_fun hresC y
      exact hy.trans rfl
    have hcomm := regularConjugateFactorRestriction_apply D g cK y
    rw [hresCy] at hcomm
    have hyx : IntermediateField.inclusion
        (regularConjugateFactor_le_overfield D g) y = x := by
      apply Subtype.ext
      rfl
    have hcKx : cK x = x := by
      rw [← hyx]
      exact hcomm.symm
    have hcx : c x = x := hcKx
    rw [IntermediateField.mem_fixedField_iff]
    intro tau htau
    have hz : Subgroup.zpowers c ≤
        MulAction.stabilizer
          (D.overfield.toExtension.field.field ≃ₐ[ℚ]
            D.overfield.toExtension.field.field) x :=
      Subgroup.zpowers_le.mpr hcx
    exact hz htau
  have hiSupLeLift : (⨆ g, (D.factor g).field.field) ≤
      IntermediateField.lift T := by
    apply iSup_le
    intro g x hx
    let xM : D.overfield.toExtension.field.field :=
      ⟨x, (regularConjugateFactor_le_overfield D g) hx⟩
    have hxRestr : xM ∈ IntermediateField.restrict
        (regularConjugateFactor_le_overfield D g) :=
      (IntermediateField.mem_restrict
        (regularConjugateFactor_le_overfield D g) xM).mpr hx
    have hxT : xM ∈ T :=
      (le_iSup (fun h => IntermediateField.restrict
        (regularConjugateFactor_le_overfield D h)) g) hxRestr
    exact (IntermediateField.mem_lift xM).mpr hxT
  have hMleLift : D.overfield.toExtension.field.field ≤
      IntermediateField.lift T := by
    calc
      D.overfield.toExtension.field.field =
          ⨆ g, (D.factor g).field.field := D.field_eq_iSup
      _ ≤ IntermediateField.lift T := hiSupLeLift
  have hLiftT : IntermediateField.lift T =
      D.overfield.toExtension.field.field :=
    le_antisymm (IntermediateField.lift_le T) hMleLift
  have hTtop : T = ⊤ := by
    apply (IntermediateField.lift_injective
      D.overfield.toExtension.field.field)
    calc
      IntermediateField.lift T =
          D.overfield.toExtension.field.field := hLiftT
      _ = IntermediateField.lift
          (⊤ : IntermediateField ℚ
            D.overfield.toExtension.field.field) :=
        (IntermediateField.lift_top ℚ
          D.overfield.toExtension.field.field).symm
  have hTS : T ≤ S := by
    apply iSup_le
    exact hfactorS
  have hStop : S = ⊤ := by
    apply top_unique
    rw [← hTtop]
    exact hTS
  apply Additive.toMul.injective
  apply AlgEquiv.ext
  intro x
  have hxS : x ∈ S := by
    rw [hStop]
    trivial
  have hcx := (IntermediateField.mem_fixedField_iff
    (H := Subgroup.zpowers c) x).mp hxS c (Subgroup.mem_zpowers c)
  have happly := congrArg aM hcx
  simpa [c, cK, aM, bM] using happly.symm

/-- Inertia at the prime labelled by `g` restricts trivially to every
other conjugate factor, which splits completely there. -/
private theorem regularConjugateFactorRestriction_eq_one_of_mem_inertia
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    {g k : N.field ≃ₐ[ℚ] N.field} (hgk : g ≠ k)
    (W : NU.LocalTheory.FinitePlace
      D.overfield.toExtension.field.field)
    (hWg : NU.LocalTheory.restrictFinitePlace N.field W = D.v g)
    (sigma : W.asIdeal.inertia
      (RegularKernelGroup N D.overfield)) :
    regularConjugateFactorRestriction D k sigma.1 = 1 := by
  let F := (D.factor k).field.field
  let M := D.overfield.toExtension.field.field
  letI : Algebra F M :=
    (IntermediateField.inclusion
      (regularConjugateFactor_le_overfield D k)).toAlgebra
  letI : IsScalarTower N.field F M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsGalois N.field F := D.factor_isGalois k
  letI : Finite (F ≃ₐ[N.field] F) :=
    Finite.of_injective (AlgEquiv.restrictScalarsHom ℚ)
      (AlgEquiv.restrictScalarsHom_injective ℚ)
  let w : NU.LocalTheory.FinitePlace F :=
    NU.LocalTheory.restrictFinitePlace F W
  have hwg : NU.LocalTheory.restrictFinitePlace N.field w = D.v g := by
    exact (regularKernel_restrictFinitePlace_tower W).trans hWg
  have hsplit := (D.factor_split k g hgk).2 w hwg
  have hwOver : w.asIdeal.LiesOver (D.v g).asIdeal :=
    regularKernel_liesOver_of_restrict_eq w (D.v g) hwg
  letI : w.asIdeal.LiesOver (D.v g).asIdeal := hwOver
  have hcard : Nat.card
      (w.asIdeal.inertia (F ≃ₐ[N.field] F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (D.v g).asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx
        (D.v g).asIdeal w.asIdeal (F ≃ₐ[N.field] F)]
    exact hsplit.1
  have hresInertia : regularConjugateFactorRestriction D k sigma.1 ∈
      w.asIdeal.inertia (F ≃ₐ[N.field] F) := by
    rw [AddSubgroup.mem_inertia]
    intro x
    change (regularConjugateFactorRestriction D k sigma.1) • x - x ∈
      w.asIdeal
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal, Ideal.mem_comap]
    have hsigma := (AddSubgroup.mem_inertia.mp sigma.2)
      (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers M) x)
    have heq : algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers M)
          ((regularConjugateFactorRestriction D k sigma.1) • x) =
        sigma.1 • algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers M) x := by
      apply Subtype.ext
      exact regularConjugateFactorRestriction_apply D k sigma.1 (x : F)
    rw [map_sub, heq]
    exact hsigma
  have hbot : w.asIdeal.inertia (F ≃ₐ[N.field] F) = ⊥ :=
    Subgroup.card_eq_one.mp hcard
  rw [hbot] at hresInertia
  exact hresInertia

/-- Injecting the kernel into additive `ZMod p` coordinates formally makes
it abelian of exponent `p`. -/
private theorem regularConjugateCompositum_kernelElementaryAbelian
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    ∃ hcomm : ∀ a b : RegularKernelGroup N D.overfield, a * b = b * a,
      letI : CommGroup (RegularKernelGroup N D.overfield) :=
        regularKernelCommGroup N D.overfield hcomm
      ∀ a : RegularKernelGroup N D.overfield, a ^ (p : ℕ) = 1 := by
  let C := regularConjugateRawFactorCoordinates hAsymmetric D
  let evaluation := regularFactorEvaluation C
  have hinjective : Function.Injective evaluation :=
    regularRawFactorEvaluation_injective hAsymmetric D
  have hcomm (a b : RegularKernelGroup N D.overfield) : a * b = b * a := by
    apply Additive.ofMul.injective
    apply hinjective
    calc
      evaluation (Additive.ofMul (a * b)) =
          evaluation (Additive.ofMul a) + evaluation (Additive.ofMul b) :=
        map_add evaluation (Additive.ofMul a) (Additive.ofMul b)
      _ = evaluation (Additive.ofMul b) + evaluation (Additive.ofMul a) :=
        add_comm _ _
      _ = evaluation (Additive.ofMul (b * a)) :=
        (map_add evaluation (Additive.ofMul b) (Additive.ofMul a)).symm
  refine ⟨hcomm, ?_⟩
  letI : CommGroup (RegularKernelGroup N D.overfield) :=
    regularKernelCommGroup N D.overfield hcomm
  intro a
  apply Additive.ofMul.injective
  apply hinjective
  change evaluation ((p : ℕ) • Additive.ofMul a) = evaluation 0
  rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul
    (R := ZMod (p : ℕ)), ZMod.natCast_self, zero_smul]

/-- Asymmetric ramification makes the conjugate factors independent, so the
evaluation map is surjective. -/
private theorem regularRawFactorEvaluation_surjective
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    Function.Surjective (regularFactorEvaluation
      (regularConjugateRawFactorCoordinates hAsymmetric D)) := by
  classical
  obtain ⟨hcomm, _⟩ :=
    regularConjugateCompositum_kernelElementaryAbelian hAsymmetric D
  letI : CommGroup (RegularKernelGroup N D.overfield) :=
    regularKernelCommGroup N D.overfield hcomm
  let evaluation := regularFactorEvaluation
    (regularConjugateRawFactorCoordinates hAsymmetric D)
  have hinjective : Function.Injective evaluation :=
    regularRawFactorEvaluation_injective hAsymmetric D
  have hbasis (g : N.field ≃ₐ[ℚ] N.field) :
      ∃ a, evaluation a = Finsupp.single g 1 := by
    obtain ⟨w, hwg, hwram⟩ := D.factor_ramified g
    let FM : NumberFieldExtension (D.factor g).field :=
      { field := D.overfield.toExtension.field
        le_base := regularConjugateFactor_le_overfield D g }
    obtain ⟨W, hWw⟩ := finitePlaceAbove_numberFieldExtension FM w
    let F := (D.factor g).field.field
    let M := D.overfield.toExtension.field.field
    letI : Algebra F M :=
      (IntermediateField.inclusion
        (regularConjugateFactor_le_overfield D g)).toAlgebra
    letI : IsScalarTower N.field F M :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ℚ N.field M :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsGalois N.field M :=
      IsGalois.tower_top_of_isGalois ℚ N.field M
    have hWg : NU.LocalTheory.restrictFinitePlace N.field W = D.v g := by
      calc
        NU.LocalTheory.restrictFinitePlace N.field W =
            NU.LocalTheory.restrictFinitePlace N.field
              (NU.LocalTheory.restrictFinitePlace F W) :=
          (regularKernel_restrictFinitePlace_tower W).symm
        _ = NU.LocalTheory.restrictFinitePlace N.field w :=
          congrArg (NU.LocalTheory.restrictFinitePlace N.field) hWw
        _ = D.v g := hwg
    have hwOver : w.asIdeal.LiesOver (D.v g).asIdeal :=
      regularKernel_liesOver_of_restrict_eq w (D.v g) hwg
    have hWOverw : W.asIdeal.LiesOver w.asIdeal :=
      regularKernel_liesOver_of_restrict_eq W w hWw
    letI : w.asIdeal.LiesOver (D.v g).asIdeal := hwOver
    letI : W.asIdeal.LiesOver w.asIdeal := hWOverw
    letI := Localization.AtPrime.algebraOfLiesOver w.asIdeal W.asIdeal
    have heTower := Ideal.ramificationIdx'_tower'
      (R := 𝓞 N.field) w.asIdeal W.asIdeal
    have hrelativePos : 0 < W.asIdeal.ramificationIdx' (𝓞 F) :=
      Ideal.ramificationIdx'_pos W.asIdeal (𝓞 F)
    have hWram : 1 < W.asIdeal.ramificationIdx' (𝓞 N.field) := by
      rw [heTower]
      exact Nat.lt_of_lt_of_le hwram
        (Nat.le_mul_of_pos_right _ hrelativePos)
    have hWOver : W.asIdeal.LiesOver (D.v g).asIdeal :=
      regularKernel_liesOver_of_restrict_eq W (D.v g) hWg
    letI : W.asIdeal.LiesOver (D.v g).asIdeal := hWOver
    letI : Finite (RegularKernelGroup N D.overfield) :=
      Finite.of_injective (AlgEquiv.restrictScalarsHom ℚ)
        (AlgEquiv.restrictScalarsHom_injective ℚ)
    have hcard : Nat.card (W.asIdeal.inertia
        (RegularKernelGroup N D.overfield)) =
        W.asIdeal.ramificationIdx' (𝓞 N.field) := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn
          (D.v g).asIdeal W.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx
          (D.v g).asIdeal W.asIdeal
          (RegularKernelGroup N D.overfield)]
    letI := Fintype.ofFinite (W.asIdeal.inertia
      (RegularKernelGroup N D.overfield))
    have hcard' : 1 < Fintype.card (W.asIdeal.inertia
        (RegularKernelGroup N D.overfield)) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact hWram
    letI : Nontrivial (W.asIdeal.inertia
        (RegularKernelGroup N D.overfield)) :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard'
    obtain ⟨sigma, hsigma⟩ := exists_ne
      (1 : W.asIdeal.inertia (RegularKernelGroup N D.overfield))
    have hsigmaVal : sigma.1 ≠ 1 := by
      intro hsigmaVal
      apply hsigma
      exact Subtype.ext hsigmaVal
    let a : Additive (RegularKernelGroup N D.overfield) :=
      Additive.ofMul sigma.1
    have haNonzero : evaluation a ≠ 0 := by
      intro haZero
      have ha : a = 0 := by
        apply hinjective
        exact haZero.trans (map_zero evaluation).symm
      apply hsigmaVal
      have ha' := congrArg Additive.toMul ha
      simpa [a] using ha'
    have haway (k : N.field ≃ₐ[ℚ] N.field) (hkg : k ≠ g) :
        evaluation a k = 0 := by
      rw [regularFactorEvaluation_apply,
        regularConjugateRawFactorCoordinates_apply]
      have hres :=
        regularConjugateFactorRestriction_eq_one_of_mem_inertia
          D hkg.symm W hWg sigma
      have haeq : Additive.toMul a = sigma.1 := rfl
      rw [haeq, hres]
      have hz : regularConjugateFactorZModEquiv D k 1 = 1 :=
        map_one (regularConjugateFactorZModEquiv D k)
      rw [hz]
      rfl
    have hgNonzero : evaluation a g ≠ 0 := by
      intro hgZero
      apply haNonzero
      apply Finsupp.ext
      intro k
      by_cases hkg : k = g
      · subst k
        simpa using hgZero
      · simpa using haway k hkg
    let b : Additive (RegularKernelGroup N D.overfield) :=
      (evaluation a g)⁻¹.val • a
    refine ⟨b, ?_⟩
    apply Finsupp.ext
    intro k
    rw [show evaluation b =
        (evaluation a g)⁻¹.val • evaluation a by
      dsimp only [b]
      exact map_nsmul evaluation _ _]
    by_cases hkg : k = g
    · subst k
      rw [Finsupp.single_eq_same]
      simp only [Finsupp.smul_apply]
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod (p : ℕ)),
        ZMod.natCast_zmod_val, smul_eq_mul,
        inv_mul_cancel₀ hgNonzero]
    · rw [Finsupp.single_eq_of_ne hkg]
      simp only [Finsupp.smul_apply]
      rw [haway k hkg, smul_zero]
  intro y
  choose b hb using hbasis
  refine ⟨∑ g, (y g).val • b g, ?_⟩
  calc
    evaluation (∑ g, (y g).val • b g) =
        ∑ g, (y g).val • evaluation (b g) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro g _
      exact map_nsmul evaluation (y g).val (b g)
    _ = ∑ g, (y g).val • Finsupp.single g 1 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hb g]
    _ = ∑ g, Finsupp.single g (y g) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finsupp.smul_single]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod (p : ℕ)),
        ZMod.natCast_zmod_val, smul_eq_mul, mul_one]
    _ = y := Finsupp.univ_sum_single y

/-- The canonical commutativity witness supplied by raw factor evaluation. -/
private theorem regularConjugateCompositum_comm
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    ∀ a b : RegularKernelGroup N D.overfield, a * b = b * a :=
  Classical.choose
    (regularConjugateCompositum_kernelElementaryAbelian hAsymmetric D)

/-- Equivariant coordinates are the translates of the identity-factor
coordinate under the canonical conjugation action. -/
private noncomputable def regularConjugateFactorCoordinates
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    RegularFactorCoordinateSystem N p D.overfield := by
  let C₀ := regularConjugateRawFactorCoordinates hAsymmetric D
  let hcomm := regularConjugateCompositum_comm hAsymmetric D
  let action := regularKernelConjugation N D.overfield hcomm
  exact ⟨fun g => (C₀.coordinate 1).comp
    (MonoidHom.toAdditive (action g⁻¹).toMonoidHom)⟩

@[simp]
private theorem regularConjugateFactorCoordinates_apply
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : RegularKernelGroup N D.overfield) :
    (regularConjugateFactorCoordinates hAsymmetric D).coordinate g
        (Additive.ofMul a) =
      (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate 1
        (Additive.ofMul
          (regularKernelConjugation N D.overfield
            (regularConjugateCompositum_comm hAsymmetric D) g⁻¹ a)) := by
  rfl

private theorem regularConjugateRawFactorCoordinate_eq_zero_iff
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : RegularKernelGroup N D.overfield) :
    (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g
        (Additive.ofMul a) = 0 ↔
      regularConjugateFactorRestriction D g a = 1 := by
  rw [regularConjugateRawFactorCoordinates_apply]
  constructor
  · intro hzero
    have hadd := (additiveMultiplicativeZModAddEquiv (p : ℕ)).injective
      (hzero.trans
        (map_zero (additiveMultiplicativeZModAddEquiv (p : ℕ))).symm)
    have hmul : regularConjugateFactorZModEquiv D g
        (regularConjugateFactorRestriction D g a) = 1 := by
      apply Additive.ofMul.injective
      exact hadd
    apply (regularConjugateFactorZModEquiv D g).injective
    rw [map_one]
    exact hmul
  · intro hres
    have haeq : Additive.toMul (Additive.ofMul a) = a := rfl
    rw [haeq, hres]
    have hone : regularConjugateFactorZModEquiv D g 1 = 1 :=
      map_one (regularConjugateFactorZModEquiv D g)
    rw [hone]
    rfl

private theorem regularConjugateFactorRestriction_conjugation_eq_one_iff
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : RegularKernelGroup N D.overfield) :
    regularConjugateFactorRestriction D 1
        (regularKernelConjugation N D.overfield
          (regularConjugateCompositum_comm hAsymmetric D) g⁻¹ a) = 1 ↔
      regularConjugateFactorRestriction D g a = 1 := by
  let M := D.overfield.toExtension.field.field
  let F₁ := (D.factor 1).field.field
  let Fg := (D.factor g).field.field
  let le₁ := regularConjugateFactor_le_overfield D 1
  let leg := regularConjugateFactor_le_overfield D g
  let hcomm := regularConjugateCompositum_comm hAsymmetric D
  let action := regularKernelConjugation N D.overfield hcomm
  let lift := D.overfield_lift g⁻¹
  have hlift : AlgEquiv.restrictNormalHom N.field lift = g⁻¹ :=
    D.overfield_lift_restrict g⁻¹
  constructor
  · intro hone
    apply AlgEquiv.ext
    intro y
    apply (IntermediateField.inclusion leg).injective
    let yM : M := IntermediateField.inclusion leg y
    have hly : (lift yM).1 ∈ F₁ := by
      have hmem := (D.overfield_lift_factor g⁻¹ g yM).mpr y.2
      simpa [F₁] using hmem
    let x : F₁ := ⟨(lift yM).1, hly⟩
    have hfixRestriction :
        regularConjugateFactorRestriction D 1 (action g⁻¹ a) x = x := by
      have hx := DFunLike.congr_fun hone x
      exact hx.trans rfl
    have hrestriction :=
      regularConjugateFactorRestriction_apply D 1 (action g⁻¹ a) x
    rw [hfixRestriction] at hrestriction
    have hxM : IntermediateField.inclusion le₁ x = lift yM := by
      apply Subtype.ext
      rfl
    have hfixConjugate : action g⁻¹ a (lift yM) = lift yM := by
      rw [← hxM]
      exact hrestriction.symm
    have hformula := regularKernelConjugation_lift N D.overfield hcomm
      g⁻¹ lift hlift a (lift yM)
    rw [lift.symm_apply_apply] at hformula
    have hay : a yM = yM := by
      apply lift.injective
      calc
        lift (a yM) = action g⁻¹ a (lift yM) := hformula.symm
        _ = lift yM := hfixConjugate
    calc
      IntermediateField.inclusion leg
          (regularConjugateFactorRestriction D g a y) = a yM :=
        regularConjugateFactorRestriction_apply D g a y
      _ = yM := hay
      _ = IntermediateField.inclusion leg y := rfl
  · intro hone
    apply AlgEquiv.ext
    intro x
    apply (IntermediateField.inclusion le₁).injective
    let xM : M := IntermediateField.inclusion le₁ x
    have hlx : (lift (lift.symm xM)).1 ∈ (D.factor (g⁻¹ * g)).field.field := by
      have hindex : g⁻¹ * g = 1 := inv_mul_cancel g
      rw [hindex]
      have hliftInv : lift (lift.symm xM) = xM :=
        lift.apply_symm_apply xM
      rw [hliftInv]
      exact x.2
    have hyMem : (lift.symm xM).1 ∈ Fg :=
      (D.overfield_lift_factor g⁻¹ g (lift.symm xM)).mp hlx
    let y : Fg := ⟨(lift.symm xM).1, hyMem⟩
    have hfixRestriction : regularConjugateFactorRestriction D g a y = y := by
      have hy := DFunLike.congr_fun hone y
      exact hy.trans rfl
    have hrestriction := regularConjugateFactorRestriction_apply D g a y
    rw [hfixRestriction] at hrestriction
    have hyM : IntermediateField.inclusion leg y = lift.symm xM := by
      apply Subtype.ext
      rfl
    have hfixA : a (lift.symm xM) = lift.symm xM := by
      rw [← hyM]
      exact hrestriction.symm
    have hformula := regularKernelConjugation_lift N D.overfield hcomm
      g⁻¹ lift hlift a xM
    have hfixConjugate : action g⁻¹ a xM = xM := by
      calc
        action g⁻¹ a xM = lift (a (lift.symm xM)) := hformula
        _ = lift (lift.symm xM) := congrArg lift hfixA
        _ = xM := lift.apply_symm_apply xM
    calc
      IntermediateField.inclusion le₁
          (regularConjugateFactorRestriction D 1 (action g⁻¹ a) x) =
          action g⁻¹ a xM :=
        regularConjugateFactorRestriction_apply D 1 (action g⁻¹ a) x
      _ = xM := hfixConjugate
      _ = IntermediateField.inclusion le₁ x := rfl

private theorem regularConjugateFactorCoordinate_eq_zero_iff_raw
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : Additive (RegularKernelGroup N D.overfield)) :
    (regularConjugateFactorCoordinates hAsymmetric D).coordinate g a = 0 ↔
      (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g a = 0 := by
  let aM : RegularKernelGroup N D.overfield := Additive.toMul a
  have ha : Additive.ofMul aM = a := rfl
  calc
    (regularConjugateFactorCoordinates hAsymmetric D).coordinate g a = 0 ↔
        (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate 1
          (Additive.ofMul
            (regularKernelConjugation N D.overfield
              (regularConjugateCompositum_comm hAsymmetric D) g⁻¹ aM)) = 0 := by
      rw [← ha, regularConjugateFactorCoordinates_apply]
    _ ↔ regularConjugateFactorRestriction D 1
          (regularKernelConjugation N D.overfield
            (regularConjugateCompositum_comm hAsymmetric D) g⁻¹ aM) = 1 :=
      regularConjugateRawFactorCoordinate_eq_zero_iff
        hAsymmetric D 1 _
    _ ↔ regularConjugateFactorRestriction D g aM = 1 :=
      regularConjugateFactorRestriction_conjugation_eq_one_iff
        hAsymmetric D g aM
    _ ↔ (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g
          (Additive.ofMul aM) = 0 :=
      (regularConjugateRawFactorCoordinate_eq_zero_iff
        hAsymmetric D g aM).symm
    _ ↔ (regularConjugateRawFactorCoordinates hAsymmetric D).coordinate g
          a = 0 := by rw [ha]

/-- Orbit coordinates have the same joint kernel as the raw factor
coordinates. -/
private theorem regularFactorEvaluation_injective
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    Function.Injective (regularFactorEvaluation
      (regularConjugateFactorCoordinates hAsymmetric D)) := by
  classical
  let C := regularConjugateFactorCoordinates hAsymmetric D
  let C₀ := regularConjugateRawFactorCoordinates hAsymmetric D
  let evaluation := regularFactorEvaluation C
  let evaluation₀ := regularFactorEvaluation C₀
  intro a b hab
  let d := -a + b
  have hdEvaluation : evaluation d = 0 := by
    dsimp only [d]
    calc
      evaluation (-a + b) = -evaluation a + evaluation b := by
        rw [map_add, map_neg]
      _ = 0 := by rw [hab, neg_add_cancel]
  have hdRaw : evaluation₀ d = 0 := by
    apply Finsupp.ext
    intro g
    have hdg := congrArg (fun z => z g) hdEvaluation
    have hdg' : C.coordinate g d = 0 := by
      exact hdg
    exact (regularConjugateFactorCoordinate_eq_zero_iff_raw
      hAsymmetric D g d).mp hdg'
  have hd : d = 0 := by
    apply regularRawFactorEvaluation_injective hAsymmetric D
    exact hdRaw.trans (map_zero evaluation₀).symm
  apply neg_add_eq_zero.mp
  exact hd

/-- The raw and orbit evaluations have equal finite cardinalities, so
injectivity of the orbit evaluation gives surjectivity. -/
private theorem regularFactorEvaluation_surjective
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    Function.Surjective (regularFactorEvaluation
      (regularConjugateFactorCoordinates hAsymmetric D)) := by
  classical
  letI := Fintype.ofFinite (N.field ≃ₐ[ℚ] N.field)
  letI : Finite ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ)) := by
    infer_instance
  let evaluation := regularFactorEvaluation
    (regularConjugateFactorCoordinates hAsymmetric D)
  let evaluation₀ := regularFactorEvaluation
    (regularConjugateRawFactorCoordinates hAsymmetric D)
  have hcard : Nat.card (Additive (RegularKernelGroup N D.overfield)) =
      Nat.card ((N.field ≃ₐ[ℚ] N.field) →₀ ZMod (p : ℕ)) :=
    Nat.card_eq_of_bijective evaluation₀
      ⟨regularRawFactorEvaluation_injective hAsymmetric D,
        regularRawFactorEvaluation_surjective hAsymmetric D⟩
  exact ((Nat.bijective_iff_injective_and_card evaluation).mpr
    ⟨regularFactorEvaluation_injective hAsymmetric D, hcard⟩).2

/-- Conjugation permutes the factor coordinates by left translation. -/
private theorem regularFactorCoordinates_conjugation
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (hcomm : ∀ a b : RegularKernelGroup N D.overfield, a * b = b * a) :
    let C := regularConjugateFactorCoordinates hAsymmetric D
    ∀ (h g : N.field ≃ₐ[ℚ] N.field)
        (a : RegularKernelGroup N D.overfield),
      C.coordinate g (Additive.ofMul
        (regularKernelConjugation N D.overfield hcomm h a)) =
      C.coordinate (h⁻¹ * g) (Additive.ofMul a) := by
  dsimp only
  intro h g a
  rw [regularConjugateFactorCoordinates_apply,
    regularConjugateFactorCoordinates_apply]
  let hcomm₀ := regularConjugateCompositum_comm hAsymmetric D
  have hproof : hcomm = hcomm₀ := Subsingleton.elim _ _
  rw [hproof]
  let action := regularKernelConjugation N D.overfield hcomm₀
  have hmul : action g⁻¹ (action h a) = action (g⁻¹ * h) a := by
    have happly := DFunLike.congr_fun (map_mul action g⁻¹ h) a
    exact happly.symm
  rw [hmul, mul_inv_rev, inv_inv]

/-- An explicit additive bridge from finitely supported coordinates to the
same coordinates viewed as a monoid algebra. -/
private def finsuppMonoidAlgebraAddEquiv
    (R G : Type*) [Semiring R] :
    (G →₀ R) ≃+ MonoidAlgebra R G where
  toEquiv := MonoidAlgebra.coeffEquiv.symm
  map_add' := by
    intro x y
    rfl

@[simp]
private theorem finsuppMonoidAlgebraAddEquiv_coeff
    (R G : Type*) [Semiring R] (x : G →₀ R) (g : G) :
    (finsuppMonoidAlgebraAddEquiv R G x).coeff g = x g := by
  rfl

/-- Build the additive regular representation from bijective factor
evaluation, without asking elaboration to identify products of raw monoid
algebras. -/
private noncomputable def regularFactorAddEquiv
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p) :
    Additive (RegularKernelGroup N D.overfield) ≃+
      MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field) := by
  let C := regularConjugateFactorCoordinates hAsymmetric D
  let evaluation := regularFactorEvaluation C
  let coordinateEquiv := AddEquiv.ofBijective evaluation
    ⟨regularFactorEvaluation_injective hAsymmetric D,
      regularFactorEvaluation_surjective hAsymmetric D⟩
  exact coordinateEquiv.trans
    (finsuppMonoidAlgebraAddEquiv (ZMod (p : ℕ))
      (N.field ≃ₐ[ℚ] N.field))

/-- Coefficients of the additive equivalence are the individual factor
coordinates. -/
private theorem regularFactorAddEquiv_coeff
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (a : Additive (RegularKernelGroup N D.overfield))
    (g : N.field ≃ₐ[ℚ] N.field) :
    (regularFactorAddEquiv hAsymmetric D a).coeff g =
      (regularConjugateFactorCoordinates hAsymmetric D).coordinate g a := by
  simp only [regularFactorAddEquiv, AddEquiv.trans_apply,
    AddEquiv.ofBijective_apply, finsuppMonoidAlgebraAddEquiv_coeff,
    regularFactorEvaluation_apply]

/-- The Finsupp coefficient calculation turns coordinate permutation into
literal multiplication by `single h 1`. -/
private theorem regularFactorAddEquiv_conjugation
    (hAsymmetric : AsymmetricCyclicConstruction)
    {N : NumberFieldInOmega} [IsGalois ℚ N.field]
    {p : NU.LocalTheory.OddPrime}
    (D : RegularConjugateCompositumData N p)
    (hcomm : ∀ a b : RegularKernelGroup N D.overfield, a * b = b * a)
    (g : N.field ≃ₐ[ℚ] N.field)
    (a : RegularKernelGroup N D.overfield) :
    regularFactorAddEquiv hAsymmetric D
        (Additive.ofMul
          (regularKernelConjugation N D.overfield hcomm g a)) =
      regularLeftTranslate p g
        (regularFactorAddEquiv hAsymmetric D (Additive.ofMul a)) := by
  apply MonoidAlgebra.coeffEquiv.injective
  apply Finsupp.ext
  intro k
  calc
    (regularFactorAddEquiv hAsymmetric D
        (Additive.ofMul
          (regularKernelConjugation N D.overfield hcomm g a))).coeff k =
        (regularConjugateFactorCoordinates hAsymmetric D).coordinate k
          (Additive.ofMul
            (regularKernelConjugation N D.overfield hcomm g a)) :=
      regularFactorAddEquiv_coeff hAsymmetric D _ k
    _ = (regularConjugateFactorCoordinates hAsymmetric D).coordinate
          (g⁻¹ * k) (Additive.ofMul a) :=
      regularFactorCoordinates_conjugation hAsymmetric D hcomm g k a
    _ = (regularFactorAddEquiv hAsymmetric D
          (Additive.ofMul a)).coeff (g⁻¹ * k) :=
      (regularFactorAddEquiv_coeff
        hAsymmetric D (Additive.ofMul a) (g⁻¹ * k)).symm
    _ = (regularLeftTranslate p g
          (regularFactorAddEquiv hAsymmetric D
            (Additive.ofMul a))).coeff k := by
      rw [regularLeftTranslate]
      have hm : (MonoidAlgebra.single g 1 *
          regularFactorAddEquiv hAsymmetric D (Additive.ofMul a)).coeff k =
          (regularFactorAddEquiv hAsymmetric D (Additive.ofMul a)).coeff
            (g⁻¹ * k) := by
        simpa only [MonoidAlgebra.coeff, one_mul] using
          (MonoidAlgebra.single_mul_apply
            (regularFactorAddEquiv hAsymmetric D (Additive.ofMul a))
            (1 : ZMod (p : ℕ)) g k)
      exact hm.symm

/-- Assembly of the compositum ladder into the exact additive seam. -/
private theorem regularKernelAdditiveConstruction :
    RegularKernelAdditiveConstruction := by
  intro N _ p
  obtain ⟨D⟩ := regularConjugateCompositumData_exists
    asymmetricCyclicConstruction N p
  obtain ⟨hcomm, _hpow⟩ :=
    regularConjugateCompositum_kernelElementaryAbelian
      asymmetricCyclicConstruction D
  letI : CommGroup (RegularKernelGroup N D.overfield) :=
    regularKernelCommGroup N D.overfield hcomm
  refine ⟨D.overfield, hcomm,
    regularFactorAddEquiv asymmetricCyclicConstruction D, ?_⟩
  intro g a
  exact regularFactorAddEquiv_conjugation
    asymmetricCyclicConstruction D hcomm g a

/-- Explicit witness record for the three arithmetic layers left after the
proved projector and conjugation infrastructure.  Keeping the fields separate
makes the fallback ledger identify cyclotomic descent, asymmetric weak
approximation, and the conjugate-compositum realization independently. -/
private structure RegularKernelDeepWitness : Prop where
  kummerDescent : KummerDescentConstruction
  asymmetricCyclic : AsymmetricCyclicConstruction
  regularKernel : RegularKernelConstruction

/-- Single fallback seam for the arithmetic witness record.  No algebraic
assembly is hidden here: each unresolved construction is a separate field of
`RegularKernelDeepWitness`. -/
private theorem regularKernelDeepWitness : RegularKernelDeepWitness := by
  have h : RegularKernelArithmeticResidual :=
    ⟨kummerDescentConstruction, asymmetricCyclicConstruction,
      regularKernelAdditiveConstruction⟩
  exact ⟨h.1, h.2.1, regularKernelConstruction_of_additive h.2.2⟩

/-- Assembly of the explicitly separated deep arithmetic witnesses. -/
private theorem regularKernelDeepConstruction :
    KummerDescentConstruction ∧
      AsymmetricCyclicConstruction ∧ RegularKernelConstruction := by
  exact ⟨regularKernelDeepWitness.kummerDescent,
    regularKernelDeepWitness.asymmetricCyclic,
    regularKernelDeepWitness.regularKernel⟩

/-- Blueprint Lemma `lem:kummer-descent`: a nonzero cyclotomic-eigenclass
descends `E(sqrt[p]{a})/E` to a cyclic degree-`p` extension of `N`.
The character equation is multiplicative notation for
`delta(c) = chi(delta)c`. -/
theorem kummer_cyclotomicEigenspace_descent
    (N : NumberFieldInOmega) (p : NU.LocalTheory.OddPrime)
    (c : KummerClass (cyclotomicCompositum N p) (p : ℕ))
    (hc : c ≠ 1)
    (heigen : ∀ delta : CyclotomicDelta N p,
      kummerAction N p delta c =
        c ^ ((cyclotomicCharacter N p delta : ZMod (p : ℕ)).val))
    (a : (cyclotomicCompositum N p).fieldˣ)
    (ha : QuotientGroup.mk a = c) :
    ∃ L : NumberFieldExtension N,
      IsGalois N.field L.field.field ∧
      Module.finrank N.field L.field.field = (p : ℕ) ∧
      IsCyclic (L.field.field ≃ₐ[N.field] L.field.field) ∧
      (cyclotomicCompositum N p).field ⊔ L.field.field =
        radicalExtension (cyclotomicCompositum N p) p a := by
  exact regularKernelDeepConstruction.1 N p c hc heigen a ha

/-- Blueprint Lemma `lem:asymmetric-cyclic`: one cyclic degree-`p`
extension, ramified at the identity-labelled prime and completely split at
all its other Galois conjugates.  The labeling is explicitly a simply
transitive `Gal(N/ℚ)`-orbit.

The witnesses `b` and `a` expose the construction omitted by the earlier
skeleton: `[a] = e_chi[b]` is nontrivial, and the descended extension becomes
the radical extension defined by `a` after adjoining `mu_p`. -/
theorem exists_asymmetricCyclicExtension
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    ∃ q : NU.Chebotarev.PrimeIdeal ℚ,
      NU.Chebotarev.PrimeIdeal.norm q ≠ (p : ℕ) ∧
      SplitsCompletelyAt N q ∧
      ∃ v : (N.field ≃ₐ[ℚ] N.field) →
          NU.LocalTheory.FinitePlace N.field,
        (∀ g, rationalPrime N (v g) = q) ∧
        Function.Injective v ∧
        (∀ w, rationalPrime N w = q → ∃ g, v g = w) ∧
        (∀ g, v g = NU.LocalTheory.conjugateFinitePlace ℚ g (v 1)) ∧
        ∃ b a : (cyclotomicCompositum N p).fieldˣ,
          QuotientGroup.mk a =
              projectedKummerClass N p (QuotientGroup.mk b) ∧
          projectedKummerClass N p (QuotientGroup.mk b) ≠ 1 ∧
          ∃ L : NumberFieldExtension N,
            IsGalois N.field L.field.field ∧
            Module.finrank N.field L.field.field = (p : ℕ) ∧
            IsCyclic (L.field.field ≃ₐ[N.field] L.field.field) ∧
            IsRamifiedAt L (v 1) ∧
            (∀ g ≠ 1, SplitsCompletelyAbove L (v g)) ∧
            (cyclotomicCompositum N p).field ⊔ L.field.field =
              radicalExtension (cyclotomicCompositum N p) p a := by
  exact regularKernelDeepConstruction.2.1 N p

/-- Blueprint Proposition `prop:regular-kernel`: above every finite Galois
`N/ℚ` and odd `p` there is a finite Galois `M/ℚ` whose kernel is the regular
`F_p[Gal(N/ℚ)]`-module.

The scalar equation pins the returned `ZMod p`-module structure to group
powers, the returned equivalence is literally linear, and the next equation
identifies conjugation with left translation.  Thus neither the scalar
structure nor the `G`-action can be replaced by a trivial model. -/
theorem exists_regularKernelExtension
    (N : NumberFieldInOmega) [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime) :
    ∃ M : GaloisOverfield N,
      ∃ hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a,
      letI : CommGroup (RegularKernelGroup N M) :=
        regularKernelCommGroup N M hcomm
      (∀ a : RegularKernelGroup N M, a ^ (p : ℕ) = 1) ∧
      ∃ moduleA : Module (ZMod (p : ℕ))
          (Additive (RegularKernelGroup N M)),
        letI : Module (ZMod (p : ℕ))
            (Additive (RegularKernelGroup N M)) := moduleA
        (∀ (a : RegularKernelGroup N M) (r : ZMod (p : ℕ)),
          Additive.toMul (r • Additive.ofMul a) = a ^ r.val) ∧
        ∃ e : Additive (RegularKernelGroup N M) ≃ₗ[ZMod (p : ℕ)]
            MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field),
          (∀ (g : N.field ≃ₐ[ℚ] N.field)
              (a : RegularKernelGroup N M),
            e (Additive.ofMul
                (regularKernelConjugation N M hcomm g a)) =
              regularLeftTranslate p g (e (Additive.ofMul a))) ∧
          Fintype.card (RegularKernelGroup N M) =
            (p : ℕ) ^ Fintype.card (N.field ≃ₐ[ℚ] N.field) := by
  exact regularKernelDeepConstruction.2.2 N p

end

end NU.NeukirchUchida
