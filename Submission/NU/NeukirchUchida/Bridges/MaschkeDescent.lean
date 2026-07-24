import Submission.NU.NeukirchUchida.Bridges.DeepUnitModule
import Submission.NU.LCFT.Basic.CompletionData
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Maschke descent after adjoining roots of unity

This standalone bridge exposes the inflation--restriction/Maschke input used
by local character-rank recovery.  It can be proved without editing
`NU.NeukirchUchida.LocalInvariants`.
-/

open scoped NumberField

namespace NU.NeukirchUchida.Bridges

noncomputable section

/-- The root-of-unity correction in the local Kummer rank formula. -/
noncomputable def primitiveRootCorrection
    (F : Type*) [Field F] (p : Nat.Primes) : ℕ := by
  classical
  exact if ∃ z : F, IsPrimitiveRoot z (p : ℕ) then 1 else 0

/-- The guarded cyclotomic averaging idempotent
`|Δ|⁻¹ ∑ δ, χ(δ)⁻¹[δ]`.  The nonvanishing hypothesis is the
prime-to-`p` Maschke input. -/
private noncomputable def maschkeCyclotomicProjector
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

@[simp] private theorem maschkeCyclotomicProjector_coeff
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) (delta : Delta) :
    (maschkeCyclotomicProjector p hcard chi).coeff delta =
      (Nat.card Delta : ZMod (p : ℕ))⁻¹ *
        ((chi delta)⁻¹ : ZMod (p : ℕ)) := by
  classical
  letI := Fintype.ofFinite Delta
  unfold maschkeCyclotomicProjector
  rw [MonoidAlgebra.coeff_sum]
  change Finsupp.applyAddHom delta (∑ d : Delta,
    (MonoidAlgebra.single d
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi d)⁻¹ : ZMod (p : ℕ)))).coeff) = _
  rw [map_sum]
  rw [Finset.sum_eq_single delta]
  · change (MonoidAlgebra.single delta
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi delta)⁻¹ : ZMod (p : ℕ)))).coeff delta = _
    rw [MonoidAlgebra.coeff_single_apply, if_pos rfl]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  · intro d hd hne
    change (MonoidAlgebra.single d
      ((↑((Units.mk0 (Nat.card Delta : ZMod (p : ℕ)) hcard)⁻¹) :
        ZMod (p : ℕ)) * ((chi d)⁻¹ : ZMod (p : ℕ)))).coeff delta = 0
    rw [MonoidAlgebra.coeff_single_apply, if_neg hne]
  · intro h
    exact (h (Finset.mem_univ delta)).elim

private theorem maschkeCyclotomicProjector_translate
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) (gamma : Delta) :
    MonoidAlgebra.single gamma 1 * maschkeCyclotomicProjector p hcard chi =
      (chi gamma : ZMod (p : ℕ)) • maschkeCyclotomicProjector p hcard chi := by
  classical
  letI := Fintype.ofFinite Delta
  ext delta
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul,
    maschkeCyclotomicProjector_coeff, MonoidAlgebra.coeff_smul_apply,
    maschkeCyclotomicProjector_coeff]
  change (Nat.card Delta : ZMod (p : ℕ))⁻¹ *
      (↑(chi (gamma⁻¹ * delta)) : ZMod (p : ℕ))⁻¹ =
    (chi gamma : ZMod (p : ℕ)) *
      ((Nat.card Delta : ZMod (p : ℕ))⁻¹ *
        (↑(chi delta) : ZMod (p : ℕ))⁻¹)
  rw [map_mul, map_inv]
  push_cast
  field_simp

private theorem maschkeCyclotomicProjector_idempotent
    (p : NU.LocalTheory.OddPrime) {Delta : Type*}
    [Finite Delta] [Group Delta]
    (hcard : (Nat.card Delta : ZMod (p : ℕ)) ≠ 0)
    (chi : Delta →* (ZMod (p : ℕ))ˣ) :
    IsIdempotentElem (maschkeCyclotomicProjector p hcard chi) := by
  classical
  letI := Fintype.ofFinite Delta
  let R := ZMod (p : ℕ)
  let P := maschkeCyclotomicProjector p hcard chi
  let a : Delta → R := fun d =>
    (Nat.card Delta : R)⁻¹ * ((chi d)⁻¹ : R)
  have hP : P = ∑ d : Delta, MonoidAlgebra.single d (a d) := rfl
  have hsingle (d : Delta) :
      MonoidAlgebra.single d (a d) =
        a d • MonoidAlgebra.single d (1 : R) := by
    ext x
    rw [MonoidAlgebra.coeff_smul_apply]
    by_cases h : d = x
    · subst x
      rw [MonoidAlgebra.coeff_single_apply, if_pos rfl,
        MonoidAlgebra.coeff_single_apply, if_pos rfl, smul_eq_mul, mul_one]
    · rw [MonoidAlgebra.coeff_single_apply, if_neg h,
        MonoidAlgebra.coeff_single_apply, if_neg h, smul_zero]
  change P * P = P
  rw [hP, Finset.sum_mul]
  calc
    (∑ d : Delta, MonoidAlgebra.single d (a d) * P) =
        ∑ d : Delta, a d •
          (MonoidAlgebra.single d (1 : R) * P) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hsingle, smul_mul_assoc]
    _ = ∑ d : Delta, a d • ((chi d : R) • P) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [maschkeCyclotomicProjector_translate]
    _ = (∑ d : Delta, a d * (chi d : R)) • P := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro d _
      rw [smul_smul]
    _ = P := by
      have hterm (d : Delta) : a d * (chi d : R) =
          (Nat.card Delta : R)⁻¹ := by
        dsimp [a, R]
        field_simp
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_univ,
        Fintype.card_eq_nat_card, nsmul_eq_mul,
        mul_inv_cancel₀ hcard, one_smul]

/-- A chosen primitive `p`-th root in an algebraic closure. -/
noncomputable def localCyclotomicRoot
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    AlgebraicClosure F :=
  Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure F) (p : ℕ))

/-- The extension obtained by adjoining the chosen primitive `p`-th root. -/
noncomputable def localCyclotomicExtension
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F {localCyclotomicRoot F p}

instance localCyclotomicExtension_finite
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    FiniteDimensional F (localCyclotomicExtension F p) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact Algebra.IsIntegral.isIntegral x

/-- The chosen primitive root, regarded as an element of the cyclotomic
extension. -/
def localCyclotomicRootInExtension
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    localCyclotomicExtension F p :=
  ⟨localCyclotomicRoot F p,
    IntermediateField.subset_adjoin F {localCyclotomicRoot F p}
      (Set.mem_singleton _)⟩

/-- The root adjoined to `localCyclotomicExtension` is primitive. -/
theorem localCyclotomicRootInExtension_spec
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    IsPrimitiveRoot (localCyclotomicRootInExtension F p) (p : ℕ) := by
  apply IsPrimitiveRoot.of_map_of_injective
    (f := (localCyclotomicExtension F p).val)
  · exact Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure F) (p : ℕ))
  · exact (localCyclotomicExtension F p).val.injective

/-- The mod-`p` cyclotomic character of the finite Galois group of
`F(μ_p)/F`. -/
private noncomputable def localCyclotomicCharacter
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    (localCyclotomicExtension F p ≃ₐ[F] localCyclotomicExtension F p) →*
      (ZMod (p : ℕ))ˣ :=
  (localCyclotomicRootInExtension_spec F p).autToPow F

@[simp] private theorem localCyclotomicCharacter_spec
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes)
    (sigma : localCyclotomicExtension F p ≃ₐ[F]
      localCyclotomicExtension F p) :
    (localCyclotomicRootInExtension F p) ^
        (localCyclotomicCharacter F p sigma : ZMod (p : ℕ)).val =
      sigma (localCyclotomicRootInExtension F p) := by
  exact (localCyclotomicRootInExtension_spec F p).autToPow_spec F sigma

private instance localCyclotomicExtension_isCyclotomic
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    IsCyclotomicExtension {(p : ℕ)} F
      (localCyclotomicExtension F p) := by
  exact (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure F) (p : ℕ)))
    |>.intermediateField_adjoin_isCyclotomicExtension F

private instance localCyclotomicExtension_isGalois
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    IsGalois F (localCyclotomicExtension F p) :=
  IsCyclotomicExtension.isGalois {(p : ℕ)} F _

/-- Adjoining `μ_p` has degree strictly below `p`. -/
private theorem localCyclotomicExtension_finrank_lt
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    Module.finrank F (localCyclotomicExtension F p) < (p : ℕ) := by
  rw [show localCyclotomicExtension F p =
      IntermediateField.adjoin F {localCyclotomicRoot F p} from rfl,
    IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral (localCyclotomicRoot F p))]
  have hdvd : minpoly F (localCyclotomicRoot F p) ∣
      Polynomial.cyclotomic (p : ℕ) F := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      Polynomial.map_cyclotomic]
    exact (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure F) (p : ℕ))).isRoot_cyclotomic p.2.pos
  calc
    (minpoly F (localCyclotomicRoot F p)).natDegree ≤
        (Polynomial.cyclotomic (p : ℕ) F).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd
        (Polynomial.cyclotomic_ne_zero (p : ℕ) F)
    _ = (p : ℕ).totient := Polynomial.natDegree_cyclotomic _ _
    _ = (p : ℕ) - 1 := Nat.totient_prime p.2
    _ < (p : ℕ) := Nat.sub_one_lt p.2.ne_zero

/-- The cyclotomic Galois-group order is a unit modulo `p`; this is
the numerical Maschke hypothesis. -/
private theorem localCyclotomic_card_ne_zero
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    (Nat.card (localCyclotomicExtension F p ≃ₐ[F]
      localCyclotomicExtension F p) : ZMod (p : ℕ)) ≠ 0 := by
  rw [IsGalois.card_aut_eq_finrank]
  intro hzero
  have hdvd : (p : ℕ) ∣
      Module.finrank F (localCyclotomicExtension F p) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hpos : 0 < Module.finrank F (localCyclotomicExtension F p) :=
    Module.finrank_pos
  exact (Nat.not_dvd_of_pos_of_lt hpos
    (localCyclotomicExtension_finrank_lt F p)) hdvd

private noncomputable def intermediateFieldClosureEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    AlgebraicClosure E ≃ₐ[E] AlgebraicClosure F := by
  letI : IsAlgClosure E (AlgebraicClosure F) :=
    ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equiv E (AlgebraicClosure E) (AlgebraicClosure F)

private noncomputable def intermediateFieldGaloisMulEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E ≃* E.fixingSubgroup := by
  let e := intermediateFieldClosureEquiv F E
  let toFun : Field.absoluteGaloisGroup E → E.fixingSubgroup := fun sigma =>
    let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
    ⟨((e.symm.trans sigma').trans e).restrictScalars F, by
      apply (IntermediateField.mem_fixingSubgroup_iff E _).2
      intro x hx
      change e (sigma' (e.symm x)) = x
      have hxe : e.symm x =
          algebraMap E (AlgebraicClosure E) ⟨x, hx⟩ := by
        apply e.injective
        simp
      rw [hxe, sigma'.commutes]
      simp⟩
  let invFun : E.fixingSubgroup → Field.absoluteGaloisGroup E := fun tau =>
    let tauE : AlgebraicClosure F ≃ₐ[E] AlgebraicClosure F :=
      { tau.1 with
        commutes' := fun x => by
          exact (IntermediateField.mem_fixingSubgroup_iff E tau.1).1
            tau.2 x x.2 }
    (e.trans tauE).trans e.symm
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro sigma
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      right_inv := by
        intro tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      map_mul' := by
        intro sigma tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, e]
        rfl }

private noncomputable def intermediateFieldRestrictionHom
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E →* Field.absoluteGaloisGroup F :=
  E.fixingSubgroup.subtype.comp
    (intermediateFieldGaloisMulEquiv F E).toMonoidHom

private theorem intermediateFieldRestrictionHom_apply
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F))
    (sigma : Field.absoluteGaloisGroup E) (x : AlgebraicClosure F) :
    (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
      intermediateFieldRestrictionHom F E sigma) x =
      intermediateFieldClosureEquiv F E
        ((show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma)
          ((intermediateFieldClosureEquiv F E).symm x)) := by
  rfl

private theorem intermediateFieldRestrictionHom_continuous
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Continuous (intermediateFieldRestrictionHom F E) := by
  let r : (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →*
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
    intermediateFieldRestrictionHom F E
  change @Continuous
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (krullTopology E (AlgebraicClosure E))
    (krullTopology F (AlgebraicClosure F)) r
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [r.map_one] at hN
  have hN' : N ∈ nhds
      (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := hN
  rw [krullTopology_mem_nhds_one_iff] at hN'
  obtain ⟨L, hLfin, hLN⟩ := hN'
  letI : FiniteDimensional F L := hLfin
  let e := intermediateFieldClosureEquiv F E
  let b := Module.Free.chooseBasis F L
  letI : Fintype (Module.Free.ChooseBasisIndex F L) := Fintype.ofFinite _
  let S : Set (AlgebraicClosure E) := Set.range
    (fun i : Module.Free.ChooseBasisIndex F L =>
      e.symm (((b i : L) : AlgebraicClosure F)))
  letI : Fintype S := (Set.finite_range _).fintype
  let L' : IntermediateField E (AlgebraicClosure E) :=
    IntermediateField.adjoin E S
  haveI : FiniteDimensional E L' := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x _
    exact Algebra.IsIntegral.isIntegral x
  apply mem_nhds_iff.mpr
  refine ⟨L'.fixingSubgroup, ?_,
    ⟨IntermediateField.fixingSubgroup_isOpen L',
      L'.fixingSubgroup.one_mem⟩⟩
  intro sigma hsigma
  apply hLN
  apply (IntermediateField.mem_fixingSubgroup_iff L _).2
  intro x hx
  have hsigma' :=
    (IntermediateField.mem_fixingSubgroup_iff L' sigma).1 hsigma
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
    intermediateFieldRestrictionHom F E sigma) x = x
  rw [intermediateFieldRestrictionHom_apply]
  let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
  let incl : L →ₐ[F] AlgebraicClosure F := L.val
  let pull : AlgebraicClosure F →ₐ[F] AlgebraicClosure E :=
    e.symm.restrictScalars F
  let f : L →ₗ[F] AlgebraicClosure E :=
    pull.toLinearMap.comp incl.toLinearMap
  let sigmaF : AlgebraicClosure E →ₐ[F] AlgebraicClosure E :=
    sigma'.restrictScalars F
  have heq : sigmaF.toLinearMap.comp f = f := by
    apply b.ext
    intro i
    change sigma' (e.symm (((b i : L) : AlgebraicClosure F))) =
      e.symm (((b i : L) : AlgebraicClosure F))
    apply hsigma'
    apply IntermediateField.subset_adjoin
    exact ⟨i, rfl⟩
  have hxfix := DFunLike.congr_fun heq (⟨x, hx⟩ : L)
  change sigma' (e.symm x) = e.symm x at hxfix
  rw [hxfix]
  exact e.apply_symm_apply x

private noncomputable def localCyclotomicClosureEquiv
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    AlgebraicClosure (localCyclotomicExtension F p) ≃ₐ[
      localCyclotomicExtension F p] AlgebraicClosure F :=
  intermediateFieldClosureEquiv F (localCyclotomicExtension F p)

private noncomputable def localCyclotomicGaloisMulEquiv
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F p) ≃*
      (localCyclotomicExtension F p).fixingSubgroup :=
  intermediateFieldGaloisMulEquiv F (localCyclotomicExtension F p)

private noncomputable def localCyclotomicRestrictionHom
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F p) →*
      Field.absoluteGaloisGroup F :=
  intermediateFieldRestrictionHom F (localCyclotomicExtension F p)

private theorem localCyclotomicRestrictionHom_continuous
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    Continuous (localCyclotomicRestrictionHom F p) :=
  intermediateFieldRestrictionHom_continuous F
    (localCyclotomicExtension F p)

private noncomputable def localCyclotomicRestrictionContinuousHom
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F p) →ₜ*
      Field.absoluteGaloisGroup F :=
  ContinuousMonoidHom.mk (localCyclotomicRestrictionHom F p)
    (localCyclotomicRestrictionHom_continuous F p)

/-- Pullback of continuous characters as a linear map. -/
private def continuousCharacterPullLinearMap
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (f : G →ₜ* H) :
    NU.LocalTheory.ContinuousCharacter H n →ₗ[ZMod n]
      NU.LocalTheory.ContinuousCharacter G n where
  toFun := NU.LocalTheory.restrictCharacter n f
  map_add' a b := by
    ext g
    rfl
  map_smul' c a := by
    ext g
    simp only [RingHom.id_apply]
    let evH : NU.LocalTheory.ContinuousCharacter H n →+ ZMod n :=
      { toFun := fun chi => chi (Additive.ofMul (f (Additive.toMul g)))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let evG : NU.LocalTheory.ContinuousCharacter G n →+ ZMod n :=
      { toFun := fun chi => chi g
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hH : (c • a) (Additive.ofMul (f (Additive.toMul g))) =
        c * a (Additive.ofMul (f (Additive.toMul g))) := by
      simpa [evH] using ZMod.map_smul evH c a
    have hG : (c • NU.LocalTheory.restrictCharacter n f a) g =
        c * NU.LocalTheory.restrictCharacter n f a g := by
      simpa [evG] using ZMod.map_smul evG c
        (NU.LocalTheory.restrictCharacter n f a)
    change (c • a) (Additive.ofMul (f (Additive.toMul g))) =
      (c • NU.LocalTheory.restrictCharacter n f a) g
    rw [hH, hG]
    rfl

/-- Restriction to the cyclotomic fixing subgroup is injective in
characteristic `p`, since its index is smaller than `p`. -/
private theorem localCyclotomic_characterPull_injective
    (F : Type*) [Field F] [CharZero F] (p : Nat.Primes)
    (hindex : (localCyclotomicExtension F p).fixingSubgroup.index <
      (p : ℕ)) :
    Function.Injective (continuousCharacterPullLinearMap (p : ℕ)
      (localCyclotomicRestrictionContinuousHom F p)) := by
  let E := localCyclotomicExtension F p
  let H := E.fixingSubgroup
  letI : H.Normal :=
    (InfiniteGalois.normal_iff_isGalois E).2 inferInstance
  intro a b hab
  let c : NU.LocalTheory.ContinuousCharacter
      (Field.absoluteGaloisGroup F) (p : ℕ) := a - b
  have hpull : continuousCharacterPullLinearMap (p : ℕ)
      (localCyclotomicRestrictionContinuousHom F p) c = 0 := by
    rw [show c = a - b from rfl, map_sub, hab, sub_self]
  have hfix (tau : E.fixingSubgroup) :
      c (Additive.ofMul
        (show Field.absoluteGaloisGroup F from tau.1)) = 0 := by
    let sigma : Field.absoluteGaloisGroup E :=
      (localCyclotomicGaloisMulEquiv F p).symm tau
    have hz := DFunLike.congr_fun hpull (Additive.ofMul sigma)
    change c (Additive.ofMul
      (localCyclotomicRestrictionContinuousHom F p sigma)) = 0 at hz
    have hsigma : localCyclotomicRestrictionContinuousHom F p sigma =
        (show Field.absoluteGaloisGroup F from tau.1) := by
      change localCyclotomicRestrictionHom F p sigma = tau.1
      change ((localCyclotomicGaloisMulEquiv F p) sigma).1 = tau.1
      rw [(localCyclotomicGaloisMulEquiv F p).apply_symm_apply]
    rwa [hsigma] at hz
  have hc : c = 0 := by
    ext g
    cases g with
    | ofMul g =>
      have hgpow : g ^ H.index ∈ H := H.pow_index_mem g
      have hzpow := hfix (⟨g ^ H.index, hgpow⟩ : H)
      change c (H.index • Additive.ofMul g) = 0 at hzpow
      rw [map_nsmul, nsmul_eq_mul] at hzpow
      have hindexpos : 0 < H.index := by
        rw [← IntermediateField.finrank_eq_fixingSubgroup_index E]
        exact Module.finrank_pos
      have hcast : ((H.index : ℕ) : ZMod (p : ℕ)) ≠ 0 := by
        intro hz
        exact (Nat.not_dvd_of_pos_of_lt hindexpos hindex)
          ((ZMod.natCast_eq_zero_iff H.index (p : ℕ)).mp hz)
      exact (mul_eq_zero.mp hzpow).resolve_left hcast
  exact sub_eq_zero.mp hc

/-! ## Linear algebra for the local multiplicative quotient -/

/-- `Additive` commutes with a fourfold product. -/
private def additiveProdFourAddEquiv
    {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D] :
    Additive (A × B × C × D) ≃+
      Additive A × Additive B × Additive C × Additive D :=
  AddEquiv.refl _

/-- An additive homomorphism induces a linear map after quotienting by `n`. -/
private noncomputable def modNLinearMapOfAddHom
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (f : G →+ H) :
    ModN G n →ₗ[ZMod n] ModN H n :=
  ModN.liftEquiv'.symm
    ⟨(ModN.mkQ n).comp f, fun g => by
      change n • ModN.mkQ n (f g) = 0
      change ModN.mkQ n (n • f g) = 0
      change Submodule.Quotient.mk (n • f g) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨f g, by simp⟩⟩

/-- Additively equivalent groups have linearly equivalent quotients modulo
`n`. -/
private noncomputable def modNLinearEquivOfAddEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (e : G ≃+ H) :
    ModN G n ≃ₗ[ZMod n] ModN H n :=
  let f := modNLinearMapOfAddHom n e.toAddMonoidHom
  let g := modNLinearMapOfAddHom n e.symm.toAddMonoidHom
  LinearEquiv.ofBijective f
    ⟨(show Function.LeftInverse g f by
        intro x
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range
            (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective x
        change ModN.mkQ n (e.symm (e x)) = ModN.mkQ n x
        rw [e.symm_apply_apply]).injective,
      (show Function.RightInverse g f by
        intro x
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range
            (LinearMap.lsmul ℤ H (n : ℤ))).mkQ_surjective x
        change ModN.mkQ n (e (e.symm x)) = ModN.mkQ n x
        rw [e.apply_symm_apply]).surjective⟩

/-- The natural Galois action on a Kummer quotient. -/
private noncomputable def kummerQuotientGaloisAction
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (σ : E ≃ₐ[F] E) :
    NU.LocalTheory.KummerQuotient E p →ₗ[ZMod p]
      NU.LocalTheory.KummerQuotient E p :=
  modNLinearMapOfAddHom p
    (Units.mapEquiv σ.toRingEquiv.toMulEquiv).toAdditive.toAddMonoidHom

@[simp] private theorem kummerQuotientGaloisAction_class
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (σ : E ≃ₐ[F] E) (a : Eˣ) :
    kummerQuotientGaloisAction p σ
        (NU.LocalTheory.kummerQuotientClass p a) =
      NU.LocalTheory.kummerQuotientClass p
        (Units.map σ.toRingEquiv.toRingHom a) := by
  rfl

/-- The field-automorphism action on Kummer classes, bundled as a linear
representation. -/
private noncomputable def kummerQuotientGaloisRep
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) : Representation (ZMod p) (E ≃ₐ[F] E)
      (NU.LocalTheory.KummerQuotient E p) where
  toFun := kummerQuotientGaloisAction p
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (Additive Eˣ) (p : ℤ))).mkQ_surjective x
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (Additive Eˣ) (p : ℤ))).mkQ_surjective x
    rfl

/-- The Maschke projector acting on the natural Kummer representation. -/
private noncomputable def maschkeKummerProjectorMap
    (p : NU.LocalTheory.OddPrime)
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite (E ≃ₐ[F] E)]
    (hcard : (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ)) ≠ 0)
    (chi : (E ≃ₐ[F] E) →* (ZMod (p : ℕ))ˣ) :
    NU.LocalTheory.KummerQuotient E (p : ℕ) →ₗ[ZMod (p : ℕ)]
      NU.LocalTheory.KummerQuotient E (p : ℕ) :=
  (kummerQuotientGaloisRep (F := F) (E := E) (p : ℕ)).asAlgebraHom
    (maschkeCyclotomicProjector p hcard chi)

/-- Left translation turns the cyclotomic projector into the corresponding
character scalar. -/
private theorem kummerGaloisAction_comp_maschkeKummerProjectorMap
    (p : NU.LocalTheory.OddPrime)
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite (E ≃ₐ[F] E)]
    (hcard : (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ)) ≠ 0)
    (chi : (E ≃ₐ[F] E) →* (ZMod (p : ℕ))ˣ)
    (gamma : E ≃ₐ[F] E) :
    (kummerQuotientGaloisRep (F := F) (E := E) (p : ℕ) gamma).comp
        (maschkeKummerProjectorMap p hcard chi) =
      (chi gamma : ZMod (p : ℕ)) •
        maschkeKummerProjectorMap p hcard chi := by
  have h := congrArg
    (kummerQuotientGaloisRep (F := F) (E := E) (p : ℕ)).asAlgebraHom
    (maschkeCyclotomicProjector_translate p hcard chi gamma)
  simpa [maschkeKummerProjectorMap, ← Module.End.mul_eq_comp] using h

/-- A vector with cyclotomic transformation law is fixed by the associated
Maschke projector. -/
private theorem maschkeKummerProjectorMap_apply_of_eigen
    (p : NU.LocalTheory.OddPrime)
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite (E ≃ₐ[F] E)]
    (hcard : (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ)) ≠ 0)
    (chi : (E ≃ₐ[F] E) →* (ZMod (p : ℕ))ˣ)
    (x : NU.LocalTheory.KummerQuotient E (p : ℕ))
    (hx : ∀ gamma,
      kummerQuotientGaloisRep (F := F) (E := E) (p : ℕ) gamma x =
        (chi gamma : ZMod (p : ℕ)) • x) :
    maschkeKummerProjectorMap p hcard chi x = x := by
  classical
  letI := Fintype.ofFinite (E ≃ₐ[F] E)
  unfold maschkeKummerProjectorMap
  unfold maschkeCyclotomicProjector
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [Representation.asAlgebraHom_single,
    LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have hterm (delta : E ≃ₐ[F] E) :
      ((↑((Units.mk0
          (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ)) hcard)⁻¹) :
          ZMod (p : ℕ)) * ((chi delta)⁻¹ : ZMod (p : ℕ))) *
        (chi delta : ZMod (p : ℕ)) =
      (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ))⁻¹ := by
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul, mul_inv_cancel₀ hcard, one_smul]

/-- The range of the idempotent is exactly the cyclotomic eigenspace; this
is the concrete Maschke characterization used in descent. -/
private theorem mem_maschkeKummerProjectorMap_range_iff
    (p : NU.LocalTheory.OddPrime)
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Finite (E ≃ₐ[F] E)]
    (hcard : (Nat.card (E ≃ₐ[F] E) : ZMod (p : ℕ)) ≠ 0)
    (chi : (E ≃ₐ[F] E) →* (ZMod (p : ℕ))ˣ)
    (x : NU.LocalTheory.KummerQuotient E (p : ℕ)) :
    x ∈ LinearMap.range (maschkeKummerProjectorMap p hcard chi) ↔
      ∀ gamma,
        kummerQuotientGaloisRep (F := F) (E := E) (p : ℕ) gamma x =
          (chi gamma : ZMod (p : ℕ)) • x := by
  constructor
  · rintro ⟨y, rfl⟩ gamma
    have h := congrArg
      (fun f : NU.LocalTheory.KummerQuotient E (p : ℕ) →ₗ[ZMod (p : ℕ)]
          NU.LocalTheory.KummerQuotient E (p : ℕ) => f y)
      (kummerGaloisAction_comp_maschkeKummerProjectorMap
        p hcard chi gamma)
    simpa using h
  · intro hx
    exact ⟨x, maschkeKummerProjectorMap_apply_of_eigen
      p hcard chi x hx⟩

/-- Quotienting a product by `n` is the product of the quotients. -/
private noncomputable def modNProdLinearMap
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    ModN (A × B) n →ₗ[ZMod n] ModN A n × ModN B n :=
  ModN.liftEquiv'.symm
    ⟨{ toFun := fun x => (ModN.mkQ n x.1, ModN.mkQ n x.2)
       map_zero' := by simp
       map_add' := by intro x y; ext <;> simp },
     fun x => by
       apply Prod.ext
       · change n • ModN.mkQ n x.1 = 0
         rw [← map_nsmul]
         change Submodule.Quotient.mk (n • x.1) = 0
         rw [Submodule.Quotient.mk_eq_zero]
         exact ⟨x.1, by simp⟩
       · change n • ModN.mkQ n x.2 = 0
         rw [← map_nsmul]
         change Submodule.Quotient.mk (n • x.2) = 0
         rw [Submodule.Quotient.mk_eq_zero]
         exact ⟨x.2, by simp⟩⟩

private theorem modNProdLinearMap_bijective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    Function.Bijective
      (modNProdLinearMap (A := A) (B := B) n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (A × B) (n : ℤ))).mkQ_surjective x
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (A × B) (n : ℤ))).mkQ_surjective y
    change (ModN.mkQ n x.1, ModN.mkQ n x.2) =
      (ModN.mkQ n y.1, ModN.mkQ n y.2) at hxy
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have h1 : ModN.mkQ n (x.1 - y.1) = 0 := by
      simpa using sub_eq_zero.mpr (congrArg Prod.fst hxy)
    have h2 : ModN.mkQ n (x.2 - y.2) = 0 := by
      simpa using sub_eq_zero.mpr (congrArg Prod.snd hxy)
    change Submodule.Quotient.mk _ = 0 at h1 h2
    rw [Submodule.Quotient.mk_eq_zero] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨(a, b), by ext <;> simp_all⟩
  · intro x
    obtain ⟨a, ha⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ A (n : ℤ))).mkQ_surjective x.1
    obtain ⟨b, hb⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ B (n : ℤ))).mkQ_surjective x.2
    refine ⟨ModN.mkQ n (a, b), ?_⟩
    change (ModN.mkQ n a, ModN.mkQ n b) = x
    exact Prod.ext ha hb

private noncomputable def modNProdLinearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    ModN (A × B) n ≃ₗ[ZMod n] ModN A n × ModN B n :=
  LinearEquiv.ofBijective
    (modNProdLinearMap (A := A) (B := B) n)
    (modNProdLinearMap_bijective n)

/-- The product comparison iterated over four factors. -/
private noncomputable def modNFourLinearEquiv
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] (n : ℕ) :
    ModN (A × B × C × D) n ≃ₗ[ZMod n]
      ModN A n × ModN B n × ModN C n × ModN D n :=
  (modNProdLinearEquiv (A := A) (B := B × C × D) n).trans
    ((LinearEquiv.refl (ZMod n) (ModN A n)).prodCongr
      ((modNProdLinearEquiv (A := B) (B := C × D) n).trans
        ((LinearEquiv.refl (ZMod n) (ModN B n)).prodCongr
          (modNProdLinearEquiv (A := C) (B := D) n))))

/-- A divisible additive group has trivial quotient modulo `n`. -/
private theorem modN_subsingleton_of_divisible
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (hdiv : ∀ x : G, ∃ y : G, n • y = x) :
    Subsingleton (ModN G n) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ :=
    (LinearMap.range
      (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective a
  obtain ⟨y, rfl⟩ :=
    (LinearMap.range
      (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective b
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨z, hz⟩ := hdiv (x - y)
  exact ⟨z, by simpa using hz⟩

private theorem modN_finrank_zero_of_divisible
    {G : Type*} [AddCommGroup G] (p : Nat.Primes)
    (hdiv : ∀ x : G, ∃ y : G, (p : ℕ) • y = x) :
    Module.finrank (ZMod (p : ℕ))
      (ModN G (p : ℕ)) = 0 := by
  letI : Subsingleton (ModN G (p : ℕ)) :=
    modN_subsingleton_of_divisible (p : ℕ) hdiv
  exact Module.finrank_eq_zero_of_subsingleton _ _

/-- The valuation lattice contributes one dimension modulo `p`. -/
private theorem intMod_finrank (p : Nat.Primes) :
    Module.finrank (ZMod (p : ℕ)) (ModN ℤ (p : ℕ)) = 1 := by
  let b := Module.Free.chooseBasis ℤ ℤ
  calc
    Module.finrank (ZMod (p : ℕ)) (ModN ℤ (p : ℕ)) =
        Fintype.card (Module.Free.ChooseBasisIndex ℤ ℤ) :=
      Module.finrank_eq_card_basis (ModN.basis b)
    _ = Module.finrank ℤ ℤ := by
      symm
      exact Module.finrank_eq_card_chooseBasisIndex ℤ ℤ
    _ = 1 := Module.finrank_self ℤ

private theorem additiveMultiplicativeIntMod_finrank
    (p : Nat.Primes) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive (Multiplicative ℤ)) (p : ℕ)) = 1 := by
  rw [(modNLinearEquivOfAddEquiv (p : ℕ)
    (AddEquiv.additiveMultiplicative ℤ)).finrank_eq]
  exact intMod_finrank p

/-- Multiplication by `n` is onto on `ZMod N` when the two are coprime. -/
private theorem zmod_is_nDivisible_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : ZMod N) : ∃ y : ZMod N, n • y = x := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime n hcop
  let y : ZMod N := (u⁻¹ : (ZMod N)ˣ) * x
  refine ⟨y, ?_⟩
  rw [nsmul_eq_mul]
  change (n : ZMod N) * y = x
  have hu : (u : ZMod N) = (n : ZMod N) :=
    ZMod.coe_unitOfCoprime n hcop
  rw [← hu]
  simp [y]

private theorem additiveMultiplicativeZMod_is_nDivisible_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : Additive (Multiplicative (ZMod N))) :
    ∃ y, n • y = x := by
  obtain ⟨y, hy⟩ := zmod_is_nDivisible_of_coprime n N hcop
    (AddEquiv.additiveMultiplicative (ZMod N) x)
  refine ⟨(AddEquiv.additiveMultiplicative (ZMod N)).symm y, ?_⟩
  apply (AddEquiv.additiveMultiplicative (ZMod N)).injective
  simpa using hy

/-- A coprime power cannot kill a nontrivial element of a cyclic group. -/
private theorem multiplicativeZMod_pow_eq_one_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : Multiplicative (ZMod N)) (hx : x ^ n = 1) : x = 1 := by
  apply Multiplicative.toAdd.injective
  have hxadd := congrArg Multiplicative.toAdd hx
  change n • Multiplicative.toAdd x = 0 at hxadd
  have hsurj : Function.Surjective
      (fun z : ZMod N => n • z) := by
    intro z
    exact zmod_is_nDivisible_of_coprime n N hcop z
  have hinj : Function.Injective
      (fun z : ZMod N => n • z) :=
    Finite.injective_iff_surjective.mpr hsurj
  exact hinj (by simpa using hxadd)

/-- Coordinatewise reduction modulo `p` on a `p`-adic vector. -/
private noncomputable def padicVectorReductionAddHom
    (p : Nat.Primes) (d : ℕ) :
    (Fin d → ℤ_[p]) →+ (Fin d → ZMod (p : ℕ)) where
  toFun x i := PadicInt.toZMod (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private noncomputable def padicVectorModLinearMap
    (p : Nat.Primes) (d : ℕ) :
    ModN (Fin d → ℤ_[p]) (p : ℕ) →ₗ[ZMod (p : ℕ)]
      (Fin d → ZMod (p : ℕ)) :=
  ModN.liftEquiv'.symm
    ⟨padicVectorReductionAddHom p d, fun x => by
      ext i
      change (p : ℕ) • PadicInt.toZMod (x i) = 0
      rw [← map_nsmul]
      simp⟩

private theorem padicVectorModLinearMap_bijective
    (p : Nat.Primes) (d : ℕ) :
    Function.Bijective (padicVectorModLinearMap p d) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Fin d → ℤ_[p])
        ((p : ℕ) : ℤ))).mkQ_surjective a
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Fin d → ℤ_[p])
        ((p : ℕ) : ℤ))).mkQ_surjective b
    apply sub_eq_zero.mp
    change ModN.mkQ (p : ℕ) x - ModN.mkQ (p : ℕ) y = 0
    rw [← map_sub]
    change Submodule.Quotient.mk (x - y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hred : ∀ i, PadicInt.toZMod (x i - y i) = 0 := by
      intro i
      have hi := congrFun hab i
      change PadicInt.toZMod (x i) = PadicInt.toZMod (y i) at hi
      simpa using sub_eq_zero.mpr hi
    have hdiv (i : Fin d) : (p : ℤ_[p]) ∣ x i - y i := by
      rw [← Ideal.mem_span_singleton,
        ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod]
      exact hred i
    choose z hz using hdiv
    refine ⟨z, ?_⟩
    funext i
    change ((p : ℕ) : ℤ) • z i = x i - y i
    change ((p : ℕ) : ℤ_[p]) * z i = x i - y i
    exact (hz i).symm
  · intro x
    choose y hy using fun i =>
      ZMod.ringHom_surjective PadicInt.toZMod (x i)
    refine ⟨ModN.mkQ (p : ℕ) y, ?_⟩
    ext i
    exact hy i

private noncomputable def padicVectorModLinearEquiv
    (p : Nat.Primes) (d : ℕ) :
    ModN (Fin d → ℤ_[p]) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      (Fin d → ZMod (p : ℕ)) :=
  LinearEquiv.ofBijective (padicVectorModLinearMap p d)
    (padicVectorModLinearMap_bijective p d)

private theorem padicVectorMod_finrank
    (p : Nat.Primes) (d : ℕ) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Fin d → ℤ_[p]) (p : ℕ)) = d := by
  rw [(padicVectorModLinearEquiv p d).finrank_eq]
  simp

/-! ## Finite `p`-power torsion in a completion -/

/-- The residue field of a number-field completion is finite. -/
private theorem completionResidueFinite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  let F := v.adicCompletion K
  let A := NU.LocalTheory.primeValuationSubring v
  let B := v.adicCompletionIntegers K
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Algebra (𝓞 K) A :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let eA := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A
  letI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_equiv ((𝓞 K) ⧸ v.asIdeal) eA.toEquiv
  let emb : K →+* F := algebraMap K F
  have hemb_mem (a : A) : emb (a : K) ∈ B := by
    rw [show B = v.adicCompletionIntegers K from rfl,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((a : K) : F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have ha : (a : K) ∈ (v.valuation K).valuationSubring := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact a.property
    exact ha
  let f : A →+* B := RingHom.codRestrict
    (emb.comp A.subtype) B hemb_mem
  have hfmax : IsLocalRing.maximalIdeal A ≤
      Ideal.comap f (IsLocalRing.maximalIdeal B) := by
    intro a ha
    rw [Ideal.mem_comap, B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v ((f a : B) : F) < Valued.v (1 : F)
    rw [map_one]
    have ha' : v.valuation K (a : K) < 1 := by
      have hA : A = (v.valuation K).valuationSubring :=
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
      let ea : A ≃+* (v.valuation K).valuationSubring :=
        RingEquiv.subringCongr
          (congrArg (fun W : ValuationSubring K => W.toSubring) hA)
      have hea : ea a ∈ IsLocalRing.maximalIdeal
          ((v.valuation K).valuationSubring) := by
        change a ∈ IsLocalRing.maximalIdeal A at ha
        simpa [ea] using ha
      exact (Valuation.mem_maximalIdeal_iff K
        (v := v.valuation K)).mp hea
    change Valued.v ((a : K) : F) < 1
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  letI : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 3 0).mp hfmax
  let rf : IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField B := IsLocalRing.ResidueField.map f
  have hrf : Function.Surjective rf := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    have hopen : Metric.ball (b : F) 1 ∈ nhds (b : F) :=
      Metric.ball_mem_nhds _ zero_lt_one
    obtain ⟨x, hx⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).mem_nhds
        hopen
    have hxclose : ‖algebraMap K F x - (b : F)‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hvclose : Valued.v (algebraMap K F x - (b : F)) < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mp hxclose
    have hxcoe : (x : F) = algebraMap K F x := rfl
    have hvclose' : Valued.v ((x : F) - (b : F)) < 1 := by
      rw [hxcoe]
      exact hvclose
    have hxint : v.valuation K x ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      rw [show (x : F) = ((x : F) - (b : F)) + (b : F) by ring]
      exact Valuation.map_add_le _ hvclose'.le b.property
    let a : A := ⟨x, by
      rw [show A = (v.valuation K).valuationSubring from
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v]
      exact hxint⟩
    refine ⟨IsLocalRing.residue A a, ?_⟩
    rw [show rf = IsLocalRing.ResidueField.map f from rfl,
      IsLocalRing.ResidueField.map_residue]
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
      B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v (((f a : B) - b : B) : F) < Valued.v (1 : F)
    rw [map_one]
    change Valued.v ((x : F) - (b : F)) < 1
    exact hvclose'
  exact Finite.of_surjective rf hrf

/-- The canonical valuation relation on a number-field completion. -/
@[reducible] private noncomputable def completionValuativeRel
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion K) _)

/-- A number-field completion is a nonarchimedean local field. -/
private theorem completionIsLocalField
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : IsDiscreteValuationRing (Valued.integer F) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : Finite (Valued.ResidueField F) := completionResidueFinite v
  letI : ProperSpace F :=
    (@Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      F _ _ _ _).2 ⟨inferInstance, inferInstance, inferInstance⟩
  letI : LocallyCompactSpace F := by infer_instance
  let vF := (Valued.v : Valuation F _)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  letI : IsValuativeTopology F :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle vF (by
      intro s
      exact Valued.is_topological_valuation s)
  letI : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vF).2 inferInstance
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The norm-one unit sphere of a nonarchimedean local field is compact. -/
private theorem localField_unitSphere_isCompact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsCompact {x : Units F |
      ValuativeRel.valuation F (x : F) = 1} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himage :
      Units.val '' {x : Units F |
        ValuativeRel.valuation F (x : F) = 1} =
        {x : F | (ValuativeRel.valuation F).restrict x = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (ValuativeRel.valuation F).restrict_eq_one_iff.mpr hy
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        simp at hx
      let y : Units F := Units.mk0 x hx0
      exact ⟨y,
        (ValuativeRel.valuation F).restrict_eq_one_iff.mp hx, rfl⟩
  rw [himage]
  have hO : IsCompact (NU.LCFT.RingOfIntegers F : Set F) := by
    change IsCompact {x : F | x ∈ NU.LCFT.RingOfIntegers F}
    simpa only [Subtype.range_coe_subtype] using
      (isCompact_range (continuous_subtype_val : Continuous
        ((↑) : NU.LCFT.RingOfIntegers F → F)))
  apply IsCompact.of_isClosed_subset hO
    ((ValuativeRel.valuation F).isClosed_sphere 1)
  intro x hx
  exact (Valuation.mem_integer_iff _ _).mpr
    ((ValuativeRel.valuation F).restrict_eq_one_iff.mp hx).le

/-- A closed subgroup all of whose elements have `p`-power order is finite. -/
private theorem pPowerTorsion_finite_of_isClosed
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F]
    (p : Nat.Primes) (P : Subgroup (Units F))
    (hclosed : IsClosed (P : Set (Units F)))
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) : Finite P := by
  have hsubset : (P : Set (Units F)) ⊆
      {x : Units F | ValuativeRel.valuation F (x : F) = 1} := by
    intro u hu
    obtain ⟨a, ha⟩ := (hP u).1 hu
    have hN : (p : ℕ) ^ a ≠ 0 := pow_ne_zero _ p.2.ne_zero
    have hv := congrArg (ValuativeRel.valuation F)
      (congrArg Units.val ha)
    change ValuativeRel.valuation F
      ((u : F) ^ ((p : ℕ) ^ a)) =
        ValuativeRel.valuation F (1 : F) at hv
    rw [map_pow, map_one] at hv
    apply pow_left_injective hN
    simpa using hv
  have hcompact : IsCompact (P : Set (Units F)) :=
    IsCompact.of_isClosed_subset (localField_unitSphere_isCompact F)
      hclosed hsubset
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hcompact
  let H (a : ℕ) : Subgroup P :=
    (powMonoidHom ((p : ℕ) ^ a) : P →* P).ker
  have hHclosed (a : ℕ) : IsClosed (H a : Set P) := by
    exact isClosed_singleton.preimage
      (continuous_id.pow ((p : ℕ) ^ a))
  have hHcover : ⋃ a : ℕ, (H a : Set P) = Set.univ := by
    ext u
    simp only [Set.mem_iUnion, SetLike.mem_coe,
      Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := (hP (u : Units F)).1 u.2
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨a, ha⟩ :=
    nonempty_interior_of_iUnion_of_closed hHclosed hHcover
  have hHopen : IsOpen (H a : Set P) := by
    obtain ⟨x, hx⟩ := ha
    exact (H a).isOpen_of_mem_nhds
      (mem_interior_iff_mem_nhds.mp hx)
  letI : Finite (P ⧸ H a) :=
    (H a).quotient_finite_of_isOpen hHopen
  have hHa : Finite (H a) := by
    let emb : H a → rootsOfUnity ((p : ℕ) ^ a) F := fun x =>
      ⟨(x.1.1 : Units F), by
        rw [mem_rootsOfUnity]
        exact congrArg (fun z : P => (z : Units F)) x.2⟩
    exact Finite.of_injective emb (fun x y h => by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact congrArg
        (fun z : rootsOfUnity ((p : ℕ) ^ a) F =>
          ((z.1 : Units F) : F)) h)
  letI : Finite (H a) := hHa
  exact Finite.of_subgroup_quotient (H a)

/-- Multiplication by `p` on the `p`-power torsion has kernel `μ_p`. -/
private noncomputable def pPowerKernelEquivRoots
    (F : Type*) [Field F] (p : Nat.Primes)
    (P : Subgroup (Units F))
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) :
    (nsmulAddMonoidHom (p : ℕ) :
      Additive P →+ Additive P).ker ≃ rootsOfUnity (p : ℕ) F where
  toFun x := by
    refine ⟨(x.1.toMul : P).1, ?_⟩
    rw [mem_rootsOfUnity]
    have hx := x.2
    change (p : ℕ) • x.1 = 0 at hx
    have hxP : (x.1.toMul : P) ^ (p : ℕ) = 1 := by
      rw [← toMul_nsmul, hx]
      rfl
    exact congrArg Subtype.val hxP
  invFun z := by
    let u : Units F := z.1
    have huz : u ^ (p : ℕ) = 1 :=
      (mem_rootsOfUnity (p : ℕ) u).mp z.2
    have huP : u ∈ P := (hP u).2 ⟨1, by simpa using huz⟩
    let x : Additive P := Additive.ofMul ⟨u, huP⟩
    refine ⟨x, ?_⟩
    change (p : ℕ) • x = 0
    apply Additive.toMul.injective
    change (⟨u, huP⟩ : P) ^ (p : ℕ) = 1
    apply Subtype.ext
    exact huz
  left_inv x := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- A finite `p`-power root subgroup contributes the root correction. -/
private theorem pPowerMod_finrank_of_finite
    (F : Type*) [Field F] (p : Nat.Primes)
    (P : Subgroup (Units F)) [Finite P]
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) =
        primitiveRootCorrection F p := by
  classical
  unfold primitiveRootCorrection
  let f : Additive P →+ Additive P :=
    nsmulAddMonoidHom (p : ℕ)
  let H : AddSubgroup (Additive P) :=
    (LinearMap.range (LinearMap.lsmul ℤ (Additive P)
      (((p : ℕ) : ℤ)))).toAddSubgroup
  letI : Finite (ModN (Additive P) (p : ℕ)) := Quotient.finite _
  letI : Module.Finite (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) := Module.Finite.of_finite
  have hH : H = f.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [f]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [f]⟩
  have hcardquot : Nat.card (ModN (Additive P) (p : ℕ)) =
      Nat.card f.ker := by
    calc
      Nat.card (ModN (Additive P) (p : ℕ)) = H.index := by
        exact (AddSubgroup.index_eq_card H).symm
      _ = f.range.index := by rw [hH]
      _ = Nat.card f.ker := AddSubgroup.index_range
  have hcardker : Nat.card f.ker =
      if ∃ z : F, IsPrimitiveRoot z (p : ℕ)
      then (p : ℕ) else 1 := by
    rw [Nat.card_congr (pPowerKernelEquivRoots F p P hP)]
    split_ifs with h
    · exact h.choose_spec.card_rootsOfUnity
    · letI : Subsingleton (rootsOfUnity (p : ℕ) F) :=
        ⟨fun x y => by
          have hxpow : (x.1 : Units F) ^ (p : ℕ) = 1 :=
            (mem_rootsOfUnity (p : ℕ) x.1).mp x.2
          have hypow : (y.1 : Units F) ^ (p : ℕ) = 1 :=
            (mem_rootsOfUnity (p : ℕ) y.1).mp y.2
          have hone (z : rootsOfUnity (p : ℕ) F)
              (hzpow : (z.1 : Units F) ^ (p : ℕ) = 1) : z = 1 := by
            have hdvd : orderOf z.1 ∣ (p : ℕ) :=
              orderOf_dvd_of_pow_eq_one hzpow
            rcases (Nat.dvd_prime p.2).mp hdvd with horder | horder
            · apply Subtype.ext
              exact orderOf_eq_one_iff.mp horder
            · exfalso
              apply h
              have hzprim : IsPrimitiveRoot z.1 (p : ℕ) := by
                simpa [horder] using IsPrimitiveRoot.orderOf z.1
              exact ⟨((z.1 : Units F) : F),
                IsPrimitiveRoot.coe_units_iff.mpr hzprim⟩
          rw [hone x hxpow, hone y hypow]⟩
      exact Nat.card_unique
  have hvcard : (p : ℕ) ^ Module.finrank (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) = Nat.card f.ker := by
    rw [← hcardquot]
    simpa using (Module.natCard_eq_pow_finrank
      (K := ZMod (p : ℕ))
      (V := ModN (Additive P) (p : ℕ))).symm
  rw [hcardker] at hvcard
  split_ifs at hvcard ⊢
  · apply Nat.pow_right_injective p.2.two_le
    simpa using hvcard
  · apply Nat.pow_right_injective p.2.two_le
    simpa using hvcard

/-! ## Exact rank from the supplied unit decomposition -/

/-- Residue characteristic is the norm of the prime contracted to `ℤ`. -/
private theorem residueCharacteristic_eq_absNorm_under
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.residueCharacteristic v =
      Ideal.absNorm (Ideal.under ℤ v.asIdeal) := by
  letI : Algebra (𝓞 K) (NU.LocalTheory.primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (NU.LocalTheory.primeValuationSubring v)
  calc
    NU.LocalTheory.residueCharacteristic v =
        ringChar ((𝓞 K) ⧸ v.asIdeal) := by
      rw [NU.LocalTheory.residueCharacteristic, ringChar.eq_iff]
      exact (e.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 K) ⧸ v.asIdeal))
    _ = Ideal.absNorm (Ideal.under ℤ v.asIdeal) :=
      Ideal.ringChar_quot v.asIdeal

/-- Restriction through a number-field extension preserves residue
characteristic. -/
private theorem residueCharacteristic_restrictFinitePlace
    (K : Type*) {L : Type*}
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : NU.LocalTheory.FinitePlace L) :
    NU.LocalTheory.residueCharacteristic
        (NU.LocalTheory.restrictFinitePlace K v) =
      NU.LocalTheory.residueCharacteristic v := by
  rw [residueCharacteristic_eq_absNorm_under,
    residueCharacteristic_eq_absNorm_under,
    NU.LocalTheory.restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

/-- A rational finite place has norm equal to its residue characteristic. -/
private theorem rationalPrimeNorm_eq_residueCharacteristic
    (v : NU.Chebotarev.PrimeIdeal ℚ) :
    NU.Chebotarev.PrimeIdeal.norm v =
      NU.LocalTheory.residueCharacteristic v := by
  rw [residueCharacteristic_eq_absNorm_under]
  change Ideal.absNorm v.asIdeal = Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  let f : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.ringOfIntegersEquiv
  have hf : f.symm.toRingHom =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) := by
    exact RingHom.ext_int _ _
  have hmap : Ideal.map f.toRingHom v.asIdeal =
      Ideal.under ℤ v.asIdeal := by
    calc
      Ideal.map f.toRingHom v.asIdeal =
          Ideal.comap f.symm v.asIdeal := by
        simpa using Ideal.map_comap_of_equiv (I := v.asIdeal) f
      _ = Ideal.under ℤ v.asIdeal := by
        rw [Ideal.under_def]
        exact congrArg
          (fun g : ℤ →+* NumberField.RingOfIntegers ℚ =>
            Ideal.comap g v.asIdeal) hf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv v.asIdeal (Ideal.under ℤ v.asIdeal)
      f hmap.symm).toEquiv

/-- The residue characteristic is coprime to one less than the residue
norm. -/
private theorem residueCharacteristic_coprime_norm_sub_one
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v) :
    (p : ℕ).Coprime
      (NU.Chebotarev.PrimeIdeal.norm v - 1) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hnorm : NU.Chebotarev.PrimeIdeal.norm v =
      NU.Chebotarev.PrimeIdeal.norm q ^
        v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    exact NU.Chebotarev.PrimeIdeal.norm_pow_inertiaDeg
      v q inferInstance
  have hq : NU.Chebotarev.PrimeIdeal.norm q =
      NU.LocalTheory.residueCharacteristic v := by
    rw [rationalPrimeNorm_eq_residueCharacteristic,
      residueCharacteristic_restrictFinitePlace]
  have hf : 0 <
      v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_pos v.asIdeal
      (NumberField.RingOfIntegers ℚ)
  rw [hnorm, hq, ← hp]
  have hpow : ((p : ℕ) ^
      v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)).Coprime
      ((p : ℕ) ^
        v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) - 1) :=
    (Nat.coprime_self_sub_right
      (pow_pos p.2.pos _)).2 (Nat.coprime_one_right _)
  exact (Nat.coprime_pow_left_iff hf _ _).mp hpow

/-- In the four-factor decomposition the `p`-power torsion factor is
closed. -/
private theorem localUnitDecomposition_pPowerTorsion_isClosed
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    IsClosed (units.pPowerTorsion :
      Set (Units (v.adicCompletion K))) := by
  let F := v.adicCompletion K
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top
      (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let e := units.productEquiv
  have hcoords (u : Units F) :
      u ∈ units.pPowerTorsion ↔
        (e u).1 = 1 ∧ (e u).2.1 = 1 ∧ (e u).2.2.2 = 1 := by
    constructor
    · intro hu
      obtain ⟨a, ha⟩ :=
        (units.pPowerTorsion_spec u).1 hu
      let N : ℕ := (p : ℕ) ^ a
      have hN : N ≠ 0 := pow_ne_zero _ p.2.ne_zero
      have hpow : (e u) ^ N = 1 := by
        rw [← map_pow, ha, map_one]
      have hvalpow : (e u).1 ^ N = 1 :=
        congrArg (fun x => x.1) hpow
      have hteichpow : (e u).2.1 ^ N = 1 :=
        congrArg (fun x => x.2.1) hpow
      have hfreepow : (e u).2.2.2 ^ N = 1 :=
        congrArg (fun x => x.2.2.2) hpow
      refine ⟨?_, ?_, ?_⟩
      · apply units.valuationEquiv.injective
        apply pow_left_injective hN
        simpa using congrArg units.valuationEquiv hvalpow
      · apply units.teichmullerEquiv.injective
        have hzpow :
            (units.teichmullerEquiv (e u).2.1) ^ N = 1 := by
          simpa using congrArg units.teichmullerEquiv hteichpow
        have hcop : N.Coprime
            (NU.Chebotarev.PrimeIdeal.norm v - 1) := by
          simpa [N, hp] using
            (residueCharacteristic_coprime_norm_sub_one v p hp).pow_left a
        simpa using multiplicativeZMod_pow_eq_one_of_coprime
          N (NU.Chebotarev.PrimeIdeal.norm v - 1) hcop
          (units.teichmullerEquiv (e u).2.1) hzpow
      · apply units.freePrincipalUnitsEquiv.injective
        apply pow_left_injective hN
        simpa using congrArg units.freePrincipalUnitsEquiv hfreepow
    · rintro ⟨hval, hteich, hfree⟩
      let cp : units.pPowerTorsion := (e u).2.2.1
      obtain ⟨a, ha⟩ :=
        (units.pPowerTorsion_spec (cp : Units F)).1 cp.2
      apply (units.pPowerTorsion_spec u).2
      refine ⟨a, ?_⟩
      apply e.injective
      rw [map_pow, map_one]
      apply Prod.ext
      · simpa [hval]
      · apply Prod.ext
        · simpa [hteich]
        · apply Prod.ext
          · apply Subtype.ext
            exact ha
          · simpa [hfree]
  have hset : (units.pPowerTorsion : Set (Units F)) =
      {u | (e u).1 = 1 ∧ (e u).2.1 = 1 ∧
        (e u).2.2.2 = 1} := by
    ext u
    exact hcoords u
  rw [hset]
  have he : Continuous e := e.continuous
  exact (isClosed_eq (continuous_fst.comp he)
    continuous_const).inter
      ((isClosed_eq (continuous_fst.comp
        (continuous_snd.comp he)) continuous_const).inter
      (isClosed_eq (continuous_snd.comp
        (continuous_snd.comp
          (continuous_snd.comp he))) continuous_const))

private theorem localUnitDecomposition_pPowerTorsion_finite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Finite units.pPowerTorsion := by
  let F := v.adicCompletion K
  letI : CharZero F := charZero_of_injective_algebraMap
    (algebraMap K F).injective
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  exact pPowerTorsion_finite_of_isClosed F p units.pPowerTorsion
    (localUnitDecomposition_pPowerTorsion_isClosed v p hp units)
    units.pPowerTorsion_spec

private theorem localUnitDecomposition_pPowerTorsionMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive units.pPowerTorsion) (p : ℕ)) =
      primitiveRootCorrection (v.adicCompletion K) p := by
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v p hp units
  exact pPowerMod_finrank_of_finite
    (v.adicCompletion K) p units.pPowerTorsion
    units.pPowerTorsion_spec

private theorem localUnitDecomposition_valuationMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive units.valuationFactor) (p : ℕ)) = 1 := by
  rw [(modNLinearEquivOfAddEquiv (p : ℕ)
    units.valuationEquiv.toMulEquiv.toAdditive).finrank_eq]
  exact additiveMultiplicativeIntMod_finrank p

private theorem localUnitDecomposition_teichmullerMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive units.teichmullerFactor) (p : ℕ)) = 0 := by
  have hnorm : 1 < NU.Chebotarev.PrimeIdeal.norm v := by
    have hne0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
      change Ideal.absNorm v.asIdeal ≠ 0
      exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
    have hne1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
      change Ideal.absNorm v.asIdeal ≠ 1
      exact fun h => v.isMaximal.ne_top
        (Ideal.absNorm_eq_one_iff.mp h)
    omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnorm).ne'⟩
  rw [(modNLinearEquivOfAddEquiv (p : ℕ)
    units.teichmullerEquiv.toMulEquiv.toAdditive).finrank_eq]
  apply modN_finrank_zero_of_divisible
  apply additiveMultiplicativeZMod_is_nDivisible_of_coprime
    (p : ℕ) (NU.Chebotarev.PrimeIdeal.norm v - 1)
  exact residueCharacteristic_coprime_norm_sub_one v p hp

private theorem localUnitDecomposition_freeMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive units.freePrincipalUnits) (p : ℕ)) =
        finitePlaceLocalDegree v := by
  rw [(modNLinearEquivOfAddEquiv (p : ℕ)
    units.freePrincipalUnitsEquiv.toMulEquiv.toAdditive).finrank_eq]
  exact padicVectorMod_finrank p (finitePlaceLocalDegree v)

/-- The unit product decomposition descends to the four factors modulo `p`. -/
private noncomputable def localUnitDecomposition_kummerQuotientLinearEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    NU.LocalTheory.KummerQuotient
        (v.adicCompletion K) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      ModN (Additive units.valuationFactor) (p : ℕ) ×
      ModN (Additive units.teichmullerFactor) (p : ℕ) ×
      ModN (Additive units.pPowerTorsion) (p : ℕ) ×
      ModN (Additive units.freePrincipalUnits) (p : ℕ) :=
  (modNLinearEquivOfAddEquiv (p : ℕ)
    (units.productEquiv.toMulEquiv.toAdditive.trans
      additiveProdFourAddEquiv)).trans
    (modNFourLinearEquiv (p : ℕ))

/-- Exact mod-`p` rank of the multiplicative group supplied by the unit
package. -/
private theorem localUnitDecomposition_kummerQuotient_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient
        (v.adicCompletion K) (p : ℕ)) =
      1 + finitePlaceLocalDegree v +
        primitiveRootCorrection (v.adicCompletion K) p := by
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top
      (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let k := ZMod (p : ℕ)
  let V := ModN (Additive units.valuationFactor) (p : ℕ)
  let T := ModN (Additive units.teichmullerFactor) (p : ℕ)
  let P := ModN (Additive units.pPowerTorsion) (p : ℕ)
  let L := ModN (Additive units.freePrincipalUnits) (p : ℕ)
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v p hp units
  letI : Finite units.teichmullerFactor := Finite.of_equiv
    (Multiplicative
      (ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)))
    units.teichmullerEquiv.toEquiv.symm
  let eV := (modNLinearEquivOfAddEquiv (p : ℕ)
    units.valuationEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (p : ℕ)
        (AddEquiv.additiveMultiplicative ℤ))
  letI : Module.Finite k V := Module.Finite.equiv eV.symm
  letI : Finite T := Quotient.finite _
  letI : Module.Finite k T := Module.Finite.of_finite
  letI : Finite P := Quotient.finite _
  letI : Module.Finite k P := Module.Finite.of_finite
  let d := finitePlaceLocalDegree v
  let eL := ((modNLinearEquivOfAddEquiv (p : ℕ)
    units.freePrincipalUnitsEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (p : ℕ)
        (AddEquiv.additiveMultiplicative
          (Fin d → ℤ_[p])))).trans
      (padicVectorModLinearEquiv p d)
  letI : Module.Finite k L := Module.Finite.equiv eL.symm
  rw [(localUnitDecomposition_kummerQuotientLinearEquiv
    v p units).finrank_eq]
  change Module.finrank k (V × T × P × L) = _
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    localUnitDecomposition_valuationMod_finrank v p units,
    localUnitDecomposition_teichmullerMod_finrank v p hp units,
    localUnitDecomposition_pPowerTorsionMod_finrank v p hp units,
    localUnitDecomposition_freeMod_finrank v p units]
  omega

/-- The supplied decomposition also makes the local Kummer quotient a
finite-dimensional `ZMod p`-module. -/
private theorem localUnitDecomposition_kummerQuotient_moduleFinite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient
        (v.adicCompletion K) (p : ℕ)) := by
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top
      (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let k := ZMod (p : ℕ)
  let V := ModN (Additive units.valuationFactor) (p : ℕ)
  let T := ModN (Additive units.teichmullerFactor) (p : ℕ)
  let P := ModN (Additive units.pPowerTorsion) (p : ℕ)
  let L := ModN (Additive units.freePrincipalUnits) (p : ℕ)
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v p hp units
  letI : Finite units.teichmullerFactor := Finite.of_equiv
    (Multiplicative
      (ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)))
    units.teichmullerEquiv.toEquiv.symm
  let eV := (modNLinearEquivOfAddEquiv (p : ℕ)
    units.valuationEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (p : ℕ)
        (AddEquiv.additiveMultiplicative ℤ))
  letI : Module.Finite k V := Module.Finite.equiv eV.symm
  letI : Finite T := Quotient.finite _
  letI : Module.Finite k T := Module.Finite.of_finite
  letI : Finite P := Quotient.finite _
  letI : Module.Finite k P := Module.Finite.of_finite
  let d := finitePlaceLocalDegree v
  let eL := ((modNLinearEquivOfAddEquiv (p : ℕ)
    units.freePrincipalUnitsEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (p : ℕ)
        (AddEquiv.additiveMultiplicative
          (Fin d → ℤ_[p])))).trans
      (padicVectorModLinearEquiv p d)
  letI : Module.Finite k L := Module.Finite.equiv eL.symm
  exact Module.Finite.equiv
    (localUnitDecomposition_kummerQuotientLinearEquiv v p units).symm

/-! ## Continuous characters of the local multiplicative group -/

/-- Every mod-`p` additive homomorphism on the supplied local
multiplicative group is continuous.  The key open neighborhood consists of
units whose first three coordinates are trivial and whose free coordinate
is divisible by `p`. -/
private theorem localUnitAddHom_continuous
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v))
    (f : Additive (Units (v.adicCompletion K)) →+ ZMod (p : ℕ)) :
    Continuous f := by
  let F := v.adicCompletion K
  let e := units.productEquiv
  let d := finitePlaceLocalDegree v
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v p hp units
  letI : DiscreteTopology units.valuationFactor :=
    units.valuationEquiv.toHomeomorph.symm.discreteTopology
  letI : DiscreteTopology units.teichmullerFactor :=
    units.teichmullerEquiv.toHomeomorph.symm.discreteTopology
  letI : DiscreteTopology units.pPowerTorsion :=
    Finite.instDiscreteTopology
  let m : Ideal ℤ_[p] := IsLocalRing.maximalIdeal ℤ_[p]
  let S : Set (Fin d → ℤ_[p]) := Set.univ.pi (fun _ => (m : Set ℤ_[p]))
  have hSopen : IsOpen S := by
    apply isOpen_set_pi Set.finite_univ
    intro i hi
    exact IsLocalRing.isOpen_maximalIdeal ℤ_[p]
  let freeCoord : Units F → (Fin d → ℤ_[p]) := fun u =>
    Multiplicative.toAdd
      (units.freePrincipalUnitsEquiv (e u).2.2.2)
  have hfreeCoord : Continuous freeCoord := by
    fun_prop
  let O : Set (Units F) :=
    {u | (e u).1 = 1 ∧ (e u).2.1 = 1 ∧ (e u).2.2.1 = 1 ∧
      freeCoord u ∈ S}
  have hOopen : IsOpen O := by
    have hval : IsOpen {u : Units F | (e u).1 = 1} :=
      (isOpen_discrete ({1} : Set units.valuationFactor)).preimage (by
        fun_prop)
    have hteich : IsOpen {u : Units F | (e u).2.1 = 1} :=
      (isOpen_discrete ({1} : Set units.teichmullerFactor)).preimage (by
        fun_prop)
    have htor : IsOpen {u : Units F | (e u).2.2.1 = 1} :=
      (isOpen_discrete ({1} : Set units.pPowerTorsion)).preimage (by
        fun_prop)
    exact hval.inter (hteich.inter (htor.inter (hSopen.preimage hfreeCoord)))
  have hOne : (1 : Units F) ∈ O := by
    simp [O, freeCoord, S, m, e]
  let fm : Units F →* Multiplicative (ZMod (p : ℕ)) :=
    f.toMultiplicativeRight
  have hOker : O ⊆ (fm.ker : Set (Units F)) := by
    intro u hu
    rcases hu with ⟨huv, hut, hup, huf⟩
    have hdiv (i : Fin d) : (p : ℤ_[p]) ∣ freeCoord u i := by
      rw [← Ideal.mem_span_singleton,
        ← PadicInt.maximalIdeal_eq_span_p]
      exact huf i (Set.mem_univ i)
    choose y hy using hdiv
    let rf : units.freePrincipalUnits :=
      units.freePrincipalUnitsEquiv.symm (Multiplicative.ofAdd y)
    let r : Units F := e.symm (1, 1, 1, rf)
    have hr : r ^ (p : ℕ) = u := by
      apply e.injective
      rw [map_pow]
      have her : e r = (1, 1, 1, rf) := e.apply_symm_apply _
      rw [her]
      apply Prod.ext
      · simpa using huv.symm
      · apply Prod.ext
        · simpa using hut.symm
        · apply Prod.ext
          · simpa using hup.symm
          · apply units.freePrincipalUnitsEquiv.injective
            change units.freePrincipalUnitsEquiv (rf ^ (p : ℕ)) =
              units.freePrincipalUnitsEquiv (e u).2.2.2
            rw [map_pow]
            apply Multiplicative.toAdd.injective
            rw [toAdd_pow]
            change (p : ℕ) •
              Multiplicative.toAdd (units.freePrincipalUnitsEquiv rf) =
                freeCoord u
            rw [show units.freePrincipalUnitsEquiv rf =
              Multiplicative.ofAdd y by
                exact units.freePrincipalUnitsEquiv.apply_symm_apply _]
            change (p : ℕ) • y = freeCoord u
            funext i
            change ((p : ℕ) : ℤ_[p]) * y i = freeCoord u i
            exact (hy i).symm
    change f (Additive.ofMul u) = 0
    rw [← hr]
    change f ((p : ℕ) • Additive.ofMul r) = 0
    rw [map_nsmul]
    simp
  have hkerOpen : IsOpen (fm.ker : Set (Units F)) := by
    apply fm.ker.isOpen_of_mem_nhds
    exact Filter.mem_of_superset (hOopen.mem_nhds hOne) hOker
  have hfm : Continuous fm :=
    continuous_of_continuousAt_one fm (by
      rw [continuousAt_def]
      intro s hs
      have hs1 : (1 : Multiplicative (ZMod (p : ℕ))) ∈ s :=
        mem_of_mem_nhds (by simpa only [map_one] using hs)
      refine Filter.mem_of_superset
        (hkerOpen.mem_nhds fm.ker.one_mem) ?_
      intro x hx
      have hfx : fm x = 1 := MonoidHom.mem_ker.mp hx
      change fm x ∈ s
      rwa [hfx])
  exact hfm

/-- Continuous local characters are the linear dual of the multiplicative
quotient modulo `p`. -/
private noncomputable def localUnitCharacterDualLinearMap
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes) :
    NU.LocalTheory.ContinuousCharacter
        (Units (v.adicCompletion K)) (p : ℕ) →ₗ[ZMod (p : ℕ)]
      Module.Dual (ZMod (p : ℕ))
        (NU.LocalTheory.KummerQuotient
          (v.adicCompletion K) (p : ℕ)) where
  toFun chi :=
    (ModN.liftEquiv').symm
      ⟨chi.toAddMonoidHom, fun x => by
        rw [← map_nsmul]
        simp⟩
  map_add' a b := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ
        (Additive (Units (v.adicCompletion K)))
        (((p : ℕ) : ℤ)))).mkQ_surjective q
    rfl
  map_smul' c a := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ
        (Additive (Units (v.adicCompletion K)))
        (((p : ℕ) : ℤ)))).mkQ_surjective q
    change (c • a) x = c • a x
    let ev : NU.LocalTheory.ContinuousCharacter
        (Units (v.adicCompletion K)) (p : ℕ) →+ ZMod (p : ℕ) :=
      { toFun := fun chi => chi x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    simpa [ev] using ZMod.map_smul ev c a

private theorem localUnitCharacterDualLinearMap_bijective
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Function.Bijective (localUnitCharacterDualLinearMap v p) := by
  constructor
  · intro a b hab
    ext x
    have hx := DFunLike.congr_fun hab
      (ModN.mkQ (p : ℕ) x)
    exact hx
  · intro L
    let raw : Additive (Units (v.adicCompletion K)) →+ ZMod (p : ℕ) :=
      L.toAddMonoidHom.comp (ModN.mkQ (p : ℕ))
    let chi : NU.LocalTheory.ContinuousCharacter
        (Units (v.adicCompletion K)) (p : ℕ) :=
      ⟨raw, localUnitAddHom_continuous v p hp units raw⟩
    refine ⟨chi, ?_⟩
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ
        (Additive (Units (v.adicCompletion K)))
        (((p : ℕ) : ℤ)))).mkQ_surjective q
    rfl

private noncomputable def localUnitCharacterDualLinearEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    NU.LocalTheory.ContinuousCharacter
        (Units (v.adicCompletion K)) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      Module.Dual (ZMod (p : ℕ))
        (NU.LocalTheory.KummerQuotient
          (v.adicCompletion K) (p : ℕ)) :=
  LinearEquiv.ofBijective (localUnitCharacterDualLinearMap v p)
    (localUnitCharacterDualLinearMap_bijective v p hp units)

/-- Evaluation on a finite linearly independent family of continuous
characters is onto.  This is the finite-dimensional part of profinite
Pontryagin reflexivity used below. -/
private theorem characterFamilyEvaluation_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (p : Nat.Primes) {ι : Type*} [Fintype ι]
    (a : ι → NU.LocalTheory.ContinuousCharacter G (p : ℕ))
    (ha : LinearIndependent (ZMod (p : ℕ)) a) :
    Function.Surjective (fun x : NU.LocalTheory.ElementaryQuotient G (p : ℕ) =>
      fun i => NU.LocalTheory.evaluation (p : ℕ) x (a i)) := by
  classical
  let R := ZMod (p : ℕ)
  let C := NU.LocalTheory.ContinuousCharacter G (p : ℕ)
  let coeff : (ι → R) →ₗ[R] C := Fintype.linearCombination R a
  have hcoeff : Function.Injective coeff := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply funext
    intro i
    have hz : coeff (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact (Fintype.linearIndependent_iff.mp ha (x - y)
      (by simpa [coeff, Fintype.linearCombination_apply] using hz)) i
  have hdual : Function.Surjective coeff.dualMap :=
    LinearMap.dualMap_surjective_iff.mpr hcoeff
  intro y
  let psi : Module.Dual R (ι → R) :=
    { toFun := fun c => ∑ i, c i * y i
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        simp only [mul_assoc] }
  obtain ⟨L, hL⟩ := hdual psi
  obtain ⟨x, hx⟩ :=
    (NU.LocalTheory.evaluationLinear_bijective_of_compact_totallyDisconnected
      (G := G) (n := (p : ℕ))).2 L
  refine ⟨x, funext fun i => ?_⟩
  let ei : ι → R := Pi.single i (1 : R)
  have hi := DFunLike.congr_fun hL ei
  have hcoeffi : coeff ei = a i := by
    simp [coeff, ei, Fintype.linearCombination_apply, Pi.single_apply]
  have hpsii : psi ei = y i := by
    simp [psi, ei, Pi.single_apply]
  have hxi := DFunLike.congr_fun hx (a i)
  change NU.LocalTheory.evaluation (p : ℕ) x (a i) = L (a i) at hxi
  exact hxi.trans (by
    rw [LinearMap.dualMap_apply, hcoeffi, hpsii] at hi
    exact hi)

private theorem elementaryClass_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Function.Surjective
      (NU.LocalTheory.elementaryClass (G := G) n) := by
  intro x
  obtain ⟨y, rfl⟩ :=
    (LinearMap.range (LinearMap.lsmul ℤ
      (Additive (TopologicalAbelianization G)) (n : ℤ))).mkQ_surjective x
  cases y with
  | ofMul q =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, rfl⟩

private def characterFamilyMonoidHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (p : Nat.Primes) {ι : Type*}
    (a : ι → NU.LocalTheory.ContinuousCharacter G (p : ℕ)) :
    G →* Multiplicative (ι → ZMod (p : ℕ)) where
  toFun g := Multiplicative.ofAdd (fun i => a i (Additive.ofMul g))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact map_zero (a i)
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i
    exact map_add (a i) (Additive.ofMul g) (Additive.ofMul h)

private theorem characterFamilyMonoidHom_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (p : Nat.Primes) {ι : Type*} [Fintype ι]
    (a : ι → NU.LocalTheory.ContinuousCharacter G (p : ℕ))
    (ha : LinearIndependent (ZMod (p : ℕ)) a) :
    Function.Surjective (characterFamilyMonoidHom p a) := by
  intro y
  obtain ⟨x, hx⟩ := characterFamilyEvaluation_surjective p a ha y.toAdd
  obtain ⟨g, hg⟩ := elementaryClass_surjective (G := G) (p : ℕ) x
  refine ⟨g, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  change a i (Additive.ofMul g) = y.toAdd i
  rw [← NU.LocalTheory.evaluation_elementaryClass]
  exact (congrArg (fun z =>
    NU.LocalTheory.evaluation (p : ℕ) z (a i)) hg).trans
      (congrFun hx i)

/-- Finite independent families of absolute Galois characters are bounded
by the local multiplicative Kummer rank.  Only the normalized finite Artin
isomorphism at the finite field cut out by the family is used; no inverse
limit Artin map or completion theorem enters. -/
private theorem finiteCharacterFamily_card_le_kummerFinrank
    (F : Type*) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : Nat.Primes)
    [Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient F (p : ℕ))]
    {ι : Type*} [Fintype ι]
    (a : ι → NU.LocalTheory.ContinuousCharacter
      (Field.absoluteGaloisGroup F) (p : ℕ))
    (ha : LinearIndependent (ZMod (p : ℕ)) a) :
    Fintype.card ι ≤ Module.finrank (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient F (p : ℕ)) := by
  classical
  let G := Field.absoluteGaloisGroup F
  let R := ZMod (p : ℕ)
  letI : CompactSpace G :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  letI : TotallyDisconnectedSpace G :=
    NU.LocalTheory.absoluteGaloisGroup_totallyDisconnectedSpace
  let phi : G →* Multiplicative (ι → R) :=
    characterFamilyMonoidHom p a
  have hphi : Function.Surjective phi :=
    characterFamilyMonoidHom_surjective p a ha
  have hphiContinuous : Continuous phi := by
    change Continuous (fun g : G => fun i => a i (Additive.ofMul g))
    exact continuous_pi fun i => (a i).continuous
  have hopen : IsOpen (phi.ker : Set G) := by
    change IsOpen {g : G | phi g = 1}
    exact (isOpen_discrete ({1} : Set (Multiplicative (ι → R)))).preimage
      hphiContinuous
  let O : OpenSubgroup G := ⟨phi.ker, hopen⟩
  let H : ClosedSubgroup G := ⟨phi.ker, O.isClosed⟩
  let E : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.fixedField H.1
  have hfix : E.fixingSubgroup = H.1 := by
    have h :=
      (InfiniteGalois.IntermediateFieldEquivClosedSubgroup
        (k := F) (K := AlgebraicClosure F)).right_inv H
    exact congrArg ClosedSubgroup.toSubgroup h
  letI : phi.ker.Normal := MonoidHom.normal_ker phi
  have hHnormal : (H : Subgroup G).Normal := by
    dsimp [H]
    exact MonoidHom.normal_ker phi
  haveI hHnormalI : (H : Subgroup G).Normal := hHnormal
  letI hHquotientGroup : Group
      (Field.absoluteGaloisGroup F ⧸
        (H : Subgroup (Field.absoluteGaloisGroup F))) :=
    @QuotientGroup.Quotient.group (Field.absoluteGaloisGroup F)
      inferInstance (H : Subgroup (Field.absoluteGaloisGroup F)) hHnormal
  letI : FiniteDimensional F E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      rw [hfix]
      exact hopen)
  letI : IsGalois F E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by
      rw [hfix]
      change phi.ker.Normal
      exact MonoidHom.normal_ker phi)
  let L : FiniteGaloisIntermediateField F (AlgebraicClosure F) :=
    FiniteGaloisIntermediateField.mk E
  let quotientEquiv : G ⧸ (H : Subgroup G) ≃*
      Multiplicative (ι → R) := by
    change G ⧸ phi.ker ≃* Multiplicative (ι → R)
    exact QuotientGroup.quotientKerEquivOfSurjective phi hphi
  let normalEquiv : (G ⧸ (H : Subgroup G)) ≃* (E ≃ₐ[F] E) :=
    @InfiniteGalois.normalAutEquivQuotient
      F (AlgebraicClosure F) inferInstance inferInstance inferInstance
      inferInstance H hHnormal
  let galoisEquiv : (E ≃ₐ[F] E) ≃* Multiplicative (ι → R) :=
    normalEquiv.symm.trans quotientEquiv
  letI : CommGroup (E ≃ₐ[F] E) :=
    { (inferInstance : Group (E ≃ₐ[F] E)) with
      mul_comm := fun x y => galoisEquiv.injective (by
        rw [map_mul, map_mul, mul_comm]) }
  let artin : (Units F ⧸ NU.LCFT.normSubgroup F E) ≃* (E ≃ₐ[F] E) :=
    (NU.LCFT.finiteArtin F (AlgebraicClosure F) L).trans
      Abelianization.equivOfComm.symm
  have htargetPow (z : Multiplicative (ι → R)) :
      z ^ (p : ℕ) = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    change (p : ℕ) • z.toAdd i = 0
    rw [← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero, zero_smul]
  have hgaloisPow (z : E ≃ₐ[F] E) : z ^ (p : ℕ) = 1 := by
    apply galoisEquiv.injective
    rw [map_pow, map_one]
    exact htargetPow _
  let q : Additive (Units F) →+ Additive
      (Units F ⧸ NU.LCFT.normSubgroup F E) :=
    (QuotientGroup.mk' (NU.LCFT.normSubgroup F E)).toAdditive
  have hq (x : Additive (Units F)) : (p : ℕ) • q x = 0 := by
    apply Additive.toMul.injective
    change (QuotientGroup.mk (Additive.toMul x) :
      Units F ⧸ NU.LCFT.normSubgroup F E) ^ (p : ℕ) = 1
    apply artin.injective
    rw [map_pow, map_one]
    exact hgaloisPow _
  let fq : NU.LocalTheory.KummerQuotient F (p : ℕ) →+
      Additive (Units F ⧸ NU.LCFT.normSubgroup F E) :=
    (ModN.liftEquiv
      (G := Additive (Units F))
      (M := Additive (Units F ⧸ NU.LCFT.normSubgroup F E))
      (n := (p : ℕ))).symm ⟨q, hq⟩
  have hfq : Function.Surjective fq := by
    intro z
    let z' : Units F ⧸ NU.LCFT.normSubgroup F E := Additive.toMul z
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective z'
    refine ⟨NU.LocalTheory.kummerQuotientClass (p : ℕ) u, ?_⟩
    apply Additive.toMul.injective
    change (QuotientGroup.mk u : Units F ⧸ NU.LCFT.normSubgroup F E) = z'
    exact hu
  let bK := Module.Free.chooseBasis R
    (NU.LocalTheory.KummerQuotient F (p : ℕ))
  letI : Finite (Module.Free.ChooseBasisIndex R
      (NU.LocalTheory.KummerQuotient F (p : ℕ))) :=
    Module.Finite.finite_basis bK
  letI : Finite (NU.LocalTheory.KummerQuotient F (p : ℕ)) :=
    Finite.of_injective bK.repr bK.repr.injective
  letI : Finite (Additive
      (Units F ⧸ NU.LCFT.normSubgroup F E)) :=
    Finite.of_surjective fq hfq
  have hcardQuotient : Nat.card
      (Units F ⧸ NU.LCFT.normSubgroup F E) =
      (p : ℕ) ^ Fintype.card ι := by
    calc
      Nat.card (Units F ⧸ NU.LCFT.normSubgroup F E) =
          Nat.card (E ≃ₐ[F] E) := Nat.card_congr artin.toEquiv
      _ = Nat.card (Multiplicative (ι → R)) :=
        Nat.card_congr galoisEquiv.toEquiv
      _ = (p : ℕ) ^ Fintype.card ι := by
        rw [Nat.card_eq_fintype_card]
        simp [R]
  have hcardKummer : Nat.card
      (NU.LocalTheory.KummerQuotient F (p : ℕ)) =
      (p : ℕ) ^ Module.finrank R
        (NU.LocalTheory.KummerQuotient F (p : ℕ)) := by
    simpa [R] using
      (Module.natCard_eq_pow_finrank
        (K := R)
        (V := NU.LocalTheory.KummerQuotient F (p : ℕ)))
  have hcard : (p : ℕ) ^ Fintype.card ι ≤
      (p : ℕ) ^ Module.finrank R
        (NU.LocalTheory.KummerQuotient F (p : ℕ)) := by
    rw [← hcardQuotient, ← hcardKummer]
    exact Nat.card_le_card_of_surjective fq hfq
  exact (Nat.pow_le_pow_iff_right p.2.one_lt).mp hcard

/-- The finite-family bound forces the full space of absolute Galois
characters to be finite-dimensional. -/
private theorem absoluteCharacter_moduleFinite
    (F : Type*) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : Nat.Primes)
    [Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient F (p : ℕ))] :
    Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (p : ℕ)) := by
  classical
  let R := ZMod (p : ℕ)
  let C := NU.LocalTheory.ContinuousCharacter
    (Field.absoluteGaloisGroup F) (p : ℕ)
  let b := Module.Free.chooseBasis R C
  let I := Module.Free.ChooseBasisIndex R C
  have hIfinite : Finite I := by
    by_contra hfinite
    letI : Infinite I := not_finite_iff_infinite.mp hfinite
    obtain ⟨s : Finset I, hs⟩ := Infinite.exists_subset_card_eq I
      (Module.finrank R (NU.LocalTheory.KummerQuotient F (p : ℕ)) + 1)
    let family : s → C := fun i => b i.1
    have hfamily : LinearIndependent R family :=
      b.linearIndependent.comp (fun i : s => i.1) Subtype.val_injective
    have hle := finiteCharacterFamily_card_le_kummerFinrank
      F p family hfamily
    rw [Fintype.card_coe, hs] at hle
    have : Module.finrank R
        (NU.LocalTheory.KummerQuotient F (p : ℕ)) + 1 ≤
      Module.finrank R
        (NU.LocalTheory.KummerQuotient F (p : ℕ)) := by
      simpa [R] using hle
    omega
  letI : Finite I := hIfinite
  exact Module.Finite.of_basis b

private theorem absoluteCharacter_finrank_le_kummerFinrank
    (F : Type*) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : Nat.Primes)
    [Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.KummerQuotient F (p : ℕ))] :
    Module.finrank (ZMod (p : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup F) (p : ℕ)) ≤
      Module.finrank (ZMod (p : ℕ))
        (NU.LocalTheory.KummerQuotient F (p : ℕ)) := by
  letI : Module.Finite (ZMod (p : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (p : ℕ)) :=
    absoluteCharacter_moduleFinite F p
  let b := Module.Free.chooseBasis (ZMod (p : ℕ))
    (NU.LocalTheory.ContinuousCharacter
      (Field.absoluteGaloisGroup F) (p : ℕ))
  letI : Fintype (Module.Free.ChooseBasisIndex (ZMod (p : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (p : ℕ))) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis b]
  exact finiteCharacterFamily_card_le_kummerFinrank
    F p b b.linearIndependent

set_option maxHeartbeats 800000

/-- Exact local character rank from compatible finite levels.  A single
rectangular Lubin--Tate/unramified level captures the finite-dimensional
space of multiplicative characters, while the preceding finite-family
argument supplies the reverse bound. -/
private theorem completionCharacter_finrank_via_finiteLevels
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup (v.adicCompletion K)) (p : ℕ)) =
      1 + finitePlaceLocalDegree v +
        primitiveRootCorrection (v.adicCompletion K) p := by
  classical
  let F := v.adicCompletion K
  let R := ZMod (p : ℕ)
  let QK := NU.LocalTheory.KummerQuotient F (p : ℕ)
  let CG := NU.LocalTheory.ContinuousCharacter
    (Field.absoluteGaloisGroup F) (p : ℕ)
  let CU := NU.LocalTheory.ContinuousCharacter (Units F) (p : ℕ)
  letI : CharZero F := charZero_of_injective_algebraMap
    (algebraMap K F).injective
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  letI : Module.Finite R QK :=
    localUnitDecomposition_kummerQuotient_moduleFinite v p hp units
  letI : Module.Finite R CG := absoluteCharacter_moduleFinite F p
  have hupper : Module.finrank R CG ≤ Module.finrank R QK :=
    absoluteCharacter_finrank_le_kummerFinrank F p
  let unitEquiv := localUnitCharacterDualLinearEquiv v p hp units
  letI : Module.Finite R (Module.Dual R QK) := by infer_instance
  letI : Module.Finite R CU := Module.Finite.equiv unitEquiv.symm
  let b := Module.Free.chooseBasis R CU
  let J := Module.Free.ChooseBasisIndex R CU
  letI : Fintype J := Fintype.ofFinite J
  let unitEval : Units F →* Multiplicative (J → R) :=
    characterFamilyMonoidHom p b
  have hunitEvalContinuous : Continuous unitEval := by
    change Continuous (fun u : Units F => fun j => b j (Additive.ofMul u))
    exact continuous_pi fun j => (b j).continuous
  have hopen : IsOpen (unitEval.ker : Set (Units F)) := by
    change IsOpen {u : Units F | unitEval u = 1}
    exact (isOpen_discrete ({1} : Set (Multiplicative (J → R)))).preimage
      hunitEvalContinuous
  let OU : OpenSubgroup (Units F) := ⟨unitEval.ker, hopen⟩
  letI : Finite unitEval.range := Finite.of_injective
    (fun x : unitEval.range => (x : Multiplicative (J → R)))
    Subtype.val_injective
  letI : Finite (Units F ⧸ unitEval.ker) := Finite.of_equiv
    unitEval.range (QuotientGroup.quotientKerEquivRange unitEval).symm.toEquiv
  let H : NU.LCFT.OpenFiniteIndexSubgroup (Units F) :=
    ⟨OU, Subgroup.finiteIndex_of_finite_quotient⟩
  let pi := NU.LCFT.defaultUniformizer F
  letI : TopologicalSpace (AlgebraicClosure F) := ⊥
  obtain ⟨a, c, ha, hc, hrect⟩ :=
    NU.LCFT.rectangularSubgroup_cofinal F pi H
  let L := NU.LCFT.rectangularClassField F (AlgebraicClosure F) pi a c ha hc
  let N : Subgroup (Units F) := NU.LCFT.normSubgroup F L.field
  have hNH : N ≤ unitEval.ker := by
    rw [show N = NU.LCFT.rectangularSubgroup F pi a c by
      exact NU.LCFT.norm_rectangularClassField
        F (AlgebraicClosure F) pi a c ha hc]
    exact hrect
  have hbzero (u : Units F) (hu : u ∈ unitEval.ker) (j : J) :
      b j (Additive.ofMul u) = 0 := by
    have hz := congrArg
      (fun z : Multiplicative (J → R) => z.toAdd j) hu
    simpa [unitEval, characterFamilyMonoidHom] using hz
  have hkill (chi : CU) (u : Units F) (hu : u ∈ N) :
      chi (Additive.ofMul u) = 0 := by
    let ev : CU →+ R :=
      { toFun := fun z => z (Additive.ofMul u)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hsum := congrArg ev (b.sum_repr chi)
    rw [map_sum] at hsum
    have hterm (j : J) : ev ((b.repr chi j) • b j) = 0 := by
      have hs := ZMod.map_smul ev (b.repr chi j) (b j)
      simpa [ev, hbzero u (hNH hu) j] using hs
    rw [Finset.sum_eq_zero fun j _ => hterm j] at hsum
    exact hsum.symm
  let D := NU.LCFT.localFieldExtensionData F L.field
  letI : ValuativeRel L.field := D.valuativeRel
  letI : TopologicalSpace L.field := D.topology
  letI : IsNonarchimedeanLocalField L.field := D.localField
  letI : ValuativeExtension F L.field := D.valuativeExtension
  letI : ContinuousSMul F L.field := D.continuousSMul
  have hNopen : IsOpen (N : Set (Units F)) := by
    exact NU.LCFT.normSubgroup_isOpen F L.field
  letI : DiscreteTopology (Units F ⧸ N) :=
    QuotientGroup.discreteTopology hNopen
  let qhom : Units F →ₜ* Units F ⧸ N :=
    ContinuousMonoidHom.mk (QuotientGroup.mk' N) continuous_quot_mk
  let pull : NU.LocalTheory.ContinuousCharacter (Units F ⧸ N) (p : ℕ)
      →ₗ[R] CU := continuousCharacterPullLinearMap (p : ℕ) qhom
  have hpull : Function.Bijective pull := by
    constructor
    · intro x y hxy
      ext z
      let z' : Units F ⧸ N := Additive.toMul z
      obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective z'
      have hv := DFunLike.congr_fun hxy (Additive.ofMul u)
      change x (Additive.ofMul (QuotientGroup.mk u)) =
        y (Additive.ofMul (QuotientGroup.mk u)) at hv
      simpa [z', hu] using hv
    · intro chi
      let am : Units F →* Multiplicative R :=
        chi.toAddMonoidHom.toMultiplicativeRight
      let qm : Units F ⧸ N →* Multiplicative R :=
        QuotientGroup.lift N am (by
          intro u hu
          apply Multiplicative.toAdd.injective
          change chi (Additive.ofMul u) = 0
          exact hkill chi u hu)
      let raw : Additive (Units F ⧸ N) →+ R :=
        MonoidHom.toAdditiveLeft qm
      let chiQ : NU.LocalTheory.ContinuousCharacter
          (Units F ⧸ N) (p : ℕ) := ⟨raw, continuous_of_discreteTopology⟩
      refine ⟨chiQ, ?_⟩
      ext x
      rfl
  let descend : CU ≃ₗ[R]
      NU.LocalTheory.ContinuousCharacter (Units F ⧸ N) (p : ℕ) :=
    (LinearEquiv.ofBijective pull hpull).symm
  letI : CommGroup (L.field ≃ₐ[F] L.field) :=
    { (inferInstance : Group (L.field ≃ₐ[F] L.field)) with
      mul_comm := L.commutative }
  let artin : (Units F ⧸ N) ≃* (L.field ≃ₐ[F] L.field) :=
    (NU.LCFT.finiteArtin F (AlgebraicClosure F) L.field).trans
      Abelianization.equivOfComm.symm
  let restriction : Field.absoluteGaloisGroup F →*
      (L.field ≃ₐ[F] L.field) := AlgEquiv.restrictNormalHom L.field
  have hrestriction : Function.Surjective restriction :=
    AlgEquiv.restrictNormalHom_surjective
      (F := F) (K₁ := L.field) (AlgebraicClosure F)
  have hrestrictionContinuous : Continuous restriction :=
    InfiniteGalois.restrictNormalHom_continuous
      L.field.toIntermediateField
  have hartinContinuous : Continuous
      (fun sigma : L.field ≃ₐ[F] L.field => artin.symm sigma) :=
    continuous_of_discreteTopology
  let artinRestriction : Field.absoluteGaloisGroup F →ₜ* Units F ⧸ N :=
    ContinuousMonoidHom.mk
      (artin.symm.toMonoidHom.comp restriction)
      (hartinContinuous.comp hrestrictionContinuous)
  let lift : CU →ₗ[R] CG :=
    (continuousCharacterPullLinearMap (p : ℕ) artinRestriction).comp
      descend.toLinearMap
  have hartinRestriction : Function.Surjective artinRestriction :=
    artin.symm.surjective.comp hrestriction
  have hpullArtin : Function.Injective
      (continuousCharacterPullLinearMap (p : ℕ) artinRestriction) := by
    intro x y hxy
    ext z
    obtain ⟨g, hg⟩ := hartinRestriction (Additive.toMul z)
    have hv := DFunLike.congr_fun hxy (Additive.ofMul g)
    change x (Additive.ofMul (artinRestriction g)) =
      y (Additive.ofMul (artinRestriction g)) at hv
    simpa [hg] using hv
  have hlift : Function.Injective lift := by
    exact hpullArtin.comp descend.injective
  have hlower : Module.finrank R QK ≤ Module.finrank R CG := by
    calc
      Module.finrank R QK = Module.finrank R (Module.Dual R QK) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank R CU := unitEquiv.finrank_eq.symm
      _ ≤ Module.finrank R CG :=
        LinearMap.finrank_le_finrank_of_injective hlift
  have hrankK : Module.finrank R QK =
      1 + finitePlaceLocalDegree v + primitiveRootCorrection F p :=
    localUnitDecomposition_kummerQuotient_finrank v p hp units
  exact le_antisymm (by simpa [hrankK] using hupper)
    (by simpa [hrankK] using hlower)

/-- Public data exhibiting continuous characters over `F` as the
cyclotomic eigenspace in the Kummer quotient after adjoining `μ_p`.
`kummerLift_spec` pins the inclusion of that eigenspace to the existing
`NU.LocalTheory.kummerEquiv`, rather than to an unrelated linear
isomorphism. -/
structure RootAbsentMaschkeDescentData
    (F : Type*) [Field F] [CharZero F]
    (p : Nat.Primes) (rank : ℕ) where
  eigenspace : Submodule (ZMod (p : ℕ))
    (NU.LocalTheory.KummerQuotient
      (localCyclotomicExtension F p) (p : ℕ))
  descentEquiv :
    NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      eigenspace
  kummerLift : eigenspace →ₗ[ZMod (p : ℕ)]
    NU.LocalTheory.ContinuousCharacter
      (Field.absoluteGaloisGroup (localCyclotomicExtension F p)) (p : ℕ)
  kummerLift_spec : ∀ x,
    NU.LocalTheory.kummerEquiv
        (localCyclotomicRootInExtension F p)
        (localCyclotomicRootInExtension_spec F p) x.1 = kummerLift x
  finrank_eigenspace :
    Module.finrank (ZMod (p : ℕ)) eigenspace = rank

/-- **Root-absent inflation--restriction/Maschke bridge (Blueprint
`lem:dim-at`; nu-inv12 blocker report: "the Maschke/normal-basis calculation
after quotienting p-power torsion and adjoining mu_p").**  If `F` does not
contain `μ_p`, restriction to `F(μ_p)` and Maschke descent identify
`ContinuousCharacter G_F p` with the cyclotomic eigenspace of the
`kummerEquiv` quotient, of rank `1 + [F : ℚ_p]`.

For local invariant recovery `F` is the completion at `v`; the supplied deep
unit package is exactly the output of `DeepUnitModule.lean`.  See
`local_invariants_recovery.tex`, `lem:dim-at`, and the nu-inv12 blocker
report. -/
private theorem rootAbsent_inflationRestriction_maschkeRank_residual
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    [CharZero (v.adicCompletion K)]
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v))
    (hroots : ¬ ∃ z : v.adicCompletion K,
      IsPrimitiveRoot z (p : ℕ)) :
    Nonempty
      (RootAbsentMaschkeDescentData (v.adicCompletion K) p
        (1 + finitePlaceLocalDegree v)) := by
  let F := v.adicCompletion K
  let E := localCyclotomicExtension F p
  let κ := NU.LocalTheory.kummerEquiv
    (localCyclotomicRootInExtension F p)
    (localCyclotomicRootInExtension_spec F p)
  let res := continuousCharacterPullLinearMap (p : ℕ)
    (localCyclotomicRestrictionContinuousHom F p)
  have hindex : E.fixingSubgroup.index < (p : ℕ) := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact localCyclotomicExtension_finrank_lt F p
  have hres : Function.Injective res :=
    localCyclotomic_characterPull_injective F p hindex
  let descentMap :
      NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup F) (p : ℕ) →ₗ[ZMod (p : ℕ)]
        NU.LocalTheory.KummerQuotient E (p : ℕ) :=
    κ.symm.toLinearMap.comp res
  have hdescent : Function.Injective descentMap :=
    κ.symm.injective.comp hres
  let descentEquiv := LinearEquiv.ofInjective descentMap hdescent
  have hrank : Module.finrank (ZMod (p : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (p : ℕ)) =
      1 + finitePlaceLocalDegree v := by
    simpa [primitiveRootCorrection, hroots] using
      completionCharacter_finrank_via_finiteLevels v p hp units
  refine ⟨{
    eigenspace := descentMap.range
    descentEquiv := descentEquiv
    kummerLift := κ.toLinearMap.comp descentMap.range.subtype
    kummerLift_spec := ?_
    finrank_eigenspace := ?_ }⟩
  · intro x
    rfl
  · calc
      Module.finrank (ZMod (p : ℕ)) descentMap.range =
          Module.finrank (ZMod (p : ℕ))
            (NU.LocalTheory.ContinuousCharacter
              (Field.absoluteGaloisGroup F) (p : ℕ)) :=
        descentEquiv.finrank_eq.symm
      _ = 1 + finitePlaceLocalDegree v := hrank

theorem rootAbsent_inflationRestriction_maschkeRank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    [CharZero (v.adicCompletion K)]
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v))
    (hroots : ¬ ∃ z : v.adicCompletion K,
      IsPrimitiveRoot z (p : ℕ)) :
    Nonempty
      (RootAbsentMaschkeDescentData (v.adicCompletion K) p
        (1 + finitePlaceLocalDegree v)) := by
  exact rootAbsent_inflationRestriction_maschkeRank_residual v p hp units hroots

/-- **Completion character-rank bridge (Blueprint `lem:dim-at`; nu-inv12
blocker report: "the root-absent inflation-restriction/Maschke rank
bridge").**  Combining the root-absent eigenspace theorem above with the
root-present Kummer equivalence gives the uniform correction-term formula
consumed by `LocalInvariants.completePIDClassification`.

The proof must quotient `μ_{p^∞}` before reducing modulo `p`, then use
inflation--restriction, Maschke, normal basis, and integral character
idempotents, exactly as prescribed by `local_invariants_recovery.tex` and the
nu-inv12 blocker report. -/
private theorem completionCharacterRank_maschkeDescent_residual
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup (v.adicCompletion K)) (p : ℕ)) =
      1 + finitePlaceLocalDegree v +
        primitiveRootCorrection (v.adicCompletion K) p := by
  let F := v.adicCompletion K
  letI : CharZero F := charZero_of_injective_algebraMap
    (algebraMap K F).injective
  by_cases hroots : ∃ z : F, IsPrimitiveRoot z (p : ℕ)
  · obtain ⟨z, hz⟩ := hroots
    calc
      Module.finrank (ZMod (p : ℕ))
          (NU.LocalTheory.ContinuousCharacter
            (Field.absoluteGaloisGroup F) (p : ℕ)) =
          Module.finrank (ZMod (p : ℕ))
            (NU.LocalTheory.KummerQuotient F (p : ℕ)) :=
        (NU.LocalTheory.kummerEquiv z hz).finrank_eq.symm
      _ = 1 + finitePlaceLocalDegree v +
          primitiveRootCorrection F p :=
        localUnitDecomposition_kummerQuotient_finrank v p hp units
  · obtain ⟨D⟩ :=
      rootAbsent_inflationRestriction_maschkeRank v p hp units hroots
    calc
      Module.finrank (ZMod (p : ℕ))
          (NU.LocalTheory.ContinuousCharacter
            (Field.absoluteGaloisGroup F) (p : ℕ)) =
          Module.finrank (ZMod (p : ℕ)) D.eigenspace :=
        D.descentEquiv.finrank_eq
      _ = 1 + finitePlaceLocalDegree v := D.finrank_eigenspace
      _ = 1 + finitePlaceLocalDegree v +
          primitiveRootCorrection F p := by
        simp [primitiveRootCorrection, hroots]

theorem completionCharacterRank_maschkeDescent
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (p : Nat.Primes)
    (hp : (p : ℕ) = NU.LocalTheory.residueCharacteristic v)
    (units : LocalUnitDecompositionData v p (finitePlaceLocalDegree v)) :
    Module.finrank (ZMod (p : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup (v.adicCompletion K)) (p : ℕ)) =
      1 + finitePlaceLocalDegree v +
        primitiveRootCorrection (v.adicCompletion K) p := by
  exact completionCharacterRank_maschkeDescent_residual v p hp units

end

end NU.NeukirchUchida.Bridges
