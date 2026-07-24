import Submission.NU.LocalTheory.Packets.Basic

/-!
# Packet stabilizers and decomposition groups

Finite decomposition groups are defined here as stabilizers of prime-ideal
places under the arithmetic Galois action, as required by Blueprint
§10.1(2).  Packet equivariance and separation then identify packet
stabilizers with those decomposition groups.  The final theorem is tower
surjectivity.
-/

open IsDedekindDomain
open scoped NumberField Pointwise

namespace NU.LocalTheory

noncomputable section

/-- The arithmetic action of `Gal(M/K)` on nonzero prime ideals of `𝓞_M`.
Its `smul` field is literally the pointwise action on the ideal; the two
remaining fields are the action equations. -/
@[reducible] noncomputable def finitePlaceAction (K M : Type*) [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M] :
    MulAction (M ≃ₐ[K] M) (FinitePlace M) where
  smul σ w :=
    { asIdeal := σ • w.asIdeal
      isPrime := w.isPrime.smul σ
      ne_bot := by
        intro hbot
        apply w.ne_bot
        have h := congrArg (fun I : Ideal (𝓞 M) => σ⁻¹ • I) hbot
        simpa using h }
  one_smul w := by
    apply HeightOneSpectrum.ext
    exact one_smul (M ≃ₐ[K] M) w.asIdeal
  mul_smul σ τ w := by
    apply HeightOneSpectrum.ext
    exact mul_smul σ τ w.asIdeal

/-- Galois conjugation of a prime-ideal place. -/
noncomputable def conjugateFinitePlace (K : Type*) {M : Type*}
    [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (w : FinitePlace M) : FinitePlace M := by
  letI := finitePlaceAction K M
  exact σ • w

@[simp]
theorem conjugateFinitePlace_asIdeal (K : Type*) {M : Type*}
    [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    (conjugateFinitePlace K σ w).asIdeal = σ • w.asIdeal :=
  rfl

/-- The finite decomposition group, represented definitionally as the
stabilizer of a prime above its base prime. -/
noncomputable def decompositionGroup (K : Type*) {M : Type*}
    [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
    (w : FinitePlace M) : Subgroup (M ≃ₐ[K] M) := by
  letI := finitePlaceAction K M
  exact MulAction.stabilizer (M ≃ₐ[K] M) w

/-- The collection `Dec(M/K)` of finite-level decomposition groups. -/
def decompositionCollection (K M : Type*) [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M] :
    Set (Subgroup (M ≃ₐ[K] M)) :=
  Set.range (decompositionGroup K)

private def automorphismCharacterEquiv
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) (σ : M ≃ₐ[K] M) :
    MulCharacter M ℓ ≃ₗ[ZMod ℓ] MulCharacter M ℓ where
  toFun p := pullbackCharacter ℓ σ.symm.toRingEquiv.toRingHom p
  invFun p := pullbackCharacter ℓ σ.toRingEquiv.toRingHom p
  left_inv p := by
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      change p (Additive.ofMul (Units.map σ.symm.toRingEquiv.toMonoidHom
        (Units.map σ.toRingEquiv.toMonoidHom u))) = p (Additive.ofMul u)
      congr 2
      apply Units.ext
      simp
  right_inv p := by
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      change p (Additive.ofMul (Units.map σ.toRingEquiv.toMonoidHom
        (Units.map σ.symm.toRingEquiv.toMonoidHom u))) = p (Additive.ofMul u)
      congr 2
      apply Units.ext
      simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem automorphismCharacterEquiv_apply
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) (σ : M ≃ₐ[K] M) (p : MulCharacter M ℓ) (u : Mˣ) :
    automorphismCharacterEquiv K M ℓ σ p (Additive.ofMul u) =
      p (Additive.ofMul
        (Units.map σ.symm.toRingEquiv.toMonoidHom u)) :=
  rfl

private def automorphismCharacterAction
    (K M : Type*) [Field K] [Field M] [Algebra K M] (ℓ : ℕ) :
    (M ≃ₐ[K] M) →* (MulCharacter M ℓ ≃ₗ[ZMod ℓ] MulCharacter M ℓ) where
  toFun := automorphismCharacterEquiv K M ℓ
  map_one' := by
    apply LinearEquiv.ext
    intro p
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      change p (Additive.ofMul
        (Units.map (1 : M ≃ₐ[K] M).symm.toRingEquiv.toMonoidHom u)) =
          p (Additive.ofMul u)
      congr 2
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro p
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      change p (Additive.ofMul
          (Units.map (σ * τ).symm.toRingEquiv.toMonoidHom u)) =
        p (Additive.ofMul (Units.map τ.symm.toRingEquiv.toMonoidHom
          (Units.map σ.symm.toRingEquiv.toMonoidHom u)))
      congr 2

private def normalizedPacketActionOfRoot
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    (M ≃ₐ[K] M) →*
      (ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
        ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) where
  toFun σ := ((kummerDualEquiv ζ hζ).trans
    (automorphismCharacterAction K M ℓ σ)).trans
      (kummerDualEquiv ζ hζ).symm
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro x
    simp

/-- The mod-`ℓ` cyclotomic character on the finite automorphism group,
using a primitive `ℓ`-th root contained in the field. -/
noncomputable def packetCyclotomicCharacter
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    (M ≃ₐ[K] M) →* (ZMod ℓ)ˣ :=
  (modularCyclotomicCharacter M hζ.card_rootsOfUnity).comp
    (MulSemiringAction.toRingAut (M ≃ₐ[K] M) M)

/-- Defining equation for the cyclotomic scalar on a primitive root. -/
@[simp]
theorem packetCyclotomicCharacter_spec
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (σ : M ≃ₐ[K] M) :
    σ ζ = ζ ^ ((packetCyclotomicCharacter K M ℓ ζ hζ σ :
      (ZMod ℓ)ˣ) : ZMod ℓ).val := by
  let ζu : Mˣ := Units.mk0 ζ (hζ.ne_zero (Fact.out : ℓ.Prime).ne_zero)
  have hζu : ζu ∈ rootsOfUnity ℓ M := by
    rw [mem_rootsOfUnity']
    exact hζ.pow_eq_one
  simpa [packetCyclotomicCharacter, ζu] using
    (modularCyclotomicCharacter.spec M hζ.card_rootsOfUnity
      σ.toRingEquiv hζu)

private def scalarLinearAction (k V : Type*) [CommSemiring k]
    [AddCommMonoid V] [Module k V] : kˣ →* (V ≃ₗ[k] V) where
  toFun := LinearEquiv.smulOfUnit
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change (1 : kˣ) • x = x
    exact one_smul _ _
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    change (a * b) • x = a • b • x
    exact mul_smul a b x

private noncomputable def cyclotomicScalarActionOfRoot
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    (M ≃ₐ[K] M) →*
      (ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
        ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) :=
  (scalarLinearAction (ZMod ℓ)
    (ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ)).comp
      (packetCyclotomicCharacter K M ℓ ζ hζ)

private noncomputable def packetActionOfRoot
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    (M ≃ₐ[K] M) →*
      (ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
        ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) where
  toFun σ := cyclotomicScalarActionOfRoot K M ℓ ζ hζ σ *
    normalizedPacketActionOfRoot K M ℓ ζ hζ σ
  map_one' := by
    rw [map_one, map_one, mul_one]
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro x
    change ((packetCyclotomicCharacter K M ℓ ζ hζ (σ * τ) :
        (ZMod ℓ)ˣ) : ZMod ℓ) •
          normalizedPacketActionOfRoot K M ℓ ζ hζ (σ * τ) x = _
    rw [map_mul, map_mul, LinearEquiv.mul_apply]
    change (((packetCyclotomicCharacter K M ℓ ζ hζ σ : (ZMod ℓ)ˣ) :
        ZMod ℓ) *
      ((packetCyclotomicCharacter K M ℓ ζ hζ τ : (ZMod ℓ)ˣ) : ZMod ℓ)) •
        (normalizedPacketActionOfRoot K M ℓ ζ hζ σ)
          (normalizedPacketActionOfRoot K M ℓ ζ hζ τ x) = _
    rw [mul_smul]
    change _ = ((packetCyclotomicCharacter K M ℓ ζ hζ σ :
      (ZMod ℓ)ˣ) : ZMod ℓ) •
        (normalizedPacketActionOfRoot K M ℓ ζ hζ σ)
          (((packetCyclotomicCharacter K M ℓ ζ hζ τ :
            (ZMod ℓ)ˣ) : ZMod ℓ) •
              normalizedPacketActionOfRoot K M ℓ ζ hζ τ x)
    rw [map_smul]

/-- The linear packet action. Whenever the prime Kummer coordinates used by
packets exist, it is the contragredient field-automorphism action transported
through Kummer duality, including the cyclotomic scalar. Outside that packet
range it is the identity action. -/
noncomputable def packetAction (K M : Type*) [Field K] [Field M]
    [NumberField K] [NumberField M] [Algebra K M]
    (ℓ : ℕ) :
    (M ≃ₐ[K] M) →*
      (ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ ≃ₗ[ZMod ℓ]
        ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) := by
  classical
  by_cases h : ℓ.Prime ∧ ∃ ζ : M, IsPrimitiveRoot ζ ℓ
  · letI : Fact ℓ.Prime := ⟨h.1⟩
    exact packetActionOfRoot K M ℓ h.2.choose h.2.choose_spec
  · exact 1

/-- In Kummer coordinates, the packet action is cyclotomic-scalar times
pullback by the inverse field automorphism. The equation is independent of
the primitive root used internally to define `packetAction`. -/
@[simp]
theorem kummerDualEquiv_packetAction_apply
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) (σ : M ≃ₐ[K] M)
    (x : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) (u : Mˣ) :
    kummerDualEquiv ζ hζ (packetAction K M ℓ σ x) (Additive.ofMul u) =
      ((packetCyclotomicCharacter K M ℓ ζ hζ σ : (ZMod ℓ)ˣ) : ZMod ℓ) *
        kummerDualEquiv ζ hζ x
          (Additive.ofMul (Units.map σ.symm.toRingEquiv.toMonoidHom u)) := by
  classical
  unfold packetAction
  split
  · next hex =>
    let ξ : M := hex.2.choose
    have hξ : IsPrimitiveRoot ξ ℓ := hex.2.choose_spec
    obtain ⟨c, hc, hchars⟩ :=
      kummerCharacter_change_primitiveRoot ζ ξ hζ hξ
    have heq (y : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) :
        kummerDualEquiv ξ hξ y = c • kummerDualEquiv ζ hζ y := by
      apply AddMonoidHom.ext
      intro z
      cases z with
      | ofMul v =>
        rw [kummerDualEquiv_apply, hchars v]
        change evaluationLinear ℓ y (c • kummerCharacter ζ hζ v) =
          c • kummerDualEquiv ζ hζ y (Additive.ofMul v)
        rw [kummerDualEquiv_apply]
        exact map_smul (evaluationLinear ℓ y) c _
    have hd : packetCyclotomicCharacter K M ℓ ξ hξ σ =
        packetCyclotomicCharacter K M ℓ ζ hζ σ := by
      rfl
    change kummerDualEquiv ζ hζ
        (((packetActionOfRoot K M ℓ ξ hξ) σ) x) (Additive.ofMul u) = _
    apply mul_left_cancel₀ hc
    calc
      c * kummerDualEquiv ζ hζ (((packetActionOfRoot K M ℓ ξ hξ) σ) x)
            (Additive.ofMul u) =
          kummerDualEquiv ξ hξ (((packetActionOfRoot K M ℓ ξ hξ) σ) x)
            (Additive.ofMul u) := by
              rw [heq]
              rfl
      _ = ((packetCyclotomicCharacter K M ℓ ξ hξ σ : (ZMod ℓ)ˣ) :
              ZMod ℓ) * kummerDualEquiv ξ hξ x
            (Additive.ofMul (Units.map σ.symm.toRingEquiv.toMonoidHom u)) := by
        change kummerDualEquiv ξ hξ
            (((cyclotomicScalarActionOfRoot K M ℓ ξ hξ σ) *
              (normalizedPacketActionOfRoot K M ℓ ξ hξ σ)) x)
              (Additive.ofMul u) = _
        rw [LinearEquiv.mul_apply]
        change kummerDualEquiv ξ hξ
            (((packetCyclotomicCharacter K M ℓ ξ hξ σ : (ZMod ℓ)ˣ) :
              ZMod ℓ) • normalizedPacketActionOfRoot K M ℓ ξ hξ σ x)
              (Additive.ofMul u) = _
        rw [map_smul]
        change _ * kummerDualEquiv ξ hξ
            (((kummerDualEquiv ξ hξ).trans
              (automorphismCharacterEquiv K M ℓ σ)).trans
                (kummerDualEquiv ξ hξ).symm x) (Additive.ofMul u) = _
        rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.trans_apply, automorphismCharacterEquiv_apply]
      _ = c * (((packetCyclotomicCharacter K M ℓ ζ hζ σ : (ZMod ℓ)ˣ) :
              ZMod ℓ) * kummerDualEquiv ζ hζ x
            (Additive.ofMul (Units.map σ.symm.toRingEquiv.toMonoidHom u))) := by
        rw [heq, hd]
        change _ * (c * _) = c * (_ * _)
        ac_rfl
  · next h => exact (h ⟨Fact.out, ζ, hζ⟩).elim

/-- The induced action on submodules of the elementary quotient. -/
noncomputable def conjugatePacket (K : Type*) {M : Type*}
    [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
    {ℓ : ℕ} (σ : M ≃ₐ[K] M)
    (P : GroupSubspace (Field.absoluteGaloisGroup M) ℓ) :
    GroupSubspace (Field.absoluteGaloisGroup M) ℓ :=
  P.map (packetAction K M ℓ σ).toLinearMap

/-- Stabilizer of a packet under the conjugation action. -/
noncomputable def packetStabilizer (K : Type*) {M : Type*}
    [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
    {ℓ : ℕ} (P : GroupSubspace (Field.absoluteGaloisGroup M) ℓ) :
    Subgroup (M ≃ₐ[K] M) where
  carrier := {σ | conjugatePacket K σ P = P}
  one_mem' := by
    simp [conjugatePacket]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_setOf_eq] at hσ hτ ⊢
    change P.map (packetAction K M ℓ σ).toLinearMap = P at hσ
    change P.map (packetAction K M ℓ τ).toLinearMap = P at hτ
    calc
      conjugatePacket K (σ * τ) P =
          P.map (((packetAction K M ℓ σ).toLinearMap).comp
            (packetAction K M ℓ τ).toLinearMap) := by
              rw [conjugatePacket, map_mul]
              congr 1
      _ = (P.map (packetAction K M ℓ τ).toLinearMap).map
          (packetAction K M ℓ σ).toLinearMap :=
            Submodule.map_comp _ _ _
      _ = P := by rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ ⊢
    change P.map (packetAction K M ℓ σ).toLinearMap = P at hσ
    calc
      conjugatePacket K σ⁻¹ P =
          P.map (packetAction K M ℓ σ).symm.toLinearMap := by
            rw [conjugatePacket, map_inv]
            congr 1
      _ = (P.map (packetAction K M ℓ σ).toLinearMap).map
          (packetAction K M ℓ σ).symm.toLinearMap := by rw [hσ]
      _ = P := by
        rw [← Submodule.map_comp]
        convert Submodule.map_id P using 1
        ext x
        simp

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

private noncomputable def primeValuationSubringEquiv
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    primeValuationSubring w ≃+*
      primeValuationSubring (conjugateFinitePlace K σ w) where
  toFun x := ⟨σ (x : M),
    (mem_primeValuationSubring_automorphism K M σ w x).1 x.prop⟩
  invFun x := ⟨σ.symm (x : M), by
    apply (mem_primeValuationSubring_automorphism K M σ w
      (σ.symm (x : M))).2
    simpa using x.prop⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

private theorem principalUnitGroup_automorphism_forward
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (σ : M ≃ₐ[K] M) (w : FinitePlace M) (u : Mˣ)
    (hu : u ∈ (primeValuationSubring w).principalUnitGroup) :
    Units.map σ.toRingEquiv.toMonoidHom u ∈
      (primeValuationSubring
        (conjugateFinitePlace K σ w)).principalUnitGroup := by
  let A := primeValuationSubring w
  let B := primeValuationSubring (conjugateFinitePlace K σ w)
  let e : A ≃+* B := primeValuationSubringEquiv K M σ w
  rw [A.mem_principalUnitGroup_iff] at hu
  rw [B.mem_principalUnitGroup_iff]
  let z : A := ⟨(u : M) - 1, by
    rw [← A.valuation_le_one_iff]
    exact hu.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal A :=
    (A.valuation_lt_one_iff z).2 hu
  letI : IsLocalHom e.toRingHom :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  have hez : e z ∈ IsLocalRing.maximalIdeal B :=
    map_nonunit e.toRingHom z hz
  have heval : (e z : M) =
      ((Units.map σ.toRingEquiv.toMonoidHom u : Mˣ) : M) - 1 := by
    simp [e, primeValuationSubringEquiv, z]
  have hlt := (B.valuation_lt_one_iff (e z)).1 hez
  rw [← heval]
  exact hlt

private theorem principalUnitGroup_automorphism
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (σ : M ≃ₐ[K] M) (w : FinitePlace M) (u : Mˣ) :
    u ∈ (primeValuationSubring w).principalUnitGroup ↔
      Units.map σ.toRingEquiv.toMonoidHom u ∈
        (primeValuationSubring
          (conjugateFinitePlace K σ w)).principalUnitGroup := by
  constructor
  · exact principalUnitGroup_automorphism_forward K M σ w u
  · intro hu
    have hplace : conjugateFinitePlace K σ.symm
        (conjugateFinitePlace K σ w) = w := by
      apply HeightOneSpectrum.ext
      rw [conjugateFinitePlace_asIdeal, conjugateFinitePlace_asIdeal]
      exact inv_smul_smul σ w.asIdeal
    have h := principalUnitGroup_automorphism_forward K M σ.symm
      (conjugateFinitePlace K σ w)
      (Units.map σ.toRingEquiv.toMonoidHom u) hu
    rw [hplace] at h
    have hucomp : Units.map σ.symm.toRingEquiv.toMonoidHom
        (Units.map σ.toRingEquiv.toMonoidHom u) = u := by
      apply Units.ext
      simp
    rw [hucomp] at h
    exact h

private theorem automorphismCharacterEquiv_mem_localD_iff
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (ℓ : ℕ) (σ : M ≃ₐ[K] M) (w : FinitePlace M)
    (p : MulCharacter M ℓ) :
    automorphismCharacterEquiv K M ℓ σ p ∈
        localD ℓ (primeValuationSubring (conjugateFinitePlace K σ w)) ↔
      p ∈ localD ℓ (primeValuationSubring w) := by
  constructor
  · intro hp u hu
    have hpu := hp (Units.map σ.toRingEquiv.toMonoidHom u)
      ((principalUnitGroup_automorphism K M σ w u).1 hu)
    change p (Additive.ofMul (Units.map σ.symm.toRingEquiv.toMonoidHom
      (Units.map σ.toRingEquiv.toMonoidHom u))) = 0 at hpu
    have hucomp : Units.map σ.symm.toRingEquiv.toMonoidHom
        (Units.map σ.toRingEquiv.toMonoidHom u) = u := by
      apply Units.ext
      simp
    rw [hucomp] at hpu
    exact hpu
  · intro hp u hu
    let u0 := Units.map σ.symm.toRingEquiv.toMonoidHom u
    have hu0 : u0 ∈ (primeValuationSubring w).principalUnitGroup := by
      apply (principalUnitGroup_automorphism K M σ w u0).2
      have hucomp : Units.map σ.toRingEquiv.toMonoidHom u0 = u := by
        apply Units.ext
        simp [u0]
      rw [hucomp]
      exact hu
    exact hp u0 hu0

private theorem automorphismCharacterAction_map_localD
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (ℓ : ℕ) (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    (localD ℓ (primeValuationSubring w)).map
        (automorphismCharacterAction K M ℓ σ).toLinearMap =
      localD ℓ (primeValuationSubring (conjugateFinitePlace K σ w)) := by
  change (localD ℓ (primeValuationSubring w)).map
      (automorphismCharacterEquiv K M ℓ σ).toLinearMap = _
  ext p
  rw [Submodule.mem_map_equiv]
  have h := (automorphismCharacterEquiv_mem_localD_iff K M ℓ σ w
    ((automorphismCharacterEquiv K M ℓ σ).symm p)).symm
  rw [(automorphismCharacterEquiv K M ℓ σ).apply_symm_apply] at h
  exact h

private theorem map_comap_conjugated
    {k X C : Type*} [Field k] [AddCommGroup X] [AddCommGroup C]
    [Module k X] [Module k C]
    (e : X ≃ₗ[k] C) (T : C ≃ₗ[k] C) (D D' : Submodule k C)
    (hT : D.map T.toLinearMap = D') :
    (D.comap e.toLinearMap).map
        (((e.trans T).trans e.symm).toLinearMap) =
      D'.comap e.toLinearMap := by
  calc
    (D.comap e.toLinearMap).map (((e.trans T).trans e.symm).toLinearMap) =
        ((D.comap e.toLinearMap).map e.toLinearMap).map
          (T.trans e.symm).toLinearMap := by
      rw [← Submodule.map_comp]
      rfl
    _ = D.map (T.trans e.symm).toLinearMap := by
      rw [Submodule.map_comap_eq, e.range, top_inf_eq]
    _ = (D.map T.toLinearMap).map e.symm.toLinearMap := by
      rw [← Submodule.map_comp]
      rfl
    _ = D'.map e.symm.toLinearMap := by rw [hT]
    _ = D'.comap e.toLinearMap :=
      Submodule.map_equiv_eq_comap_symm e.symm D'

private theorem submodule_map_smulOfUnit
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (P : Submodule k V) (a : kˣ) :
    P.map (LinearEquiv.smulOfUnit a).toLinearMap = P := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact P.smul_mem (a : k) hy
  · intro x hx
    refine ⟨((a⁻¹ : kˣ) : k) • x, P.smul_mem ((a⁻¹ : kˣ) : k) hx, ?_⟩
    change (a : k) • (((a⁻¹ : kˣ) : k) • x) = x
    rw [← mul_smul]
    simp

private theorem packet_action_localPlane_core
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    conjugatePacket K σ (groupLocalPlane ζ hζ w) =
      groupLocalPlane ζ hζ (conjugateFinitePlace K σ w) := by
  classical
  let hex : ℓ.Prime ∧ ∃ ξ : M, IsPrimitiveRoot ξ ℓ :=
    ⟨Fact.out, ζ, hζ⟩
  let ξ : M := hex.2.choose
  have hξ : IsPrimitiveRoot ξ ℓ := hex.2.choose_spec
  rw [groupLocalPlane_change_primitiveRoot ζ ξ hζ hξ w,
    groupLocalPlane_change_primitiveRoot ζ ξ hζ hξ
      (conjugateFinitePlace K σ w)]
  rw [conjugatePacket, packetAction, dif_pos hex]
  let N := normalizedPacketActionOfRoot K M ℓ ξ hξ σ
  let c := packetCyclotomicCharacter K M ℓ ξ hξ σ
  have hnormalized : (groupLocalPlane ξ hξ w).map N.toLinearMap =
      groupLocalPlane ξ hξ (conjugateFinitePlace K σ w) := by
    change (groupLocalPlane ξ hξ w).map
      ((((kummerDualEquiv ξ hξ).trans
        (automorphismCharacterAction K M ℓ σ)).trans
          (kummerDualEquiv ξ hξ).symm).toLinearMap) = _
    unfold groupLocalPlane
    exact map_comap_conjugated (kummerDualEquiv ξ hξ)
      (automorphismCharacterAction K M ℓ σ)
      (localD ℓ (primeValuationSubring w))
      (localD ℓ (primeValuationSubring (conjugateFinitePlace K σ w)))
      (automorphismCharacterAction_map_localD K M ℓ σ w)
  change (groupLocalPlane ξ hξ w).map
    ((LinearEquiv.smulOfUnit c * N).toLinearMap) = _
  calc
    (groupLocalPlane ξ hξ w).map
        ((LinearEquiv.smulOfUnit c * N).toLinearMap) =
      ((groupLocalPlane ξ hξ w).map N.toLinearMap).map
        (LinearEquiv.smulOfUnit c).toLinearMap := by
          rw [← Submodule.map_comp]
          rfl
    _ = (groupLocalPlane ξ hξ w).map N.toLinearMap :=
      submodule_map_smulOfUnit _ c
    _ = _ := hnormalized

private theorem groupLocalPlane_finrank_eq_one_of_residueChar
    {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (w : FinitePlace M) (hw : residueCharacteristic w = ℓ) :
    Module.finrank (ZMod ℓ) (groupLocalPlane ζ hζ w) = 1 := by
  rw [groupLocalPlane, Submodule.comap_equiv_eq_map_symm,
    (kummerDualEquiv ζ hζ).symm.finrank_map_eq]
  exact localD_finrank_eq_one_of_residueChar w hw

/-- Blueprint (6.4), including the cyclotomic scalar twist: conjugating a
local plane transports the place and the chosen primitive root. -/
theorem packet_action_cyclotomic_twist
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    conjugatePacket K σ (groupLocalPlane ζ hζ w) =
      groupLocalPlane (σ ζ) (hζ.map_of_injective σ.injective)
        (conjugateFinitePlace K σ w) := by
  exact (packet_action_localPlane_core K M ζ hζ σ w).trans
    (groupLocalPlane_change_primitiveRoot ζ (σ ζ) hζ
      (hζ.map_of_injective σ.injective) (conjugateFinitePlace K σ w))

/-- After removing the common cyclotomic scalar, packet planes are equivariant
with the action on places. -/
theorem packet_action_localPlane
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (σ : M ≃ₐ[K] M) (w : FinitePlace M) :
    conjugatePacket K σ (groupLocalPlane ζ hζ w) =
      groupLocalPlane ζ hζ (conjugateFinitePlace K σ w) := by
  exact packet_action_localPlane_core K M ζ hζ σ w

/-- Blueprint Corollary 6.3 (`cor:stabilizer`): the stabilizer of a local
packet is exactly the finite decomposition group of its prime-ideal place. -/
theorem packetStabilizer_eq_decompositionGroup
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (w : FinitePlace M) (hw : residueCharacteristic w ≠ ℓ) :
    packetStabilizer K (groupLocalPlane ζ hζ w) =
      decompositionGroup K w := by
  ext σ
  change conjugatePacket K σ (groupLocalPlane ζ hζ w) =
      groupLocalPlane ζ hζ w ↔ conjugateFinitePlace K σ w = w
  rw [packet_action_localPlane]
  constructor
  · intro hplane
    have hσchar : residueCharacteristic (conjugateFinitePlace K σ w) ≠ ℓ := by
      intro hchar
      have hleft := groupLocalPlane_finrank_eq_one_of_residueChar
        ζ hζ (conjugateFinitePlace K σ w) hchar
      have hright := groupLocalPlane_finrank ζ hζ w hw
      rw [hplane] at hleft
      omega
    by_contra hplace
    exact (packet_separation ζ hζ hplace hσchar hw) hplane
  · intro hplace
    rw [hplace]

/-- Restriction of Galois automorphisms in a finite Galois tower. -/
noncomputable def galoisRestriction (K L M : Type*)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L] :
    (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) :=
  AlgEquiv.restrictNormalHom L

/-- Defining equation for restriction in a tower. -/
theorem galoisRestriction_apply (K L M : Type*)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L]
    (σ : M ≃ₐ[K] M) (x : L) :
    algebraMap L M (galoisRestriction K L M σ x) =
      σ (algebraMap L M x) :=
  AlgEquiv.restrictNormal_commutes σ L x

/-- Restriction of a prime-ideal place through a finite number-field
extension, implemented by ideal contraction. -/
noncomputable def restrictFinitePlace (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : FinitePlace M) : FinitePlace L :=
  HeightOneSpectrum.under (𝓞 L) w

/-- Defining prime-ideal equation for place restriction. -/
theorem restrictFinitePlace_asIdeal (L : Type*) {M : Type*}
    [Field L] [Field M] [NumberField L] [NumberField M]
    [Algebra L M] (w : FinitePlace M) :
    (restrictFinitePlace L w).asIdeal =
      Ideal.comap (algebraMap (𝓞 L) (𝓞 M)) w.asIdeal :=
  rfl

private theorem under_galoisRestriction_smul
    (K L M : Type*) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L]
    (σ : M ≃ₐ[K] M) (P : Ideal (𝓞 M)) :
    (galoisRestriction K L M σ) • Ideal.under (𝓞 L) P =
      Ideal.under (𝓞 L) (σ • P) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_under, Ideal.mem_under,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hfield : algebraMap L M
      ((galoisRestriction K L M σ)⁻¹ (x : L)) =
      σ⁻¹ (algebraMap L M (x : L)) := by
    rw [← map_inv, galoisRestriction_apply]
  change algebraMap (𝓞 L) (𝓞 M)
      ((galoisRestriction K L M σ)⁻¹ • x) ∈ P ↔
    σ⁻¹ • algebraMap (𝓞 L) (𝓞 M) x ∈ P
  have hint : algebraMap (𝓞 L) (𝓞 M)
      ((galoisRestriction K L M σ)⁻¹ • x) =
      σ⁻¹ • algebraMap (𝓞 L) (𝓞 M) x := by
    apply Subtype.ext
    exact hfield
  rw [hint]

/-- Blueprint Lemma 7.1 (`lem:tower-surjectivity`): restriction maps a
finite decomposition group onto the decomposition group of the restricted
place.  Equality of the subgroup map includes surjectivity. -/
theorem tower_surjectivity (K L M : Type*)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]
    (w : FinitePlace M) :
    Subgroup.map (galoisRestriction K L M)
      (decompositionGroup K w) =
        decompositionGroup K (restrictFinitePlace L w) := by
  letI := finitePlaceAction K M
  letI := finitePlaceAction K L
  apply le_antisymm
  · rintro τ ⟨σ, hσ, rfl⟩
    change conjugateFinitePlace K σ w = w at hσ
    change conjugateFinitePlace K (galoisRestriction K L M σ)
      (restrictFinitePlace L w) = restrictFinitePlace L w
    apply HeightOneSpectrum.ext
    change (galoisRestriction K L M σ) • Ideal.under (𝓞 L) w.asIdeal =
      Ideal.under (𝓞 L) w.asIdeal
    rw [under_galoisRestriction_smul]
    exact congrArg (Ideal.under (𝓞 L))
      (congrArg HeightOneSpectrum.asIdeal hσ)
  · intro τ hτ
    change conjugateFinitePlace K τ (restrictFinitePlace L w) =
      restrictFinitePlace L w at hτ
    obtain ⟨σ0, hσ0⟩ :=
      AlgEquiv.restrictNormalHom_surjective M τ
    change galoisRestriction K L M σ0 = τ at hσ0
    let p : Ideal (𝓞 L) := (restrictFinitePlace L w).asIdeal
    let P0 : Ideal (𝓞 M) := σ0 • w.asIdeal
    have hP0over : P0.LiesOver p := by
      constructor
      change p = Ideal.under (𝓞 L) P0
      rw [← under_galoisRestriction_smul, hσ0]
      change p = τ • (restrictFinitePlace L w).asIdeal
      exact congrArg HeightOneSpectrum.asIdeal hτ.symm
    letI : P0.LiesOver p := hP0over
    have hwOver : w.asIdeal.LiesOver p := ⟨rfl⟩
    letI : w.asIdeal.LiesOver p := hwOver
    letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    obtain ⟨δ, hδ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      p P0 w.asIdeal (M ≃ₐ[L] M)
    let δK : M ≃ₐ[K] M := δ.restrictScalars K
    let σ : M ≃ₐ[K] M := δK * σ0
    refine ⟨σ, ?_, ?_⟩
    · change conjugateFinitePlace K σ w = w
      apply HeightOneSpectrum.ext
      change σ • w.asIdeal = w.asIdeal
      rw [show σ = δK * σ0 by rfl, mul_smul]
      exact hδ
    · apply AlgEquiv.ext
      intro x
      apply (algebraMap L M).injective
      rw [galoisRestriction_apply]
      change δ (σ0 (algebraMap L M x)) = algebraMap L M (τ x)
      rw [← galoisRestriction_apply K L M σ0 x,
        DFunLike.congr_fun hσ0 x]
      exact δ.commutes (τ x)

end

end NU.LocalTheory
