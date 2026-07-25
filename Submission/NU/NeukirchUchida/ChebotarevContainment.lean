import Submission.NU.NeukirchUchida.PrimeCorrespondence

/-!
# Chebotarev containment and normal-field rigidity

Blueprint §3: higher-degree primes are negligible, Chebotarev turns an
almost-everywhere splitting implication into field containment, and a
corresponding normal field is fixed literally inside the common `Omega`.
-/

open Filter Topology
open Filter Topology
open scoped NumberField Pointwise
open IsDedekindDomain

namespace NU.NeukirchUchida

noncomputable section

/-- The set `P₁(L)` of primes of residue degree one over their underlying
rational prime, blueprint §3.1. -/
def degreeOnePrimeSet (L : NumberFieldInOmega) :
    Set (NU.Chebotarev.PrimeIdeal L.field) :=
  {v | absoluteResidueDegree L v = 1}

/-- Rational primes having an unramified residue-degree-one factor in `L`;
this is `Sigma₁(L)` from blueprint §3.2. -/
def degreeOneRationalPrimeSet (L : NumberFieldInOmega) :
    Set (NU.Chebotarev.PrimeIdeal ℚ) :=
  {q | ∃ v : NU.Chebotarev.PrimeIdeal L.field,
    rationalPrime L v = q ∧
      absoluteRamificationIndex L v = 1 ∧
      absoluteResidueDegree L v = 1}

/-- A rational prime splits completely in an embedded number field.  Both
`e = 1` and `f = 1` are required at every prime above it, so the predicate is
not satisfiable by a merely residue-degree-one factor. -/
def SplitsCompletelyAt (L : NumberFieldInOmega)
    (q : NU.Chebotarev.PrimeIdeal ℚ) : Prop :=
  (∃ v : NU.Chebotarev.PrimeIdeal L.field,
    rationalPrime L v = q) ∧
  ∀ v : NU.Chebotarev.PrimeIdeal L.field,
    rationalPrime L v = q →
      absoluteRamificationIndex L v = 1 ∧
        absoluteResidueDegree L v = 1

/-- The split-prime set `Spl(L)`. -/
def splitPrimeSet (L : NumberFieldInOmega) :
    Set (NU.Chebotarev.PrimeIdeal ℚ) :=
  {q | SplitsCompletelyAt L q}

private theorem absoluteRamificationIndex_eq_ramificationIdx
    (L : NumberFieldInOmega)
    (v : NU.Chebotarev.PrimeIdeal L.field) :
    absoluteRamificationIndex L v =
      v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ) := rfl

private theorem absoluteResidueDegree_eq_inertiaDeg
    (L : NumberFieldInOmega)
    (v : NU.Chebotarev.PrimeIdeal L.field) :
    absoluteResidueDegree L v =
      v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ) := rfl

/-- Blueprint Lemma `lem:higher-degree-negligible`: primes of residue degree
at least two have Dirichlet density zero. -/
theorem higherDegreePrimes_hasDirichletDensity_zero
    (L : NumberFieldInOmega) :
    NU.Chebotarev.HasDirichletDensity
      ((degreeOnePrimeSet L)ᶜ) 0 := by
  let S : Set (NU.Chebotarev.PrimeIdeal L.field) :=
    {v | 2 ≤ (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal}
  have hset : (degreeOnePrimeSet L)ᶜ = S := by
    ext v
    rw [Set.mem_compl_iff]
    letI : v.asIdeal.LiesOver (Ideal.under (𝓞 ℚ) v.asIdeal) := ⟨rfl⟩
    change absoluteResidueDegree L v ≠ 1 ↔
      2 ≤ (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal
    rw [absoluteResidueDegree_eq_inertiaDeg,
      ← Ideal.inertiaDeg_eq_inertiaDeg'
        (Ideal.under (𝓞 ℚ) v.asIdeal) v.asIdeal]
    have hpos : 0 < (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal :=
      Ideal.inertiaDeg_pos (Ideal.under (𝓞 ℚ) v.asIdeal) v.asIdeal
    omega
  rw [hset]
  exact NU.Chebotarev.sqrt_bound_hasDirichletDensity_zero S
    (NU.Chebotarev.PrimeIdeal.count_residueDegree_ge_two
      (K := ℚ) (E := L.field))

/-- Density-one form of `lem:higher-degree-negligible`. -/
theorem degreeOnePrimes_hasDirichletDensity_one
    (L : NumberFieldInOmega) :
    NU.Chebotarev.HasDirichletDensity (degreeOnePrimeSet L) 1 := by
  apply NU.Chebotarev.HasDirichletDensity.congr_of_symmetricDifference_zero
    (NU.Chebotarev.allPrimes_dirichletDensity_one (K := L.field))
  have heq : NU.Chebotarev.symmetricDifference
      (Set.univ : Set (NU.Chebotarev.PrimeIdeal L.field))
      (degreeOnePrimeSet L) = (degreeOnePrimeSet L)ᶜ := by
    ext v
    simp [NU.Chebotarev.symmetricDifference]
  rw [heq]
  exact higherDegreePrimes_hasDirichletDensity_zero L

set_option maxHeartbeats 800000 in
/-- Blueprint Proposition `prop:containment` (Chebotarev containment).

If, away from finitely many rational primes, every rational prime with a
degree-one factor in `L` splits completely in a finite Galois field `K`, then
`K` is literally contained in `L` inside `Omega`. -/
theorem chebotarev_containment
    (K L : NumberFieldInOmega) [IsGalois ℚ K.field]
    (exceptional : Finset (NU.Chebotarev.PrimeIdeal ℚ))
    (hsplit : ∀ q, q ∉ exceptional →
      q ∈ degreeOneRationalPrimeSet L → SplitsCompletelyAt K q) :
    K.field ≤ L.field := by
  have hK0 : IsGalois ℚ K.field := inferInstance
  let M : NumberFieldInOmega :=
    { field := K.field ⊔ L.field
      finite := IntermediateField.finiteDimensional_sup K.field L.field }
  have hKM : K.field ≤ M.field := le_sup_left
  have hLM : L.field ≤ M.field := le_sup_right
  letI : Algebra ℚ M.field := M.field.algebra'
  letI : NumberField M.field := NumberField.of_module_finite ℚ M.field
  letI : Algebra K.field M.field :=
    (IntermediateField.inclusion hKM).toRingHom.toAlgebra
  letI : Algebra L.field M.field :=
    (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : IsScalarTower ℚ K.field M.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  letI : IsScalarTower ℚ L.field M.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let K' : IntermediateField ℚ M.field := IntermediateField.restrict hKM
  let L' : IntermediateField ℚ M.field := IntermediateField.restrict hLM
  letI : Algebra ℚ K' := K'.algebra'
  letI : Algebra ℚ L' := L'.algebra'
  have htop : K' ⊔ L' = ⊤ := by
    apply IntermediateField.lift_injective M.field
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  let eK := IntermediateField.restrict_algEquiv hKM
  let eL := IntermediateField.restrict_algEquiv hLM
  have hK' : IsGalois ℚ K' := by
    apply IsGalois.of_equiv_equiv (h := hK0)
      (f := RingEquiv.refl ℚ) (g := eK.toRingEquiv)
    ext x
    simp
  letI : IsGalois ℚ K' := hK'
  have hL'M : IsGalois L' M.field := IsGalois.sup_right K' L' htop
  have hLMgal : IsGalois L.field M.field := by
    apply IsGalois.of_equiv_equiv (h := hL'M)
      (f := eL.symm.toRingEquiv) (g := RingEquiv.refl M.field)
    ext x
    change (eL.symm x).1 = x.1.1
    exact congrArg (fun y : L' => y.1.1) (eL.apply_symm_apply x)
  letI : IsGalois L.field M.field := hLMgal
  letI : Finite (M.field ≃ₐ[L.field] M.field) :=
    Finite.of_injective (AlgEquiv.restrictScalarsHom ℚ)
      (AlgEquiv.restrictScalarsHom_injective ℚ)

  have restriction_eq
      (v : NU.Chebotarev.PrimeIdeal L.field)
      (W : NU.Chebotarev.PrimeIdeal M.field)
      (hWv : W.asIdeal.LiesOver v.asIdeal) :
      rationalPrime K (NU.LocalTheory.restrictFinitePlace K.field W) =
        rationalPrime L v := by
    apply HeightOneSpectrum.ext
    unfold rationalPrime
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
      NU.LocalTheory.restrictFinitePlace_asIdeal,
      NU.LocalTheory.restrictFinitePlace_asIdeal]
    have hv : Ideal.comap (algebraMap (𝓞 L.field) (𝓞 M.field))
        W.asIdeal = v.asIdeal := by
      rw [← Ideal.under_def]
      exact hWv.over.symm
    rw [← hv]
    simp only [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 K.field) (𝓞 M.field),
      ← IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 L.field) (𝓞 M.field)]

  have automorphism_eq_one_of_split
      (v : NU.Chebotarev.PrimeIdeal L.field)
      (W : NU.Chebotarev.PrimeIdeal M.field)
      (hWv : W.asIdeal.LiesOver v.asIdeal)
      (hsplitK : SplitsCompletelyAt K (rationalPrime L v))
      (sigma : M.field ≃ₐ[L.field] M.field)
      (hsigma : sigma • W.asIdeal = W.asIdeal) : sigma = 1 := by
    let sigmaQ : M.field ≃ₐ[ℚ] M.field := sigma.restrictScalars ℚ
    let sigmaK' : K' ≃ₐ[ℚ] K' := AlgEquiv.restrictNormalHom K' sigmaQ
    let sigmaK : K.field ≃ₐ[ℚ] K.field :=
      eK.trans (sigmaK'.trans eK.symm)
    let u := NU.LocalTheory.restrictFinitePlace K.field W
    have hcomm (x : K.field) :
        algebraMap K.field M.field (sigmaK x) =
          sigmaQ (algebraMap K.field M.field x) := by
      apply Subtype.ext
      change (sigmaK x).1 = (sigmaQ (algebraMap K.field M.field x)).1
      calc
        (sigmaK x).1 = (sigmaK' (eK x)).1.1 := by
          have hx := congrArg (fun y : K' => y.1.1)
            (eK.apply_symm_apply (sigmaK' (eK x)))
          change (eK.symm (sigmaK' (eK x))).1 =
            (sigmaK' (eK x)).1.1 at hx
          exact hx
        _ = (sigmaQ (eK x).1).1 := by
          exact congrArg Subtype.val
            (AlgEquiv.restrictNormal_commutes sigmaQ K' (eK x))
        _ = (sigmaQ (algebraMap K.field M.field x)).1 := by rfl
    have hcomm_int (x : 𝓞 K.field) :
        algebraMap (𝓞 K.field) (𝓞 M.field) (sigmaK • x) =
          sigmaQ • algebraMap (𝓞 K.field) (𝓞 M.field) x := by
      apply Subtype.ext
      exact hcomm x
    have hWQ : sigmaQ • W.asIdeal = W.asIdeal := by
      change sigma • W.asIdeal = W.asIdeal
      exact hsigma
    have hstab : sigmaK • u.asIdeal = u.asIdeal := by
      apply Ideal.ext
      intro x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      change algebraMap (𝓞 K.field) (𝓞 M.field) (sigmaK⁻¹ • x) ∈ W.asIdeal ↔
        algebraMap (𝓞 K.field) (𝓞 M.field) x ∈ W.asIdeal
      have hi := hcomm_int (sigmaK⁻¹ • x)
      have hi' := congrArg (fun y : 𝓞 M.field => sigmaQ⁻¹ • y) hi
      have hinv : algebraMap (𝓞 K.field) (𝓞 M.field) (sigmaK⁻¹ • x) =
          sigmaQ⁻¹ • algebraMap (𝓞 K.field) (𝓞 M.field) x := by
        simpa using hi'.symm
      rw [hinv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hWQ]
    have hsplitKu : SplitsCompletelyAt K (rationalPrime K u) := by
      rw [restriction_eq v W hWv]
      exact hsplitK
    have hs := hsplitKu.2 u rfl
    let q := rationalPrime K u
    have hover : u.asIdeal.LiesOver q.asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal]
      rfl⟩
    letI : u.asIdeal.LiesOver q.asIdeal := hover
    have hcard : Nat.card
        (MulAction.stabilizer (K.field ≃ₐ[ℚ] K.field) u.asIdeal) = 1 := by
      rw [Ideal.card_stabilizer_eq q.asIdeal u.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal u.asIdeal
          (K.field ≃ₐ[ℚ] K.field),
        Ideal.inertiaDegIn_eq_inertiaDeg q.asIdeal u.asIdeal
          (K.field ≃ₐ[ℚ] K.field)]
      exact one_mul 1 ▸ congrArg₂ (· * ·) hs.1 hs.2
    have hbot : MulAction.stabilizer (K.field ≃ₐ[ℚ] K.field) u.asIdeal = ⊥ :=
      Subgroup.card_eq_one.mp hcard
    have hsK : sigmaK = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact hstab
    have hsK' : sigmaK' = 1 := by
      apply AlgEquiv.ext
      intro y
      obtain ⟨x, rfl⟩ := eK.surjective y
      have hx := DFunLike.congr_fun hsK x
      change eK.symm (sigmaK' (eK x)) = x at hx
      have hx' := congrArg eK hx
      rw [eK.apply_symm_apply] at hx'
      exact hx'
    let H : IntermediateField ℚ M.field :=
      IntermediateField.fixedField (Subgroup.zpowers sigmaQ)
    have hKle : K' ≤ H := by
      intro y hy
      rw [IntermediateField.mem_fixedField_iff]
      intro tau htau
      let yK : K' := ⟨y, hy⟩
      have hfix : sigmaQ y = y := by
        have hc := AlgEquiv.restrictNormal_commutes sigmaQ K' yK
        have hy' := DFunLike.congr_fun hsK' yK
        exact hc.symm.trans (congrArg Subtype.val hy')
      have hz : Subgroup.zpowers sigmaQ ≤
          MulAction.stabilizer (M.field ≃ₐ[ℚ] M.field) y :=
        Subgroup.zpowers_le.mpr hfix
      exact hz htau
    have hLle : L' ≤ H := by
      intro y hy
      rw [IntermediateField.mem_fixedField_iff]
      intro tau htau
      let yL : L' := ⟨y, hy⟩
      have hfix : sigmaQ y = y := by
        obtain ⟨x, hx⟩ := eL.surjective yL
        have hxval := congrArg Subtype.val hx
        change (eL x).1 = y at hxval
        change sigma y = y
        rw [← hxval]
        change sigma (algebraMap L.field M.field x) =
          algebraMap L.field M.field x
        exact sigma.commutes x
      have hz : Subgroup.zpowers sigmaQ ≤
          MulAction.stabilizer (M.field ≃ₐ[ℚ] M.field) y :=
        Subgroup.zpowers_le.mpr hfix
      exact hz htau
    have htopH : (⊤ : IntermediateField ℚ M.field) ≤ H := by
      rw [← htop]
      exact sup_le hKle hLle
    apply AlgEquiv.ext
    intro x
    have hx : x ∈ H := htopH trivial
    change x ∈ IntermediateField.fixedField (Subgroup.zpowers sigmaQ) at hx
    exact (IntermediateField.mem_fixedField_iff
      (H := Subgroup.zpowers sigmaQ) x).mp hx sigmaQ
        (Subgroup.mem_zpowers sigmaQ)

  have stabilizer_eq_bot_of_split
      (v : NU.Chebotarev.PrimeIdeal L.field)
      (hsplitK : SplitsCompletelyAt K (rationalPrime L v))
      (W : NU.Chebotarev.PrimeIdeal M.field)
      (hWv : W.asIdeal.LiesOver v.asIdeal) :
      MulAction.stabilizer (M.field ≃ₐ[L.field] M.field) W.asIdeal = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro sigma hsigma
    exact automorphism_eq_one_of_split v W hWv hsplitK sigma hsigma

  let T : Set (NU.Chebotarev.PrimeIdeal L.field) :=
    NU.Chebotarev.frobeniusPrimeSet (K := L.field) (L := M.field)
      (ConjClasses.mk (1 : M.field ≃ₐ[L.field] M.field))
  let badExc : Set (NU.Chebotarev.PrimeIdeal L.field) :=
    {v | rationalPrime L v ∈ exceptional}
  let badRam : Set (NU.Chebotarev.PrimeIdeal L.field) :=
    {v | v.asIdeal ∣ differentIdeal (𝓞 ℚ) (𝓞 L.field)}
  let bad := badExc ∪ badRam
  let good := degreeOnePrimeSet L \ bad

  have badExc_finite : badExc.Finite := by
    let fiber : NU.Chebotarev.PrimeIdeal ℚ →
        Set (NU.Chebotarev.PrimeIdeal L.field) := fun q =>
          {v | rationalPrime L v = q}
    have hfiber (q : NU.Chebotarev.PrimeIdeal ℚ) : (fiber q).Finite := by
      dsimp [fiber]
      let S : Set (Ideal (𝓞 L.field)) := q.asIdeal.primesOver (𝓞 L.field)
      have hS : S.Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
      apply Set.Finite.of_finite_image
        (f := fun v : NU.Chebotarev.PrimeIdeal L.field => v.asIdeal)
      · apply hS.subset
        rintro I ⟨v, hv, rfl⟩
        change v.asIdeal ∈ q.asIdeal.primesOver (𝓞 L.field)
        refine ⟨inferInstance, ⟨?_⟩⟩
        rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal]
        exact congrArg HeightOneSpectrum.asIdeal hv.symm
      · intro v hv w hw hvw
        exact HeightOneSpectrum.asIdeal_injective hvw
    have heq : badExc = ⋃ q ∈ (exceptional : Set _), fiber q := by
      ext v
      simp [badExc, fiber]
    rw [heq]
    exact exceptional.finite_toSet.biUnion fun q hq => hfiber q
  have badRam_finite : badRam.Finite := by
    let I : Ideal (𝓞 L.field) := differentIdeal (𝓞 ℚ) (𝓞 L.field)
    have hI : I ≠ ⊥ := differentIdeal_ne_bot
    letI : NeZero I := ⟨hI⟩
    letI : Finite ((𝓞 L.field) ⧸ I) :=
      Ring.HasFiniteQuotients.finiteQuotient hI
    apply Set.Finite.of_finite_image
      (f := fun v : NU.Chebotarev.PrimeIdeal L.field =>
        v.asIdeal.map (Ideal.Quotient.mk I))
    · exact Set.toFinite _
    · intro v hv w hw hvw
      apply HeightOneSpectrum.asIdeal_injective
      have heq := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hvw
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at heq
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker, sup_eq_left.mpr (Ideal.dvd_iff_le.mp hv),
        sup_eq_left.mpr (Ideal.dvd_iff_le.mp hw)] at heq
      exact heq
  have bad_finite : bad.Finite := badExc_finite.union badRam_finite
  have good_density : NU.Chebotarev.HasDirichletDensity good 1 := by
    apply NU.Chebotarev.HasDirichletDensity.congr_of_symmetricDifference_zero
      (degreeOnePrimes_hasDirichletDensity_one L)
    apply NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero
    apply bad_finite.subset
    intro v hv
    rcases hv with hv | hv
    · by_contra hvbad
      exact hv.2 ⟨hv.1, hvbad⟩
    · exact (hv.2 hv.1.1).elim

  have good_subset_T : good ⊆ T := by
    intro v hv
    have hvdeg : absoluteResidueDegree L v = 1 := hv.1
    have hvbad : v ∉ bad := hv.2
    have hnotExc : v ∉ badExc := fun h => hvbad (Or.inl h)
    have hnotRam : v ∉ badRam := fun h => hvbad (Or.inr h)
    have hqexc : rationalPrime L v ∉ exceptional := by
      exact hnotExc
    have hunrv : Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal := by
      by_contra h
      exact hnotRam ((dvd_differentIdeal_iff (A := 𝓞 ℚ)
        (B := 𝓞 L.field)).mpr h)
    have hover : v.asIdeal.LiesOver (rationalPrime L v).asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal]
      rfl⟩
    letI : v.asIdeal.LiesOver (rationalPrime L v).asIdeal := hover
    letI : Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal := hunrv
    have he : absoluteRamificationIndex L v = 1 := by
      change v.asIdeal.ramificationIdx' (𝓞 ℚ) = 1
      rw [← Ideal.ramificationIdx_eq_ramificationIdx'
        (rationalPrime L v).asIdeal v.asIdeal (rationalPrime L v).ne_bot]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
        (R := 𝓞 ℚ) v.ne_bot
    have hsplitK : SplitsCompletelyAt K (rationalPrime L v) :=
      hsplit (rationalPrime L v) hqexc ⟨v, rfl, he, hvdeg⟩
    have hunr : NU.Chebotarev.IsUnramifiedPrime
        (K := L.field) (L := M.field) v := by
      intro W hWv
      letI : W.asIdeal.LiesOver v.asIdeal := hWv
      have hstab := stabilizer_eq_bot_of_split v hsplitK W hWv
      have hcard : Nat.card
          (MulAction.stabilizer (M.field ≃ₐ[L.field] M.field) W.asIdeal) = 1 := by
        rw [hstab]
        exact Nat.card_unique
      rw [Ideal.card_stabilizer_eq v.asIdeal W.asIdeal] at hcard
      have heIn : v.asIdeal.ramificationIdxIn (𝓞 M.field) = 1 := by
        apply Nat.eq_one_of_dvd_one
        exact ⟨v.asIdeal.inertiaDegIn (𝓞 M.field), hcard.symm⟩
      have heW : W.asIdeal.ramificationIdx' (𝓞 L.field) = 1 := by
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W.asIdeal
          (M.field ≃ₐ[L.field] M.field)]
        exact heIn
      have heW' : v.asIdeal.ramificationIdx W.asIdeal = 1 := by
        rw [Ideal.ramificationIdx_eq_ramificationIdx'
          v.asIdeal W.asIdeal v.ne_bot]
        exact heW
      apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain W.ne_bot).mpr
      rw [← hWv.over]
      exact heW'
    change v ∈ NU.Chebotarev.frobeniusPrimeSet
      (K := L.field) (L := M.field)
      (ConjClasses.mk (1 : M.field ≃ₐ[L.field] M.field))
    refine ⟨hunr, ?_⟩
    obtain ⟨Wideal, hWmax, hWv⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := 𝓞 M.field) v.asIdeal
    let W : NU.Chebotarev.PrimeIdeal M.field :=
      ⟨Wideal, hWmax.isPrime, by
        intro hbot
        apply v.ne_bot
        have hoverW := hWv.over
        rw [hbot] at hoverW
        simpa using hoverW⟩
    refine ⟨W, hWv, ?_⟩
    have hstab := stabilizer_eq_bot_of_split v hsplitK W hWv
    have hfrob : NU.Chebotarev.arithFrobeniusAt
        (K := L.field) (L := M.field) W ∈
        MulAction.stabilizer (M.field ≃ₐ[L.field] M.field) W.asIdeal := by
      set_option maxHeartbeats 800000 in
      exact IsArithFrobAt.arithFrobAt_mem_stabilizer
        (𝓞 L.field) (M.field ≃ₐ[L.field] M.field) W.asIdeal
    rw [hstab] at hfrob
    change ConjClasses.mk (NU.Chebotarev.arithFrobeniusAt
      (K := L.field) (L := M.field) W) = ConjClasses.mk 1
    rw [Subgroup.mem_bot.mp hfrob]

  have primeCountingSet_finite
      (S : Set (NU.Chebotarev.PrimeIdeal L.field)) (x : ℝ) :
      {v : NU.Chebotarev.PrimeIdeal L.field |
        v ∈ S ∧ (NU.Chebotarev.PrimeIdeal.norm v : ℝ) ≤ x}.Finite := by
    obtain ⟨n : ℕ, hn⟩ := exists_nat_ge x
    apply Set.Finite.of_finite_image
      (f := fun v : NU.Chebotarev.PrimeIdeal L.field => v.asIdeal)
    · apply (Ideal.finite_setOf_absNorm_le (S := 𝓞 L.field) n).subset
      rintro I ⟨v, hv, rfl⟩
      change Ideal.absNorm v.asIdeal ≤ n
      exact_mod_cast hv.2.trans hn
    · intro v hv w hw hvw
      exact HeightOneSpectrum.asIdeal_injective hvw
  have primeCounting_mono {S U : Set (NU.Chebotarev.PrimeIdeal L.field)}
      (hSU : S ⊆ U) (x : ℝ) :
      NU.Chebotarev.primeCounting S x ≤ NU.Chebotarev.primeCounting U x := by
    unfold NU.Chebotarev.primeCounting
    apply Set.ncard_le_ncard
    · intro v hv
      exact ⟨hSU hv.1, hv.2⟩
    · exact primeCountingSet_finite U x
  have hresidue (v : NU.Chebotarev.PrimeIdeal L.field) :
      absoluteResidueDegree L v =
        v.asIdeal.inertiaDeg' (𝓞 ℚ) := rfl
  let D : Set (NU.Chebotarev.PrimeIdeal L.field) := (degreeOnePrimeSet L)ᶜ
  let D' : Set (NU.Chebotarev.PrimeIdeal L.field) :=
    {v | 2 ≤ (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal}
  have hDD' : D = D' := by
    ext v
    letI : v.asIdeal.LiesOver (Ideal.under (𝓞 ℚ) v.asIdeal) := ⟨rfl⟩
    change absoluteResidueDegree L v ≠ 1 ↔
      2 ≤ (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal
    rw [hresidue, ← Ideal.inertiaDeg_eq_inertiaDeg'
      (Ideal.under (𝓞 ℚ) v.asIdeal) v.asIdeal]
    have hpos : 0 < (Ideal.under (𝓞 ℚ) v.asIdeal).inertiaDeg v.asIdeal :=
      Ideal.inertiaDeg_pos (Ideal.under (𝓞 ℚ) v.asIdeal) v.asIdeal
    omega
  have hDbound : (fun x => (NU.Chebotarev.primeCounting D x : ℝ))
      =O[atTop] fun x => Real.sqrt x := by
    rw [hDD']
    exact NU.Chebotarev.PrimeIdeal.count_residueDegree_ge_two
      (K := ℚ) (E := L.field)
  let X := NU.Chebotarev.symmetricDifference good T
  let A := X ∩ D
  let B := X \ D
  have hA_subset_D : A ⊆ D := fun _ h => h.2
  have hAcount : (fun x => (NU.Chebotarev.primeCounting A x : ℝ))
      =O[atTop] fun x => Real.sqrt x := by
    apply (Asymptotics.IsBigO.of_bound' (Eventually.of_forall fun x => ?_)).trans hDbound
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤
      (NU.Chebotarev.primeCounting A x : ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (show 0 ≤
        (NU.Chebotarev.primeCounting D x : ℝ) from Nat.cast_nonneg _)]
    exact_mod_cast primeCounting_mono hA_subset_D x
  have hAzero : NU.Chebotarev.HasDirichletDensity A 0 :=
    NU.Chebotarev.sqrt_bound_hasDirichletDensity_zero A hAcount
  have hBfinite : B.Finite := by
    apply bad_finite.subset
    intro v hv
    have hvdeg : v ∈ degreeOnePrimeSet L := by
      have hvnot : ¬v ∈ D := hv.2
      change ¬v ∈ (degreeOnePrimeSet L)ᶜ at hvnot
      simpa using hvnot
    by_contra hvbad
    have hvgood : v ∈ good := ⟨hvdeg, hvbad⟩
    rcases hv.1 with hvX | hvX
    · exact hvX.2 (good_subset_T hvX.1)
    · exact hvX.2 hvgood
  have hsymAXfinite :
      (NU.Chebotarev.symmetricDifference A X).Finite := by
    apply hBfinite.subset
    intro v hv
    rcases hv with hv | hv
    · exact (hv.2 hv.1.1).elim
    · refine ⟨hv.1, ?_⟩
      intro hvD
      exact hv.2 ⟨hv.1, hvD⟩
  have hXzero : NU.Chebotarev.HasDirichletDensity X 0 := by
    apply NU.Chebotarev.HasDirichletDensity.congr_of_symmetricDifference_zero hAzero
    exact NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hsymAXfinite
  have hTone : NU.Chebotarev.HasDirichletDensity T 1 := by
    apply NU.Chebotarev.HasDirichletDensity.congr_of_symmetricDifference_zero good_density
    exact hXzero
  have hcarrier :
      (ConjClasses.mk (1 : M.field ≃ₐ[L.field] M.field)).carrier = {1} := by
    ext g
    rw [ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj]
    simp
  have hTcheb : NU.Chebotarev.HasDirichletDensity T
      (1 / (Nat.card (M.field ≃ₐ[L.field] M.field) : ℝ)) := by
    simpa [T, hcarrier] using
      (NU.Chebotarev.chebotarev_dirichletDensity
        (K := L.field) (L := M.field)
        (ConjClasses.mk (1 : M.field ≃ₐ[L.field] M.field)))
  have hdensity : (1 : ℝ) =
      1 / (Nat.card (M.field ≃ₐ[L.field] M.field) : ℝ) :=
    tendsto_nhds_unique hTone hTcheb
  have hcardpos : (0 : ℝ) <
      (Nat.card (M.field ≃ₐ[L.field] M.field) : ℝ) := by
    exact_mod_cast Nat.card_pos (α := M.field ≃ₐ[L.field] M.field)
  have hcardle : (Nat.card (M.field ≃ₐ[L.field] M.field) : ℝ) ≤ 1 := by
    have hmul := (le_div_iff₀ hcardpos).mp hdensity.le
    simpa using hmul
  have hcard : Nat.card (M.field ≃ₐ[L.field] M.field) = 1 := by
    have hle : Nat.card (M.field ≃ₐ[L.field] M.field) ≤ 1 := by
      exact_mod_cast hcardle
    exact Nat.le_antisymm hle Nat.card_pos
  have hfinrank : Module.finrank L.field M.field = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hcard
  letI : Module.Free L.field M.field :=
    Module.Free.of_divisionRing L.field M.field
  have hbij : Function.Bijective (algebraMap L.field M.field) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank
  intro x hx
  let xM : M.field := ⟨x, hKM hx⟩
  obtain ⟨y, hy⟩ := hbij.2 xM
  have hval : y.1 = x := congrArg Subtype.val hy
  rw [← hval]
  exact y.2

/-- Blueprint Corollary `cor:normality`: the almost-everywhere splitting
criterion forces a number field to be Galois over `ℚ`. -/
theorem galois_of_degreeOnePrime_splitsCompletely
    (L : NumberFieldInOmega)
    (exceptional : Finset (NU.Chebotarev.PrimeIdeal ℚ))
    (hsplit : ∀ q, q ∉ exceptional →
      q ∈ degreeOneRationalPrimeSet L → SplitsCompletelyAt L q) :
    IsGalois ℚ L.field := by
  let Nfield := IntermediateField.normalClosure ℚ L.field Omega
  let N : NumberFieldInOmega :=
    { field := Nfield
      finite := normalClosure.is_finiteDimensional ℚ L.field Omega }
  have hLN : L.field ≤ N.field := IntermediateField.le_normalClosure L.field
  letI : NumberField N.field :=
    @NumberField.of_module_finite ℚ N.field _ _ (inferInstance : NumberField ℚ)
      N.field.algebra' N.finite
  letI : Algebra L.field N.field :=
    (IntermediateField.inclusion hLN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ L.field N.field := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  have hOmega : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  letI : IsGalois ℚ Omega := hOmega
  have hNgal : IsGalois ℚ N.field := by
    have hraw : @IsGalois ℚ _ N.field _ N.field.algebra' :=
      IsGalois.normalClosure ℚ L.field Omega
    apply IsGalois.of_equiv_equiv (h := hraw)
      (f := RingEquiv.refl ℚ) (g := RingEquiv.refl N.field)
    ext x
    simp
  letI : IsGalois ℚ N.field := hNgal
  letI : IsGalois L.field N.field :=
    IsGalois.tower_top_of_isGalois ℚ L.field N.field
  letI : Finite (N.field ≃ₐ[L.field] N.field) :=
    Finite.of_injective (AlgEquiv.restrictScalarsHom ℚ)
      (AlgEquiv.restrictScalarsHom_injective ℚ)
  let inclusionHom : L.field →ₐ[ℚ] N.field :=
    IsScalarTower.toAlgHom ℚ L.field N.field
  let L' : IntermediateField ℚ N.field := inclusionHom.fieldRange
  let eL : L.field ≃ₐ[ℚ] L' := inclusionHom.equivFieldRange
  let H := relativeGaloisGroup L N hLN
  have hH : H = L'.fixingSubgroup := by
    ext sigma
    constructor
    · intro hs y
      obtain ⟨x, rfl⟩ := eL.surjective y
      change sigma (algebraMap L.field N.field x) =
        algebraMap L.field N.field x
      exact hs x
    · intro hs x
      have hx := hs (eL x)
      exact hx

  have restriction_eq
      (q : NU.Chebotarev.PrimeIdeal ℚ)
      (w : NU.Chebotarev.PrimeIdeal N.field)
      (hwq : w.asIdeal.LiesOver q.asIdeal) :
      rationalPrime L (NU.LocalTheory.restrictFinitePlace L.field w) = q := by
    apply HeightOneSpectrum.ext
    unfold rationalPrime
    rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
      NU.LocalTheory.restrictFinitePlace_asIdeal]
    have hq : Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 N.field))
        w.asIdeal = q.asIdeal := by
      rw [← Ideal.under_def]
      exact hwq.over.symm
    simp only [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 L.field) (𝓞 N.field), hq]

  have local_iff
      (q : NU.Chebotarev.PrimeIdeal ℚ)
      (w : NU.Chebotarev.PrimeIdeal N.field)
      (hwq : w.asIdeal.LiesOver q.asIdeal) :
      let v := NU.LocalTheory.restrictFinitePlace L.field w
      (absoluteRamificationIndex L v = 1 ∧
        absoluteResidueDegree L v = 1) ↔
      ∀ sigma : N.field ≃ₐ[ℚ] N.field,
        sigma • w.asIdeal = w.asIdeal → sigma ∈ H := by
    dsimp only
    let v := NU.LocalTheory.restrictFinitePlace L.field w
    have hvq : rationalPrime L v = q := restriction_eq q w hwq
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rfl⟩
    letI : w.asIdeal.LiesOver q.asIdeal := hwq
    letI : w.asIdeal.LiesOver v.asIdeal := hwv
    have hvq' : v.asIdeal.LiesOver q.asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
        ← hvq]
      rfl⟩
    letI : v.asIdeal.LiesOver q.asIdeal := hvq'
    have hvbase : v.asIdeal.LiesOver (rationalPrime L v).asIdeal := ⟨by
      rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal]
      rfl⟩
    letI : v.asIdeal.LiesOver (rationalPrime L v).asIdeal := hvbase
    let Dq := MulAction.stabilizer (N.field ≃ₐ[ℚ] N.field) w.asIdeal
    let Dl := MulAction.stabilizer (N.field ≃ₐ[L.field] N.field) w.asIdeal
    let inc : Dl → Dq := fun tau =>
      ⟨tau.1.restrictScalars ℚ, tau.2⟩
    have hinc : Function.Injective inc := by
      intro a b hab
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      have hx := DFunLike.congr_fun (congrArg Subtype.val hab) x
      exact hx
    have he : absoluteRamificationIndex L v =
        v.asIdeal.ramificationIdx' (𝓞 ℚ) := rfl
    have hf : absoluteResidueDegree L v =
        v.asIdeal.inertiaDeg' (𝓞 ℚ) := rfl
    have hcardq : Nat.card Dq =
        w.asIdeal.ramificationIdx' (𝓞 ℚ) *
          w.asIdeal.inertiaDeg' (𝓞 ℚ) := by
      rw [Ideal.card_stabilizer_eq q.asIdeal w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal w.asIdeal
          (N.field ≃ₐ[ℚ] N.field),
        Ideal.inertiaDegIn_eq_inertiaDeg q.asIdeal w.asIdeal
          (N.field ≃ₐ[ℚ] N.field)]
    have hcardl : Nat.card Dl =
        w.asIdeal.ramificationIdx' (𝓞 L.field) *
          w.asIdeal.inertiaDeg' (𝓞 L.field) := by
      rw [Ideal.card_stabilizer_eq v.asIdeal w.asIdeal,
        Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal
          (N.field ≃ₐ[L.field] N.field),
        Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal
          (N.field ≃ₐ[L.field] N.field)]
    letI := Localization.AtPrime.algebraOfLiesOver v.asIdeal w.asIdeal
    have hcard : Nat.card Dq =
        (absoluteRamificationIndex L v * absoluteResidueDegree L v) *
          Nat.card Dl := by
      rw [hcardq, hcardl, he, hf,
        Ideal.ramificationIdx'_tower' v.asIdeal w.asIdeal,
        Ideal.inertiaDeg'_tower v.asIdeal w.asIdeal]
      ring
    constructor
    · intro hlocal sigma hsigma
      have hdeg : absoluteRamificationIndex L v *
          absoluteResidueDegree L v = 1 := by
        rw [hlocal.1, hlocal.2, one_mul]
      have hcards : Nat.card Dq = Nat.card Dl := by
        rw [hcard, hdeg, one_mul]
      letI : Fintype Dl := Fintype.ofFinite Dl
      letI : Fintype Dq := Fintype.ofFinite Dq
      have hbij : Function.Bijective inc :=
        (Fintype.bijective_iff_injective_and_card inc).2
          ⟨hinc, by simpa only [Nat.card_eq_fintype_card] using hcards.symm⟩
      let d : Dq := ⟨sigma, hsigma⟩
      obtain ⟨tau, htau⟩ := hbij.2 d
      intro x
      have heq : tau.1.restrictScalars ℚ = sigma := congrArg Subtype.val htau
      have hx := tau.1.commutes x
      calc
        sigma (algebraMap L.field N.field x) =
            tau.1 (algebraMap L.field N.field x) := by
          rw [← heq]
          rfl
        _ = algebraMap L.field N.field x := hx
    · intro hle
      have hsurj : Function.Surjective inc := by
        intro d
        have hdH : d.1 ∈ H := hle d.1 d.2
        let tau0 : N.field ≃ₐ[L.field] N.field :=
          { d.1.toRingEquiv with
            commutes' := hdH }
        let tau : Dl := ⟨tau0, d.2⟩
        exact ⟨tau, rfl⟩
      have hcards : Nat.card Dl = Nat.card Dq :=
        Nat.card_congr (Equiv.ofBijective inc ⟨hinc, hsurj⟩)
      have hdeg : absoluteRamificationIndex L v *
          absoluteResidueDegree L v = 1 := by
        have hpos : 0 < Nat.card Dl := Nat.card_pos
        have hm : 1 * Nat.card Dl =
            (absoluteRamificationIndex L v * absoluteResidueDegree L v) *
              Nat.card Dl := by
          calc
            1 * Nat.card Dl = Nat.card Dl := one_mul _
            _ = Nat.card Dq := hcards
            _ = _ := hcard
        exact (Nat.eq_of_mul_eq_mul_right hpos hm).symm
      change absoluteRamificationIndex L v = 1 ∧
        absoluteResidueDegree L v = 1
      constructor
      · apply Nat.eq_one_of_dvd_one
        exact ⟨absoluteResidueDegree L v, hdeg.symm⟩
      · apply Nat.eq_one_of_dvd_one
        exact ⟨absoluteRamificationIndex L v, by
          rw [Nat.mul_comm]
          exact hdeg.symm⟩

  have exists_frobenius_outside (n : N.field ≃ₐ[ℚ] N.field) :
      ∃ q : NU.Chebotarev.PrimeIdeal ℚ,
        q ∉ exceptional ∧
        q ∈ NU.Chebotarev.frobeniusPrimeSet (K := ℚ) (L := N.field)
          (ConjClasses.mk n) := by
    let S := NU.Chebotarev.frobeniusPrimeSet (K := ℚ) (L := N.field)
      (ConjClasses.mk n)
    have hden := NU.Chebotarev.chebotarev_dirichletDensity
      (K := ℚ) (L := N.field) (ConjClasses.mk n)
    have hnum : (0 : ℝ) < ((ConjClasses.mk n).carrier.ncard : ℝ) := by
      exact_mod_cast ((Set.ncard_pos (s := (ConjClasses.mk n).carrier)).2
        (show (ConjClasses.mk n).carrier.Nonempty from
          ⟨n, ConjClasses.mem_carrier_mk⟩))
    have hdenom : (0 : ℝ) < Nat.card (N.field ≃ₐ[ℚ] N.field) := by
      exact_mod_cast Nat.card_pos (α := N.field ≃ₐ[ℚ] N.field)
    have hpositive : (0 : ℝ) <
        ((ConjClasses.mk n).carrier.ncard : ℝ) /
          (Nat.card (N.field ≃ₐ[ℚ] N.field) : ℝ) :=
      div_pos hnum hdenom
    by_contra hex
    have hsub : S ⊆ (exceptional : Set _) := by
      intro q hq
      by_contra hqe
      exact hex ⟨q, hqe, hq⟩
    have hfin : S.Finite := exceptional.finite_toSet.subset hsub
    have hzero : NU.Chebotarev.HasDirichletDensity S 0 :=
      NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfin
    have heq : ((ConjClasses.mk n).carrier.ncard : ℝ) /
        (Nat.card (N.field ≃ₐ[ℚ] N.field) : ℝ) = 0 :=
      tendsto_nhds_unique hden hzero
    linarith

  let conjugatePrime
      (a : N.field ≃ₐ[ℚ] N.field)
      (w : NU.Chebotarev.PrimeIdeal N.field) :
      NU.Chebotarev.PrimeIdeal N.field :=
    { asIdeal := a • w.asIdeal
      isPrime := w.isPrime.smul a
      ne_bot := by
        intro hbot
        apply w.ne_bot
        have h := congrArg (fun I : Ideal (𝓞 N.field) => a⁻¹ • I) hbot
        simpa using h }

  have hnormal : H.Normal := by
    constructor
    intro n hn g
    obtain ⟨q, hqexc, hqfrobenius⟩ := exists_frobenius_outside n
    rcases hqfrobenius with ⟨hunr, w, hwq, hclass⟩
    let f : N.field ≃ₐ[ℚ] N.field :=
      NU.Chebotarev.arithFrobeniusAt (K := ℚ) (L := N.field) w
    have hconj : IsConj f n := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mp
      exact hclass
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    let w' := conjugatePrime a w
    have hw'q : w'.asIdeal.LiesOver q.asIdeal := ⟨by
      change q.asIdeal = Ideal.under (𝓞 ℚ) (a • w.asIdeal)
      rw [Ideal.under_smul]
      exact hwq.over⟩
    have hfmem : f • w.asIdeal = w.asIdeal :=
      IsArithFrobAt.arithFrobAt_mem_stabilizer
        (𝓞 ℚ) (N.field ≃ₐ[ℚ] N.field) w.asIdeal
    have hnmem : n • w'.asIdeal = w'.asIdeal := by
      have ht := congrArg (fun I : Ideal (𝓞 N.field) => a • I) hfmem
      change n • (a • w.asIdeal) = a • w.asIdeal
      rw [← ha]
      simpa only [← mul_smul, mul_assoc, inv_mul_cancel a, mul_one] using ht
    have hdecomp : ∀ tau : N.field ≃ₐ[ℚ] N.field,
        tau • w'.asIdeal = w'.asIdeal → tau ∈ H := by
      intro tau htau
      have hback : (a⁻¹ * tau * a) • w.asIdeal = w.asIdeal := by
        have ht := congrArg (fun I : Ideal (𝓞 N.field) => a⁻¹ • I) htau
        change a⁻¹ • (tau • (a • w.asIdeal)) =
          a⁻¹ • (a • w.asIdeal) at ht
        simpa only [← mul_smul, mul_assoc, inv_mul_cancel a, one_smul] using ht
      have hwunr : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := hunr w hwq
      have hgen := NU.Chebotarev.arithFrobAt_generates_decomposition
        (K := ℚ) (L := N.field) w hwunr
      have hback' : a⁻¹ * tau * a ∈
          NU.Chebotarev.decompositionSubgroup (K := ℚ) (L := N.field) w := hback
      rw [hgen, Subgroup.mem_zpowers_iff] at hback'
      obtain ⟨k, hk⟩ := hback'
      have htau : tau = n ^ k := by
        calc
          tau = a * (a⁻¹ * tau * a) * a⁻¹ := by group
          _ = a * (f ^ k) * a⁻¹ := by rw [hk]
          _ = (a * f * a⁻¹) ^ k := conj_zpow.symm
          _ = n ^ k := congrArg (fun z => z ^ k) ha
      rw [htau]
      exact H.zpow_mem hn k
    have hlocal := (local_iff q w' hw'q).mpr hdecomp
    let v := NU.LocalTheory.restrictFinitePlace L.field w'
    have hvq : rationalPrime L v = q := restriction_eq q w' hw'q
    have hqdegree : q ∈ degreeOneRationalPrimeSet L :=
      ⟨v, hvq, hlocal.1, hlocal.2⟩
    have hsplitq := hsplit q hqexc hqdegree
    let w'' := conjugatePrime g w'
    have hw''q : w''.asIdeal.LiesOver q.asIdeal := ⟨by
      change q.asIdeal = Ideal.under (𝓞 ℚ) (g • w'.asIdeal)
      rw [Ideal.under_smul]
      exact hw'q.over⟩
    have htargetmem : (g * n * g⁻¹) • w''.asIdeal = w''.asIdeal := by
      change (g * n * g⁻¹) • (g • w'.asIdeal) = g • w'.asIdeal
      have ht := congrArg (fun I : Ideal (𝓞 N.field) => g • I) hnmem
      simpa only [← mul_smul, mul_assoc, inv_mul_cancel g, mul_one] using ht
    let v' := NU.LocalTheory.restrictFinitePlace L.field w''
    have hv'q : rationalPrime L v' = q := restriction_eq q w'' hw''q
    have hlocal' : absoluteRamificationIndex L v' = 1 ∧
        absoluteResidueDegree L v' = 1 := hsplitq.2 v' hv'q
    exact (local_iff q w'' hw''q).mp hlocal' (g * n * g⁻¹) htargetmem

  have hnormal' : L'.fixingSubgroup.Normal := by
    rw [← hH]
    exact hnormal
  letI : L'.fixingSubgroup.Normal := hnormal'
  have hgalFixed : IsGalois ℚ
      (IntermediateField.fixedField L'.fixingSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup L'.fixingSubgroup
  have hgalL' : IsGalois ℚ L' :=
    IsGalois.of_algEquiv (IntermediateField.equivOfEq
      (IsGalois.fixedField_fixingSubgroup L'))
  apply IsGalois.of_equiv_equiv (h := hgalL')
    (f := RingEquiv.refl ℚ) (g := eL.symm.toRingEquiv)
  ext x
  simp

/-- Blueprint equation `eq:prime-set-correspondence`: corresponding fields
have the same rational degree-one and completely split prime sets. -/
theorem corresponding_primeSets
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁) :
    degreeOneRationalPrimeSet K₁.field =
        degreeOneRationalPrimeSet (correspondingField theta K₁) ∧
      splitPrimeSet K₁.field =
        splitPrimeSet (correspondingField theta K₁) := by
  let e := finitePrimeCorrespondence theta K₁
  constructor
  · ext q
    constructor
    · rintro ⟨v, hvq, he, hf⟩
      have hi := finitePrimeCorrespondence_invariants theta K₁ v
      refine ⟨e v, ?_, ?_, ?_⟩
      · exact hi.1.symm.trans hvq
      · exact hi.2.1.symm.trans he
      · exact hi.2.2.symm.trans hf
    · rintro ⟨w, hwq, he, hf⟩
      have hi := finitePrimeCorrespondence_invariants theta K₁ (e.symm w)
      refine ⟨e.symm w, ?_, ?_, ?_⟩
      · exact hi.1.trans (by simpa [e] using hwq)
      · exact hi.2.1.trans (by simpa [e] using he)
      · exact hi.2.2.trans (by simpa [e] using hf)
  · ext q
    constructor
    · rintro ⟨⟨v, hvq⟩, hall⟩
      refine ⟨⟨e v, ?_⟩, ?_⟩
      · have hi := finitePrimeCorrespondence_invariants theta K₁ v
        exact hi.1.symm.trans hvq
      · intro w hwq
        have hi := finitePrimeCorrespondence_invariants theta K₁ (e.symm w)
        have hsource : rationalPrime K₁.field (e.symm w) = q :=
          hi.1.trans (by simpa [e] using hwq)
        have hs := hall (e.symm w) hsource
        constructor
        · simpa [e] using hi.2.1.symm.trans hs.1
        · simpa [e] using hi.2.2.symm.trans hs.2
    · rintro ⟨⟨w, hwq⟩, hall⟩
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · have hi := finitePrimeCorrespondence_invariants theta K₁ (e.symm w)
        exact hi.1.trans (by simpa [e] using hwq)
      · intro v hvq
        have hi := finitePrimeCorrespondence_invariants theta K₁ v
        have htarget :
            rationalPrime (correspondingField theta K₁) (e v) = q :=
          hi.1.symm.trans hvq
        have ht := hall (e v) htarget
        constructor
        · exact hi.2.1.trans ht.1
        · exact hi.2.2.trans ht.2

private theorem splitsCompletelyAt_of_degreeOne_of_isGalois
    (L : NumberFieldInOmega) [IsGalois ℚ L.field]
    (q : NU.Chebotarev.PrimeIdeal ℚ)
    (hq : q ∈ degreeOneRationalPrimeSet L) :
    SplitsCompletelyAt L q := by
  rcases hq with ⟨v₀, hv₀q, he₀, hf₀⟩
  refine ⟨⟨v₀, hv₀q⟩, ?_⟩
  intro v hvq
  have hv₀over : v₀.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hv₀q]
    rfl⟩
  have hvover : v.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, ← NU.LocalTheory.restrictFinitePlace_asIdeal,
      ← hvq]
    rfl⟩
  letI : v₀.asIdeal.LiesOver q.asIdeal := hv₀over
  letI : v.asIdeal.LiesOver q.asIdeal := hvover
  have heq_e : v₀.asIdeal.ramificationIdx'
      (NumberField.RingOfIntegers ℚ) =
      v.asIdeal.ramificationIdx' (NumberField.RingOfIntegers ℚ) :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup q.asIdeal v₀.asIdeal v.asIdeal
      (L.field ≃ₐ[ℚ] L.field)
  have heq_f : v₀.asIdeal.inertiaDeg'
      (NumberField.RingOfIntegers ℚ) =
      v.asIdeal.inertiaDeg' (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup q.asIdeal v₀.asIdeal v.asIdeal
      (L.field ≃ₐ[ℚ] L.field)
  constructor
  · rw [absoluteRamificationIndex_eq_ramificationIdx, ← heq_e,
      ← absoluteRamificationIndex_eq_ramificationIdx]
    exact he₀
  · rw [absoluteResidueDegree_eq_inertiaDeg, ← heq_f,
      ← absoluteResidueDegree_eq_inertiaDeg]
    exact hf₀

/-- Blueprint Proposition `prop:normal-fixed`: if a corresponding source
field is Galois over `ℚ`, then its correspondent is Galois and is *literally
the same intermediate field* of `Omega`. -/
theorem normal_correspondingField_fixed
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (K₁ : NumberFieldExtension F₁)
    [IsGalois ℚ K₁.field.field] :
    IsGalois ℚ (correspondingField theta K₁).field ∧
      K₁.field.field = (correspondingField theta K₁).field := by
  let K₂ := correspondingField theta K₁
  have hsets := corresponding_primeSets theta K₁
  have hcrit₂ : ∀ q, q ∉ (∅ : Finset (NU.Chebotarev.PrimeIdeal ℚ)) →
      q ∈ degreeOneRationalPrimeSet K₂ → SplitsCompletelyAt K₂ q := by
    intro q _ hq₂
    have hq₁ : q ∈ degreeOneRationalPrimeSet K₁.field := by
      rw [hsets.1]
      exact hq₂
    have hs₁ : q ∈ splitPrimeSet K₁.field :=
      splitsCompletelyAt_of_degreeOne_of_isGalois K₁.field q hq₁
    have hs₂ : q ∈ splitPrimeSet K₂ := by
      rw [← hsets.2]
      exact hs₁
    exact hs₂
  have hgal₂ : IsGalois ℚ K₂.field :=
    galois_of_degreeOnePrime_splitsCompletely K₂ ∅ hcrit₂
  letI : IsGalois ℚ K₂.field := hgal₂
  have h₁₂ : K₁.field.field ≤ K₂.field := by
    apply chebotarev_containment K₁.field K₂ ∅
    intro q _ hq₂
    have hq₁ : q ∈ degreeOneRationalPrimeSet K₁.field := by
      rw [hsets.1]
      exact hq₂
    exact splitsCompletelyAt_of_degreeOne_of_isGalois K₁.field q hq₁
  have h₂₁ : K₂.field ≤ K₁.field.field := by
    apply chebotarev_containment K₂ K₁.field ∅
    intro q _ hq₁
    have hq₂ : q ∈ degreeOneRationalPrimeSet K₂ := by
      rw [← hsets.1]
      exact hq₁
    exact splitsCompletelyAt_of_degreeOne_of_isGalois K₂ q hq₂
  exact ⟨hgal₂, le_antisymm h₁₂ h₂₁⟩

/-- Blueprint Corollary `cor:normal-subgroup-fixed`: every common finite
Galois level containing both base fields is preserved by `theta`, so the
named quotient isomorphism is available. -/
theorem normalLevel_fixed
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field] :
    PreservesNormalLevel theta N h₁ h₂ := by
  let K : NumberFieldExtension F₁ := ⟨N, h₁⟩
  have hfield : N.field = (correspondingField theta K).field :=
    (normal_correspondingField_fixed theta K).2
  have hgroups : absoluteGaloisGroup (correspondingField theta K) =
      absoluteGaloisGroup N := by
    unfold absoluteGaloisGroup
    rw [← hfield]
  have hout :
      Subgroup.map (absoluteGaloisGroup F₂).subtype
          (Subgroup.map theta.toMulEquiv.toMonoidHom
            ((absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₁))) =
        Subgroup.map (absoluteGaloisGroup F₂).subtype
          ((absoluteGaloisGroup N).subgroupOf (absoluteGaloisGroup F₂)) := by
    calc
      _ = absoluteGaloisGroup (correspondingField theta K) :=
        (fixingSubgroup_correspondingField theta K).symm
      _ = absoluteGaloisGroup N := hgroups
      _ = _ := (Subgroup.map_subgroupOf_eq_of_le
        (absoluteGaloisGroup_mono h₂)).symm
  exact Subgroup.map_injective
    (absoluteGaloisGroup F₂).subtype_injective hout

/-- The quotient isomorphism at a common normal field, named as
`theta_N` in blueprint `cor:normal-subgroup-fixed`. -/
noncomputable def normalLevelQuotientIso
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field] :
    relativeGaloisGroup F₁ N h₁ ≃* relativeGaloisGroup F₂ N h₂ :=
  finiteQuotientIso theta N h₁ h₂
    (normalLevel_fixed theta N h₁ h₂)

/-- Defining restriction equation for `theta_N`. -/
@[simp]
theorem normalLevelQuotientIso_comp_restriction
    {F₁ F₂ : NumberFieldInOmega}
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (N : NumberFieldInOmega)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (g : absoluteGaloisGroup F₁) :
    normalLevelQuotientIso theta N h₁ h₂
        (finiteQuotientMap F₁ N h₁ g) =
      finiteQuotientMap F₂ N h₂ (theta g) :=
  finiteQuotientIso_comp_restriction theta N h₁ h₂
    (normalLevel_fixed theta N h₁ h₂) g

end

end NU.NeukirchUchida
