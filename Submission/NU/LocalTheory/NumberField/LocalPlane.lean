import Submission.NU.LocalTheory.NumberField.ValuationBridge

/-!
# Local quotients and local two-planes

This module states the split local quotient of Blueprint (4.1) and the
finite-field dimension computation of Lemma 4.2.  No henselianity of the
global localization is assumed.
-/

open scoped NumberField

namespace NU.LocalTheory

noncomputable section

private theorem valuationOfNeZero_surjective
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    Function.Surjective
      (v.valuationOfNeZero : Kˣ →* Multiplicative ℤ) := by
  intro z
  obtain ⟨x, hx⟩ := v.valuation_surjective K
    (z : WithZero (Multiplicative ℤ))
  have hx0 : x ≠ 0 := by
    apply (Valuation.ne_zero_iff (v.valuation K)).mp
    rw [hx]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply WithZero.coe_injective
  simpa only [v.valuationOfNeZero_eq, Units.val_mk0] using hx

private theorem unitGroup_eq_ker_valuationOfNeZero
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    (primeValuationSubring v).unitGroup =
      v.valuationOfNeZero.ker := by
  ext x
  rw [primeValuationSubring,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_unitGroup_iff, MonoidHom.mem_ker]
  constructor
  · intro h
    apply WithZero.coe_injective
    simpa only [v.valuationOfNeZero_eq, WithZero.coe_one] using h
  · intro h
    apply_fun ((↑) : Multiplicative ℤ →
      WithZero (Multiplicative ℤ)) at h
    simpa only [v.valuationOfNeZero_eq, WithZero.coe_one] using h

/-- Blueprint (4.1), `eq:local-quotient-exact`: after choosing a
uniformizer, `Kˣ/U_v¹` is the product of the residue-field units and the
value group `ℤ`.  `Nonempty` records the noncanonical splitting. -/
theorem local_quotient_exact {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) :
    Nonempty
      ((Kˣ ⧸ (primeValuationSubring v).principalUnitGroup) ≃*
        ((ResidueFieldAt v)ˣ × Multiplicative ℤ)) := by
  let A := primeValuationSubring v
  let ord : Kˣ →* Multiplicative ℤ := v.valuationOfNeZero
  have hord_surj : Function.Surjective ord :=
    valuationOfNeZero_surjective v
  obtain ⟨π, hπ⟩ := hord_surj (Multiplicative.ofAdd 1)
  let sec : Multiplicative ℤ →* Kˣ := zpowersHom Kˣ π
  have hsec : Function.RightInverse sec ord := by
    intro z
    apply Multiplicative.toAdd.injective
    simp [sec, hπ]
  have hU : A.unitGroup = ord.ker :=
    unitGroup_eq_ker_valuationOfNeZero v
  let unitPart : Kˣ →* A.unitGroup :=
    { toFun := fun x => ⟨x * (sec (ord x))⁻¹, by
        rw [hU, MonoidHom.mem_ker, map_mul, map_inv, hsec,
          mul_inv_cancel]
      ⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        ac_rfl }
  let residuePart : Kˣ →* (ResidueFieldAt v)ˣ :=
    A.unitGroupToResidueFieldUnits.comp unitPart
  let phi : Kˣ →* ((ResidueFieldAt v)ˣ × Multiplicative ℤ) :=
    residuePart.prod ord
  have hker : phi.ker = A.principalUnitGroup := by
    ext x
    constructor
    · intro hx
      have hpair : phi x = 1 := MonoidHom.mem_ker.mp hx
      have hxord : ord x = 1 := congr_arg Prod.snd hpair
      have hxU : x ∈ A.unitGroup := by
        rw [hU, MonoidHom.mem_ker]
        exact hxord
      have hunitPart :
          unitPart x = (⟨x, hxU⟩ : A.unitGroup) := by
        apply Subtype.ext
        simp [unitPart, hxord]
      have hres : residuePart x = 1 := congr_arg Prod.fst hpair
      have hmapker : (⟨x, hxU⟩ : A.unitGroup) ∈
          A.unitGroupToResidueFieldUnits.ker := by
        rw [MonoidHom.mem_ker]
        simpa [residuePart, hunitPart] using hres
      rw [A.ker_unitGroupToResidueFieldUnits] at hmapker
      exact hmapker
    · intro hx
      rw [MonoidHom.mem_ker]
      apply Prod.ext
      · have hxU : x ∈ A.unitGroup :=
          A.principal_units_le_units hx
        have hxord : ord x = 1 := by
          rw [← MonoidHom.mem_ker, ← hU]
          exact hxU
        have hunitPart :
            unitPart x = (⟨x, hxU⟩ : A.unitGroup) := by
          apply Subtype.ext
          simp [unitPart, hxord]
        have hmapker : (⟨x, hxU⟩ : A.unitGroup) ∈
            A.unitGroupToResidueFieldUnits.ker := by
          rw [A.ker_unitGroupToResidueFieldUnits]
          exact hx
        simpa [phi, residuePart, hunitPart] using
          (MonoidHom.mem_ker.mp hmapker)
      · change ord x = 1
        rw [← MonoidHom.mem_ker, ← hU]
        exact A.principal_units_le_units hx
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨r, z⟩
    obtain ⟨u, hu⟩ :=
      A.surjective_unitGroupToResidueFieldUnits r
    have huord : ord (u : Kˣ) = 1 := by
      rw [← MonoidHom.mem_ker, ← hU]
      exact u.prop
    let x : Kˣ := (u : Kˣ) * sec z
    have hxord : ord x = z := by
      rw [show x = (u : Kˣ) * sec z by rfl, map_mul, huord,
        one_mul, hsec]
    have hunitPart : unitPart x = u := by
      apply Subtype.ext
      simp [unitPart, x, hxord]
    refine ⟨x, ?_⟩
    apply Prod.ext
    · simpa [phi, residuePart, hunitPart] using hu
    · simpa [phi] using hxord
  let barPhi : (Kˣ ⧸ A.principalUnitGroup) →*
      ((ResidueFieldAt v)ˣ × Multiplicative ℤ) :=
    QuotientGroup.lift A.principalUnitGroup phi (by
      rw [← hker])
  have hbar_surj : Function.Surjective barPhi := by
    intro y
    obtain ⟨x, hx⟩ := hphi_surj y
    exact ⟨QuotientGroup.mk x, by simpa [barPhi] using hx⟩
  have hbar_ker : barPhi.ker = ⊥ := by
    ext q
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ :=
        QuotientGroup.mk'_surjective A.principalUnitGroup q
      have hxphi : phi x = 1 := by
        simpa [barPhi] using MonoidHom.mem_ker.mp hq
      have hxP : x ∈ A.principalUnitGroup := by
        rw [← hker, MonoidHom.mem_ker]
        exact hxphi
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff x).mpr hxP
    · intro hq
      rw [Subgroup.mem_bot] at hq
      subst q
      exact Subgroup.one_mem _
  exact ⟨MulEquiv.ofBijective barPhi
    ⟨(MonoidHom.ker_eq_bot_iff barPhi).mp hbar_ker,
      hbar_surj⟩⟩

private def addEquivToZModLinearEquiv {n : ℕ}
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (e : M ≃+ N) :
    M ≃ₗ[ZMod n] N :=
  e.toLinearEquiv (ZMod.map_smul e.toAddMonoidHom)

private def modNMap {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (f : G →+ H) : ModN G n →ₗ[ZMod n] ModN H n :=
  (ModN.liftEquiv').symm ⟨(ModN.mkQ n).comp f, by
    intro g
    change n • ModN.mkQ n (f g) = 0
    rw [← map_nsmul]
    change (LinearMap.range (LinearMap.lsmul ℤ H (n : ℤ))).mkQ
      (n • f g) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨f g, by simp⟩⟩

@[simp]
private theorem modNMap_mkQ {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] (n : ℕ) (f : G →+ H) (g : G) :
    modNMap n f (ModN.mkQ n g) = ModN.mkQ n (f g) := by
  rfl

private theorem modN_mkQ_surjective {G : Type*} [AddCommGroup G]
    (n : ℕ) : Function.Surjective (ModN.mkQ n : G →+ ModN G n) :=
  QuotientAddGroup.mk'_surjective _

private def modNLinearEquiv {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] (n : ℕ) (e : G ≃+ H) :
    ModN G n ≃ₗ[ZMod n] ModN H n :=
  { modNMap n e.toAddMonoidHom with
    invFun := modNMap n e.symm.toAddMonoidHom
    left_inv := by
      intro x
      obtain ⟨g, rfl⟩ :=
        (LinearMap.range
          (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective x
      change modNMap n e.symm.toAddMonoidHom
        (modNMap n e.toAddMonoidHom (ModN.mkQ n g)) = ModN.mkQ n g
      rw [modNMap_mkQ, modNMap_mkQ]
      simp
    right_inv := by
      intro x
      obtain ⟨h, rfl⟩ :=
        (LinearMap.range
          (LinearMap.lsmul ℤ H (n : ℤ))).mkQ_surjective x
      change modNMap n e.toAddMonoidHom
        (modNMap n e.symm.toAddMonoidHom (ModN.mkQ n h)) = ModN.mkQ n h
      rw [modNMap_mkQ, modNMap_mkQ]
      simp }

private def modNProdLinearEquiv {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] (n : ℕ) :
    ModN (G × H) n ≃ₗ[ZMod n] (ModN G n × ModN H n) := by
  let NG : AddSubgroup G :=
    (LinearMap.range (LinearMap.lsmul ℤ G (n : ℤ))).toAddSubgroup
  let NH : AddSubgroup H :=
    (LinearMap.range (LinearMap.lsmul ℤ H (n : ℤ))).toAddSubgroup
  let NGH : AddSubgroup (G × H) :=
    (LinearMap.range
      (LinearMap.lsmul ℤ (G × H) (n : ℤ))).toAddSubgroup
  have hrange : NGH = NG.prod NH := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
    · rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
      change (n : ℤ) • g = x.1 at hg
      change (n : ℤ) • h = x.2 at hh
      refine ⟨(g, h), ?_⟩
      change ((n : ℤ) • g, (n : ℤ) • h) = x
      exact Prod.ext hg hh
  let e : ModN (G × H) n ≃+ (ModN G n × ModN H n) :=
    (QuotientAddGroup.quotientAddEquivOfEq hrange).trans
      (QuotientAddGroup.prodAddEquiv NG NH)
  exact addEquivToZModLinearEquiv e

private def modNIntLinearEquiv (n : ℕ) :
    ModN ℤ n ≃ₗ[ZMod n] ZMod n := by
  let N : AddSubgroup ℤ :=
    (LinearMap.range (LinearMap.lsmul ℤ ℤ (n : ℤ))).toAddSubgroup
  have hrange : N = AddSubgroup.zmultiples (n : ℤ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [mul_comm]⟩
  let e : ModN ℤ n ≃+ ZMod n :=
    (QuotientAddGroup.quotientAddEquivOfEq hrange).trans
      (Int.quotientZMultiplesNatEquivZMod n)
  exact addEquivToZModLinearEquiv e

private def additiveProdSwapEquiv {G H : Type*} [CommGroup G]
    [CommGroup H] : Additive (G × H) ≃+ (Additive H × Additive G) where
  toFun x := (Additive.ofMul x.toMul.2, Additive.ofMul x.toMul.1)
  invFun x := Additive.ofMul (x.2.toMul, x.1.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def additiveMultiplicativeIntEquiv :
    Additive (Multiplicative ℤ) ≃+ ℤ where
  toFun x := x.toMul.toAdd
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The mod-`n` form of the split local quotient. -/
theorem local_quotient_mod_ell {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (n : ℕ) :
    Nonempty
      (PrincipalUnitModEll (primeValuationSubring v) n ≃ₗ[ZMod n]
        (ZMod n × ResidueUnitModEll v n)) := by
  obtain ⟨e⟩ := local_quotient_exact v
  let ea :
      Additive (Kˣ ⧸ (primeValuationSubring v).principalUnitGroup) ≃+
        (ℤ × Additive (ResidueFieldAt v)ˣ) :=
    (MulEquiv.toAdditive e).trans <|
      additiveProdSwapEquiv.trans <|
        additiveMultiplicativeIntEquiv.prodCongr (AddEquiv.refl _)
  exact ⟨(modNLinearEquiv n ea).trans <|
    (modNProdLinearEquiv n).trans <|
      (modNIntLinearEquiv n).prodCongr (LinearEquiv.refl _ _)⟩

private def additiveQuotientMk {G : Type*} [CommGroup G]
    (S : Subgroup G) : Additive G →+ Additive (G ⧸ S) where
  toFun x := Additive.ofMul (QuotientGroup.mk x.toMul)
  map_zero' := by simp
  map_add' _ _ := rfl

private def annihilatorQuotientCharacter
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (p : annihilator n S) : Additive (Fˣ ⧸ S) →+ ZMod n := by
  let pmul : Fˣ →* Multiplicative (ZMod n) :=
    { toFun := fun x => Multiplicative.ofAdd
        ((p : MulCharacter F n) (Additive.ofMul x))
      map_one' := by simp
      map_mul' := by
        intro x y
        simpa using (p : MulCharacter F n).map_add
          (Additive.ofMul x) (Additive.ofMul y) }
  let qmul : (Fˣ ⧸ S) →* Multiplicative (ZMod n) :=
    QuotientGroup.lift S pmul (by
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

@[simp]
private theorem annihilatorQuotientCharacter_mk
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (p : annihilator n S) (x : Fˣ) :
    annihilatorQuotientCharacter S p
      (Additive.ofMul (QuotientGroup.mk x)) =
        (p : MulCharacter F n) (Additive.ofMul x) := by
  rfl

private def annihilatorToDual
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (p : annihilator n S) :
    ModN (Additive (Fˣ ⧸ S)) n →ₗ[ZMod n] ZMod n :=
  (ModN.liftEquiv').symm
    ⟨annihilatorQuotientCharacter S p, by
      intro x
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), CharP.cast_eq_zero,
        zero_smul]⟩

@[simp]
private theorem annihilatorToDual_mk
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (p : annihilator n S) (x : Fˣ) :
    annihilatorToDual S p
      (ModN.mkQ n (Additive.ofMul (QuotientGroup.mk x))) =
        (p : MulCharacter F n) (Additive.ofMul x) := by
  rfl

private def dualToAnnihilator
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (L : ModN (Additive (Fˣ ⧸ S)) n →ₗ[ZMod n] ZMod n) :
    annihilator n S :=
  ⟨L.toAddMonoidHom.comp
      ((ModN.mkQ n).comp (additiveQuotientMk S)), by
    intro x hx
    change L (ModN.mkQ n (Additive.ofMul (QuotientGroup.mk x))) = 0
    have hqx : (QuotientGroup.mk x : Fˣ ⧸ S) = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    simp⟩

@[simp]
private theorem dualToAnnihilator_apply
    {F : Type*} [Field F] {n : ℕ} (S : Subgroup Fˣ)
    (L : ModN (Additive (Fˣ ⧸ S)) n →ₗ[ZMod n] ZMod n)
    (x : Fˣ) :
    (dualToAnnihilator S L : MulCharacter F n) (Additive.ofMul x) =
      L (ModN.mkQ n (Additive.ofMul (QuotientGroup.mk x))) :=
  rfl

private def annihilatorEquivDual
    {F : Type*} [Field F] {n : ℕ} [Fact n.Prime]
    (S : Subgroup Fˣ) :
    annihilator n S ≃ₗ[ZMod n]
      (ModN (Additive (Fˣ ⧸ S)) n →ₗ[ZMod n] ZMod n) :=
  { toFun := annihilatorToDual S
    map_add' := by
      intro p q
      apply LinearMap.ext
      intro z
      obtain ⟨g, rfl⟩ := modN_mkQ_surjective n z
      cases g with
      | ofMul g =>
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
        rfl
    map_smul' := by
      intro c p
      apply LinearMap.ext
      intro z
      obtain ⟨g, rfl⟩ := modN_mkQ_surjective n z
      cases g with
      | ofMul g =>
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
        rfl
    invFun := dualToAnnihilator S
    left_inv := by
      intro p
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      rfl
    right_inv := by
      intro L
      apply LinearMap.ext
      intro z
      obtain ⟨g, rfl⟩ := modN_mkQ_surjective n z
      cases g with
      | ofMul g =>
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
        rfl }

private theorem finrank_annihilator_eq_modN_quotient
    {F : Type*} [Field F] {n : ℕ} [Fact n.Prime]
    (S : Subgroup Fˣ) [Finite (ModN (Additive (Fˣ ⧸ S)) n)] :
    Module.finrank (ZMod n) (annihilator n S) =
      Module.finrank (ZMod n) (ModN (Additive (Fˣ ⧸ S)) n) := by
  rw [(annihilatorEquivDual S).finrank_eq,
    Module.finrank_linearMap, Module.finrank_self, mul_one]

private theorem natCard_modN_eq_gcd
    {G : Type*} [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (n : ℕ) : Nat.card (ModN G n) = (Nat.card G).gcd n := by
  let N : AddSubgroup G :=
    (LinearMap.range (LinearMap.lsmul ℤ G (n : ℤ))).toAddSubgroup
  change Nat.card (G ⧸ N) = (Nat.card G).gcd n
  rw [← N.index_eq_card]
  have hN : N = (nsmulAddMonoidHom n).range := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change n • y = x
      simpa using hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change (n : ℤ) • y = x
      simpa using hy
  rw [hN, IsAddCyclic.index_nsmulAddMonoidHom_range]

private noncomputable def quotientEquivResidueFieldAt
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    (𝓞 K ⧸ v.asIdeal) ≃+* ResidueFieldAt v := by
  change (𝓞 K ⧸ v.asIdeal) ≃+*
    IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)

private theorem residueFieldAt_finite
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    Finite (ResidueFieldAt v) :=
  Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (quotientEquivResidueFieldAt v).toEquiv

private theorem absNorm_eq_natCard_residueFieldAt
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    Ideal.absNorm v.asIdeal = Nat.card (ResidueFieldAt v) := by
  calc
    Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = Nat.card (ResidueFieldAt v) :=
      Nat.card_congr (quotientEquivResidueFieldAt v).toEquiv

private theorem finrank_eq_of_natCard_eq_prime_pow
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {d : ℕ}
    (hcard : Nat.card V = p ^ d) :
    Module.finrank (ZMod p) V = d := by
  letI := Fintype.ofFinite (ZMod p)
  letI := Fintype.ofFinite V
  apply Nat.pow_right_injective ((Fact.out : Nat.Prime p).two_le)
  have hdim : Fintype.card V =
      p ^ Module.finrank (ZMod p) V := by
    simpa only [ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := V))
  calc
    p ^ Module.finrank (ZMod p) V = Fintype.card V := hdim.symm
    _ = Nat.card V := Nat.card_eq_fintype_card.symm
    _ = p ^ d := hcard

private theorem residueUnitModEll_finite
    {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (n : ℕ) :
    Finite (ResidueUnitModEll v n) := by
  let k := ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite v
  letI : Finite (Additive kˣ) := inferInstance
  exact Finite.of_surjective (ModN.mkQ n)
    (QuotientAddGroup.mk'_surjective _)

private theorem residueUnitModEll_finrank_eq_zero
    {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (v : FinitePlace K)
    (hv : residueCharacteristic v = ℓ) :
    Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) = 0 := by
  let k := ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite v
  letI := Fintype.ofFinite k
  letI : Finite (Additive kˣ) := inferInstance
  letI : Finite (ResidueUnitModEll v ℓ) :=
    residueUnitModEll_finite v ℓ
  have hcardMod : Nat.card (ResidueUnitModEll v ℓ) =
      (Nat.card kˣ).gcd ℓ := natCard_modN_eq_gcd ℓ
  apply finrank_eq_of_natCard_eq_prime_pow (d := 0)
  rw [hcardMod, Nat.card_units]
  obtain ⟨d, hp, hkcard⟩ :=
    FiniteField.card k (residueCharacteristic v)
  have hkpos : 0 < Nat.card k := Nat.card_pos
  have hkcard' : Nat.card k =
      residueCharacteristic v ^ (d : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hkcard
  have hconsecutive : (Nat.card k - 1).Coprime (Nat.card k) := by
    have hq : Nat.card k = 1 + (Nat.card k - 1) := by omega
    nth_rewrite 2 [hq]
    rw [Nat.coprime_add_self_right]
    exact Nat.coprime_one_right _
  have hell_dvd : ℓ ∣ Nat.card k := by
    rw [hkcard', hv]
    exact dvd_pow_self ℓ d.ne_zero
  have hcop : (Nat.card k - 1).Coprime ℓ :=
    Nat.Coprime.of_dvd_right hell_dvd hconsecutive
  rw [hcop.gcd_eq_one]
  rfl

private theorem residueUnitModEll_finrank_eq_one
    {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace K) (hv : residueCharacteristic v ≠ ℓ) :
    Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) = 1 := by
  let k := ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite v
  letI := Fintype.ofFinite k
  letI : Finite (Additive kˣ) := inferInstance
  letI : Finite (ResidueUnitModEll v ℓ) :=
    residueUnitModEll_finite v ℓ
  have hcardMod : Nat.card (ResidueUnitModEll v ℓ) =
      (Nat.card kˣ).gcd ℓ := natCard_modN_eq_gcd ℓ
  apply finrank_eq_of_natCard_eq_prime_pow (d := 1)
  rw [hcardMod]
  have hnorm : Ideal.absNorm v.asIdeal = Nat.card k :=
    absNorm_eq_natCard_residueFieldAt v
  obtain ⟨d, hp, hkcard⟩ :=
    FiniteField.card k (residueCharacteristic v)
  have hkcard' : Nat.card k =
      residueCharacteristic v ^ (d : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hkcard
  have hprimeCoprime : (residueCharacteristic v).Coprime ℓ :=
    (Nat.coprime_primes hp (Fact.out : Nat.Prime ℓ)).mpr hv
  have hnormCoprime : (Ideal.absNorm v.asIdeal).Coprime ℓ := by
    rw [hnorm, hkcard']
    exact hprimeCoprime.pow_left d
  have hnorm_ne_one : Ideal.absNorm v.asIdeal ≠ 1 :=
    Ideal.absNorm_eq_one_iff.not.mpr v.isMaximal.ne_top
  let e : (𝓞 K ⧸ v.asIdeal) ≃+* k :=
    quotientEquivResidueFieldAt v
  have hrootQuot : IsPrimitiveRoot
      (Ideal.Quotient.mk v.asIdeal hζ.toInteger) ℓ :=
    hζ.toInteger_isPrimitiveRoot.idealQuotient_mk hnorm_ne_one
      hnormCoprime
  have hroot : IsPrimitiveRoot
      (e (Ideal.Quotient.mk v.asIdeal hζ.toInteger)) ℓ :=
    hrootQuot.map_of_injective e.injective
  let u : kˣ := Units.mk0
    (e (Ideal.Quotient.mk v.asIdeal hζ.toInteger))
    (hroot.ne_zero (Fact.out : Nat.Prime ℓ).ne_zero)
  have huroot : IsPrimitiveRoot u ℓ := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [u] using hroot
  have hell_dvd : ℓ ∣ Nat.card kˣ := by
    rw [huroot.eq_orderOf]
    exact orderOf_dvd_natCard u
  rw [Nat.gcd_eq_right_iff_dvd.mpr hell_dvd]
  simp

private theorem residueUnitModEll_finrank
    {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace K) :
    Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) =
      if residueCharacteristic v = ℓ then 0 else 1 := by
  by_cases hv : residueCharacteristic v = ℓ
  · simpa [hv] using residueUnitModEll_finrank_eq_zero v hv
  · simpa [hv] using residueUnitModEll_finrank_eq_one ζ hζ v hv

private noncomputable def unitQuotientModEllEquivZMod
    {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) (n : ℕ) :
    ModN (Additive (Kˣ ⧸ (primeValuationSubring v).unitGroup)) n ≃ₗ[ZMod n]
      ZMod n := by
  let A := primeValuationSubring v
  let ord : Kˣ →* Multiplicative ℤ := v.valuationOfNeZero
  have hord : Function.Surjective ord := valuationOfNeZero_surjective v
  have hker : A.unitGroup = ord.ker :=
    unitGroup_eq_ker_valuationOfNeZero v
  let emul : (Kˣ ⧸ A.unitGroup) ≃* Multiplicative ℤ :=
    QuotientGroup.liftEquiv A.unitGroup hord hker
  let eadd : Additive (Kˣ ⧸ A.unitGroup) ≃+ ℤ :=
    (MulEquiv.toAdditive emul).trans additiveMultiplicativeIntEquiv
  exact (modNLinearEquiv n eadd).trans (modNIntLinearEquiv n)

private theorem localI_finrank_eq_one
    {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (v : FinitePlace K) :
    Module.finrank (ZMod ℓ) (localI ℓ (primeValuationSubring v)) = 1 := by
  let Q := ModN
    (Additive (Kˣ ⧸ (primeValuationSubring v).unitGroup)) ℓ
  let e : Q ≃ₗ[ZMod ℓ] ZMod ℓ :=
    unitQuotientModEllEquivZMod v ℓ
  letI : Finite Q := Finite.of_equiv (ZMod ℓ) e.symm.toEquiv
  calc
    Module.finrank (ZMod ℓ) (localI ℓ (primeValuationSubring v)) =
        Module.finrank (ZMod ℓ) Q := by
      exact finrank_annihilator_eq_modN_quotient
        (primeValuationSubring v).unitGroup
    _ = Module.finrank (ZMod ℓ) (ZMod ℓ) := e.finrank_eq
    _ = 1 := Module.finrank_self _

private theorem localD_finrank_eq_one_add_residue
    {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (v : FinitePlace K) :
    Module.finrank (ZMod ℓ) (localD ℓ (primeValuationSubring v)) =
      1 + Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) := by
  let k := ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite v
  letI : Finite (Additive kˣ) := inferInstance
  letI : Finite (ResidueUnitModEll v ℓ) :=
    residueUnitModEll_finite v ℓ
  let Q := PrincipalUnitModEll (primeValuationSubring v) ℓ
  let e : Q ≃ₗ[ZMod ℓ] (ZMod ℓ × ResidueUnitModEll v ℓ) :=
    (local_quotient_mod_ell v ℓ).some
  letI : Finite Q :=
    Finite.of_equiv (ZMod ℓ × ResidueUnitModEll v ℓ) e.symm.toEquiv
  calc
    Module.finrank (ZMod ℓ) (localD ℓ (primeValuationSubring v)) =
        Module.finrank (ZMod ℓ) Q := by
      exact finrank_annihilator_eq_modN_quotient
        (primeValuationSubring v).principalUnitGroup
    _ = Module.finrank (ZMod ℓ)
        (ZMod ℓ × ResidueUnitModEll v ℓ) := e.finrank_eq
    _ = Module.finrank (ZMod ℓ) (ZMod ℓ) +
        Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) :=
      Module.finrank_prod
    _ = 1 + Module.finrank (ZMod ℓ) (ResidueUnitModEll v ℓ) := by
      rw [Module.finrank_self]

/-- Blueprint Lemma 4.2 (`lem:local-dimensions`).  The inertia line always
has dimension one.  The principal-unit annihilator has dimension two away
from residue characteristic `ℓ` and dimension one at residue characteristic
`ℓ`.  The primitive root hypothesis is what supplies the residue-unit line
in the tame case. -/
theorem local_dimensions {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace K) :
    Module.finrank (ZMod ℓ) (localI ℓ (primeValuationSubring v)) = 1 ∧
      Module.finrank (ZMod ℓ) (localD ℓ (primeValuationSubring v)) =
        if residueCharacteristic v = ℓ then 1 else 2 := by
  refine ⟨localI_finrank_eq_one v, ?_⟩
  rw [localD_finrank_eq_one_add_residue,
    residueUnitModEll_finrank ζ hζ v]
  by_cases hv : residueCharacteristic v = ℓ <;> simp [hv]

/-- Away from `ℓ`, the local principal-unit annihilator is a genuine
cohomological two-plane. -/
theorem localD_finrank_eq_two {K : Type*} [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace K) (hv : residueCharacteristic v ≠ ℓ) :
    Module.finrank (ZMod ℓ) (localD ℓ (primeValuationSubring v)) = 2 := by
  rw [localD_finrank_eq_one_add_residue,
    residueUnitModEll_finrank_eq_one ζ hζ v hv]

/-- In residue characteristic `ℓ`, no independent two-plane can lie in
`𝔇_v^ℓ`. -/
theorem localD_finrank_eq_one_of_residueChar {K : Type*} [Field K]
    [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
    (v : FinitePlace K) (hv : residueCharacteristic v = ℓ) :
    Module.finrank (ZMod ℓ) (localD ℓ (primeValuationSubring v)) = 1 := by
  rw [localD_finrank_eq_one_add_residue,
    residueUnitModEll_finrank_eq_zero v hv]

end

end NU.LocalTheory
