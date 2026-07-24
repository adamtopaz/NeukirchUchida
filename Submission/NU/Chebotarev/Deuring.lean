import Submission.NU.Chebotarev.Frobenius

/-!
# M3. Deuring reduction

Blueprint §4. The exact degree-one fiber count is deliberately separated from
the `O(x^(1/2))` exceptional-prime estimate, as required by §10.5(2).
-/

open Filter Topology
open scoped Pointwise

namespace NU.Chebotarev

variable {K L : Type*} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The fixed field `E = L^⟨g⟩` in Deuring's reduction (blueprint §4). -/
abbrev deuringFixedField (g : Gal(L/K)) : Type _ :=
  ↥(IntermediateField.fixedField (Subgroup.zpowers g))

/-- The integer `n_g = |C_G(g)| / |⟨g⟩|` from blueprint Proposition 4.1. -/
noncomputable def deuringFactor (g : Gal(L/K)) : ℕ :=
  Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) / orderOf g

/-- The prime set `Q_g` over `E = L^⟨g⟩`. Frobenius over `E` is kept as an
element and then included into `Gal(L/K)` (blueprint §4 and §10.5(1)). -/
def deuringUpstairsPrimeSet (g : Gal(L/K)) :
    Set (PrimeIdeal (deuringFixedField g)) :=
  {q | IsUnramifiedPrime (K := deuringFixedField g) (L := L) q ∧
    ∃ P : PrimeIdeal L,
      P.asIdeal.LiesOver q.asIdeal ∧
      AlgEquiv.restrictScalarsHom K
        (arithFrobeniusAt (K := deuringFixedField g) (L := L) P) = g}

/-- The degree-one subset `Q_g^(1)` used for the exact Deuring map: both
ramification index and residue degree over `K` are one. -/
def deuringDegreeOnePrimeSet (g : Gal(L/K)) :
    Set (PrimeIdeal (deuringFixedField g)) :=
  {q | q ∈ deuringUpstairsPrimeSet g ∧
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
    q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1}

private theorem frobenius_eq_of_isArith (P : PrimeIdeal L)
    (hunr : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal)
    (s : Gal(L/K))
    (hs : IsArithFrobAt (NumberField.RingOfIntegers K) s P.asIdeal) :
    s = arithFrobeniusAt (K := K) (L := L) P := by
  letI : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal := hunr
  have hfield : s.toRingEquiv.toRingHom =
      (arithFrobeniusAt (K := K) (L := L) P).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers L)
    intro x
    have heq := hs.eq_of_isUnramifiedAt
      (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
        (Gal(L/K)) P.asIdeal) P.asIdeal.primeCompl_le_nonZeroDivisors
    exact congrArg Subtype.val (DFunLike.congr_fun heq x)
  ext x
  exact DFunLike.congr_fun hfield x

private theorem frobenius_smul (P : PrimeIdeal L)
    (hunr : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal)
    (s : Gal(L/K)) :
    arithFrobeniusAt (K := K) (L := L)
      ⟨s • P.asIdeal, inferInstance, by
        intro h
        apply P.ne_bot
        have h' := congrArg (s⁻¹ • ·) h
        simpa only [smul_smul, inv_mul_cancel, one_smul, Ideal.smul_bot] using h'⟩ =
      s * arithFrobeniusAt (K := K) (L := L) P * s⁻¹ := by
  have hne : s • P.asIdeal ≠ ⊥ := by
    intro h
    have h' := congrArg (s⁻¹ • ·) h
    apply P.ne_bot
    simpa only [smul_smul, inv_mul_cancel, one_smul, Ideal.smul_bot] using h'
  let Q : PrimeIdeal L := ⟨s • P.asIdeal, inferInstance, hne⟩
  have hunrQ : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal := by
    rw [← Ideal.ramificationIdx_eq_one_iff]
    rw [Ideal.ramificationIdx_smul]
    letI : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal := hunr
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  symm
  apply frobenius_eq_of_isArith Q hunrQ
  exact (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
    (Gal(L/K)) P.asIdeal).conj s

private theorem fixedField_contraction_degreeOne
    (g : Gal(L/K)) (p : PrimeIdeal K) (P : PrimeIdeal L)
    (hPp : P.asIdeal.LiesOver p.asIdeal)
    (hunr : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal)
    (hfrob : arithFrobeniusAt (K := K) (L := L) P = g) :
    let q : PrimeIdeal (deuringFixedField g) :=
      ⟨P.asIdeal.under (NumberField.RingOfIntegers (deuringFixedField g)),
        inferInstance, by
          intro h
          letI : P.asIdeal.LiesOver
              (⊥ : Ideal (NumberField.RingOfIntegers (deuringFixedField g))) :=
            ⟨by simpa [h]⟩
          exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot
            (NumberField.RingOfIntegers (deuringFixedField g)) P.asIdeal)⟩
    q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 ∧
      (∀ Q : PrimeIdeal L, Q.asIdeal.LiesOver q.asIdeal → Q = P) := by
  let H := Subgroup.zpowers g
  let E := deuringFixedField g
  let q : PrimeIdeal E :=
    ⟨P.asIdeal.under (NumberField.RingOfIntegers E), inferInstance, by
      intro h
      letI : P.asIdeal.LiesOver (⊥ : Ideal (NumberField.RingOfIntegers E)) :=
        ⟨by simpa [h]⟩
      exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot
        (NumberField.RingOfIntegers E) P.asIdeal)⟩
  have hPq : P.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  letI : P.asIdeal.LiesOver q.asIdeal := hPq
  have hunrE : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers E) P.asIdeal := by
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := hunr
    exact Algebra.IsUnramifiedAt.of_restrictScalars
      (NumberField.RingOfIntegers K) P.asIdeal
  have heqD : decompositionSubgroup (K := K) (L := L) P = H := by
    simpa [H, hfrob] using arithFrobAt_generates_decomposition P hunr
  have hfix (s : Gal(L/E)) : s • P.asIdeal = P.asIdeal := by
    let r : Gal(L/K) := AlgEquiv.restrictScalarsHom K s
    have hrH : r ∈ H := by
      rw [← IntermediateField.fixingSubgroup_fixedField H]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact s.commutes ⟨x, hx⟩
    have hrD : r ∈ decompositionSubgroup (K := K) (L := L) P := by
      rw [heqD]
      exact hrH
    have hr : r • P.asIdeal = P.asIdeal :=
      (MulAction.mem_stabilizer_iff.mp hrD)
    exact hr
  have hstabE : decompositionSubgroup (K := E) (L := L) P = ⊤ := by
    ext s
    simp only [decompositionSubgroup, Subgroup.mem_top, iff_true]
    exact MulAction.mem_stabilizer_iff.mpr (hfix s)
  have hfPE : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) = orderOf g := by
    rw [← arithFrobAt_order_eq_inertiaDeg P hunrE]
    rw [← Nat.card_zpowers]
    rw [← arithFrobAt_generates_decomposition P hunrE, hstabE]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun _ : Gal(L/E) => Subgroup.mem_top _))]
    rw [IsGalois.card_aut_eq_finrank]
    rw [IntermediateField.finrank_fixedField_eq_card]
    rw [Nat.card_zpowers]
  have hfPK : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = orderOf g := by
    rw [← arithFrobAt_order_eq_inertiaDeg P hunr, hfrob]
  have hqf : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
    have ht := Ideal.inertiaDeg_tower
      (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers E)
      (T := NumberField.RingOfIntegers L) q.asIdeal P.asIdeal
    rw [hfPK, hfPE] at ht
    apply Nat.eq_of_mul_eq_mul_right (orderOf_pos g)
    simpa using ht.symm
  have hqe : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
    have hunrq : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) q.asIdeal := by
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers K) P.asIdeal := hunr
      exact Algebra.IsUnramifiedAt.of_liesOver
        (NumberField.RingOfIntegers K) q.asIdeal P.asIdeal
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) q.asIdeal := hunrq
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  refine ⟨hqe, hqf, ?_⟩
  intro Q hQq
  letI : Q.asIdeal.LiesOver q.asIdeal := hQq
  obtain ⟨s, hs⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    q.asIdeal P.asIdeal Q.asIdeal Gal(L/E)
  apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  rw [← hs, hfix]

private theorem isArithFrobAt_restrictScalars_of_inertiaDeg_one
    {E : Type*} [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [IsGalois E L]
    (P : PrimeIdeal L) (q : PrimeIdeal E)
    (hPq : P.asIdeal.LiesOver q.asIdeal)
    (hf : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1)
    (s : Gal(L/E))
    (hs : IsArithFrobAt (NumberField.RingOfIntegers E) s P.asIdeal) :
    IsArithFrobAt (NumberField.RingOfIntegers K)
      (AlgEquiv.restrictScalarsHom K s) P.asIdeal := by
  intro x
  have hcard : Nat.card (NumberField.RingOfIntegers K ⧸
        P.asIdeal.under (NumberField.RingOfIntegers K)) =
      Nat.card (NumberField.RingOfIntegers E ⧸
        P.asIdeal.under (NumberField.RingOfIntegers E)) := by
    change Ideal.absNorm (P.asIdeal.under (NumberField.RingOfIntegers K)) =
      Ideal.absNorm (P.asIdeal.under (NumberField.RingOfIntegers E))
    rw [← Ideal.under_under (B := NumberField.RingOfIntegers E) P.asIdeal,
      ← hPq.over]
    let p : PrimeIdeal K :=
      ⟨q.asIdeal.under (NumberField.RingOfIntegers K), inferInstance, by
        intro hp
        letI : q.asIdeal.LiesOver (⊥ : Ideal (NumberField.RingOfIntegers K)) :=
          ⟨by simpa [hp]⟩
        exact q.ne_bot (Ideal.eq_bot_of_liesOver_bot
          (NumberField.RingOfIntegers K) q.asIdeal)⟩
    have hnorm := PrimeIdeal.norm_pow_inertiaDeg q p (by
      change q.asIdeal.LiesOver (q.asIdeal.under (NumberField.RingOfIntegers K))
      exact ⟨rfl⟩)
    unfold PrimeIdeal.norm at hnorm
    rw [hf, pow_one] at hnorm
    exact hnorm.symm
  rw [hcard]
  exact hs x

/-- Blueprint Proposition 4.1, equation (2),
`deuring_degreeOne_fiber_card`: the contraction map on `Q_g^(1)` has exactly
`n_g` points over every prime with Frobenius class `[g]`. This is the exact
combinatorial statement, with no asymptotics mixed into it. -/
theorem deuring_degreeOne_fiber_card (g : Gal(L/K))
    (p : PrimeIdeal K)
    (hp : p ∈ frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)) :
    Nat.card {q : PrimeIdeal (deuringFixedField g) //
      q ∈ deuringDegreeOnePrimeSet g ∧
      q.asIdeal.under (NumberField.RingOfIntegers K) = p.asIdeal} =
      deuringFactor g := by
  classical
  let G := Gal(L/K)
  let H := Subgroup.zpowers g
  let C := Subgroup.centralizer ({g} : Set G)
  rcases hp with ⟨hunrp, P', hP'p, hclass⟩
  have hconj : IsConj (arithFrobeniusAt (K := K) (L := L) P') g := by
    exact ConjClasses.mk_eq_mk_iff_isConj.mp hclass
  obtain ⟨s, hs⟩ := isConj_iff.mp hconj
  have hsmulne : s • P'.asIdeal ≠ ⊥ := by
    intro h
    apply P'.ne_bot
    have h' := congrArg (s⁻¹ • ·) h
    simpa only [smul_smul, inv_mul_cancel, one_smul, Ideal.smul_bot] using h'
  let P0 : PrimeIdeal L := ⟨s • P'.asIdeal, inferInstance, hsmulne⟩
  have hP0p : P0.asIdeal.LiesOver p.asIdeal := by
    dsimp [P0]
    letI : P'.asIdeal.LiesOver p.asIdeal := hP'p
    infer_instance
  have hunrP' := hunrp P' hP'p
  have hunrP0 := hunrp P0 hP0p
  have hfrobP0 : arithFrobeniusAt (K := K) (L := L) P0 = g := by
    rw [frobenius_smul P' hunrP' s]
    exact hs
  let source := {P : PrimeIdeal L //
    P.asIdeal.LiesOver p.asIdeal ∧
      arithFrobeniusAt (K := K) (L := L) P = g}
  let toOrbit : source → MulAction.orbit C P0.asIdeal := fun P =>
    ⟨P.val.asIdeal, by
      letI : P0.asIdeal.LiesOver p.asIdeal := hP0p
      letI : P.val.asIdeal.LiesOver p.asIdeal := P.prop.1
      let hex := Ideal.exists_smul_eq_of_isGaloisGroup
        p.asIdeal P0.asIdeal P.val.asIdeal G
      let t := Classical.choose hex
      have ht := Classical.choose_spec hex
      have ht' : t * g * t⁻¹ = g := by
        have hf := frobenius_smul P0 hunrP0 t
        have hPt : (⟨t • P0.asIdeal, inferInstance, by
            intro h
            apply P0.ne_bot
            have h' := congrArg (t⁻¹ • ·) h
            simpa only [smul_smul, inv_mul_cancel, one_smul, Ideal.smul_bot] using h'⟩ :
            PrimeIdeal L) = P.val := by
          apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
          exact ht
        rw [hPt, hfrobP0, P.prop.2] at hf
        exact hf.symm
      have htC : t ∈ C := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        calc
          t * g = (t * g * t⁻¹) * t := by simp
          _ = g * t := by rw [ht']
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨⟨t, htC⟩, ?_⟩
      simpa only [Subgroup.smul_def] using ht⟩
  have htoOrbit_val (P : source) : (toOrbit P).val = P.val.asIdeal := rfl
  have htoOrbit_inj : Function.Injective toOrbit := by
    intro P Q hPQ
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    rw [← htoOrbit_val P, ← htoOrbit_val Q]
    exact congrArg Subtype.val hPQ
  have htoOrbit_surj : Function.Surjective toOrbit := by
    intro I
    obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp I.prop
    have htC : (t : G) ∈ C := t.prop
    have hne : (t : G) • P0.asIdeal ≠ ⊥ := by
      intro h
      apply P0.ne_bot
      have h' := congrArg ((t : G)⁻¹ • ·) h
      simpa only [smul_smul, inv_mul_cancel, one_smul, Ideal.smul_bot] using h'
    let Pt : PrimeIdeal L := ⟨(t : G) • P0.asIdeal, inferInstance, hne⟩
    have hPtp : Pt.asIdeal.LiesOver p.asIdeal := by
      dsimp [Pt]
      letI : P0.asIdeal.LiesOver p.asIdeal := hP0p
      infer_instance
    have hfrobPt : arithFrobeniusAt (K := K) (L := L) Pt = g := by
      rw [frobenius_smul P0 hunrP0 (t : G), hfrobP0]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp htC
      calc
        (t : G) * g * (t : G)⁻¹ = g * (t : G) * (t : G)⁻¹ := by rw [hc]
        _ = g := by simp
    let Pt' : source := ⟨Pt, hPtp, hfrobPt⟩
    refine ⟨Pt', ?_⟩
    apply Subtype.ext
    rw [htoOrbit_val]
    exact ht
  have hsource : Nat.card source = Nat.card (MulAction.orbit C P0.asIdeal) :=
    Nat.card_congr (Equiv.ofBijective toOrbit ⟨htoOrbit_inj, htoOrbit_surj⟩)
  let target := {q : PrimeIdeal (deuringFixedField g) //
    q ∈ deuringDegreeOnePrimeSet g ∧
      q.asIdeal.under (NumberField.RingOfIntegers K) = p.asIdeal}
  let contract : PrimeIdeal L → PrimeIdeal (deuringFixedField g) := fun P =>
    ⟨P.asIdeal.under
        (NumberField.RingOfIntegers (deuringFixedField g)), inferInstance, by
      intro h
      letI : P.asIdeal.LiesOver
          (⊥ : Ideal (NumberField.RingOfIntegers (deuringFixedField g))) :=
        ⟨by simpa [h]⟩
      exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot
        (NumberField.RingOfIntegers (deuringFixedField g)) P.asIdeal)⟩
  have hcontract_mem (P : source) :
      contract P.val ∈ deuringDegreeOnePrimeSet g ∧
        (contract P.val).asIdeal.under (NumberField.RingOfIntegers K) = p.asIdeal := by
    let q := contract P.val
    have hunrP := hunrp P.val P.prop.1
    have hdata := fixedField_contraction_degreeOne g p P.val P.prop.1 hunrP P.prop.2
    change q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 ∧
      (∀ Q : PrimeIdeal L, Q.asIdeal.LiesOver q.asIdeal → Q = P.val) at hdata
    rcases hdata with ⟨hqe, hqf, hunique⟩
    have hPq : P.val.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
    have hunrE : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers (deuringFixedField g)) P.val.asIdeal := by
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers K) P.val.asIdeal := hunrP
      exact Algebra.IsUnramifiedAt.of_restrictScalars
        (NumberField.RingOfIntegers K) P.val.asIdeal
    have hfrobE : AlgEquiv.restrictScalarsHom K
          (arithFrobeniusAt (K := deuringFixedField g) (L := L) P.val) = g := by
      have harithK := isArithFrobAt_restrictScalars_of_inertiaDeg_one P.val q hPq hqf
        (arithFrobeniusAt (K := deuringFixedField g) (L := L) P.val)
        (IsArithFrobAt.arithFrobAt
          (NumberField.RingOfIntegers (deuringFixedField g))
          (Gal(L/deuringFixedField g)) P.val.asIdeal)
      exact (frobenius_eq_of_isArith P.val hunrP _ harithK).trans P.prop.2
    refine ⟨⟨⟨?_, ⟨P.val, hPq, hfrobE⟩⟩, hqe, hqf⟩, ?_⟩
    · intro Q hQq
      rw [hunique Q hQq]
      exact hunrE
    · change (P.val.asIdeal.under
          (NumberField.RingOfIntegers (deuringFixedField g))).under
          (NumberField.RingOfIntegers K) = p.asIdeal
      rw [Ideal.under_under]
      exact P.prop.1.over.symm
  let toTarget : source → target := fun P => ⟨contract P.val, hcontract_mem P⟩
  have htoTarget_val (P : source) : (toTarget P).val = contract P.val := rfl
  have htoTarget_inj : Function.Injective toTarget := by
    intro P Q hPQ
    apply Subtype.ext
    have hdata := fixedField_contraction_degreeOne g p P.val P.prop.1
      (hunrp P.val P.prop.1) P.prop.2
    let q := contract P.val
    have hunique : ∀ R : PrimeIdeal L, R.asIdeal.LiesOver q.asIdeal → R = P.val := by
      change q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 ∧
        (∀ R : PrimeIdeal L, R.asIdeal.LiesOver q.asIdeal → R = P.val) at hdata
      exact hdata.2.2
    symm
    apply hunique Q.val
    refine ⟨?_⟩
    change q.asIdeal = Q.val.asIdeal.under
      (NumberField.RingOfIntegers (deuringFixedField g))
    rw [← show contract Q.val = q from by
      calc
        contract Q.val = (toTarget Q).val := (htoTarget_val Q).symm
        _ = (toTarget P).val := congrArg Subtype.val hPQ.symm
        _ = contract P.val := htoTarget_val P
        _ = q := rfl]
  have htoTarget_surj : Function.Surjective toTarget := by
    intro q
    rcases q.prop.1.1.2 with ⟨P, hPq, hfrobE⟩
    have hunrE := q.prop.1.1.1 P hPq
    have hunrqK : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) q.val.asIdeal := by
      rw [← Ideal.ramificationIdx_eq_one_iff]
      exact q.prop.1.2.1
    have hunrP : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := by
      letI : q.val.asIdeal.LiesOver p.asIdeal := ⟨q.prop.2.symm⟩
      letI : P.asIdeal.LiesOver q.val.asIdeal := hPq
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers K) q.val.asIdeal := hunrqK
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers (deuringFixedField g)) P.asIdeal := hunrE
      exact Algebra.IsUnramifiedAt.comp q.val.asIdeal P.asIdeal
    have hPp : P.asIdeal.LiesOver p.asIdeal := by
      letI : P.asIdeal.LiesOver q.val.asIdeal := hPq
      letI : q.val.asIdeal.LiesOver p.asIdeal := ⟨q.prop.2.symm⟩
      exact Ideal.LiesOver.trans P.asIdeal q.val.asIdeal p.asIdeal
    have hfrobP : arithFrobeniusAt (K := K) (L := L) P = g := by
      have harithK := isArithFrobAt_restrictScalars_of_inertiaDeg_one P q.val hPq q.prop.1.2.2
        (arithFrobeniusAt (K := deuringFixedField g) (L := L) P)
        (IsArithFrobAt.arithFrobAt
          (NumberField.RingOfIntegers (deuringFixedField g))
          (Gal(L/deuringFixedField g)) P.asIdeal)
      rw [hfrobE] at harithK
      exact (frobenius_eq_of_isArith P hunrP g harithK).symm
    let Ps : source := ⟨P, hPp, hfrobP⟩
    refine ⟨Ps, ?_⟩
    apply Subtype.ext
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    rw [htoTarget_val]
    exact hPq.over.symm
  have htarget : Nat.card target = Nat.card source :=
    Nat.card_congr (Equiv.ofBijective toTarget
      ⟨htoTarget_inj, htoTarget_surj⟩).symm
  have hHC : H ≤ C := by
    apply Subgroup.zpowers_le.mpr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl g)
  have hstabG : decompositionSubgroup (K := K) (L := L) P0 = H := by
    simpa [H, hfrobP0] using arithFrobAt_generates_decomposition P0 hunrP0
  have hstabC : MulAction.stabilizer C P0.asIdeal = H.subgroupOf C := by
    ext t
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro ht
      have htG : (t : G) ∈ decompositionSubgroup (K := K) (L := L) P0 :=
        MulAction.mem_stabilizer_iff.mpr ht
      rwa [hstabG] at htG
    · intro ht
      have htG : (t : G) ∈ decompositionSubgroup (K := K) (L := L) P0 := by
        rw [hstabG]
        exact ht
      exact MulAction.mem_stabilizer_iff.mpr
        (MulAction.mem_stabilizer_iff.mp htG)
  have hstabCard : Nat.card (MulAction.stabilizer C P0.asIdeal) = orderOf g := by
    rw [hstabC]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv]
    exact Nat.card_zpowers g
  have horbitProd : Nat.card (MulAction.orbit C P0.asIdeal) * orderOf g = Nat.card C := by
    rw [← hstabCard, ← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup C P0.asIdeal)
  have horbit : Nat.card (MulAction.orbit C P0.asIdeal) =
      Nat.card C / orderOf g := by
    apply Nat.eq_div_of_mul_eq_right (orderOf_pos g).ne'
    simpa only [Nat.mul_comm] using horbitProd
  change Nat.card target = deuringFactor g
  rw [htarget, hsource, horbit]
  rfl

/-- Blueprint Proposition 4.1 (`deuringFactor_isInteger`): orbit--stabilizer
shows `|⟨g⟩|` divides `|C_G(g)|`. -/
theorem deuringFactor_isInteger (g : Gal(L/K)) :
    orderOf g ∣ Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) := by
  rw [← Nat.card_zpowers]
  apply Subgroup.card_dvd_of_le
  apply Subgroup.zpowers_le.mpr
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl g)

private theorem boundedPrimeSet_finite
    {E : Type*} [Field E] [NumberField E]
    (S : Set (PrimeIdeal E)) (x : ℝ) :
    {p : PrimeIdeal E | p ∈ S ∧ (PrimeIdeal.norm p : ℝ) ≤ x}.Finite := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge x
  refine Set.Finite.of_finite_image
    (f := fun p : PrimeIdeal E => p.asIdeal) ?_ ?_
  · apply (Ideal.finite_setOf_absNorm_le
      (S := NumberField.RingOfIntegers E) n).subset
    rintro I ⟨p, hp, rfl⟩
    change Ideal.absNorm p.asIdeal ≤ n
    exact_mod_cast hp.2.trans hn
  · intro p _ q _ hpq
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hpq

private theorem primeCounting_le_three_of_subset
    {E : Type*} [Field E] [NumberField E]
    {A B C D : Set (PrimeIdeal E)}
    (h : A ⊆ B ∪ C ∪ D) (x : ℝ) :
    primeCounting A x ≤ primeCounting B x + primeCounting C x + primeCounting D x := by
  let AX := {p : PrimeIdeal E | p ∈ A ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  let BX := {p : PrimeIdeal E | p ∈ B ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  let CX := {p : PrimeIdeal E | p ∈ C ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  let DX := {p : PrimeIdeal E | p ∈ D ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
  have hsub : AX ⊆ (BX ∪ CX) ∪ DX := by
    intro p hp
    rcases h hp.1 with hpBC | hpD
    · rcases hpBC with hpB | hpC
      · exact Or.inl (Or.inl ⟨hpB, hp.2⟩)
      · exact Or.inl (Or.inr ⟨hpC, hp.2⟩)
    · exact Or.inr ⟨hpD, hp.2⟩
  unfold primeCounting
  change AX.ncard ≤ BX.ncard + CX.ncard + DX.ncard
  calc
    AX.ncard ≤ ((BX ∪ CX) ∪ DX).ncard := Set.ncard_le_ncard hsub
      (((boundedPrimeSet_finite B x).union (boundedPrimeSet_finite C x)).union
        (boundedPrimeSet_finite D x))
    _ ≤ (BX ∪ CX).ncard + DX.ncard := Set.ncard_union_le _ _
    _ ≤ BX.ncard + CX.ncard + DX.ncard :=
      Nat.add_le_add_right (Set.ncard_union_le _ _) _

private def primeUnder
    {E : Type*} [Field E] [NumberField E] [Algebra K E]
    (q : PrimeIdeal E) : PrimeIdeal K :=
  ⟨q.asIdeal.under (NumberField.RingOfIntegers K), inferInstance, by
    intro h
    letI : q.asIdeal.LiesOver (⊥ : Ideal (NumberField.RingOfIntegers K)) :=
      ⟨by simpa [h]⟩
    exact q.ne_bot (Ideal.eq_bot_of_liesOver_bot
      (NumberField.RingOfIntegers K) q.asIdeal)⟩

private theorem primeUnder_fiber_finite
    {E : Type*} [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] (p : PrimeIdeal K) :
    {q : PrimeIdeal E | primeUnder (K := K) q = p}.Finite := by
  apply Set.Finite.of_finite_image
    (f := fun q : PrimeIdeal E => q.asIdeal)
  · apply (IsDedekindDomain.primesOver_finite p.asIdeal
      (NumberField.RingOfIntegers E)).subset
    rintro I ⟨q, hq, rfl⟩
    exact ⟨inferInstance, ⟨by
      change p.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers K)
      rw [← hq]
      rfl⟩⟩
  · intro q _ r _ hqr
    exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective hqr

/-- Blueprint Proposition 4.1, equation (1),
`deuring_exceptional_primeCounting`: removing primes with `e > 1` or `f > 1`
from `Q_g` changes its counting function by only `O(x^(1/2))`. -/
theorem deuring_exceptional_primeCounting (g : Gal(L/K)) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ =>
        (primeCounting (deuringUpstairsPrimeSet g) x : ℝ) -
          (primeCounting (deuringDegreeOnePrimeSet g) x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
  let E := deuringFixedField g
  let A := deuringUpstairsPrimeSet g
  let B := deuringDegreeOnePrimeSet g
  let R : Set (PrimeIdeal K) :=
    {p | ¬ IsUnramifiedPrime (K := K) (L := L) p}
  let C : Set (PrimeIdeal E) :=
    {q | q ∈ A ∧
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}
  let D : Set (PrimeIdeal E) :=
    {q | 2 ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)}
  have hR : R.Finite := ramifiedPrimes_finite (K := K) (L := L)
  have hpre : {q : PrimeIdeal E | primeUnder (K := K) q ∈ R}.Finite := by
    exact hR.preimage' (fun p _ => primeUnder_fiber_finite (E := E) p)
  have hC : C.Finite := hpre.subset (by
    intro q hq
    have hqA := hq.1
    rcases hqA.2 with ⟨P, hPq, _⟩
    have hunrPE := hqA.1 P hPq
    have hPp : P.asIdeal.LiesOver (primeUnder (K := K) q).asIdeal := by
      letI : P.asIdeal.LiesOver q.asIdeal := hPq
      change P.asIdeal.LiesOver
        (q.asIdeal.under (NumberField.RingOfIntegers K))
      exact Ideal.LiesOver.trans P.asIdeal q.asIdeal
        (q.asIdeal.under (NumberField.RingOfIntegers K))
    have hePE : P.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers E) = 1 := by
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers E) P.asIdeal := hunrPE
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hePK : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) =
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
      letI : P.asIdeal.LiesOver q.asIdeal := hPq
      rw [Ideal.ramificationIdx_tower
        (R := NumberField.RingOfIntegers K)
        (S := NumberField.RingOfIntegers E)
        (T := NumberField.RingOfIntegers L) q.asIdeal P.asIdeal, hePE, mul_one]
    change ¬ IsUnramifiedPrime (K := K) (L := L) (primeUnder (K := K) q)
    intro hunrp
    have hunrPK := hunrp P hPp
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := hunrPK
    have := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R := NumberField.RingOfIntegers K) (p := P.asIdeal)
    exact hq.2 (hePK.symm.trans this))
  have hsub : A ⊆ B ∪ C ∪ D := by
    intro q hqA
    by_cases he : q.asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) = 1
    · by_cases hf : q.asIdeal.inertiaDeg
          (NumberField.RingOfIntegers K) = 1
      · exact Or.inl (Or.inl ⟨hqA, he, hf⟩)
      · apply Or.inr
        apply (Nat.two_le_iff _).mpr
        exact ⟨(q.asIdeal.inertiaDeg_pos
          (NumberField.RingOfIntegers K)).ne', hf⟩
    · exact Or.inl (Or.inr ⟨hqA, he⟩)
  have hCle (x : ℝ) : primeCounting C x ≤ Nat.card C := by
    letI : Fintype C := hC.fintype
    unfold primeCounting
    apply Nat.card_le_card_of_injective
      (fun q : {q : PrimeIdeal E // q ∈ C ∧ (PrimeIdeal.norm q : ℝ) ≤ x} =>
        (⟨q.val, q.prop.1⟩ : C))
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : C => (z : PrimeIdeal E)) hqr
  have hCO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting C x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
    apply Asymptotics.IsBigO.of_bound (Nat.card C)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrt : 1 ≤ Real.sqrt x := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x), Real.sqrt_nonneg x]
    have hcount : (primeCounting C x : ℝ) ≤ Nat.card C := by
      exact_mod_cast hCle x
    nlinarith [show (0 : ℝ) ≤ Nat.card C from Nat.cast_nonneg _]
  have hDO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting D x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
    exact PrimeIdeal.count_residueDegree_ge_two (K := K) (E := E)
  have hdiff (x : ℝ) :
      |(primeCounting A x : ℝ) - (primeCounting B x : ℝ)| ≤
        (primeCounting C x : ℝ) + (primeCounting D x : ℝ) := by
    have hBA : primeCounting B x ≤ primeCounting A x := by
      unfold primeCounting
      letI : Finite {q : PrimeIdeal E // q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x} :=
        boundedPrimeSet_finite A x
      apply Nat.card_le_card_of_injective
        (fun q : {q : PrimeIdeal E // q ∈ B ∧ (PrimeIdeal.norm q : ℝ) ≤ x} =>
          (⟨q.val, q.prop.1.1, q.prop.2⟩ :
            {q : PrimeIdeal E // q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x}))
      intro q r hqr
      apply Subtype.ext
      exact congrArg
        (fun z : {q : PrimeIdeal E // q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x} =>
          (z : PrimeIdeal E)) hqr
    have hABC := primeCounting_le_three_of_subset hsub x
    rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hBA))]
    have hnat : primeCounting A x - primeCounting B x ≤
        primeCounting C x + primeCounting D x := by omega
    exact_mod_cast hnat
  have hdiffO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting A x : ℝ) - (primeCounting B x : ℝ))
      (fun x : ℝ => (primeCounting C x : ℝ) + (primeCounting D x : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound (1 : ℝ)
    filter_upwards with x
    change |(primeCounting A x : ℝ) - (primeCounting B x : ℝ)| ≤
      1 * |(primeCounting C x : ℝ) + (primeCounting D x : ℝ)|
    rw [one_mul]
    conv_rhs => rw [abs_of_nonneg
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact hdiff x
  exact hdiffO.trans (hCO.add hDO)

private theorem degreeOne_contraction_mem
    (g : Gal(L/K)) (q : PrimeIdeal (deuringFixedField g))
    (hq : q ∈ deuringDegreeOnePrimeSet g) :
    let p := primeUnder (K := K) q
    p ∈ frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g) ∧
      PrimeIdeal.norm q = PrimeIdeal.norm p := by
  let p := primeUnder (K := K) q
  rcases hq.1.2 with ⟨P, hPq, hfrobE⟩
  have hunrPE := hq.1.1 P hPq
  have hunrqK : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) q.asIdeal := by
    rw [← Ideal.ramificationIdx_eq_one_iff]
    exact hq.2.1
  have hunrPK : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) P.asIdeal := by
    letI : P.asIdeal.LiesOver q.asIdeal := hPq
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) q.asIdeal := hunrqK
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers (deuringFixedField g)) P.asIdeal := hunrPE
    exact Algebra.IsUnramifiedAt.comp q.asIdeal P.asIdeal
  have hPp : P.asIdeal.LiesOver p.asIdeal := by
    letI : P.asIdeal.LiesOver q.asIdeal := hPq
    change P.asIdeal.LiesOver
      (q.asIdeal.under (NumberField.RingOfIntegers K))
    exact Ideal.LiesOver.trans P.asIdeal q.asIdeal
      (q.asIdeal.under (NumberField.RingOfIntegers K))
  have hfrobP : arithFrobeniusAt (K := K) (L := L) P = g := by
    have harithK := isArithFrobAt_restrictScalars_of_inertiaDeg_one
      P q hPq hq.2.2
      (arithFrobeniusAt (K := deuringFixedField g) (L := L) P)
      (IsArithFrobAt.arithFrobAt
        (NumberField.RingOfIntegers (deuringFixedField g))
        (Gal(L/deuringFixedField g)) P.asIdeal)
    rw [hfrobE] at harithK
    exact (frobenius_eq_of_isArith P hunrPK g harithK).symm
  have hunrp : IsUnramifiedPrime (K := K) (L := L) p := by
    intro Q hQp
    have heP : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers K) P.asIdeal := hunrPK
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have heQ : Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
      letI : P.asIdeal.LiesOver p.asIdeal := hPp
      letI : Q.asIdeal.LiesOver p.asIdeal := hQp
      rw [Ideal.ramificationIdx_eq_of_isGaloisGroup
        p.asIdeal Q.asIdeal P.asIdeal (Gal(L/K))]
      exact heP
    rw [← Ideal.ramificationIdx_eq_one_iff]
    exact heQ
  refine ⟨⟨hunrp, P, hPp, ?_⟩, ?_⟩
  · exact congrArg ConjClasses.mk hfrobP
  · have hnorm := PrimeIdeal.norm_pow_inertiaDeg q p (by
      change q.asIdeal.LiesOver
        (q.asIdeal.under (NumberField.RingOfIntegers K))
      exact ⟨rfl⟩)
    simpa [hq.2.2] using hnorm

/-- Blueprint Proposition 4.1, equation (D), proposed declaration
`deuring_primeCounting`:
`π_Qg(x) = n_g π_PC(x) + O(x^(1/2))`. -/
theorem deuring_primeCounting (g : Gal(L/K)) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ =>
        (primeCounting (deuringUpstairsPrimeSet g) x : ℝ) -
          (deuringFactor g : ℝ) *
            (primeCounting
              (frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)) x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
  classical
  let E := deuringFixedField g
  let B := deuringDegreeOnePrimeSet g
  let T := frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)
  have hexact (x : ℝ) :
      primeCounting B x = deuringFactor g * primeCounting T x := by
    let X := {q : PrimeIdeal E // q ∈ B ∧ (PrimeIdeal.norm q : ℝ) ≤ x}
    let Y := {p : PrimeIdeal K // p ∈ T ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
    letI : Finite X := boundedPrimeSet_finite B x
    letI : Finite Y := boundedPrimeSet_finite T x
    letI : Fintype Y := Fintype.ofFinite Y
    let f : X → Y := fun q =>
      ⟨primeUnder (K := K) q.val,
        (degreeOne_contraction_mem g q.val q.prop.1).1,
        by rw [← (degreeOne_contraction_mem g q.val q.prop.1).2]
           exact q.prop.2⟩
    have hfiber (p : Y) : Nat.card {q : X // f q = p} = deuringFactor g := by
      let Z := {q : PrimeIdeal E // q ∈ B ∧
        q.asIdeal.under (NumberField.RingOfIntegers K) = p.val.asIdeal}
      let toZ : {q : X // f q = p} → Z := fun q =>
        ⟨q.val.val, q.val.prop.1, by
          have hp := congrArg Subtype.val q.prop
          exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hp⟩
      have htoZ_inj : Function.Injective toZ := by
        intro q r hqr
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Z => (z.val : PrimeIdeal E)) hqr
      have htoZ_surj : Function.Surjective toZ := by
        intro q
        have hdata := degreeOne_contraction_mem g q.val q.prop.1
        have hnorm : PrimeIdeal.norm q.val = PrimeIdeal.norm p.val := by
          rw [hdata.2]
          congr 1
          exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective q.prop.2
        let qX : X := ⟨q.val, q.prop.1, by rw [hnorm]; exact p.prop.2⟩
        have hfq : f qX = p := by
          apply Subtype.ext
          apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
          exact q.prop.2
        refine ⟨⟨qX, hfq⟩, ?_⟩
        apply Subtype.ext
        rfl
      rw [Nat.card_congr (Equiv.ofBijective toZ ⟨htoZ_inj, htoZ_surj⟩)]
      exact deuring_degreeOne_fiber_card g p.val p.prop.1
    unfold primeCounting
    change Nat.card X = deuringFactor g * Nat.card Y
    calc
      Nat.card X = Nat.card (Σ p : Y, {q : X // f q = p}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
      _ = ∑ p : Y, Nat.card {q : X // f q = p} := Nat.card_sigma
      _ = ∑ _p : Y, deuringFactor g := by
        apply Finset.sum_congr rfl
        intro p _
        exact hfiber p
      _ = deuringFactor g * Nat.card Y := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
        simpa [nsmul_eq_mul] using
          (Nat.mul_comm (Nat.card Y) (deuringFactor g))
  apply (deuring_exceptional_primeCounting (K := K) (L := L) g).congr'
  · filter_upwards with x
    rw [hexact x]
    push_cast
    rfl
  · exact Eventually.of_forall fun _ => rfl

private theorem normalized_zero_of_bigO_sqrt {f : ℝ → ℝ}
    (h : Asymptotics.IsBigO atTop f (fun x : ℝ => Real.sqrt x)) :
    Tendsto (fun x : ℝ => f x / (x / Real.log x)) atTop (𝓝 0) := by
  have hlog : (fun x : ℝ => Real.log x) =o[atTop]
      fun x => Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hprod : (fun x : ℝ => f x * Real.log x) =o[atTop]
      fun x => Real.sqrt x * Real.sqrt x := h.mul_isLittleO hlog
  have hsqrt : (fun x : ℝ => f x * Real.log x) =o[atTop]
      fun x => x := by
    apply hprod.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.mul_self_sqrt hx]
  apply hsqrt.tendsto_div_nhds_zero.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp

private theorem primeDensity_iff_of_bigO_sqrt
    {E : Type*} [Field E] [NumberField E]
    {S : Set (PrimeIdeal E)} {T : Set (PrimeIdeal K)} {n δ : ℝ} (hn : n ≠ 0)
    (h : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting S x : ℝ) - n * (primeCounting T x : ℝ))
      (fun x : ℝ => Real.sqrt x)) :
    HasPrimeDensity S (n * δ) ↔ HasPrimeDensity T δ := by
  have hzero := normalized_zero_of_bigO_sqrt h
  have hdiff : Tendsto (fun x : ℝ =>
      (primeCounting S x : ℝ) / (x / Real.log x) -
        n * ((primeCounting T x : ℝ) / (x / Real.log x))) atTop (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    field_simp
  constructor
  · intro hS
    unfold HasPrimeDensity at hS ⊢
    have hsub : Tendsto (fun x : ℝ =>
        (primeCounting S x : ℝ) / (x / Real.log x) -
          ((primeCounting S x : ℝ) / (x / Real.log x) -
            n * ((primeCounting T x : ℝ) / (x / Real.log x)))) atTop
          (𝓝 (n * δ)) := by
      simpa using hS.sub hdiff
    have hmul : Tendsto (fun x : ℝ =>
        n * ((primeCounting T x : ℝ) / (x / Real.log x))) atTop (𝓝 (n * δ)) := by
      apply hsub.congr'
      filter_upwards with x
      ring
    have hdiv := hmul.div_const n
    simpa [hn] using hdiv.congr' (Eventually.of_forall fun x => by field_simp)
  · intro hT
    unfold HasPrimeDensity at hT ⊢
    have hadd : Tendsto (fun x : ℝ =>
        ((primeCounting S x : ℝ) / (x / Real.log x) -
          n * ((primeCounting T x : ℝ) / (x / Real.log x))) +
          n * ((primeCounting T x : ℝ) / (x / Real.log x))) atTop
          (𝓝 (n * δ)) := by
      simpa using hdiff.add (hT.const_mul n)
    apply hadd.congr'
    filter_upwards with x
    ring

/-- Blueprint Proposition 4.1 (`deuring_primeDensity`): the same exact factor
transfers prime-number-theorem density. -/
theorem deuring_primeDensity (g : Gal(L/K)) (δ : ℝ) :
    HasPrimeDensity (deuringUpstairsPrimeSet g) ((deuringFactor g : ℝ) * δ) ↔
      HasPrimeDensity
        (frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)) δ := by
  apply primeDensity_iff_of_bigO_sqrt
    (S := deuringUpstairsPrimeSet g)
    (T := frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g))
    (n := deuringFactor g) (δ := δ)
  · apply Nat.cast_ne_zero.mpr
    unfold deuringFactor
    apply Nat.ne_of_gt
    apply Nat.div_pos
    · exact Nat.le_of_dvd Nat.card_pos (deuringFactor_isInteger g)
    · exact orderOf_pos g
  · exact deuring_primeCounting (K := K) (L := L) g

private theorem degreeOne_dirichletPrimeSum (g : Gal(L/K)) (s : ℝ) :
    dirichletPrimeSum (deuringDegreeOnePrimeSet g) s =
      (deuringFactor g : ℝ) *
        dirichletPrimeSum
          (frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)) s := by
  classical
  let E := deuringFixedField g
  let B := deuringDegreeOnePrimeSet g
  let T := frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)
  let X := {q : PrimeIdeal E // q ∈ B}
  let Y := {p : PrimeIdeal K // p ∈ T}
  let f : X → Y := fun q =>
    ⟨primeUnder (K := K) q.val, (degreeOne_contraction_mem g q.val q.prop).1⟩
  have hfiber (p : Y) : Nat.card {q : X // f q = p} = deuringFactor g := by
    let Z := {q : PrimeIdeal E // q ∈ B ∧
      q.asIdeal.under (NumberField.RingOfIntegers K) = p.val.asIdeal}
    let toZ : {q : X // f q = p} → Z := fun q =>
      ⟨q.val.val, q.val.prop, by
        have hp := congrArg Subtype.val q.prop
        exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hp⟩
    have htoZ_inj : Function.Injective toZ := by
      intro q r hqr
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Z => (z.val : PrimeIdeal E)) hqr
    have htoZ_surj : Function.Surjective toZ := by
      intro q
      let qX : X := ⟨q.val, q.prop.1⟩
      have hfq : f qX = p := by
        apply Subtype.ext
        apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        exact q.prop.2
      refine ⟨⟨qX, hfq⟩, ?_⟩
      apply Subtype.ext
      rfl
    rw [Nat.card_congr (Equiv.ofBijective toZ ⟨htoZ_inj, htoZ_surj⟩)]
    exact deuring_degreeOne_fiber_card g p.val p.prop
  have hnpos : 0 < deuringFactor g := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd Nat.card_pos (deuringFactor_isInteger g)
    · exact orderOf_pos g
  have hfiberFinite (p : Y) : Finite {q : X // f q = p} :=
    (Nat.card_pos_iff.mp (by rw [hfiber p]; exact hnpos)).2
  have hsubB : dirichletPrimeSum B s =
      ∑' q : X, Real.rpow (PrimeIdeal.norm q.val : ℝ) (-s) := by
    unfold dirichletPrimeSum
    symm
    simpa [Set.indicator] using
      (tsum_subtype B
        (fun q : PrimeIdeal E => Real.rpow (PrimeIdeal.norm q : ℝ) (-s)))
  have hsubT : dirichletPrimeSum T s =
      ∑' p : Y, Real.rpow (PrimeIdeal.norm p.val : ℝ) (-s) := by
    unfold dirichletPrimeSum
    symm
    simpa [Set.indicator] using
      (tsum_subtype T
        (fun p : PrimeIdeal K => Real.rpow (PrimeIdeal.norm p : ℝ) (-s)))
  change dirichletPrimeSum B s =
    (deuringFactor g : ℝ) * dirichletPrimeSum T s
  rw [hsubB, hsubT]
  let a : Y → ℝ := fun p => Real.rpow (PrimeIdeal.norm p.val : ℝ) (-s)
  have hterm (q : X) :
      Real.rpow (PrimeIdeal.norm q.val : ℝ) (-s) = a (f q) := by
    apply congrArg (fun z : ℝ => Real.rpow z (-s))
    exact_mod_cast (degreeOne_contraction_mem g q.val q.prop).2
  have hinternal (p : Y) :
      ∑' q : {q : X // f q = p}, a p = (deuringFactor g : ℝ) * a p := by
    letI : Finite {q : X // f q = p} := hfiberFinite p
    letI : Fintype {q : X // f q = p} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hfiber]
    simp [nsmul_eq_mul]
  have hnonneg (z : Σ p : Y, {q : X // f q = p}) :
      0 ≤ a z.1 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsigma :
      (∑' z : Σ p : Y, {q : X // f q = p}, a z.1) =
        (deuringFactor g : ℝ) * ∑' p : Y, a p := by
    by_cases ha : Summable a
    · have hz : Summable (fun z : Σ p : Y, {q : X // f q = p} => a z.1) := by
        rw [summable_sigma_of_nonneg hnonneg]
        constructor
        · intro p
          letI : Finite {q : X // f q = p} := hfiberFinite p
          letI : Fintype {q : X // f q = p} := Fintype.ofFinite _
          exact (hasSum_fintype _).summable
        · simpa only [hinternal] using ha.mul_left (deuringFactor g : ℝ)
      rw [hz.tsum_sigma]
      simp_rw [hinternal]
      exact tsum_mul_left
    · have hz : ¬ Summable (fun z : Σ p : Y, {q : X // f q = p} => a z.1) := by
        intro hz
        have hout := hz.sigma
        simp_rw [hinternal] at hout
        have hn : (deuringFactor g : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.div_pos
            (Nat.le_of_dvd Nat.card_pos (deuringFactor_isInteger g)) (orderOf_pos g)))
        exact ha ((summable_mul_left_iff hn).mp hout)
      rw [tsum_eq_zero_of_not_summable hz, tsum_eq_zero_of_not_summable ha, mul_zero]
  calc
    (∑' q : X, Real.rpow (PrimeIdeal.norm q.val : ℝ) (-s)) =
        ∑' q : X, a (f q) := tsum_congr hterm
    _ = ∑' z : Σ p : Y, {q : X // f q = p}, a z.1 := by
      rw [← (Equiv.sigmaFiberEquiv f).tsum_eq]
      apply tsum_congr
      intro z
      rw [Equiv.sigmaFiberEquiv_apply]
      exact congrArg a z.2.prop
    _ = (deuringFactor g : ℝ) * ∑' p : Y, a p := hsigma

/-- Blueprint Proposition 4.1 and §9 (`deuring_dirichletDensity`): the
identical factor relation for Dirichlet density; no Tauberian input occurs. -/
theorem deuring_dirichletDensity (g : Gal(L/K)) (δ : ℝ) :
    HasDirichletDensity (deuringUpstairsPrimeSet g)
        ((deuringFactor g : ℝ) * δ) ↔
      HasDirichletDensity
        (frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)) δ := by
  let A := deuringUpstairsPrimeSet g
  let B := deuringDegreeOnePrimeSet g
  let T := frobeniusPrimeSet (K := K) (L := L) (ConjClasses.mk g)
  let n : ℝ := deuringFactor g
  have hBA : B ⊆ A := fun _ h => h.1
  have hcount (x : ℝ) :
      primeCounting (symmetricDifference A B) x =
        primeCounting A x - primeCounting B x := by
    let AX := {p : PrimeIdeal (deuringFixedField g) |
      p ∈ A ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
    let BX := {p : PrimeIdeal (deuringFixedField g) |
      p ∈ B ∧ (PrimeIdeal.norm p : ℝ) ≤ x}
    have hBX : BX ⊆ AX := fun _ h => ⟨hBA h.1, h.2⟩
    have hset : {p : PrimeIdeal (deuringFixedField g) |
        p ∈ symmetricDifference A B ∧ (PrimeIdeal.norm p : ℝ) ≤ x} = AX \ BX := by
      ext p
      simp only [symmetricDifference, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨(⟨hpA, hpB⟩ | ⟨hpB, hpA⟩), hn⟩
        · exact ⟨⟨hpA, hn⟩, fun h => hpB h.1⟩
        · exact (hpA (hBA hpB)).elim
      · rintro ⟨⟨hpA, hn⟩, hpB⟩
        exact ⟨Or.inl ⟨hpA, fun h => hpB ⟨h, hn⟩⟩, hn⟩
    unfold primeCounting
    change ({p : PrimeIdeal (deuringFixedField g) |
      p ∈ symmetricDifference A B ∧ (PrimeIdeal.norm p : ℝ) ≤ x}).ncard =
        AX.ncard - BX.ncard
    rw [hset]
    exact Set.ncard_diff hBX (boundedPrimeSet_finite B x)
  have hsymO : Asymptotics.IsBigO atTop
      (fun x : ℝ => (primeCounting (symmetricDifference A B) x : ℝ))
      (fun x : ℝ => Real.sqrt x) := by
    apply (deuring_exceptional_primeCounting (K := K) (L := L) g).congr'
    · filter_upwards with x
      rw [hcount]
      have hle : primeCounting B x ≤ primeCounting A x := by
        unfold primeCounting
        letI : Finite {q : PrimeIdeal (deuringFixedField g) //
            q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x} := boundedPrimeSet_finite A x
        apply Nat.card_le_card_of_injective
          (fun q : {q : PrimeIdeal (deuringFixedField g) //
              q ∈ B ∧ (PrimeIdeal.norm q : ℝ) ≤ x} =>
            (⟨q.val, hBA q.prop.1, q.prop.2⟩ :
              {q : PrimeIdeal (deuringFixedField g) //
                q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x}))
        intro q r hqr
        apply Subtype.ext
        exact congrArg
          (fun z : {q : PrimeIdeal (deuringFixedField g) //
            q ∈ A ∧ (PrimeIdeal.norm q : ℝ) ≤ x} =>
              (z : PrimeIdeal (deuringFixedField g))) hqr
      rw [Nat.cast_sub hle]
    · exact Eventually.of_forall fun _ => rfl
  have hsym : HasDirichletDensity (symmetricDifference A B) 0 :=
    sqrt_bound_hasDirichletDensity_zero _ hsymO
  have hn : n ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Nat.ne_of_gt
    apply Nat.div_pos
    · exact Nat.le_of_dvd Nat.card_pos (deuringFactor_isInteger g)
    · exact orderOf_pos g
  have hBT : HasDirichletDensity B (n * δ) ↔ HasDirichletDensity T δ := by
    unfold HasDirichletDensity
    constructor
    · intro hB
      have hd := hB.div_const n
      have hd' : Tendsto
          (fun s : ℝ => dirichletPrimeSum T s / dirichletNormalizer s)
          (𝓝[>] (1 : ℝ)) (𝓝 ((n * δ) / n)) := by
        apply hd.congr'
        filter_upwards with s
        rw [degreeOne_dirichletPrimeSum (K := K) (L := L) g s]
        field_simp
        rfl
      simpa [hn] using hd'
    · intro hT
      have hm := hT.const_mul n
      apply hm.congr'
      filter_upwards with s
      rw [degreeOne_dirichletPrimeSum (K := K) (L := L) g s]
      ring
  constructor
  · intro hA
    have hB : HasDirichletDensity B (n * δ) :=
      hA.congr_of_symmetricDifference_zero hsym
    exact hBT.mp hB
  · intro hT
    have hB := hBT.mpr hT
    apply hB.congr_of_symmetricDifference_zero
    have heq : symmetricDifference B A = symmetricDifference A B := by
      ext p
      simp only [symmetricDifference, Set.mem_union, Set.mem_diff]
      aesop
    rwa [heq]

end NU.Chebotarev
