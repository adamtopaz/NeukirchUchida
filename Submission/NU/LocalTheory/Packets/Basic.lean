import Submission.NU.LocalTheory.NumberField.CupZeroAlternating

/-!
# Cohomological packets

Packets are two-dimensional subspaces of the explicit elementary quotient,
tested only against the cochain-level `CupZero` relation.  This module also
states weak approximation and packet separation before any stabilizer is
introduced, preserving the dependency order of Blueprint §13.
-/

open IsDedekindDomain
open scoped NumberField

namespace NU.LocalTheory

noncomputable section

/-- A linear subspace of the explicit elementary quotient. -/
abbrev GroupSubspace (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ℓ : ℕ) :=
  Submodule (ZMod ℓ) (ElementaryQuotient G ℓ)

/-- The evaluation determinant associated with two points in the elementary
quotient and two continuous characters. -/
def evaluationDet {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {ℓ : ℕ}
    (p q : ElementaryQuotient G ℓ) (a b : ContinuousCharacter G ℓ) :
    ZMod ℓ :=
  evaluation ℓ p a * evaluation ℓ q b -
    evaluation ℓ p b * evaluation ℓ q a

/-- An ordered basis of a specified plane.  Membership, independence, and
the spanning equation are all recorded, avoiding a vacuous basis bundle. -/
def IsPlaneBasis {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {ℓ : ℕ} [Fact ℓ.Prime]
    (P : GroupSubspace G ℓ) (p q : ElementaryQuotient G ℓ) : Prop :=
  p ∈ P ∧ q ∈ P ∧
    PairIndependent (k := ZMod ℓ) p q ∧
    pairSpan p q = P

/-- Blueprint Definition 6.1 (`def:packet`): a plane is a packet when one
actual basis has determinant zero on every explicit cup-zero pair. -/
def IsPacket {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : GroupSubspace G ℓ) : Prop :=
  ∃ p q : ElementaryQuotient G ℓ,
    IsPlaneBasis P p q ∧
      ∀ a b : ContinuousCharacter G ℓ,
        CupZero ℓ a b → evaluationDet p q a b = 0

private theorem pairSpan_map_linearEquiv
    {k V W : Type*} [DivisionRing k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (e : V ≃ₗ[k] W) (x y : V) :
    (pairSpan (k := k) x y).map e.toLinearMap =
      pairSpan (e x) (e y) := by
  calc
    (pairSpan (k := k) x y).map e.toLinearMap =
        Submodule.span k (e '' {x, y}) := LinearMap.map_span _ _
    _ = Submodule.span k {e x, e y} := by rw [Set.image_pair]
    _ = pairSpan (e x) (e y) := rfl

private theorem exists_planeBasis_of_finrank_eq_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ℓ : ℕ} [Fact ℓ.Prime] (P : GroupSubspace G ℓ)
    (hfin : Module.finrank (ZMod ℓ) P = 2) :
    ∃ p q, IsPlaneBasis P p q := by
  letI : Module.Finite (ZMod ℓ) P :=
    Module.finite_of_finrank_pos (by rw [hfin]; omega)
  let b : Module.Basis (Fin 2) (ZMod ℓ) P :=
    Module.finBasisOfFinrankEq (ZMod ℓ) P hfin
  let p : ElementaryQuotient G ℓ := b 0
  let q : ElementaryQuotient G ℓ := b 1
  refine ⟨p, q, (b 0).prop, (b 1).prop, ?_, ?_⟩
  · have hb := b.linearIndependent.map' P.subtype (by simp)
    change LinearIndependent (ZMod ℓ)
      (fun i => ((b i : P) : ElementaryQuotient G ℓ)) at hb
    have hfun : (fun i => ((b i : P) : ElementaryQuotient G ℓ)) =
        pairVector p q := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at hb
    exact hb
  · have hrange : Set.range
        (fun i => ((b i : P) : ElementaryQuotient G ℓ)) = {p, q} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [p, q]
      · intro hx
        rcases hx with (rfl | hx)
        · exact ⟨0, rfl⟩
        · have : x = q := by simpa using hx
          subst x
          exact ⟨1, rfl⟩
    have himage : Set.range
        (fun i => ((b i : P) : ElementaryQuotient G ℓ)) =
        P.subtype '' Set.range b := by
      ext x
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [pairSpan, ← hrange, himage, ← LinearMap.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]

private theorem kummerCharacter_surjective
    {M : Type*} [Field M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Surjective (kummerCharacter ζ hζ) := by
  intro χ
  obtain ⟨x, hx⟩ := (kummerEquiv ζ hζ).surjective χ
  obtain ⟨z, rfl⟩ := (LinearMap.range
    (LinearMap.lsmul ℤ (Additive Mˣ) (ℓ : ℤ))).mkQ_surjective x
  cases z with
  | ofMul a => exact ⟨a, hx⟩

private theorem satisfiesValuationConclusion_of_span_eq_localD
    {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace M) (p q : MulCharacter M ℓ)
    (hind : PairIndependent (k := ZMod ℓ) p q)
    (hspan : pairSpan (k := ZMod ℓ) p q =
      localD ℓ (primeValuationSubring v)) :
    SatisfiesValuationConclusion ℓ (primeValuationSubring v) p q := by
  refine ⟨hspan.le, ?_⟩
  let W := pairSpan (k := ZMod ℓ) p q
  let I := localI ℓ (primeValuationSubring v)
  let N : Submodule (ZMod ℓ) W := Submodule.comap W.subtype I
  have hWrank : Module.finrank (ZMod ℓ) W = 2 :=
    pairSpan_finrank_eq_two p q hind
  letI : Module.Finite (ZMod ℓ) W :=
    Module.finite_of_finrank_pos (by rw [hWrank]; omega)
  have hIrank : Module.finrank (ZMod ℓ) I = 1 :=
    (local_dimensions ζ hζ v).1
  have hIle : I ≤ W := by
    dsimp [I, W]
    rw [hspan]
    exact localI_le_localD ℓ (primeValuationSubring v)
  have hNrank : Module.finrank (ZMod ℓ) N = 1 := by
    rw [show Module.finrank (ZMod ℓ) N = Module.finrank (ZMod ℓ) I from
      (Submodule.comapSubtypeEquivOfLe hIle).finrank_eq, hIrank]
  change Module.finrank (ZMod ℓ) (W ⧸ N) ≤ 1
  have hsum := Submodule.finrank_quotient_add_finrank N
  rw [hNrank, hWrank] at hsum
  omega

/-- A change of plane basis scales the evaluation determinant by the
nonzero determinant of the change-of-basis matrix. -/
theorem evaluationDet_change_basis {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {ℓ : ℕ} [Fact ℓ.Prime]
    (P : GroupSubspace G ℓ)
    {p q p' q' : ElementaryQuotient G ℓ}
    (h : IsPlaneBasis P p q) (h' : IsPlaneBasis P p' q') :
    ∃ c : ZMod ℓ, c ≠ 0 ∧
      ∀ a b, evaluationDet p' q' a b = c * evaluationDet p q a b := by
  have hp'mem : p' ∈ pairSpan (k := ZMod ℓ) p q := by
    rw [h.2.2.2]
    exact h'.1
  have hq'mem : q' ∈ pairSpan (k := ZMod ℓ) p q := by
    rw [h.2.2.2]
    exact h'.2.1
  obtain ⟨A, B, hp'⟩ := Submodule.mem_span_pair.mp hp'mem
  obtain ⟨C, D, hq'⟩ := Submodule.mem_span_pair.mp hq'mem
  let c : ZMod ℓ := A * D - B * C
  have hc : c ≠ 0 := by
    intro hc0
    have hi : q' ≠ 0 ∧ ∀ t : ZMod ℓ, t • q' ≠ p' := by
      simpa [PairIndependent, pairVector] using
        (linearIndependent_fin2.mp h'.2.2.1)
    by_cases hD : D = 0
    · have hC : C ≠ 0 := by
        intro hC
        apply hi.1
        rw [← hq', hC, hD, zero_smul, zero_smul, zero_add]
      have hB : B = 0 := by
        apply mul_right_cancel₀ hC
        have : B * C = 0 := by simpa [c, hD] using hc0
        rw [this, zero_mul]
      apply hi.2 (A * C⁻¹)
      rw [← hp', ← hq', hD, hB, zero_smul, add_zero]
      simp only [smul_smul]
      have htC : A * C⁻¹ * C = A := by field_simp
      rw [htC]
      simp
    · have hAD : A * D = B * C := sub_eq_zero.mp hc0
      have htD : (B * D⁻¹) * D = B := by field_simp
      have htC : (B * D⁻¹) * C = A := by
        apply mul_right_cancel₀ hD
        calc
          (B * D⁻¹) * C * D = B * C * (D⁻¹ * D) := by ring
          _ = B * C := by rw [inv_mul_cancel₀ hD, mul_one]
          _ = A * D := hAD.symm
      apply hi.2 (B * D⁻¹)
      rw [← hp', ← hq']
      simp only [smul_add, smul_smul, htC, htD]
  refine ⟨c, hc, ?_⟩
  intro a b
  rw [← hp', ← hq']
  simp only [evaluationDet, evaluation, map_add, map_smul]
  dsimp [c]
  ring

/-- Packet testing is independent of the chosen basis. -/
theorem packet_iff_every_basis {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {ℓ : ℕ} [Fact ℓ.Prime]
    (P : GroupSubspace G ℓ) :
    IsPacket ℓ P ↔
      (∃ p q, IsPlaneBasis P p q) ∧
      ∀ p q, IsPlaneBasis P p q →
        ∀ a b, CupZero ℓ a b → evaluationDet p q a b = 0 := by
  constructor
  · rintro ⟨p, q, hpq, hzero⟩
    refine ⟨⟨p, q, hpq⟩, ?_⟩
    intro p' q' hpq' a b hab
    obtain ⟨c, _, hc⟩ := evaluationDet_change_basis P hpq hpq'
    rw [hc a b, hzero a b hab, mul_zero]
  · rintro ⟨⟨p, q, hpq⟩, hzero⟩
    exact ⟨p, q, hpq, hzero p q hpq⟩

/-- The prime-ideal local plane transported into the group quotient by the
dual Kummer equivalence. -/
def groupLocalPlane {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace M) :
    GroupSubspace (Field.absoluteGaloisGroup M) ℓ :=
  (localD ℓ (primeValuationSubring v)).comap
    (kummerDualEquiv ζ hζ).toLinearMap

/-- A tame group-local plane has dimension two. -/
theorem groupLocalPlane_finrank {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FinitePlace M) (hv : residueCharacteristic v ≠ ℓ) :
    Module.finrank (ZMod ℓ) (groupLocalPlane ζ hζ v) = 2 := by
  rw [groupLocalPlane, Submodule.comap_equiv_eq_map_symm,
    (kummerDualEquiv ζ hζ).symm.finrank_map_eq]
  exact localD_finrank_eq_two ζ hζ v hv

/-- Blueprint packet theorem (`thm:packet`): packets are exactly the local
planes at prime-ideal places of residue characteristic different from
`ℓ`. -/
theorem packet_theorem {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ) :
    {P : GroupSubspace (Field.absoluteGaloisGroup M) ℓ | IsPacket ℓ P} =
      {P | ∃ v : FinitePlace M,
        residueCharacteristic v ≠ ℓ ∧ P = groupLocalPlane ζ hζ v} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, y, hxy, hzero⟩
    let e := kummerDualEquiv ζ hζ
    let p : MulCharacter M ℓ := e x
    let q : MulCharacter M ℓ := e y
    have hind : PairIndependent (k := ZMod ℓ) p q := by
      have hi := hxy.2.2.1.map' e.toLinearMap (by simp)
      change LinearIndependent (ZMod ℓ) (fun i => e (pairVector x y i)) at hi
      have hfun : (fun i => e (pairVector x y i)) = pairVector p q := by
        funext i
        fin_cases i <;> rfl
      rw [hfun] at hi
      exact hi
    have hdet : KummerCupDeterminantCondition ζ hζ p q := by
      intro a b hab
      have hz := hzero (kummerCharacter ζ hζ a)
        (kummerCharacter ζ hζ b) hab
      simpa [evaluationDet, characterDet, p, q, e] using hz
    have halt : AlternatingPair ℓ p q :=
      (cupZero_alternating_iff hℓodd ζ hζ p q hind).2 hdet
    obtain ⟨v, hv, hspan⟩ :=
      exists_tame_local_plane_of_alternating hℓodd ζ hζ p q hind halt
    refine ⟨v, hv, ?_⟩
    calc
      P = pairSpan (k := ZMod ℓ) x y := hxy.2.2.2.symm
      _ = (pairSpan (k := ZMod ℓ) p q).comap e.toLinearMap := by
        rw [Submodule.comap_equiv_eq_map_symm]
        simpa [p, q, e] using (pairSpan_map_linearEquiv e.symm p q).symm
      _ = (localD ℓ (primeValuationSubring v)).comap e.toLinearMap := by
        rw [hspan]
      _ = groupLocalPlane ζ hζ v := rfl
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, y, hxy⟩ :=
      exists_planeBasis_of_finrank_eq_two (groupLocalPlane ζ hζ v)
        (groupLocalPlane_finrank ζ hζ v hv)
    refine ⟨x, y, hxy, ?_⟩
    let e := kummerDualEquiv ζ hζ
    let p : MulCharacter M ℓ := e x
    let q : MulCharacter M ℓ := e y
    have hind : PairIndependent (k := ZMod ℓ) p q := by
      have hi := hxy.2.2.1.map' e.toLinearMap (by simp)
      change LinearIndependent (ZMod ℓ) (fun i => e (pairVector x y i)) at hi
      have hfun : (fun i => e (pairVector x y i)) = pairVector p q := by
        funext i
        fin_cases i <;> rfl
      rw [hfun] at hi
      exact hi
    have hspan : pairSpan (k := ZMod ℓ) p q =
        localD ℓ (primeValuationSubring v) := by
      calc
        pairSpan (k := ZMod ℓ) p q =
            (pairSpan (k := ZMod ℓ) x y).map e.toLinearMap :=
          (pairSpan_map_linearEquiv e x y).symm
        _ = (groupLocalPlane ζ hζ v).map e.toLinearMap := by
          rw [hxy.2.2.2]
        _ = localD ℓ (primeValuationSubring v) := by
          simp [groupLocalPlane, e, Submodule.map_comap_eq]
    have halt : AlternatingPair ℓ p q :=
      alternatingPair_of_valuation hℓodd (primeValuationSubring v) p q
        (satisfiesValuationConclusion_of_span_eq_localD
          ζ hζ v p q hind hspan)
    have hdet := (cupZero_alternating_iff hℓodd ζ hζ p q hind).1 halt
    intro χ ψ hcup
    obtain ⟨a, rfl⟩ := kummerCharacter_surjective ζ hζ χ
    obtain ⟨b, rfl⟩ := kummerCharacter_surjective ζ hζ ψ
    have hz := hdet a b hcup
    simpa [evaluationDet, characterDet, p, q, e] using hz

/-- Two-prime weak approximation in the exact principal-unit form used for
packet separation. -/
theorem weakApproximation_principalUnits {M : Type*} [Field M]
    [NumberField M] (v w : FinitePlace M) (hvw : v ≠ w) (a : Mˣ) :
    ∃ t : Mˣ,
      t ∈ (primeValuationSubring v).principalUnitGroup ∧
        a * t⁻¹ ∈ (primeValuationSubring w).principalUnitGroup := by
  obtain ⟨A, B, _, hfrac⟩ := IsFractionRing.div_surjective (𝓞 M) (a : M)
  have hBK0 : (B : M) ≠ 0 := by
    intro hB0
    change algebraMap (𝓞 M) M B = 0 at hB0
    rw [hB0, div_zero] at hfrac
    exact a.ne_zero hfrac.symm
  have hAK0 : (A : M) ≠ 0 := by
    intro hA0
    change algebraMap (𝓞 M) M A = 0 at hA0
    rw [hA0, zero_div] at hfrac
    exact a.ne_zero hfrac.symm
  let vv := v.valuation M
  let vw := w.valuation M
  have hvB0 : vv (B : M) ≠ 0 := (vv.ne_zero_iff).2 hBK0
  have hwA0 : vw (A : M) ≠ 0 := (vw.ne_zero_iff).2 hAK0
  obtain ⟨nv, hnv⟩ := WithZero.exists_exp_neg_natCast_lt hvB0
  obtain ⟨nw, hnw⟩ := WithZero.exists_exp_neg_natCast_lt hwA0
  let I : Fin 2 → Ideal (𝓞 M) := ![v.asIdeal ^ nv, w.asIdeal ^ nw]
  let z : Fin 2 → 𝓞 M := ![B, A]
  have hvwideal : v.asIdeal ≠ w.asIdeal := by
    intro h
    apply hvw
    exact HeightOneSpectrum.ext h
  have hcop : IsCoprime (v.asIdeal ^ nv) (w.asIdeal ^ nw) :=
    (Ideal.isCoprime_of_isMaximal hvwideal).pow
  have hpair : Pairwise (Function.onFun IsCoprime I) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact hcop
    · exact hcop.symm
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hpair z
  have hxv : x - B ∈ v.asIdeal ^ nv := by
    simpa [I, z] using hx 0
  have hxw : x - A ∈ w.asIdeal ^ nw := by
    simpa [I, z] using hx 1
  have hvcloseNum : vv ((x : M) - (B : M)) < vv (B : M) := by
    apply lt_of_le_of_lt _ hnv
    rw [← map_sub, HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem (x - B) nv).2 hxv
  have hwcloseNum : vw ((x : M) - (A : M)) < vw (A : M) := by
    apply lt_of_le_of_lt _ hnw
    rw [← map_sub, HeightOneSpectrum.valuation_of_algebraMap]
    exact (w.intValuation_le_pow_iff_mem (x - A) nw).2 hxw
  have hwx : vw (x : M) = vw (A : M) := by
    have h := vw.map_add_eq_of_lt_left hwcloseNum
    convert h using 1 <;> ring
  have hx0 : (x : M) ≠ 0 := by
    intro h
    rw [h, map_zero] at hwx
    exact hwA0 hwx.symm
  let t : Mˣ := Units.mk0 ((x : M) / (B : M)) (div_ne_zero hx0 hBK0)
  refine ⟨t, ?_, ?_⟩
  · rw [primeValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      ValuationSubring.mem_principalUnitGroup_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring vv).lt_iff_lt.mp
    change vv ((x : M) / (B : M) - 1) < vv 1
    rw [show (x : M) / (B : M) - 1 =
      ((x : M) - (B : M)) / (B : M) by field_simp]
    rw [vv.map_div, map_one]
    exact (div_lt_one₀ (vv.pos_iff.mpr hBK0)).2 hvcloseNum
  · rw [primeValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      ValuationSubring.mem_principalUnitGroup_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring vw).lt_iff_lt.mp
    have hratio : ((a * t⁻¹ : Mˣ) : M) = (A : M) / (x : M) := by
      change (a : M) * (((x : M) / (B : M))⁻¹) = (A : M) / (x : M)
      rw [← hfrac]
      field_simp
    rw [hratio]
    change vw ((A : M) / (x : M) - 1) < vw 1
    rw [show (A : M) / (x : M) - 1 =
      ((A : M) - (x : M)) / (x : M) by field_simp]
    rw [vw.map_div, map_one, vw.map_sub_swap, hwx]
    exact (div_lt_one₀ (vw.pos_iff.mpr hAK0)).2 hwcloseNum

/-- Blueprint Lemma 6.2 (`lem:packet-separation`): distinct finite places
with two-dimensional local spaces give distinct packet planes. -/
theorem packet_separation {M : Type*} [Field M] [NumberField M]
    {ℓ : ℕ} [Fact ℓ.Prime] (ζ : M) (hζ : IsPrimitiveRoot ζ ℓ)
    {v w : FinitePlace M} (hvw : v ≠ w)
    (hv : residueCharacteristic v ≠ ℓ)
    (hw : residueCharacteristic w ≠ ℓ) :
    groupLocalPlane ζ hζ v ≠ groupLocalPlane ζ hζ w := by
  intro heq
  let e := kummerDualEquiv ζ hζ
  have hlocal : localD ℓ (primeValuationSubring v) =
      localD ℓ (primeValuationSubring w) := by
    have h := congrArg (Submodule.map e.toLinearMap) heq
    simpa [groupLocalPlane, e, Submodule.map_comap_eq] using h
  have hbot : localD ℓ (primeValuationSubring v) = ⊥ := by
    ext p
    constructor
    · intro hp
      rw [Submodule.mem_bot]
      apply AddMonoidHom.ext
      intro z
      cases z with
      | ofMul a =>
        obtain ⟨t, ht, hat⟩ := weakApproximation_principalUnits v w hvw a
        have hpt : p (Additive.ofMul t) = 0 := hp t ht
        have hpw : p ∈ localD ℓ (primeValuationSubring w) := hlocal ▸ hp
        have hpat : p (Additive.ofMul (a * t⁻¹)) = 0 :=
          hpw (a * t⁻¹) hat
        have haeq : Additive.ofMul a =
            Additive.ofMul t + Additive.ofMul (a * t⁻¹) := by
          change Additive.ofMul a = Additive.ofMul (t * (a * t⁻¹))
          congr 1
          simp
        calc
          p (Additive.ofMul a) =
              p (Additive.ofMul t + Additive.ofMul (a * t⁻¹)) :=
            congrArg p haeq
          _ = p (Additive.ofMul t) + p (Additive.ofMul (a * t⁻¹)) :=
            map_add p _ _
          _ = 0 := by rw [hpt, hpat, zero_add]
    · intro hp
      rw [Submodule.mem_bot] at hp
      subst p
      exact Submodule.zero_mem _
  have hrank := localD_finrank_eq_two ζ hζ v hv
  rw [hbot] at hrank
  simp at hrank

/-- The recovered local plane is independent of the chosen primitive root;
the common cyclotomic scalar does not change a subspace. -/
theorem groupLocalPlane_change_primitiveRoot {M : Type*} [Field M]
    [NumberField M] {ℓ : ℕ} [Fact ℓ.Prime]
    (ζ ζ' : M) (hζ : IsPrimitiveRoot ζ ℓ)
    (hζ' : IsPrimitiveRoot ζ' ℓ) (v : FinitePlace M) :
    groupLocalPlane ζ hζ v = groupLocalPlane ζ' hζ' v := by
  obtain ⟨c, hc, hchars⟩ :=
    kummerCharacter_change_primitiveRoot ζ ζ' hζ hζ'
  have heq (x : ElementaryQuotient (Field.absoluteGaloisGroup M) ℓ) :
      kummerDualEquiv ζ' hζ' x = c • kummerDualEquiv ζ hζ x := by
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      rw [kummerDualEquiv_apply, hchars u]
      change evaluationLinear ℓ x (c • kummerCharacter ζ hζ u) =
        c • kummerDualEquiv ζ hζ x (Additive.ofMul u)
      rw [kummerDualEquiv_apply]
      exact map_smul (evaluationLinear ℓ x) c _
  ext x
  change kummerDualEquiv ζ hζ x ∈ localD ℓ (primeValuationSubring v) ↔
    kummerDualEquiv ζ' hζ' x ∈ localD ℓ (primeValuationSubring v)
  rw [heq]
  constructor
  · exact fun h => (localD ℓ (primeValuationSubring v)).smul_mem c h
  · intro h
    have h' := (localD ℓ (primeValuationSubring v)).smul_mem c⁻¹ h
    rw [← mul_smul, inv_mul_cancel₀ hc, one_smul] at h'
    exact h'

end

end NU.LocalTheory
