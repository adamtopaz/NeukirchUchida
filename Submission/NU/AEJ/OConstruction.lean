import Submission.NU.AEJ.Rigid

/-!
# §2. The ring `O_F(H,T)` (AEJ, journal pp. 453–459)

All four objects in Definition 2.2 are kept as sets in the ambient field.  A
claim that such a set is a valuation ring uses `IsValuationRingCarrier`, or an
explicit `ValuationSubring F` witness when its units are also mentioned.
-/

open Pointwise

namespace NU.AEJ

noncomputable section

variable {F : Type*} [Field F]

/-- AEJ, Definition 2.2, journal p. 453:
`O_F⁻(H,T) = {x ∈ F | x ∉ H ∧ 1 + x ∈ T}`.  In particular this is a subset
of all of `F`, not merely of `Ḟ`. -/
def Ominus (H T : Set F) : Set F :=
  {x : F | x ∉ H ∧ 1 + x ∈ T}

/-- AEJ, Definition 2.2, journal p. 453:
`O_F⁺(H,T) = {x ∈ Ḟ | x ∈ H ∧ x O_F⁻(H,T) ⊆ O_F⁻(H,T)}`. -/
def Oplus (H T : Set F) : Set F :=
  {x : F | x ≠ 0 ∧ x ∈ H ∧ x • Ominus H T ⊆ Ominus H T}

/-- AEJ, Definition 2.2, journal p. 453:
`O_F(H,T) = O_F⁻(H,T) ∪ O_F⁺(H,T)`. -/
def O (H T : Set F) : Set F :=
  Ominus H T ∪ Oplus H T

/-- AEJ, Definition 2.2, journal p. 453:
`U_F(H,T) = O_F⁺(H,T) ∩ (O_F⁺(H,T))⁻¹`. -/
def U (H T : Set F) : Set F :=
  {x : F | x ∈ Oplus H T ∧ x⁻¹ ∈ Oplus H T}

/-- The predicate that a set is the carrier of a `T`-compatible valuation
ring.  It packages the wording used in AEJ, Theorem 2.10, journal p. 456. -/
def IsCompatibleValuationRingCarrier (S T : Set F) : Prop :=
  ∃ A : ValuationSubring F,
    (A : Set F) = S ∧ ValuationSubring.IsCompatible A T

private theorem one_mem_basicPart (T : Set F) (hT : IsMulSubgroup T) :
    (1 : F) ∈ basicPart T := by
  rw [basicPart]
  refine ⟨one_ne_zero, ?_⟩
  rintro ⟨h₁, hneg₁⟩
  by_cases hneg : (-1 : F) ∈ T
  · have hz : (0 : F) ∈ T + (1 : F) • T := by
      rw [show (0 : F) = (-1) + 1 by ring]
      exact Set.add_mem_add hneg
        (by simpa using Set.smul_mem_smul_set (a := (1 : F)) hT.one_mem)
    rcases h₁ hz with hz | hz
    · exact hT.zero_notMem hz
    · rcases Set.mem_smul_set.mp hz with ⟨t, ht, ht_eq⟩
      have ht0 : t = 0 := by simpa using ht_eq
      exact hT.zero_notMem (ht0 ▸ ht)
  · have hz : (0 : F) ∈ T + (-1 : F) • T := by
      rw [show (0 : F) = 1 + (-1) • 1 by simp]
      exact Set.add_mem_add hT.one_mem
        (by simpa using Set.smul_mem_smul_set (a := (-1 : F)) hT.one_mem)
    rcases hneg₁ hz with hz | hz
    · exact hT.zero_notMem hz
    · rcases Set.mem_smul_set.mp hz with ⟨t, ht, ht_eq⟩
      have ht0 : t = 0 := by simpa using ht_eq
      exact hT.zero_notMem (ht0 ▸ ht)

private theorem neg_one_mem_basicPart (T : Set F) (hT : IsMulSubgroup T) :
    (-1 : F) ∈ basicPart T := by
  rw [basicPart]
  refine ⟨neg_ne_zero.mpr one_ne_zero, ?_⟩
  simpa [IsBirigid, neg_neg, and_comm] using
    (one_mem_basicPart T hT).2

private theorem rigid_unscale (T : Set F) (hT : IsMulSubgroup T) {c a : F}
    (hc : c ∈ T) : IsRigid T (c * a) → IsRigid T a := by
  intro h q hq
  rcases Set.mem_add.mp hq with ⟨r, hr, s, hs, rfl⟩
  rcases Set.mem_smul_set.mp hs with ⟨v, hv, rfl⟩
  have hm : c * r + (c * a) • v ∈ T + (c * a) • T :=
    Set.add_mem_add (hT.mul_mem hc hr) (Set.smul_mem_smul_set hv)
  rcases h hm with hm | hm
  · left
    have hh := hT.mul_mem (hT.inv_mem hc) hm
    convert hh using 1 <;> field_simp [show c ≠ 0 from fun e => hT.zero_notMem (e ▸ hc)] <;>
      simp [smul_eq_mul] <;> ring
  · right
    rcases Set.mem_smul_set.mp hm with ⟨u, hu, heu⟩
    refine Set.mem_smul_set.mpr ⟨u, hu, ?_⟩
    rw [smul_eq_mul] at heu ⊢
    calc
      a * u = c⁻¹ * (c * a * u) := by
        field_simp [show c ≠ 0 from fun e => hT.zero_notMem (e ▸ hc)]
      _ = c⁻¹ * (c * r + (c * a) * v) := by
        simpa [smul_eq_mul] using congrArg (fun q => c⁻¹ * q) heu
      _ = r + a * v := by
        field_simp [show c ≠ 0 from fun e => hT.zero_notMem (e ▸ hc)]

private theorem rigid_smul_iff (T : Set F) (hT : IsMulSubgroup T) {c a : F}
    (hc : c ∈ T) : IsRigid T (c * a) ↔ IsRigid T a := by
  constructor
  · exact rigid_unscale T hT hc
  · intro ha
    have hh := rigid_unscale T hT (hT.inv_mem hc) (a := c * a)
      (by simpa [mul_assoc, show c ≠ 0 from fun e => hT.zero_notMem (e ▸ hc)] using ha)
    simpa [mul_assoc] using hh

private theorem subset_H (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) : T ⊆ H := by
  intro t ht
  have ht_basic : t ∈ basicPart T := by
    rw [basicPart]
    refine ⟨fun e => hT.zero_notMem (e ▸ ht), ?_⟩
    intro hb
    apply (one_mem_basicPart T hT).2
    constructor
    · simpa using (rigid_smul_iff T hT ht (a := 1)).mp (by simpa using hb.1)
    · simpa using (rigid_smul_iff T hT ht (a := -1)).mp (by simpa using hb.2)
  exact hbasic ht_basic

private theorem neg_one_mem_H (T H : Set F) (hT : IsMulSubgroup T)
    (hbasic : basicPart T ⊆ H) : (-1 : F) ∈ H :=
  hbasic (neg_one_mem_basicPart T hT)

/-- AEJ, Observation 2.3(1), journal p. 453: `O_F⁺(H,T)` is a multiplicative
monoid and `U_F(H,T)` is a subgroup of `Ḟ`. -/
theorem observation_2_3_part1 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) :
    ((1 : F) ∈ Oplus H T ∧
      ∀ ⦃x y : F⦄, x ∈ Oplus H T → y ∈ Oplus H T → x * y ∈ Oplus H T) ∧
      IsMulSubgroup (U H T) := by
  constructor
  · constructor
    · simp [Oplus, hH.one_mem]
    · intro x y hx hy
      rcases hx with ⟨hx0, hxH, hx⟩
      rcases hy with ⟨hy0, hyH, hy⟩
      refine ⟨mul_ne_zero hx0 hy0, hH.mul_mem hxH hyH, ?_⟩
      intro z hz
      rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
      simpa [smul_eq_mul, mul_assoc] using
        hx (Set.smul_mem_smul_set (hy (Set.smul_mem_smul_set hw)))
  · refine { one_mem := ?_, mul_mem := ?_, inv_mem := ?_, zero_notMem := ?_ }
    · exact ⟨by simp [Oplus, hH.one_mem], by simp [Oplus, hH.one_mem]⟩
    · intro x y hx hy
      rcases hx with ⟨hx, hxi⟩
      rcases hy with ⟨hy, hyi⟩
      constructor
      · rcases hx with ⟨hx0, hxH, hx'⟩
        rcases hy with ⟨hy0, hyH, hy'⟩
        refine ⟨mul_ne_zero hx0 hy0, hH.mul_mem hxH hyH, ?_⟩
        intro z hz
        rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
        simpa [smul_eq_mul, mul_assoc] using
          hx' (Set.smul_mem_smul_set (hy' (Set.smul_mem_smul_set hw)))
      · rcases hxi with ⟨hxi0, hxiH, hxi'⟩
        rcases hyi with ⟨hyi0, hyiH, hyi'⟩
        refine ⟨by simpa using mul_ne_zero hyi0 hxi0,
          by simpa using hH.mul_mem hyiH hxiH, ?_⟩
        intro z hz
        rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
        simpa [smul_eq_mul, mul_assoc] using
          hyi' (Set.smul_mem_smul_set (hxi' (Set.smul_mem_smul_set hw)))
    · intro x hx
      rcases hx with ⟨hx, hxi⟩
      exact ⟨hxi, by simpa using hx⟩
    · intro hx
      exact hx.1.1 rfl

/-- AEJ, Observation 2.3(2), journal p. 453: `0 ∈ O_F⁻(H,T)`.  This records
explicitly that `O_F⁻` lives in `F`, rather than in `Ḟ`. -/
theorem observation_2_3_part2 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) :
    (0 : F) ∈ Ominus H T := by
  exact ⟨hH.zero_notMem, by simpa using hT.one_mem⟩

/-- AEJ, Observation 2.3(3), journal pp. 453–454: if `x ∈ Ḟ \ H`, then
`T ∩ xT = ∅`, and exactly one of `x` and `x⁻¹` belongs to `O_F⁻(H,T)`. -/
theorem observation_2_3_part3 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) {x : F}
    (hx0 : x ≠ 0) (hxH : x ∉ H) :
    T ∩ x • T = ∅ ∧ (x ∈ Ominus H T ↔ x⁻¹ ∉ Ominus H T) := by
  have hTH := subset_H T H hT hH hbasic
  have hdisj : T ∩ x • T = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ht
    rcases ht.2 with ⟨u, hu, he⟩
    apply hxH
    have huH := hTH hu
    have htH := hTH ht.1
    have hxiH := hH.mul_mem htH (hH.inv_mem huH)
    have he' : x * u = t := by simpa [smul_eq_mul] using he
    rw [← he'] at hxiH
    have hu0 : u ≠ 0 := fun e => hT.zero_notMem (e ▸ hu)
    simpa [mul_assoc, mul_inv_cancel₀ hu0] using hxiH
  have hbir : IsBirigid T x := by
    by_contra hn
    exact hxH (hbasic ⟨hx0, hn⟩)
  have hchoice : 1 + x ∈ T ∨ 1 + x ∈ x • T := by
    apply hbir.1
    simpa [smul_eq_mul] using
      Set.add_mem_add hT.one_mem (Set.smul_mem_smul_set (a := x) hT.one_mem)
  have hinvH : x⁻¹ ∉ H := by
    intro hi
    apply hxH
    simpa using hH.inv_mem hi
  constructor
  · exact hdisj
  · constructor
    · intro hx hinv
      have hxm : 1 + x ∈ x • T := by
        rw [show 1 + x = x * (1 + x⁻¹) by field_simp; ring]
        exact Set.smul_mem_smul_set hinv.2
      have hfalse : 1 + x ∈ T ∩ x • T := ⟨hx.2, hxm⟩
      rw [hdisj] at hfalse
      exact hfalse
    · intro hinv
      refine ⟨hxH, ?_⟩
      rcases hchoice with hh | hh
      · exact hh
      · exfalso
        apply hinv
        refine ⟨hinvH, ?_⟩
        rcases Set.mem_smul_set.mp hh with ⟨t, ht, he⟩
        rw [smul_eq_mul] at he
        have hxt : 1 + x⁻¹ = t := by
          calc
            1 + x⁻¹ = x⁻¹ * (1 + x) := by field_simp; ring
            _ = x⁻¹ * (x * t) := by rw [he]
            _ = t := by field_simp
        exact hxt ▸ ht

private theorem mem_unitCarrier_iff (A : ValuationSubring F) (x : F) :
    x ∈ ValuationSubring.unitCarrier A ↔ x ≠ 0 ∧ x ∈ A ∧ x⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huval : A.valuation ((u : Fˣ) : F) = 1 :=
      (A.mem_unitGroup_iff u).mp hu
    refine ⟨Units.ne_zero u, (A.valuation_le_one_iff _).mp ?_,
      (A.valuation_le_one_iff _).mp ?_⟩
    · rw [huval]
    · rw [A.valuation.map_inv, huval]
      simp
  · rintro ⟨hx0, hxA, hxiA⟩
    let u : Fˣ := Units.mk0 x hx0
    refine ⟨u, ?_, rfl⟩
    change u ∈ A.unitGroup
    rw [A.mem_unitGroup_iff]
    apply le_antisymm ((A.valuation_le_one_iff _).mpr hxA)
    have hvi : (A.valuation x)⁻¹ ≤ 1 := by
      rw [← A.valuation.map_inv]
      exact (A.valuation_le_one_iff _).mpr hxiA
    exact (inv_le_one₀ (A.valuation.pos_iff.mpr hx0)).mp hvi

/-- AEJ, Observation 2.3(3), journal pp. 453–454, “in particular” clause:
when `O_F(H,T)` is a valuation ring, `O_F⁻` lies in its maximal ideal and its
unit group is exactly `U_F(H,T)`, hence is contained in `H`. -/
theorem observation_2_3_part3_inParticular (T H : Set F)
    (hT : IsMulSubgroup T) (hH : IsMulSubgroup H)
    (hbasic : basicPart T ⊆ H) (A : ValuationSubring F)
    (hA : (A : Set F) = O H T) :
    Ominus H T ⊆ (A.nonunits : Set F) ∧
      U H T = ValuationSubring.unitCarrier A ∧
      ValuationSubring.unitCarrier A ⊆ H := by
  have hminus : Ominus H T ⊆ (A.nonunits : Set F) := by
    intro x hx
    change x ∈ A.nonunits
    rw [A.mem_nonunits_iff_or]
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      intro hxiA
      have hxiO : x⁻¹ ∈ O H T := by rwa [← hA]
      rcases hxiO with hxi | hxi
      · exact ((observation_2_3_part3 T H hT hH hbasic hx0 hx.1).2).mp hx hxi
      · have hone := hxi.2.2 (Set.smul_mem_smul_set hx)
        rw [smul_eq_mul] at hone
        exact hone.1 (by simpa [hx0] using hH.one_mem)
  refine ⟨hminus, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hxi⟩
      apply (mem_unitCarrier_iff A x).mpr
      refine ⟨hx.1, ?_, ?_⟩
      · change x ∈ (A : Set F)
        rw [hA]
        exact Or.inr hx
      · change x⁻¹ ∈ (A : Set F)
        rw [hA]
        exact Or.inr hxi
    · intro hx
      rcases (mem_unitCarrier_iff A x).mp hx with ⟨hx0, hxA, hxiA⟩
      have hunit_not_nonunit : x ∉ A.nonunits := by
        rw [A.mem_nonunits_iff_or]
        exact not_or.mpr ⟨hx0, not_not.mpr hxiA⟩
      have hxplus : x ∈ Oplus H T := by
        have hxO : x ∈ O H T := by rwa [← hA]
        rcases hxO with hxminus | hxplus
        · exact False.elim (hunit_not_nonunit (hminus hxminus))
        · exact hxplus
      have hxi0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
      have hxi_not_nonunit : x⁻¹ ∉ A.nonunits := by
        rw [A.mem_nonunits_iff_or]
        simpa using not_or.mpr ⟨hxi0, not_not.mpr hxA⟩
      have hxiplus : x⁻¹ ∈ Oplus H T := by
        have hxiO : x⁻¹ ∈ O H T := by rwa [← hA]
        rcases hxiO with hximinus | hxiplus
        · exact False.elim (hxi_not_nonunit (hminus hximinus))
        · exact hxiplus
      exact ⟨hxplus, hxiplus⟩
  · rw [← show U H T = ValuationSubring.unitCarrier A from by
      ext x
      constructor
      · rintro ⟨hx, hxi⟩
        exact (mem_unitCarrier_iff A x).mpr ⟨hx.1, by
          change x ∈ (A : Set F)
          rw [hA]
          exact Or.inr hx, by
          change x⁻¹ ∈ (A : Set F)
          rw [hA]
          exact Or.inr hxi⟩
      · intro hx
        rcases (mem_unitCarrier_iff A x).mp hx with ⟨hx0, hxA, hxiA⟩
        have hn : x ∉ A.nonunits := by
          rw [A.mem_nonunits_iff_or]
          exact not_or.mpr ⟨hx0, not_not.mpr hxiA⟩
        have hni : x⁻¹ ∉ A.nonunits := by
          rw [A.mem_nonunits_iff_or]
          simpa using not_or.mpr ⟨inv_ne_zero hx0, not_not.mpr hxA⟩
        constructor
        · have := show x ∈ O H T by rwa [← hA]
          rcases this with h | h
          · exact False.elim (hn (hminus h))
          · exact h
        · have := show x⁻¹ ∈ O H T by rwa [← hA]
          rcases this with h | h
          · exact False.elim (hni (hminus h))
          · exact h]
    intro x hx
    exact hx.1.2.1

/-- AEJ, Observation 2.3(4), journal p. 454: if
`x ∈ H \ O_F⁺(H,T)`, then `x⁻¹` is a product of two elements of `O_F⁻`. -/
theorem observation_2_3_part4 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) {x : F}
    (hxH : x ∈ H) (hxplus : x ∉ Oplus H T) :
    ∃ y ∈ Ominus H T, ∃ z ∈ Ominus H T, x * y * z = 1 := by
  have hx0 : x ≠ 0 := fun e => hH.zero_notMem (e ▸ hxH)
  have hxy : ¬ x • Ominus H T ⊆ Ominus H T := by
    intro hs
    apply hxplus
    exact ⟨hx0, hxH, hs⟩
  rcases Set.not_subset.mp hxy with ⟨w, hw, hw_not⟩
  rcases Set.mem_smul_set.mp hw with ⟨y, hy, hxy_eq⟩
  rw [smul_eq_mul] at hxy_eq
  have hxy_not : x * y ∉ Ominus H T := by
    intro h
    apply hw_not
    rwa [← hxy_eq]
  have hxyH : x * y ∉ H := by
    intro h
    apply hy.1
    have hh := hH.mul_mem (hH.inv_mem hxH) h
    have heq : y = x⁻¹ * (x * y) := by field_simp
    exact heq ▸ hh
  have hxy0 : x * y ≠ 0 := by
    intro e
    apply hxy_not
    rw [e]
    exact observation_2_3_part2 T H hT hH hbasic
  have hi := (observation_2_3_part3 T H hT hH hbasic hxy0 hxyH).2
  have hz : (x * y)⁻¹ ∈ Ominus H T := by
    by_contra hn
    exact hxy_not (hi.mpr hn)
  refine ⟨y, hy, (x * y)⁻¹, hz, ?_⟩
  exact mul_inv_cancel₀ hxy0

/-- AEJ, Observation 2.3(5), journal p. 454: `O_F⁻(H,T)` is closed under the
transformation `x ↦ -x/(1+x)`. -/
theorem observation_2_3_part5 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) {x : F}
    (hx : x ∈ Ominus H T) :
    -x / (1 + x) ∈ Ominus H T := by
  have hTH := subset_H T H hT hH hbasic
  have hden : 1 + x ≠ 0 := fun e => hT.zero_notMem (e ▸ hx.2)
  refine ⟨?_, ?_⟩
  · intro hn
    apply hx.1
    have hh := hH.mul_mem (neg_one_mem_H T H hT hbasic)
      (hH.mul_mem hn (hTH hx.2))
    field_simp at hh
    simpa using hh
  · convert hT.inv_mem hx.2 using 1 <;> field_simp <;> ring

/-- AEJ, Observation 2.3(6), journal p. 454: every valuation ring `A` is
recovered as `O_F(U_A,1+𝔪_A)`, with the displayed identifications of its
maximal ideal and unit group. -/
theorem observation_2_3_part6 (A : ValuationSubring F) :
    (A.nonunits : Set F) =
        Ominus (ValuationSubring.unitCarrier A)
          (ValuationSubring.onePlusMaximalIdeal A) ∧
      ValuationSubring.unitCarrier A =
        Oplus (ValuationSubring.unitCarrier A)
          (ValuationSubring.onePlusMaximalIdeal A) ∧
      (A : Set F) =
        O (ValuationSubring.unitCarrier A)
          (ValuationSubring.onePlusMaximalIdeal A) := by
  have hnotunit : ∀ {x : F}, x ∈ A.nonunits →
      x ∉ ValuationSubring.unitCarrier A := by
    intro x hx hu
    rcases (mem_unitCarrier_iff A x).mp hu with ⟨hx0, -, hxiA⟩
    rw [A.mem_nonunits_iff_or] at hx
    exact (not_or.mpr ⟨hx0, not_not.mpr hxiA⟩) hx
  have hminus : (A.nonunits : Set F) =
      Ominus (ValuationSubring.unitCarrier A)
        (ValuationSubring.onePlusMaximalIdeal A) := by
    ext x
    constructor
    · intro hx
      refine ⟨hnotunit hx, ?_⟩
      exact Set.add_mem_add (by simp) hx
    · rintro ⟨hxunit, hxone⟩
      rcases Set.mem_add.mp hxone with ⟨a, ha, m, hm, ham⟩
      have ha' : a = 1 := by simpa using ha
      rw [ha'] at ham
      have hxm : x = m := by
        calc
          x = 1 + x - 1 := by ring
          _ = 1 + m - 1 := by rw [ham]
          _ = m := by ring
      exact hxm ▸ hm
  have hplus : ValuationSubring.unitCarrier A =
      Oplus (ValuationSubring.unitCarrier A)
        (ValuationSubring.onePlusMaximalIdeal A) := by
    ext x
    constructor
    · intro hx
      rcases (mem_unitCarrier_iff A x).mp hx with ⟨hx0, hxA, hxiA⟩
      refine ⟨hx0, hx, ?_⟩
      rintro z ⟨y, hy, rfl⟩
      have hy' : y ∈ A.nonunits := by
        change y ∈ (A.nonunits : Set F)
        rw [hminus]
        exact hy
      have hxy : x * y ∈ A.nonunits := by
        rw [A.mem_nonunits_iff_or] at hy' ⊢
        rcases hy' with hy0 | hyi
        · left
          simp [hy0]
        · right
          intro h
          apply hyi
          have hh := A.mul_mem _ _ h hxA
          have heq : (x * y)⁻¹ * x = y⁻¹ := by field_simp [hx0]
          exact heq ▸ hh
      rw [← hminus]
      exact hxy
    · intro hx
      exact hx.2.1
  refine ⟨hminus, hplus, ?_⟩
  ext x
  constructor
  · intro hx
    have hxval := (A.valuation_le_one_iff x).mpr hx
    rcases lt_or_eq_of_le hxval with hlt | heq
    · left
      rw [← hminus]
      change x ∈ A.nonunits
      rw [A.mem_nonunits_iff]
      exact hlt
    · right
      rw [← hplus]
      apply (mem_unitCarrier_iff A x).mpr
      have hx0 : x ≠ 0 := by
        intro hzero
        rw [hzero, A.valuation.map_zero] at heq
        exact zero_ne_one heq
      refine ⟨hx0, hx, ?_⟩
      apply (A.valuation_le_one_iff _).mp
      rw [A.valuation.map_inv, heq]
      simp
  · rintro (hx | hx)
    · rw [← hminus] at hx
      exact A.nonunits_subset hx
    · rw [← hplus] at hx
      exact (mem_unitCarrier_iff A x).mp hx |>.2.1

/-- AEJ, Definition 2.4, journal p. 454: `O_F(H,T)` is preadditive when
`1 + O_F⁻(H,T) ⊆ O_F⁺(H,T)`. -/
def IsPreadditive (H T : Set F) : Prop :=
  ({1} : Set F) + Ominus H T ⊆ Oplus H T

private theorem mem_one_sub_iff (T : Set F) (a : F) :
    a ∈ ({1} : Set F) - T ↔ 1 - a ∈ T := by
  constructor
  · rintro ⟨b, hb, t, ht, he⟩
    have hb' : b = 1 := by simpa using hb
    rw [hb'] at he
    rw [← he]
    ring_nf
    exact ht
  · intro ha
    refine ⟨1, by simp, 1 - a, ha, ?_⟩
    ring

/-- AEJ, Lemma 2.6(1)–(2), journal p. 454: preadditivity is equivalent to
`O_F⁻(H,T) O_F⁻(H,T) ⊆ 1 - T`. -/
theorem lemma_2_6 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) :
    IsPreadditive H T ↔
      Ominus H T * Ominus H T ⊆ ({1} : Set F) - T := by
  constructor
  · intro hpre w hw
    rcases Set.mem_mul.mp hw with ⟨x, hx, y, hy, rfl⟩
    have hxplus : 1 + x ∈ Oplus H T := hpre
      (show 1 + x ∈ ({1} : Set F) + Ominus H T from
        Set.add_mem_add (by simp) hx)
    have hy' := observation_2_3_part5 T H hT hH hbasic hy
    have hr : (1 + x) * (-y / (1 + y)) ∈ Ominus H T := by
      simpa [smul_eq_mul] using hxplus.2.2 (Set.smul_mem_smul_set hy')
    apply (mem_one_sub_iff T _).mpr
    have hm := hT.mul_mem hy.2 hr.2
    have hy0 : 1 + y ≠ 0 := fun e => hT.zero_notMem (e ▸ hy.2)
    convert hm using 1 <;> field_simp [hy0] <;> ring
  · intro hprod
    intro w hw
    rcases Set.mem_add.mp hw with ⟨a, ha, x, hx, hax⟩
    have ha' : a = 1 := by simpa using ha
    subst a
    subst w
    have hTH := subset_H T H hT hH hbasic
    have hden : 1 + x ≠ 0 := fun e => hT.zero_notMem (e ▸ hx.2)
    refine ⟨hden, hTH hx.2, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hy' := observation_2_3_part5 T H hT hH hbasic hy
    have hp := hprod (Set.mul_mem_mul hx hy')
    have hpT : 1 - x * (-y / (1 + y)) ∈ T :=
      (mem_one_sub_iff T _).mp hp
    have hTgoal : 1 + (1 + x) * y ∈ T := by
      have hm := hT.mul_mem hy.2 hpT
      have hyden : 1 + y ≠ 0 := fun e => hT.zero_notMem (e ▸ hy.2)
      convert hm using 1 <;> field_simp [hyden] <;> ring
    refine ⟨?_, hTgoal⟩
    intro hxy
    apply hy.1
    have hh := hH.mul_mem (hH.inv_mem (hTH hx.2)) hxy
    have heq : y = (1 + x)⁻¹ * ((1 + x) * y) := by field_simp
    exact heq ▸ hh

/-- AEJ, Lemma 2.6(3), journal p. 454: under preadditivity, if `x ≠ 0`,
`1+x ∈ O_F⁺`, and `y ∈ O_F⁻`, then `1-xy ∈ T ∩ O_F⁺`. -/
theorem lemma_2_6_part3 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hpre : IsPreadditive H T) {x y : F} (hx0 : x ≠ 0)
    (hx : 1 + x ∈ Oplus H T) (hy : y ∈ Ominus H T) :
    1 - x * y ∈ T ∩ Oplus H T := by
  have hy' := observation_2_3_part5 T H hT hH hbasic hy
  have hr : (1 + x) * (-y / (1 + y)) ∈ Ominus H T := by
    simpa [smul_eq_mul] using hx.2.2 (Set.smul_mem_smul_set hy')
  have hone_r : 1 + (1 + x) * (-y / (1 + y)) ∈ Oplus H T :=
    hpre (Set.add_mem_add (by simp) hr)
  have hone_y : 1 + y ∈ Oplus H T :=
    hpre (Set.add_mem_add (by simp) hy)
  have hmonoid := (observation_2_3_part1 T H hT hH hbasic).1.2
  refine ⟨?_, ?_⟩
  · have hm := hT.mul_mem hy.2 hr.2
    have hyden : 1 + y ≠ 0 := fun e => hT.zero_notMem (e ▸ hy.2)
    convert hm using 1 <;> field_simp [hyden] <;> ring
  · have hm := hmonoid hone_y hone_r
    have hyden : 1 + y ≠ 0 := fun e => hT.zero_notMem (e ▸ hy.2)
    convert hm using 1 <;> field_simp [hyden] <;> ring

/-- AEJ, equation (2.7), journal p. 454: under preadditivity,
`x,z ∈ O_F⁻(H,T)` implies `1 + (1+x)z ∈ T`. -/
theorem equation_2_7 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hpre : IsPreadditive H T) {x z : F}
    (hx : x ∈ Ominus H T) (hz : z ∈ Ominus H T) :
    1 + (1 + x) * z ∈ T := by
  have hxplus : 1 + x ∈ Oplus H T :=
    hpre (Set.add_mem_add (by simp) hx)
  have hz' : (1 + x) * z ∈ Ominus H T := by
    simpa [smul_eq_mul] using hxplus.2.2 (Set.smul_mem_smul_set hz)
  exact hz'.2

/-- AEJ, equation (2.8), journal p. 455: under preadditivity,
`x,y ∈ O_F⁻(H,T)` implies `1 + (1+x)(-y/(1+y)) ∈ T`. -/
theorem equation_2_8 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hpre : IsPreadditive H T) {x y : F}
    (hx : x ∈ Ominus H T) (hy : y ∈ Ominus H T) :
    1 + (1 + x) * (-y / (1 + y)) ∈ T := by
  have hxplus : 1 + x ∈ Oplus H T :=
    hpre (Set.add_mem_add (by simp) hx)
  have hy' := observation_2_3_part5 T H hT hH hbasic hy
  have hy'' : (1 + x) * (-y / (1 + y)) ∈ Ominus H T := by
    simpa [smul_eq_mul] using hxplus.2.2 (Set.smul_mem_smul_set hy')
  exact hy''.2

/-- AEJ, Lemma 2.9(1)–(3), journal p. 455: the three structural consequences
of preadditivity used to prove that `O_F(H,T)` is a valuation ring. -/
theorem lemma_2_9 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hpre : IsPreadditive H T) :
    ((Ominus H T * Ominus H T) ∩ H ⊆ Oplus H T) ∧
      (∀ x : F, x ∉ O H T → x⁻¹ ∈ O H T) ∧
      (-1 : F) ∈ Oplus H T := by
  have hpart1 : (Ominus H T * Ominus H T) ∩ H ⊆ Oplus H T := by
    rintro w ⟨hw, hwH⟩
    rcases Set.mem_mul.mp hw with ⟨x, hx, y, hy, rfl⟩
    have hxy0 : x * y ≠ 0 := fun hzero => hH.zero_notMem (hzero ▸ hwH)
    have hx0 : x ≠ 0 := fun hzero => hxy0 (by simp [hzero])
    have hfirst := lemma_2_6_part3 T H hT hH hbasic hpre hx0
      (hpre (Set.add_mem_add (by simp) hx)) hy
    refine ⟨hxy0, hwH, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    have hnotH : x * y * z ∉ H := by
      intro hxyzH
      apply hz.1
      have hh := hH.mul_mem (hH.inv_mem hwH) hxyzH
      have heq : z = (x * y)⁻¹ * (x * y * z) := by
        rw [← mul_assoc, inv_mul_cancel₀ hxy0, one_mul]
      exact heq ▸ hh
    refine ⟨hnotH, ?_⟩
    have hsecond := lemma_2_6_part3 T H hT hH hbasic hpre
      (neg_ne_zero.mpr hxy0) (by simpa [sub_eq_add_neg] using hfirst.2) hz
    convert hsecond.1 using 1 <;> ring
  have hpart2 : ∀ x : F, x ∉ O H T → x⁻¹ ∈ O H T := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hx
      left
      simpa [hzero] using observation_2_3_part2 T H hT hH hbasic
    by_cases hxH : x ∈ H
    · have hxplus : x ∉ Oplus H T := fun h => hx (Or.inr h)
      rcases observation_2_3_part4 T H hT hH hbasic hxH hxplus with
        ⟨y, hy, z, hz, hxyz⟩
      have hyz_eq : y * z = x⁻¹ := by
        calc
          y * z = (x⁻¹ * x) * (y * z) := by rw [inv_mul_cancel₀ hx0, one_mul]
          _ = x⁻¹ * (x * y * z) := by ring
          _ = x⁻¹ := by rw [hxyz, mul_one]
      have hyzH : y * z ∈ H := by
        rw [hyz_eq]
        exact hH.inv_mem hxH
      exact Or.inr (hyz_eq ▸ hpart1 ⟨Set.mul_mem_mul hy hz, hyzH⟩)
    · have hxi : x⁻¹ ∈ Ominus H T := by
        by_contra hxi
        apply hx
        left
        exact (observation_2_3_part3 T H hT hH hbasic hx0 hxH).2.mpr hxi
      exact Or.inl hxi
  refine ⟨hpart1, hpart2, ?_⟩
  have hnegH := neg_one_mem_H T H hT hbasic
  by_cases hnegO : (-1 : F) ∈ O H T
  · rcases hnegO with hminus | hplus
    · exact False.elim (hminus.1 hnegH)
    · exact hplus
  · have hinv := hpart2 (-1 : F) hnegO
    have hnegInvH : (-1 : F)⁻¹ ∈ H := by simpa using hnegH
    simpa using (hinv.resolve_left (fun hminus => hminus.1 hnegInvH))

/-- AEJ, Theorem 2.10, journal p. 456: if `O_F(H,T)` is preadditive, it is a
`T`-compatible valuation ring and its units satisfy `U_A · T ⊆ H`. -/
theorem theorem_2_10 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hpre : IsPreadditive H T) :
    ∃ A : ValuationSubring F,
      (A : Set F) = O H T ∧
        ValuationSubring.IsCompatible A T ∧
        ValuationSubring.unitCarrier A * T ⊆ H := by
  have h29 := lemma_2_9 T H hT hH hbasic hpre
  have hmul : ∀ ⦃x y : F⦄, x ∈ O H T → y ∈ O H T → x * y ∈ O H T := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · by_cases hxyH : x * y ∈ H
      · exact Or.inr (h29.1 ⟨Set.mul_mem_mul hx hy, hxyH⟩)
      · left
        refine ⟨hxyH, ?_⟩
        have hnegx : -x ∈ Ominus H T := by
          simpa [smul_eq_mul] using h29.2.2.2.2 (Set.smul_mem_smul_set hx)
        have hp := (lemma_2_6 T H hT hH hbasic).mp hpre
          (Set.mul_mem_mul hnegx hy)
        have hpT := (mem_one_sub_iff T ((-x) * y)).mp hp
        convert hpT using 1 <;> ring
    · exact Or.inl (by
        simpa [smul_eq_mul, mul_comm] using
          hy.2.2 (Set.smul_mem_smul_set hx))
    · exact Or.inl (by
        simpa [smul_eq_mul] using hx.2.2 (Set.smul_mem_smul_set hy))
    · exact Or.inr ((observation_2_3_part1 T H hT hH hbasic).1.2 hx hy)
  have hone_add : ∀ ⦃z : F⦄, z ∈ O H T → 1 + z ∈ O H T := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inr (hpre (Set.add_mem_add (by simp) hz))
    · by_cases honez0 : 1 + z = 0
      · left
        rw [honez0]
        exact observation_2_3_part2 T H hT hH hbasic
      have hnegz : -z ∈ Oplus H T := by
        have hm := (observation_2_3_part1 T H hT hH hbasic).1.2 h29.2.2 hz
        simpa using hm
      have hall : ∀ y ∈ Ominus H T, 1 + (1 + z) * y ∈ T := by
        intro y hy
        have hp := lemma_2_6_part3 T H hT hH hbasic hpre
          (neg_ne_zero.mpr honez0) (by simpa [sub_eq_add_neg] using hnegz) hy
        convert hp.1 using 1 <;> ring
      by_cases honezH : 1 + z ∈ H
      · right
        refine ⟨honez0, honezH, ?_⟩
        rintro q ⟨y, hy, rfl⟩
        change (1 + z) * y ∈ Ominus H T
        refine ⟨?_, hall y hy⟩
        intro hprodH
        apply hy.1
        have hh := hH.mul_mem (hH.inv_mem honezH) hprodH
        have heq : y = (1 + z)⁻¹ * ((1 + z) * y) := by
          rw [← mul_assoc, inv_mul_cancel₀ honez0, one_mul]
        exact heq ▸ hh
      · have hnegonez0 : -(1 + z) ≠ 0 := neg_ne_zero.mpr honez0
        have hnegonezH : -(1 + z) ∉ H := by
          intro hh
          apply honezH
          have hm := hH.mul_mem (neg_one_mem_H T H hT hbasic) hh
          simpa using hm
        have hinv_not : (-(1 + z))⁻¹ ∉ Ominus H T := by
          intro hi
          have ht := hall (-(1 + z))⁻¹ hi
          have heq : 1 + (1 + z) * (-(1 + z))⁻¹ = 0 := by
            rw [inv_neg, mul_neg, mul_inv_cancel₀ honez0]
            ring
          exact hT.zero_notMem (heq ▸ ht)
        have hnegonez : -(1 + z) ∈ Ominus H T :=
          (observation_2_3_part3 T H hT hH hbasic hnegonez0 hnegonezH).2.mpr
            hinv_not
        left
        have hm := h29.2.2.2.2 (Set.smul_mem_smul_set hnegonez)
        simpa [smul_eq_mul] using hm
  have hadd : ∀ ⦃x y : F⦄, x ∈ O H T → y ∈ O H T → x + y ∈ O H T := by
    intro x y hx hy
    by_cases hx0 : x = 0
    · simpa [hx0] using hy
    by_cases hy0 : y = 0
    · simpa [hy0] using hx
    by_cases hratio : x * y⁻¹ ∈ O H T
    · have hsum := hmul hy (hone_add hratio)
      convert hsum using 1 <;> field_simp <;> ring
    · have hinv := h29.2.1 (x * y⁻¹) hratio
      have hratio' : y * x⁻¹ ∈ O H T := by
        convert hinv using 1 <;> field_simp <;> ring
      have hsum := hmul hx (hone_add hratio')
      convert hsum using 1 <;> field_simp <;> ring
  have hneg : ∀ ⦃x : F⦄, x ∈ O H T → -x ∈ O H T := by
    intro x hx
    have hm := hmul (Or.inr h29.2.2) hx
    simpa using hm
  let R : Subring F :=
    { carrier := O H T
      zero_mem' := Or.inl (observation_2_3_part2 T H hT hH hbasic)
      one_mem' := Or.inr (observation_2_3_part1 T H hT hH hbasic).1.1
      add_mem' := fun ha hb => hadd ha hb
      mul_mem' := fun ha hb => hmul ha hb
      neg_mem' := fun hx => hneg hx }
  have hval : ∀ x : F, x ∈ R ∨ x⁻¹ ∈ R := by
    intro x
    change x ∈ O H T ∨ x⁻¹ ∈ O H T
    by_cases hx : x ∈ O H T
    · exact Or.inl hx
    · exact Or.inr (h29.2.1 x hx)
  let A : ValuationSubring F := ValuationSubring.ofSubring R hval
  have hA : (A : Set F) = O H T := by
    change (R : Set F) = O H T
    rfl
  have hobs := observation_2_3_part3_inParticular T H hT hH hbasic A hA
  have hone_nonunit : ∀ {x : F}, x ∈ A.nonunits → 1 + x ∈ T := by
    intro x hx
    have hxA : x ∈ O H T := by
      rw [← hA]
      exact A.nonunits_subset hx
    rcases hxA with hxminus | hxplus
    · exact hxminus.2
    · have hx0 := hxplus.1
      have hxi_not_plus : x⁻¹ ∉ Oplus H T := by
        intro hxi
        have hxU : x ∈ U H T := ⟨hxplus, hxi⟩
        have hxunit : x ∈ ValuationSubring.unitCarrier A := hobs.2.1 ▸ hxU
        rcases (mem_unitCarrier_iff A x).mp hxunit with ⟨-, -, hxiA⟩
        rw [A.mem_nonunits_iff_or] at hx
        exact hx.elim hx0 (fun hn => hn hxiA)
      rcases observation_2_3_part4 T H hT hH hbasic
          (hH.inv_mem hxplus.2.1) hxi_not_plus with ⟨y, hy, z, hz, hyz⟩
      have hyz_eq : y * z = x := by
        calc
          y * z = x * (x⁻¹ * (y * z)) := by field_simp
          _ = x * (x⁻¹ * y * z) := by ring
          _ = x := by rw [hyz, mul_one]
      have hnegy : -y ∈ Ominus H T := by
        simpa [smul_eq_mul] using h29.2.2.2.2 (Set.smul_mem_smul_set hy)
      have hp := (lemma_2_6 T H hT hH hbasic).mp hpre
        (Set.mul_mem_mul hnegy hz)
      have hpT := (mem_one_sub_iff T ((-y) * z)).mp hp
      have heq : 1 + x = 1 - (-y) * z := by rw [← hyz_eq]; ring
      exact heq ▸ hpT
  have hcompat : ValuationSubring.IsCompatible A T := by
    rintro p ⟨u, hu, rfl⟩
    have hnon : ((u : F) - 1) ∈ A.nonunits := by
      apply A.mem_nonunits_iff.mpr
      exact (A.mem_principalUnitGroup_iff u).mp hu
    have ht := hone_nonunit hnon
    convert ht using 1 <;> ring
  refine ⟨A, hA, hcompat, ?_⟩
  rintro q ⟨u, hu, t, ht, rfl⟩
  exact hH.mul_mem (hobs.2.2 hu) ((subset_H T H hT hH hbasic) ht)

/-- AEJ, Corollary 2.11, journal p. 456, first assertion: if
`T ⊆ T̂ ⊆ H`, then `B_F(T̂) ⊆ H` (under the standing assumption
`B_F(T) ⊆ H`). -/
theorem corollary_2_11_basicPart (T T_hat H : Set F)
    (hT : IsMulSubgroup T) (hT_hat : IsMulSubgroup T_hat)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hT_le : T ⊆ T_hat) (hT_hat_le : T_hat ⊆ H) :
    basicPart T_hat ⊆ H := by
  have hout_rigid : ∀ {a : F}, a ≠ 0 → a ∉ H → IsRigid T a := by
    intro a ha0 haH
    by_contra hr
    exact haH (hbasic ⟨ha0, fun hbir => hr hbir.1⟩)
  have lift_rigid : ∀ {a : F}, a ≠ 0 → a ∉ H → IsRigid T_hat a := by
    intro a ha0 haH q hq
    rcases Set.mem_add.mp hq with ⟨s, hs, w, hw, rfl⟩
    rcases Set.mem_smul_set.mp hw with ⟨t, ht, rfl⟩
    have hs0 : s ≠ 0 := fun e => hT_hat.zero_notMem (e ▸ hs)
    let r := t * s⁻¹
    have hr : r ∈ T_hat := hT_hat.mul_mem ht (hT_hat.inv_mem hs)
    have hr0 : r ≠ 0 := fun e => hT_hat.zero_notMem (e ▸ hr)
    have har0 : a * r ≠ 0 := mul_ne_zero ha0 hr0
    have harH : a * r ∉ H := by
      intro hh
      apply haH
      have hrH := hT_hat_le hr
      have hm := hH.mul_mem hh (hH.inv_mem hrH)
      have heq : a = a * r * r⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hr0, mul_one]
      exact heq ▸ hm
    have hnorm := hout_rigid har0 harH
      (Set.add_mem_add hT.one_mem (Set.smul_mem_smul_set hT.one_mem))
    have hnorm' : 1 + a * r ∈ T ∪ (a * r) • T := by
      simpa [smul_eq_mul] using hnorm
    rcases hnorm' with hnorm | ⟨v, hv, hev⟩
    · left
      have hm := hT_hat.mul_mem hs (hT_le hnorm)
      convert hm using 1 <;> dsimp [r] <;> field_simp <;> ring
    · right
      refine ⟨s * r * v, hT_hat.mul_mem (hT_hat.mul_mem hs hr) (hT_le hv), ?_⟩
      change (a * r) * v = 1 + a * r at hev
      change a * (s * r * v) = s + a * t
      calc
        a * (s * r * v) = s * ((a * r) * v) := by ring
        _ = s * (1 + a * r) := by rw [hev]
        _ = s + a * t := by dsimp [r]; field_simp
  rintro b ⟨hb0, hb⟩
  by_contra hbH
  apply hb
  refine ⟨lift_rigid hb0 hbH, lift_rigid (neg_ne_zero.mpr hb0) ?_⟩
  intro hnegbH
  apply hbH
  have hm := hH.mul_mem (neg_one_mem_H T H hT hbasic) hnegbH
  simpa using hm

/-- AEJ, Corollary 2.11(1)–(2), journal p. 456: enlarging `H` enlarges the
constructed valuation ring, while enlarging `T` to `T̂ ⊆ H` leaves
`O_F(H,T)` unchanged. -/
theorem corollary_2_11 (T T_hat H H_hat : Set F)
    (hT : IsMulSubgroup T) (hT_hat : IsMulSubgroup T_hat)
    (hH : IsMulSubgroup H) (hH_hat : IsMulSubgroup H_hat)
    (hbasic : basicPart T ⊆ H) (hT_le : T ⊆ T_hat)
    (hT_hat_le : T_hat ⊆ H) (hH_le : H ⊆ H_hat)
    (A : ValuationSubring F) (hA : (A : Set F) = O H T)
    (hcompat : ValuationSubring.IsCompatible A T) :
    (∃ A_hat : ValuationSubring F,
      (A_hat : Set F) = O H_hat T ∧
        ValuationSubring.IsCompatible A_hat T ∧ A ≤ A_hat) ∧
      O H T = O H T_hat := by
  have hobs := observation_2_3_part3_inParticular T H hT hH hbasic A hA
  have hpre_old : IsPreadditive H T := by
    apply (lemma_2_6 T H hT hH hbasic).mpr
    rintro q ⟨x, hx, y, hy, rfl⟩
    apply (mem_one_sub_iff T (x * y)).mpr
    have hxy_non : x * y ∈ A.nonunits := A.nonunits.mul_mem (hobs.1 hx) (hobs.1 hy)
    have hneg_non : -(x * y) ∈ A.nonunits := A.nonunits.neg_mem hxy_non
    have hv : A.valuation (-(x * y)) < 1 := A.mem_nonunits_iff.mp hneg_non
    have hone0 : 1 - x * y ≠ 0 := by
      intro heq
      have hval := A.valuation.map_one_add_of_lt hv
      have hone_eq : 1 + -(x * y) = 1 - x * y := by ring
      rw [hone_eq, heq, A.valuation.map_zero] at hval
      exact zero_ne_one hval
    let u : Fˣ := Units.mk0 (1 - x * y) hone0
    apply hcompat
    refine ⟨u, ?_, rfl⟩
    change u ∈ A.principalUnitGroup
    rw [A.mem_principalUnitGroup_iff]
    change A.valuation ((1 - x * y) - 1) < 1
    convert hv using 1 <;> ring
  have hminus_le : Ominus H_hat T ⊆ Ominus H T := by
    rintro x ⟨hxH, hxT⟩
    exact ⟨fun hx => hxH (hH_le hx), hxT⟩
  have hpre_hat : IsPreadditive H_hat T := by
    apply (lemma_2_6 T H_hat hT hH_hat (hbasic.trans hH_le)).mpr
    intro q hq
    rcases Set.mem_mul.mp hq with ⟨x, hx, y, hy, rfl⟩
    exact (lemma_2_6 T H hT hH hbasic).mp hpre_old
      (Set.mul_mem_mul (hminus_le hx) (hminus_le hy))
  rcases theorem_2_10 T H_hat hT hH_hat (hbasic.trans hH_le) hpre_hat with
    ⟨A_hat, hA_hat, hcompat_hat, -⟩
  have hO_le : O H T ⊆ O H_hat T := by
    intro x hx
    by_cases hxHhat : x ∈ H_hat
    · right
      have hx0 : x ≠ 0 := fun e => hH_hat.zero_notMem (e ▸ hxHhat)
      refine ⟨hx0, hxHhat, ?_⟩
      rintro q ⟨y, hy, rfl⟩
      change x * y ∈ Ominus H_hat T
      have hyold := hminus_le hy
      have hxyold : x * y ∈ O H T := by
        rw [← hA]
        exact A.mul_mem x y (by
          change x ∈ (A : Set F)
          rw [hA]
          exact hx) (by
          change y ∈ (A : Set F)
          rw [hA]
          exact Or.inl hyold)
      have hxy_not : x * y ∉ H_hat := by
        intro hxyH
        apply hy.1
        have hh := hH_hat.mul_mem (hH_hat.inv_mem hxHhat) hxyH
        have heq : y = x⁻¹ * (x * y) := by
          rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
        exact heq ▸ hh
      rcases hxyold with hxyminus | hxyplus
      · exact ⟨hxy_not, hxyminus.2⟩
      · exact False.elim (hxy_not (hH_le hxyplus.2.1))
    · left
      rcases hx with hxminus | hxplus
      · exact ⟨hxHhat, hxminus.2⟩
      · exact False.elim (hxHhat (hH_le hxplus.2.1))
  have hminus_eq : Ominus H T = Ominus H T_hat := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hT_le hx.2⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      by_contra hnotT
      have hx0 : x ≠ 0 := by
        intro heq
        apply hnotT
        simpa [heq] using hT.one_mem
      have hinv_notH : x⁻¹ ∉ H := by
        intro hi
        apply hx.1
        simpa using hH.inv_mem hi
      have hinvminus : x⁻¹ ∈ Ominus H T := by
        by_contra hn
        exact hnotT
          ((observation_2_3_part3 T H hT hH hbasic hx0 hx.1).2.mpr hn).2
      have hxThat : x ∈ T_hat := by
        have hm := hT_hat.mul_mem hx.2 (hT_le (hT.inv_mem hinvminus.2))
        have hone0 : 1 + x ≠ 0 := fun e => hT_hat.zero_notMem (e ▸ hx.2)
        have heq : (1 + x) * (1 + x⁻¹)⁻¹ = x := by
          field_simp [hx0, hone0]
          rw [add_comm x 1, div_self hone0]
        exact heq ▸ hm
      exact hx.1 (hT_hat_le hxThat)
  have hO_eq : O H T = O H T_hat := by
    rw [O, O, hminus_eq]
    congr 1
    ext x
    simp only [Oplus, hminus_eq]
  refine ⟨⟨A_hat, hA_hat, hcompat_hat, ?_⟩, hO_eq⟩
  intro x hx
  change x ∈ (A_hat : Set F)
  rw [hA_hat]
  apply hO_le
  change x ∈ (A : Set F) at hx
  rwa [hA] at hx

/-- AEJ, Proposition 2.12, journal p. 457: if
`U_F(H,T) \ T` is nonempty, then `O_F(H,T)` is a `T`-compatible valuation
ring. -/
theorem proposition_2_12 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hex : ∃ u ∈ U H T, u ∉ T) :
    IsCompatibleValuationRingCarrier (O H T) T := by
  rcases hex with ⟨u, hu, huT⟩
  have hpre : IsPreadditive H T := by
    apply (lemma_2_6 T H hT hH hbasic).mpr
    rintro q ⟨x, hx, y, hy, rfl⟩
    apply (mem_one_sub_iff T (x * y)).mpr
    by_cases hx0 : x = 0
    · simpa [hx0] using hT.one_mem
    have hsum : ∀ {a b : F}, a ∈ Ominus H T → b ∈ Ominus H T → a ≠ 0 →
        1 - a * b ∈ T ∪ (-a) • T := by
      intro a b ha hb ha0
      have harigid : IsRigid T (-a) := by
        by_contra hn
        exact ha.1 (hbasic ⟨ha0, fun hbir => hn hbir.2⟩)
      have hh := harigid
        (Set.add_mem_add ha.2 (Set.smul_mem_smul_set (a := -a) hb.2))
      convert hh using 1 <;> ring
    have hfirst := hsum hx hy hx0
    rcases hfirst with hfirst | hfirst
    · exact hfirst
    · have hxu : x * u⁻¹ ∈ Ominus H T := by
        simpa [smul_eq_mul, mul_comm] using
          hu.2.2.2 (Set.smul_mem_smul_set hx)
      have hyu : y * u ∈ Ominus H T := by
        simpa [smul_eq_mul, mul_comm] using
          hu.1.2.2 (Set.smul_mem_smul_set hy)
      have hxu0 : x * u⁻¹ ≠ 0 := mul_ne_zero hx0 (inv_ne_zero hu.1.1)
      have hsecond := hsum hxu hyu hxu0
      have heqprod : (x * u⁻¹) * (y * u) = x * y := by
        field_simp [hu.1.1]
      rw [heqprod] at hsecond
      rcases hsecond with hsecond | hsecond
      · exact hsecond
      · rcases Set.mem_smul_set.mp hfirst with ⟨a, ha, haeq⟩
        rcases Set.mem_smul_set.mp hsecond with ⟨b, hb, hbeq⟩
        exfalso
        apply huT
        have ha0 : a ≠ 0 := fun e => hT.zero_notMem (e ▸ ha)
        have hrel : (-x) * a = (-(x * u⁻¹)) * b := by
          simpa [smul_eq_mul] using haeq.trans hbeq.symm
        have hrel' : x * a = x * (u⁻¹ * b) := by
          calc
            x * a = -((-x) * a) := by ring
            _ = -((-(x * u⁻¹)) * b) := by rw [hrel]
            _ = x * (u⁻¹ * b) := by ring
        have haub : a = u⁻¹ * b := mul_left_cancel₀ hx0 hrel'
        have hab : a * u = b := by
          rw [haub]
          field_simp [hu.1.1]
        have heq : b * a⁻¹ = u := by
          rw [← hab]
          field_simp [ha0]
        exact heq ▸ hT.mul_mem hb (hT.inv_mem ha)
  rcases theorem_2_10 T H hT hH hbasic hpre with ⟨A, hA, hcompat, -⟩
  exact ⟨A, hA, hcompat⟩

/-- AEJ, Lemma 2.13, journal p. 457: if `u ∈ H`, `u ∉ T`, and
`1-u⁻¹ ∉ T`, then `u ∈ O_F⁺(H,T)`. -/
theorem lemma_2_13 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) {u : F}
    (huH : u ∈ H) (huT : u ∉ T) (hone : 1 - u⁻¹ ∉ T) :
    u ∈ Oplus H T := by
  have hu0 : u ≠ 0 := fun e => hH.zero_notMem (e ▸ huH)
  have hsub0 : u - 1 ≠ 0 := by
    intro heq
    apply huT
    have hu1 : u = 1 := sub_eq_zero.mp heq
    simpa [hu1] using hT.one_mem
  have hnotrigid : ¬IsRigid T (u - 1) := by
    intro hr
    have hh := hr (Set.add_mem_add hT.one_mem
      (Set.smul_mem_smul_set (a := u - 1) hT.one_mem))
    have hh' : u ∈ T ∪ (u - 1) • T := by
      convert hh using 1 <;> ring
    rcases hh' with hh' | ⟨t, ht, heq⟩
    · exact huT hh'
    · apply hone
      have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
      have hone_eq : 1 - u⁻¹ = t⁻¹ := by
        change (u - 1) * t = u at heq
        have hsolve : u - 1 = u * t⁻¹ := by
          calc
            u - 1 = ((u - 1) * t) * t⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ ht0, mul_one]
            _ = u * t⁻¹ := by rw [heq]
        calc
          1 - u⁻¹ = (u - 1) * u⁻¹ := by field_simp [hu0]
          _ = (u * t⁻¹) * u⁻¹ := by rw [hsolve]
          _ = t⁻¹ := by field_simp [hu0]
      exact hone_eq ▸ hT.inv_mem ht
  have hsubH : u - 1 ∈ H :=
    hbasic ⟨hsub0, fun hbir => hnotrigid hbir.1⟩
  refine ⟨hu0, huH, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  change u * x ∈ Ominus H T
  by_cases hx0 : x = 0
  · simpa [hx0] using observation_2_3_part2 T H hT hH hbasic
  have hux_notH : u * x ∉ H := by
    intro hh
    apply hx.1
    have hm := hH.mul_mem (hH.inv_mem huH) hh
    have heq : x = u⁻¹ * (u * x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
    exact heq ▸ hm
  have hsx_notH : (u - 1) * x ∉ H := by
    intro hh
    apply hx.1
    have hm := hH.mul_mem (hH.inv_mem hsubH) hh
    have heq : x = (u - 1)⁻¹ * ((u - 1) * x) := by
      rw [← mul_assoc, inv_mul_cancel₀ hsub0, one_mul]
    exact heq ▸ hm
  have hout_rigid : ∀ {a : F}, a ≠ 0 → a ∉ H → IsRigid T a := by
    intro a ha0 haH
    by_contra hn
    exact haH (hbasic ⟨ha0, fun hbir => hn hbir.1⟩)
  have hfirst := hout_rigid (mul_ne_zero hu0 hx0) hux_notH
    (Set.add_mem_add hT.one_mem (Set.smul_mem_smul_set hT.one_mem))
  have hfirst' : 1 + u * x ∈ T ∪ (u * x) • T := by
    simpa [smul_eq_mul] using hfirst
  have hsecond := hout_rigid (mul_ne_zero hsub0 hx0) hsx_notH
    (Set.add_mem_add hx.2 (Set.smul_mem_smul_set hT.one_mem))
  have hsecond' : 1 + u * x ∈ T ∪ ((u - 1) * x) • T := by
    convert hsecond using 1 <;> ring
  refine ⟨hux_notH, ?_⟩
  rcases hfirst' with hfirst | hfirst
  · exact hfirst
  rcases hsecond' with hsecond | hsecond
  · exact hsecond
  exfalso
  apply hone
  rcases Set.mem_smul_set.mp hfirst with ⟨a, ha, haeq⟩
  rcases Set.mem_smul_set.mp hsecond with ⟨b, hb, hbeq⟩
  have hb0 : b ≠ 0 := fun e => hT.zero_notMem (e ▸ hb)
  have hrel : (u * x) * a = ((u - 1) * x) * b := by
    simpa [smul_eq_mul] using haeq.trans hbeq.symm
  have hfactor : (u - 1) * x = (u * x) * (1 - u⁻¹) := by
    field_simp [hu0]
  rw [hfactor] at hrel
  have hrel' : (u * x) * a = (u * x) * ((1 - u⁻¹) * b) := by
    simpa [mul_assoc] using hrel
  have haeq' : a = (1 - u⁻¹) * b :=
    mul_left_cancel₀ (mul_ne_zero hu0 hx0) hrel'
  have heq : a * b⁻¹ = 1 - u⁻¹ := by
    rw [haeq']
    field_simp [hb0]
  exact heq ▸ hT.mul_mem ha (hT.inv_mem hb)

/-- AEJ, Proposition 2.14, journal pp. 457–458: if some
`a ∈ Ḟ \ T` has `-a` not `T`-rigid, then `O_F(H,T)` is a `T`-compatible
valuation ring. -/
theorem proposition_2_14 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hex : ∃ a : F, a ≠ 0 ∧ a ∉ T ∧ ¬IsRigid T (-a)) :
    IsCompatibleValuationRingCarrier (O H T) T := by
  rcases hex with ⟨a, ha0, haT, hnota⟩
  have haH : a ∈ H := hbasic ⟨ha0, fun hbir => hnota hbir.2⟩
  rcases Set.not_subset.mp hnota with ⟨q, hq, hqnot⟩
  rcases Set.mem_add.mp hq with ⟨s, hs, w, hw, rfl⟩
  rcases Set.mem_smul_set.mp hw with ⟨r, hr, rfl⟩
  have hs0 : s ≠ 0 := fun e => hT.zero_notMem (e ▸ hs)
  let t := r * s⁻¹
  have ht : t ∈ T := hT.mul_mem hr (hT.inv_mem hs)
  have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
  let u := a * t
  have hu0 : u ≠ 0 := mul_ne_zero ha0 ht0
  have huH : u ∈ H := hH.mul_mem haH ((subset_H T H hT hH hbasic) ht)
  have huT : u ∉ T := by
    intro hut
    apply haT
    have hm := hT.mul_mem hut (hT.inv_mem ht)
    have heq : u * t⁻¹ = a := by dsimp [u]; field_simp [ht0]
    exact heq ▸ hm
  have hqeq : s + (-a) * r = s * (1 - u) := by
    dsimp [u, t]
    field_simp [hs0]
    ring
  have hnorm : 1 - u ∉ T ∪ (-u) • T := by
    intro hn
    rcases hn with hn | ⟨v, hv, hev⟩
    · apply hqnot
      left
      change s + (-a) * r ∈ T
      rw [hqeq]
      exact hT.mul_mem hs hn
    · apply hqnot
      right
      refine ⟨r * v, hT.mul_mem hr hv, ?_⟩
      change (-a) * (r * v) = s + (-a) * r
      change (-u) * v = 1 - u at hev
      rw [hqeq, ← hev]
      dsimp [u, t]
      field_simp [hs0]
  have honeu : 1 - u ∉ T := fun h => hnorm (Or.inl h)
  have honeui : 1 - u⁻¹ ∉ T := by
    intro hi
    apply hnorm
    right
    refine ⟨1 - u⁻¹, hi, ?_⟩
    change (-u) * (1 - u⁻¹) = 1 - u
    field_simp [hu0]
    ring
  have huplus := lemma_2_13 T H hT hH hbasic huH huT honeui
  have huiH : u⁻¹ ∈ H := hH.inv_mem huH
  have huiT : u⁻¹ ∉ T := by
    intro hi
    apply huT
    simpa [hu0] using hT.inv_mem hi
  have huiplus := lemma_2_13 T H hT hH hbasic huiH huiT (by
    simpa [hu0] using honeu)
  apply proposition_2_12 T H hT hH hbasic
  exact ⟨u, ⟨huplus, huiplus⟩, huT⟩

/-- The set `±T = T ∪ (-T)` from AEJ, Definition 2.15, journal p. 458. -/
def plusMinus (T : Set F) : Set F :=
  T ∪ (-1 : F) • T

/-- AEJ, Definition 2.15, journal p. 458: `T` is exceptional when
`B_F(T)=±T` and either `-1 ∈ T` or `T` is additively closed. -/
def IsExceptional (T : Set F) : Prop :=
  basicPart T = plusMinus T ∧
    ((-1 : F) ∈ T ∨ T + T ⊆ T)

private theorem plusMinus_subset_basicPart (T : Set F) (hT : IsMulSubgroup T) :
    plusMinus T ⊆ basicPart T := by
  have hTbasic : T ⊆ basicPart T := by
    intro t ht
    rw [basicPart]
    refine ⟨fun e => hT.zero_notMem (e ▸ ht), ?_⟩
    intro hbir
    apply (one_mem_basicPart T hT).2
    constructor
    · exact (rigid_smul_iff T hT ht (a := 1)).mp (by
        simpa using hbir.1)
    · exact (rigid_smul_iff T hT ht (a := -1)).mp (by
        simpa [mul_neg] using hbir.2)
  rintro x (hx | hx)
  · exact hTbasic hx
  · rcases Set.mem_smul_set.mp hx with ⟨t, ht, rfl⟩
    have htb := hTbasic ht
    rw [basicPart] at htb ⊢
    refine ⟨by simpa using htb.1, ?_⟩
    intro hbir
    apply htb.2
    exact ⟨by simpa [IsBirigid] using hbir.2,
      by simpa [IsBirigid] using hbir.1⟩

private theorem exceptional_of_rigid_neg_outside (T : Set F)
    (hT : IsMulSubgroup T)
    (hall : ∀ ⦃a : F⦄, a ≠ 0 → a ∉ T → IsRigid T (-a)) :
    IsExceptional T := by
  have hbasic_eq : basicPart T = plusMinus T := by
    apply Set.Subset.antisymm
    · rintro a ⟨ha0, habir⟩
      by_contra ha
      have haT : a ∉ T := fun h => ha (Or.inl h)
      have hnegaT : -a ∉ T := by
        intro h
        apply ha
        right
        refine Set.mem_smul_set.mpr ⟨-a, h, ?_⟩
        simp
      apply habir
      exact ⟨by simpa using hall (a := -a) (neg_ne_zero.mpr ha0) hnegaT,
        hall ha0 haT⟩
    · exact plusMinus_subset_basicPart T hT
  refine ⟨hbasic_eq, ?_⟩
  by_cases hneg : (-1 : F) ∈ T
  · exact Or.inl hneg
  · right
    have hr : IsRigid T (1 : F) := by
      simpa using hall (a := (-1 : F)) (by simp) hneg
    rintro q ⟨x, hx, y, hy, rfl⟩
    have hq := hr (Set.add_mem_add hx
      (Set.smul_mem_smul_set (a := (1 : F)) hy))
    simpa [smul_eq_mul] using hq

private theorem compatible_O_with_bound (T H : Set F)
    (hT : IsMulSubgroup T) (hH : IsMulSubgroup H)
    (hbasic : basicPart T ⊆ H)
    (hval : IsCompatibleValuationRingCarrier (O H T) T) :
    ∃ A : ValuationSubring F,
      (A : Set F) = O H T ∧ ValuationSubring.IsCompatible A T ∧
        ValuationSubring.unitCarrier A * T ⊆ H := by
  rcases hval with ⟨A, hA, hcompat⟩
  refine ⟨A, hA, hcompat, ?_⟩
  have hunit :=
    (observation_2_3_part3_inParticular T H hT hH hbasic A hA).2.2
  have hTH := subset_H T H hT hH hbasic
  rintro q ⟨u, hu, t, ht, rfl⟩
  exact hH.mul_mem (hunit hu) (hTH ht)

private theorem smul_set_eq_of_neg_smul_inter (T : Set F)
    (hT : IsMulSubgroup T) {a b c : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hca : c ∈ (-a) • T) (hcb : c ∈ (-b) • T) :
    a • T = b • T := by
  rcases Set.mem_smul_set.mp hca with ⟨t, ht, hteq⟩
  rcases Set.mem_smul_set.mp hcb with ⟨s, hs, hseq⟩
  rw [smul_eq_mul] at hteq hseq
  have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
  have hs0 : s ≠ 0 := fun e => hT.zero_notMem (e ▸ hs)
  have hrel : a * t = b * s := by
    simpa using hteq.trans hseq.symm
  have hab : a = b * s * t⁻¹ := by
    calc
      a = (a * t) * t⁻¹ := by field_simp
      _ = (b * s) * t⁻¹ := by rw [hrel]
  have hba : b = a * t * s⁻¹ := by
    calc
      b = (b * s) * s⁻¹ := by field_simp
      _ = (a * t) * s⁻¹ := by rw [hrel]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine Set.mem_smul_set.mpr
      ⟨s * t⁻¹ * u, hT.mul_mem (hT.mul_mem hs (hT.inv_mem ht)) hu, ?_⟩
    change b * (s * t⁻¹ * u) = a * u
    rw [hab]
    ring
  · rintro ⟨u, hu, rfl⟩
    refine Set.mem_smul_set.mpr
      ⟨t * s⁻¹ * u, hT.mul_mem (hT.mul_mem ht (hT.inv_mem hs)) hu, ?_⟩
    change a * (t * s⁻¹ * u) = b * u
    rw [hba]
    ring

private theorem exceptional_star (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (hall : ∀ ⦃x : F⦄, x ≠ 0 → x ∉ plusMinus T → IsBirigid T x)
    {a b : F} (ha : a ∈ Ominus H T) (hb : b ∈ Ominus H T)
    (hnot : 1 - a * b ∉ T) :
    1 - a * b ∈ (-a) • T ∧ a • T = b • T := by
  have ha0 : a ≠ 0 := by
    intro e
    apply hnot
    simpa [e] using hT.one_mem
  have hb0 : b ≠ 0 := by
    intro e
    apply hnot
    simpa [e] using hT.one_mem
  have ha_pm : a ∉ plusMinus T := fun h =>
    ha.1 (hbasic (plusMinus_subset_basicPart T hT h))
  have hb_pm : b ∉ plusMinus T := fun h =>
    hb.1 (hbasic (plusMinus_subset_basicPart T hT h))
  have habir := hall ha0 ha_pm
  have hbbir := hall hb0 hb_pm
  have hfirst : 1 - a * b ∈ (-a) • T := by
    have hs : 1 - a * b ∈ T + (-a) • T := by
      rw [show 1 - a * b = (1 + a) + (-a) * (1 + b) by ring]
      exact Set.add_mem_add ha.2 (by
        simpa [smul_eq_mul] using
          Set.smul_mem_smul_set (a := -a) hb.2)
    exact (habir.2 hs).resolve_left hnot
  have hsecond : 1 - a * b ∈ (-b) • T := by
    have hs : 1 - a * b ∈ T + (-b) • T := by
      rw [show 1 - a * b = (1 + b) + (-b) * (1 + a) by ring]
      exact Set.add_mem_add hb.2 (by
        simpa [smul_eq_mul] using
          Set.smul_mem_smul_set (a := -b) ha.2)
    exact (hbbir.2 hs).resolve_left hnot
  exact ⟨hfirst,
    smul_set_eq_of_neg_smul_inter T hT ha0 hb0 hfirst hsecond⟩

private theorem two_coset_mulSubgroup (H : Set F) (hH : IsMulSubgroup H)
    {a : F} (ha0 : a ≠ 0) (ha2 : a ^ 2 ∈ H) :
    IsMulSubgroup (H ∪ a • H) := by
  have ha2' : a * a ∈ H := by simpa [pow_two] using ha2
  constructor
  · exact Or.inl hH.one_mem
  · rintro x y (hx | ⟨u, hu, rfl⟩) (hy | ⟨v, hv, rfl⟩)
    · exact Or.inl (hH.mul_mem hx hy)
    · right
      refine Set.mem_smul_set.mpr ⟨x * v, hH.mul_mem hx hv, ?_⟩
      simp only [smul_eq_mul]
      ring
    · right
      refine Set.mem_smul_set.mpr ⟨u * y, hH.mul_mem hu hy, ?_⟩
      simp only [smul_eq_mul]
      ring
    · left
      simp only [smul_eq_mul]
      have hh := hH.mul_mem ha2' (hH.mul_mem hu hv)
      convert hh using 1 <;> ring
  · rintro x (hx | ⟨u, hu, rfl⟩)
    · exact Or.inl (hH.inv_mem hx)
    · right
      refine Set.mem_smul_set.mpr
        ⟨(a ^ 2)⁻¹ * u⁻¹,
          hH.mul_mem (hH.inv_mem ha2) (hH.inv_mem hu), ?_⟩
      simp only [smul_eq_mul]
      field_simp [ha0]
  · intro hzero
    rcases hzero with hzero | ⟨u, hu, heq⟩
    · exact hH.zero_notMem hzero
    · change a * u = 0 at heq
      have hu0 : u ≠ 0 := fun e => hH.zero_notMem (e ▸ hu)
      exact mul_ne_zero ha0 hu0 heq

private theorem subgroup_mul_not_mem {G : Set F} (hG : IsMulSubgroup G)
    {g z : F} (hg : g ∈ G) (hz : z ∉ G) : g * z ∉ G := by
  intro hgz
  apply hz
  have hh := hG.mul_mem (hG.inv_mem hg) hgz
  have hg0 : g ≠ 0 := fun e => hG.zero_notMem (e ▸ hg)
  have heq : z = g⁻¹ * (g * z) := by
    rw [← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  exact heq ▸ hh

private theorem exceptional_ab_and_square (T H : Set F)
    (hT : IsMulSubgroup T) (hH : IsMulSubgroup H)
    (hbasic : basicPart T ⊆ H) {a b : F}
    (ha : a ∈ Ominus H T) (hb : b ∈ Ominus H T)
    (habir : IsBirigid T a) (hfirst : 1 - a * b ∈ (-a) • T)
    (hcoset : a • T = b • T) : a * b ∈ T ∧ a ^ 2 ∈ T := by
  have ha0 : a ≠ 0 := by
    intro e
    subst a
    rcases Set.mem_smul_set.mp hfirst with ⟨t, ht, heq⟩
    simp only [smul_eq_mul] at heq
    have heq' : (0 : F) = 1 := by simpa using heq
    exact zero_ne_one heq'
  have hTH := subset_H T H hT hH hbasic
  have hbT : b ∉ T := fun h => hb.1 (hTH h)
  rcases Set.mem_smul_set.mp hfirst with ⟨t, ht, hteq⟩
  rw [smul_eq_mul] at hteq
  have hab_sum : a * b ∈ T + a • T := by
    have hm := Set.add_mem_add hT.one_mem
      (Set.smul_mem_smul_set (a := a) ht)
    have heq : a * b = 1 + a * t := by
      calc
        a * b = 1 - (1 - a * b) := by ring
        _ = 1 - (-a * t) := by rw [hteq]
        _ = 1 + a * t := by ring
    rw [heq]
    simpa [smul_eq_mul] using hm
  have habT : a * b ∈ T := by
    rcases habir.1 hab_sum with h | ⟨s, hs, hseq⟩
    · exact h
    · apply False.elim
      apply hbT
      change a * s = a * b at hseq
      have heq : s = b := mul_left_cancel₀ ha0 hseq
      exact heq ▸ hs
  have ha_in : a ∈ a • T := by
    simpa [smul_eq_mul] using
      Set.smul_mem_smul_set (a := a) hT.one_mem
  rw [hcoset] at ha_in
  rcases Set.mem_smul_set.mp ha_in with ⟨s, hs, hseq⟩
  rw [smul_eq_mul] at hseq
  refine ⟨habT, ?_⟩
  have hm := hT.mul_mem habT hs
  have heq : a ^ 2 = (a * b) * s := by
    rw [pow_two, ← hseq]
    ring
  exact heq ▸ hm

private theorem smul_overgroup_eq_of_smul_eq (T H : Set F)
    (hT : IsMulSubgroup T) (hH : IsMulSubgroup H) (hTH : T ⊆ H)
    {a b : F} (ha0 : a ≠ 0) (hcoset : a • T = b • T) :
    a • H = b • H := by
  have ha_in : a ∈ a • T := by
    simpa [smul_eq_mul] using
      Set.smul_mem_smul_set (a := a) hT.one_mem
  rw [hcoset] at ha_in
  rcases Set.mem_smul_set.mp ha_in with ⟨t, ht, hteq⟩
  rw [smul_eq_mul] at hteq
  have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine Set.mem_smul_set.mpr
      ⟨t * u, hH.mul_mem (hTH ht) hu, ?_⟩
    change b * (t * u) = a * u
    calc
      b * (t * u) = (b * t) * u := by ring
      _ = a * u := by rw [hteq]
  · rintro ⟨u, hu, rfl⟩
    refine Set.mem_smul_set.mpr
      ⟨t⁻¹ * u, hH.mul_mem (hH.inv_mem (hTH ht)) hu, ?_⟩
    change a * (t⁻¹ * u) = b * u
    rw [← hteq]
    field_simp

private theorem neg_a_mem_U_two_coset (T H : Set F)
    (hT : IsMulSubgroup T) (hH : IsMulSubgroup H)
    (hbasic : basicPart T ⊆ H)
    (hall : ∀ ⦃x : F⦄, x ≠ 0 → x ∉ plusMinus T → IsBirigid T x)
    {a b : F} (ha : a ∈ Ominus H T) (hb : b ∈ Ominus H T)
    (hnot : 1 - a * b ∉ T) (hfirst : 1 - a * b ∈ (-a) • T)
    (hcoset : a • T = b • T) (ha2 : a ^ 2 ∈ T) :
    -a ∈ U (H ∪ a • H) T := by
  let H_hat := H ∪ a • H
  have ha0 : a ≠ 0 := by
    intro e
    apply hnot
    simpa [e] using hT.one_mem
  have hb0 : b ≠ 0 := by
    intro e
    apply hnot
    simpa [e] using hT.one_mem
  have hTH := subset_H T H hT hH hbasic
  have hHhat : IsMulSubgroup H_hat :=
    two_coset_mulSubgroup H hH ha0 (hTH ha2)
  have hH_le : H ⊆ H_hat := fun _ h => Or.inl h
  have hbasic_hat : basicPart T ⊆ H_hat := hbasic.trans hH_le
  have hminus_le : Ominus H_hat T ⊆ Ominus H T := by
    rintro z ⟨hz, hzone⟩
    exact ⟨fun h => hz (hH_le h), hzone⟩
  have hnegaH : -a ∈ H_hat := by
    right
    refine Set.mem_smul_set.mpr
      ⟨-1, neg_one_mem_H T H hT hbasic, ?_⟩
    simp
  have hcosetH : a • H = b • H :=
    smul_overgroup_eq_of_smul_eq T H hT hH hTH ha0 hcoset
  have hbH : b ∈ H_hat := by
    right
    rw [hcosetH]
    simpa [smul_eq_mul] using
      Set.smul_mem_smul_set (a := b) hH.one_mem
  have hnegbH : -b ∈ H_hat := by
    have hn1 : (-1 : F) ∈ H_hat := hH_le (neg_one_mem_H T H hT hbasic)
    simpa using hHhat.mul_mem hn1 hbH
  have hone_a : ∀ ⦃z : F⦄, z ∈ Ominus H_hat T → 1 - a * z ∈ T := by
    intro z hz
    by_contra hn
    have hs := exceptional_star T H hT hH hbasic hall ha (hminus_le hz) hn
    have hzself : z ∈ z • T := by
      simpa [smul_eq_mul] using
        Set.smul_mem_smul_set (a := z) hT.one_mem
    rw [← hs.2] at hzself
    rcases Set.mem_smul_set.mp hzself with ⟨t, ht, hteq⟩
    apply hz.1
    right
    exact Set.mem_smul_set.mpr ⟨t, hTH ht, hteq⟩
  have hone_b : ∀ ⦃z : F⦄, z ∈ Ominus H_hat T → 1 - b * z ∈ T := by
    intro z hz
    by_contra hn
    have hs := exceptional_star T H hT hH hbasic hall hb (hminus_le hz) hn
    have hzself : z ∈ z • T := by
      simpa [smul_eq_mul] using
        Set.smul_mem_smul_set (a := z) hT.one_mem
    rw [← hs.2] at hzself
    rcases Set.mem_smul_set.mp hzself with ⟨t, ht, hteq⟩
    apply hz.1
    right
    rw [hcosetH]
    exact Set.mem_smul_set.mpr ⟨t, hTH ht, hteq⟩
  have hneg_a_plus : -a ∈ Oplus H_hat T := by
    refine ⟨neg_ne_zero.mpr ha0, hnegaH, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    change -a * z ∈ Ominus H_hat T
    exact ⟨subgroup_mul_not_mem hHhat hnegaH hz.1,
      by convert hone_a hz using 1 <;> ring⟩
  have hneg_ai_plus : (-a)⁻¹ ∈ Oplus H_hat T := by
    have hnegaInvH : (-a)⁻¹ ∈ H_hat := hHhat.inv_mem hnegaH
    refine ⟨inv_ne_zero (neg_ne_zero.mpr ha0), hnegaInvH, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    change (-a)⁻¹ * z ∈ Ominus H_hat T
    refine ⟨subgroup_mul_not_mem hHhat hnegaInvH hz.1, ?_⟩
    by_contra hn
    have hz0 : z ≠ 0 := by
      intro e
      apply hn
      simpa [e] using hT.one_mem
    have hxnot : (-a)⁻¹ * z ∉ Ominus H_hat T := by
      intro hx
      apply hn
      convert hx.2 using 1 <;> field_simp [ha0] <;> ring
    have hx0 : (-a)⁻¹ * z ≠ 0 :=
      mul_ne_zero (inv_ne_zero (neg_ne_zero.mpr ha0)) hz0
    have hobs := observation_2_3_part3 T H_hat hT hHhat hbasic_hat
      hx0 (subgroup_mul_not_mem hHhat hnegaInvH hz.1)
    have hxinv : ((-a)⁻¹ * z)⁻¹ ∈ Ominus H_hat T := by
      by_contra hi
      exact hxnot (hobs.2.mpr hi)
    have hq : -a * z⁻¹ ∈ Ominus H T := by
      apply hminus_le
      convert hxinv using 1 <;> field_simp [ha0, hz0] <;> ring
    have hr_hat : -b * z ∈ Ominus H_hat T :=
      ⟨subgroup_mul_not_mem hHhat hnegbH hz.1,
        by convert hone_b hz using 1 <;> ring⟩
    have hr : -b * z ∈ Ominus H T := hminus_le hr_hat
    have hqrnot : 1 - (-a * z⁻¹) * (-b * z) ∉ T := by
      convert hnot using 1 <;> field_simp [hz0] <;> ring
    have hs := exceptional_star T H hT hH hbasic hall hq hr hqrnot
    have hcaz : 1 - a * b ∈ (a * z⁻¹) • T := by
      convert hs.1 using 1 <;> field_simp [hz0] <;> ring
    rcases Set.mem_smul_set.mp hcaz with ⟨t, ht, hteq⟩
    rcases Set.mem_smul_set.mp hfirst with ⟨s, hsT, hseq⟩
    rw [smul_eq_mul] at hteq hseq
    have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
    have hrel : z⁻¹ * t = -s := by
      apply mul_left_cancel₀ ha0
      calc
        a * (z⁻¹ * t) = (a * z⁻¹) * t := by ring
        _ = 1 - a * b := hteq
        _ = (-a) * s := hseq.symm
        _ = a * (-s) := by ring
    have hnegzi : -z⁻¹ ∈ T := by
      have heq : -z⁻¹ = s * t⁻¹ := by
        calc
          -z⁻¹ = -((z⁻¹ * t) * t⁻¹) := by field_simp
          _ = -((-s) * t⁻¹) := by rw [hrel]
          _ = s * t⁻¹ := by ring
      exact heq ▸ hT.mul_mem hsT (hT.inv_mem ht)
    have hnegzH : -z ∈ H := by
      have hh := hTH (hT.inv_mem hnegzi)
      convert hh using 1 <;> field_simp [hz0] <;> ring
    have hzH := hH.mul_mem (neg_one_mem_H T H hT hbasic) hnegzH
    apply hz.1
    left
    simpa using hzH
  exact ⟨hneg_a_plus, hneg_ai_plus⟩

/-- AEJ, Theorem 2.16, journal p. 458: `H` has an overgroup `Ĥ` of index at
most two for which `O_F(Ĥ,T)` is a `T`-compatible valuation ring with
`U_A·T ⊆ Ĥ`; if `T` is not exceptional, `Ĥ` may be chosen equal to `H`.
The index assertion uses the documented two-coset predicate
`HasIndexAtMostTwo`. -/
theorem theorem_2_16 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) :
    ∃ H_hat : Set F,
      IsMulSubgroup H_hat ∧ H ⊆ H_hat ∧
        HasIndexAtMostTwo H_hat H ∧
        (∃ A : ValuationSubring F,
          (A : Set F) = O H_hat T ∧
            ValuationSubring.IsCompatible A T ∧
            ValuationSubring.unitCarrier A * T ⊆ H_hat) ∧
        (¬IsExceptional T → H_hat = H) := by
  by_cases hex : ∃ a : F, a ≠ 0 ∧ a ∉ T ∧ ¬IsRigid T (-a)
  · have hval := proposition_2_14 T H hT hH hbasic hex
    have hpack := compatible_O_with_bound T H hT hH hbasic hval
    refine ⟨H, hH, Set.Subset.rfl, ?_, hpack, fun _ => rfl⟩
    exact ⟨Set.Subset.rfl, 1, fun x hx => Or.inl hx⟩
  · have hallneg : ∀ ⦃a : F⦄, a ≠ 0 → a ∉ T → IsRigid T (-a) := by
      intro a ha0 haT
      by_contra hn
      exact hex ⟨a, ha0, haT, hn⟩
    have hexceptional := exceptional_of_rigid_neg_outside T hT hallneg
    have hallbir : ∀ ⦃x : F⦄, x ≠ 0 → x ∉ plusMinus T →
        IsBirigid T x := by
      intro x hx0 hxpm
      have hxT : x ∉ T := fun h => hxpm (Or.inl h)
      have hnegxT : -x ∉ T := by
        intro h
        apply hxpm
        right
        refine Set.mem_smul_set.mpr ⟨-x, h, ?_⟩
        simp
      exact ⟨by simpa using hallneg (a := -x) (neg_ne_zero.mpr hx0) hnegxT,
        hallneg hx0 hxT⟩
    by_cases hpre : IsPreadditive H T
    · rcases theorem_2_10 T H hT hH hbasic hpre with
        ⟨A, hA, hcompat, hbound⟩
      refine ⟨H, hH, Set.Subset.rfl, ?_, ⟨A, hA, hcompat, hbound⟩, ?_⟩
      · exact ⟨Set.Subset.rfl, 1, fun x hx => Or.inl hx⟩
      · intro hnon
        exact False.elim (hnon hexceptional)
    · have hprod : ¬Ominus H T * Ominus H T ⊆ ({1} : Set F) - T := by
        intro hp
        exact hpre ((lemma_2_6 T H hT hH hbasic).mpr hp)
      rcases Set.not_subset.mp hprod with ⟨q, hq, hqnot⟩
      rcases Set.mem_mul.mp hq with ⟨a, ha, b, hb, rfl⟩
      have habnot : 1 - a * b ∉ T := by
        intro h
        exact hqnot ((mem_one_sub_iff T (a * b)).mpr h)
      have hstar := exceptional_star T H hT hH hbasic hallbir ha hb habnot
      have habir : IsBirigid T a := by
        apply hallbir
        · intro e
          apply habnot
          simpa [e] using hT.one_mem
        · intro h
          exact ha.1 (hbasic (plusMinus_subset_basicPart T hT h))
      have hab2 := exceptional_ab_and_square T H hT hH hbasic ha hb
        habir hstar.1 hstar.2
      let H_hat : Set F := H ∪ a • H
      have ha0 : a ≠ 0 := by
        intro e
        apply habnot
        simpa [e] using hT.one_mem
      have hTH := subset_H T H hT hH hbasic
      have hHhat : IsMulSubgroup H_hat :=
        two_coset_mulSubgroup H hH ha0 (hTH hab2.2)
      have hH_le : H ⊆ H_hat := fun _ h => Or.inl h
      have hbasic_hat : basicPart T ⊆ H_hat := hbasic.trans hH_le
      have hnegaU : -a ∈ U H_hat T :=
        neg_a_mem_U_two_coset T H hT hH hbasic hallbir ha hb habnot
          hstar.1 hstar.2 hab2.2
      have hnegaT : -a ∉ T := by
        intro h
        apply ha.1
        have hh := hH.mul_mem (neg_one_mem_H T H hT hbasic) (hTH h)
        simpa using hh
      have hval := proposition_2_12 T H_hat hT hHhat hbasic_hat
        ⟨-a, hnegaU, hnegaT⟩
      have hpack := compatible_O_with_bound T H_hat hT hHhat hbasic_hat hval
      refine ⟨H_hat, hHhat, hH_le, ?_, hpack, ?_⟩
      · exact ⟨hH_le, a, Set.Subset.rfl⟩
      · intro hnon
        exact False.elim (hnon hexceptional)

private theorem mulSubgroupClosureCarrier_isMulSubgroup (S : Set F) :
    IsMulSubgroup (mulSubgroupClosureCarrier S) := by
  constructor
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    simp
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    refine ⟨u * v, Subgroup.mul_mem _ hu hv, ?_⟩
    simp
  · rintro x ⟨u, hu, rfl⟩
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    simp
  · rintro ⟨u, hu, heq⟩
    exact Units.ne_zero u heq

private theorem basicPart_subset_mulSubgroupClosureCarrier (T : Set F) :
    basicPart T ⊆ mulSubgroupClosureCarrier (basicPart T) := by
  intro x hx
  let u : Fˣ := Units.mk0 x hx.1
  refine ⟨u, ?_, rfl⟩
  apply Subgroup.subset_closure
  exact hx

private theorem mulSubgroupClosureCarrier_minimal (S G : Set F)
    (hG : IsMulSubgroup G) (hSG : S ⊆ G) :
    mulSubgroupClosureCarrier S ⊆ G := by
  let G' : Subgroup Fˣ :=
    { carrier := {u : Fˣ | ((u : F) ∈ G)}
      one_mem' := hG.one_mem
      mul_mem' := fun hu hv => hG.mul_mem hu hv
      inv_mem' := fun hu => by simpa using hG.inv_mem hu }
  have hgen : {u : Fˣ | ((u : F) ∈ S)} ⊆ G' := by
    intro u hu
    exact hSG hu
  have hcl : mulSubgroupClosure S ≤ G' := by
    exact (Subgroup.closure_le G').mpr hgen
  rintro x ⟨u, hu, rfl⟩
  exact hcl hu

private theorem unitCarrier_isMulSubgroup (A : ValuationSubring F) :
    IsMulSubgroup (ValuationSubring.unitCarrier A) := by
  constructor
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, Subgroup.mul_mem _ hu hv, by simp⟩
  · rintro x ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, Subgroup.inv_mem _ hu, by simp⟩
  · rintro ⟨u, hu, heq⟩
    exact Units.ne_zero u heq

private theorem mul_set_isMulSubgroup (G K : Set F)
    (hG : IsMulSubgroup G) (hK : IsMulSubgroup K) :
    IsMulSubgroup (G * K) := by
  constructor
  · exact ⟨1, hG.one_mem, 1, hK.one_mem, by simp⟩
  · rintro x y ⟨g, hg, k, hk, rfl⟩ ⟨g', hg', k', hk', rfl⟩
    refine ⟨g * g', hG.mul_mem hg hg', k * k', hK.mul_mem hk hk', ?_⟩
    ring
  · rintro x ⟨g, hg, k, hk, rfl⟩
    refine ⟨g⁻¹, hG.inv_mem hg, k⁻¹, hK.inv_mem hk, ?_⟩
    simp [mul_comm]
  · rintro ⟨g, hg, k, hk, heq⟩
    exact mul_ne_zero (fun e => hG.zero_notMem (e ▸ hg))
      (fun e => hK.zero_notMem (e ▸ hk)) heq

/-- AEJ, Corollary 2.17, journal p. 459: there is a `T`-compatible valuation
ring with `[U_A·T : ⟨B_F(T)⟩] ≤ 2`; outside the exceptional case one can
choose it with equality.  The index bound is represented by a two-coset
cover. -/
theorem corollary_2_17 (T : Set F) (hT : IsMulSubgroup T) :
    (∃ A : ValuationSubring F,
      ValuationSubring.IsCompatible A T ∧
        HasIndexAtMostTwo (ValuationSubring.unitCarrier A * T)
          (mulSubgroupClosureCarrier (basicPart T))) ∧
      (¬IsExceptional T →
        ∃ A : ValuationSubring F,
          ValuationSubring.IsCompatible A T ∧
            ValuationSubring.unitCarrier A * T =
              mulSubgroupClosureCarrier (basicPart T)) := by
  let H := mulSubgroupClosureCarrier (basicPart T)
  have hH : IsMulSubgroup H :=
    mulSubgroupClosureCarrier_isMulSubgroup (basicPart T)
  have hbasic : basicPart T ⊆ H :=
    basicPart_subset_mulSubgroupClosureCarrier T
  rcases theorem_2_16 T H hT hH hbasic with
    ⟨H_hat, hH_hat, hH_le, hindex, hpack, hmore⟩
  rcases hpack with ⟨A, hA, hcompat, hbound⟩
  have hUT : IsMulSubgroup (ValuationSubring.unitCarrier A * T) :=
    mul_set_isMulSubgroup _ _ (unitCarrier_isMulSubgroup A) hT
  have hbase : H ⊆ ValuationSubring.unitCarrier A * T := by
    apply mulSubgroupClosureCarrier_minimal (basicPart T)
      (ValuationSubring.unitCarrier A * T) hUT
    exact proposition_1_9_part1 A T hT hcompat
  constructor
  · refine ⟨A, hcompat, hbase, ?_⟩
    rcases hindex.2 with ⟨a, ha⟩
    exact ⟨a, hbound.trans ha⟩
  · intro hnon
    refine ⟨A, hcompat, Set.Subset.antisymm ?_ hbase⟩
    change ValuationSubring.unitCarrier A * T ⊆ H
    rw [← hmore hnon]
    exact hbound

end

end NU.AEJ
