import Submission.NU.AEJ.Coarse

/-!
# AEJ Theorem 3.9 (journal p. 462)

This file records the structural conclusions about the smallest `T`-coarse,
`T`-compatible valuation ring constructed in Theorem 3.8.
-/

open Pointwise

namespace NU.AEJ

noncomputable section

variable {F : Type*} [Field F]

/-- The unit set `U_F(T) := U_{O_F(T)}` from AEJ, Theorem 3.9,
journal p. 462. -/
def UF (T : Set F) (hT : IsMulSubgroup T) : Set F :=
  ValuationSubring.unitCarrier (OF T hT)

private theorem theorem39_unitCarrier_isMulSubgroup (A : ValuationSubring F) :
    IsMulSubgroup (ValuationSubring.unitCarrier A) := by
  constructor
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, Subgroup.mul_mem _ hu hv, by simp⟩
  · rintro x ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, Subgroup.inv_mem _ hu, by simp⟩
  · rintro ⟨u, -, heq⟩
    exact Units.ne_zero u heq

private theorem theorem39_mul_isMulSubgroup (G K : Set F)
    (hG : IsMulSubgroup G) (hK : IsMulSubgroup K) :
    IsMulSubgroup (G * K) := by
  constructor
  · exact ⟨1, hG.one_mem, 1, hK.one_mem, by simp⟩
  · rintro x y ⟨g, hg, k, hk, rfl⟩ ⟨g', hg', k', hk', rfl⟩
    exact ⟨g * g', hG.mul_mem hg hg', k * k', hK.mul_mem hk hk', by ring⟩
  · rintro x ⟨g, hg, k, hk, rfl⟩
    exact ⟨g⁻¹, hG.inv_mem hg, k⁻¹, hK.inv_mem hk, by simp [mul_comm]⟩
  · rintro ⟨g, hg, k, hk, heq⟩
    exact mul_ne_zero (fun e => hG.zero_notMem (e ▸ hg))
      (fun e => hK.zero_notMem (e ▸ hk)) heq

private theorem theorem39_closure_minimal (S G : Set F)
    (hG : IsMulSubgroup G) (hSG : S ⊆ G) :
    mulSubgroupClosureCarrier S ⊆ G := by
  let G' : Subgroup Fˣ :=
    { carrier := {u : Fˣ | (u : F) ∈ G}
      one_mem' := hG.one_mem
      mul_mem' := fun hu hv => hG.mul_mem hu hv
      inv_mem' := fun hu => by simpa using hG.inv_mem hu }
  have hgen : {u : Fˣ | (u : F) ∈ S} ⊆ G' := fun _ hu => hSG hu
  have hcl : mulSubgroupClosure S ≤ G' :=
    (Subgroup.closure_le G').mpr hgen
  rintro x ⟨u, hu, rfl⟩
  exact hcl hu

private theorem theorem39_unitCarrier_mono (A B : ValuationSubring F)
    (hAB : A ≤ B) :
    ValuationSubring.unitCarrier A ⊆ ValuationSubring.unitCarrier B := by
  rintro x ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  change B.valuation (u : F) = 1
  rw [← ValuationSubring.mapOfLE_valuation_apply A B hAB,
    (A.mem_unitGroup_iff u).mp hu]
  exact (A.mapOfLE B hAB).map_one

private theorem theorem39_compatible_of_le (A B : ValuationSubring F)
    (hAB : A ≤ B) {T : Set F}
    (hcompat : ValuationSubring.IsCompatible A T) :
    ValuationSubring.IsCompatible B T := by
  rintro x ⟨u, hu, rfl⟩
  apply hcompat
  refine ⟨u, ?_, rfl⟩
  change A.valuation ((u : F) - 1) < 1
  have hu' : B.valuation ((u : F) - 1) < 1 := by
    exact hu
  by_contra hn
  have hge : 1 ≤ A.valuation ((u : F) - 1) := le_of_not_gt hn
  have hmap := ValuationSubring.monotone_mapOfLE A B hAB hge
  rw [(A.mapOfLE B hAB).map_one,
    ValuationSubring.mapOfLE_valuation_apply A B hAB] at hmap
  exact (not_le_of_gt hu') hmap

private theorem theorem39_mem_unitCarrier_of_valuation_eq_one
    (A : ValuationSubring F) {x : F} (hx : A.valuation x = 1) :
    x ∈ ValuationSubring.unitCarrier A := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, A.valuation.map_zero] at hx
    exact zero_ne_one hx
  let u : Fˣ := Units.mk0 x hx0
  refine ⟨u, ?_, rfl⟩
  change A.valuation (u : F) = 1
  exact hx

private theorem theorem39_UF_mul_subset_of_compatible (T : Set F)
    (hT : IsMulSubgroup T) (A : ValuationSubring F)
    (hcompat : ValuationSubring.IsCompatible A T) :
    UF T hT * T ⊆ ValuationSubring.unitCarrier A * T := by
  let H := ValuationSubring.unitCarrier A * T
  have hH : IsMulSubgroup H :=
    theorem39_mul_isMulSubgroup _ _ (theorem39_unitCarrier_isMulSubgroup A) hT
  have hbasic : basicPart T ⊆ H :=
    proposition_1_9_part1 A T hT hcompat
  have hT_H : T ⊆ H := by
    intro t ht
    exact ⟨1, ⟨1, Subgroup.one_mem _, by simp⟩, t, ht, by simp⟩
  obtain ⟨B, hB, hAB, -⟩ :=
    proposition_3_2 T H hT hH hbasic A hcompat Set.Subset.rfl
  have hBcompat : ValuationSubring.IsCompatible B T :=
    theorem39_compatible_of_le A B hAB hcompat
  have hBcoarse : IsTCoarse B T := by
    have hno := lemma_3_1 T H hT hH hbasic B hB
    intro Δ hΔ hΔT
    apply hno Δ hΔ
    intro d hd
    obtain ⟨t, ht, hval⟩ := hΔT hd
    exact ⟨t, hT_H ht, hval⟩
  have hOF_B : OF T hT ≤ B := OF_le T hT B hBcompat hBcoarse
  have hUB_H : ValuationSubring.unitCarrier B ⊆ H :=
    (observation_2_3_part3_inParticular T H hT hH hbasic B hB).2.2
  rintro q ⟨u, hu, t, ht, rfl⟩
  apply hH.mul_mem
  · apply hUB_H
    apply theorem39_unitCarrier_mono (OF T hT) B hOF_B
    exact hu
  · exact hT_H ht

/-- AEJ, Theorem 3.9(1)–(3) and its moreover clause, journal p. 462.
The index in part (2) is rendered by `HasIndexAtMostTwo`, i.e. inclusion plus
a cover by at most two cosets.  Part (3) uses the project-wide explicit
predicate `IsValuationRingCarrier`. -/
theorem theorem_3_9 (T : Set F) (hT : IsMulSubgroup T) :
    mulSubgroupClosureCarrier (basicPart T) ⊆ UF T hT * T ∧
      HasIndexAtMostTwo (UF T hT * T)
        (mulSubgroupClosureCarrier (basicPart T)) ∧
      (∀ H : Set F, IsMulSubgroup H → basicPart T ⊆ H →
        (IsValuationRingCarrier (O H T) ↔ UF T hT * T ⊆ H)) ∧
      (¬IsExceptional T →
        UF T hT * T = mulSubgroupClosureCarrier (basicPart T)) := by
  let C := mulSubgroupClosureCarrier (basicPart T)
  let HT := UF T hT * T
  have hHT : IsMulSubgroup HT :=
    theorem39_mul_isMulSubgroup _ _
      (theorem39_unitCarrier_isMulSubgroup (OF T hT)) hT
  have hbasic_HT : basicPart T ⊆ HT := by
    simpa [HT, UF] using
      proposition_1_9_part1 (OF T hT) T hT (OF_isCompatible T hT)
  have hC_HT : C ⊆ HT :=
    theorem39_closure_minimal (basicPart T) HT hHT hbasic_HT
  have hindex : HasIndexAtMostTwo HT C := by
    obtain ⟨A, hAcompat, -, a, ha⟩ := (corollary_2_17 T hT).1
    refine ⟨hC_HT, a, ?_⟩
    have hsub := theorem39_UF_mul_subset_of_compatible T hT A hAcompat
    exact hsub.trans ha
  have hpart3 : ∀ H : Set F, IsMulSubgroup H → basicPart T ⊆ H →
      (IsValuationRingCarrier (O H T) ↔ HT ⊆ H) := by
    intro H hH hbasic
    constructor
    · rintro ⟨A, hA⟩
      have hobs :=
        observation_2_3_part3_inParticular T H hT hH hbasic A hA
      have hpre : IsPreadditive H T := by
        rintro z hz
        rcases Set.mem_add.mp hz with ⟨a, ha, x, hx, rfl⟩
        have ha1 : a = 1 := by simpa using ha
        subst a
        have hxnon : x ∈ A.nonunits := hobs.1 hx
        have hval : A.valuation (1 + x) = 1 :=
          A.valuation.map_one_add_of_lt (A.mem_nonunits_iff.mp hxnon)
        have hunit : 1 + x ∈ ValuationSubring.unitCarrier A :=
          theorem39_mem_unitCarrier_of_valuation_eq_one A hval
        have hU : 1 + x ∈ U H T := by
          rw [hobs.2.1]
          exact hunit
        exact hU.1
      obtain ⟨B, hB, hBcompat, hBbound⟩ :=
        theorem_2_10 T H hT hH hbasic hpre
      have hAB : A = B := by
        apply ValuationSubring.ext
        intro x
        change x ∈ (A : Set F) ↔ x ∈ (B : Set F)
        rw [hA, hB]
      have hAcompat : ValuationSubring.IsCompatible A T := by
        rw [hAB]
        exact hBcompat
      have hAbound : ValuationSubring.unitCarrier A * T ⊆ H := by
        rw [hAB]
        exact hBbound
      have hT_H : T ⊆ H := by
        intro t ht
        apply hAbound
        exact ⟨1, ⟨1, Subgroup.one_mem _, by simp⟩, t, ht, by simp⟩
      have hAcoarse : IsTCoarse A T := by
        have hno := lemma_3_1 T H hT hH hbasic A hA
        intro Δ hΔ hΔT
        apply hno Δ hΔ
        intro d hd
        obtain ⟨t, ht, hval⟩ := hΔT hd
        exact ⟨t, hT_H ht, hval⟩
      have hOF_A : OF T hT ≤ A := OF_le T hT A hAcompat hAcoarse
      rintro q ⟨u, hu, t, ht, rfl⟩
      apply hAbound
      refine ⟨u, ?_, t, ht, rfl⟩
      apply theorem39_unitCarrier_mono (OF T hT) A hOF_A
      exact hu
    · intro hHT_H
      have hT_HT : T ⊆ HT := by
        intro t ht
        exact ⟨1, ⟨1, Subgroup.one_mem _, by simp⟩, t, ht, by simp⟩
      have hOF : ((OF T hT : ValuationSubring F) : Set F) = O HT T := by
        simpa [HT, UF] using
          corollary_3_4 T hT (OF T hT) (OF_isTCoarse T hT)
            (OF_isCompatible T hT)
      obtain ⟨A, hA, -, -⟩ :=
        (corollary_2_11 T T HT H hT hT hHT hH hbasic_HT
          Set.Subset.rfl hT_HT hHT_H (OF T hT) hOF
          (OF_isCompatible T hT)).1
      exact ⟨A, hA⟩
  have hmore : ¬IsExceptional T → HT = C := by
    intro hnon
    obtain ⟨A, hAcompat, hAeq⟩ := (corollary_2_17 T hT).2 hnon
    apply Set.Subset.antisymm
    · have hsub := theorem39_UF_mul_subset_of_compatible T hT A hAcompat
      simpa [HT, C, hAeq] using hsub
    · exact hC_HT
  exact ⟨hC_HT, hindex, hpart3, hmore⟩

/-- AEJ, Theorem 3.9(1), journal p. 462:
`⟨B_F(T)⟩ ⊆ U_F(T)·T`. -/
theorem theorem_3_9_part1 (T : Set F) (hT : IsMulSubgroup T) :
    mulSubgroupClosureCarrier (basicPart T) ⊆ UF T hT * T :=
  (theorem_3_9 T hT).1

/-- AEJ, Theorem 3.9(2), journal p. 462:
`[U_F(T)·T : ⟨B_F(T)⟩] ≤ 2`, represented by a two-coset cover. -/
theorem theorem_3_9_part2 (T : Set F) (hT : IsMulSubgroup T) :
    HasIndexAtMostTwo (UF T hT * T)
      (mulSubgroupClosureCarrier (basicPart T)) :=
  (theorem_3_9 T hT).2.1

/-- AEJ, Theorem 3.9(3), journal p. 462: for a subgroup `H` containing
`B_F(T)`, `O_F(H,T)` is a valuation ring exactly when `U_F(T)·T ⊆ H`. -/
theorem theorem_3_9_part3 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H) :
    IsValuationRingCarrier (O H T) ↔ UF T hT * T ⊆ H :=
  (theorem_3_9 T hT).2.2.1 H hH hbasic

/-- AEJ, Theorem 3.9, moreover clause, journal p. 462: outside the
exceptional case, `U_F(T)·T = ⟨B_F(T)⟩`. -/
theorem theorem_3_9_moreover (T : Set F) (hT : IsMulSubgroup T)
    (hnonexceptional : ¬IsExceptional T) :
    UF T hT * T = mulSubgroupClosureCarrier (basicPart T) :=
  (theorem_3_9 T hT).2.2.2 hnonexceptional

end

end NU.AEJ
