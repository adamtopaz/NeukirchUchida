import Submission.NU.AEJ.OConstruction

/-!
# §3. T-coarse valuation rings (AEJ, journal pp. 460–461)

Mathlib's value group has an adjoined zero and currently has no bundled convex
subgroups.  `IsConvexValueSubgroup` therefore represents a convex subgroup of
`Γ_A` by a subset of `A.ValueGroup` which is multiplicatively closed, excludes
zero, and is order-convex.
-/

open Pointwise

namespace NU.AEJ

noncomputable section

variable {F : Type*} [Field F]

/-- The value set `v_A(S)`.  This is the notation used in AEJ, Lemma 3.1,
journal p. 460. -/
def valueSet (A : ValuationSubring F) (S : Set F) : Set A.ValueGroup :=
  A.valuation '' S

/-- A convex multiplicative subgroup of the nonzero part `Γ_A` of Mathlib's
value group.  The explicit exclusion of zero removes the adjoined value
`v_A(0)`.  This is the local encoding used for AEJ, Lemma 3.1, journal p. 460. -/
structure IsConvexValueSubgroup (A : ValuationSubring F)
    (Δ : Set A.ValueGroup) : Prop where
  one_mem : (1 : A.ValueGroup) ∈ Δ
  mul_mem : ∀ ⦃a b : A.ValueGroup⦄, a ∈ Δ → b ∈ Δ → a * b ∈ Δ
  inv_mem : ∀ ⦃a : A.ValueGroup⦄, a ∈ Δ → a⁻¹ ∈ Δ
  zero_notMem : (0 : A.ValueGroup) ∉ Δ
  convex : ∀ ⦃a b c : A.ValueGroup⦄,
    a ∈ Δ → c ∈ Δ → a ≤ b → b ≤ c → b ∈ Δ

/-- The assertion that `v_A(S)` contains no nontrivial convex subgroup: every
convex value subgroup contained in it is `{1}`.  This spells out the conclusion
of AEJ, Lemma 3.1, journal p. 460. -/
def ContainsNoNontrivialConvexSubgroup (A : ValuationSubring F)
    (S : Set F) : Prop :=
  ∀ Δ : Set A.ValueGroup,
    IsConvexValueSubgroup A Δ → Δ ⊆ valueSet A S → Δ = {1}

/-- `Δ` is the greatest convex subgroup of `Γ_A` contained in `v_A(S)`.
This is the subgroup denoted `Δ` in AEJ, Proposition 3.2, journal p. 460. -/
def IsMaximalConvexSubgroupIn (A : ValuationSubring F)
    (Δ : Set A.ValueGroup) (S : Set F) : Prop :=
  IsConvexValueSubgroup A Δ ∧ Δ ⊆ valueSet A S ∧
    ∀ E : Set A.ValueGroup,
      IsConvexValueSubgroup A E → E ⊆ valueSet A S → E ⊆ Δ

/-- AEJ, Lemma 3.1, journal p. 460: if `O_F(H,T)` is a valuation ring, then
`v_A(H)` contains no nontrivial convex subgroup of its value group. -/
theorem lemma_3_1 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (A : ValuationSubring F) (hA : (A : Set F) = O H T) :
    ContainsNoNontrivialConvexSubgroup A H := by
  intro Δ hΔ hsub
  have hobs := observation_2_3_part3_inParticular T H hT hH hbasic A hA
  ext d
  constructor
  · intro hd
    by_cases hd1 : d = 1
    · simpa [hd1]
    have hd0 : d ≠ 0 := fun e => hΔ.zero_notMem (e ▸ hd)
    let q := if d < 1 then d else d⁻¹
    have hqD : q ∈ Δ := by
      dsimp [q]
      split_ifs
      · exact hd
      · exact hΔ.inv_mem hd
    have hq0 : q ≠ 0 := fun e => hΔ.zero_notMem (e ▸ hqD)
    have hq1 : q < 1 := by
      dsimp [q]
      split_ifs with h
      · exact h
      · have h1d : 1 < d := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hd1)
        exact (inv_lt_one₀ (zero_lt_one.trans h1d)).mpr h1d
    obtain ⟨x, hxH, hxval⟩ := hsub hqD
    have hx0 : x ≠ 0 := by
      intro e
      apply hq0
      rw [← hxval, e, A.valuation.map_zero]
    have hxiH : x⁻¹ ∈ H := hH.inv_mem hxH
    have hxiA : x⁻¹ ∉ A := by
      intro hi
      have hv := (A.valuation_le_one_iff x⁻¹).mpr hi
      rw [A.valuation.map_inv, hxval] at hv
      exact (not_le_of_gt ((one_lt_inv₀ (pos_iff_ne_zero.mpr hq0)).mpr hq1)) hv
    have hxiO : x⁻¹ ∉ O H T := by
      intro hi
      apply hxiA
      change x⁻¹ ∈ (A : Set F)
      rw [hA]
      exact hi
    have hnotact : ¬x⁻¹ • Ominus H T ⊆ Ominus H T := by
      intro hact
      apply hxiO
      right
      exact ⟨inv_ne_zero hx0, hxiH, hact⟩
    obtain ⟨z, hz, hznot⟩ := Set.not_subset.mp hnotact
    obtain ⟨y, hy, rfl⟩ := hz
    have hy0 : y ≠ 0 := by
      intro e
      apply hznot
      simpa [e] using observation_2_3_part2 T H hT hH hbasic
    have hprodH : x⁻¹ * y ∉ H := by
      intro hp
      apply hy.1
      have hm := hH.mul_mem hxH hp
      have heq : x * (x⁻¹ * y) = y := by field_simp
      exact heq ▸ hm
    have hprodO : x⁻¹ * y ∉ O H T := by
      rintro (hm | hp)
      · exact hznot hm
      · exact hprodH hp.2.1
    have hprodA : x⁻¹ * y ∉ A := by
      intro hp
      apply hprodO
      change x⁻¹ * y ∈ (A : Set F) at hp
      rwa [hA] at hp
    have hinvA : (x⁻¹ * y)⁻¹ ∈ A :=
      (A.mem_or_inv_mem (x⁻¹ * y)).resolve_left hprodA
    have hinvH : (x⁻¹ * y)⁻¹ ∉ H := by
      intro hi
      apply hprodH
      simpa [mul_ne_zero (inv_ne_zero hx0) hy0] using hH.inv_mem hi
    have hinvminus : (x⁻¹ * y)⁻¹ ∈ Ominus H T := by
      have hiO : (x⁻¹ * y)⁻¹ ∈ O H T := by
        rw [← hA]
        exact hinvA
      rcases hiO with hi | hi
      · exact hi
      · exact False.elim (hinvH hi.2.1)
    have hxyminus : x * y⁻¹ ∈ Ominus H T := by
      convert hinvminus using 1 <;> field_simp [hx0, hy0] <;> ring
    have hvxy : A.valuation (x * y⁻¹) < 1 :=
      A.mem_nonunits_iff.mp (hobs.1 hxyminus)
    have hvy : A.valuation y < 1 :=
      A.mem_nonunits_iff.mp (hobs.1 hy)
    have hqvy : q < A.valuation y := by
      rw [A.valuation.map_mul, A.valuation.map_inv, hxval] at hvxy
      exact (div_lt_one₀ (A.valuation.pos_iff.mpr hy0)).mp hvxy
    have hvyD : A.valuation y ∈ Δ :=
      hΔ.convex hqD hΔ.one_mem hqvy.le hvy.le
    obtain ⟨h, hhH, hhval⟩ := hsub hvyD
    have hh0 : h ≠ 0 := fun e => hH.zero_notMem (e ▸ hhH)
    let u : Fˣ := Units.mk0 (h⁻¹ * y) (mul_ne_zero (inv_ne_zero hh0) hy0)
    have hu : (u : F) ∈ ValuationSubring.unitCarrier A := by
      refine ⟨u, ?_, rfl⟩
      change A.valuation (h⁻¹ * y) = 1
      rw [A.valuation.map_mul, A.valuation.map_inv, hhval]
      exact inv_mul_cancel₀ (A.valuation.ne_zero_iff.mpr hy0)
    have huH := hobs.2.2 hu
    apply False.elim
    apply hy.1
    have hm := hH.mul_mem hhH huH
    have heq : h * (h⁻¹ * y) = y := by field_simp
    exact heq ▸ hm
  · intro hd
    rw [Set.mem_singleton_iff] at hd
    subst d
    exact hΔ.one_mem

-- TODO(value-group quotient): Mathlib v4.32.0 has no convex-subgroup quotient
-- or coarsening/composite-valuation correspondence.  The next statement uses
-- the equivalent overring characterization: the units of the coarsening have
-- exactly the greatest convex value subgroup contained in `v_A(H)`.

/-- AEJ, Proposition 3.2, journal p. 460, in the faithful overring
formulation supported by Mathlib's surveyed API.  `O_F(H,T)` is the coarsening
`B ≥ A` whose kernel value subgroup `v_A(U_B)` is the greatest convex subgroup
of `Γ_A` contained in `v_A(H)`.  This is equivalent to saying that `B`
corresponds to `F˙ → Γ_A → Γ_A/Δ`. -/
theorem proposition_3_2 (T H : Set F) (hT : IsMulSubgroup T)
    (hH : IsMulSubgroup H) (hbasic : basicPart T ⊆ H)
    (A : ValuationSubring F) (hcompat : ValuationSubring.IsCompatible A T)
    (hunits : ValuationSubring.unitCarrier A * T ⊆ H) :
    ∃ B : ValuationSubring F,
      (B : Set F) = O H T ∧ A ≤ B ∧
        IsMaximalConvexSubgroupIn A
          (valueSet A (ValuationSubring.unitCarrier B)) H := by
  let P := ValuationSubring.principalUnitCarrier A
  let U := ValuationSubring.unitCarrier A
  have hP_eq : P = ValuationSubring.onePlusMaximalIdeal A := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨1, by simp, (u : F) - 1, ?_, by ring⟩
      change A.valuation ((u : F) - 1) < 1
      exact hu
    · rintro ⟨a, ha, m, hm, heq⟩
      have ha1 : a = 1 := by simpa using ha
      subst a
      have hval := A.valuation.map_one_add_of_lt (A.mem_nonunits_iff.mp hm)
      have hne : 1 + m ≠ 0 := by
        intro e
        rw [e, A.valuation.map_zero] at hval
        exact zero_ne_one hval
      let u : Fˣ := Units.mk0 (1 + m) hne
      refine ⟨u, ?_, ?_⟩
      · change A.valuation ((u : F) - 1) < 1
        change A.valuation ((1 + m) - 1) < 1
        simpa using A.mem_nonunits_iff.mp hm
      · change (1 + m : F) = q
        exact heq
  have hP : IsMulSubgroup P := by
    constructor
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · rintro q r ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u * v, Subgroup.mul_mem _ hu hv, by simp⟩
    · rintro q ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, Subgroup.inv_mem _ hu, by simp⟩
    · rintro ⟨u, -, heq⟩
      exact Units.ne_zero u heq
  have hU : IsMulSubgroup U := by
    constructor
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · rintro q r ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u * v, Subgroup.mul_mem _ hu hv, by simp⟩
    · rintro q ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, Subgroup.inv_mem _ hu, by simp⟩
    · rintro ⟨u, -, heq⟩
      exact Units.ne_zero u heq
  have hPU : P ⊆ U := by
    rintro q ⟨u, hu, rfl⟩
    exact ⟨u, A.principal_units_le_units hu, rfl⟩
  have hPT : P ⊆ T := hcompat
  have hcompatP : ValuationSubring.IsCompatible A P := Set.Subset.rfl
  have hbasicU : basicPart P ⊆ U := by
    intro q hq
    obtain ⟨u, hu, p, hp, rfl⟩ :=
      proposition_1_9_part1 A P hP hcompatP hq
    exact hU.mul_mem hu (hPU hp)
  have hUH : U ⊆ H := by
    intro u hu
    apply hunits
    exact ⟨u, hu, 1, hT.one_mem, by simp⟩
  have hTH : T ⊆ H := by
    intro t ht
    apply hunits
    exact ⟨1, hU.one_mem, t, ht, by simp⟩
  have hAO : (A : Set F) = O U P := by
    calc
      (A : Set F) = O U (ValuationSubring.onePlusMaximalIdeal A) :=
        (observation_2_3_part6 A).2.2
      _ = O U P := congrArg (fun S => O U S) hP_eq.symm
  obtain ⟨⟨B, hBP, hBcompatP, hAB⟩, -⟩ :=
    corollary_2_11 P P U H hP hP hU hH hbasicU Set.Subset.rfl hPU hUH
      A hAO hcompatP
  have hbasicH : basicPart P ⊆ H := hbasicU.trans hUH
  have hEq := (corollary_2_11 P T H H hP hT hH hH hbasicH hPT hTH
    Set.Subset.rfl B hBP hBcompatP).2
  have hB : (B : Set F) = O H T := hBP.trans hEq
  let f := A.mapOfLE B hAB
  let K := valueSet A (ValuationSubring.unitCarrier B)
  have hKker : ∀ d : A.ValueGroup, d ∈ K ↔ f d = 1 := by
    intro d
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      change B.valuation (u : F) = 1
      exact (B.mem_unitGroup_iff u).mp hu
    · intro hd
      obtain ⟨x, hx⟩ := A.valuation_surjective d
      have hx0 : x ≠ 0 := by
        intro e
        have : d = 0 := by rw [← hx, e, A.valuation.map_zero]
        rw [this] at hd
        change f 0 = 1 at hd
        rw [f.map_zero] at hd
        exact zero_ne_one hd
      let u : Fˣ := Units.mk0 x hx0
      refine ⟨x, ⟨u, ?_, rfl⟩, hx⟩
      change B.valuation x = 1
      rw [← ValuationSubring.mapOfLE_valuation_apply A B hAB x, hx]
      exact hd
  have hK : IsConvexValueSubgroup A K := by
    constructor
    · apply (hKker 1).mpr
      exact f.map_one
    · intro a b ha hb
      apply (hKker (a * b)).mpr
      rw [f.map_mul, (hKker a).mp ha, (hKker b).mp hb, one_mul]
    · intro a ha
      apply (hKker a⁻¹).mpr
      rw [map_inv₀, (hKker a).mp ha, inv_one]
    · intro hz
      have := (hKker 0).mp hz
      rw [f.map_zero] at this
      exact zero_ne_one this
    · intro a b c ha hc hab hbc
      apply (hKker b).mpr
      have hfab : f a ≤ f b := ValuationSubring.monotone_mapOfLE A B hAB hab
      have hfbc : f b ≤ f c := ValuationSubring.monotone_mapOfLE A B hAB hbc
      rw [(hKker a).mp ha] at hfab
      rw [(hKker c).mp hc] at hfbc
      exact le_antisymm hfbc hfab
  have hKH : K ⊆ valueSet A H := by
    have hunitH :=
      (observation_2_3_part3_inParticular T H hT hH hbasic B hB).2.2
    rintro d ⟨x, hx, rfl⟩
    exact ⟨x, hunitH hx, rfl⟩
  have convexComparable : ∀ (D E : Set A.ValueGroup),
      IsConvexValueSubgroup A D → IsConvexValueSubgroup A E →
      D ⊆ E ∨ E ⊆ D := by
    intro D E hD hE
    by_cases hDE : D ⊆ E
    · exact Or.inl hDE
    · right
      obtain ⟨d, hdD, hdE⟩ := Set.not_subset.mp hDE
      have hd0 : d ≠ 0 := fun e => hD.zero_notMem (e ▸ hdD)
      have hd1 : d ≠ 1 := fun e => hdE (e ▸ hE.one_mem)
      let q := if d < 1 then d else d⁻¹
      have hqD : q ∈ D := by
        dsimp [q]; split_ifs
        · exact hdD
        · exact hD.inv_mem hdD
      have hq0 : q ≠ 0 := fun e => hD.zero_notMem (e ▸ hqD)
      have hq1 : q < 1 := by
        dsimp [q]; split_ifs with h
        · exact h
        · have h1d : 1 < d := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hd1)
          exact (inv_lt_one₀ (zero_lt_one.trans h1d)).mpr h1d
      have hqE : q ∉ E := by
        dsimp [q]; split_ifs
        · exact hdE
        · intro hi
          exact hdE (by simpa [hd0] using hE.inv_mem hi)
      intro e heE
      have hqe : q ≤ e := by
        by_contra hn
        exact hqE (hE.convex heE hE.one_mem (le_of_not_ge hn) hq1.le)
      have heqi : e ≤ q⁻¹ := by
        by_contra hn
        have hqiE : q⁻¹ ∈ E := hE.convex hE.one_mem heE
          ((one_le_inv₀ (pos_iff_ne_zero.mpr hq0)).mpr hq1.le) (le_of_not_ge hn)
        exact hqE (by simpa [hq0] using hE.inv_mem hqiE)
      exact hD.convex hqD (hD.inv_mem hqD) hqe heqi
  have hmax : ∀ E : Set A.ValueGroup,
      IsConvexValueSubgroup A E → E ⊆ valueSet A H → E ⊆ K := by
    intro E hE hEH
    rcases convexComparable E K hE hK with hEK | hKE
    · exact hEK
    · let I : Set B.ValueGroup := f '' E
      have hI : IsConvexValueSubgroup B I := by
        constructor
        · exact ⟨1, hE.one_mem, f.map_one⟩
        · rintro a b ⟨da, hda, rfl⟩ ⟨db, hdb, rfl⟩
          exact ⟨da * db, hE.mul_mem hda hdb, f.map_mul da db⟩
        · rintro a ⟨da, hda, rfl⟩
          exact ⟨da⁻¹, hE.inv_mem hda, map_inv₀ f da⟩
        · rintro ⟨d, hd, hfd⟩
          obtain ⟨x, hx⟩ := A.valuation_surjective d
          have hd0 : d ≠ 0 := fun ed => hE.zero_notMem (ed ▸ hd)
          have hx0 : x ≠ 0 := by
            intro ex
            apply hd0
            rw [← hx, ex, A.valuation.map_zero]
          have : f d ≠ 0 := by
            rw [← hx, ValuationSubring.mapOfLE_valuation_apply]
            exact B.valuation.ne_zero_iff.mpr hx0
          exact this hfd
        · rintro a b c ⟨da, hda, rfl⟩ ⟨dc, hdc, rfl⟩ hab hbc
          obtain ⟨x, hx⟩ := A.valuation_surjective da
          obtain ⟨y, hy⟩ := B.valuation_surjective b
          obtain ⟨z, hz⟩ := A.valuation_surjective dc
          let e := A.valuation y
          have hfe : f e = b := by
            change B.valuation y = b
            exact hy
          refine ⟨e, ?_, hfe⟩
          have hxy : B.valuation x ≤ B.valuation y := by
            rw [← ValuationSubring.mapOfLE_valuation_apply A B hAB x, hx, hy]
            exact hab
          have hyz : B.valuation y ≤ B.valuation z := by
            rw [← ValuationSubring.mapOfLE_valuation_apply A B hAB z, hz, hy]
            exact hbc
          obtain ⟨r, hr⟩ := (B.valuation_le_iff x y).mp hxy
          obtain ⟨s, hs⟩ := (B.valuation_le_iff y z).mp hyz
          have lower : da ≤ e ∨ e ∈ E := by
            by_cases hrA : (r : F) ∈ A
            · left
              rw [← hx]
              exact (A.valuation_le_iff x y).mpr ⟨⟨r, hrA⟩, hr⟩
            · right
              have hriA : (r : F)⁻¹ ∈ A := (A.mem_or_inv_mem (r : F)).resolve_left hrA
              have hriB : (r : F)⁻¹ ∈ B := hAB hriA
              have hr0 : (r : F) ≠ 0 := by
                intro er
                have ex : x = 0 := by rw [← hr, er, zero_mul]
                apply hE.zero_notMem
                have : da = 0 := by rw [← hx, ex, A.valuation.map_zero]
                exact this ▸ hda
              have hrval : B.valuation (r : F) = 1 := by
                apply le_antisymm (B.valuation_le_one r)
                have hi := (B.valuation_le_one_iff ((r : F)⁻¹)).mpr hriB
                rw [B.valuation.map_inv] at hi
                exact (inv_le_one₀ (B.valuation.pos_iff.mpr hr0)).mp hi
              have hkr : A.valuation (r : F) ∈ K := by
                apply (hKker _).mpr
                rw [ValuationSubring.mapOfLE_valuation_apply, hrval]
              have hvaleq : da = A.valuation (r : F) * e := by
                rw [← hx]
                change A.valuation x = A.valuation (r : F) * A.valuation y
                rw [← A.valuation.map_mul, hr]
              have hkr0 := A.valuation.ne_zero_iff.mpr hr0
              have heq : (A.valuation (r : F))⁻¹ * da = e := by
                rw [hvaleq, ← mul_assoc, inv_mul_cancel₀ hkr0, one_mul]
              exact heq ▸ hE.mul_mem (hE.inv_mem (hKE hkr)) hda
          have upper : e ≤ dc ∨ e ∈ E := by
            by_cases hsA : (s : F) ∈ A
            · left
              rw [← hz]
              exact (A.valuation_le_iff y z).mpr ⟨⟨s, hsA⟩, hs⟩
            · right
              have hsiA : (s : F)⁻¹ ∈ A := (A.mem_or_inv_mem (s : F)).resolve_left hsA
              have hsiB : (s : F)⁻¹ ∈ B := hAB hsiA
              have hda0 : da ≠ 0 := fun ed => hE.zero_notMem (ed ▸ hda)
              have hfda0 : f da ≠ 0 := by
                obtain ⟨w, hw⟩ := A.valuation_surjective da
                rw [← hw, ValuationSubring.mapOfLE_valuation_apply]
                exact B.valuation.ne_zero_iff.mpr (by
                  intro ew
                  apply hda0
                  rw [← hw, ew, A.valuation.map_zero])
              have hb0 : b ≠ 0 := by
                intro eb
                apply hfda0
                apply le_antisymm
                · rw [eb] at hab
                  exact hab
                · exact bot_le
              have hy0 : y ≠ 0 := by
                intro ey
                apply hb0
                rw [← hy, ey, B.valuation.map_zero]
              have hs0 : (s : F) ≠ 0 := by
                intro es
                apply hy0
                rw [← hs, es, zero_mul]
              have hsval : B.valuation (s : F) = 1 := by
                apply le_antisymm (B.valuation_le_one s)
                have hi := (B.valuation_le_one_iff ((s : F)⁻¹)).mpr hsiB
                rw [B.valuation.map_inv] at hi
                exact (inv_le_one₀ (B.valuation.pos_iff.mpr hs0)).mp hi
              have hks : A.valuation (s : F) ∈ K := by
                apply (hKker _).mpr
                rw [ValuationSubring.mapOfLE_valuation_apply, hsval]
              have hvaleq : e = A.valuation (s : F) * dc := by
                dsimp [e]
                rw [← hz, ← A.valuation.map_mul, hs]
              exact hvaleq ▸ hE.mul_mem (hKE hks) hdc
          rcases lower with hle | he
          · rcases upper with heu | he
            · exact hE.convex hda hdc hle heu
            · exact he
          · exact he
      have hIH : I ⊆ valueSet B H := by
        rintro d ⟨c, hc, rfl⟩
        obtain ⟨x, hxH, hxc⟩ := hEH hc
        refine ⟨x, hxH, ?_⟩
        rw [← hxc]
        exact ValuationSubring.mapOfLE_valuation_apply A B hAB x
      have hItriv : I = {1} := lemma_3_1 T H hT hH hbasic B hB I hI hIH
      intro d hd
      apply (hKker d).mpr
      have : f d ∈ I := ⟨d, hd, rfl⟩
      rw [hItriv] at this
      exact this
  exact ⟨B, hB, hAB, hK, hKH, hmax⟩

/-- AEJ, Definition 3.3, journal p. 461: `A` is `T`-coarse when `v_A(T)`
(equivalently `v_A(U_A·T)`) contains no nontrivial convex subgroup of `Γ_A`. -/
def IsTCoarse (A : ValuationSubring F) (T : Set F) : Prop :=
  ContainsNoNontrivialConvexSubgroup A T

/-- AEJ, Corollary 3.4, journal p. 461: a `T`-coarse, `T`-compatible valuation
ring is recovered as `O_F(U_A·T,T)`. -/
theorem corollary_3_4 (T : Set F) (hT : IsMulSubgroup T)
    (A : ValuationSubring F) (hcoarse : IsTCoarse A T)
    (hcompat : ValuationSubring.IsCompatible A T) :
    (A : Set F) = O (ValuationSubring.unitCarrier A * T) T := by
  let H := ValuationSubring.unitCarrier A * T
  have hU : IsMulSubgroup (ValuationSubring.unitCarrier A) := by
    constructor
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u * v, Subgroup.mul_mem _ hu hv, by simp⟩
    · rintro x ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, Subgroup.inv_mem _ hu, by simp⟩
    · rintro ⟨u, -, heq⟩
      exact Units.ne_zero u heq
  have hH : IsMulSubgroup H := by
    constructor
    · exact ⟨1, hU.one_mem, 1, hT.one_mem, by simp⟩
    · rintro x y ⟨u, hu, t, ht, rfl⟩ ⟨v, hv, s, hs, rfl⟩
      exact ⟨u * v, hU.mul_mem hu hv, t * s, hT.mul_mem ht hs, by ring⟩
    · rintro x ⟨u, hu, t, ht, rfl⟩
      exact ⟨u⁻¹, hU.inv_mem hu, t⁻¹, hT.inv_mem ht, by simp [mul_comm]⟩
    · rintro ⟨u, hu, t, ht, heq⟩
      exact mul_ne_zero (fun e => hU.zero_notMem (e ▸ hu))
        (fun e => hT.zero_notMem (e ▸ ht)) heq
  have hbasic : basicPart T ⊆ H :=
    proposition_1_9_part1 A T hT hcompat
  obtain ⟨B, hB, hAB, hmax⟩ :=
    proposition_3_2 T H hT hH hbasic A hcompat Set.Subset.rfl
  have hDeltaT : valueSet A (ValuationSubring.unitCarrier B) ⊆ valueSet A T := by
    intro d hd
    obtain ⟨x, ⟨u, hu, t, ht, rfl⟩, rfl⟩ := hmax.2.1 hd
    refine ⟨t, ht, ?_⟩
    obtain ⟨u', hu', rfl⟩ := hu
    change A.valuation t = A.valuation ((u' : F) * t)
    rw [A.valuation.map_mul]
    have huv : A.valuation (u' : F) = 1 :=
      (A.mem_unitGroup_iff u').mp hu'
    rw [huv, one_mul]
  have htriv : valueSet A (ValuationSubring.unitCarrier B) = {1} :=
    hcoarse _ hmax.1 hDeltaT
  have hBA : B ≤ A := by
    rw [← ValuationSubring.unitGroup_le_unitGroup]
    intro u hu
    have hd : A.valuation ((u : Fˣ) : F) ∈
        valueSet A (ValuationSubring.unitCarrier B) := by
      refine ⟨((u : Fˣ) : F), ?_, rfl⟩
      exact ⟨u, hu, rfl⟩
    rw [htriv] at hd
    simpa [ValuationSubring.mem_unitGroup_iff] using hd
  have hEq : A = B := le_antisymm hAB hBA
  exact (congrArg (fun C : ValuationSubring F => (C : Set F)) hEq).trans hB

/-- AEJ, Proposition 3.5, journal p. 461: two incomparable `T`-compatible
valuation rings force `B_F(T)=T=U_B·T`; moreover `O_F(T,T)` is a valuation
ring containing both, and `-1 ∈ T`. -/
theorem proposition_3_5 (T : Set F) (hT : IsMulSubgroup T)
    (A B : ValuationSubring F)
    (hA : ValuationSubring.IsCompatible A T)
    (hB : ValuationSubring.IsCompatible B T)
    (hincomp : ¬A ≤ B ∧ ¬B ≤ A) :
    basicPart T = T ∧
      T = ValuationSubring.unitCarrier B * T ∧
      (∃ C : ValuationSubring F,
        (C : Set F) = O T T ∧ A ≤ C ∧ B ≤ C) ∧
      (-1 : F) ∈ T := by
  obtain ⟨a, haA, haB⟩ := Set.not_subset.mp hincomp.1
  obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hincomp.2
  have ha0 : a ≠ 0 := by
    intro e
    exact haB (e ▸ B.zero_mem)
  have hb0 : b ≠ 0 := by
    intro e
    exact hbA (e ▸ A.zero_mem)
  let x := a * b⁻¹
  have hx0 : x ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
  have hxA : x ∈ A := A.mul_mem _ _ haA (A.mem_or_inv_mem b |>.resolve_left hbA)
  have hxiB : x⁻¹ ∈ B := by
    have haiB : a⁻¹ ∈ B := (B.mem_or_inv_mem a).resolve_left haB
    convert B.mul_mem _ _ haiB hbB using 1 <;> dsimp [x] <;> field_simp
  have hxiA : x⁻¹ ∉ A := by
    intro h
    apply hbA
    have hh := A.mul_mem _ _ haA h
    have heq : a * x⁻¹ = b := by dsimp [x]; field_simp
    exact heq ▸ hh
  have hxB : x ∉ B := by
    intro h
    apply haB
    have hh := B.mul_mem _ _ h hbB
    have heq : x * b = a := by dsimp [x]; field_simp
    exact heq ▸ hh
  have hxnonA : x ∈ A.nonunits :=
    (A.mem_nonunits_iff_or).mpr (Or.inr hxiA)
  have hxinonB : x⁻¹ ∈ B.nonunits :=
    (B.mem_nonunits_iff_or).mpr (Or.inr (by simpa using hxB))
  have hone : ∀ (V : ValuationSubring F),
      ValuationSubring.IsCompatible V T → ∀ {z : F}, z ∈ V.nonunits → 1 + z ∈ T := by
    intro V hV z hz
    have hv := V.valuation.map_one_add_of_lt (V.mem_nonunits_iff.mp hz)
    have hn : 1 + z ≠ 0 := by
      intro e
      rw [e, V.valuation.map_zero] at hv
      exact zero_ne_one hv
    let u : Fˣ := Units.mk0 (1 + z) hn
    apply hV
    refine ⟨u, ?_, rfl⟩
    change V.valuation ((u : F) - 1) < 1
    change V.valuation ((1 + z) - 1) < 1
    simpa using V.mem_nonunits_iff.mp hz
  have hcross : ∀ (V W : ValuationSubring F),
      ValuationSubring.IsCompatible V T → ValuationSubring.IsCompatible W T →
      ∀ {z : F}, z ≠ 0 → z ∈ V.nonunits → z⁻¹ ∈ W.nonunits → z ∈ T := by
    intro V W hV hW z hz0 hzV hziW
    have hz1 := hone V hV hzV
    have hzi1 := hone W hW hziW
    have hm := hT.mul_mem hz1 (hT.inv_mem hzi1)
    have hzi1ne : 1 + z⁻¹ ≠ 0 := fun e => hT.zero_notMem (e ▸ hzi1)
    have heq : (1 + z) * (1 + z⁻¹)⁻¹ = z := by
      rw [← div_eq_mul_inv]
      apply (div_eq_iff hzi1ne).2
      field_simp [hz0]
      <;> ring
    exact heq ▸ hm
  have hunit_general : ∀ (V W : ValuationSubring F),
      ValuationSubring.IsCompatible V T → ValuationSubring.IsCompatible W T →
      ∀ {z : F}, z ≠ 0 → z ∈ V.nonunits → z⁻¹ ∈ W.nonunits →
        ValuationSubring.unitCarrier W ⊆ T := by
    intro V W hV hW z hz0 hzV hziW y hy
    have hziV : z⁻¹ ∉ V := ((V.mem_nonunits_iff_or).mp hzV).resolve_left hz0
    have hzW : z ∉ W := by
      have hh := ((W.mem_nonunits_iff_or).mp hziW).resolve_left (inv_ne_zero hz0)
      simpa [hz0] using hh
    have hzT := hcross V W hV hW hz0 hzV hziW
    obtain ⟨u, hu, rfl⟩ := hy
    have hy0 : (u : F) ≠ 0 := Units.ne_zero u
    have hyW : (u : F) ∈ W :=
      (W.valuation_le_one_iff _).mp ((W.mem_unitGroup_iff u).mp hu).le
    have hyiW : (u : F)⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, W.valuation.map_inv,
        (W.mem_unitGroup_iff u).mp hu]
      simp
    have hmem : ∀ {y : F}, y ≠ 0 → y ∈ W → y⁻¹ ∈ W → y ∈ V → y ∈ T := by
      intro y hy0 hyW hyiW hyV
      have hzyV : z * y ∈ V.nonunits := by
        apply V.mem_nonunits_iff_or.mpr
        right
        intro hi
        apply hziV
        have hh := V.mul_mem _ _ hi hyV
        convert hh using 1 <;> field_simp [hz0, hy0]
      have hzyiW : (z * y)⁻¹ ∈ W.nonunits := by
        apply W.mem_nonunits_iff_or.mpr
        right
        intro hi
        apply hzW
        have hzyW : z * y ∈ W := by
          simpa [mul_ne_zero hz0 hy0] using hi
        have hh := W.mul_mem _ _ hzyW hyiW
        convert hh using 1 <;> field_simp [hy0]
      have hzyT := hcross V W hV hW (mul_ne_zero hz0 hy0) hzyV hzyiW
      have hm := hT.mul_mem (hT.inv_mem hzT) hzyT
      convert hm using 1 <;> field_simp [hz0]
    by_cases hyV : (u : F) ∈ V
    · exact hmem hy0 hyW hyiW hyV
    · have hyiV : (u : F)⁻¹ ∈ V := (V.mem_or_inv_mem (u : F)).resolve_left hyV
      have hyiT := hmem (inv_ne_zero hy0) hyiW (by simpa [hy0] using hyW) hyiV
      simpa [hy0] using hT.inv_mem hyiT
  have hUB : ValuationSubring.unitCarrier B ⊆ T :=
    hunit_general A B hA hB hx0 hxnonA hxinonB
  have hUA : ValuationSubring.unitCarrier A ⊆ T := by
    have hi0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hiiA : (x⁻¹)⁻¹ ∈ A.nonunits := by simpa [hx0] using hxnonA
    exact hunit_general B A hB hA hi0 hxinonB hiiA
  have hUT (V : ValuationSubring F)
      (hU : ValuationSubring.unitCarrier V ⊆ T) :
      ValuationSubring.unitCarrier V * T = T := by
    apply Set.Subset.antisymm
    · rintro q ⟨u, hu, t, ht, rfl⟩
      exact hT.mul_mem (hU hu) ht
    · intro t ht
      refine ⟨1, ?_, t, ht, by simp⟩
      exact ⟨1, by simp, by simp⟩
  have hUBT := hUT B hUB
  have hUAT := hUT A hUA
  have hbasic_le : basicPart T ⊆ T := by
    intro q hq
    have hh := proposition_1_9_part1 B T hT hB hq
    rw [hUBT] at hh
    exact hh
  have hT_le_basic : T ⊆ basicPart T := by
    intro t ht
    refine ⟨fun e => hT.zero_notMem (e ▸ ht), ?_⟩
    rintro ⟨hrt, hrnt⟩
    by_cases hn : (-1 : F) ∈ T
    · have hnt : -t ∈ T := by simpa using hT.mul_mem hn ht
      have hz := hrt (Set.add_mem_add hnt
        (Set.smul_mem_smul_set (a := t) hT.one_mem))
      have hz0 : (-t) + t • (1 : F) = 0 := by simp [smul_eq_mul]
      rw [hz0] at hz
      rcases hz with hz | ⟨s, hs, heq⟩
      · exact hT.zero_notMem hz
      · change t * s = 0 at heq
        exact mul_ne_zero (fun e => hT.zero_notMem (e ▸ ht))
          (fun e => hT.zero_notMem (e ▸ hs)) heq
    · have hz := hrnt (Set.add_mem_add ht
        (Set.smul_mem_smul_set (a := -t) hT.one_mem))
      have hz0 : t + (-t) • (1 : F) = 0 := by simp [smul_eq_mul]
      rw [hz0] at hz
      rcases hz with hz | ⟨s, hs, heq⟩
      · exact hT.zero_notMem hz
      · change (-t) * s = 0 at heq
        exact mul_ne_zero (neg_ne_zero.mpr (fun e => hT.zero_notMem (e ▸ ht)))
          (fun e => hT.zero_notMem (e ▸ hs)) heq
  have hbasic : basicPart T = T := Set.Subset.antisymm hbasic_le hT_le_basic
  obtain ⟨CA, hCA, hACA, -⟩ :=
    proposition_3_2 T T hT hT (by rw [hbasic]) A hA (by rw [hUAT])
  obtain ⟨CB, hCB, hBCB, -⟩ :=
    proposition_3_2 T T hT hT (by rw [hbasic]) B hB (by rw [hUBT])
  have hCBCA : CB = CA := by
    apply ValuationSubring.ext
    intro q
    change q ∈ (CB : Set F) ↔ q ∈ (CA : Set F)
    rw [hCB, hCA]
  have hBCA : B ≤ CA := hBCB.trans_eq hCBCA
  have hnegUnit : (-1 : F) ∈ ValuationSubring.unitCarrier CA := by
    let u : Fˣ := Units.mk0 (-1 : F) (by simp)
    refine ⟨u, ?_, rfl⟩
    change CA.valuation (u : F) = 1
    simp [u]
  have hunitCA : ValuationSubring.unitCarrier CA ⊆ T := by
    have hobs := observation_2_3_part3_inParticular T T hT hT
      (by rw [hbasic]) CA hCA
    exact hobs.2.2
  exact ⟨hbasic, hUBT.symm, ⟨CA, hCA, hACA, hBCA⟩, hunitCA hnegUnit⟩

/-- AEJ, Corollary 3.7, journal p. 461: any two `T`-coarse,
`T`-compatible valuation rings are comparable. -/
theorem corollary_3_7 (T : Set F) (hT : IsMulSubgroup T)
    (A B : ValuationSubring F)
    (hAcoarse : IsTCoarse A T) (hAcompat : ValuationSubring.IsCompatible A T)
    (hBcoarse : IsTCoarse B T) (hBcompat : ValuationSubring.IsCompatible B T) :
    A ≤ B ∨ B ≤ A := by
  by_contra h
  rw [not_or] at h
  obtain ⟨-, hBT, -, -⟩ :=
    proposition_3_5 T hT A B hAcompat hBcompat h
  obtain ⟨-, hAT, -, -⟩ :=
    proposition_3_5 T hT B A hBcompat hAcompat ⟨h.2, h.1⟩
  have hAe := corollary_3_4 T hT A hAcoarse hAcompat
  have hBe := corollary_3_4 T hT B hBcoarse hBcompat
  have hAc : (A : Set F) = O T T :=
    hAe.trans (congrArg (fun H => O H T) hAT.symm)
  have hBc : (B : Set F) = O T T :=
    hBe.trans (congrArg (fun H => O H T) hBT.symm)
  have hEq : A = B := by
    apply ValuationSubring.ext
    intro x
    change x ∈ (A : Set F) ↔ x ∈ (B : Set F)
    rw [hAc, hBc]
  exact h.1 hEq.le

/-- AEJ, Theorem 3.8, journal p. 461: there is a unique smallest (finest)
`T`-coarse, `T`-compatible valuation ring of `F`. -/
theorem theorem_3_8 (T : Set F) (hT : IsMulSubgroup T) :
    ∃! A : ValuationSubring F,
      ValuationSubring.IsCompatible A T ∧ IsTCoarse A T ∧
        ∀ B : ValuationSubring F,
          ValuationSubring.IsCompatible B T → IsTCoarse B T → A ≤ B := by
  have topval : ∀ {x : F}, x ≠ 0 →
      (⊤ : ValuationSubring F).valuation x = 1 := by
    intro x hx
    apply le_antisymm
    · exact ((⊤ : ValuationSubring F).valuation_le_one_iff x).mpr trivial
    · have hi : (⊤ : ValuationSubring F).valuation x⁻¹ ≤ 1 :=
        ((⊤ : ValuationSubring F).valuation_le_one_iff x⁻¹).mpr trivial
      rw [(⊤ : ValuationSubring F).valuation.map_inv] at hi
      exact (inv_le_one₀ ((⊤ : ValuationSubring F).valuation.pos_iff.mpr hx)).mp hi
  have htopCompat : ValuationSubring.IsCompatible (⊤ : ValuationSubring F) T := by
    rintro q ⟨u, hu, rfl⟩
    have heq : (u : F) - 1 = 0 := by
      by_contra hn
      have hv := topval hn
      exact (not_lt_of_ge hv.ge) hu
    have hu1 : (u : F) = 1 := sub_eq_zero.mp heq
    simpa [hu1] using hT.one_mem
  have htopCoarse : IsTCoarse (⊤ : ValuationSubring F) T := by
    intro Δ hΔ hsub
    ext d
    constructor
    · intro hd
      obtain ⟨t, ht, rfl⟩ := hsub hd
      have ht0 : t ≠ 0 := fun e => hT.zero_notMem (e ▸ ht)
      simp [topval ht0]
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      exact hΔ.one_mem
  let 𝒱 := {A : ValuationSubring F //
    ValuationSubring.IsCompatible A T ∧ IsTCoarse A T}
  have h𝒱 : Nonempty 𝒱 := ⟨⟨⊤, htopCompat, htopCoarse⟩⟩
  let R : Subring F :=
    { carrier := {x : F | ∀ V : 𝒱, x ∈ V.1}
      zero_mem' := fun _ => ValuationSubring.zero_mem _
      one_mem' := fun _ => ValuationSubring.one_mem _
      add_mem' := fun hx hy V => V.1.add_mem _ _ (hx V) (hy V)
      mul_mem' := fun hx hy V => V.1.mul_mem _ _ (hx V) (hy V)
      neg_mem' := fun hx V => V.1.neg_mem _ (hx V) }
  have hval : ∀ x : F, x ∈ R ∨ x⁻¹ ∈ R := by
    intro x
    by_cases hx : ∀ V : 𝒱, x ∈ V.1
    · exact Or.inl hx
    · right
      change ∀ W : 𝒱, x⁻¹ ∈ W.1
      push_neg at hx
      obtain ⟨V, hxV⟩ := hx
      have hxiV : x⁻¹ ∈ V.1 := (V.1.mem_or_inv_mem x).resolve_left hxV
      intro W
      rcases corollary_3_7 T hT V.1 W.1 V.2.2 V.2.1 W.2.2 W.2.1 with hVW | hWV
      · exact hVW hxiV
      · exact (W.1.mem_or_inv_mem x).resolve_left (fun hxW => hxV (hWV hxW))
  let C : ValuationSubring F := ValuationSubring.ofSubring R hval
  have hCV : ∀ V : 𝒱, C ≤ V.1 := by
    intro V x hx
    exact hx V
  have hCcompat : ValuationSubring.IsCompatible C T := by
    rintro q ⟨u, hu, rfl⟩
    let z : F := (u : F) - 1
    by_cases hz : z = 0
    · have hu1 : (u : F) = 1 := sub_eq_zero.mp hz
      simpa [hu1] using hT.one_mem
    · have hzinv : z⁻¹ ∉ C := by
        have hznon : z ∈ C.nonunits := C.mem_nonunits_iff.mpr hu
        exact ((C.mem_nonunits_iff_or).mp hznon).resolve_left hz
      change ¬(∀ V : 𝒱, z⁻¹ ∈ V.1) at hzinv
      push_neg at hzinv
      obtain ⟨V, hzV⟩ := hzinv
      apply V.2.1
      refine ⟨u, ?_, rfl⟩
      change V.1.valuation ((u : F) - 1) < 1
      apply V.1.mem_nonunits_iff.mp
      apply V.1.mem_nonunits_iff_or.mpr
      exact Or.inr hzV
  have convexComparable : ∀ (D E : Set C.ValueGroup),
      IsConvexValueSubgroup C D → IsConvexValueSubgroup C E →
      D ⊆ E ∨ E ⊆ D := by
    intro D E hD hE
    by_cases hDE : D ⊆ E
    · exact Or.inl hDE
    · right
      obtain ⟨d, hdD, hdE⟩ := Set.not_subset.mp hDE
      have hd0 : d ≠ 0 := fun e => hD.zero_notMem (e ▸ hdD)
      have hd1 : d ≠ 1 := fun e => hdE (e ▸ hE.one_mem)
      let q := if d < 1 then d else d⁻¹
      have hqD : q ∈ D := by
        dsimp [q]
        split_ifs
        · exact hdD
        · exact hD.inv_mem hdD
      have hq0 : q ≠ 0 := fun e => hD.zero_notMem (e ▸ hqD)
      have hq1 : q < 1 := by
        dsimp [q]
        split_ifs with h
        · exact h
        · have h1d : 1 < d := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hd1)
          exact (inv_lt_one₀ (zero_lt_one.trans h1d)).mpr h1d
      have hqE : q ∉ E := by
        dsimp [q]
        split_ifs
        · exact hdE
        · intro hi
          exact hdE (by simpa [hd0] using hE.inv_mem hi)
      intro e heE
      have hqe : q ≤ e := by
        by_contra hn
        have heq : e ≤ q := le_of_not_ge hn
        exact hqE (hE.convex heE hE.one_mem heq hq1.le)
      have heqi : e ≤ q⁻¹ := by
        by_contra hn
        have hqie : q⁻¹ ≤ e := le_of_not_ge hn
        have hqiE : q⁻¹ ∈ E := hE.convex hE.one_mem heE
          (by exact (one_le_inv₀ (pos_iff_ne_zero.mpr hq0)).mpr hq1.le) hqie
        exact hqE (by simpa [hq0] using hE.inv_mem hqiE)
      exact hD.convex hqD (hD.inv_mem hqD) hqe heqi
  have hCcoarse : IsTCoarse C T := by
    intro Δ hΔ hΔT
    have hall : ∀ V : 𝒱, ∀ d ∈ Δ,
        C.mapOfLE V.1 (hCV V) d = 1 := by
      intro V
      let f := C.mapOfLE V.1 (hCV V)
      let K : Set C.ValueGroup := {d | f d = 1}
      have hK : IsConvexValueSubgroup C K := by
        constructor
        · exact f.map_one
        · intro a b ha hb
          change f (a * b) = 1
          rw [f.map_mul, ha, hb, one_mul]
        · intro a ha
          change f a⁻¹ = 1
          rw [map_inv₀, ha, inv_one]
        · intro hz
          change f 0 = 1 at hz
          rw [f.map_zero] at hz
          exact zero_ne_one hz
        · intro a b c ha hc hab hbc
          change f b = 1
          have hfab : f a ≤ f b := ValuationSubring.monotone_mapOfLE C V.1 (hCV V) hab
          have hfbc : f b ≤ f c := ValuationSubring.monotone_mapOfLE C V.1 (hCV V) hbc
          change f a = 1 at ha
          change f c = 1 at hc
          exact le_antisymm (hc ▸ hfbc) (ha ▸ hfab)
      rcases convexComparable Δ K hΔ hK with hΔK | hKΔ
      · exact fun d hd => hΔK hd
      · let E : Set V.1.ValueGroup := f '' Δ
        have hE : IsConvexValueSubgroup V.1 E := by
          constructor
          · exact ⟨1, hΔ.one_mem, f.map_one⟩
          · rintro a b ⟨da, hda, rfl⟩ ⟨db, hdb, rfl⟩
            exact ⟨da * db, hΔ.mul_mem hda hdb, f.map_mul da db⟩
          · rintro a ⟨da, hda, rfl⟩
            exact ⟨da⁻¹, hΔ.inv_mem hda, map_inv₀ f da⟩
          · rintro ⟨d, hd, hfd⟩
            obtain ⟨x, hx⟩ := C.valuation_surjective d
            have hx0 : x ≠ 0 := by
              intro ex
              apply hΔ.zero_notMem
              have hd0 : d = 0 := by rw [← hx, ex, C.valuation.map_zero]
              exact hd0 ▸ hd
            have hfx0 : f d ≠ 0 := by
              rw [← hx]
              change V.1.valuation x ≠ 0
              exact V.1.valuation.ne_zero_iff.mpr hx0
            exact hfx0 hfd
          · rintro a b c ⟨da, hda, rfl⟩ ⟨dc, hdc, rfl⟩ hab hbc
            obtain ⟨x, hx⟩ := C.valuation_surjective da
            obtain ⟨y, hy⟩ := V.1.valuation_surjective b
            obtain ⟨z, hz⟩ := C.valuation_surjective dc
            let e := C.valuation y
            have hfe : f e = b := by
              change V.1.valuation y = b
              exact hy
            refine ⟨e, ?_, hfe⟩
            have hxy : V.1.valuation x ≤ V.1.valuation y := by
              rw [← ValuationSubring.mapOfLE_valuation_apply C V.1 (hCV V) x,
                hx, hy]
              exact hab
            have hyz : V.1.valuation y ≤ V.1.valuation z := by
              rw [← ValuationSubring.mapOfLE_valuation_apply C V.1 (hCV V) z,
                hz, hy]
              exact hbc
            obtain ⟨r, hr⟩ := (V.1.valuation_le_iff x y).mp hxy
            obtain ⟨s, hs⟩ := (V.1.valuation_le_iff y z).mp hyz
            have lower : da ≤ e ∨ e ∈ Δ := by
              by_cases hrC : (r : F) ∈ C
              · left
                rw [← hx]
                exact (C.valuation_le_iff x y).mpr ⟨⟨r, hrC⟩, hr⟩
              · right
                have hriC : (r : F)⁻¹ ∈ C :=
                  (C.mem_or_inv_mem (r : F)).resolve_left hrC
                have hriV : (r : F)⁻¹ ∈ V.1 := hCV V hriC
                have hr0 : (r : F) ≠ 0 := by
                  intro er
                  have ex : x = 0 := by rw [← hr, er, zero_mul]
                  apply hΔ.zero_notMem
                  have hda0 : da = 0 := by rw [← hx, ex, C.valuation.map_zero]
                  exact hda0 ▸ hda
                have hrval : V.1.valuation (r : F) = 1 := by
                  apply le_antisymm (V.1.valuation_le_one r)
                  have hi := (V.1.valuation_le_one_iff ((r : F)⁻¹)).mpr hriV
                  rw [V.1.valuation.map_inv] at hi
                  exact (inv_le_one₀ (V.1.valuation.pos_iff.mpr hr0)).mp hi
                have hkr : C.valuation (r : F) ∈ K := by
                  change f (C.valuation (r : F)) = 1
                  rw [ValuationSubring.mapOfLE_valuation_apply, hrval]
                have hvaleq : da = C.valuation (r : F) * e := by
                  rw [← hx]
                  change C.valuation x = C.valuation (r : F) * C.valuation y
                  rw [← C.valuation.map_mul, hr]
                have hkr0 : C.valuation (r : F) ≠ 0 :=
                  C.valuation.ne_zero_iff.mpr hr0
                have heq : (C.valuation (r : F))⁻¹ * da = e := by
                  rw [hvaleq, ← mul_assoc, inv_mul_cancel₀ hkr0, one_mul]
                exact heq ▸ hΔ.mul_mem (hΔ.inv_mem (hKΔ hkr)) hda
            have upper : e ≤ dc ∨ e ∈ Δ := by
              by_cases hsC : (s : F) ∈ C
              · left
                rw [← hz]
                exact (C.valuation_le_iff y z).mpr ⟨⟨s, hsC⟩, hs⟩
              · right
                have hsiC : (s : F)⁻¹ ∈ C :=
                  (C.mem_or_inv_mem (s : F)).resolve_left hsC
                have hsiV : (s : F)⁻¹ ∈ V.1 := hCV V hsiC
                have hda0 : da ≠ 0 := fun ed => hΔ.zero_notMem (ed ▸ hda)
                have hfda0 : f da ≠ 0 := by
                  obtain ⟨w, hw⟩ := C.valuation_surjective da
                  rw [← hw, ValuationSubring.mapOfLE_valuation_apply]
                  exact V.1.valuation.ne_zero_iff.mpr (by
                    intro ew
                    apply hda0
                    rw [← hw, ew, C.valuation.map_zero])
                have hb0 : b ≠ 0 := by
                  intro eb
                  apply hfda0
                  apply le_antisymm
                  · rw [eb] at hab
                    exact hab
                  · exact bot_le
                have hy0 : y ≠ 0 := by
                  intro ey
                  apply hb0
                  rw [← hy, ey, V.1.valuation.map_zero]
                have hs0 : (s : F) ≠ 0 := by
                  intro es
                  apply hy0
                  rw [← hs, es, zero_mul]
                have hsval : V.1.valuation (s : F) = 1 := by
                  apply le_antisymm (V.1.valuation_le_one s)
                  have hi := (V.1.valuation_le_one_iff ((s : F)⁻¹)).mpr hsiV
                  rw [V.1.valuation.map_inv] at hi
                  exact (inv_le_one₀ (V.1.valuation.pos_iff.mpr hs0)).mp hi
                have hks : C.valuation (s : F) ∈ K := by
                  change f (C.valuation (s : F)) = 1
                  rw [ValuationSubring.mapOfLE_valuation_apply, hsval]
                have hvaleq : e = C.valuation (s : F) * dc := by
                  dsimp [e]
                  rw [← hz, ← C.valuation.map_mul, hs]
                exact hvaleq ▸ hΔ.mul_mem (hKΔ hks) hdc
            rcases lower with hle | he
            · rcases upper with heu | he
              · exact hΔ.convex hda hdc hle heu
              · exact he
            · exact he
        have hET : E ⊆ valueSet V.1 T := by
          rintro d ⟨c, hc, rfl⟩
          obtain ⟨t, ht, htc⟩ := hΔT hc
          refine ⟨t, ht, ?_⟩
          rw [← htc]
          exact ValuationSubring.mapOfLE_valuation_apply C V.1 (hCV V) t
        have hEtriv : E = {1} := V.2.2 E hE hET
        intro d hd
        have : f d ∈ E := ⟨d, hd, rfl⟩
        rw [hEtriv] at this
        exact this
    ext d
    constructor
    · intro hd
      obtain ⟨x, hx⟩ := C.valuation_surjective d
      have hxV : ∀ V : 𝒱, V.1.valuation x = 1 := by
        intro V
        rw [← ValuationSubring.mapOfLE_valuation_apply C V.1 (hCV V) x, hx]
        exact hall V d hd
      have hxC : x ∈ C := by
        change ∀ V : 𝒱, x ∈ V.1
        intro V
        exact (V.1.valuation_le_one_iff x).mp (hxV V).le
      have hxiC : x⁻¹ ∈ C := by
        change ∀ V : 𝒱, x⁻¹ ∈ V.1
        intro V
        rw [← V.1.valuation_le_one_iff, V.1.valuation.map_inv, hxV V]
        simp
      have hdx : d = 1 := by
        rw [← hx]
        apply le_antisymm ((C.valuation_le_one_iff x).mpr hxC)
        have hi := (C.valuation_le_one_iff x⁻¹).mpr hxiC
        rw [C.valuation.map_inv] at hi
        by_cases hx0 : x = 0
        · have : d = 0 := by rw [← hx, hx0, C.valuation.map_zero]
          exact False.elim (hΔ.zero_notMem (this ▸ hd))
        · exact (inv_le_one₀ (C.valuation.pos_iff.mpr hx0)).mp hi
      simpa [hdx]
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      exact hΔ.one_mem
  have hCsmall : ∀ B : ValuationSubring F,
      ValuationSubring.IsCompatible B T → IsTCoarse B T → C ≤ B := by
    intro B hB hBc
    exact hCV ⟨B, hB, hBc⟩
  refine ⟨C, ⟨hCcompat, hCcoarse, hCsmall⟩, ?_⟩
  intro D hD
  exact le_antisymm (hD.2.2 C hCcompat hCcoarse)
    (hCsmall D hD.1 hD.2.1)

/-- The valuation ring `O_F(T)` supplied by AEJ, Theorem 3.8, journal p. 461. -/
noncomputable def OF (T : Set F) (hT : IsMulSubgroup T) : ValuationSubring F :=
  Classical.choose (ExistsUnique.exists (theorem_3_8 T hT))

/-- The ring `O_F(T)` is `T`-compatible, by AEJ, Theorem 3.8, journal p. 461. -/
theorem OF_isCompatible (T : Set F) (hT : IsMulSubgroup T) :
    ValuationSubring.IsCompatible (OF T hT) T := by
  exact (Classical.choose_spec
    (ExistsUnique.exists (theorem_3_8 T hT))).1

/-- The ring `O_F(T)` is `T`-coarse, by AEJ, Theorem 3.8, journal p. 461. -/
theorem OF_isTCoarse (T : Set F) (hT : IsMulSubgroup T) :
    IsTCoarse (OF T hT) T := by
  exact (Classical.choose_spec
    (ExistsUnique.exists (theorem_3_8 T hT))).2.1

/-- The ring `O_F(T)` lies in every `T`-coarse, `T`-compatible valuation
ring, by the minimality clause of AEJ, Theorem 3.8, journal p. 461. -/
theorem OF_le (T : Set F) (hT : IsMulSubgroup T) (A : ValuationSubring F)
    (hcompat : ValuationSubring.IsCompatible A T) (hcoarse : IsTCoarse A T) :
    OF T hT ≤ A := by
  exact (Classical.choose_spec
    (ExistsUnique.exists (theorem_3_8 T hT))).2.2 A hcompat hcoarse

/-- Any smallest `T`-coarse, `T`-compatible valuation ring equals `O_F(T)`;
this is the uniqueness clause of AEJ, Theorem 3.8, journal p. 461. -/
theorem OF_eq_of_smallest (T : Set F) (hT : IsMulSubgroup T)
    (A : ValuationSubring F) (hcompat : ValuationSubring.IsCompatible A T)
    (hcoarse : IsTCoarse A T)
    (hsmallest : ∀ B : ValuationSubring F,
      ValuationSubring.IsCompatible B T → IsTCoarse B T → A ≤ B) :
    A = OF T hT := by
  apply le_antisymm
  · exact hsmallest _ (OF_isCompatible T hT) (OF_isTCoarse T hT)
  · exact OF_le T hT A hcompat hcoarse

end

end NU.AEJ
