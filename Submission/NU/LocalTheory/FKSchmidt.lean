import Mathlib

open scoped Polynomial
open Polynomial

namespace NU.LocalTheory.FKSchmidt

noncomputable section

abbrev RealValue := WithTop ℝ
abbrev RealValuation (K : Type*) [Ring K] := AddValuation K RealValue

/-- The finite real value of an element, with `0` used only at the top value. -/
def order {K : Type*} [Ring K] (v : RealValuation K) (x : K) : ℝ :=
  (v x).untopD 0

lemma coe_order_of_ne {K : Type*} [Field K] (v : RealValuation K) {x : K}
    (hx : x ≠ 0) : (order v x : RealValue) = v x := by
  have htop : v x ≠ (⊤ : RealValue) := (AddValuation.ne_top_iff v).2 hx
  refine WithTop.recTopCoe
    (C := fun y => y ≠ (⊤ : RealValue) → ((y.untopD 0 : ℝ) : RealValue) = y)
    ?_ ?_ (v x) htop
  · intro h
    exact (h rfl).elim
  · intro a _
    rfl

/-- Indices of nonzero coefficients strictly below the leading degree. -/
def lowerSupport {K : Type*} [Semiring K] (f : K[X]) : Finset ℕ := by
  classical
  exact (Finset.range f.natDegree).filter fun i => f.coeff i ≠ 0

/-- The slope contributed by a lower nonzero coefficient.  It is only read on
`lowerSupport`; its value at zero coefficients is immaterial. -/
def coefficientSlope {K : Type*} [Field K] (v : RealValuation K)
    (f : K[X]) (i : ℕ) : ℝ :=
  -order v (f.coeff i) / (f.natDegree - i : ℝ)

/-- The inner maximum in the root bound, implemented by `Finset.max'`; it is
`0` when the nonzero lower support is empty. -/
def coefficientMax {K : Type*} [Field K] (v : RealValuation K)
    (f : K[X]) : ℝ :=
  if h : (lowerSupport f).Nonempty then
    ((lowerSupport f).image (coefficientSlope v f)).max' (h.image _)
  else 0

/-- The explicit coefficient root-bound constant from the blueprint. -/
def M_f {K : Type*} [Field K] (v : RealValuation K) (f : K[X]) : ℝ :=
  max 0 (coefficientMax v f)

lemma M_f_nonneg {K : Type*} [Field K] (v : RealValuation K) (f : K[X]) :
    0 ≤ M_f v f := by
  exact le_max_left _ _

lemma coefficientSlope_le_M_f {K : Type*} [Field K]
    (v : RealValuation K) (f : K[X]) {i : ℕ}
    (hi : i < f.natDegree) (hci : f.coeff i ≠ 0) :
    coefficientSlope v f i ≤ M_f v f := by
  have his : i ∈ lowerSupport f := by
    simp [lowerSupport, hi, hci]
  have hne : (lowerSupport f).Nonempty := ⟨i, his⟩
  have himage : coefficientSlope v f i ∈
      (lowerSupport f).image (coefficientSlope v f) :=
    Finset.mem_image.mpr ⟨i, his, rfl⟩
  rw [M_f, coefficientMax, dif_pos hne]
  exact (Finset.le_max' _ _ himage).trans (le_max_right _ _)

lemma coefficient_bound {K : Type*} [Field K]
    (v : RealValuation K) (f : K[X]) {i : ℕ}
    (hi : i < f.natDegree) :
    ((-((f.natDegree - i : ℕ) : ℝ) * M_f v f : ℝ) : RealValue) ≤
      v (f.coeff i) := by
  by_cases hci : f.coeff i = 0
  · simp [hci]
  have hs := coefficientSlope_le_M_f v f hi hci
  have hpos : (0 : ℝ) < (f.natDegree - i : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hi
  have hfinite := coe_order_of_ne v hci
  rw [← hfinite, WithTop.coe_le_coe]
  dsimp [coefficientSlope] at hs
  rw [← Nat.cast_sub hi.le] at hs
  have hs' := (div_le_iff₀ hpos).mp hs
  nlinarith

/-- A valuation on an extension agrees exactly with the base valuation. -/
def Extends {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) (v : RealValuation K) (w : RealValuation L) : Prop :=
  w.comap ι = v

lemma Extends.apply {K L : Type*} [Field K] [Field L]
    {ι : K →+* L} {v : RealValuation K} {w : RealValuation L}
    (h : Extends ι v w) (x : K) : w (ι x) = v x := by
  exact DFunLike.congr_fun h x

lemma valuation_sum_gt {K : Type*} [Field K] (v : RealValuation K)
    {ι : Type*} {s : Finset ι} {z : ι → K} {A : ℝ}
    (hz : ∀ i ∈ s, (A : RealValue) < v (z i)) :
    (A : RealValue) < v (∑ i ∈ s, z i) := by
  exact v.map_lt_sum (by simp) hz

lemma valuation_prod {K : Type*} [Field K] (v : RealValuation K)
    {ι : Type*} (s : Finset ι) (z : ι → K) :
    v (∏ i ∈ s, z i) = ∑ i ∈ s, v (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, AddValuation.map_mul]

lemma lower_term_gt {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) (v : RealValuation K) (w : RealValuation L)
    (hext : Extends ι v w) (f : K[X]) {b : L}
    {i : ℕ} (hi : i < f.natDegree)
    (hb : w b < ((-M_f v f : ℝ) : RealValue)) :
    f.natDegree • w b < w (ι (f.coeff i) * b ^ i) := by
  have hbtop : w b ≠ ⊤ := ne_of_lt (hb.trans_le le_top)
  have hbcoe : ((order w b : ℝ) : RealValue) = w b := by
    have hb0 : b ≠ 0 := (AddValuation.ne_top_iff w).mp hbtop
    exact coe_order_of_ne w hb0
  have hbR : order w b < -M_f v f := by
    rw [← hbcoe, WithTop.coe_lt_coe] at hb
    exact hb
  have hcoeff := coefficient_bound v f hi
  rw [← hext.apply (f.coeff i)] at hcoeff
  calc
    f.natDegree • w b = (((f.natDegree : ℝ) * order w b : ℝ) : RealValue) := by
      rw [← hbcoe, ← WithTop.coe_nsmul]
      norm_num [nsmul_eq_mul]
    _ < (((-((f.natDegree - i : ℕ) : ℝ) * M_f v f) +
          (i : ℝ) * order w b : ℝ) : RealValue) := by
      rw [WithTop.coe_lt_coe]
      have hiR : (i : ℝ) < f.natDegree := by exact_mod_cast hi
      have hM := M_f_nonneg v f
      rw [Nat.cast_sub hi.le]
      nlinarith
    _ ≤ w (ι (f.coeff i)) + i • w b := by
      rw [WithTop.coe_add]
      apply add_le_add
      · exact hcoeff
      · rw [← hbcoe, ← WithTop.coe_nsmul]
        norm_num [nsmul_eq_mul]
    _ = w (ι (f.coeff i) * b ^ i) := by simp

/-- **Root bound.** A root of a monic polynomial has value at least `-M_f`. -/
theorem root_bound {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) (v : RealValuation K) (w : RealValuation L)
    (hext : Extends ι v w) (f : K[X]) (hf : f.Monic) {b : L}
    (hbroot : f.eval₂ ι b = 0) :
    ((-M_f v f : ℝ) : RealValue) ≤ w b := by
  by_contra hbound
  have hb : w b < ((-M_f v f : ℝ) : RealValue) := lt_of_not_ge hbound
  let n := f.natDegree
  have hncoe : n • w b = (((n : ℝ) * order w b : ℝ) : RealValue) := by
    have hb0 : b ≠ 0 := by
      apply (AddValuation.ne_top_iff w).mp
      exact ne_of_lt (hb.trans_le le_top)
    rw [← coe_order_of_ne w hb0, ← WithTop.coe_nsmul]
    norm_num [nsmul_eq_mul]
  have hlower : n • w b <
      w (∑ i ∈ Finset.range n, ι (f.coeff i) * b ^ i) := by
    rw [hncoe]
    apply valuation_sum_gt w
    intro i hi
    simpa [n, hncoe] using
      (lower_term_gt ι v w hext f (Finset.mem_range.mp hi) hb)
  have hlead : w (b ^ n) = n • w b := by simp
  have heval : f.eval₂ ι b = b ^ n +
      ∑ i ∈ Finset.range n, ι (f.coeff i) * b ^ i := by
    rw [Polynomial.eval₂_eq_sum_range]
    rw [Finset.sum_range_succ, hf.coeff_natDegree]
    simp [n, add_comm]
  have hval : w (f.eval₂ ι b) = n • w b := by
    rw [heval, ← hlead]
    exact w.map_add_eq_of_lt_left (by simpa [hlead] using hlower)
  rw [hbroot, AddValuation.map_zero] at hval
  have hfinite : n • w b ≠ ⊤ := by
    rw [hncoe]
    exact WithTop.coe_ne_top
  exact hfinite hval.symm

/-- The coefficientwise valuation of `g - f` below degree `n`.  The value at
`n = 0` is `⊤`; all applications have positive degree. -/
def polynomialDistance {K : Type*} [Field K] (v : RealValuation K)
    (n : ℕ) (f g : K[X]) : RealValue :=
  if hn : n ≠ 0 then
    (Finset.range n).inf' ((Finset.nonempty_range_iff).2 hn)
      fun i => v ((g - f).coeff i)
  else ⊤

lemma polynomialDistance_le_coefficient {K : Type*} [Field K]
    (v : RealValuation K) {n : ℕ} (hn : n ≠ 0) (f g : K[X])
    {i : ℕ} (hi : i < n) :
    polynomialDistance v n f g ≤ v ((g - f).coeff i) := by
  rw [polynomialDistance, dif_pos hn]
  exact Finset.inf'_le _ (Finset.mem_range.mpr hi)

/-- The repaired threshold `max {-M, nT + (n-1)M}`, with `M = M_f + 1`. -/
def proximityDelta {K : Type*} [Field K] (v : RealValuation K)
    (f : K[X]) (n : ℕ) (T : ℝ) : ℝ :=
  let M := M_f v f + 1
  max (-M) ((n : ℝ) * T + (n - 1 : ℕ) * M)

lemma M_f_le_of_coefficients {K : Type*} [Field K]
    (v : RealValuation K) (f : K[X]) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ i < f.natDegree,
      ((-((f.natDegree - i : ℕ) : ℝ) * C : ℝ) : RealValue) ≤
        v (f.coeff i)) :
    M_f v f ≤ C := by
  classical
  have hslope : ∀ i ∈ lowerSupport f, coefficientSlope v f i ≤ C := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hirange : i < f.natDegree := Finset.mem_range.mp hi'.1
    have hci : f.coeff i ≠ 0 := hi'.2
    have hbound := hc i hirange
    rw [← coe_order_of_ne v hci, WithTop.coe_le_coe] at hbound
    have hpos : (0 : ℝ) < (f.natDegree - i : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt hirange
    rw [coefficientSlope, ← Nat.cast_sub hirange.le]
    apply (div_le_iff₀ hpos).2
    nlinarith
  rw [M_f, max_le_iff]
  refine ⟨hC, ?_⟩
  rw [coefficientMax]
  split_ifs with hne
  · apply Finset.max'_le
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hslope i hi
  · exact hC

lemma perturbed_M_f_le {K : Type*} [Field K]
    (v : RealValuation K) (f g : K[X]) (hf : f.Monic) (hg : g.Monic)
    (hdegree : g.natDegree = f.natDegree) (hn : f.natDegree ≠ 0)
    (T : ℝ)
    (hclose : ((proximityDelta v f f.natDegree T : ℝ) : RealValue) ≤
      polynomialDistance v f.natDegree f g) :
    M_f v g ≤ M_f v f + 1 := by
  let M := M_f v f + 1
  let δ := proximityDelta v f f.natDegree T
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [M_f_nonneg v f]
  have hδ : -M ≤ δ := by
    exact le_max_left _ _
  apply M_f_le_of_coefficients v g M (le_trans (by norm_num) hM)
  intro i hi
  have hi' : i < f.natDegree := by simpa [hdegree] using hi
  have hmone : 1 ≤ (f.natDegree - i : ℕ) := Nat.one_le_iff_ne_zero.mpr
    (Nat.sub_ne_zero_iff_lt.mpr hi')
  have hqδ : ((δ : ℝ) : RealValue) ≤ v ((g - f).coeff i) :=
    hclose.trans (polynomialDistance_le_coefficient v hn f g hi')
  have hq :
      ((-((f.natDegree - i : ℕ) : ℝ) * M : ℝ) : RealValue) ≤
        v ((g - f).coeff i) := by
    apply le_trans (b := ((δ : ℝ) : RealValue))
    · rw [WithTop.coe_le_coe]
      have hM0 : 0 ≤ M := le_trans (by norm_num) hM
      exact le_trans (by
        have hmoneR : (1 : ℝ) ≤ (f.natDegree - i : ℕ) := by exact_mod_cast hmone
        nlinarith) hδ
    · exact hqδ
  have hfcoeff :
      ((-((f.natDegree - i : ℕ) : ℝ) * M : ℝ) : RealValue) ≤
        v (f.coeff i) := by
    refine le_trans ?_ (coefficient_bound v f hi')
    rw [WithTop.coe_le_coe]
    have hsub : M_f v f ≤ M := by simp [M]
    have hm0 : (0 : ℝ) ≤ (f.natDegree - i : ℕ) := by positivity
    nlinarith
  rw [hdegree]
  have hcoeffeq : g.coeff i = (g - f).coeff i + f.coeff i := by
    simp
  rw [hcoeffeq]
  exact v.map_le_add hq hfcoeff

/-- **Root proximity.** The threshold is exactly the repaired formula from
Version 2 of the blueprint. -/
theorem root_proximity {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) (v : RealValuation K) (w : RealValuation L)
    (hext : Extends ι v w) (f g : K[X]) (hf : f.Monic) (hg : g.Monic)
    (hdegree : g.natDegree = f.natDegree) (hn : f.natDegree ≠ 0)
    (a : Fin f.natDegree → L)
    (hfactor : f.map ι = ∏ j : Fin f.natDegree, (X - C (a j)))
    {b : L} (hbroot : g.eval₂ ι b = 0) (T : ℝ)
    (hclose : ((proximityDelta v f f.natDegree T : ℝ) : RealValue) ≤
      polynomialDistance v f.natDegree f g) :
    ∃ i : Fin f.natDegree, ((T : ℝ) : RealValue) ≤ w (b - a i) := by
  let n := f.natDegree
  let M := M_f v f + 1
  let δ := proximityDelta v f n T
  have hn' : n ≠ 0 := by simpa [n] using hn
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [M_f_nonneg v f]
  have hMg : M_f v g ≤ M := by
    simpa [n, M, δ] using
      perturbed_M_f_le v f g hf hg hdegree hn T hclose
  have hbM : ((-M : ℝ) : RealValue) ≤ w b := by
    refine le_trans ?_ (root_bound ι v w hext g hg hbroot)
    rw [WithTop.coe_le_coe]
    linarith
  have hqdeg : (f - g).natDegree < n := by
    apply Polynomial.IsMonicOfDegree.natDegree_sub_lt hn'
    · rw [Polynomial.isMonicOfDegree_iff]
      exact ⟨by simp [n], by simpa [n] using hf.coeff_natDegree⟩
    · rw [Polynomial.isMonicOfDegree_iff]
      exact ⟨by simp [n, hdegree], by simpa [n, hdegree] using hg.coeff_natDegree⟩
  have hδcoeff : ∀ i < n,
      ((δ : ℝ) : RealValue) ≤ w (ι ((f - g).coeff i)) := by
    intro i hi
    rw [hext.apply]
    have hd := hclose.trans
      (polynomialDistance_le_coefficient v hn' f g hi)
    have heq : (f - g).coeff i = -((g - f).coeff i) := by simp
    rw [heq, AddValuation.map_neg]
    simpa [δ, n] using hd
  have hevalLower :
      (((δ - ((n - 1 : ℕ) : ℝ) * M : ℝ)) : RealValue) ≤
        w ((f - g).eval₂ ι b) := by
    rw [Polynomial.eval₂_eq_sum_range' ι hqdeg b]
    apply w.map_le_sum
    intro i hi
    have hiN := Finset.mem_range.mp hi
    rw [AddValuation.map_mul, AddValuation.map_pow]
    have hci := hδcoeff i hiN
    have hbi :
        (((-(i : ℝ) * M : ℝ)) : RealValue) ≤ i • w b := by
      have := nsmul_le_nsmul_right hbM i
      rw [← WithTop.coe_nsmul] at this
      simpa [nsmul_eq_mul] using this
    refine le_trans ?_ (add_le_add hci hbi)
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    have hiLe : (i : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast Nat.le_sub_one_of_lt hiN
    have hM0 : 0 ≤ M := le_trans (by norm_num) hM
    nlinarith
  have hevalEq : (f - g).eval₂ ι b = f.eval₂ ι b := by
    rw [Polynomial.eval₂_sub, hbroot, sub_zero]
  rw [hevalEq] at hevalLower
  have hdeltaMain : (n : ℝ) * T + ((n - 1 : ℕ) : ℝ) * M ≤ δ := by
    exact le_max_right _ _
  have hevalFactor : f.eval₂ ι b = ∏ j : Fin n, (b - a j) := by
    rw [← Polynomial.eval_map, hfactor, Polynomial.eval_prod]
    simp [n]
  rw [hevalFactor] at hevalLower
  have hproduct : (((n : ℝ) * T : ℝ) : RealValue) ≤
      w (∏ j : Fin n, (b - a j)) := by
    refine le_trans ?_ hevalLower
    rw [WithTop.coe_le_coe]
    linarith
  by_contra hnone
  push Not at hnone
  have hreal : ∀ j : Fin n, order w (b - a j) < T := by
    intro j
    have hjtop : w (b - a j) ≠ (⊤ : RealValue) :=
      ne_of_lt ((hnone j).trans_le le_top)
    have hj0 : b - a j ≠ 0 := (AddValuation.ne_top_iff w).mp hjtop
    have hj : w (b - a j) < ((T : ℝ) : RealValue) := by
      simpa [n] using hnone j
    rw [← coe_order_of_ne w hj0, WithTop.coe_lt_coe] at hj
    exact hj
  letI : Nonempty (Fin n) := (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn'))
  have hsumReal : (∑ j : Fin n, order w (b - a j)) <
      ∑ _j : Fin n, T := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro j _
    exact hreal j
  have hsumlt :
      (((∑ j : Fin n, order w (b - a j)) : ℝ) : RealValue) <
        (((n : ℝ) * T : ℝ) : RealValue) := by
    rw [WithTop.coe_lt_coe]
    simpa [Finset.sum_const, nsmul_eq_mul] using hsumReal
  have hprodVal : w (∏ j : Fin n, (b - a j)) =
      (((∑ j : Fin n, order w (b - a j)) : ℝ) : RealValue) := by
    rw [valuation_prod w Finset.univ]
    calc
      (∑ j : Fin n, w (b - a j)) =
          ∑ j : Fin n, ((order w (b - a j) : ℝ) : RealValue) := by
        apply Finset.sum_congr rfl
        intro j _
        have hjlt : w (b - a j) < ((T : ℝ) : RealValue) := by
          simpa [n] using hnone j
        have hjtop : w (b - a j) ≠ (⊤ : RealValue) :=
          ne_of_lt (hjlt.trans_le le_top)
        have hj0 : b - a j ≠ 0 := (AddValuation.ne_top_iff w).mp hjtop
        exact (coe_order_of_ne w hj0).symm
      _ = (((∑ j : Fin n, order w (b - a j)) : ℝ) : RealValue) :=
        WithTop.coe_sum _ _ |>.symm
  rw [hprodVal] at hproduct
  exact (not_lt_of_ge hproduct) hsumlt

/-! ## Unique prolongation and Krasner's lemma -/

universe u

/-- Henselianity in the working, unique-prolongation sense: every algebraic
field extension in the universe carries exactly one extension of `v` with
the fixed real normalization. -/
def IsHenselian {F : Type u} [Field F] (v : RealValuation F) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra F E], Algebra.IsAlgebraic F E →
    ∃! w : RealValuation E, Extends (algebraMap F E) v w

/-- The valuation-subring formulation used verbatim by the downstream bare
recovery module. -/
def IsHenselianValuationIn
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring F) : Prop :=
  ∀ E : IntermediateField F Ω,
    ∃! B : ValuationSubring E,
      B.comap (algebraMap F E) = A

lemma IsHenselian.unique_extension {F E : Type u} [Field F] [Field E]
    [Algebra F E] (v : RealValuation F) (h : IsHenselian v)
    (halg : Algebra.IsAlgebraic F E) {w₁ w₂ : RealValuation E}
    (hw₁ : Extends (algebraMap F E) v w₁)
    (hw₂ : Extends (algebraMap F E) v w₂) : w₁ = w₂ :=
  (h E halg).unique hw₁ hw₂

/-- Pulling an extension back by a base-field automorphism still extends the
same normalized base valuation. -/
lemma conjugate_extends {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    (v : RealValuation F) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) (σ : Ω ≃ₐ[F] Ω) :
    Extends (algebraMap F Ω) v
      (w.comap σ.toRingEquiv.toRingHom) := by
  apply AddValuation.ext
  intro x
  change w (σ (algebraMap F Ω x)) = v x
  rw [σ.commutes]
  exact hext.apply x

/-- Unique prolongation makes the chosen extension invariant under every
base-field automorphism. -/
lemma IsHenselian.extension_aut_invariant
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω]
    (v : RealValuation F) (h : IsHenselian v) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    w (σ x) = w x := by
  have heq : w.comap σ.toRingEquiv.toRingHom = w :=
    h.unique_extension v inferInstance (conjugate_extends v w hext σ) hext
  exact DFunLike.congr_fun heq x

/-- The radius-free form of Krasner separation.  It says that `b` is closer
to `a` than `a` is to every distinct conjugate. -/
def KrasnerSeparated (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (w : RealValuation Ω) (a b : Ω) : Prop :=
  ∀ σ : Ω ≃ₐ[F] Ω, σ a ≠ a → w (a - σ a) < w (b - a)

/-- The automorphism-fixing core of Krasner's lemma. -/
lemma krasner_fixed {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω]
    (v : RealValuation F) (hv : IsHenselian v) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) {a b : Ω}
    (hclose : KrasnerSeparated F w a b) (σ : Ω ≃ₐ[F] Ω)
    (hσb : σ b = b) : σ a = a := by
  by_contra hσa
  have hab : w (a - b) = w (b - a) := w.map_sub_swap _ _
  have hσab : w (σ (a - b)) = w (a - b) :=
    hv.extension_aut_invariant v w hext σ (a - b)
  have hbσa : w (b - σ a) = w (b - a) := by
    calc
      w (b - σ a) = w (σ a - b) := w.map_sub_swap _ _
      _ = w (σ (a - b)) := by
        congr 1
        simp [hσb]
      _ = w (a - b) := hσab
      _ = w (b - a) := hab
  have hle : w (b - a) ≤ w (a - σ a) := by
    have hadd := w.map_le_add (x := a - b) (y := b - σ a)
      (show w (b - a) ≤ w (a - b) from hab.ge)
      (show w (b - a) ≤ w (b - σ a) from hbσa.ge)
    simpa only [sub_add_sub_cancel] using hadd
  exact (not_lt_of_ge hle) (hclose σ hσa)

/-- Krasner's lemma in fixed-field form. -/
theorem krasner_separated {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsGalois F Ω]
    (v : RealValuation F) (hv : IsHenselian v) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) {a b : Ω}
    (hclose : KrasnerSeparated F w a b) :
    IntermediateField.adjoin F {a} ≤ IntermediateField.adjoin F {b} := by
  rw [IntermediateField.adjoin_simple_le_iff]
  let E : IntermediateField F Ω := IntermediateField.adjoin F {b}
  have haFixed : a ∈ IntermediateField.fixedField E.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    apply krasner_fixed v hv w hext hclose σ
    exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ b
      (IntermediateField.subset_adjoin F {b} (Set.mem_singleton b))
  rw [InfiniteGalois.fixedField_fixingSubgroup E] at haFixed
  exact haFixed

/-- A finite Krasner radius, with the certified empty convention
`max ∅ = -∞`.  The supplied set is the set of conjugates other than `a`. -/
def krasnerRadius {Ω : Type*} [Field Ω] (w : RealValuation Ω)
    (a : Ω) (s : Finset Ω) : WithBot ℝ := by
  classical
  exact if hs : s.Nonempty then
    (((s.image (fun x : Ω => order w (a - x))).max' (hs.image _)) : ℝ)
  else ⊥

lemma le_krasnerRadius {Ω : Type*} [Field Ω] (w : RealValuation Ω)
    (a : Ω) (s : Finset Ω) {x : Ω} (hx : x ∈ s) :
    ((order w (a - x) : ℝ) : WithBot ℝ) ≤ krasnerRadius w a s := by
  classical
  have hs : s.Nonempty := ⟨x, hx⟩
  rw [krasnerRadius, dif_pos hs, WithBot.coe_le_coe]
  exact Finset.le_max'
    (s.image (fun y : Ω => order w (a - y))) (order w (a - x))
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- **Krasner.** The finite-radius statement, including the empty-radius
case.  `s` contains every distinct `F`-conjugate of `a`; hence
`R(a) < v(b-a)` forces `F(a) ⊆ F(b)`. -/
theorem krasner {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsGalois F Ω]
    (v : RealValuation F) (hv : IsHenselian v) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) (a b : Ω) (s : Finset Ω)
    (hs : ∀ x ∈ s, x ≠ a)
    (hconj : ∀ σ : Ω ≃ₐ[F] Ω, σ a ≠ a → σ a ∈ s)
    (hclose : krasnerRadius w a s <
      ((order w (b - a) : ℝ) : WithBot ℝ)) :
    IntermediateField.adjoin F {a} ≤ IntermediateField.adjoin F {b} := by
  classical
  by_cases hba : b = a
  · subst b
    exact le_rfl
  apply krasner_separated v hv w hext
  intro σ hσ
  have hmem := hconj σ hσ
  have hrad := le_krasnerRadius w a s hmem
  have hord : order w (a - σ a) < order w (b - a) := by
    exact_mod_cast hrad.trans_lt hclose
  have hleft : a - σ a ≠ 0 := sub_ne_zero.mpr hσ.symm
  have hright : b - a ≠ 0 := sub_ne_zero.mpr hba
  rw [← coe_order_of_ne w hleft, ← coe_order_of_ne w hright,
    WithTop.coe_lt_coe]
  exact hord

/-! ## Approximation for two rank-one valuations -/

/-- The valuation subring associated to a real additive valuation. -/
def realValuationSubring {K : Type*} [Field K]
    (v : RealValuation K) : ValuationSubring K :=
  (AddValuation.toValuation v).valuationSubring

@[simp] lemma mem_realValuationSubring {K : Type*} [Field K]
    (v : RealValuation K) (x : K) :
    x ∈ realValuationSubring v ↔ (0 : RealValue) ≤ v x :=
  Iff.rfl

/-- Independence in the exact valuation-subring order used by the consumer. -/
def IndependentValuationSubrings {F : Type*} [Field F]
    (A B : ValuationSubring F) : Prop :=
  ∀ C : ValuationSubring F, A ≤ C → B ≤ C → C = ⊤

/-- Rank one in the coarsening form used by `BareRecovery`. -/
def IsRankOneValuationSubring {F : Type*} [Field F]
    (A : ValuationSubring F) : Prop :=
  A ≠ ⊤ ∧
    ∀ C : ValuationSubring F, A ≤ C → C = A ∨ C = ⊤

/-- Inequivalent nontrivial rank-one valuation rings are incomparable. -/
theorem rank_one_incomparable {F : Type*} [Field F]
    {A B : ValuationSubring F}
    (hA : IsRankOneValuationSubring A)
    (hB : IsRankOneValuationSubring B) (hne : A ≠ B) :
    ¬ A ≤ B ∧ ¬ B ≤ A := by
  constructor
  · intro hAB
    rcases hA.2 B hAB with hBA | hBtop
    · exact hne hBA.symm
    · exact hB.1 hBtop
  · intro hBA
    rcases hB.2 A hBA with hAB | hAtop
    · exact hne hAB
    · exact hA.1 hAtop

lemma order_inv_of_ne {F : Type*} [Field F] (v : RealValuation F)
    {x : F} (hx : x ≠ 0) : order v x⁻¹ = -order v x := by
  have hmul := v.map_mul x⁻¹ x
  rw [inv_mul_cancel₀ hx, AddValuation.map_one,
    ← coe_order_of_ne v (inv_ne_zero hx), ← coe_order_of_ne v hx,
    ← WithTop.coe_add] at hmul
  have hreal : order v x⁻¹ + order v x = 0 := by
    exact_mod_cast hmul.symm
  linarith

lemma order_div_of_ne {F : Type*} [Field F] (v : RealValuation F)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    order v (x / y) = order v x - order v y := by
  have hdiv : x / y ≠ 0 := div_ne_zero hx hy
  have hmul := v.map_mul (x / y) y
  rw [div_mul_cancel₀ x hy, ← coe_order_of_ne v hdiv,
    ← coe_order_of_ne v hy, ← coe_order_of_ne v hx,
    ← WithTop.coe_add] at hmul
  have hreal : order v (x / y) + order v y = order v x := by
    exact_mod_cast hmul.symm
  linarith

/-- The same incomparability supplies elements with the two opposite sign
patterns needed in Step 1 of approximation. -/
lemma exists_switch_elements {F : Type*} [Field F]
    (v₁ v₂ : RealValuation F)
    (h₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (h₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂) :
    ∃ u u' : F, u ≠ 0 ∧ u' ≠ 0 ∧
      0 < order v₁ u ∧ order v₂ u ≤ 0 ∧
      0 < order v₂ u' ∧ order v₁ u' ≤ 0 := by
  have hinc := rank_one_incomparable h₁ h₂ hne
  obtain ⟨x, hx₂, hx₁⟩ := SetLike.not_le_iff_exists.mp hinc.2
  obtain ⟨y, hy₁, hy₂⟩ := SetLike.not_le_iff_exists.mp hinc.1
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    exact hx₁ (realValuationSubring v₁).zero_mem
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    exact hy₂ (realValuationSubring v₂).zero_mem
  refine ⟨x⁻¹, y⁻¹, inv_ne_zero hx0, inv_ne_zero hy0, ?_, ?_, ?_, ?_⟩
  · have hxneg : v₁ x < (0 : RealValue) := lt_of_not_ge hx₁
    have hxord : order v₁ x < 0 := by
      rw [← coe_order_of_ne v₁ hx0] at hxneg
      exact_mod_cast hxneg
    rw [order_inv_of_ne v₁ hx0]
    linarith
  · have hxnonneg : (0 : RealValue) ≤ v₂ x := hx₂
    have hxord : 0 ≤ order v₂ x := by
      rw [← coe_order_of_ne v₂ hx0] at hxnonneg
      exact_mod_cast hxnonneg
    rw [order_inv_of_ne v₂ hx0]
    linarith
  · have hyneg : v₂ y < (0 : RealValue) := lt_of_not_ge hy₂
    have hyord : order v₂ y < 0 := by
      rw [← coe_order_of_ne v₂ hy0] at hyneg
      exact_mod_cast hyneg
    rw [order_inv_of_ne v₂ hy0]
    linarith
  · have hynonneg : (0 : RealValue) ≤ v₁ y := hy₁
    have hyord : 0 ≤ order v₁ y := by
      rw [← coe_order_of_ne v₁ hy0] at hynonneg
      exact_mod_cast hynonneg
    rw [order_inv_of_ne v₁ hy0]
    linarith

/-- Step 2: the certified idempotent orientation
`e = w^k / (1 + w^k)`. -/
lemma exists_approximation_idempotent {F : Type*} [Field F]
    (v₁ v₂ : RealValuation F)
    (h₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (h₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (T₁ T₂ : ℝ) :
    ∃ e : F, ((T₁ : ℝ) : RealValue) ≤ v₁ (e - 1) ∧
      ((T₂ : ℝ) : RealValue) ≤ v₂ e := by
  obtain ⟨u, u', hu0, hu'0, hu₁, hu₂, hu'₂, hu'₁⟩ :=
    exists_switch_elements v₁ v₂ h₁ h₂ hne
  let w : F := u' / u
  have hw0 : w ≠ 0 := div_ne_zero hu'0 hu0
  let α : ℝ := order v₁ w
  let β : ℝ := order v₂ w
  have hαeq : α = order v₁ u' - order v₁ u := by
    exact order_div_of_ne v₁ hu'0 hu0
  have hβeq : β = order v₂ u' - order v₂ u := by
    exact order_div_of_ne v₂ hu'0 hu0
  have hα : α < 0 := by linarith
  have hβ : 0 < β := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max 0 (max ((T₁ + 1) / (-α)) ((T₂ + 1) / β)))
  have hk0 : 0 < k := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left 0 _) hk)
  have hk₁ : T₁ ≤ -(k : ℝ) * α := by
    have hratio : (T₁ + 1) / (-α) < k :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_right 0 _) hk)
    have hposa : 0 < -α := by linarith
    have := (div_lt_iff₀ hposa).mp hratio
    nlinarith
  have hk₂ : T₂ ≤ (k : ℝ) * β := by
    have hratio : (T₂ + 1) / β < k :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_right 0 _) hk)
    have := (div_lt_iff₀ hβ).mp hratio
    nlinarith
  have hwk0 : w ^ k ≠ 0 := pow_ne_zero _ hw0
  have hv₁wk : v₁ (w ^ k) = (((k : ℝ) * α : ℝ) : RealValue) := by
    rw [AddValuation.map_pow, ← coe_order_of_ne v₁ hw0,
      ← WithTop.coe_nsmul]
    simp [α, nsmul_eq_mul]
  have hv₂wk : v₂ (w ^ k) = (((k : ℝ) * β : ℝ) : RealValue) := by
    rw [AddValuation.map_pow, ← coe_order_of_ne v₂ hw0,
      ← WithTop.coe_nsmul]
    simp [β, nsmul_eq_mul]
  have hv₁wkneg : v₁ (w ^ k) < (0 : RealValue) := by
    rw [hv₁wk]
    exact_mod_cast mul_neg_of_pos_of_neg (by exact_mod_cast hk0) hα
  have hv₂wkpos : (0 : RealValue) < v₂ (w ^ k) := by
    rw [hv₂wk]
    exact_mod_cast mul_pos (by exact_mod_cast hk0) hβ
  have hden0 : 1 + w ^ k ≠ 0 := by
    intro hden
    have heq : w ^ k = -1 := eq_neg_of_add_eq_zero_right hden
    have : v₁ (w ^ k) = 0 := by rw [heq, AddValuation.map_neg, AddValuation.map_one]
    exact (ne_of_lt hv₁wkneg) this
  let e : F := w ^ k / (1 + w ^ k)
  refine ⟨e, ?_, ?_⟩
  · have hdenval : v₁ (1 + w ^ k) = v₁ (w ^ k) := by
      apply v₁.map_add_eq_of_lt_right
      simpa using hv₁wkneg
    have heminus : e - 1 = -1 / (1 + w ^ k) := by
      dsimp [e]
      field_simp
      ring
    have heminus0 : e - 1 ≠ 0 := by
      rw [heminus]
      exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hden0
    have hone : order v₁ (-1 : F) = 0 := by
      rw [← WithTop.coe_eq_coe, coe_order_of_ne v₁ (neg_ne_zero.mpr one_ne_zero),
        AddValuation.map_neg, AddValuation.map_one]
      rfl
    have hdenord : order v₁ (1 + w ^ k) = (k : ℝ) * α := by
      rw [← WithTop.coe_eq_coe, coe_order_of_ne v₁ hden0, hdenval, hv₁wk]
    have heord : order v₁ (e - 1) = -(k : ℝ) * α := by
      rw [heminus, order_div_of_ne v₁ (neg_ne_zero.mpr one_ne_zero) hden0,
        hone, hdenord]
      ring
    rw [← coe_order_of_ne v₁ heminus0, heord]
    exact_mod_cast hk₁
  · have hdenval : v₂ (1 + w ^ k) = 0 := by
      have h := v₂.map_add_eq_of_lt_left
        (show v₂ 1 < v₂ (w ^ k) by simpa using hv₂wkpos)
      simpa using h
    have he0 : e ≠ 0 := by
      dsimp [e]
      exact div_ne_zero hwk0 hden0
    have hwkord : order v₂ (w ^ k) = (k : ℝ) * β := by
      rw [← WithTop.coe_eq_coe, coe_order_of_ne v₂ hwk0, hv₂wk]
    have hdenord : order v₂ (1 + w ^ k) = 0 := by
      rw [← WithTop.coe_eq_coe, coe_order_of_ne v₂ hden0, hdenval]
      rfl
    have heord : order v₂ e = (k : ℝ) * β := by
      dsimp [e]
      rw [order_div_of_ne v₂ hwk0 hden0, hwkord, hdenord, sub_zero]
    rw [← coe_order_of_ne v₂ he0, heord]
    exact_mod_cast hk₂

/-- **Two-valuation approximation**, Steps 1--3 exactly as in the certified
blueprint. -/
theorem approximation {F : Type*} [Field F]
    (v₁ v₂ : RealValuation F)
    (h₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (h₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (x₁ x₂ : F) (T₁ T₂ : ℝ) :
    ∃ x : F, ((T₁ : ℝ) : RealValue) ≤ v₁ (x - x₁) ∧
      ((T₂ : ℝ) : RealValue) ≤ v₂ (x - x₂) := by
  by_cases hd : x₁ = x₂
  · subst x₂
    exact ⟨x₁, by simp, by simp⟩
  let d := x₁ - x₂
  have hd0 : d ≠ 0 := sub_ne_zero.mpr hd
  obtain ⟨e, he₁, he₂⟩ := exists_approximation_idempotent
    v₁ v₂ h₁ h₂ hne (T₁ - order v₁ d) (T₂ - order v₂ d)
  let x := e * x₁ + (1 - e) * x₂
  refine ⟨x, ?_, ?_⟩
  · have hformula : x - x₁ = (1 - e) * (x₂ - x₁) := by
      dsimp [x]
      ring
    rw [hformula, AddValuation.map_mul]
    have hsign : v₁ (1 - e) = v₁ (e - 1) := v₁.map_sub_swap _ _
    rw [hsign]
    have hdval := coe_order_of_ne v₁ hd0
    have hdswap : v₁ (x₂ - x₁) = v₁ d := by
      exact v₁.map_sub_swap _ _
    rw [hdswap, ← hdval]
    calc
      ((T₁ : ℝ) : RealValue) =
          ((T₁ - order v₁ d : ℝ) : RealValue) +
            ((order v₁ d : ℝ) : RealValue) := by
              rw [← WithTop.coe_add]
              congr 1
              ring
      _ ≤ v₁ (e - 1) + ((order v₁ d : ℝ) : RealValue) :=
        add_le_add he₁ le_rfl
  · have hformula : x - x₂ = e * (x₁ - x₂) := by
      dsimp [x]
      ring
    rw [hformula, AddValuation.map_mul, ← coe_order_of_ne v₂ hd0]
    calc
      ((T₂ : ℝ) : RealValue) =
          ((T₂ - order v₂ d : ℝ) : RealValue) +
            ((order v₂ d : ℝ) : RealValue) := by
              rw [← WithTop.coe_add]
              congr 1
              ring
      _ ≤ v₂ e + ((order v₂ d : ℝ) : RealValue) :=
        add_le_add he₂ le_rfl

/-- The symmetric one-threshold spelling. -/
theorem approximation_same_threshold {F : Type*} [Field F]
    (v₁ v₂ : RealValuation F)
    (h₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (h₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (x₁ x₂ : F) (T : ℝ) :
    ∃ x : F, ((T : ℝ) : RealValue) ≤ v₁ (x - x₁) ∧
      ((T : ℝ) : RealValue) ≤ v₂ (x - x₂) :=
  approximation v₁ v₂ h₁ h₂ hne x₁ x₂ T T

lemma coeff_finset_sum {F ι : Type*} [Semiring F]
    (s : Finset ι) (p : ι → F[X]) (m : ℕ) :
    (∑ i ∈ s, p i).coeff m = ∑ i ∈ s, (p i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Polynomial.coeff_add]

/-- Coefficientwise polynomial approximation.  The single invocation uses
`max T₁ T₂`, so the two requested thresholds are both met. -/
theorem polynomial_approximation {F : Type*} [Field F]
    (v₁ v₂ : RealValuation F)
    (h₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (h₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (f₁ f₂ : F[X]) (hf₁ : f₁.Monic) (hf₂ : f₂.Monic)
    (hdegree : f₂.natDegree = f₁.natDegree) (hn : f₁.natDegree ≠ 0)
    (T₁ T₂ : ℝ) :
    ∃ g : F[X], g.Monic ∧ g.natDegree = f₁.natDegree ∧
      ((T₁ : ℝ) : RealValue) ≤
        polynomialDistance v₁ f₁.natDegree f₁ g ∧
      ((T₂ : ℝ) : RealValue) ≤
        polynomialDistance v₂ f₁.natDegree f₂ g := by
  let n := f₁.natDegree
  choose c hc₁ hc₂ using fun i : Fin n =>
    approximation_same_threshold v₁ v₂ h₁ h₂ hne
      (f₁.coeff i) (f₂.coeff i) (max T₁ T₂)
  let q : F[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  let g : F[X] := X ^ n + q
  have hqdeg : q.degree < n := by
    exact Polynomial.degree_sum_fin_lt c
  have hg : g.Monic := Polynomial.monic_X_pow_add hqdeg
  have hgdeg : g.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    dsimp [g]
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow n
    · simpa [Polynomial.degree_X_pow] using hqdeg
  refine ⟨g, hg, by simpa [n] using hgdeg, ?_, ?_⟩
  · rw [polynomialDistance, dif_pos (by simpa [n] using hn)]
    apply Finset.le_inf'
    intro i hi
    have hiN : i < n := Finset.mem_range.mp hi
    let j : Fin n := ⟨i, hiN⟩
    have hcoeff : g.coeff i = c j := by
      simp only [g, q, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        if_neg hiN.ne, zero_add]
      rw [coeff_finset_sum]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Fintype.sum_eq_single j]
      · simp [j]
      · intro k hkj
        rw [if_neg]
        intro hik
        apply hkj
        apply Fin.ext
        simpa [j] using hik.symm
    rw [Polynomial.coeff_sub, hcoeff]
    refine (show ((T₁ : ℝ) : RealValue) ≤
      ((max T₁ T₂ : ℝ) : RealValue) by exact_mod_cast le_max_left T₁ T₂).trans ?_
    simpa [j] using hc₁ j
  · rw [polynomialDistance, dif_pos (by simpa [n] using hn)]
    apply Finset.le_inf'
    intro i hi
    have hiN : i < n := Finset.mem_range.mp hi
    let j : Fin n := ⟨i, hiN⟩
    have hcoeff : g.coeff i = c j := by
      simp only [g, q, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        if_neg hiN.ne, zero_add]
      rw [coeff_finset_sum]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Fintype.sum_eq_single j]
      · simp [j]
      · intro k hkj
        rw [if_neg]
        intro hik
        apply hkj
        apply Fin.ext
        simpa [j] using hik.symm
    rw [Polynomial.coeff_sub, hcoeff]
    refine (show ((T₂ : ℝ) : RealValue) ≤
      ((max T₁ T₂ : ℝ) : RealValue) by exact_mod_cast le_max_right T₁ T₂).trans ?_
    simpa [j] using hc₂ j

alias poly_approx := polynomial_approximation

/-! ## Split stability -/

/-- A root product whose valuation is at least `nT` has a factor of
valuation at least `T`. -/
lemma exists_factor_ge {K : Type*} [Field K] (v : RealValuation K)
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → K) (T : ℝ)
    (hprod : ((((n : ℝ) * T : ℝ)) : RealValue) ≤ v (∏ i, z i)) :
    ∃ i : Fin n, ((T : ℝ) : RealValue) ≤ v (z i) := by
  by_contra hnone
  push Not at hnone
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have hreal : ∀ i : Fin n, order v (z i) < T := by
    intro i
    have hitop : v (z i) ≠ (⊤ : RealValue) :=
      ne_of_lt ((hnone i).trans_le le_top)
    have hi0 : z i ≠ 0 := (AddValuation.ne_top_iff v).mp hitop
    have hi := hnone i
    rw [← coe_order_of_ne v hi0] at hi
    exact_mod_cast hi
  have hsum : (∑ i : Fin n, order v (z i)) < (n : ℝ) * T := by
    have h := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => hreal i)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hvalprod : v (∏ i, z i) =
      (((∑ i : Fin n, order v (z i)) : ℝ) : RealValue) := by
    rw [valuation_prod v Finset.univ]
    calc
      (∑ i : Fin n, v (z i)) =
          ∑ i : Fin n, ((order v (z i) : ℝ) : RealValue) := by
        apply Finset.sum_congr rfl
        intro i _
        have hitop : v (z i) ≠ (⊤ : RealValue) :=
          ne_of_lt ((hnone i).trans_le le_top)
        exact (coe_order_of_ne v ((AddValuation.ne_top_iff v).mp hitop)).symm
      _ = (((∑ i : Fin n, order v (z i)) : ℝ) : RealValue) :=
        (WithTop.coe_sum _ _).symm
  rw [hvalprod] at hprod
  have hsum' :
      (((∑ i : Fin n, order v (z i)) : ℝ) : RealValue) <
        ((((n : ℝ) * T : ℝ)) : RealValue) := by exact_mod_cast hsum
  exact (not_lt_of_ge hprod) hsum'

/-- The coefficient bound for a family of target centers. -/
def centerBound {F : Type*} [Field F] {n : ℕ}
    (v : RealValuation F) (c : Fin n → F) : ℝ := by
  classical
  exact max 0 (if h : (Finset.univ : Finset (Fin n)).Nonempty then
    (((Finset.univ.image fun i => -order v (c i)).max' (h.image _)) : ℝ)
  else 0)

lemma center_bound_nonneg {F : Type*} [Field F] {n : ℕ}
    (v : RealValuation F) (c : Fin n → F) : 0 ≤ centerBound v c :=
  le_max_left _ _

lemma center_coefficient_bound {F : Type*} [Field F] {n : ℕ}
    (v : RealValuation F) (c : Fin n → F) (i : Fin n) :
    ((-centerBound v c : ℝ) : RealValue) ≤ v (c i) := by
  classical
  by_cases hci : c i = 0
  · simp [hci]
  rw [← coe_order_of_ne v hci, WithTop.coe_le_coe]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  have hle : -order v (c i) ≤ centerBound v c := by
    rw [centerBound, dif_pos hne]
    exact (Finset.le_max'
      (Finset.univ.image fun j : Fin n => -order v (c j))
      (-order v (c i))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).trans
        (le_max_right (0 : ℝ) _)
  linarith

/-- The split threshold `nT + (n-1)C`. -/
def splitDelta {F : Type*} [Field F] {n : ℕ}
    (v : RealValuation F) (c : Fin n → F) (T : ℝ) : ℝ :=
  (n : ℝ) * T + ((n - 1 : ℕ) : ℝ) * centerBound v c

/-- A monic polynomial over an algebraically closed extension can be
indexed by `Fin n`, including multiplicities. -/
lemma exists_fin_root_factorization {F Ω : Type*} [Field F] [Field Ω]
    (ι : F →+* Ω) [IsAlgClosed Ω] (f : F[X]) (hf : f.Monic) :
    ∃ a : Fin f.natDegree → Ω,
      f.map ι = ∏ i : Fin f.natDegree, (X - C (a i)) := by
  let p : Polynomial Ω := f.map ι
  have hpmonic : p.Monic := hf.map ι
  have hsplits : p.Splits := IsAlgClosed.splits p
  let l : List Ω := p.roots.toList
  have hlen : l.length = f.natDegree := by
    calc
      l.length = p.roots.card := Multiset.length_toList _
      _ = p.natDegree := hsplits.natDegree_eq_card_roots.symm
      _ = f.natDegree := by dsimp [p]; exact hf.natDegree_map ι
  let e : Fin f.natDegree ≃ Fin l.length := (Fin.castOrderIso hlen.symm).toEquiv
  let a : Fin f.natDegree → Ω := fun i => l.get (e i)
  refine ⟨a, ?_⟩
  change p = ∏ i : Fin f.natDegree, (X - C (a i))
  rw [hsplits.eq_prod_roots_of_monic hpmonic]
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe]
  calc
    (l.map fun x => X - C x).prod =
        ∏ j : Fin l.length, (X - C (l.get j)) := by
          rw [← List.prod_ofFn]
          congr 1
          simpa using (List.ofFn_getElem_eq_map l (fun x => X - C x)).symm
    _ = ∏ i : Fin f.natDegree, (X - C (a i)) := by
      symm
      exact Fintype.prod_equiv e
        (fun i : Fin f.natDegree => X - C (a i))
        (fun j : Fin l.length => X - C (l.get j)) (fun _ => rfl)

/-- If the original polynomial is separable, the root indexing above can be
chosen injective. -/
lemma exists_fin_root_factorization_injective
    {F Ω : Type*} [Field F] [Field Ω]
    (ι : F →+* Ω) [IsAlgClosed Ω] (f : F[X]) (hf : f.Monic)
    (hsep : f.Separable) :
    ∃ a : Fin f.natDegree → Ω, Function.Injective a ∧
      f.map ι = ∏ i : Fin f.natDegree, (X - C (a i)) := by
  let p : Polynomial Ω := f.map ι
  have hpmonic : p.Monic := hf.map ι
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hpsep : p.Separable := by
    dsimp [p]
    exact hsep.map
  let l : List Ω := p.roots.toList
  have hlen : l.length = f.natDegree := by
    calc
      l.length = p.roots.card := Multiset.length_toList _
      _ = p.natDegree := hsplits.natDegree_eq_card_roots.symm
      _ = f.natDegree := by dsimp [p]; exact hf.natDegree_map ι
  let e : Fin f.natDegree ≃ Fin l.length := (Fin.castOrderIso hlen.symm).toEquiv
  let a : Fin f.natDegree → Ω := fun i => l.get (e i)
  have hlNodup : l.Nodup := by
    dsimp [l]
    rw [← Multiset.coe_nodup, Multiset.coe_toList]
    exact Polynomial.nodup_roots hpsep
  have hainj : Function.Injective a := by
    intro i j hij
    apply e.injective
    exact hlNodup.get_inj_iff.mp hij
  refine ⟨a, hainj, ?_⟩
  change p = ∏ i : Fin f.natDegree, (X - C (a i))
  rw [hsplits.eq_prod_roots_of_monic hpmonic]
  rw [← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe]
  calc
    (l.map fun x => X - C x).prod =
        ∏ j : Fin l.length, (X - C (l.get j)) := by
          rw [← List.prod_ofFn]
          congr 1
          simpa using (List.ofFn_getElem_eq_map l (fun x => X - C x)).symm
    _ = ∏ i : Fin f.natDegree, (X - C (a i)) := by
      symm
      exact Fintype.prod_equiv e
        (fun i : Fin f.natDegree => X - C (a i))
        (fun j : Fin l.length => X - C (l.get j)) (fun _ => rfl)

lemma monic_finset_prod {F ι : Type*} [CommRing F]
    (s : Finset ι) (p : ι → F[X])
    (hp : ∀ i ∈ s, (p i).Monic) : (∏ i ∈ s, p i).Monic := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

/-- **Split stability.** Reverse proximity at all target centers, disjoint
ball counting, and unique prolongation force every root into the base field. -/
theorem split_stability {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] [IsGalois F Ω]
    (v : RealValuation F) (hv : IsHenselian v) (w : RealValuation Ω)
    (hext : Extends (algebraMap F Ω) v w) {n : ℕ} (hn : 2 ≤ n)
    (c : Fin n → F) (hc : Function.Injective c)
    (g : F[X]) (hg : g.Monic) (hgdeg : g.natDegree = n)
    (r : Fin n → Ω)
    (hrfactor : g.map (algebraMap F Ω) = ∏ j : Fin n, (X - C (r j)))
    (T : ℝ)
    (hsep : ∀ i j : Fin n, i ≠ j →
      w (algebraMap F Ω (c i) - algebraMap F Ω (c j)) <
        ((T : ℝ) : RealValue))
    (hclose : ((splitDelta v c T : ℝ) : RealValue) ≤
      polynomialDistance v n (∏ i : Fin n, (X - C (c i))) g) :
    g.Splits := by
  let h : F[X] := ∏ i : Fin n, (X - C (c i))
  let C₀ := centerBound v c
  let Δ := splitDelta v c T
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hhmonic : h.Monic := by
    dsimp [h]
    apply monic_finset_prod
    intro i _
    exact Polynomial.monic_X_sub_C (c i)
  have hhdeg : h.natDegree = n := by
    dsimp [h]
    rw [Polynomial.natDegree_prod]
    · simp
    · intro i _
      exact (Polynomial.monic_X_sub_C (c i)).ne_zero
  have hqdeg : (g - h).natDegree < n := by
    apply Polynomial.IsMonicOfDegree.natDegree_sub_lt hn0
    · rw [Polynomial.isMonicOfDegree_iff]
      exact ⟨hgdeg.le, by simpa [hgdeg] using hg.coeff_natDegree⟩
    · rw [Polynomial.isMonicOfDegree_iff]
      exact ⟨hhdeg.le, by simpa [hhdeg] using hhmonic.coeff_natDegree⟩
  have hoccupy : ∀ i : Fin n,
      ∃ j : Fin n, ((T : ℝ) : RealValue) ≤
        w (algebraMap F Ω (c i) - r j) := by
    intro i
    have hcoeff : ∀ k < n,
        ((Δ : ℝ) : RealValue) ≤ v ((g - h).coeff k) := by
      intro k hk
      exact hclose.trans (by
        simpa [h, Δ] using polynomialDistance_le_coefficient v hn0 h g hk)
    have heval : ((((n : ℝ) * T : ℝ)) : RealValue) ≤ v ((g - h).eval (c i)) := by
      rw [Polynomial.eval_eq_sum_range' hqdeg]
      apply v.map_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      rw [AddValuation.map_mul, AddValuation.map_pow]
      have hpow := nsmul_le_nsmul_right (center_coefficient_bound v c i) k
      rw [← WithTop.coe_nsmul] at hpow
      refine le_trans ?_ (add_le_add (hcoeff k hkN) hpow)
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      have hkLe : (k : ℝ) ≤ (n - 1 : ℕ) := by
        exact_mod_cast Nat.le_sub_one_of_lt hkN
      have hC₀ : 0 ≤ C₀ := center_bound_nonneg v c
      dsimp [Δ, splitDelta]
      dsimp [C₀] at hC₀ ⊢
      simp only [nsmul_eq_mul]
      nlinarith
    have hhroot : h.eval (c i) = 0 := by
      dsimp [h]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have hgeval : (g - h).eval (c i) = g.eval (c i) := by
      rw [Polynomial.eval_sub, hhroot, sub_zero]
    rw [hgeval] at heval
    have hevalΩ : ((((n : ℝ) * T : ℝ)) : RealValue) ≤
        w (g.eval₂ (algebraMap F Ω) (algebraMap F Ω (c i))) := by
      rw [Polynomial.eval₂_hom, hext.apply]
      exact heval
    have hprod : g.eval₂ (algebraMap F Ω) (algebraMap F Ω (c i)) =
        ∏ j : Fin n, (algebraMap F Ω (c i) - r j) := by
      rw [← Polynomial.eval_map, hrfactor, Polynomial.eval_prod]
      simp
    rw [hprod] at hevalΩ
    exact exists_factor_ge w hn0 _ T hevalΩ
  choose φ hφ using hoccupy
  have hφinj : Function.Injective φ := by
    intro i j hij
    by_contra hij'
    have hcenters : ((T : ℝ) : RealValue) ≤
        w (algebraMap F Ω (c i) - algebraMap F Ω (c j)) := by
      have hadd := w.map_le_add
        (x := algebraMap F Ω (c i) - r (φ i))
        (y := r (φ i) - algebraMap F Ω (c j))
        (hφ i) (by
          rw [hij]
          exact le_trans (hφ j) (le_of_eq (w.map_sub_swap _ _)))
      simpa only [sub_add_sub_cancel] using hadd
    exact (not_lt_of_ge hcenters) (hsep i j hij')
  have hφsurj : Function.Surjective φ :=
    (Finite.injective_iff_surjective).mp hφinj
  have hroot_unique : ∀ i k : Fin n,
      ((T : ℝ) : RealValue) ≤
        w (algebraMap F Ω (c i) - r k) → k = φ i := by
    intro i k hk
    obtain ⟨j, rfl⟩ := hφsurj k
    by_contra hji
    have hcenters : ((T : ℝ) : RealValue) ≤
        w (algebraMap F Ω (c i) - algebraMap F Ω (c j)) := by
      have hadd := w.map_le_add
        (x := algebraMap F Ω (c i) - r (φ j))
        (y := r (φ j) - algebraMap F Ω (c j))
        hk (by exact le_trans (hφ j) (le_of_eq (w.map_sub_swap _ _)))
      simpa only [sub_add_sub_cancel] using hadd
    have hij : i ≠ j := fun hij => hji (congrArg φ hij.symm)
    exact (not_lt_of_ge hcenters) (hsep i j hij)
  have hrootBase : ∀ k : Fin n, ∃ x : F, algebraMap F Ω x = r k := by
    intro k
    obtain ⟨i, rfl⟩ := hφsurj k
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (r (φ i))).mpr
    intro σ
    have hrzero : g.eval₂ (algebraMap F Ω) (r (φ i)) = 0 := by
      rw [← Polynomial.eval_map, hrfactor, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (φ i))
      simp
    have hσzero : g.eval₂ (algebraMap F Ω) (σ (r (φ i))) = 0 := by
      have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap F Ω) =
          algebraMap F Ω := by
        ext x
        exact σ.commutes x
      calc
        g.eval₂ (algebraMap F Ω) (σ (r (φ i))) =
            g.eval₂ (σ.toRingEquiv.toRingHom.comp (algebraMap F Ω))
              (σ (r (φ i))) := by rw [hcomp]
        _ = σ (g.eval₂ (algebraMap F Ω) (r (φ i))) :=
          (Polynomial.hom_eval₂ g (algebraMap F Ω)
            σ.toRingEquiv.toRingHom (r (φ i))).symm
        _ = 0 := by rw [hrzero, map_zero]
    have hk : ∃ k : Fin n, σ (r (φ i)) = r k := by
      rw [← Polynomial.eval_map, hrfactor, Polynomial.eval_prod,
        Finset.prod_eq_zero_iff] at hσzero
      obtain ⟨k, _, hk⟩ := hσzero
      have hk' : σ (r (φ i)) - r k = 0 := by simpa using hk
      exact ⟨k, sub_eq_zero.mp hk'⟩
    obtain ⟨k, hk⟩ := hk
    have hball : ((T : ℝ) : RealValue) ≤
        w (algebraMap F Ω (c i) - r k) := by
      rw [← hk]
      have hinv := hv.extension_aut_invariant v w hext σ
        (algebraMap F Ω (c i) - r (φ i))
      rw [map_sub, σ.commutes] at hinv
      exact (hφ i).trans (le_of_eq hinv.symm)
    have hki := hroot_unique i k hball
    rw [hki] at hk
    exact hk
  choose d hd using hrootBase
  have hmap : g.map (algebraMap F Ω) =
      (∏ k : Fin n, (X - C (d k))).map (algebraMap F Ω) := by
    rw [Polynomial.map_prod]
    simpa [hd] using hrfactor
  have hgprod : g = ∏ k : Fin n, (X - C (d k)) :=
    (Polynomial.map_injective (algebraMap F Ω)
      (FaithfulSMul.algebraMap_injective F Ω)) hmap
  rw [hgprod]
  simp

/-! ## F. K. Schmidt's theorem -/

/-- Maximum of a finite real set, defaulting to zero. -/
def finiteMax (s : Finset ℝ) : ℝ :=
  if hs : s.Nonempty then s.max' hs else 0

lemma le_finiteMax_of_mem {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) :
    x ≤ finiteMax s := by
  have hs : s.Nonempty := ⟨x, hx⟩
  rw [finiteMax, dif_pos hs]
  exact Finset.le_max' s x hx

/-- Values of all ordered pairs of distinct points in a finite family. -/
def pairValues {K : Type*} [Field K] {n : ℕ}
    (v : RealValuation K) (a : Fin n → K) : Finset ℝ := by
  classical
  exact (((Finset.univ : Finset (Fin n)).product Finset.univ).filter
    fun p => p.1 ≠ p.2).image fun p => order v (a p.1 - a p.2)

lemma pair_value_le {K : Type*} [Field K] {n : ℕ}
    (v : RealValuation K) (a : Fin n → K) {i j : Fin n} (hij : i ≠ j) :
    order v (a i - a j) ≤ finiteMax (pairValues v a) := by
  apply le_finiteMax_of_mem
  classical
  rw [pairValues, Finset.mem_image]
  exact ⟨(i, j), by simp [hij], rfl⟩

/-- **F. K. Schmidt, rank-one characteristic-zero form.** -/
theorem main {F Ω : Type u} [Field F] [Field Ω] [CharZero F]
    [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω]
    (v₁ v₂ : RealValuation F)
    (hrank₁ : IsRankOneValuationSubring (realValuationSubring v₁))
    (hrank₂ : IsRankOneValuationSubring (realValuationSubring v₂))
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (hhens₁ : IsHenselian v₁) (hhens₂ : IsHenselian v₂) :
    IsAlgClosed F := by
  letI : IsAlgClosure F Ω := IsAlgClosure.mk inferInstance inferInstance
  letI : Normal F Ω := IsAlgClosure.normal F Ω
  letI : IsGalois F Ω := IsGalois.mk
  obtain ⟨w₁, hw₁, _⟩ := hhens₁ Ω inferInstance
  obtain ⟨w₂, hw₂, _⟩ := hhens₂ Ω inferInstance
  apply IsAlgClosed.of_exists_root F
  intro p hpmon hirr
  let n := p.natDegree
  have hnpos : 0 < n := by
    have hpne : p ≠ 1 := hirr.ne_one
    simpa [n] using hpmon.natDegree_pos.mpr hpne
  by_cases hn1 : n = 1
  · refine ⟨-(p.coeff 0), ?_⟩
    rw [hpmon.eq_X_add_C (by simpa [n] using hn1)]
    simp
  have hn : 2 ≤ n := by omega
  have hpsep : p.Separable := PerfectField.separable_of_irreducible hirr
  obtain ⟨a, hainj, hafactor⟩ :=
    exists_fin_root_factorization_injective (algebraMap F Ω) p hpmon hpsep
  let c : Fin n → F := fun i => (i : F)
  have hcinj : Function.Injective c := by
    intro i j hij
    have hcasteq : (((i : ℕ) : F)) = ((j : ℕ) : F) := by
      simpa [c] using hij
    exact Fin.ext (Nat.cast_injective hcasteq)
  let h : F[X] := ∏ i : Fin n, (X - C (c i))
  have hhmonic : h.Monic := by
    dsimp [h]
    apply monic_finset_prod
    intro i _
    exact Polynomial.monic_X_sub_C (c i)
  have hhdeg : h.natDegree = n := by
    dsimp [h]
    rw [Polynomial.natDegree_prod]
    · simp
    · intro i _
      exact (Polynomial.monic_X_sub_C (c i)).ne_zero
  let rootPairs : Finset ℝ := pairValues w₁ a
  let centerPairs : Finset ℝ := pairValues v₂ c
  let T : ℝ := max (finiteMax rootPairs) (finiteMax centerPairs) + 1
  have hrootSep : ∀ i j : Fin n, i ≠ j →
      w₁ (a i - a j) < ((T : ℝ) : RealValue) := by
    intro i j hij
    have hneij : a i - a j ≠ 0 := sub_ne_zero.mpr (hainj.ne hij)
    rw [← coe_order_of_ne w₁ hneij]
    apply WithTop.coe_lt_coe.mpr
    have hpairs : order w₁ (a i - a j) ≤ finiteMax rootPairs := by
      simpa [rootPairs] using pair_value_le w₁ a hij
    dsimp [T]
    linarith [le_max_left (finiteMax rootPairs) (finiteMax centerPairs)]
  have hcenterSepBase : ∀ i j : Fin n, i ≠ j →
      v₂ (c i - c j) < ((T : ℝ) : RealValue) := by
    intro i j hij
    have hneij : c i - c j ≠ 0 := sub_ne_zero.mpr (hcinj.ne hij)
    rw [← coe_order_of_ne v₂ hneij]
    apply WithTop.coe_lt_coe.mpr
    have hpairs : order v₂ (c i - c j) ≤ finiteMax centerPairs := by
      simpa [centerPairs] using pair_value_le v₂ c hij
    dsimp [T]
    linarith [le_max_right (finiteMax rootPairs) (finiteMax centerPairs)]
  let δ₁ := proximityDelta v₁ p n T
  let δ₂ := splitDelta v₂ c T
  obtain ⟨g, hgmonic, hgdeg, hgclose₁, hgclose₂⟩ :=
    polynomial_approximation v₁ v₂ hrank₁ hrank₂ hne p h hpmon hhmonic
      (by simpa [n] using hhdeg) (by omega) δ₁ δ₂
  obtain ⟨r, hrfactor⟩ :=
    exists_fin_root_factorization (algebraMap F Ω) g hgmonic
  have hrtype : Fin g.natDegree = Fin n := by rw [hgdeg]
  let r' : Fin n → Ω := fun i => r (Fin.cast hgdeg.symm i)
  have hrfactor' : g.map (algebraMap F Ω) =
      ∏ i : Fin n, (X - C (r' i)) := by
    rw [hrfactor]
    exact Fintype.prod_equiv (Fin.castOrderIso hgdeg).toEquiv
      (fun i : Fin g.natDegree => X - C (r i))
      (fun j : Fin n => X - C (r' j)) (fun _ => rfl)
  let i₀ : Fin n := ⟨0, hnpos⟩
  let b : Ω := r' i₀
  have hbroot : g.eval₂ (algebraMap F Ω) b = 0 := by
    rw [← Polynomial.eval_map, hrfactor', Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    simp [b]
  obtain ⟨i, hbi⟩ := root_proximity (algebraMap F Ω) v₁ w₁ hw₁
    p g hpmon hgmonic (by simpa [n] using hgdeg) (by omega)
    a hafactor hbroot T (by simpa [δ₁, n] using hgclose₁)
  have hkclose : KrasnerSeparated F w₁ (a i) b := by
    intro σ hσ
    have hairoot : p.eval₂ (algebraMap F Ω) (a i) = 0 := by
      rw [← Polynomial.eval_map, hafactor, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have hσroot : p.eval₂ (algebraMap F Ω) (σ (a i)) = 0 := by
      have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap F Ω) =
          algebraMap F Ω := by
        ext x
        exact σ.commutes x
      calc
        p.eval₂ (algebraMap F Ω) (σ (a i)) =
            p.eval₂ (σ.toRingEquiv.toRingHom.comp (algebraMap F Ω))
              (σ (a i)) := by rw [hcomp]
        _ = σ (p.eval₂ (algebraMap F Ω) (a i)) :=
          (Polynomial.hom_eval₂ p (algebraMap F Ω)
            σ.toRingEquiv.toRingHom (a i)).symm
        _ = 0 := by rw [hairoot, map_zero]
    have hj : ∃ j : Fin n, σ (a i) = a j := by
      rw [← Polynomial.eval_map, hafactor, Polynomial.eval_prod,
        Finset.prod_eq_zero_iff] at hσroot
      obtain ⟨j, _, hj⟩ := hσroot
      refine ⟨j, ?_⟩
      have : σ (a i) - a j = 0 := by simpa using hj
      exact sub_eq_zero.mp this
    obtain ⟨j, hj⟩ := hj
    have hji : j ≠ i := by
      intro hji
      apply hσ
      rw [hj, hji]
    have hleft : w₁ (a i - σ (a i)) < ((T : ℝ) : RealValue) := by
      rw [hj]
      exact hrootSep i j hji.symm
    exact hleft.trans_le hbi
  have hincl := krasner_separated v₁ hhens₁ w₁ hw₁ hkclose
  have haiInt : IsIntegral F (a i) := Algebra.IsIntegral.isIntegral (a i)
  have hbInt : IsIntegral F b := Algebra.IsIntegral.isIntegral b
  letI : FiniteDimensional F (IntermediateField.adjoin F {b}) :=
    IntermediateField.adjoin.finiteDimensional hbInt
  have hincl' :
      (IntermediateField.adjoin F {a i}).toSubalgebra.toSubmodule ≤
        (IntermediateField.adjoin F {b}).toSubalgebra.toSubmodule := hincl
  have hfinrank :
      Module.finrank F (IntermediateField.adjoin F {a i}) ≤
        Module.finrank F (IntermediateField.adjoin F {b}) :=
    Submodule.finrank_mono hincl'
  rw [IntermediateField.adjoin.finrank haiInt,
    IntermediateField.adjoin.finrank hbInt] at hfinrank
  have hpaeval : Polynomial.aeval (a i) p = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hafactor,
      Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hpmin : p = minpoly F (a i) :=
    (minpoly.eq_iff_aeval_eq_zero hirr hpmon).2 hpaeval
  have hdegreeLower : n ≤ (minpoly F b).natDegree := by
    change p.natDegree ≤ (minpoly F b).natDegree
    rw [hpmin]
    exact hfinrank
  have hbaeval : Polynomial.aeval b g = 0 := by
    simpa [Polynomial.aeval_def] using hbroot
  have hmindvd : minpoly F b ∣ g := minpoly.dvd F b hbaeval
  have hgeq : g = minpoly F b :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hbInt) hgmonic hmindvd (by simpa [hgdeg] using hdegreeLower)
  have hgirr : Irreducible g := by
    rw [hgeq]
    exact minpoly.irreducible hbInt
  have hcenterSep : ∀ i j : Fin n, i ≠ j →
      w₂ (algebraMap F Ω (c i) - algebraMap F Ω (c j)) <
        ((T : ℝ) : RealValue) := by
    intro i j hij
    rw [← map_sub, hw₂.apply]
    exact hcenterSepBase i j hij
  have hgsplit : g.Splits := split_stability v₂ hhens₂ w₂ hw₂ hn c hcinj
    g hgmonic hgdeg r' hrfactor' T hcenterSep
    (by simpa [δ₂, h] using hgclose₂)
  have hgdegreeOne := hgsplit.degree_eq_one_of_irreducible hgirr
  have hgdegreeN : g.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hgmonic.ne_zero, hgdeg]
  rw [hgdegreeN] at hgdegreeOne
  norm_num at hgdegreeOne
  omega

/-! ## Rank-one bridge and consumed form -/

lemma order_pow_of_ne {F : Type*} [Field F] (v : RealValuation F)
    {x : F} (hx : x ≠ 0) (m : ℕ) :
    order v (x ^ m) = (m : ℝ) * order v x := by
  have hpow0 : x ^ m ≠ 0 := pow_ne_zero _ hx
  rw [← WithTop.coe_eq_coe, coe_order_of_ne v hpow0,
    AddValuation.map_pow, ← coe_order_of_ne v hx,
    ← WithTop.coe_nsmul]
  simp [nsmul_eq_mul]

/-- Every nontrivial real-valued valuation has no proper nontrivial
coarsening.  This direct archimedean argument is stronger than the
algebraic-over-`ℚ` bridge needed below. -/
theorem realValuation_rank_one {F : Type*} [Field F]
    (v : RealValuation F) (hv : realValuationSubring v ≠ ⊤) :
    IsRankOneValuationSubring (realValuationSubring v) := by
  refine ⟨hv, ?_⟩
  intro D hAD
  by_cases hDA : D = realValuationSubring v
  · exact Or.inl hDA
  right
  apply ValuationSubring.ext
  intro y
  constructor
  · intro _
    exact ValuationSubring.mem_top y
  · intro _
    have hnot : ¬ D ≤ realValuationSubring v := by
      intro hle
      exact hDA (le_antisymm hle hAD)
    obtain ⟨x, hxD, hxA⟩ := SetLike.not_le_iff_exists.mp hnot
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      exact hxA (realValuationSubring v).zero_mem
    have hxnegV : v x < (0 : RealValue) := lt_of_not_ge hxA
    have hxneg : order v x < 0 := by
      rw [← coe_order_of_ne v hx0] at hxnegV
      exact_mod_cast hxnegV
    by_cases hy0 : y = 0
    · subst y
      exact D.zero_mem
    obtain ⟨m, hm⟩ := exists_nat_gt
      ((-order v y) / (-order v x))
    have hpos : 0 < -order v x := by linarith
    have hm' := (div_lt_iff₀ hpos).mp hm
    have hquot : 0 ≤ order v (y / x ^ m) := by
      rw [order_div_of_ne v hy0 (pow_ne_zero _ hx0), order_pow_of_ne v hx0]
      nlinarith
    have hquotA : y / x ^ m ∈ realValuationSubring v := by
      rw [mem_realValuationSubring, ← coe_order_of_ne v
        (div_ne_zero hy0 (pow_ne_zero _ hx0))]
      exact_mod_cast hquot
    have hquotD : y / x ^ m ∈ D := hAD hquotA
    have hxpowD : x ^ m ∈ D := pow_mem hxD m
    rw [← div_mul_cancel₀ y (pow_ne_zero _ hx0)]
    exact D.mul_mem _ _ hquotD hxpowD

/-- Rank-one bridge for a subfield of an algebraic closure of `ℚ`.
The real-valued representation already supplies the order embedding into
`ℝ`; the proof above shows the equivalent coarsening characterization. -/
theorem rank_one_bridge {Ω : Type u} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (Z : IntermediateField ℚ Ω)
    (v : RealValuation Z) (hv : realValuationSubring v ≠ ⊤) :
    IsRankOneValuationSubring (realValuationSubring v) :=
  realValuation_rank_one v hv

/-- The separably-closed conclusion in the real-valued interface proved in
this file. -/
theorem fkSchmidt_two_henselian_valuations
    {F Ω : Type u} [Field F] [Field Ω] [CharZero F]
    [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [IsAlgClosed Ω]
    (v₁ v₂ : RealValuation F)
    (h₁ : realValuationSubring v₁ ≠ ⊤)
    (h₂ : realValuationSubring v₂ ≠ ⊤)
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (hhens₁ : IsHenselian v₁) (hhens₂ : IsHenselian v₂) :
    IsSepClosed F := by
  letI : IsAlgClosed F := main (Ω := Ω) v₁ v₂
    (realValuation_rank_one v₁ h₁) (realValuation_rank_one v₂ h₂)
    hne hhens₁ hhens₂
  infer_instance

alias fkSchmidt_two_henselian_rank_one := fkSchmidt_two_henselian_valuations

/-- A nontrivial absolute automorphism excludes two inequivalent
nontrivial Henselian real-valued valuations. -/
theorem consumed_of_algEquiv {Ω : Type u} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω)
    (hG : ∃ σ : Ω ≃ₐ[Z] Ω, σ ≠ 1)
    (v₁ v₂ : RealValuation Z)
    (h₁ : realValuationSubring v₁ ≠ ⊤)
    (h₂ : realValuationSubring v₂ ≠ ⊤)
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (hhens₁ : IsHenselian v₁) (hhens₂ : IsHenselian v₂) : False := by
  have hZclosed : IsAlgClosed Z := main (Ω := Ω) v₁ v₂
    (rank_one_bridge Z v₁ h₁) (rank_one_bridge Z v₂ h₂)
    hne hhens₁ hhens₂
  letI : IsAlgClosed Z := hZclosed
  have hsurj : Function.Surjective (algebraMap Z Ω) :=
    IsSepClosed.algebraMap_surjective Z Ω
  obtain ⟨σ, hσ⟩ := hG
  apply hσ
  ext x
  obtain ⟨z, rfl⟩ := hsurj x
  exact σ.commutes z

/-- The fixing-subgroup form used by the recovery consumer.  The valuation
arguments here are the normalized real-valued presentations used throughout
this file. -/
theorem consumed {Ω : Type u} [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [IsAlgClosed Ω]
    (Z : IntermediateField ℚ Ω)
    (hG : Z.fixingSubgroup ≠ ⊥)
    (v₁ v₂ : RealValuation Z)
    (h₁ : realValuationSubring v₁ ≠ ⊤)
    (h₂ : realValuationSubring v₂ ≠ ⊤)
    (hne : realValuationSubring v₁ ≠ realValuationSubring v₂)
    (hhens₁ : IsHenselian v₁) (hhens₂ : IsHenselian v₂) : False := by
  obtain ⟨σ, hσ⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hG
  let τ : Ω ≃ₐ[Z] Ω := IntermediateField.fixingSubgroupEquiv Z σ
  have hτ : τ ≠ 1 := by
    intro h
    apply hσ
    apply (IntermediateField.fixingSubgroupEquiv Z).injective
    simpa [τ] using h
  exact consumed_of_algEquiv Z ⟨τ, hτ⟩ v₁ v₂ h₁ h₂ hne hhens₁ hhens₂

end

end NU.LocalTheory.FKSchmidt
