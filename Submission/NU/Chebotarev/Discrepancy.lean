import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Quantitative affine-lattice point counting

A self-contained fundamental-cell form of Davenport's lattice-point argument.
The estimates in this file are uniform in the translate of the lattice.
-/

open Bornology Filter MeasureTheory Metric Module Pointwise Set Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace NU.Chebotarev
namespace Discrepancy

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The half-open fundamental cell based at a point of the affine lattice. -/
def fundamentalCell (b : Basis ι ℤ L) (v : E) (l : L) : Set E :=
  (v + (l : E)) +ᵥ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)

/-- Indices of points of the affine lattice `v + L` which lie in `S`. -/
def affineLatticeIndexSet (v : E) (S : Set E) : Set L :=
  {l | v + (l : E) ∈ S}

/-- The number of points of `v + L` in `S` (for bounded `S`). -/
def affineLatticePointCount (v : E) (S : Set E) : ℕ :=
  (affineLatticeIndexSet L v S).ncard

/-- Indexing an affine lattice by its underlying lattice is equivalent to the
usual set of ambient affine-lattice points. -/
def affineLatticePointEquiv (v : E) (S : Set E) :
    affineLatticeIndexSet L v S ≃ {x : E // x ∈ S ∧ x - v ∈ L} where
  toFun l := ⟨v + (l.1 : E), l.2, by simpa using l.1.2⟩
  invFun x := ⟨⟨x.1 - v, x.2.2⟩, by simpa [affineLatticeIndexSet] using x.2.1⟩
  left_inv l := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- `affineLatticePointCount` is literally the cardinality of the ambient
intersection of `S` with the affine lattice `v + L`. -/
theorem affineLatticePointCount_eq_natCard (v : E) (S : Set E) :
    affineLatticePointCount L v S =
      Nat.card {x : E // x ∈ S ∧ x - v ∈ L} := by
  rw [affineLatticePointCount, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (affineLatticePointEquiv L v S)

/-- Fundamental cells which meet the topological boundary of `S`. -/
def boundaryCellIndices (b : Basis ι ℤ L) (v : E) (S : Set E) : Set L :=
  {l | (fundamentalCell L b v l ∩ frontier S).Nonempty}

/-- A convenient radius containing the chosen half-open fundamental cell. -/
def fundamentalCellRadius (b : Basis ι ℤ L) : ℝ :=
  ∑ i, ‖b.ofZLatticeBasis ℝ L i‖

private theorem norm_le_fundamentalCellRadius (b : Basis ι ℤ L)
    {x : E} (hx : x ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) :
    ‖x‖ ≤ fundamentalCellRadius L b := by
  rw [← ZSpan.fract_eq_self.mpr hx]
  exact ZSpan.norm_fract_le _ _

private theorem zero_mem_fundamentalDomain (b : Basis ι ℤ L) :
    (0 : E) ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) := by
  rw [ZSpan.mem_fundamentalDomain]
  intro i
  simp

private theorem fundamentalDomain_convex (b : Basis ι ℤ L) :
    Convex ℝ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) := by
  rw [show ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) =
      ⋂ i, (b.ofZLatticeBasis ℝ).coord i ⁻¹' Set.Ico (0 : ℝ) 1 by
    ext x
    simp [ZSpan.mem_fundamentalDomain]]
  exact convex_iInter fun i => (convex_Ico (0 : ℝ) 1).linear_preimage _

private theorem anchor_mem_fundamentalCell (b : Basis ι ℤ L) (v : E) (l : L) :
    v + (l : E) ∈ fundamentalCell L b v l := by
  rw [fundamentalCell, Set.mem_vadd_set]
  exact ⟨0, zero_mem_fundamentalDomain L b, by simp⟩

private theorem fundamentalCell_isPreconnected (b : Basis ι ℤ L) (v : E) (l : L) :
    IsPreconnected (fundamentalCell L b v l) :=
  ((fundamentalDomain_convex L b).vadd (v + (l : E))).isPreconnected

private theorem preconnected_cell_dichotomy {C S : Set E} {p : E}
    (hC : IsPreconnected C) (hp : p ∈ C)
    (hbd : ¬ (C ∩ frontier S).Nonempty) :
    (p ∈ S → C ⊆ S) ∧ (p ∉ S → Disjoint C S) := by
  have hsub : C ⊆ interior S ∪ interior Sᶜ := by
    intro x hx
    have hx' : x ∈ (frontier S)ᶜ := by
      simpa [Set.mem_compl_iff] using fun hxf => hbd ⟨x, hx, hxf⟩
    simpa only [compl_frontier_eq_union_interior] using hx'
  have hd : Disjoint (interior S) (interior Sᶜ) :=
    (disjoint_compl_right.mono interior_subset interior_subset)
  rcases hC.subset_or_subset isOpen_interior isOpen_interior hd hsub with hleft | hright
  · refine ⟨fun _ => hleft.trans interior_subset, fun hps => ?_⟩
    exact (hps (interior_subset (hleft hp))).elim
  · refine ⟨fun hps => ?_, fun _ => ?_⟩
    · exact ((interior_subset (hright hp) : p ∈ Sᶜ) hps).elim
    · exact Set.disjoint_left.2 fun x hxC hxS =>
        (interior_subset (hright hxC) : x ∈ Sᶜ) hxS

private theorem affineLatticeIndexSet_finite (v : E) {S : Set E} (hS : IsBounded S) :
    (affineLatticeIndexSet L v S).Finite := by
  let K : Set E := (-v) +ᵥ S
  have hK : IsBounded K := hS.vadd (-v)
  have hKL : (K ∩ (L : Set E)).Finite := by
    change (K ∩ L.toAddSubgroup).Finite
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hK inferInstance
  apply Set.Finite.of_finite_image
    (hKL.subset (show ((fun l : L => (l : E)) '' affineLatticeIndexSet L v S) ⊆
        K ∩ (L : Set E) by
      rintro x ⟨l, hl, rfl⟩
      refine ⟨?_, l.property⟩
      rw [Set.mem_vadd_set]
      exact ⟨v + (l : E), hl, by simp⟩))
  exact Subtype.coe_injective.injOn

/-- The ambient intersection of a bounded set with an affine lattice is finite. -/
theorem finite_affineLatticePointSubtype (v : E) {S : Set E} (hS : IsBounded S) :
    Finite {x : E // x ∈ S ∧ x - v ∈ L} := by
  letI : Fintype (affineLatticeIndexSet L v S) :=
    (affineLatticeIndexSet_finite L v hS).fintype
  exact Finite.of_equiv _ (affineLatticePointEquiv L v S)

private theorem boundaryCellIndices_finite (b : Basis ι ℤ L) (v : E)
    {S : Set E} (hS : IsBounded S) :
    (boundaryCellIndices L b v S).Finite := by
  let F : Set E := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  let K : Set E := ((-v) +ᵥ frontier S) - F
  have hfront : IsBounded (frontier S) :=
    hS.closure.subset frontier_subset_closure
  have hK : IsBounded K := (hfront.vadd (-v)).sub (ZSpan.fundamentalDomain_isBounded _)
  have hKL : (K ∩ (L : Set E)).Finite := by
    change (K ∩ L.toAddSubgroup).Finite
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hK inferInstance
  apply Set.Finite.of_finite_image
    (hKL.subset (show ((fun l : L => (l : E)) '' boundaryCellIndices L b v S) ⊆
        K ∩ (L : Set E) by
      rintro x ⟨l, hl, rfl⟩
      obtain ⟨y, hycell, hyfront⟩ := hl
      rw [fundamentalCell, Set.mem_vadd_set] at hycell
      obtain ⟨f, hfF, hfy⟩ := hycell
      refine ⟨?_, l.property⟩
      rw [Set.mem_sub]
      refine ⟨-v + y, ?_, f, hfF, ?_⟩
      · rw [Set.mem_vadd_set]
        exact ⟨y, hyfront, rfl⟩
      · rw [← hfy]
        simp only [vadd_eq_add]
        abel))
  exact Subtype.coe_injective.injOn

private theorem inter_fundamentalCell_eq_of_mem (b : Basis ι ℤ L) (v : E)
    (S : Set E) (l : L) (hl : l ∉ boundaryCellIndices L b v S)
    (hp : v + (l : E) ∈ S) :
    S ∩ fundamentalCell L b v l = fundamentalCell L b v l := by
  have h := preconnected_cell_dichotomy
    (fundamentalCell_isPreconnected L b v l)
    (anchor_mem_fundamentalCell L b v l) hl
  ext x
  simp only [Set.mem_inter_iff]
  exact ⟨fun hx => hx.2, fun hx => ⟨h.1 hp hx, hx⟩⟩

private theorem inter_fundamentalCell_eq_empty_of_not_mem (b : Basis ι ℤ L) (v : E)
    (S : Set E) (l : L) (hl : l ∉ boundaryCellIndices L b v S)
    (hp : v + (l : E) ∉ S) :
    S ∩ fundamentalCell L b v l = ∅ := by
  have h := preconnected_cell_dichotomy
    (fundamentalCell_isPreconnected L b v l)
    (anchor_mem_fundamentalCell L b v l) hl
  exact Set.disjoint_iff_inter_eq_empty.mp (h.2 hp).symm

private theorem measureReal_fundamentalCell (μ : Measure E) [μ.IsAddHaarMeasure]
    (b : Basis ι ℤ L) (v : E) (l : L) :
    μ.real (fundamentalCell L b v l) = ZLattice.covolume L μ := by
  rw [fundamentalCell, Measure.real_def, measure_vadd]
  exact (ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)).symm

/-- **Fundamental-cell discrepancy inequality.** For every translate `v + L`, the
absolute difference between its point count in a bounded set and volume divided
by covolume is at most the number of chosen fundamental cells meeting the
frontier. The right hand side is finite and the estimate is uniform in `v`. -/
theorem abs_affineLatticePointCount_sub_volume_div_covolume_le_boundaryCells
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    (b : Basis ι ℤ L) (v : E) (S : Set E) (hS : IsBounded S) :
    |(affineLatticePointCount L v S : ℝ) -
        μ.real S / ZLattice.covolume L μ| ≤
      (boundaryCellIndices L b v S).ncard := by
  classical
  let A : Set L := affineLatticeIndexSet L v S
  let B : Set L := boundaryCellIndices L b v S
  let T : Set L := A ∪ B
  have hA : A.Finite := affineLatticeIndexSet_finite L v hS
  have hB : B.Finite := boundaryCellIndices_finite L b v hS
  have hT : T.Finite := hA.union hB
  let t : Finset L := hT.toFinset
  have hAt : A ⊆ T := Set.subset_union_left
  have hBt : B ⊆ T := Set.subset_union_right
  have ht_mem {l : L} : l ∈ t ↔ l ∈ T := by
    simp [t]
  have hcellset (l : L) :
      l +ᵥ (v +ᵥ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) =
        fundamentalCell L b v l := by
    ext x
    simp only [fundamentalCell, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      simp only [Submodule.vadd_def, vadd_eq_add]
      abel
    · rintro ⟨z, hz, rfl⟩
      refine ⟨v +ᵥ z, ⟨z, hz, rfl⟩, ?_⟩
      simp only [Submodule.vadd_def, vadd_eq_add]
      abel
  have hzero (l : L) (hlt : l ∉ T) :
      μ (S ∩ fundamentalCell L b v l) = 0 := by
    have hlB : l ∉ B := fun hl => hlt (hBt hl)
    have hlA : v + (l : E) ∉ S := by
      simpa only [A, affineLatticeIndexSet, Set.mem_setOf_eq] using
        (fun hl => hlt (hAt hl))
    rw [inter_fundamentalCell_eq_empty_of_not_mem L b v S l hlB hlA, measure_empty]
  letI : VAddInvariantMeasure L E μ :=
    ⟨fun l s _ => by
      simpa only [Submodule.vadd_def, vadd_eq_add] using
        measure_preimage_add μ (l : E) s⟩
  have hdecomp :=
    ((ZLattice.isAddFundamentalDomain b μ).vadd_of_comm v).measure_eq_tsum' S
  have hmeasure : μ.real S =
      ∑ l ∈ t, μ.real (S ∩ fundamentalCell L b v l) := by
    rw [Measure.real_def, hdecomp]
    rw [tsum_eq_sum (s := t) (fun l hlt => by
      rw [hcellset]
      exact hzero l (by simpa [ht_mem] using hlt))]
    simp_rw [hcellset]
    apply ENNReal.toReal_sum
    intro l hl
    exact measure_ne_top_of_subset Set.inter_subset_left hS.measure_lt_top.ne
  have hcountNat : A.ncard = {l ∈ t | l ∈ A}.card := by
    rw [Set.ncard_eq_toFinset_card A hA]
    congr 1
    ext l
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun hl => ⟨ht_mem.mpr (hAt hl), hl⟩, fun hl => hl.2⟩
  have hcount : (A.ncard : ℝ) =
      ∑ l ∈ t, if l ∈ A then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole, hcountNat]
  let c : ℝ := ZLattice.covolume L μ
  have hc : 0 < c := ZLattice.covolume_pos L μ
  have hmain : (A.ncard : ℝ) - μ.real S / c =
      ∑ l ∈ t, ((if l ∈ A then (1 : ℝ) else 0) -
        μ.real (S ∩ fundamentalCell L b v l) / c) := by
    rw [Finset.sum_sub_distrib, ← hcount, ← Finset.sum_div, ← hmeasure]
  have hcell_ne_top (l : L) : μ (fundamentalCell L b v l) ≠ ⊤ :=
    ((ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ)).vadd
      (v + (l : E))).measure_lt_top.ne
  have hquotient (l : L) :
      0 ≤ μ.real (S ∩ fundamentalCell L b v l) / c ∧
        μ.real (S ∩ fundamentalCell L b v l) / c ≤ 1 := by
    constructor
    · exact div_nonneg measureReal_nonneg hc.le
    · rw [div_le_one hc]
      calc
        μ.real (S ∩ fundamentalCell L b v l)
            ≤ μ.real (fundamentalCell L b v l) :=
          measureReal_mono Set.inter_subset_right (hcell_ne_top l)
        _ = c := measureReal_fundamentalCell L μ b v l
  have hdelta (l : L) (hlt : l ∈ t) :
      |(if l ∈ A then (1 : ℝ) else 0) -
          μ.real (S ∩ fundamentalCell L b v l) / c| ≤
        if l ∈ B then (1 : ℝ) else 0 := by
    by_cases hlB : l ∈ B
    · rw [if_pos hlB]
      obtain ⟨hq0, hq1⟩ := hquotient l
      by_cases hlA : l ∈ A
      · rw [if_pos hlA, abs_of_nonneg (sub_nonneg.mpr hq1)]
        linarith
      · rw [if_neg hlA, zero_sub, abs_neg, abs_of_nonneg hq0]
        exact hq1
    · rw [if_neg hlB]
      by_cases hlA : l ∈ A
      · have hp : v + (l : E) ∈ S := hlA
        rw [if_pos hlA, inter_fundamentalCell_eq_of_mem L b v S l hlB hp,
          measureReal_fundamentalCell L μ b v l]
        simp [c, hc.ne']
      · have hp : v + (l : E) ∉ S := hlA
        rw [if_neg hlA,
          inter_fundamentalCell_eq_empty_of_not_mem L b v S l hlB hp]
        simp
  calc
    |(affineLatticePointCount L v S : ℝ) - μ.real S / ZLattice.covolume L μ|
        = |∑ l ∈ t, ((if l ∈ A then (1 : ℝ) else 0) -
            μ.real (S ∩ fundamentalCell L b v l) / c)| := by
          rw [affineLatticePointCount]
          change |(A.ncard : ℝ) - μ.real S / c| = _
          rw [hmain]
    _ ≤ ∑ l ∈ t, |(if l ∈ A then (1 : ℝ) else 0) -
            μ.real (S ∩ fundamentalCell L b v l) / c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ t, if l ∈ B then (1 : ℝ) else 0 := by
      exact Finset.sum_le_sum fun l hl => hdelta l hl
    _ = (B.ncard : ℝ) := by
      rw [Finset.sum_boole]
      norm_cast
      rw [Set.ncard_eq_toFinset_card B hB]
      congr 1
      ext l
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, and_iff_right_iff_imp]
      exact fun hl => ht_mem.mpr (hBt hl)
    _ = (boundaryCellIndices L b v S).ncard := rfl

/-- Lattice vectors in a norm ball. -/
def latticeNormBall (r : ℝ) : Set L :=
  {l | ‖(l : E)‖ ≤ r}

private theorem latticeNormBall_finite (r : ℝ) :
    (latticeNormBall L r).Finite := by
  have hKL : (Metric.closedBall (0 : E) r ∩ (L : Set E)).Finite := by
    change (Metric.closedBall (0 : E) r ∩ L.toAddSubgroup).Finite
    have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall inferInstance
  apply Set.Finite.of_finite_image
    (hKL.subset (show ((fun l : L => (l : E)) '' latticeNormBall L r) ⊆
        Metric.closedBall (0 : E) r ∩ (L : Set E) by
      rintro x ⟨l, hl, rfl⟩
      exact ⟨mem_closedBall_zero_iff.mpr hl, l.property⟩))
  exact Subtype.coe_injective.injOn

/-- A finite, explicit upper bound for the number of points of any translate
of `L` in a ball of radius `r`. -/
def affineLatticeLocalMultiplicity (b : Basis ι ℤ L) (r : ℝ) : ℕ :=
  (latticeNormBall L (max r 0 + fundamentalCellRadius L b)).ncard

/-- The local multiplicity bound is independent of both the translate and the
center of the ball. -/
theorem ncard_affineLatticeIndexSet_closedBall_le_localMultiplicity
    (b : Basis ι ℤ L) (v c₀ : E) (r : ℝ) :
    (affineLatticeIndexSet L v (Metric.closedBall c₀ r)).ncard ≤
      affineLatticeLocalMultiplicity L b r := by
  classical
  let bR : Basis ι ℝ E := b.ofZLatticeBasis ℝ
  let y : E := c₀ - v
  obtain ⟨q₀, hq₀⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain bR y
  have hspan : Submodule.span ℤ (Set.range bR) = L :=
    b.ofZLatticeBasis_span ℝ
  let q : L := ⟨(q₀ : E), by rw [← hspan]; exact q₀.property⟩
  let A : Set L := affineLatticeIndexSet L v (Metric.closedBall c₀ r)
  let R : ℝ := max r 0 + fundamentalCellRadius L b
  have hRfinite : (latticeNormBall L R).Finite := latticeNormBall_finite L R
  have himage : (fun l : L => l + q) '' A ⊆ latticeNormBall L R := by
    rintro z ⟨l, hl, rfl⟩
    change ‖((l + q : L) : E)‖ ≤ R
    have hlball : dist (v + (l : E)) c₀ ≤ r := by
      exact (Metric.mem_closedBall.mp hl)
    have hqnorm : ‖(q₀ : E) + y‖ ≤ fundamentalCellRadius L b :=
      norm_le_fundamentalCellRadius L b hq₀.1
    have heq : ((l + q : L) : E) =
        (v + (l : E) - c₀) + ((q₀ : E) + y) := by
      dsimp only [q, y]
      push_cast
      abel
    rw [heq]
    calc
      ‖(v + (l : E) - c₀) + ((q₀ : E) + y)‖
          ≤ ‖v + (l : E) - c₀‖ + ‖(q₀ : E) + y‖ := norm_add_le _ _
      _ ≤ r + fundamentalCellRadius L b := by
        gcongr
        simpa only [dist_eq_norm] using hlball
      _ ≤ R := by
        dsimp only [R]
        gcongr
        exact le_max_left r 0
  calc
    A.ncard = ((fun l : L => l + q) '' A).ncard :=
      (Set.ncard_image_of_injective A (add_left_injective q)).symm
    _ ≤ (latticeNormBall L R).ncard := Set.ncard_le_ncard himage hRfinite
    _ = affineLatticeLocalMultiplicity L b r := rfl

/-- A finite metric cover of the frontier bounds the number of boundary cells.
The bound is uniform in the affine translate `v`. -/
theorem boundaryCellIndices_ncard_le_of_isCover
    (b : Basis ι ℤ L) (v : E) (S : Set E) (ε : ℝ≥0) (N : Set E)
    (hN : N.Finite) (hcover : Metric.IsCover ε (frontier S) N) :
    (boundaryCellIndices L b v S).ncard ≤
      N.ncard * affineLatticeLocalMultiplicity L b
        ((ε : ℝ) + fundamentalCellRadius L b) := by
  classical
  let r : ℝ := (ε : ℝ) + fundamentalCellRadius L b
  let Q : ℕ := affineLatticeLocalMultiplicity L b r
  let C : E → Set L := fun z =>
    affineLatticeIndexSet L v (Metric.closedBall z r)
  have hCfinite (z : E) : (C z).Finite :=
    affineLatticeIndexSet_finite L v Metric.isBounded_closedBall
  have hsub : boundaryCellIndices L b v S ⊆ ⋃ z ∈ N, C z := by
    intro l hl
    obtain ⟨x, hxcell, hxfront⟩ := hl
    rw [fundamentalCell, Set.mem_vadd_set] at hxcell
    obtain ⟨f, hf, hfx⟩ := hxcell
    have hxcov := (Metric.isCover_iff_subset_iUnion_closedBall.mp hcover) hxfront
    simp only [Set.mem_iUnion] at hxcov
    obtain ⟨z, hzN, hxz⟩ := hxcov
    rw [Set.mem_iUnion]
    refine ⟨z, Set.mem_iUnion.mpr ⟨hzN, ?_⟩⟩
    change v + (l : E) ∈ Metric.closedBall z r
    rw [Metric.mem_closedBall]
    calc
      dist (v + (l : E)) z ≤ dist (v + (l : E)) x + dist x z :=
        dist_triangle _ _ _
      _ ≤ fundamentalCellRadius L b + (ε : ℝ) := by
        gcongr
        · rw [← hfx]
          calc
            dist (v + (l : E)) ((v + (l : E)) +ᵥ f) =
                dist ((v + (l : E)) + 0) ((v + (l : E)) + f) := by
                  simp only [vadd_eq_add, add_zero]
            _ = dist 0 f := dist_add_left _ _ _
            _ = ‖f‖ := dist_zero_left f
            _ ≤ fundamentalCellRadius L b := norm_le_fundamentalCellRadius L b hf
        · exact Metric.mem_closedBall.mp hxz
      _ = r := by simp [r, add_comm]
  have hUnionFinite : (⋃ z ∈ N, C z).Finite :=
    hN.biUnion fun z _ => hCfinite z
  calc
    (boundaryCellIndices L b v S).ncard
        ≤ (⋃ z ∈ N, C z).ncard := Set.ncard_le_ncard hsub hUnionFinite
    _ ≤ ∑ᶠ z ∈ N, (C z).ncard := hN.ncard_biUnion_le C
    _ = ∑ z ∈ hN.toFinset, (C z).ncard :=
      finsum_mem_eq_finite_toFinset_sum (fun z => (C z).ncard) hN
    _ ≤ ∑ _z ∈ hN.toFinset, Q := by
      exact Finset.sum_le_sum fun z _ =>
        ncard_affineLatticeIndexSet_closedBall_le_localMultiplicity L b v z r
    _ = N.ncard * Q := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Set.ncard_eq_toFinset_card N hN]
    _ = N.ncard * affineLatticeLocalMultiplicity L b
        ((ε : ℝ) + fundamentalCellRadius L b) := rfl

section LipschitzBoundary

variable {κ : Type*} [Fintype κ]

/-- The parameter cube used for Lipschitz boundary charts. -/
def unitCube : Set (κ → ℝ) := Set.Icc 0 1

/-- The regular grid with denominator `n` in the unit cube. -/
def cubeGrid (n : ℕ) : Set (κ → ℝ) :=
  Set.range fun q : κ → Fin (n + 1) => fun i => (q i : ℝ) / n

/-- Radius of the denominator-`n` cube grid. -/
def cubeGridRadius (n : ℕ) : ℝ≥0 :=
  ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n)⟩

private theorem cubeGrid_finite (n : ℕ) : (cubeGrid (κ := κ) n).Finite :=
  Set.finite_range _

/-- The denominator-`n` grid has at most `(n+1)^k` points. -/
theorem cubeGrid_ncard_le (n : ℕ) :
    (cubeGrid (κ := κ) n).ncard ≤ (n + 1) ^ Fintype.card κ := by
  classical
  rw [cubeGrid, ← Set.image_univ]
  calc
    ((fun q : κ → Fin (n + 1) => fun i => (q i : ℝ) / n) '' Set.univ).ncard
        ≤ (Set.univ : Set (κ → Fin (n + 1))).ncard := Set.ncard_image_le Set.finite_univ
    _ = Nat.card (κ → Fin (n + 1)) := Set.ncard_univ _
    _ = (n + 1) ^ Fintype.card κ := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_fin]

/-- The regular grid is a `1/n`-cover of the unit cube. -/
theorem unitCube_isCover_cubeGrid (n : ℕ) (hn : 0 < n) :
    Metric.IsCover (cubeGridRadius n) (unitCube (κ := κ)) (cubeGrid n) := by
  classical
  rw [Metric.isCover_iff_subset_iUnion_closedBall]
  intro x hx
  let q : κ → Fin (n + 1) := fun i =>
    ⟨⌈(n : ℝ) * x i⌉₊, Nat.lt_succ_of_le (Nat.ceil_le.mpr (calc
      (n : ℝ) * x i ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (hx.2 i) (Nat.cast_nonneg n)
      _ = (n : ℝ) := mul_one _))⟩
  let y : κ → ℝ := fun i => (q i : ℝ) / n
  rw [Set.mem_iUnion]
  refine ⟨y, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact ⟨q, rfl⟩
  · rw [Metric.mem_closedBall]
    change dist x y ≤ (n : ℝ)⁻¹
    rw [dist_pi_le_iff (inv_nonneg.mpr (Nat.cast_nonneg n))]
    intro i
    rw [Real.dist_eq]
    have hxn : 0 ≤ (n : ℝ) * x i :=
      mul_nonneg (Nat.cast_nonneg n) (hx.1 i)
    have hlo : (n : ℝ) * x i ≤ (q i : ℕ) := by
      exact Nat.le_ceil _
    have hhi : ((q i : ℕ) : ℝ) < (n : ℝ) * x i + 1 := by
      exact Nat.ceil_lt_add_one hxn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    dsimp only [y]
    rw [abs_of_nonpos]
    · rw [neg_sub, inv_eq_one_div]
      have hxdiv : x i = ((n : ℝ) * x i) / n := by
        rw [mul_div_cancel_left₀ _ hnR.ne']
      rw [hxdiv, ← sub_div, div_le_div_iff_of_pos_right hnR]
      linarith
    · apply sub_nonpos.mpr
      apply (le_div_iff₀ hnR).mpr
      simpa [q, mul_comm] using hlo

/-- Coordinatewise projection onto the parameter cube. -/
def cubeProjection (x : κ → ℝ) : κ → ℝ :=
  fun i => Set.projIcc 0 1 zero_le_one (x i)

@[simp]
theorem cubeProjection_mem_unitCube (x : κ → ℝ) :
    cubeProjection x ∈ unitCube := by
  exact ⟨fun i => (Set.projIcc 0 1 zero_le_one (x i)).2.1,
    fun i => (Set.projIcc 0 1 zero_le_one (x i)).2.2⟩

@[simp]
theorem cubeProjection_eq_self {x : κ → ℝ} (hx : x ∈ unitCube) :
    cubeProjection x = x := by
  funext i
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hx.1 i, hx.2 i⟩)

/-- Coordinatewise projection onto a finite cube is a contraction for the sup metric. -/
theorem lipschitzWith_cubeProjection :
    LipschitzWith 1 (cubeProjection (κ := κ)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  norm_num
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  calc
    dist (cubeProjection x i) (cubeProjection y i) ≤ dist (x i) (y i) :=
      (LipschitzWith.projIcc zero_le_one).dist_le_mul (x i) (y i) |>.trans_eq (one_mul _)
    _ ≤ dist x y := (dist_pi_le_iff dist_nonneg).mp le_rfl i

/-- A finite family of uniformly Lipschitz charts covering a frontier. -/
structure LipschitzBoundaryCover (S : Set E) where
  /-- Number of boundary pieces. -/
  pieces : ℕ
  /-- A common Lipschitz constant. -/
  K : ℝ≥0
  /-- Boundary charts. -/
  chart : Fin pieces → (κ → ℝ) → E
  lipschitz : ∀ j, LipschitzWith K (chart j)
  covers : frontier S ⊆ ⋃ j, chart j '' unitCube

/-- A finite family of `C¹` cube charts gives a Lipschitz boundary cover.  The
charts are extended to the whole parameter space by coordinatewise projection
onto the cube; compactness supplies one common Lipschitz constant. -/
noncomputable def LipschitzBoundaryCover.ofContDiff
    {J : Type*} [Fintype J] {S : Set E}
    (chart : J → (κ → ℝ) → E)
    (smooth : ∀ j, ContDiff ℝ 1 (chart j))
    (covers : frontier S ⊆ ⋃ j, chart j '' unitCube) :
    LipschitzBoundaryCover (κ := κ) S := by
  classical
  have hconv : Convex ℝ (unitCube (κ := κ)) := convex_Icc 0 1
  have hcompact : IsCompact (unitCube (κ := κ)) := isCompact_Icc
  choose K hK using fun j =>
    (smooth j).contDiffOn.exists_lipschitzOnWith one_ne_zero hconv hcompact
  let Kmax : ℝ≥0 := Finset.univ.sup K
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine
    { pieces := Fintype.card J
      K := Kmax
      chart := fun i x => chart (e.symm i) (cubeProjection x)
      lipschitz := fun i => ?_
      covers := ?_ }
  · apply (show LipschitzWith (K (e.symm i))
        (fun x => chart (e.symm i) (cubeProjection x)) from ?_).weaken
      (Finset.le_sup (f := K) (Finset.mem_univ (e.symm i)))
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    apply (hK (e.symm i)).dist_le_mul
      (cubeProjection x) (cubeProjection_mem_unitCube x)
      (cubeProjection y) (cubeProjection_mem_unitCube y) |>.trans
    gcongr
    simpa using (lipschitzWith_cubeProjection (κ := κ)).dist_le_mul x y
  · intro x hx
    have hx' := covers hx
    simp only [Set.mem_iUnion, Set.mem_image] at hx' ⊢
    obtain ⟨j, u, hu, rfl⟩ := hx'
    refine ⟨e j, u, hu, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [cubeProjection_eq_self hu]

/-- Reuse a boundary cover along an inclusion of frontiers. -/
def LipschitzBoundaryCover.of_frontier_subset {S T : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S)
    (h : frontier T ⊆ frontier S) : LipschitzBoundaryCover (κ := κ) T where
  pieces := data.pieces
  K := data.K
  chart := data.chart
  lipschitz := data.lipschitz
  covers := h.trans data.covers

/-- Append two finite chart families. This is the basic closure operation used
for finite unions and intersections. -/
def LipschitzBoundaryCover.appendOfFrontierSubset {S T U : Set E}
    (left : LipschitzBoundaryCover (κ := κ) S)
    (right : LipschitzBoundaryCover (κ := κ) T)
    (hU : frontier U ⊆ frontier S ∪ frontier T) :
    LipschitzBoundaryCover (κ := κ) U where
  pieces := left.pieces + right.pieces
  K := max left.K right.K
  chart := Fin.append left.chart right.chart
  lipschitz := fun j => Fin.addCases
    (fun i => by
      rw [Fin.append_left]
      exact (left.lipschitz i).weaken (le_max_left _ _))
    (fun i => by
      rw [Fin.append_right]
      exact (right.lipschitz i).weaken (le_max_right _ _)) j
  covers := by
    classical
    intro x hx
    rcases hU hx with hxS | hxT
    · have h := left.covers hxS
      simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
      obtain ⟨i, u, hu, hiu⟩ := h
      exact ⟨Fin.castAdd right.pieces i, u, hu, by
        rw [Fin.append_left]
        exact hiu⟩
    · have h := right.covers hxT
      simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
      obtain ⟨i, u, hu, hiu⟩ := h
      exact ⟨Fin.natAdd left.pieces i, u, hu, by
        rw [Fin.append_right]
        exact hiu⟩

/-- Finite unions preserve finite Lipschitz boundary covers. -/
def LipschitzBoundaryCover.union {S T : Set E}
    (left : LipschitzBoundaryCover (κ := κ) S)
    (right : LipschitzBoundaryCover (κ := κ) T) :
    LipschitzBoundaryCover (κ := κ) (S ∪ T) :=
  left.appendOfFrontierSubset right <| fun x hx => by
    rcases frontier_union_subset S T hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr hx.2

/-- Finite intersections preserve finite Lipschitz boundary covers. -/
def LipschitzBoundaryCover.inter {S T : Set E}
    (left : LipschitzBoundaryCover (κ := κ) S)
    (right : LipschitzBoundaryCover (κ := κ) T) :
    LipschitzBoundaryCover (κ := κ) (S ∩ T) :=
  left.appendOfFrontierSubset right <| fun x hx => by
    rcases frontier_inter_subset S T hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr hx.2

/-- Intersect with a set whose boundary inside `closure S` has its own finite
Lipschitz chart family. This is the form used for sign chambers: only the
bounded cut of the coordinate hyperplane, not the whole hyperplane, is charted. -/
def LipschitzBoundaryCover.interOfLipschitzCut {S H : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S)
    (pieces : ℕ) (K : ℝ≥0) (chart : Fin pieces → (κ → ℝ) → E)
    (hlip : ∀ j, LipschitzWith K (chart j))
    (hcut : closure S ∩ frontier H ⊆ ⋃ j, chart j '' unitCube) :
    LipschitzBoundaryCover (κ := κ) (S ∩ H) where
  pieces := data.pieces + pieces
  K := max data.K K
  chart := Fin.append data.chart chart
  lipschitz := fun j => Fin.addCases
    (fun i => by
      rw [Fin.append_left]
      exact (data.lipschitz i).weaken (le_max_left _ _))
    (fun i => by
      rw [Fin.append_right]
      exact (hlip i).weaken (le_max_right _ _)) j
  covers := by
    classical
    intro x hx
    rcases frontier_inter_subset S H hx with hx | hx
    · have h := data.covers hx.1
      simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
      obtain ⟨i, u, hu, hiu⟩ := h
      exact ⟨Fin.castAdd pieces i, u, hu, by
        rw [Fin.append_left]
        exact hiu⟩
    · have h := hcut hx
      simp only [Set.mem_iUnion, Set.mem_image] at h ⊢
      obtain ⟨i, u, hu, hiu⟩ := h
      exact ⟨Fin.natAdd data.pieces i, u, hu, by
        rw [Fin.append_right]
        exact hiu⟩

section CoordinateSignChambers

/-- The nonnegative coordinate half-space. -/
def coordinateNonnegative {k : ℕ} (i : Fin (k + 1)) :
    Set (Fin (k + 1) → ℝ) := {x | 0 ≤ x i}

/-- The positive coordinate half-space. -/
def coordinatePositive {k : ℕ} (i : Fin (k + 1)) :
    Set (Fin (k + 1) → ℝ) := {x | 0 < x i}

/-- The nonpositive coordinate half-space. -/
def coordinateNonpositive {k : ℕ} (i : Fin (k + 1)) :
    Set (Fin (k + 1) → ℝ) := {x | x i ≤ 0}

/-- The negative coordinate half-space. -/
def coordinateNegative {k : ℕ} (i : Fin (k + 1)) :
    Set (Fin (k + 1) → ℝ) := {x | x i < 0}

private theorem frontier_coordinateNonnegative {k : ℕ} (i : Fin (k + 1)) :
    frontier (coordinateNonnegative i) = {x | x i = 0} := by
  let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : Function.Surjective e := fun x => ⟨fun _ => x, rfl⟩
  change frontier (e ⁻¹' Set.Ici 0) = e ⁻¹' {0}
  rw [e.frontier_preimage he, frontier_Ici]

private theorem frontier_coordinatePositive {k : ℕ} (i : Fin (k + 1)) :
    frontier (coordinatePositive i) = {x | x i = 0} := by
  let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : Function.Surjective e := fun x => ⟨fun _ => x, rfl⟩
  change frontier (e ⁻¹' Set.Ioi 0) = e ⁻¹' {0}
  rw [e.frontier_preimage he, frontier_Ioi]

private theorem frontier_coordinateNonpositive {k : ℕ} (i : Fin (k + 1)) :
    frontier (coordinateNonpositive i) = {x | x i = 0} := by
  let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : Function.Surjective e := fun x => ⟨fun _ => x, rfl⟩
  change frontier (e ⁻¹' Set.Iic 0) = e ⁻¹' {0}
  rw [e.frontier_preimage he, frontier_Iic]

private theorem frontier_coordinateNegative {k : ℕ} (i : Fin (k + 1)) :
    frontier (coordinateNegative i) = {x | x i = 0} := by
  let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he : Function.Surjective e := fun x => ⟨fun _ => x, rfl⟩
  change frontier (e ⁻¹' Set.Iio 0) = e ⁻¹' {0}
  rw [e.frontier_preimage he, frontier_Iio]

private def hyperplaneChart {k : ℕ} (i : Fin (k + 1)) (R : ℝ)
    (u : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  i.insertNth 0 (fun j => R * (2 * u j - 1))

private theorem hyperplaneChart_lipschitz {k : ℕ} (i : Fin (k + 1))
    {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith (⟨2 * R, mul_nonneg (by norm_num) hR⟩ : ℝ≥0)
      (hyperplaneChart i R) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  unfold hyperplaneChart
  rw [Fin.dist_insertNth_insertNth, dist_self, max_eq_right dist_nonneg]
  change dist (fun j => R * (2 * x j - 1)) (fun j => R * (2 * y j - 1)) ≤
    (2 * R) * dist x y
  rw [dist_pi_le_iff (mul_nonneg (mul_nonneg (by norm_num) hR) dist_nonneg)]
  intro j
  rw [Real.dist_eq]
  have hj : |x j - y j| ≤ dist x y := by
    have h := (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).mp le_rfl j
    simpa only [Real.dist_eq] using h
  calc
    |R * (2 * x j - 1) - R * (2 * y j - 1)| =
        (2 * R) * |x j - y j| := by
      rw [show R * (2 * x j - 1) - R * (2 * y j - 1) =
          (2 * R) * (x j - y j) by ring,
        abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hR)]
    _ ≤ (2 * R) * dist x y :=
      mul_le_mul_of_nonneg_left hj (mul_nonneg (by norm_num) hR)

private theorem mem_image_hyperplaneChart_of_mem_closedBall {k : ℕ}
    (i : Fin (k + 1)) {R : ℝ} (hR : 0 < R) {x : Fin (k + 1) → ℝ}
    (hx : x ∈ Metric.closedBall 0 R) (hxi : x i = 0) :
    x ∈ hyperplaneChart i R '' unitCube := by
  let u : Fin k → ℝ := fun j => (x (i.succAbove j) / R + 1) / 2
  have hxnorm : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have hcoord (j : Fin k) : |x (i.succAbove j)| ≤ R := by
    calc
      |x (i.succAbove j)| = ‖x (i.succAbove j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl _
      _ ≤ R := hxnorm
  have hu : u ∈ unitCube := by
    constructor <;> intro j
    · have hj := (abs_le.mp (hcoord j)).1
      have hj' : -1 ≤ x (i.succAbove j) / R :=
        (le_div_iff₀ hR).mpr (by linarith)
      dsimp only [u]
      apply div_nonneg <;> linarith
    · have hj := (abs_le.mp (hcoord j)).2
      have hj' : x (i.succAbove j) / R ≤ 1 := (div_le_one hR).mpr hj
      dsimp only [u]
      apply (div_le_one (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
  refine ⟨u, hu, ?_⟩
  funext j
  induction j using i.succAboveCases
  · simpa [hyperplaneChart] using hxi.symm
  · simp only [hyperplaneChart, Fin.insertNth_apply_succAbove, u]
    field_simp
    ring

/-- Intersecting a bounded Lipschitz region in `ℝ^(k+1)` with any set whose
frontier lies in a coordinate hyperplane preserves the boundary-cover
property. This includes all open and closed coordinate sign half-spaces. -/
noncomputable def LipschitzBoundaryCover.interCoordinateHalfSpace {k : ℕ}
    {S H : Set (Fin (k + 1) → ℝ)}
    (data : LipschitzBoundaryCover (κ := Fin k) S) (hS : IsBounded S)
    (i : Fin (k + 1)) (hH : frontier H ⊆ {x | x i = 0}) :
    LipschitzBoundaryCover (κ := Fin k) (S ∩ H) := by
  classical
  let hex := hS.closure.subset_closedBall_lt 0 0
  let R : ℝ := Classical.choose hex
  have hR : 0 < R := (Classical.choose_spec hex).1
  have hSR : closure S ⊆ Metric.closedBall 0 R := (Classical.choose_spec hex).2
  let K : ℝ≥0 := ⟨2 * R, mul_nonneg (by norm_num) hR.le⟩
  let chart : Fin 1 → (Fin k → ℝ) → (Fin (k + 1) → ℝ) :=
    fun _ => hyperplaneChart i R
  apply data.interOfLipschitzCut 1 K chart
  · intro j
    exact hyperplaneChart_lipschitz i hR.le
  · intro x hx
    rw [Set.mem_iUnion]
    refine ⟨0, ?_⟩
    exact mem_image_hyperplaneChart_of_mem_closedBall i hR (hSR hx.1) (hH hx.2)

/-- Restriction to a nonnegative coordinate sign chamber. -/
noncomputable def LipschitzBoundaryCover.interCoordinateNonnegative {k : ℕ}
    {S : Set (Fin (k + 1) → ℝ)}
    (data : LipschitzBoundaryCover (κ := Fin k) S) (hS : IsBounded S)
    (i : Fin (k + 1)) :
    LipschitzBoundaryCover (κ := Fin k) (S ∩ coordinateNonnegative i) :=
  data.interCoordinateHalfSpace hS i (frontier_coordinateNonnegative i).le

/-- Restriction to a positive coordinate sign chamber. -/
noncomputable def LipschitzBoundaryCover.interCoordinatePositive {k : ℕ}
    {S : Set (Fin (k + 1) → ℝ)}
    (data : LipschitzBoundaryCover (κ := Fin k) S) (hS : IsBounded S)
    (i : Fin (k + 1)) :
    LipschitzBoundaryCover (κ := Fin k) (S ∩ coordinatePositive i) :=
  data.interCoordinateHalfSpace hS i (frontier_coordinatePositive i).le

/-- Restriction to a nonpositive coordinate sign chamber. -/
noncomputable def LipschitzBoundaryCover.interCoordinateNonpositive {k : ℕ}
    {S : Set (Fin (k + 1) → ℝ)}
    (data : LipschitzBoundaryCover (κ := Fin k) S) (hS : IsBounded S)
    (i : Fin (k + 1)) :
    LipschitzBoundaryCover (κ := Fin k) (S ∩ coordinateNonpositive i) :=
  data.interCoordinateHalfSpace hS i (frontier_coordinateNonpositive i).le

/-- Restriction to a negative coordinate sign chamber. -/
noncomputable def LipschitzBoundaryCover.interCoordinateNegative {k : ℕ}
    {S : Set (Fin (k + 1) → ℝ)}
    (data : LipschitzBoundaryCover (κ := Fin k) S) (hS : IsBounded S)
    (i : Fin (k + 1)) :
    LipschitzBoundaryCover (κ := Fin k) (S ∩ coordinateNegative i) :=
  data.interCoordinateHalfSpace hS i (frontier_coordinateNegative i).le

end CoordinateSignChambers

/-- Centers obtained by scaling the images of a cube grid in every boundary chart. -/
def LipschitzBoundaryCover.scaledCenters {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (t : ℝ) (n : ℕ) : Set E :=
  ⋃ j, (fun u => t • data.chart j u) '' cubeGrid n

private theorem LipschitzBoundaryCover.scaledCenters_finite {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (t : ℝ) (n : ℕ) :
    (data.scaledCenters t n).Finite := by
  apply Set.Finite.iUnion Set.finite_univ
  · intro j _
    exact (cubeGrid_finite n).image _
  · intro j hj
    exact (hj (Set.mem_univ j)).elim

/-- The scaled grid has at most `M (n+1)^k` centers for `M` charts. -/
theorem LipschitzBoundaryCover.scaledCenters_ncard_le {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (t : ℝ) (n : ℕ) :
    (data.scaledCenters t n).ncard ≤
      data.pieces * (n + 1) ^ Fintype.card κ := by
  classical
  calc
    (data.scaledCenters t n).ncard
        ≤ ∑ j : Fin data.pieces,
            ((fun u => t • data.chart j u) '' cubeGrid n).ncard := by
          exact ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _j : Fin data.pieces, (n + 1) ^ Fintype.card κ := by
      exact Finset.sum_le_sum fun j _ =>
        (Set.ncard_image_le (cubeGrid_finite n)).trans (cubeGrid_ncard_le n)
    _ = data.pieces * (n + 1) ^ Fintype.card κ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

private theorem frontier_smul_eq (S : Set E) {t : ℝ} (ht : t ≠ 0) :
    frontier (t • S) = t • frontier S := by
  let u : ℝˣ := Units.mk0 t ht
  have h := (isHomeomorph_smul u : IsHomeomorph fun x : E => u • x).image_frontier S
  simpa only [u, Units.smul_def, Units.val_mk0, Set.image_smul] using h.symm

/-- If `n ≥ t > 0`, the scaled boundary is covered by the scaled chart-grid
centers with the original (unscaled) Lipschitz radius. -/
theorem LipschitzBoundaryCover.isCover_scaledFrontier {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (t : ℝ) (n : ℕ)
    (ht : 0 < t) (hn : 0 < n) (htn : t ≤ n) :
    Metric.IsCover data.K (frontier (t • S)) (data.scaledCenters t n) := by
  classical
  rw [Metric.isCover_iff_subset_iUnion_closedBall]
  intro x hx
  rw [frontier_smul_eq S ht.ne'] at hx
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hyfront, rfl⟩ := hx
  have hychart := data.covers hyfront
  simp only [Set.mem_iUnion, Set.mem_image] at hychart
  obtain ⟨j, u, hu, rfl⟩ := hychart
  have hugrid := (Metric.isCover_iff_subset_iUnion_closedBall.mp
    (unitCube_isCover_cubeGrid n hn)) hu
  simp only [Set.mem_iUnion] at hugrid
  obtain ⟨q, hqgrid, huq⟩ := hugrid
  let z : E := t • data.chart j q
  rw [Set.mem_iUnion]
  refine ⟨z, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · rw [LipschitzBoundaryCover.scaledCenters, Set.mem_iUnion]
    exact ⟨j, ⟨q, hqgrid, rfl⟩⟩
  · rw [Metric.mem_closedBall]
    dsimp only [z]
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht]
    calc
      t * dist (data.chart j u) (data.chart j q)
          ≤ t * ((data.K : ℝ) * dist u q) := by
            gcongr
            exact (data.lipschitz j).dist_le_mul u q
      _ ≤ t * ((data.K : ℝ) * (n : ℝ)⁻¹) := by
            gcongr
            exact Metric.mem_closedBall.mp huq
      _ ≤ data.K := by
        have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        have hK : (0 : ℝ) ≤ data.K := data.K.2
        calc
          t * ((data.K : ℝ) * (n : ℝ)⁻¹) = (t / n) * data.K := by ring
          _ ≤ 1 * data.K := by
            gcongr
            exact (div_le_one hnR).mpr htn
          _ = data.K := one_mul _

/-- The explicit Davenport constant attached to a lattice basis and a finite
Lipschitz boundary cover. -/
def LipschitzBoundaryCover.davenportConstant {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (b : Basis ι ℤ L) : ℝ :=
  (data.pieces : ℝ) * 3 ^ Fintype.card κ *
    affineLatticeLocalMultiplicity L b
      ((data.K : ℝ) + fundamentalCellRadius L b)

/-- Quantitative boundary-cell estimate for a dilated Lipschitz boundary. -/
theorem LipschitzBoundaryCover.boundaryCellIndices_ncard_smul_le {S : Set E}
    (data : LipschitzBoundaryCover (κ := κ) S) (b : Basis ι ℤ L)
    (v : E) {t : ℝ} (ht : 1 ≤ t) :
    ((boundaryCellIndices L b v (t • S)).ncard : ℝ) ≤
      data.davenportConstant L b * t ^ Fintype.card κ := by
  classical
  let n : ℕ := ⌈t⌉₊
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn : 0 < n := Nat.ceil_pos.mpr ht0
  have htn : t ≤ (n : ℝ) := Nat.le_ceil t
  let N : Set E := data.scaledCenters t n
  let Q : ℕ := affineLatticeLocalMultiplicity L b
    ((data.K : ℝ) + fundamentalCellRadius L b)
  have hNfinite : N.Finite := data.scaledCenters_finite t n
  have hboundary : (boundaryCellIndices L b v (t • S)).ncard ≤ N.ncard * Q := by
    exact boundaryCellIndices_ncard_le_of_isCover L b v (t • S) data.K N hNfinite
      (data.isCover_scaledFrontier t n ht0 hn htn)
  have hNcard : N.ncard ≤ data.pieces * (n + 1) ^ Fintype.card κ :=
    data.scaledCenters_ncard_le t n
  have hnat : (boundaryCellIndices L b v (t • S)).ncard ≤
      data.pieces * (n + 1) ^ Fintype.card κ * Q :=
    hboundary.trans (Nat.mul_le_mul_right Q hNcard)
  have hnreal : ((n + 1 : ℕ) : ℝ) ≤ 3 * t := by
    have hceil := Nat.ceil_lt_add_one ht0.le
    calc
      ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
      _ ≤ t + 2 := by dsimp only [n]; linarith
      _ ≤ 3 * t := by linarith
  have hpow : (((n + 1) ^ Fintype.card κ : ℕ) : ℝ) ≤
      (3 * t) ^ Fintype.card κ := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 by positivity)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hnreal) _
  calc
    ((boundaryCellIndices L b v (t • S)).ncard : ℝ)
        ≤ ((data.pieces * (n + 1) ^ Fintype.card κ * Q : ℕ) : ℝ) := by
          exact_mod_cast hnat
    _ = (data.pieces : ℝ) * (((n + 1) ^ Fintype.card κ : ℕ) : ℝ) * Q := by
      push_cast
      ring
    _ ≤ (data.pieces : ℝ) * (3 * t) ^ Fintype.card κ * Q := by
      gcongr
    _ = data.davenportConstant L b * t ^ Fintype.card κ := by
      rw [mul_pow]
      simp only [LipschitzBoundaryCover.davenportConstant]
      ring

private theorem measureReal_smul_of_nonneg
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E} (hS : IsBounded S)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real (t • S) = t ^ finrank ℝ E * μ.real S := by
  rw [Measure.real_def, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg ht _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht _), Measure.real_def]

/-- **Quantitative affine-lattice Davenport theorem.** If the frontier of `D`
is covered by finitely many `k`-dimensional Lipschitz charts, then for every
translate `v` and every `t ≥ 1`, the lattice discrepancy is at most `C t^k`.
The displayed constant is independent of `v`. -/
theorem LipschitzBoundaryCover.abs_affineLatticePointCount_smul_sub_main_le
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {D : Set E} (data : LipschitzBoundaryCover (κ := κ) D)
    (b : Basis ι ℤ L) (hD : IsBounded D) (v : E) {t : ℝ} (ht : 1 ≤ t) :
    |(affineLatticePointCount L v (t • D) : ℝ) -
        t ^ finrank ℝ E * μ.real D / ZLattice.covolume L μ| ≤
      data.davenportConstant L b * t ^ Fintype.card κ := by
  rw [← measureReal_smul_of_nonneg μ hD (zero_le_one.trans ht)]
  exact (abs_affineLatticePointCount_sub_volume_div_covolume_le_boundaryCells
    L μ b v (t • D) (hD.smul₀ t)).trans
      (data.boundaryCellIndices_ncard_smul_le L b v ht)

/-- Codimension-one specialization: in real dimension `d`, the error is
`C * t^(d-1)`. -/
theorem LipschitzBoundaryCover.abs_affineLatticePointCount_smul_sub_main_codimOne_le
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {D : Set E} (data : LipschitzBoundaryCover (κ := κ) D)
    (b : Basis ι ℤ L) (hD : IsBounded D)
    (hdim : Fintype.card κ + 1 = finrank ℝ E)
    (v : E) {t : ℝ} (ht : 1 ≤ t) :
    |(affineLatticePointCount L v (t • D) : ℝ) -
        t ^ finrank ℝ E * μ.real D / ZLattice.covolume L μ| ≤
      data.davenportConstant L b * t ^ (finrank ℝ E - 1) := by
  have hk : Fintype.card κ = finrank ℝ E - 1 := by omega
  simpa only [hk] using
    data.abs_affineLatticePointCount_smul_sub_main_le L μ b hD v ht

/-- Big-O form of the quantitative affine-lattice theorem, still uniform in
all affine translates because the same explicit constant works for every `v`. -/
theorem LipschitzBoundaryCover.affineLatticePointCount_smul_isBigO
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {D : Set E} (data : LipschitzBoundaryCover (κ := κ) D)
    (b : Basis ι ℤ L) (hD : IsBounded D) (v : E) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => (affineLatticePointCount L v (t • D) : ℝ) -
        t ^ finrank ℝ E * μ.real D / ZLattice.covolume L μ)
      (fun t : ℝ => t ^ Fintype.card κ) := by
  apply Asymptotics.IsBigO.of_bound (data.davenportConstant L b)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (zero_le_one.trans ht) _)]
  exact data.abs_affineLatticePointCount_smul_sub_main_le L μ b hD v ht

/-- Radial (`x = t^d`) form of Davenport's estimate.  When the charts have
codimension one, the error is `x^(1-1/d)`. -/
theorem LipschitzBoundaryCover.abs_affineLatticePointCount_rpow_sub_main_le
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {D : Set E} (data : LipschitzBoundaryCover (κ := κ) D)
    (b : Basis ι ℤ L) (hD : IsBounded D)
    (hdim : Fintype.card κ + 1 = finrank ℝ E) (v : E)
    {x : ℝ} (hx : 1 ≤ x) :
    |(affineLatticePointCount L v
          (Real.rpow x ((finrank ℝ E : ℝ)⁻¹) • D) : ℝ) -
        x * μ.real D / ZLattice.covolume L μ| ≤
      data.davenportConstant L b *
        Real.rpow x (1 - 1 / (finrank ℝ E : ℝ)) := by
  let d : ℕ := finrank ℝ E
  let k : ℕ := Fintype.card κ
  have hd : 0 < d := by omega
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let t : ℝ := Real.rpow x (d : ℝ)⁻¹
  have ht : 1 ≤ t := Real.one_le_rpow hx (inv_nonneg.mpr (Nat.cast_nonneg d))
  have htd : t ^ d = x := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_inv_rpow hx0 hdR
  have htk : t ^ k = Real.rpow x (1 - 1 / (d : ℝ)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast]
    change Real.rpow (Real.rpow x (d : ℝ)⁻¹) (k : ℝ) = _
    calc
      Real.rpow (Real.rpow x (d : ℝ)⁻¹) (k : ℝ) =
          Real.rpow x ((d : ℝ)⁻¹ * (k : ℝ)) :=
        (Real.rpow_mul hx0 ((d : ℝ)⁻¹) (k : ℝ)).symm
      _ = Real.rpow x (1 - 1 / (d : ℝ)) := by
        congr 1
        have hdim' : k + 1 = d := by simpa only [k, d] using hdim
        have hdimR := congrArg (fun n : ℕ => (n : ℝ)) hdim'
        push_cast at hdimR
        field_simp [hdR]
        nlinarith
  have h := data.abs_affineLatticePointCount_smul_sub_main_le L μ b hD v ht
  change |(affineLatticePointCount L v (t • D) : ℝ) -
      t ^ d * μ.real D / ZLattice.covolume L μ| ≤
    data.davenportConstant L b * t ^ k at h
  simpa only [t, d, k, htd, htk] using h

/-- Big-O radial form, with a constant uniform in the affine translate. -/
theorem LipschitzBoundaryCover.affineLatticePointCount_rpow_isBigO
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {D : Set E} (data : LipschitzBoundaryCover (κ := κ) D)
    (b : Basis ι ℤ L) (hD : IsBounded D)
    (hdim : Fintype.card κ + 1 = finrank ℝ E) (v : E) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => (affineLatticePointCount L v
          (Real.rpow x ((finrank ℝ E : ℝ)⁻¹) • D) : ℝ) -
        (μ.real D / ZLattice.covolume L μ) * x)
      (fun x : ℝ => Real.rpow x
        (1 - 1 / (finrank ℝ E : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (data.davenportConstant L b)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hr : 0 ≤ Real.rpow x (1 - 1 / (finrank ℝ E : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr]
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    data.abs_affineLatticePointCount_rpow_sub_main_le L μ b hD hdim v hx

end LipschitzBoundary

end Discrepancy
end NU.Chebotarev
