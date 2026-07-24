import Submission.NU.LocalTheory.Alternating.Basic

/-!
# The prime-field projective bridge

This file isolates the incidence calculation in Blueprint Lemma 3.3
(`lem:projective-bridge`).  The six named configuration lemmas mirror the six
rows of the table in its proof.  The terminal statement is the rank-one bound
needed before invoking AEJ; no AEJ conclusion is used here.
-/

open scoped Pointwise

namespace NU.LocalTheory

noncomputable section

/-- Homogeneous coordinates in a projective plane.  We retain coordinates
rather than quotienting, because every bridge lemma is a determinant or
proportionality certificate. -/
abbrev ProjectiveCoord (k : Type*) := Fin 3 → k

/-- The coordinate triple `(z:r:s)`. -/
def projectiveCoord {k : Type*} [Zero k] (z r s : k) : ProjectiveCoord k :=
  ![z, r, s]

/-- Equality of projective coordinate triples up to a nonzero scalar. -/
def ProjectivelyEqual {k : Type*} [Field k]
    (v w : ProjectiveCoord k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ w = c • v

/-- The homogeneous `3 × 3` determinant. -/
def projectiveDet {k : Type*} [CommRing k]
    (u v w : ProjectiveCoord k) : k :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Three coordinate triples are collinear when their determinant vanishes. -/
def ProjectivelyCollinear {k : Type*} [CommRing k]
    (u v w : ProjectiveCoord k) : Prop :=
  projectiveDet u v w = 0

/-- Blueprint (3.10): addition and subtraction are sent to projective lines. -/
def IncidenceAxiom {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) : Prop :=
  (∀ a : F, φ a ≠ 0) ∧
    ∀ a b : F,
      ProjectivelyCollinear (φ a) (φ b) (φ (a + b)) ∧
        ProjectivelyCollinear (φ a) (φ b) (φ (a - b))

/-- Blueprint (3.9): the five points of the normalized projective frame. -/
def HasProjectiveFrame {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F) : Prop :=
  ProjectivelyEqual (φ 0) (projectiveCoord 1 0 0) ∧
    ProjectivelyEqual (φ 1) (projectiveCoord 1 0 0) ∧
    ProjectivelyEqual (φ x) (projectiveCoord 1 1 0) ∧
    ProjectivelyEqual (φ y) (projectiveCoord 1 0 1) ∧
    ProjectivelyEqual (φ (1 + x)) (projectiveCoord 0 1 0) ∧
    ProjectivelyEqual (φ (1 + y)) (projectiveCoord 0 0 1)

/-- Blueprint (3.8), the projective linear transform
`(z,r,s) ↦ (zAB-rB-sA, rB(A-1), sA(B-1))`. -/
def projectiveTransform {k : Type*} [CommRing k] (A B : k)
    (v : ProjectiveCoord k) : ProjectiveCoord k :=
  projectiveCoord
    (v 0 * A * B - v 1 * B - v 2 * A)
    (v 1 * B * (A - 1))
    (v 2 * A * (B - 1))

/-- The determinant of the transform in Blueprint (3.8) is
`A² B² (A-1)(B-1)`. -/
theorem projectiveTransform_det {k : Type*} [Field k] (A B : k) :
    Matrix.det !![A * B, -B, -A;
                  0, B * (A - 1), 0;
                  0, 0, A * (B - 1)] =
      A ^ 2 * B ^ 2 * (A - 1) * (B - 1) := by
  simp [Matrix.det_fin_three]
  ring

/-- Consequently the transform is injective under the four nonvanishing
hypotheses used in the bridge proof. -/
theorem projectiveTransform_injective {k : Type*} [Field k] {A B : k}
    (hA : A ≠ 0) (hB : B ≠ 0) (hA1 : A - 1 ≠ 0)
    (hB1 : B - 1 ≠ 0) :
    Function.Injective (projectiveTransform A B) := by
  intro u v huv
  have h0 := congrFun huv 0
  have h1 := congrFun huv 1
  have h2 := congrFun huv 2
  simp only [projectiveTransform, projectiveCoord, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  have huv1 : u 1 = v 1 := by
    apply mul_right_cancel₀ (mul_ne_zero hB hA1)
    simpa [mul_assoc] using h1
  have huv2 : u 2 = v 2 := by
    apply mul_right_cancel₀ (mul_ne_zero hA hB1)
    simpa [mul_assoc] using h2
  have huv0 : u 0 = v 0 := by
    rw [huv1, huv2] at h0
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    simpa [mul_assoc] using h0
  funext i
  fin_cases i
  · exact huv0
  · exact huv1
  · exact huv2

private theorem collinear_scale_first_two
    {k : Type*} [Field k] {u u' v v' w : ProjectiveCoord k}
    (hu : ProjectivelyEqual u u') (hv : ProjectivelyEqual v v')
    (h : ProjectivelyCollinear u v w) :
    ProjectivelyCollinear u' v' w := by
  rcases hu with ⟨c, hc, rfl⟩
  rcases hv with ⟨d, hd, rfl⟩
  unfold ProjectivelyCollinear projectiveDet at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * d * h

private theorem projectivelyEqual_n_one_one
    {k : Type*} [Field k] (u : ProjectiveCoord k) (a : k)
    (hu : u ≠ 0) (h0 : u 0 = a * u 1) (h2 : u 2 = u 1) :
    ProjectivelyEqual u (projectiveCoord a 1 1) := by
  have h1ne : u 1 ≠ 0 := by
    intro h1
    apply hu
    apply funext
    intro i
    fin_cases i <;> simp_all
  refine ⟨(u 1)⁻¹, inv_ne_zero h1ne, ?_⟩
  apply funext
  intro i
  fin_cases i <;> simp [projectiveCoord, h0, h2, h1ne] <;> field_simp

private theorem projectivelyEqual_n_one_zero
    {k : Type*} [Field k] (u : ProjectiveCoord k) (a : k)
    (hu : u ≠ 0) (h0 : u 0 = a * u 1) (h2 : u 2 = 0) :
    ProjectivelyEqual u (projectiveCoord a 1 0) := by
  have h1ne : u 1 ≠ 0 := by
    intro h1
    apply hu
    apply funext
    intro i
    fin_cases i <;> simp_all
  refine ⟨(u 1)⁻¹, inv_ne_zero h1ne, ?_⟩
  apply funext
  intro i
  fin_cases i <;> simp [projectiveCoord, h0, h2, h1ne] <;> field_simp

private theorem projectivelyEqual_n_m_one
    {k : Type*} [Field k] (u : ProjectiveCoord k) (a b : k)
    (hu : u ≠ 0) (h0 : u 0 = a * u 2) (h1 : u 1 = b * u 2) :
    ProjectivelyEqual u (projectiveCoord a b 1) := by
  have h2ne : u 2 ≠ 0 := by
    intro h2
    apply hu
    apply funext
    intro i
    fin_cases i <;> simp_all
  refine ⟨(u 2)⁻¹, inv_ne_zero h2ne, ?_⟩
  apply funext
  intro i
  fin_cases i <;> simp [projectiveCoord, h0, h1, h2ne] <;> field_simp

/-- Incidence configuration 1: `1+x+y` is forced to `(1:1:1)`. -/
theorem incidence_config_one_add_x_add_y {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual (φ (1 + x + y)) (projectiveCoord 1 1 1) := by
  rcases hframe with ⟨h0, h1, hx, hy, h1x, h1y⟩
  have hline1 : ProjectivelyCollinear (projectiveCoord 0 1 0)
      (projectiveCoord 1 0 1) (φ (1 + x + y)) := by
    apply collinear_scale_first_two h1x hy
    exact (hinc.2 (1 + x) y).1
  have hline2 : ProjectivelyCollinear (projectiveCoord 0 0 1)
      (projectiveCoord 1 1 0) (φ (1 + x + y)) := by
    apply collinear_scale_first_two h1y hx
    convert (hinc.2 (1 + y) x).1 using 1 <;> ring
  simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
  have hz : φ (1 + x + y) 0 = φ (1 + x + y) 2 := by
    linear_combination hline1
  have hr : φ (1 + x + y) 1 = φ (1 + x + y) 0 := by
    linear_combination hline2
  have hcoord0 : φ (1 + x + y) 0 = (1 : k) * φ (1 + x + y) 1 := by
    simpa using hr.symm
  have hcoord2 : φ (1 + x + y) 2 = φ (1 + x + y) 1 :=
    hz.symm.trans hr.symm
  exact projectivelyEqual_n_one_one _ 1 (hinc.1 _) hcoord0 hcoord2

/-- Incidence configuration 2: `2+x+y` is forced to `(0:1:1)`. -/
theorem incidence_config_two_add_x_add_y {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual (φ ((2 : F) + x + y)) (projectiveCoord 0 1 1) := by
  rcases hframe with ⟨h0, h1, hx, hy, h1x, h1y⟩
  have ht := incidence_config_one_add_x_add_y φ x y hinc
    ⟨h0, h1, hx, hy, h1x, h1y⟩
  have hline1 : ProjectivelyCollinear (projectiveCoord 1 0 0)
      (projectiveCoord 1 1 1) (φ ((2 : F) + x + y)) := by
    apply collinear_scale_first_two h1 ht
    convert (hinc.2 1 (1 + x + y)).1 using 1 <;> ring
  have hline2 : ProjectivelyCollinear (projectiveCoord 0 1 0)
      (projectiveCoord 0 0 1) (φ ((2 : F) + x + y)) := by
    apply collinear_scale_first_two h1x h1y
    convert (hinc.2 (1 + x) (1 + y)).1 using 1 <;> ring
  simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
  have h2 : φ ((2 : F) + x + y) 2 = φ ((2 : F) + x + y) 1 := by
    linear_combination hline1
  have h0' : φ ((2 : F) + x + y) 0 =
      (0 : k) * φ ((2 : F) + x + y) 1 := by
    simp
    linear_combination hline2
  exact projectivelyEqual_n_one_one _ 0 (hinc.1 _) h0' h2

private theorem incidence_config_n_pair {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) (n : ℤ) :
    ProjectivelyEqual
        (φ (((2 - n : ℤ) : F) + x + y))
        (projectiveCoord (n : k) 1 1) ∧
      ProjectivelyEqual
        (φ (((1 - n : ℤ) : F) + x))
        (projectiveCoord (n : k) 1 0) := by
  rcases hframe with ⟨hzero, hone, hx, hy, h1x, h1y⟩
  let P : ℤ → Prop := fun n =>
    ProjectivelyEqual
        (φ (((2 - n : ℤ) : F) + x + y))
        (projectiveCoord (n : k) 1 1) ∧
      ProjectivelyEqual
        (φ (((1 - n : ℤ) : F) + x))
        (projectiveCoord (n : k) 1 0)
  have hbase : P 0 := by
    constructor
    · simpa [P] using incidence_config_two_add_x_add_y φ x y hinc
        ⟨hzero, hone, hx, hy, h1x, h1y⟩
    · simpa [P] using h1x
  have hsucc : ∀ z : ℤ, P z → P (z + 1) := by
    intro z hz
    let t : F := (((2 - (z + 1) : ℤ) : F) + x + y)
    have ht : ProjectivelyEqual (φ t)
        (projectiveCoord (((z + 1 : ℤ) : k)) 1 1) := by
      have hline1 : ProjectivelyCollinear (projectiveCoord (z : k) 1 0)
          (projectiveCoord 1 0 1) (φ t) := by
        apply collinear_scale_first_two hz.2 hy
        convert (hinc.2 (((1 - z : ℤ) : F) + x) y).1 using 1 <;>
          dsimp [t] <;> push_cast <;> ring
      have hline2 : ProjectivelyCollinear (projectiveCoord (z : k) 1 1)
          (projectiveCoord 1 0 0) (φ t) := by
        apply collinear_scale_first_two hz.1 hone
        convert (hinc.2 (((2 - z : ℤ) : F) + x + y) 1).2 using 1 <;>
          dsimp [t] <;> push_cast <;> ring
      simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
      have h2 : φ t 2 = φ t 1 := by
        linear_combination -hline2
      have h0 : φ t 0 = ((z + 1 : ℤ) : k) * φ t 1 := by
        push_cast
        linear_combination hline1 - hline2
      exact projectivelyEqual_n_one_one _ _ (hinc.1 t) h0 h2
    let s : F := (((1 - (z + 1) : ℤ) : F) + x)
    have hs : ProjectivelyEqual (φ s)
        (projectiveCoord (((z + 1 : ℤ) : k)) 1 0) := by
      have hline1 : ProjectivelyCollinear
          (projectiveCoord (((z + 1 : ℤ) : k)) 1 1)
          (projectiveCoord 0 0 1) (φ s) := by
        apply collinear_scale_first_two ht h1y
        convert (hinc.2 t (1 + y)).2 using 1 <;>
          dsimp [t, s] <;> push_cast <;> ring
      have hline2 : ProjectivelyCollinear (projectiveCoord (z : k) 1 0)
          (projectiveCoord 1 0 0) (φ s) := by
        apply collinear_scale_first_two hz.2 hone
        convert (hinc.2 (((1 - z : ℤ) : F) + x) 1).2 using 1 <;>
          dsimp [s] <;> push_cast <;> ring
      simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
      have h2 : φ s 2 = 0 := by
        linear_combination hline2
      have h0 : φ s 0 = ((z + 1 : ℤ) : k) * φ s 1 := by
        push_cast
        linear_combination hline1
      exact projectivelyEqual_n_one_zero _ _ (hinc.1 s) h0 h2
    exact ⟨ht, hs⟩
  have hpred : ∀ z : ℤ, P z → P (z - 1) := by
    intro z hz
    let s : F := (((1 - (z - 1) : ℤ) : F) + x)
    have hs : ProjectivelyEqual (φ s)
        (projectiveCoord (((z - 1 : ℤ) : k)) 1 0) := by
      have hline1 : ProjectivelyCollinear (projectiveCoord (z : k) 1 1)
          (projectiveCoord 1 0 1) (φ s) := by
        apply collinear_scale_first_two hz.1 hy
        convert (hinc.2 (((2 - z : ℤ) : F) + x + y) y).2 using 1 <;>
          dsimp [s] <;> push_cast <;> ring
      have hline2 : ProjectivelyCollinear (projectiveCoord (z : k) 1 0)
          (projectiveCoord 1 0 0) (φ s) := by
        apply collinear_scale_first_two hz.2 hone
        convert (hinc.2 (((1 - z : ℤ) : F) + x) 1).1 using 1 <;>
          dsimp [s] <;> push_cast <;> ring
      simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
      have h2 : φ s 2 = 0 := hline2
      have h0 : φ s 0 = ((z - 1 : ℤ) : k) * φ s 1 := by
        push_cast
        linear_combination hline1 + hline2
      exact projectivelyEqual_n_one_zero _ _ (hinc.1 s) h0 h2
    let t : F := (((2 - (z - 1) : ℤ) : F) + x + y)
    have ht : ProjectivelyEqual (φ t)
        (projectiveCoord (((z - 1 : ℤ) : k)) 1 1) := by
      have hline1 : ProjectivelyCollinear
          (projectiveCoord (((z - 1 : ℤ) : k)) 1 0)
          (projectiveCoord 0 0 1) (φ t) := by
        apply collinear_scale_first_two hs h1y
        convert (hinc.2 s (1 + y)).1 using 1 <;>
          dsimp [s, t] <;> push_cast <;> ring
      have hline2 : ProjectivelyCollinear (projectiveCoord (z : k) 1 1)
          (projectiveCoord 1 0 0) (φ t) := by
        apply collinear_scale_first_two hz.1 hone
        convert (hinc.2 (((2 - z : ℤ) : F) + x + y) 1).1 using 1 <;>
          dsimp [t] <;> push_cast <;> ring
      simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
      have h2 : φ t 2 = φ t 1 := by
        linear_combination -hline2
      have h0 : φ t 0 = ((z - 1 : ℤ) : k) * φ t 1 := by
        push_cast
        linear_combination hline1
      exact projectivelyEqual_n_one_one _ _ (hinc.1 t) h0 h2
    exact ⟨ht, hs⟩
  exact Int.inductionOn' n 0 hbase
    (fun z _ hz => hsucc z hz)
    (fun z _ hz => hpred z hz)

/-- Incidence configuration 3: `(2-n)+x+y` is forced to `(n:1:1)`.
Integer coefficients make the statement valid in finite characteristic. -/
theorem incidence_config_n_one_one {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F) (n : ℤ)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual
      (φ (((2 - n : ℤ) : F) + x + y))
      (projectiveCoord (n : k) 1 1) := by
  exact (incidence_config_n_pair φ x y hinc hframe n).1

/-- Incidence configuration 4: `(1-n)+x` is forced to `(n:1:0)`. -/
theorem incidence_config_n_one_zero {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F) (n : ℤ)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual
      (φ (((1 - n : ℤ) : F) + x))
      (projectiveCoord (n : k) 1 0) := by
  exact (incidence_config_n_pair φ x y hinc hframe n).2

/-- Incidence configuration 5: `(1+m-n)+mx+y` is forced to `(n:m:1)`. -/
theorem incidence_config_n_m_one {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F) (m n : ℤ)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual
      (φ (((1 + m - n : ℤ) : F) + (m : F) * x + y))
      (projectiveCoord (n : k) (m : k) 1) := by
  rcases hframe with ⟨hzero, hone, hx, hy, h1x, h1y⟩
  let Q : ℤ → Prop := fun m => ∀ n : ℤ,
    ProjectivelyEqual
      (φ (((1 + m - n : ℤ) : F) + (m : F) * x + y))
      (projectiveCoord (n : k) (m : k) 1)
  have hbase : Q 1 := by
    intro n
    dsimp [Q]
    convert incidence_config_n_one_one φ x y n hinc
      ⟨hzero, hone, hx, hy, h1x, h1y⟩ using 1 <;> push_cast <;> ring
  have hsucc : ∀ z : ℤ, Q z → Q (z + 1) := by
    intro z hz n
    let t : F := (((1 + (z + 1) - n : ℤ) : F) + ((z + 1 : ℤ) : F) * x + y)
    have hline1 : ProjectivelyCollinear
        (projectiveCoord (n : k) (z : k) 1) (projectiveCoord 0 1 0) (φ t) := by
      apply collinear_scale_first_two (hz n) h1x
      convert (hinc.2
        (((1 + z - n : ℤ) : F) + (z : F) * x + y) (1 + x)).1 using 1 <;>
        dsimp [t] <;> push_cast <;> ring
    have hline2 : ProjectivelyCollinear
        (projectiveCoord ((n - 1 : ℤ) : k) (z : k) 1)
        (projectiveCoord 1 1 0) (φ t) := by
      apply collinear_scale_first_two (hz (n - 1)) hx
      convert (hinc.2
        (((1 + z - (n - 1) : ℤ) : F) + (z : F) * x + y) x).1 using 1 <;>
        dsimp [t] <;> push_cast <;> ring
    simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
    have h0 : φ t 0 = (n : k) * φ t 2 := by
      linear_combination -hline1
    have h1 : φ t 1 = ((z + 1 : ℤ) : k) * φ t 2 := by
      push_cast
      linear_combination hline2 - hline1
    exact projectivelyEqual_n_m_one _ _ _ (hinc.1 t) h0 h1
  have hpred : ∀ z : ℤ, Q z → Q (z - 1) := by
    intro z hz n
    let t : F := (((1 + (z - 1) - n : ℤ) : F) + ((z - 1 : ℤ) : F) * x + y)
    have hline1 : ProjectivelyCollinear
        (projectiveCoord (n : k) (z : k) 1) (projectiveCoord 0 1 0) (φ t) := by
      apply collinear_scale_first_two (hz n) h1x
      convert (hinc.2
        (((1 + z - n : ℤ) : F) + (z : F) * x + y) (1 + x)).2 using 1 <;>
        dsimp [t] <;> push_cast <;> ring
    have hline2 : ProjectivelyCollinear
        (projectiveCoord ((n + 1 : ℤ) : k) (z : k) 1)
        (projectiveCoord 1 1 0) (φ t) := by
      apply collinear_scale_first_two (hz (n + 1)) hx
      convert (hinc.2
        (((1 + z - (n + 1) : ℤ) : F) + (z : F) * x + y) x).2 using 1 <;>
        dsimp [t] <;> push_cast <;> ring
    simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
    have h0 : φ t 0 = (n : k) * φ t 2 := by
      linear_combination -hline1
    have h1 : φ t 1 = ((z - 1 : ℤ) : k) * φ t 2 := by
      push_cast
      linear_combination hline2 - hline1
    exact projectivelyEqual_n_m_one _ _ _ (hinc.1 t) h0 h1
  exact Int.inductionOn' m 1 hbase
    (fun z _ hz => hsucc z hz)
    (fun z _ hz => hpred z hz) n

private theorem projectivelyEqual_n_m_zero
    {k : Type*} [Field k] (u : ProjectiveCoord k) (n m : k)
    (hu : u ≠ 0) (hn : n ≠ 0)
    (h1 : n * u 1 = m * u 0) (h2 : u 2 = 0) :
    ProjectivelyEqual u (projectiveCoord n m 0) := by
  have h0ne : u 0 ≠ 0 := by
    intro h0
    have hu1 : u 1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hn
      simpa [h0] using h1
    apply hu
    funext i
    fin_cases i <;> simp_all
  refine ⟨n * (u 0)⁻¹, mul_ne_zero hn (inv_ne_zero h0ne), ?_⟩
  funext i
  fin_cases i
  · simp [projectiveCoord, h0ne]
  · simp only [projectiveCoord, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    field_simp
    exact h1.symm
  · simp [projectiveCoord, h2]

/-- Incidence configuration 6: `(m-n)+mx` is forced to `(n:m:0)`.

The hypothesis `(n : k) ≠ 0` excludes the degenerate target `(0:0:0)` (the
statement is false at `m = n = 0`, e.g. over `𝔽₈/𝔽₂`); the blueprint's
terminal use of this configuration only requires the `(n : k) ≠ 0` case
(orchestrator repair, prover counterexample 2026-07-23). -/
theorem incidence_config_n_m_zero {F k : Type*} [Field F] [Field k]
    (φ : F → ProjectiveCoord k) (x y : F) (m n : ℤ)
    (hn : (n : k) ≠ 0)
    (hinc : IncidenceAxiom φ) (hframe : HasProjectiveFrame φ x y) :
    ProjectivelyEqual
      (φ (((m - n : ℤ) : F) + (m : F) * x))
      (projectiveCoord (n : k) (m : k) 0) := by
  let t : F := (((m - n : ℤ) : F) + (m : F) * x)
  have hnm := incidence_config_n_m_one φ x y m n hinc hframe
  have hzerozero := incidence_config_n_m_one φ x y 0 0 hinc hframe
  have hline1 : ProjectivelyCollinear
      (projectiveCoord (n : k) (m : k) 1)
      (projectiveCoord ((0 : ℤ) : k) ((0 : ℤ) : k) 1) (φ t) := by
    apply collinear_scale_first_two hnm hzerozero
    convert (hinc.2
      (((1 + m - n : ℤ) : F) + (m : F) * x + y)
      (((1 + 0 - 0 : ℤ) : F) + (0 : F) * x + y)).2 using 1 <;>
      dsimp [t] <;> push_cast <;> ring
  have hnm1 := incidence_config_n_m_one φ x y (m + 1) n hinc hframe
  have hzeroone := incidence_config_n_m_one φ x y 1 0 hinc hframe
  have hline2 : ProjectivelyCollinear
      (projectiveCoord (n : k) ((m + 1 : ℤ) : k) 1)
      (projectiveCoord ((0 : ℤ) : k) ((1 : ℤ) : k) 1) (φ t) := by
    apply collinear_scale_first_two hnm1 hzeroone
    convert (hinc.2
      (((1 + (m + 1) - n : ℤ) : F) + ((m + 1 : ℤ) : F) * x + y)
      (((1 + 1 - 0 : ℤ) : F) + (1 : F) * x + y)).2 using 1 <;>
      dsimp [t] <;> push_cast <;> ring
  simp [ProjectivelyCollinear, projectiveDet, projectiveCoord] at hline1 hline2
  have h2 : φ t 2 = 0 := by
    apply mul_left_cancel₀ hn
    push_cast at hline2
    linear_combination hline2 - hline1
  have h1 : (n : k) * φ t 1 = (m : k) * φ t 0 := by
    linear_combination -hline1
  exact projectivelyEqual_n_m_zero _ _ _ (hinc.1 t) hn h1 h2

/-- Blueprint (3.6): a unit is nonrigid modulo `T` when it is outside `T`
and `1+x` lies in neither `T` nor `xT`. -/
def IsTNonrigid {F : Type*} [Field F] (T : Set F) (x : Fˣ) : Prop :=
  (x : F) ∉ T ∧
    (1 + (x : F)) ∉ T ∪ (x : F) • T

/-- Evaluation of a character pair in the affine coefficient plane. -/
def characterPairValue {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) (x : Fˣ) : ZMod n × ZMod n :=
  (p (Additive.ofMul x), q (Additive.ofMul x))

/-- The image of `⟨T,B(T)⟩/T` inside `𝔽_ℓ²`.  Since `T` is the common
kernel, adjoining `T` does not change this span. -/
def nonrigidQuotientImage {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) :
    Submodule (ZMod ℓ) (ZMod ℓ × ZMod ℓ) :=
  Submodule.span (ZMod ℓ)
    {z | ∃ x : Fˣ,
      IsTNonrigid (commonKernelCarrier p q) x ∧
        z = characterPairValue p q x}

private def characterFieldValue {F : Type*} [Field F] {n : ℕ}
    (p : MulCharacter F n) (a : F) : ZMod n := by
  classical
  exact if ha : a = 0 then 0 else p (Additive.ofMul (Units.mk0 a ha))

private theorem characterFieldValue_zero {F : Type*} [Field F] {n : ℕ}
    (p : MulCharacter F n) : characterFieldValue p 0 = 0 := by
  simp [characterFieldValue]

private theorem characterFieldValue_one {F : Type*} [Field F] {n : ℕ}
    (p : MulCharacter F n) : characterFieldValue p 1 = 0 := by
  simp [characterFieldValue]

private theorem characterFieldValue_unit {F : Type*} [Field F] {n : ℕ}
    (p : MulCharacter F n) (x : Fˣ) :
    characterFieldValue p (x : F) = p (Additive.ofMul x) := by
  simp only [characterFieldValue, Units.ne_zero, ↓reduceDIte]
  congr 2
  apply Units.ext
  rfl

private theorem character_kills_neg_one_pb
    {F : Type*} [Field F] {ℓ : ℕ} (hℓodd : Odd ℓ)
    (p : MulCharacter F ℓ) :
    p (Additive.ofMul (-1 : Fˣ)) = 0 := by
  apply (ZMod.add_self_eq_zero_iff_eq_zero hℓodd).mp
  rw [← p.map_add]
  have ha : Additive.ofMul (-1 : Fˣ) + Additive.ofMul (-1 : Fˣ) = 0 := by
    ext
    simp
  rw [ha, p.map_zero]

private theorem characterFieldValue_neg {F : Type*} [Field F] {ℓ : ℕ}
    (hℓodd : Odd ℓ) (p : MulCharacter F ℓ) (a : F) :
    characterFieldValue p (-a) = characterFieldValue p a := by
  classical
  by_cases ha : a = 0
  · simp [ha, characterFieldValue]
  have hna : -a ≠ 0 := neg_ne_zero.mpr ha
  rw [characterFieldValue, dif_neg hna, characterFieldValue, dif_neg ha]
  have hu : Units.mk0 (-a) hna = (-1 : Fˣ) * Units.mk0 a ha := by
    apply Units.ext
    simp
  rw [hu]
  change p (Additive.ofMul (-1 : Fˣ) + Additive.ofMul (Units.mk0 a ha)) = _
  rw [p.map_add, character_kills_neg_one_pb hℓodd p, zero_add]

private def characterProjectiveMap {F : Type*} [Field F] {n : ℕ}
    (p q : MulCharacter F n) (a : F) : ProjectiveCoord (ZMod n) :=
  projectiveCoord 1 (characterFieldValue p a) (characterFieldValue q a)

private theorem affine_collinear_iff {k : Type*} [Field k]
    (pa qa pb qb pc qc : k) :
    ProjectivelyCollinear (projectiveCoord 1 pa qa)
      (projectiveCoord 1 pb qb) (projectiveCoord 1 pc qc) ↔
      (pa - pc) * (qb - qc) = (pb - pc) * (qa - qc) := by
  simp [ProjectivelyCollinear, projectiveDet, projectiveCoord]
  constructor <;> intro h <;> linear_combination h

private theorem characterProjectiveMap_add_collinear
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (p q : MulCharacter F ℓ) (halt : AlternatingPair ℓ p q) (a b : F) :
    ProjectivelyCollinear (characterProjectiveMap p q a)
      (characterProjectiveMap p q b) (characterProjectiveMap p q (a + b)) := by
  rw [characterProjectiveMap, characterProjectiveMap, characterProjectiveMap,
    affine_collinear_iff]
  by_cases ha : a = 0
  · subst a
    simp [characterFieldValue_zero]
  by_cases hb : b = 0
  · subst b
    simp [characterFieldValue_zero]
  by_cases hc : a + b = 0
  · have hba : b = -a := by linear_combination hc
    rw [hc, hba, characterFieldValue_zero,
      characterFieldValue_neg hℓodd p, characterFieldValue_neg hℓodd q]
  let ua : Fˣ := Units.mk0 a ha
  let ub : Fˣ := Units.mk0 b hb
  let uc : Fˣ := Units.mk0 (a + b) hc
  have hsum : ((ua * uc⁻¹ : Fˣ) : F) + ((ub * uc⁻¹ : Fˣ) : F) = 1 := by
    dsimp [ua, ub, uc]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  have h := halt (ua * uc⁻¹) (ub * uc⁻¹) hsum
  simpa [map_sub, sub_eq_add_neg, ua, ub, uc, characterFieldValue, ha, hb, hc] using h

private theorem mem_commonKernelCarrier_iff_pair_zero
    {F : Type*} [Field F] {ℓ : ℕ} (p q : MulCharacter F ℓ) (x : Fˣ) :
    (x : F) ∈ commonKernelCarrier p q ↔ characterPairValue p q x = 0 := by
  constructor
  · rintro ⟨u, hu, hux⟩
    have heq : u = x := by
      apply Units.ext
      exact hux
    subst u
    exact Prod.ext hu.1 hu.2
  · intro hx
    refine ⟨x, ?_, rfl⟩
    exact (Prod.ext_iff.mp hx)

private def normalizedFirst {F : Type*} [Field F] {ℓ : ℕ}
    (p q : MulCharacter F ℓ) (x y : Fˣ) : MulCharacter F ℓ :=
  (characterDet p q x y)⁻¹ •
    ((q (Additive.ofMul y)) • p - (p (Additive.ofMul y)) • q)

private def normalizedSecond {F : Type*} [Field F] {ℓ : ℕ}
    (p q : MulCharacter F ℓ) (x y : Fˣ) : MulCharacter F ℓ :=
  (characterDet p q x y)⁻¹ •
    ((p (Additive.ofMul x)) • q - (q (Additive.ofMul x)) • p)

private theorem normalizedFirst_x {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y : Fˣ)
    (hdet : characterDet p q x y ≠ 0) :
    normalizedFirst p q x y (Additive.ofMul x) = 1 := by
  change (characterDet p q x y)⁻¹ *
    (q (Additive.ofMul y) * p (Additive.ofMul x) -
      p (Additive.ofMul y) * q (Additive.ofMul x)) = 1
  rw [show q (Additive.ofMul y) * p (Additive.ofMul x) -
      p (Additive.ofMul y) * q (Additive.ofMul x) = characterDet p q x y by
    simp [characterDet]; ring]
  exact inv_mul_cancel₀ hdet

private theorem normalizedFirst_y {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y : Fˣ) :
    normalizedFirst p q x y (Additive.ofMul y) = 0 := by
  change (characterDet p q x y)⁻¹ *
    (q (Additive.ofMul y) * p (Additive.ofMul y) -
      p (Additive.ofMul y) * q (Additive.ofMul y)) = 0
  ring

private theorem normalizedSecond_x {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y : Fˣ) :
    normalizedSecond p q x y (Additive.ofMul x) = 0 := by
  change (characterDet p q x y)⁻¹ *
    (p (Additive.ofMul x) * q (Additive.ofMul x) -
      q (Additive.ofMul x) * p (Additive.ofMul x)) = 0
  ring

private theorem normalizedSecond_y {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y : Fˣ)
    (hdet : characterDet p q x y ≠ 0) :
    normalizedSecond p q x y (Additive.ofMul y) = 1 := by
  change (characterDet p q x y)⁻¹ *
    (p (Additive.ofMul x) * q (Additive.ofMul y) -
      q (Additive.ofMul x) * p (Additive.ofMul y)) = 1
  rw [show p (Additive.ofMul x) * q (Additive.ofMul y) -
      q (Additive.ofMul x) * p (Additive.ofMul y) = characterDet p q x y by
    simp [characterDet]; ring]
  exact inv_mul_cancel₀ hdet

private theorem normalized_reconstruct_first {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y u : Fˣ)
    (hdet : characterDet p q x y ≠ 0) :
    p (Additive.ofMul x) * normalizedFirst p q x y (Additive.ofMul u) +
        p (Additive.ofMul y) * normalizedSecond p q x y (Additive.ofMul u) =
      p (Additive.ofMul u) := by
  change p (Additive.ofMul x) * ((characterDet p q x y)⁻¹ *
        (q (Additive.ofMul y) * p (Additive.ofMul u) -
          p (Additive.ofMul y) * q (Additive.ofMul u))) +
      p (Additive.ofMul y) * ((characterDet p q x y)⁻¹ *
        (p (Additive.ofMul x) * q (Additive.ofMul u) -
          q (Additive.ofMul x) * p (Additive.ofMul u))) =
    p (Additive.ofMul u)
  field_simp [hdet]
  <;> unfold characterDet
  <;> ring

private theorem normalized_reconstruct_second {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y u : Fˣ)
    (hdet : characterDet p q x y ≠ 0) :
    q (Additive.ofMul x) * normalizedFirst p q x y (Additive.ofMul u) +
        q (Additive.ofMul y) * normalizedSecond p q x y (Additive.ofMul u) =
      q (Additive.ofMul u) := by
  change q (Additive.ofMul x) * ((characterDet p q x y)⁻¹ *
        (q (Additive.ofMul y) * p (Additive.ofMul u) -
          p (Additive.ofMul y) * q (Additive.ofMul u))) +
      q (Additive.ofMul y) * ((characterDet p q x y)⁻¹ *
        (p (Additive.ofMul x) * q (Additive.ofMul u) -
          q (Additive.ofMul x) * p (Additive.ofMul u))) =
    q (Additive.ofMul u)
  field_simp [hdet]
  <;> unfold characterDet
  <;> ring

private theorem normalized_pair_zero_iff {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y u : Fˣ)
    (hdet : characterDet p q x y ≠ 0) :
    (normalizedFirst p q x y (Additive.ofMul u) = 0 ∧
      normalizedSecond p q x y (Additive.ofMul u) = 0) ↔
    characterPairValue p q u = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · change p (Additive.ofMul u) = 0
      simpa [h1, h2] using
        (normalized_reconstruct_first p q x y u hdet).symm
    · change q (Additive.ofMul u) = 0
      simpa [h1, h2] using
        (normalized_reconstruct_second p q x y u hdet).symm
  · intro hu
    have hpq := Prod.ext_iff.mp hu
    change p (Additive.ofMul u) = 0 ∧ q (Additive.ofMul u) = 0 at hpq
    constructor
    · change (characterDet p q x y)⁻¹ *
        (q (Additive.ofMul y) * p (Additive.ofMul u) -
          p (Additive.ofMul y) * q (Additive.ofMul u)) = 0
      rw [hpq.1, hpq.2]
      ring
    · change (characterDet p q x y)⁻¹ *
        (p (Additive.ofMul x) * q (Additive.ofMul u) -
          q (Additive.ofMul x) * p (Additive.ofMul u)) = 0
      rw [hpq.1, hpq.2]
      ring

private theorem normalized_alternating {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (p q : MulCharacter F ℓ) (x y : Fˣ)
    (halt : AlternatingPair ℓ p q) :
    AlternatingPair ℓ (normalizedFirst p q x y) (normalizedSecond p q x y) := by
  intro a b hab
  have h := halt a b hab
  change ((characterDet p q x y)⁻¹ *
      (q (Additive.ofMul y) * p (Additive.ofMul a) -
        p (Additive.ofMul y) * q (Additive.ofMul a))) *
      ((characterDet p q x y)⁻¹ *
        (p (Additive.ofMul x) * q (Additive.ofMul b) -
          q (Additive.ofMul x) * p (Additive.ofMul b))) =
    ((characterDet p q x y)⁻¹ *
      (q (Additive.ofMul y) * p (Additive.ofMul b) -
        p (Additive.ofMul y) * q (Additive.ofMul b))) *
      ((characterDet p q x y)⁻¹ *
        (p (Additive.ofMul x) * q (Additive.ofMul a) -
          q (Additive.ofMul x) * p (Additive.ofMul a)))
  linear_combination
    (characterDet p q x y)⁻¹ ^ 2 *
      (q (Additive.ofMul y) * p (Additive.ofMul x) -
        p (Additive.ofMul y) * q (Additive.ofMul x)) * h

private theorem normalized_nonrigid_parameters
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (p q : MulCharacter F ℓ) (halt : AlternatingPair ℓ p q)
    (x y : Fˣ) (hx : IsTNonrigid (commonKernelCarrier p q) x)
    (hy : IsTNonrigid (commonKernelCarrier p q) y)
    (hdet : characterDet p q x y ≠ 0) :
    let p' := normalizedFirst p q x y
    let q' := normalizedSecond p q x y
    let A := characterFieldValue p' (1 + (x : F))
    let B := characterFieldValue q' (1 + (y : F))
    A ≠ 0 ∧ A - 1 ≠ 0 ∧ B ≠ 0 ∧ B - 1 ≠ 0 ∧
      characterFieldValue q' (1 + (x : F)) = 0 ∧
      characterFieldValue p' (1 + (y : F)) = 0 := by
  dsimp only
  let p' := normalizedFirst p q x y
  let q' := normalizedSecond p q x y
  let A := characterFieldValue p' (1 + (x : F))
  let B := characterFieldValue q' (1 + (y : F))
  have halt' : AlternatingPair ℓ p' q' := normalized_alternating p q x y halt
  have hpx : p' (Additive.ofMul x) = 1 := normalizedFirst_x p q x y hdet
  have hqx : q' (Additive.ofMul x) = 0 := normalizedSecond_x p q x y
  have hpy : p' (Additive.ofMul y) = 0 := normalizedFirst_y p q x y
  have hqy : q' (Additive.ofMul y) = 1 := normalizedSecond_y p q x y hdet
  have hxsum : 1 + (x : F) ≠ 0 := by
    intro hsum
    have hxeq : x = (-1 : Fˣ) := by
      apply Units.ext
      dsimp
      linear_combination hsum
    rw [hxeq, character_kills_neg_one_pb hℓodd p'] at hpx
    exact zero_ne_one hpx
  have hysum : 1 + (y : F) ≠ 0 := by
    intro hsum
    have hyeq : y = (-1 : Fˣ) := by
      apply Units.ext
      dsimp
      linear_combination hsum
    rw [hyeq, character_kills_neg_one_pb hℓodd q'] at hqy
    exact zero_ne_one hqy
  have hqxsum : characterFieldValue q' (1 + (x : F)) = 0 := by
    have hcol := characterProjectiveMap_add_collinear hℓodd p' q' halt' 1 (x : F)
    simp [characterProjectiveMap, ProjectivelyCollinear, projectiveDet,
      projectiveCoord, characterFieldValue_one, characterFieldValue_unit,
      hpx, hqx] at hcol
    exact hcol
  have hpysum : characterFieldValue p' (1 + (y : F)) = 0 := by
    have hcol := characterProjectiveMap_add_collinear hℓodd p' q' halt' 1 (y : F)
    simp [characterProjectiveMap, ProjectivelyCollinear, projectiveDet,
      projectiveCoord, characterFieldValue_one, characterFieldValue_unit,
      hpy, hqy] at hcol
    exact hcol
  have hA : A ≠ 0 := by
    intro hA0
    let u : Fˣ := Units.mk0 (1 + (x : F)) hxsum
    have hpu : p' (Additive.ofMul u) = 0 := by
      rw [← characterFieldValue_unit p' u]
      exact hA0
    have hqu : q' (Additive.ofMul u) = 0 := by
      rw [← characterFieldValue_unit q' u]
      exact hqxsum
    have hpq0 : characterPairValue p q u = 0 :=
      (normalized_pair_zero_iff p q x y u hdet).mp ⟨hpu, hqu⟩
    have huT : (u : F) ∈ commonKernelCarrier p q :=
      (mem_commonKernelCarrier_iff_pair_zero p q u).mpr hpq0
    exact hx.2 (Set.mem_union_left _ huT)
  have hA1 : A - 1 ≠ 0 := by
    intro hAone
    let u : Fˣ := Units.mk0 (1 + (x : F)) hxsum
    let v : Fˣ := u * x⁻¹
    have hpv : p' (Additive.ofMul v) = 0 := by
      change p' (Additive.ofMul u - Additive.ofMul x) = 0
      rw [map_sub, ← characterFieldValue_unit p' u, hpx]
      exact hAone
    have hqv : q' (Additive.ofMul v) = 0 := by
      change q' (Additive.ofMul u - Additive.ofMul x) = 0
      rw [map_sub, ← characterFieldValue_unit q' u, hqx, sub_zero]
      exact hqxsum
    have hpq0 : characterPairValue p q v = 0 :=
      (normalized_pair_zero_iff p q x y v hdet).mp ⟨hpv, hqv⟩
    have hvT : (v : F) ∈ commonKernelCarrier p q :=
      (mem_commonKernelCarrier_iff_pair_zero p q v).mpr hpq0
    apply hx.2
    apply Set.mem_union_right
    rw [Set.mem_smul_set]
    refine ⟨(v : F), hvT, ?_⟩
    dsimp [v, u]
    field_simp
    rw [Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero x)
  have hB : B ≠ 0 := by
    intro hB0
    let u : Fˣ := Units.mk0 (1 + (y : F)) hysum
    have hpu : p' (Additive.ofMul u) = 0 := by
      rw [← characterFieldValue_unit p' u]
      exact hpysum
    have hqu : q' (Additive.ofMul u) = 0 := by
      rw [← characterFieldValue_unit q' u]
      exact hB0
    have hpq0 : characterPairValue p q u = 0 :=
      (normalized_pair_zero_iff p q x y u hdet).mp ⟨hpu, hqu⟩
    have huT : (u : F) ∈ commonKernelCarrier p q :=
      (mem_commonKernelCarrier_iff_pair_zero p q u).mpr hpq0
    exact hy.2 (Set.mem_union_left _ huT)
  have hB1 : B - 1 ≠ 0 := by
    intro hBone
    let u : Fˣ := Units.mk0 (1 + (y : F)) hysum
    let v : Fˣ := u * y⁻¹
    have hpv : p' (Additive.ofMul v) = 0 := by
      change p' (Additive.ofMul u - Additive.ofMul y) = 0
      rw [map_sub, ← characterFieldValue_unit p' u, hpy, sub_zero]
      exact hpysum
    have hqv : q' (Additive.ofMul v) = 0 := by
      change q' (Additive.ofMul u - Additive.ofMul y) = 0
      rw [map_sub, ← characterFieldValue_unit q' u, hqy]
      exact hBone
    have hpq0 : characterPairValue p q v = 0 :=
      (normalized_pair_zero_iff p q x y v hdet).mp ⟨hpv, hqv⟩
    have hvT : (v : F) ∈ commonKernelCarrier p q :=
      (mem_commonKernelCarrier_iff_pair_zero p q v).mpr hpq0
    apply hy.2
    apply Set.mem_union_right
    rw [Set.mem_smul_set]
    refine ⟨(v : F), hvT, ?_⟩
    dsimp [v, u]
    field_simp
    rw [Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero y)
  exact ⟨hA, hA1, hB, hB1, hqxsum, hpysum⟩

private theorem characterProjectiveMap_incidence
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (p q : MulCharacter F ℓ) (halt : AlternatingPair ℓ p q) :
    IncidenceAxiom (characterProjectiveMap p q) := by
  constructor
  · intro a ha
    have h := congrFun ha 0
    simp [characterProjectiveMap, projectiveCoord] at h
  intro a b
  constructor
  · exact characterProjectiveMap_add_collinear hℓodd p q halt a b
  · have h := characterProjectiveMap_add_collinear hℓodd p q halt a (-b)
    simpa [characterProjectiveMap, characterFieldValue_neg hℓodd p,
      characterFieldValue_neg hℓodd q, sub_eq_add_neg] using h

private theorem projectiveTransform_preserves_collinear
    {k : Type*} [Field k] (A B : k) {u v w : ProjectiveCoord k}
    (h : ProjectivelyCollinear u v w) :
    ProjectivelyCollinear (projectiveTransform A B u)
      (projectiveTransform A B v) (projectiveTransform A B w) := by
  unfold ProjectivelyCollinear projectiveDet at h ⊢
  simp [projectiveTransform, projectiveCoord]
  linear_combination A ^ 2 * B ^ 2 * (A - 1) * (B - 1) * h

private theorem projectiveTransform_incidence
    {F k : Type*} [Field F] [Field k] (φ : F → ProjectiveCoord k)
    (A B : k) (hA : A ≠ 0) (hB : B ≠ 0)
    (hA1 : A - 1 ≠ 0) (hB1 : B - 1 ≠ 0)
    (hinc : IncidenceAxiom φ) :
    IncidenceAxiom (fun a => projectiveTransform A B (φ a)) := by
  have hinj := projectiveTransform_injective hA hB hA1 hB1
  constructor
  · intro a ha
    apply hinc.1 a
    apply hinj
    simpa [projectiveTransform, projectiveCoord] using ha
  · intro a b
    exact ⟨projectiveTransform_preserves_collinear A B (hinc.2 a b).1,
      projectiveTransform_preserves_collinear A B (hinc.2 a b).2⟩

private theorem projectivelyEqual_repeated
    {k : Type*} [Field k] (a b c : k) (hc : c ≠ 0) :
    ProjectivelyEqual (projectiveCoord (c * a) (c * b) 0)
      (projectiveCoord a b 0) := by
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext i
  fin_cases i <;> simp [projectiveCoord, hc]

private theorem projectivelyEqual_first_third
    {k : Type*} [Field k] (a b c : k) (hc : c ≠ 0) :
    ProjectivelyEqual (projectiveCoord (c * a) 0 (c * b))
      (projectiveCoord a 0 b) := by
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext i
  fin_cases i <;> simp [projectiveCoord, hc]

private theorem projectivelyEqual_axis_first
    {k : Type*} [Field k] (c : k) (hc : c ≠ 0) :
    ProjectivelyEqual (projectiveCoord c 0 0) (projectiveCoord 1 0 0) := by
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext i
  fin_cases i <;> simp [projectiveCoord, hc]

private theorem projectivelyEqual_axis_second
    {k : Type*} [Field k] (c : k) (hc : c ≠ 0) :
    ProjectivelyEqual (projectiveCoord 0 c 0) (projectiveCoord 0 1 0) := by
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext i
  fin_cases i <;> simp [projectiveCoord, hc]

private theorem projectivelyEqual_axis_third
    {k : Type*} [Field k] (c : k) (hc : c ≠ 0) :
    ProjectivelyEqual (projectiveCoord 0 0 c) (projectiveCoord 0 0 1) := by
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext i
  fin_cases i <;> simp [projectiveCoord, hc]

private theorem projectiveTransform_avoids_special
    {k : Type*} [Field k] (A B : k)
    (hA : A ≠ 0) (hB : B ≠ 0) (hA1 : A - 1 ≠ 0) (hB1 : B - 1 ≠ 0)
    (u : ProjectiveCoord k) (hu0 : u 0 = 1) :
    ¬ ProjectivelyEqual (projectiveTransform A B u)
      (projectiveCoord 1 (1 - A) 0) := by
  rintro ⟨c, hc, heq⟩
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [projectiveTransform, projectiveCoord, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  rw [hu0] at h0
  change 0 = c * (u 2 * A * (B - 1)) at h2
  have hprod : c * A * B * (A - 1) * (B - 1) = 0 := by
    linear_combination
      -(A - 1) * (B - 1) * h0 - (B - 1) * h1 - (A - 1) * h2
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hA) hB) hA1) hB1) hprod

private theorem pair_mem_span_of_det_zero
    {k : Type*} [Field k] (v w : k × k) (hv : v ≠ 0)
    (hdet : v.1 * w.2 - w.1 * v.2 = 0) : w ∈ k ∙ v := by
  rw [Submodule.mem_span_singleton]
  by_cases hv1 : v.1 = 0
  · have hv2 : v.2 ≠ 0 := by
      intro hv2
      apply hv
      exact Prod.ext hv1 hv2
    refine ⟨w.2 / v.2, ?_⟩
    apply Prod.ext
    · dsimp
      have hw1 : w.1 = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right hv2
        simpa [hv1] using hdet
      simp [hv1, hw1]
    · dsimp
      field_simp
  · refine ⟨w.1 / v.1, ?_⟩
    apply Prod.ext
    · dsimp
      field_simp
    · dsimp
      field_simp
      linear_combination -hdet

private theorem characterDet_eq_zero_of_nonrigid
    {F : Type*} [Field F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (p q : MulCharacter F ℓ) (halt : AlternatingPair ℓ p q)
    (x y : Fˣ) (hx : IsTNonrigid (commonKernelCarrier p q) x)
    (hy : IsTNonrigid (commonKernelCarrier p q) y) :
    characterDet p q x y = 0 := by
  by_contra hdet
  let p' := normalizedFirst p q x y
  let q' := normalizedSecond p q x y
  let A := characterFieldValue p' (1 + (x : F))
  let B := characterFieldValue q' (1 + (y : F))
  have halt' : AlternatingPair ℓ p' q' := normalized_alternating p q x y halt
  rcases normalized_nonrigid_parameters hℓodd p q halt x y hx hy hdet with
    ⟨hA, hA1, hB, hB1, hqxsum, hpysum⟩
  change A ≠ 0 at hA
  change A - 1 ≠ 0 at hA1
  change B ≠ 0 at hB
  change B - 1 ≠ 0 at hB1
  change characterFieldValue q' (1 + (x : F)) = 0 at hqxsum
  change characterFieldValue p' (1 + (y : F)) = 0 at hpysum
  have hpx : p' (Additive.ofMul x) = 1 := normalizedFirst_x p q x y hdet
  have hqx : q' (Additive.ofMul x) = 0 := normalizedSecond_x p q x y
  have hpy : p' (Additive.ofMul y) = 0 := normalizedFirst_y p q x y
  have hqy : q' (Additive.ofMul y) = 1 := normalizedSecond_y p q x y hdet
  let θ : F → ProjectiveCoord (ZMod ℓ) := characterProjectiveMap p' q'
  let φ : F → ProjectiveCoord (ZMod ℓ) := fun a => projectiveTransform A B (θ a)
  have hθinc : IncidenceAxiom θ :=
    characterProjectiveMap_incidence hℓodd p' q' halt'
  have hφinc : IncidenceAxiom φ :=
    projectiveTransform_incidence θ A B hA hB hA1 hB1 hθinc
  have hframe : HasProjectiveFrame φ (x : F) (y : F) := by
    dsimp [φ, θ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [characterProjectiveMap, characterFieldValue_zero,
        projectiveTransform, projectiveCoord] using
        (projectivelyEqual_axis_first (A * B) (mul_ne_zero hA hB))
    · simpa [characterProjectiveMap, characterFieldValue_one,
        projectiveTransform, projectiveCoord] using
        (projectivelyEqual_axis_first (A * B) (mul_ne_zero hA hB))
    · convert (projectivelyEqual_repeated (1 : ZMod ℓ) 1 (B * (A - 1))
          (mul_ne_zero hB hA1)) using 1 <;>
        simp [characterProjectiveMap, characterFieldValue_unit, hpx, hqx,
          projectiveTransform, projectiveCoord] <;> ring
    · convert (projectivelyEqual_first_third (1 : ZMod ℓ) 1 (A * (B - 1))
          (mul_ne_zero hA hB1)) using 1 <;>
        simp [characterProjectiveMap, characterFieldValue_unit, hpy, hqy,
          projectiveTransform, projectiveCoord] <;> ring
    · convert (projectivelyEqual_axis_second (A * B * (A - 1))
          (mul_ne_zero (mul_ne_zero hA hB) hA1)) using 1 <;>
        simp [characterProjectiveMap, A, hqxsum,
          projectiveTransform, projectiveCoord] <;> ring
    · convert (projectivelyEqual_axis_third (B * A * (B - 1))
          (mul_ne_zero (mul_ne_zero hB hA) hB1)) using 1 <;>
        simp [characterProjectiveMap, B, hpysum,
          projectiveTransform, projectiveCoord] <;> ring
  let m : ℤ := Int.ofNat (1 - A).val
  let t : F := (((m - 1 : ℤ) : F) + (m : F) * (x : F))
  have hcfg := incidence_config_n_m_zero φ (x : F) (y : F) m 1
    (by simp) hφinc hframe
  have hm : (m : ZMod ℓ) = 1 - A := by
    dsimp [m]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcfg' : ProjectivelyEqual (φ t) (projectiveCoord 1 (1 - A) 0) := by
    simpa [t, hm] using hcfg
  apply projectiveTransform_avoids_special A B hA hB hA1 hB1 (θ t)
  · simp [θ, characterProjectiveMap, projectiveCoord]
  · exact hcfg'

/-- Blueprint Lemma 3.3 (`lem:projective-bridge`): the image of
`⟨T,B(T)⟩/T` has dimension at most one.  This is the terminal theorem of
the projective work package. -/
theorem finrank_nonrigidQuotient_le_one {F : Type*} [Field F] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓodd : Odd ℓ) (p q : MulCharacter F ℓ)
    (halt : AlternatingPair ℓ p q) :
    Module.finrank (ZMod ℓ) (nonrigidQuotientImage p q) ≤ 1 := by
  let S : Set (ZMod ℓ × ZMod ℓ) :=
    {z | ∃ x : Fˣ,
      IsTNonrigid (commonKernelCarrier p q) x ∧
        z = characterPairValue p q x}
  change Module.finrank (ZMod ℓ) (Submodule.span (ZMod ℓ) S) ≤ 1
  by_cases hS : S.Nonempty
  · rcases hS with ⟨v, hv⟩
    rcases hv with ⟨x, hx, rfl⟩
    have hv0 : characterPairValue p q x ≠ 0 := by
      intro hvzero
      exact hx.1 ((mem_commonKernelCarrier_iff_pair_zero p q x).mpr hvzero)
    have hle : Submodule.span (ZMod ℓ) S ≤
        (ZMod ℓ) ∙ characterPairValue p q x := by
      rw [Submodule.span_le]
      intro w hw
      rcases hw with ⟨y, hy, rfl⟩
      apply pair_mem_span_of_det_zero _ _ hv0
      simpa [characterPairValue, characterDet] using
        characterDet_eq_zero_of_nonrigid hℓodd p q halt x y hx hy
    calc
      Module.finrank (ZMod ℓ) (Submodule.span (ZMod ℓ) S) ≤
          Module.finrank (ZMod ℓ) ((ZMod ℓ) ∙ characterPairValue p q x) :=
        Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton hv0
  · have hsempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hsempty, Submodule.span_empty, finrank_bot]
    simp

end

end NU.LocalTheory
