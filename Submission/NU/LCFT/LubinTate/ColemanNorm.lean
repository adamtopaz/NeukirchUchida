import Submission.NU.LCFT.LubinTate.Torsion
import Submission.NU.LCFT.Basic.Norm

/-!
# The finite Coleman norm operator

The source copy of `𝒪_K[[X]]` acts on the target copy through `h ↦ h(f(X))`.  The displayed
Weierstrass basis and every multiplication matrix are pinned to this action.  Products over
division points are derived only afterward, inside the finite Lubin--Tate level where evaluation
converges.
-/

namespace PowerSeries

universe u

variable {R : Type u} [CommRing R]

section

variable (I : Ideal R) [IsAdicComplete I R]
variable {f : PowerSeries R} (H : f.IsWeierstrassDivisorAt I)

private noncomputable def colemanQuotient (g : PowerSeries R) : PowerSeries R := H.div g
private noncomputable def colemanRemainder (g : PowerSeries R) : Polynomial R := H.mod g

private lemma coleman_division_eq (g : PowerSeries R) :
    g = f * colemanQuotient I H g + (colemanRemainder I H g : PowerSeries R) := by
  exact (H.isWeierstrassDivisionAt_div_mod g).eq_mul_add

private lemma coleman_iter_division (g : PowerSeries R) (N : ℕ) :
    g = (∑ n ∈ Finset.range N,
        f ^ n * (colemanRemainder I H ((colemanQuotient I H)^[n] g) : PowerSeries R)) +
      f ^ N * (colemanQuotient I H)^[N] g := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        g = (∑ n ∈ Finset.range N,
              f ^ n * (colemanRemainder I H ((colemanQuotient I H)^[n] g) : PowerSeries R)) +
            f ^ N * (colemanQuotient I H)^[N] g := ih
        _ = (∑ n ∈ Finset.range (N + 1),
              f ^ n * (colemanRemainder I H ((colemanQuotient I H)^[n] g) : PowerSeries R)) +
            f ^ (N + 1) * (colemanQuotient I H)^[N + 1] g := by
          rw [Finset.sum_range_succ, Function.iterate_succ_apply']
          have hd := coleman_division_eq I H ((colemanQuotient I H)^[N] g)
          conv_lhs =>
            rhs
            rw [hd]
          ring

end

private lemma coleman_coeff_pow_eq_zero (f g : PowerSeries R)
    (hf0 : f.constantCoeff = 0) {d n : ℕ} (hdn : d < n) :
    coeff d (f ^ n * g) = 0 := by
  apply coeff_of_lt_order
  apply lt_of_lt_of_le (show (d : ℕ∞) < n by exact_mod_cast hdn)
  exact (le_order_pow_of_constantCoeff_eq_zero n hf0).trans
    ((le_add_right le_rfl).trans (le_order_mul _ _))

private noncomputable def colemanRemainderPolynomial (q : ℕ)
    (a : Fin q → R) : Polynomial R :=
  ∑ i : Fin q, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

private lemma colemanRemainderPolynomial_degree_lt (q : ℕ) (a : Fin q → R) :
    (colemanRemainderPolynomial q a).degree < q := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [colemanRemainderPolynomial]
  have hsum : (∑ i : Fin q,
      Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).coeff n =
      ∑ i : Fin q, (Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).coeff n := by
    exact Polynomial.finsetSum_coeff (Finset.univ : Finset (Fin q))
      (fun i => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) n
  rw [hsum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : n ≠ (i : ℕ) := fun h => (not_lt_of_ge hn) (h ▸ i.isLt)
  rw [if_neg hne]

private lemma colemanRemainderPolynomial_coeff (q : ℕ) (a : Fin q → R) (i : Fin q) :
    (colemanRemainderPolynomial q a).coeff i = a i := by
  rw [colemanRemainderPolynomial]
  have hsum : (∑ j : Fin q,
      Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) =
      ∑ j : Fin q, (Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) := by
    exact Polynomial.finsetSum_coeff (Finset.univ : Finset (Fin q))
      (fun j => Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) (i : ℕ)
  rw [hsum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    rw [if_neg hne]
  · simp

private lemma colemanRemainderPolynomial_eq_of_degree_lt (q : ℕ) (r : Polynomial R)
    (hr : r.degree < q) :
    colemanRemainderPolynomial q (fun i => r.coeff i) = r := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < q
  · simpa using colemanRemainderPolynomial_coeff q (fun i : Fin q => r.coeff i) ⟨n, hn⟩
  · have hrn : r.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hr (by simpa using hn)
    have htest : (colemanRemainderPolynomial q (fun i : Fin q => r.coeff i)).coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le (colemanRemainderPolynomial_degree_lt q _) (by simpa using hn)
    rw [htest, hrn]

private lemma colemanRemainderPolynomial_coe (q : ℕ) (a : Fin q → R) :
    (colemanRemainderPolynomial q a : PowerSeries R) =
      ∑ i : Fin q, C (a i) * X ^ (i : ℕ) := by
  rw [colemanRemainderPolynomial]
  change Polynomial.coeToPowerSeries.algHom R
      (∑ i : Fin q, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private def colemanTruncatedSeries (a : ℕ → R) (N : ℕ) : PowerSeries R :=
  mk fun n => if n < N then a n else 0

private lemma colemanTruncatedSeries_eq_sum (a : ℕ → R) (N : ℕ) :
    colemanTruncatedSeries a N = ∑ n ∈ Finset.range N, C (a n) * X ^ n := by
  ext d
  rw [colemanTruncatedSeries, coeff_mk]
  simp only [map_sum, coeff_C_mul_X_pow]
  by_cases hd : d < N
  · rw [if_pos hd, Finset.sum_eq_single d]
    · simp
    · intro b hb hbd
      have hne : d ≠ b := fun h => hbd h.symm
      rw [if_neg hne]
    · simp [hd]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hne : d ≠ n := fun h => hd (h ▸ Finset.mem_range.mp hn)
    rw [if_neg hne]

private lemma coleman_subst_trunc (f : PowerSeries R) (hf0 : f.constantCoeff = 0)
    (a : ℕ → R) (N : ℕ) :
    subst f (colemanTruncatedSeries a N) =
      ∑ n ∈ Finset.range N, C (a n) * f ^ n := by
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  rw [colemanTruncatedSeries_eq_sum]
  rw [← coe_substAlgHom hf, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [congrFun (coe_substAlgHom hf) (C (a n) * X ^ n)]
  rw [subst_mul hf, subst_C, subst_pow hf, subst_X hf]
  rfl

section

variable (I : Ideal R) [IsAdicComplete I R]
variable {f : PowerSeries R} (H : f.IsWeierstrassDivisorAt I)

private noncomputable def colemanPresentation (q : ℕ)
    (a : Fin q → PowerSeries R) : PowerSeries R :=
  ∑ i : Fin q, subst f (a i) * X ^ (i : ℕ)

private noncomputable def colemanCoordinates (q : ℕ) (g : PowerSeries R) (i : Fin q) :
    PowerSeries R :=
  mk fun n => (H.mod ((colemanQuotient I H)^[n] g)).coeff i

private lemma coleman_finite_expansion (hf0 : f.constantCoeff = 0) (q N : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (g : PowerSeries R) :
    colemanPresentation (f := f) q (fun i => colemanTruncatedSeries
      (fun n => (H.mod ((colemanQuotient I H)^[n] g)).coeff i) N) =
      ∑ n ∈ Finset.range N,
        f ^ n * (H.mod ((colemanQuotient I H)^[n] g) : PowerSeries R) := by
  have hrem (n : ℕ) :
      (H.mod ((colemanQuotient I H)^[n] g) : PowerSeries R) =
        ∑ i : Fin q,
          C ((H.mod ((colemanQuotient I H)^[n] g)).coeff i) * X ^ (i : ℕ) := by
    rw [← colemanRemainderPolynomial_coe]
    congr 1
    symm
    apply colemanRemainderPolynomial_eq_of_degree_lt
    simpa [horder] using
      (H.isWeierstrassDivisionAt_div_mod ((colemanQuotient I H)^[n] g)).degree_lt
  rw [colemanPresentation]
  simp_rw [coleman_subst_trunc f hf0]
  simp_rw [hrem]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

private lemma coleman_coeff_subst_congr (f : PowerSeries R) (hf0 : f.constantCoeff = 0)
    (a b : PowerSeries R) (d : ℕ)
    (hcoeff : ∀ n ≤ d, coeff n a = coeff n b) :
    coeff d (subst f a) = coeff d (subst f b) := by
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  rw [coeff_subst' hf, coeff_subst' hf]
  apply finsum_congr
  intro n
  by_cases hn : n ≤ d
  · rw [hcoeff n hn]
  · have hz : coeff d (f ^ n) = 0 := by
      apply coeff_of_lt_order
      apply lt_of_lt_of_le (show (d : ℕ∞) < n by exact_mod_cast (not_le.mp hn))
      exact le_order_pow_of_constantCoeff_eq_zero n hf0
    simp [hz]

section

variable (I : Ideal R) [IsAdicComplete I R]
variable {f : PowerSeries R} (H : f.IsWeierstrassDivisorAt I)

private noncomputable def colemanShift (a : PowerSeries R) : PowerSeries R :=
  mk fun n => coeff (n + 1) a

private lemma coleman_subst_shift (hf0 : f.constantCoeff = 0) (a : PowerSeries R) :
    subst f a = f * subst f (colemanShift a) + C (constantCoeff a) := by
  have hf : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  have ha := congrArg (subst f) (eq_X_mul_shift_add_const a)
  rw [subst_add hf, subst_mul hf, subst_X hf, subst_C] at ha
  exact ha

private lemma colemanPresentation_shift (hf0 : f.constantCoeff = 0) (q : ℕ)
    (a : Fin q → PowerSeries R) :
    colemanPresentation (f := f) q a =
      f * colemanPresentation (f := f) q (fun i => colemanShift (a i)) +
        (colemanRemainderPolynomial q (fun i => constantCoeff (a i)) : PowerSeries R) := by
  rw [colemanPresentation, colemanPresentation, colemanRemainderPolynomial_coe]
  calc
    (∑ i : Fin q, subst f (a i) * X ^ (i : ℕ)) =
        ∑ i : Fin q,
          (f * subst f (colemanShift (a i)) + C (constantCoeff (a i))) *
            X ^ (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z => z * X ^ (i : ℕ))
        (coleman_subst_shift (f := f) hf0 (a i))
    _ = f * (∑ i : Fin q, subst f (colemanShift (a i)) * X ^ (i : ℕ)) +
          ∑ i : Fin q, C (constantCoeff (a i)) * X ^ (i : ℕ) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        ring
      · rfl

private lemma coleman_quotient_raw (hf0 : f.constantCoeff = 0) (q : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (a : Fin q → PowerSeries R) :
    colemanQuotient I H (colemanPresentation (f := f) q a) =
      colemanPresentation (f := f) q (fun i => colemanShift (a i)) := by
  let g := colemanPresentation (f := f) q a
  let r := colemanRemainderPolynomial q (fun i => constantCoeff (a i))
  have actual := H.isWeierstrassDivisionAt_div_mod g
  have proposed : g.IsWeierstrassDivisionAt f
      (colemanPresentation (f := f) q (fun i => colemanShift (a i))) r I := by
    constructor
    · simpa [horder, r] using colemanRemainderPolynomial_degree_lt q
        (fun i => constantCoeff (a i))
    · exact colemanPresentation_shift (f := f) hf0 q a
  exact (H.eq_of_mul_add_eq_mul_add actual.degree_lt proposed.degree_lt
    (actual.eq_mul_add.symm.trans proposed.eq_mul_add)).1

private lemma coleman_mod_raw (hf0 : f.constantCoeff = 0) (q : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (a : Fin q → PowerSeries R) :
    H.mod (colemanPresentation (f := f) q a) =
      colemanRemainderPolynomial q (fun i => constantCoeff (a i)) := by
  let g := colemanPresentation (f := f) q a
  let r := colemanRemainderPolynomial q (fun i => constantCoeff (a i))
  have actual := H.isWeierstrassDivisionAt_div_mod g
  have proposed : g.IsWeierstrassDivisionAt f
      (colemanPresentation (f := f) q (fun i => colemanShift (a i))) r I := by
    constructor
    · simpa [horder, r] using colemanRemainderPolynomial_degree_lt q
        (fun i => constantCoeff (a i))
    · exact colemanPresentation_shift (f := f) hf0 q a
  exact (H.eq_of_mul_add_eq_mul_add actual.degree_lt proposed.degree_lt
    (actual.eq_mul_add.symm.trans proposed.eq_mul_add)).2

private lemma coleman_quotient_iter_raw (hf0 : f.constantCoeff = 0) (q : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (a : Fin q → PowerSeries R) (n : ℕ) :
    (colemanQuotient I H)^[n] (colemanPresentation (f := f) q a) =
      colemanPresentation (f := f) q (fun i => (colemanShift^[n]) (a i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        coleman_quotient_raw I H hf0 q horder]
      congr 2
      funext i
      rw [Function.iterate_succ_apply']

private lemma coleman_shift_iter_coeff (a : PowerSeries R) (n d : ℕ) :
    coeff d ((colemanShift^[n]) a) = coeff (d + n) a := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', colemanShift, coeff_mk, ih]
      rw [show d + 1 + n = d + (n + 1) by omega]

private lemma coleman_coord_raw (hf0 : f.constantCoeff = 0) (q : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (a : Fin q → PowerSeries R) :
    colemanCoordinates I H q (colemanPresentation (f := f) q a) = a := by
  funext i
  ext n
  rw [colemanCoordinates, coeff_mk, coleman_quotient_iter_raw I H hf0 q horder]
  rw [coleman_mod_raw I H hf0 q horder, colemanRemainderPolynomial_coeff]
  rw [← coeff_zero_eq_constantCoeff, coleman_shift_iter_coeff]
  simp

private lemma coleman_raw_coord (hf0 : f.constantCoeff = 0) (q : ℕ)
    (horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q)
    (g : PowerSeries R) :
    colemanPresentation (f := f) q (colemanCoordinates I H q g) = g := by
  ext d
  let truncCoord : Fin q → PowerSeries R := fun i => colemanTruncatedSeries
    (fun n => (H.mod ((colemanQuotient I H)^[n] g)).coeff i) (d + 1)
  have hraw :
      coeff d (colemanPresentation (f := f) q (colemanCoordinates I H q g)) =
        coeff d (colemanPresentation (f := f) q truncCoord) := by
    rw [colemanPresentation, colemanPresentation]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coeff_mul_X_pow', coeff_mul_X_pow']
    split_ifs with hid
    · apply coleman_coeff_subst_congr f hf0
      intro n hn
      simp only [colemanCoordinates, coeff_mk, truncCoord, colemanTruncatedSeries]
      rw [if_pos]
      omega
    · rfl
  have htail : coeff d
      (f ^ (d + 1) * (colemanQuotient I H)^[d + 1] g) = 0 :=
    coleman_coeff_pow_eq_zero f _ hf0 (Nat.lt_succ_self d)
  have hiter := congrArg (coeff d) (coleman_iter_division I H g (d + 1))
  simp only [map_add] at hiter
  rw [htail, add_zero] at hiter
  have hfinite := congrArg (coeff d)
    (coleman_finite_expansion I H hf0 q (d + 1) horder g)
  calc
    coeff d (colemanPresentation (f := f) q (colemanCoordinates I H q g)) =
        coeff d (colemanPresentation (f := f) q truncCoord) := hraw
    _ = coeff d (∑ n ∈ Finset.range (d + 1),
          f ^ n * (H.mod ((colemanQuotient I H)^[n] g) : PowerSeries R)) := hfinite
    _ = coeff d g := hiter.symm

end

end PowerSeries

namespace NU.LCFT

noncomputable section

open scoped ValuativeRel
open MvPowerSeries

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Coefficientwise congruence of power series modulo an ideal. -/
def PowerSeriesCongruent (I : Ideal (RingOfIntegers K))
    (f g : PowerSeries (RingOfIntegers K)) : Prop :=
  ∀ n, PowerSeries.coeff n f - PowerSeries.coeff n g ∈ I

/--
A nominal copy of `𝒪_K[[X]]` used only as the target of the substitution action.  Keeping this
copy nominal prevents Lean from replacing the substitution module by the canonical self-module.
-/
@[ext]
structure SubstDomain (π : Uniformizer K) where
  /-- The underlying power series. -/
  toPowerSeries : PowerSeries (RingOfIntegers K)

namespace SubstDomain

/-- The underlying-type equivalence for the nominal substitution domain. -/
def equiv (π : Uniformizer K) :
    SubstDomain K π ≃ PowerSeries (RingOfIntegers K) where
  toFun := toPowerSeries
  invFun := fun g => ⟨g⟩
  left_inv := by rintro ⟨g⟩; rfl
  right_inv := by intro g; rfl

noncomputable instance (π : Uniformizer K) : CommRing (SubstDomain K π) :=
  (equiv K π).commRing

/-- The ring equivalence forgetting the nominal substitution-domain wrapper. -/
def ringEquiv (π : Uniformizer K) :
    SubstDomain K π ≃+* PowerSeries (RingOfIntegers K) where
  __ := equiv K π
  map_add' := by intros; rfl
  map_mul' := by intros; rfl

/-- Regard a power series as an element of the nominal substitution domain. -/
def ofPowerSeries (π : Uniformizer K)
    (g : PowerSeries (RingOfIntegers K)) : SubstDomain K π :=
  (ringEquiv K π).symm g

@[simp]
theorem toPowerSeries_ofPowerSeries (π : Uniformizer K)
    (g : PowerSeries (RingOfIntegers K)) :
    (ofPowerSeries K π g).toPowerSeries = g :=
  rfl

@[simp]
theorem toPowerSeries_zero (π : Uniformizer K) :
    (0 : SubstDomain K π).toPowerSeries = 0 :=
  rfl

@[simp]
theorem toPowerSeries_one (π : Uniformizer K) :
    (1 : SubstDomain K π).toPowerSeries = 1 :=
  rfl

@[simp]
theorem toPowerSeries_add (π : Uniformizer K) (g h : SubstDomain K π) :
    (g + h).toPowerSeries = g.toPowerSeries + h.toPowerSeries :=
  rfl

@[simp]
theorem toPowerSeries_mul (π : Uniformizer K) (g h : SubstDomain K π) :
    (g * h).toPowerSeries = g.toPowerSeries * h.toPowerSeries :=
  rfl

private theorem lubinTateSeries_hasSubst (π : Uniformizer K) :
    PowerSeries.HasSubst (lubinTateSeries K π) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  have hq : residueCard K ≠ 0 := Nat.card_pos.ne'
  simp [lubinTateSeries, lubinTatePolynomial, hq]

/-- The scalar embedding `h ↦ h(f(X))`, with nominal codomain. -/
noncomputable def algebraMapHom (π : Uniformizer K) :
    PowerSeries (RingOfIntegers K) →+* SubstDomain K π :=
  (ringEquiv K π).symm.toRingHom.comp
    (PowerSeries.substAlgHom (lubinTateSeries_hasSubst K π)).toRingHom

/-- The unique module structure used on `SubstDomain`: scalars act through substitution by `f`. -/
noncomputable instance (π : Uniformizer K) :
    Algebra (PowerSeries (RingOfIntegers K)) (SubstDomain K π) :=
  (algebraMapHom K π).toAlgebra

@[simp]
theorem algebraMap_apply (π : Uniformizer K)
    (h : PowerSeries (RingOfIntegers K)) :
    (algebraMap (PowerSeries (RingOfIntegers K)) (SubstDomain K π) h).toPowerSeries =
      PowerSeries.subst (lubinTateSeries K π) h := by
  rw [RingHom.algebraMap_toAlgebra]
  change (PowerSeries.substAlgHom (R := RingOfIntegers K)
    (lubinTateSeries_hasSubst K π)) h = _
  exact congrFun (PowerSeries.coe_substAlgHom (R := RingOfIntegers K)
    (lubinTateSeries_hasSubst K π)) h

/-- The promised substitution action, stated on underlying power series. -/
@[simp]
theorem smul_apply (π : Uniformizer K) (a : PowerSeries (RingOfIntegers K))
    (g : SubstDomain K π) :
    (a • g).toPowerSeries =
      PowerSeries.subst (lubinTateSeries K π) a * g.toPowerSeries := by
  rw [Algebra.smul_def]
  simp

end SubstDomain

/-- Determinant data defining the finite Coleman operator on the actual substitution module. -/
structure ColemanNormData (π : Uniformizer K) where
  /-- The Weierstrass basis of the finite free substitution module. -/
  weierstrassBasis :
    Module.Basis (Fin (residueCard K)) (PowerSeries (RingOfIntegers K))
      (SubstDomain K π)
  /-- The basis vector indexed by `i` is literally `X^i`. -/
  weierstrassBasis_apply : ∀ i,
    (weierstrassBasis i).toPowerSeries = PowerSeries.X ^ (i : ℕ)
  /-- Matrix assigned to multiplication by each series. -/
  multiplicationMatrix : PowerSeries (RingOfIntegers K) →
    Matrix (Fin (residueCard K)) (Fin (residueCard K))
      (PowerSeries (RingOfIntegers K))
  /-- It is the actual matrix of `x ↦ gx` in the displayed Weierstrass basis. -/
  multiplicationMatrix_apply : ∀ g, multiplicationMatrix g =
    LinearMap.toMatrix weierstrassBasis weierstrassBasis
      (LinearMap.mulLeft (PowerSeries (RingOfIntegers K))
        (SubstDomain.ofPowerSeries K π g))
  /-- The multiplicative Coleman operator. -/
  operator : PowerSeries (RingOfIntegers K) →* PowerSeries (RingOfIntegers K)
  /--
  The defining identity `𝒩(g)(f(X)) = det(m_g)`, in the nominal target.  The scalar determinant
  is embedded by the substitution action before it is compared with the underlying series.
  -/
  determinant_spec : ∀ g,
    SubstDomain.ofPowerSeries K π
        (PowerSeries.subst (lubinTateSeries K π) (operator g)) =
      algebraMap (PowerSeries (RingOfIntegers K)) (SubstDomain K π)
        (Matrix.det (multiplicationMatrix g))

private theorem coleman_uniformizerInteger_mem_maximalIdeal (π : Uniformizer K) :
    uniformizerInteger K π ∈ LocalMaximalIdeal K := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hpunit
  obtain ⟨u, hu⟩ := hpunit
  let x := Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom u
  have hxnonneg : 0 ≤ normalizedValuation K x :=
    (exists_normalizedValuationHom K).choose_spec.2 x |>.2
      ⟨(u : RingOfIntegers K), rfl⟩
  have hxinvnonneg : 0 ≤ normalizedValuation K x⁻¹ :=
    (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.2
      ⟨((u⁻¹ : Units (RingOfIntegers K)) : RingOfIntegers K), rfl⟩
  have hxinv : normalizedValuation K x⁻¹ = -normalizedValuation K x := by
    simp [normalizedValuation]
  have hxzero : normalizedValuation K x = 0 := by omega
  have hxp : x = π.val := by
    apply Units.ext
    change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
    rw [hu]
    exact (uniformizer_integer_exists K π).choose_spec
  rw [hxp, π.valuation_eq_one] at hxzero
  omega

private theorem coleman_lubinTateSeries_constantCoeff (π : Uniformizer K) :
    PowerSeries.constantCoeff (lubinTateSeries K π) = 0 := by
  have hq : residueCard K ≠ 0 := Nat.card_pos.ne'
  simp [lubinTateSeries, lubinTatePolynomial, hq]

private theorem coleman_lubinTateSeries_map_residue (π : Uniformizer K) :
    (lubinTateSeries K π).map (IsLocalRing.residue (RingOfIntegers K)) =
      PowerSeries.X ^ residueCard K := by
  have hpzero :
      IsLocalRing.residue (RingOfIntegers K) (uniformizerInteger K π) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact coleman_uniformizerInteger_mem_maximalIdeal K π
  rw [lubinTateSeries, lubinTatePolynomial]
  simp [hpzero]

/--
**L04**, Lemma `lem:coleman-norm`: Weierstrass division gives the pinned finite-free
substitution algebra and determinant of actual multiplication defines the Coleman norm.
-/
theorem colemanNorm_exists (π : Uniformizer K) :
    Nonempty (ColemanNormData K π) := by
  classical
  let R := RingOfIntegers K
  let A := PowerSeries R
  let f := lubinTateSeries K π
  let I := LocalMaximalIdeal K
  let q := residueCard K
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : IsAdicComplete I R := by
    dsimp [I, R]
    infer_instance
  have hf0 : PowerSeries.constantCoeff f = 0 :=
    coleman_lubinTateSeries_constantCoeff K π
  have hfmap : f.map (IsLocalRing.residue R) = PowerSeries.X ^ q :=
    coleman_lubinTateSeries_map_residue K π
  have hfne : f.map (IsLocalRing.residue R) ≠ 0 := by
    rw [hfmap]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  let H : f.IsWeierstrassDivisorAt I :=
    PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hfne
  have horder : (f.map (Ideal.Quotient.mk I)).order.toNat = q := by
    change (f.map (IsLocalRing.residue R)).order.toNat = q
    rw [hfmap, PowerSeries.order_X_pow]
    simp
  let v : Fin q → SubstDomain K π := fun i =>
    SubstDomain.ofPowerSeries K π (PowerSeries.X ^ (i : ℕ))
  let lc : (Fin q → A) →ₗ[A] SubstDomain K π :=
    Fintype.linearCombination A v
  have hlc_apply (a : Fin q → A) :
      (lc a).toPowerSeries = PowerSeries.colemanPresentation (f := f) q a := by
    dsimp [lc]
    rw [Fintype.linearCombination_apply, PowerSeries.colemanPresentation]
    change SubstDomain.ringEquiv K π (∑ i, a i • v i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [v]
    change (a i • SubstDomain.ofPowerSeries K π
      (PowerSeries.X ^ (i : ℕ))).toPowerSeries = _
    exact SubstDomain.smul_apply K π _ _
  have hraw : Function.Bijective (PowerSeries.colemanPresentation (f := f) q) := by
    constructor
    · intro a b hab
      rw [← PowerSeries.coleman_coord_raw I H hf0 q horder a,
        ← PowerSeries.coleman_coord_raw I H hf0 q horder b, hab]
    · intro g
      exact ⟨PowerSeries.colemanCoordinates I H q g,
        PowerSeries.coleman_raw_coord I H hf0 q horder g⟩
  have hlc : Function.Bijective lc := by
    constructor
    · intro a b hab
      apply hraw.1
      rw [← hlc_apply a, ← hlc_apply b, hab]
    · intro g
      obtain ⟨a, ha⟩ := hraw.2 g.toPowerSeries
      refine ⟨a, SubstDomain.ext ?_⟩
      rw [hlc_apply, ha]
  let e : (Fin q → A) ≃ₗ[A] SubstDomain K π := LinearEquiv.ofBijective lc hlc
  let b : Module.Basis (Fin q) A (SubstDomain K π) :=
    Module.Basis.ofEquivFun e.symm
  have hb (i : Fin q) : (b i).toPowerSeries = PowerSeries.X ^ (i : ℕ) := by
    dsimp [b]
    rw [Module.Basis.coe_ofEquivFun]
    change (e (Pi.single i 1)).toPowerSeries = _
    change (lc (Pi.single i 1)).toPowerSeries = _
    dsimp [lc]
    rw [Fintype.linearCombination_apply]
    simp [v]
  let mat : A → Matrix (Fin q) (Fin q) A := fun g =>
    LinearMap.toMatrix b b
      (LinearMap.mulLeft A (SubstDomain.ofPowerSeries K π g))
  let op : A →* A :=
    { toFun := fun g => LinearMap.det
        (LinearMap.mulLeft A (SubstDomain.ofPowerSeries K π g))
      map_one' := by
        change LinearMap.det (LinearMap.mulLeft A (1 : SubstDomain K π)) = 1
        rw [LinearMap.mulLeft_one, LinearMap.det_id]
      map_mul' := by
        intro g h
        change LinearMap.det (LinearMap.mulLeft A
          (SubstDomain.ofPowerSeries K π g * SubstDomain.ofPowerSeries K π h)) = _
        rw [LinearMap.mulLeft_mul, LinearMap.det_comp] }
  refine ⟨⟨b, hb, mat, fun g => rfl, op, ?_⟩⟩
  intro g
  apply SubstDomain.ext
  simp only [SubstDomain.toPowerSeries_ofPowerSeries,
    SubstDomain.algebraMap_apply]
  change PowerSeries.subst f
      (LinearMap.det (LinearMap.mulLeft A (SubstDomain.ofPowerSeries K π g))) =
    PowerSeries.subst f (Matrix.det (mat g))
  exact congrArg (PowerSeries.subst f)
    (LinearMap.det_toMatrix b
      (LinearMap.mulLeft A (SubstDomain.ofPowerSeries K π g))).symm

/-- The chosen determinant-defined Coleman norm. -/
noncomputable def colemanNorm (π : Uniformizer K) : ColemanNormData K π :=
  (colemanNorm_exists K π).some

/-- The principal ideal `(π)`. -/
def uniformizerIdeal (π : Uniformizer K) : Ideal (RingOfIntegers K) :=
  Ideal.span {uniformizerInteger K π}

private theorem colemanNorm_algMap_injective (π : Uniformizer K) (D : ColemanNormData K π) :
    Function.Injective (algebraMap (PowerSeries (RingOfIntegers K)) (SubstDomain K π)) := by
  classical
  intro a b hab
  have hq : 0 < residueCard K := Nat.card_pos
  let i : Fin (residueCard K) := ⟨0, hq⟩
  have hact : a • D.weierstrassBasis i = b • D.weierstrassBasis i := by
    rw [Algebra.smul_def, Algebra.smul_def, hab]
  have hcoord := congrArg (fun x => D.weierstrassBasis.repr x i) hact
  simpa [i] using hcoord

private theorem colemanNorm_operator_eq_det (π : Uniformizer K) (D : ColemanNormData K π)
    (g : PowerSeries (RingOfIntegers K)) :
    D.operator g = Matrix.det (D.multiplicationMatrix g) := by
  apply colemanNorm_algMap_injective K π D
  calc
    algebraMap (PowerSeries (RingOfIntegers K)) (SubstDomain K π) (D.operator g) =
        SubstDomain.ofPowerSeries K π
          (PowerSeries.subst (lubinTateSeries K π) (D.operator g)) := by
      apply SubstDomain.ext
      simp
    _ = _ := D.determinant_spec g

private theorem colemanNorm_matrix_add (π : Uniformizer K) (D : ColemanNormData K π)
    (g h : PowerSeries (RingOfIntegers K)) :
    D.multiplicationMatrix (g + h) = D.multiplicationMatrix g + D.multiplicationMatrix h := by
  classical
  rw [D.multiplicationMatrix_apply, D.multiplicationMatrix_apply,
    D.multiplicationMatrix_apply]
  have hlin : LinearMap.mulLeft (PowerSeries (RingOfIntegers K))
      (SubstDomain.ofPowerSeries K π (g + h)) =
      LinearMap.mulLeft _ (SubstDomain.ofPowerSeries K π g) +
        LinearMap.mulLeft _ (SubstDomain.ofPowerSeries K π h) := by
    apply LinearMap.ext
    intro x
    apply SubstDomain.ext
    change (g + h) * x.toPowerSeries = g * x.toPowerSeries + h * x.toPowerSeries
    ring
  rw [hlin, map_add]

private theorem colemanNorm_matrix_mul (π : Uniformizer K) (D : ColemanNormData K π)
    (g h : PowerSeries (RingOfIntegers K)) :
    D.multiplicationMatrix (g * h) = D.multiplicationMatrix g * D.multiplicationMatrix h := by
  classical
  rw [D.multiplicationMatrix_apply, D.multiplicationMatrix_apply,
    D.multiplicationMatrix_apply]
  change LinearMap.toMatrix D.weierstrassBasis D.weierstrassBasis
      (LinearMap.mulLeft _ (SubstDomain.ofPowerSeries K π g *
        SubstDomain.ofPowerSeries K π h)) = _
  rw [LinearMap.mulLeft_mul,
    LinearMap.toMatrix_comp D.weierstrassBasis D.weierstrassBasis D.weierstrassBasis]

private theorem colemanNorm_matrix_one (π : Uniformizer K) (D : ColemanNormData K π) :
    D.multiplicationMatrix 1 = 1 := by
  classical
  rw [D.multiplicationMatrix_apply]
  change LinearMap.toMatrix D.weierstrassBasis D.weierstrassBasis
    (LinearMap.mulLeft _ (1 : SubstDomain K π)) = 1
  rw [LinearMap.mulLeft_one, LinearMap.toMatrix_id]

private theorem colemanNorm_matrix_scalar (π : Uniformizer K) (D : ColemanNormData K π)
    (a : PowerSeries (RingOfIntegers K)) :
    D.multiplicationMatrix (PowerSeries.subst (lubinTateSeries K π) a) =
      a • (1 : Matrix (Fin (residueCard K)) (Fin (residueCard K))
        (PowerSeries (RingOfIntegers K))) := by
  classical
  rw [D.multiplicationMatrix_apply]
  rw [← LinearMap.toMatrix_id D.weierstrassBasis]
  rw [← map_smul]
  have hlin : LinearMap.mulLeft (PowerSeries (RingOfIntegers K))
      (SubstDomain.ofPowerSeries K π (PowerSeries.subst (lubinTateSeries K π) a)) =
      a • (LinearMap.id : SubstDomain K π →ₗ[PowerSeries (RingOfIntegers K)]
        SubstDomain K π) := by
    apply LinearMap.ext
    intro x
    apply SubstDomain.ext
    simp [Algebra.smul_def]
  rw [hlin]

private theorem colemanNorm_matrix_pow (π : Uniformizer K) (D : ColemanNormData K π)
    (g : PowerSeries (RingOfIntegers K)) (n : ℕ) :
    D.multiplicationMatrix (g ^ n) = D.multiplicationMatrix g ^ n := by
  induction n with
  | zero => simp [colemanNorm_matrix_one K π D]
  | succ n ih => rw [pow_succ, colemanNorm_matrix_mul K π D, ih, pow_succ]

private theorem colemanNorm_powerSeries_eq_C_mul_of_coeff_dvd
    {R : Type u} [CommRing R] (a : R) (g : PowerSeries R)
    (hg : ∀ n, a ∣ PowerSeries.coeff n g) :
    ∃ h : PowerSeries R, g = PowerSeries.C a * h := by
  choose c hc using hg
  let h : PowerSeries R := PowerSeries.mk c
  refine ⟨h, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hc n

private theorem colemanNorm_congruent_factor (π : Uniformizer K) (r : ℕ)
    (g h : PowerSeries (RingOfIntegers K))
    (hgh : PowerSeriesCongruent K (uniformizerIdeal K π ^ r) g h) :
    ∃ z : PowerSeries (RingOfIntegers K),
      g = h + PowerSeries.C (uniformizerInteger K π ^ r) * z := by
  have hdvd (n : ℕ) : uniformizerInteger K π ^ r ∣
      PowerSeries.coeff n (g - h) := by
    rw [map_sub]
    have hm := hgh n
    rw [uniformizerIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
    exact hm
  obtain ⟨z, hz⟩ := colemanNorm_powerSeries_eq_C_mul_of_coeff_dvd
    (uniformizerInteger K π ^ r) (g - h) hdvd
  refine ⟨z, ?_⟩
  calc
    g = h + (g - h) := by ring
    _ = h + PowerSeries.C (uniformizerInteger K π ^ r) * z := by rw [hz]

private theorem colemanNorm_normalizedValuation_inv (x : Units K) :
    normalizedValuation K x⁻¹ = -normalizedValuation K x := by
  simp [normalizedValuation]

private theorem colemanNorm_isUnit_of_normalizedValuation_eq_zero
    (a : RingOfIntegers K) (ha : (a : K) ≠ 0)
    (hval : normalizedValuation K (Units.mk0 (a : K) ha) = 0) : IsUnit a := by
  let x : Units K := Units.mk0 (a : K) ha
  have hxinv : normalizedValuation K x⁻¹ = 0 := by
    rw [colemanNorm_normalizedValuation_inv K, hval, neg_zero]
  obtain ⟨b, hb⟩ := (exists_normalizedValuationHom K).choose_spec.2 x⁻¹ |>.1 hxinv.ge
  let u : Units (RingOfIntegers K) :=
    { val := a
      inv := b
      val_inv := by
        apply Subtype.ext
        change (a : K) * (b : K) = 1
        rw [hb]
        exact mul_inv_cancel₀ ha
      inv_val := by
        apply Subtype.ext
        change (b : K) * (a : K) = 1
        rw [hb]
        exact inv_mul_cancel₀ ha }
  exact ⟨u, rfl⟩

private theorem colemanNorm_uniformizerInteger_irreducible (π : Uniformizer K) :
    Irreducible (uniformizerInteger K π) := by
  let p := uniformizerInteger K π
  have hp : (p : K) = (π.val : K) := (uniformizer_integer_exists K π).choose_spec
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hunit
    obtain ⟨u, hu⟩ := hunit
    have huval : normalizedValuation K
        (Units.map (algebraMap (RingOfIntegers K) K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
      rw [colemanNorm_normalizedValuation_inv K] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers K) K) u = π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
      rw [hu, hp]
    rw [heq, π.valuation_eq_one] at huval
    omega
  · intro a b hab
    have ha0 : (a : K) ≠ 0 := by
      intro ha
      have : (p : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [ha]
      apply π.val.ne_zero
      rw [← hp]
      exact this
    have hb0 : (b : K) ≠ 0 := by
      intro hb
      have : (p : K) = 0 := by
        change ((uniformizerInteger K π : RingOfIntegers K) : K) = 0
        rw [hab]
        simp [hb]
      apply π.val.ne_zero
      rw [← hp]
      exact this
    let ua : Units K := Units.mk0 (a : K) ha0
    let ub : Units K := Units.mk0 (b : K) hb0
    have hva : 0 ≤ normalizedValuation K ua :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨a, rfl⟩
    have hvb : 0 ≤ normalizedValuation K ub :=
      (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨b, rfl⟩
    have huv : ua * ub = π.val := by
      apply Units.ext
      simpa [ua, ub, ← hp] using congr_arg Subtype.val hab.symm
    have hvsum : normalizedValuation K ua + normalizedValuation K ub = 1 := by
      rw [← normalizedValuation_mul, huv, π.valuation_eq_one]
    rcases (show normalizedValuation K ua = 0 ∨ normalizedValuation K ub = 0 by omega) with
      ha | hb
    · exact Or.inl (colemanNorm_isUnit_of_normalizedValuation_eq_zero K a ha0 ha)
    · exact Or.inr (colemanNorm_isUnit_of_normalizedValuation_eq_zero K b hb0 hb)

private theorem colemanNorm_maximalIdeal_eq (π : Uniformizer K) :
    uniformizerIdeal K π = LocalMaximalIdeal K :=
  (colemanNorm_uniformizerInteger_irreducible K π).maximalIdeal_eq.symm

private theorem colemanNorm_map_eq_of_factor (π : Uniformizer K) (D : ColemanNormData K π)
    (x y z : PowerSeries (RingOfIntegers K))
    (hxy : x = y + PowerSeries.C (uniformizerInteger K π) * z) :
    (D.multiplicationMatrix x).map
        (PowerSeries.map (IsLocalRing.residue (RingOfIntegers K))) =
      (D.multiplicationMatrix y).map
        (PowerSeries.map (IsLocalRing.residue (RingOfIntegers K))) := by
  classical
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  rw [hxy, colemanNorm_matrix_add K π D, colemanNorm_matrix_mul K π D]
  have hCp : PowerSeries.C (uniformizerInteger K π) =
      PowerSeries.subst (lubinTateSeries K π)
        (PowerSeries.C (uniformizerInteger K π)) := by
    symm
    exact PowerSeries.subst_C (uniformizerInteger K π)
  rw [hCp, colemanNorm_matrix_scalar K π D]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    smul_eq_mul]
  have hp : ρ (uniformizerInteger K π) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    change uniformizerInteger K π ∈ LocalMaximalIdeal K
    rw [← colemanNorm_maximalIdeal_eq K π]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  simp [ρ, hp]

private theorem colemanNorm_mvPowerSeries_expand_card_fintype
    {σ k : Type*} [Field k] [Fintype k] (f : MvPowerSeries σ k) :
    f.expand (Fintype.card k) Fintype.card_ne_zero = f ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases FiniteField.card k p with ⟨⟨n, _⟩, ⟨hp, hn⟩⟩
  letI : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  have h := MvPowerSeries.map_iterateFrobenius_expand p hp.ne_zero f n
  rw [iterateFrobenius_eq_pow, FiniteField.frobenius_pow hn] at h
  rw [show (1 : k →+* k) = RingHom.id k from rfl, map_id] at h
  change f.expand (p ^ n) (pow_ne_zero n hp.ne_zero) = f ^ p ^ n at h
  simpa only [hn] using h

private theorem colemanNorm_mvPowerSeries_expand_card
    {σ k : Type*} [Field k] [Finite k] (f : MvPowerSeries σ k) :
    f.expand (Nat.card k) (Nat.card_pos.ne') = f ^ Nat.card k := by
  letI := Fintype.ofFinite k
  simpa only [Nat.card_eq_fintype_card] using colemanNorm_mvPowerSeries_expand_card_fintype f

private theorem colemanNorm_frobenius_factor (π : Uniformizer K)
    (g : PowerSeries (RingOfIntegers K)) :
    ∃ z : PowerSeries (RingOfIntegers K),
      g ^ residueCard K = PowerSeries.subst (lubinTateSeries K π) g +
        PowerSeries.C (uniformizerInteger K π) * z := by
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  let q := residueCard K
  have hq : q ≠ 0 := Nat.card_pos.ne'
  have hf0 : PowerSeries.constantCoeff (lubinTateSeries K π) = 0 := by
    have hq' : residueCard K ≠ 0 := Nat.card_pos.ne'
    simp [lubinTateSeries, lubinTatePolynomial, hq']
  have hpzero : ρ (uniformizerInteger K π) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    change uniformizerInteger K π ∈ LocalMaximalIdeal K
    rw [← colemanNorm_maximalIdeal_eq K π]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hfmap : MvPowerSeries.map ρ (lubinTateSeries K π) =
      PowerSeries.X ^ q := by
    change PowerSeries.map ρ (lubinTateSeries K π) = PowerSeries.X ^ q
    rw [lubinTateSeries, lubinTatePolynomial]
    simp [q, hpzero]
  have hmap : PowerSeries.map ρ (g ^ q) =
      PowerSeries.map ρ (PowerSeries.subst (lubinTateSeries K π) g) := by
    rw [map_pow]
    change (PowerSeries.map ρ g) ^ q =
      MvPowerSeries.map ρ (PowerSeries.subst (lubinTateSeries K π) g)
    rw [PowerSeries.map_subst (h := ρ)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) g]
    rw [hfmap]
    rw [← PowerSeries.expand_apply q hq]
    exact (colemanNorm_mvPowerSeries_expand_card (PowerSeries.map ρ g)).symm
  have hdvd (n : ℕ) : uniformizerInteger K π ∣
      PowerSeries.coeff n (g ^ q - PowerSeries.subst (lubinTateSeries K π) g) := by
    rw [← Ideal.mem_span_singleton]
    change PowerSeries.coeff n
      (g ^ q - PowerSeries.subst (lubinTateSeries K π) g) ∈ uniformizerIdeal K π
    rw [colemanNorm_maximalIdeal_eq K π, ← IsLocalRing.residue_eq_zero_iff]
    have hc := congrArg (PowerSeries.coeff n) hmap
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at hc
    simpa only [map_sub, sub_eq_zero] using hc
  obtain ⟨z, hz⟩ := colemanNorm_powerSeries_eq_C_mul_of_coeff_dvd
    (uniformizerInteger K π)
    (g ^ q - PowerSeries.subst (lubinTateSeries K π) g) hdvd
  refine ⟨z, ?_⟩
  calc
    g ^ q = PowerSeries.subst (lubinTateSeries K π) g +
        (g ^ q - PowerSeries.subst (lubinTateSeries K π) g) := by ring
    _ = _ := by rw [hz]

private theorem colemanNorm_expand_injective {k : Type*} [CommRing k]
    (q : ℕ) (hq : q ≠ 0) : Function.Injective (PowerSeries.expand q hq : PowerSeries k → PowerSeries k) := by
  intro x y hxy
  ext n
  have hc := congrArg (PowerSeries.coeff (q * n)) hxy
  simpa only [PowerSeries.coeff_expand_mul] using hc

private theorem colemanNorm_mul_expansion (π : Uniformizer K) (D : ColemanNormData K π)
    (z : PowerSeries (RingOfIntegers K)) (j : Fin (residueCard K)) :
    z * PowerSeries.X ^ (j : ℕ) =
      ∑ i : Fin (residueCard K),
        PowerSeries.subst (lubinTateSeries K π) (D.multiplicationMatrix z i j) *
          PowerSeries.X ^ (i : ℕ) := by
  classical
  let T := LinearMap.mulLeft (PowerSeries (RingOfIntegers K))
    (SubstDomain.ofPowerSeries K π z)
  have hsum := D.weierstrassBasis.sum_repr (T (D.weierstrassBasis j))
  have hsum' := congrArg (SubstDomain.ringEquiv K π) hsum
  rw [map_sum] at hsum'
  change (∑ i, ((D.weierstrassBasis.repr
      (T (D.weierstrassBasis j))) i • D.weierstrassBasis i).toPowerSeries) =
    (SubstDomain.ofPowerSeries K π z * D.weierstrassBasis j).toPowerSeries at hsum'
  simp_rw [SubstDomain.smul_apply] at hsum'
  simp_rw [D.weierstrassBasis_apply] at hsum'
  rw [SubstDomain.toPowerSeries_mul, SubstDomain.toPowerSeries_ofPowerSeries,
    D.weierstrassBasis_apply] at hsum'
  rw [D.multiplicationMatrix_apply]
  simp_rw [LinearMap.toMatrix_apply]
  exact hsum'.symm

private theorem colemanNorm_mapped_expansion (π : Uniformizer K) (D : ColemanNormData K π)
    (z : PowerSeries (RingOfIntegers K)) (j : Fin (residueCard K)) :
    let ρ := IsLocalRing.residue (RingOfIntegers K)
    PowerSeries.map ρ z * PowerSeries.X ^ (j : ℕ) =
      ∑ i : Fin (residueCard K),
        PowerSeries.subst (PowerSeries.X ^ residueCard K)
          (PowerSeries.map ρ (D.multiplicationMatrix z i j)) *
          PowerSeries.X ^ (i : ℕ) := by
  classical
  dsimp only
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  have hq : residueCard K ≠ 0 := Nat.card_pos.ne'
  have hf0 : PowerSeries.constantCoeff (lubinTateSeries K π) = 0 := by
    simp [lubinTateSeries, lubinTatePolynomial, hq]
  have hpzero : ρ (uniformizerInteger K π) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    change uniformizerInteger K π ∈ LocalMaximalIdeal K
    rw [← colemanNorm_maximalIdeal_eq K π]
    exact Ideal.mem_span_singleton.mpr (dvd_refl _)
  have hfmap : MvPowerSeries.map ρ (lubinTateSeries K π) =
      PowerSeries.X ^ residueCard K := by
    change PowerSeries.map ρ (lubinTateSeries K π) =
      PowerSeries.X ^ residueCard K
    rw [lubinTateSeries, lubinTatePolynomial]
    simp [hpzero]
  calc
    PowerSeries.map ρ z * PowerSeries.X ^ (j : ℕ) =
        PowerSeries.map ρ (z * PowerSeries.X ^ (j : ℕ)) := by
      rw [map_mul, map_pow, PowerSeries.map_X]
    _ = PowerSeries.map ρ (∑ i : Fin (residueCard K),
          PowerSeries.subst (lubinTateSeries K π) (D.multiplicationMatrix z i j) *
            PowerSeries.X ^ (i : ℕ)) :=
      congrArg (PowerSeries.map ρ) (colemanNorm_mul_expansion K π D z j)
    _ = ∑ i : Fin (residueCard K), PowerSeries.map ρ
          (PowerSeries.subst (lubinTateSeries K π) (D.multiplicationMatrix z i j) *
            PowerSeries.X ^ (i : ℕ)) := by rw [map_sum]
    _ = ∑ i : Fin (residueCard K),
          PowerSeries.subst (PowerSeries.X ^ residueCard K)
            (PowerSeries.map ρ (D.multiplicationMatrix z i j)) *
              PowerSeries.X ^ (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, map_pow, PowerSeries.map_X]
      change MvPowerSeries.map ρ
          (PowerSeries.subst (lubinTateSeries K π) (D.multiplicationMatrix z i j)) * _ = _
      rw [PowerSeries.map_subst (h := ρ)
        (PowerSeries.HasSubst.of_constantCoeff_zero' hf0), hfmap]

private theorem colemanNorm_diagonal_coeff (π : Uniformizer K) (D : ColemanNormData K π)
    (z : PowerSeries (RingOfIntegers K)) (j : Fin (residueCard K)) (n : ℕ) :
    let ρ := IsLocalRing.residue (RingOfIntegers K)
    PowerSeries.coeff n (PowerSeries.map ρ (D.multiplicationMatrix z j j)) =
      PowerSeries.coeff (residueCard K * n) (PowerSeries.map ρ z) := by
  classical
  dsimp only
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  let q := residueCard K
  have hq : q ≠ 0 := Nat.card_pos.ne'
  have heq := colemanNorm_mapped_expansion K π D z j
  dsimp only at heq
  have hc := congrArg (PowerSeries.coeff (q * n + (j : ℕ))) heq
  rw [PowerSeries.coeff_mul_X_pow] at hc
  have hrs : PowerSeries.coeff (q * n + (j : ℕ))
      (∑ i : Fin q,
        PowerSeries.subst (PowerSeries.X ^ q)
          (PowerSeries.map ρ (D.multiplicationMatrix z i j)) *
            PowerSeries.X ^ (i : ℕ)) =
      PowerSeries.coeff n (PowerSeries.map ρ (D.multiplicationMatrix z j j)) := by
    rw [map_sum, Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_mul_X_pow]
      rw [PowerSeries.coeff_subst_X_pow (S := LocalResidueField K) hq]
      simp [hq]
    · intro i hi hij
      rw [PowerSeries.coeff_mul_X_pow']
      split_ifs with hid
      · rw [PowerSeries.coeff_subst_X_pow (S := LocalResidueField K) hq]
        rw [if_neg]
        intro hdvd
        obtain ⟨c, hcdiv⟩ := hdvd
        have heqnat : q * n + (j : ℕ) = q * c + (i : ℕ) := by
          omega
        have hjlt : (j : ℕ) < q := j.isLt
        have hilt : (i : ℕ) < q := i.isLt
        have hleft : (q * n + (j : ℕ)) % q = (j : ℕ) := by
          simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hjlt]
        have hright : (q * c + (i : ℕ)) % q = (i : ℕ) := by
          simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hilt]
        have hmod := congrArg (fun x : ℕ => x % q) heqnat
        rw [hleft, hright] at hmod
        exact hij (Fin.ext hmod.symm)
      · rfl
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hrs] at hc
  exact hc.symm

private theorem colemanNorm_trace_map_zero (π : Uniformizer K) (D : ColemanNormData K π)
    (z : PowerSeries (RingOfIntegers K)) :
    PowerSeries.map (IsLocalRing.residue (RingOfIntegers K))
      (Matrix.trace (D.multiplicationMatrix z)) = 0 := by
  classical
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  let q := residueCard K
  have ht := AddMonoidHom.map_trace (PowerSeries.map ρ)
    (D.multiplicationMatrix z)
  change PowerSeries.map ρ (Matrix.trace (D.multiplicationMatrix z)) =
    Matrix.trace ((D.multiplicationMatrix z).map (PowerSeries.map ρ)) at ht
  rw [ht]
  ext n
  rw [Matrix.trace, map_sum]
  change (∑ i : Fin q, PowerSeries.coeff n
      (PowerSeries.map ρ (D.multiplicationMatrix z i i))) = 0
  calc
    (∑ i : Fin q, PowerSeries.coeff n
        (PowerSeries.map ρ (D.multiplicationMatrix z i i))) =
        ∑ _i : Fin q, PowerSeries.coeff (q * n) (PowerSeries.map ρ z) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact colemanNorm_diagonal_coeff K π D z i n
    _ = 0 := by
      rw [Fin.sum_const, nsmul_eq_mul]
      have hcast : (q : LocalResidueField K) = 0 := by
        letI := Fintype.ofFinite (LocalResidueField K)
        change (Nat.card (LocalResidueField K) : LocalResidueField K) = 0
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.cast_card_eq_zero (K := LocalResidueField K)
      rw [hcast, zero_mul]

private theorem colemanNorm_map_operator_eq (π : Uniformizer K) (D : ColemanNormData K π)
    (g : PowerSeries (RingOfIntegers K)) :
    PowerSeries.map (IsLocalRing.residue (RingOfIntegers K)) (D.operator g) =
      PowerSeries.map (IsLocalRing.residue (RingOfIntegers K)) g := by
  classical
  let ρ := IsLocalRing.residue (RingOfIntegers K)
  let Φ := PowerSeries.map ρ
  let q := residueCard K
  have hq : q ≠ 0 := Nat.card_pos.ne'
  let B := (D.multiplicationMatrix g).map Φ
  obtain ⟨z, hz⟩ := colemanNorm_frobenius_factor K π g
  have hBpow : B ^ q = (Φ g) • (1 : Matrix (Fin q) (Fin q)
      (PowerSeries (LocalResidueField K))) := by
    calc
      B ^ q = (D.multiplicationMatrix g ^ q).map Φ := by
        exact (Matrix.map_pow (D.multiplicationMatrix g) Φ q).symm
      _ = (D.multiplicationMatrix (g ^ q)).map Φ := by
        rw [colemanNorm_matrix_pow K π D]
      _ = (D.multiplicationMatrix
          (PowerSeries.subst (lubinTateSeries K π) g)).map Φ :=
        colemanNorm_map_eq_of_factor K π D _ _ z hz
      _ = (g • (1 : Matrix (Fin q) (Fin q)
          (PowerSeries (RingOfIntegers K)))).map Φ := by
        rw [colemanNorm_matrix_scalar K π D]
      _ = (Φ g) • (1 : Matrix (Fin q) (Fin q)
          (PowerSeries (LocalResidueField K))) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Φ]
        · simp [Φ, hij]
  have hdetpow := congrArg Matrix.det hBpow
  have hpowers : Matrix.det B ^ q = (Φ g) ^ q := by
    rw [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at hdetpow
    exact hdetpow
  have hdet : Matrix.det B = Φ g := by
    apply colemanNorm_expand_injective q hq
    calc
      (Matrix.det B).expand q hq = Matrix.det B ^ q := by
        exact colemanNorm_mvPowerSeries_expand_card (Matrix.det B)
      _ = (Φ g) ^ q := hpowers
      _ = (Φ g).expand q hq := by
        symm
        exact colemanNorm_mvPowerSeries_expand_card (Φ g)
  rw [colemanNorm_operator_eq_det K π D]
  change Φ (Matrix.det (D.multiplicationMatrix g)) = Φ g
  rw [RingHom.map_det]
  change Matrix.det B = Φ g
  exact hdet

private theorem colemanNorm_congruent_of_map_eq (π : Uniformizer K)
    (g h : PowerSeries (RingOfIntegers K))
    (heq : PowerSeries.map (IsLocalRing.residue (RingOfIntegers K)) g =
      PowerSeries.map (IsLocalRing.residue (RingOfIntegers K)) h) :
    PowerSeriesCongruent K (uniformizerIdeal K π) g h := by
  intro n
  rw [colemanNorm_maximalIdeal_eq K π, ← IsLocalRing.residue_eq_zero_iff]
  have hc := congrArg (PowerSeries.coeff n) heq
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at hc
  simpa only [map_sub, sub_eq_zero] using hc


/--
**L05**, Lemma `lem:coleman-norm` (a)--(b): reduction modulo `π` fixes a unit, and for
`r≥1` one Coleman application improves `1 mod π^r` to `1 mod π^(r+1)`.
-/
theorem colemanNorm_congruences (π : Uniformizer K)
    (g : PowerSeries (RingOfIntegers K)) (hg : IsUnit g) :
    PowerSeriesCongruent K (uniformizerIdeal K π)
      ((colemanNorm K π).operator g) g ∧
    ∀ r, 1 ≤ r → PowerSeriesCongruent K (uniformizerIdeal K π ^ r) g 1 →
      PowerSeriesCongruent K (uniformizerIdeal K π ^ (r + 1))
        ((colemanNorm K π).operator g) 1 := by
  classical
  clear hg
  let D := colemanNorm K π
  constructor
  · apply colemanNorm_congruent_of_map_eq K π
    exact colemanNorm_map_operator_eq K π D g
  · intro r hr hgr
    obtain ⟨z, hz⟩ := colemanNorm_congruent_factor K π r g 1 hgr
    have hmat : D.multiplicationMatrix g =
        1 + PowerSeries.C (uniformizerInteger K π ^ r) •
          D.multiplicationMatrix z := by
      rw [hz, colemanNorm_matrix_add K π D, colemanNorm_matrix_one K π D,
        colemanNorm_matrix_mul K π D]
      have hCp : PowerSeries.C (uniformizerInteger K π ^ r) =
          PowerSeries.subst (lubinTateSeries K π)
            (PowerSeries.C (uniformizerInteger K π ^ r)) := by
        symm
        exact PowerSeries.subst_C (uniformizerInteger K π ^ r)
      have hMC : D.multiplicationMatrix
          (PowerSeries.C (uniformizerInteger K π ^ r)) =
          PowerSeries.C (uniformizerInteger K π ^ r) •
            (1 : Matrix (Fin (residueCard K)) (Fin (residueCard K))
              (PowerSeries (RingOfIntegers K))) := by
        calc
          D.multiplicationMatrix (PowerSeries.C (uniformizerInteger K π ^ r)) =
              D.multiplicationMatrix (PowerSeries.subst (lubinTateSeries K π)
                (PowerSeries.C (uniformizerInteger K π ^ r))) := congrArg _ hCp
          _ = _ := colemanNorm_matrix_scalar K π D _
      rw [hMC, Matrix.smul_mul, one_mul]
    have htrace_dvd (n : ℕ) : uniformizerInteger K π ∣
        PowerSeries.coeff n (Matrix.trace (D.multiplicationMatrix z)) := by
      rw [← Ideal.mem_span_singleton]
      change PowerSeries.coeff n (Matrix.trace (D.multiplicationMatrix z)) ∈
        uniformizerIdeal K π
      rw [colemanNorm_maximalIdeal_eq K π, ← IsLocalRing.residue_eq_zero_iff]
      have hztrace := congrArg (PowerSeries.coeff n) (colemanNorm_trace_map_zero K π D z)
      rw [PowerSeries.coeff_map] at hztrace
      simpa using hztrace
    obtain ⟨t, ht⟩ := colemanNorm_powerSeries_eq_C_mul_of_coeff_dvd
      (uniformizerInteger K π) (Matrix.trace (D.multiplicationMatrix z)) htrace_dvd
    let W : PowerSeries (RingOfIntegers K) :=
      Polynomial.eval (PowerSeries.C (uniformizerInteger K π ^ r))
        (Matrix.det (1 + (Polynomial.X : Polynomial
          (PowerSeries (RingOfIntegers K))) •
            (D.multiplicationMatrix z).map Polynomial.C)).divX.divX
    have hdetexpand : D.operator g =
        1 + Matrix.trace (D.multiplicationMatrix z) *
            PowerSeries.C (uniformizerInteger K π ^ r) +
          W * PowerSeries.C (uniformizerInteger K π ^ r) ^ 2 := by
      rw [colemanNorm_operator_eq_det K π D, hmat,
        Matrix.det_one_add_smul]
    have hpowfactor : (uniformizerInteger K π ^ r) ^ 2 =
        uniformizerInteger K π ^ (r + 1) *
          uniformizerInteger K π ^ (r - 1) := by
      rw [pow_two, ← pow_add, ← pow_add]
      congr 1
      omega
    have hC1 : PowerSeries.C (uniformizerInteger K π) *
        PowerSeries.C (uniformizerInteger K π ^ r) =
        PowerSeries.C (uniformizerInteger K π ^ (r + 1)) := by
      rw [← map_mul, pow_succ']
    have hC2 : PowerSeries.C (uniformizerInteger K π ^ r) ^ 2 =
        PowerSeries.C (uniformizerInteger K π ^ (r + 1)) *
          PowerSeries.C (uniformizerInteger K π ^ (r - 1)) := by
      calc
        PowerSeries.C (uniformizerInteger K π ^ r) ^ 2 =
            PowerSeries.C ((uniformizerInteger K π ^ r) ^ 2) :=
          (map_pow (PowerSeries.C : RingOfIntegers K →+*
            PowerSeries (RingOfIntegers K)) (uniformizerInteger K π ^ r) 2).symm
        _ = PowerSeries.C (uniformizerInteger K π ^ (r + 1) *
            uniformizerInteger K π ^ (r - 1)) := by rw [hpowfactor]
        _ = _ := by rw [map_mul]
    let y := t + W * PowerSeries.C (uniformizerInteger K π ^ (r - 1))
    have hopfactor : D.operator g =
        1 + PowerSeries.C (uniformizerInteger K π ^ (r + 1)) * y := by
      rw [hdetexpand, ht]
      dsimp [y]
      rw [hC2, ← hC1]
      ring
    intro n
    rw [hopfactor, map_add, PowerSeries.coeff_C_mul]
    simp only [add_sub_cancel_left]
    rw [uniformizerIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨PowerSeries.coeff n y, rfl⟩

/-- The `m`-fold iterate of the Coleman operator. -/
def colemanNormIterate (π : Uniformizer K) (m : ℕ)
    (g : PowerSeries (RingOfIntegers K)) : PowerSeries (RingOfIntegers K) :=
  ((colemanNorm K π).operator : PowerSeries (RingOfIntegers K) →
    PowerSeries (RingOfIntegers K))^[m] g

/-- The convergent coefficientwise value of a series at a point of a complete finite level. -/
noncomputable def powerSeriesValue
    {L : Type*} [Field L] [TopologicalSpace L]
    (φ : RingOfIntegers K →+* L) (x : L)
    (g : PowerSeries (RingOfIntegers K)) : L :=
  ∑' n : ℕ, φ (PowerSeries.coeff n g) * x ^ n

/-- The literal product of `g(β)` over roots of the primitive polynomial in the `m`th level. -/
noncomputable def lubinTatePrimitiveTorsionProduct
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : PowerSeries (RingOfIntegers K)) :
    (lubinTateLevel K Ksep π m hm).field := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  exact (((primitiveDivisionPolynomial K π m).map
      (algebraMap (RingOfIntegers K) level.field)).roots.map
        (fun β => powerSeriesValue K (algebraMap (RingOfIntegers K) level.field) β g)).prod

/-- The literal product of `g(β)` over all roots killed by the `m`th iterate. -/
noncomputable def lubinTateTorsionProduct
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : PowerSeries (RingOfIntegers K)) :
    (lubinTateLevel K Ksep π m hm).field := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  exact (((lubinTateIterate K π m).map
      (algebraMap (RingOfIntegers K) level.field)).roots.map
        (fun β => powerSeriesValue K (algebraMap (RingOfIntegers K) level.field) β g)).prod

/--
The derived primitive product is the field norm of the actual evaluation `g(α_m)`; it is not an
independent functional.
-/
noncomputable def lubinTatePrimitiveProduct
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : Units (PowerSeries (RingOfIntegers K))) : Units K := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  exact normUnitsHom K level.field (Units.map level.evaluation.toMonoidHom g)

private theorem test_summable
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (β : L) (hβ : PowerSeries.HasEval β)
    (g : PowerSeries (RingOfIntegers K)) :
    Summable (fun n : ℕ => algebraMap (RingOfIntegers K) L
      (PowerSeries.coeff n g) * β ^ n) := by
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : NonarchimedeanRing L := by
    rw [Valuation.toTopologicalSpace_eq (ValuativeRel.valuation L)]
    exact ValuativeRel.nonarchimedeanRing L
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  change Filter.Tendsto (fun n : ℕ => β ^ n) Filter.atTop (nhds 0) at hβ
  rw [Filter.tendsto_def] at hβ ⊢
  intro s hs
  obtain ⟨γ, -, hγs⟩ := (IsValuativeTopology.hasBasis_nhds_zero L).mem_iff.mp hs
  have hp := hβ {x : L | ValuativeRel.valuation L x < (γ : ValuativeRel.ValueGroupWithZero L)}
    ((IsValuativeTopology.hasBasis_nhds_zero L).mem_iff.mpr ⟨γ, trivial, Set.Subset.rfl⟩)
  filter_upwards [hp] with n hn
  apply hγs
  dsimp only [Set.mem_setOf_eq] at hn ⊢
  have hcK : ((PowerSeries.coeff n g : RingOfIntegers K) : K) ≤ᵥ (1 : K) := by
    apply (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) _ _).mpr
    exact (Valuation.mem_integer_iff (ValuativeRel.valuation K) _).mp
      (PowerSeries.coeff n g).prop
  have hcL : algebraMap K L ((PowerSeries.coeff n g : RingOfIntegers K) : K) ≤ᵥ
      (1 : L) := by
    simpa using (ValuativeExtension.vle_iff_vle (A := K) (B := L) _ _).mpr hcK
  have hc : algebraMap (RingOfIntegers K) L (PowerSeries.coeff n g) ≤ᵥ (1 : L) := by
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L]
    exact hcL
  have hmul := ValuativeRel.mul_vle_mul hc (ValuativeRel.vle_refl (β ^ n))
  rw [one_mul] at hmul
  exact lt_of_le_of_lt
    ((Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L) _ _).mp hmul)
    hn


private theorem test_normalizedValuation_le_iff
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x y : Units F) :
    normalizedValuation F x ≤ normalizedValuation F y ↔
      ValuativeRel.valuation F (y : F) ≤ ValuativeRel.valuation F (x : F) := by
  have hnonneg : 0 ≤ normalizedValuation F (y * x⁻¹) ↔
      ValuativeRel.valuation F ((y * x⁻¹ : Units F) : F) ≤ 1 := by
    unfold normalizedValuation normalizedValuationHom
    rw [(exists_normalizedValuationHom F).choose_spec.2]
    constructor
    · rintro ⟨a, ha⟩
      rw [← Valuation.mem_integer_iff]
      exact ha ▸ a.prop
    · intro h
      exact ⟨⟨y * x⁻¹, (Valuation.mem_integer_iff _ _).mpr h⟩, rfl⟩
  rw [normalizedValuation_mul, show normalizedValuation F x⁻¹ =
      -normalizedValuation F x by simp [normalizedValuation]] at hnonneg
  rw [← sub_nonneg]
  rw [show 0 ≤ normalizedValuation F y - normalizedValuation F x ↔
      ValuativeRel.valuation F ((y * x⁻¹ : Units F) : F) ≤ 1 by
    simpa [sub_eq_add_neg] using hnonneg]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  change ValuativeRel.valuation F (y : F) / ValuativeRel.valuation F (x : F) ≤ 1 ↔ _
  rw [div_le_one₀ ((ValuativeRel.valuation F).pos_iff.mpr x.ne_zero)]

private theorem test_normalizedValuation_lt_iff
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x y : Units F) :
    normalizedValuation F x < normalizedValuation F y ↔
      ValuativeRel.valuation F (y : F) < ValuativeRel.valuation F (x : F) := by
  simpa only [not_le] using (test_normalizedValuation_le_iff F y x).not

private theorem test_adic_inclusion_continuous
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (p : RingOfIntegers F) (hp : (p : F) ≠ 0)
    (hmax : Ideal.span {p} = LocalMaximalIdeal F)
    (hpval : normalizedValuation F (Units.mk0 (p : F) hp) = 1) :
    letI : WithIdeal (RingOfIntegers F) := ⟨LocalMaximalIdeal F⟩
    letI : TopologicalSpace (RingOfIntegers F) := (LocalMaximalIdeal F).adicTopology
    Continuous (algebraMap (RingOfIntegers F) F) := by
  letI : WithIdeal (RingOfIntegers F) := ⟨LocalMaximalIdeal F⟩
  letI : TopologicalSpace (RingOfIntegers F) := (LocalMaximalIdeal F).adicTopology
  let incl : RingOfIntegers F →+* F := algebraMap (RingOfIntegers F) F
  apply continuous_of_continuousAt_zero incl
  rw [ContinuousAt, map_zero]
  rw [(Ideal.hasBasis_nhds_zero_adic (LocalMaximalIdeal F)).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero F)]
  intro γ _
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
    (K := F) (γ : ValuativeRel.ValueGroupWithZero F)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact γ.ne_zero hy.symm
  let yu : Units F := Units.mk0 y hy0
  let t : ℤ := normalizedValuation F yu
  let N : ℕ := t.natAbs + 1
  let pu : Units F := Units.mk0 (p : F) hp
  have htN : t < (N : ℤ) := by
    dsimp [N]
    have habs := le_abs_self t
    omega
  have hpuN : normalizedValuation F (pu ^ N) = (N : ℤ) := by
    rw [show normalizedValuation F (pu ^ N) =
      (N : ℤ) * normalizedValuation F pu by
        simp [normalizedValuation]]
    rw [show normalizedValuation F pu = 1 from hpval, mul_one]
  have hvpow : ValuativeRel.valuation F ((pu ^ N : Units F) : F) <
      ValuativeRel.valuation F (yu : F) :=
    (test_normalizedValuation_lt_iff F yu (pu ^ N)).mp (by rw [hpuN]; exact htN)
  refine ⟨N, trivial, ?_⟩
  intro x hx
  change ValuativeRel.valuation F (x : F) < (γ : ValuativeRel.ValueGroupWithZero F)
  rw [← hy]
  apply lt_of_le_of_lt _ hvpow
  have hxspan : x ∈ Ideal.span ({p ^ N} : Set (RingOfIntegers F)) := by
    rw [← Ideal.span_singleton_pow, hmax]
    exact hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hxspan
  have hcval : ValuativeRel.valuation F (c : F) ≤ 1 :=
    (Valuation.mem_integer_iff (ValuativeRel.valuation F) c).mpr c.prop
  rw [hc]
  change ValuativeRel.valuation F ((p : F) ^ N * (c : F)) ≤
    ValuativeRel.valuation F ((p : F) ^ N)
  rw [map_mul]
  exact mul_le_of_le_one_right (bot_le : (0 : ValuativeRel.ValueGroupWithZero F) ≤ _)
    hcval


private noncomputable def testAdicEval
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (c : RingOfIntegers K →+* RingOfIntegers L)
    (β : RingOfIntegers L) (hβ : β ∈ LocalMaximalIdeal L) :
    PowerSeries (RingOfIntegers K) →+* RingOfIntegers L := by
  letI : TopologicalSpace (RingOfIntegers K) := ⊥
  letI : UniformSpace (RingOfIntegers K) := ⊥
  letI : DiscreteUniformity (RingOfIntegers K) := ⟨rfl⟩
  letI : DiscreteTopology (RingOfIntegers K) := ⟨rfl⟩
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal (RingOfIntegers L) := ⟨LocalMaximalIdeal L⟩
  letI : TopologicalSpace (RingOfIntegers L) := (LocalMaximalIdeal L).adicTopology
  letI : UniformSpace (RingOfIntegers L) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (RingOfIntegers L) := isUniformAddGroup_of_addCommGroup
  letI : IsLinearTopology (RingOfIntegers L) (RingOfIntegers L) :=
    (LocalMaximalIdeal L).isLinearTopology
  have hadic : IsAdic (LocalMaximalIdeal L) := rfl
  have hcomplete := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (LocalMaximalIdeal L) (RingOfIntegers L))
  letI : CompleteSpace (RingOfIntegers L) := hcomplete.1
  letI : T2Space (RingOfIntegers L) := hcomplete.2
  letI : Algebra (RingOfIntegers K) (RingOfIntegers L) := c.toAlgebra
  exact PowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous c)
    (WithIdeal.isTopologicallyNilpotent_of_mem hβ)

private theorem testAdicEval_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (c : RingOfIntegers K →+* RingOfIntegers L)
    (hc : ∀ x, ((c x : RingOfIntegers L) : L) =
      algebraMap (RingOfIntegers K) L x)
    (β : RingOfIntegers L) (hβ : β ∈ LocalMaximalIdeal L)
    (hinc : letI : WithIdeal (RingOfIntegers L) := ⟨LocalMaximalIdeal L⟩
      letI : TopologicalSpace (RingOfIntegers L) := (LocalMaximalIdeal L).adicTopology
      Continuous (algebraMap (RingOfIntegers L) L))
    (g : PowerSeries (RingOfIntegers K)) :
    algebraMap (RingOfIntegers L) L (testAdicEval K c β hβ g) =
      powerSeriesValue K (algebraMap (RingOfIntegers K) L) (β : L) g := by
  letI : TopologicalSpace (RingOfIntegers K) := ⊥
  letI : UniformSpace (RingOfIntegers K) := ⊥
  letI : DiscreteUniformity (RingOfIntegers K) := ⟨rfl⟩
  letI : DiscreteTopology (RingOfIntegers K) := ⟨rfl⟩
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal (RingOfIntegers L) := ⟨LocalMaximalIdeal L⟩
  letI : TopologicalSpace (RingOfIntegers L) := (LocalMaximalIdeal L).adicTopology
  letI : UniformSpace (RingOfIntegers L) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (RingOfIntegers L) := isUniformAddGroup_of_addCommGroup
  letI : IsLinearTopology (RingOfIntegers L) (RingOfIntegers L) :=
    (LocalMaximalIdeal L).isLinearTopology
  have hadic : IsAdic (LocalMaximalIdeal L) := rfl
  have hcomplete := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (LocalMaximalIdeal L) (RingOfIntegers L))
  letI : CompleteSpace (RingOfIntegers L) := hcomplete.1
  letI : T2Space (RingOfIntegers L) := hcomplete.2
  letI : Algebra (RingOfIntegers K) (RingOfIntegers L) := c.toAlgebra
  have hs := PowerSeries.hasSum_eval₂
    (continuous_of_discreteTopology : Continuous c)
    (WithIdeal.isTopologicallyNilpotent_of_mem hβ) g
  have hsL := hs.map (algebraMap (RingOfIntegers L) L) hinc
  have heval : testAdicEval K c β hβ g = PowerSeries.eval₂ c β g := by
    rw [testAdicEval, PowerSeries.coe_eval₂Hom]
  rw [heval]
  unfold powerSeriesValue
  rw [← hsL.tsum_eq]
  congr 1
  funext n
  simp only [Function.comp_apply, map_mul, map_pow]
  apply congrArg₂ (· * ·)
  · exact hc _
  · rfl


private theorem testAdicEval_coe
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (c : RingOfIntegers K →+* RingOfIntegers L)
    (β : RingOfIntegers L) (hβ : β ∈ LocalMaximalIdeal L)
    (p : Polynomial (RingOfIntegers K)) :
    testAdicEval K c β hβ (p : PowerSeries (RingOfIntegers K)) =
      p.eval₂ c β := by
  letI : TopologicalSpace (RingOfIntegers K) := ⊥
  letI : UniformSpace (RingOfIntegers K) := ⊥
  letI : DiscreteUniformity (RingOfIntegers K) := ⟨rfl⟩
  letI : DiscreteTopology (RingOfIntegers K) := ⟨rfl⟩
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal (RingOfIntegers L) := ⟨LocalMaximalIdeal L⟩
  letI : TopologicalSpace (RingOfIntegers L) := (LocalMaximalIdeal L).adicTopology
  letI : UniformSpace (RingOfIntegers L) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (RingOfIntegers L) := isUniformAddGroup_of_addCommGroup
  letI : IsLinearTopology (RingOfIntegers L) (RingOfIntegers L) :=
    (LocalMaximalIdeal L).isLinearTopology
  have hadic : IsAdic (LocalMaximalIdeal L) := rfl
  have hcomplete := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (LocalMaximalIdeal L) (RingOfIntegers L))
  letI : CompleteSpace (RingOfIntegers L) := hcomplete.1
  letI : T2Space (RingOfIntegers L) := hcomplete.2
  letI : Algebra (RingOfIntegers K) (RingOfIntegers L) := c.toAlgebra
  rw [testAdicEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe]

private theorem testAdicEval_X
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (c : RingOfIntegers K →+* RingOfIntegers L)
    (β : RingOfIntegers L) (hβ : β ∈ LocalMaximalIdeal L) :
    testAdicEval K c β hβ PowerSeries.X = β := by
  rw [← Polynomial.coe_X, testAdicEval_coe, Polynomial.eval₂_X]

private theorem testAdicEval_subst
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (c : RingOfIntegers K →+* RingOfIntegers L)
    (β a : RingOfIntegers L) (hβ : β ∈ LocalMaximalIdeal L)
    (ha : a ∈ LocalMaximalIdeal L)
    (f h : PowerSeries (RingOfIntegers K))
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hfa : testAdicEval K c β hβ f = a) :
    testAdicEval K c β hβ (PowerSeries.subst f h) =
      testAdicEval K c a ha h := by
  letI : TopologicalSpace (RingOfIntegers K) := ⊥
  letI : UniformSpace (RingOfIntegers K) := ⊥
  letI : DiscreteUniformity (RingOfIntegers K) := ⟨rfl⟩
  letI : DiscreteTopology (RingOfIntegers K) := ⟨rfl⟩
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : WithIdeal (RingOfIntegers L) := ⟨LocalMaximalIdeal L⟩
  letI : TopologicalSpace (RingOfIntegers L) := (LocalMaximalIdeal L).adicTopology
  letI : UniformSpace (RingOfIntegers L) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (RingOfIntegers L) := isUniformAddGroup_of_addCommGroup
  letI : IsLinearTopology (RingOfIntegers L) (RingOfIntegers L) :=
    (LocalMaximalIdeal L).isLinearTopology
  have hadic : IsAdic (LocalMaximalIdeal L) := rfl
  have hcomplete := hadic.isAdicComplete_iff.mp
    (inferInstance : IsAdicComplete (LocalMaximalIdeal L) (RingOfIntegers L))
  letI : CompleteSpace (RingOfIntegers L) := hcomplete.1
  letI : T2Space (RingOfIntegers L) := hcomplete.2
  letI : Algebra (RingOfIntegers K) (RingOfIntegers L) := c.toAlgebra
  have hf : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hβe : PowerSeries.HasEval β := WithIdeal.isTopologicallyNilpotent_of_mem hβ
  have hae : PowerSeries.HasEval a := WithIdeal.isTopologicallyNilpotent_of_mem ha
  have H := MvPowerSeries.eval₂_subst
    (R := RingOfIntegers K) (S := RingOfIntegers K)
    (T := RingOfIntegers L)
    (a := fun _ : Unit => (f : MvPowerSeries Unit (RingOfIntegers K)))
    (b := fun _ : Unit => β) hf.const (PowerSeries.hasEval hβe) h
  change PowerSeries.eval₂ c β (PowerSeries.subst f h) =
    PowerSeries.eval₂ c (PowerSeries.eval₂ c β f) h at H
  rw [testAdicEval, PowerSeries.coe_eval₂Hom] at hfa ⊢
  rw [hfa] at H
  rw [show testAdicEval K c a ha h = PowerSeries.eval₂ c a h by
    rw [testAdicEval, PowerSeries.coe_eval₂Hom]]
  exact H


private theorem test_iterate_monic_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K) :
    ∀ n, (lubinTateIterate K π n).Monic ∧
      (lubinTateIterate K π n).natDegree = residueCard K ^ n := by
  have hp : uniformizerInteger K π ≠ 0 := by
    intro h
    apply π.val.ne_zero
    rw [← (uniformizer_integer_exists K π).choose_spec]
    exact congrArg (fun x : RingOfIntegers K => (x : K)) h
  have hq : 1 < residueCard K := by
    letI := Fintype.ofFinite (LocalResidueField K)
    change 1 < Nat.card (LocalResidueField K)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hf : (lubinTatePolynomial K π).Monic ∧
      (lubinTatePolynomial K π).natDegree = residueCard K := by
    have hmonic : (lubinTatePolynomial K π).Monic := by
      rw [lubinTatePolynomial]
      apply (Polynomial.monic_X_pow (residueCard K)).add_of_right
      rw [Polynomial.degree_C_mul_X hp, Polynomial.degree_X_pow]
      exact_mod_cast hq
    refine ⟨hmonic, ?_⟩
    rw [lubinTatePolynomial, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]
    · rw [Polynomial.natDegree_C_mul_X _ hp, Polynomial.natDegree_X_pow]
      exact hq
  intro n
  induction n with
  | zero => simp [lubinTateIterate]
  | succ n ih =>
      constructor
      · rw [lubinTateIterate]
        exact hf.1.comp ih.1 (by rw [ih.2]; positivity)
      · rw [lubinTateIterate, Polynomial.natDegree_comp, hf.2, ih.2, pow_succ']

private theorem test_iterate_map_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K)
    {k : Type*} [Field k] (ρ : RingOfIntegers K →+* k)
    (hp : ρ (uniformizerInteger K π) = 0) :
    ∀ n, (lubinTateIterate K π n).map ρ =
      Polynomial.X ^ (residueCard K ^ n) := by
  intro n
  induction n with
  | zero => simp [lubinTateIterate]
  | succ n ih =>
      rw [lubinTateIterate, Polynomial.map_comp, ih]
      rw [lubinTatePolynomial]
      simp [hp, ← pow_mul, pow_succ, Polynomial.pow_comp]


private noncomputable def testTorsionRootInteger
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (β : (lubinTateLevel K Ksep π m hm).field)
    (hβ : ((lubinTateIterate K π m).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot β) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    RingOfIntegers level.field := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  let c := level.integerAlgebraMap
  letI : Algebra (RingOfIntegers K) (RingOfIntegers level.field) := c.toAlgebra
  have hc : (algebraMap (RingOfIntegers level.field) level.field).comp c =
      algebraMap (RingOfIntegers K) level.field := by
    apply RingHom.ext
    intro x
    change (((c x : RingOfIntegers level.field) : level.field)) =
      algebraMap (RingOfIntegers K) level.field x
    exact level.integerAlgebraMap_apply x
  have hint : IsIntegral (RingOfIntegers level.field) β := by
    refine ⟨(lubinTateIterate K π m).map c,
      (test_iterate_monic_natDegree K π m).1.map c, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hβ
  exact ⟨β, (Valuation.integer.integers
    (ValuativeRel.valuation level.field)).mem_of_integral hint⟩

@[simp] private theorem testTorsionRootInteger_val
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (β : (lubinTateLevel K Ksep π m hm).field)
    (hβ : ((lubinTateIterate K π m).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot β) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    ((testTorsionRootInteger K Ksep π m hm β hβ : RingOfIntegers level.field) :
      level.field) = β := by
  rfl


private theorem testTorsionRootInteger_mem_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (β : (lubinTateLevel K Ksep π m hm).field)
    (hβ : ((lubinTateIterate K π m).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot β) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    testTorsionRootInteger K Ksep π m hm β hβ ∈ LocalMaximalIdeal level.field := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  let c := level.integerAlgebraMap
  letI : Algebra (RingOfIntegers K) (RingOfIntegers level.field) := c.toAlgebra
  letI : IsScalarTower (RingOfIntegers K) (RingOfIntegers level.field) level.field :=
    IsScalarTower.of_algebraMap_eq fun x => (level.integerAlgebraMap_apply x).symm
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation level.field) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  let βO := testTorsionRootInteger K Ksep π m hm β hβ
  have hpK : uniformizerInteger K π ∈ LocalMaximalIdeal K := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hval : normalizedValuation K
        (Units.map (algebraMap (RingOfIntegers K) K) u) = 0 := by
      have hnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u) :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ :=
        (exists_normalizedValuationHom K).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers K)), rfl⟩
      have hinv : normalizedValuation K
          (Units.map (algebraMap (RingOfIntegers K) K) u)⁻¹ =
          -normalizedValuation K
            (Units.map (algebraMap (RingOfIntegers K) K) u) := by
        simp [normalizedValuation]
      rw [hinv] at hinvnonneg
      omega
    have heq : Units.map (algebraMap (RingOfIntegers K) K) u = π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers K)) : RingOfIntegers K) : K) = (π.val : K)
      rw [hu]
      exact (uniformizer_integer_exists K π).choose_spec
    rw [heq, π.valuation_eq_one] at hval
    omega
  have hpc : c (uniformizerInteger K π) ∈ LocalMaximalIdeal level.field := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    let uL := Units.map (algebraMap (RingOfIntegers level.field) level.field).toMonoidHom u
    have huval : normalizedValuation level.field uL = 0 := by
      have hnonneg : 0 ≤ normalizedValuation level.field uL :=
        (exists_normalizedValuationHom level.field).choose_spec.2 _ |>.2 ⟨u, rfl⟩
      have hinvnonneg : 0 ≤ normalizedValuation level.field uL⁻¹ :=
        (exists_normalizedValuationHom level.field).choose_spec.2 _ |>.2
          ⟨(u⁻¹ : Units (RingOfIntegers level.field)), rfl⟩
      have hinv : normalizedValuation level.field uL⁻¹ =
          -normalizedValuation level.field uL := by
        simp [normalizedValuation]
      rw [hinv] at hinvnonneg
      omega
    have heq : uL = Units.map (algebraMap K level.field).toMonoidHom π.val := by
      apply Units.ext
      change (((u : Units (RingOfIntegers level.field)) : RingOfIntegers level.field) :
        level.field) = algebraMap K level.field (π.val : K)
      rw [hu, level.integerAlgebraMap_apply,
        IsScalarTower.algebraMap_apply (RingOfIntegers K) K level.field]
      have hpfield : algebraMap (RingOfIntegers K) K (uniformizerInteger K π) =
          (π.val : K) := (uniformizer_integer_exists K π).choose_spec
      rw [hpfield]
    rw [heq] at huval
    have hvalmap := normalizedValuation_algebraMap K level.field π.val
    rw [π.valuation_eq_one, mul_one] at hvalmap
    have hezero : (ramificationIndex K level.field : ℤ) = 0 := by
      calc
        (ramificationIndex K level.field : ℤ) =
            normalizedValuation level.field
              (Units.map (algebraMap K level.field) π.val) := hvalmap.symm
        _ = 0 := huval
    have hepos : 0 < ramificationIndex K level.field :=
      (ramificationInvariants_exists K level.field).choose_spec.choose_spec.1
    omega
  let ρ := IsLocalRing.residue (RingOfIntegers level.field)
  have hpρ : (ρ.comp c) (uniformizerInteger K π) = 0 := by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact hpc
  have hβOroot : ((lubinTateIterate K π m).map c).IsRoot βO := by
    rw [Polynomial.IsRoot.def]
    apply Subtype.ext
    change algebraMap (RingOfIntegers level.field) level.field
      (Polynomial.eval βO ((lubinTateIterate K π m).map c)) = 0
    rw [Polynomial.eval_map, Polynomial.hom_eval₂]
    change (lubinTateIterate K π m).eval₂
      ((algebraMap (RingOfIntegers level.field) level.field).comp c) (βO : level.field) = 0
    rw [show (algebraMap (RingOfIntegers level.field) level.field).comp c =
      algebraMap (RingOfIntegers K) level.field by
        apply RingHom.ext
        intro x
        exact level.integerAlgebraMap_apply x]
    rw [show (βO : level.field) = β by rfl]
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hβ
  have hresroot := hβOroot.map (f := ρ)
  rw [Polynomial.map_map, test_iterate_map_residue K π (ρ.comp c) hpρ m] at hresroot
  rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at hresroot
  have hqpow : residueCard K ^ m ≠ 0 := pow_ne_zero _ Nat.card_pos.ne'
  have hρzero : ρ βO = 0 := (pow_eq_zero_iff hqpow).mp hresroot
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact hρzero


private theorem test_primitive_monic_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    (primitiveDivisionPolynomial K π m).Monic ∧
      (primitiveDivisionPolynomial K π m).natDegree =
        (residueCard K - 1) * residueCard K ^ (m - 1) := by
  have hp : uniformizerInteger K π ≠ 0 := by
    intro h
    apply π.val.ne_zero
    rw [← (uniformizer_integer_exists K π).choose_spec]
    exact congrArg (fun x : RingOfIntegers K => (x : K)) h
  have hq : 1 < residueCard K := by
    letI := Fintype.ofFinite (LocalResidueField K)
    change 1 < Nat.card (LocalResidueField K)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hi := test_iterate_monic_natDegree K π (m - 1)
  let d := (residueCard K - 1) * residueCard K ^ (m - 1)
  have hd : 0 < d := mul_pos (Nat.sub_pos_of_lt hq) (pow_pos (by omega) _)
  have hpow : ((lubinTateIterate K π (m - 1)) ^ (residueCard K - 1)).Monic :=
    hi.1.pow _
  have hmonic : (primitiveDivisionPolynomial K π m).Monic := by
    rw [primitiveDivisionPolynomial]
    apply hpow.add_of_right
    rw [Polynomial.degree_C hp, Polynomial.degree_eq_natDegree hpow.ne_zero,
      Polynomial.natDegree_pow, hi.2]
    exact_mod_cast hd
  refine ⟨hmonic, ?_⟩
  rw [primitiveDivisionPolynomial, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow, hi.2]
  · rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, hi.2]
    exact hd

private theorem test_iterate_factor_primitive
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    lubinTateIterate K π m = lubinTateIterate K π (m - 1) *
      primitiveDivisionPolynomial K π m := by
  have hq : 0 < residueCard K := Nat.card_pos
  conv_lhs => rw [show m = (m - 1) + 1 by omega, lubinTateIterate]
  rw [lubinTatePolynomial, primitiveDivisionPolynomial]
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.pow_comp]
  have hpow : lubinTateIterate K π (m - 1) ^ residueCard K =
      lubinTateIterate K π (m - 1) ^ (residueCard K - 1) *
        lubinTateIterate K π (m - 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  rw [hpow, mul_add]
  ac_rfl

private theorem test_tower_field_le
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    (lubinTateLevel K Ksep π j hj).field ≤
      (lubinTateLevel K Ksep π m (hj.trans hjm)).field := by
  induction m, hjm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hjm ih =>
      exact ih.trans ((lubinTateTower K Ksep π).field_le m (hj.trans hjm))


private theorem test_primitive_irreducible_K
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    Irreducible ((primitiveDivisionPolynomial K π m).map
      (algebraMap (RingOfIntegers K) K)) := by
  have hmonic := (test_primitive_monic_natDegree K π m hm).1
  have hq : 1 < residueCard K := by
    letI := Fintype.ofFinite (LocalResidueField K)
    change 1 < Nat.card (LocalResidueField K)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hdeg : 0 < (primitiveDivisionPolynomial K π m).natDegree := by
    rw [(primitiveDivisionPolynomial_eisenstein K Ksep π m hm).2.1]
    exact mul_pos (Nat.sub_pos_of_lt hq) (pow_pos (by omega) _)
  have hirr : Irreducible (primitiveDivisionPolynomial K π m) :=
    (primitiveDivisionPolynomial_eisenstein K Ksep π m hm).1.irreducible
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime hmonic.isPrimitive hdeg
  exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr


private theorem test_primitive_splits_separable_in_level
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
    (((primitiveDivisionPolynomial K π j).map
      (algebraMap (RingOfIntegers K) level.field)).Splits ∧
     ((primitiveDivisionPolynomial K π j).map
      (algebraMap (RingOfIntegers K) level.field)).Separable) := by
  let level := lubinTateLevel K Ksep π m hm
  let lower := lubinTateLevel K Ksep π j hj
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : FiniteDimensional K lower.field := lower.finiteDimensional
  letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
  have hle : lower.field ≤ level.field := by
    simpa only [level, lower, proof_irrel_heq] using
      test_tower_field_le K Ksep π hj hjm
  let i := IntermediateField.inclusion hle
  let x : level.field := i lower.generator
  let QK := (primitiveDivisionPolynomial K π j).map
    (algebraMap (RingOfIntegers K) K)
  have hxroot : ((primitiveDivisionPolynomial K π j).map
      (algebraMap (RingOfIntegers K) level.field)).IsRoot x := by
    rw [Polynomial.IsRoot.def]
    apply (algebraMap level.field Ksep).injective
    rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂]
    change (primitiveDivisionPolynomial K π j).eval₂
      ((algebraMap level.field Ksep).comp
        (algebraMap (RingOfIntegers K) level.field))
      (((x : level.field) : Ksep)) = 0
    rw [show (algebraMap level.field Ksep).comp
      (algebraMap (RingOfIntegers K) level.field) =
        algebraMap (RingOfIntegers K) Ksep by
          apply RingHom.ext
          intro z
          exact IsScalarTower.algebraMap_apply (RingOfIntegers K) level.field Ksep z]
    simpa [x, i, Polynomial.IsRoot.def, Polynomial.eval_map] using lower.isRoot
  have hxK : Polynomial.aeval x QK = 0 := by
    rw [Polynomial.aeval_def]
    dsimp only [QK]
    rw [Polynomial.eval₂_map]
    rw [show (algebraMap K level.field).comp
      (algebraMap (RingOfIntegers K) K) =
        algebraMap (RingOfIntegers K) level.field by
          apply RingHom.ext
          intro z
          exact (IsScalarTower.algebraMap_apply
            (RingOfIntegers K) K level.field z).symm]
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hxroot
  have hQmonic : QK.Monic :=
    (test_primitive_monic_natDegree K π j hj).1.map _
  have hmin : QK = minpoly K x :=
    minpoly.eq_of_irreducible_of_monic
      (test_primitive_irreducible_K K Ksep π j hj) hxK hQmonic
  have hsplitK := IsGalois.splits K x
  have hsplit : ((primitiveDivisionPolynomial K π j).map
      (algebraMap (RingOfIntegers K) level.field)).Splits := by
    rw [← hmin] at hsplitK
    simpa only [QK, Polynomial.map_map,
      IsScalarTower.algebraMap_eq (RingOfIntegers K) K level.field] using hsplitK
  have hsepK : QK.Separable := by
    rw [hmin]
    exact Algebra.IsSeparable.isSeparable K x
  have hsepMap := (Polynomial.separable_map (algebraMap K level.field)).2 hsepK
  have hsep : ((primitiveDivisionPolynomial K π j).map
      (algebraMap (RingOfIntegers K) level.field)).Separable := by
    simpa only [QK, Polynomial.map_map,
      IsScalarTower.algebraMap_eq (RingOfIntegers K) K level.field] using hsepMap
  exact ⟨hsplit, hsep⟩


set_option maxHeartbeats 800000 in
private theorem test_iterate_primitive_isCoprime_in_level
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (j : ℕ) (hj : 1 ≤ j) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    IsCoprime
      ((lubinTateIterate K π (j - 1)).map
        (algebraMap (RingOfIntegers K) level.field))
      ((primitiveDivisionPolynomial K π j).map
        (algebraMap (RingOfIntegers K) level.field)) := by
  let level := lubinTateLevel K Ksep π m hm
  let lower := lubinTateLevel K Ksep π j hj
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : FiniteDimensional K lower.field := lower.finiteDimensional
  let QK := (primitiveDivisionPolynomial K π j).map
    (algebraMap (RingOfIntegers K) K)
  let FK := (lubinTateIterate K π (j - 1)).map
    (algebraMap (RingOfIntegers K) K)
  have hcopK : IsCoprime FK QK := by
    apply IsCoprime.symm
    apply (Irreducible.coprime_iff_not_dvd
      (test_primitive_irreducible_K K Ksep π j hj)).2
    intro hdvd
    have hdvdsep : (primitiveDivisionPolynomial K π j).map
        (algebraMap (RingOfIntegers K) Ksep) ∣
        (lubinTateIterate K π (j - 1)).map
          (algebraMap (RingOfIntegers K) Ksep) := by
      have hmap := Polynomial.map_dvd (algebraMap K Ksep) hdvd
      simpa only [QK, FK, Polynomial.map_map,
        IsScalarTower.algebraMap_eq (RingOfIntegers K) K Ksep] using hmap
    have hprev := lower.isRoot.dvd hdvdsep
    have hprim := (primitiveDivisionPolynomial_eisenstein K Ksep π j hj).2.2
      (((lower.generator : lower.field) : Ksep)) |>.mp lower.isRoot
    exact hprim.2 hprev
  have hmap := (Polynomial.isCoprime_map (algebraMap K level.field)).2 hcopK
  have hc : (algebraMap K level.field).comp
      (algebraMap (RingOfIntegers K) K) =
      algebraMap (RingOfIntegers K) level.field := by
    apply RingHom.ext
    intro z
    exact (IsScalarTower.algebraMap_apply
      (RingOfIntegers K) K level.field z).symm
  simpa only [FK, QK, Polynomial.map_map, hc, level] using hmap


set_option maxHeartbeats 800000 in
private theorem test_iterate_splits_separable_in_level
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (hnm : n ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
    (((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K) level.field)).Splits ∧
     ((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K) level.field)).Separable) := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
  induction n with
  | zero => simp [lubinTateIterate, Polynomial.separable_X]
  | succ n ih =>
      have hnle : n ≤ m := n.le_succ.trans hnm
      have hprev := ih hnle
      have hq := test_primitive_splits_separable_in_level
        K Ksep π m hm (n + 1) (Nat.succ_pos n) hnm
      have hcop := test_iterate_primitive_isCoprime_in_level
        K Ksep π m hm (n + 1) (Nat.succ_pos n)
      have hfac := congrArg (Polynomial.map
        (algebraMap (RingOfIntegers K) level.field))
        (test_iterate_factor_primitive K π (n + 1) (Nat.succ_pos n))
      simp only [Polynomial.map_mul, Nat.add_sub_cancel] at hfac
      dsimp only at hprev hq hcop ⊢
      simp only [Nat.add_sub_cancel] at hcop
      rw [hfac]
      exact ⟨hprev.1.mul hq.1, hprev.2.mul hq.2 hcop⟩


private theorem test_iterate_comp_polynomial
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (π : Uniformizer K) (n : ℕ) :
    (lubinTateIterate K π n).comp (lubinTatePolynomial K π) =
      (lubinTatePolynomial K π).comp (lubinTateIterate K π n) := by
  induction n with
  | zero => simp [lubinTateIterate]
  | succ n ih =>
      rw [lubinTateIterate, Polynomial.comp_assoc, ih,
        ← Polynomial.comp_assoc]

private theorem test_fiber_dvd_iterate
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (π : Uniformizer K) {L : Type v} [Field L]
    (φ : RingOfIntegers K →+* L) (n : ℕ) (a : L)
    (ha : ((lubinTateIterate K π n).map φ).IsRoot a) :
    (lubinTatePolynomial K π).map φ - Polynomial.C a ∣
      (lubinTateIterate K π (n + 1)).map φ := by
  let F := (lubinTatePolynomial K π).map φ
  let Fn := (lubinTateIterate K π n).map φ
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot.mpr ha)
  have hcomp := congrArg (fun p : Polynomial L => p.comp F) hq
  have hcomm := congrArg (Polynomial.map φ) (test_iterate_comp_polynomial K π n)
  simp only [Polynomial.map_comp] at hcomm
  have hnext : (lubinTateIterate K π (n + 1)).map φ = Fn.comp F := by
    rw [lubinTateIterate, Polynomial.map_comp, hcomm]
  refine ⟨q.comp F, ?_⟩
  rw [hnext]
  calc
    Fn.comp F = ((Polynomial.X - Polynomial.C a) * q).comp F := by rw [← hq]
    _ = (F - Polynomial.C a) * q.comp F := by
      rw [Polynomial.mul_comp, Polynomial.sub_comp]
      simp
    _ = _ := rfl

private theorem test_fiber_splits_separable
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (hnm : n + 1 ≤ m)
    (a : (lubinTateLevel K Ksep π m hm).field)
    (ha : ((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot a) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    let P := (lubinTatePolynomial K π).map
      (algebraMap (RingOfIntegers K) level.field) - Polynomial.C a
    P.Splits ∧ P.Separable := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  let φ := algebraMap (RingOfIntegers K) level.field
  let P := (lubinTatePolynomial K π).map φ - Polynomial.C a
  have hall := test_iterate_splits_separable_in_level
    K Ksep π m hm (n + 1) hnm
  have hdvd : P ∣ (lubinTateIterate K π (n + 1)).map φ :=
    test_fiber_dvd_iterate K π φ n a ha
  have hne : (lubinTateIterate K π (n + 1)).map φ ≠ 0 :=
    ((test_iterate_monic_natDegree K π (n + 1)).1.map φ).ne_zero
  exact ⟨hall.1.of_dvd hne hdvd, hall.2.of_dvd hdvd⟩


private theorem test_iterate_root_mono
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (π : Uniformizer K) {L : Type v} [Field L]
    (φ : RingOfIntegers K →+* L) (x : L) {n m : ℕ} (hnm : n ≤ m)
    (hx : ((lubinTateIterate K π n).map φ).IsRoot x) :
    ((lubinTateIterate K π m).map φ).IsRoot x := by
  induction m, hnm using Nat.le_induction with
  | base => exact hx
  | succ m hnm ih =>
      rw [lubinTateIterate, Polynomial.map_comp, Polynomial.IsRoot.def,
        Polynomial.eval_comp]
      rw [show Polynomial.eval x ((lubinTateIterate K π m).map φ) = 0 from ih]
      have hq : residueCard K ≠ 0 := Nat.card_pos.ne'
      simp [lubinTatePolynomial, hq]


private theorem test_algMap_injective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : Uniformizer K) (D : ColemanNormData K π) :
    Function.Injective (algebraMap (PowerSeries (RingOfIntegers K))
      (SubstDomain K π)) := by
  classical
  intro a b hab
  have hq : 0 < residueCard K := Nat.card_pos
  let i : Fin (residueCard K) := ⟨0, hq⟩
  have hact : a • D.weierstrassBasis i = b • D.weierstrassBasis i := by
    rw [Algebra.smul_def, Algebra.smul_def, hab]
  have hcoord := congrArg (fun x => D.weierstrassBasis.repr x i) hact
  simpa [i] using hcoord

private theorem test_operator_eq_det (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : Uniformizer K) (D : ColemanNormData K π)
    (g : PowerSeries (RingOfIntegers K)) :
    D.operator g = Matrix.det (D.multiplicationMatrix g) := by
  apply test_algMap_injective K π D
  calc
    algebraMap (PowerSeries (RingOfIntegers K)) (SubstDomain K π) (D.operator g) =
        SubstDomain.ofPowerSeries K π
          (PowerSeries.subst (lubinTateSeries K π) (D.operator g)) := by
      apply SubstDomain.ext
      simp
    _ = _ := D.determinant_spec g

private theorem test_mul_expansion (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : Uniformizer K) (D : ColemanNormData K π)
    (z : PowerSeries (RingOfIntegers K)) (j : Fin (residueCard K)) :
    z * PowerSeries.X ^ (j : ℕ) =
      ∑ i : Fin (residueCard K),
        PowerSeries.subst (lubinTateSeries K π) (D.multiplicationMatrix z i j) *
          PowerSeries.X ^ (i : ℕ) := by
  classical
  let T := LinearMap.mulLeft (PowerSeries (RingOfIntegers K))
    (SubstDomain.ofPowerSeries K π z)
  have hsum := D.weierstrassBasis.sum_repr (T (D.weierstrassBasis j))
  have hsum' := congrArg (SubstDomain.ringEquiv K π) hsum
  rw [map_sum] at hsum'
  change (∑ i, ((D.weierstrassBasis.repr
      (T (D.weierstrassBasis j))) i • D.weierstrassBasis i).toPowerSeries) =
    (SubstDomain.ofPowerSeries K π z * D.weierstrassBasis j).toPowerSeries at hsum'
  simp_rw [SubstDomain.smul_apply] at hsum'
  simp_rw [D.weierstrassBasis_apply] at hsum'
  rw [SubstDomain.toPowerSeries_mul, SubstDomain.toPowerSeries_ofPowerSeries,
    D.weierstrassBasis_apply] at hsum'
  rw [D.multiplicationMatrix_apply]
  simp_rw [LinearMap.toMatrix_apply]
  exact hsum'.symm


set_option maxHeartbeats 1200000 in
private theorem test_fiber_operator_product
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (hnm : n + 1 ≤ m)
    (a : (lubinTateLevel K Ksep π m hm).field)
    (ha : ((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot a)
    (hinc :
      let level := lubinTateLevel K Ksep π m hm
      letI : FiniteDimensional K level.field := level.finiteDimensional
      letI : ValuativeRel level.field := level.localFieldData.valuativeRel
      letI : TopologicalSpace level.field := level.localFieldData.topology
      letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
      letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
      letI : TopologicalSpace (RingOfIntegers level.field) :=
        (LocalMaximalIdeal level.field).adicTopology
      Continuous (algebraMap (RingOfIntegers level.field) level.field))
    (g : PowerSeries (RingOfIntegers K)) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    let P := (lubinTatePolynomial K π).map
      (algebraMap (RingOfIntegers K) level.field) - Polynomial.C a
    powerSeriesValue K (algebraMap (RingOfIntegers K) level.field) a
        ((colemanNorm K π).operator g) =
      (P.roots.map (fun β => powerSeriesValue K
        (algebraMap (RingOfIntegers K) level.field) β g)).prod := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  let c := level.integerAlgebraMap
  let φ := algebraMap (RingOfIntegers K) level.field
  let F := (lubinTatePolynomial K π).map φ
  let P := F - Polynomial.C a
  let D := colemanNorm K π
  let q := residueCard K
  have hqpos : 0 < q := Nat.card_pos
  have hFdata := test_iterate_monic_natDegree K π 1
  have hFmonic0 : (lubinTatePolynomial K π).Monic := by
    simpa [lubinTateIterate] using hFdata.1
  have hFnat0 : (lubinTatePolynomial K π).natDegree = q := by
    simpa [lubinTateIterate, q] using hFdata.2
  have hFmonic : F.Monic := hFmonic0.map φ
  have hFnat : F.natDegree = q := by
    rw [hFmonic0.natDegree_map, hFnat0]
  have hPmonic : P.Monic := by
    apply hFmonic.sub_of_left
    exact Polynomial.degree_C_le.trans_lt (by
      rw [Polynomial.degree_eq_natDegree hFmonic.ne_zero, hFnat]
      exact_mod_cast hqpos)
  have hPnat : P.natDegree = q := by
    calc
      P.natDegree = F.natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
          rw [Polynomial.natDegree_C, hFnat]
          exact hqpos)
      _ = q := hFnat
  have hPss := test_fiber_splits_separable K Ksep π m hm n hnm a ha
  dsimp only at hPss
  change P.Splits ∧ P.Separable at hPss
  have hcardRoots : Fintype.card P.roots = q := by
    rw [Multiset.card_coe, ← hPss.1.natDegree_eq_card_roots, hPnat]
  let e : P.roots ≃ Fin q := (Fintype.equivFin P.roots).trans (finCongr hcardRoots)
  let β : Fin q → level.field := fun i => ((e.symm i : P.roots) : level.field)
  have hβroot (i : Fin q) : P.IsRoot (β i) := by
    apply (Polynomial.mem_roots hPmonic.ne_zero).mp
    exact Multiset.coe_mem
  have hcoe : Function.Injective (fun r : P.roots => (r : level.field)) := by
    rintro ⟨x, ix⟩ ⟨y, iy⟩ hxy
    dsimp at hxy
    subst y
    congr
    have hc := Multiset.nodup_iff_count_le_one.mp (Polynomial.nodup_roots hPss.2) x
    omega
  have hβinj : Function.Injective β := by
    intro i j hij
    apply e.symm.injective
    exact hcoe hij
  let V : Matrix (Fin q) (Fin q) level.field := Matrix.vandermonde β
  have hdetV : Matrix.det V ≠ 0 := by
    dsimp only [V]
    rw [Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro hji
    have heq := hβinj hji
    subst j
    exact (Finset.mem_Ioi.mp hj).false
  have ham : ((lubinTateIterate K π m).map φ).IsRoot a :=
    test_iterate_root_mono K π φ a (by omega) ha
  let aO := testTorsionRootInteger K Ksep π m hm a ham
  have haOmax : aO ∈ LocalMaximalIdeal level.field :=
    testTorsionRootInteger_mem_maximalIdeal K Ksep π m hm a ham
  have hdvd := test_fiber_dvd_iterate K π φ n a ha
  have hβm (i : Fin q) : ((lubinTateIterate K π m).map φ).IsRoot (β i) := by
    have hnext : ((lubinTateIterate K π (n + 1)).map φ).IsRoot (β i) :=
      (hβroot i).dvd hdvd
    exact test_iterate_root_mono K π φ (β i) (by omega) hnext
  let βO (i : Fin q) := testTorsionRootInteger K Ksep π m hm (β i) (hβm i)
  have hβOmax (i : Fin q) : βO i ∈ LocalMaximalIdeal level.field :=
    testTorsionRootInteger_mem_maximalIdeal K Ksep π m hm (β i) (hβm i)
  have hc : ∀ x, ((c x : RingOfIntegers level.field) : level.field) = φ x :=
    level.integerAlgebraMap_apply
  have hfa (i : Fin q) :
      testAdicEval K c (βO i) (hβOmax i) (lubinTateSeries K π) = aO := by
    rw [show lubinTateSeries K π =
      ((lubinTatePolynomial K π : Polynomial (RingOfIntegers K)) :
        PowerSeries (RingOfIntegers K)) from rfl,
      testAdicEval_coe]
    apply Subtype.ext
    change algebraMap (RingOfIntegers level.field) level.field
      (Polynomial.eval₂ c (βO i) (lubinTatePolynomial K π)) = (aO : level.field)
    rw [Polynomial.hom_eval₂]
    rw [show (algebraMap (RingOfIntegers level.field) level.field).comp c = φ by
      apply RingHom.ext
      intro x
      exact hc x]
    change Polynomial.eval₂ φ (β i) (lubinTatePolynomial K π) = a
    have hr := hβroot i
    dsimp only [P, F] at hr
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_map, Polynomial.eval_C, sub_eq_zero] at hr
    exact hr
  have hsubst (i : Fin q) (h : PowerSeries (RingOfIntegers K)) :
      testAdicEval K c (βO i) (hβOmax i)
          (PowerSeries.subst (lubinTateSeries K π) h) =
        testAdicEval K c aO haOmax h := by
    apply testAdicEval_subst K c (βO i) aO (hβOmax i) haOmax
      (lubinTateSeries K π) h
    · have hq0 : residueCard K ≠ 0 := Nat.card_pos.ne'
      simp [lubinTateSeries, lubinTatePolynomial, hq0]
    · exact hfa i
  have hvalueA (h : PowerSeries (RingOfIntegers K)) :
      algebraMap (RingOfIntegers level.field) level.field
          (testAdicEval K c aO haOmax h) =
        powerSeriesValue K φ a h := by
    have hv := testAdicEval_apply K c hc aO haOmax hinc h
    rw [show (aO : level.field) = a by rfl] at hv
    exact hv
  have hvalueβ (i : Fin q) (h : PowerSeries (RingOfIntegers K)) :
      algebraMap (RingOfIntegers level.field) level.field
          (testAdicEval K c (βO i) (hβOmax i) h) =
        powerSeriesValue K φ (β i) h := by
    have hv := testAdicEval_apply K c hc (βO i) (hβOmax i) hinc h
    rw [show (βO i : level.field) = β i by rfl] at hv
    exact hv
  let A : Matrix (Fin q) (Fin q) level.field := fun i j =>
    powerSeriesValue K φ a (D.multiplicationMatrix g i j)
  let lam : Fin q → level.field := fun i => powerSeriesValue K φ (β i) g
  have heigen (k j : Fin q) :
      ∑ i : Fin q, β k ^ (i : ℕ) * A i j = lam k * β k ^ (j : ℕ) := by
    have hexp := congrArg (testAdicEval K c (βO k) (hβOmax k))
      (test_mul_expansion K π D g j)
    simp only [map_mul, map_pow, map_sum] at hexp
    have hX : testAdicEval K c (βO k) (hβOmax k) PowerSeries.X = βO k :=
      testAdicEval_X K c (βO k) (hβOmax k)
    rw [hX] at hexp
    simp_rw [hsubst] at hexp
    have hmap := congrArg (algebraMap (RingOfIntegers level.field) level.field) hexp
    simp only [map_mul, map_pow, map_sum] at hmap
    simp_rw [hvalueA] at hmap
    rw [hvalueβ] at hmap
    change lam k * β k ^ (j : ℕ) =
      ∑ i : Fin q, A i j * β k ^ (i : ℕ) at hmap
    calc
      ∑ i : Fin q, β k ^ (i : ℕ) * A i j =
          ∑ i : Fin q, A i j * β k ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = lam k * β k ^ (j : ℕ) := hmap.symm
  have hmatrix : V * A = Matrix.diagonal lam * V := by
    apply Matrix.ext
    intro k j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simpa [V, Matrix.vandermonde_apply] using heigen k j
  have hdetA : Matrix.det A = ∏ i, lam i := by
    have hdet := congrArg Matrix.det hmatrix
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
    rw [mul_comm (∏ i, lam i) (Matrix.det V)] at hdet
    exact mul_left_cancel₀ hdetV hdet
  calc
    powerSeriesValue K φ a (D.operator g) =
        algebraMap (RingOfIntegers level.field) level.field
          (testAdicEval K c aO haOmax (D.operator g)) := (hvalueA _).symm
    _ = algebraMap (RingOfIntegers level.field) level.field
          (testAdicEval K c aO haOmax (Matrix.det (D.multiplicationMatrix g))) := by
      rw [test_operator_eq_det K π D g]
    _ = Matrix.det A := by
      rw [RingHom.map_det, RingHom.map_det]
      apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      change algebraMap (RingOfIntegers level.field) level.field
        (testAdicEval K c aO haOmax (D.multiplicationMatrix g i j)) =
          powerSeriesValue K φ a (D.multiplicationMatrix g i j)
      exact hvalueA _
    _ = ∏ i, lam i := hdetA
    _ = (P.roots.map (fun z => powerSeriesValue K φ z g)).prod := by
      let f : level.field → level.field := fun z => powerSeriesValue K φ z g
      have hprod : (P.roots.map f).prod = ∏ z : P.roots, f z := by
        symm
        change (((Finset.univ : Finset P.roots).val.map
          (fun z : P.roots => f (z : level.field))).prod) = _
        rw [Multiset.map_univ]
      rw [show (P.roots.map (fun z => powerSeriesValue K φ z g)).prod =
        ∏ z : P.roots, f z from hprod]
      symm
      apply Fintype.prod_equiv e
      intro z
      simp [f, lam, β]


set_option maxHeartbeats 800000 in
private theorem test_fiber_roots_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (n r : ℕ) (hnm : n + 1 ≤ m)
    (a : (lubinTateLevel K Ksep π m hm).field)
    (ha : ((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot a) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    let φ := algebraMap (RingOfIntegers K) level.field
    ((lubinTateIterate K π (r + 1)).map φ - Polynomial.C a).roots =
      ((lubinTatePolynomial K π).map φ - Polynomial.C a).roots.bind
        (fun b => ((lubinTateIterate K π r).map φ - Polynomial.C b).roots) := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  let φ := algebraMap (RingOfIntegers K) level.field
  let F := (lubinTatePolynomial K π).map φ
  let Fr := (lubinTateIterate K π r).map φ
  let P := F - Polynomial.C a
  have houter := test_fiber_splits_separable K Ksep π m hm n hnm a ha
  dsimp only at houter
  have hFdata := test_iterate_monic_natDegree K π 1
  have hFmonic0 : (lubinTatePolynomial K π).Monic := by
    simpa [lubinTateIterate] using hFdata.1
  have hFnat0 : (lubinTatePolynomial K π).natDegree = residueCard K := by
    simpa [lubinTateIterate] using hFdata.2
  have hFmonic : F.Monic := hFmonic0.map φ
  have hPmonic : P.Monic := by
    apply hFmonic.sub_of_left
    exact Polynomial.degree_C_le.trans_lt (by
      rw [Polynomial.degree_eq_natDegree hFmonic.ne_zero,
        hFmonic0.natDegree_map, hFnat0]
      exact_mod_cast (Nat.card_pos : 0 < residueCard K))
  have hfactor := houter.1.eq_prod_roots_of_monic hPmonic
  change P = (P.roots.map fun x => Polynomial.X - Polynomial.C x).prod at hfactor
  have hFrmonic : Fr.Monic :=
    (test_iterate_monic_natDegree K π r).1.map φ
  have hinner (b : level.field) : (Fr - Polynomial.C b).Monic := by
    apply hFrmonic.sub_of_left
    exact Polynomial.degree_C_le.trans_lt (by
      rw [Polynomial.degree_eq_natDegree hFrmonic.ne_zero,
        (test_iterate_monic_natDegree K π r).1.natDegree_map,
        (test_iterate_monic_natDegree K π r).2]
      exact_mod_cast (pow_pos Nat.card_pos r))
  have hpoly : (lubinTateIterate K π (r + 1)).map φ - Polynomial.C a =
      (P.roots.map fun b => Fr - Polynomial.C b).prod := by
    calc
      (lubinTateIterate K π (r + 1)).map φ - Polynomial.C a =
          P.comp Fr := by
        rw [lubinTateIterate, Polynomial.map_comp]
        dsimp only [P, F, Fr]
        rw [Polynomial.sub_comp]
        simp
      _ = ((P.roots.map fun x => Polynomial.X - Polynomial.C x).prod).comp Fr := by
        rw [← hfactor]
      _ = (P.roots.map fun b => Fr - Polynomial.C b).prod := by
        induction P.roots using Multiset.induction_on with
        | empty => simp
        | @cons b s ih =>
            simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_comp, ih,
              Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  dsimp only
  rw [hpoly, Polynomial.roots_multiset_prod]
  · simpa only [Multiset.bind_map, P, F, Fr, φ, level]
  · simp only [Multiset.mem_map, not_exists, not_and]
    intro b hb
    exact (hinner b).ne_zero


set_option maxHeartbeats 1600000 in
private theorem test_operator_iterate_fiber_product
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (hinc :
      let level := lubinTateLevel K Ksep π m hm
      letI : FiniteDimensional K level.field := level.finiteDimensional
      letI : ValuativeRel level.field := level.localFieldData.valuativeRel
      letI : TopologicalSpace level.field := level.localFieldData.topology
      letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
      letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
      letI : TopologicalSpace (RingOfIntegers level.field) :=
        (LocalMaximalIdeal level.field).adicTopology
      Continuous (algebraMap (RingOfIntegers level.field) level.field))
    (n r : ℕ) (hnr : n + r ≤ m)
    (a : (lubinTateLevel K Ksep π m hm).field)
    (ha : ((lubinTateIterate K π n).map
      (algebraMap (RingOfIntegers K)
        (lubinTateLevel K Ksep π m hm).field)).IsRoot a)
    (g : PowerSeries (RingOfIntegers K)) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    let φ := algebraMap (RingOfIntegers K) level.field
    powerSeriesValue K φ a (colemanNormIterate K π r g) =
      ((((lubinTateIterate K π r).map φ - Polynomial.C a).roots.map
        (fun z => powerSeriesValue K φ z g)).prod) := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  let φ := algebraMap (RingOfIntegers K) level.field
  dsimp only
  induction r generalizing n a with
  | zero =>
      simp [colemanNormIterate, lubinTateIterate, Polynomial.roots_X_sub_C]
  | succ r ih =>
      have hn1m : n + 1 ≤ m := by omega
      have hstep := test_fiber_operator_product K Ksep π m hm n hn1m a ha hinc
        (colemanNormIterate K π r g)
      dsimp only at hstep
      have hrootb (b : level.field)
          (hb : b ∈ ((lubinTatePolynomial K π).map φ - Polynomial.C a).roots) :
          ((lubinTateIterate K π (n + 1)).map φ).IsRoot b := by
        have hbroot := (Polynomial.mem_roots
          (show (lubinTatePolynomial K π).map φ - Polynomial.C a ≠ 0 from by
            have hm0 := (test_iterate_monic_natDegree K π 1).1
            have hmF0 : (lubinTatePolynomial K π).Monic := by
              simpa [lubinTateIterate] using hm0
            have hmF : ((lubinTatePolynomial K π).map φ).Monic := hmF0.map φ
            have hnat : (lubinTatePolynomial K π).natDegree = residueCard K := by
              simpa [lubinTateIterate] using (test_iterate_monic_natDegree K π 1).2
            apply (hmF.sub_of_left (Polynomial.degree_C_le.trans_lt ?_)).ne_zero
            rw [Polynomial.degree_eq_natDegree hmF.ne_zero,
              hmF0.natDegree_map, hnat]
            exact_mod_cast (Nat.card_pos : 0 < residueCard K))).mp hb
        exact hbroot.dvd (test_fiber_dvd_iterate K π φ n a ha)
      have hreplace :
          (((lubinTatePolynomial K π).map φ - Polynomial.C a).roots.map
            (fun b => powerSeriesValue K φ b (colemanNormIterate K π r g))).prod =
          (((lubinTatePolynomial K π).map φ - Polynomial.C a).roots.map
            (fun b => (((lubinTateIterate K π r).map φ - Polynomial.C b).roots.map
              (fun z => powerSeriesValue K φ z g)).prod)).prod := by
        apply congrArg Multiset.prod
        apply Multiset.map_congr rfl
        intro b hb
        exact ih (n := n + 1) (a := b) (by omega) (hrootb b hb)
      calc
        powerSeriesValue K φ a (colemanNormIterate K π (r + 1) g) =
            powerSeriesValue K φ a
              ((colemanNorm K π).operator (colemanNormIterate K π r g)) := by
          change powerSeriesValue K φ a
            (((colemanNorm K π).operator^[r + 1]) g) =
              powerSeriesValue K φ a
                ((colemanNorm K π).operator (((colemanNorm K π).operator^[r]) g))
          rw [Function.iterate_succ_apply']
        _ = (((lubinTatePolynomial K π).map φ - Polynomial.C a).roots.map
              (fun b => powerSeriesValue K φ b (colemanNormIterate K π r g))).prod := hstep
        _ = (((lubinTatePolynomial K π).map φ - Polynomial.C a).roots.map
              (fun b => (((lubinTateIterate K π r).map φ - Polynomial.C b).roots.map
                (fun z => powerSeriesValue K φ z g)).prod)).prod := hreplace
        _ = (Multiset.map (fun z => powerSeriesValue K φ z g)
              (Multiset.bind
                ((lubinTatePolynomial K π).map φ - Polynomial.C a).roots
                (fun b => ((lubinTateIterate K π r).map φ - Polynomial.C b).roots))).prod := by
          rw [Multiset.map_bind, Multiset.prod_bind]
        _ = (((lubinTateIterate K π (r + 1)).map φ - Polynomial.C a).roots.map
              (fun z => powerSeriesValue K φ z g)).prod := by
          rw [test_fiber_roots_succ K Ksep π m hm n r hn1m a ha]


private theorem test_powerSeriesValue_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [TopologicalSpace L] (φ : RingOfIntegers K →+* L)
    (g : PowerSeries (RingOfIntegers K)) :
    powerSeriesValue K φ 0 g = φ (PowerSeries.constantCoeff g) := by
  unfold powerSeriesValue
  rw [tsum_eq_single 0]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · intro b hb
    simp [zero_pow hb]

private theorem test_iteration_torsion_product
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (hinc :
      let level := lubinTateLevel K Ksep π m hm
      letI : FiniteDimensional K level.field := level.finiteDimensional
      letI : ValuativeRel level.field := level.localFieldData.valuativeRel
      letI : TopologicalSpace level.field := level.localFieldData.topology
      letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
      letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
      letI : TopologicalSpace (RingOfIntegers level.field) :=
        (LocalMaximalIdeal level.field).adicTopology
      Continuous (algebraMap (RingOfIntegers level.field) level.field))
    (g : PowerSeries (RingOfIntegers K)) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    algebraMap (RingOfIntegers K) level.field
        (PowerSeries.constantCoeff (colemanNormIterate K π m g)) =
      lubinTateTorsionProduct K Ksep π m hm g := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  let φ := algebraMap (RingOfIntegers K) level.field
  have hzero : ((lubinTateIterate K π 0).map φ).IsRoot (0 : level.field) := by
    simp [lubinTateIterate]
  have h := test_operator_iterate_fiber_product K Ksep π m hm hinc 0 m
    (by omega) (0 : level.field) hzero g
  dsimp only at h
  rw [test_powerSeriesValue_zero K φ] at h
  change _ = (((lubinTateIterate K π m).map φ).roots.map
    (fun β => powerSeriesValue K φ β g)).prod
  simpa only [sub_zero, Polynomial.C_0] using h


private theorem test_algEquiv_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [T2Space L] [ContinuousSMul K L]
    (σ : L ≃ₐ[K] L) : Continuous σ := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let hnorm : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValuativeRel.ValueGroupWithZero K)
  exact LinearMap.continuous_of_finiteDimensional (hnorm := hnorm) σ.toLinearMap

private theorem test_powerSeriesValue_algEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (σ : L ≃ₐ[K] L) (x : L) (hx : PowerSeries.HasEval x)
    (g : PowerSeries (RingOfIntegers K)) :
    σ (powerSeriesValue K (algebraMap (RingOfIntegers K) L) x g) =
      powerSeriesValue K (algebraMap (RingOfIntegers K) L) (σ x) g := by
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  letI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  have hs := (test_summable K x hx g).hasSum
  have hsmap := hs.map σ.toRingEquiv.toRingHom (test_algEquiv_continuous K σ)
  unfold powerSeriesValue
  change σ.toRingEquiv.toRingHom
    (∑' n : ℕ, algebraMap (RingOfIntegers K) L (PowerSeries.coeff n g) * x ^ n) = _
  rw [← hsmap.tsum_eq]
  congr 1
  funext n
  simp only [Function.comp_apply, map_mul, map_pow]
  apply congrArg₂ (· * ·)
  · rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K L]
    exact σ.commutes ((PowerSeries.coeff n g : RingOfIntegers K) : K)
  · rfl


set_option maxHeartbeats 1200000 in
private theorem test_galoisEquiv_primitiveRoots
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
    letI : DecidableEq level.field := Classical.decEq level.field
    let Q := (primitiveDivisionPolynomial K π m).map
      (algebraMap (RingOfIntegers K) level.field)
    ∃ e : (level.field ≃ₐ[K] level.field) ≃ Q.roots.toFinset,
      ∀ σ, ((e σ : Q.roots.toFinset) : level.field) = σ level.generator := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
  letI : DecidableEq level.field := Classical.decEq level.field
  let Q := (primitiveDivisionPolynomial K π m).map
    (algebraMap (RingOfIntegers K) level.field)
  have hQdata := test_primitive_splits_separable_in_level K Ksep π m hm m hm le_rfl
  dsimp only at hQdata
  have hQss : Q.Splits ∧ Q.Separable := by simpa only [Q] using hQdata
  have hQmonic0 := (test_primitive_monic_natDegree K π m hm).1
  have hQmonic : Q.Monic := hQmonic0.map _
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hambient_to_level {x : level.field}
      (hx : ((primitiveDivisionPolynomial K π m).map
        (algebraMap (RingOfIntegers K) Ksep)).IsRoot (x : Ksep)) : Q.IsRoot x := by
    rw [Polynomial.IsRoot.def]
    apply (algebraMap level.field Ksep).injective
    rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂]
    change (primitiveDivisionPolynomial K π m).eval₂
      ((algebraMap level.field Ksep).comp
        (algebraMap (RingOfIntegers K) level.field)) (x : Ksep) = 0
    rw [show (algebraMap level.field Ksep).comp
      (algebraMap (RingOfIntegers K) level.field) =
        algebraMap (RingOfIntegers K) Ksep by
          apply RingHom.ext
          intro z
          exact IsScalarTower.algebraMap_apply
            (RingOfIntegers K) level.field Ksep z]
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  have hconj := (lubinTateLevel_galoisEquiv K Ksep π m hm).2.2
  let f : (level.field ≃ₐ[K] level.field) → Q.roots.toFinset := fun σ => by
    let y := σ level.generator
    have hyprim : IsPrimitiveLubinTateDivisionPoint K Ksep π m (y : Ksep) := by
      have hyrange : (y : Ksep) ∈ Set.range (fun τ :
          (level.field ≃ₐ[K] level.field) => (((τ level.generator : level.field) : Ksep))) :=
        ⟨σ, rfl⟩
      rw [hconj] at hyrange
      exact hyrange
    have hyamb := (primitiveDivisionPolynomial_eisenstein K Ksep π m hm).2.2
      (y : Ksep) |>.mpr hyprim
    exact ⟨y, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hQne).mpr (hambient_to_level hyamb))⟩
  have hfsurj : Function.Surjective f := by
    intro y
    have hyroot : Q.IsRoot (y : level.field) :=
      (Polynomial.mem_roots hQne).mp (Multiset.mem_toFinset.mp y.prop)
    have hyamb : ((primitiveDivisionPolynomial K π m).map
        (algebraMap (RingOfIntegers K) Ksep)).IsRoot ((y : level.field) : Ksep) := by
      have hmap := hyroot.map (f := algebraMap level.field Ksep)
      dsimp only [Q] at hmap
      rw [Polynomial.map_map] at hmap
      have hcmap : (algebraMap level.field Ksep).comp
          (algebraMap (RingOfIntegers K) level.field) =
          algebraMap (RingOfIntegers K) Ksep := by
        apply RingHom.ext
        intro z
        exact IsScalarTower.algebraMap_apply
          (RingOfIntegers K) level.field Ksep z
      rw [hcmap] at hmap
      have hycoe : algebraMap level.field Ksep (y : level.field) =
          ((y : level.field) : Ksep) := rfl
      rw [hycoe] at hmap
      exact hmap
    have hyprim := (primitiveDivisionPolynomial_eisenstein K Ksep π m hm).2.2
      (((y : level.field) : Ksep)) |>.mp hyamb
    have hyrange : ((y : level.field) : Ksep) ∈ Set.range (fun σ :
        (level.field ≃ₐ[K] level.field) => (((σ level.generator : level.field) : Ksep))) := by
      rw [hconj]
      exact hyprim
    obtain ⟨σ, hσ⟩ := hyrange
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    change σ level.generator = (y : level.field)
    apply (algebraMap level.field Ksep).injective
    change (((σ level.generator : level.field) : Ksep)) =
      (((y : level.field) : Ksep))
    exact hσ
  have hcard : Fintype.card (level.field ≃ₐ[K] level.field) =
      Fintype.card Q.roots.toFinset := by
    calc
      Fintype.card (level.field ≃ₐ[K] level.field) =
          Nat.card (level.field ≃ₐ[K] level.field) := Nat.card_eq_fintype_card.symm
      _ = Module.finrank K level.field := IsGalois.card_aut_eq_finrank K level.field
      _ = (residueCard K - 1) * residueCard K ^ (m - 1) := level.degree
      _ = (primitiveDivisionPolynomial K π m).natDegree :=
        (primitiveDivisionPolynomial_eisenstein K Ksep π m hm).2.1.symm
      _ = Q.natDegree := (hQmonic0.natDegree_map _).symm
      _ = Q.roots.card := hQss.1.natDegree_eq_card_roots
      _ = Q.roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hQss.2)).symm
      _ = Fintype.card Q.roots.toFinset := by
        symm
        exact Fintype.card_coe _
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hfsurj, hcard⟩
  let e := Equiv.ofBijective f hfbij
  dsimp only
  refine ⟨e, ?_⟩
  intro σ
  rfl


set_option maxHeartbeats 1200000 in
private theorem test_primitive_norm_product
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : Units (PowerSeries (RingOfIntegers K))) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
    algebraMap K level.field
        (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)) =
      lubinTatePrimitiveTorsionProduct K Ksep π m hm
        (g : PowerSeries (RingOfIntegers K)) := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  letI : IsGalois K level.field := (lubinTateGaloisData K Ksep π).isGalois m hm
  letI : DecidableEq level.field := Classical.decEq level.field
  let Q := (primitiveDivisionPolynomial K π m).map
    (algebraMap (RingOfIntegers K) level.field)
  obtain ⟨e, he⟩ := test_galoisEquiv_primitiveRoots K Ksep π m hm
  have hQdata := test_primitive_splits_separable_in_level K Ksep π m hm m hm le_rfl
  dsimp only at hQdata
  have hQsep : Q.Separable := by simpa only [Q] using hQdata.2
  have heval (σ : level.field ≃ₐ[K] level.field) :
      σ (level.evaluation (g : PowerSeries (RingOfIntegers K))) =
        powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
          (σ level.generator) (g : PowerSeries (RingOfIntegers K)) := by
    rw [level.evaluation_apply]
    exact test_powerSeriesValue_algEquiv K σ level.generator
      level.generator_hasEval (g : PowerSeries (RingOfIntegers K))
  have hrootprod :
      ∏ y : Q.roots.toFinset,
          powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
            (y : level.field) (g : PowerSeries (RingOfIntegers K)) =
        (Q.roots.map (fun y => powerSeriesValue K
          (algebraMap (RingOfIntegers K) level.field) y
            (g : PowerSeries (RingOfIntegers K)))).prod := by
    rw [Finset.prod_multiset_map_count]
    calc
      (∏ y : Q.roots.toFinset,
          powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
            (y : level.field) (g : PowerSeries (RingOfIntegers K))) =
        ∏ y ∈ Q.roots.toFinset,
          powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
            y (g : PowerSeries (RingOfIntegers K)) :=
          Finset.prod_coe_sort Q.roots.toFinset
            (fun y : level.field => powerSeriesValue K
              (algebraMap (RingOfIntegers K) level.field) y
                (g : PowerSeries (RingOfIntegers K)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro y hy
        rw [Multiset.count_eq_one_of_mem (Polynomial.nodup_roots hQsep)
          (Multiset.mem_toFinset.mp hy), pow_one]
  change algebraMap K level.field
      (((normUnitsHom K level.field
        (Units.map level.evaluation.toMonoidHom g) : Units K) : K)) = _
  rw [normUnitsHom_eq_galoisProduct]
  change (∏ σ : (level.field ≃ₐ[K] level.field),
      σ (level.evaluation (g : PowerSeries (RingOfIntegers K)))) =
    (Q.roots.map (fun β => powerSeriesValue K
      (algebraMap (RingOfIntegers K) level.field) β
        (g : PowerSeries (RingOfIntegers K)))).prod
  calc
    (∏ σ : (level.field ≃ₐ[K] level.field),
        σ (level.evaluation (g : PowerSeries (RingOfIntegers K)))) =
      ∏ σ : (level.field ≃ₐ[K] level.field),
        powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
          (σ level.generator) (g : PowerSeries (RingOfIntegers K)) := by
      apply Finset.prod_congr rfl
      intro σ hσ
      exact heval σ
    _ = ∏ y : Q.roots.toFinset,
        powerSeriesValue K (algebraMap (RingOfIntegers K) level.field)
          (y : level.field) (g : PowerSeries (RingOfIntegers K)) := by
      apply Fintype.prod_equiv e
      intro σ
      rw [he σ]
    _ = _ := hrootprod


private theorem test_torsion_roots_hasEval
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (hinc :
      let level := lubinTateLevel K Ksep π m hm
      letI : FiniteDimensional K level.field := level.finiteDimensional
      letI : ValuativeRel level.field := level.localFieldData.valuativeRel
      letI : TopologicalSpace level.field := level.localFieldData.topology
      letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
      letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
      letI : TopologicalSpace (RingOfIntegers level.field) :=
        (LocalMaximalIdeal level.field).adicTopology
      Continuous (algebraMap (RingOfIntegers level.field) level.field)) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    (∀ β : level.field,
      ((primitiveDivisionPolynomial K π m).map
        (algebraMap (RingOfIntegers K) level.field)).IsRoot β →
          PowerSeries.HasEval β) ∧
    (∀ β : level.field,
      ((lubinTateIterate K π m).map
        (algebraMap (RingOfIntegers K) level.field)).IsRoot β →
          PowerSeries.HasEval β) := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  let φ := algebraMap (RingOfIntegers K) level.field
  have hall (β : level.field)
      (hβ : ((lubinTateIterate K π m).map φ).IsRoot β) :
      PowerSeries.HasEval β := by
    let βO := testTorsionRootInteger K Ksep π m hm β hβ
    have hβmax : βO ∈ LocalMaximalIdeal level.field :=
      testTorsionRootInteger_mem_maximalIdeal K Ksep π m hm β hβ
    letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
    letI : TopologicalSpace (RingOfIntegers level.field) :=
      (LocalMaximalIdeal level.field).adicTopology
    have hO : PowerSeries.HasEval βO :=
      WithIdeal.isTopologicallyNilpotent_of_mem hβmax
    have hmap := IsTopologicallyNilpotent.map hinc hO
    change IsTopologicallyNilpotent
      (algebraMap (RingOfIntegers level.field) level.field βO) at hmap
    rw [show algebraMap (RingOfIntegers level.field) level.field βO = β by rfl] at hmap
    exact hmap
  refine ⟨?_, hall⟩
  intro β hβ
  have hfac := congrArg (Polynomial.map φ)
    (test_iterate_factor_primitive K π m hm)
  rw [Polynomial.map_mul] at hfac
  have hdvd : (primitiveDivisionPolynomial K π m).map φ ∣
      (lubinTateIterate K π m).map φ := by
    rw [hfac]
    exact dvd_mul_left _ _
  exact hall β (hβ.dvd hdvd)


set_option maxHeartbeats 1200000 in
private theorem test_constant_iteration_primitive
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (hinc :
      let level := lubinTateLevel K Ksep π m hm
      letI : FiniteDimensional K level.field := level.finiteDimensional
      letI : ValuativeRel level.field := level.localFieldData.valuativeRel
      letI : TopologicalSpace level.field := level.localFieldData.topology
      letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
      letI : WithIdeal (RingOfIntegers level.field) := ⟨LocalMaximalIdeal level.field⟩
      letI : TopologicalSpace (RingOfIntegers level.field) :=
        (LocalMaximalIdeal level.field).adicTopology
      Continuous (algebraMap (RingOfIntegers level.field) level.field))
    (g : Units (PowerSeries (RingOfIntegers K))) :
    algebraMap (RingOfIntegers K) K
        (PowerSeries.constantCoeff (colemanNormIterate K π m
          (g : PowerSeries (RingOfIntegers K)))) =
      algebraMap (RingOfIntegers K) K
          (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1)
            (g : PowerSeries (RingOfIntegers K)))) *
        (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)) := by
  classical
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  let φ := algebraMap (RingOfIntegers K) level.field
  let gm := (g : PowerSeries (RingOfIntegers K))
  have hfull := test_iteration_torsion_product K Ksep π m hm hinc gm
  dsimp only at hfull
  have hzero : ((lubinTateIterate K π 0).map φ).IsRoot (0 : level.field) := by
    simp [lubinTateIterate]
  have hprev := test_operator_iterate_fiber_product K Ksep π m hm hinc 0 (m - 1)
    (by omega) (0 : level.field) hzero gm
  dsimp only at hprev
  rw [test_powerSeriesValue_zero K φ] at hprev
  simp only [Polynomial.C_0, sub_zero] at hprev
  have hnorm := test_primitive_norm_product K Ksep π m hm g
  dsimp only at hnorm
  let Fm := (lubinTateIterate K π m).map φ
  let Fprev := (lubinTateIterate K π (m - 1)).map φ
  let Q := (primitiveDivisionPolynomial K π m).map φ
  have hfac0 := congrArg (Polynomial.map φ)
    (test_iterate_factor_primitive K π m hm)
  have hfac : Fm = Fprev * Q := by
    simpa only [Fm, Fprev, Q, Polynomial.map_mul] using hfac0
  have hFprevne : Fprev ≠ 0 :=
    ((test_iterate_monic_natDegree K π (m - 1)).1.map φ).ne_zero
  have hQne : Q ≠ 0 :=
    ((test_primitive_monic_natDegree K π m hm).1.map φ).ne_zero
  have hroots : Fm.roots = Fprev.roots + Q.roots := by
    rw [hfac, Polynomial.roots_mul (mul_ne_zero hFprevne hQne)]
  let valfun : level.field → level.field := fun z => powerSeriesValue K φ z gm
  have hprod : (Fm.roots.map valfun).prod =
      (Fprev.roots.map valfun).prod * (Q.roots.map valfun).prod := by
    rw [hroots, Multiset.map_add, Multiset.prod_add]
  apply (algebraMap K level.field).injective
  rw [map_mul]
  rw [← IsScalarTower.algebraMap_apply (RingOfIntegers K) K level.field,
    ← IsScalarTower.algebraMap_apply (RingOfIntegers K) K level.field]
  change φ (PowerSeries.constantCoeff (colemanNormIterate K π m gm)) =
    φ (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1) gm)) *
      algebraMap K level.field
        (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K))
  rw [hfull, hprev, hnorm]
  exact hprod


private theorem test_powerSeriesCongruent_iff_map_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (I : Ideal (RingOfIntegers K))
    (f h : PowerSeries (RingOfIntegers K)) :
    PowerSeriesCongruent K I f h ↔
      PowerSeries.map (Ideal.Quotient.mk I) f =
        PowerSeries.map (Ideal.Quotient.mk I) h := by
  constructor
  · intro hfh
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact Ideal.Quotient.eq.mpr (hfh n)
  · intro hmap n
    have hn := congrArg (PowerSeries.coeff n) hmap
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, Ideal.Quotient.eq] at hn
    exact hn

private theorem test_primitive_product_mem_principal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : Units (PowerSeries (RingOfIntegers K)))
    (hmax : uniformizerIdeal K π = LocalMaximalIdeal K)
    (hconstant :
      algebraMap (RingOfIntegers K) K
          (PowerSeries.constantCoeff (colemanNormIterate K π m
            (g : PowerSeries (RingOfIntegers K)))) =
        algebraMap (RingOfIntegers K) K
            (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1)
              (g : PowerSeries (RingOfIntegers K)))) *
          (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K))) :
    lubinTatePrimitiveProduct K Ksep π m hm g ∈ principalUnitSubgroup K m := by
  classical
  let D := colemanNorm K π
  let T : Units (PowerSeries (RingOfIntegers K)) →*
      Units (PowerSeries (RingOfIntegers K)) := Units.map D.operator
  let G : ℕ → Units (PowerSeries (RingOfIntegers K)) := fun r =>
    (T : Units (PowerSeries (RingOfIntegers K)) →
      Units (PowerSeries (RingOfIntegers K)))^[r] g
  let d : ℕ → Units (PowerSeries (RingOfIntegers K)) := fun r =>
    G (r + 1) * (G r)⁻¹
  have hG (r : ℕ) : (G r : PowerSeries (RingOfIntegers K)) =
      colemanNormIterate K π r (g : PowerSeries (RingOfIntegers K)) := by
    induction r with
    | zero => rfl
    | succ r ihr =>
        change ((T^[r + 1] g : Units (PowerSeries (RingOfIntegers K))) :
          PowerSeries (RingOfIntegers K)) = _
        rw [show r + 1 = r.succ by omega, Function.iterate_succ_apply']
        change D.operator ((T^[r] g : Units (PowerSeries (RingOfIntegers K))) :
          PowerSeries (RingOfIntegers K)) = _
        rw [ihr]
        unfold colemanNormIterate
        rw [Function.iterate_succ_apply']
  have hdsucc (r : ℕ) : d (r + 1) = T (d r) := by
    change G (r + 2) * (G (r + 1))⁻¹ = T (G (r + 1) * (G r)⁻¹)
    rw [map_mul, map_inv]
    congr 1
    · change T^[r + 2] g = T (T^[r + 1] g)
      rw [show r + 2 = (r + 1).succ by omega, Function.iterate_succ_apply']
    · congr 1
      change T^[r + 1] g = T (T^[r] g)
      rw [show r + 1 = r.succ by omega, Function.iterate_succ_apply']
  have hdcong : ∀ r : ℕ, 1 ≤ r →
      PowerSeriesCongruent K (uniformizerIdeal K π ^ r)
        (d (r - 1) : PowerSeries (RingOfIntegers K)) 1 := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
        norm_num
        have hbase := (colemanNorm_congruences K π
          (g : PowerSeries (RingOfIntegers K)) g.isUnit).1
        apply (test_powerSeriesCongruent_iff_map_eq K _ _ _).2
        have hmap := (test_powerSeriesCongruent_iff_map_eq K _ _ _).1 hbase
        let Φ := PowerSeries.map
          (Ideal.Quotient.mk (uniformizerIdeal K π))
        change Φ (D.operator (g : PowerSeries (RingOfIntegers K))) = Φ g at hmap
        let Φu : Units (PowerSeries (RingOfIntegers K)) →*
            Units (PowerSeries (RingOfIntegers K ⧸ uniformizerIdeal K π)) :=
          Units.map Φ.toMonoidHom
        have hmapu : Φu (T g) = Φu g := by
          apply Units.ext
          exact hmap
        have hu : Φu (d 0) = 1 := by
          change Φu (T g * g⁻¹) = 1
          rw [map_mul, map_inv, hmapu]
          exact mul_inv_cancel _
        have hv := congrArg Units.val hu
        simp only [Φu, Units.coe_map, Units.val_one, map_one] at hv
        dsimp only [Φ] at hv
        rw [map_one]
        change (PowerSeries.map (Ideal.Quotient.mk (uniformizerIdeal K π)))
          (d 0 : PowerSeries (RingOfIntegers K)) = 1
        exact hv
    | succ r hr ih =>
        have himprove := (colemanNorm_congruences K π
          (d (r - 1) : PowerSeries (RingOfIntegers K)) (d (r - 1)).isUnit).2
          r hr ih
        have hv := congrArg Units.val (hdsucc (r - 1))
        change ((d ((r - 1) + 1) : Units (PowerSeries (RingOfIntegers K))) :
          PowerSeries (RingOfIntegers K)) =
            D.operator (d (r - 1) : PowerSeries (RingOfIntegers K)) at hv
        rw [← hv] at himprove
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
          Nat.sub_add_cancel hr] using himprove
  have hd := hdcong m hm
  let c : Units (RingOfIntegers K) :=
    Units.map PowerSeries.constantCoeff.toMonoidHom (d (m - 1))
  refine ⟨c, ?_, ?_⟩
  · change integralUnitReduction K m c = 1
    apply Units.ext
    change Ideal.Quotient.mk (LocalMaximalIdeal K ^ m) (c : RingOfIntegers K) =
      Ideal.Quotient.mk (LocalMaximalIdeal K ^ m) 1
    rw [Ideal.Quotient.eq]
    have hd0 := hd 0
    rw [hmax] at hd0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hd0
    change PowerSeries.constantCoeff
      ((d (m - 1) : Units (PowerSeries (RingOfIntegers K))) :
        PowerSeries (RingOfIntegers K)) - 1 ∈ LocalMaximalIdeal K ^ m
    exact hd0
  · apply Units.ext
    change algebraMap (RingOfIntegers K) K (c : RingOfIntegers K) =
      ((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)
    have hprevne : algebraMap (RingOfIntegers K) K
        (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1)
          (g : PowerSeries (RingOfIntegers K)))) ≠ 0 := by
      have hunit : IsUnit (PowerSeries.constantCoeff
          (colemanNormIterate K π (m - 1)
            (g : PowerSeries (RingOfIntegers K)))) := by
        rw [← PowerSeries.isUnit_iff_constantCoeff]
        rw [← hG (m - 1)]
        exact (G (m - 1)).isUnit
      intro hz
      apply hunit.ne_zero
      apply Subtype.ext
      exact hz
    let C : Units (PowerSeries (RingOfIntegers K)) →* Units (RingOfIntegers K) :=
      Units.map PowerSeries.constantCoeff.toMonoidHom
    have hcunit : c = C (G m) * (C (G (m - 1)))⁻¹ := by
      change C (d (m - 1)) = _
      change C (G ((m - 1) + 1) * (G (m - 1))⁻¹) = _
      rw [map_mul, map_inv, Nat.sub_add_cancel hm]
    let A : Units (RingOfIntegers K) →* Units K :=
      Units.map (algebraMap (RingOfIntegers K) K).toMonoidHom
    have hcfield := congrArg Units.val (congrArg A hcunit)
    simp only [A, C, Units.coe_map, map_mul, map_inv,
      Units.val_mul, Units.val_inv_eq_inv_val] at hcfield
    have hcval : algebraMap (RingOfIntegers K) K (c : RingOfIntegers K) =
        algebraMap (RingOfIntegers K) K
            (PowerSeries.constantCoeff (colemanNormIterate K π m
              (g : PowerSeries (RingOfIntegers K)))) *
          (algebraMap (RingOfIntegers K) K
            (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1)
              (g : PowerSeries (RingOfIntegers K)))))⁻¹ := by
      rw [hG m, hG (m - 1)] at hcfield
      exact hcfield
    rw [hcval, hconstant]
    let a := algebraMap (RingOfIntegers K) K
      (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1)
        (g : PowerSeries (RingOfIntegers K))))
    let p := ((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)
    change (a * p) * a⁻¹ = p
    rw [mul_comm a p, mul_assoc, mul_inv_cancel₀ hprevne, mul_one]

/--
**L05**, Lemma `lem:coleman-norm` (c): iteration, evaluation, primitive torsion product, and
field norm are the same pinned quantity, which lies in `U_K^m`.
-/
theorem colemanNorm_iteration_product
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (π : Uniformizer K) (m : ℕ) (hm : 1 ≤ m)
    (g : Units (PowerSeries (RingOfIntegers K))) :
    let level := lubinTateLevel K Ksep π m hm
    letI : FiniteDimensional K level.field := level.finiteDimensional
    letI : ValuativeRel level.field := level.localFieldData.valuativeRel
    letI : TopologicalSpace level.field := level.localFieldData.topology
    letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
    letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
    letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
    algebraMap (RingOfIntegers K) K
        (PowerSeries.constantCoeff (colemanNormIterate K π m (g :
          PowerSeries (RingOfIntegers K)))) =
      algebraMap (RingOfIntegers K) K
          (PowerSeries.constantCoeff (colemanNormIterate K π (m - 1) (g :
            PowerSeries (RingOfIntegers K)))) *
        (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)) ∧
    algebraMap (RingOfIntegers K) level.field
        (PowerSeries.constantCoeff (colemanNormIterate K π m (g :
          PowerSeries (RingOfIntegers K)))) =
      lubinTateTorsionProduct K Ksep π m hm (g : PowerSeries (RingOfIntegers K)) ∧
    algebraMap K level.field
        (((lubinTatePrimitiveProduct K Ksep π m hm g : Units K) : K)) =
      lubinTatePrimitiveTorsionProduct K Ksep π m hm
        (g : PowerSeries (RingOfIntegers K)) ∧
    (∀ β : level.field,
      ((primitiveDivisionPolynomial K π m).map
        (algebraMap (RingOfIntegers K) level.field)).IsRoot β →
          PowerSeries.HasEval β) ∧
    (∀ β : level.field,
      ((lubinTateIterate K π m).map
        (algebraMap (RingOfIntegers K) level.field)).IsRoot β →
          PowerSeries.HasEval β) ∧
    lubinTatePrimitiveProduct K Ksep π m hm g =
      normUnitsHom K level.field (Units.map level.evaluation.toMonoidHom g) ∧
    lubinTatePrimitiveProduct K Ksep π m hm g ∈ principalUnitSubgroup K m := by
  let level := lubinTateLevel K Ksep π m hm
  letI : FiniteDimensional K level.field := level.finiteDimensional
  letI : ValuativeRel level.field := level.localFieldData.valuativeRel
  letI : TopologicalSpace level.field := level.localFieldData.topology
  letI : IsNonarchimedeanLocalField level.field := level.localFieldData.localField
  letI : ValuativeExtension K level.field := level.localFieldData.valuativeExtension
  letI : ContinuousSMul K level.field := level.localFieldData.continuousSMul
  let ϖ := defaultUniformizer level.field
  let p := uniformizerInteger level.field ϖ
  have hpvalField : (p : level.field) = (ϖ.val : level.field) :=
    (uniformizer_integer_exists level.field ϖ).choose_spec
  have hp : (p : level.field) ≠ 0 := by
    rw [hpvalField]
    exact ϖ.val.ne_zero
  have hpmax : Ideal.span ({p} : Set (RingOfIntegers level.field)) =
      LocalMaximalIdeal level.field := by
    change uniformizerIdeal level.field ϖ = LocalMaximalIdeal level.field
    exact colemanNorm_maximalIdeal_eq level.field ϖ
  have hpval : normalizedValuation level.field
      (Units.mk0 (p : level.field) hp) = 1 := by
    have hunit : Units.mk0 (p : level.field) hp = ϖ.val := by
      apply Units.ext
      exact hpvalField
    rw [hunit, ϖ.valuation_eq_one]
  have hinc := test_adic_inclusion_continuous level.field p hp hpmax hpval
  have hconstant := test_constant_iteration_primitive K Ksep π m hm hinc g
  have hfull := test_iteration_torsion_product K Ksep π m hm hinc
    (g : PowerSeries (RingOfIntegers K))
  have hnorm := test_primitive_norm_product K Ksep π m hm g
  have hevals := test_torsion_roots_hasEval K Ksep π m hm hinc
  have hmem := test_primitive_product_mem_principal K Ksep π m hm g
    (colemanNorm_maximalIdeal_eq K π) hconstant
  dsimp only at hconstant hfull hnorm hevals ⊢
  refine ⟨hconstant, hfull, hnorm, hevals.1, hevals.2, ?_, hmem⟩
  rfl

end

end NU.LCFT
