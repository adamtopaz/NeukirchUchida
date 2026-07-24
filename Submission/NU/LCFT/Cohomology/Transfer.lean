import Submission.NU.LCFT.Cohomology.TateLowDegree

/-!
# Concrete transfer on normalized inhomogeneous cochains

This file constructs transfer from an explicit finite right transversal.  We use right
transversals (so every `x : G` is uniquely `s * rᵢ`) because the resulting formulas agree
term-for-term with the differentials in `Cohomology/Inhomogeneous.lean`.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory

namespace Inhomogeneous.Transfer

variable {G ι : Type} [Group G] [Fintype ι]

/-- A computable right transversal for `S`: every element of `G` is uniquely `s * rep i`. -/
structure ExplicitTransversal (S : Subgroup G) (ι : Type) where
  rep : ι → G
  decomposition : ι × S ≃ G
  decomposition_apply : ∀ i s, decomposition (i, s) = (s : G) * rep i

namespace ExplicitTransversal

variable {S : Subgroup G} (T : ExplicitTransversal S ι)

/-- The transversal coordinates of a group element. -/
def coord (x : G) : ι × S := T.decomposition.symm x

@[simp]
theorem decomposition_coord (x : G) :
    T.decomposition (T.coord x) = x :=
  T.decomposition.apply_symm_apply x

@[simp]
theorem coord_decomposition (p : ι × S) :
    T.coord (T.decomposition p) = p :=
  T.decomposition.symm_apply_apply p

@[simp]
theorem coord_smul_rep (i : ι) (s : S) :
    T.coord ((s : G) * T.rep i) = (i, s) := by
  rw [← T.decomposition_apply]
  exact T.coord_decomposition (i, s)

/-- Multiplication on the right permutes the transversal indices. -/
def next (i : ι) (g : G) : ι := (T.coord (T.rep i * g)).1

/-- The Schreier factor determined by `rep i * g = factor i g * rep (next i g)`. -/
def factor (i : ι) (g : G) : S := (T.coord (T.rep i * g)).2

/-- The defining Schreier factorization. -/
theorem factorization (i : ι) (g : G) :
    T.rep i * g = (T.factor i g : G) * T.rep (T.next i g) := by
  have h := T.decomposition_coord (T.rep i * g)
  rw [T.decomposition_apply] at h
  exact h.symm

@[simp]
theorem next_one (i : ι) : T.next i 1 = i := by
  change (T.coord (T.rep i * 1)).1 = i
  rw [mul_one]
  have h := T.coord_smul_rep i (1 : S)
  simpa using congrArg Prod.fst h

@[simp]
theorem factor_one (i : ι) : T.factor i 1 = 1 := by
  change (T.coord (T.rep i * 1)).2 = 1
  rw [mul_one]
  have h := T.coord_smul_rep i (1 : S)
  simpa using congrArg Prod.snd h

/-- The Schreier factor as the familiar twisted product of representatives. -/
theorem factor_coe (i : ι) (g : G) :
    (T.factor i g : G) = T.rep i * g * (T.rep (T.next i g))⁻¹ := by
  rw [T.factorization]
  simp [mul_assoc]

/-- Successive Schreier indices compose in the same order as multiplication in `G`. -/
theorem next_mul (i : ι) (g h : G) :
    T.next i (g * h) = T.next (T.next i g) h := by
  have hgh : T.rep i * (g * h) =
      ((T.factor i g * T.factor (T.next i g) h : S) : G) *
        T.rep (T.next (T.next i g) h) := by
    rw [← mul_assoc, T.factorization i g, mul_assoc,
      T.factorization (T.next i g) h]
    simp only [Subgroup.coe_mul, mul_assoc]
  change (T.coord (T.rep i * (g * h))).1 = T.next (T.next i g) h
  rw [hgh, T.coord_smul_rep]

/-- Successive Schreier factors satisfy the cocycle identity. -/
theorem factor_mul (i : ι) (g h : G) :
    T.factor i (g * h) = T.factor i g * T.factor (T.next i g) h := by
  have hgh : T.rep i * (g * h) =
      ((T.factor i g * T.factor (T.next i g) h : S) : G) *
        T.rep (T.next (T.next i g) h) := by
    rw [← mul_assoc, T.factorization i g, mul_assoc,
      T.factorization (T.next i g) h]
    simp only [Subgroup.coe_mul, mul_assoc]
  change (T.coord (T.rep i * (g * h))).2 =
    T.factor i g * T.factor (T.next i g) h
  rw [hgh, T.coord_smul_rep]

/-- `next (-) g` is a permutation, with inverse `next (-) g⁻¹`. -/
def nextEquiv (g : G) : ι ≃ ι where
  toFun := fun i => T.next i g
  invFun := fun i => T.next i g⁻¹
  left_inv := fun i => by
    change T.next (T.next i g) g⁻¹ = i
    rw [← T.next_mul, mul_inv_cancel, T.next_one]
  right_inv := fun i => by
    change T.next (T.next i g⁻¹) g = i
    rw [← T.next_mul, inv_mul_cancel, T.next_one]

@[simp]
theorem nextEquiv_apply (g : G) (i : ι) : T.nextEquiv g i = T.next i g := rfl

/-- The labels of an explicit transversal are canonically the right-coset quotient. -/
noncomputable def indexEquivRightCosets :
    ι ≃ Quotient (QuotientGroup.rightRel S) := by
  let f : ι → Quotient (QuotientGroup.rightRel S) :=
    fun i => Quotient.mk'' (T.rep i)
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hr : QuotientGroup.rightRel S (T.rep i) (T.rep j) :=
      Quotient.exact' hij
    have hs : T.rep j * (T.rep i)⁻¹ ∈ S :=
      QuotientGroup.rightRel_apply.mp hr
    let s : S := ⟨T.rep j * (T.rep i)⁻¹, hs⟩
    have heq : T.decomposition (j, (1 : S)) = T.decomposition (i, s) := by
      rw [T.decomposition_apply, T.decomposition_apply]
      dsimp [s]
      simp [mul_assoc]
    exact (congrArg Prod.fst (T.decomposition.injective heq)).symm
  · intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      let p := T.coord x
      refine ⟨p.1, ?_⟩
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have hx := T.decomposition_coord x
      rw [T.decomposition_apply] at hx
      rw [← hx]
      change ((p.2 : S) : G) * T.rep p.1 * (T.rep p.1)⁻¹ ∈ S
      simpa [mul_assoc] using p.2.2

/-- The number of labels is the subgroup index. -/
theorem card_index (T : ExplicitTransversal S ι) : Fintype.card ι = S.index := by
  rw [Subgroup.index_eq_card]
  calc
    Fintype.card ι = Nat.card ι := Nat.card_eq_fintype_card.symm
    _ = Nat.card (Quotient (QuotientGroup.rightRel S)) :=
      Nat.card_congr (indexEquivRightCosets T)
    _ = Nat.card (G ⧸ S) :=
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)

/-- The identity used to reindex the leading action in the transfer differential. -/
theorem action_factorization (i : ι) (g : G) :
    g * (T.rep (T.next i g))⁻¹ = (T.rep i)⁻¹ * (T.factor i g : G) := by
  calc
    g * (T.rep (T.next i g))⁻¹ =
        (T.rep i)⁻¹ * (T.rep i * g) * (T.rep (T.next i g))⁻¹ := by simp [mul_assoc]
    _ = (T.rep i)⁻¹ * ((T.factor i g : G) * T.rep (T.next i g)) *
        (T.rep (T.next i g))⁻¹ := by rw [T.factorization]
    _ = (T.rep i)⁻¹ * (T.factor i g : G) := by simp [mul_assoc]

end ExplicitTransversal

variable {S : Subgroup G} (T : ExplicitTransversal S ι)

private theorem rho_inv_rho (M : Rep ℤ G) (g : G) (x : M) :
    M.ρ g⁻¹ (M.ρ g x) = x := by
  letI : Module ℤ M := M.hV2
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem rho_action_factorization (M : Rep ℤ G) (i : ι) (g : G) (x : M) :
    M.ρ g (M.ρ (T.rep (T.next i g))⁻¹ x) =
      M.ρ (T.rep i)⁻¹ (M.ρ (T.factor i g : G) x) := by
  letI : Module ℤ M := M.hV2
  rw [← Module.End.mul_apply, ← map_mul, T.action_factorization,
    map_mul, Module.End.mul_apply]

/-- Transfer in degree zero, for a fixed explicit right transversal. -/
def corC0 (M : Rep ℤ G) : C0 (Rep.res S.subtype M) →+ C0 M where
  toFun a := ∑ i : ι, M.ρ (T.rep i)⁻¹ a
  map_zero' := by simp
  map_add' a b := by simp [map_add, Finset.sum_add_distrib]

/-- Transfer in degree one.  Here `factor i g` is the usual first Schreier argument. -/
def corC1 (M : Rep ℤ G) : C1 (Rep.res S.subtype M) →+ C1 M where
  toFun b g := ∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i g))
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [map_add, Finset.sum_add_distrib]

/-- Transfer in degree two, with the two successive Schreier factors. -/
def corC2 (M : Rep ℤ G) : C2 (Rep.res S.subtype M) →+ C2 M where
  toFun c g h := ∑ i : ι, M.ρ (T.rep i)⁻¹
    (c (T.factor i g) (T.factor (T.next i g) h))
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [map_add, Finset.sum_add_distrib]

/-- The degree-three formula, used only as the target of `d²`. -/
def corC3 (M : Rep ℤ G) : C3 (Rep.res S.subtype M) →+ C3 M where
  toFun c g h k := ∑ i : ι, M.ρ (T.rep i)⁻¹
    (c (T.factor i g) (T.factor (T.next i g) h)
      (T.factor (T.next (T.next i g) h) k))
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [map_add, Finset.sum_add_distrib]

/-- Reindexing the leading action is the computational heart of transfer. -/
private theorem rho_sum_reindex (M : Rep ℤ G) (g : G) (f : ι → M) :
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (f i)) =
      ∑ i : ι, M.ρ (T.rep i)⁻¹
        (M.ρ (T.factor i g : G) (f (T.next i g))) := by
  letI : Module ℤ M := M.hV2
  rw [map_sum]
  calc
    (∑ i : ι, M.ρ g (M.ρ (T.rep i)⁻¹ (f i))) =
        ∑ i : ι, M.ρ g
          (M.ρ (T.rep (T.next i g))⁻¹ (f (T.next i g))) := by
            symm
            simpa using Equiv.sum_comp (T.nextEquiv g)
              (fun i : ι => M.ρ g (M.ρ (T.rep i)⁻¹ (f i)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact rho_action_factorization T M i g (f (T.next i g))

/-- Concrete transfer commutes with `d⁰`. -/
theorem corC0_d0 (M : Rep ℤ G) (a : C0 (Rep.res S.subtype M)) :
    corC1 T M (d0 (Rep.res S.subtype M) a) = d0 M (corC0 T M a) := by
  letI : Module ℤ M := M.hV2
  ext g
  change (∑ i : ι, M.ρ (T.rep i)⁻¹
      (M.ρ (T.factor i g : G) a - a)) =
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ a) -
      ∑ i : ι, M.ρ (T.rep i)⁻¹ a
  simp only [map_sub, Finset.sum_sub_distrib]
  congr 1
  calc
    (∑ i : ι, M.ρ (T.rep i)⁻¹ (M.ρ (T.factor i g : G) a)) =
        ∑ i : ι, M.ρ g (M.ρ (T.rep (T.next i g))⁻¹ a) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (rho_action_factorization T M i g a).symm
    _ = ∑ i : ι, M.ρ g (M.ρ (T.rep i)⁻¹ a) := by
          simpa using Equiv.sum_comp (T.nextEquiv g)
            (fun i : ι => M.ρ g (M.ρ (T.rep i)⁻¹ a))
    _ = M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ a) := by rw [map_sum]

/-- Concrete transfer commutes with `d¹`. -/
theorem corC1_d1 (M : Rep ℤ G) (b : C1 (Rep.res S.subtype M)) :
    corC2 T M (d1 (Rep.res S.subtype M) b) = d1 M (corC1 T M b) := by
  letI : Module ℤ M := M.hV2
  ext g h
  change (∑ i : ι, M.ρ (T.rep i)⁻¹
      (M.ρ (T.factor i g : G) (b (T.factor (T.next i g) h)) -
        b (T.factor i g * T.factor (T.next i g) h) + b (T.factor i g))) =
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i h))) -
      (∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i (g * h)))) +
      ∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i g))
  rw [rho_sum_reindex T M g (fun i => b (T.factor i h))]
  simp only [map_sub, map_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [T.factor_mul]

/-- Concrete transfer commutes with `d²`. -/
theorem corC2_d2 (M : Rep ℤ G) (c : C2 (Rep.res S.subtype M)) :
    corC3 T M (d2 (Rep.res S.subtype M) c) = d2 M (corC2 T M c) := by
  letI : Module ℤ M := M.hV2
  ext g h k
  change (∑ i : ι, M.ρ (T.rep i)⁻¹
      (M.ρ (T.factor i g : G)
          (c (T.factor (T.next i g) h)
            (T.factor (T.next (T.next i g) h) k)) -
        c (T.factor i g * T.factor (T.next i g) h)
          (T.factor (T.next (T.next i g) h) k) +
        c (T.factor i g)
          (T.factor (T.next i g) h *
            T.factor (T.next (T.next i g) h) k) -
        c (T.factor i g) (T.factor (T.next i g) h))) =
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i h) (T.factor (T.next i h) k))) -
    (∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i (g * h)) (T.factor (T.next i (g * h)) k))) +
    (∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i g) (T.factor (T.next i g) (h * k)))) -
    ∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i g) (T.factor (T.next i g) h))
  rw [rho_sum_reindex T M g
    (fun i => c (T.factor i h) (T.factor (T.next i h) k))]
  simp only [map_sub, map_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [T.factor_mul, T.next_mul]

/-- Transfer sends normalized one-cocycles to normalized one-cocycles. -/
def corCocycles1 (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    cocycles1 (Rep.res S.subtype M) →+ cocycles1 M where
  toFun b := ⟨corC1 T M b, ⟨by
    change d1 M (corC1 T M b) = 0
    rw [← corC1_d1 T M]
    have hb : d1 (Rep.res S.subtype M) b = 0 := b.2.1
    rw [hb, map_zero], by
    change corC1 T M b 1 = 0
    simp only [corC1, AddMonoidHom.coe_mk, ZeroHom.coe_mk, T.factor_one]
    have hb : b.1 1 = 0 := b.2.2
    simp [hb]⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero (corC1 T M)
  map_add' a b := by apply Subtype.ext; exact map_add (corC1 T M) a.1 b.1

/-- Transfer sends normalized two-cocycles to normalized two-cocycles. -/
def corCocycles2 (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    cocycles2 (Rep.res S.subtype M) →+ cocycles2 M where
  toFun c := ⟨corC2 T M c, ⟨by
    change d2 M (corC2 T M c) = 0
    rw [← corC2_d2 T M]
    have hc : d2 (Rep.res S.subtype M) c = 0 := c.2.1
    rw [hc, map_zero], ⟨by
      intro g
      change corC2 T M c 1 g = 0
      simp only [corC2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, T.factor_one,
        T.next_one]
      have hc : ∀ h, c.1 1 h = 0 := c.2.2.1
      simp [hc], by
      intro g
      change corC2 T M c g 1 = 0
      simp only [corC2, AddMonoidHom.coe_mk, ZeroHom.coe_mk, T.factor_one]
      have hc : ∀ h, c.1 h 1 = 0 := c.2.2.2
      simp [hc]⟩⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero (corC2 T M)
  map_add' a b := by apply Subtype.ext; exact map_add (corC2 T M) a.1 b.1

/-- Degree-zero transfer on invariant elements. -/
def corH0 (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    H0 (Rep.res S.subtype M) →+ H0 M where
  toFun a := ⟨corC0 T M a.1, by
    intro g
    have ha : d0 (Rep.res S.subtype M) a.1 = 0 := by
      ext s
      change M.ρ (s : G) a.1 - a.1 = 0
      exact sub_eq_zero.mpr (a.2 s)
    have hd := corC0_d0 T M a.1
    rw [ha, map_zero] at hd
    have hg := congrFun hd g
    change 0 = M.ρ g (corC0 T M a.1) - corC0 T M a.1 at hg
    exact sub_eq_zero.mp hg.symm⟩
  map_zero' := by apply Subtype.ext; exact map_zero (corC0 T M)
  map_add' a b := by apply Subtype.ext; exact map_add (corC0 T M) a.1 b.1

/-- Degree-one transfer on the concrete quotient. -/
def corH1 (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    H1 (Rep.res S.subtype M) →+ H1 M :=
  QuotientAddGroup.map (coboundaries1 (Rep.res S.subtype M)) (coboundaries1 M)
    (corCocycles1 T M) (by
      rintro b ⟨a, ha⟩
      refine ⟨corC0 T M a, ?_⟩
      change d0 M (corC0 T M a) = (corCocycles1 T M b).1
      rw [← corC0_d0 T M, ha]
      rfl)

/-- Degree-two transfer on the concrete quotient. -/
def corH2 (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    H2 (Rep.res S.subtype M) →+ H2 M :=
  QuotientAddGroup.map (coboundaries2 (Rep.res S.subtype M)) (coboundaries2 M)
    (corCocycles2 T M) (by
      rintro c ⟨b, hb⟩
      refine ⟨corC1 T M b, ?_⟩
      change d1 M (corC1 T M b) = (corCocycles2 T M c).1
      rw [← corC1_d1 T M, hb]
      rfl)

@[simp]
theorem corH1_mk (T : ExplicitTransversal S ι) (M : Rep ℤ G)
    (b : cocycles1 (Rep.res S.subtype M)) :
    corH1 T M (QuotientAddGroup.mk' (coboundaries1 (Rep.res S.subtype M)) b) =
      QuotientAddGroup.mk' (coboundaries1 M) (corCocycles1 T M b) := rfl

@[simp]
theorem corH2_mk (T : ExplicitTransversal S ι) (M : Rep ℤ G)
    (c : cocycles2 (Rep.res S.subtype M)) :
    corH2 T M (QuotientAddGroup.mk' (coboundaries2 (Rep.res S.subtype M)) c) =
      QuotientAddGroup.mk' (coboundaries2 M) (corCocycles2 T M c) := rfl

/-- On invariant zero-cochains, transfer after restriction is multiplication by the index. -/
theorem corC0_restrict_of_invariant (M : Rep ℤ G) (a : C0 M)
    (ha : ∀ g, M.ρ g a = a) :
    corC0 T M (restrictC0 S.subtype M a) = Fintype.card ι • a := by
  change (∑ i : ι, M.ρ (T.rep i)⁻¹ a) = Fintype.card ι • a
  simp only [ha, Finset.sum_const, Finset.card_univ]

/-- The degree-zero restriction/corestriction law, stated with the actual subgroup index. -/
theorem corH0_restriction (M : Rep ℤ G) (a : H0 M) :
    corH0 T M (restrictionH0 S.subtype M a) = S.index • a := by
  apply Subtype.ext
  change corC0 T M (restrictC0 S.subtype M a.1) = S.index • a.1
  rw [← T.card_index]
  exact corC0_restrict_of_invariant T M a.1 a.2

/-- The explicit primitive measuring `cor (res b) - [G:S] b` in degree one. -/
def restrictionCorPrimitive1 (M : Rep ℤ G) (b : C1 M) : C0 M :=
  -∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.rep i))

private theorem corC1_restrict_summand (M : Rep ℤ G) (b : C1 M)
    (hb : d1 M b = 0) (i : ι) (g : G) :
    M.ρ (T.rep i)⁻¹ (b (T.factor i g : G)) =
      b g + M.ρ (T.rep i)⁻¹ (b (T.rep i)) -
        M.ρ g (M.ρ (T.rep (T.next i g))⁻¹ (b (T.rep (T.next i g)))) := by
  letI : Module ℤ M := M.hV2
  have hmul (x y : G) : b (x * y) = M.ρ x (b y) + b x := by
    have h := congrFun (congrFun hb x) y
    change M.ρ x (b y) - b (x * y) + b x = 0 at h
    apply sub_eq_zero.mp
    calc
      b (x * y) - (M.ρ x (b y) + b x) =
          -(M.ρ x (b y) - b (x * y) + b x) := by abel
      _ = 0 := by rw [h, neg_zero]
  calc
    M.ρ (T.rep i)⁻¹ (b (T.factor i g : G)) =
        M.ρ (T.rep i)⁻¹
          (b ((T.factor i g : G) * T.rep (T.next i g)) -
            M.ρ (T.factor i g : G) (b (T.rep (T.next i g)))) := by
              congr 1
              rw [hmul]
              abel
    _ = M.ρ (T.rep i)⁻¹
          (b (T.rep i * g) -
            M.ρ (T.factor i g : G) (b (T.rep (T.next i g)))) := by
              rw [T.factorization]
    _ = M.ρ (T.rep i)⁻¹
          ((M.ρ (T.rep i) (b g) + b (T.rep i)) -
            M.ρ (T.factor i g : G) (b (T.rep (T.next i g)))) := by
              rw [hmul]
    _ = b g + M.ρ (T.rep i)⁻¹ (b (T.rep i)) -
        M.ρ g (M.ρ (T.rep (T.next i g))⁻¹
          (b (T.rep (T.next i g)))) := by
            rw [map_sub, map_add, rho_inv_rho]
            rw [rho_action_factorization T M i g]

/-- In degree one, the cochain-level composite is index multiplication up to the displayed
coboundary.  Exact equality on all cochains is false; this is the standard corrected statement. -/
theorem corC1_restrict (M : Rep ℤ G) (b : C1 M) (hb : d1 M b = 0) :
    corC1 T M (restrictC1 S.subtype M b) =
      Fintype.card ι • b + d0 M (restrictionCorPrimitive1 T M b) := by
  letI : Module ℤ M := M.hV2
  ext g
  change (∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i g : G))) =
    Fintype.card ι • b g +
      (M.ρ g (-∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.rep i))) -
        (-∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.rep i))))
  rw [Finset.sum_congr rfl (fun i _ => corC1_restrict_summand T M b hb i g)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hnext :
      (∑ i : ι, M.ρ g
        (M.ρ (T.rep (T.next i g))⁻¹ (b (T.rep (T.next i g))))) =
      M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.rep i))) := by
    calc
      _ = ∑ i : ι, M.ρ g (M.ρ (T.rep i)⁻¹ (b (T.rep i))) := by
        simpa using Equiv.sum_comp (T.nextEquiv g)
          (fun i : ι => M.ρ g (M.ρ (T.rep i)⁻¹ (b (T.rep i))))
      _ = _ := by rw [map_sum]
  rw [hnext, Finset.sum_const, Finset.card_univ, map_neg]
  abel

/-- Restriction followed by concrete transfer is multiplication by `[G:S]` on `H¹`. -/
theorem corH1_restriction (M : Rep ℤ G) (x : H1 M) :
    corH1 T M (restrictionH1 S.subtype M x) = S.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    change corH1 T M (restrictionH1 S.subtype M
      (QuotientAddGroup.mk' (coboundaries1 M) b)) =
        S.index • QuotientAddGroup.mk' (coboundaries1 M) b
    rw [restrictionH1_mk, corH1_mk]
    rw [← T.card_index]
    rw [← map_nsmul (QuotientAddGroup.mk' (coboundaries1 M))
      (Fintype.card ι) b]
    apply QuotientAddGroup.eq.mpr
    change -(corCocycles1 T M (restrictCocycles1 S.subtype M b)) +
      Fintype.card ι • b ∈ coboundaries1 M
    refine ⟨-restrictionCorPrimitive1 T M b.1, ?_⟩
    change d0 M (-restrictionCorPrimitive1 T M b.1) =
      -(corC1 T M (restrictC1 S.subtype M b.1)) + Fintype.card ι • b.1
    rw [map_neg, corC1_restrict T M b.1 b.2.1]
    abel

/-- Homogeneous form of an inhomogeneous two-cochain. -/
private def homogeneous2 (M : Rep ℤ G) (c : C2 M) (x₀ x₁ x₂ : G) : M :=
  M.ρ x₀ (c (x₀⁻¹ * x₁) (x₁⁻¹ * x₂))

private theorem homogeneous2_equivariant (M : Rep ℤ G) (c : C2 M)
    (g x₀ x₁ x₂ : G) :
    M.ρ g (homogeneous2 M c x₀ x₁ x₂) =
      homogeneous2 M c (g * x₀) (g * x₁) (g * x₂) := by
  letI : Module ℤ M := M.hV2
  simp only [homogeneous2]
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2 <;> simp [mul_assoc]

private theorem homogeneous2_cocycle (M : Rep ℤ G) (c : C2 M)
    (hc : d2 M c = 0) (x₀ x₁ x₂ x₃ : G) :
    homogeneous2 M c x₁ x₂ x₃ - homogeneous2 M c x₀ x₂ x₃ +
      homogeneous2 M c x₀ x₁ x₃ - homogeneous2 M c x₀ x₁ x₂ = 0 := by
  letI : Module ℤ M := M.hV2
  have h := congrFun (congrFun (congrFun hc (x₀⁻¹ * x₁))
    (x₁⁻¹ * x₂)) (x₂⁻¹ * x₃)
  change M.ρ (x₀⁻¹ * x₁) (c (x₁⁻¹ * x₂) (x₂⁻¹ * x₃)) -
      c ((x₀⁻¹ * x₁) * (x₁⁻¹ * x₂)) (x₂⁻¹ * x₃) +
      c (x₀⁻¹ * x₁) ((x₁⁻¹ * x₂) * (x₂⁻¹ * x₃)) -
      c (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) = 0 at h
  have h' := congrArg (fun z : M => M.ρ x₀ z) h
  simp only [map_sub, map_add, map_zero] at h'
  change homogeneous2 M c x₁ x₂ x₃ - homogeneous2 M c x₀ x₂ x₃ +
      homogeneous2 M c x₀ x₁ x₃ - homogeneous2 M c x₀ x₁ x₂ = 0
  simpa [homogeneous2, ← Module.End.mul_apply, ← map_mul, mul_assoc] using h'

private theorem homogeneous2_prism (M : Rep ℤ G) (c : C2 M)
    (hc : d2 M c = 0) (o₀ o₁ o₂ n₀ n₁ n₂ : G) :
    (homogeneous2 M c o₁ n₁ n₂ - homogeneous2 M c o₁ o₂ n₂) -
        (homogeneous2 M c o₀ n₀ n₂ - homogeneous2 M c o₀ o₂ n₂) +
        (homogeneous2 M c o₀ n₀ n₁ - homogeneous2 M c o₀ o₁ n₁) =
      homogeneous2 M c n₀ n₁ n₂ - homogeneous2 M c o₀ o₁ o₂ := by
  let A := homogeneous2 M c n₀ n₁ n₂ - homogeneous2 M c o₀ n₁ n₂ +
    homogeneous2 M c o₀ n₀ n₂ - homogeneous2 M c o₀ n₀ n₁
  let B := homogeneous2 M c o₁ n₁ n₂ - homogeneous2 M c o₀ n₁ n₂ +
    homogeneous2 M c o₀ o₁ n₂ - homogeneous2 M c o₀ o₁ n₁
  let C := homogeneous2 M c o₁ o₂ n₂ - homogeneous2 M c o₀ o₂ n₂ +
    homogeneous2 M c o₀ o₁ n₂ - homogeneous2 M c o₀ o₁ o₂
  have hA : A = 0 := homogeneous2_cocycle M c hc o₀ n₀ n₁ n₂
  have hB : B = 0 := homogeneous2_cocycle M c hc o₀ o₁ n₁ n₂
  have hC : C = 0 := homogeneous2_cocycle M c hc o₀ o₁ o₂ n₂
  apply sub_eq_zero.mp
  calc
    ((homogeneous2 M c o₁ n₁ n₂ - homogeneous2 M c o₁ o₂ n₂) -
        (homogeneous2 M c o₀ n₀ n₂ - homogeneous2 M c o₀ o₂ n₂) +
        (homogeneous2 M c o₀ n₀ n₁ - homogeneous2 M c o₀ o₁ n₁)) -
        (homogeneous2 M c n₀ n₁ n₂ - homogeneous2 M c o₀ o₁ o₂) =
      -A + B - C := by dsimp [A, B, C]; abel
    _ = 0 := by rw [hA, hB, hC]; simp

private def restrictionCorPrismTerm (M : Rep ℤ G) (c : C2 M) (i : ι) (g : G) : M :=
  homogeneous2 M c 1 (T.rep i)⁻¹ (g * (T.rep (T.next i g))⁻¹) -
    homogeneous2 M c 1 g (g * (T.rep (T.next i g))⁻¹)

/-- The explicit degree-one primitive for the degree-two restriction/transfer composite. -/
def restrictionCorPrimitive2 (M : Rep ℤ G) (c : C2 M) : C1 M :=
  fun g => ∑ i : ι, restrictionCorPrismTerm T M c i g

private theorem homogeneous2_transfer_summand (M : Rep ℤ G) (c : C2 M)
    (i : ι) (g h : G) :
    homogeneous2 M c (T.rep i)⁻¹
        (g * (T.rep (T.next i g))⁻¹)
        (g * h * (T.rep (T.next (T.next i g) h))⁻¹) =
      M.ρ (T.rep i)⁻¹
        (c (T.factor i g : G) (T.factor (T.next i g) h : G)) := by
  simp only [homogeneous2]
  congr 2
  · simpa [mul_assoc] using (T.factor_coe i g).symm
  · simpa [mul_assoc] using (T.factor_coe (T.next i g) h).symm

private theorem homogeneous2_standard (M : Rep ℤ G) (c : C2 M) (g h : G) :
    homogeneous2 M c 1 g (g * h) = c g h := by
  simp [homogeneous2, mul_assoc]

private theorem rho_restrictionCorPrismTerm (M : Rep ℤ G) (c : C2 M)
    (i : ι) (g h : G) :
    M.ρ g (restrictionCorPrismTerm T M c (T.next i g) h) =
      homogeneous2 M c g
          (g * (T.rep (T.next i g))⁻¹)
          (g * h * (T.rep (T.next (T.next i g) h))⁻¹) -
        homogeneous2 M c g (g * h)
          (g * h * (T.rep (T.next (T.next i g) h))⁻¹) := by
  rw [restrictionCorPrismTerm, map_sub,
    homogeneous2_equivariant, homogeneous2_equivariant]
  congr 2 <;> simp [mul_assoc]

private theorem restrictionCorPrismTerm_d (M : Rep ℤ G) (c : C2 M)
    (hc : d2 M c = 0) (i : ι) (g h : G) :
    M.ρ g (restrictionCorPrismTerm T M c (T.next i g) h) -
        restrictionCorPrismTerm T M c i (g * h) +
        restrictionCorPrismTerm T M c i g =
      M.ρ (T.rep i)⁻¹
          (c (T.factor i g : G) (T.factor (T.next i g) h : G)) - c g h := by
  rw [rho_restrictionCorPrismTerm T M c i g h]
  simp only [restrictionCorPrismTerm, T.next_mul]
  calc
    _ = homogeneous2 M c (T.rep i)⁻¹
          (g * (T.rep (T.next i g))⁻¹)
          (g * h * (T.rep (T.next (T.next i g) h))⁻¹) -
        homogeneous2 M c 1 g (g * h) := by
      exact homogeneous2_prism M c hc 1 g (g * h)
        (T.rep i)⁻¹
        (g * (T.rep (T.next i g))⁻¹)
        (g * h * (T.rep (T.next (T.next i g) h))⁻¹)
    _ = _ := by
      rw [homogeneous2_transfer_summand T M c i g h,
        homogeneous2_standard]

private theorem d1_restrictionCorPrimitive2 (M : Rep ℤ G) (c : C2 M)
    (hc : d2 M c = 0) :
    d1 M (restrictionCorPrimitive2 T M c) =
      corC2 T M (restrictC2 S.subtype M c) - Fintype.card ι • c := by
  letI : Module ℤ M := M.hV2
  ext g h
  change M.ρ g (∑ i : ι, restrictionCorPrismTerm T M c i h) -
      (∑ i : ι, restrictionCorPrismTerm T M c i (g * h)) +
      ∑ i : ι, restrictionCorPrismTerm T M c i g =
    (∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i g : G) (T.factor (T.next i g) h : G))) -
      Fintype.card ι • c g h
  rw [map_sum]
  have hreindex :
      (∑ i : ι, M.ρ g (restrictionCorPrismTerm T M c i h)) =
        ∑ i : ι, M.ρ g
          (restrictionCorPrismTerm T M c (T.next i g) h) := by
    symm
    simpa using Equiv.sum_comp (T.nextEquiv g)
      (fun i : ι => M.ρ g (restrictionCorPrismTerm T M c i h))
  rw [hreindex, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl
    (fun i _ => restrictionCorPrismTerm_d T M c hc i g h)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]

/-- In degree two, restriction followed by transfer is index multiplication up to an explicit
prism coboundary. -/
theorem corC2_restrict (M : Rep ℤ G) (c : C2 M) (hc : d2 M c = 0) :
    corC2 T M (restrictC2 S.subtype M c) =
      Fintype.card ι • c + d1 M (restrictionCorPrimitive2 T M c) := by
  rw [d1_restrictionCorPrimitive2 T M c hc]
  abel

/-- Restriction followed by concrete transfer is multiplication by `[G:S]` on `H²`. -/
theorem corH2_restriction (M : Rep ℤ G) (x : H2 M) :
    corH2 T M (restrictionH2 S.subtype M x) = S.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    change corH2 T M (restrictionH2 S.subtype M
      (QuotientAddGroup.mk' (coboundaries2 M) c)) =
        S.index • QuotientAddGroup.mk' (coboundaries2 M) c
    rw [restrictionH2_mk, corH2_mk]
    rw [← T.card_index]
    rw [← map_nsmul (QuotientAddGroup.mk' (coboundaries2 M))
      (Fintype.card ι) c]
    apply QuotientAddGroup.eq.mpr
    change -(corCocycles2 T M (restrictCocycles2 S.subtype M c)) +
      Fintype.card ι • c ∈ coboundaries2 M
    refine ⟨-restrictionCorPrimitive2 T M c.1, ?_⟩
    change d1 M (-restrictionCorPrimitive2 T M c.1) =
      -(corC2 T M (restrictC2 S.subtype M c.1)) + Fintype.card ι • c.1
    rw [map_neg, corC2_restrict T M c.1 c.2.1]
    abel

/-- Explicit gauge data comparing two labelled right transversals.  Relabelling an arbitrary
transversal along its coset equivalence produces data of this form. -/
structure TransversalChange (T U : ExplicitTransversal S ι) where
  gauge : ι → S
  rep_eq : ∀ i, U.rep i = (gauge i : G) * T.rep i
  next_eq : ∀ i g, U.next i g = T.next i g
  factor_eq : ∀ i g,
    U.factor i g = gauge i * T.factor i g * (gauge (T.next i g))⁻¹

namespace TransversalChange

variable {T U : ExplicitTransversal S ι} (C : TransversalChange T U)

/-- The degree-zero cochain implementing independence in degree one. -/
def primitive1 (C : TransversalChange T U) (M : Rep ℤ G)
    (b : C1 (Rep.res S.subtype M)) : C0 M :=
  ∑ i : ι, M.ρ (T.rep i)⁻¹ (b (C.gauge i)⁻¹)

private theorem corC1_change_summand (M : Rep ℤ G)
    (b : cocycles1 (Rep.res S.subtype M)) (i : ι) (g : G) :
    M.ρ (U.rep i)⁻¹ (b.1 (U.factor i g)) -
        M.ρ (T.rep i)⁻¹ (b.1 (T.factor i g)) =
      M.ρ g (M.ρ (T.rep (T.next i g))⁻¹
          (b.1 (C.gauge (T.next i g))⁻¹)) -
        M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹) := by
  letI : Module ℤ M := M.hV2
  have hmul (x y : S) : b.1 (x * y) = M.ρ (x : G) (b.1 y) + b.1 x := by
    have h := congrFun (congrFun b.2.1 x) y
    change M.ρ (x : G) (b.1 y) - b.1 (x * y) + b.1 x = 0 at h
    apply sub_eq_zero.mp
    calc
      b.1 (x * y) - (M.ρ (x : G) (b.1 y) + b.1 x) =
          -(M.ρ (x : G) (b.1 y) - b.1 (x * y) + b.1 x) := by abel
      _ = 0 := by rw [h, neg_zero]
  have hinv (x : S) : M.ρ ((x : G)⁻¹) (b.1 x) = -b.1 x⁻¹ := by
    have h := hmul x⁻¹ x
    rw [show x⁻¹ * x = (1 : S) by simp, b.2.2] at h
    have h' : 0 = M.ρ ((x : G)⁻¹) (b.1 x) + b.1 x⁻¹ := by
      simpa using h
    calc
      M.ρ ((x : G)⁻¹) (b.1 x) =
          (M.ρ ((x : G)⁻¹) (b.1 x) + b.1 x⁻¹) - b.1 x⁻¹ := by simp
      _ = -b.1 x⁻¹ := by rw [← h']; simp
  have hu (z : M) : M.ρ (U.rep i)⁻¹ z =
      M.ρ (T.rep i)⁻¹ (M.ρ (C.gauge i : G)⁻¹ z) := by
    rw [C.rep_eq, mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hu, C.factor_eq]
  have hinside :
      M.ρ (C.gauge i : G)⁻¹
          (b.1 (C.gauge i * T.factor i g *
            (C.gauge (T.next i g))⁻¹)) =
        M.ρ (T.factor i g : G) (b.1 (C.gauge (T.next i g))⁻¹) +
          b.1 (T.factor i g) - b.1 (C.gauge i)⁻¹ := by
    rw [mul_assoc,
      hmul (C.gauge i) (T.factor i g * (C.gauge (T.next i g))⁻¹)]
    rw [map_add, rho_inv_rho]
    rw [hmul (T.factor i g) (C.gauge (T.next i g))⁻¹, hinv]
    abel
  rw [hinside, map_sub, map_add]
  rw [rho_action_factorization T M i g]
  abel

/-- Changing the explicit transversal changes transfer of a one-cocycle by a coboundary. -/
theorem corC1_change (M : Rep ℤ G) (b : cocycles1 (Rep.res S.subtype M)) :
    corC1 U M b.1 - corC1 T M b.1 = d0 M (primitive1 C M b.1) := by
  letI : Module ℤ M := M.hV2
  ext g
  change (∑ i : ι, M.ρ (U.rep i)⁻¹ (b.1 (U.factor i g))) -
      (∑ i : ι, M.ρ (T.rep i)⁻¹ (b.1 (T.factor i g))) =
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹)) -
      ∑ i : ι, M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹)
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => C.corC1_change_summand M b i g)]
  rw [Finset.sum_sub_distrib]
  have hreindex :
      (∑ i : ι, M.ρ g (M.ρ (T.rep (T.next i g))⁻¹
        (b.1 (C.gauge (T.next i g))⁻¹))) =
      M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹)) := by
    calc
      _ = ∑ i : ι, M.ρ g
          (M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹)) := by
        simpa using Equiv.sum_comp (T.nextEquiv g)
          (fun i : ι => M.ρ g
            (M.ρ (T.rep i)⁻¹ (b.1 (C.gauge i)⁻¹)))
      _ = _ := by rw [map_sum]
  rw [hreindex]

/-- Transfer on invariant zero-cochains is independent of the transversal. -/
theorem corH0_eq (C : TransversalChange T U) (M : Rep ℤ G) :
    corH0 U M = corH0 T M := by
  letI : Module ℤ M := M.hV2
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change (∑ i : ι, M.ρ (U.rep i)⁻¹ a.1) =
    ∑ i : ι, M.ρ (T.rep i)⁻¹ a.1
  apply Finset.sum_congr rfl
  intro i _
  rw [C.rep_eq, mul_inv_rev, map_mul, Module.End.mul_apply]
  have ha := a.2 (C.gauge i)⁻¹
  change M.ρ ((C.gauge i : G)⁻¹) a.1 = a.1 at ha
  rw [ha]

/-- Transfer on `H¹` is independent of the aligned explicit transversal. -/
theorem corH1_eq (C : TransversalChange T U) (M : Rep ℤ G) :
    corH1 U M = corH1 T M := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    change corH1 U M (QuotientAddGroup.mk'
      (coboundaries1 (Rep.res S.subtype M)) b) =
        corH1 T M (QuotientAddGroup.mk'
          (coboundaries1 (Rep.res S.subtype M)) b)
    rw [corH1_mk, corH1_mk]
    apply QuotientAddGroup.eq.mpr
    change -(corCocycles1 U M b) + corCocycles1 T M b ∈ coboundaries1 M
    refine ⟨-primitive1 C M b.1, ?_⟩
    change d0 M (-primitive1 C M b.1) =
      -(corC1 U M b.1) + corC1 T M b.1
    rw [map_neg, ← corC1_change C M b]
    abel

private def innerPrism2 (M : Rep ℤ G)
    (c : C2 (Rep.res S.subtype M)) (i : ι) (g : G) : M :=
  homogeneous2 (Rep.res S.subtype M) c 1 (C.gauge i)⁻¹
      (T.factor i g * (C.gauge (T.next i g))⁻¹) -
    homogeneous2 (Rep.res S.subtype M) c 1 (T.factor i g)
      (T.factor i g * (C.gauge (T.next i g))⁻¹)

/-- The prism homotopy proving transversal independence in degree two. -/
def primitive2 (C : TransversalChange T U) (M : Rep ℤ G)
    (c : C2 (Rep.res S.subtype M)) : C1 M :=
  fun g => ∑ i : ι, M.ρ (T.rep i)⁻¹ (innerPrism2 C M c i g)

private theorem homogeneous2_change_new (M : Rep ℤ G)
    (c : C2 (Rep.res S.subtype M)) (i : ι) (g h : G) :
    M.ρ (U.rep i)⁻¹
        (c (U.factor i g) (U.factor (U.next i g) h)) =
      M.ρ (T.rep i)⁻¹
        (homogeneous2 (Rep.res S.subtype M) c
          (C.gauge i)⁻¹
          (T.factor i g * (C.gauge (T.next i g))⁻¹)
          (T.factor i g * T.factor (T.next i g) h *
            (C.gauge (T.next (T.next i g) h))⁻¹)) := by
  letI : Module ℤ M := M.hV2
  rw [C.rep_eq, mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 1
  simp only [homogeneous2, Rep.res_obj_ρ, MonoidHom.coe_comp,
    Subgroup.coe_subtype, Function.comp_apply]
  congr 2
  · apply Subtype.ext
    simp [C.factor_eq, mul_assoc]
  · rw [C.next_eq, C.factor_eq]
    apply Subtype.ext
    simp [mul_assoc]

private theorem homogeneous2_change_old (M : Rep ℤ G)
    (c : C2 (Rep.res S.subtype M)) (i : ι) (g h : G) :
    M.ρ (T.rep i)⁻¹ (c (T.factor i g) (T.factor (T.next i g) h)) =
      M.ρ (T.rep i)⁻¹
        (homogeneous2 (Rep.res S.subtype M) c 1 (T.factor i g)
          (T.factor i g * T.factor (T.next i g) h)) := by
  congr 1
  simp [homogeneous2]

private theorem rho_innerPrism2 (M : Rep ℤ G)
    (c : C2 (Rep.res S.subtype M)) (i : ι) (g h : G) :
    M.ρ g (M.ρ (T.rep (T.next i g))⁻¹
        (innerPrism2 C M c (T.next i g) h)) =
      M.ρ (T.rep i)⁻¹
        (homogeneous2 (Rep.res S.subtype M) c (T.factor i g)
            (T.factor i g * (C.gauge (T.next i g))⁻¹)
            (T.factor i g * T.factor (T.next i g) h *
              (C.gauge (T.next (T.next i g) h))⁻¹) -
          homogeneous2 (Rep.res S.subtype M) c (T.factor i g)
            (T.factor i g * T.factor (T.next i g) h)
            (T.factor i g * T.factor (T.next i g) h *
              (C.gauge (T.next (T.next i g) h))⁻¹)) := by
  rw [rho_action_factorization T M i g]
  congr 1
  simp only [innerPrism2, map_sub]
  change (Rep.res S.subtype M).ρ (T.factor i g)
        (homogeneous2 (Rep.res S.subtype M) c 1
          (C.gauge (T.next i g))⁻¹
          (T.factor (T.next i g) h *
            (C.gauge (T.next (T.next i g) h))⁻¹)) -
      (Rep.res S.subtype M).ρ (T.factor i g)
        (homogeneous2 (Rep.res S.subtype M) c 1
          (T.factor (T.next i g) h)
          (T.factor (T.next i g) h *
            (C.gauge (T.next (T.next i g) h))⁻¹)) = _
  rw [homogeneous2_equivariant, homogeneous2_equivariant]
  congr 2 <;> simp [mul_assoc]

private theorem corC2_change_local (M : Rep ℤ G)
    (c : cocycles2 (Rep.res S.subtype M)) (i : ι) (g h : G) :
    M.ρ g (M.ρ (T.rep (T.next i g))⁻¹
        (innerPrism2 C M c.1 (T.next i g) h)) -
        M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i (g * h)) +
        M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i g) =
      M.ρ (U.rep i)⁻¹
          (c.1 (U.factor i g) (U.factor (U.next i g) h)) -
        M.ρ (T.rep i)⁻¹
          (c.1 (T.factor i g) (T.factor (T.next i g) h)) := by
  rw [rho_innerPrism2 C M c.1 i g h]
  rw [homogeneous2_change_new C M c.1 i g h,
    homogeneous2_change_old (T := T) M c.1 i g h]
  have hp := homogeneous2_prism (Rep.res S.subtype M) c.1 c.2.1
    (1 : S) (T.factor i g)
    (T.factor i g * T.factor (T.next i g) h)
    (C.gauge i)⁻¹
    (T.factor i g * (C.gauge (T.next i g))⁻¹)
    (T.factor i g * T.factor (T.next i g) h *
      (C.gauge (T.next (T.next i g) h))⁻¹)
  have hp' := congrArg (fun z : M => M.ρ (T.rep i)⁻¹ z) hp
  simp only [innerPrism2, T.factor_mul, T.next_mul] at hp' ⊢
  simp only [map_sub, map_add] at hp' ⊢
  exact hp'

/-- Changing the explicit transversal changes transfer of a two-cocycle by the displayed prism
coboundary. -/
theorem corC2_change (M : Rep ℤ G) (c : cocycles2 (Rep.res S.subtype M)) :
    corC2 U M c.1 - corC2 T M c.1 = d1 M (primitive2 C M c.1) := by
  letI : Module ℤ M := M.hV2
  ext g h
  change (∑ i : ι, M.ρ (U.rep i)⁻¹
      (c.1 (U.factor i g) (U.factor (U.next i g) h))) -
      (∑ i : ι, M.ρ (T.rep i)⁻¹
        (c.1 (T.factor i g) (T.factor (T.next i g) h))) =
    M.ρ g (∑ i : ι, M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i h)) -
      (∑ i : ι, M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i (g * h))) +
      ∑ i : ι, M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i g)
  rw [map_sum]
  have hreindex :
      (∑ i : ι, M.ρ g
        (M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i h))) =
      ∑ i : ι, M.ρ g
        (M.ρ (T.rep (T.next i g))⁻¹
          (innerPrism2 C M c.1 (T.next i g) h)) := by
    symm
    simpa using Equiv.sum_comp (T.nextEquiv g)
      (fun i : ι => M.ρ g
        (M.ρ (T.rep i)⁻¹ (innerPrism2 C M c.1 i h)))
  rw [hreindex]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (corC2_change_local C M c i g h).symm

/-- Transfer on `H²` is independent of the aligned explicit transversal. -/
theorem corH2_eq (C : TransversalChange T U) (M : Rep ℤ G) :
    corH2 U M = corH2 T M := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    change corH2 U M (QuotientAddGroup.mk'
      (coboundaries2 (Rep.res S.subtype M)) c) =
        corH2 T M (QuotientAddGroup.mk'
          (coboundaries2 (Rep.res S.subtype M)) c)
    rw [corH2_mk, corH2_mk]
    apply QuotientAddGroup.eq.mpr
    change -(corCocycles2 U M c) + corCocycles2 T M c ∈ coboundaries2 M
    refine ⟨-primitive2 C M c.1, ?_⟩
    change d1 M (-primitive2 C M c.1) =
      -(corC2 U M c.1) + corC2 T M c.1
    rw [map_neg, ← corC2_change C M c]
    abel

end TransversalChange

/-- Pointwise coefficient map on zero-cochains. -/
def mapC0 {M N : Rep ℤ G} (φ : M ⟶ N) : C0 M →+ C0 N :=
  φ.hom.toAddMonoidHom

/-- Pointwise coefficient map on one-cochains. -/
def mapC1 {M N : Rep ℤ G} (φ : M ⟶ N) : C1 M →+ C1 N where
  toFun b g := φ.hom (b g)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- Pointwise coefficient map on two-cochains. -/
def mapC2 {M N : Rep ℤ G} (φ : M ⟶ N) : C2 M →+ C2 N where
  toFun c g h := φ.hom (c g h)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- Transfer is natural in coefficients in degree zero. -/
theorem corC0_naturality {M N : Rep ℤ G} (φ : M ⟶ N)
    (a : C0 (Rep.res S.subtype M)) :
    mapC0 φ (corC0 T M a) =
      corC0 T N (mapC0 ((Rep.resFunctor S.subtype).map φ) a) := by
  change φ.hom (∑ i : ι, M.ρ (T.rep i)⁻¹ a) =
    ∑ i : ι, N.ρ (T.rep i)⁻¹ (φ.hom a)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Rep.hom_comm_apply φ (T.rep i)⁻¹ a

/-- Transfer is natural in coefficients in degree one. -/
theorem corC1_naturality {M N : Rep ℤ G} (φ : M ⟶ N)
    (b : C1 (Rep.res S.subtype M)) :
    mapC1 φ (corC1 T M b) =
      corC1 T N (mapC1 ((Rep.resFunctor S.subtype).map φ) b) := by
  ext g
  change φ.hom (∑ i : ι, M.ρ (T.rep i)⁻¹ (b (T.factor i g))) =
    ∑ i : ι, N.ρ (T.rep i)⁻¹ (φ.hom (b (T.factor i g)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Rep.hom_comm_apply φ (T.rep i)⁻¹ _

/-- Transfer is natural in coefficients in degree two. -/
theorem corC2_naturality {M N : Rep ℤ G} (φ : M ⟶ N)
    (c : C2 (Rep.res S.subtype M)) :
    mapC2 φ (corC2 T M c) =
      corC2 T N (mapC2 ((Rep.resFunctor S.subtype).map φ) c) := by
  ext g h
  change φ.hom (∑ i : ι, M.ρ (T.rep i)⁻¹
      (c (T.factor i g) (T.factor (T.next i g) h))) =
    ∑ i : ι, N.ρ (T.rep i)⁻¹
      (φ.hom (c (T.factor i g) (T.factor (T.next i g) h)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Rep.hom_comm_apply φ (T.rep i)⁻¹ _

/-- A completely concrete zig-zag representative for the `H¹ → H²` connecting map. -/
structure ConnectingZigZag {K : Type} [Group K]
    (X : ShortComplex (Rep ℤ K)) where
  cocycle : C1 X.X₃
  cocycle_mem : cocycle ∈ cocycles1 X.X₃
  lift : C1 X.X₂
  lift_spec : mapC1 X.g lift = cocycle
  preimage : C2 X.X₁
  preimage_mem : preimage ∈ cocycles2 X.X₁
  preimage_spec : mapC2 X.f preimage = d1 X.X₂ lift

/-- The same concrete zig-zag after literal restriction of all three representations. -/
structure RestrictedConnectingZigZag (S : Subgroup G)
    (X : ShortComplex (Rep ℤ G)) where
  cocycle : C1 (Rep.res S.subtype X.X₃)
  cocycle_mem : cocycle ∈ cocycles1 (Rep.res S.subtype X.X₃)
  lift : C1 (Rep.res S.subtype X.X₂)
  lift_spec : mapC1 ((Rep.resFunctor S.subtype).map X.g) lift = cocycle
  preimage : C2 (Rep.res S.subtype X.X₁)
  preimage_mem : preimage ∈ cocycles2 (Rep.res S.subtype X.X₁)
  preimage_spec : mapC2 ((Rep.resFunctor S.subtype).map X.f) preimage =
    d1 (Rep.res S.subtype X.X₂) lift

namespace ConnectingZigZag

variable {X : ShortComplex (Rep ℤ G)}

/-- The cohomology class represented by the end of a concrete connecting zig-zag. -/
def connectingClass (Z : ConnectingZigZag X) : H2 X.X₁ :=
  QuotientAddGroup.mk' (coboundaries2 X.X₁) ⟨Z.preimage, Z.preimage_mem⟩

/-- The class at the end of a restricted concrete zig-zag. -/
def restrictedConnectingClass (Z : RestrictedConnectingZigZag S X) :
    H2 (Rep.res S.subtype X.X₁) :=
  QuotientAddGroup.mk' (coboundaries2 (Rep.res S.subtype X.X₁))
    ⟨Z.preimage, Z.preimage_mem⟩

/-- Transfer every cochain in a restricted connecting zig-zag.  Naturality in coefficients and
commutation with `d¹` make the result a zig-zag for the original sequence. -/
def transfer (X : ShortComplex (Rep ℤ G))
    (Z : RestrictedConnectingZigZag S X) : ConnectingZigZag X where
  cocycle := corC1 T X.X₃ Z.cocycle
  cocycle_mem := (corCocycles1 T X.X₃ ⟨Z.cocycle, Z.cocycle_mem⟩).2
  lift := corC1 T X.X₂ Z.lift
  lift_spec := by
    rw [corC1_naturality T X.g Z.lift, Z.lift_spec]
  preimage := corC2 T X.X₁ Z.preimage
  preimage_mem := (corCocycles2 T X.X₁ ⟨Z.preimage, Z.preimage_mem⟩).2
  preimage_spec := by
    rw [corC2_naturality T X.f Z.preimage, Z.preimage_spec,
      corC1_d1 T X.X₂ Z.lift]

/-- Concrete connecting classes commute with transfer.  This is a literal zig-zag computation,
with no appeal to the categorical Tate connecting morphism. -/
theorem transfer_connectingClass (X : ShortComplex (Rep ℤ G))
    (Z : RestrictedConnectingZigZag S X) :
    connectingClass (transfer T X Z) =
      corH2 T X.X₁ (restrictedConnectingClass Z) := by
  rfl

end ConnectingZigZag

end Inhomogeneous.Transfer

namespace TateTransfer

open Inhomogeneous Inhomogeneous.Transfer

variable {G ι : Type} [Group G] [Fintype G] [Fintype ι]
variable {S : Subgroup G} [Fintype S]

/-- Sum over the chosen right-transversal representatives. -/
def cosetSum (T : ExplicitTransversal S ι) (M : Rep ℤ G) : M →+ M where
  toFun a := ∑ i : ι, M.ρ (T.rep i) a
  map_zero' := by simp
  map_add' a b := by simp [map_add, Finset.sum_add_distrib]

/-- Decompose the full norm as the subgroup norm of a transversal sum. -/
theorem norm_eq_subgroupNorm_cosetSum (T : ExplicitTransversal S ι)
    (M : Rep ℤ G) (a : M) :
    M.norm.hom a = (Rep.res S.subtype M).norm.hom (cosetSum T M a) := by
  letI : Module ℤ M := M.hV2
  rw [Rep.norm_apply, Rep.norm_apply, Representation.norm, Representation.norm]
  simp only [LinearMap.sum_apply, cosetSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_sum]
  calc
    (∑ g : G, M.ρ g a) = ∑ p : ι × S, M.ρ (T.decomposition p) a := by
      symm
      simpa using Equiv.sum_comp T.decomposition (fun g : G => M.ρ g a)
    _ = ∑ i : ι, ∑ s : S, M.ρ ((s : G) * T.rep i) a := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      rw [T.decomposition_apply]
    _ = ∑ s : S, ∑ i : ι, M.ρ (s : G) (M.ρ (T.rep i) a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = _ := by
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [Finset.sum_comm]
      rfl

/-- The full norm is also transfer of the subgroup norm; this is the norm compatibility needed
for Tate corestriction. -/
theorem norm_eq_cor_subgroupNorm (T : ExplicitTransversal S ι)
    (M : Rep ℤ G) (a : M) :
    M.norm.hom a = corC0 T M ((Rep.res S.subtype M).norm.hom a) := by
  letI : Module ℤ M := M.hV2
  rw [Rep.norm_apply, Rep.norm_apply, Representation.norm, Representation.norm]
  simp only [LinearMap.sum_apply, corC0, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_sum]
  let e : ι × S ≃ G := T.decomposition.trans (Equiv.inv G)
  calc
    (∑ g : G, M.ρ g a) = ∑ p : ι × S, M.ρ (e p) a := by
      symm
      simpa using Equiv.sum_comp e (fun g : G => M.ρ g a)
    _ = ∑ i : ι, ∑ s : S, M.ρ ((T.rep i)⁻¹ * (s : G)⁻¹) a := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      simp only [e, Equiv.trans_apply, Equiv.inv_apply, T.decomposition_apply,
        mul_inv_rev]
    _ = ∑ i : ι, ∑ s : S, M.ρ ((T.rep i)⁻¹ * (s : G)) a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Equiv.sum_comp (Equiv.inv S)
        (fun s : S => M.ρ ((T.rep i)⁻¹ * (s : G)) a)]
      rfl
    _ = ∑ i : ι, M.ρ (T.rep i)⁻¹ (∑ s : S, M.ρ (s : G) a) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = _ := by
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      rfl

/-- Literal restriction of invariant elements. -/
def restrictInvariants (M : Rep ℤ G) :
    Inhomogeneous.invariants0 M →+ Inhomogeneous.invariants0 (Rep.res S.subtype M) where
  toFun x := ⟨x.1, fun s => x.2 (s : G)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction on the concrete Tate group `H⁰ = Aᴳ/N_G A`. -/
def restrictionH0Tate (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.H0 M →+ TateLowDegree.H0 (Rep.res S.subtype M) :=
  QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M)
    (TateLowDegree.normRangeInInvariants (Rep.res S.subtype M))
    (restrictInvariants M) (by
      rintro x ⟨a, ha⟩
      change M.norm.hom a = x.1 at ha
      refine ⟨cosetSum T M a, ?_⟩
      change (Rep.res S.subtype M).norm.hom (cosetSum T M a) = x.1
      rw [← norm_eq_subgroupNorm_cosetSum T M a, ha])

/-- Corestriction on concrete Tate `H⁰`, induced by the same degree-zero transfer sum. -/
def corestrictionH0Tate (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.H0 (Rep.res S.subtype M) →+ TateLowDegree.H0 M :=
  QuotientAddGroup.map
    (TateLowDegree.normRangeInInvariants (Rep.res S.subtype M))
    (TateLowDegree.normRangeInInvariants M)
    (Inhomogeneous.Transfer.corH0 T M) (by
      rintro x ⟨a, ha⟩
      change (Rep.res S.subtype M).norm.hom a = x.1 at ha
      refine ⟨a, ?_⟩
      change M.norm.hom a = corC0 T M x.1
      rw [norm_eq_cor_subgroupNorm T M a, ha])

/-- The Tate-degree-zero restriction/corestriction composite is multiplication by the subgroup
index. -/
theorem corestrictionH0Tate_restrictionH0Tate
    (T : ExplicitTransversal S ι) (M : Rep ℤ G) (x : TateLowDegree.H0 M) :
    corestrictionH0Tate T M (restrictionH0Tate T M x) = S.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change QuotientAddGroup.mk' (TateLowDegree.normRangeInInvariants M)
        (Inhomogeneous.Transfer.corH0 T M (restrictInvariants M a)) =
      S.index • QuotientAddGroup.mk'
        (TateLowDegree.normRangeInInvariants M) a
    rw [← map_nsmul (QuotientAddGroup.mk'
      (TateLowDegree.normRangeInInvariants M)) S.index a]
    congr 1
    exact Inhomogeneous.Transfer.corH0_restriction T M a

private theorem subgroupAugmentation_le (M : Rep ℤ G) :
    TateLowDegree.augmentation (Rep.res S.subtype M) ≤ TateLowDegree.augmentation M := by
  intro x hx
  refine AddSubgroup.closure_induction (p := fun x _ => x ∈ TateLowDegree.augmentation M)
    ?_ (TateLowDegree.augmentation M).zero_mem
    (fun _ _ _ _ => (TateLowDegree.augmentation M).add_mem)
    (fun _ _ => (TateLowDegree.augmentation M).neg_mem) hx
  rintro x ⟨s, a, rfl⟩
  apply AddSubgroup.subset_closure
  exact ⟨(s : G), a, rfl⟩

/-- The identity coefficient map gives Tate corestriction in degree `-1`. -/
def corestrictNormKernel (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.normKernel (Rep.res S.subtype M) →+
      TateLowDegree.normKernel M where
  toFun x := ⟨x.1, by
    change M.norm.hom x.1 = 0
    have hx : (Rep.res S.subtype M).norm.hom x.1 = 0 := x.2
    rw [norm_eq_cor_subgroupNorm T M x.1, hx, map_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Corestriction on `H⁻¹ = ker N/I A` is induced by the identity on coefficients. -/
def corestrictionHMinusOne (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.HMinusOne (Rep.res S.subtype M) →+
      TateLowDegree.HMinusOne M :=
  QuotientAddGroup.map
    (TateLowDegree.augmentationInNormKernel (Rep.res S.subtype M))
    (TateLowDegree.augmentationInNormKernel M)
    (corestrictNormKernel T M) (by
      intro x hx
      exact subgroupAugmentation_le M hx)

/-- The transversal sum sends the full norm kernel into the subgroup norm kernel. -/
def restrictNormKernel (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.normKernel M →+
      TateLowDegree.normKernel (Rep.res S.subtype M) where
  toFun x := ⟨cosetSum T M x.1, by
    change (Rep.res S.subtype M).norm.hom (cosetSum T M x.1) = 0
    have hx : M.norm.hom x.1 = 0 := x.2
    rw [← norm_eq_subgroupNorm_cosetSum T M x.1, hx]⟩
  map_zero' := by apply Subtype.ext; exact map_zero (cosetSum T M)
  map_add' x y := by apply Subtype.ext; exact map_add (cosetSum T M) x.1 y.1

private theorem cosetSum_generator_mem_augmentation
    (T : ExplicitTransversal S ι) (M : Rep ℤ G) (g : G) (a : M) :
    cosetSum T M (M.ρ g a - a) ∈
      TateLowDegree.augmentation (Rep.res S.subtype M) := by
  letI : Module ℤ M := M.hV2
  have hreindex :
      (∑ i : ι, M.ρ (T.rep (T.next i g)) a) =
        ∑ i : ι, M.ρ (T.rep i) a := by
    simpa using Equiv.sum_comp (T.nextEquiv g)
      (fun i : ι => M.ρ (T.rep i) a)
  have heq : cosetSum T M (M.ρ g a - a) =
      ∑ i : ι, ((Rep.res S.subtype M).ρ (T.factor i g)
        (M.ρ (T.rep (T.next i g)) a) - M.ρ (T.rep (T.next i g)) a) := by
    change (∑ i : ι, M.ρ (T.rep i) (M.ρ g a - a)) = _
    simp only [map_sub]
    rw [Finset.sum_sub_distrib]
    calc
      (∑ i : ι, M.ρ (T.rep i) (M.ρ g a)) -
          ∑ i : ι, M.ρ (T.rep i) a =
        (∑ i : ι, (Rep.res S.subtype M).ρ (T.factor i g)
          (M.ρ (T.rep (T.next i g)) a)) -
          ∑ i : ι, M.ρ (T.rep i) a := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            change M.ρ (T.rep i) (M.ρ g a) =
              M.ρ (T.factor i g : G) (M.ρ (T.rep (T.next i g)) a)
            rw [← Module.End.mul_apply, ← map_mul,
              ← Module.End.mul_apply, ← map_mul, T.factorization]
      _ = (∑ i : ι, (Rep.res S.subtype M).ρ (T.factor i g)
          (M.ρ (T.rep (T.next i g)) a)) -
          ∑ i : ι, M.ρ (T.rep (T.next i g)) a := by rw [hreindex]
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [heq]
  apply AddSubgroup.sum_mem
  intro i _
  apply AddSubgroup.subset_closure
  exact ⟨T.factor i g, M.ρ (T.rep (T.next i g)) a, rfl⟩

private theorem cosetSum_augmentation
    (T : ExplicitTransversal S ι) (M : Rep ℤ G) {x : M}
    (hx : x ∈ TateLowDegree.augmentation M) :
    cosetSum T M x ∈ TateLowDegree.augmentation (Rep.res S.subtype M) := by
  refine AddSubgroup.closure_induction
    (p := fun x _ => cosetSum T M x ∈
      TateLowDegree.augmentation (Rep.res S.subtype M))
    ?_ (by rw [map_zero]; exact AddSubgroup.zero_mem _)
    (fun x y _ _ hx hy => by rw [map_add]; exact AddSubgroup.add_mem _ hx hy)
    (fun x _ hx => by rw [map_neg]; exact AddSubgroup.neg_mem _ hx) hx
  rintro x ⟨g, a, rfl⟩
  exact cosetSum_generator_mem_augmentation T M g a

/-- Restriction on concrete Tate degree `-1`, induced by the transversal sum. -/
def restrictionHMinusOne (T : ExplicitTransversal S ι) (M : Rep ℤ G) :
    TateLowDegree.HMinusOne M →+
      TateLowDegree.HMinusOne (Rep.res S.subtype M) :=
  QuotientAddGroup.map
    (TateLowDegree.augmentationInNormKernel M)
    (TateLowDegree.augmentationInNormKernel (Rep.res S.subtype M))
    (restrictNormKernel T M) (by
      intro x hx
      exact cosetSum_augmentation T M hx)

private theorem cosetSum_sub_index_mem_augmentation
    (T : ExplicitTransversal S ι) (M : Rep ℤ G) (x : M) :
    cosetSum T M x - Fintype.card ι • x ∈ TateLowDegree.augmentation M := by
  have heq : cosetSum T M x - Fintype.card ι • x =
      ∑ i : ι, (M.ρ (T.rep i) x - x) := by
    change (∑ i : ι, M.ρ (T.rep i) x) - Fintype.card ι • x = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [heq]
  apply AddSubgroup.sum_mem
  intro i _
  apply AddSubgroup.subset_closure
  exact ⟨T.rep i, x, rfl⟩

/-- The degree-minus-one restriction/corestriction composite is multiplication by `[G:S]`. -/
theorem corestrictionHMinusOne_restrictionHMinusOne
    (T : ExplicitTransversal S ι) (M : Rep ℤ G)
    (x : TateLowDegree.HMinusOne M) :
    corestrictionHMinusOne T M (restrictionHMinusOne T M x) = S.index • x := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change QuotientAddGroup.mk'
        (TateLowDegree.augmentationInNormKernel M)
          (corestrictNormKernel T M (restrictNormKernel T M a)) =
      S.index • QuotientAddGroup.mk'
        (TateLowDegree.augmentationInNormKernel M) a
    rw [← T.card_index]
    rw [← map_nsmul (QuotientAddGroup.mk'
      (TateLowDegree.augmentationInNormKernel M)) (Fintype.card ι) a]
    apply QuotientAddGroup.eq.mpr
    change -(corestrictNormKernel T M (restrictNormKernel T M a)) +
      Fintype.card ι • a ∈ TateLowDegree.augmentationInNormKernel M
    change -(cosetSum T M a.1) + Fintype.card ι • a.1 ∈
      TateLowDegree.augmentation M
    have h := cosetSum_sub_index_mem_augmentation T M a.1
    convert (TateLowDegree.augmentation M).neg_mem h using 1 <;> abel

end TateTransfer

end

end NU.LCFT
