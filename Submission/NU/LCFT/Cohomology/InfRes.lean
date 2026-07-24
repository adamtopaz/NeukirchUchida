import Submission.NU.LCFT.Cohomology.Transfer

/-!
# Degree-two inflation--restriction on normalized inhomogeneous cochains

This file develops the low-degree Hochschild--Serre edge sequence directly on the
normalized complex from `Cohomology/Inhomogeneous.lean`.  A relative one-cochain is a
one-cochain whose coboundary vanishes whenever one argument belongs to the normal
subgroup.  Its coboundary therefore descends to the quotient with values in the
subgroup invariants.  This is the concrete transgression construction.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory

namespace Inhomogeneous
namespace InfRes

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (M : Rep ℤ G)

private theorem d1_d0 (a : C0 M) : d1 M (d0 M a) = 0 := by
  ext g h
  letI : Module ℤ M := M.hV2
  simp only [d1, d0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
  rw [map_sub, ← Module.End.mul_apply, ← map_mul]
  abel

private theorem d2_d1 (b : C1 M) : d2 M (d1 M b) = 0 := by
  ext g h t
  letI : Module ℤ M := M.hV2
  simp only [d2, d1, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
    map_add, map_sub]
  rw [← Module.End.mul_apply, ← map_mul]
  simp only [mul_assoc]
  abel

/-- One-cochains whose coboundary vanishes as soon as one argument lies in `N`. -/
def relativeC1 : AddSubgroup (C1 M) where
  carrier := {b | (∀ (n : N) (g : G), d1 M b n g = 0) ∧
    (∀ (g : G) (n : N), d1 M b g n = 0)}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
    constructor
    · intro n g
      simpa using congrArg₂ (· + ·) (ha₁ n g) (hb₁ n g)
    · intro g n
      simpa using congrArg₂ (· + ·) (ha₂ g n) (hb₂ g n)
  neg_mem' := by
    rintro b ⟨hb₁, hb₂⟩
    constructor
    · intro n g
      simpa using congrArg Neg.neg (hb₁ n g)
    · intro g n
      simpa using congrArg Neg.neg (hb₂ g n)

private theorem relative_d1_left (b : relativeC1 N M) (n : N) (g : G) :
    d1 M b n g = 0 := b.2.1 n g

private theorem relative_d1_right (b : relativeC1 N M) (g : G) (n : N) :
    d1 M b g n = 0 := b.2.2 g n

private theorem relative_apply_one (b : relativeC1 N M) : b.1 1 = 0 := by
  have h := relative_d1_left N M b (1 : N) 1
  simpa [d1] using h

/-- Restriction of a relative cochain is a normalized `N`-cocycle. -/
def relativeRestrictionCocycle (b : relativeC1 N M) :
    cocycles1 (Rep.res N.subtype M) := ⟨restrictC1 N.subtype M b, ⟨by
  change d1 (Rep.res N.subtype M) (restrictC1 N.subtype M b) = 0
  rw [← restrictC1_d1]
  ext n h
  exact relative_d1_left N M b n h, by
  change b.1 (N.subtype 1) = 0
  simpa using relative_apply_one N M b⟩⟩

/-- The class on `N` represented by the restriction of a relative cochain. -/
def relativeClass : relativeC1 N M →+ H1 (Rep.res N.subtype M) :=
  (QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))).comp
    { toFun := relativeRestrictionCocycle N M
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Concrete `H¹(N,M)^{G/N}`: the stable classes admitting a relative cochain lift.

The theorem `mem_quotientInvariantH1_iff_fixed` below identifies this subgroup with the
usual fixed subgroup for the conjugation action of `G/N` on `H¹(N,M)`.
-/
def quotientInvariantH1 : AddSubgroup (H1 (Rep.res N.subtype M)) :=
  (relativeClass N M).range

private abbrev Q := G ⧸ N
private abbrev MQ := M.quotientToInvariants N

private theorem d1_right_mul (b : relativeC1 N M) (g h : G) (n : N) :
    d1 M b g (h * n) = d1 M b g h := by
  have hd := congrFun (congrFun (congrFun (d2_d1 M b.1) g) h) (n : G)
  change M.ρ g (d1 M b h n) - d1 M b (g * h) n +
    d1 M b g (h * n) - d1 M b g h = 0 at hd
  rw [relative_d1_right N M b h n, relative_d1_right N M b (g * h) n,
    map_zero] at hd
  have hd' : d1 M b g (h * n) - d1 M b g h = 0 := by
    simpa only [zero_sub, neg_zero, zero_add] using hd
  exact sub_eq_zero.mp hd'

private theorem d1_left_mul (b : relativeC1 N M) (g h : G) (n : N) :
    d1 M b (g * n) h = d1 M b g h := by
  have hd := congrFun (congrFun (congrFun (d2_d1 M b.1) g) (n : G)) h
  change M.ρ g (d1 M b n h) - d1 M b (g * n) h +
    d1 M b g (n * h) - d1 M b g n = 0 at hd
  rw [relative_d1_left N M b n h, relative_d1_right N M b g n, map_zero,
    zero_sub, sub_zero] at hd
  have hn' : h⁻¹ * (n : G) * h ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 h
  let n' : N := ⟨h⁻¹ * (n : G) * h, hn'⟩
  have hnh : (n : G) * h = h * (n' : G) := by
    dsimp [n']
    simp [mul_assoc]
  rw [hnh, d1_right_mul N M b g h n', neg_add_eq_sub] at hd
  exact (sub_eq_zero.mp hd).symm

private theorem d1_invariant (b : relativeC1 N M) (n : N) (g h : G) :
    M.ρ n (d1 M b g h) = d1 M b g h := by
  have hd := congrFun (congrFun (congrFun (d2_d1 M b.1) (n : G)) g) h
  change M.ρ n (d1 M b g h) - d1 M b (n * g) h +
    d1 M b n (g * h) - d1 M b n g = 0 at hd
  rw [relative_d1_left N M b n (g * h), relative_d1_left N M b n g,
    sub_zero, add_zero] at hd
  have hn' : g⁻¹ * (n : G) * g ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 g
  let n' : N := ⟨g⁻¹ * (n : G) * g, hn'⟩
  have hng : (n : G) * g = g * (n' : G) := by
    dsimp [n']
    simp [mul_assoc]
  rw [hng, d1_left_mul N M b g h n'] at hd
  exact sub_eq_zero.mp hd

/-- The coboundary of a relative cochain, descended literally to quotient arguments and
with its values bundled in `M^N`. -/
def descendedD1 (b : relativeC1 N M) : C2 (MQ N M) :=
  fun q r => Quotient.liftOn' q (fun g =>
    Quotient.liftOn' r (fun h =>
      (⟨d1 M b g h, fun n => d1_invariant N M b n g h⟩ : MQ N M)) (by
        intro h h' hh
        apply Subtype.ext
        change d1 M b g h = d1 M b g h'
        rw [QuotientGroup.leftRel_apply] at hh
        let n : N := ⟨h⁻¹ * h', hh⟩
        have heq : h' = h * (n : G) := by simp [n]
        rw [heq, d1_right_mul N M b g h n])) (by
      intro g g' hgg'
      induction r using QuotientGroup.induction_on with
      | _ h =>
        apply Subtype.ext
        change d1 M b g h = d1 M b g' h
        rw [QuotientGroup.leftRel_apply] at hgg'
        let n : N := ⟨g⁻¹ * g', hgg'⟩
        have heq : g' = g * (n : G) := by simp [n]
        rw [heq, d1_left_mul N M b g h n])

@[simp]
theorem descendedD1_mk (b : relativeC1 N M) (g h : G) :
    descendedD1 N M b (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) =
      (⟨d1 M b g h, fun n => d1_invariant N M b n g h⟩ : MQ N M) := rfl

private theorem descendedD1_normalized (b : relativeC1 N M) :
    descendedD1 N M b ∈ normalized2 (MQ N M) := by
  constructor
  · intro q
    induction q using QuotientGroup.induction_on with
    | _ g =>
      apply Subtype.ext
      exact relative_d1_left N M b (1 : N) g
  · intro q
    induction q using QuotientGroup.induction_on with
    | _ g =>
      apply Subtype.ext
      exact relative_d1_right N M b g (1 : N)

private theorem descendedD1_cocycle (b : relativeC1 N M) :
    d2 (MQ N M) (descendedD1 N M b) = 0 := by
  ext q r s
  induction q using QuotientGroup.induction_on with
  | _ g =>
    induction r using QuotientGroup.induction_on with
    | _ h =>
      induction s using QuotientGroup.induction_on with
      | _ t =>
        change d2 M (d1 M b.1) g h t = 0
        exact congrFun (congrFun (congrFun (d2_d1 M b.1) g) h) t

/-- The normalized quotient cocycle defining transgression for a relative cochain. -/
def transgressionCocycle (b : relativeC1 N M) : cocycles2 (MQ N M) :=
  ⟨descendedD1 N M b, descendedD1_cocycle N M b, descendedD1_normalized N M b⟩

/-- Transgression before quotienting by the ambiguity in the relative lift. -/
def relativeTransgression : relativeC1 N M →+ H2 (MQ N M) :=
  (QuotientAddGroup.mk' (coboundaries2 (MQ N M))).comp
    { toFun := transgressionCocycle N M
      map_zero' := by
        apply Subtype.ext
        funext q r
        induction q using QuotientGroup.induction_on with
        | _ g =>
          induction r using QuotientGroup.induction_on with
          | _ h =>
            apply Subtype.ext
            exact congrFun (congrFun (d1 M).map_zero g) h
      map_add' := by
        intro a b
        apply Subtype.ext
        funext q r
        induction q using QuotientGroup.induction_on with
        | _ g =>
          induction r using QuotientGroup.induction_on with
          | _ h =>
            apply Subtype.ext
            exact congrFun (congrFun ((d1 M).map_add a.1 b.1) g) h }

/-- Relative cochains which vanish on the normal subgroup.  Such cochains themselves
(descending one degree before their coboundaries) descend to quotient one-cochains. -/
def zeroRelativeC1 : AddSubgroup (relativeC1 N M) where
  carrier := {b | ∀ n : N, b.1 n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb n
    simpa [ha n, hb n]
  neg_mem' := by
    intro b hb n
    simpa [hb n]

private theorem zeroRelative_right (b : zeroRelativeC1 N M) (g : G) (n : N) :
    b.1.1 (g * n) = b.1.1 g := by
  have h := relative_d1_right N M b.1 g n
  change M.ρ g (b.1.1 n) - b.1.1 (g * n) + b.1.1 g = 0 at h
  rw [b.2 n, map_zero, zero_sub, neg_add_eq_sub] at h
  exact (sub_eq_zero.mp h).symm

private theorem zeroRelative_invariant (b : zeroRelativeC1 N M) (n : N) (g : G) :
    M.ρ n (b.1.1 g) = b.1.1 g := by
  have h := relative_d1_left N M b.1 n g
  change M.ρ n (b.1.1 g) - b.1.1 (n * g) + b.1.1 n = 0 at h
  rw [b.2 n, add_zero] at h
  have hn' : g⁻¹ * (n : G) * g ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 g
  let n' : N := ⟨g⁻¹ * (n : G) * g, hn'⟩
  have hng : (n : G) * g = g * (n' : G) := by
    dsimp [n']
    simp [mul_assoc]
  rw [hng, zeroRelative_right N M b g n'] at h
  exact sub_eq_zero.mp h

/-- A relative cochain vanishing on `N`, descended to a quotient one-cochain with
values in `M^N`. -/
def descendedC1 (b : zeroRelativeC1 N M) : C1 (MQ N M) :=
  fun q => Quotient.liftOn' q (fun g =>
    (⟨b.1.1 g, fun n => zeroRelative_invariant N M b n g⟩ : MQ N M)) (by
      intro g g' hgg'
      apply Subtype.ext
      change b.1.1 g = b.1.1 g'
      rw [QuotientGroup.leftRel_apply] at hgg'
      let n : N := ⟨g⁻¹ * g', hgg'⟩
      have heq : g' = g * (n : G) := by simp [n]
      rw [heq, zeroRelative_right N M b g n])

@[simp]
private theorem descendedC1_mk (b : zeroRelativeC1 N M) (g : G) :
    descendedC1 N M b (QuotientGroup.mk' N g) =
      (⟨b.1.1 g, fun n => zeroRelative_invariant N M b n g⟩ : MQ N M) := rfl

private theorem descendedC1_d1 (b : zeroRelativeC1 N M) (g h : G) :
    d1 (MQ N M) (descendedC1 N M b) (QuotientGroup.mk' N g)
      (QuotientGroup.mk' N h) =
        (⟨d1 M b.1.1 g h, fun n => d1_invariant N M b.1 n g h⟩ : MQ N M) := by
  apply Subtype.ext
  rfl

private theorem relativeTransgression_mem_ker_of_relativeClass_eq_zero
    (b : relativeC1 N M) (hb : relativeClass N M b = 0) :
    relativeTransgression N M b = 0 := by
  have hbmem : relativeRestrictionCocycle N M b ∈
      coboundaries1 (Rep.res N.subtype M) :=
    (QuotientAddGroup.eq_zero_iff (relativeRestrictionCocycle N M b)).mp hb
  obtain ⟨a, ha⟩ := hbmem
  let e0 : C1 M := b.1 - d0 M a
  have heRel : e0 ∈ relativeC1 N M := by
    constructor
    · intro n g
      change d1 M (b.1 - d0 M a) n g = 0
      rw [map_sub, d1_d0]
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
      exact relative_d1_left N M b n g
    · intro g n
      change d1 M (b.1 - d0 M a) g n = 0
      rw [map_sub, d1_d0]
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
      exact relative_d1_right N M b g n
  let e : relativeC1 N M := ⟨e0, heRel⟩
  have heZero : ∀ n : N, e.1 n = 0 := by
    intro n
    change b.1 n - d0 M a n = 0
    have han := congrFun ha n
    change d0 (Rep.res N.subtype M) a n = b.1 n at han
    rw [← han]
    simp [d0, Rep.res]
  let ez : zeroRelativeC1 N M := ⟨e, heZero⟩
  apply (QuotientAddGroup.eq_zero_iff (transgressionCocycle N M b)).mpr
  refine ⟨descendedC1 N M ez, ?_⟩
  funext q r
  induction q using QuotientGroup.induction_on with
  | _ g =>
    induction r using QuotientGroup.induction_on with
    | _ h =>
      apply Subtype.ext
      change d1 (MQ N M) (descendedC1 N M ez)
          (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) = d1 M b.1 g h
      rw [descendedC1_d1]
      change d1 M (b.1 - d0 M a) g h = d1 M b.1 g h
      rw [map_sub, d1_d0]
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]

private theorem relativeTransgression_ker_le :
    (relativeClass N M).ker ≤ (relativeTransgression N M).ker := by
  intro b hb
  exact AddMonoidHom.mem_ker.mpr
    (relativeTransgression_mem_ker_of_relativeClass_eq_zero N M b
      (AddMonoidHom.mem_ker.mp hb))

/-- Concrete transgression `H¹(N,M)^{G/N} → H²(G/N,M^N)`.  It is the map induced by
`b ↦ [d b]`; the preceding kernel calculation proves independence of the relative lift. -/
def transgression : quotientInvariantH1 N M →+ H2 (MQ N M) :=
  (QuotientAddGroup.lift (relativeClass N M).ker (relativeTransgression N M)
      (relativeTransgression_ker_le N M)).comp
    (QuotientAddGroup.quotientKerEquivRange (relativeClass N M)).symm.toAddMonoidHom

/-- Inflation on zero-cochains: inclusion of `N`-invariants into `M`. -/
def inflateC0 : C0 (MQ N M) →+ C0 M where
  toFun a := a.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Inflation on one-cochains: quotient precomposition followed by invariant inclusion. -/
def inflateC1 : C1 (MQ N M) →+ C1 M where
  toFun b g := (b (QuotientGroup.mk' N g)).1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Inflation on two-cochains: quotient precomposition followed by invariant inclusion. -/
def inflateC2 : C2 (MQ N M) →+ C2 M where
  toFun c g h := (c (QuotientGroup.mk' N g) (QuotientGroup.mk' N h)).1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Relative normalized two-cocycles: cocycles vanishing whenever one argument lies in
`N`.  These are precisely the cocycles which descend literally to `G/N`. -/
def relativeCocycles2 : AddSubgroup (cocycles2 M) where
  carrier := {c | (∀ (n : N) (g : G), c.1 n g = 0) ∧
    (∀ (g : G) (n : N), c.1 g n = 0)}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha₁, ha₂⟩ ⟨hb₁, hb₂⟩
    exact ⟨fun n g => by simpa using congrArg₂ (· + ·) (ha₁ n g) (hb₁ n g),
      fun g n => by simpa using congrArg₂ (· + ·) (ha₂ g n) (hb₂ g n)⟩
  neg_mem' := by
    rintro c ⟨hc₁, hc₂⟩
    exact ⟨fun n g => by simpa using congrArg Neg.neg (hc₁ n g),
      fun g n => by simpa using congrArg Neg.neg (hc₂ g n)⟩

private theorem relativeC2_right_mul (c : relativeCocycles2 N M) (g h : G) (n : N) :
    c.1.1 g (h * n) = c.1.1 g h := by
  have hd := congrFun (congrFun (congrFun c.1.2.1 g) h) (n : G)
  change M.ρ g (c.1.1 h n) - c.1.1 (g * h) n +
    c.1.1 g (h * n) - c.1.1 g h = 0 at hd
  rw [c.2.2 h n, c.2.2 (g * h) n, map_zero] at hd
  simpa only [zero_sub, neg_zero, zero_add] using sub_eq_zero.mp hd

private theorem relativeC2_left_mul (c : relativeCocycles2 N M) (g h : G) (n : N) :
    c.1.1 (g * n) h = c.1.1 g h := by
  have hd := congrFun (congrFun (congrFun c.1.2.1 g) (n : G)) h
  change M.ρ g (c.1.1 n h) - c.1.1 (g * n) h +
    c.1.1 g (n * h) - c.1.1 g n = 0 at hd
  rw [c.2.1 n h, c.2.2 g n, map_zero, zero_sub, sub_zero] at hd
  have hn' : h⁻¹ * (n : G) * h ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 h
  let n' : N := ⟨h⁻¹ * (n : G) * h, hn'⟩
  have hnh : (n : G) * h = h * (n' : G) := by
    dsimp [n']
    simp [mul_assoc]
  rw [hnh, relativeC2_right_mul N M c g h n', neg_add_eq_sub] at hd
  exact (sub_eq_zero.mp hd).symm

private theorem relativeC2_invariant (c : relativeCocycles2 N M) (n : N) (g h : G) :
    M.ρ n (c.1.1 g h) = c.1.1 g h := by
  have hd := congrFun (congrFun (congrFun c.1.2.1 (n : G)) g) h
  change M.ρ n (c.1.1 g h) - c.1.1 (n * g) h +
    c.1.1 n (g * h) - c.1.1 n g = 0 at hd
  rw [c.2.1 n (g * h), c.2.1 n g, sub_zero, add_zero] at hd
  have hn' : g⁻¹ * (n : G) * g ∈ N :=
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 g
  let n' : N := ⟨g⁻¹ * (n : G) * g, hn'⟩
  have hng : (n : G) * g = g * (n' : G) := by
    dsimp [n']
    simp [mul_assoc]
  rw [hng, relativeC2_left_mul N M c g h n'] at hd
  exact sub_eq_zero.mp hd

/-- Literal descent of a relative two-cocycle to quotient arguments and invariant values. -/
def descendedRelativeC2 (c : relativeCocycles2 N M) : C2 (MQ N M) :=
  fun q r => Quotient.liftOn' q (fun g =>
    Quotient.liftOn' r (fun h =>
      (⟨c.1.1 g h, fun n => relativeC2_invariant N M c n g h⟩ : MQ N M)) (by
        intro h h' hh
        apply Subtype.ext
        change c.1.1 g h = c.1.1 g h'
        rw [QuotientGroup.leftRel_apply] at hh
        let n : N := ⟨h⁻¹ * h', hh⟩
        have heq : h' = h * (n : G) := by simp [n]
        rw [heq, relativeC2_right_mul N M c g h n])) (by
      intro g g' hgg'
      induction r using QuotientGroup.induction_on with
      | _ h =>
        apply Subtype.ext
        change c.1.1 g h = c.1.1 g' h
        rw [QuotientGroup.leftRel_apply] at hgg'
        let n : N := ⟨g⁻¹ * g', hgg'⟩
        have heq : g' = g * (n : G) := by simp [n]
        rw [heq, relativeC2_left_mul N M c g h n])

@[simp]
theorem descendedRelativeC2_mk (c : relativeCocycles2 N M) (g h : G) :
    descendedRelativeC2 N M c (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) =
      (⟨c.1.1 g h, fun n => relativeC2_invariant N M c n g h⟩ : MQ N M) := rfl

/-- A descended relative cocycle, bundled as a normalized quotient two-cocycle. -/
def descendRelativeCocycle2 (c : relativeCocycles2 N M) : cocycles2 (MQ N M) :=
  ⟨descendedRelativeC2 N M c, ⟨by
    ext q r s
    induction q using QuotientGroup.induction_on with
    | _ g =>
      induction r using QuotientGroup.induction_on with
      | _ h =>
        induction s using QuotientGroup.induction_on with
        | _ t =>
          exact congrFun (congrFun (congrFun c.1.2.1 g) h) t, ⟨
    fun q => by
      induction q using QuotientGroup.induction_on with
      | _ g =>
        apply Subtype.ext
        exact c.1.2.2.1 g,
    fun q => by
      induction q using QuotientGroup.induction_on with
      | _ g =>
        apply Subtype.ext
        exact c.1.2.2.2 g⟩⟩⟩

private theorem inflateC0_d0 (a : C0 (MQ N M)) :
    inflateC1 N M (d0 (MQ N M) a) = d0 M (inflateC0 N M a) := by
  ext g
  rfl

private theorem inflateC1_d1 (b : C1 (MQ N M)) :
    inflateC2 N M (d1 (MQ N M) b) = d1 M (inflateC1 N M b) := by
  ext g h
  rfl

private theorem inflateC2_d2 (c : C2 (MQ N M)) :
    (fun g h t => (d2 (MQ N M) c (QuotientGroup.mk' N g)
      (QuotientGroup.mk' N h) (QuotientGroup.mk' N t)).1) =
      d2 M (inflateC2 N M c) := by
  ext g h t
  rfl

/-- Inflation of normalized quotient one-cocycles. -/
def inflateCocycles1 : cocycles1 (MQ N M) →+ cocycles1 M where
  toFun b := ⟨inflateC1 N M b, ⟨by
    change d1 M (inflateC1 N M b) = 0
    rw [← inflateC1_d1, b.2.1]
    rfl, by
    change (b.1 (QuotientGroup.mk' N 1)).1 = 0
    simpa using congrArg Subtype.val b.2.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Inflation of normalized quotient two-cocycles. -/
def inflateCocycles2 : cocycles2 (MQ N M) →+ cocycles2 M where
  toFun c := ⟨inflateC2 N M c, ⟨by
    change d2 M (inflateC2 N M c) = 0
    rw [← inflateC2_d2]
    ext g h t
    exact congrArg Subtype.val (congrFun (congrFun (congrFun c.2.1
      (QuotientGroup.mk' N g)) (QuotientGroup.mk' N h)) (QuotientGroup.mk' N t)), ⟨
      fun g => by
        change (c.1 1 (QuotientGroup.mk' N g)).1 = 0
        exact congrArg Subtype.val (c.2.2.1 _),
      fun g => by
        change (c.1 (QuotientGroup.mk' N g) 1).1 = 0
        exact congrArg Subtype.val (c.2.2.2 _)⟩⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem inflate_descendRelativeCocycle2 (c : relativeCocycles2 N M) :
    inflateCocycles2 N M (descendRelativeCocycle2 N M c) = c.1 := by
  apply Subtype.ext
  rfl

/-- Concrete inflation in degree one. -/
def inflationH1 : H1 (MQ N M) →+ H1 M :=
  QuotientAddGroup.map (coboundaries1 (MQ N M)) (coboundaries1 M)
    (inflateCocycles1 N M) (by
      rintro b ⟨a, ha⟩
      refine ⟨inflateC0 N M a, ?_⟩
      change d0 M (inflateC0 N M a) = inflateC1 N M b
      rw [← inflateC0_d0, ha]
      rfl)

/-- Concrete inflation in degree two. -/
def inflationH2 : H2 (MQ N M) →+ H2 M :=
  QuotientAddGroup.map (coboundaries2 (MQ N M)) (coboundaries2 M)
    (inflateCocycles2 N M) (by
      rintro c ⟨b, hb⟩
      refine ⟨inflateC1 N M b, ?_⟩
      change d1 M (inflateC1 N M b) = inflateC2 N M c
      rw [← inflateC1_d1, hb]
      rfl)

@[simp]
theorem inflationH1_mk (b : cocycles1 (MQ N M)) :
    inflationH1 N M (QuotientAddGroup.mk' (coboundaries1 (MQ N M)) b) =
      QuotientAddGroup.mk' (coboundaries1 M) (inflateCocycles1 N M b) := rfl

@[simp]
theorem inflationH2_mk (c : cocycles2 (MQ N M)) :
    inflationH2 N M (QuotientAddGroup.mk' (coboundaries2 (MQ N M)) c) =
      QuotientAddGroup.mk' (coboundaries2 M) (inflateCocycles2 N M c) := rfl

private def cocycleRelative (b : cocycles1 M) : relativeC1 N M := ⟨b.1, ⟨by
  intro n g
  exact congrFun (congrFun b.2.1 n) g, by
  intro g n
  exact congrFun (congrFun b.2.1 g) n⟩⟩

private theorem restrictionH1_mem_quotientInvariant (x : H1 M) :
    restrictionH1 N.subtype M x ∈ quotientInvariantH1 N M := by
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    refine ⟨cocycleRelative N M b, ?_⟩
    rfl

/-- Restriction with codomain narrowed to the concrete quotient-invariant subgroup. -/
def invariantRestrictionH1 : H1 M →+ quotientInvariantH1 N M :=
  (restrictionH1 N.subtype M).codRestrict (quotientInvariantH1 N M)
    (restrictionH1_mem_quotientInvariant N M)

@[simp]
theorem invariantRestrictionH1_coe (x : H1 M) :
    (invariantRestrictionH1 N M x : H1 (Rep.res N.subtype M)) =
      restrictionH1 N.subtype M x := rfl

@[simp]
theorem transgression_relativeClass (b : relativeC1 N M) :
    transgression N M
      (⟨relativeClass N M b, ⟨b, rfl⟩⟩ : quotientInvariantH1 N M) =
        relativeTransgression N M b := by
  let e := QuotientAddGroup.quotientKerEquivRange (relativeClass N M)
  have he : e.symm ⟨relativeClass N M b, ⟨b, rfl⟩⟩ =
      QuotientAddGroup.mk' (relativeClass N M).ker b := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  change (QuotientAddGroup.lift (relativeClass N M).ker
    (relativeTransgression N M) (relativeTransgression_ker_le N M))
      (e.symm ⟨relativeClass N M b, ⟨b, rfl⟩⟩) = relativeTransgression N M b
  rw [he]
  exact QuotientAddGroup.lift_mk' (relativeClass N M).ker
    (relativeTransgression_ker_le N M) b

private noncomputable def invariantInclusion :
    Rep.res (QuotientGroup.mk' N) (MQ N M) ⟶ M := by
  letI : Module ℤ M := M.hV2
  letI : Module ℤ (MQ N M) := (MQ N M).hV2
  exact Rep.ofHom <| M.ρ.quotientToInvariants_lift N

/-- The concrete degree-one inflation commutes with the project's fixed comparison and
Mathlib's actual inflation map. -/
theorem comparisonH1_inflation (x : H1 (MQ N M)) :
    comparisonH1 M (inflationH1 N M x) =
      groupCohomology.map (QuotientGroup.mk' N) (invariantInclusion N M) 1
        (comparisonH1 (MQ N M) x) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change groupCohomology.H1π M _ =
      groupCohomology.map (QuotientGroup.mk' N) (invariantInclusion N M) 1
        (groupCohomology.H1π (MQ N M) _)
    rw [groupCohomology.H1π_comp_map_apply]
    congr 1

/-- The analogous comparison square in degree two. -/
theorem comparisonH2_inflation (x : H2 (MQ N M)) :
    comparisonH2 M (inflationH2 N M x) =
      groupCohomology.map (QuotientGroup.mk' N) (invariantInclusion N M) 2
        (comparisonH2 (MQ N M) x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    change groupCohomology.H2π M _ =
      groupCohomology.map (QuotientGroup.mk' N) (invariantInclusion N M) 2
        (groupCohomology.H2π (MQ N M) _)
    rw [groupCohomology.H2π_comp_map_apply]
    congr 1

/-- Inflation is injective in degree one.  This is the cocycle proof: a primitive of an
inflated cocycle is automatically `N`-invariant. -/
theorem inflationH1_injective : Function.Injective (inflationH1 N M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change inflationH1 N M
      (QuotientAddGroup.mk' (coboundaries1 (MQ N M)) a) = 0 at hx
    rw [inflationH1_mk] at hx
    change (QuotientAddGroup.mk' (coboundaries1 (MQ N M)) a : H1 (MQ N M)) = 0
    have hamem : inflateCocycles1 N M a ∈ coboundaries1 M :=
      (QuotientAddGroup.eq_zero_iff (inflateCocycles1 N M a)).mp hx
    obtain ⟨m, hm⟩ := hamem
    have hminv : ∀ n : N, M.ρ n m = m := by
      intro n
      have hn := congrFun hm n
      change M.ρ n m - m = (a.1 (QuotientGroup.mk' N n)).1 at hn
      have ha1 : a.1 1 = 0 := a.2.2
      rw [show QuotientGroup.mk' N (n : G) = 1 by
        exact (QuotientGroup.eq_one_iff (n : G)).2 n.2, ha1] at hn
      exact sub_eq_zero.mp hn
    let mi : C0 (MQ N M) := ⟨m, hminv⟩
    apply (QuotientAddGroup.eq_zero_iff a).mpr
    refine ⟨mi, ?_⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | _ g =>
      change M.ρ g m - m = (a.1 (QuotientGroup.mk' N g)).1
      exact congrFun hm g

private theorem invariantRestrictionH1_inflation_zero (x : H1 (MQ N M)) :
    invariantRestrictionH1 N M (inflationH1 N M x) = 0 := by
  apply Subtype.ext
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change restrictionH1 N.subtype M
      (inflationH1 N M (QuotientAddGroup.mk' (coboundaries1 (MQ N M)) a)) = 0
    rw [inflationH1_mk, restrictionH1_mk]
    have hz : restrictCocycles1 N.subtype M (inflateCocycles1 N M a) = 0 := by
      apply Subtype.ext
      funext n
      change (a.1 (QuotientGroup.mk' N n)).1 = 0
      rw [show QuotientGroup.mk' N (n : G) = 1 by
        exact (QuotientGroup.eq_one_iff (n : G)).2 n.2, a.2.2]
      rfl
    rw [hz]
    rfl

/-- Exactness at `H¹(G,M)`, proved directly on normalized cocycles. -/
theorem inflation_invariantRestriction_exact :
    Function.Exact (inflationH1 N M) (invariantRestrictionH1 N M) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      have hxcoe := congrArg (fun u : quotientInvariantH1 N M =>
        (u : H1 (Rep.res N.subtype M))) hx
      change restrictionH1 N.subtype M
        (QuotientAddGroup.mk' (coboundaries1 M) z) = 0 at hxcoe
      rw [restrictionH1_mk] at hxcoe
      have hzmem : restrictCocycles1 N.subtype M z ∈
          coboundaries1 (Rep.res N.subtype M) :=
        (QuotientAddGroup.eq_zero_iff _).mp hxcoe
      obtain ⟨a, ha⟩ := hzmem
      let e0 : C1 M := z.1 - d0 M a
      have heRel : e0 ∈ relativeC1 N M := by
        constructor
        · intro n g
          change d1 M (z.1 - d0 M a) n g = 0
          rw [map_sub, d1_d0]
          simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
          exact congrFun (congrFun z.2.1 n) g
        · intro g n
          change d1 M (z.1 - d0 M a) g n = 0
          rw [map_sub, d1_d0]
          simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
          exact congrFun (congrFun z.2.1 g) n
      let e : relativeC1 N M := ⟨e0, heRel⟩
      have heZero : ∀ n : N, e.1 n = 0 := by
        intro n
        change z.1 n - d0 M a n = 0
        have han := congrFun ha n
        change d0 (Rep.res N.subtype M) a n = z.1 n at han
        rw [← han]
        simp [d0, Rep.res]
      let ez : zeroRelativeC1 N M := ⟨e, heZero⟩
      let qz : cocycles1 (MQ N M) := ⟨descendedC1 N M ez, ⟨by
        ext q r
        induction q using QuotientGroup.induction_on with
        | _ g =>
          induction r using QuotientGroup.induction_on with
          | _ h =>
            change d1 M (z.1 - d0 M a) g h = 0
            rw [map_sub, d1_d0, z.2.1]
            simp, by
        apply Subtype.ext
        change z.1 1 - d0 M a 1 = 0
        rw [z.2.2]
        simp [d0]⟩⟩
      refine ⟨QuotientAddGroup.mk' (coboundaries1 (MQ N M)) qz, ?_⟩
      rw [inflationH1_mk]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨-a, ?_⟩
      ext g
      change d0 M (-a) g =
        (descendedC1 N M ez (QuotientGroup.mk' N g)).1 - z.1 g
      change d0 M (-a) g = (z.1 g - d0 M a g) - z.1 g
      rw [map_neg]
      simp only [Pi.neg_apply]
      abel
  · rintro ⟨y, rfl⟩
    exact invariantRestrictionH1_inflation_zero N M y

private theorem transgression_invariantRestriction_zero (x : H1 M) :
    transgression N M (invariantRestrictionH1 N M x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let b := cocycleRelative N M z
    have heq : invariantRestrictionH1 N M
        (QuotientAddGroup.mk' (coboundaries1 M) z) =
        (⟨relativeClass N M b, ⟨b, rfl⟩⟩ : quotientInvariantH1 N M) := by
      apply Subtype.ext
      rfl
    change transgression N M (invariantRestrictionH1 N M
      (QuotientAddGroup.mk' (coboundaries1 M) z)) = 0
    rw [heq, transgression_relativeClass]
    have hz : transgressionCocycle N M b = 0 := by
      apply Subtype.ext
      funext q r
      induction q using QuotientGroup.induction_on with
      | _ g =>
        induction r using QuotientGroup.induction_on with
        | _ h =>
          apply Subtype.ext
          exact congrFun (congrFun z.2.1 g) h
    change QuotientAddGroup.mk' (coboundaries2 (MQ N M))
      (transgressionCocycle N M b) = 0
    rw [hz]
    rfl

/-- Exactness at the quotient-invariant `H¹(N,M)` term. -/
theorem invariantRestriction_transgression_exact :
    Function.Exact (invariantRestrictionH1 N M) (transgression N M) := by
  intro x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := x.2
    have hxeq : x =
        (⟨relativeClass N M b, ⟨b, rfl⟩⟩ : quotientInvariantH1 N M) := by
      apply Subtype.ext
      exact hb.symm
    have ht : relativeTransgression N M b = 0 := by
      rw [← transgression_relativeClass N M b, ← hxeq]
      exact hx
    have htmem : transgressionCocycle N M b ∈ coboundaries2 (MQ N M) :=
      (QuotientAddGroup.eq_zero_iff _).mp ht
    obtain ⟨k, hk⟩ := htmem
    have hk0 : k 1 = 0 := by
      have h := congrFun (congrFun hk 1) 1
      have hzero : d1 (MQ N M) k 1 1 = 0 := by
        rw [h]
        apply Subtype.ext
        change d1 M b.1 1 1 = 0
        exact relative_d1_left N M b (1 : N) 1
      simpa [d1] using hzero
    let z0 : C1 M := b.1 - inflateC1 N M k
    have hzCocycle : d1 M z0 = 0 := by
      ext g h
      change d1 M (b.1 - inflateC1 N M k) g h = 0
      rw [map_sub]
      simp only [Pi.sub_apply]
      have hcomm := congrFun (congrFun (inflateC1_d1 N M k) g) h
      have hkh := congrFun (congrFun hk (QuotientGroup.mk' N g))
        (QuotientGroup.mk' N h)
      have hval := congrArg Subtype.val hkh
      change d1 M (inflateC1 N M k) g h =
        (d1 (MQ N M) k (QuotientGroup.mk' N g) (QuotientGroup.mk' N h)).1 at hcomm
      rw [hcomm, hval]
      exact sub_self _
    have hzNorm : z0 1 = 0 := by
      change b.1 1 - (k 1).1 = 0
      rw [relative_apply_one N M b, hk0]
      simp
    let z : cocycles1 M := ⟨z0, hzCocycle, hzNorm⟩
    refine ⟨QuotientAddGroup.mk' (coboundaries1 M) z, ?_⟩
    rw [hxeq]
    apply Subtype.ext
    change restrictionH1 N.subtype M
      (QuotientAddGroup.mk' (coboundaries1 M) z) = relativeClass N M b
    rw [restrictionH1_mk]
    change QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
      (restrictCocycles1 N.subtype M z) =
        QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
          (relativeRestrictionCocycle N M b)
    congr 1
    apply Subtype.ext
    funext n
    change b.1 n - (k (QuotientGroup.mk' N n)).1 = b.1 n
    rw [show QuotientGroup.mk' N (n : G) = 1 by
      exact (QuotientGroup.eq_one_iff (n : G)).2 n.2, hk0]
    simp
  · rintro ⟨y, rfl⟩
    exact transgression_invariantRestriction_zero N M y

private theorem inflationH2_transgression_zero (x : quotientInvariantH1 N M) :
    inflationH2 N M (transgression N M x) = 0 := by
  obtain ⟨b, hb⟩ := x.2
  have hxeq : x =
      (⟨relativeClass N M b, ⟨b, rfl⟩⟩ : quotientInvariantH1 N M) := by
    apply Subtype.ext
    exact hb.symm
  rw [hxeq, transgression_relativeClass]
  change inflationH2 N M
    (QuotientAddGroup.mk' (coboundaries2 (MQ N M))
      (transgressionCocycle N M b)) = 0
  rw [inflationH2_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨b.1, ?_⟩
  ext g h
  rfl

/-- Exactness at `H²(G/N,M^N)`.  Together with the preceding theorem this is the
cocycle-level transgression part of the Hochschild--Serre five-term sequence. -/
theorem transgression_inflation_exact :
    Function.Exact (transgression N M) (inflationH2 N M) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      change inflationH2 N M
        (QuotientAddGroup.mk' (coboundaries2 (MQ N M)) c) = 0 at hx
      rw [inflationH2_mk] at hx
      have hcmem : inflateCocycles2 N M c ∈ coboundaries2 M :=
        (QuotientAddGroup.eq_zero_iff _).mp hx
      obtain ⟨b, hb⟩ := hcmem
      have hbRel : b ∈ relativeC1 N M := by
        constructor
        · intro n g
          have h := congrFun (congrFun hb n) g
          change d1 M b n g =
            (c.1 (QuotientGroup.mk' N n) (QuotientGroup.mk' N g)).1 at h
          rw [show QuotientGroup.mk' N (n : G) = 1 by
            exact (QuotientGroup.eq_one_iff (n : G)).2 n.2, c.2.2.1] at h
          exact h
        · intro g n
          have h := congrFun (congrFun hb g) n
          change d1 M b g n =
            (c.1 (QuotientGroup.mk' N g) (QuotientGroup.mk' N n)).1 at h
          rw [show QuotientGroup.mk' N (n : G) = 1 by
            exact (QuotientGroup.eq_one_iff (n : G)).2 n.2, c.2.2.2] at h
          exact h
      let br : relativeC1 N M := ⟨b, hbRel⟩
      let y : quotientInvariantH1 N M :=
        ⟨relativeClass N M br, ⟨br, rfl⟩⟩
      refine ⟨y, ?_⟩
      change transgression N M y =
        QuotientAddGroup.mk' (coboundaries2 (MQ N M)) c
      rw [show transgression N M y = relativeTransgression N M br by
        exact transgression_relativeClass N M br]
      change QuotientAddGroup.mk' (coboundaries2 (MQ N M))
        (transgressionCocycle N M br) =
          QuotientAddGroup.mk' (coboundaries2 (MQ N M)) c
      congr 1
      apply Subtype.ext
      funext q r
      induction q using QuotientGroup.induction_on with
      | _ g =>
        induction r using QuotientGroup.induction_on with
        | _ h =>
          apply Subtype.ext
          exact congrFun (congrFun hb g) h
  · rintro ⟨y, rfl⟩
    exact inflationH2_transgression_zero N M y

/-- Conjugation by `g`, viewed as an endomorphism of the normal subgroup. -/
def conjugateSubgroup (g : G) : N →* N where
  toFun n := ⟨g⁻¹ * (n : G) * g,
    (inferInstance : N.Normal).conj_mem' (n : G) n.2 g⟩
  map_one' := by ext; simp
  map_mul' n m := by ext; simp [mul_assoc]

/-- The standard conjugation operation on `N`-one-cochains,
`(g⋅a)(n)=g⋅a(g⁻¹ng)`. -/
def conjugateC1 (g : G) : C1 (Rep.res N.subtype M) →+ C1 (Rep.res N.subtype M) where
  toFun a n := M.ρ g (a (conjugateSubgroup N g n))
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

private theorem conjugateC1_cocycle (g : G) (a : cocycles1 (Rep.res N.subtype M)) :
    d1 (Rep.res N.subtype M) (conjugateC1 N M g a) = 0 := by
  ext n h
  let n' := conjugateSubgroup N g n
  let h' := conjugateSubgroup N g h
  have ha := congrFun (congrFun a.2.1 n') h'
  change M.ρ n (M.ρ g (a.1 h')) -
    M.ρ g (a.1 (conjugateSubgroup N g (n * h))) + M.ρ g (a.1 n') = 0
  letI : Module ℤ M := M.hV2
  have hng : (n : G) * g = g * (n' : G) := by
    dsimp [n', conjugateSubgroup]
    simp [mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hng, map_mul, Module.End.mul_apply]
  have hmul : conjugateSubgroup N g (n * h) = n' * h' := by
    ext
    simp [n', h', conjugateSubgroup, mul_assoc]
  rw [hmul]
  change M.ρ g (M.ρ n' (a.1 h')) - M.ρ g (a.1 (n' * h')) +
    M.ρ g (a.1 n') = 0
  change M.ρ n' (a.1 h') - a.1 (n' * h') + a.1 n' = 0 at ha
  rw [← map_sub, ← map_add, ha, map_zero]

/-- Conjugation on normalized `N`-cocycles. -/
def conjugateCocycles1 (g : G) :
    cocycles1 (Rep.res N.subtype M) →+ cocycles1 (Rep.res N.subtype M) where
  toFun a := ⟨conjugateC1 N M g a, conjugateC1_cocycle N M g a, by
    change M.ρ g (a.1 (conjugateSubgroup N g 1)) = 0
    rw [map_one, a.2.2, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    ext n
    simp [conjugateC1]
  map_add' := by
    intro a b
    apply Subtype.ext
    ext n
    exact map_add (M.ρ g) (a.1 (conjugateSubgroup N g n))
      (b.1 (conjugateSubgroup N g n))

/-- The induced standard conjugation action on `H¹(N,M)`. -/
def conjugationH1 (g : G) :
    H1 (Rep.res N.subtype M) →+ H1 (Rep.res N.subtype M) :=
  QuotientAddGroup.map (coboundaries1 (Rep.res N.subtype M))
    (coboundaries1 (Rep.res N.subtype M)) (conjugateCocycles1 N M g) (by
      rintro a ⟨m, hm⟩
      refine ⟨M.ρ g m, ?_⟩
      change d0 (Rep.res N.subtype M) (M.ρ g m) =
        (conjugateCocycles1 N M g a).1
      ext n
      have hn := congrFun hm (conjugateSubgroup N g n)
      change M.ρ n (M.ρ g m) - M.ρ g m =
        M.ρ g (a.1 (conjugateSubgroup N g n))
      letI : Module ℤ M := M.hV2
      have hng : (n : G) * g = g * (conjugateSubgroup N g n : G) := by
        simp [conjugateSubgroup, mul_assoc]
      change M.ρ (conjugateSubgroup N g n) m - m =
        a.1 (conjugateSubgroup N g n) at hn
      rw [← Module.End.mul_apply, ← map_mul, hng, map_mul, Module.End.mul_apply,
        ← map_sub, hn])

/-- The usual fixed subgroup for the `G/N`-action on `H¹(N,M)`.  Requiring all `g : G`
to fix a class is equivalent to quotient invariance, since inner `N`-conjugations act
trivially on cohomology. -/
def fixedH1 : AddSubgroup (H1 (Rep.res N.subtype M)) where
  carrier := {x | ∀ g : G, conjugationH1 N M g x = x}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g]
  neg_mem' := by
    intro x hx g
    rw [map_neg, hx g]

private theorem relativeClass_fixed (b : relativeC1 N M) (g : G) :
    conjugationH1 N M g (relativeClass N M b) = relativeClass N M b := by
  change QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
      (conjugateCocycles1 N M g (relativeRestrictionCocycle N M b)) =
    QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
      (relativeRestrictionCocycle N M b)
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  refine ⟨b.1 g, ?_⟩
  change d0 (Rep.res N.subtype M) (b.1 g) =
    (conjugateCocycles1 N M g (relativeRestrictionCocycle N M b) -
      relativeRestrictionCocycle N M b).1
  ext n
  have hright := relative_d1_right N M b g (conjugateSubgroup N g n)
  have hleft := relative_d1_left N M b n g
  change M.ρ g (b.1 (conjugateSubgroup N g n)) - b.1 (g *
    (conjugateSubgroup N g n : G)) + b.1 g = 0 at hright
  change M.ρ n (b.1 g) - b.1 (n * g) + b.1 n = 0 at hleft
  have heq : g * (conjugateSubgroup N g n : G) = (n : G) * g := by
    simp [conjugateSubgroup, mul_assoc]
  change M.ρ n (b.1 g) - b.1 g =
    M.ρ g (b.1 (conjugateSubgroup N g n)) - b.1 n
  rw [heq] at hright
  apply sub_eq_sub_iff_add_eq_add.mpr
  calc
    M.ρ n (b.1 g) + b.1 n = b.1 (n * g) := by
      rw [← sub_eq_zero]
      calc
        M.ρ n (b.1 g) + b.1 n - b.1 (n * g) =
            M.ρ n (b.1 g) - b.1 (n * g) + b.1 n := by abel
        _ = 0 := hleft
    _ = M.ρ g (b.1 (conjugateSubgroup N g n)) + b.1 g := by
      symm
      rw [← sub_eq_zero]
      calc
        M.ρ g (b.1 (conjugateSubgroup N g n)) + b.1 g - b.1 (n * g) =
            M.ρ g (b.1 (conjugateSubgroup N g n)) - b.1 (n * g) + b.1 g := by abel
        _ = 0 := hright

/-- A normalized set-theoretic section of the quotient map. -/
noncomputable def quotientSection (q : Q N) : G := by
  classical
  exact if h : q = 1 then 1 else Function.surjInv (QuotientGroup.mk'_surjective N) q

@[simp]
private theorem quotientSection_one : quotientSection N (1 : Q N) = 1 := by
  simp [quotientSection]

private theorem quotientSection_spec (q : Q N) :
    QuotientGroup.mk' N (quotientSection N q) = q := by
  by_cases h : q = 1
  · simp [h, quotientSection]
  · simp only [quotientSection, h, ↓reduceDIte]
    exact Function.surjInv_eq (QuotientGroup.mk'_surjective N) q

/-- The `N`-part in the decomposition `g = kernelPart(g) * section(gN)`. -/
noncomputable def kernelPart (g : G) : N := ⟨
  g * (quotientSection N (QuotientGroup.mk' N g))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N
      (g * (quotientSection N (QuotientGroup.mk' N g))⁻¹) = 1
    rw [map_mul, map_inv, quotientSection_spec]
    simp⟩

private theorem kernelPart_decomposition (g : G) :
    (kernelPart N g : G) * quotientSection N (QuotientGroup.mk' N g) = g := by
  simp [kernelPart, mul_assoc]

private theorem quotient_mk_left_N (n : N) (g : G) :
    QuotientGroup.mk' N ((n : G) * g) = QuotientGroup.mk' N g := by
  rw [map_mul, show QuotientGroup.mk' N (n : G) = 1 from
    (QuotientGroup.eq_one_iff (n : G)).2 n.2, one_mul]

private theorem quotient_mk_right_N (g : G) (n : N) :
    QuotientGroup.mk' N (g * (n : G)) = QuotientGroup.mk' N g := by
  rw [map_mul, show QuotientGroup.mk' N (n : G) = 1 from
    (QuotientGroup.eq_one_iff (n : G)).2 n.2, mul_one]

private theorem kernelPart_left (n : N) (g : G) :
    kernelPart N ((n : G) * g) = n * kernelPart N g := by
  apply Subtype.ext
  simp [kernelPart, quotient_mk_left_N N n g, mul_assoc]

private theorem kernelPart_subgroup (n : N) : kernelPart N (n : G) = n := by
  apply Subtype.ext
  simp [kernelPart, quotientSection]

private theorem kernelPart_section (q : Q N) :
    kernelPart N (quotientSection N q) = 1 := by
  apply Subtype.ext
  simp [kernelPart, quotientSection_spec N q]

/-- Every concrete quotient-invariant class is fixed by the standard conjugation action. -/
theorem quotientInvariantH1_le_fixedH1 : quotientInvariantH1 N M ≤ fixedH1 N M := by
  intro x hx g
  obtain ⟨b, hb⟩ := hx
  rw [← hb]
  exact relativeClass_fixed N M b g

/-- A fixed `H¹(N,M)` class admits a relative cochain lift.  This is the classical
set-theoretic-section construction used in the transgression proof. -/
private theorem fixedH1_le_quotientInvariantH1 : fixedH1 N M ≤ quotientInvariantH1 N M := by
  classical
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    have hw : ∀ g : G, ∃ m : M,
        d0 (Rep.res N.subtype M) m =
          (conjugateCocycles1 N M g a - a).1 := by
      intro g
      have hg := hx g
      change QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
          (conjugateCocycles1 N M g a) =
        QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M)) a at hg
      exact (QuotientAddGroup.eq_iff_sub_mem.mp hg)
    choose raw hraw using hw
    let corr : Q N → M := fun q => raw (quotientSection N q) - raw 1
    have hcorr_one : corr 1 = 0 := by
      simp [corr]
    have hcorr (q : Q N) (n : N) :
        M.ρ n (corr q) - corr q =
          M.ρ (quotientSection N q)
              (a.1 (conjugateSubgroup N (quotientSection N q) n)) - a.1 n := by
      have hs := congrFun (hraw (quotientSection N q)) n
      change M.ρ n (raw (quotientSection N q)) - raw (quotientSection N q) =
        M.ρ (quotientSection N q)
          (a.1 (conjugateSubgroup N (quotientSection N q) n)) - a.1 n at hs
      have h1 := congrFun (hraw 1) n
      change M.ρ n (raw 1) - raw 1 =
        M.ρ 1 (a.1 (conjugateSubgroup N 1 n)) - a.1 n at h1
      have h1zero : M.ρ n (raw 1) - raw 1 = 0 := by
        rw [h1]
        simp [conjugateSubgroup]
      change M.ρ n (raw (quotientSection N q) - raw 1) -
          (raw (quotientSection N q) - raw 1) = _
      rw [map_sub]
      calc
        (M.ρ n (raw (quotientSection N q)) - M.ρ n (raw 1)) -
            (raw (quotientSection N q) - raw 1) =
          (M.ρ n (raw (quotientSection N q)) - raw (quotientSection N q)) -
            (M.ρ n (raw 1) - raw 1) := by abel
        _ = _ := by rw [hs, h1zero, sub_zero]
    let bc : C1 M := fun g =>
      M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g)) + a.1 (kernelPart N g)
    have hkernelN (n : N) : kernelPart N (n : G) = n := by
      apply Subtype.ext
      simp [kernelPart, show QuotientGroup.mk' N (n : G) = 1 from
        (QuotientGroup.eq_one_iff (n : G)).2 n.2]
    have hbcN (n : N) : bc n = a.1 n := by
      change M.ρ (kernelPart N (n : G))
          (corr (QuotientGroup.mk' N (n : G))) +
          a.1 (kernelPart N (n : G)) = a.1 n
      rw [hkernelN n, show QuotientGroup.mk' N (n : G) = 1 from
        (QuotientGroup.eq_one_iff (n : G)).2 n.2, hcorr_one, map_zero, zero_add]
    have hbleft (n : N) (g : G) :
        bc ((n : G) * g) = M.ρ n (bc g) + a.1 n := by
      let k := kernelPart N g
      have ha := congrFun (congrFun a.2.1 n) k
      change M.ρ n (a.1 k) - a.1 (n * k) + a.1 n = 0 at ha
      have hak : a.1 (n * k) = M.ρ n (a.1 k) + a.1 n := by
        apply (sub_eq_zero.mp ?_).symm
        calc
          M.ρ n (a.1 k) + a.1 n - a.1 (n * k) =
              M.ρ n (a.1 k) - a.1 (n * k) + a.1 n := by abel
          _ = 0 := ha
      change M.ρ (kernelPart N ((n : G) * g))
          (corr (QuotientGroup.mk' N ((n : G) * g))) +
          a.1 (kernelPart N ((n : G) * g)) =
        M.ρ n (M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g)) +
          a.1 (kernelPart N g)) + a.1 n
      rw [quotient_mk_left_N N n g, kernelPart_left N n g, hak, map_add]
      letI : Module ℤ M := M.hV2
      change M.ρ ((n : G) * (kernelPart N g : G))
          (corr (QuotientGroup.mk' N g)) +
          (M.ρ n (a.1 k) + a.1 n) =
        M.ρ n (M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g))) +
          M.ρ n (a.1 (kernelPart N g)) + a.1 n
      rw [map_mul, Module.End.mul_apply]
      abel
    have hbright (g : G) (n : N) :
        bc (g * (n : G)) = M.ρ g (a.1 n) + bc g := by
      let q := QuotientGroup.mk' N g
      let s := quotientSection N q
      let k := kernelPart N g
      have hgs : (k : G) * s = g := kernelPart_decomposition N g
      have hns : s * (n : G) * s⁻¹ ∈ N :=
        (inferInstance : N.Normal).conj_mem (n : G) n.2 s
      let ns : N := ⟨s * (n : G) * s⁻¹, hns⟩
      have hsn : s * (n : G) = (ns : G) * s := by
        dsimp [ns]
        simp [mul_assoc]
      have hkright : kernelPart N (g * (n : G)) = k * ns := by
        apply Subtype.ext
        change g * (n : G) *
            (quotientSection N (QuotientGroup.mk' N (g * (n : G))))⁻¹ =
          (k : G) * (ns : G)
        rw [quotient_mk_right_N N g n]
        rw [← hgs]
        have hqks : QuotientGroup.mk' N ((k : G) * s) = q := by
          rw [hgs]
        rw [hqks]
        change (k : G) * s * (n : G) * s⁻¹ =
          (k : G) * (s * (n : G) * s⁻¹)
        simp [mul_assoc]
      have hcorrns := hcorr q ns
      have hcorrns' : M.ρ ns (corr q) + a.1 ns =
          corr q + M.ρ s (a.1 n) := by
        have hconj : conjugateSubgroup N s ns = n := by
          apply Subtype.ext
          dsimp [conjugateSubgroup, ns]
          simp [mul_assoc]
        rw [hconj] at hcorrns
        simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp
          (show M.ρ ns (corr q) - corr q = M.ρ s (a.1 n) - a.1 ns from hcorrns)
      have ha := congrFun (congrFun a.2.1 k) ns
      change M.ρ k (a.1 ns) - a.1 (k * ns) + a.1 k = 0 at ha
      have hak : a.1 (k * ns) = M.ρ k (a.1 ns) + a.1 k := by
        apply (sub_eq_zero.mp ?_).symm
        calc
          M.ρ k (a.1 ns) + a.1 k - a.1 (k * ns) =
              M.ρ k (a.1 ns) - a.1 (k * ns) + a.1 k := by abel
          _ = 0 := ha
      change M.ρ (kernelPart N (g * (n : G)))
          (corr (QuotientGroup.mk' N (g * (n : G)))) +
          a.1 (kernelPart N (g * (n : G))) =
        M.ρ g (a.1 n) +
          (M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g)) +
            a.1 (kernelPart N g))
      rw [quotient_mk_right_N N g n, hkright, hak]
      letI : Module ℤ M := M.hV2
      change M.ρ ((k : G) * (ns : G)) (corr q) +
          (M.ρ k (a.1 ns) + a.1 k) =
        M.ρ g (a.1 n) + (M.ρ k (corr q) + a.1 k)
      rw [map_mul, Module.End.mul_apply]
      have hρ : M.ρ g (a.1 n) = M.ρ k (M.ρ s (a.1 n)) := by
        rw [← Module.End.mul_apply, ← map_mul, hgs]
      calc
        M.ρ k (M.ρ ns (corr q)) + (M.ρ k (a.1 ns) + a.1 k) =
            M.ρ k (M.ρ ns (corr q) + a.1 ns) + a.1 k := by
              rw [map_add]
              exact (add_assoc _ _ _).symm
        _ = M.ρ k (corr q + M.ρ s (a.1 n)) + a.1 k := by
              rw [hcorrns']
        _ = M.ρ k (corr q) + M.ρ k (M.ρ s (a.1 n)) + a.1 k := by
              rw [map_add]
        _ = M.ρ g (a.1 n) + (M.ρ k (corr q) + a.1 k) := by
              rw [hρ]
              abel
    have hbcRel : bc ∈ relativeC1 N M := by
      constructor
      · intro n g
        change M.ρ n (bc g) - bc ((n : G) * g) + bc n = 0
        rw [hbleft, hbcN]
        abel
      · intro g n
        change M.ρ g (bc n) - bc (g * (n : G)) + bc g = 0
        rw [hbcN, hbright]
        abel
    let b : relativeC1 N M := ⟨bc, hbcRel⟩
    refine ⟨b, ?_⟩
    change QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M))
      (relativeRestrictionCocycle N M b) =
        QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M)) a
    congr 1
    apply Subtype.ext
    funext n
    exact hbcN n

/-- The stable-lift model used to construct transgression is exactly the usual fixed
subgroup `H¹(N,M)^{G/N}`. -/
theorem quotientInvariantH1_eq_fixedH1 : quotientInvariantH1 N M = fixedH1 N M :=
  le_antisymm (quotientInvariantH1_le_fixedH1 N M)
    (fixedH1_le_quotientInvariantH1 N M)

private theorem restrictionH2_inflation_zero
    (x : H2 (M.quotientToInvariants N)) :
    restrictionH2 N.subtype M (inflationH2 N M x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    change restrictionH2 N.subtype M
      (inflationH2 N M (QuotientAddGroup.mk'
        (coboundaries2 (M.quotientToInvariants N)) c)) = 0
    rw [inflationH2_mk, restrictionH2_mk]
    have hz : restrictCocycles2 N.subtype M (inflateCocycles2 N M c) = 0 := by
      apply Subtype.ext
      funext n h
      change (c.1 (QuotientGroup.mk' N n) (QuotientGroup.mk' N h)).1 = 0
      rw [show QuotientGroup.mk' N (n : G) = 1 by
        exact (QuotientGroup.eq_one_iff (n : G)).2 n.2,
        show QuotientGroup.mk' N (h : G) = 1 by
          exact (QuotientGroup.eq_one_iff (h : G)).2 h.2,
        c.2.2.1]
      rfl
    rw [hz]
    rfl

/-- If `H¹(N,M)=0`, inflation followed by restriction is exact at `H²(G,M)`.
This is the next Hochschild--Serre edge after the five-term sequence, proved directly on
normalized inhomogeneous cocycles. -/
theorem inflation_restrictionH2_exact_of_H1_zero
    (hH1 : ∀ x : H1 (Rep.res N.subtype M), x = 0) :
    Function.Exact (inflationH2 N M) (restrictionH2 N.subtype M) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      change restrictionH2 N.subtype M
        (QuotientAddGroup.mk' (coboundaries2 M) c) = 0 at hx
      rw [restrictionH2_mk] at hx
      change (QuotientAddGroup.mk' (coboundaries2 M) c : H2 M) ∈
        Set.range (inflationH2 N M)
      have hcmem : restrictCocycles2 N.subtype M c ∈
          coboundaries2 (Rep.res N.subtype M) :=
        (QuotientAddGroup.eq_zero_iff _).mp hx
      obtain ⟨a, ha⟩ := hcmem
      have haone : a 1 = 0 := by
        have h := congrFun (congrFun ha 1) 1
        change d1 (Rep.res N.subtype M) a 1 1 = c.1 1 1 at h
        rw [c.2.2.1] at h
        simpa [d1] using h
      let b0 : C1 M := fun g =>
        a (kernelPart N g) - c.1 (kernelPart N g)
          (quotientSection N (QuotientGroup.mk' N g))
      have hb0one : b0 1 = 0 := by
        change a (kernelPart N (1 : G)) - c.1 (kernelPart N (1 : G))
          (quotientSection N (QuotientGroup.mk' N (1 : G))) = 0
        have hk1 : kernelPart N (1 : G) = (1 : N) := by
          simpa using kernelPart_subgroup N (1 : N)
        rw [hk1, haone]
        simp only [quotientSection, map_one, dite_true, zero_sub]
        have hc11 : c.1 ((1 : N) : G) 1 = 0 := by
          simpa using c.2.2.1 (1 : G)
        rw [hc11]
        exact neg_zero
      have hbLeft (n : N) (g : G) : d1 M b0 n g = c.1 n g := by
        let k := kernelPart N g
        let s := quotientSection N (QuotientGroup.mk' N g)
        have hdecomp : (k : G) * s = g := kernelPart_decomposition N g
        have hak := congrFun (congrFun ha n) k
        change M.ρ n (a k) - a (n * k) + a n = c.1 n k at hak
        have hc := congrFun (congrFun (congrFun c.2.1 (n : G)) (k : G)) s
        change M.ρ n (c.1 k s) - c.1 (n * k) s +
          c.1 n ((k : G) * s) - c.1 n k = 0 at hc
        have hc' : d2 M c.1 (n : G) (k : G) s = 0 :=
          congrFun (congrFun (congrFun c.2.1 (n : G)) (k : G)) s
        change M.ρ n (a k - c.1 k s) -
          (a (kernelPart N ((n : G) * g)) -
            c.1 (kernelPart N ((n : G) * g))
              (quotientSection N (QuotientGroup.mk' N ((n : G) * g)))) +
          (a (kernelPart N (n : G)) -
            c.1 (kernelPart N (n : G))
              (quotientSection N (QuotientGroup.mk' N (n : G)))) = c.1 n g
        rw [kernelPart_left N n g, quotient_mk_left_N N n g,
          kernelPart_subgroup N n]
        rw [show QuotientGroup.mk' N (n : G) = 1 by
          exact (QuotientGroup.eq_one_iff (n : G)).2 n.2]
        simp only [quotientSection, dite_true, map_sub]
        rw [c.2.2.2]
        change M.ρ n (a k) - M.ρ n (c.1 k s) -
          (a (n * k) - c.1 (n * k) s) + (a n - 0) = c.1 n g
        calc
          _ = (M.ρ n (a k) - a (n * k) + a n) +
              (-M.ρ n (c.1 k s) + c.1 (n * k) s) := by abel
          _ = c.1 n k + (-M.ρ n (c.1 k s) + c.1 (n * k) s) := by rw [hak]
          _ = c.1 n ((k : G) * s) := by
            rw [← sub_eq_zero]
            calc
              c.1 n k + (-M.ρ n (c.1 k s) + c.1 (n * k) s) -
                  c.1 n ((k : G) * s) = -d2 M c.1 n k s := by
                    simp only [d2, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
                    abel
              _ = 0 := by rw [hc']; exact neg_zero
          _ = c.1 n g := by rw [hdecomp]
      let δ : C2 M := d1 M b0 - c.1
      have hδcocycle : d2 M δ = 0 := by
        change d2 M (d1 M b0 - c.1) = 0
        rw [map_sub, d2_d1, c.2.1]
        exact sub_self 0
      have hδleft (n : N) (g : G) : δ n g = 0 := by
        change d1 M b0 n g - c.1 n g = 0
        exact sub_eq_zero.mpr (hbLeft n g)
      have hδrightOne (g : G) : δ g 1 = 0 := by
        change d1 M b0 g 1 - c.1 g 1 = 0
        rw [c.2.2.2, sub_zero]
        simp [d1, hb0one]
      have hδtransport (n : N) (g h : G) :
          δ ((n : G) * g) h = M.ρ n (δ g h) := by
        have hd := congrFun (congrFun (congrFun hδcocycle (n : G)) g) h
        change M.ρ n (δ g h) - δ (n * g) h + δ n (g * h) - δ n g = 0 at hd
        rw [hδleft n (g * h), hδleft n g, sub_zero, add_zero] at hd
        exact (sub_eq_zero.mp hd).symm
      have hAcocycle (q : G ⧸ N) :
          d1 (Rep.res N.subtype M)
            (fun n => δ (quotientSection N q)
              (conjugateSubgroup N (quotientSection N q) n)) = 0 := by
        ext n m
        let s := quotientSection N q
        let n0 := conjugateSubgroup N s n
        let m0 := conjugateSubgroup N s m
        have hd := congrFun (congrFun (congrFun hδcocycle s) (n0 : G)) (m0 : G)
        change M.ρ s (δ n0 m0) - δ (s * n0) m0 +
          δ s (n0 * m0) - δ s n0 = 0 at hd
        rw [hδleft n0 m0, map_zero, zero_sub] at hd
        have hsn : s * (n0 : G) = (n : G) * s := by
          dsimp [n0]
          simp [conjugateSubgroup, mul_assoc]
        have hmul : n0 * m0 = conjugateSubgroup N s (n * m) := by
          exact ((conjugateSubgroup N s).map_mul n m).symm
        have hmulG : (n0 : G) * (m0 : G) =
            (conjugateSubgroup N s (n * m) : G) := by
          exact congrArg Subtype.val hmul
        rw [hsn, hδtransport n s m0, hmulG] at hd
        change M.ρ n (δ s m0) - δ s (conjugateSubgroup N s (n * m)) +
          δ s n0 = 0
        rw [← neg_eq_zero]
        calc
          -(M.ρ n (δ s m0) - δ s (conjugateSubgroup N s (n * m)) +
              δ s n0) =
              -M.ρ n (δ s m0) + δ s (conjugateSubgroup N s (n * m)) -
                δ s n0 := by abel
          _ = 0 := hd
      have hAnormalized (q : G ⧸ N) :
          (fun n => δ (quotientSection N q)
            (conjugateSubgroup N (quotientSection N q) n)) 1 = 0 := by
        change δ (quotientSection N q)
          (conjugateSubgroup N (quotientSection N q) 1) = 0
        rw [map_one]
        exact hδrightOne (quotientSection N q)
      let A : (G ⧸ N) → cocycles1 (Rep.res N.subtype M) := fun q =>
        ⟨fun n => δ (quotientSection N q)
            (conjugateSubgroup N (quotientSection N q) n),
          hAcocycle q, hAnormalized q⟩
      have hAone (n : N) : (A 1).1 n = 0 := by
        change δ (quotientSection N 1)
          (conjugateSubgroup N (quotientSection N 1) n) = 0
        have h := hδleft (1 : N) (n : G)
        simpa [quotientSection, conjugateSubgroup] using h
      have hv_exists (q : G ⧸ N) : ∃ v : M,
          d0 (Rep.res N.subtype M) v = (A q).1 := by
        have hz : (QuotientAddGroup.mk' (coboundaries1 (Rep.res N.subtype M)) (A q) :
            H1 (Rep.res N.subtype M)) = 0 := hH1 _
        have hm : A q ∈ coboundaries1 (Rep.res N.subtype M) :=
          (QuotientAddGroup.eq_zero_iff _).mp hz
        exact hm
      choose v hv using hv_exists
      let corr : (G ⧸ N) → M := fun q => v q - v 1
      have hcorr_one : corr 1 = 0 := by simp [corr]
      have hcorr_coboundary (q : G ⧸ N) (n : N) :
          M.ρ n (corr q) - corr q = (A q).1 n := by
        have hq := congrFun (hv q) n
        have h1 := congrFun (hv 1) n
        change M.ρ n (v q) - v q = (A q).1 n at hq
        change M.ρ n (v 1) - v 1 = (A 1).1 n at h1
        change M.ρ n (v q - v 1) - (v q - v 1) = (A q).1 n
        rw [map_sub]
        calc
          (M.ρ n (v q) - M.ρ n (v 1)) - (v q - v 1) =
              (M.ρ n (v q) - v q) - (M.ρ n (v 1) - v 1) := by abel
          _ = (A q).1 n - (A 1).1 n := by rw [hq, h1]
          _ = (A q).1 n := by rw [hAone]; exact sub_zero _
      let e : C1 M := fun g =>
        M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g))
      have he_subgroup (n : N) : e n = 0 := by
        change M.ρ (kernelPart N (n : G))
          (corr (QuotientGroup.mk' N (n : G))) = 0
        rw [kernelPart_subgroup N n,
          show QuotientGroup.mk' N (n : G) = 1 by
            exact (QuotientGroup.eq_one_iff (n : G)).2 n.2,
          hcorr_one, map_zero]
      have he_left (n : N) (g : G) : e ((n : G) * g) = M.ρ n (e g) := by
        change M.ρ (kernelPart N ((n : G) * g))
            (corr (QuotientGroup.mk' N ((n : G) * g))) =
          M.ρ n (M.ρ (kernelPart N g) (corr (QuotientGroup.mk' N g)))
        rw [kernelPart_left N n g, quotient_mk_left_N N n g]
        letI : Module ℤ M := M.hV2
        rw [← Module.End.mul_apply, ← map_mul]
        rfl
      have he_section (q : G ⧸ N) : e (quotientSection N q) = corr q := by
        change M.ρ (kernelPart N (quotientSection N q))
          (corr (QuotientGroup.mk' N (quotientSection N q))) = corr q
        rw [kernelPart_section N q, quotientSection_spec N q]
        simp
      have hde_left (n : N) (g : G) : d1 M e n g = 0 := by
        change M.ρ n (e g) - e ((n : G) * g) + e n = 0
        rw [he_left n g, he_subgroup n]
        abel
      have hde_section (q : G ⧸ N) (n : N) :
          d1 M e (quotientSection N q)
              (conjugateSubgroup N (quotientSection N q) n) = -(A q).1 n := by
        let s := quotientSection N q
        let n0 := conjugateSubgroup N s n
        have hsn : s * (n0 : G) = (n : G) * s := by
          dsimp [n0]
          simp [conjugateSubgroup, mul_assoc]
        change M.ρ s (e n0) - e (s * n0) + e s = -(A q).1 n
        rw [he_subgroup n0, map_zero, zero_sub, hsn, he_left n s, he_section q]
        rw [← hcorr_coboundary q n]
        abel
      let b : C1 M := b0 + e
      let ε : C2 M := d1 M b - c.1
      have hεcocycle : d2 M ε = 0 := by
        change d2 M (d1 M b - c.1) = 0
        rw [map_sub, d2_d1, c.2.1]
        exact sub_self 0
      have hεleft (n : N) (g : G) : ε n g = 0 := by
        change d1 M (b0 + e) n g - c.1 n g = 0
        rw [map_add]
        simp only [Pi.add_apply]
        rw [hbLeft n g, hde_left n g]
        abel
      have hεtransport (n : N) (g h : G) :
          ε ((n : G) * g) h = M.ρ n (ε g h) := by
        have hd := congrFun (congrFun (congrFun hεcocycle (n : G)) g) h
        change M.ρ n (ε g h) - ε (n * g) h + ε n (g * h) - ε n g = 0 at hd
        rw [hεleft n (g * h), hεleft n g, sub_zero, add_zero] at hd
        exact (sub_eq_zero.mp hd).symm
      have hεsection (q : G ⧸ N) (n : N) :
          ε (quotientSection N q)
            (conjugateSubgroup N (quotientSection N q) n) = 0 := by
        change d1 M (b0 + e) (quotientSection N q)
            (conjugateSubgroup N (quotientSection N q) n) -
          c.1 (quotientSection N q)
            (conjugateSubgroup N (quotientSection N q) n) = 0
        rw [map_add]
        simp only [Pi.add_apply]
        calc
          d1 M b0 (quotientSection N q)
                (conjugateSubgroup N (quotientSection N q) n) +
              d1 M e (quotientSection N q)
                (conjugateSubgroup N (quotientSection N q) n) -
              c.1 (quotientSection N q)
                (conjugateSubgroup N (quotientSection N q) n) =
            δ (quotientSection N q)
                (conjugateSubgroup N (quotientSection N q) n) +
              d1 M e (quotientSection N q)
                (conjugateSubgroup N (quotientSection N q) n) := by
                  dsimp only [δ]
                  simp only [Pi.sub_apply]
                  abel
          _ = (A q).1 n + -(A q).1 n := by rw [hde_section q n]
          _ = 0 := add_neg_cancel _
      have hεright (g : G) (n : N) : ε g n = 0 := by
        let k := kernelPart N g
        let s := quotientSection N (QuotientGroup.mk' N g)
        let nf : N := ⟨s * (n : G) * s⁻¹, by
          have hn := (inferInstance : N.Normal).conj_mem' (n : G) n.2 s⁻¹
          simpa using hn⟩
        have hconj : conjugateSubgroup N s nf = n := by
          apply Subtype.ext
          simp [nf, conjugateSubgroup, mul_assoc]
        have hs : ε s n = 0 := by
          rw [← hconj]
          exact hεsection (QuotientGroup.mk' N g) nf
        have hg : (k : G) * s = g := kernelPart_decomposition N g
        rw [← hg, hεtransport k s n, hs, map_zero]
      let z0 : C2 M := c.1 - d1 M b
      have hzCocycle : d2 M z0 = 0 := by
        change d2 M (c.1 - d1 M b) = 0
        rw [map_sub, c.2.1, d2_d1]
        exact sub_self 0
      have hzNormalized : z0 ∈ normalized2 M := by
        constructor
        · intro g
          change c.1 1 g - d1 M b 1 g = 0
          have h := hεleft (1 : N) g
          change d1 M b (1 : G) g - c.1 (1 : G) g = 0 at h
          exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
        · intro g
          change c.1 g 1 - d1 M b g 1 = 0
          have h := hεright g (1 : N)
          change d1 M b g (1 : G) - c.1 g (1 : G) = 0 at h
          exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
      let z : cocycles2 M := ⟨z0, hzCocycle, hzNormalized⟩
      have hzRelative : z ∈ relativeCocycles2 N M := by
        constructor
        · intro n g
          change c.1 n g - d1 M b n g = 0
          have h := hεleft n g
          change d1 M b n g - c.1 n g = 0 at h
          exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
        · intro g n
          change c.1 g n - d1 M b g n = 0
          have h := hεright g n
          change d1 M b g n - c.1 g n = 0 at h
          exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
      let zr : relativeCocycles2 N M := ⟨z, hzRelative⟩
      let qz : cocycles2 (M.quotientToInvariants N) :=
        descendRelativeCocycle2 N M zr
      refine ⟨QuotientAddGroup.mk'
        (coboundaries2 (M.quotientToInvariants N)) qz, ?_⟩
      rw [inflationH2_mk]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨-b, ?_⟩
      ext g h
      change d1 M (-b) g h =
        (inflateCocycles2 N M qz).1 g h - c.1 g h
      rw [show inflateCocycles2 N M qz = z by
        exact inflate_descendRelativeCocycle2 N M zr]
      change d1 M (-b) g h = (c.1 g h - d1 M b g h) - c.1 g h
      rw [map_neg]
      simp only [Pi.neg_apply]
      abel
  · rintro ⟨y, rfl⟩
    exact restrictionH2_inflation_zero N M y

/-- The identity-on-classes equivalence between the relative-lift model and the literal
fixed subgroup. -/
def invariantFixedEquiv : quotientInvariantH1 N M ≃+ fixedH1 N M where
  toFun x := ⟨x.1, quotientInvariantH1_le_fixedH1 N M x.2⟩
  invFun x := ⟨x.1, by
    rw [quotientInvariantH1_eq_fixedH1 N M]
    exact x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl

/-- Literal restriction with codomain `H¹(N,M)^{G/N}`. -/
def fixedRestrictionH1 : H1 M →+ fixedH1 N M :=
  (invariantFixedEquiv N M).toAddMonoidHom.comp (invariantRestrictionH1 N M)

/-- Transgression whose domain is the literal fixed subgroup. -/
def fixedTransgression : fixedH1 N M →+ H2 (MQ N M) :=
  (transgression N M).comp (invariantFixedEquiv N M).symm.toAddMonoidHom

private theorem inflation_fixedRestriction_exact :
    Function.Exact (inflationH1 N M) (fixedRestrictionH1 N M) := by
  intro x
  have hzero : fixedRestrictionH1 N M x = 0 ↔ invariantRestrictionH1 N M x = 0 := by
    constructor
    · intro h
      apply (invariantFixedEquiv N M).injective
      simpa [fixedRestrictionH1] using h
    · intro h
      simp [fixedRestrictionH1, h]
  rw [hzero]
  exact inflation_invariantRestriction_exact N M x

private theorem fixedRestriction_transgression_exact :
    Function.Exact (fixedRestrictionH1 N M) (fixedTransgression N M) := by
  intro x
  let e := invariantFixedEquiv N M
  have ht : fixedTransgression N M x = 0 ↔
      transgression N M (e.symm x) = 0 := Iff.rfl
  rw [ht, invariantRestriction_transgression_exact N M]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change e (invariantRestrictionH1 N M y) = x
    rw [hy, e.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply e.injective
    change e (invariantRestrictionH1 N M y) = x
    exact hy

private theorem fixedTransgression_inflation_exact :
    Function.Exact (fixedTransgression N M) (inflationH2 N M) := by
  intro x
  rw [transgression_inflation_exact N M]
  let e := invariantFixedEquiv N M
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    simpa [fixedTransgression, e] using hy
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    simpa [fixedTransgression, e] using hy

/-- Exactness data for the concrete five-term Hochschild--Serre sequence. -/
structure FiveTermExact : Prop where
  inflation_injective : Function.Injective (inflationH1 N M)
  exact_at_H1G : Function.Exact (inflationH1 N M) (fixedRestrictionH1 N M)
  exact_at_H1N : Function.Exact (fixedRestrictionH1 N M) (fixedTransgression N M)
  exact_at_H2Q : Function.Exact (fixedTransgression N M) (inflationH2 N M)

/-- Exactness data through restriction in degree two when `H¹(N,M)=0`. -/
structure SixTermExactOfH1Zero : Prop extends FiveTermExact N M where
  exact_at_H2G : Function.Exact (inflationH2 N M) (restrictionH2 N.subtype M)

/-- The degree-two inflation--restriction (five-term Hochschild--Serre) sequence on the
project's normalized inhomogeneous complex:

`0 → H¹(G/N,M^N) → H¹(G,M) → H¹(N,M)^{G/N} → H²(G/N,M^N) → H²(G,M)`.

All four arrows are the concrete maps defined above: quotient precomposition and invariant
inclusion, literal subgroup restriction, the descended coboundary transgression, and degree-two
quotient precomposition. -/
theorem fiveTerm_exact : FiveTermExact N M where
  inflation_injective := inflationH1_injective N M
  exact_at_H1G := inflation_fixedRestriction_exact N M
  exact_at_H1N := fixedRestriction_transgression_exact N M
  exact_at_H2Q := fixedTransgression_inflation_exact N M

/-- The six-term exact fragment

`0 → H¹(G/N,Mᴺ) → H¹(G,M) → H¹(N,M)^{G/N} → H²(G/N,Mᴺ)
  → H²(G,M) → H²(N,M)`

under the classical edge hypothesis `H¹(N,M)=0`. -/
theorem sixTerm_exact_of_H1_zero
    (hH1 : ∀ x : H1 (Rep.res N.subtype M), x = 0) :
    SixTermExactOfH1Zero N M where
  toFiveTermExact := fiveTerm_exact N M
  exact_at_H2G := inflation_restrictionH2_exact_of_H1_zero N M hH1

end InfRes
end Inhomogeneous

end

end NU.LCFT
