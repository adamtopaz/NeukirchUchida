import Submission.NU.LCFT.Basic.Norm
import Submission.NU.LCFT.Cohomology.ShapiroDelta

/-!
# Normalized inhomogeneous cohomology in degrees zero, one, and two

Mathlib already provides an inhomogeneous complex, but its public low-degree API is categorical.
For the carry cocycle and Tate row-sum calculations we keep the following normalized concrete
complex.  Comparison is asserted only in degrees `0`, `1`, and `2`.

## Comparison-layer design

Restriction and inflation are literal precomposition.  Corestriction is represented by bundled
low-degree maps together with comparison squares; this avoids committing later files to a choice
of coset transversal.  These are the intended design liberties in the inhomogeneous-vs-Mathlib
bridge.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory

namespace Inhomogeneous

variable {G H : Type} [Group G] [Group H]

/-- Degree-zero inhomogeneous cochains. -/
abbrev C0 (M : Rep ℤ G) := M

/-- Degree-one inhomogeneous cochains. -/
abbrev C1 (M : Rep ℤ G) := G → M

/-- Degree-two inhomogeneous cochains. -/
abbrev C2 (M : Rep ℤ G) := G → G → M

/-- Degree-three inhomogeneous cochains, needed as the target of `d₂`. -/
abbrev C3 (M : Rep ℤ G) := G → G → G → M

/-- The differential `d⁰a(g) = g • a - a`. -/
def d0 (M : Rep ℤ G) : C0 M →+ C1 M where
  toFun a g := M.ρ g a - a
  map_zero' := by ext; simp
  map_add' a b := by
    ext g
    change M.ρ g (a + b) - (a + b) =
      (M.ρ g a - a) + (M.ρ g b - b)
    rw [map_add]
    abel

/-- The differential `d¹b(g,h) = g • b(h) - b(gh) + b(g)`. -/
def d1 (M : Rep ℤ G) : C1 M →+ C2 M where
  toFun b g h := M.ρ g (b h) - b (g * h) + b g
  map_zero' := by ext; simp
  map_add' a b := by
    ext g h
    change M.ρ g (a h + b h) - (a (g * h) + b (g * h)) + (a g + b g) =
      (M.ρ g (a h) - a (g * h) + a g) +
        (M.ρ g (b h) - b (g * h) + b g)
    rw [map_add]
    abel

/-- The differential `d²c(g,h,t) = g • c(h,t) - c(gh,t) + c(g,ht) - c(g,h)`. -/
def d2 (M : Rep ℤ G) : C2 M →+ C3 M where
  toFun c g h t := M.ρ g (c h t) - c (g * h) t + c g (h * t) - c g h
  map_zero' := by ext; simp
  map_add' a b := by
    ext g h t
    change M.ρ g (a h t + b h t) - (a (g * h) t + b (g * h) t) +
        (a g (h * t) + b g (h * t)) - (a g h + b g h) =
      (M.ρ g (a h t) - a (g * h) t + a g (h * t) - a g h) +
        (M.ρ g (b h t) - b (g * h) t + b g (h * t) - b g h)
    rw [map_add]
    abel

/-- Normalized one-cochains vanish at the identity. -/
def normalized1 (M : Rep ℤ G) : AddSubgroup (C1 M) where
  carrier := {b | b 1 = 0}
  zero_mem' := rfl
  add_mem' ha hb := by simpa using congrArg₂ (· + ·) ha hb
  neg_mem' ha := by simpa using congrArg Neg.neg ha

/-- Normalized two-cochains vanish if either argument is the identity. -/
def normalized2 (M : Rep ℤ G) : AddSubgroup (C2 M) where
  carrier := {c | (∀ g, c 1 g = 0) ∧ (∀ g, c g 1 = 0)}
  zero_mem' := ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  add_mem' ha hb :=
    ⟨fun g ↦ by rw [Pi.add_apply, Pi.add_apply, ha.1 g, hb.1 g, add_zero],
      fun g ↦ by rw [Pi.add_apply, Pi.add_apply, ha.2 g, hb.2 g, add_zero]⟩
  neg_mem' ha :=
    ⟨fun g ↦ by rw [Pi.neg_apply, Pi.neg_apply, ha.1 g, neg_zero],
      fun g ↦ by rw [Pi.neg_apply, Pi.neg_apply, ha.2 g, neg_zero]⟩

/-- Normalized one-cocycles. -/
def cocycles1 (M : Rep ℤ G) : AddSubgroup (C1 M) :=
  (d1 M).ker ⊓ normalized1 M

/-- One-coboundaries, as a subgroup of normalized one-cocycles. -/
def coboundaries1 (M : Rep ℤ G) : AddSubgroup (cocycles1 M) :=
  (d0 M).range.comap (cocycles1 M).subtype

/-- Normalized two-cocycles. -/
def cocycles2 (M : Rep ℤ G) : AddSubgroup (C2 M) :=
  (d2 M).ker ⊓ normalized2 M

/-- Two-coboundaries, as a subgroup of normalized two-cocycles. -/
def coboundaries2 (M : Rep ℤ G) : AddSubgroup (cocycles2 M) :=
  (d1 M).range.comap (cocycles2 M).subtype

/-- The concrete subgroup of invariant elements. -/
def invariants0 (M : Rep ℤ G) : AddSubgroup M where
  carrier := {a | ∀ g, M.ρ g a = a}
  zero_mem' := fun g ↦ by simp
  add_mem' ha hb := fun g ↦ by rw [map_add, ha g, hb g]
  neg_mem' ha := fun g ↦ by rw [map_neg, ha g]

/-- Concrete normalized `H⁰`. -/
abbrev H0 (M : Rep ℤ G) := invariants0 M

/-- Concrete normalized `H¹ = Z¹/B¹`. -/
abbrev H1 (M : Rep ℤ G) := cocycles1 M ⧸ coboundaries1 M

/-- Concrete normalized `H² = Z²/B²`. -/
abbrev H2 (M : Rep ℤ G) := cocycles2 M ⧸ coboundaries2 M

/-- Restriction (and, for a quotient homomorphism, inflation) on zero-cochains. -/
def restrictC0 (f : H →* G) (M : Rep ℤ G) : C0 M →+ C0 (Rep.res f M) :=
  AddMonoidHom.id M

/-- Restriction (and, for a quotient homomorphism, inflation) on one-cochains. -/
def restrictC1 (f : H →* G) (M : Rep ℤ G) : C1 M →+ C1 (Rep.res f M) where
  toFun b h := b (f h)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction (and, for a quotient homomorphism, inflation) on two-cochains. -/
def restrictC2 (f : H →* G) (M : Rep ℤ G) : C2 M →+ C2 (Rep.res f M) where
  toFun c h₁ h₂ := c (f h₁) (f h₂)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **C02**, Remark `rem:tate-naturality`: restriction commutes with `d⁰`. -/
theorem restrictC0_d0 (f : H →* G) (M : Rep ℤ G) (a : C0 M) :
    restrictC1 f M (d0 M a) = d0 (Rep.res f M) (restrictC0 f M a) := by
  ext h
  simp [restrictC0, restrictC1, d0, Rep.res]

/-- **C02**, Remark `rem:tate-naturality`: restriction commutes with `d¹`. -/
theorem restrictC1_d1 (f : H →* G) (M : Rep ℤ G) (b : C1 M) :
    restrictC2 f M (d1 M b) = d1 (Rep.res f M) (restrictC1 f M b) := by
  ext h₁ h₂
  simp [restrictC1, restrictC2, d1, Rep.res]

/-- **C02**, Remark `rem:tate-naturality`: restriction commutes with `d²`. -/
theorem restrictC2_d2 (f : H →* G) (M : Rep ℤ G) (c : C2 M) :
    (fun h₁ h₂ h₃ ↦ d2 M c (f h₁) (f h₂) (f h₃)) =
      d2 (Rep.res f M) (restrictC2 f M c) := by
  ext h₁ h₂ h₃
  simp [restrictC2, d2, Rep.res]

/-- Restriction on normalized one-cocycles, induced by literal cochain precomposition. -/
def restrictCocycles1 (f : H →* G) (M : Rep ℤ G) :
    cocycles1 M →+ cocycles1 (Rep.res f M) where
  toFun b := ⟨restrictC1 f M b, ⟨by
    change d1 (Rep.res f M) (restrictC1 f M b) = 0
    have hb := b.2.1
    change d1 M b = 0 at hb
    rw [← restrictC1_d1, hb]
    rfl, by
    change b.1 (f 1) = 0
    have hb := b.2.2
    change b.1 1 = 0 at hb
    simpa using hb⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction on normalized two-cocycles, induced by literal cochain precomposition. -/
def restrictCocycles2 (f : H →* G) (M : Rep ℤ G) :
    cocycles2 M →+ cocycles2 (Rep.res f M) where
  toFun c := ⟨restrictC2 f M c, ⟨by
    change d2 (Rep.res f M) (restrictC2 f M c) = 0
    have hc := c.2.1
    change d2 M c = 0 at hc
    rw [← restrictC2_d2, hc]
    rfl, ⟨fun h => by
      change c.1 (f 1) (f h) = 0
      have hc := c.2.2
      change (∀ g, c.1 1 g = 0) ∧ (∀ g, c.1 g 1 = 0) at hc
      simpa using hc.1 (f h), fun h => by
      change c.1 (f h) (f 1) = 0
      have hc := c.2.2
      change (∀ g, c.1 1 g = 0) ∧ (∀ g, c.1 g 1 = 0) at hc
      simpa using hc.2 (f h)⟩⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction on concrete `H⁰`; on representatives it is the identity coefficient map. -/
def restrictionH0 (f : H →* G) (M : Rep ℤ G) :
    H0 M →+ H0 (Rep.res f M) where
  toFun x := ⟨restrictC0 f M x, fun h => x.2 (f h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction on concrete `H¹`, quotienting literal precomposition of one-cocycles. -/
def restrictionH1 (f : H →* G) (M : Rep ℤ G) :
    H1 M →+ H1 (Rep.res f M) :=
  QuotientAddGroup.map (coboundaries1 M) (coboundaries1 (Rep.res f M))
    (restrictCocycles1 f M) (by
      rintro b ⟨a, ha⟩
      refine ⟨restrictC0 f M a, ?_⟩
      change d0 (Rep.res f M) (restrictC0 f M a) = restrictC1 f M b
      rw [← restrictC0_d0, ha]
      rfl)

/-- Restriction on concrete `H²`, quotienting literal precomposition of two-cocycles. -/
def restrictionH2 (f : H →* G) (M : Rep ℤ G) :
    H2 M →+ H2 (Rep.res f M) :=
  QuotientAddGroup.map (coboundaries2 M) (coboundaries2 (Rep.res f M))
    (restrictCocycles2 f M) (by
      rintro c ⟨b, hb⟩
      refine ⟨restrictC1 f M b, ?_⟩
      change d1 (Rep.res f M) (restrictC1 f M b) = restrictC2 f M c
      rw [← restrictC1_d1, hb]
      rfl)

@[simp]
theorem restrictionH1_mk (f : H →* G) (M : Rep ℤ G) (b : cocycles1 M) :
    restrictionH1 f M (QuotientAddGroup.mk' (coboundaries1 M) b) =
      QuotientAddGroup.mk' (coboundaries1 (Rep.res f M)) (restrictCocycles1 f M b) := rfl

@[simp]
theorem restrictionH2_mk (f : H →* G) (M : Rep ℤ G) (c : cocycles2 M) :
    restrictionH2 f M (QuotientAddGroup.mk' (coboundaries2 M) c) =
      QuotientAddGroup.mk' (coboundaries2 (Rep.res f M)) (restrictCocycles2 f M c) := rfl

end Inhomogeneous

section MultiplicativeDictionary

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The single additive representation used for multiplicative coefficients. -/
abbrev MulRep := Rep.ofAlgebraAutOnUnits K L

/-- **C01 (M1)**: addition in `Additive (Units L)` is multiplication of units. -/
theorem mulRep_add (x y : Units L) :
    Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y := rfl

/-- **C01 (M2)**: zero in `Additive (Units L)` is the unit `1`. -/
theorem mulRep_zero :
    (0 : Additive (Units L)) = Additive.ofMul (1 : Units L) := rfl

/--
**C01 (M3)**, Lemma `lem:hilbert90` dictionary: the additive representation norm is the field
norm, after embedding the latter back into `L`.
-/
theorem mulRep_norm [IsGalois K L] (x : Units L) :
    Additive.toMul ((MulRep K L).norm.hom (Additive.ofMul x)) =
      Units.map (algebraMap K L) (normUnitsHom K L x) := by
  apply Units.ext
  exact groupCohomology.norm_ofAlgebraAutOnUnits_eq x

/--
**C01 (M4)**: invariant additive units identify with additive units of the fixed field.
-/
theorem mulRep_invariants [IsGalois K L] :
    Nonempty ((MulRep K L).ρ.invariants ≃+ Additive (Units K)) := by
  let f₀ : Additive (Units K) →+ Additive (Units L) :=
    (Units.map (algebraMap K L).toMonoidHom).toAdditive
  let f : Additive (Units K) →+ (MulRep K L).ρ.invariants :=
    { toFun := fun x => ⟨f₀ x, by
          intro σ
          change Additive.ofMul (Units.map σ.toRingEquiv.toRingHom.toMonoidHom
            (Units.map (algebraMap K L).toMonoidHom x.toMul)) =
            Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x.toMul)
          apply Additive.toMul.injective
          apply Units.ext
          simp⟩
      map_zero' := Subtype.ext f₀.map_zero
      map_add' := fun x y => Subtype.ext (f₀.map_add x y) }
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Additive.toMul.injective
    apply Units.ext
    apply (algebraMap K L).injective
    have h' := congrArg (fun z : (MulRep K L).ρ.invariants =>
      ((show Units L from Additive.toMul z.1) : L)) h
    exact h'
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hfixed : ∀ σ : L ≃ₐ[K] L,
        σ ((show Units L from Additive.toMul x) : L) =
          ((show Units L from Additive.toMul x) : L) := by
      intro σ
      have h := congrArg (fun z : Additive (Units L) => ((z.toMul : Units L) : L)) (hx σ)
      exact h
    rcases (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L)
      ((show Units L from Additive.toMul x) : L)).2 hfixed with ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyz
      rw [hyz, map_zero] at hy
      exact (show Units L from Additive.toMul x).ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    exact hy
  exact ⟨(AddEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm⟩

/-- The additive augmentation subgroup generated by `σ(x) - x`. -/
def mulRepAugmentation : AddSubgroup (Additive (Units L)) :=
  AddSubgroup.closure {z | ∃ (σ : L ≃ₐ[K] L) (x : Units L),
    z = Additive.ofMul (Units.map σ.toRingEquiv.toRingHom x) - Additive.ofMul x}

/-- Its multiplicative counterpart, generated by `σ(x)/x`. -/
def multiplicativeAugmentation : Subgroup (Units L) :=
  Subgroup.closure {z | ∃ (σ : L ≃ₐ[K] L) (x : Units L),
    z = Units.map σ.toRingEquiv.toRingHom x / x}

/-- **C01 (M5)**: the additive and multiplicative augmentation subgroups agree. -/
theorem mem_mulRepAugmentation_iff (x : Units L) :
    Additive.ofMul x ∈ mulRepAugmentation K L ↔
      x ∈ multiplicativeAugmentation K L := by
  have h : mulRepAugmentation K L = (multiplicativeAugmentation K L).toAddSubgroup := by
    rw [multiplicativeAugmentation, Subgroup.toAddSubgroup_closure]
    unfold mulRepAugmentation
    congr 1
  rw [h]
  rfl

end MultiplicativeDictionary

section Comparison

variable {G H : Type} [Group G] [Group H]

/--
**C01**, beginning of Part II: normalized inhomogeneous `H⁰` agrees with Mathlib group
cohomology.
-/
noncomputable def comparisonH0 (M : Rep ℤ G) :
    Inhomogeneous.H0 M ≃+ groupCohomology.H0 M := by
  let e : Inhomogeneous.H0 M ≃+ groupCohomology.H0 M :=
    { toFun := fun x => (groupCohomology.H0Iso M).inv ⟨x, x.2⟩
      invFun := fun x => ⟨(groupCohomology.H0Iso M).hom x,
        (groupCohomology.H0Iso M).hom x |>.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact congr_arg Subtype.val
          ((groupCohomology.H0Iso M).inv_hom_id_apply ⟨x, x.2⟩)
      right_inv := fun x => (groupCohomology.H0Iso M).hom_inv_id_apply x
      map_add' := fun x y => by
        rw [← map_add]
        rfl }
  exact e

/-- **C01**, beginning of Part II: normalized inhomogeneous `H¹` agrees with Mathlib. -/
noncomputable def comparisonH1 (M : Rep ℤ G) :
    Inhomogeneous.H1 M ≃+ groupCohomology.H1 M := by
  let ec : Inhomogeneous.cocycles1 M →+ groupCohomology.cocycles₁ M :=
    { toFun := fun x => ⟨x, by
          rw [groupCohomology.mem_cocycles₁_def]
          intro g h
          exact congr_fun (congr_fun x.2.1 g) h⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : Inhomogeneous.cocycles1 M →+ groupCohomology.H1 M :=
    (groupCohomology.H1π M).hom.toAddMonoidHom.comp ec
  have hf : Function.Surjective f := by
    intro y
    rcases (ModuleCat.epi_iff_surjective (groupCohomology.H1π M)).1 inferInstance y with
      ⟨z, rfl⟩
    let x : Inhomogeneous.cocycles1 M := ⟨z, ⟨by
      ext g h
      exact (groupCohomology.mem_cocycles₁_def z).1 z.2 g h,
      groupCohomology.cocycles₁_map_one z⟩⟩
    refine ⟨x, ?_⟩
    change groupCohomology.H1π M (ec x) = groupCohomology.H1π M z
    congr 1
  have hker : Inhomogeneous.coboundaries1 M = f.ker := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      apply AddMonoidHom.mem_ker.mpr
      apply (groupCohomology.H1π_eq_zero_iff _).2
      refine ⟨a, ?_⟩
      ext g
      exact congr_fun ha g
    · intro hx
      have hx' := (groupCohomology.H1π_eq_zero_iff (ec x)).1
        (AddMonoidHom.mem_ker.mp hx)
      rcases hx' with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      ext g
      exact congr_fun ha g
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- **C01**, beginning of Part II: normalized inhomogeneous `H²` agrees with Mathlib. -/
noncomputable def comparisonH2 (M : Rep ℤ G) :
    Inhomogeneous.H2 M ≃+ groupCohomology.H2 M := by
  let ec : Inhomogeneous.cocycles2 M →+ groupCohomology.cocycles₂ M :=
    { toFun := fun x => ⟨fun p => x.1 p.1 p.2, by
          rw [groupCohomology.mem_cocycles₂_def]
          intro g h t
          exact congr_fun (congr_fun (congr_fun x.2.1 g) h) t⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : Inhomogeneous.cocycles2 M →+ groupCohomology.H2 M :=
    (groupCohomology.H2π M).hom.toAddMonoidHom.comp ec
  have hf : Function.Surjective f := by
    intro y
    rcases (ModuleCat.epi_iff_surjective (groupCohomology.H2π M)).1 inferInstance y with
      ⟨z, rfl⟩
    let a : M := z (1, 1)
    let b : G → M := fun _ => a
    let zn : G × G → M := fun p => z p - groupCohomology.d₁₂ M b p
    have hzn : zn ∈ groupCohomology.cocycles₂ M := by
      exact Submodule.sub_mem _ z.2 (groupCohomology.d₁₂_apply_mem_cocycles₂ b)
    let x : Inhomogeneous.cocycles2 M := ⟨fun g h => zn (g, h), ⟨by
      ext g h t
      exact (groupCohomology.mem_cocycles₂_def zn).1 hzn g h t,
      ⟨fun g => by
          change z (1, g) - (M.ρ 1 (b g) - b (1 * g) + b 1) = 0
          rw [groupCohomology.cocycles₂_map_one_fst z g]
          simp [b, a],
        fun g => by
          change z (g, 1) - (M.ρ g (b 1) - b (g * 1) + b g) = 0
          rw [groupCohomology.cocycles₂_map_one_snd z g]
          simp [b, a]⟩⟩⟩
    refine ⟨x, ?_⟩
    change groupCohomology.H2π M (ec x) = groupCohomology.H2π M z
    rw [groupCohomology.H2π_eq_iff]
    refine ⟨-b, ?_⟩
    ext p
    dsimp [ec, x, zn, groupCohomology.d₁₂]
    simp
    abel
  have hker : Inhomogeneous.coboundaries2 M = f.ker := by
    ext x
    constructor
    · rintro ⟨b, hb⟩
      apply AddMonoidHom.mem_ker.mpr
      apply (groupCohomology.H2π_eq_zero_iff _).2
      refine ⟨b, ?_⟩
      ext p
      exact congr_fun (congr_fun hb p.1) p.2
    · intro hx
      have hx' := (groupCohomology.H2π_eq_zero_iff (ec x)).1
        (AddMonoidHom.mem_ker.mp hx)
      rcases hx' with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      ext g h
      exact congr_fun hb (g, h)
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- The named degree-zero construction witnesses the comparison existence statement. -/
theorem comparisonH0_exists (M : Rep ℤ G) :
    Nonempty (Inhomogeneous.H0 M ≃+ groupCohomology.H0 M) :=
  ⟨comparisonH0 M⟩

/-- The named degree-one construction witnesses the comparison existence statement. -/
theorem comparisonH1_exists (M : Rep ℤ G) :
    Nonempty (Inhomogeneous.H1 M ≃+ groupCohomology.H1 M) :=
  ⟨comparisonH1 M⟩

/-- The named degree-two construction witnesses the comparison existence statement. -/
theorem comparisonH2_exists (M : Rep ℤ G) :
    Nonempty (Inhomogeneous.H2 M ≃+ groupCohomology.H2 M) :=
  ⟨comparisonH2 M⟩

/-- Mathlib's restriction map, exposed as an additive homomorphism. -/
noncomputable def mathlibRestriction (f : H →* G) (M : Rep ℤ G) (n : ℕ) :
    groupCohomology M n →+ groupCohomology (Rep.res f M) n :=
  (groupCohomology.map f (𝟙 _) n).hom.toAddMonoidHom

/--
Restriction maps in degrees `0,1,2`.  The equality fields rule out transported or zero-map
substitutes: the concrete maps are the quotient maps induced by literal cochain precomposition,
and the Mathlib maps are `groupCohomology.map`.
-/
structure RestrictionComparisonData (f : H →* G) (M : Rep ℤ G) where
  /-- Concrete restriction in degree zero. -/
  map0 : Inhomogeneous.H0 M →+ Inhomogeneous.H0 (Rep.res f M)
  /-- `map0` is the named coefficient/precomposition restriction. -/
  map0_eq_precomposition : map0 = Inhomogeneous.restrictionH0 f M
  /-- Concrete restriction in degree one. -/
  map1 : Inhomogeneous.H1 M →+ Inhomogeneous.H1 (Rep.res f M)
  /-- `map1` is induced by literal precomposition of normalized one-cochains. -/
  map1_eq_precomposition : map1 = Inhomogeneous.restrictionH1 f M
  /-- Concrete restriction in degree two. -/
  map2 : Inhomogeneous.H2 M →+ Inhomogeneous.H2 (Rep.res f M)
  /-- `map2` is induced by literal precomposition of normalized two-cochains. -/
  map2_eq_precomposition : map2 = Inhomogeneous.restrictionH2 f M
  /-- Mathlib restriction in degree zero. -/
  mathlibMap0 : groupCohomology.H0 M →+ groupCohomology.H0 (Rep.res f M)
  /-- The degree-zero Mathlib map is its functoriality API, not an arbitrary map. -/
  mathlibMap0_eq_restriction : mathlibMap0 = mathlibRestriction f M 0
  /-- Mathlib restriction in degree one. -/
  mathlibMap1 : groupCohomology.H1 M →+ groupCohomology.H1 (Rep.res f M)
  /-- The degree-one Mathlib map is its functoriality API, not an arbitrary map. -/
  mathlibMap1_eq_restriction : mathlibMap1 = mathlibRestriction f M 1
  /-- Mathlib restriction in degree two. -/
  mathlibMap2 : groupCohomology.H2 M →+ groupCohomology.H2 (Rep.res f M)
  /-- The degree-two Mathlib map is its functoriality API, not an arbitrary map. -/
  mathlibMap2_eq_restriction : mathlibMap2 = mathlibRestriction f M 2
  /-- The fixed degree-zero comparison commutes with the named restriction maps. -/
  commutes0 : ∀ x, comparisonH0 _ (Inhomogeneous.restrictionH0 f M x) =
    mathlibRestriction f M 0 (comparisonH0 M x)
  /-- The fixed degree-one comparison commutes with the named restriction maps. -/
  commutes1 : ∀ x, comparisonH1 _ (Inhomogeneous.restrictionH1 f M x) =
    mathlibRestriction f M 1 (comparisonH1 M x)
  /-- The fixed degree-two comparison commutes with the named restriction maps. -/
  commutes2 : ∀ x, comparisonH2 _ (Inhomogeneous.restrictionH2 f M x) =
    mathlibRestriction f M 2 (comparisonH2 M x)

/--
**C02**, Remark `rem:tate-naturality`: the named restriction/precomposition maps and Mathlib's
restriction maps commute with the fixed comparisons.  Inflation is the same construction when
`f` is a quotient homomorphism.
-/
noncomputable def restrictionComparison (f : H →* G) (M : Rep ℤ G) :
    RestrictionComparisonData f M := by
  refine {
    map0 := Inhomogeneous.restrictionH0 f M
    map0_eq_precomposition := rfl
    map1 := Inhomogeneous.restrictionH1 f M
    map1_eq_precomposition := rfl
    map2 := Inhomogeneous.restrictionH2 f M
    map2_eq_precomposition := rfl
    mathlibMap0 := mathlibRestriction f M 0
    mathlibMap0_eq_restriction := rfl
    mathlibMap1 := mathlibRestriction f M 1
    mathlibMap1_eq_restriction := rfl
    mathlibMap2 := mathlibRestriction f M 2
    mathlibMap2_eq_restriction := rfl
    commutes0 := ?_
    commutes1 := ?_
    commutes2 := ?_ }
  · intro x
    letI : Module ℤ M := M.hV2
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.H0Iso (Rep.res f M)).hom).1 inferInstance
    apply Subtype.ext
    let y : (Rep.res f M).ρ.invariants := ⟨x.1, fun h => x.2 (f h)⟩
    let z : M.ρ.invariants := ⟨x.1, x.2⟩
    have hy := congrArg Subtype.val
      ((groupCohomology.H0Iso (Rep.res f M)).inv_hom_id_apply y)
    have hz := congrArg Subtype.val
      ((groupCohomology.H0Iso M).inv_hom_id_apply z)
    have hm := ConcreteCategory.congr_hom
      (groupCohomology.map_H0Iso_hom_f f (𝟙 _)) (comparisonH0 M x)
    have hm' :
        ((groupCohomology.H0Iso (Rep.res f M)).hom
          (groupCohomology.map f (𝟙 _) 0 (comparisonH0 M x))).1 =
        ((groupCohomology.H0Iso M).hom (comparisonH0 M x)).1 := by
      exact hm
    simpa [comparisonH0, Inhomogeneous.restrictionH0,
      Inhomogeneous.restrictC0, mathlibRestriction, y, z] using
        hy.trans (hz.symm.trans hm'.symm)
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change comparisonH1 _ (Inhomogeneous.restrictionH1 f M
        (QuotientAddGroup.mk' (Inhomogeneous.coboundaries1 M) x)) =
          mathlibRestriction f M 1
            (comparisonH1 M (QuotientAddGroup.mk' (Inhomogeneous.coboundaries1 M) x))
      rw [Inhomogeneous.restrictionH1_mk]
      change groupCohomology.H1π (Rep.res f M) _ =
        groupCohomology.map f (𝟙 _) 1 (groupCohomology.H1π M _)
      rw [groupCohomology.H1π_comp_map_apply]
      rfl
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change comparisonH2 _ (Inhomogeneous.restrictionH2 f M
        (QuotientAddGroup.mk' (Inhomogeneous.coboundaries2 M) x)) =
          mathlibRestriction f M 2
            (comparisonH2 M (QuotientAddGroup.mk' (Inhomogeneous.coboundaries2 M) x))
      rw [Inhomogeneous.restrictionH2_mk]
      change groupCohomology.H2π (Rep.res f M) _ =
        groupCohomology.map f (𝟙 _) 2 (groupCohomology.H2π M _)
      rw [groupCohomology.H2π_comp_map_apply]
      rfl

/-- Existence wrapper for the named restriction comparison data. -/
theorem restrictionComparison_exists (f : H →* G) (M : Rep ℤ G) :
    Nonempty (RestrictionComparisonData f M) :=
  ⟨restrictionComparison f M⟩

/--
Mathlib corestriction for a finite-index subgroup.  This is Shapiro's inverse followed by the
cohomology map induced by the finite-index `Coind ≅ Ind` counit (the transfer/trace map).
-/
noncomputable def mathlibCorestriction (S : Subgroup G) [S.FiniteIndex]
    (M : Rep ℤ G) (n : ℕ) :
    groupCohomology (Rep.res S.subtype M) n ⟶ groupCohomology M n := by
  classical
  exact (groupCohomology.coindIso (Rep.res S.subtype M) n).inv ≫
    groupCohomology.map (.id G) ((Rep.coindResAdjunction ℤ S).counit.app M) n

/-- Concrete degree-one corestriction transported along the fixed, constructed comparisons. -/
noncomputable def corestrictionH1 (S : Subgroup G) [S.FiniteIndex] (M : Rep ℤ G) :
    Inhomogeneous.H1 (Rep.res S.subtype M) →+ Inhomogeneous.H1 M :=
  (comparisonH1 M).symm.toAddMonoidHom.comp
    ((mathlibCorestriction S M 1).hom.toAddMonoidHom.comp
      (comparisonH1 (Rep.res S.subtype M)).toAddMonoidHom)

/-- Concrete degree-two corestriction transported along the fixed, constructed comparisons. -/
noncomputable def corestrictionH2 (S : Subgroup G) [S.FiniteIndex] (M : Rep ℤ G) :
    Inhomogeneous.H2 (Rep.res S.subtype M) →+ Inhomogeneous.H2 M :=
  (comparisonH2 M).symm.toAddMonoidHom.comp
    ((mathlibCorestriction S M 2).hom.toAddMonoidHom.comp
      (comparisonH2 (Rep.res S.subtype M)).toAddMonoidHom)

/--
Corestriction data tied to Mathlib's finite-index transfer, the fixed comparisons, and the
connecting homomorphism from degree one to degree two.
-/
structure CorestrictionComparisonData (S : Subgroup G) [S.FiniteIndex] (M : Rep ℤ G) where
  /-- Concrete corestriction in degree one. -/
  map1 : Inhomogeneous.H1 (Rep.res S.subtype M) →+ Inhomogeneous.H1 M
  /-- The concrete degree-one map is the named transported corestriction. -/
  map1_eq_corestriction : map1 = corestrictionH1 S M
  /-- Concrete corestriction in degree two. -/
  map2 : Inhomogeneous.H2 (Rep.res S.subtype M) →+ Inhomogeneous.H2 M
  /-- The concrete degree-two map is the named transported corestriction. -/
  map2_eq_corestriction : map2 = corestrictionH2 S M
  /-- The corresponding Mathlib-side degree-one map. -/
  mathlibMap1 : groupCohomology.H1 (Rep.res S.subtype M) →+ groupCohomology.H1 M
  /-- The degree-one Mathlib map is exactly the finite-index transfer. -/
  mathlibMap1_eq_corestriction :
    mathlibMap1 = (mathlibCorestriction S M 1).hom.toAddMonoidHom
  /-- The corresponding Mathlib-side degree-two map. -/
  mathlibMap2 : groupCohomology.H2 (Rep.res S.subtype M) →+ groupCohomology.H2 M
  /-- The degree-two Mathlib map is exactly the finite-index transfer. -/
  mathlibMap2_eq_corestriction :
    mathlibMap2 = (mathlibCorestriction S M 2).hom.toAddMonoidHom
  /-- The fixed comparison commutes with corestriction in degree one. -/
  commutes1 : ∀ x, comparisonH1 M (corestrictionH1 S M x) =
    mathlibCorestriction S M 1 (comparisonH1 _ x)
  /-- The fixed comparison commutes with corestriction in degree two. -/
  commutes2 : ∀ x, comparisonH2 M (corestrictionH2 S M x) =
    mathlibCorestriction S M 2 (comparisonH2 _ x)
  /--
  Corestriction commutes with the `H¹ → H²` connecting map for every short exact sequence.
  The upper connecting map is formed after literal restriction of the sequence to `S`.
  -/
  connecting_commutes : ∀ (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact),
    groupCohomology.δ ((Rep.shortExact_res S.subtype).2 hX) 1 2 rfl ≫
        mathlibCorestriction S X.X₁ 2 =
      mathlibCorestriction S X.X₃ 1 ≫ groupCohomology.δ hX 1 2 rfl

private theorem coindCounit_connecting (S : Subgroup G) [S.FiniteIndex]
    (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact) :
    let C := X.map (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor ℤ S.subtype)
    let hC : C.ShortExact := by
      change (X.map (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor ℤ S.subtype)).ShortExact
      rw [X.map_comp]
      exact ((Rep.shortExact_res S.subtype).2 hX).map_of_exact
        (Rep.coindFunctor ℤ S.subtype)
    let ε1 : Rep.coind S.subtype (Rep.res S.subtype X.X₁) ⟶ X.X₁ := by
      classical exact (Rep.coindResAdjunction ℤ S).counit.app X.X₁
    let ε3 : Rep.coind S.subtype (Rep.res S.subtype X.X₃) ⟶ X.X₃ := by
      classical exact (Rep.coindResAdjunction ℤ S).counit.app X.X₃
    groupCohomology.δ hC 1 2 rfl ≫ groupCohomology.map (.id G) ε1 2 =
      groupCohomology.map (.id G) ε3 1 ≫ groupCohomology.δ hX 1 2 rfl := by
  classical
  dsimp only
  exact groupCohomology.δ_naturality (by
    rw [X.map_comp]
    exact ((Rep.shortExact_res S.subtype).2 hX).map_of_exact
      (Rep.coindFunctor ℤ S.subtype)) hX
    (X.mapNatTrans (Rep.coindResAdjunction ℤ S).counit) 1 2 rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
**C02**, Remark `rem:tate-naturality`: the named finite-index corestriction commutes with the
fixed low-degree comparisons and with connecting homomorphisms.
-/
noncomputable def corestrictionComparison (S : Subgroup G) [S.FiniteIndex] (M : Rep ℤ G) :
    CorestrictionComparisonData S M := by
  refine {
    map1 := corestrictionH1 S M
    map1_eq_corestriction := rfl
    map2 := corestrictionH2 S M
    map2_eq_corestriction := rfl
    mathlibMap1 := (mathlibCorestriction S M 1).hom.toAddMonoidHom
    mathlibMap1_eq_corestriction := rfl
    mathlibMap2 := (mathlibCorestriction S M 2).hom.toAddMonoidHom
    mathlibMap2_eq_corestriction := rfl
    commutes1 := ?_
    commutes2 := ?_
    connecting_commutes := ?_ }
  · intro x
    exact (comparisonH1 M).apply_symm_apply _
  · intro x
    exact (comparisonH2 M).apply_symm_apply _
  · intro X hX
    dsimp [mathlibCorestriction]
    simp only [Category.assoc]
    slice_lhs 1 3 =>
      rw [← Category.assoc]
      erw [groupCohomology.coindIso_inv_δ_res S hX]
    slice_lhs 2 3 => erw [coindCounit_connecting S X hX]

/-- Existence wrapper for the named corestriction comparison data. -/
theorem corestrictionComparison_exists (S : Subgroup G) [S.FiniteIndex] (M : Rep ℤ G) :
    Nonempty (CorestrictionComparisonData S M) :=
  ⟨corestrictionComparison S M⟩

end Comparison

end

end NU.LCFT
