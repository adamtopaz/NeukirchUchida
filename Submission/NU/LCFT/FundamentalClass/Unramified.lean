import Submission.NU.LCFT.FundamentalClass.Cyclic
import Submission.NU.Chebotarev.Frobenius

/-!
# The unramified carry cocycle

The carry cocycle in this file has values in the actual representation `MulRep K L`; it is not a
cocycle in an unrelated trivial coefficient module.  Arithmetic Frobenius data identify the
actual Galois group with the appropriate cyclic group.  Tower and base-change maps are built from
pinned group homomorphisms and coefficient morphisms and are transported through the proved
`comparisonH2` layer.
-/

namespace NU.LCFT

noncomputable section

open CategoryTheory
open scoped ValuativeRel

/--
**F07–F09**, equations (4.2)–(4.3) and Propositions `prop:fundamental-inflation`/
`prop:fundamental-restriction`: push a two-cochain along the actual group/coefficient maps.
-/
def transportedC2 {G H : Type} [Group G] [Group H]
    {M : Rep ℤ G} {N : Rep ℤ H} (f : H →* G) (φ : Rep.res f M ⟶ N) :
    Inhomogeneous.C2 M →+ Inhomogeneous.C2 N where
  toFun a h₁ h₂ := φ.hom (a (f h₁) (f h₂))
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/--
**F07–F09**, equations (4.2)–(4.3) and the fundamental-class compatibility propositions: the
concrete `H²` map obtained from Mathlib's actual functorial map and the fixed **C01**
comparisons.  This is the only inflation/restriction-with-coefficients map used below.
-/
noncomputable def transportedH2 {G H : Type} [Group G] [Group H]
    {M : Rep ℤ G} {N : Rep ℤ H} (f : H →* G) (φ : Rep.res f M ⟶ N) :
    Inhomogeneous.H2 M →+ Inhomogeneous.H2 N :=
  (comparisonH2 N).symm.toAddMonoidHom.comp
    ((groupCohomology.map f φ 2).hom.toAddMonoidHom.comp
      (comparisonH2 M).toAddMonoidHom)

/-- **F06**, Lemma `lem:unramified-class`: the carry in `ZMod n`. -/
def carryExponent (n : ℕ) [NeZero n] (r s : ZMod n) : ℕ :=
  if r.val + s.val < n then 0 else 1

/-- **F06**, Lemma `lem:unramified-class`: the actual carry representation. -/
abbrev CarryRep (K L : Type) [Field K] [Field L] [Algebra K L] := MulRep K L

/-- **F06**, Lemma `lem:unramified-class`: its concrete second cohomology. -/
abbrev CarryH2 (K L : Type) [Field K] [Field L] [Algebra K L] :=
  Inhomogeneous.H2 (CarryRep K L)

/-- **F06**, Lemma `lem:unramified-class`: the trivial integer coefficient representation. -/
abbrev TrivialIntegerRep (K L : Type) [Field K] [Field L] [Algebra K L] :=
  Rep.trivial ℤ (L ≃ₐ[K] L) ℤ

/-- **F06**, Lemma `lem:unramified-class`: concrete `H²(G,ℤ)` in the comparison layer. -/
abbrev TrivialIntegerH2 (K L : Type) [Field K] [Field L] [Algebra K L] :=
  Inhomogeneous.H2 (TrivialIntegerRep K L)

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ContinuousSMul K L]

/-- The normalized valuation, regarded literally as an additive homomorphism on `Lˣ`. -/
noncomputable def normalizedValuationAddHom : Additive (Units L) →+ ℤ where
  toFun x := normalizedValuation L x.toMul
  map_zero' := by simp [normalizedValuation]
  map_add' x y := normalizedValuation_mul L x.toMul y.toMul

/--
**F06**, Lemma `lem:unramified-class`: normalized valuation is invariant under every
`K`-automorphism of `L`.
-/
theorem normalizedValuation_algEquiv (σ : L ≃ₐ[K] L) (x : Units L) :
    normalizedValuation L (Units.map σ.toRingEquiv.toRingHom x) =
      normalizedValuation L x := by
  have hnorm : normUnitsHom K L (Units.map σ.toRingEquiv.toRingHom x) =
      normUnitsHom K L x := by
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv σ (x : L)
  have h₁ := normalizedValuation_norm K L (Units.map σ.toRingEquiv.toRingHom x)
  have h₂ := normalizedValuation_norm K L x
  rw [hnorm, h₂] at h₁
  have hf : 0 < residueDegree K L := by
    dsimp [residueDegree]
    exact (ramificationInvariants_exists K L).choose_spec.choose_spec.2.1
  nlinarith

/--
**F06**, Lemma `lem:unramified-class`: the literal valuation-induced coefficient morphism
`Lˣ → ℤ`.  Its underlying map is `x ↦ normalizedValuation L x`; equivariance is the identity
`v_L(σx)=v_L(x)`.
-/
noncomputable def valuationCoefficient :
    MulRep K L ⟶ TrivialIntegerRep K L :=
  Rep.ofHom ⟨(normalizedValuationAddHom L).toIntLinearMap, fun σ => by
    apply LinearMap.ext
    intro x
    change normalizedValuation L
        (Units.map σ.toRingEquiv.toRingHom.toMonoidHom x.toMul) =
      normalizedValuation L x.toMul
    exact normalizedValuation_algEquiv K L σ x.toMul⟩

/--
**F06**, Lemma `lem:unramified-class`: the map on concrete `H²` induced by the literal
valuation coefficient morphism, transported through the fixed **C01** comparison equivalences.
-/
noncomputable def valuationInducedH2 : CarryH2 K L →+ TrivialIntegerH2 K L :=
  (comparisonH2 (TrivialIntegerRep K L)).symm.toAddMonoidHom.comp
    ((groupCohomology.map (.id (L ≃ₐ[K] L)) (valuationCoefficient K L) 2).hom.toAddMonoidHom.comp
      (comparisonH2 (MulRep K L)).toAddMonoidHom)

/--
**F06**, Lemma `lem:unramified-class`: arithmetic Frobenius data for an unramified local
extension.  The equation on
`frobeniusEquiv` pins the cyclic identification on every element, so it cannot be replaced by an
arbitrary group equivalence.
-/
structure UnramifiedCyclicExtensionData where
  /-- Valuation-theoretic unramifiedness. -/
  unramified : IsUnramifiedLocalExtension K L
  /-- Arithmetic Frobenius. -/
  frobenius : L ≃ₐ[K] L
  /-- Frobenius preserves the valuation ring. -/
  frobenius_preserves_integral : ∀ x : RingOfIntegers L,
    ∃ y : RingOfIntegers L, (y : L) = frobenius (x : L)
  /-- Its defining residue-field equation `x ↦ x^|k_K|`. -/
  frobenius_residue : ∀ (x y : RingOfIntegers L),
    (y : L) = frobenius (x : L) →
      Ideal.Quotient.mk (LocalMaximalIdeal L) y =
        (Ideal.Quotient.mk (LocalMaximalIdeal L) x) ^ residueCard K
  /-- Frobenius generates the actual Galois group. -/
  frobenius_generates : Subgroup.zpowers frobenius = ⊤
  /-- Cyclic coordinates of the actual Galois group. -/
  frobeniusEquiv :
    Multiplicative (ZMod (Module.finrank K L)) ≃* (L ≃ₐ[K] L)
  /-- Defining equation `r ↦ F^r` for the cyclic coordinates. -/
  frobeniusEquiv_apply : ∀ r : ZMod (Module.finrank K L),
    frobeniusEquiv (Multiplicative.ofAdd r) = frobenius ^ r.val

/--
**F06**, Lemma `lem:unramified-class`: the standard integer carry cocycle in the Frobenius
coordinates fixed by `D`.  This is the explicit comparison-layer representative of
`1 mod [L:K]` in `H²(G,ℤ)`.
-/
def integerCarryCocycle (D : UnramifiedCyclicExtensionData K L) :
    Inhomogeneous.C2 (TrivialIntegerRep K L) := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  exact fun σ τ =>
    let r := (D.frobeniusEquiv.symm σ).toAdd
    let s := (D.frobeniusEquiv.symm τ).toAdd
    (carryExponent n r s : ℤ)

private theorem add_mod_eq_carry (n a b : ℕ) (hn : 0 < n) (ha : a < n) (hb : b < n) :
    (a + b) % n = if a + b < n then a + b else a + b - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h), Nat.mod_eq_of_lt]
    omega

private theorem carryExponent_cocycleIdentity_aux
    (n : ℕ) [NeZero n] (r s t : ZMod n) :
    carryExponent n r s + carryExponent n (r + s) t =
      carryExponent n s t + carryExponent n r (s + t) := by
  have hn : 0 < n := NeZero.pos n
  have hr := r.val_lt
  have hs := s.val_lt
  have ht := t.val_lt
  rw [carryExponent, carryExponent, carryExponent, carryExponent,
    ZMod.val_add, ZMod.val_add,
    add_mod_eq_carry n r.val s.val hn hr hs,
    add_mod_eq_carry n s.val t.val hn hs ht]
  split_ifs <;> omega

/-- The explicit integer carry function is a normalized two-cocycle. -/
theorem integerCarryCocycle_mem (D : UnramifiedCyclicExtensionData K L) :
    AbstractReciprocity.IsNormalizedCocycle2
      (TrivialIntegerRep K L) (integerCarryCocycle K L D) := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  constructor
  · change Inhomogeneous.d2 (TrivialIntegerRep K L)
      (integerCarryCocycle K L D) = 0
    ext σ τ υ
    change (integerCarryCocycle K L D τ υ) -
      integerCarryCocycle K L D (σ * τ) υ +
      integerCarryCocycle K L D σ (τ * υ) -
      integerCarryCocycle K L D σ τ = 0
    let r := (D.frobeniusEquiv.symm σ).toAdd
    let s := (D.frobeniusEquiv.symm τ).toAdd
    let t := (D.frobeniusEquiv.symm υ).toAdd
    have hmul (a b : Multiplicative (ZMod (Module.finrank K L))) :
        (a * b).toAdd = a.toAdd + b.toAdd := rfl
    simp only [integerCarryCocycle, map_mul, hmul]
    have h := carryExponent_cocycleIdentity_aux (Module.finrank K L) r s t
    have h' : (carryExponent (Module.finrank K L) r s : ℤ) +
        carryExponent (Module.finrank K L) (r + s) t =
        carryExponent (Module.finrank K L) s t +
          carryExponent (Module.finrank K L) r (s + t) := by
      exact_mod_cast h
    dsimp [r, s, t] at h'
    omega
  · constructor
    · intro σ
      have hs := (D.frobeniusEquiv.symm σ).toAdd.val_lt
      have hto : (1 : Multiplicative (ZMod (Module.finrank K L))).toAdd = 0 := rfl
      simp only [integerCarryCocycle, map_one, hto, ZMod.val_zero,
        zero_add, carryExponent, if_pos hs, Nat.cast_zero]
    · intro σ
      have hs := (D.frobeniusEquiv.symm σ).toAdd.val_lt
      have hto : (1 : Multiplicative (ZMod (Module.finrank K L))).toAdd = 0 := rfl
      simp only [integerCarryCocycle, map_one, hto, ZMod.val_zero,
        add_zero, carryExponent, if_pos hs, Nat.cast_zero]

/-- The concrete comparison-layer `H²(G,ℤ)` class of the standard integer carry. -/
def integerCarryClass (D : UnramifiedCyclicExtensionData K L) :
    TrivialIntegerH2 K L :=
  AbstractReciprocity.cocycleClass2 (TrivialIntegerRep K L)
    (integerCarryCocycle K L D) (integerCarryCocycle_mem K L D)

private noncomputable def unramifiedCyclicH2EquivH0
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G) :
    Inhomogeneous.H2 M ≃+ TateLowDegree.H0 M := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let g := (IsCyclic.exists_generator (α := G)).choose
  have hg := (IsCyclic.exists_generator (α := G)).choose_spec
  let e : Inhomogeneous.invariants0 M ≃+
      LinearMap.ker (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap :=
    { toFun := fun x => ⟨x, by
          rw [LinearMap.mem_ker]
          simpa [Rep.sub_hom, Rep.applyAsHom_apply, sub_eq_zero] using
            (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x).1 x.2⟩
      invFun := fun x => ⟨x, by
          apply (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x).2
          have hx : ((M.applyAsHom g).hom - (𝟙 M : M ⟶ M).hom) (x : M) = 0 := by
            rw [← Rep.sub_hom]
            exact x.2
          change M.ρ g (x : M) - x = 0 at hx
          exact sub_eq_zero.mp hx⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let p := Rep.FiniteCyclicGroup.groupCohomologyπEven M g hg 2 (by simp)
  let q : Inhomogeneous.invariants0 M →+ Inhomogeneous.H2 M :=
    (comparisonH2 M).symm.toAddMonoidHom.comp
      (p.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective p).1 inferInstance
  have hq : Function.Surjective q :=
    (comparisonH2 M).symm.surjective.comp (hp.comp e.surjective)
  have hker : q.ker = TateLowDegree.normRangeInInvariants M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change (comparisonH2 M).symm (p (e x)) = 0 ↔ _
    rw [(comparisonH2 M).symm.map_eq_zero_iff,
      Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [e, TateLowDegree.normAddHom] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by simpa [e, TateLowDegree.normAddHom] using hy⟩
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : Inhomogeneous.invariants0 M ⧸ q.ker →+ TateLowDegree.H0 M :=
    QuotientAddGroup.map q.ker (TateLowDegree.normRangeInInvariants M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.H0 M →+ Inhomogeneous.invariants0 M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

set_option maxRecDepth 10000 in
private noncomputable def unramifiedTrivialH0EquivZMod
    {G : Type} [Group G] [Fintype G] :
    TateLowDegree.H0 (Rep.trivial ℤ G ℤ) ≃+ ZMod (Nat.card G) := by
  let M := Rep.trivial ℤ G ℤ
  let e : Inhomogeneous.invariants0 M ≃+ ℤ :=
    { toFun := fun x => x
      invFun := fun x => ⟨x, fun _ => rfl⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hmem (x : Inhomogeneous.invariants0 M) :
      x ∈ TateLowDegree.normRangeInInvariants M ↔
        e x ∈ AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y * (Nat.card G : ℤ) = x
      have hcard : Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
      dsimp [TateLowDegree.normAddHom, M] at hy
      rw [Rep.norm_apply] at hy
      simp only [Representation.norm, LinearMap.sum_apply] at hy
      simp only [Representation.trivial_apply, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul] at hy
      rw [hcard] at hy
      simpa [mul_comm] using hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have hcard : Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
      dsimp [TateLowDegree.normAddHom, M]
      rw [Rep.norm_apply]
      simp only [Representation.norm, LinearMap.sum_apply]
      change y * (Nat.card G : ℤ) = (x : ℤ) at hy
      simp only [Representation.trivial_apply, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      simpa [mul_comm] using hy
  let r : TateLowDegree.H0 M →+ ℤ ⧸ AddSubgroup.zmultiples (Nat.card G : ℤ) :=
    QuotientAddGroup.map (TateLowDegree.normRangeInInvariants M)
      (AddSubgroup.zmultiples (Nat.card G : ℤ)) e.toAddMonoidHom (by
        intro x hx
        exact (hmem x).1 hx)
  have hr : Function.Bijective r := by
    let s : (ℤ ⧸ AddSubgroup.zmultiples (Nat.card G : ℤ)) →+
        TateLowDegree.H0 M :=
      QuotientAddGroup.map (AddSubgroup.zmultiples (Nat.card G : ℤ))
        (TateLowDegree.normRangeInInvariants M) e.symm.toAddMonoidHom (by
          intro x hx
          exact (hmem (e.symm x)).2 (by simpa using hx))
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact (AddEquiv.ofBijective r hr).trans (Int.quotientZMultiplesNatEquivZMod _)

private noncomputable def integerRowSumOnCocycles
    (D : UnramifiedCyclicExtensionData K L) :
    Inhomogeneous.cocycles2 (TrivialIntegerRep K L) →+
      ZMod (Module.finrank K L) where
  toFun a := (∑ σ : (L ≃ₐ[K] L), a.1 σ
    (D.frobeniusEquiv (Multiplicative.ofAdd 1)) : ℤ)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

private theorem integerRowSum_killsCoboundaries
    (D : UnramifiedCyclicExtensionData K L) :
    Inhomogeneous.coboundaries2 (TrivialIntegerRep K L) ≤
      (integerRowSumOnCocycles K L D).ker := by
  rintro x ⟨b, hb⟩
  rw [AddMonoidHom.mem_ker]
  let g := D.frobeniusEquiv (Multiplicative.ofAdd 1)
  have hpoint (σ : L ≃ₐ[K] L) :
      (x.1 σ g : ℤ) = b g - b (σ * g) + b σ := by
    have h := congrFun (congrFun hb σ) g
    change Inhomogeneous.d1 (TrivialIntegerRep K L) b σ g = x.1 σ g at h
    simpa [Inhomogeneous.d1] using h.symm
  dsimp only [integerRowSumOnCocycles]
  change (↑(∑ σ : L ≃ₐ[K] L, (x.1 σ g : ℤ)) :
    ZMod (Module.finrank K L)) = 0
  rw [show (∑ σ : L ≃ₐ[K] L, (x.1 σ g : ℤ)) =
      ∑ σ : L ≃ₐ[K] L, (b g - b (σ * g) + b σ) by
        apply Finset.sum_congr rfl
        intro σ _
        exact hpoint σ]
  rw [show (∑ σ : L ≃ₐ[K] L, (b g - b (σ * g) + b σ)) =
      (Fintype.card (L ≃ₐ[K] L) : ℤ) * b g by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hr : (∑ σ : L ≃ₐ[K] L, b (σ * g)) = ∑ σ, b σ := by
      simpa using Equiv.sum_comp (Equiv.mulRight g) b
    rw [hr, sub_add_cancel]
    simp]
  rw [show Fintype.card (L ≃ₐ[K] L) = Module.finrank K L by
    rw [← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K L]
  simp

private noncomputable def integerRowInvariant
    (D : UnramifiedCyclicExtensionData K L) :
    TrivialIntegerH2 K L →+ ZMod (Module.finrank K L) :=
  QuotientAddGroup.lift (Inhomogeneous.coboundaries2 (TrivialIntegerRep K L))
    (integerRowSumOnCocycles K L D) (integerRowSum_killsCoboundaries K L D)

private theorem sum_carryExponent_one (n : ℕ) [NeZero n] :
    (↑(∑ r : ZMod n, (carryExponent n r 1 : ℤ)) : ZMod n) = 1 := by
  by_cases hn : n = 1
  · subst n
    exact Subsingleton.elim _ _
  · have hnpos : 0 < n := NeZero.pos n
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
    have hn2 : 1 < m + 1 := by omega
    letI : Fact (1 < m + 1) := ⟨hn2⟩
    have hval (i : Fin (m + 1)) : (ZMod.finEquiv (m + 1) i).val = i.val := by rfl
    have hsum : (∑ r : ZMod (m + 1),
        (carryExponent (m + 1) r 1 : ℤ)) = 1 := by
      rw [← Equiv.sum_comp (ZMod.finEquiv (m + 1)).toEquiv
        (fun r : ZMod (m + 1) => (carryExponent (m + 1) r 1 : ℤ))]
      calc
        _ = (carryExponent (m + 1)
              ((ZMod.finEquiv (m + 1)).toEquiv (Fin.last ((m + 1) - 1))) 1 : ℤ) := by
          apply Fintype.sum_eq_single
          intro b hb
          have hbval : b.val < m + 1 := b.isLt
          have hbne : b.val ≠ (m + 1) - 1 := by
            intro heq
            apply hb
            apply Fin.ext
            simpa using heq
          have hlt : b.val + 1 < m + 1 := by omega
          simp [carryExponent, hval, ZMod.val_one, hlt]
        _ = 1 := by simp [carryExponent, hval, ZMod.val_one]
    rw [hsum]
    norm_num

private theorem integerRowInvariant_carry
    (D : UnramifiedCyclicExtensionData K L) :
    integerRowInvariant K L D (integerCarryClass K L D) = 1 := by
  letI : NeZero (Module.finrank K L) :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  rw [integerCarryClass, AbstractReciprocity.cocycleClass2, integerRowInvariant,
    QuotientAddGroup.lift_mk]
  rw [show integerRowSumOnCocycles K L D
      ⟨integerCarryCocycle K L D, integerCarryCocycle_mem K L D⟩ =
      (↑(∑ σ : L ≃ₐ[K] L, (integerCarryCocycle K L D σ
        (D.frobeniusEquiv (Multiplicative.ofAdd 1)) : ℤ)) :
          ZMod (Module.finrank K L)) by rfl]
  simp only [integerCarryCocycle, MulEquiv.symm_apply_apply]
  have hto : (Multiplicative.ofAdd (1 : ZMod (Module.finrank K L))).toAdd = 1 := rfl
  simp only [hto]
  have hsum :
      (∑ σ : L ≃ₐ[K] L,
        (carryExponent (Module.finrank K L) (D.frobeniusEquiv.symm σ).toAdd 1 : ℤ)) =
      ∑ r : ZMod (Module.finrank K L),
        (carryExponent (Module.finrank K L) r 1 : ℤ) := by
    calc
      _ = ∑ m : Multiplicative (ZMod (Module.finrank K L)),
          (carryExponent (Module.finrank K L) m.toAdd 1 : ℤ) := by
        symm
        simpa using Equiv.sum_comp D.frobeniusEquiv.toEquiv
          (fun σ : L ≃ₐ[K] L =>
            (carryExponent (Module.finrank K L)
              (D.frobeniusEquiv.symm σ).toAdd 1 : ℤ))
      _ = _ := by
        simpa using (Equiv.sum_comp Multiplicative.ofAdd
          (fun m : Multiplicative (ZMod (Module.finrank K L)) =>
            (carryExponent (Module.finrank K L) m.toAdd 1 : ℤ))).symm
  rw [hsum]
  exact sum_carryExponent_one (Module.finrank K L)

private theorem trivialIntegerH2_card (D : UnramifiedCyclicExtensionData K L) :
    Nat.card (TrivialIntegerH2 K L) = Module.finrank K L := by
  letI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.2 ⟨D.frobenius, D.frobenius_generates⟩
  calc
    Nat.card (TrivialIntegerH2 K L) =
        Nat.card (TateLowDegree.H0 (TrivialIntegerRep K L)) :=
      Nat.card_congr (unramifiedCyclicH2EquivH0 (TrivialIntegerRep K L)).toEquiv
    _ = Nat.card (ZMod (Nat.card (L ≃ₐ[K] L))) :=
      Nat.card_congr unramifiedTrivialH0EquivZMod.toEquiv
    _ = Nat.card (L ≃ₐ[K] L) := Nat.card_zmod _
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/--
**F06**, Lemma `lem:unramified-class`: the explicit positive-orientation identification
`H²(G,ℤ) ≅ ℤ/[L:K]`, characterized in the concrete comparison layer by sending the standard
integer carry class to `1 mod [L:K]`.
-/
theorem integerH2Comparison_existsUnique (D : UnramifiedCyclicExtensionData K L) :
    ∃! e : TrivialIntegerH2 K L ≃+ ZMod (Module.finrank K L),
      e (integerCarryClass K L D) = 1 := by
  letI : NeZero (Module.finrank K L) :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  letI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.2 ⟨D.frobenius, D.frobenius_generates⟩
  letI : NeZero (Nat.card (L ≃ₐ[K] L)) :=
    ⟨(Nat.card_pos (α := L ≃ₐ[K] L)).ne'⟩
  let efin := (unramifiedCyclicH2EquivH0 (TrivialIntegerRep K L)).trans
    (unramifiedTrivialH0EquivZMod (G := L ≃ₐ[K] L))
  let hfin : Finite (TrivialIntegerH2 K L) :=
    Finite.of_equiv (ZMod (Nat.card (L ≃ₐ[K] L))) efin.symm.toEquiv
  letI : Finite (TrivialIntegerH2 K L) := hfin
  letI : Fintype (TrivialIntegerH2 K L) := Fintype.ofFinite _
  letI : Fintype (ZMod (Module.finrank K L)) := Fintype.ofFinite _
  have hsurj : Function.Surjective (integerRowInvariant K L D) := by
    intro y
    refine ⟨y.val • integerCarryClass K L D, ?_⟩
    rw [map_nsmul, integerRowInvariant_carry, nsmul_one]
    exact ZMod.natCast_zmod_val y
  have hcards : Fintype.card (TrivialIntegerH2 K L) =
      Fintype.card (ZMod (Module.finrank K L)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      trivialIntegerH2_card K L D, Nat.card_zmod]
  have hbij : Function.Bijective (integerRowInvariant K L D) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcards⟩
  let e := AddEquiv.ofBijective (integerRowInvariant K L D) hbij
  have he : e (integerCarryClass K L D) = 1 := integerRowInvariant_carry K L D
  refine ⟨e, he, ?_⟩
  intro f hf
  apply AddEquiv.ext
  intro x
  have hx : ((integerRowInvariant K L D x).val) • integerCarryClass K L D = x := by
    apply hbij.1
    rw [map_nsmul, integerRowInvariant_carry, nsmul_one]
    exact ZMod.natCast_zmod_val (integerRowInvariant K L D x)
  rw [← hx, map_nsmul, hf, map_nsmul, he]

/-- The positive-orientation `H²(G,ℤ) ≅ ℤ/[L:K]` comparison fixed by the integer carry. -/
noncomputable def integerH2Comparison (D : UnramifiedCyclicExtensionData K L) :
    TrivialIntegerH2 K L ≃+ ZMod (Module.finrank K L) :=
  (integerH2Comparison_existsUnique K L D).choose

/-- The defining positive-orientation equation for `integerH2Comparison`. -/
theorem integerH2Comparison_carry (D : UnramifiedCyclicExtensionData K L) :
    integerH2Comparison K L D (integerCarryClass K L D) = 1 :=
  (integerH2Comparison_existsUnique K L D).choose_spec.1

/--
**F06**, Lemma `lem:unramified-class`: the carry cochain with value the image of `π_K` exactly
when adding Frobenius exponents causes a
carry.  Its values lie in `MulRep K L` and hence in `Lˣ`.
-/
def carryCocycle (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    Inhomogeneous.C2 (CarryRep K L) := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  exact fun σ τ =>
    let r := (D.frobeniusEquiv.symm σ).toAdd
    let s := (D.frobeniusEquiv.symm τ).toAdd
    if carryExponent n r s = 0 then 0
    else Additive.ofMul (Units.map (algebraMap K L) π.val)

/--
**F06**, Lemma `lem:unramified-class`: a fully pinned unramified fundamental class.  The cocycle,
its quotient class, and its normalized
invariant all carry their defining equations.
-/
structure UnramifiedClassData (D : UnramifiedCyclicExtensionData K L)
    (π : Uniformizer K) where
  /-- The concrete normalized carry cocycle. -/
  cocycle : Inhomogeneous.C2 (CarryRep K L)
  /-- The cocycle is the literal carry function above. -/
  cocycle_eq_carry : cocycle = carryCocycle K L D π
  /-- The carry function is a normalized two-cocycle. -/
  cocycle_mem : AbstractReciprocity.IsNormalizedCocycle2 (CarryRep K L) cocycle
  /-- Its concrete cohomology class. -/
  «class» : CarryH2 K L
  /-- The class is the quotient class of the displayed cocycle. -/
  class_eq_cocycle : «class» =
    AbstractReciprocity.cocycleClass2 (CarryRep K L) cocycle cocycle_mem
  /-- The class has exact order `[L:K]`. -/
  order_class : addOrderOf «class» = Module.finrank K L
  /-- It generates all of unramified `H²`. -/
  generates : ∀ β : CarryH2 K L, ∃ m : ℤ, m • «class» = β
  /-- The valuation-induced map on `H²` is an equivalence in the unramified case. -/
  valuation_h2_bijective : Function.Bijective (valuationInducedH2 K L)
  /--
  F06 normalization: valuation sends the carry class to the element corresponding to
  `1 mod [L:K]` under the explicit positive-orientation `H²(G,ℤ) ≅ ℤ/[L:K]` comparison.
  The minus sign of Deviation 15 belongs to the degree `-2` bar normalization and is absorbed by
  finite reciprocity; it is not inserted in this coefficient-map normalization.
  -/
  valuation_class :
    integerH2Comparison K L D (valuationInducedH2 K L «class») = 1
  /-- The normalized invariant, retained as data derived from the valuation-induced map. -/
  invariant : CarryH2 K L ≃+ ZMod (Module.finrank K L)
  /-- The invariant is pinned to valuation on `H²`, rather than chosen after the carry class. -/
  invariant_eq_valuation : invariant =
    (AddEquiv.ofBijective (valuationInducedH2 K L) valuation_h2_bijective).trans
      (integerH2Comparison K L D)
  /-- Derived normalization `inv(α_{L/K}) = 1 mod n` (equivalently `1/n mod ℤ`). -/
  invariant_class : invariant «class» = 1
  /-- This normalization uniquely determines the pinned invariant map. -/
  invariant_unique : ∀ e : CarryH2 K L ≃+ ZMod (Module.finrank K L),
    e «class» = 1 → e = invariant

/-- **F06**, Lemma `lem:unramified-class`: the elementary integer carry identity. -/
theorem carryExponent_cocycleIdentity (n : ℕ) [NeZero n] (r s t : ZMod n) :
    carryExponent n r s + carryExponent n (r + s) t =
      carryExponent n s t + carryExponent n r (s + t) := by
  exact carryExponent_cocycleIdentity_aux n r s t

private theorem carryCocycle_mem
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    AbstractReciprocity.IsNormalizedCocycle2 (CarryRep K L)
      (carryCocycle K L D π) := by
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  let u : Additive (Units L) :=
    Additive.ofMul (Units.map (algebraMap K L) π.val)
  have hu (σ : L ≃ₐ[K] L) : (MulRep K L).ρ σ u = u := by
    change Additive.ofMul (Units.map σ.toRingEquiv.toRingHom
      (Units.map (algebraMap K L).toMonoidHom π.val)) = u
    apply Additive.toMul.injective
    apply Units.ext
    simp [u]
  constructor
  · change Inhomogeneous.d2 (CarryRep K L) (carryCocycle K L D π) = 0
    ext σ τ υ
    let r := (D.frobeniusEquiv.symm σ).toAdd
    let s := (D.frobeniusEquiv.symm τ).toAdd
    let t := (D.frobeniusEquiv.symm υ).toAdd
    have hmul (a b : Multiplicative (ZMod n)) :
        (a * b).toAdd = a.toAdd + b.toAdd := rfl
    have hc := carryExponent_cocycleIdentity n r s t
    have hc' : (carryExponent n s t : ℤ) - carryExponent n (r + s) t +
        carryExponent n r (s + t) - carryExponent n r s = 0 := by omega
    simp only [Inhomogeneous.d2, carryCocycle, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Pi.zero_apply, map_mul, hmul]
    change (show Additive (Units L) from ((MulRep K L).ρ σ)
          (if carryExponent n s t = 0 then (0 : Additive (Units L)) else u)) -
        (if carryExponent n (r + s) t = 0 then 0 else u) +
        (if carryExponent n r (s + t) = 0 then 0 else u) -
        (if carryExponent n r s = 0 then 0 else u) = 0
    have hind (a b : ZMod n) :
        (if carryExponent n a b = 0 then (0 : Additive (Units L)) else u) =
          (carryExponent n a b : ℤ) • u := by
      unfold carryExponent
      by_cases h : a.val + b.val < n
      · rw [if_pos h, if_pos rfl]
        simp
      · rw [if_neg h]
        simp
    have hact : (MulRep K L).ρ σ
        (if carryExponent n s t = 0 then (0 : Additive (Units L)) else u) =
          (carryExponent n s t : ℤ) • u := by
      by_cases h : carryExponent n s t = 0
      · rw [if_pos h]
        calc
          _ = 0 := ((MulRep K L).ρ σ).map_zero
          _ = (carryExponent n s t : ℤ) • u := by rw [h]; simp; rfl
      · have hle : carryExponent n s t ≤ 1 := by
          simp only [carryExponent]
          split_ifs <;> omega
        have hone : carryExponent n s t = 1 := by omega
        rw [if_neg h, hu, hone]
        simp
    rw [hact, hind, hind, hind]
    calc
      _ = ((carryExponent n s t : ℤ) - carryExponent n (r + s) t +
          carryExponent n r (s + t) - carryExponent n r s) • u := by
        simp only [sub_zsmul, add_zsmul, sub_eq_add_neg, neg_zsmul]
      _ = 0 := by rw [hc']; simp
  · constructor
    · intro σ
      have hs := (D.frobeniusEquiv.symm σ).toAdd.val_lt
      have hto : (1 : Multiplicative (ZMod n)).toAdd = 0 := rfl
      simp [carryCocycle, hto, carryExponent, hs]
    · intro σ
      have hs := (D.frobeniusEquiv.symm σ).toAdd.val_lt
      have hto : (1 : Multiplicative (ZMod n)).toAdd = 0 := rfl
      simp [carryCocycle, hto, carryExponent, hs]

private theorem valuation_carry_cochain
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    (fun σ τ => (valuationCoefficient K L).hom (carryCocycle K L D π σ τ)) =
      integerCarryCocycle K L D := by
  letI : IsUnramifiedLocalExtension K L := D.unramified
  let n := Module.finrank K L
  letI : NeZero n := ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  have hval : normalizedValuation L (Units.map (algebraMap K L) π.val) = 1 := by
    rw [normalizedValuation_algebraMap, π.valuation_eq_one,
      IsUnramifiedLocalExtension.ramificationIndex_eq_one]
    norm_num
  ext σ τ
  let r := (D.frobeniusEquiv.symm σ).toAdd
  let s := (D.frobeniusEquiv.symm τ).toAdd
  change normalizedValuation L
      (if carryExponent n r s = 0 then (1 : Units L)
        else Units.map (algebraMap K L) π.val) =
    (carryExponent n r s : ℤ)
  have hle : carryExponent n r s ≤ 1 := by
    simp only [carryExponent]
    split_ifs <;> omega
  by_cases h : carryExponent n r s = 0
  · rw [if_pos h, h]
    simp [normalizedValuation]
  · have hone : carryExponent n r s = 1 := by omega
    rw [if_neg h, hone, hval]
    rfl

private theorem valuationInducedH2_carryClass
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    valuationInducedH2 K L
      (AbstractReciprocity.cocycleClass2 (CarryRep K L)
        (carryCocycle K L D π) (carryCocycle_mem K L D π)) =
      integerCarryClass K L D := by
  apply (comparisonH2 (TrivialIntegerRep K L)).injective
  simp [valuationInducedH2]
  change groupCohomology.map (.id (L ≃ₐ[K] L)) (valuationCoefficient K L) 2
      (comparisonH2 (MulRep K L)
        (AbstractReciprocity.cocycleClass2 (CarryRep K L)
          (carryCocycle K L D π) (carryCocycle_mem K L D π))) =
    comparisonH2 (TrivialIntegerRep K L) (integerCarryClass K L D)
  change groupCohomology.map (.id (L ≃ₐ[K] L)) (valuationCoefficient K L) 2
      (groupCohomology.H2π (MulRep K L) _) =
    groupCohomology.H2π (TrivialIntegerRep K L) _
  rw [groupCohomology.H2π_comp_map_apply]
  congr 1
  ext σ τ
  exact congrFun (congrFun (valuation_carry_cochain K L D π) σ) τ

/--
**F06**, Lemma `lem:unramified-class`: the actual `Lˣ`-valued carry function is a normalized
cocycle, its class generates `H²`, and the displayed invariant sends it to `1/n`.
-/
theorem carryCocycle_isGenerator
    (D : UnramifiedCyclicExtensionData K L) (π : Uniformizer K) :
    Nonempty (UnramifiedClassData K L D π) := by
  letI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.2 ⟨D.frobenius, D.frobenius_generates⟩
  letI : NeZero (Module.finrank K L) :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  let c := carryCocycle K L D π
  have hmem : AbstractReciprocity.IsNormalizedCocycle2 (CarryRep K L) c :=
    carryCocycle_mem K L D π
  let α := AbstractReciprocity.cocycleClass2 (CarryRep K L) c hmem
  have hvalα : valuationInducedH2 K L α = integerCarryClass K L D :=
    valuationInducedH2_carryClass K L D π
  letI : Finite (CarryH2 K L) := cyclic_local_H2_finite K L
  letI : Finite (TrivialIntegerH2 K L) :=
    Finite.of_equiv (ZMod (Module.finrank K L))
      (integerH2Comparison K L D).symm.toEquiv
  have hsurj : Function.Surjective (valuationInducedH2 K L) := by
    intro β
    refine ⟨(integerH2Comparison K L D β).val • α, ?_⟩
    apply (integerH2Comparison K L D).injective
    rw [map_nsmul, hvalα, map_nsmul, integerH2Comparison_carry, nsmul_one]
    exact ZMod.natCast_zmod_val (integerH2Comparison K L D β)
  letI : Fintype (CarryH2 K L) := Fintype.ofFinite _
  letI : Fintype (TrivialIntegerH2 K L) := Fintype.ofFinite _
  have hcards : Fintype.card (CarryH2 K L) =
      Fintype.card (TrivialIntegerH2 K L) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      cyclic_local_H2_card K L,
      Nat.card_congr (integerH2Comparison K L D).toEquiv, Nat.card_zmod]
  have hbij : Function.Bijective (valuationInducedH2 K L) :=
    (Fintype.bijective_iff_surjective_and_card _).2 ⟨hsurj, hcards⟩
  let vEquiv := AddEquiv.ofBijective (valuationInducedH2 K L) hbij
  let inv := vEquiv.trans (integerH2Comparison K L D)
  have hinvα : inv α = 1 := by
    change integerH2Comparison K L D (valuationInducedH2 K L α) = 1
    rw [hvalα, integerH2Comparison_carry]
  have horder : addOrderOf α = Module.finrank K L := by
    rw [← inv.addOrderOf_eq α, hinvα, ZMod.addOrderOf_one]
  have hgen : ∀ β : CarryH2 K L, ∃ m : ℤ, m • α = β := by
    intro β
    refine ⟨(inv β).val, ?_⟩
    apply inv.injective
    rw [map_zsmul, hinvα, zsmul_one]
    rw [← ZMod.cast_eq_val (R := ℤ)]
    exact ZMod.intCast_zmod_cast (inv β)
  refine ⟨{
    cocycle := c
    cocycle_eq_carry := rfl
    cocycle_mem := hmem
    «class» := α
    class_eq_cocycle := rfl
    order_class := horder
    generates := hgen
    valuation_h2_bijective := hbij
    valuation_class := ?_
    invariant := inv
    invariant_eq_valuation := rfl
    invariant_class := hinvα
    invariant_unique := ?_ }⟩
  · exact hinvα
  · intro e he
    apply AddEquiv.ext
    intro β
    obtain ⟨m, rfl⟩ := hgen β
    rw [map_zsmul, he, map_zsmul, hinvα]

/--
**F06**, Lemma `lem:unramified-class`: changing the uniformizer changes the carry cocycle by a
coboundary, so the resulting classes agree.  The equality is between the pinned quotient classes,
not merely between unspecified generators.
-/
theorem carryClass_uniformizer_independent
    (D : UnramifiedCyclicExtensionData K L) (π ϖ : Uniformizer K)
    (Cπ : UnramifiedClassData K L D π) (Cϖ : UnramifiedClassData K L D ϖ) :
    Cπ.class = Cϖ.class := by
  apply Cπ.valuation_h2_bijective.1
  apply (integerH2Comparison K L D).injective
  rw [Cπ.valuation_class, Cϖ.valuation_class]

private noncomputable def subgroupHilbert90Aux
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (S : Subgroup (L ≃ₐ[K] L)) (f : S → Units L) : L → L :=
  Finsupp.linearCombination L (fun σ : S => (σ.1 : L → L))
    (Finsupp.equivFunOnFinite.symm (fun σ => (f σ : L)))

private theorem subgroupHilbert90Aux_ne_zero
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] (f : S → Units L) :
    subgroupHilbert90Aux S f ≠ 0 := by
  have hli : LinearIndependent L (fun σ : S => (σ.1 : L → L)) :=
    LinearIndependent.comp (ι' := S)
      (linearIndependent_monoidHom L L) (fun σ : S => σ.1)
      (fun x y h => by
        apply Subtype.ext
        ext z
        exact DFunLike.congr_fun h z)
  have h := linearIndependent_iff.1 hli
    (Finsupp.equivFunOnFinite.symm (fun σ => (f σ : L)))
  intro H
  exact Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

private theorem subgroup_hilbert90
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype S]
    (f : S → Units L)
    (hf : ∀ g h, f (g * h) = Units.map g.1.toRingEquiv.toRingHom (f h) * f g) :
    ∃ β : Units L, ∀ g, Units.map g.1.toRingEquiv.toRingHom β / β = f g := by
  obtain ⟨z, hz⟩ : ∃ z, subgroupHilbert90Aux S f z ≠ 0 :=
    not_forall.1 (fun H => subgroupHilbert90Aux_ne_zero S f <| funext <| fun x => H x)
  have haux : subgroupHilbert90Aux S f z = ∑ h : S, (f h : L) * h.1 z := by
    simp [subgroupHilbert90Aux, Finsupp.linearCombination, Finsupp.sum_fintype]
  let β : Units L := (Units.mk0 (subgroupHilbert90Aux S f z) hz)⁻¹
  refine ⟨β, ?_⟩
  intro g
  apply Units.ext
  simp only [β, map_inv, div_inv_eq_mul, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0, haux] at hf ⊢
  have hsumne : (∑ h : S, (f h : L) * h.1 z) ≠ 0 := by
    rw [← haux]
    exact hz
  have hgne : g.1.toRingEquiv.toRingHom (∑ h : S, (f h : L) * h.1 z) ≠ 0 :=
    (map_ne_zero_iff g.1.toRingEquiv.toRingHom g.1.injective).2 hsumne
  field_simp [hgne]
  apply (div_eq_iff (by exact hgne)).2
  change (∑ x : S, (f x : L) * x.1 z) =
    (f g : L) * g.1 (∑ x : S, (f x : L) * x.1 z)
  rw [map_sum, Finset.mul_sum]
  have hfval (a b : S) : (f (a * b) : L) = a.1 (f b : L) * (f a : L) :=
    congrArg Units.val (hf a b)
  symm
  calc
    (∑ x : S, (f g : L) * g.1 ((f x : L) * x.1 z)) =
        ∑ x : S, (f (g * x) : L) * (g * x).1 z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [map_mul, hfval]
      change (f g : L) * (g.1 (f x : L) * g.1 (x.1 z)) =
        (g.1 (f x : L) * (f g : L)) * g.1 (x.1 z)
      ac_rfl
    _ = ∑ x : S, (f x : L) * x.1 z :=
      Fintype.sum_bijective (fun i : S => g * i)
        (Group.mulLeft_bijective g) _ _ (fun i => rfl)

private theorem mem_unitSubgroup_iff_normalizedValuation_eq_zero_unramified
    {L : Type} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Units L) :
    x ∈ unitSubgroup L ↔ normalizedValuation L x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hnonneg : 0 ≤ normalizedValuation L (ringUnitsToFieldUnits L u) :=
      (exists_normalizedValuationHom L).choose_spec.2 _ |>.2 ⟨u, rfl⟩
    have hinvnonneg : 0 ≤ normalizedValuation L ((ringUnitsToFieldUnits L u)⁻¹) :=
      (exists_normalizedValuationHom L).choose_spec.2 _ |>.2 ⟨↑u⁻¹, rfl⟩
    have hneg : normalizedValuation L ((ringUnitsToFieldUnits L u)⁻¹) =
        -normalizedValuation L (ringUnitsToFieldUnits L u) := by
      simp [normalizedValuation]
    omega
  · intro hx
    have hxi : 0 ≤ normalizedValuation L x := hx.ge
    have hxinv : normalizedValuation L x⁻¹ = 0 := by
      have h := normalizedValuation_mul L x x⁻¹
      have hzero : normalizedValuation L 1 = 0 := by simp [normalizedValuation]
      rw [mul_inv_cancel, hzero, hx, zero_add] at h
      exact h.symm
    obtain ⟨a, ha⟩ := (exists_normalizedValuationHom L).choose_spec.2 x |>.1 hxi
    obtain ⟨b, hb⟩ := (exists_normalizedValuationHom L).choose_spec.2 x⁻¹ |>.1 hxinv.ge
    let u : Units (RingOfIntegers L) :=
      { val := a
        inv := b
        val_inv := by apply Subtype.ext; dsimp; rw [ha, hb]; simp
        inv_val := by apply Subtype.ext; dsimp; rw [ha, hb]; simp }
    refine ⟨u, ?_⟩
    apply Units.ext
    exact ha

private noncomputable def cyclicH1EquivHMinusOne_unramified
    {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G) :
    Inhomogeneous.H1 M ≃+ TateLowDegree.HMinusOne M := by
  letI : CommGroup G := IsCyclic.commGroup
  letI : Module ℤ M := M.hV2
  let g := (IsCyclic.exists_generator (α := G)).choose
  have hg := (IsCyclic.exists_generator (α := G)).choose_spec
  let e : TateLowDegree.normKernel M ≃+
      LinearMap.ker M.norm.hom.toLinearMap :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  let p := Rep.FiniteCyclicGroup.groupCohomologyπOdd M g hg 1 (by simp)
  let q : TateLowDegree.normKernel M →+ Inhomogeneous.H1 M :=
    (comparisonH1 M).symm.toAddMonoidHom.comp
      (p.hom.toAddMonoidHom.comp e.toAddMonoidHom)
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective p).1 inferInstance
  have hq : Function.Surjective q :=
    (comparisonH1 M).symm.surjective.comp (hp.comp e.surjective)
  have hker : q.ker = TateLowDegree.augmentationInNormKernel M := by
    ext x
    rw [AddMonoidHom.mem_ker]
    change (comparisonH1 M).symm (p (e x)) = 0 ↔ _
    rw [(comparisonH1 M).symm.map_eq_zero_iff,
      Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff]
    change (x : M) ∈ LinearMap.range (M.applyAsHom g - 𝟙 M).hom.toLinearMap ↔
      (x : M) ∈ TateLowDegree.augmentation M
    constructor
    · rintro ⟨y, hy⟩
      apply AddSubgroup.subset_closure
      refine ⟨g, y, ?_⟩
      change (x : M) = M.ρ g y - y
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy.symm
    · intro hx
      have hcoin : (x : M) ∈ Representation.Coinvariants.ker M.ρ := by
        refine AddSubgroup.closure_induction (p := fun z _ =>
          z ∈ Representation.Coinvariants.ker M.ρ) ?_ ?_ ?_ ?_ hx
        · rintro z ⟨s, a, rfl⟩
          exact Representation.Coinvariants.sub_mem_ker s a
        · exact Submodule.zero_mem _
        · exact fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb
        · exact fun _ _ ha => Submodule.neg_mem _ ha
      rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg] at hcoin
      rcases hcoin with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      simpa [Rep.sub_hom, Rep.applyAsHom_apply] using hy
  let E := QuotientAddGroup.quotientKerEquivOfSurjective q hq
  let r : TateLowDegree.normKernel M ⧸ q.ker →+
      TateLowDegree.HMinusOne M :=
    QuotientAddGroup.map q.ker (TateLowDegree.augmentationInNormKernel M)
      (AddMonoidHom.id _) (by
        intro x hx
        rw [← hker]
        exact hx)
  have hr : Function.Bijective r := by
    let s : TateLowDegree.HMinusOne M →+
        TateLowDegree.normKernel M ⧸ q.ker :=
      QuotientAddGroup.map (TateLowDegree.augmentationInNormKernel M) q.ker
        (AddMonoidHom.id _) (by
          intro x hx
          rw [hker]
          exact hx)
    have hleft : Function.LeftInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    have hright : Function.RightInverse s r := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H x => simp [r, s]
    exact ⟨hleft.injective, hright.surjective⟩
  exact E.symm.trans (AddEquiv.ofBijective r hr)

private theorem finite_middle_unramified
    {A B C : Type} [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C] (p : A →+ B) (q : B →+ C)
    (h : p.range = q.ker) : Finite B := by
  letI : Finite p.range := Finite.of_surjective
    (fun x : A => (⟨p x, x, rfl⟩ : p.range)) (fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩)
  letI : Finite q.ker := Finite.of_injective (fun x : q.ker =>
    (⟨x, by rw [h]; exact x.2⟩ : p.range)) (fun x y hxy => by
      apply Subtype.ext
      exact congrArg (fun z : p.range => (z : B)) hxy)
  letI : Finite q.range := Finite.of_injective (fun x : q.range => (x : C))
    Subtype.val_injective
  exact (q.finite_iff_finite_ker_range).2 ⟨inferInstance, inferInstance⟩

open CategoryTheory.Limits in
private theorem rep_shortExact_of_function_unramified
    {G : Type} [Group G] {A B C : Rep ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (hzero : f ≫ g = 0)
    (hexact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    (ShortComplex.mk f g hzero).ShortExact := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  letI : Module ℤ C := C.hV2
  letI : Mono f := (Rep.mono_iff_injective f).2 hf
  have f_is_kernel : IsLimit (KernelFork.ofι f hzero) := by
    let lift (s : KernelFork g) : s.pt ⟶ A := by
      letI : Module ℤ s.pt := s.pt.hV2
      let pre (z : s.pt) : A := Classical.choose ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
      have hpre (z : s.pt) : f (pre z) = s.ι z :=
        Classical.choose_spec ((hexact (s.ι z)).1 (by
          have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
          exact hs))
      let add : s.pt →+ A :=
        { toFun := pre
          map_zero' := hf (by rw [map_zero, hpre, map_zero])
          map_add' := fun x y => hf (by rw [map_add, hpre, hpre, map_add, hpre]) }
      let l : s.pt →ₗ[ℤ] A :=
        { toFun := add
          map_add' := add.map_add
          map_smul' := fun n x => by
            change add (s.pt.hV2.smul n x) = A.hV2.smul n (add x)
            rw [int_smul_eq_zsmul s.pt.hV2, int_smul_eq_zsmul A.hV2]
            exact add.map_zsmul n x }
      exact Rep.ofHom ⟨l, fun σ => by
        apply LinearMap.ext
        intro z
        apply hf
        dsimp [l, add]
        calc
          f (pre (s.pt.ρ σ z)) = s.ι (s.pt.ρ σ z) := hpre _
          _ = B.ρ σ (s.ι z) := Rep.hom_comm_apply s.ι σ z
          _ = B.ρ σ (f (pre z)) := by rw [hpre]
          _ = f (A.ρ σ (pre z)) := (Rep.hom_comm_apply f σ (pre z)).symm⟩
    have lift_fac (s : KernelFork g) : lift s ≫ f = s.ι := by
      letI : Module ℤ s.pt := s.pt.hV2
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      change f ((lift s).hom z) = s.ι z
      simp only [lift]
      exact Classical.choose_spec ((hexact (s.ι z)).1 (by
        have hs := congrArg (fun q : s.pt ⟶ C => q.hom z) (KernelFork.condition s)
        exact hs))
    exact Fork.IsLimit.mk _ lift lift_fac
      (fun s m hm => by
        have hm' : m ≫ f = s.ι := hm
        apply (cancel_mono f).1
        exact hm'.trans (lift_fac s).symm)
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ f_is_kernel
  · exact (Rep.mono_iff_injective f).2 hf
  · exact (Rep.epi_iff_surjective g).2 hg

private theorem deepUnitQuotient_finite_unramified
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (π : Uniformizer K) (D : DeepUnitFiltrationData K L π) :
    Finite ((unitSubgroup L) ⧸ (D.V 0).comap (unitSubgroup L).subtype) := by
  let U := unitSubgroup L
  let V : Subgroup U := (D.V 0).comap U.subtype
  let rinj : Function.Injective (ringUnitsToFieldUnits L) := by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val h
  let e : Units (RingOfIntegers L) ≃* U :=
    MulEquiv.ofBijective (ringUnitsToFieldUnits L).rangeRestrict ⟨
      (fun x y h => rinj (congrArg Subtype.val h)), fun x => by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨y, Subtype.ext hy⟩⟩
  obtain ⟨r, hr⟩ := D.V_cofinal_principal_right 0
  let red : U →* Units (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)) :=
    (integralUnitReduction L (r + 1)).comp e.symm.toMonoidHom
  haveI : Finite (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)) :=
    (IsLocalRing.finite_quotient_iff).2 ⟨r + 1, le_rfl⟩
  let P : Subgroup U := (principalUnitSubgroup L (r + 1)).comap U.subtype
  have hP : P = red.ker := by
    ext x
    change (x : Units L) ∈ principalUnitSubgroup L (r + 1) ↔ red x = 1
    constructor
    · rintro ⟨y, hy, heq⟩
      change integralUnitReduction L (r + 1) (e.symm x) = 1
      have hey : e y = x := by
        apply Subtype.ext
        exact heq
      rw [← hey, e.symm_apply_apply]
      exact hy
    · intro hx
      refine ⟨e.symm x, hx, ?_⟩
      change ringUnitsToFieldUnits L (e.symm x) = (x : Units L)
      exact congrArg Subtype.val (e.apply_symm_apply x)
  haveI : Finite red.range := Finite.of_injective (fun x : red.range => (x :
    Units (RingOfIntegers L ⧸ LocalMaximalIdeal L ^ (r + 1)))) Subtype.val_injective
  haveI : Finite (U ⧸ red.ker) :=
    Finite.of_equiv red.range (QuotientGroup.quotientKerEquivRange red).symm.toEquiv
  letI : P.FiniteIndex := by rw [hP]; exact Subgroup.finiteIndex_of_finite_quotient
  have hPV : P ≤ V := by
    intro x hx
    exact hr hx
  letI : V.FiniteIndex := Subgroup.finiteIndex_of_le hPV
  exact Subgroup.finite_quotient_of_finiteIndex

private theorem restricted_localUnit_H1_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (D : UnramifiedCyclicExtensionData K L)
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype S] :
    Subsingleton (Inhomogeneous.H1 (Rep.res S.subtype (localUnitRep K L))) := by
  letI : IsUnramifiedLocalExtension K L := D.unramified
  let M := Rep.res S.subtype (localUnitRep K L)
  constructor
  intro a b
  suffices hz : ∀ c : Inhomogeneous.H1 M, c = 0 by
    rw [hz a, hz b]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H z =>
      let f : S → Units L := fun g => Additive.toMul (z.1 g).1
      have hf (g h : S) :
          f (g * h) = Units.map g.1.toRingEquiv.toRingHom (f h) * f g := by
        have hc := congrFun (congrFun z.2.1 g) h
        change M.ρ g (z.1 h) - z.1 (g * h) + z.1 g = 0 at hc
        have hc' : z.1 (g * h) = M.ρ g (z.1 h) + z.1 g := by
          calc
            z.1 (g * h) = 0 + z.1 (g * h) := by simp
            _ = (M.ρ g (z.1 h) - z.1 (g * h) + z.1 g) + z.1 (g * h) := by
              rw [hc]
            _ = M.ρ g (z.1 h) + z.1 g := by abel
        have hu := congrArg
          (fun x : M => Additive.toMul (x.1 : Additive (Units L))) hc'
        exact hu
      obtain ⟨β, hβ⟩ := subgroup_hilbert90 S f hf
      let π := defaultUniformizer K
      let p : Units L := Units.map (algebraMap K L) π.val
      let q : ℤ := normalizedValuation L β
      let γ : Units L := β * p ^ (-q)
      have hp : normalizedValuation L p = 1 := by
        rw [normalizedValuation_algebraMap, π.valuation_eq_one,
          IsUnramifiedLocalExtension.ramificationIndex_eq_one]
        norm_num
      have hγval : normalizedValuation L γ = 0 := by
        have hpow : normalizedValuation L (p ^ (-q)) =
            (-q) * normalizedValuation L p := by
          simp [normalizedValuation]
        dsimp [γ]
        rw [normalizedValuation_mul, hpow, hp]
        dsimp [q]
        ring
      have hγmem : γ ∈ unitSubgroup L :=
        (mem_unitSubgroup_iff_normalizedValuation_eq_zero_unramified γ).2 hγval
      have hpfix (g : S) : Units.map g.1.toRingEquiv.toRingHom p = p := by
        apply Units.ext
        simp [p]
      have hγ (g : S) :
          Units.map g.1.toRingEquiv.toRingHom γ / γ = f g := by
        dsimp [γ]
        rw [map_mul, map_zpow]
        change Units.map g.1.toRingEquiv.toMonoidHom β *
            (Units.map g.1.toRingEquiv.toMonoidHom p) ^ (-q) /
              (β * p ^ (-q)) = f g
        have hpfix' : Units.map g.1.toRingEquiv.toMonoidHom p = p := by
          apply Units.ext
          simp [p]
        rw [hpfix']
        have hb := hβ g
        calc
          Units.map g.1.toRingEquiv.toRingHom β * p ^ (-q) / (β * p ^ (-q)) =
              Units.map g.1.toRingEquiv.toRingHom β / β := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            group
          _ = f g := hb
      let x : M := ⟨Additive.ofMul γ, hγmem⟩
      apply (QuotientAddGroup.eq_zero_iff z).2
      refine ⟨x, ?_⟩
      ext g
      apply Subtype.ext
      apply Additive.toMul.injective
      change Units.map g.1.toRingEquiv.toRingHom γ / γ = f g
      exact hγ g

private theorem restricted_local_units_herbrand
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (Dcyc : UnramifiedCyclicExtensionData K L)
    (π : Uniformizer K) (D : DeepUnitFiltrationData K L π)
    (hD : AbstractReciprocity.CohomologicallyTrivial
      (stableUnitSubgroupRep K L (D.V 0) (D.V_stable 0)))
    (Sg : Subgroup (L ≃ₐ[K] L)) [Fintype Sg] :
    ∃ h : HerbrandFinite (Rep.res Sg.subtype (localUnitRep K L)),
      @herbrandQuotient _ _ _ (Rep.res Sg.subtype (localUnitRep K L)) h.h0 h.h1 = 1 := by
  letI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_iff_exists_zpowers_eq_top.2
      ⟨Dcyc.frobenius, Dcyc.frobenius_generates⟩
  letI : IsCyclic Sg := inferInstance
  let U := unitSubgroup L
  let V := D.V 0
  let VU : Subgroup U := V.comap U.subtype
  let base : localUnitRep K L ≃+ Additive U :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul x.1, x.2⟩
      invFun := fun x => ⟨Additive.ofMul (x.toMul : Units L), x.toMul.2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl }
  let W : Submodule ℤ (localUnitRep K L) :=
    VU.toAddSubgroup.toIntSubmodule.comap base.toAddMonoidHom.toIntLinearMap
  have W_stable : ∀ σ, W ≤ W.comap ((localUnitRep K L).ρ σ) := by
    intro σ x hx
    change Units.map σ.toRingEquiv.toRingHom (Additive.toMul x.1) ∈ V
    exact D.V_stable 0 σ _ hx
  let Q : Rep.{0, 0, 0} ℤ (L ≃ₐ[K] L) := Rep.quotient (localUnitRep K L) W W_stable
  let deep : Rep.{0, 0, 0} ℤ (L ≃ₐ[K] L) :=
    stableUnitSubgroupRep K L V (D.V_stable 0)
  let incLinear : deep →ₗ[ℤ] localUnitRep K L :=
    { toFun := fun x => ⟨x.1, D.V_le_integralUnits 0 x.2⟩
      map_add' := fun x y => by apply Subtype.ext; rfl
      map_smul' := fun n x => by apply Subtype.ext; rfl }
  let inc : deep ⟶ localUnitRep K L := Rep.ofHom ⟨incLinear, fun σ => by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl⟩
  let proj : localUnitRep K L ⟶ Q := Rep.mkQ (localUnitRep K L) W W_stable
  have hzero : inc ≫ proj = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change Submodule.Quotient.mk (incLinear x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact x.2
  have hexact : Function.Exact inc proj := by
    intro x
    rw [show proj x = 0 ↔ x ∈ W by exact Submodule.Quotient.mk_eq_zero W]
    constructor
    · intro hx
      refine ⟨⟨x.1, hx⟩, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨y, rfl⟩
      exact y.2
  have hinc : Function.Injective inc := fun x y h => by
    apply Subtype.ext
    exact congrArg (fun z : localUnitRep K L => (z.1 : Additive (Units L))) h
  have hproj : Function.Surjective proj := W.mkQ_surjective
  letI : Finite (U ⧸ VU) := deepUnitQuotient_finite_unramified K L π D
  have base_mem (x : localUnitRep K L) :
      x ∈ W ↔ base x ∈ VU.toAddSubgroup := Iff.rfl
  let qb : (localUnitRep K L ⧸ W.toAddSubgroup) →+
      (Additive U ⧸ VU.toAddSubgroup) :=
    QuotientAddGroup.map _ _ base.toAddMonoidHom (fun x hx => (base_mem x).1 hx)
  let qbi : (Additive U ⧸ VU.toAddSubgroup) →+
      (localUnitRep K L ⧸ W.toAddSubgroup) :=
    QuotientAddGroup.map _ _ base.symm.toAddMonoidHom (by
      intro x hx
      exact (base_mem (base.symm x)).2 (by simpa using hx))
  have hqleft : Function.LeftInverse qbi qb := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [qb, qbi]
  have hqright : Function.RightInverse qbi qb := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x => simp [qb, qbi]
  let eqQ : (localUnitRep K L ⧸ W.toAddSubgroup) ≃+
      (Additive U ⧸ VU.toAddSubgroup) :=
    AddEquiv.ofBijective qb ⟨hqleft.injective, hqright.surjective⟩
  letI : Finite Q := Finite.of_equiv (Additive (U ⧸ VU)) eqQ.symm.toEquiv
  let deepS : Rep.{0, 0, 0} ℤ Sg := Rep.res Sg.subtype deep
  let unitS : Rep.{0, 0, 0} ℤ Sg := Rep.res Sg.subtype (localUnitRep K L)
  let QS : Rep.{0, 0, 0} ℤ Sg := Rep.res Sg.subtype Q
  let incS : deepS ⟶ unitS := (Rep.resFunctor Sg.subtype).map inc
  let projS : unitS ⟶ QS := (Rep.resFunctor Sg.subtype).map proj
  have hzeroS : incS ≫ projS = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun q : deep ⟶ Q => q.hom x) hzero
    exact hx
  have hexactS : Function.Exact incS projS := by
    intro x
    exact hexact x
  have hincS : Function.Injective incS := hinc
  have hprojS : Function.Surjective projS := hproj
  let SC : ShortComplex (Rep.{0, 0, 0} ℤ Sg) := ShortComplex.mk incS projS hzeroS
  have hSC : SC.ShortExact :=
    rep_shortExact_of_function_unramified incS projS hzeroS hexactS hincS hprojS
  have hdt0 : Subsingleton (tateCohomology deepS 0) := hD Sg 0
  have hdtm : Subsingleton (tateCohomology deepS (-1)) := hD Sg (-1)
  have hd0 : Subsingleton (TateLowDegree.H0 deepS) :=
    ⟨fun x y => (TateLowDegree.comparisonH0Tate deepS).injective (hdt0.elim _ _)⟩
  have hdm : Subsingleton (TateLowDegree.HMinusOne deepS) := by
    let e := (TateLowDegree.HMinusOne_equiv_tate deepS).some
    exact ⟨fun x y => e.injective (hdtm.elim _ _)⟩
  letI : Subsingleton (TateLowDegree.H0 deepS) := hd0
  letI : Subsingleton (TateLowDegree.HMinusOne deepS) := hdm
  letI : Finite (TateLowDegree.H0 deepS) := Finite.of_subsingleton
  letI : Finite (TateLowDegree.HMinusOne deepS) := Finite.of_subsingleton
  letI : Finite QS := inferInstance
  letI : Finite (TateLowDegree.H0 QS) := inferInstance
  letI : Finite (TateLowDegree.HMinusOne QS) := inferInstance
  let TS := SC.map (tateComplexFunctor ℤ Sg)
  have hTS : TS.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact hSC
  let tD0 := TS.X₁.homology 0
  let tU0 := TS.X₂.homology 0
  let tQ0 := TS.X₃.homology 0
  letI : Finite tD0 := Finite.of_equiv (TateLowDegree.H0 deepS)
    (TateLowDegree.comparisonH0Tate deepS).toEquiv
  letI : Finite tQ0 := Finite.of_equiv (TateLowDegree.H0 QS)
    (TateLowDegree.comparisonH0Tate QS).toEquiv
  let p0 : tD0 →+ tU0 :=
    (HomologicalComplex.homologyMap TS.f 0).hom.toAddMonoidHom
  let q0 : tU0 →+ tQ0 :=
    (HomologicalComplex.homologyMap TS.g 0).hom.toAddMonoidHom
  have hpq0 : p0.range = q0.ker := by
    ext x
    change (∃ y, p0 y = x) ↔ q0 x = 0
    change (∃ y, (HomologicalComplex.homologyMap TS.f 0).hom y = x) ↔
      (HomologicalComplex.homologyMap TS.g 0).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hTS.homology_exact₂ 0).moduleCat_range_eq_ker]
  letI : Finite tU0 := finite_middle_unramified p0 q0 hpq0
  letI : Finite (TateLowDegree.H0 unitS) := Finite.of_equiv tU0
    (TateLowDegree.comparisonH0Tate unitS).symm.toEquiv
  let tDm := TS.X₁.homology (-1)
  let tUm := TS.X₂.homology (-1)
  let tQm := TS.X₃.homology (-1)
  let emD := (TateLowDegree.HMinusOne_equiv_tate deepS).some
  let emQ := (TateLowDegree.HMinusOne_equiv_tate QS).some
  letI : Finite tDm := Finite.of_equiv (TateLowDegree.HMinusOne deepS) emD.toEquiv
  letI : Finite tQm := Finite.of_equiv (TateLowDegree.HMinusOne QS) emQ.toEquiv
  let pm : tDm →+ tUm :=
    (HomologicalComplex.homologyMap TS.f (-1)).hom.toAddMonoidHom
  let qm : tUm →+ tQm :=
    (HomologicalComplex.homologyMap TS.g (-1)).hom.toAddMonoidHom
  have hpqm : pm.range = qm.ker := by
    ext x
    change (∃ y, pm y = x) ↔ qm x = 0
    change (∃ y, (HomologicalComplex.homologyMap TS.f (-1)).hom y = x) ↔
      (HomologicalComplex.homologyMap TS.g (-1)).hom x = 0
    rw [← LinearMap.mem_range, ← LinearMap.mem_ker,
      (hTS.homology_exact₂ (-1)).moduleCat_range_eq_ker]
  letI : Finite tUm := finite_middle_unramified pm qm hpqm
  let emU := (TateLowDegree.HMinusOne_equiv_tate unitS).some
  letI : Finite (TateLowDegree.HMinusOne unitS) :=
    Finite.of_equiv tUm emU.symm.toEquiv
  let h : HerbrandFinite unitS := ⟨inferInstance, inferInstance⟩
  refine ⟨h, ?_⟩
  have hdq := herbrandQuotient_eq_one_of_subsingleton deepS
  have hqq := (herbrandQuotient_rules.{0, 0} (G := Sg)).1 QS
  have hmul := (herbrandQuotient_rules.{0, 0} (G := Sg)).2.2.2
    deepS unitS QS incS projS hexactS hincS hprojS
  rw [hmul, hdq, hqq, mul_one]

/--
**F06**, Lemma `lem:unramified-class`: for an unramified extension, the actual integral-unit
representation is Tate-acyclic (hence has zero positive cohomology) after restriction to every
subgroup.
-/
theorem unramified_units_cohomologicallyTrivial
    (D : UnramifiedCyclicExtensionData K L) :
    AbstractReciprocity.CohomologicallyTrivial (localUnitRep K L) := by
  let π := defaultUniformizer K
  obtain ⟨F, hF⟩ := deepUnitFiltration_exists K L π
  apply AbstractReciprocity.cohomologicallyTrivial_of_H1_H2_zero
  · intro S _
    have hi := restricted_localUnit_H1_subsingleton K L D S
    exact ⟨fun x y => (comparisonH1 _).symm.injective (hi.elim _ _)⟩
  · intro S _
    letI : IsCyclic (L ≃ₐ[K] L) :=
      isCyclic_iff_exists_zpowers_eq_top.2
        ⟨D.frobenius, D.frobenius_generates⟩
    letI : IsCyclic S := inferInstance
    obtain ⟨h, hq⟩ := restricted_local_units_herbrand K L D π F hF S
    letI : Finite (TateLowDegree.H0 (Rep.res S.subtype (localUnitRep K L))) := h.h0
    letI : Finite (TateLowDegree.HMinusOne
        (Rep.res S.subtype (localUnitRep K L))) := h.h1
    have hH1 := restricted_localUnit_H1_subsingleton K L D S
    have hminus : Subsingleton (TateLowDegree.HMinusOne
        (Rep.res S.subtype (localUnitRep K L))) :=
      ⟨fun x y => (cyclicH1EquivHMinusOne_unramified
        (Rep.res S.subtype (localUnitRep K L))).symm.injective (hH1.elim _ _)⟩
    letI := hminus
    have hmcard : Nat.card (TateLowDegree.HMinusOne
        (Rep.res S.subtype (localUnitRep K L))) = 1 := Nat.card_unique
    rw [herbrandQuotient, hmcard] at hq
    norm_num at hq
    have h0card : Nat.card (TateLowDegree.H0
        (Rep.res S.subtype (localUnitRep K L))) = 1 := by
      exact_mod_cast hq
    have h0sub : Subsingleton (TateLowDegree.H0
        (Rep.res S.subtype (localUnitRep K L))) :=
      (Nat.card_eq_one_iff_unique.mp h0card).1
    have hi : Subsingleton (Inhomogeneous.H2
        (Rep.res S.subtype (localUnitRep K L))) :=
      ⟨fun x y => (unramifiedCyclicH2EquivH0
        (Rep.res S.subtype (localUnitRep K L))).injective (h0sub.elim _ _)⟩
    exact ⟨fun x y => (comparisonH2 _).symm.injective (hi.elim _ _)⟩

private theorem transportedC2_mem
    {G H : Type} [Group G] [Group H] {M : Rep ℤ G} {N : Rep ℤ H}
    (f : H →* G) (φ : Rep.res f M ⟶ N)
    (a : Inhomogeneous.C2 M) (ha : AbstractReciprocity.IsNormalizedCocycle2 M a) :
    AbstractReciprocity.IsNormalizedCocycle2 N (transportedC2 f φ a) := by
  constructor
  · change Inhomogeneous.d2 N (transportedC2 f φ a) = 0
    ext x y z
    change N.ρ x (φ.hom (a (f y) (f z))) - φ.hom (a (f (x * y)) (f z)) +
      φ.hom (a (f x) (f (y * z))) - φ.hom (a (f x) (f y)) = 0
    rw [← Rep.hom_comm_apply]
    have h := congrFun (congrFun (congrFun ha.1 (f x)) (f y)) (f z)
    change M.ρ (f x) (a (f y) (f z)) - a (f x * f y) (f z) +
      a (f x) (f y * f z) - a (f x) (f y) = 0 at h
    rw [map_mul, map_mul]
    rw [← map_sub, ← map_add, ← map_sub]
    change φ.hom (M.ρ (f x) (a (f y) (f z)) - a (f x * f y) (f z) +
      a (f x) (f y * f z) - a (f x) (f y)) = 0
    rw [h, map_zero]
  · constructor
    · intro x
      change φ.hom (a (f 1) (f x)) = 0
      rw [map_one, ha.2.1, map_zero]
    · intro x
      change φ.hom (a (f x) (f 1)) = 0
      rw [map_one, ha.2.2, map_zero]

private theorem transportedH2_cocycleClass_eq_of_coboundary
    {G H : Type} [Group G] [Group H] {M : Rep ℤ G} {N : Rep ℤ H}
    (f : H →* G) (φ : Rep.res f M ⟶ N)
    (a : Inhomogeneous.C2 M) (ha : AbstractReciprocity.IsNormalizedCocycle2 M a)
    (b : Inhomogeneous.C2 N) (hb : AbstractReciprocity.IsNormalizedCocycle2 N b)
    (c : Inhomogeneous.C1 N)
    (h : transportedC2 f φ a = b + Inhomogeneous.d1 N c) :
    transportedH2 f φ (AbstractReciprocity.cocycleClass2 M a ha) =
      AbstractReciprocity.cocycleClass2 N b hb := by
  apply (comparisonH2 N).injective
  simp [transportedH2]
  change groupCohomology.map f φ 2 (groupCohomology.H2π M _) =
    groupCohomology.H2π N _
  rw [groupCohomology.H2π_comp_map_apply]
  rw [groupCohomology.H2π_eq_iff]
  refine ⟨c, ?_⟩
  ext p
  have hp := congrFun (congrFun h p.1) p.2
  change φ.hom (a (f p.1) (f p.2)) =
    b p.1 p.2 + Inhomogeneous.d1 N c p.1 p.2 at hp
  change groupCohomology.d₁₂ N c p =
    φ.hom (a (f p.1) (f p.2)) - b p.1 p.2
  rw [hp]
  abel

private theorem exists_d1_of_cocycleClass_eq
    {G : Type} [Group G] (M : Rep ℤ G)
    (a b : Inhomogeneous.C2 M)
    (ha : AbstractReciprocity.IsNormalizedCocycle2 M a)
    (hb : AbstractReciprocity.IsNormalizedCocycle2 M b)
    (h : AbstractReciprocity.cocycleClass2 M a ha =
      AbstractReciprocity.cocycleClass2 M b hb) :
    ∃ c : Inhomogeneous.C1 M, a - b = Inhomogeneous.d1 M c := by
  have hm : (⟨a, ha⟩ : Inhomogeneous.cocycles2 M) - ⟨b, hb⟩ ∈
      Inhomogeneous.coboundaries2 M := QuotientAddGroup.eq_iff_sub_mem.mp h
  rcases hm with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

private theorem transportedH2_cocycleClass_eq
    {G H : Type} [Group G] [Group H] {M : Rep ℤ G} {N : Rep ℤ H}
    (f : H →* G) (φ : Rep.res f M ⟶ N)
    (a : Inhomogeneous.C2 M) (ha : AbstractReciprocity.IsNormalizedCocycle2 M a)
    (b : Inhomogeneous.C2 N) (hb : AbstractReciprocity.IsNormalizedCocycle2 N b)
    (h : transportedC2 f φ a = b) :
    transportedH2 f φ (AbstractReciprocity.cocycleClass2 M a ha) =
      AbstractReciprocity.cocycleClass2 N b hb := by
  apply transportedH2_cocycleClass_eq_of_coboundary f φ a ha b hb 0
  rw [map_zero, add_zero]
  exact h

private theorem residueFinrank_eq_residueDegree
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    Module.finrank (LocalResidueField K) (LocalResidueField L) =
      residueDegree K L := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
    ringOfIntegers_module_finite K L
  let p : Ideal (RingOfIntegers K) := IsLocalRing.maximalIdeal (RingOfIntegers K)
  let P : Ideal (RingOfIntegers L) := IsLocalRing.maximalIdeal (RingOfIntegers L)
  obtain ⟨ϖK, hϖK, hϖKirr⟩ := integral_normalizedUniformizer K
  obtain ⟨ϖL, hϖL, hϖLirr⟩ := integral_normalizedUniformizer L
  let mϖ : RingOfIntegers L := algebraMap (RingOfIntegers K) (RingOfIntegers L) ϖK
  have hmϖ0 : mϖ ≠ 0 := by
    intro h
    have h' := congr_arg (fun z : RingOfIntegers L => (z : L)) h
    have hz : algebraMap K L (ϖK : K) = 0 := by simpa [mϖ] using h'
    exact hϖKirr.ne_zero (Subtype.ext ((algebraMap K L).injective (by simpa using hz)))
  obtain ⟨n, unit, hfac⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hmϖ0 hϖLirr
  let xu : Units L := Units.map (algebraMap (RingOfIntegers L) L) unit
  have hfacUnits : Units.map (algebraMap K L) (defaultUniformizer K).val =
      xu * (defaultUniformizer L).val ^ n := by
    apply Units.ext
    change algebraMap K L (((defaultUniformizer K).val : Units K) : K) =
      algebraMap (RingOfIntegers L) L (unit : RingOfIntegers L) *
        (((defaultUniformizer L).val : Units L) : L) ^ n
    rw [show algebraMap (RingOfIntegers L) L (unit : RingOfIntegers L) =
      (((unit : Units (RingOfIntegers L)) : RingOfIntegers L) : L) from rfl, ← hϖK]
    simpa [mϖ, hϖL] using congr_arg (fun z : RingOfIntegers L => (z : L)) hfac
  have hn : n = ramificationIndex K L := by
    have hval := congr_arg (normalizedValuation L) hfacUnits
    rw [normalizedValuation_mul, normalizedValuation_ringUnit] at hval
    have hpow : normalizedValuation L ((defaultUniformizer L).val ^ n) = (n : ℤ) := by
      change Multiplicative.toAdd
        (normalizedValuationHom L ((defaultUniformizer L).val ^ n)) = _
      rw [map_pow, toAdd_pow]
      change (n : ℤ) * normalizedValuation L (defaultUniformizer L).val = _
      rw [(defaultUniformizer L).valuation_eq_one, mul_one]
    rw [hpow] at hval
    have hbase := normalizedValuation_algebraMap K L (defaultUniformizer K).val
    rw [(defaultUniformizer K).valuation_eq_one, mul_one] at hbase
    rw [hbase] at hval
    norm_num at hval
    exact_mod_cast hval.symm
  have hp : p = Ideal.span {ϖK} := hϖKirr.maximalIdeal_eq
  have hP : P = Ideal.span {ϖL} := hϖLirr.maximalIdeal_eq
  have hmap : Ideal.map (algebraMap (RingOfIntegers K) (RingOfIntegers L)) p =
      P ^ ramificationIndex K L := by
    rw [hp, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {mϖ} = P ^ ramificationIndex K L
    rw [hfac, Ideal.span_singleton_mul_left_unit unit.isUnit, hn, hP,
      Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map (algebraMap (RingOfIntegers K) (RingOfIntegers L)) p ≤
      P ^ (ramificationIndex K L + 1) := by
    rw [hmap]
    intro hle
    have heq : P ^ ramificationIndex K L = P ^ (ramificationIndex K L + 1) :=
      le_antisymm hle (Ideal.pow_le_pow_right (Nat.le_succ _))
    have hc := congr_arg Order.coheight heq
    rw [show P = IsLocalRing.maximalIdeal (RingOfIntegers L) from rfl,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal,
      IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hc
    have : ramificationIndex K L = ramificationIndex K L + 1 := by exact_mod_cast hc
    omega
  have hram : p.ramificationIdx P = ramificationIndex K L :=
    Ideal.ramificationIdx_spec hmap.le hnot
  have hdegree := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (S := RingOfIntegers L) K L (p := p) (by
      rw [hp, ne_eq, Ideal.span_singleton_eq_bot]
      exact hϖKirr.ne_zero)
  rw [hram] at hdegree
  have hselected := finrank_eq_ramificationIndex_mul_residueDegree K L
  have hinertia : p.inertiaDeg P = residueDegree K L := by
    apply Nat.eq_of_mul_eq_mul_left
      (ramificationInvariants_exists K L).choose_spec.choose_spec.1
    exact hdegree.trans hselected
  calc
    Module.finrank (LocalResidueField K) (LocalResidueField L) = p.inertiaDeg P := by
      rw [Ideal.inertiaDeg_algebraMap]
      rfl
    _ = residueDegree K L := hinertia

/-- The residue-field degree is the selected residue degree of a finite local extension. -/
theorem residueFinrank_eq_residueDegree_of_localFields
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver
        (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    Module.finrank (LocalResidueField K) (LocalResidueField L) =
      residueDegree K L :=
  residueFinrank_eq_residueDegree

private theorem residueFinrank_eq_finrank_unramified
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [IsUnramifiedLocalExtension K L] :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    Module.finrank (LocalResidueField K) (LocalResidueField L) =
      Module.finrank K L := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  rw [residueFinrank_eq_residueDegree (K := K) (L := L),
    finrank_eq_ramificationIndex_mul_residueDegree K L,
    IsUnramifiedLocalExtension.ramificationIndex_eq_one, one_mul]

private noncomputable def localAlgEquivOnIntegers
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] (σ : L ≃ₐ[K] L) :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    RingOfIntegers L ≃ₐ[RingOfIntegers K] RingOfIntegers L := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Module.Finite (RingOfIntegers K) (RingOfIntegers L) :=
    ringOfIntegers_module_finite K L
  have map_mem (τ : L ≃ₐ[K] L) (x : RingOfIntegers L) :
      τ (x : L) ∈ (ValuativeRel.valuation L).integer := by
    have hxO : IsIntegral (RingOfIntegers K) x := Algebra.IsIntegral.isIntegral x
    have hxL : IsIntegral (RingOfIntegers K) (x : L) :=
      IsIntegral.map (IsScalarTower.toAlgHom
        (RingOfIntegers K) (RingOfIntegers L) L) hxO
    have hτ : IsIntegral (RingOfIntegers K) (τ (x : L)) := IsIntegral.map τ hxL
    exact (Valuation.integer.integers (ValuativeRel.valuation L)).mem_of_integral
      hτ.tower_top
  let mapInt (τ : L ≃ₐ[K] L) (x : RingOfIntegers L) : RingOfIntegers L :=
    ⟨τ (x : L), map_mem τ x⟩
  exact
    { toFun := mapInt σ
      invFun := mapInt σ.symm
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : L))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : L))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : L) (y : L))
      map_add' := fun x y => Subtype.ext (map_add σ (x : L) (y : L))
      commutes' := fun x => Subtype.ext (σ.commutes (x : K)) }

private noncomputable def localResidueAlgEquivHom
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] :
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    (L ≃ₐ[K] L) →* (LocalResidueField L ≃ₐ[LocalResidueField K] LocalResidueField L) := by
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let red (σ : L ≃ₐ[K] L) :
      LocalResidueField L ≃ₐ[LocalResidueField K] LocalResidueField L := by
    let σO := localAlgEquivOnIntegers σ
    refine { IsLocalRing.ResidueField.mapEquiv σO.toRingEquiv with commutes' := ?_ }
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    change IsLocalRing.ResidueField.mapEquiv σO.toRingEquiv
        (IsLocalRing.residue (RingOfIntegers L)
          (algebraMap (RingOfIntegers K) (RingOfIntegers L) r)) =
      IsLocalRing.residue (RingOfIntegers L)
        (algebraMap (RingOfIntegers K) (RingOfIntegers L) r)
    rw [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    exact congr_arg (IsLocalRing.residue (RingOfIntegers L)) (σO.commutes r)
  exact
    { toFun := red
      map_one' := by
        apply AlgEquiv.ext
        intro x
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.residue (RingOfIntegers L)
            (localAlgEquivOnIntegers (1 : L ≃ₐ[K] L) r) =
          IsLocalRing.residue (RingOfIntegers L) r
        congr 1
      map_mul' := by
        intro σ τ
        apply AlgEquiv.ext
        intro x
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.residue (RingOfIntegers L)
            (localAlgEquivOnIntegers (σ * τ) r) =
          IsLocalRing.residue (RingOfIntegers L)
            (localAlgEquivOnIntegers σ (localAlgEquivOnIntegers τ r))
        congr 1 }

private theorem localResidueAlgEquivHom_frobenius
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (D : UnramifiedCyclicExtensionData K L) :
    letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    localResidueAlgEquivHom D.frobenius =
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (LocalResidueField K) (LocalResidueField L) := by
  letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let φO := localAlgEquivOnIntegers D.frobenius
  apply AlgEquiv.ext
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨y, hy⟩ := D.frobenius_preserves_integral r
  have hyr : y = φO r := Subtype.ext hy
  change IsLocalRing.residue (RingOfIntegers L) (φO r) =
    (IsLocalRing.residue (RingOfIntegers L) r) ^ Fintype.card (LocalResidueField K)
  rw [← hyr]
  have hres := D.frobenius_residue r y hy
  change IsLocalRing.residue (RingOfIntegers L) y =
    (IsLocalRing.residue (RingOfIntegers L) r) ^ residueCard K at hres
  rw [hres]
  congr 1
  exact Nat.card_eq_fintype_card

private theorem localResidueAlgEquivHom_injective
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L] [ContinuousSMul K L]
    (D : UnramifiedCyclicExtensionData K L) :
    letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      ⟨ValuativeRel.isEquiv _ _⟩
    letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
      Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
        (IsLocalRing.maximalIdeal (RingOfIntegers K))
    Function.Injective (localResidueAlgEquivHom (K := K) (L := L)) := by
  letI : IsUnramifiedLocalExtension K L := D.unramified
  letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let red := localResidueAlgEquivHom (K := K) (L := L)
  let φbar := FiniteField.frobeniusAlgEquivOfAlgebraic
    (LocalResidueField K) (LocalResidueField L)
  have hφ : red D.frobenius = φbar := localResidueAlgEquivHom_frobenius D
  have hsurj : Function.Surjective red := by
    intro τ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (LocalResidueField K) (LocalResidueField L)).2 τ
    refine ⟨D.frobenius ^ i.1, ?_⟩
    rw [map_pow, hφ]
    exact hi
  have hresrank : Module.finrank (LocalResidueField K) (LocalResidueField L) =
      Module.finrank K L := residueFinrank_eq_finrank_unramified (K := K) (L := L)
  have hcard : Nat.card (L ≃ₐ[K] L) =
      Nat.card (LocalResidueField L ≃ₐ[LocalResidueField K] LocalResidueField L) := by
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hresrank]
  exact (hsurj.bijective_of_nat_card_le hcard.le).1

private theorem arithmeticFrobenius_restrict
    {K L M : Type} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    [IsGalois K L] [IsGalois K M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [ValuativeExtension K L] [ValuativeExtension K M] [ValuativeExtension L M]
    [ContinuousSMul K L] [ContinuousSMul K M]
    (lower : UnramifiedCyclicExtensionData K L)
    (total : UnramifiedCyclicExtensionData K M) :
    AlgEquiv.restrictNormalHom L total.frobenius = lower.frobenius := by
  letI : IsUnramifiedLocalExtension K L := lower.unramified
  letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField L) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers L))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let redL := localResidueAlgEquivHom (K := K) (L := L)
  apply (localResidueAlgEquivHom_injective lower)
  apply AlgEquiv.ext
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  let qF : L ≃ₐ[K] L := AlgEquiv.restrictNormalHom L total.frobenius
  let qFO := localAlgEquivOnIntegers qF
  let lowerO := localAlgEquivOnIntegers lower.frobenius
  let totalO := localAlgEquivOnIntegers total.frobenius
  letI : Module.Finite (RingOfIntegers L) (RingOfIntegers M) :=
    ringOfIntegers_module_finite L M
  have hint : (algebraMap (RingOfIntegers L) (RingOfIntegers M)).IsIntegral :=
    Algebra.IsIntegral.isIntegral
  have hincinj : Function.Injective
      (algebraMap (RingOfIntegers L) (RingOfIntegers M)) := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap L M).injective (congr_arg Subtype.val hxy)
  letI : IsLocalHom (algebraMap (RingOfIntegers L) (RingOfIntegers M)) :=
    hint.isLocalHom hincinj
  let resMap : LocalResidueField L →+* LocalResidueField M :=
    IsLocalRing.ResidueField.map (algebraMap (RingOfIntegers L) (RingOfIntegers M))
  have hresMap (z : RingOfIntegers L) :
      IsLocalRing.residue (RingOfIntegers M)
          (algebraMap (RingOfIntegers L) (RingOfIntegers M) z) =
        resMap (IsLocalRing.residue (RingOfIntegers L) z) := by
    exact (IsLocalRing.ResidueField.map_residue
      (algebraMap (RingOfIntegers L) (RingOfIntegers M)) z).symm
  have hqval (z : RingOfIntegers L) :
      algebraMap (RingOfIntegers L) (RingOfIntegers M) (qFO z) =
        totalO (algebraMap (RingOfIntegers L) (RingOfIntegers M) z) := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes total.frobenius L (z : L)
  have htot (z : RingOfIntegers M) :
      IsLocalRing.residue (RingOfIntegers M) (totalO z) =
        (IsLocalRing.residue (RingOfIntegers M) z) ^ residueCard K := by
    exact total.frobenius_residue z (totalO z) rfl
  have hlow (z : RingOfIntegers L) :
      IsLocalRing.residue (RingOfIntegers L) (lowerO z) =
        (IsLocalRing.residue (RingOfIntegers L) z) ^ residueCard K := by
    exact lower.frobenius_residue z (lowerO z) rfl
  apply resMap.injective
  change resMap (IsLocalRing.residue (RingOfIntegers L) (qFO r)) =
    resMap (IsLocalRing.residue (RingOfIntegers L) (lowerO r))
  calc
    resMap (IsLocalRing.residue (RingOfIntegers L) (qFO r)) =
        IsLocalRing.residue (RingOfIntegers M)
          (algebraMap (RingOfIntegers L) (RingOfIntegers M) (qFO r)) :=
      (hresMap (qFO r)).symm
    _ = IsLocalRing.residue (RingOfIntegers M)
          (totalO (algebraMap (RingOfIntegers L) (RingOfIntegers M) r)) := by
      rw [hqval]
    _ = (IsLocalRing.residue (RingOfIntegers M)
          (algebraMap (RingOfIntegers L) (RingOfIntegers M) r)) ^ residueCard K :=
      htot _
    _ = (resMap (IsLocalRing.residue (RingOfIntegers L) r)) ^ residueCard K := by
      rw [hresMap]
    _ = resMap ((IsLocalRing.residue (RingOfIntegers L) r) ^ residueCard K) := by
      rw [map_pow]
    _ = resMap (IsLocalRing.residue (RingOfIntegers L) (lowerO r)) := by
      rw [hlow]

private theorem arithmeticFrobenius_baseChange
    {K E U W : Type} [Field K] [Field E] [Field U] [Field W]
    [Algebra K E] [Algebra K U] [Algebra K W] [Algebra E W] [Algebra U W]
    [IsScalarTower K E W] [IsScalarTower K U W]
    [FiniteDimensional K E] [FiniteDimensional K U] [FiniteDimensional K W]
    [FiniteDimensional E W] [FiniteDimensional U W]
    [IsGalois K U] [IsGalois E W]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
    [ValuativeRel W] [TopologicalSpace W] [IsNonarchimedeanLocalField W]
    [ValuativeExtension K E] [ValuativeExtension K U] [ValuativeExtension K W]
    [ValuativeExtension E W] [ValuativeExtension U W]
    [ContinuousSMul K U] [ContinuousSMul E W]
    (source : UnramifiedCyclicExtensionData K U)
    (common : UnramifiedCyclicExtensionData E W) :
    let q : (W ≃ₐ[E] W) →* (U ≃ₐ[K] U) :=
      (AlgEquiv.restrictNormalHom U).comp (AlgEquiv.restrictScalarsHom K)
    q common.frobenius = source.frobenius ^ residueDegree K E := by
  letI : IsUnramifiedLocalExtension K U := source.unramified
  letI : Fintype (LocalResidueField K) := Fintype.ofFinite _
  letI : Fintype (LocalResidueField E) := Fintype.ofFinite _
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation U) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : (ValuativeRel.valuation U).HasExtension (ValuativeRel.valuation W) :=
    ⟨ValuativeRel.isEquiv _ _⟩
  letI : Algebra (LocalResidueField K) (LocalResidueField E) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers E))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  letI : Algebra (LocalResidueField K) (LocalResidueField U) :=
    Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal (RingOfIntegers U))
      (IsLocalRing.maximalIdeal (RingOfIntegers K))
  let q : (W ≃ₐ[E] W) →* (U ≃ₐ[K] U) :=
    (AlgEquiv.restrictNormalHom U).comp (AlgEquiv.restrictScalarsHom K)
  let redU := localResidueAlgEquivHom (K := K) (L := U)
  apply (localResidueAlgEquivHom_injective source)
  have hredSource : redU source.frobenius =
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (LocalResidueField K) (LocalResidueField U) := localResidueAlgEquivHom_frobenius source
  let qF : U ≃ₐ[K] U := q common.frobenius
  let qFO := localAlgEquivOnIntegers qF
  let commonO := localAlgEquivOnIntegers common.frobenius
  letI : Module.Finite (RingOfIntegers U) (RingOfIntegers W) :=
    ringOfIntegers_module_finite U W
  have hint : (algebraMap (RingOfIntegers U) (RingOfIntegers W)).IsIntegral :=
    Algebra.IsIntegral.isIntegral
  have hincinj : Function.Injective
      (algebraMap (RingOfIntegers U) (RingOfIntegers W)) := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap U W).injective (congr_arg Subtype.val hxy)
  letI : IsLocalHom (algebraMap (RingOfIntegers U) (RingOfIntegers W)) :=
    hint.isLocalHom hincinj
  let resMap : LocalResidueField U →+* LocalResidueField W :=
    IsLocalRing.ResidueField.map (algebraMap (RingOfIntegers U) (RingOfIntegers W))
  have hresMap (z : RingOfIntegers U) :
      IsLocalRing.residue (RingOfIntegers W)
          (algebraMap (RingOfIntegers U) (RingOfIntegers W) z) =
        resMap (IsLocalRing.residue (RingOfIntegers U) z) :=
    (IsLocalRing.ResidueField.map_residue
      (algebraMap (RingOfIntegers U) (RingOfIntegers W)) z).symm
  have hqval (z : RingOfIntegers U) :
      algebraMap (RingOfIntegers U) (RingOfIntegers W) (qFO z) =
        commonO (algebraMap (RingOfIntegers U) (RingOfIntegers W) z) := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes
      (common.frobenius.restrictScalars K) U (z : U)
  have hcommon (z : RingOfIntegers W) :
      IsLocalRing.residue (RingOfIntegers W) (commonO z) =
        (IsLocalRing.residue (RingOfIntegers W) z) ^ residueCard E :=
    common.frobenius_residue z (commonO z) rfl
  have hresdegree : Module.finrank (LocalResidueField K) (LocalResidueField E) =
      residueDegree K E := residueFinrank_eq_residueDegree (K := K) (L := E)
  have hcardE : residueCard E = residueCard K ^ residueDegree K E := by
    calc
      residueCard E = Nat.card (LocalResidueField E) := rfl
      _ = Nat.card (LocalResidueField K) ^
          Module.finrank (LocalResidueField K) (LocalResidueField E) :=
        Module.natCard_eq_pow_finrank
      _ = residueCard K ^ residueDegree K E := by
        rw [hresdegree]
        rfl
  have hright (x : LocalResidueField U) :
      redU (source.frobenius ^ residueDegree K E) x =
        x ^ (residueCard K ^ residueDegree K E) := by
    rw [map_pow, hredSource, AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp only [residueCard, Nat.card_eq_fintype_card]
  apply AlgEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
  change IsLocalRing.residue (RingOfIntegers U) (qFO z) =
    redU (source.frobenius ^ residueDegree K E)
      (IsLocalRing.residue (RingOfIntegers U) z)
  apply resMap.injective
  calc
    resMap (IsLocalRing.residue (RingOfIntegers U) (qFO z)) =
        IsLocalRing.residue (RingOfIntegers W)
          (algebraMap (RingOfIntegers U) (RingOfIntegers W) (qFO z)) :=
      (hresMap (qFO z)).symm
    _ = IsLocalRing.residue (RingOfIntegers W)
          (commonO (algebraMap (RingOfIntegers U) (RingOfIntegers W) z)) := by
      rw [hqval]
    _ = (IsLocalRing.residue (RingOfIntegers W)
          (algebraMap (RingOfIntegers U) (RingOfIntegers W) z)) ^ residueCard E :=
      hcommon _
    _ = (resMap (IsLocalRing.residue (RingOfIntegers U) z)) ^ residueCard E := by
      rw [hresMap]
    _ = (resMap (IsLocalRing.residue (RingOfIntegers U) z)) ^
          (residueCard K ^ residueDegree K E) := by rw [hcardE]
    _ = resMap ((IsLocalRing.residue (RingOfIntegers U) z) ^
          (residueCard K ^ residueDegree K E)) := by rw [map_pow]
    _ = resMap (redU (source.frobenius ^ residueDegree K E)
          (IsLocalRing.residue (RingOfIntegers U) z)) := by rw [hright]

section Tower

variable (M : Type) [Field M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K M] [IsGalois L M]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension K M] [ValuativeExtension L M]
  [ContinuousSMul K M] [ContinuousSMul L M]

/--
**F07**, equations (4.2)–(4.3): actual group and coefficient maps for an unramified tower
`M/L/K`.  Pointwise equations pin both
group homomorphisms to restriction of automorphisms and both coefficient morphisms to the field
embeddings (or identity on `Mˣ`).
-/
structure UnramifiedCarryTowerData where
  /-- Frobenius data for `L/K`. -/
  lower : UnramifiedCyclicExtensionData K L
  /-- Frobenius data for `M/K`. -/
  total : UnramifiedCyclicExtensionData K M
  /-- Frobenius data for `M/L`. -/
  upper : UnramifiedCyclicExtensionData L M
  /-- Restriction `Gal(M/K) → Gal(L/K)`. -/
  quotientHom : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)
  /-- The quotient homomorphism is literal restriction on elements of `L`. -/
  quotientHom_apply : ∀ (σ : M ≃ₐ[K] M) (x : L),
    algebraMap L M (quotientHom σ x) = σ (algebraMap L M x)
  /-- Inclusion `Gal(M/L) → Gal(M/K)`. -/
  subgroupHom : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)
  /-- The subgroup homomorphism does not change the underlying automorphism of `M`. -/
  subgroupHom_apply : ∀ (σ : M ≃ₐ[L] M) (x : M), subgroupHom σ x = σ x
  /-- Coefficient embedding used with inflation. -/
  inflationCoefficient :
    Rep.res quotientHom (MulRep K L) ⟶ MulRep K M
  /-- Inflation maps a unit of `L` through `L ↪ M`. -/
  inflationCoefficient_apply : ∀ x : Units L,
    Additive.toMul (inflationCoefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap L M) x
  /-- Coefficient identification used with subgroup restriction. -/
  restrictionCoefficient :
    Rep.res subgroupHom (MulRep K M) ⟶ MulRep L M
  /-- Restriction leaves every coefficient in `Mˣ` unchanged. -/
  restrictionCoefficient_apply : ∀ x : Units M,
    restrictionCoefficient.hom (Additive.ofMul x) = Additive.ofMul x
  /-- Frobenius descends through the quotient. -/
  quotientHom_frobenius : quotientHom total.frobenius = lower.frobenius
  /-- `F_{M/L}=F_{M/K}^{[L:K]}` inside the total Galois group. -/
  subgroupHom_frobenius : subgroupHom upper.frobenius =
    total.frobenius ^ Module.finrank K L

/--
**F07**, equations (4.2)–(4.3): arithmetic Frobenius data on an appropriate unramified
local-field tower extend to the pinned quotient, subgroup, and coefficient maps required by
`UnramifiedCarryTowerData`.  The equalities retain the three supplied normalizations.
-/
theorem unramifiedCarryTowerData_exists
    (lower : UnramifiedCyclicExtensionData K L)
    (total : UnramifiedCyclicExtensionData K M)
    (upper : UnramifiedCyclicExtensionData L M) :
    ∃ T : UnramifiedCarryTowerData K L M,
      T.lower = lower ∧ T.total = total ∧ T.upper = upper := by
  let q : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let s : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M) := AlgEquiv.restrictScalarsHom K
  let i : Additive (Units L) →+ Additive (Units M) :=
    (Units.map (algebraMap L M)).toAdditive
  let infCoeff : Rep.res q (MulRep K L) ⟶ MulRep K M :=
    Rep.ofHom ⟨i.toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes σ L
        ((Additive.toMul x : Units L) : L)⟩
  let resCoeff : Rep.res s (MulRep K M) ⟶ MulRep L M :=
    Rep.ofHom ⟨(AddMonoidHom.id (Additive (Units M))).toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      rfl⟩
  have hfrob : q total.frobenius = lower.frobenius ∧
      s upper.frobenius = total.frobenius ^ Module.finrank K L := by
    constructor
    · change AlgEquiv.restrictNormalHom L total.frobenius = lower.frobenius
      exact arithmeticFrobenius_restrict lower total
    · letI : ValuativeExtension M M := ⟨fun _ _ => by rfl⟩
      have hsub := arithmeticFrobenius_baseChange
        (K := K) (E := L) (U := M) (W := M) total upper
      have hresLower : residueDegree K L = Module.finrank K L := by
        rw [finrank_eq_ramificationIndex_mul_residueDegree K L,
          lower.unramified.ramificationIndex_eq_one, one_mul]
      dsimp only at hsub
      change (AlgEquiv.restrictNormalHom M)
          ((AlgEquiv.restrictScalarsHom K) upper.frobenius) =
        total.frobenius ^ residueDegree K L at hsub
      have hnormal : (AlgEquiv.restrictNormalHom M)
          ((AlgEquiv.restrictScalarsHom K) upper.frobenius) =
        (AlgEquiv.restrictScalarsHom K) upper.frobenius := by
        apply AlgEquiv.ext
        intro x
        simpa using AlgEquiv.restrictNormal_commutes
          ((AlgEquiv.restrictScalarsHom K) upper.frobenius) M x
      change (AlgEquiv.restrictScalarsHom K) upper.frobenius =
        total.frobenius ^ Module.finrank K L
      rw [hnormal, hresLower] at hsub
      exact hsub
  refine ⟨{
    lower := lower
    total := total
    upper := upper
    quotientHom := q
    quotientHom_apply := fun σ x => AlgEquiv.restrictNormal_commutes σ L x
    subgroupHom := s
    subgroupHom_apply := fun _ _ => rfl
    inflationCoefficient := infCoeff
    inflationCoefficient_apply := fun _ => rfl
    restrictionCoefficient := resCoeff
    restrictionCoefficient_apply := fun _ => rfl
    quotientHom_frobenius := hfrob.1
    subgroupHom_frobenius := hfrob.2 }, rfl, rfl, rfl⟩

private theorem carryCocycle_inflation_cochain
    (T : UnramifiedCarryTowerData K L M) (π : Uniformizer K)
    (CL : UnramifiedClassData K L T.lower π)
    (CM : UnramifiedClassData K M T.total π) :
    ∃ b : Inhomogeneous.C1 (MulRep K M),
      transportedC2 T.quotientHom T.inflationCoefficient CL.cocycle =
        (Module.finrank L M : ℤ) • CM.cocycle +
          Inhomogeneous.d1 (MulRep K M) b := by
  let n := Module.finrank K L
  let d := Module.finrank L M
  let N := Module.finrank K M
  have hN : n * d = N := Module.finrank_mul_finrank K L M
  have hn : 0 < n := Module.finrank_pos
  have hd : 0 < d := Module.finrank_pos
  have hNpos : 0 < N := Module.finrank_pos
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero d := ⟨hd.ne'⟩
  letI : NeZero N := ⟨hNpos.ne'⟩
  have horder : orderOf T.lower.frobenius = n := by
    rw [orderOf_eq_card_of_zpowers_eq_top T.lower.frobenius_generates,
      IsGalois.card_aut_eq_finrank K L]
  have hcoord (σ : M ≃ₐ[K] M) :
      (T.lower.frobeniusEquiv.symm (T.quotientHom σ)).toAdd =
        ((T.total.frobeniusEquiv.symm σ).toAdd.val : ℕ) := by
    let r := (T.total.frobeniusEquiv.symm σ).toAdd
    apply Multiplicative.ofAdd.injective
    apply T.lower.frobeniusEquiv.injective
    have hto (x : Multiplicative (ZMod n)) : Multiplicative.ofAdd x.toAdd = x := rfl
    rw [hto, T.lower.frobeniusEquiv.apply_symm_apply,
      T.lower.frobeniusEquiv_apply, ZMod.val_natCast]
    have hsigma : σ = T.total.frobenius ^ r.val := by
      rw [← T.total.frobeniusEquiv_apply r]
      exact (T.total.frobeniusEquiv.apply_symm_apply σ).symm
    have hq : T.quotientHom σ = T.lower.frobenius ^ r.val := by
      rw [hsigma, map_pow, T.quotientHom_frobenius]
    rw [hq]
    change T.lower.frobenius ^ r.val = T.lower.frobenius ^ (r.val % n)
    rw [← horder, pow_mod_orderOf]
  let u : Additive (Units M) :=
    Additive.ofMul (Units.map (algebraMap K M) π.val)
  have hu (σ : M ≃ₐ[K] M) : (MulRep K M).ρ σ u = u := by
    change Additive.ofMul (Units.map σ.toRingEquiv.toRingHom
      (Units.map (algebraMap K M).toMonoidHom π.val)) = u
    apply Additive.toMul.injective
    apply Units.ext
    simp [u]
  let b : Inhomogeneous.C1 (MulRep K M) := fun σ =>
    -(((T.total.frobeniusEquiv.symm σ).toAdd.val / n : ℕ) : ℤ) • u
  refine ⟨b, ?_⟩
  rw [CL.cocycle_eq_carry, CM.cocycle_eq_carry]
  ext σ τ
  let r := (T.total.frobeniusEquiv.symm σ).toAdd
  let s := (T.total.frobeniusEquiv.symm τ).toAdd
  have hr := r.val_lt
  have hs := s.val_lt
  have hrslt : r.val + s.val < 2 * N := by omega
  have hsumcoord :
      (T.total.frobeniusEquiv.symm (σ * τ)).toAdd.val = (r.val + s.val) % N := by
    have hmul (a c : Multiplicative (ZMod N)) : (a * c).toAdd = a.toAdd + c.toAdd := rfl
    rw [map_mul, hmul, ZMod.val_add]
  have hcn : carryExponent n (r.val : ℕ) (s.val : ℕ) =
      if r.val % n + s.val % n < n then 0 else 1 := by
    rw [carryExponent, ZMod.val_natCast, ZMod.val_natCast]
  have hcN : carryExponent N r s = if r.val + s.val < N then 0 else 1 := rfl
  have hadddiv := Nat.add_div (a := r.val) (b := s.val) hn
  have hcombNat :
      carryExponent n (r.val : ℕ) (s.val : ℕ) + s.val / n + r.val / n =
        d * carryExponent N r s + ((r.val + s.val) % N) / n := by
    rw [hcn, hcN]
    by_cases hbig : r.val + s.val < N
    · simp only [if_pos hbig, Nat.mod_eq_of_lt hbig, mul_zero, zero_add]
      split_ifs with hsmall
      · have hi : ¬n ≤ r.val % n + s.val % n := by omega
        rw [if_neg hi] at hadddiv
        omega
      · have hi : n ≤ r.val % n + s.val % n := by omega
        rw [if_pos hi] at hadddiv
        omega
    · simp only [if_neg hbig, mul_one]
      have hle : N ≤ r.val + s.val := Nat.le_of_not_gt hbig
      have hmod : (r.val + s.val) % N = r.val + s.val - N := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt]
        omega
      rw [hmod]
      have hq : (r.val + s.val - N) / n + d = (r.val + s.val) / n := by
        have heq : (r.val + s.val - N) + n * d = r.val + s.val := by
          rw [hN, Nat.sub_add_cancel hle]
        nth_rw 2 [← heq]
        rw [Nat.add_mul_div_left _ _ hn]
      split_ifs with hsmall
      · have hi : ¬n ≤ r.val % n + s.val % n := by omega
        rw [if_neg hi] at hadddiv
        omega
      · have hi : n ≤ r.val % n + s.val % n := by omega
        rw [if_pos hi] at hadddiv
        omega
  have hcomb : (carryExponent n (r.val : ℕ) (s.val : ℕ) : ℤ) =
      (d : ℤ) * carryExponent N r s +
        (-((s.val / n : ℕ) : ℤ) -
          -((((r.val + s.val) % N) / n : ℕ) : ℤ) +
          -((r.val / n : ℕ) : ℤ)) := by
    have hcombInt :
        (carryExponent n (r.val : ℕ) (s.val : ℕ) : ℤ) + (s.val / n : ℕ) +
            (r.val / n : ℕ) =
          (d : ℤ) * carryExponent N r s + ((r.val + s.val) % N) / n := by
      exact_mod_cast hcombNat
    omega
  change T.inflationCoefficient.hom
      (if carryExponent n
          (T.lower.frobeniusEquiv.symm (T.quotientHom σ)).toAdd
          (T.lower.frobeniusEquiv.symm (T.quotientHom τ)).toAdd = 0 then 0
        else Additive.ofMul (Units.map (algebraMap K L) π.val)) =
    (d : ℤ) • (if carryExponent N r s = 0 then 0 else u) +
      ((show Additive (Units M) from (MulRep K M).ρ σ (b τ)) -
        (show Additive (Units M) from b (σ * τ)) +
        (show Additive (Units M) from b σ))
  rw [hcoord, hcoord]
  change T.inflationCoefficient.hom
      (if carryExponent n (r.val : ℕ) (s.val : ℕ) = 0 then
        (0 : Additive (Units L))
      else Additive.ofMul (Units.map (algebraMap K L) π.val)) =
    (d : ℤ) • (if carryExponent N r s = 0 then (0 : Additive (Units M)) else u) +
      ((show Additive (Units M) from (MulRep K M).ρ σ (b τ)) -
        (show Additive (Units M) from b (σ * τ)) +
        (show Additive (Units M) from b σ))
  have hcoeff : T.inflationCoefficient.hom
      (Additive.ofMul (Units.map (algebraMap K L) π.val)) = u := by
    apply Additive.toMul.injective
    rw [T.inflationCoefficient_apply]
    apply Units.ext
    change algebraMap L M (algebraMap K L (π.val : K)) =
      algebraMap K M (π.val : K)
    exact (IsScalarTower.algebraMap_apply K L M (π.val : K)).symm
  have hind (e : ℕ) (v : Additive (Units M)) (he : e ≤ 1) :
      (if e = 0 then (0 : Additive (Units M)) else v) = (e : ℤ) • v := by
    interval_cases e <;> simp
  have hle1 : carryExponent n (r.val : ℕ) (s.val : ℕ) ≤ 1 := by
    simp only [carryExponent]; split_ifs <;> omega
  have hle2 : carryExponent N r s ≤ 1 := by
    simp only [carryExponent]; split_ifs <;> omega
  have hmap : T.inflationCoefficient.hom
      (if carryExponent n (r.val : ℕ) (s.val : ℕ) = 0 then
        (0 : Additive (Units L))
      else Additive.ofMul (Units.map (algebraMap K L) π.val)) =
      if carryExponent n (r.val : ℕ) (s.val : ℕ) = 0 then
        (0 : Additive (Units M)) else u := by
    by_cases h : carryExponent n (r.val : ℕ) (s.val : ℕ) = 0
    · rw [if_pos h, if_pos h]
      exact T.inflationCoefficient.hom.map_zero
    · rw [if_neg h, if_neg h, hcoeff]
  have hact : (MulRep K M).ρ σ (b τ) =
      -((s.val / n : ℕ) : ℤ) • u := by
    change (MulRep K M).ρ σ (-((s.val / n : ℕ) : ℤ) • u) =
      -((s.val / n : ℕ) : ℤ) • u
    calc
      _ = -((s.val / n : ℕ) : ℤ) • ((MulRep K M).ρ σ u) :=
        map_zsmul ((MulRep K M).ρ σ) _ u
      _ = _ := by rw [hu]; rfl
  rw [hmap, hind _ u hle1, hind _ u hle2, hact]
  dsimp only [b]
  rw [hsumcoord]
  change (carryExponent n (r.val : ℕ) (s.val : ℕ) : ℤ) • u =
    (d : ℤ) • ((carryExponent N r s : ℤ) • u) +
      (-((s.val / n : ℕ) : ℤ) • u -
        -((((r.val + s.val) % N) / n : ℕ) : ℤ) • u +
        -((r.val / n : ℕ) : ℤ) • u)
  have hz := congrArg (fun z : ℤ => z • u) hcomb
  simpa only [add_zsmul, sub_zsmul, mul_zsmul, neg_zsmul,
    sub_eq_add_neg] using hz

/--
**F07**, equation (4.3): inflation in an unramified tower multiplies the fundamental class by
`[M:L]`.  The first conjunct is the pre-cohomology carry calculation; the second uses the actual
`transportedH2` map fixed by the tower data.
-/
theorem carryClass_inflation
    (T : UnramifiedCarryTowerData K L M) (π : Uniformizer K)
    (CL : UnramifiedClassData K L T.lower π)
    (CM : UnramifiedClassData K M T.total π) :
    (∃ b : Inhomogeneous.C1 (MulRep K M),
      transportedC2 T.quotientHom T.inflationCoefficient CL.cocycle =
        (Module.finrank L M : ℤ) • CM.cocycle +
          Inhomogeneous.d1 (MulRep K M) b) ∧
    transportedH2 T.quotientHom T.inflationCoefficient CL.class =
      (Module.finrank L M : ℤ) • CM.class := by
  obtain ⟨b, hb⟩ := carryCocycle_inflation_cochain K L M T π CL CM
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [CL.class_eq_cocycle, CM.class_eq_cocycle]
  let d : ℤ := Module.finrank L M
  have hmem : AbstractReciprocity.IsNormalizedCocycle2 (MulRep K M)
      (d • CM.cocycle) := zsmul_mem CM.cocycle_mem d
  have hclass := transportedH2_cocycleClass_eq_of_coboundary
    T.quotientHom T.inflationCoefficient CL.cocycle CL.cocycle_mem
      (d • CM.cocycle) hmem b hb
  exact hclass

private theorem carryCocycle_restriction_cochain
    (T : UnramifiedCarryTowerData K L M) (πK : Uniformizer K) (πL : Uniformizer L)
    (hπ : Units.map (algebraMap K L) πK.val = πL.val)
    (CM : UnramifiedClassData K M T.total πK)
    (CML : UnramifiedClassData L M T.upper πL) :
    transportedC2 T.subgroupHom T.restrictionCoefficient CM.cocycle = CML.cocycle := by
  let n := Module.finrank K L
  let m := Module.finrank L M
  let N := Module.finrank K M
  have hN : n * m = N := Module.finrank_mul_finrank K L M
  have hn : 0 < n := Module.finrank_pos
  have hm : 0 < m := Module.finrank_pos
  have hNpos : 0 < N := Module.finrank_pos
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero N := ⟨hNpos.ne'⟩
  have hcoord (σ : M ≃ₐ[L] M) :
      (T.total.frobeniusEquiv.symm (T.subgroupHom σ)).toAdd =
        (n * (T.upper.frobeniusEquiv.symm σ).toAdd.val : ℕ) := by
    let r := (T.upper.frobeniusEquiv.symm σ).toAdd
    have hr : n * r.val < N := by
      rw [← hN]
      exact Nat.mul_lt_mul_of_pos_left r.val_lt hn
    apply Multiplicative.ofAdd.injective
    apply T.total.frobeniusEquiv.injective
    have hto (x : Multiplicative (ZMod N)) : Multiplicative.ofAdd x.toAdd = x := rfl
    rw [hto, T.total.frobeniusEquiv.apply_symm_apply,
      T.total.frobeniusEquiv_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
    have hsigma : σ = T.upper.frobenius ^ r.val := by
      rw [← T.upper.frobeniusEquiv_apply r]
      exact (T.upper.frobeniusEquiv.apply_symm_apply σ).symm
    rw [hsigma, map_pow, T.subgroupHom_frobenius, ← pow_mul]
  have hcarry (r s : ZMod m) :
      carryExponent N (n * r.val : ℕ) (n * s.val : ℕ) = carryExponent m r s := by
    have hr : n * r.val < N := by
      rw [← hN]
      exact Nat.mul_lt_mul_of_pos_left r.val_lt hn
    have hs : n * s.val < N := by
      rw [← hN]
      exact Nat.mul_lt_mul_of_pos_left s.val_lt hn
    rw [carryExponent, carryExponent, ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]
    have heq : n * r.val + n * s.val < N ↔ r.val + s.val < m := by
      rw [← hN, ← Nat.mul_add, Nat.mul_lt_mul_left hn]
    simp only [heq]
  have hunit : Units.map (algebraMap K M).toMonoidHom πK.val =
      Units.map (algebraMap L M).toMonoidHom πL.val := by
    rw [← hπ]
    apply Units.ext
    simp [IsScalarTower.algebraMap_apply K L M]
  rw [CM.cocycle_eq_carry, CML.cocycle_eq_carry]
  ext σ τ
  let r := (T.upper.frobeniusEquiv.symm σ).toAdd
  let s := (T.upper.frobeniusEquiv.symm τ).toAdd
  change T.restrictionCoefficient.hom
      (if carryExponent N
          (T.total.frobeniusEquiv.symm (T.subgroupHom σ)).toAdd
          (T.total.frobeniusEquiv.symm (T.subgroupHom τ)).toAdd = 0 then 0
        else Additive.ofMul (Units.map (algebraMap K M) πK.val)) =
    if carryExponent m r s = 0 then 0
    else Additive.ofMul (Units.map (algebraMap L M) πL.val)
  rw [hcoord, hcoord, hcarry]
  by_cases h : carryExponent m r s = 0
  · rw [if_pos h, if_pos h, map_zero]
    rfl
  · rw [if_neg h, if_neg h, T.restrictionCoefficient_apply]
    apply Additive.toMul.injective
    exact hunit

/--
**F07**, equation (4.2): subgroup restriction in an unramified tower sends the total carry class
to the upper carry class.  Compatible uniformizers are stated explicitly, and both the cochain
identity and the induced class identity use the pinned restriction maps.
-/
theorem carryClass_restriction
    (T : UnramifiedCarryTowerData K L M) (πK : Uniformizer K) (πL : Uniformizer L)
    (hπ : Units.map (algebraMap K L) πK.val = πL.val)
    (CM : UnramifiedClassData K M T.total πK)
    (CML : UnramifiedClassData L M T.upper πL) :
    transportedC2 T.subgroupHom T.restrictionCoefficient CM.cocycle = CML.cocycle ∧
      transportedH2 T.subgroupHom T.restrictionCoefficient CM.class = CML.class := by
  have hc := carryCocycle_restriction_cochain K L M T πK πL hπ CM CML
  refine ⟨hc, ?_⟩
  rw [CM.class_eq_cocycle, CML.class_eq_cocycle]
  exact transportedH2_cocycleClass_eq T.subgroupHom T.restrictionCoefficient
    CM.cocycle CM.cocycle_mem CML.cocycle CML.cocycle_mem hc

end Tower

section BaseChange

variable (E U R W : Type) [Field E] [Field U] [Field R] [Field W]
  [Algebra K E] [Algebra K U] [Algebra K W]
  [Algebra E R] [Algebra E W] [Algebra U W] [Algebra R W]
  [IsScalarTower K E W] [IsScalarTower K U W] [IsScalarTower E R W]
  [FiniteDimensional K E] [FiniteDimensional K U] [FiniteDimensional K W]
  [FiniteDimensional E R] [FiniteDimensional E W]
  [FiniteDimensional U W] [FiniteDimensional R W]
  [IsGalois K U] [IsGalois E R] [IsGalois E W]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeRel U] [TopologicalSpace U] [IsNonarchimedeanLocalField U]
  [ValuativeRel R] [TopologicalSpace R] [IsNonarchimedeanLocalField R]
  [ValuativeRel W] [TopologicalSpace W] [IsNonarchimedeanLocalField W]
  [ValuativeExtension K E] [ValuativeExtension K U] [ValuativeExtension K W]
  [ValuativeExtension E R] [ValuativeExtension E W]
  [ValuativeExtension U W] [ValuativeExtension R W]
  [ContinuousSMul K E] [ContinuousSMul K U] [ContinuousSMul K W]
  [ContinuousSMul E R] [ContinuousSMul E W]
  [ContinuousSMul U W] [ContinuousSMul R W]

/--
**F07**, Proposition `prop:fundamental-restriction`: pinned data for the general base-change
carry calculation.  `U/K` has degree `[R:E][E:K]`, `W=EU` is the common unramified envelope,
and the degree-`[R:E]` unramified extension `R/E` is embedded in `W`.  This formulation allows a
ramified base field: it does not incorrectly identify `R` with the whole compositum `W`.
-/
structure CarryBaseChangeData where
  /-- Source unramified extension `U/K`. -/
  source : UnramifiedCyclicExtensionData K U
  /-- Common unramified envelope `W/E`. -/
  common : UnramifiedCyclicExtensionData E W
  /-- The degree-`[R:E]` unramified target `R/E` inside `W`. -/
  target : UnramifiedCyclicExtensionData E R
  /-- `W` is the compositum of the displayed copies of `E` and `U`. -/
  compositum_eq_top :
    Algebra.adjoin K (Set.range (algebraMap E W) ∪ Set.range (algebraMap U W)) = ⊤
  /-- The intersection of `E` and `U` in the common envelope. -/
  intersection : IntermediateField K W
  /-- Literal carrier equation for that intersection. -/
  mem_intersection_iff : ∀ x : W, x ∈ intersection ↔
    (∃ e : E, algebraMap E W e = x) ∧ (∃ u : U, algebraMap U W u = x)
  /-- Its degree is the residue degree of `E/K`. -/
  intersection_degree : Module.finrank K intersection = residueDegree K E
  /-- The source degree is `[R:E][E:K]`, as in the blueprint's `K_{rs}`. -/
  source_degree : Module.finrank K U =
    Module.finrank E R * Module.finrank K E
  /-- The compositum degree formula `[W:E] [E∩U:K] = [U:K]`. -/
  common_degree : Module.finrank E W * Module.finrank K intersection =
    Module.finrank K U
  /-- The target degree divides the common-envelope degree. -/
  target_degree_dvd_common : Module.finrank E R ∣ Module.finrank E W
  /-- Restriction from the common envelope to the source unramified field. -/
  sourceGroupHom : (W ≃ₐ[E] W) →* (U ≃ₐ[K] U)
  /-- This map is literal restriction along `U ↪ W`. -/
  sourceGroupHom_apply : ∀ (σ : W ≃ₐ[E] W) (x : U),
    algebraMap U W (sourceGroupHom σ x) = σ (algebraMap U W x)
  /-- Coefficient inclusion `Uˣ → Wˣ`. -/
  sourceCoefficient : Rep.res sourceGroupHom (MulRep K U) ⟶ MulRep E W
  /-- The source coefficient morphism is the actual field embedding. -/
  sourceCoefficient_apply : ∀ x : Units U,
    Additive.toMul (sourceCoefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap U W) x
  /-- Quotient `Gal(W/E) → Gal(R/E)` for inflation from the target. -/
  targetGroupHom : (W ≃ₐ[E] W) →* (R ≃ₐ[E] R)
  /-- It is literal restriction along `R ↪ W`. -/
  targetGroupHom_apply : ∀ (σ : W ≃ₐ[E] W) (x : R),
    algebraMap R W (targetGroupHom σ x) = σ (algebraMap R W x)
  /-- Coefficient inclusion `Rˣ → Wˣ`. -/
  targetCoefficient : Rep.res targetGroupHom (MulRep E R) ⟶ MulRep E W
  /-- The target coefficient morphism is the actual field embedding. -/
  targetCoefficient_apply : ∀ x : Units R,
    Additive.toMul (targetCoefficient.hom (Additive.ofMul x)) =
      Units.map (algebraMap R W) x
  /-- Base-change Frobenius acts on `U` by the residue-degree power. -/
  source_frobenius : sourceGroupHom common.frobenius =
    source.frobenius ^ residueDegree K E
  /-- Common-envelope Frobenius restricts to target Frobenius. -/
  target_frobenius : targetGroupHom common.frobenius = target.frobenius

/--
**F07**, Proposition `prop:fundamental-restriction`: the geometric degree and intersection
conditions defining an appropriate common unramified envelope extend to all pinned group and
coefficient maps in `CarryBaseChangeData`.  This is the existence interface consumed by the
general restriction construction.
-/
theorem carryBaseChangeData_exists
    (source : UnramifiedCyclicExtensionData K U)
    (common : UnramifiedCyclicExtensionData E W)
    (target : UnramifiedCyclicExtensionData E R)
    (compositum_eq_top :
      Algebra.adjoin K (Set.range (algebraMap E W) ∪ Set.range (algebraMap U W)) = ⊤)
    (intersection : IntermediateField K W)
    (mem_intersection_iff : ∀ x : W, x ∈ intersection ↔
      (∃ e : E, algebraMap E W e = x) ∧ (∃ u : U, algebraMap U W u = x))
    (intersection_degree : Module.finrank K intersection = residueDegree K E)
    (source_degree : Module.finrank K U =
      Module.finrank E R * Module.finrank K E)
    (common_degree : Module.finrank E W * Module.finrank K intersection =
      Module.finrank K U)
    (target_degree_dvd_common : Module.finrank E R ∣ Module.finrank E W) :
    ∃ B : CarryBaseChangeData K E U R W,
      B.source = source ∧ B.common = common ∧ B.target = target ∧
        B.intersection = intersection := by
  let sourceGroup : (W ≃ₐ[E] W) →* (U ≃ₐ[K] U) :=
    (AlgEquiv.restrictNormalHom U).comp (AlgEquiv.restrictScalarsHom K)
  let targetGroup : (W ≃ₐ[E] W) →* (R ≃ₐ[E] R) :=
    AlgEquiv.restrictNormalHom R
  let sourceMap : Additive (Units U) →+ Additive (Units W) :=
    (Units.map (algebraMap U W)).toAdditive
  let sourceCoeff : Rep.res sourceGroup (MulRep K U) ⟶ MulRep E W :=
    Rep.ofHom ⟨sourceMap.toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes
        ((AlgEquiv.restrictScalarsHom K) σ) U
          ((Additive.toMul x : Units U) : U)⟩
  let targetMap : Additive (Units R) →+ Additive (Units W) :=
    (Units.map (algebraMap R W)).toAdditive
  let targetCoeff : Rep.res targetGroup (MulRep E R) ⟶ MulRep E W :=
    Rep.ofHom ⟨targetMap.toIntLinearMap, by
      intro σ
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes σ R
        ((Additive.toMul x : Units R) : R)⟩
  have hsource : sourceGroup common.frobenius =
      source.frobenius ^ residueDegree K E := by
    exact arithmeticFrobenius_baseChange source common
  have htarget : targetGroup common.frobenius = target.frobenius := by
    exact arithmeticFrobenius_restrict target common
  refine ⟨{
    source := source
    common := common
    target := target
    compositum_eq_top := compositum_eq_top
    intersection := intersection
    mem_intersection_iff := mem_intersection_iff
    intersection_degree := intersection_degree
    source_degree := source_degree
    common_degree := common_degree
    target_degree_dvd_common := target_degree_dvd_common
    sourceGroupHom := sourceGroup
    sourceGroupHom_apply := ?_
    sourceCoefficient := sourceCoeff
    sourceCoefficient_apply := fun _ => rfl
    targetGroupHom := targetGroup
    targetGroupHom_apply := fun σ x => AlgEquiv.restrictNormal_commutes σ R x
    targetCoefficient := targetCoeff
    targetCoefficient_apply := fun _ => rfl
    source_frobenius := hsource
    target_frobenius := htarget }, rfl, rfl, rfl, rfl⟩
  intro σ x
  exact AlgEquiv.restrictNormal_commutes
    ((AlgEquiv.restrictScalarsHom K) σ) U x

private theorem baseChange_valuation_classes_eq_of_coboundary
    (a b : Inhomogeneous.C2 (MulRep E W))
    (ha : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) a)
    (hb : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) b)
    (c : Inhomogeneous.C1 (TrivialIntegerRep E W))
    (h : transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) a =
      transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) b +
        Inhomogeneous.d1 (TrivialIntegerRep E W) c) :
    valuationInducedH2 E W (AbstractReciprocity.cocycleClass2 (MulRep E W) a ha) =
      valuationInducedH2 E W (AbstractReciprocity.cocycleClass2 (MulRep E W) b hb) := by
  apply (comparisonH2 (TrivialIntegerRep E W)).injective
  simp [valuationInducedH2]
  change groupCohomology.map (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) 2
      (groupCohomology.H2π (MulRep E W) _) =
    groupCohomology.map (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) 2
      (groupCohomology.H2π (MulRep E W) _)
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply,
    groupCohomology.H2π_eq_iff]
  refine ⟨c, ?_⟩
  ext p
  have hp := congrFun (congrFun h p.1) p.2
  change (valuationCoefficient E W).hom (a p.1 p.2) =
    (valuationCoefficient E W).hom (b p.1 p.2) +
      Inhomogeneous.d1 (TrivialIntegerRep E W) c p.1 p.2 at hp
  change groupCohomology.d₁₂ (TrivialIntegerRep E W) c p =
    (valuationCoefficient E W).hom (a p.1 p.2) -
      (valuationCoefficient E W).hom (b p.1 p.2)
  rw [hp]
  abel

private theorem baseChange_degrees (B : CarryBaseChangeData K E U R W) :
    Module.finrank E W = Module.finrank E R * ramificationIndex K E := by
  let f := residueDegree K E
  have hf : 0 < f := by
    dsimp [f, residueDegree]
    exact (ramificationInvariants_exists K E).choose_spec.choose_spec.2.1
  have hcommon : Module.finrank E W * f = Module.finrank K U := by
    dsimp [f]
    rw [← B.intersection_degree]
    exact B.common_degree
  have hsource := B.source_degree
  rw [finrank_eq_ramificationIndex_mul_residueDegree K E] at hsource
  have hmul : Module.finrank E W * f =
      (Module.finrank E R * ramificationIndex K E) * f := by
    calc
      _ = Module.finrank K U := hcommon
      _ = Module.finrank E R * (ramificationIndex K E * f) := hsource
      _ = _ := by rw [Nat.mul_assoc]
  exact Nat.mul_right_cancel hf hmul

private theorem baseChange_source_valuation_cochain
    (B : CarryBaseChangeData K E U R W) (πK : Uniformizer K)
    (CU : UnramifiedClassData K U B.source πK) :
    transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W)
        (transportedC2 B.sourceGroupHom B.sourceCoefficient CU.cocycle) =
      (ramificationIndex K E : ℤ) • integerCarryCocycle E W B.common := by
  let f := residueDegree K E
  let m := Module.finrank E W
  let N := Module.finrank K U
  have hf : 0 < f := by
    dsimp [f, residueDegree]
    exact (ramificationInvariants_exists K E).choose_spec.choose_spec.2.1
  have hm : 0 < m := Module.finrank_pos
  have hN : m * f = N := by
    dsimp [m, f, N]
    rw [← B.intersection_degree]
    exact B.common_degree
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero N := ⟨Module.finrank_pos.ne'⟩
  have hcoord (σ : W ≃ₐ[E] W) :
      (B.source.frobeniusEquiv.symm (B.sourceGroupHom σ)).toAdd =
        (f * (B.common.frobeniusEquiv.symm σ).toAdd.val : ℕ) := by
    let a := (B.common.frobeniusEquiv.symm σ).toAdd
    have hlt : f * a.val < N := by
      rw [← hN]
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left a.val_lt hf
    apply Multiplicative.ofAdd.injective
    apply B.source.frobeniusEquiv.injective
    have hto (x : Multiplicative (ZMod N)) : Multiplicative.ofAdd x.toAdd = x := rfl
    rw [hto, B.source.frobeniusEquiv.apply_symm_apply,
      B.source.frobeniusEquiv_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    have hsigma : σ = B.common.frobenius ^ a.val := by
      rw [← B.common.frobeniusEquiv_apply a]
      exact (B.common.frobeniusEquiv.apply_symm_apply σ).symm
    rw [hsigma, map_pow, B.source_frobenius, ← pow_mul]
  have hcarry (a b : ZMod m) :
      carryExponent N (f * a.val : ℕ) (f * b.val : ℕ) = carryExponent m a b := by
    have ha : f * a.val < N := by
      rw [← hN]
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left a.val_lt hf
    have hb : f * b.val < N := by
      rw [← hN]
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left b.val_lt hf
    rw [carryExponent, carryExponent, ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    have heq : f * a.val + f * b.val < N ↔ a.val + b.val < m := by
      rw [← hN, ← Nat.mul_add, Nat.mul_comm m f, Nat.mul_lt_mul_left hf]
    simp only [heq]
  letI : IsUnramifiedLocalExtension E W := B.common.unramified
  have hval : normalizedValuation W
      (Units.map (algebraMap U W).toMonoidHom
        (Units.map (algebraMap K U).toMonoidHom πK.val)) =
      ramificationIndex K E := by
    have hembed : Units.map (algebraMap U W).toMonoidHom
          (Units.map (algebraMap K U).toMonoidHom πK.val) =
        Units.map (algebraMap E W).toMonoidHom
          (Units.map (algebraMap K E).toMonoidHom πK.val) := by
      apply Units.ext
      change algebraMap U W (algebraMap K U (πK.val : K)) =
        algebraMap E W (algebraMap K E (πK.val : K))
      rw [← IsScalarTower.algebraMap_apply K U W,
        ← IsScalarTower.algebraMap_apply K E W]
    rw [hembed]
    have hEW := normalizedValuation_algebraMap E W
      (Units.map (algebraMap K E).toMonoidHom πK.val)
    have hKE := normalizedValuation_algebraMap K E πK.val
    calc
      normalizedValuation W (Units.map (algebraMap E W).toMonoidHom
          (Units.map (algebraMap K E).toMonoidHom πK.val)) =
          (1 : ℤ) * normalizedValuation E
            (Units.map (algebraMap K E).toMonoidHom πK.val) := by
        simpa [IsUnramifiedLocalExtension.ramificationIndex_eq_one] using hEW
      _ = (1 : ℤ) * ((ramificationIndex K E : ℤ) *
          normalizedValuation K πK.val) :=
        congrArg (fun z : ℤ => (1 : ℤ) * z) hKE
      _ = ramificationIndex K E := by rw [πK.valuation_eq_one]; norm_num
  rw [CU.cocycle_eq_carry]
  ext σ τ
  let a := (B.common.frobeniusEquiv.symm σ).toAdd
  let b := (B.common.frobeniusEquiv.symm τ).toAdd
  change normalizedValuation W (Additive.toMul (B.sourceCoefficient.hom
      (if carryExponent N
          (B.source.frobeniusEquiv.symm (B.sourceGroupHom σ)).toAdd
          (B.source.frobeniusEquiv.symm (B.sourceGroupHom τ)).toAdd = 0 then 0
       else Additive.ofMul (Units.map (algebraMap K U).toMonoidHom πK.val)))) =
    (ramificationIndex K E : ℤ) * (carryExponent m a b : ℤ)
  rw [hcoord, hcoord, hcarry]
  by_cases hc : carryExponent m a b = 0
  · rw [if_pos hc, map_zero, hc]
    change normalizedValuation W (1 : Units W) = 0
    simp [normalizedValuation]
  · have hle : carryExponent m a b ≤ 1 := by
      simp only [carryExponent]
      split_ifs <;> omega
    have hone : carryExponent m a b = 1 := by omega
    rw [if_neg hc]
    let x : Units U := Units.map (algebraMap K U).toMonoidHom πK.val
    have hcoeff := B.sourceCoefficient_apply x
    calc
      normalizedValuation W (Additive.toMul (B.sourceCoefficient.hom
          (Additive.ofMul x))) =
          normalizedValuation W (Units.map (algebraMap U W).toMonoidHom x) :=
        congrArg (normalizedValuation W) hcoeff
      _ = ramificationIndex K E := hval
      _ = (ramificationIndex K E : ℤ) * (carryExponent m a b : ℤ) := by
        rw [hone, Int.natCast_one, mul_one]

private theorem baseChange_target_valuation_cochain
    (B : CarryBaseChangeData K E U R W) (πE : Uniformizer E)
    (CR : UnramifiedClassData E R B.target πE) :
    ∃ c : Inhomogeneous.C1 (TrivialIntegerRep E W),
      transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W)
          (transportedC2 B.targetGroupHom B.targetCoefficient CR.cocycle) =
        (ramificationIndex K E : ℤ) • integerCarryCocycle E W B.common +
          Inhomogeneous.d1 (TrivialIntegerRep E W) c := by
  let r := Module.finrank E R
  let e := ramificationIndex K E
  let m := Module.finrank E W
  have hr : 0 < r := Module.finrank_pos
  have he : 0 < e := by
    dsimp [e, ramificationIndex]
    exact (ramificationInvariants_exists K E).choose_spec.choose_spec.1
  have hm : r * e = m := by
    simpa [r, e, m] using (baseChange_degrees K E U R W B).symm
  have hmpos : 0 < m := Module.finrank_pos
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero m := ⟨hmpos.ne'⟩
  have horder : orderOf B.target.frobenius = r := by
    rw [orderOf_eq_card_of_zpowers_eq_top B.target.frobenius_generates,
      IsGalois.card_aut_eq_finrank E R]
  have hcoord (σ : W ≃ₐ[E] W) :
      (B.target.frobeniusEquiv.symm (B.targetGroupHom σ)).toAdd =
        ((B.common.frobeniusEquiv.symm σ).toAdd.val : ℕ) := by
    let a := (B.common.frobeniusEquiv.symm σ).toAdd
    apply Multiplicative.ofAdd.injective
    apply B.target.frobeniusEquiv.injective
    have hto (x : Multiplicative (ZMod r)) : Multiplicative.ofAdd x.toAdd = x := rfl
    rw [hto, B.target.frobeniusEquiv.apply_symm_apply,
      B.target.frobeniusEquiv_apply, ZMod.val_natCast]
    have hsigma : σ = B.common.frobenius ^ a.val := by
      rw [← B.common.frobeniusEquiv_apply a]
      exact (B.common.frobeniusEquiv.apply_symm_apply σ).symm
    have hq : B.targetGroupHom σ = B.target.frobenius ^ a.val := by
      rw [hsigma, map_pow, B.target_frobenius]
    rw [hq]
    change B.target.frobenius ^ a.val = B.target.frobenius ^ (a.val % r)
    rw [← horder, pow_mod_orderOf]
  letI : IsUnramifiedLocalExtension E W := B.common.unramified
  have hval : normalizedValuation W
      (Units.map (algebraMap R W).toMonoidHom
        (Units.map (algebraMap E R).toMonoidHom πE.val)) = 1 := by
    have hembed : Units.map (algebraMap R W).toMonoidHom
          (Units.map (algebraMap E R).toMonoidHom πE.val) =
        Units.map (algebraMap E W).toMonoidHom πE.val := by
      apply Units.ext
      change algebraMap R W (algebraMap E R (πE.val : E)) = algebraMap E W (πE.val : E)
      rw [IsScalarTower.algebraMap_apply E R W]
    rw [hembed]
    have hEW := normalizedValuation_algebraMap E W πE.val
    rw [IsUnramifiedLocalExtension.ramificationIndex_eq_one,
      πE.valuation_eq_one] at hEW
    norm_num at hEW
    exact hEW
  let c : Inhomogeneous.C1 (TrivialIntegerRep E W) := fun σ =>
    -(((B.common.frobeniusEquiv.symm σ).toAdd.val / r : ℕ) : ℤ)
  refine ⟨c, ?_⟩
  rw [CR.cocycle_eq_carry]
  ext σ τ
  let a := (B.common.frobeniusEquiv.symm σ).toAdd
  let b := (B.common.frobeniusEquiv.symm τ).toAdd
  have ha := a.val_lt
  have hb := b.val_lt
  have hablt : a.val + b.val < 2 * m := by omega
  have hsumcoord :
      (B.common.frobeniusEquiv.symm (σ * τ)).toAdd.val = (a.val + b.val) % m := by
    have hmul (x y : Multiplicative (ZMod m)) : (x * y).toAdd = x.toAdd + y.toAdd := rfl
    rw [map_mul, hmul, ZMod.val_add]
  have hcr : carryExponent r (a.val : ℕ) (b.val : ℕ) =
      if a.val % r + b.val % r < r then 0 else 1 := by
    rw [carryExponent, ZMod.val_natCast, ZMod.val_natCast]
  have hcm : carryExponent m a b = if a.val + b.val < m then 0 else 1 := rfl
  have hadddiv := Nat.add_div (a := a.val) (b := b.val) hr
  have hcombNat :
      carryExponent r (a.val : ℕ) (b.val : ℕ) + b.val / r + a.val / r =
        e * carryExponent m a b + ((a.val + b.val) % m) / r := by
    rw [hcr, hcm]
    by_cases hbig : a.val + b.val < m
    · simp only [if_pos hbig, Nat.mod_eq_of_lt hbig, mul_zero, zero_add]
      split_ifs with hsmall
      · have hi : ¬r ≤ a.val % r + b.val % r := by omega
        rw [if_neg hi] at hadddiv
        omega
      · have hi : r ≤ a.val % r + b.val % r := by omega
        rw [if_pos hi] at hadddiv
        omega
    · simp only [if_neg hbig, mul_one]
      have hle : m ≤ a.val + b.val := Nat.le_of_not_gt hbig
      have hmod : (a.val + b.val) % m = a.val + b.val - m := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt]
        omega
      rw [hmod]
      have hq : (a.val + b.val - m) / r + e = (a.val + b.val) / r := by
        have heq : (a.val + b.val - m) + r * e = a.val + b.val := by
          rw [hm, Nat.sub_add_cancel hle]
        nth_rw 2 [← heq]
        rw [Nat.add_mul_div_left _ _ hr]
      split_ifs with hsmall
      · have hi : ¬r ≤ a.val % r + b.val % r := by omega
        rw [if_neg hi] at hadddiv
        omega
      · have hi : r ≤ a.val % r + b.val % r := by omega
        rw [if_pos hi] at hadddiv
        omega
  have hcomb : (carryExponent r (a.val : ℕ) (b.val : ℕ) : ℤ) =
      (e : ℤ) * carryExponent m a b +
        (-((b.val / r : ℕ) : ℤ) -
          -((((a.val + b.val) % m) / r : ℕ) : ℤ) +
          -((a.val / r : ℕ) : ℤ)) := by
    have hcombInt :
        (carryExponent r (a.val : ℕ) (b.val : ℕ) : ℤ) + (b.val / r : ℕ) +
            (a.val / r : ℕ) =
          (e : ℤ) * carryExponent m a b + ((a.val + b.val) % m) / r := by
      exact_mod_cast hcombNat
    omega
  have hleft : normalizedValuation W (Additive.toMul (B.targetCoefficient.hom
      (if carryExponent r
          (B.target.frobeniusEquiv.symm (B.targetGroupHom σ)).toAdd
          (B.target.frobeniusEquiv.symm (B.targetGroupHom τ)).toAdd = 0 then 0
       else Additive.ofMul (Units.map (algebraMap E R).toMonoidHom πE.val)))) =
      (carryExponent r (a.val : ℕ) (b.val : ℕ) : ℤ) := by
    rw [hcoord, hcoord]
    by_cases hc : carryExponent r (a.val : ℕ) (b.val : ℕ) = 0
    · rw [if_pos hc, map_zero, hc]
      change normalizedValuation W (1 : Units W) = 0
      simp [normalizedValuation]
    · have hle1 : carryExponent r (a.val : ℕ) (b.val : ℕ) ≤ 1 := by
        simp only [carryExponent]
        split_ifs <;> omega
      have hone : carryExponent r (a.val : ℕ) (b.val : ℕ) = 1 := by omega
      rw [if_neg hc]
      let x : Units R := Units.map (algebraMap E R).toMonoidHom πE.val
      have hcoeff := B.targetCoefficient_apply x
      calc
        normalizedValuation W (Additive.toMul (B.targetCoefficient.hom
            (Additive.ofMul x))) =
            normalizedValuation W (Units.map (algebraMap R W).toMonoidHom x) :=
          congrArg (normalizedValuation W) hcoeff
        _ = 1 := hval
        _ = (carryExponent r (a.val : ℕ) (b.val : ℕ) : ℤ) := by rw [hone]; norm_num
  change normalizedValuation W (Additive.toMul (B.targetCoefficient.hom
      (if carryExponent r
          (B.target.frobeniusEquiv.symm (B.targetGroupHom σ)).toAdd
          (B.target.frobeniusEquiv.symm (B.targetGroupHom τ)).toAdd = 0 then 0
       else Additive.ofMul (Units.map (algebraMap E R).toMonoidHom πE.val)))) =
    (e : ℤ) * (carryExponent m a b : ℤ) +
      ((TrivialIntegerRep E W).ρ σ (c τ) - c (σ * τ) + c σ)
  rw [hleft]
  change (carryExponent r (a.val : ℕ) (b.val : ℕ) : ℤ) =
    (e : ℤ) * (carryExponent m a b : ℤ) +
      (-((b.val / r : ℕ) : ℤ) -
        -((((B.common.frobeniusEquiv.symm (σ * τ)).toAdd.val / r : ℕ)) : ℤ) +
        -((a.val / r : ℕ) : ℤ))
  rw [hsumcoord]
  exact hcomb

set_option maxHeartbeats 800000 in
-- The two nested transported cocycle proofs need extra elaboration budget.
private theorem baseChange_class_eq
    (B : CarryBaseChangeData K E U R W) (πK : Uniformizer K) (πE : Uniformizer E)
    (CU : UnramifiedClassData K U B.source πK)
    (CR : UnramifiedClassData E R B.target πE) :
    transportedH2 B.sourceGroupHom B.sourceCoefficient CU.class =
      transportedH2 B.targetGroupHom B.targetCoefficient CR.class := by
  let sC := transportedC2 B.sourceGroupHom B.sourceCoefficient CU.cocycle
  have hs : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) sC :=
    transportedC2_mem B.sourceGroupHom B.sourceCoefficient CU.cocycle CU.cocycle_mem
  let tC := transportedC2 B.targetGroupHom B.targetCoefficient CR.cocycle
  have ht : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) tC :=
    transportedC2_mem B.targetGroupHom B.targetCoefficient CR.cocycle CR.cocycle_mem
  have hsclass :
      transportedH2 B.sourceGroupHom B.sourceCoefficient CU.class =
        AbstractReciprocity.cocycleClass2 (MulRep E W) sC hs := by
    rw [CU.class_eq_cocycle]
    exact transportedH2_cocycleClass_eq B.sourceGroupHom B.sourceCoefficient
      CU.cocycle CU.cocycle_mem sC hs rfl
  have htclass :
      transportedH2 B.targetGroupHom B.targetCoefficient CR.class =
        AbstractReciprocity.cocycleClass2 (MulRep E W) tC ht := by
    rw [CR.class_eq_cocycle]
    exact transportedH2_cocycleClass_eq B.targetGroupHom B.targetCoefficient
      CR.cocycle CR.cocycle_mem tC ht rfl
  have hsmap := baseChange_source_valuation_cochain K E U R W B πK CU
  obtain ⟨c, htmap⟩ := baseChange_target_valuation_cochain K E U R W B πE CR
  have hmaps : transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) sC =
      transportedC2 (.id (W ≃ₐ[E] W)) (valuationCoefficient E W) tC +
        Inhomogeneous.d1 (TrivialIntegerRep E W) (-c) := by
    rw [hsmap, htmap, map_neg]
    abel
  have hval := baseChange_valuation_classes_eq_of_coboundary E W
    sC tC hs ht (-c) hmaps
  obtain ⟨CW⟩ := carryCocycle_isGenerator E W B.common πE
  exact hsclass.trans
    ((CW.valuation_h2_bijective.1 hval).trans htclass.symm)

private theorem baseChange_coboundary
    (B : CarryBaseChangeData K E U R W) (πK : Uniformizer K) (πE : Uniformizer E)
    (CU : UnramifiedClassData K U B.source πK)
    (CR : UnramifiedClassData E R B.target πE)
    (hclass : transportedH2 B.sourceGroupHom B.sourceCoefficient CU.class =
      transportedH2 B.targetGroupHom B.targetCoefficient CR.class) :
    ∃ b : Inhomogeneous.C1 (MulRep E W),
      transportedC2 B.sourceGroupHom B.sourceCoefficient CU.cocycle -
          transportedC2 B.targetGroupHom B.targetCoefficient CR.cocycle =
        Inhomogeneous.d1 (MulRep E W) b := by
  let sC := transportedC2 B.sourceGroupHom B.sourceCoefficient CU.cocycle
  have hs : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) sC :=
    transportedC2_mem B.sourceGroupHom B.sourceCoefficient CU.cocycle CU.cocycle_mem
  let tC := transportedC2 B.targetGroupHom B.targetCoefficient CR.cocycle
  have ht : AbstractReciprocity.IsNormalizedCocycle2 (MulRep E W) tC :=
    transportedC2_mem B.targetGroupHom B.targetCoefficient CR.cocycle CR.cocycle_mem
  have hsclass :
      transportedH2 B.sourceGroupHom B.sourceCoefficient CU.class =
        AbstractReciprocity.cocycleClass2 (MulRep E W) sC hs := by
    rw [CU.class_eq_cocycle]
    exact transportedH2_cocycleClass_eq B.sourceGroupHom B.sourceCoefficient
      CU.cocycle CU.cocycle_mem sC hs rfl
  have htclass :
      transportedH2 B.targetGroupHom B.targetCoefficient CR.class =
        AbstractReciprocity.cocycleClass2 (MulRep E W) tC ht := by
    rw [CR.class_eq_cocycle]
    exact transportedH2_cocycleClass_eq B.targetGroupHom B.targetCoefficient
      CR.cocycle CR.cocycle_mem tC ht rfl
  have hcoc : AbstractReciprocity.cocycleClass2 (MulRep E W) sC hs =
      AbstractReciprocity.cocycleClass2 (MulRep E W) tC ht :=
    hsclass.symm.trans (hclass.trans htclass)
  exact exists_d1_of_cocycleClass_eq (MulRep E W) sC tC hs ht hcoc

/--
**F07**, Proposition `prop:fundamental-restriction` (base-change carry lemma): restriction of the
`K_{rs}/K` carry class to the common envelope equals inflation of the degree-`r` carry class over
`E`.  Equivalently, the invariant is multiplied by `[E:K]`.  The first conjunct is the required
pre-cohomology coboundary calculation; the second compares classes through the two actual
`transportedH2` maps.
-/
theorem carryClass_baseChange
    (B : CarryBaseChangeData K E U R W) (πK : Uniformizer K) (πE : Uniformizer E)
    (CU : UnramifiedClassData K U B.source πK)
    (CR : UnramifiedClassData E R B.target πE) :
    (∃ b : Inhomogeneous.C1 (MulRep E W),
      transportedC2 B.sourceGroupHom B.sourceCoefficient CU.cocycle -
          transportedC2 B.targetGroupHom B.targetCoefficient CR.cocycle =
        Inhomogeneous.d1 (MulRep E W) b) ∧
      transportedH2 B.sourceGroupHom B.sourceCoefficient CU.class =
        transportedH2 B.targetGroupHom B.targetCoefficient CR.class := by
  have hclass := baseChange_class_eq K E U R W B πK πE CU CR
  exact ⟨baseChange_coboundary K E U R W B πK πE CU CR hclass, hclass⟩

end BaseChange

end

end NU.LCFT
