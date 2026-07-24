import Submission.NU.Chebotarev.Density

/-!
# M2. Arithmetic Frobenius

Element-valued Frobenius is defined first, as required by blueprint §3 and the
design caution in §10.5(1). Conjugacy classes and prime sets are introduced only
after the chosen-prime API.
-/

open Filter Topology
open scoped Pointwise

namespace NU.Chebotarev

variable {K L : Type*} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]

/-- The arithmetic Frobenius chosen by Mathlib at an upstairs prime. This is the
element-valued object used by all tower lemmas (blueprint §3). -/
noncomputable def arithFrobeniusAt
    [FiniteDimensional K L] [IsGalois K L] (P : PrimeIdeal L) : Gal(L/K) :=
  arithFrobAt (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal

/-- A prime of `K` is unramified in `L` when every prime above it is unramified.
No Frobenius value is assigned at ramified primes (blueprint §3 and §10.2). -/
def IsUnramifiedPrime (p : PrimeIdeal K) : Prop :=
  ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal

/-- The decomposition subgroup at a chosen upstairs prime (blueprint §3). -/
def decompositionSubgroup [FiniteDimensional K L] [IsGalois K L]
    (P : PrimeIdeal L) : Subgroup (Gal(L/K)) :=
  MulAction.stabilizer (Gal(L/K)) P.asIdeal

/-- The conjugacy class attached to a chosen prime upstairs. Independence of the
choice is the next theorem. -/
noncomputable def frobeniusClassAt
    [FiniteDimensional K L] [IsGalois K L] (P : PrimeIdeal L) :
    ConjClasses (Gal(L/K)) :=
  ConjClasses.mk (arithFrobeniusAt (K := K) (L := L) P)

/-- Blueprint Definition 3.1 and proposed declaration
`frobeniusClass_wellDefined`: primes above the same base prime give the same
class. This is the descent of Mathlib's `isConj_arithFrobAt`. -/
theorem frobeniusClass_wellDefined
    [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeIdeal K) (P Q : PrimeIdeal L)
    (hP : P.asIdeal.LiesOver p.asIdeal)
    (hQ : Q.asIdeal.LiesOver p.asIdeal) :
    frobeniusClassAt (K := K) (L := L) P =
      frobeniusClassAt (K := K) (L := L) Q := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply isConj_arithFrobAt
  rw [← hP.over, ← hQ.over]

/-- A rewrite-friendly predicate for an unramified prime to have Frobenius
class `C` (blueprint §10.2). -/
def HasFrobeniusClass [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeIdeal K) (C : ConjClasses (Gal(L/K))) : Prop :=
  IsUnramifiedPrime (L := L) p ∧
    ∃ P : PrimeIdeal L,
      P.asIdeal.LiesOver p.asIdeal ∧
        frobeniusClassAt (K := K) (L := L) P = C

/-- Element-valued version of `HasFrobeniusClass`, useful for abelian and cyclic
extensions. The choice of upstairs prime remains explicit (blueprint §10.5(1)). -/
def HasFrobeniusElement [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeIdeal K) (g : Gal(L/K)) : Prop :=
  IsUnramifiedPrime (L := L) p ∧
    ∃ P : PrimeIdeal L,
      P.asIdeal.LiesOver p.asIdeal ∧
        arithFrobeniusAt (K := K) (L := L) P = g

/-- The Chebotarev prime set for a conjugacy class (blueprint Theorem 1.2). -/
def frobeniusPrimeSet [FiniteDimensional K L] [IsGalois K L]
    (C : ConjClasses (Gal(L/K))) : Set (PrimeIdeal K) :=
  {p | HasFrobeniusClass (L := L) p C}

/-- The element-valued Frobenius prime set used for cyclic/abelian extensions. -/
def frobeniusElementPrimeSet [FiniteDimensional K L] [IsGalois K L]
    (g : Gal(L/K)) : Set (PrimeIdeal K) :=
  {p | HasFrobeniusElement (L := L) p g}

/-- Blueprint Lemma 3.2, proposed declaration
`arithFrobAt_order_eq_inertiaDeg`: at an unramified prime, the order of
arithmetic Frobenius is the residue degree. -/
theorem arithFrobAt_order_eq_inertiaDeg
    [FiniteDimensional K L] [IsGalois K L]
    (P : PrimeIdeal L)
    (hP : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal) :
    orderOf (arithFrobeniusAt (K := K) (L := L) P) =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  let G := Gal(L/K)
  let p : Ideal R := P.asIdeal.under R
  letI : p.IsPrime := inferInstance
  letI : p.IsMaximal := inferInstance
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : Fintype (R ⧸ p) := Fintype.ofFinite (R ⧸ p)
  letI : Fintype (S ⧸ P.asIdeal) := Fintype.ofFinite (S ⧸ P.asIdeal)
  letI := Localization.AtPrime.algebraOfLiesOver p P.asIdeal
  let σ : MulAction.stabilizer G P.asIdeal :=
    ⟨arithFrobeniusAt (K := K) (L := L) P,
      IsArithFrobAt.arithFrobAt_mem_stabilizer R G P.asIdeal⟩
  let ρ := Ideal.Quotient.stabilizerHom P.asIdeal p G
  have hram : P.asIdeal.ramificationIdx R = 1 := by
    letI : Algebra.IsUnramifiedAt R P.asIdeal := hP
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hIcard : Nat.card (P.asIdeal.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P.asIdeal G]
    exact hram
  have hIcard' :
      Nat.card (P.asIdeal.inertia (MulAction.stabilizer G P.asIdeal)) = 1 := by
    change Nat.card
      (P.asIdeal.toAddSubgroup.inertia (MulAction.stabilizer G P.asIdeal)) = 1
    rw [← AddSubgroup.subgroupOf_inertia]
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) P.asIdeal)).toEquiv]
    exact hIcard
  have hker : ρ.ker = ⊥ := by
    rw [Ideal.Quotient.ker_stabilizerHom]
    exact Subgroup.card_eq_one.mp hIcard'
  have hρinj : Function.Injective ρ :=
    (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have himage :
      ρ σ = FiniteField.frobeniusAlgEquivOfAlgebraic
        (R ⧸ p) (S ⧸ P.asIdeal) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk P.asIdeal
      ((MulSemiringAction.toAlgHom R S (arithFrobAt R G P.asIdeal)) x) = _
    rw [(IsArithFrobAt.arithFrobAt R G P.asIdeal).mk_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    congr 1
    exact Nat.card_eq_fintype_card
  have hordσ : orderOf σ = P.asIdeal.inertiaDeg R := by
    rw [← orderOf_injective ρ hρinj σ, himage,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      ← Ideal.inertiaDeg_eq_of_isMaximal p P.asIdeal]
  rw [← hordσ]
  exact orderOf_injective (Subgroup.subtype _) Subtype.coe_injective σ

/-- Blueprint Lemma 3.2 (`arithFrobAt_generates_decomposition`): unramified
Frobenius generates the decomposition subgroup. -/
theorem arithFrobAt_generates_decomposition
    [FiniteDimensional K L] [IsGalois K L]
    (P : PrimeIdeal L)
    (hP : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) P.asIdeal) :
    decompositionSubgroup (K := K) (L := L) P =
      Subgroup.zpowers (arithFrobeniusAt (K := K) (L := L) P) := by
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · exact Subgroup.zpowers_le.mpr
      (IsArithFrobAt.arithFrobAt_mem_stabilizer
        (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal)
  · rw [Nat.card_zpowers, arithFrobAt_order_eq_inertiaDeg P hP]
    unfold decompositionSubgroup
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := hP
    rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank
      (P.asIdeal.under (NumberField.RingOfIntegers K)) P.asIdeal,
      Ideal.card_inertia_eq_ramificationIdxIn
        (P.asIdeal.under (NumberField.RingOfIntegers K)) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx
        (P.asIdeal.under (NumberField.RingOfIntegers K)) P.asIdeal (Gal(L/K)),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]

private theorem arithFrobAt_pow_mod
    [FiniteDimensional K L] [IsGalois K L]
    (P : PrimeIdeal L) (n : ℕ) (x : NumberField.RingOfIntegers L) :
    Ideal.Quotient.mk P.asIdeal
      ((arithFrobeniusAt (K := K) (L := L) P ^ n) • x) =
    Ideal.Quotient.mk P.asIdeal
      (x ^ (Nat.card (NumberField.RingOfIntegers K ⧸
        P.asIdeal.under (NumberField.RingOfIntegers K))) ^ n) := by
  let N := Nat.card (NumberField.RingOfIntegers K ⧸
    P.asIdeal.under (NumberField.RingOfIntegers K))
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_smul]
      rw [ih]
      rw [map_pow]
      change (Ideal.Quotient.mk P.asIdeal
        ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)
          (arithFrobAt (NumberField.RingOfIntegers K)
            (Gal(L/K)) P.asIdeal)) x)) ^ _ = _
      rw [(IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
        (Gal(L/K)) P.asIdeal).mk_apply]
      rw [← pow_mul]
      congr 2
      simp [Nat.pow_succ, Nat.mul_comm]

/-- Blueprint Lemma 3.3, proposed declaration `arithFrobAt_restrict_pow`:
in a tower `K ⊆ E ⊆ L`, Frobenius over `E`, included into `Gal(L/K)`, is the
`f(q/p)`-th power of Frobenius over `K`. -/
theorem arithFrobAt_restrict_pow
    {E : Type*} [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K L] [FiniteDimensional E L]
    [IsGalois K L] [IsGalois E L]
    (P : PrimeIdeal L) (q : PrimeIdeal E)
    (hPq : P.asIdeal.LiesOver q.asIdeal)
    (hunr : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) P.asIdeal) :
    AlgEquiv.restrictScalarsHom K (arithFrobeniusAt (K := E) P) =
      arithFrobeniusAt (K := K) P ^
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  let G := Gal(L/K)
  let s := arithFrobeniusAt (K := K) (L := L) P
  let m := q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  let i : Gal(L/E) →* G := AlgEquiv.restrictScalarsHom K
  let D : Subgroup G := Subgroup.zpowers s
  let H : Subgroup G := i.range
  let J : Subgroup D := H.comap (Subgroup.subtype D)
  have hunrE : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers E) P.asIdeal := by
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := hunr
    exact Algebra.IsUnramifiedAt.of_restrictScalars
      (NumberField.RingOfIntegers K) P.asIdeal
  have hDK : decompositionSubgroup (K := K) (L := L) P = D := by
    exact arithFrobAt_generates_decomposition P hunr
  let fromDE : decompositionSubgroup (K := E) (L := L) P → J := fun t => by
    have hitD : i t.val ∈ D := by
      rw [← hDK]
      apply MulAction.mem_stabilizer_iff.mpr
      exact MulAction.mem_stabilizer_iff.mp t.prop
    exact ⟨⟨i t.val, hitD⟩, ⟨t.val, rfl⟩⟩
  have hfromDE_inj : Function.Injective fromDE := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.restrictScalarsHom_injective K
    exact congrArg (fun j : J => (j.val.val : G)) hab
  have hfromDE_surj : Function.Surjective fromDE := by
    intro j
    have hjH : (j.val.val : G) ∈ H := j.prop
    let t : Gal(L/E) := Classical.choose hjH
    have ht : i t = (j.val.val : G) := Classical.choose_spec hjH
    have htstab : t ∈ decompositionSubgroup (K := E) (L := L) P := by
      apply MulAction.mem_stabilizer_iff.mpr
      have hjD : (j.val.val : G) ∈ decompositionSubgroup (K := K) (L := L) P := by
        rw [hDK]
        exact j.val.prop
      have hfix : (j.val.val : G) • P.asIdeal = P.asIdeal :=
        MulAction.mem_stabilizer_iff.mp hjD
      change i t • P.asIdeal = P.asIdeal
      rw [ht]
      exact hfix
    refine ⟨⟨t, htstab⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ht
  have hJcard : Nat.card J =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
    rw [Nat.card_congr (Equiv.ofBijective fromDE ⟨hfromDE_inj, hfromDE_surj⟩).symm]
    rw [arithFrobAt_generates_decomposition P hunrE, Nat.card_zpowers,
      arithFrobAt_order_eq_inertiaDeg P hunrE]
  have hDcard : Nat.card D =
      P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [Nat.card_zpowers, arithFrobAt_order_eq_inertiaDeg P hunr]
  have htower := Ideal.inertiaDeg_tower
    (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers E)
    (T := NumberField.RingOfIntegers L) q.asIdeal P.asIdeal
  letI : IsMulCommutative D := Subgroup.zpowers_isMulCommutative s
  letI : J.Normal := Subgroup.normal_of_isMulCommutative J
  have hindex : J.index = m := by
    have hc := Subgroup.card_mul_index J
    rw [hJcard, hDcard, htower] at hc
    apply Nat.mul_left_cancel
      (P.asIdeal.inertiaDeg_pos (NumberField.RingOfIntegers E))
    simpa [Nat.mul_comm] using hc
  have hpowJ := J.pow_index_mem (⟨s, Subgroup.mem_zpowers s⟩ : D)
  rw [hindex] at hpowJ
  have hpowH : s ^ m ∈ H := hpowJ
  obtain ⟨t : Gal(L/E), ht⟩ := hpowH
  have htArith : IsArithFrobAt (NumberField.RingOfIntegers E) t P.asIdeal := by
    intro x
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
    have hp := arithFrobAt_pow_mod (K := K) P m x
    have hcard : Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) ^ m =
        Nat.card (NumberField.RingOfIntegers E ⧸
          P.asIdeal.under (NumberField.RingOfIntegers E)) := by
      change Ideal.absNorm (P.asIdeal.under (NumberField.RingOfIntegers K)) ^ m =
        Ideal.absNorm (P.asIdeal.under (NumberField.RingOfIntegers E))
      rw [← Ideal.under_under (B := NumberField.RingOfIntegers E) P.asIdeal,
        ← hPq.over]
      exact Ideal.absNorm_pow_inertiaDeg
        (q.asIdeal.under (NumberField.RingOfIntegers K)) q.asIdeal
    rw [← hcard]
    change Ideal.Quotient.mk P.asIdeal (i t • x) = _
    rw [ht]
    exact hp
  letI : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers E) P.asIdeal := hunrE
  have heq := htArith.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers E)
      (Gal(L/E)) P.asIdeal) P.asIdeal.primeCompl_le_nonZeroDivisors
  have htEq : t = arithFrobeniusAt (K := E) (L := L) P := by
    have hfield : t.toRingEquiv.toRingHom =
        (arithFrobeniusAt (K := E) (L := L) P).toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers L)
      intro x
      exact congrArg Subtype.val (DFunLike.congr_fun heq x)
    ext x
    exact DFunLike.congr_fun hfield x
  rw [← htEq, ht]

/-- Blueprint Lemma 3.4, proposed declaration `arithFrobAt_restrict`: for a
Galois intermediate extension, restriction carries Frobenius to Frobenius. -/
theorem arithFrobAt_restrict
    {M : Type*} [Field M] [NumberField M]
    [Algebra K M] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M] [Normal K M]
    (P : PrimeIdeal L) (Q : PrimeIdeal M)
    (hPQ : P.asIdeal.LiesOver Q.asIdeal)
    (hunr : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) P.asIdeal) :
    AlgEquiv.restrictNormalHom M (arithFrobeniusAt (K := K) P) =
      arithFrobeniusAt (K := K) Q := by
  let s := arithFrobeniusAt (K := K) (L := L) P
  let r : Gal(M/K) := AlgEquiv.restrictNormalHom M s
  have hunrQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.asIdeal := by
    letI : P.asIdeal.LiesOver Q.asIdeal := hPQ
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) P.asIdeal := hunr
    exact Algebra.IsUnramifiedAt.of_liesOver
      (NumberField.RingOfIntegers K) Q.asIdeal P.asIdeal
  have hr : IsArithFrobAt (NumberField.RingOfIntegers K) r Q.asIdeal := by
    intro x
    rw [hPQ.over, Ideal.mem_under, Ideal.under_under]
    have hs := (IsArithFrobAt.arithFrobAt
      (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal)
      (algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers L) x)
    have hact : algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers L)
        ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers M) r) x) =
        (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L) s)
          (algebraMap (NumberField.RingOfIntegers M)
            (NumberField.RingOfIntegers L) x) := by
      apply NumberField.RingOfIntegers.coe_injective (K := L)
      change algebraMap M L
          (r (algebraMap (NumberField.RingOfIntegers M) M x)) =
        s (algebraMap M L
          (algebraMap (NumberField.RingOfIntegers M) M x))
      exact AlgEquiv.restrictNormal_commutes s M
        (algebraMap (NumberField.RingOfIntegers M) M x)
    change (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) s)
        (algebraMap (NumberField.RingOfIntegers M)
          (NumberField.RingOfIntegers L) x) -
      (algebraMap (NumberField.RingOfIntegers M)
        (NumberField.RingOfIntegers L) x) ^
        Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) ∈ P.asIdeal at hs
    simpa only [map_sub, map_pow, hact] using hs
  letI : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.asIdeal := hunrQ
  have heq := hr.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
      (Gal(M/K)) Q.asIdeal) Q.asIdeal.primeCompl_le_nonZeroDivisors
  have hfield : r.toRingEquiv.toRingHom =
      (arithFrobeniusAt (K := K) (L := M) Q).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers M)
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun heq x)
  ext x
  exact DFunLike.congr_fun hfield x

/-- Blueprint Lemma 3.5 (`arithFrobAt_apply_rootOfUnity`): arithmetic
Frobenius acts on an `m`-th root of unity by the absolute norm exponent, away
from residue characteristic dividing `m`. -/
theorem arithFrobAt_apply_rootOfUnity
    [FiniteDimensional K L] [IsGalois K L]
    (p : PrimeIdeal K) (P : PrimeIdeal L)
    (hPp : P.asIdeal.LiesOver p.asIdeal)
    (hunr : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) P.asIdeal)
    (m : ℕ) (ζ : L) (hζ : ζ ^ m = 1)
    (hm : algebraMap ℤ (NumberField.RingOfIntegers L) (m : ℤ) ∉ P.asIdeal) :
    arithFrobeniusAt (K := K) (L := L) P ζ = ζ ^ PrimeIdeal.norm p := by
  let ζ' : NumberField.RingOfIntegers L := ⟨ζ, by
    refine ⟨Polynomial.X ^ m - 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (by
        intro hm0
        apply hm
        simp [hm0])
    · simpa [Polynomial.eval₂_sub, Polynomial.eval₂_pow] using sub_eq_zero.mpr hζ⟩
  have hζ' : ζ' ^ m = 1 := by
    apply NumberField.RingOfIntegers.coe_injective (K := L)
    exact hζ
  have hmain := (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K)
    (Gal(L/K)) P.asIdeal).apply_of_pow_eq_one hζ' (by simpa [ζ'] using hm)
  change algebraMap (NumberField.RingOfIntegers L) L
    ((arithFrobAt (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal) • ζ') = _
  change algebraMap (NumberField.RingOfIntegers L) L
    ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)
      (arithFrobAt (NumberField.RingOfIntegers K) (Gal(L/K)) P.asIdeal)) ζ') = _
  rw [hmain]
  simp only [map_pow]
  change ζ ^ Nat.card (NumberField.RingOfIntegers K ⧸
    Ideal.under (NumberField.RingOfIntegers K) P.asIdeal) =
      ζ ^ Ideal.absNorm p.asIdeal
  rw [hPp.over]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot, AddSubgroup.index_eq_card]
  apply congrArg (ζ ^ ·)
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl _) ?_
  intro x y
  change (QuotientAddGroup.leftRel
    (Ideal.under (NumberField.RingOfIntegers K) P.asIdeal).toAddSubgroup) x y ↔ _
  rfl

/-- Blueprint §3 (`ramifiedPrimes_finite`): only finitely many base primes
ramify in a finite extension. -/
theorem ramifiedPrimes_finite
    [FiniteDimensional K L] [IsGalois K L] :
    {p : PrimeIdeal K | ¬ IsUnramifiedPrime (L := L) p}.Finite := by
  classical
  let A := NumberField.RingOfIntegers K
  let B := NumberField.RingOfIntegers L
  let I : Ideal B := differentIdeal A B
  have hI : I ≠ ⊥ := differentIdeal_ne_bot
  letI : NeZero I := ⟨hI⟩
  letI : Finite (B ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  let ramUp : Set (PrimeIdeal L) := {P | P.asIdeal ∣ I}
  have hramUp : ramUp.Finite := by
    apply Set.Finite.of_finite_image
      (f := fun P : PrimeIdeal L => P.asIdeal.map (Ideal.Quotient.mk I))
    · exact Set.toFinite _
    · intro P hP Q hQ hPQ
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      have heq := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hPQ
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at heq
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker, sup_eq_left.mpr (Ideal.dvd_iff_le.mp hP),
        sup_eq_left.mpr (Ideal.dvd_iff_le.mp hQ)] at heq
      exact heq
  let under : PrimeIdeal L → PrimeIdeal K := fun P =>
    ⟨P.asIdeal.under A, inferInstance, by
      intro h
      letI : P.asIdeal.LiesOver (⊥ : Ideal A) := ⟨by simpa [h]⟩
      exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot A P.asIdeal)⟩
  apply (hramUp.image under).subset
  intro p hp
  simp only [IsUnramifiedPrime, not_forall] at hp
  obtain ⟨P, hP⟩ := hp
  obtain ⟨hPp, hPram⟩ := hP
  refine ⟨P, ?_, ?_⟩
  · exact (dvd_differentIdeal_iff (A := A) (B := B)).mpr hPram
  · apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    exact hPp.over.symm

end NU.Chebotarev
