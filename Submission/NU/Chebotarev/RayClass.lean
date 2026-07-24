import Submission.NU.Chebotarev.Deuring

/-!
# M4. Ray class groups

Blueprint §5.1 and §10.3. The ideal group is represented by the nonzero
fractional ideals whose valuations vanish at every prime dividing the finite
modulus. The quotient is therefore the literal group
`I_K(m₀) / P_{K,1}(m)`.
-/

open scoped nonZeroDivisors

namespace NU.Chebotarev

variable (K : Type*) [Field K] [NumberField K]

/-- A number-field modulus `m = m₀ m∞`: a nonzero integral ideal and a finite
set of real embeddings (blueprint §5.1). -/
structure RayModulus where
  /-- The finite part `m₀`. -/
  finite : Ideal (NumberField.RingOfIntegers K)
  /-- A modulus has nonzero finite part. -/
  finite_ne : finite ≠ 0
  /-- The selected real places `m∞`. -/
  infinite : Finset (K →+* ℝ)

variable {K}

/-- The ambient group of nonzero fractional ideals. -/
abbrev FractionalIdealGroup :=
  (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ

/-- The group `I_K(m₀)` of nonzero fractional ideals prime to `m₀`. Vanishing
of the Dedekind valuations at primes dividing `m₀` is the prime-to condition. -/
noncomputable def RayIdealGroup (m : RayModulus K) :
    Subgroup (FractionalIdealGroup (K := K)) where
  carrier := {I | ∀ p : PrimeIdeal K, p.asIdeal ∣ m.finite →
    FractionalIdeal.count K p
      (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = 0}
  one_mem' := by
    intro p hp
    exact FractionalIdeal.count_one K p
  mul_mem' := by
    intro a b ha hb p hp
    simpa using
      (FractionalIdeal.count_mul K p (Units.ne_zero a) (Units.ne_zero b)).trans
        (by rw [ha p hp, hb p hp, add_zero])
  inv_mem' := by
    intro a ha p hp
    rw [show ((↑(a⁻¹) : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)) = (↑a)⁻¹ by
        exact Units.val_inv_eq_inv_val a]
    rw [FractionalIdeal.count_inv, ha p hp, neg_zero]

/-- The explicit congruence-and-sign condition defining `P_{K,1}(m)`.
The witnesses `β/γ` encode `α ≡ 1 mod m₀` with denominator prime to `m₀`;
the last conjunct imposes positivity at all places in `m∞` (blueprint §5.1). -/
def RayAdmissible (m : RayModulus K) (α : Kˣ) : Prop :=
  (∃ β γ : NumberField.RingOfIntegers K,
    γ ≠ 0 ∧
    algebraMap (NumberField.RingOfIntegers K) K β /
        algebraMap (NumberField.RingOfIntegers K) K γ = (α : K) ∧
    IsCoprime (Ideal.span {β}) m.finite ∧
    IsCoprime (Ideal.span {γ}) m.finite ∧
    β - γ ∈ m.finite) ∧
  ∀ σ ∈ m.infinite, 0 < σ (α : K)

/-- The principal ray subgroup `P_{K,1}(m)`. Taking `closure` gives a subgroup
without hiding closure proofs; the exactness theorem below identifies it with
the admissible principal ideals of blueprint §5.1. -/
noncomputable def RayPrincipalSubgroup (m : RayModulus K) :
    Subgroup (RayIdealGroup m) :=
  Subgroup.closure {I : RayIdealGroup m |
    ∃ α : Kˣ, RayAdmissible m α ∧
      (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
        FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (α : K)}

/-- Blueprint §5.1, proposed declaration `RayClassGroup`:
`Cl_K^m = I_K(m₀) / P_{K,1}(m)`. -/
noncomputable def RayClassGroup (m : RayModulus K) :=
  (RayIdealGroup m) ⧸ RayPrincipalSubgroup m

noncomputable instance (m : RayModulus K) : CommGroup (RayClassGroup m) :=
  inferInstanceAs (CommGroup ((RayIdealGroup m) ⧸ RayPrincipalSubgroup m))

noncomputable instance (m : RayModulus K) : Inhabited (RayClassGroup m) :=
  inferInstanceAs (Inhabited ((RayIdealGroup m) ⧸ RayPrincipalSubgroup m))

namespace RayClassGroup

/-- The quotient map from ideals prime to the modulus to ray classes. -/
noncomputable def mk (m : RayModulus K) :
    RayIdealGroup m →* RayClassGroup m :=
  QuotientGroup.mk' (RayPrincipalSubgroup m)

/-- An integral ideal `a`, necessarily nonzero and prime to `m₀` in uses, has
ray class `c`. This relational form avoids inserting arbitrary classes for
ideals not prime to the modulus. -/
def IsClassOfIdeal (m : RayModulus K)
    (a : Ideal (NumberField.RingOfIntegers K)) (c : RayClassGroup m) : Prop :=
  ∃ I : RayIdealGroup m,
    (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      (a : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ∧
    mk m I = c

/-- The residue-and-sign term
`(O_K/m₀)ˣ × {±1}^{m∞}` in the elementary ray exact sequence. -/
abbrev LocalData (m : RayModulus K) :=
  (NumberField.RingOfIntegers K ⧸ m.finite)ˣ ×
    ((σ : ↥m.infinite) → Multiplicative (ZMod 2))

private theorem rayAdmissible_one (m : RayModulus K) : RayAdmissible m 1 := by
  constructor
  · refine ⟨1, 1, one_ne_zero, ?_, ?_, ?_, ?_⟩
    · simp
    · exact ⟨1, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · simp
  · intro σ hσ
    simp

private theorem rayAdmissible_mul (m : RayModulus K) {a b : Kˣ}
    (ha : RayAdmissible m a) (hb : RayAdmissible m b) :
    RayAdmissible m (a * b) := by
  rcases ha with ⟨⟨β, γ, hγ, hfrac, hβ, hγc, hcong⟩, hpos⟩
  rcases hb with ⟨⟨β', γ', hγ', hfrac', hβ', hγc', hcong'⟩, hpos'⟩
  constructor
  · refine ⟨β * β', γ * γ', mul_ne_zero hγ hγ', ?_, ?_, ?_, ?_⟩
    · push_cast
      rw [mul_div_mul_comm, hfrac, hfrac']
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact hβ.mul_left hβ'
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact hγc.mul_left hγc'
    · show β * β' - γ * γ' ∈ m.finite
      rw [show β * β' - γ * γ' = β * (β' - γ') + (β - γ) * γ' by ring]
      exact m.finite.add_mem
        (m.finite.mul_mem_left β hcong') (m.finite.mul_mem_right γ' hcong)
  · intro σ hσ
    simpa only [Units.val_mul, map_mul] using mul_pos (hpos σ hσ) (hpos' σ hσ)

private theorem rayAdmissible_inv (m : RayModulus K) {a : Kˣ}
    (ha : RayAdmissible m a) : RayAdmissible m a⁻¹ := by
  rcases ha with ⟨⟨β, γ, hγ, hfrac, hβ, hγc, hcong⟩, hpos⟩
  have hβ0 : β ≠ 0 := by
    intro h
    subst β
    simp only [map_zero, zero_div] at hfrac
    exact a.ne_zero hfrac.symm
  constructor
  · refine ⟨γ, β, hβ0, ?_, hγc, hβ, ?_⟩
    · rw [Units.val_inv_eq_inv_val]
      rw [← hfrac, inv_div]
    · simpa only [neg_sub] using m.finite.neg_mem hcong
  · intro σ hσ
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hpos σ hσ)

private def admissiblePrincipalSubgroup (m : RayModulus K) :
    Subgroup (RayIdealGroup m) where
  carrier := {I | ∃ α : Kˣ, RayAdmissible m α ∧
    (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰ (α : K)}
  one_mem' := by
    refine ⟨1, rayAdmissible_one m, ?_⟩
    simp
  mul_mem' := by
    rintro I J ⟨a, ha, hI⟩ ⟨b, hb, hJ⟩
    refine ⟨a * b, rayAdmissible_mul m ha hb, ?_⟩
    change (I.1.1 : FractionalIdeal _ K) * (J.1.1 : FractionalIdeal _ K) = _
    rw [hI, hJ, FractionalIdeal.spanSingleton_mul_spanSingleton]
    rfl
  inv_mem' := by
    rintro I ⟨a, ha, hI⟩
    refine ⟨a⁻¹, rayAdmissible_inv m ha, ?_⟩
    rw [show (I⁻¹).1 = I.1⁻¹ by rfl, Units.val_inv_eq_inv_val,
      hI, FractionalIdeal.spanSingleton_inv]
    rw [Units.val_inv_eq_inv_val]

private noncomputable def rayElementGroup (m : RayModulus K) : Subgroup Kˣ :=
  (RayIdealGroup m).comap
    (toPrincipalIdeal (NumberField.RingOfIntegers K) K)

private noncomputable def principalRayIdeal (m : RayModulus K) :
    rayElementGroup m →* RayIdealGroup m :=
  ((toPrincipalIdeal (NumberField.RingOfIntegers K) K).comp
    (rayElementGroup m).subtype).codRestrict (RayIdealGroup m)
      (fun a ↦ a.2)

private theorem principalRayIdeal_val (m : RayModulus K) (a : rayElementGroup m) :
    ((principalRayIdeal m a).1 :
      FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
        FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
          (((a : Kˣ) : K)) := by
  change ((toPrincipalIdeal (NumberField.RingOfIntegers K) K) (a : Kˣ) :
    FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = _
  exact coe_toPrincipalIdeal (a : Kˣ)

private noncomputable def unitsToRayElements (m : RayModulus K) :
    (NumberField.RingOfIntegers K)ˣ →* rayElementGroup m := by
  let toK : (NumberField.RingOfIntegers K)ˣ →* Kˣ :=
    Units.map (algebraMap (NumberField.RingOfIntegers K) K)
  refine toK.codRestrict (rayElementGroup m) fun u ↦ ?_
  change toPrincipalIdeal (NumberField.RingOfIntegers K) K (toK u) ∈
    RayIdealGroup m
  rw [show toPrincipalIdeal (NumberField.RingOfIntegers K) K (toK u) = 1 by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    change FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
      (algebraMap (NumberField.RingOfIntegers K) K
        (u : NumberField.RingOfIntegers K)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top]]
  exact (RayIdealGroup m).one_mem

private noncomputable def rayToClass (m : RayModulus K) :
    RayIdealGroup m →* ClassGroup (NumberField.RingOfIntegers K) :=
  (ClassGroup.mk K).comp (RayIdealGroup m).subtype

private theorem rayToClass_kills_principal (m : RayModulus K) :
    RayPrincipalSubgroup m ≤ (rayToClass m).ker := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro I ⟨a, _ha, hI⟩
  change rayToClass m I = 1
  change ClassGroup.mk K I.1 = 1
  rw [ClassGroup.mk_eq_one_iff]
  refine ⟨⟨(a : K), ?_⟩⟩
  simpa only [FractionalIdeal.val_eq_coe, hI, FractionalIdeal.coe_spanSingleton]

private noncomputable def forgetToClass (m : RayModulus K) :
    RayClassGroup m →* ClassGroup (NumberField.RingOfIntegers K) :=
  QuotientGroup.lift (RayPrincipalSubgroup m) (rayToClass m)
    (rayToClass_kills_principal m)

private theorem forgetToClass_mk (m : RayModulus K) (I : RayIdealGroup m) :
    forgetToClass m (mk m I) = rayToClass m I := by
  rfl

private theorem rayToClass_surjective (m : RayModulus K) :
    Function.Surjective (rayToClass m) := by
  classical
  intro c
  obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective (c⁻¹)
  let ps : Finset (Ideal (NumberField.RingOfIntegers K)) :=
    (UniqueFactorizationMonoid.normalizedFactors m.finite).toFinset
  have hprime : ∀ p ∈ ps, Prime p := by
    intro p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors m.finite :=
      Multiset.mem_toFinset.mp hp
    have hdata := (Ideal.mem_normalizedFactors_iff m.finite_ne).mp hp'
    have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      exact m.finite_ne (bot_unique hdata.2)
    exact Ideal.prime_of_isPrime hp0 hdata.1
  let e (p : Ideal (NumberField.RingOfIntegers K)) : ℕ :=
    Multiset.count p (UniqueFactorizationMonoid.normalizedFactors (I : Ideal _))
  have hlocal : ∀ p ∈ ps, ∃ x : NumberField.RingOfIntegers K,
      x ∈ p ^ e p ∧ x ∉ p ^ (e p + 1) := by
    intro p hp
    exact Ideal.exists_mem_pow_notMem_pow_succ p (hprime p hp).ne_zero
      (by simpa only [Ideal.one_eq_top] using (hprime p hp).ne_one) (e p)
  choose xp hxp using hlocal
  by_cases hps : ps = ∅
  · let J : FractionalIdealGroup (K := K) := (FractionalIdeal.mk0 K I)⁻¹
    have hJray : J ∈ RayIdealGroup m := by
      intro p hp
      have hp_mem : p.asIdeal ∈ ps := by
        apply Multiset.mem_toFinset.mpr
        apply (Ideal.mem_normalizedFactors_iff m.finite_ne).mpr
        exact ⟨p.isPrime, Ideal.dvd_iff_le.mp hp⟩
      rw [hps] at hp_mem
      simp at hp_mem
    refine ⟨⟨J, hJray⟩, ?_⟩
    change ClassGroup.mk K J = c
    rw [map_inv, ClassGroup.mk_mk0, hIc, inv_inv]
  · have hcoprime : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → p ≠ q := by aesop
    obtain ⟨x, hx⟩ := IsDedekindDomain.exists_representative_mod_finset
      (s := ps) (fun p ↦ p) (fun p ↦ e p + 1) hprime hcoprime
      (fun p ↦ Ideal.Quotient.mk (_ ^ (e p + 1)) (xp p p.2))
    have hxpow : ∀ p ∈ ps, x ∈ p ^ e p := by
      intro p hp
      have hsub : x - xp p hp ∈ p ^ (e p + 1) := Ideal.Quotient.eq.mp (hx p hp)
      rw [show x = (x - xp p hp) + xp p hp by ring]
      exact (p ^ e p).add_mem
        ((Ideal.pow_le_pow_right (Nat.le_succ _)) hsub) (hxp p hp).1
    have hxnot : ∀ p ∈ ps, x ∉ p ^ (e p + 1) := by
      intro p hp hxin
      have hsub : x - xp p hp ∈ p ^ (e p + 1) := Ideal.Quotient.eq.mp (hx p hp)
      apply (hxp p hp).2
      have : xp p hp = x - (x - xp p hp) := by ring
      rw [this]
      exact (p ^ (e p + 1)).sub_mem hxin hsub
    have hx0 : x ≠ 0 := by
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hps
      intro hx0
      subst x
      exact hxnot p hp (by simp)
    let X : FractionalIdealGroup (K := K) :=
      Units.mk0 (Ideal.span {x} : FractionalIdeal
        (NumberField.RingOfIntegers K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa))
    let J : FractionalIdealGroup (K := K) := X * (FractionalIdeal.mk0 K I)⁻¹
    have hJray : J ∈ RayIdealGroup m := by
      intro p hp
      have hp_mem : p.asIdeal ∈ ps := by
        apply Multiset.mem_toFinset.mpr
        apply (Ideal.mem_normalizedFactors_iff m.finite_ne).mpr
        exact ⟨p.isPrime, Ideal.dvd_iff_le.mp hp⟩
      have hspan0 : Ideal.span {x} ≠ (0 : Ideal (NumberField.RingOfIntegers K)) := by
        simpa using hx0
      have hcountX : FractionalIdeal.count K p
          (Ideal.span {x} : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = e p.asIdeal := by
        rw [FractionalIdeal.count_coe K p hspan0]
        rw [Ideal.count_associates_factors_eq hspan0 p.isPrime p.ne_bot]
        exact_mod_cast Ideal.count_normalizedFactors_eq
          ((Ideal.span_singleton_le_iff_mem _).mpr (hxpow p.asIdeal hp_mem))
          (by simpa [Ideal.span_singleton_le_iff_mem] using hxnot p.asIdeal hp_mem)
      have hcountI : FractionalIdeal.count K p
          (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = e p.asIdeal := by
        have hI0 : (I : Ideal (NumberField.RingOfIntegers K)) ≠ 0 :=
          mem_nonZeroDivisors_iff_ne_zero.mp I.2
        rw [FractionalIdeal.count_coe K p hI0]
        rw [Ideal.count_associates_factors_eq hI0 p.isPrime p.ne_bot]
      change FractionalIdeal.count K p
        ((X : FractionalIdeal _ K) *
          ((FractionalIdeal.mk0 K I)⁻¹ : FractionalIdeal _ K)) = 0
      rw [FractionalIdeal.count_mul K p X.ne_zero
          (inv_ne_zero (FractionalIdeal.mk0 K I).ne_zero),
        FractionalIdeal.count_inv]
      change FractionalIdeal.count K p
        (Ideal.span {x} : FractionalIdeal _ K) -
          FractionalIdeal.count K p (I : FractionalIdeal _ K) = 0
      rw [hcountX, hcountI, sub_self]
    refine ⟨⟨J, hJray⟩, ?_⟩
    change ClassGroup.mk K J = c
    change ClassGroup.mk K (X * (FractionalIdeal.mk0 K I)⁻¹) = c
    rw [map_mul, map_inv, ClassGroup.mk_mk0, hIc, inv_inv]
    have hX : ClassGroup.mk K X = 1 := by
      rw [ClassGroup.mk_eq_one_iff]
      refine ⟨⟨(x : K), ?_⟩⟩
      simp [X, FractionalIdeal.coe_spanSingleton,
        FractionalIdeal.coeIdeal_span_singleton]
    rw [hX, one_mul]

private theorem principal_iff_aux (m : RayModulus K) (I : RayIdealGroup m) :
    mk m I = 1 ↔
      ∃ a : Kˣ, RayAdmissible m a ∧
        (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
          FractionalIdeal.spanSingleton
            (NumberField.RingOfIntegers K)⁰ (a : K) := by
  change QuotientGroup.mk' (RayPrincipalSubgroup m) I = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hI
    exact (Subgroup.closure_le (admissiblePrincipalSubgroup m)).mpr (fun _ h ↦ h) hI
  · intro hI
    exact Subgroup.subset_closure hI

local notation "O" => NumberField.RingOfIntegers K

private theorem count_span_eq_zero_iff {x : O} (hx : x ≠ 0) (p : PrimeIdeal K) :
    FractionalIdeal.count K p
      (Ideal.span {x} : FractionalIdeal O⁰ K) = 0 ↔ x ∉ p.asIdeal := by
  classical
  have hs : Ideal.span {x} ≠ (0 : Ideal O) := by simpa
  rw [FractionalIdeal.count_coe K p hs, Int.ofNat_eq_zero]
  constructor
  · intro hc hxp
    have hdvd : p.asIdeal ∣ Ideal.span {x} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem p.asIdeal).2 hxp)
    exact ((Associates.count_ne_zero_iff_dvd hs p.irreducible).2 hdvd) hc
  · intro hnot
    by_contra hc
    apply hnot
    exact (Ideal.span_singleton_le_iff_mem p.asIdeal).1
      (Ideal.dvd_iff_le.mp ((Associates.count_ne_zero_iff_dvd hs p.irreducible).1 hc))

private theorem count_span_eq_zero_of_coprime
    {x : O} (hx : x ≠ 0) {M : Ideal O}
    (hcop : IsCoprime (Ideal.span {x}) M) (p : PrimeIdeal K)
    (hp : p.asIdeal ∣ M) :
    FractionalIdeal.count K p
      (Ideal.span {x} : FractionalIdeal O⁰ K) = 0 := by
  rw [count_span_eq_zero_iff hx p]
  intro hxp
  have hspan : Ideal.span {x} ≤ p.asIdeal :=
    (Ideal.span_singleton_le_iff_mem p.asIdeal).2 hxp
  have hM : M ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
  have : (⊤ : Ideal O) ≤ p.asIdeal := by
    rw [← hcop.sup_eq]
    exact sup_le hspan hM
  exact p.isPrime.ne_top (top_unique this)

private theorem fraction_prime_mem_iff (a : Kˣ) (p : PrimeIdeal K)
    (hcount : FractionalIdeal.count K p
      (FractionalIdeal.spanSingleton O⁰ (a : K)) = 0)
    {β γ : O} (hγ : γ ≠ 0)
    (hfrac : algebraMap O K β / algebraMap O K γ = (a : K)) :
    β ∈ p.asIdeal ↔ γ ∈ p.asIdeal := by
  have hβ : β ≠ 0 := by
    intro h
    subst β
    simp only [map_zero, zero_div] at hfrac
    exact a.ne_zero hfrac.symm
  have hsβ : (Ideal.span {β} : FractionalIdeal O⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa)
  have hsγ : (Ideal.span {γ} : FractionalIdeal O⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa)
  have hspan : FractionalIdeal.spanSingleton O⁰ (a : K) =
      (Ideal.span {β} : FractionalIdeal O⁰ K) *
        (Ideal.span {γ} : FractionalIdeal O⁰ K)⁻¹ := by
    simp only [FractionalIdeal.coeIdeal_span_singleton]
    rw [FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    rw [← hfrac]
    simp only [div_eq_mul_inv]
  have heq : FractionalIdeal.count K p
      (Ideal.span {β} : FractionalIdeal O⁰ K) =
      FractionalIdeal.count K p
        (Ideal.span {γ} : FractionalIdeal O⁰ K) := by
    rw [hspan, FractionalIdeal.count_mul K p hsβ (inv_ne_zero hsγ),
      FractionalIdeal.count_inv] at hcount
    omega
  rw [← not_iff_not]
  rw [← count_span_eq_zero_iff hβ p, ← count_span_eq_zero_iff hγ p, heq]

private theorem exists_coprime_fraction (M : Ideal O) (hM : M ≠ 0)
    (a : Kˣ)
    (ha : ∀ p : PrimeIdeal K, p.asIdeal ∣ M →
      FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton O⁰ (a : K)) = 0) :
    ∃ β γ : O, γ ≠ 0 ∧
      algebraMap O K β / algebraMap O K γ = (a : K) ∧
      IsCoprime (Ideal.span {β}) M ∧ IsCoprime (Ideal.span {γ}) M := by
  classical
  let ps : Finset (Ideal O) :=
    (UniqueFactorizationMonoid.normalizedFactors M).toFinset
  by_cases hps : ps = ∅
  · have hMtop : M = ⊤ := by
      rw [← Ideal.prod_normalizedFactors_eq_self hM]
      rw [show UniqueFactorizationMonoid.normalizedFactors M = 0 by
        exact Multiset.toFinset_eq_empty.mp hps]
      simp
    obtain ⟨β, γ, hγ, hfrac⟩ := IsFractionRing.div_surjective O (a : K)
    refine ⟨β, γ, nonZeroDivisors.ne_zero hγ, hfrac, ?_, ?_⟩ <;>
      rw [hMtop, Ideal.isCoprime_iff_sup_eq] <;> simp
  let D : Ideal O :=
    { carrier := {x | IsLocalization.IsInteger O
        (algebraMap O K x * (a : K))}
      zero_mem' := by simp [IsLocalization.isInteger_zero]
      add_mem' := by
        intro x y hx hy
        change IsLocalization.IsInteger O
          (algebraMap O K x * (a : K)) at hx
        change IsLocalization.IsInteger O
          (algebraMap O K y * (a : K)) at hy
        change IsLocalization.IsInteger O
          (algebraMap O K (x + y) * (a : K))
        rw [map_add, add_mul]
        exact IsLocalization.isInteger_add hx hy
      smul_mem' := by
        intro c x hx
        change IsLocalization.IsInteger O
          (algebraMap O K x * (a : K)) at hx
        change IsLocalization.IsInteger O
          (algebraMap O K (c * x) * (a : K))
        rw [map_mul, mul_assoc]
        exact IsLocalization.isInteger_mul ⟨c, rfl⟩ hx }
  have hD : ∀ p ∈ ps, ¬D ≤ p := by
    intro p hp hle
    have hpdata := (Ideal.mem_normalizedFactors_iff hM).mp
      (Multiset.mem_toFinset.mp hp)
    have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      exact hM (le_bot_iff.mp hpdata.2)
    let P : PrimeIdeal K := ⟨p, hpdata.1, hp0⟩
    obtain ⟨t, htint, i, hi, htout⟩ :=
      Ideal.exist_integer_multiples_notMem (K := K) hpdata.1.ne_top
        (s := {false, true}) (fun b : Bool => if b then (a : K) else 1)
        (j := false) (by simp) (by simp)
    have htI : IsLocalization.IsInteger O t := by simpa using htint false (by simp)
    obtain ⟨γ, hγeq⟩ := htI
    have htaI : IsLocalization.IsInteger O (t * (a : K)) := by
      simpa using htint true (by simp)
    obtain ⟨β, hβeq⟩ := htaI
    have ht0 : t ≠ 0 := by
      intro ht
      apply htout
      rw [ht]
      simpa using (p : FractionalIdeal O⁰ K).zero_mem
    have hγ0 : γ ≠ 0 := by
      intro hγ
      subst γ
      simp at hγeq
      exact ht0 hγeq.symm
    have hfrac : algebraMap O K β / algebraMap O K γ = (a : K) := by
      rw [hβeq, hγeq]
      field_simp
    have hmem : γ ∈ D := by
      change IsLocalization.IsInteger O (algebraMap O K γ * (a : K))
      rw [hγeq, ← hβeq]
      exact ⟨β, rfl⟩
    have hγp : γ ∉ p := by
      intro hgp
      have htP : t ∈ (p : FractionalIdeal O⁰ K) := by
        rw [← hγeq]
        exact FractionalIdeal.mem_coeIdeal_of_mem O⁰ hgp
      have hβp : β ∈ p :=
        (fraction_prime_mem_iff a P (ha P (by
          change p ∣ M
          exact Ideal.dvd_iff_le.mpr hpdata.2)) hγ0 hfrac).2 hgp
      have htaP : t * (a : K) ∈ (p : FractionalIdeal O⁰ K) := by
        rw [← hβeq]
        exact FractionalIdeal.mem_coeIdeal_of_mem O⁰ hβp
      fin_cases i <;> simp_all
    exact hγp (hle hmem)
  have hnot : ¬(D : Set O) ⊆ ⋃ p ∈ (ps : Set (Ideal O)), (p : Set O) := by
    rw [Ideal.subset_union_prime (⊥ : Ideal O) (⊥ : Ideal O)]
    · push_neg
      exact hD
    · intro p hp _ _
      exact (Ideal.mem_normalizedFactors_iff hM).mp
        (Multiset.mem_toFinset.mp hp) |>.1
  obtain ⟨γ, hγD, hγout⟩ := Set.not_subset.mp hnot
  have hγ0 : γ ≠ 0 := by
    intro hγ
    subst γ
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hps
    exact hγout (Set.mem_biUnion hp (Ideal.zero_mem p))
  change IsLocalization.IsInteger O
    (algebraMap O K γ * (a : K)) at hγD
  obtain ⟨β, hβeq⟩ := hγD
  have hfrac : algebraMap O K β / algebraMap O K γ = (a : K) := by
    apply (div_eq_iff ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hγ0)).2
    rw [hβeq]
    exact mul_comm _ _
  have hcop (x : O) (hxout : x ∉ ⋃ p ∈ (ps : Set (Ideal O)), (p : Set O)) :
      IsCoprime (Ideal.span {x}) M := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra htop
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {x} ⊔ M) htop
    have hMq : M ≤ q := le_sup_right.trans hle
    have hq0 : q ≠ 0 := by
      intro hq0
      subst q
      exact hM (le_bot_iff.mp hMq)
    have hqps : q ∈ ps := by
      apply Multiset.mem_toFinset.mpr
      exact (Ideal.mem_normalizedFactors_iff hM).mpr ⟨hq.isPrime, hMq⟩
    apply hxout
    exact Set.mem_biUnion hqps
      ((Ideal.span_singleton_le_iff_mem q).1 (le_sup_left.trans hle))
  have hγcop := hcop γ hγout
  have hβout : β ∉ ⋃ p ∈ (ps : Set (Ideal O)), (p : Set O) := by
    intro hβunion
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hβunion
    obtain ⟨p, hp, hβp⟩ := hβunion
    have hpdata := (Ideal.mem_normalizedFactors_iff hM).mp
      (Multiset.mem_toFinset.mp hp)
    have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      exact hM (le_bot_iff.mp hpdata.2)
    let P : PrimeIdeal K := ⟨p, hpdata.1, hp0⟩
    have hγp : γ ∈ p :=
      (fraction_prime_mem_iff a P (ha P (by
        change p ∣ M
        exact Ideal.dvd_iff_le.mpr hpdata.2)) hγ0 hfrac).1 hβp
    exact hγout (Set.mem_biUnion hp hγp)
  exact ⟨β, γ, hγ0, hfrac, hcop β hβout, hγcop⟩

private theorem quotient_isUnit_iff_coprime (M : Ideal O) (x : O) :
    IsUnit (Ideal.Quotient.mk M x) ↔ IsCoprime (Ideal.span {x}) M := by
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
    change Ideal.Quotient.mk M (x * y) = Ideal.Quotient.mk M 1 at hv
    have hv' : x * y - 1 ∈ M := (Ideal.Quotient.eq).mp hv
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨x * y, (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩),
      1 - x * y, ?_, by ring⟩
    simpa only [neg_sub] using M.neg_mem hv'
  · intro hcop
    obtain ⟨i, hi, j, hj, hij⟩ := hcop.exists
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hi
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk M y, ?_⟩
    rw [← map_mul]
    apply (Ideal.Quotient.eq).2
    have hxy : x * y = i := by rw [hy]
    rw [hxy, ← hij]
    simpa using M.neg_mem hj

private noncomputable def quotientUnitOfCoprime (M : Ideal O) (x : O)
    (hx : IsCoprime (Ideal.span {x}) M) : (O ⧸ M)ˣ :=
  (quotient_isUnit_iff_coprime M x).2 hx |>.unit

@[simp] private theorem quotientUnitOfCoprime_val (M : Ideal O) (x : O)
    (hx : IsCoprime (Ideal.span {x}) M) :
    (quotientUnitOfCoprime M x hx : O ⧸ M) = Ideal.Quotient.mk M x := by
  rfl

private theorem quotient_ratio_eq {M : Ideal O}
    {β γ β' γ' : O}
    (hγ : γ ≠ 0) (hγ' : γ' ≠ 0)
    (hβ : IsCoprime (Ideal.span {β}) M)
    (hγc : IsCoprime (Ideal.span {γ}) M)
    (hβ' : IsCoprime (Ideal.span {β'}) M)
    (hγc' : IsCoprime (Ideal.span {γ'}) M)
    (hfrac : algebraMap O K β / algebraMap O K γ =
      algebraMap O K β' / algebraMap O K γ') :
    quotientUnitOfCoprime M β hβ * (quotientUnitOfCoprime M γ hγc)⁻¹ =
      quotientUnitOfCoprime M β' hβ' * (quotientUnitOfCoprime M γ' hγc')⁻¹ := by
  have hcrossK : algebraMap O K (β * γ') = algebraMap O K (β' * γ) := by
    push_cast
    apply (div_eq_div_iff
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 hγ)
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 hγ')).mp hfrac
  have hcross : β * γ' = β' * γ :=
    (FaithfulSMul.algebraMap_injective O K) hcrossK
  have hcrossU :
      quotientUnitOfCoprime M β hβ * quotientUnitOfCoprime M γ' hγc' =
        quotientUnitOfCoprime M β' hβ' * quotientUnitOfCoprime M γ hγc := by
    apply Units.ext
    simp only [Units.val_mul, quotientUnitOfCoprime_val]
    rw [← map_mul, ← map_mul, hcross]
  calc
    quotientUnitOfCoprime M β hβ * (quotientUnitOfCoprime M γ hγc)⁻¹ =
        (quotientUnitOfCoprime M β hβ * quotientUnitOfCoprime M γ' hγc') *
          (quotientUnitOfCoprime M γ hγc *
            quotientUnitOfCoprime M γ' hγc')⁻¹ := by group
    _ = (quotientUnitOfCoprime M β' hβ' * quotientUnitOfCoprime M γ hγc) *
          (quotientUnitOfCoprime M γ hγc *
            quotientUnitOfCoprime M γ' hγc')⁻¹ := by rw [hcrossU]
    _ = quotientUnitOfCoprime M β' hβ' *
        (quotientUnitOfCoprime M γ' hγc')⁻¹ := by
      simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

private noncomputable def realSignHom (σ : K →+* ℝ) :
    Kˣ →* Multiplicative (ZMod 2) where
  toFun a := if 0 < σ (a : K) then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' := by
    intro a b
    have ha0 : σ (a : K) ≠ 0 := (map_ne_zero σ).2 a.ne_zero
    have hb0 : σ (b : K) ≠ 0 := (map_ne_zero σ).2 b.ne_zero
    by_cases ha : 0 < σ (a : K) <;> by_cases hb : 0 < σ (b : K)
    · simp [ha, hb, mul_pos]
    · have hb' : σ (b : K) < 0 := lt_of_le_of_ne (le_of_not_gt hb) hb0
      simp [ha, hb, hb', mul_neg_of_pos_of_neg]
    · have ha' : σ (a : K) < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha0
      simp [ha, hb, ha', mul_neg_of_neg_of_pos]
    · have ha' : σ (a : K) < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha0
      have hb' : σ (b : K) < 0 := lt_of_le_of_ne (le_of_not_gt hb) hb0
      simp only [Units.val_mul, map_mul, if_pos (mul_pos_of_neg_of_neg ha' hb'),
        if_neg ha, if_neg hb]
      rw [← ofAdd_add]
      congr 1

private theorem realSignHom_eq_one_iff (σ : K →+* ℝ) (a : Kˣ) :
    realSignHom σ a = 1 ↔ 0 < σ (a : K) := by
  change (if 0 < σ (a : K) then 1 else Multiplicative.ofAdd 1) = 1 ↔ _
  split_ifs with h
  · simp [h]
  · constructor
    · intro heq
      have heq' := congr_arg Multiplicative.toAdd heq
      change (1 : ZMod 2) = 0 at heq'
      norm_num at heq'
    · exact fun h' => (h h').elim

private noncomputable def realPlace (σ : K →+* ℝ) : NumberField.InfinitePlace K :=
  NumberField.InfinitePlace.mk (Complex.ofRealHom.comp σ)

private theorem realPlace_injective : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  simp only [realPlace, NumberField.InfinitePlace.mk_eq_iff] at h
  rcases h with h | h
  · ext x
    have hx := congr_fun (congr_arg DFunLike.coe h) x
    exact Complex.ofReal_injective hx
  · ext x
    have hx := congr_fun (congr_arg DFunLike.coe h) x
    simpa using congr_arg Complex.re hx

@[simp] private theorem realPlace_apply (σ : K →+* ℝ) (x : K) :
    realPlace σ x = |σ x| := by
  simp [realPlace, NumberField.InfinitePlace.apply, Real.norm_eq_abs]

private theorem exists_integer_with_signs (s : Finset (K →+* ℝ))
    (e : (σ : ↥s) → Multiplicative (ZMod 2)) :
    ∃ q : O, q ≠ 0 ∧ ∀ σ : ↥s,
      (if 0 < σ.1 (algebraMap O K q) then
        (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = e σ := by
  classical
  by_cases hs : s = ∅
  · refine ⟨1, one_ne_zero, ?_⟩
    intro σ
    exact (Finset.notMem_empty σ.1 (hs ▸ σ.2)).elim
  let w : ↥s → NumberField.InfinitePlace K := fun σ => realPlace (σ : K →+* ℝ)
  have hw : Function.Injective w := fun σ τ h =>
    Subtype.ext (realPlace_injective h)
  have hdense : DenseRange
      (algebraMap K ((σ : ↥s) → WithAbs (w σ).1)) := by
    refine Metric.denseRange_iff.mpr fun z r hr => ?_
    let z' : (v : NumberField.InfinitePlace K) → WithAbs v.1 :=
      ∑ σ : ↥s, Pi.single (w σ) (z σ)
    have hz' (σ : ↥s) : z' (w σ) = z σ := by
      simp only [z']
      rw [Finset.sum_apply, Finset.sum_eq_single σ]
      · simp
      · intro τ _ hτσ
        rw [Pi.single_eq_of_ne]
        exact fun h => hτσ (hw h.symm)
      · simp
    obtain ⟨k, hk⟩ :=
      (NumberField.InfinitePlace.denseRange_algebraMap_pi K).exists_dist_lt z' hr
    refine ⟨k, (dist_pi_lt_iff hr).2 fun σ => ?_⟩
    have hki := (dist_pi_lt_iff hr).1 hk (w σ)
    rw [hz' σ] at hki
    exact hki
  let z : (σ : ↥s) → WithAbs (w σ).1 := fun σ =>
    if e σ = 1 then WithAbs.toAbs _ (2 : K) else WithAbs.toAbs _ (-2 : K)
  obtain ⟨k, hk⟩ := hdense.exists_dist_lt z (by norm_num : (0 : ℝ) < 1)
  have hkσ (σ : ↥s) :
      |σ.1 k - (if e σ = 1 then 2 else -2)| < 1 := by
    have hki := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1)).mp hk σ
    rw [dist_eq_norm] at hki
    rw [Pi.algebraMap_apply] at hki
    have hmap : (algebraMap K (WithAbs (w σ).1)) k =
        WithAbs.toAbs (w σ).1 k := rfl
    rw [hmap] at hki
    by_cases he : e σ = 1
    · rw [show z σ = WithAbs.toAbs (w σ).1 (2 : K) by simp [z, he]] at hki
      rw [← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hki
      change realPlace σ.1 ((2 : K) - k) < 1 at hki
      rw [realPlace_apply] at hki
      simp only [map_sub, map_ofNat] at hki
      rw [abs_sub_comm] at hki
      simpa [he] using hki
    · rw [show z σ = WithAbs.toAbs (w σ).1 (-2 : K) by simp [z, he]] at hki
      rw [← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hki
      change realPlace σ.1 ((-2 : K) - k) < 1 at hki
      rw [realPlace_apply] at hki
      simp only [map_sub, map_neg, map_ofNat] at hki
      rw [abs_sub_comm] at hki
      simpa [he] using hki
  have hksign (σ : ↥s) :
      (if 0 < σ.1 k then (1 : Multiplicative (ZMod 2))
        else Multiplicative.ofAdd 1) = e σ := by
    by_cases he : e σ = 1
    · have habs := abs_lt.mp (by simpa [he] using hkσ σ)
      rw [if_pos (by linarith), he]
    · have habs := abs_lt.mp (by simpa [he] using hkσ σ)
      have hkneg : σ.1 k < 0 := by linarith
      rw [if_neg (not_lt_of_ge hkneg.le)]
      rw [← ofAdd_toAdd (e σ)]
      generalize hz : Multiplicative.toAdd (e σ) = z₂
      fin_cases z₂
      · exfalso
        apply he
        rw [← ofAdd_toAdd (e σ), hz]
        rfl
      · rfl
  have hk0 : k ≠ 0 := by
    obtain ⟨σ, hσ⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    intro hk0
    have hkbad := hkσ ⟨σ, hσ⟩
    rw [hk0, map_zero] at hkbad
    split at hkbad <;> norm_num at hkbad
  obtain ⟨b, hbI⟩ := IsLocalization.exists_integer_multiple O⁰ k
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hb2I : IsLocalization.IsInteger O
      (algebraMap O K (b : O) * ((b : O) • k)) :=
    IsLocalization.isInteger_mul ⟨(b : O), rfl⟩ hbI
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← pow_two] at hb2I
  obtain ⟨q, hq⟩ := hb2I
  have hq0 : q ≠ 0 := by
    intro hq0
    subst q
    rw [map_zero] at hq
    apply hk0
    apply mul_eq_zero.mp hq.symm |>.resolve_left
    exact pow_ne_zero _ ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hb0)
  refine ⟨q, hq0, ?_⟩
  intro σ
  have hbσ : σ.1 (algebraMap O K (b : O)) ≠ 0 :=
    (map_ne_zero σ.1).2 ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hb0)
  have hσq : σ.1 (algebraMap O K q) =
      (σ.1 (algebraMap O K (b : O))) ^ 2 * σ.1 k := by
    rw [hq, map_mul, map_pow, map_pow]
  change (if 0 < σ.1 (algebraMap O K q) then 1
    else Multiplicative.ofAdd 1) = e σ
  rw [hσq]
  have hbσpos : 0 < (σ.1 (algebraMap O K (b : O))) ^ 2 := sq_pos_of_ne_zero hbσ
  by_cases hkpos : 0 < σ.1 k
  · rw [if_pos (mul_pos hbσpos hkpos)]
    have hs := hksign σ
    rw [if_pos hkpos] at hs
    exact hs
  · have hprod : ¬0 < (σ.1 (algebraMap O K (b : O))) ^ 2 * σ.1 k :=
      not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hbσpos.le (le_of_not_gt hkpos))
    rw [if_neg hprod]
    have hs := hksign σ
    rw [if_neg hkpos] at hs
    exact hs

private theorem exists_add_with_signs (s : Finset (K →+* ℝ))
    {x t : O} (hx0 : x ≠ 0) (ht0 : t ≠ 0)
    (e : (σ : ↥s) → Multiplicative (ZMod 2))
    (htsign : ∀ σ : ↥s,
      (if 0 < σ.1 (algebraMap O K t) then
        (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = e σ) :
    ∃ N : ℕ, x + N * t ≠ 0 ∧ ∀ σ : ↥s,
      (if 0 < σ.1 (algebraMap O K (x + N * t)) then
        (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = e σ := by
  classical
  by_cases hs : s = ∅
  · refine ⟨0, by simpa, ?_⟩
    intro σ
    exact (Finset.notMem_empty σ.1 (hs ▸ σ.2)).elim
  have htσ0 (σ : ↥s) : σ.1 (algebraMap O K t) ≠ 0 :=
    (map_ne_zero σ.1).2 ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 ht0)
  choose n hn using fun σ : ↥s => exists_nat_gt
    (|σ.1 (algebraMap O K x) * σ.1 (algebraMap O K t)| /
      (σ.1 (algebraMap O K t)) ^ 2)
  let N : ℕ := ∑ σ : ↥s, n σ
  have hprod (σ : ↥s) :
      0 < σ.1 (algebraMap O K (x + N * t)) * σ.1 (algebraMap O K t) := by
    let X := σ.1 (algebraMap O K x)
    let T := σ.1 (algebraMap O K t)
    have hT2 : 0 < T ^ 2 := sq_pos_of_ne_zero (htσ0 σ)
    have hn' : |X * T| < (n σ : ℝ) * T ^ 2 :=
      (div_lt_iff₀ hT2).mp (hn σ)
    have hnN : (n σ : ℝ) ≤ N := by
      exact_mod_cast Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ σ)
    have hdom : |X * T| < (N : ℝ) * T ^ 2 :=
      lt_of_lt_of_le hn' (mul_le_mul_of_nonneg_right hnN hT2.le)
    have hcalc : 0 < (X + (N : ℝ) * T) * T := by
      rw [add_mul]
      nlinarith [neg_le_abs (X * T)]
    simpa [X, T, map_add, map_mul, map_natCast] using hcalc
  have hy0 : x + N * t ≠ 0 := by
    obtain ⟨σ, hσ⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    intro hy
    have := hprod ⟨σ, hσ⟩
    simp only [hy, map_zero, zero_mul] at this
    exact lt_irrefl 0 this
  refine ⟨N, hy0, ?_⟩
  intro σ
  have hsσ := htsign σ
  by_cases htpos : 0 < σ.1 (algebraMap O K t)
  · have hypos : 0 < σ.1 (algebraMap O K (x + N * t)) := by
      nlinarith [hprod σ]
    rw [if_pos htpos] at hsσ
    rw [if_pos hypos]
    exact hsσ
  · have htneg : σ.1 (algebraMap O K t) < 0 :=
      lt_of_le_of_ne (le_of_not_gt htpos) (htσ0 σ)
    have hyneg : σ.1 (algebraMap O K (x + N * t)) < 0 := by
      nlinarith [hprod σ]
    rw [if_neg htpos] at hsσ
    rw [if_neg (not_lt_of_ge hyneg.le)]
    exact hsσ


private structure RayFractionRep (m : RayModulus K) (a : rayElementGroup m) where
  num : O
  den : O
  den_ne : den ≠ 0
  quotient_eq : algebraMap O K num / algebraMap O K den = (a : Kˣ)
  num_coprime : IsCoprime (Ideal.span {num}) m.finite
  den_coprime : IsCoprime (Ideal.span {den}) m.finite

private theorem rayFractionRep_nonempty (m : RayModulus K) (a : rayElementGroup m) :
    Nonempty (RayFractionRep m a) := by
  have hcount : ∀ p : PrimeIdeal K, p.asIdeal ∣ m.finite →
      FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton O⁰ ((a : Kˣ) : K)) = 0 := by
    intro p hp
    have ha := a.2 p hp
    change FractionalIdeal.count K p
      ((toPrincipalIdeal O K (a : Kˣ) : FractionalIdeal O⁰ K)) = 0 at ha
    rw [coe_toPrincipalIdeal] at ha
    exact ha
  let h := exists_coprime_fraction m.finite m.finite_ne (a : Kˣ) hcount
  let β := h.choose
  let γ := h.choose_spec.choose
  have hγ := h.choose_spec.choose_spec
  exact ⟨⟨β, γ, hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2⟩⟩

private noncomputable def rayFractionRep (m : RayModulus K) (a : rayElementGroup m) :
    RayFractionRep m a :=
  Classical.choice (rayFractionRep_nonempty m a)

private theorem quotientUnitOfCoprime_one (M : Ideal O) :
    quotientUnitOfCoprime M 1 (by
      rw [Ideal.isCoprime_iff_sup_eq]
      simp) = 1 := by
  apply Units.ext
  simp

private theorem quotientUnitOfCoprime_mul (M : Ideal O) (x y : O)
    (hx : IsCoprime (Ideal.span {x}) M) (hy : IsCoprime (Ideal.span {y}) M) :
    quotientUnitOfCoprime M (x * y) (by
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hx.mul_left hy) =
      quotientUnitOfCoprime M x hx * quotientUnitOfCoprime M y hy := by
  apply Units.ext
  simp only [quotientUnitOfCoprime_val, Units.val_mul]
  rw [map_mul]

private noncomputable def finiteRaySignature (m : RayModulus K) :
    rayElementGroup m →* (O ⧸ m.finite)ˣ where
  toFun a :=
    quotientUnitOfCoprime m.finite (rayFractionRep m a).num
        (rayFractionRep m a).num_coprime *
      (quotientUnitOfCoprime m.finite (rayFractionRep m a).den
        (rayFractionRep m a).den_coprime)⁻¹
  map_one' := by
    let r := rayFractionRep m (1 : rayElementGroup m)
    have h := quotient_ratio_eq (M := m.finite) r.den_ne one_ne_zero
      r.num_coprime r.den_coprime
      (by rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq])
      (by rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq])
      (by
        have hr := r.quotient_eq
        change algebraMap O K r.num / algebraMap O K r.den = (1 : K) at hr
        simpa only [map_one, div_one] using hr)
    simpa only [quotientUnitOfCoprime_one, inv_one, mul_one] using h
  map_mul' := by
    intro a b
    let ra := rayFractionRep m a
    let rb := rayFractionRep m b
    let rab := rayFractionRep m (a * b)
    have hnum : IsCoprime (Ideal.span {ra.num * rb.num}) m.finite := by
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact ra.num_coprime.mul_left rb.num_coprime
    have hden : IsCoprime (Ideal.span {ra.den * rb.den}) m.finite := by
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact ra.den_coprime.mul_left rb.den_coprime
    have hfrac : algebraMap O K rab.num / algebraMap O K rab.den =
        algebraMap O K (ra.num * rb.num) / algebraMap O K (ra.den * rb.den) := by
      rw [rab.quotient_eq]
      push_cast
      rw [mul_div_mul_comm, ra.quotient_eq, rb.quotient_eq]
    have h := quotient_ratio_eq (M := m.finite) rab.den_ne
      (mul_ne_zero ra.den_ne rb.den_ne) rab.num_coprime rab.den_coprime
      hnum hden hfrac
    rw [quotientUnitOfCoprime_mul m.finite ra.num rb.num
        ra.num_coprime rb.num_coprime,
      quotientUnitOfCoprime_mul m.finite ra.den rb.den
        ra.den_coprime rb.den_coprime] at h
    change quotientUnitOfCoprime m.finite rab.num rab.num_coprime *
        (quotientUnitOfCoprime m.finite rab.den rab.den_coprime)⁻¹ =
      (quotientUnitOfCoprime m.finite ra.num ra.num_coprime *
        (quotientUnitOfCoprime m.finite ra.den ra.den_coprime)⁻¹) *
      (quotientUnitOfCoprime m.finite rb.num rb.num_coprime *
        (quotientUnitOfCoprime m.finite rb.den rb.den_coprime)⁻¹)
    calc
      _ = (quotientUnitOfCoprime m.finite ra.num ra.num_coprime *
            quotientUnitOfCoprime m.finite rb.num rb.num_coprime) *
          (quotientUnitOfCoprime m.finite ra.den ra.den_coprime *
            quotientUnitOfCoprime m.finite rb.den rb.den_coprime)⁻¹ := h
      _ = _ := by
        rw [mul_inv_rev]
        ac_rfl

private noncomputable def raySignature (m : RayModulus K) :
    rayElementGroup m →* LocalData m where
  toFun a := (finiteRaySignature m a,
    fun σ => realSignHom (σ : K →+* ℝ) (a : Kˣ))
  map_one' := by
    ext σ <;> simp
  map_mul' := by
    intro a b
    ext σ <;> simp

private theorem finiteRaySignature_eq_one_iff (m : RayModulus K)
    (a : rayElementGroup m) :
    finiteRaySignature m a = 1 ↔
      (rayFractionRep m a).num - (rayFractionRep m a).den ∈ m.finite := by
  change quotientUnitOfCoprime m.finite (rayFractionRep m a).num
      (rayFractionRep m a).num_coprime *
    (quotientUnitOfCoprime m.finite (rayFractionRep m a).den
      (rayFractionRep m a).den_coprime)⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, Units.ext_iff]
  simp only [quotientUnitOfCoprime_val]
  exact Ideal.Quotient.eq

private theorem raySignature_eq_one_iff (m : RayModulus K) (a : rayElementGroup m) :
    raySignature m a = 1 ↔ RayAdmissible m (a : Kˣ) := by
  constructor
  · intro ha
    have hfin : finiteRaySignature m a = 1 := congr_arg Prod.fst ha
    have hsign : ∀ σ : ↥m.infinite,
        realSignHom (σ : K →+* ℝ) (a : Kˣ) = 1 := by
      intro σ
      exact congr_fun (congr_arg Prod.snd ha) σ
    constructor
    · exact ⟨(rayFractionRep m a).num, (rayFractionRep m a).den,
        (rayFractionRep m a).den_ne, (rayFractionRep m a).quotient_eq,
        (rayFractionRep m a).num_coprime, (rayFractionRep m a).den_coprime,
        (finiteRaySignature_eq_one_iff m a).mp hfin⟩
    · intro σ hσ
      exact (realSignHom_eq_one_iff σ (a : Kˣ)).mp (hsign ⟨σ, hσ⟩)
  · rintro ⟨⟨β, γ, hγ, hfrac, hβc, hγc, hcong⟩, hpos⟩
    apply Prod.ext
    · have hratio := quotient_ratio_eq (M := m.finite)
        (rayFractionRep m a).den_ne hγ
        (rayFractionRep m a).num_coprime (rayFractionRep m a).den_coprime
        hβc hγc (by rw [(rayFractionRep m a).quotient_eq, hfrac])
      rw [show quotientUnitOfCoprime m.finite β hβc *
          (quotientUnitOfCoprime m.finite γ hγc)⁻¹ = 1 by
        rw [mul_inv_eq_one, Units.ext_iff]
        simp only [quotientUnitOfCoprime_val]
        exact (Ideal.Quotient.eq).2 hcong] at hratio
      exact hratio
    · funext σ
      exact (realSignHom_eq_one_iff (σ : K →+* ℝ) (a : Kˣ)).mpr
        (hpos σ σ.2)

private theorem exists_nonzero_coprime_lift (M : Ideal O) (u : (O ⧸ M)ˣ) :
    ∃ x : O, ∃ hx0 : x ≠ 0, ∃ hxc : IsCoprime (Ideal.span {x}) M,
      quotientUnitOfCoprime M x hxc = u := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ M)
  have hxc : IsCoprime (Ideal.span {x}) M :=
    (quotient_isUnit_iff_coprime M x).mp (by rw [hx]; exact u.isUnit)
  by_cases hx0 : x = 0
  · have hM : M = ⊤ := by
      subst x
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, bot_sup_eq] at hxc
      exact hxc
    have hc1 : IsCoprime (Ideal.span {(1 : O)}) M := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq]
    refine ⟨1, one_ne_zero, hc1, ?_⟩
    apply Units.ext
    rw [quotientUnitOfCoprime_val, ← hx, hx0]
    apply (Ideal.Quotient.eq).2
    simp [hM]
  · refine ⟨x, hx0, hxc, ?_⟩
    apply Units.ext
    simpa using hx

private theorem integral_mem_rayElementGroup (m : RayModulus K) {y : O} (hy0 : y ≠ 0)
    (hyc : IsCoprime (Ideal.span {y}) m.finite) :
    Units.mk0 (algebraMap O K y)
      ((map_ne_zero_iff (algebraMap O K)
        (FaithfulSMul.algebraMap_injective O K)).2 hy0) ∈ rayElementGroup m := by
  intro p hp
  change FractionalIdeal.count K p
    ((toPrincipalIdeal O K (Units.mk0 (algebraMap O K y) _) :
      FractionalIdeal O⁰ K)) = 0
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.count K p
    (FractionalIdeal.spanSingleton O⁰ (algebraMap O K y)) = 0
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact count_span_eq_zero_of_coprime hy0 hyc p hp

private theorem rayApproximation (m : RayModulus K) :
    ∃ signature : rayElementGroup m →* LocalData m,
      Function.Surjective signature ∧
      ∀ a, signature a = 1 ↔ RayAdmissible m (a : Kˣ) := by
  classical
  refine ⟨raySignature m, ?_, raySignature_eq_one_iff m⟩
  rintro ⟨u, e⟩
  obtain ⟨x, hx0, hxc, hxu⟩ := exists_nonzero_coprime_lift (K := K) m.finite u
  obtain ⟨d, hd0⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr m.finite_ne)
  have hd0' : (d : O) ≠ 0 := by
    intro h
    exact hd0 (Subtype.ext h)
  let dU : Kˣ := Units.mk0 (algebraMap O K (d : O))
    ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hd0')
  let correction : (σ : ↥m.infinite) → Multiplicative (ZMod 2) := fun σ =>
    e σ * (realSignHom (σ : K →+* ℝ) dU)⁻¹
  obtain ⟨q, hq0, hqsign⟩ := exists_integer_with_signs m.infinite correction
  let qU : Kˣ := Units.mk0 (algebraMap O K q)
    ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hq0)
  let t : O := (d : O) * q
  have ht0 : t ≠ 0 := mul_ne_zero hd0' hq0
  let tU : Kˣ := Units.mk0 (algebraMap O K t)
    ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 ht0)
  have hqsign' (σ : ↥m.infinite) :
      realSignHom (σ : K →+* ℝ) qU = correction σ := by
    exact hqsign σ
  have htU : dU * qU = tU := by
    apply Units.ext
    simp [dU, qU, tU, t]
  have htsign (σ : ↥m.infinite) :
      (if 0 < σ.1 (algebraMap O K t) then
        (1 : Multiplicative (ZMod 2)) else Multiplicative.ofAdd 1) = e σ := by
    change realSignHom (σ : K →+* ℝ) tU = e σ
    rw [← htU, map_mul, hqsign']
    simp only [correction]
    simp [mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨N, hy0, hysign⟩ :=
    exists_add_with_signs m.infinite hx0 ht0 e htsign
  let y : O := x + N * t
  have hymod : y - x ∈ m.finite := by
    change x + N * ((d : O) * q) - x ∈ m.finite
    rw [add_sub_cancel_left]
    exact m.finite.mul_mem_left (N : O)
      (m.finite.mul_mem_right q d.2)
  have hyc : IsCoprime (Ideal.span {y}) m.finite := by
    apply (quotient_isUnit_iff_coprime m.finite y).mp
    have hyx : Ideal.Quotient.mk m.finite y = Ideal.Quotient.mk m.finite x :=
      (Ideal.Quotient.eq).2 hymod
    rw [hyx]
    exact (quotient_isUnit_iff_coprime m.finite x).2 hxc
  let yU : Kˣ := Units.mk0 (algebraMap O K y)
    ((map_ne_zero_iff (algebraMap O K)
      (FaithfulSMul.algebraMap_injective O K)).2 hy0)
  let yR : rayElementGroup m :=
    ⟨yU, integral_mem_rayElementGroup m hy0 hyc⟩
  have hyu : quotientUnitOfCoprime m.finite y hyc = u := by
    rw [← hxu]
    apply Units.ext
    simp only [quotientUnitOfCoprime_val]
    exact (Ideal.Quotient.eq).2 hymod
  have hyfin : finiteRaySignature m yR = u := by
    change quotientUnitOfCoprime m.finite (rayFractionRep m yR).num
        (rayFractionRep m yR).num_coprime *
      (quotientUnitOfCoprime m.finite (rayFractionRep m yR).den
        (rayFractionRep m yR).den_coprime)⁻¹ = u
    calc
      _ = quotientUnitOfCoprime m.finite y hyc *
          (quotientUnitOfCoprime m.finite 1 (by
            rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq]))⁻¹ :=
        quotient_ratio_eq (M := m.finite) (rayFractionRep m yR).den_ne one_ne_zero
          (rayFractionRep m yR).num_coprime (rayFractionRep m yR).den_coprime
          hyc (by
            rw [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_one, top_sup_eq]) (by
            rw [(rayFractionRep m yR).quotient_eq]
            change algebraMap O K y = algebraMap O K y / algebraMap O K 1
            simp)
      _ = u := by rw [quotientUnitOfCoprime_one, inv_one, mul_one, hyu]
  refine ⟨yR, ?_⟩
  apply Prod.ext
  · exact hyfin
  · funext σ
    exact hysign σ

/-- Blueprint Lemma 5.1 (`RayClassGroup.exactSequence`): the elementary exact
sequence from units through residue/sign data and ray classes to the ordinary
class group. -/
theorem exactSequence (m : RayModulus K) :
    ∃ (unitSignature : (NumberField.RingOfIntegers K)ˣ →* LocalData m)
      (localToRay : LocalData m →* RayClassGroup m)
      (forget : RayClassGroup m →* ClassGroup (NumberField.RingOfIntegers K)),
      MonoidHom.range unitSignature = MonoidHom.ker localToRay ∧
      MonoidHom.range localToRay = MonoidHom.ker forget ∧
      Function.Surjective forget := by
  obtain ⟨signature, hsignature, hone⟩ := rayApproximation m
  have hkernel : ∀ a, mk m (principalRayIdeal m a) = 1 ↔
      signature a ∈ MonoidHom.range (signature.comp (unitsToRayElements m)) := by
    intro a
    rw [principal_iff_aux]
    constructor
    · rintro ⟨b, hb, hab⟩
      have hspan : FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (((a : Kˣ) : K)) =
          FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰ (b : K) := by
        rw [← principalRayIdeal_val]
        exact hab
      obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
      have hbmem : b ∈ rayElementGroup m := by
        change toPrincipalIdeal (NumberField.RingOfIntegers K) K b ∈ RayIdealGroup m
        have heq : toPrincipalIdeal (NumberField.RingOfIntegers K) K b =
            (principalRayIdeal m a).1 := by
          apply Units.ext
          rw [coe_toPrincipalIdeal, hab]
        rw [heq]
        exact (principalRayIdeal m a).2
      let bR : rayElementGroup m := ⟨b, hbmem⟩
      have hub : unitsToRayElements m u * a = bR := by
        apply Subtype.ext
        apply Units.ext
        change algebraMap (NumberField.RingOfIntegers K) K
          (u : NumberField.RingOfIntegers K) * (((a : Kˣ) : K)) = (b : K) at hu
        simpa [unitsToRayElements, bR] using hu
      have hb1 : signature bR = 1 := (hone bR).2 (by simpa [bR] using hb)
      have hua : signature (unitsToRayElements m u) * signature a = 1 := by
        rw [← map_mul, hub, hb1]
      refine ⟨u⁻¹, ?_⟩
      change signature (unitsToRayElements m u⁻¹) = signature a
      simpa only [map_inv] using (eq_inv_of_mul_eq_one_right hua).symm
    · rintro ⟨u, hu⟩
      let d : rayElementGroup m := a * (unitsToRayElements m u)⁻¹
      have hd1 : signature d = 1 := by
        change signature (a * (unitsToRayElements m u)⁻¹) = 1
        change signature (unitsToRayElements m u) = signature a at hu
        rw [map_mul, map_inv, ← hu, mul_inv_cancel]
      have hdadm : RayAdmissible m (d : Kˣ) := (hone d).1 hd1
      refine ⟨(d : Kˣ), hdadm, ?_⟩
      rw [principalRayIdeal_val]
      change _ = FractionalIdeal.spanSingleton _ (((d : Kˣ) : K))
      change _ = FractionalIdeal.spanSingleton _
        ((((a : Kˣ) * ((unitsToRayElements m u : rayElementGroup m) : Kˣ)⁻¹) : Kˣ) : K)
      rw [Units.val_mul, Units.val_inv_eq_inv_val,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton]
      have huone : FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
          (((unitsToRayElements m u : rayElementGroup m) : Kˣ) : K) = 1 := by
        change FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
          (algebraMap (NumberField.RingOfIntegers K) K
            (u : NumberField.RingOfIntegers K)) = 1
        rw [← FractionalIdeal.coeIdeal_span_singleton,
          Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]
      rw [← FractionalIdeal.spanSingleton_inv, huone, inv_one, mul_one]
  let principalToRay : rayElementGroup m →* RayClassGroup m :=
    (mk m).comp (principalRayIdeal m)
  have hsignature_ker : signature.ker ≤ principalToRay.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    change mk m (principalRayIdeal m a) = 1
    rw [hkernel, ha]
    exact ⟨1, by simp⟩
  let localToRay : LocalData m →* RayClassGroup m :=
    signature.liftOfSurjective hsignature ⟨principalToRay, hsignature_ker⟩
  let unitSignature : (NumberField.RingOfIntegers K)ˣ →* LocalData m :=
    signature.comp (unitsToRayElements m)
  have hlocal (a : rayElementGroup m) :
      localToRay (signature a) = principalToRay a := by
    exact MonoidHom.liftOfRightInverse_comp_apply signature
      (Function.surjInv hsignature) (Function.rightInverse_surjInv hsignature)
      ⟨principalToRay, hsignature_ker⟩ a
  refine ⟨unitSignature, localToRay, forgetToClass m, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      change localToRay (signature (unitsToRayElements m u)) = 1
      rw [hlocal]
      change mk m (principalRayIdeal m (unitsToRayElements m u)) = 1
      rw [hkernel]
      exact ⟨u, rfl⟩
    · intro hy
      obtain ⟨a, rfl⟩ := hsignature y
      rw [MonoidHom.mem_ker] at hy
      have ha : principalToRay a = 1 := by
        rw [← hlocal]
        exact hy
      change mk m (principalRayIdeal m a) = 1 at ha
      rw [hkernel] at ha
      rcases ha with ⟨u, hu⟩
      exact ⟨u, hu⟩
  · ext c
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := hsignature y
      rw [MonoidHom.mem_ker]
      change forgetToClass m (localToRay (signature a)) = 1
      rw [hlocal]
      change forgetToClass m (mk m (principalRayIdeal m a)) = 1
      rw [forgetToClass_mk]
      change ClassGroup.mk K (principalRayIdeal m a).1 = 1
      rw [ClassGroup.mk_eq_one_iff]
      refine ⟨⟨((a : Kˣ) : K), ?_⟩⟩
      rw [principalRayIdeal_val, FractionalIdeal.coe_spanSingleton]
    · intro hc
      obtain ⟨I, hIc⟩ := QuotientGroup.mk'_surjective (RayPrincipalSubgroup m) c
      change mk m I = c at hIc
      rw [← hIc] at hc ⊢
      rw [MonoidHom.mem_ker, forgetToClass_mk] at hc
      change ClassGroup.mk K I.1 = 1 at hc
      rw [ClassGroup.mk_eq_one_iff] at hc
      rcases hc with ⟨⟨a, ha⟩⟩
      have ha0 : a ≠ 0 := by
        intro ha0
        subst a
        apply I.1.ne_zero
        apply Subtype.coe_injective
        simpa using ha
      let au : Kˣ := Units.mk0 a ha0
      have heq : toPrincipalIdeal (NumberField.RingOfIntegers K) K au = I.1 := by
        apply Units.ext
        apply Subtype.coe_injective
        simpa [au, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using ha.symm
      have hau : au ∈ rayElementGroup m := by
        change toPrincipalIdeal (NumberField.RingOfIntegers K) K au ∈
          RayIdealGroup m
        rw [heq]
        exact I.2
      let aR : rayElementGroup m := ⟨au, hau⟩
      refine ⟨signature aR, ?_⟩
      change localToRay (signature aR) = mk m I
      rw [hlocal]
      apply congr_arg (mk m)
      apply Subtype.ext
      exact heq
  · intro c
    obtain ⟨I, hI⟩ := rayToClass_surjective m c
    refine ⟨mk m I, ?_⟩
    rw [forgetToClass_mk]
    exact hI

/-- Blueprint Lemma 5.1 (`RayClassGroup.principal_iff`): the kernel of the
quotient consists exactly of ray-admissible principal fractional ideals. -/
theorem principal_iff (m : RayModulus K) (I : RayIdealGroup m) :
    mk m I = 1 ↔
      ∃ α : Kˣ, RayAdmissible m α ∧
        (I.1 : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
          FractionalIdeal.spanSingleton
            (NumberField.RingOfIntegers K)⁰ (α : K) := by
  change QuotientGroup.mk' (RayPrincipalSubgroup m) I = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hI
    exact (Subgroup.closure_le (admissiblePrincipalSubgroup m)).mpr (fun _ h ↦ h) hI
  · intro hI
    exact Subgroup.subset_closure hI

/-- Blueprint Lemma 5.1, proposed declaration `RayClassGroup.finite`: every
ray class group is finite. -/
theorem finite (m : RayModulus K) : Finite (RayClassGroup m) := by
  letI : Finite (NumberField.RingOfIntegers K ⧸ m.finite) :=
    Ring.HasFiniteQuotients.finiteQuotient m.finite_ne
  letI : Fintype (LocalData m) := Fintype.ofFinite (LocalData m)
  obtain ⟨_unitSignature, localToRay, forget, _hunit, hrange, _hforget⟩ :=
    exactSequence m
  let ft : Fintype (RayClassGroup m) :=
    Group.fintypeOfKerEqRange localToRay forget hrange.symm
  exact @Fintype.finite _ ft

/-- The finite typeclass promised by the ray-class finiteness theorem. -/
noncomputable instance instFinite (m : RayModulus K) : Finite (RayClassGroup m) :=
  finite m

/-- The ray-class quotient map is surjective. -/
theorem mk_surjective (m : RayModulus K) : Function.Surjective (mk m) := by
  exact QuotientGroup.mk'_surjective (RayPrincipalSubgroup m)

end RayClassGroup

end NU.Chebotarev
