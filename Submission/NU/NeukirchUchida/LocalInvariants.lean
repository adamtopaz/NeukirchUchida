import Submission.NU.LocalTheory.Main
import Submission.NU.NeukirchUchida.Bridges.HenselianCompletion
import Submission.NU.NeukirchUchida.Bridges.MaschkeDescent
import Submission.NU.Chebotarev.FieldCrossing
import Submission.NU.LCFT.FundamentalClass.DeepUnits
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Local arithmetic invariants from recovered decomposition groups

This file is the construction-level bridge between `NU.LocalTheory` and the
Neukirch--Uchida local interface.  Its primary input is not an abstractly
postulated local-field invariant: it is the one-prime family
`bareRecoveredAtPrime`, whose finite quotients are built from packet
stabilizers and whose soundness is proved with the finite witness systems.

The easy bookkeeping rungs (restriction of an ambient place, the odd-prime
packet profile, detection of residue characteristic, and consequences of
residue-norm equality) are proved here.  The genuinely local-anabelian rungs
are isolated under descriptive names and documented at their exact intended
mathematical strength.
-/

open scoped NumberField Pointwise ValuativeRel
open IsDedekindDomain

namespace NU.NeukirchUchida.LocalInvariants

noncomputable section

/-- A realization of the usual absolute Galois action in a supplied ambient
algebraic closure.  The compatibility equation prevents the group
isomorphism from being unrelated to the action on the ambient field. -/
structure AbsoluteGaloisActionRealization
    (K Omega G : Type*) [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega] where
  /-- Comparison of Mathlib's chosen algebraic closure with the ambient one. -/
  closureEquiv : AlgebraicClosure K ≃ₐ[K] Omega
  /-- Comparison of absolute Galois groups. -/
  galoisEquiv : Field.absoluteGaloisGroup K ≃ₜ* G
  /-- The two comparisons intertwine the actual actions on field elements. -/
  action_compat : ∀ (g : Field.absoluteGaloisGroup K)
      (x : AlgebraicClosure K),
    closureEquiv
        ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) x) =
      galoisEquiv g • closureEquiv x

/-- An absolute finite place in a supplied ambient algebraic closure. -/
abbrev AmbientAbsolutePlace
    (K Omega : Type*) [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega] :=
  NU.LocalTheory.AbsoluteFinitePlaceIn K Omega

/-- The restriction of an ambient absolute place to its number field is a
nontrivial valuation. -/
theorem ambientPlace_comap_nontrivial
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    NU.LocalTheory.IsNontrivialValuation
      (P.1.comap (algebraMap K Omega)) := by
  obtain ⟨_, v, hv⟩ := P.2
  rw [hv]
  exact NU.LocalTheory.primeValuationSubring_ne_top v

/-- The finite prime obtained by restricting an ambient absolute place. -/
noncomputable def ambientFinitePlace
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    NU.LocalTheory.FinitePlace K :=
  NU.LocalTheory.centerFinitePlace
    (P.1.comap (algebraMap K Omega))
    (ambientPlace_comap_nontrivial P)

/-- The selected finite prime has exactly the contracted valuation ring. -/
@[simp]
theorem primeValuationSubring_ambientFinitePlace
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    NU.LocalTheory.primeValuationSubring (ambientFinitePlace P) =
      P.1.comap (algebraMap K Omega) :=
  NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _

/-- The rational prime below an ambient absolute place. -/
noncomputable def ambientRationalPrime
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    NU.LocalTheory.FinitePlace ℚ :=
  NU.LocalTheory.restrictFinitePlace ℚ (ambientFinitePlace P)

/-- Absolute ramification index of an ambient place over `ℚ`. -/
noncomputable def ambientRamificationIndex
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) : ℕ :=
  (ambientRationalPrime P).asIdeal.ramificationIdx'
    (ambientFinitePlace P).asIdeal

/-- Absolute residue degree of an ambient place over `ℚ`. -/
noncomputable def ambientResidueDegree
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) : ℕ :=
  (ambientRationalPrime P).asIdeal.inertiaDeg'
    (ambientFinitePlace P).asIdeal

/-- Cardinality of the finite residue field at an ambient place. -/
noncomputable def ambientResidueNorm
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) : ℕ :=
  NU.Chebotarev.PrimeIdeal.norm (ambientFinitePlace P)

/-- An ambient automorphism acts on the residue field by the `n`-th power
map, stated on valuation-ring representatives.  This formulation avoids an
arbitrary choice of a residue-field action and is exactly what the quotient
predicate in `LocalInterface` needs. -/
def ActsAsPowerOnResidue
    {Omega G : Type*} [Field Omega] [Group G]
    [MulSemiringAction G Omega]
    (W : ValuationSubring Omega) (g : G) (n : ℕ) : Prop :=
  ∀ x y : W, (y : Omega) = g • (x : Omega) →
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal W) y =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal W) x) ^ n

/-- Transporting an absolute place to another algebraic closure does not
change its restricted finite prime.  This is pure center-of-valuation
bookkeeping and uses no local recovery theorem. -/
theorem ambientFinitePlace_transport
    (K Omega : Type*) [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (e : AlgebraicClosure K ≃ₐ[K] Omega)
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    ambientFinitePlace
        (NU.LocalTheory.ambientAbsoluteFinitePlaceEquiv K Omega e P) =
      ambientFinitePlace P := by
  let Q := NU.LocalTheory.ambientAbsoluteFinitePlaceEquiv K Omega e P
  let A := P.1.comap (algebraMap K (AlgebraicClosure K))
  have hA : NU.LocalTheory.IsNontrivialValuation A :=
    ambientPlace_comap_nontrivial P
  have hcomap : Q.1.comap (algebraMap K Omega) = A := by
    apply ValuationSubring.ext
    intro x
    change e.symm (algebraMap K Omega x) ∈ P.1 ↔
      algebraMap K (AlgebraicClosure K) x ∈ P.1
    rw [show e.symm (algebraMap K Omega x) =
      algebraMap K (AlgebraicClosure K) x by
        apply e.injective
        simp]
  apply (NU.LocalTheory.numberField_valuations A hA).unique
  · rw [← hcomap]
    exact (primeValuationSubring_ambientFinitePlace Q).symm
  · exact (primeValuationSubring_ambientFinitePlace P).symm

/-! ## The odd-prime packet profile and residue characteristic -/

/-- The construction-level odd-prime profile of an absolute place.  Membership
at `ell` means that its decomposition group passes the bare packet criterion
cofinally at `ell`; by marked-level correctness this is exactly the condition
that the residue characteristic is not `ell`. -/
def oddPacketProfile
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    Set NU.LocalTheory.OddPrime :=
  {ell | NU.LocalTheory.absoluteDecompositionGroup K P.1 ∈
    NU.LocalTheory.bareRecoveredAtPrime
      (Field.absoluteGaloisGroup K) ell}

/-- For a fixed absolute place, LocalTheory's arithmetic away-predicate is
exactly inequality between the selected residue characteristic and the
auxiliary odd prime. -/
theorem isAbsoluteFinitePlaceAway_iff
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (ell : NU.LocalTheory.OddPrime) :
    NU.LocalTheory.IsAbsoluteFinitePlaceAway K ell P.1 ↔
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
        (ell : ℕ) := by
  constructor
  · rintro ⟨_, v, hv, hchar⟩
    have hvP : v = ambientFinitePlace P := by
      let A := P.1.comap (algebraMap K (AlgebraicClosure K))
      have hA : NU.LocalTheory.IsNontrivialValuation A :=
        ambientPlace_comap_nontrivial P
      exact (NU.LocalTheory.numberField_valuations A hA).choose_spec.2 v hv
    rwa [← hvP]
  · intro hchar
    refine ⟨P.2, ambientFinitePlace P, ?_, hchar⟩
    exact (primeValuationSubring_ambientFinitePlace P).symm

/-- Membership in the packet profile is the concrete away-from-`ell`
condition.  The forward direction uses soundness and distinctness of absolute
decomposition groups; the reverse direction uses completeness. -/
theorem mem_oddPacketProfile_iff
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (ell : NU.LocalTheory.OddPrime) :
    ell ∈ oddPacketProfile K P ↔
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
        (ell : ℕ) := by
  rw [← isAbsoluteFinitePlaceAway_iff K P ell]
  constructor
  · intro hprofile
    have hcollection :
        NU.LocalTheory.absoluteDecompositionGroup K P.1 ∈
          NU.LocalTheory.absoluteDecompositionCollectionAway K ell := by
      rw [← NU.LocalTheory.bare_reconstruction_at_prime K ell]
      exact hprofile
    obtain ⟨W, hW, hgroup⟩ := hcollection
    have hWP : W = P.1 := by
      by_contra hne
      exact NU.LocalTheory.absoluteDecompositionGroup_ne_of_ne K W P.1
        hW.1 P.2 hne (hgroup.symm)
    rwa [hWP] at hW
  · intro haway
    exact NU.LocalTheory.bare_recovery_complete K ell P.1 haway

/-- Mapping a recovered decomposition subgroup along a profinite isomorphism
preserves membership in every fixed-prime packet recovery set. -/
theorem oddPacketProfile_transport
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂)
    (hmap : Subgroup.map alpha.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1)
    (ell : NU.LocalTheory.OddPrime) :
    ell ∈ oddPacketProfile K₁ P₁ ↔
      ell ∈ oddPacketProfile K₂ P₂ := by
  let D₁ := NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1
  let D₂ := NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1
  constructor
  · intro h₁
    have hmapped : Subgroup.map alpha.toMulEquiv.toMonoidHom D₁ ∈
        NU.LocalTheory.bareRecoveredAtPrime
          (Field.absoluteGaloisGroup K₂) ell := by
      rw [← NU.LocalTheory.bareRecoveredAtPrime_functorial alpha ell]
      exact ⟨D₁, h₁, rfl⟩
    rwa [hmap] at hmapped
  · intro h₂
    have hmap' :
        Subgroup.map alpha.symm.toMulEquiv.toMonoidHom D₂ = D₁ := by
      dsimp only [D₁, D₂]
      rw [← hmap]
      exact NU.LocalTheory.subgroupMap_mulEquiv_symm alpha.symm.toMulEquiv
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1)
    have hmapped : Subgroup.map alpha.symm.toMulEquiv.toMonoidHom D₂ ∈
        NU.LocalTheory.bareRecoveredAtPrime
          (Field.absoluteGaloisGroup K₁) ell := by
      rw [← NU.LocalTheory.bareRecoveredAtPrime_functorial alpha.symm ell]
      exact ⟨D₂, h₂, rfl⟩
    rwa [hmap'] at hmapped

/-- A prime natural number is determined by the set of odd primes unequal to
it.  The `2`-case is why the packet construction must vary all odd auxiliary
primes rather than select one of them. -/
theorem prime_eq_of_ne_oddPrime_iff
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hprofile : ∀ ell : NU.LocalTheory.OddPrime,
      (p ≠ (ell : ℕ)) ↔ (q ≠ (ell : ℕ))) :
    p = q := by
  by_contra hpq
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · have hq2 : q ≠ 2 := by
      intro h
      exact hpq (hp2.trans h.symm)
    let ell : NU.LocalTheory.OddPrime :=
      ⟨⟨q, hq⟩, hq.odd_of_ne_two hq2⟩
    have hleft : p ≠ (ell : ℕ) := by
      simpa [ell] using hpq
    exact (hprofile ell).mp hleft rfl
  · let ell : NU.LocalTheory.OddPrime := ⟨⟨p, hp⟩, hpodd⟩
    have hright : q ≠ (ell : ℕ) := by
      simpa [ell] using Ne.symm hpq
    exact (hprofile ell).mpr hright rfl

/-- The residue characteristic of a number-field finite place is prime. -/
theorem residueCharacteristic_prime
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    (NU.LocalTheory.residueCharacteristic v).Prime := by
  letI : Algebra (𝓞 K) (NU.LocalTheory.primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let e : (𝓞 K ⧸ v.asIdeal) ≃+*
      NU.LocalTheory.ResidueFieldAt v :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
      (NU.LocalTheory.primeValuationSubring v)
  letI : Finite (NU.LocalTheory.ResidueFieldAt v) :=
    Finite.of_equiv (𝓞 K ⧸ v.asIdeal) e.toEquiv
  exact CharP.prime_ringChar _

/-- **Proved recovery rung (residue characteristic).**  Any profinite
isomorphism carrying one absolute decomposition group to another preserves
residue characteristic.  The proof uses only the fixed-prime packet recovery
sets and their finite-witness correctness, including the exceptional
characteristic-two bookkeeping above. -/
theorem residueCharacteristic_preserved
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂)
    (hmap : Subgroup.map alpha.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1) :
    NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂) := by
  apply prime_eq_of_ne_oddPrime_iff
    (residueCharacteristic_prime (ambientFinitePlace P₁))
    (residueCharacteristic_prime (ambientFinitePlace P₂))
  intro ell
  rw [← mem_oddPacketProfile_iff K₁ P₁ ell,
    ← mem_oddPacketProfile_iff K₂ P₂ ell]
  exact oddPacketProfile_transport alpha P₁ P₂ hmap ell

/-! ## Transport from a common ambient realization -/

/-- Pull an ambient place back to Mathlib's chosen algebraic closure. -/
noncomputable def abstractPlace
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) :
    NU.LocalTheory.AbsoluteFinitePlaceOf K :=
  (NU.LocalTheory.ambientAbsoluteFinitePlaceEquiv
    K Omega R.closureEquiv).symm P

/-- The realization equivalence restricts to an equivalence between the
pulled-back and ambient valuation rings. -/
private noncomputable def abstractPlaceValuationEquiv
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) :
    (abstractPlace R P).1 ≃+* P.1 where
  toFun x := ⟨R.closureEquiv x, x.property⟩
  invFun x := ⟨R.closureEquiv.symm x, by
    simpa [abstractPlace, NU.LocalTheory.ambientAbsoluteFinitePlaceEquiv,
      NU.LocalTheory.transportValuationSubring] using x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- Pull an isomorphism between two realized actions back to the chosen
absolute Galois groups. -/
noncomputable def abstractGaloisIso
    {K₁ K₂ Omega G₁ G₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Omega] [Algebra K₁ Omega] [Algebra K₂ Omega]
    [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [MulSemiringAction G₁ Omega] [MulSemiringAction G₂ Omega]
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂) :
    Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂ :=
  R₁.galoisEquiv.trans (theta.trans R₂.galoisEquiv.symm)

/-- Exact decomposition-group bookkeeping for two common-ambient
realizations.  This is the reusable bridge from a mapped stabilizer equation
to the input expected by the proved packet-profile theorem. -/
theorem map_abstractDecompositionGroup
    {K₁ K₂ Omega G₁ G₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Omega] [Algebra K₁ Omega] [Algebra K₂ Omega]
    [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [MulSemiringAction G₁ Omega] [MulSemiringAction G₂ Omega]
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    Subgroup.map
        (abstractGaloisIso R₁ R₂ theta).toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁
          (abstractPlace R₁ P₁).1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂
        (abstractPlace R₂ P₂).1 := by
  let A₁ := abstractPlace R₁ P₁
  let A₂ := abstractPlace R₂ P₂
  let alpha := abstractGaloisIso R₁ R₂ theta
  have h₁ : Subgroup.map R₁.galoisEquiv.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) =
        NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 := by
    simpa [A₁, abstractPlace] using
      NU.LocalTheory.map_absoluteDecompositionGroup_ambient
        R₁.closureEquiv R₁.galoisEquiv.toMulEquiv R₁.action_compat A₁
  have h₂ : Subgroup.map R₂.galoisEquiv.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K₂ A₂.1) =
        NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
    simpa [A₂, abstractPlace] using
      NU.LocalTheory.map_absoluteDecompositionGroup_ambient
        R₂.closureEquiv R₂.galoisEquiv.toMulEquiv R₂.action_compat A₂
  have hcomp :
      R₂.galoisEquiv.toMulEquiv.toMonoidHom.comp
          alpha.toMulEquiv.toMonoidHom =
        theta.toMulEquiv.toMonoidHom.comp
          R₁.galoisEquiv.toMulEquiv.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change R₂.galoisEquiv
        (R₂.galoisEquiv.symm (theta (R₁.galoisEquiv g))) =
      theta (R₁.galoisEquiv g)
    exact R₂.galoisEquiv.apply_symm_apply _
  apply NU.LocalTheory.subgroupMap_mulEquiv_injective
    R₂.galoisEquiv.toMulEquiv
  calc
    Subgroup.map R₂.galoisEquiv.toMulEquiv.toMonoidHom
        (Subgroup.map alpha.toMulEquiv.toMonoidHom
          (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1)) =
      Subgroup.map
        (R₂.galoisEquiv.toMulEquiv.toMonoidHom.comp
          alpha.toMulEquiv.toMonoidHom)
        (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) := by
          rw [Subgroup.map_map]
    _ = Subgroup.map
        (theta.toMulEquiv.toMonoidHom.comp
          R₁.galoisEquiv.toMulEquiv.toMonoidHom)
        (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) := by
          rw [hcomp]
    _ = Subgroup.map theta.toMulEquiv.toMonoidHom
        (Subgroup.map R₁.galoisEquiv.toMulEquiv.toMonoidHom
          (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1)) := by
          rw [Subgroup.map_map]
    _ = NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
          rw [h₁, hmap]
    _ = Subgroup.map R₂.galoisEquiv.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₂ A₂.1) := h₂.symm

/-- Restriction to the number field commutes with pulling an ambient place
back along its realization. -/
theorem ambientFinitePlace_abstractPlace
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) :
    ambientFinitePlace (abstractPlace R P) = ambientFinitePlace P := by
  let eP := NU.LocalTheory.ambientAbsoluteFinitePlaceEquiv
    K Omega R.closureEquiv
  have htransport := ambientFinitePlace_transport K Omega R.closureEquiv
    (abstractPlace R P)
  have hplace : eP (abstractPlace R P) = P := by
    exact eP.apply_symm_apply P
  rw [hplace] at htransport
  exact htransport.symm

/-- **Proved common-ambient residue-characteristic rung.**  This is the form
consumed by `LocalInterface`: packet-profile recovery is transported through
the explicitly compatible closure and Galois-action realizations. -/
theorem ambientResidueCharacteristic_preserved
    {K₁ K₂ Omega G₁ G₂ : Type*}
    [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [Field Omega] [Algebra K₁ Omega] [Algebra K₂ Omega]
    [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
    [MulSemiringAction G₁ Omega] [MulSemiringAction G₂ Omega]
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂) := by
  have h := residueCharacteristic_preserved
    (abstractGaloisIso R₁ R₂ theta)
    (abstractPlace R₁ P₁) (abstractPlace R₂ P₂)
    (map_abstractDecompositionGroup R₁ R₂ theta P₁ P₂ hmap)
  rwa [ambientFinitePlace_abstractPlace R₁ P₁,
    ambientFinitePlace_abstractPlace R₂ P₂] at h

/-! ## Rational prime and residue-degree bookkeeping -/

/-- Residue characteristic is the norm of the prime contracted to `ℤ`.
This public copy of the arithmetic bookkeeping lemma is used to compare
rational finite places without introducing a classification axiom. -/
theorem residueCharacteristic_eq_absNorm_under
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    NU.LocalTheory.residueCharacteristic v =
      Ideal.absNorm (Ideal.under ℤ v.asIdeal) := by
  letI : Algebra (𝓞 K) (NU.LocalTheory.primeValuationSubring v) :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime
      (NU.LocalTheory.primeValuationSubring v) v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (NU.LocalTheory.primeValuationSubring v)
  calc
    NU.LocalTheory.residueCharacteristic v =
        ringChar ((𝓞 K) ⧸ v.asIdeal) := by
      rw [NU.LocalTheory.residueCharacteristic, ringChar.eq_iff]
      exact (e.symm.toRingHom.charP_iff_charP _).mpr
        (ringChar.charP ((𝓞 K) ⧸ v.asIdeal))
    _ = Ideal.absNorm (Ideal.under ℤ v.asIdeal) :=
      Ideal.ringChar_quot v.asIdeal

/-- Restriction through a number-field extension preserves residue
characteristic. -/
theorem residueCharacteristic_restrictFinitePlace
    (K : Type*) {L : Type*}
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : NU.LocalTheory.FinitePlace L) :
    NU.LocalTheory.residueCharacteristic
        (NU.LocalTheory.restrictFinitePlace K v) =
      NU.LocalTheory.residueCharacteristic v := by
  rw [residueCharacteristic_eq_absNorm_under,
    residueCharacteristic_eq_absNorm_under,
    NU.LocalTheory.restrictFinitePlace_asIdeal]
  congr 1
  rw [← Ideal.under_def, Ideal.under_under]

/-- Restricting a prime-local valuation ring through a number-field
extension gives the valuation ring at the contracted prime. -/
private theorem primeValuationSubring_restrictFinitePlace
    (K : Type*) {L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : NU.LocalTheory.FinitePlace L) :
    (NU.LocalTheory.primeValuationSubring w).comap (algebraMap K L) =
      NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.restrictFinitePlace K w) := by
  let v := NU.LocalTheory.restrictFinitePlace K w
  have hle : NU.LocalTheory.primeValuationSubring v ≤
      (NU.LocalTheory.primeValuationSubring w).comap
        (algebraMap K L) := by
    intro x hx
    rw [NU.LocalTheory.mem_primeValuationSubring_iff] at hx
    rw [ValuationSubring.mem_comap,
      NU.LocalTheory.mem_primeValuationSubring_iff]
    obtain ⟨a, b, hb, hab⟩ := hx
    refine ⟨algebraMap (𝓞 K) (𝓞 L) a,
      algebraMap (𝓞 K) (𝓞 L) b, ?_, ?_⟩
    · intro hbw
      apply hb
      change b ∈ (NU.LocalTheory.restrictFinitePlace K w).asIdeal
      exact hbw
    · have hcoe (c : 𝓞 K) :
          ((algebraMap (𝓞 K) (𝓞 L) c : 𝓞 L) : L) =
            algebraMap K L (c : K) := by
        calc
          _ = algebraMap (𝓞 K) L c :=
            (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L c).symm
          _ = algebraMap K L (c : K) :=
            IsScalarTower.algebraMap_apply (𝓞 K) K L c
      rw [hcoe, hcoe, ← map_mul, hab]
  have hne : (NU.LocalTheory.primeValuationSubring w).comap
      (algebraMap K L) ≠ ⊤ := by
    obtain ⟨a, ha, ha0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have haw : algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal := ha
    have hlt : w.valuation L
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) < 1 :=
      (w.valuation_lt_one_iff_mem
        (algebraMap (𝓞 K) (𝓞 L) a)).2 haw
    have hmap0 : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero (algebraMap K L)).2 (by exact_mod_cast ha0)
    have hpos : 0 < w.valuation L (algebraMap K L (a : K)) :=
      (w.valuation L).pos_iff.mpr hmap0
    have hcoe :
        ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) =
          algebraMap K L (a : K) := by
      calc
        _ = algebraMap (𝓞 K) L a :=
          (IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a).symm
        _ = algebraMap K L (a : K) :=
          IsScalarTower.algebraMap_apply (𝓞 K) K L a
    rw [hcoe] at hlt
    have hinv : 1 <
        (w.valuation L (algebraMap K L (a : K)))⁻¹ :=
      (one_lt_inv₀ hpos).2 hlt
    intro htop
    have hz : (a : K)⁻¹ ∈
        (NU.LocalTheory.primeValuationSubring w).comap
          (algebraMap K L) := by
      rw [htop]
      trivial
    rw [ValuationSubring.mem_comap, NU.LocalTheory.primeValuationSubring,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hz
    rw [map_inv₀, Valuation.map_inv] at hz
    exact (not_le_of_gt hinv) hz
  letI : Ring.KrullDimLE 1
      (NU.LocalTheory.primeValuationSubring v) := by
    change Ring.KrullDimLE 1
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
    infer_instance
  exact (ValuationSubring.eq_of_le_of_ne_top
    (NU.LocalTheory.primeValuationSubring v) hle hne).symm

/-- A rational finite place is determined by its residue characteristic. -/
theorem rationalFinitePlace_eq_of_residueCharacteristic_eq
    (v w : NU.LocalTheory.FinitePlace ℚ)
    (hchar : NU.LocalTheory.residueCharacteristic v =
      NU.LocalTheory.residueCharacteristic w) :
    v = w := by
  have hunder : Ideal.under ℤ v.asIdeal = Ideal.under ℤ w.asIdeal := by
    calc
      Ideal.under ℤ v.asIdeal =
          Ideal.span {(Ideal.absNorm (Ideal.under ℤ v.asIdeal) : ℤ)} :=
        (Int.ideal_span_absNorm_eq_self _).symm
      _ = Ideal.span
          {(Ideal.absNorm (Ideal.under ℤ w.asIdeal) : ℤ)} := by
        rw [← residueCharacteristic_eq_absNorm_under v,
          ← residueCharacteristic_eq_absNorm_under w, hchar]
      _ = Ideal.under ℤ w.asIdeal :=
        Int.ideal_span_absNorm_eq_self _
  have hsurj : Function.Surjective
      (algebraMap ℤ (𝓞 ℚ)) := by
    intro x
    refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
    apply Subtype.ext
    exact Rat.ringOfIntegersEquiv_apply_coe x
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact Ideal.comap_injective_of_surjective
    (algebraMap ℤ (𝓞 ℚ)) hsurj hunder

/-! ## Certified local-invariant recovery ladder

The declarations below follow the obligation groups in the certified
`local_invariants_recovery.tex` blueprint.  Arithmetic inputs are isolated as
named lemmas; the finite-level, profinite-linear, and final assembly steps are
kept separate so that replacing any arithmetic input does not change the
three public theorem statements at the end of the file. -/

/-! ### Marked levels and packet determinants (`def:marked`, `lem:matrix`) -/

/-- The simultaneous marked kernel
`C_{ell,1} ∩ theta⁻¹(C_{ell,2})`.  In particular, this definition makes no
claim that `theta` preserves either cyclotomic kernel. -/
private def thetaMarkedKernel
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (ell : NU.LocalTheory.OddPrime) :
    Subgroup (Field.absoluteGaloisGroup K₁) :=
  NU.LocalTheory.cyclotomicKernel K₁ (ell : ℕ) ⊓
    Subgroup.comap alpha.toMulEquiv.toMonoidHom
      (NU.LocalTheory.cyclotomicKernel K₂ (ell : ℕ))

/-- Membership in the cofinal system of simultaneous marked levels from
Blueprint `def:marked`. -/
private def IsThetaMarkedLevel
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (ell : NU.LocalTheory.OddPrime)
    (U : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K₁)) : Prop :=
  U.toSubgroup ≤ thetaMarkedKernel alpha ell

/-- Blueprint `def:marked`: simultaneous marked levels are cofinal.  The
proof intersects both genuine cyclotomic kernels with an arbitrary open
level and then takes an open normal subgroup inside that neighbourhood. -/
private theorem thetaMarkedLevels_cofinal
    (K₁ K₂ : Type*) [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (ell : NU.LocalTheory.OddPrime) :
    NU.LocalTheory.IsCofinalOpenNormalSystem
      {U : NU.LocalTheory.OpenNormalSubgroup
          (Field.absoluteGaloisGroup K₁) |
        IsThetaMarkedLevel alpha ell U} := by
  rw [NU.LocalTheory.cofinalOpenNormalSystem_iff]
  intro V hV
  let C₁ := NU.LocalTheory.cyclotomicKernel K₁ (ell : ℕ)
  let C₂ := NU.LocalTheory.cyclotomicKernel K₂ (ell : ℕ)
  have hopen₂ : IsOpen
      (alpha ⁻¹' (C₂ : Set (Field.absoluteGaloisGroup K₂))) :=
    (NU.LocalTheory.cyclotomicKernel_isOpen K₂ ell).preimage
      alpha.continuous_toFun
  have hopen : IsOpen
      (((V : Set (Field.absoluteGaloisGroup K₁)) ∩
          (C₁ : Set (Field.absoluteGaloisGroup K₁))) ∩
        alpha ⁻¹' (C₂ : Set (Field.absoluteGaloisGroup K₂))) :=
    (hV.inter (NU.LocalTheory.cyclotomicKernel_isOpen K₁ ell)).inter
      hopen₂
  have hone : (1 : Field.absoluteGaloisGroup K₁) ∈
      (((V : Set (Field.absoluteGaloisGroup K₁)) ∩
          (C₁ : Set (Field.absoluteGaloisGroup K₁))) ∩
        alpha ⁻¹' (C₂ : Set (Field.absoluteGaloisGroup K₂))) :=
    ⟨⟨V.one_mem, C₁.one_mem⟩, by simp [C₂]⟩
  letI : CompactSpace (Field.absoluteGaloisGroup K₁) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  letI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K₁) :=
    NU.LocalTheory.absoluteGaloisGroup_totallyDisconnectedSpace
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  let U : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K₁) :=
    { toSubgroup := N.toSubgroup
      isOpen' := N.isOpen'
      normal' := N.isNormal' }
  refine ⟨U, ?_, ?_⟩
  · intro g hg
    change g ∈ C₁ ∧ alpha g ∈ C₂
    exact ⟨(hN hg).1.2, (hN hg).2⟩
  · intro g hg
    exact (hN hg).1.1

/-- A basis-free determinant certificate for the action on a packet plane.
The four displayed coefficients are the matrix entries in the certified
ordered basis, and the final equation is its `2 × 2` determinant. -/
private def IsPlaneActionDeterminant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ell : ℕ} [Fact ell.Prime]
    (T : NU.LocalTheory.ElementaryQuotient G ell ≃ₗ[ZMod ell]
      NU.LocalTheory.ElementaryQuotient G ell)
    (P : NU.LocalTheory.GroupSubspace G ell) (d : ZMod ell) : Prop :=
  ∃ x y : NU.LocalTheory.ElementaryQuotient G ell,
    NU.LocalTheory.IsPlaneBasis P x y ∧
      ∃ a b c e : ZMod ell,
        T x = a • x + c • y ∧
        T y = b • x + e • y ∧
        d = a * e - b * c

open NU.LocalTheory

/-- The construction-level formula
`T_g = chi_ell(g) (B_g⁻¹)^dual`.  This is a named adapter to the existing
`NU.LocalTheory.kummerDualEquiv_packetAction_apply`; Blueprint
`lem:matrix`. -/
private theorem packetAction_twistedDual_apply
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ell : ℕ} [Fact ell.Prime]
    (zeta : M) (hzeta : IsPrimitiveRoot zeta ell)
    (sigma : M ≃ₐ[K] M)
    (x : NU.LocalTheory.ElementaryQuotient
      (Field.absoluteGaloisGroup M) ell)
    (u : Mˣ) :
    NU.LocalTheory.kummerDualEquiv zeta hzeta
        (NU.LocalTheory.packetAction K M ell sigma x) (Additive.ofMul u) =
      ((NU.LocalTheory.packetCyclotomicCharacter K M ell zeta hzeta sigma :
          (ZMod ell)ˣ) : ZMod ell) *
        NU.LocalTheory.kummerDualEquiv zeta hzeta x
          (Additive.ofMul (Units.map
            sigma.symm.toRingEquiv.toMonoidHom u)) := by
  exact NU.LocalTheory.kummerDualEquiv_packetAction_apply
    K M zeta hzeta sigma x u

private noncomputable def quotientEquivResidueFieldAt_matrix
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    (𝓞 K ⧸ v.asIdeal) ≃+* ResidueFieldAt v := by
  change (𝓞 K ⧸ v.asIdeal) ≃+*
    IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)

private theorem residueFieldAt_finite_matrix
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    Finite (ResidueFieldAt v) :=
  Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (quotientEquivResidueFieldAt_matrix v).toEquiv

private theorem absNorm_eq_natCard_residueFieldAt_matrix
    {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) :
    Ideal.absNorm v.asIdeal = Nat.card (ResidueFieldAt v) := by
  calc
    Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = Nat.card (ResidueFieldAt v) :=
      Nat.card_congr (quotientEquivResidueFieldAt_matrix v).toEquiv

private theorem primitiveRoot_residueFieldAt_matrix
    {K : Type*} [Field K] [NumberField K]
    {ell : ℕ} [Fact ell.Prime]
    (zeta : K) (hzeta : IsPrimitiveRoot zeta ell)
    (v : FinitePlace K) (hv : residueCharacteristic v ≠ ell) :
    IsPrimitiveRoot
      ((quotientEquivResidueFieldAt_matrix v)
        (Ideal.Quotient.mk v.asIdeal hzeta.toInteger)) ell := by
  let k := ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite_matrix v
  letI := Fintype.ofFinite k
  have hnorm : Ideal.absNorm v.asIdeal = Nat.card k :=
    absNorm_eq_natCard_residueFieldAt_matrix v
  obtain ⟨d, hp, hkcard⟩ :=
    FiniteField.card k (residueCharacteristic v)
  have hkcard' : Nat.card k = residueCharacteristic v ^ (d : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hkcard
  have hprimeCoprime : (residueCharacteristic v).Coprime ell :=
    (Nat.coprime_primes hp (Fact.out : Nat.Prime ell)).mpr hv
  have hnormCoprime : (Ideal.absNorm v.asIdeal).Coprime ell := by
    rw [hnorm, hkcard']
    exact hprimeCoprime.pow_left d
  have hnorm_ne_one : Ideal.absNorm v.asIdeal ≠ 1 :=
    Ideal.absNorm_eq_one_iff.not.mpr v.isMaximal.ne_top
  have hrootQuot : IsPrimitiveRoot
      (Ideal.Quotient.mk v.asIdeal hzeta.toInteger) ell :=
    hzeta.toInteger_isPrimitiveRoot.idealQuotient_mk hnorm_ne_one
      hnormCoprime
  exact hrootQuot.map_of_injective
    (quotientEquivResidueFieldAt_matrix v).injective

private theorem finiteField_ringEquiv_eq_pow_matrix
    {k : Type*} [Field k] [Finite k] (tau : k ≃+* k) :
    ∃ a : ℕ, ∀ x : k, tau x = x ^ ((ringChar k) ^ a) := by
  let p := ringChar k
  letI : Fact p.Prime := ⟨CharP.prime_ringChar k⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let taua : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := tau) (by
    intro z
    have hhom : tau.toRingHom.comp (algebraMap (ZMod p) k) =
        algebraMap (ZMod p) k := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun hhom z)
  letI := Fintype.ofFinite (ZMod p)
  obtain ⟨a, ha⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 taua
  refine ⟨a.1, ?_⟩
  intro x
  have hx := DFunLike.congr_fun ha x
  rw [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at hx
  change x ^ p ^ a.1 = tau x at hx
  simpa [p] using hx.symm

/-- Every automorphism of a finite-field extension is a unique bounded
power of the base-cardinality Frobenius.  The final field records the exact
congruence detector needed when comparing two nested residue levels. -/
private theorem finiteField_algEquiv_eq_pow_matrix
    {k F : Type*} [Field k] [Finite k] [Field F] [Finite F]
    [Algebra k F] (tau : F ≃ₐ[k] F) :
    ∃ d a : ℕ, d = Module.finrank k F ∧ 0 < d ∧ a < d ∧
      (∀ x : F, tau x = x ^ (Nat.card k ^ a)) ∧
      ∀ b : ℕ, (∀ x : F,
        x ^ (Nat.card k ^ a) = x ^ (Nat.card k ^ b)) →
          Nat.ModEq d a b := by
  letI := Fintype.ofFinite k
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic k F
  obtain ⟨a, ha⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k F).2 tau
  let d := Module.finrank k F
  refine ⟨d, a, rfl, Module.finrank_pos, a.isLt, ?_, ?_⟩
  · intro x
    have hx := DFunLike.congr_fun ha x
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at hx
    simpa only [Nat.card_eq_fintype_card] using hx.symm
  · intro b hb
    have heq : frob ^ (a : ℕ) = frob ^ b := by
      ext x
      rw [AlgEquiv.coe_pow, AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      simpa only [Nat.card_eq_fintype_card] using hb x
    have hm := (pow_eq_pow_iff_modEq.mp heq)
    rwa [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic] at hm

private theorem mem_primeValuationSubring_automorphism_matrix
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (sigma : M ≃ₐ[K] M) (w : FinitePlace M) (x : M) :
    x ∈ primeValuationSubring w ↔
      sigma x ∈ primeValuationSubring (conjugateFinitePlace K sigma w) := by
  rw [mem_primeValuationSubring_iff, mem_primeValuationSubring_iff]
  constructor
  · rintro ⟨a, b, hb, h⟩
    refine ⟨sigma • a, sigma • b, ?_, ?_⟩
    · simpa [conjugateFinitePlace_asIdeal] using hb
    · change sigma x * sigma (b : M) = sigma (a : M)
      simpa only [map_mul] using congrArg sigma h
  · rintro ⟨a, b, hb, h⟩
    refine ⟨sigma⁻¹ • a, sigma⁻¹ • b, ?_, ?_⟩
    · intro hmem
      apply hb
      rw [conjugateFinitePlace_asIdeal,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact hmem
    · have hh := congrArg sigma.symm h
      change x * sigma.symm (b : M) = sigma.symm (a : M)
      simpa only [map_mul, AlgEquiv.symm_apply_apply] using hh

private noncomputable def stableValuationRingEquiv_matrix
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] (sigma : M ≃ₐ[K] M) (w : FinitePlace M)
    (hw : conjugateFinitePlace K sigma w = w) :
    primeValuationSubring w ≃+* primeValuationSubring w where
  toFun x := ⟨sigma (x : M), by
    have hm :=
      (mem_primeValuationSubring_automorphism_matrix K M sigma w x).1 x.prop
    simpa only [hw] using hm⟩
  invFun x := ⟨sigma.symm (x : M), by
    apply (mem_primeValuationSubring_automorphism_matrix K M sigma w
      (sigma.symm (x : M))).2
    rw [hw]
    simpa using x.prop⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

private theorem localD_twisted_pullback_sub_localI
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ell : ℕ} [Fact ell.Prime]
    (zeta : M) (hzeta : IsPrimitiveRoot zeta ell)
    (sigma : M ≃ₐ[K] M) (v : FinitePlace M)
    (hv : residueCharacteristic v ≠ ell)
    (hplace : conjugateFinitePlace K sigma v = v)
    (p : MulCharacter M ell)
    (hp : p ∈ localD ell (primeValuationSubring v)) :
    ((packetCyclotomicCharacter K M ell zeta hzeta sigma : (ZMod ell)ˣ) :
        ZMod ell) •
        pullbackCharacter ell sigma.symm.toRingEquiv.toRingHom p - p ∈
      localI ell (primeValuationSubring v) := by
  let A := primeValuationSubring v
  let k := ResidueFieldAt v
  letI : Algebra (𝓞 M) A :=
    show Algebra (𝓞 M)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v) from
      inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)
      v.asIdeal from inferInstance
  letI : Finite k := residueFieldAt_finite_matrix v
  have hinvplace : conjugateFinitePlace K sigma.symm v = v := by
    apply HeightOneSpectrum.ext
    rw [conjugateFinitePlace_asIdeal]
    have hi := congrArg HeightOneSpectrum.asIdeal hplace
    rw [conjugateFinitePlace_asIdeal] at hi
    change sigma⁻¹ • v.asIdeal = v.asIdeal
    simpa only [hi] using inv_smul_smul sigma v.asIdeal
  let e : A ≃+* A :=
    stableValuationRingEquiv_matrix K M sigma.symm v hinvplace
  let tau : k ≃+* k := IsLocalRing.ResidueField.mapEquiv e
  obtain ⟨a, ha⟩ := finiteField_ringEquiv_eq_pow_matrix tau
  let t : ℕ := ringChar k ^ a
  let rz : k := (quotientEquivResidueFieldAt_matrix v)
    (Ideal.Quotient.mk v.asIdeal hzeta.toInteger)
  have hrz : rz = IsLocalRing.residue A
      (algebraMap (𝓞 M) A hzeta.toInteger) := by
    rfl
  have hroot : IsPrimitiveRoot rz ell :=
    primitiveRoot_residueFieldAt_matrix zeta hzeta v hv
  let chiInv : (ZMod ell)ˣ :=
    packetCyclotomicCharacter K M ell zeta hzeta sigma.symm
  have htaur : tau rz = rz ^ chiInv.val.val := by
    rw [hrz]
    change IsLocalRing.residue A
        (e (algebraMap (𝓞 M) A hzeta.toInteger)) =
      (IsLocalRing.residue A
        (algebraMap (𝓞 M) A hzeta.toInteger)) ^ chiInv.val.val
    rw [← map_pow]
    apply congrArg (IsLocalRing.residue A)
    apply Subtype.ext
    change sigma.symm zeta = zeta ^ chiInv.val.val
    exact packetCyclotomicCharacter_spec K M ell zeta hzeta sigma.symm
  have hpowers : rz ^ t = rz ^ chiInv.val.val :=
    (ha rz).symm.trans htaur
  let rzu : kˣ := Units.mk0 rz
    (hroot.ne_zero (Fact.out : Nat.Prime ell).ne_zero)
  have hrootu : IsPrimitiveRoot rzu ell := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [rzu] using hroot
  have hpowersu : rzu ^ t = rzu ^ chiInv.val.val := by
    apply Units.ext
    exact hpowers
  have htmod : t ≡ chiInv.val.val [MOD ell] := by
    have hm : t ≡ chiInv.val.val [MOD orderOf rzu] :=
      (pow_eq_pow_iff_modEq (x := rzu) (m := chiInv.val.val)
        (n := t)).mp hpowersu
    rw [← hrootu.eq_orderOf] at hm
    exact hm
  have htcast : (t : ZMod ell) = (chiInv : ZMod ell) := by
    calc
      (t : ZMod ell) = (chiInv.val.val : ZMod ell) :=
        (ZMod.natCast_eq_natCast_iff t chiInv.val.val ell).2 htmod
      _ = chiInv.val := ZMod.natCast_zmod_val chiInv.val
      _ = (chiInv : ZMod ell) := rfl
  have hchiInv : chiInv =
      (packetCyclotomicCharacter K M ell zeta hzeta sigma)⁻¹ := by
    change packetCyclotomicCharacter K M ell zeta hzeta sigma⁻¹ = _
    exact map_inv (packetCyclotomicCharacter K M ell zeta hzeta) sigma
  have hscalar :
      ((packetCyclotomicCharacter K M ell zeta hzeta sigma :
        (ZMod ell)ˣ) : ZMod ell) * (t : ZMod ell) = 1 := by
    rw [htcast, hchiInv]
    exact Units.mul_inv
      (packetCyclotomicCharacter K M ell zeta hzeta sigma)
  intro u hu
  let us : A.unitGroup := ⟨u, hu⟩
  let ua : Aˣ := A.unitGroupMulEquiv us
  let eua : Aˣ := Units.map e.toMonoidHom ua
  let uat : Aˣ := ua ^ t
  let eus : A.unitGroup := A.unitGroupMulEquiv.symm eua
  let uts : A.unitGroup := A.unitGroupMulEquiv.symm uat
  have hres : A.unitGroupToResidueFieldUnits eus =
      A.unitGroupToResidueFieldUnits uts := by
    apply Units.ext
    rw [A.coe_unitGroupToResidueFieldUnits_apply,
      A.coe_unitGroupToResidueFieldUnits_apply]
    change IsLocalRing.residue A (e ua) =
      IsLocalRing.residue A (ua ^ t)
    have hpow := ha (IsLocalRing.residue A ua)
    change IsLocalRing.residue A (e ua) =
      (IsLocalRing.residue A ua) ^ t at hpow
    simpa only [map_pow] using hpow
  have hker : eus * uts⁻¹ ∈
      A.unitGroupToResidueFieldUnits.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hres]
    exact mul_inv_cancel (A.unitGroupToResidueFieldUnits uts)
  rw [A.ker_unitGroupToResidueFieldUnits] at hker
  have hprincipal :
      (eus : Mˣ) * (uts : Mˣ)⁻¹ ∈ A.principalUnitGroup := hker
  have hpzero := hp _ hprincipal
  have hpeq : p (Additive.ofMul (eus : Mˣ)) =
      p (Additive.ofMul (uts : Mˣ)) := by
    change p (Additive.ofMul ((eus : Mˣ) * (uts : Mˣ)⁻¹)) = 0 at hpzero
    rw [show Additive.ofMul ((eus : Mˣ) * (uts : Mˣ)⁻¹) =
      Additive.ofMul (eus : Mˣ) - Additive.ofMul (uts : Mˣ) by rfl,
      map_sub] at hpzero
    exact sub_eq_zero.mp hpzero
  have heus : (eus : Mˣ) =
      Units.map sigma.symm.toRingEquiv.toMonoidHom u := by
    apply Units.ext
    rfl
  have huts : (uts : Mˣ) = u ^ t := by
    apply Units.ext
    rfl
  have hpull :
      p (Additive.ofMul
        (Units.map sigma.symm.toRingEquiv.toMonoidHom u)) =
      (t : ZMod ell) * p (Additive.ofMul u) := by
    rw [← heus, hpeq, huts]
    change p (t • Additive.ofMul u) = _
    rw [map_nsmul]
    simpa [smul_eq_mul] using
      (Nat.cast_smul_eq_nsmul (ZMod ell) t
        (p (Additive.ofMul u))).symm
  change ((packetCyclotomicCharacter K M ell zeta hzeta sigma :
      (ZMod ell)ˣ) : ZMod ell) *
      p (Additive.ofMul
        (Units.map sigma.symm.toRingEquiv.toMonoidHom u)) -
      p (Additive.ofMul u) = 0
  rw [hpull, ← mul_assoc, hscalar, one_mul, sub_self]

private theorem localI_pullback_fixed
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ell : ℕ} [Fact ell.Prime]
    (sigma : M ≃ₐ[K] M) (v : FinitePlace M)
    (hv : conjugateFinitePlace K sigma v = v)
    (p : MulCharacter M ell)
    (hp : p ∈ localI ell (primeValuationSubring v)) :
    pullbackCharacter ell sigma.symm.toRingEquiv.toRingHom p = p := by
  let A := primeValuationSubring v
  letI : Algebra (𝓞 M) A :=
    show Algebra (𝓞 M)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v) from
      inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v)
      v.asIdeal from inferInstance
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 M) v.ne_bot A
  let e : A ≃+* A := stableValuationRingEquiv_matrix K M sigma v hv
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hepi : Irreducible (e.symm pi) := hpi.map e.symm
  have hassoc : Associated (e.symm pi) pi :=
    IsDiscreteValuationRing.associated_of_irreducible A hepi hpi
  apply AddMonoidHom.ext
  intro z
  cases z with
  | ofMul x =>
    obtain ⟨n, u, hx⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
        hpi x.ne_zero
    have huA : Units.map (algebraMap A M).toMonoidHom u ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      change A.valuation
          ((Units.map (algebraMap A M).toMonoidHom u : Mˣ) : M) =
        A.valuation 1
      rw [A.valuation_eq_iff]
      exact ⟨u, by simp⟩
    let piM : Mˣ := Units.mk0 (pi : M) (by simpa using hpi.ne_zero)
    let epiM : Mˣ := Units.mk0 (e.symm pi : M) (by
      simpa using hepi.ne_zero)
    let uM : Mˣ := Units.map (algebraMap A M).toMonoidHom u
    let eu : Aˣ := Units.map e.symm.toMonoidHom u
    let euM : Mˣ := Units.map (algebraMap A M).toMonoidHom eu
    have hpu : p (Additive.ofMul uM) = 0 := hp _ huA
    have heuA : euM ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      change A.valuation (euM : M) = A.valuation 1
      rw [A.valuation_eq_iff]
      exact ⟨eu, by simp [euM]⟩
    have hpeu : p (Additive.ofMul euM) = 0 := hp _ heuA
    obtain ⟨a, ha⟩ := hassoc
    let aM : Mˣ := Units.map (algebraMap A M).toMonoidHom a
    have haA : aM ∈ A.unitGroup := by
      rw [A.mem_unitGroup_iff]
      change A.valuation (aM : M) = A.valuation 1
      rw [A.valuation_eq_iff]
      exact ⟨a, by simp [aM]⟩
    have hpa : p (Additive.ofMul aM) = 0 := hp _ haA
    have haM : epiM * aM = piM := by
      apply Units.ext
      simpa [epiM, aM, piM] using
        congrArg (fun z : A => (z : M)) ha
    have hpepi : p (Additive.ofMul epiM) = p (Additive.ofMul piM) := by
      have hm := p.map_add (Additive.ofMul epiM) (Additive.ofMul aM)
      change p (Additive.ofMul (epiM * aM)) =
        p (Additive.ofMul epiM) + p (Additive.ofMul aM) at hm
      rw [haM, hpa, add_zero] at hm
      exact hm.symm
    have hxU : x = uM * piM ^ n := by
      apply Units.ext
      simpa [uM, piM, Units.smul_def, Algebra.smul_def] using hx
    have hmapu : Units.map sigma.symm.toRingEquiv.toMonoidHom uM = euM := by
      apply Units.ext
      rfl
    have hmappi : Units.map sigma.symm.toRingEquiv.toMonoidHom piM = epiM := by
      apply Units.ext
      rfl
    have hp_mul (a b : Mˣ) :
        p (Additive.ofMul (a * b)) =
          p (Additive.ofMul a) + p (Additive.ofMul b) := by
      exact p.map_add (Additive.ofMul a) (Additive.ofMul b)
    have hp_zpow (a : Mˣ) (m : ℤ) :
        p (Additive.ofMul (a ^ m)) = m • p (Additive.ofMul a) := by
      exact p.map_zsmul m (Additive.ofMul a)
    change p (Additive.ofMul
      (Units.map sigma.symm.toRingEquiv.toMonoidHom x)) =
        p (Additive.ofMul x)
    rw [hxU, map_mul, map_zpow, hmapu, hmappi,
      hp_mul, hp_mul, hp_zpow, hp_zpow, hpeu, hpu,
      zero_add, zero_add, hpepi]

/-- **Arithmetic obligation, Blueprint `lem:matrix`.**  On a local packet
plane the twisted-dual packet action has triangular matrix with diagonal
`(1, chi_ell(sigma))`.  Its proof chooses a uniformizer and a Teichmüller
unit, uses the residue action `x ↦ x^(p^a)`, and invokes
`packetAction_twistedDual_apply`; it does not identify that unit with the
class of a primitive root. -/
private theorem packetAction_localPlane_triangular
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ell : ℕ} [Fact ell.Prime]
    (zeta : M) (hzeta : IsPrimitiveRoot zeta ell)
    (v : NU.LocalTheory.FinitePlace M)
    (hv : NU.LocalTheory.residueCharacteristic v ≠ ell)
    (sigma : M ≃ₐ[K] M)
    (hstable :
      (NU.LocalTheory.groupLocalPlane zeta hzeta v).map
          (NU.LocalTheory.packetAction K M ell sigma).toLinearMap =
        NU.LocalTheory.groupLocalPlane zeta hzeta v) :
    ∃ x y : NU.LocalTheory.ElementaryQuotient
        (Field.absoluteGaloisGroup M) ell,
      NU.LocalTheory.IsPlaneBasis
          (NU.LocalTheory.groupLocalPlane zeta hzeta v) x y ∧
        ∃ c : ZMod ell,
          NU.LocalTheory.packetAction K M ell sigma x = x + c • y ∧
          NU.LocalTheory.packetAction K M ell sigma y =
            ((NU.LocalTheory.packetCyclotomicCharacter
              K M ell zeta hzeta sigma : (ZMod ell)ˣ) : ZMod ell) • y := by
  let E := kummerDualEquiv zeta hzeta
  let P := groupLocalPlane zeta hzeta v
  let I := localI ell (primeValuationSubring v)
  let Y : Submodule (ZMod ell)
      (ElementaryQuotient (Field.absoluteGaloisGroup M) ell) :=
    I.comap E.toLinearMap
  have hplace : conjugateFinitePlace K sigma v = v := by
    have hsigma : sigma ∈ packetStabilizer K P := by
      exact hstable
    rw [packetStabilizer_eq_decompositionGroup K M zeta hzeta v hv]
      at hsigma
    exact hsigma
  have hYle : Y ≤ P := by
    intro y hy
    exact localI_le_localD ell (primeValuationSubring v) hy
  have hYrank : Module.finrank (ZMod ell) Y = 1 := by
    change Module.finrank (ZMod ell)
      ((localI ell (primeValuationSubring v)).comap
        (kummerDualEquiv zeta hzeta).toLinearMap) = 1
    rw [Submodule.comap_equiv_eq_map_symm,
      (kummerDualEquiv zeta hzeta).symm.finrank_map_eq]
    exact (local_dimensions zeta hzeta v).1
  have hPrank : Module.finrank (ZMod ell) P = 2 := by
    exact groupLocalPlane_finrank zeta hzeta v hv
  have hYlt : Y < P := by
    refine lt_of_le_of_ne hYle ?_
    intro hEq
    have h := hYrank
    rw [hEq, hPrank] at h
    omega
  obtain ⟨x, hxP, hxY⟩ := SetLike.exists_of_lt hYlt
  letI : Module.Finite (ZMod ell) Y :=
    Module.finite_of_finrank_pos (by rw [hYrank]; omega)
  let byY : Module.Basis (Fin 1) (ZMod ell) Y :=
    Module.finBasisOfFinrankEq (ZMod ell) Y hYrank
  let y : ElementaryQuotient (Field.absoluteGaloisGroup M) ell := byY 0
  have hyY : y ∈ Y := (byY 0).property
  have hyP : y ∈ P := hYle hyY
  have hy0 : y ≠ 0 := by
    intro hy
    apply byY.ne_zero 0
    apply Subtype.ext
    exact hy
  have hind : PairIndependent (k := ZMod ell) x y := by
    change LinearIndependent (ZMod ell) (pairVector x y)
    rw [linearIndependent_fin2]
    refine ⟨hy0, ?_⟩
    intro a ha
    change a • y = x at ha
    apply hxY
    rw [← ha]
    exact Y.smul_mem a hyY
  have hspanle : pairSpan (k := ZMod ell) x y ≤ P := by
    change Submodule.span (ZMod ell) {x, y} ≤ P
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxP
    · exact hyP
  letI : Module.Finite (ZMod ell) P :=
    Module.finite_of_finrank_pos (by rw [hPrank]; omega)
  have hspanrank :
      Module.finrank (ZMod ell) (pairSpan (k := ZMod ell) x y) = 2 := by
    have hrange : Set.range (pairVector x y) = {x, y} := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [pairVector]
      · intro hz
        rcases hz with (rfl | hz)
        · exact ⟨0, rfl⟩
        · have : z = y := by simpa using hz
          subst z
          exact ⟨1, rfl⟩
    change Module.finrank (ZMod ell)
      (Submodule.span (ZMod ell) {x, y}) = 2
    rw [← hrange, finrank_span_eq_card hind]
    rfl
  have hspan : pairSpan (k := ZMod ell) x y = P := by
    apply Submodule.eq_of_le_of_finrank_eq hspanle
    exact hspanrank.trans hPrank.symm
  have hbasis : IsPlaneBasis P x y :=
    ⟨hxP, hyP, hind, hspan⟩
  have hychar : E y ∈ I := hyY
  have hpull_y :
      pullbackCharacter ell sigma.symm.toRingEquiv.toRingHom (E y) = E y :=
    localI_pullback_fixed K M sigma v hplace (E y) hychar
  have hyaction : packetAction K M ell sigma y =
      ((packetCyclotomicCharacter K M ell zeta hzeta sigma :
        (ZMod ell)ˣ) : ZMod ell) • y := by
    apply E.injective
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      rw [kummerDualEquiv_packetAction_apply]
      have heval := DFunLike.congr_fun hpull_y (Additive.ofMul u)
      change E y (Additive.ofMul
        (Units.map sigma.symm.toRingEquiv.toMonoidHom u)) =
          E y (Additive.ofMul u) at heval
      rw [heval, map_smul]
      rfl
  have hxchar : E x ∈ localD ell (primeValuationSubring v) := hxP
  have hdiffchar := localD_twisted_pullback_sub_localI
    K M zeta hzeta sigma v hv hplace (E x) hxchar
  have hxactionChar : E (packetAction K M ell sigma x) =
      ((packetCyclotomicCharacter K M ell zeta hzeta sigma :
        (ZMod ell)ˣ) : ZMod ell) •
        pullbackCharacter ell sigma.symm.toRingEquiv.toRingHom (E x) := by
    apply AddMonoidHom.ext
    intro z
    cases z with
    | ofMul u =>
      change kummerDualEquiv zeta hzeta
        (packetAction K M ell sigma x) (Additive.ofMul u) = _
      rw [kummerDualEquiv_packetAction_apply]
      rfl
  have hdiff : packetAction K M ell sigma x - x ∈ Y := by
    change E (packetAction K M ell sigma x - x) ∈ I
    rw [map_sub, hxactionChar]
    exact hdiffchar
  let yd : Y := ⟨packetAction K M ell sigma x - x, hdiff⟩
  let c : ZMod ell := byY.repr yd 0
  have hcy : packetAction K M ell sigma x - x = c • y := by
    have hr := byY.sum_repr yd
    change (∑ i : Fin 1, (byY.repr yd i) • (byY i : Y)) = yd at hr
    have hr' : (c • (byY 0 : Y)) = yd := by
      have hdefault : (default : Fin 1) = 0 := Subsingleton.elim _ _
      simpa only [Fintype.sum_unique, hdefault] using hr
    exact (congrArg Subtype.val hr').symm
  refine ⟨x, y, hbasis, c, ?_, hyaction⟩
  exact eq_add_of_sub_eq' hcy

/-- Formal determinant extraction from the triangular matrix in Blueprint
`lem:matrix`. -/
private theorem packetAction_localPlane_determinant
    (K M : Type*) [Field K] [Field M] [NumberField K] [NumberField M]
    [Algebra K M] {ell : ℕ} [Fact ell.Prime]
    (zeta : M) (hzeta : IsPrimitiveRoot zeta ell)
    (v : NU.LocalTheory.FinitePlace M)
    (hv : NU.LocalTheory.residueCharacteristic v ≠ ell)
    (sigma : M ≃ₐ[K] M)
    (hstable :
      (NU.LocalTheory.groupLocalPlane zeta hzeta v).map
          (NU.LocalTheory.packetAction K M ell sigma).toLinearMap =
        NU.LocalTheory.groupLocalPlane zeta hzeta v) :
    IsPlaneActionDeterminant
      (NU.LocalTheory.packetAction K M ell sigma)
      (NU.LocalTheory.groupLocalPlane zeta hzeta v)
      ((NU.LocalTheory.packetCyclotomicCharacter
        K M ell zeta hzeta sigma : (ZMod ell)ˣ) : ZMod ell) := by
  obtain ⟨x, y, hxy, c, hx, hy⟩ :=
    packetAction_localPlane_triangular K M zeta hzeta v hv sigma hstable
  refine ⟨x, y, hxy, 1, 0, c,
    ((NU.LocalTheory.packetCyclotomicCharacter
      K M ell zeta hzeta sigma : (ZMod ell)ˣ) : ZMod ell), ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · simp

/-- The genuine mod-`ell` cyclotomic character of an absolute Galois group,
constructed from a primitive root in the chosen algebraic closure. -/
private noncomputable def absoluteCyclotomicCharacter
    (K : Type*) [Field K] [CharZero K]
    (ell : NU.LocalTheory.OddPrime) :
    Field.absoluteGaloisGroup K →* (ZMod (ell : ℕ))ˣ := by
  let zeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose
  let hzeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose_spec
  exact hzeta.autToPow K

/-- The scalar underlying `absoluteCyclotomicCharacter`. -/
private noncomputable def absoluteCyclotomicScalar
    (K : Type*) [Field K] [CharZero K]
    (ell : NU.LocalTheory.OddPrime)
    (g : Field.absoluteGaloisGroup K) : ZMod (ell : ℕ) :=
  (absoluteCyclotomicCharacter K ell g : (ZMod (ell : ℕ))ˣ)

/-- The scalar form of the cyclotomic character is one exactly when the
absolute Galois element fixes every root of unity of that order. -/
private theorem absoluteCyclotomicScalar_eq_one_iff
    (K : Type*) [Field K] [CharZero K]
    (ell : NU.LocalTheory.OddPrime)
    (g : Field.absoluteGaloisGroup K) :
    absoluteCyclotomicScalar K ell g = 1 ↔
      g ∈ NU.LocalTheory.cyclotomicKernel K (ell : ℕ) := by
  letI : Fact (1 < (ell : ℕ)) := ⟨ell.1.2.one_lt⟩
  let zeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose
  let hzeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose_spec
  have hspec : zeta ^ (absoluteCyclotomicScalar K ell g).val =
      NU.LocalTheory.absoluteGaloisAlgEquiv g zeta := by
    change zeta ^
      (hzeta.autToPow K
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) :
          ZMod (ell : ℕ)).val = _
    exact hzeta.autToPow_spec K
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
  constructor
  · intro hscalar eta heta
    obtain ⟨i, _, hi⟩ := hzeta.eq_pow_of_pow_eq_one heta
    rw [← hi]
    change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      (zeta ^ i) = zeta ^ i
    rw [map_pow, ← hspec, hscalar, ZMod.val_one, pow_one]
  · intro hfix
    have hzfix : NU.LocalTheory.absoluteGaloisAlgEquiv g zeta = zeta :=
      hfix zeta hzeta.pow_eq_one
    have hpows : zeta ^ (absoluteCyclotomicScalar K ell g).val =
        zeta ^ 1 := by
      rw [hspec, hzfix, pow_one]
    have hmod : (absoluteCyclotomicScalar K ell g).val ≡
        1 [MOD (ell : ℕ)] := by
      have hm := (pow_eq_pow_iff_modEq).mp
        (show hzeta.toRootsOfUnity ^
            (absoluteCyclotomicScalar K ell g).val =
              hzeta.toRootsOfUnity ^ 1 by
          apply rootsOfUnity.coe_injective
          simpa only [rootsOfUnity.coe_pow,
            hzeta.val_toRootsOfUnity_coe] using hpows)
      rw [← Subgroup.orderOf_coe, ← orderOf_units,
        hzeta.val_toRootsOfUnity_coe, ← hzeta.eq_orderOf] at hm
      exact hm
    calc
      absoluteCyclotomicScalar K ell g =
          ((absoluteCyclotomicScalar K ell g).val : ZMod (ell : ℕ)) := by
        exact (ZMod.natCast_zmod_val _).symm
      _ = (1 : ZMod (ell : ℕ)) := by
        simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod

/-- A packet determinant at one finite quotient level, with the packet,
stabilizer membership, and matrix determinant all retained. -/
private def HasPacketDeterminantAtLevel
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : NU.LocalTheory.OpenNormalSubgroup G)
    (ell : NU.LocalTheory.OddPrime) (g : G)
    (d : ZMod (ell : ℕ)) : Prop :=
  ∃ P : NU.LocalTheory.GroupSubspace U.toSubgroup (ell : ℕ),
    NU.LocalTheory.IsPacket (ell : ℕ) P ∧
      QuotientGroup.mk g ∈ NU.LocalTheory.barePacketStabilizer U ell P ∧
      IsPlaneActionDeterminant
        (NU.LocalTheory.barePacketAction U ell (QuotientGroup.mk g)) P d

namespace PacketTransport

open NU.LocalTheory

/-- Restriction of a topological group equivalence to two subgroups whose
images agree. -/
private noncomputable def subgroupMapEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (S : Subgroup G) (T : Subgroup H)
    (hmap : Subgroup.map e.toMulEquiv.toMonoidHom S = T) :
    S ≃ₜ* T where
  toFun x := ⟨e x, by
    rw [← hmap]
    exact ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨e.symm y, by
    have hy : (y : H) ∈ Subgroup.map e.toMulEquiv.toMonoidHom S := by
      rw [hmap]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    change e x = (y : H) at hxy
    change e.symm (y : H) ∈ S
    have heq : e.symm (y : H) = x := by
      rw [← hxy, e.symm_apply_apply]
    rw [heq]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact e.map_mul x y
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.continuous_invFun.comp continuous_subtype_val

/-- Restriction of an ambient topological group equivalence to a transported
open normal level. -/
private noncomputable def levelEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : NU.LocalTheory.OpenNormalSubgroup G) :
    U.toSubgroup ≃ₜ* (U.map e).toSubgroup where
  toFun x := ⟨e x,
    (NU.LocalTheory.OpenNormalSubgroup.mem_map e U x).2 x.property⟩
  invFun y := ⟨e.symm y, by
    rw [← NU.LocalTheory.OpenNormalSubgroup.mem_map e U]
    simpa using y.property⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y
  map_mul' x y := by ext; exact e.map_mul x y
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.continuous_invFun.comp continuous_subtype_val

@[simp]
private theorem levelEquiv_apply
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : NU.LocalTheory.OpenNormalSubgroup G)
    (x : U.toSubgroup) : ((levelEquiv e U x : (U.map e).toSubgroup) : H) =
      e x :=
  rfl

private def continuousHom
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) : G →ₜ* H :=
  ContinuousMonoidHom.mk e.toMulEquiv.toMonoidHom e.continuous_toFun

private def pullCharacter
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) (a : ContinuousCharacter H n) :
    ContinuousCharacter G n :=
  a.comp (additiveContinuousHom (continuousHom e))

/-- Continuous characters are transported intrinsically by a topological
group equivalence.  This is the character identification used below; it does
not pass through a reciprocity map. -/
private noncomputable def pullCharacterLinearEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) :
    ContinuousCharacter H n ≃ₗ[ZMod n] ContinuousCharacter G n where
  toFun := pullCharacter n e
  invFun := pullCharacter n e.symm
  left_inv a := by
    ext h
    cases h with
    | ofMul h =>
        change a (Additive.ofMul (e (e.symm h))) = a (Additive.ofMul h)
        rw [e.apply_symm_apply]
  right_inv a := by
    ext g
    cases g with
    | ofMul g =>
        change a (Additive.ofMul (e.symm (e g))) = a (Additive.ofMul g)
        rw [e.symm_apply_apply]
  map_add' a b := by
    ext g
    rfl
  map_smul' c a := by
    ext g
    simp only [RingHom.id_apply]
    let evH : ContinuousCharacter H n →+ ZMod n :=
      { toFun := fun chi => chi (Additive.ofMul (e (Additive.toMul g)))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let evG : ContinuousCharacter G n →+ ZMod n :=
      { toFun := fun chi => chi g
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hH : (c • a) (Additive.ofMul (e (Additive.toMul g))) =
        c * a (Additive.ofMul (e (Additive.toMul g))) := by
      simpa [evH] using ZMod.map_smul evH c a
    have hG : (c • pullCharacter n e a) g =
        c * pullCharacter n e a g := by
      simpa [evG] using ZMod.map_smul evG c (pullCharacter n e a)
    change (c • a) (Additive.ofMul (e (Additive.toMul g))) =
      (c • pullCharacter n e a) g
    rw [hH, hG]
    rfl

private theorem cupZero_pull
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (e : G ≃ₜ* H) {a b : ContinuousCharacter H n}
    (h : CupZero n a b) :
    CupZero n (pullCharacter n e a) (pullCharacter n e b) := by
  obtain ⟨c, hc⟩ := h
  let c' : C(G, ZMod n) :=
    ⟨fun g => c (e g), c.continuous.comp e.continuous_toFun⟩
  refine ⟨c', ?_⟩
  intro sigma tau
  change a (Additive.ofMul (e sigma)) * b (Additive.ofMul (e tau)) =
    c (e sigma) + c (e tau) - c (e (sigma * tau))
  simpa only [continuousCharacterValue, map_mul] using hc (e sigma) (e tau)

private theorem elementaryClass_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Function.Surjective (elementaryClass (G := G) n) := by
  intro x
  obtain ⟨y, rfl⟩ :=
    (LinearMap.range (LinearMap.lsmul ℤ
      (Additive (TopologicalAbelianization G)) (n : ℤ))).mkQ_surjective x
  cases y with
  | ofMul q =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, rfl⟩

private theorem evaluation_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x : ElementaryQuotient G n)
    (a : ContinuousCharacter H n) :
    evaluation n (elementaryQuotientTransport n e x) a =
      evaluation n x (pullCharacter n e a) := by
  obtain ⟨g, rfl⟩ := elementaryClass_surjective n x
  rw [elementaryQuotientTransport_elementaryClass,
    evaluation_elementaryClass, evaluation_elementaryClass]
  rfl

private theorem evaluationDet_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) (e : G ≃ₜ* H) (x y : ElementaryQuotient G n)
    (a b : ContinuousCharacter H n) :
    evaluationDet (elementaryQuotientTransport n e x)
        (elementaryQuotientTransport n e y) a b =
      evaluationDet x y (pullCharacter n e a)
        (pullCharacter n e b) := by
  simp only [evaluationDet, evaluation_transport]

private theorem planeBasis_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    {n : ℕ} [Fact n.Prime] (e : G ≃ₜ* H)
    (P : GroupSubspace G n) {x y : ElementaryQuotient G n}
    (h : IsPlaneBasis P x y) :
    IsPlaneBasis (P.map (elementaryQuotientTransport n e).toLinearMap)
      (elementaryQuotientTransport n e x)
      (elementaryQuotientTransport n e y) := by
  refine ⟨⟨x, h.1, rfl⟩, ⟨y, h.2.1, rfl⟩, ?_, ?_⟩
  · have hmap := h.2.2.1.map'
      (elementaryQuotientTransport n e).toLinearMap
      (elementaryQuotientTransport n e).ker
    change LinearIndependent (ZMod n)
      (fun i => elementaryQuotientTransport n e (pairVector x y i)) at hmap
    have hfun :
        (fun i => elementaryQuotientTransport n e (pairVector x y i)) =
          pairVector (elementaryQuotientTransport n e x)
            (elementaryQuotientTransport n e y) := by
      funext i
      fin_cases i <;> rfl
    rwa [hfun] at hmap
  · rw [← h.2.2.2]
    calc
      pairSpan (elementaryQuotientTransport n e x)
          (elementaryQuotientTransport n e y) =
          Submodule.span (ZMod n)
            {(elementaryQuotientTransport n e) x,
              (elementaryQuotientTransport n e) y} := rfl
      _ = Submodule.span (ZMod n)
          ((elementaryQuotientTransport n e) '' {x, y}) := by
            rw [Set.image_pair]
      _ = Submodule.map (elementaryQuotientTransport n e).toLinearMap
          (Submodule.span (ZMod n) {x, y}) :=
            (LinearMap.map_span _ _).symm
      _ = Submodule.map (elementaryQuotientTransport n e).toLinearMap
          (pairSpan x y) := rfl

set_option maxHeartbeats 800000 in
private theorem packet_transport
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (n : ℕ) [Fact n.Prime] (e : G ≃ₜ* H)
    (P : GroupSubspace G n) (hP : IsPacket n P) :
    IsPacket n (P.map (elementaryQuotientTransport n e).toLinearMap) := by
  obtain ⟨x, y, hxy, hzero⟩ := hP
  refine ⟨elementaryQuotientTransport n e x,
    elementaryQuotientTransport n e y,
    planeBasis_transport e P hxy, ?_⟩
  intro a b hab
  rw [evaluationDet_transport]
  exact hzero _ _ (cupZero_pull n e hab)

private theorem action_intertwines
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : NU.LocalTheory.OpenNormalSubgroup G) (p : OddPrime)
    (sigma : G ⧸ U.toSubgroup)
    (x : ElementaryQuotient U.toSubgroup (p : ℕ)) :
    elementaryQuotientTransport (p : ℕ) (levelEquiv e U)
        (barePacketAction U p sigma x) =
      barePacketAction (U.map e) p (openNormalQuotientEquiv e U sigma)
        (elementaryQuotientTransport (p : ℕ) (levelEquiv e U) x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective sigma
  obtain ⟨h, rfl⟩ := elementaryClass_surjective (p : ℕ) x
  simp only [barePacketAction_elementaryClass,
    elementaryQuotientTransport_elementaryClass,
    openNormalQuotientEquiv_mk]
  congr 1
  apply Subtype.ext
  simp [conjugateInOpenNormal]

set_option maxHeartbeats 800000 in
private theorem packet_map
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (U : NU.LocalTheory.OpenNormalSubgroup G) (p : OddPrime)
    (sigma : G ⧸ U.toSubgroup) (P : GroupSubspace U.toSubgroup (p : ℕ)) :
    conjugateBarePacket (U.map e) p (openNormalQuotientEquiv e U sigma)
        (P.map (elementaryQuotientTransport (p : ℕ)
          (levelEquiv e U)).toLinearMap) =
      (conjugateBarePacket U p sigma P).map
        (elementaryQuotientTransport (p : ℕ)
          (levelEquiv e U)).toLinearMap := by
  rw [conjugateBarePacket, conjugateBarePacket,
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  exact (action_intertwines e U p sigma x).symm

end PacketTransport

/-- Identity transport between equal subgroups, used to compare a bare marked
level with its arithmetic cyclotomic realization. -/
private def subgroupContinuousMulEquivOfEq
    {G : Type*} [Group G] [TopologicalSpace G]
    {A B : Subgroup G} (h : A = B) : A ≃ₜ* B where
  toFun x := ⟨x, by rw [← h]; exact x.property⟩
  invFun y := ⟨y, by rw [h]; exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

set_option maxHeartbeats 1200000 in
/-- Plane bases transport along any linear equivalence of elementary
quotients; no underlying group equivalence is needed for this step. -/
private theorem planeBasis_map_linearEquiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    {n : ℕ} [Fact n.Prime]
    (e : NU.LocalTheory.ElementaryQuotient G n ≃ₗ[ZMod n]
      NU.LocalTheory.ElementaryQuotient H n)
    (P : NU.LocalTheory.GroupSubspace G n)
    {x y : NU.LocalTheory.ElementaryQuotient G n}
    (h : NU.LocalTheory.IsPlaneBasis P x y) :
    NU.LocalTheory.IsPlaneBasis (P.map e.toLinearMap) (e x) (e y) := by
  refine ⟨⟨x, h.1, rfl⟩, ⟨y, h.2.1, rfl⟩, ?_, ?_⟩
  · have hmap := h.2.2.1.map' e.toLinearMap e.ker
    change LinearIndependent (ZMod n)
      (fun i => e (NU.LocalTheory.pairVector x y i)) at hmap
    have hfun : (fun i => e (NU.LocalTheory.pairVector x y i)) =
        NU.LocalTheory.pairVector (e x) (e y) := by
      funext i
      fin_cases i <;> rfl
    rwa [hfun] at hmap
  · rw [← h.2.2.2]
    calc
      NU.LocalTheory.pairSpan (e x) (e y) =
          Submodule.span (ZMod n) {e x, e y} := rfl
      _ = Submodule.span (ZMod n) (e '' {x, y}) := by
        rw [Set.image_pair]
      _ = Submodule.map e.toLinearMap
          (Submodule.span (ZMod n) {x, y}) :=
        (LinearMap.map_span _ _).symm
      _ = Submodule.map e.toLinearMap
          (NU.LocalTheory.pairSpan x y) := rfl

set_option maxHeartbeats 1200000 in
/-- **Arithmetic obligation, Blueprint `lem:matrix` + `def:marked`.**  The
finite image of a decomposition group supplies a source packet at one
simultaneously marked level, and the local triangular calculation identifies
its determinant with the source cyclotomic scalar. -/
private theorem source_packetDeterminant_at_markedLevel
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂)
    (hmap : Subgroup.map alpha.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1)
    (g : Field.absoluteGaloisGroup K₁)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1)
    (ell : NU.LocalTheory.OddPrime)
    (haway : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace P₁) ≠ (ell : ℕ))
    (U : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K₁))
    (hmarked : IsThetaMarkedLevel alpha ell U) :
    HasPacketDeterminantAtLevel U ell g
      (absoluteCyclotomicScalar K₁ ell g) := by
  let H := NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1
  let D := NU.LocalTheory.openNormalQuotientImage U H
  have hU : NU.LocalTheory.IsMarkedLevel K₁ ell U := by
    intro u hu
    exact (hmarked hu).1
  have hDcrit : D ∈ NU.LocalTheory.bareCrit U ell := by
    rw [NU.LocalTheory.bareCrit_marked_correct K₁ U ell hU]
    refine ⟨P₁.1, ?_, rfl⟩
    exact ⟨P₁.2, ambientFinitePlace P₁,
      (primeValuationSubring_ambientFinitePlace P₁).symm, haway⟩
  obtain ⟨P, hP, hDP⟩ :=
    (NU.LocalTheory.mem_bareCrit U ell D).mp hDcrit
  have hgD : QuotientGroup.mk g ∈ D := by
    exact ⟨g, hg, rfl⟩
  have hstableBare :
      P.map (NU.LocalTheory.barePacketAction U ell
        (QuotientGroup.mk g)).toLinearMap = P := by
    rw [hDP] at hgD
    exact hgD
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K₁ U
  let o := NU.LocalTheory.canonicalCyclotomicOrientation K₁
  have hlevel : NU.LocalTheory.orientedCyclotomicLevel o L ell =
      U.toSubgroup := by
    rw [NU.LocalTheory.orientedCyclotomicLevel, inf_eq_left.mpr]
    · exact NU.LocalTheory.levelKernel_galoisLevelOfOpenNormal K₁ U
    · simpa [L, o, NU.LocalTheory.IsMarkedLevel,
        NU.LocalTheory.canonicalCyclotomicOrientation] using hU
  let e0 : U.toSubgroup ≃ₜ*
      NU.LocalTheory.orientedCyclotomicLevel o L ell :=
    subgroupContinuousMulEquivOfEq hlevel.symm
  let eQ0 : (Field.absoluteGaloisGroup K₁ ⧸ U.toSubgroup) ≃*
      NU.LocalTheory.orientedCyclotomicQuotient o L ell :=
    QuotientGroup.quotientMulEquivOfEq hlevel.symm
  obtain ⟨eC, eQC, hrestrict, hpacket, hactionC⟩ :=
    NU.LocalTheory.exists_orientedCyclotomicComparison o L ell
  let E0 := NU.LocalTheory.elementaryQuotientTransport (ell : ℕ) e0
  let EC := NU.LocalTheory.elementaryQuotientTransport (ell : ℕ) eC
  let E := E0.trans EC
  let gamma := eQ0 (QuotientGroup.mk g)
  let sigma := eQC gamma
  have haction0 (x : NU.LocalTheory.ElementaryQuotient
      U.toSubgroup (ell : ℕ)) :
      E0 (NU.LocalTheory.barePacketAction U ell
        (QuotientGroup.mk g) x) =
      NU.LocalTheory.orientedPacketAction o L ell gamma (E0 x) := by
    dsimp only [E0, gamma, eQ0]
    obtain ⟨u, rfl⟩ :=
      PacketTransport.elementaryClass_surjective (ell : ℕ) x
    simp only [NU.LocalTheory.barePacketAction_elementaryClass,
      NU.LocalTheory.orientedPacketAction_elementaryClass,
      NU.LocalTheory.elementaryQuotientTransport_elementaryClass,
      QuotientGroup.quotientMulEquivOfEq_mk]
    congr 1
  have haction (x : NU.LocalTheory.ElementaryQuotient
      U.toSubgroup (ell : ℕ)) :
      E (NU.LocalTheory.barePacketAction U ell
        (QuotientGroup.mk g) x) =
      NU.LocalTheory.packetAction K₁
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma (E x) := by
    calc
      E (NU.LocalTheory.barePacketAction U ell
          (QuotientGroup.mk g) x) =
          EC (E0 (NU.LocalTheory.barePacketAction U ell
            (QuotientGroup.mk g) x)) := rfl
      _ = EC (NU.LocalTheory.orientedPacketAction o L ell gamma (E0 x)) := by
        rw [haction0]
      _ = NU.LocalTheory.packetAction K₁
          (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma
            (EC (E0 x)) := hactionC gamma (E0 x)
      _ = _ := rfl
  let P0 := P.map E0.toLinearMap
  let PC := P0.map EC.toLinearMap
  have hP0 : NU.LocalTheory.IsPacket (ell : ℕ) P0 :=
    PacketTransport.packet_transport (ell : ℕ) e0 P hP
  have hPC : NU.LocalTheory.IsPacket (ell : ℕ) PC :=
    (hpacket P0).2 hP0
  have hPCeq : PC = P.map E.toLinearMap := by
    dsimp [PC, P0, E]
    rw [← Submodule.map_comp]
    rfl
  have hstableC :
      PC.map (NU.LocalTheory.packetAction K₁
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma).toLinearMap =
        PC := by
    rw [hPCeq]
    calc
      (P.map E.toLinearMap).map
          (NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap =
          P.map ((NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap.comp E.toLinearMap) :=
        (Submodule.map_comp _ _ _).symm
      _ = P.map (E.toLinearMap.comp
          (NU.LocalTheory.barePacketAction U ell
            (QuotientGroup.mk g)).toLinearMap) := by
        congr 1
        ext x
        exact (haction x).symm
      _ = (P.map (NU.LocalTheory.barePacketAction U ell
          (QuotientGroup.mk g)).toLinearMap).map E.toLinearMap :=
        Submodule.map_comp _ _ _
      _ = P.map E.toLinearMap := by rw [hstableBare]
  let zetaAbs := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K₁) (ell : ℕ)).choose
  have hzetaAbs : IsPrimitiveRoot zetaAbs (ell : ℕ) :=
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure K₁) (ell : ℕ)).choose_spec
  have hzetaMem : zetaAbs ∈ L.field := by
    change zetaAbs ∈ IntermediateField.fixedField U.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro u hu
    exact hU hu zetaAbs hzetaAbs.pow_eq_one
  let zetaL : L.field := ⟨zetaAbs, hzetaMem⟩
  let zeta : CyclotomicField (ell : ℕ) L.field :=
    algebraMap L.field (CyclotomicField (ell : ℕ) L.field) zetaL
  have hzetaL : IsPrimitiveRoot zetaL (ell : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := L.field.val.toMonoidHom) (hf := L.field.val.injective)
    simpa [zetaL] using hzetaAbs
  have hzeta : IsPrimitiveRoot zeta (ell : ℕ) :=
    hzetaL.map_of_injective
      (algebraMap L.field
        (CyclotomicField (ell : ℕ) L.field)).injective
  have hpMem : PC ∈
      {Q : NU.LocalTheory.GroupSubspace
          (Field.absoluteGaloisGroup
            (CyclotomicField (ell : ℕ) L.field)) (ell : ℕ) |
        NU.LocalTheory.IsPacket (ell : ℕ) Q} := hPC
  rw [NU.LocalTheory.packet_theorem ell.2 zeta hzeta] at hpMem
  obtain ⟨w, hw, hPCw⟩ := hpMem
  have hstableW :
      (NU.LocalTheory.groupLocalPlane zeta hzeta w).map
          (NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap =
        NU.LocalTheory.groupLocalPlane zeta hzeta w := by
    rw [← hPCw]
    exact hstableC
  have hdetC := packetAction_localPlane_determinant K₁
    (CyclotomicField (ell : ℕ) L.field) zeta hzeta w hw sigma hstableW
  have hresSigma :
      NU.LocalTheory.galoisRestriction K₁ L.field
        (CyclotomicField (ell : ℕ) L.field) sigma =
      NU.LocalTheory.absoluteRestriction L g := by
    simpa [sigma, gamma, eQ0] using hrestrict g
  have habsSpec :
      (show AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁ from g)
          zetaAbs =
        zetaAbs ^ (absoluteCyclotomicScalar K₁ ell g).val := by
    exact (hzetaAbs.autToPow_spec K₁ g).symm
  have hrestrictZeta :
      NU.LocalTheory.absoluteRestriction L g zetaL =
        zetaL ^ (absoluteCyclotomicScalar K₁ ell g).val := by
    apply Subtype.ext
    rw [NU.LocalTheory.absoluteRestriction_apply]
    exact habsSpec
  have hsigmaZeta : sigma zeta =
      zeta ^ (absoluteCyclotomicScalar K₁ ell g).val := by
    calc
      sigma zeta = algebraMap L.field
          (CyclotomicField (ell : ℕ) L.field)
          (NU.LocalTheory.galoisRestriction K₁ L.field
            (CyclotomicField (ell : ℕ) L.field) sigma zetaL) := by
              symm
              exact NU.LocalTheory.galoisRestriction_apply K₁ L.field
                (CyclotomicField (ell : ℕ) L.field) sigma zetaL
      _ = algebraMap L.field (CyclotomicField (ell : ℕ) L.field)
          (NU.LocalTheory.absoluteRestriction L g zetaL) := by
            rw [hresSigma]
      _ = algebraMap L.field (CyclotomicField (ell : ℕ) L.field)
          (zetaL ^ (absoluteCyclotomicScalar K₁ ell g).val) := by
            rw [hrestrictZeta]
      _ = zeta ^ (absoluteCyclotomicScalar K₁ ell g).val := by
            rw [map_pow]
  have hscalar :
      ((NU.LocalTheory.packetCyclotomicCharacter K₁
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
          zeta hzeta sigma : (ZMod (ell : ℕ))ˣ) : ZMod (ell : ℕ)) =
        absoluteCyclotomicScalar K₁ ell g := by
    apply ZMod.val_injective
    apply hzeta.pow_inj
    · exact ZMod.val_lt _
    · exact ZMod.val_lt _
    · exact (NU.LocalTheory.packetCyclotomicCharacter_spec K₁
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
          zeta hzeta sigma).symm.trans hsigmaZeta
  rcases hdetC with
    ⟨xc, yc, hxyC, a, b, c, r, hxc, hyc, hdet⟩
  let x := E.symm xc
  let y := E.symm yc
  have hPCback : PC.map E.symm.toLinearMap = P := by
    rw [hPCeq, ← Submodule.map_comp]
    convert Submodule.map_id P using 1
    ext z
    simp
  have hxyPC : NU.LocalTheory.IsPlaneBasis PC xc yc := by
    rw [hPCw]
    exact hxyC
  have hxyBack := planeBasis_map_linearEquiv E.symm PC hxyPC
  rw [hPCback] at hxyBack
  have hxBack :
      NU.LocalTheory.barePacketAction U ell (QuotientGroup.mk g) x =
        a • x + c • y := by
    apply E.injective
    calc
      E (NU.LocalTheory.barePacketAction U ell
          (QuotientGroup.mk g) x) =
          NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma (E x) := haction x
      _ = NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma xc := by simp [x]
      _ = a • xc + c • yc := hxc
      _ = E (a • x + c • y) := by simp [x, y]
  have hyBack :
      NU.LocalTheory.barePacketAction U ell (QuotientGroup.mk g) y =
        b • x + r • y := by
    apply E.injective
    calc
      E (NU.LocalTheory.barePacketAction U ell
          (QuotientGroup.mk g) y) =
          NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma (E y) := haction y
      _ = NU.LocalTheory.packetAction K₁
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma yc := by simp [y]
      _ = b • xc + r • yc := hyc
      _ = E (b • x + r • y) := by simp [x, y]
  refine ⟨P, hP, hstableBare, x, y, hxyBack,
    a, b, c, r, hxBack, hyBack, ?_⟩
  exact hscalar.symm.trans hdet

/-- The coefficient determinant in any certified plane basis is the
basis-independent determinant of the restricted endomorphism. -/
private theorem planeActionCoefficient_det
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ell : ℕ} [Fact ell.Prime]
    (T : ElementaryQuotient G ell ≃ₗ[ZMod ell] ElementaryQuotient G ell)
    (P : GroupSubspace G ell)
    (hstable : P.map T.toLinearMap = P)
    (x y : ElementaryQuotient G ell)
    (hxy : IsPlaneBasis P x y)
    (a b c e : ZMod ell)
    (hx : T x = a • x + c • y)
    (hy : T y = b • x + e • y) :
    a * e - b * c = LinearMap.det
      ((T.toLinearMap.domRestrict P).codRestrict P (fun z => by
        have hz : T z ∈ P.map T.toLinearMap := ⟨z, z.property, rfl⟩
        rwa [hstable] at hz)) := by
  let f : P →ₗ[ZMod ell] P :=
    (T.toLinearMap.domRestrict P).codRestrict P (fun z => by
      have hz : T z ∈ P.map T.toLinearMap := ⟨z, z.property, rfl⟩
      rwa [hstable] at hz)
  let v : Fin 2 → P := fun i =>
    ⟨pairVector x y i, by
      fin_cases i
      · exact hxy.1
      · exact hxy.2.1⟩
  have hv0 : v 0 = ⟨x, hxy.1⟩ := rfl
  have hv1 : v 1 = ⟨y, hxy.2.1⟩ := rfl
  have hvli : LinearIndependent (ZMod ell) v := by
    apply LinearIndependent.of_comp P.subtype
    exact hxy.2.2.1
  have hvspan : (⊤ : Submodule (ZMod ell) P) ≤
      Submodule.span (ZMod ell) (Set.range v) := by
    intro z _
    have hz : (z : ElementaryQuotient G ell) ∈
        pairSpan (k := ZMod ell) x y := by
      rw [hxy.2.2.2]
      exact z.property
    obtain ⟨A, B, hAB⟩ := Submodule.mem_span_pair.mp hz
    have hrange : Set.range v = {v 0, v 1} := by
      ext q
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hq
        rcases hq with (rfl | hq)
        · exact ⟨0, rfl⟩
        · have : q = v 1 := by simpa using hq
          subst q
          exact ⟨1, rfl⟩
    rw [hrange, Submodule.mem_span_pair]
    refine ⟨A, B, ?_⟩
    apply Subtype.ext
    simpa [hv0, hv1] using hAB
  let basis : Module.Basis (Fin 2) (ZMod ell) P :=
    Module.Basis.mk hvli hvspan
  have hb0 : basis 0 = ⟨x, hxy.1⟩ := by
    rw [Module.Basis.mk_apply, hv0]
  have hb1 : basis 1 = ⟨y, hxy.2.1⟩ := by
    rw [Module.Basis.mk_apply, hv1]
  have hf0 : f (basis 0) = a • basis 0 + c • basis 1 := by
    apply Subtype.ext
    simpa [f, hb0, hb1] using hx
  have hf1 : f (basis 1) = b • basis 0 + e • basis 1 := by
    apply Subtype.ext
    simpa [f, hb0, hb1] using hy
  let A := LinearMap.toMatrix basis basis f
  have hA00 : A 0 0 = a := by
    change (LinearMap.toMatrix basis basis) f 0 0 = a
    rw [LinearMap.toMatrix_apply, hf0, map_add, map_smul, map_smul,
      basis.repr_self, basis.repr_self]
    simp
  have hA10 : A 1 0 = c := by
    change (LinearMap.toMatrix basis basis) f 1 0 = c
    rw [LinearMap.toMatrix_apply, hf0, map_add, map_smul, map_smul,
      basis.repr_self, basis.repr_self]
    simp
  have hA01 : A 0 1 = b := by
    change (LinearMap.toMatrix basis basis) f 0 1 = b
    rw [LinearMap.toMatrix_apply, hf1, map_add, map_smul, map_smul,
      basis.repr_self, basis.repr_self]
    simp
  have hA11 : A 1 1 = e := by
    change (LinearMap.toMatrix basis basis) f 1 1 = e
    rw [LinearMap.toMatrix_apply, hf1, map_add, map_smul, map_smul,
      basis.repr_self, basis.repr_self]
    simp
  change a * e - b * c = LinearMap.det f
  rw [← LinearMap.det_toMatrix basis, Matrix.det_fin_two]
  change a * e - b * c = A 0 0 * A 1 1 - A 0 1 * A 1 0
  rw [hA00, hA11, hA01, hA10]

/-- A plane action has only one certified coefficient determinant. -/
private theorem planeActionDeterminant_unique
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ell : ℕ} [Fact ell.Prime]
    (T : ElementaryQuotient G ell ≃ₗ[ZMod ell] ElementaryQuotient G ell)
    (P : GroupSubspace G ell)
    (hstable : P.map T.toLinearMap = P)
    {d₁ d₂ : ZMod ell}
    (h₁ : IsPlaneActionDeterminant T P d₁)
    (h₂ : IsPlaneActionDeterminant T P d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨x₁, y₁, hxy₁, a₁, b₁, c₁, e₁, hx₁, hy₁, hd₁⟩
  rcases h₂ with ⟨x₂, y₂, hxy₂, a₂, b₂, c₂, e₂, hx₂, hy₂, hd₂⟩
  calc
    d₁ = a₁ * e₁ - b₁ * c₁ := hd₁
    _ = LinearMap.det
        ((T.toLinearMap.domRestrict P).codRestrict P (fun z => by
          have hz : T z ∈ P.map T.toLinearMap := ⟨z, z.property, rfl⟩
          rwa [hstable] at hz)) :=
      planeActionCoefficient_det T P hstable x₁ y₁ hxy₁
        a₁ b₁ c₁ e₁ hx₁ hy₁
    _ = a₂ * e₂ - b₂ * c₂ :=
      (planeActionCoefficient_det T P hstable x₂ y₂ hxy₂
        a₂ b₂ c₂ e₂ hx₂ hy₂).symm
    _ = d₂ := hd₂.symm

/-- **Finite transport obligation, Blueprint `thm:det`.**  T2 transports a
packet plane and conjugates its action, so its determinant is unchanged. -/
private theorem packetDeterminant_transport_at_markedLevel
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (ell : NU.LocalTheory.OddPrime)
    (U : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K₁))
    (g : Field.absoluteGaloisGroup K₁) (d : ZMod (ell : ℕ))
    (hdet : HasPacketDeterminantAtLevel U ell g d) :
    HasPacketDeterminantAtLevel (U.map alpha) ell (alpha g) d := by
  rcases hdet with
    ⟨P, hP, hstabilizes, x, y, hxy, a, b, c, r, hx, hy, hd⟩
  let eU := PacketTransport.levelEquiv alpha U
  let E := NU.LocalTheory.elementaryQuotientTransport (ell : ℕ) eU
  let Q := P.map E.toLinearMap
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact PacketTransport.packet_transport (ell : ℕ) eU P hP
  · change NU.LocalTheory.conjugateBarePacket (U.map alpha) ell
      (QuotientGroup.mk (alpha g)) Q = Q
    rw [show QuotientGroup.mk (alpha g) =
      NU.LocalTheory.openNormalQuotientEquiv alpha U (QuotientGroup.mk g)
        from rfl]
    change NU.LocalTheory.conjugateBarePacket (U.map alpha) ell
      (NU.LocalTheory.openNormalQuotientEquiv alpha U (QuotientGroup.mk g))
        (P.map (NU.LocalTheory.elementaryQuotientTransport (ell : ℕ)
          (PacketTransport.levelEquiv alpha U)).toLinearMap) = _
    rw [PacketTransport.packet_map]
    change NU.LocalTheory.conjugateBarePacket U ell
      (QuotientGroup.mk g) P = P at hstabilizes
    rw [hstabilizes]
  · refine ⟨E x, E y,
      PacketTransport.planeBasis_transport eU P hxy,
      a, b, c, r, ?_, ?_, hd⟩
    · have hintertwines := PacketTransport.action_intertwines
        alpha U ell (QuotientGroup.mk g) x
      calc
        NU.LocalTheory.barePacketAction (U.map alpha) ell
            (QuotientGroup.mk (alpha g)) (E x) =
            E (NU.LocalTheory.barePacketAction U ell
              (QuotientGroup.mk g) x) := by
                symm
                simpa [E, eU] using hintertwines
        _ = E (a • x + c • y) := by rw [hx]
        _ = a • E x + c • E y := by simp [E]
    · have hintertwines := PacketTransport.action_intertwines
        alpha U ell (QuotientGroup.mk g) y
      calc
        NU.LocalTheory.barePacketAction (U.map alpha) ell
            (QuotientGroup.mk (alpha g)) (E y) =
            E (NU.LocalTheory.barePacketAction U ell
              (QuotientGroup.mk g) y) := by
                symm
                simpa [E, eU] using hintertwines
        _ = E (b • x + r • y) := by rw [hy]
        _ = b • E x + r • E y := by simp [E]

set_option maxHeartbeats 1200000 in
/-- **Arithmetic obligation, Blueprint `cor:chi`.**  The target packet is
identified only existentially: `packet_theorem` supplies some finite place
`z` prime to `ell`, and `lem:matrix` computes its determinant as the global
target cyclotomic scalar.  No identification of `z` with the designated
place is asserted. -/
private theorem target_packetDeterminant_identifies_cyclotomic
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (ell : NU.LocalTheory.OddPrime)
    (U : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K₁))
    (g : Field.absoluteGaloisGroup K₁) (d : ZMod (ell : ℕ))
    (hmarked : IsThetaMarkedLevel alpha ell U)
    (hdet : HasPacketDeterminantAtLevel (U.map alpha) ell (alpha g) d) :
    d = absoluteCyclotomicScalar K₂ ell (alpha g) := by
  let V := U.map alpha
  let g₂ := alpha g
  have hV : IsMarkedLevel K₂ ell V := by
    intro x hx
    have hy : alpha.symm x ∈ U.toSubgroup := by
      rw [← NU.LocalTheory.OpenNormalSubgroup.mem_map alpha U]
      simpa [V]
    have hx₂ := (hmarked hy).2
    change alpha (alpha.symm x) ∈
      NU.LocalTheory.cyclotomicKernel K₂ (ell : ℕ) at hx₂
    rw [alpha.apply_symm_apply] at hx₂
    exact hx₂
  rcases hdet with
    ⟨P, hP, hstableBare, x, y, hxy, a, b, c, r, hx, hy, hd⟩
  change P.map (NU.LocalTheory.barePacketAction V ell
    (QuotientGroup.mk g₂)).toLinearMap = P at hstableBare
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K₂ V
  let o := NU.LocalTheory.canonicalCyclotomicOrientation K₂
  have hlevel : NU.LocalTheory.orientedCyclotomicLevel o L ell =
      V.toSubgroup := by
    rw [NU.LocalTheory.orientedCyclotomicLevel, inf_eq_left.mpr]
    · exact NU.LocalTheory.levelKernel_galoisLevelOfOpenNormal K₂ V
    · simpa [L, o, NU.LocalTheory.IsMarkedLevel,
        NU.LocalTheory.canonicalCyclotomicOrientation] using hV
  let e0 : V.toSubgroup ≃ₜ*
      NU.LocalTheory.orientedCyclotomicLevel o L ell :=
    subgroupContinuousMulEquivOfEq hlevel.symm
  let eQ0 : (Field.absoluteGaloisGroup K₂ ⧸ V.toSubgroup) ≃*
      NU.LocalTheory.orientedCyclotomicQuotient o L ell :=
    QuotientGroup.quotientMulEquivOfEq hlevel.symm
  obtain ⟨eC, eQC, hrestrict, hpacket, hactionC⟩ :=
    NU.LocalTheory.exists_orientedCyclotomicComparison o L ell
  let E0 := NU.LocalTheory.elementaryQuotientTransport (ell : ℕ) e0
  let EC := NU.LocalTheory.elementaryQuotientTransport (ell : ℕ) eC
  let E := E0.trans EC
  let gamma := eQ0 (QuotientGroup.mk g₂)
  let sigma := eQC gamma
  have haction0 (q : NU.LocalTheory.ElementaryQuotient
      V.toSubgroup (ell : ℕ)) :
      E0 (NU.LocalTheory.barePacketAction V ell
        (QuotientGroup.mk g₂) q) =
      NU.LocalTheory.orientedPacketAction o L ell gamma (E0 q) := by
    dsimp only [E0, gamma, eQ0]
    obtain ⟨u, rfl⟩ :=
      PacketTransport.elementaryClass_surjective (ell : ℕ) q
    simp only [NU.LocalTheory.barePacketAction_elementaryClass,
      NU.LocalTheory.orientedPacketAction_elementaryClass,
      NU.LocalTheory.elementaryQuotientTransport_elementaryClass,
      QuotientGroup.quotientMulEquivOfEq_mk]
    congr 1
  have haction (q : NU.LocalTheory.ElementaryQuotient
      V.toSubgroup (ell : ℕ)) :
      E (NU.LocalTheory.barePacketAction V ell
        (QuotientGroup.mk g₂) q) =
      NU.LocalTheory.packetAction K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma (E q) := by
    calc
      E (NU.LocalTheory.barePacketAction V ell
          (QuotientGroup.mk g₂) q) =
          EC (E0 (NU.LocalTheory.barePacketAction V ell
            (QuotientGroup.mk g₂) q)) := rfl
      _ = EC (NU.LocalTheory.orientedPacketAction o L ell gamma (E0 q)) := by
        rw [haction0]
      _ = NU.LocalTheory.packetAction K₂
          (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma
            (EC (E0 q)) := hactionC gamma (E0 q)
      _ = _ := rfl
  let P0 := P.map E0.toLinearMap
  let PC := P0.map EC.toLinearMap
  have hP0 : NU.LocalTheory.IsPacket (ell : ℕ) P0 :=
    PacketTransport.packet_transport (ell : ℕ) e0 P hP
  have hPC : NU.LocalTheory.IsPacket (ell : ℕ) PC :=
    (hpacket P0).2 hP0
  have hPCeq : PC = P.map E.toLinearMap := by
    dsimp [PC, P0, E]
    rw [← Submodule.map_comp]
    rfl
  have hstableC :
      PC.map (NU.LocalTheory.packetAction K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma).toLinearMap =
        PC := by
    rw [hPCeq]
    calc
      (P.map E.toLinearMap).map
          (NU.LocalTheory.packetAction K₂
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap =
          P.map ((NU.LocalTheory.packetAction K₂
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap.comp E.toLinearMap) :=
        (Submodule.map_comp _ _ _).symm
      _ = P.map (E.toLinearMap.comp
          (NU.LocalTheory.barePacketAction V ell
            (QuotientGroup.mk g₂)).toLinearMap) := by
        congr 1
        ext q
        exact (haction q).symm
      _ = (P.map (NU.LocalTheory.barePacketAction V ell
          (QuotientGroup.mk g₂)).toLinearMap).map E.toLinearMap :=
        Submodule.map_comp _ _ _
      _ = P.map E.toLinearMap := by rw [hstableBare]
  have hxyC0 := planeBasis_map_linearEquiv E P hxy
  have hxyC : NU.LocalTheory.IsPlaneBasis PC (E x) (E y) := by
    rw [hPCeq]
    exact hxyC0
  have hxC : NU.LocalTheory.packetAction K₂
      (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma (E x) =
      a • E x + c • E y := by
    calc
      _ = E (NU.LocalTheory.barePacketAction V ell
          (QuotientGroup.mk g₂) x) := (haction x).symm
      _ = E (a • x + c • y) := by rw [hx]
      _ = _ := by simp [E]
  have hyC : NU.LocalTheory.packetAction K₂
      (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma (E y) =
      b • E x + r • E y := by
    calc
      _ = E (NU.LocalTheory.barePacketAction V ell
          (QuotientGroup.mk g₂) y) := (haction y).symm
      _ = E (b • x + r • y) := by rw [hy]
      _ = _ := by simp [E]
  have hdetTransport : IsPlaneActionDeterminant
      (NU.LocalTheory.packetAction K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma) PC d :=
    ⟨E x, E y, hxyC, a, b, c, r, hxC, hyC, hd⟩
  let zetaAbs := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K₂) (ell : ℕ)).choose
  have hzetaAbs : IsPrimitiveRoot zetaAbs (ell : ℕ) :=
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure K₂) (ell : ℕ)).choose_spec
  have hzetaMem : zetaAbs ∈ L.field := by
    change zetaAbs ∈ IntermediateField.fixedField V.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro u hu
    exact hV hu zetaAbs hzetaAbs.pow_eq_one
  let zetaL : L.field := ⟨zetaAbs, hzetaMem⟩
  let zeta : CyclotomicField (ell : ℕ) L.field :=
    algebraMap L.field (CyclotomicField (ell : ℕ) L.field) zetaL
  have hzetaL : IsPrimitiveRoot zetaL (ell : ℕ) := by
    apply IsPrimitiveRoot.of_map_of_injective
      (f := L.field.val.toMonoidHom) (hf := L.field.val.injective)
    simpa [zetaL] using hzetaAbs
  have hzeta : IsPrimitiveRoot zeta (ell : ℕ) :=
    hzetaL.map_of_injective
      (algebraMap L.field
        (CyclotomicField (ell : ℕ) L.field)).injective
  have hpMem : PC ∈
      {Q : NU.LocalTheory.GroupSubspace
          (Field.absoluteGaloisGroup
            (CyclotomicField (ell : ℕ) L.field)) (ell : ℕ) |
        NU.LocalTheory.IsPacket (ell : ℕ) Q} := hPC
  rw [NU.LocalTheory.packet_theorem ell.2 zeta hzeta] at hpMem
  obtain ⟨w, hw, hPCw⟩ := hpMem
  have hstableW :
      (NU.LocalTheory.groupLocalPlane zeta hzeta w).map
          (NU.LocalTheory.packetAction K₂
            (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
              sigma).toLinearMap =
        NU.LocalTheory.groupLocalPlane zeta hzeta w := by
    rw [← hPCw]
    exact hstableC
  have hdetLocal := packetAction_localPlane_determinant K₂
    (CyclotomicField (ell : ℕ) L.field) zeta hzeta w hw sigma hstableW
  have hdetLocalPC : IsPlaneActionDeterminant
      (NU.LocalTheory.packetAction K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma) PC
      ((NU.LocalTheory.packetCyclotomicCharacter K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
          zeta hzeta sigma : (ZMod (ell : ℕ))ˣ) : ZMod (ell : ℕ)) := by
    rw [hPCw]
    exact hdetLocal
  have hdetEq := planeActionDeterminant_unique
    (NU.LocalTheory.packetAction K₂
      (CyclotomicField (ell : ℕ) L.field) (ell : ℕ) sigma)
    PC hstableC hdetTransport hdetLocalPC
  have hresSigma :
      NU.LocalTheory.galoisRestriction K₂ L.field
        (CyclotomicField (ell : ℕ) L.field) sigma =
      NU.LocalTheory.absoluteRestriction L g₂ := by
    simpa [sigma, gamma, eQ0] using hrestrict g₂
  have habsSpec :
      (show AlgebraicClosure K₂ ≃ₐ[K₂] AlgebraicClosure K₂ from g₂)
          zetaAbs =
        zetaAbs ^ (absoluteCyclotomicScalar K₂ ell g₂).val := by
    exact (hzetaAbs.autToPow_spec K₂ g₂).symm
  have hrestrictZeta :
      NU.LocalTheory.absoluteRestriction L g₂ zetaL =
        zetaL ^ (absoluteCyclotomicScalar K₂ ell g₂).val := by
    apply Subtype.ext
    rw [NU.LocalTheory.absoluteRestriction_apply]
    exact habsSpec
  have hsigmaZeta : sigma zeta =
      zeta ^ (absoluteCyclotomicScalar K₂ ell g₂).val := by
    calc
      sigma zeta = algebraMap L.field
          (CyclotomicField (ell : ℕ) L.field)
          (NU.LocalTheory.galoisRestriction K₂ L.field
            (CyclotomicField (ell : ℕ) L.field) sigma zetaL) := by
              symm
              exact NU.LocalTheory.galoisRestriction_apply K₂ L.field
                (CyclotomicField (ell : ℕ) L.field) sigma zetaL
      _ = algebraMap L.field (CyclotomicField (ell : ℕ) L.field)
          (NU.LocalTheory.absoluteRestriction L g₂ zetaL) := by
            rw [hresSigma]
      _ = algebraMap L.field (CyclotomicField (ell : ℕ) L.field)
          (zetaL ^ (absoluteCyclotomicScalar K₂ ell g₂).val) := by
            rw [hrestrictZeta]
      _ = zeta ^ (absoluteCyclotomicScalar K₂ ell g₂).val := by
            rw [map_pow]
  have hscalar :
      ((NU.LocalTheory.packetCyclotomicCharacter K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
          zeta hzeta sigma : (ZMod (ell : ℕ))ˣ) : ZMod (ell : ℕ)) =
        absoluteCyclotomicScalar K₂ ell g₂ := by
    apply ZMod.val_injective
    apply hzeta.pow_inj
    · exact ZMod.val_lt _
    · exact ZMod.val_lt _
    · exact (NU.LocalTheory.packetCyclotomicCharacter_spec K₂
        (CyclotomicField (ell : ℕ) L.field) (ell : ℕ)
          zeta hzeta sigma).symm.trans hsigmaZeta
  exact hdetEq.trans (by simpa [g₂] using hscalar)

/-- Blueprint `cor:chi`: pointwise mod-`ell` cyclotomic-character
preservation on a recovered decomposition group.  Only one simultaneous
marked level is used for each `ell`. -/
private theorem pointwiseCyclotomic_preserved
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂)
    (hmap : Subgroup.map alpha.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1)
    (g : Field.absoluteGaloisGroup K₁)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1)
    (ell : NU.LocalTheory.OddPrime)
    (haway : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace P₁) ≠ (ell : ℕ)) :
    absoluteCyclotomicScalar K₂ ell (alpha g) =
      absoluteCyclotomicScalar K₁ ell g := by
  obtain ⟨U, hmarked, _⟩ :=
    (thetaMarkedLevels_cofinal K₁ K₂ alpha ell).2.2
      (⊤ : Subgroup (Field.absoluteGaloisGroup K₁)) isOpen_univ
  have hsource := source_packetDeterminant_at_markedLevel
    alpha P₁ P₂ hmap g hg ell haway U hmarked
  have htarget := packetDeterminant_transport_at_markedLevel
    alpha ell U g (absoluteCyclotomicScalar K₁ ell g) hsource
  have hdet := target_packetDeterminant_identifies_cyclotomic
    alpha ell U g (absoluteCyclotomicScalar K₁ ell g)
      hmarked htarget
  exact hdet.symm

/-! ### T5 and Kummer dimensions (`lem:units`, `lem:dim-at`, `prop:p-n`) -/

/-- A finite Galois level containing one prescribed algebraic element. -/
private noncomputable def galoisLevelOfElement
    {K : Type*} [Field K] [NumberField K]
    (x : AlgebraicClosure K) : NU.LocalTheory.GaloisLevel K := by
  let A : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {x}
  letI : FiniteDimensional K A :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x)
  let Nfield : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.normalClosure K A (AlgebraicClosure K)
  exact
    { field := Nfield
      finiteDimensional := normalClosure.is_finiteDimensional K A
        (AlgebraicClosure K)
      numberField := NumberField.of_module_finite K _
      isGalois := IsGalois.normalClosure K A (AlgebraicClosure K) }

private theorem mem_galoisLevelOfElement
    {K : Type*} [Field K] [NumberField K]
    (x : AlgebraicClosure K) : x ∈ (galoisLevelOfElement x).field := by
  apply IntermediateField.le_normalClosure
  exact IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)

/-- Enlarge a finite Galois level so that it also contains one prescribed
root of unity. -/
private noncomputable def galoisLevelJoinElement
    {K : Type*} [Field K] [NumberField K]
    (L : NU.LocalTheory.GaloisLevel K) (zeta : AlgebraicClosure K) :
    NU.LocalTheory.GaloisLevel K := by
  let Z : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.adjoin K {zeta}
  letI : FiniteDimensional K Z :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral zeta)
  let A : IntermediateField K (AlgebraicClosure K) := L.field ⊔ Z
  letI : FiniteDimensional K A := by infer_instance
  let Nfield : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.normalClosure K A (AlgebraicClosure K)
  exact
    { field := Nfield
      finiteDimensional := normalClosure.is_finiteDimensional K A
        (AlgebraicClosure K)
      numberField := NumberField.of_module_finite K _
      isGalois := IsGalois.normalClosure K A (AlgebraicClosure K) }

private theorem le_galoisLevelJoinElement
    {K : Type*} [Field K] [NumberField K]
    (L : NU.LocalTheory.GaloisLevel K) (zeta : AlgebraicClosure K) :
    L.LE (galoisLevelJoinElement L zeta) :=
  le_trans le_sup_left (IntermediateField.le_normalClosure _)

private theorem mem_galoisLevelJoinElement
    {K : Type*} [Field K] [NumberField K]
    (L : NU.LocalTheory.GaloisLevel K) (zeta : AlgebraicClosure K) :
    zeta ∈ (galoisLevelJoinElement L zeta).field := by
  change zeta ∈ IntermediateField.normalClosure K
    ↥(L.field ⊔ IntermediateField.adjoin K {zeta}) (AlgebraicClosure K)
  apply IntermediateField.le_normalClosure
  apply (show IntermediateField.adjoin K {zeta} ≤
    L.field ⊔ IntermediateField.adjoin K {zeta} from le_sup_right)
  exact IntermediateField.subset_adjoin K {zeta} (Set.mem_singleton zeta)

/-- Restricting an element of an absolute decomposition group to any
finite Galois level stabilizes the finite place cut out by the absolute
valuation. -/
private theorem absoluteRestriction_stabilizes_place
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.conjugateFinitePlace K
        (NU.LocalTheory.absoluteRestriction L g)
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) =
      NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L := by
  have hsigma : NU.LocalTheory.absoluteRestriction L g ∈
      NU.LocalTheory.finiteLevelImage L
        (NU.LocalTheory.absoluteDecompositionGroup K P.1) :=
    ⟨g, hg, rfl⟩
  rw [NU.LocalTheory.absoluteDecompositionGroup_finiteImage
    P.1 P.2 L] at hsigma
  exact hsigma

/-- Restriction to the identity Galois level is trivial. -/
private theorem absoluteRestriction_trivialGaloisLevel
    {K : Type*} [Field K] [NumberField K]
    (g : Field.absoluteGaloisGroup K) :
    NU.LocalTheory.absoluteRestriction
        (NU.LocalTheory.trivialGaloisLevel K) g = 1 := by
  ext x
  rw [NU.LocalTheory.absoluteRestriction_apply]
  change (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
      (x : AlgebraicClosure K) = (x : AlgebraicClosure K)
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp x.property
  rw [← ha]
  exact (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g).commutes a

/-- The standard T5 comparison between the local completion's absolute
Galois group and the recovered absolute decomposition group. -/
private structure DecompositionCompletionBridge
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) where
  comparison :
    Field.absoluteGaloisGroup
        ((ambientFinitePlace P).adicCompletion K) ≃ₜ*
      NU.LocalTheory.absoluteDecompositionGroup K P.1

/-- Package a pinned completion/decomposition-group comparison as the bridge
used by the local-invariant recovery argument. -/
private theorem decompositionCompletionBridge_of_comparison
    {K : Type*} [Field K] [NumberField K]
    {P : NU.LocalTheory.AbsoluteFinitePlaceOf K}
    (comparison :
      Field.absoluteGaloisGroup
          ((ambientFinitePlace P).adicCompletion K) ≃ₜ*
        NU.LocalTheory.absoluteDecompositionGroup K P.1) :
    Nonempty (DecompositionCompletionBridge K P) :=
  ⟨⟨comparison⟩⟩

/-- Compare the chosen algebraic closure of an intermediate field with the
ambient algebraic closure of its base. -/
private noncomputable def intermediateFieldClosureEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    AlgebraicClosure E ≃ₐ[E] AlgebraicClosure F := by
  letI : IsAlgClosure E (AlgebraicClosure F) :=
    ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equiv E (AlgebraicClosure E) (AlgebraicClosure F)

/-- Algebraically, the absolute Galois group of an intermediate field is its
fixing subgroup in the absolute Galois group of the base. -/
private noncomputable def intermediateFieldGaloisMulEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E ≃* E.fixingSubgroup := by
  let e := intermediateFieldClosureEquiv F E
  let toFun : Field.absoluteGaloisGroup E → E.fixingSubgroup := fun sigma =>
    let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
    ⟨((e.symm.trans sigma').trans e).restrictScalars F, by
      apply (IntermediateField.mem_fixingSubgroup_iff E _).2
      intro x hx
      change e (sigma' (e.symm x)) = x
      have hxe : e.symm x =
          algebraMap E (AlgebraicClosure E) ⟨x, hx⟩ := by
        apply e.injective
        simp
      rw [hxe, sigma'.commutes]
      simp⟩
  let invFun : E.fixingSubgroup → Field.absoluteGaloisGroup E := fun tau =>
    let tauE : AlgebraicClosure F ≃ₐ[E] AlgebraicClosure F :=
      { tau.1 with
        commutes' := fun x => by
          exact (IntermediateField.mem_fixingSubgroup_iff E tau.1).1
            tau.2 x x.2 }
    (e.trans tauE).trans e.symm
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro sigma
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      right_inv := by
        intro tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, invFun, e]
      map_mul' := by
        intro sigma tau
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        simp [toFun, e]
        rfl }

/-- Restriction from the absolute Galois group of an intermediate field into
the absolute Galois group of its base. -/
private noncomputable def intermediateFieldRestrictionHom
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E →* Field.absoluteGaloisGroup F :=
  E.fixingSubgroup.subtype.comp
    (intermediateFieldGaloisMulEquiv F E).toMonoidHom

private theorem intermediateFieldRestrictionHom_apply
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F))
    (sigma : Field.absoluteGaloisGroup E) (x : AlgebraicClosure F) :
    (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
      intermediateFieldRestrictionHom F E sigma) x =
      intermediateFieldClosureEquiv F E
        ((show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma)
          ((intermediateFieldClosureEquiv F E).symm x)) := by
  rfl

/-- Restriction along the chosen closure comparison is continuous in the two
Krull topologies, without a finiteness assumption on the intermediate
field. -/
private theorem intermediateFieldRestrictionHom_continuous
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Continuous (intermediateFieldRestrictionHom F E) := by
  let r : (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →*
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
    intermediateFieldRestrictionHom F E
  change @Continuous
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (krullTopology E (AlgebraicClosure E))
    (krullTopology F (AlgebraicClosure F)) r
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr ?_)
  intro N hN
  rw [r.map_one] at hN
  have hN' : N ∈ nhds
      (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) := hN
  rw [krullTopology_mem_nhds_one_iff] at hN'
  obtain ⟨L, hLfin, hLN⟩ := hN'
  letI : FiniteDimensional F L := hLfin
  let e := intermediateFieldClosureEquiv F E
  let b := Module.Free.chooseBasis F L
  letI : Fintype (Module.Free.ChooseBasisIndex F L) := Fintype.ofFinite _
  let S : Set (AlgebraicClosure E) := Set.range
    (fun i : Module.Free.ChooseBasisIndex F L =>
      e.symm (((b i : L) : AlgebraicClosure F)))
  letI : Fintype S := (Set.finite_range _).fintype
  let L' : IntermediateField E (AlgebraicClosure E) :=
    IntermediateField.adjoin E S
  haveI : FiniteDimensional E L' := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x _
    exact Algebra.IsIntegral.isIntegral x
  apply mem_nhds_iff.mpr
  refine ⟨L'.fixingSubgroup, ?_,
    ⟨IntermediateField.fixingSubgroup_isOpen L',
      L'.fixingSubgroup.one_mem⟩⟩
  intro sigma hsigma
  apply hLN
  apply (IntermediateField.mem_fixingSubgroup_iff L _).2
  intro x hx
  have hsigma' :=
    (IntermediateField.mem_fixingSubgroup_iff L' sigma).1 hsigma
  change (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
    intermediateFieldRestrictionHom F E sigma) x = x
  rw [intermediateFieldRestrictionHom_apply]
  let sigma' := show AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E from sigma
  let incl : L →ₐ[F] AlgebraicClosure F := L.val
  let pull : AlgebraicClosure F →ₐ[F] AlgebraicClosure E :=
    e.symm.restrictScalars F
  let f : L →ₗ[F] AlgebraicClosure E :=
    pull.toLinearMap.comp incl.toLinearMap
  let sigmaF : AlgebraicClosure E →ₐ[F] AlgebraicClosure E :=
    sigma'.restrictScalars F
  have heq : sigmaF.toLinearMap.comp f = f := by
    apply b.ext
    intro i
    change sigma' (e.symm (((b i : L) : AlgebraicClosure F))) =
      e.symm (((b i : L) : AlgebraicClosure F))
    apply hsigma'
    apply IntermediateField.subset_adjoin
    exact ⟨i, rfl⟩
  have hxfix := DFunLike.congr_fun heq (⟨x, hx⟩ : L)
  change sigma' (e.symm x) = e.symm x at hxfix
  rw [hxfix]
  exact e.apply_symm_apply x

/-- Topological fixed-field comparison for an arbitrary intermediate field.
Compactness of the source upgrades the continuous algebraic equivalence to a
homeomorphism. -/
private noncomputable def intermediateFieldGaloisContinuousMulEquiv
    (F : Type*) [Field F]
    (E : IntermediateField F (AlgebraicClosure F)) :
    Field.absoluteGaloisGroup E ≃ₜ* E.fixingSubgroup := by
  let e := intermediateFieldGaloisMulEquiv F E
  have he : Continuous e := by
    exact Continuous.subtype_mk
      (intermediateFieldRestrictionHom_continuous F E) _
  letI : CompactSpace (Field.absoluteGaloisGroup E) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  let h := he.homeoOfEquivCompactToT2
  exact ContinuousMulEquiv.mk' h (by
    intro x y
    change e (x * y) = e x * e y
    exact e.map_mul x y)

/-- The absolute Galois group of the decomposition field is the recovered
absolute decomposition subgroup, with its induced Krull topology. -/
private noncomputable def decompositionFieldGaloisEquiv
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    Field.absoluteGaloisGroup
        (NU.LocalTheory.decompositionField K P.1) ≃ₜ*
      NU.LocalTheory.absoluteDecompositionGroup K P.1 := by
  let e := intermediateFieldGaloisContinuousMulEquiv K
    (NU.LocalTheory.decompositionField K P.1)
  rw [NU.LocalTheory.decompositionField_fixingSubgroup K P.1] at e
  exact e

/-- The two proved BareRecovery inputs for T5: the fixed decomposition field
has exactly the decomposition group as fixing subgroup and its restricted
valuation is Henselian. -/
private theorem henselianDecompositionField_facts
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    (NU.LocalTheory.decompositionField K P.1).fixingSubgroup =
        NU.LocalTheory.absoluteDecompositionGroup K P.1 ∧
      NU.LocalTheory.IsHenselianValuationIn
        (NU.LocalTheory.decompositionField K P.1) (AlgebraicClosure K)
        (P.1.comap
          (NU.LocalTheory.decompositionField K P.1).val.toRingHom) := by
  exact ⟨NU.LocalTheory.decompositionField_fixingSubgroup K P.1,
    NU.LocalTheory.decompositionField_isHenselian K P.1 P.2⟩

/-- The remaining standard completion theorem: finite separable extensions
of the rank-one Henselian decomposition field and of its completion are
equivalent, hence their absolute Galois groups are topologically isomorphic. -/
private theorem henselianCompletion_absoluteGaloisEquiv
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (hhens : NU.LocalTheory.IsHenselianValuationIn
      (NU.LocalTheory.decompositionField K P.1) (AlgebraicClosure K)
      (P.1.comap
        (NU.LocalTheory.decompositionField K P.1).val.toRingHom))
    (hrank : NU.LocalTheory.IsRankOneValuationSubring
      (P.1.comap
        (NU.LocalTheory.decompositionField K P.1).val.toRingHom)) :
    Nonempty
      (Field.absoluteGaloisGroup
          ((ambientFinitePlace P).adicCompletion K) ≃ₜ*
        Field.absoluteGaloisGroup
          (NU.LocalTheory.decompositionField K P.1)) := by
  exact NU.NeukirchUchida.Bridges.henselianCompletion_absoluteGaloisEquiv
    K P (ambientFinitePlace P)
      (primeValuationSubring_ambientFinitePlace P) hhens hrank

/-- Resistant standard branch of T5: promote equivalence of finite
extensions of a rank-one Henselian field and its completion to the pinned
topological isomorphism of absolute Galois groups. -/
private theorem henselianCompletion_finiteExtensionEquivalence
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (hfacts :
      (NU.LocalTheory.decompositionField K P.1).fixingSubgroup =
          NU.LocalTheory.absoluteDecompositionGroup K P.1 ∧
        NU.LocalTheory.IsHenselianValuationIn
          (NU.LocalTheory.decompositionField K P.1) (AlgebraicClosure K)
          (P.1.comap
            (NU.LocalTheory.decompositionField K P.1).val.toRingHom)) :
    Nonempty (DecompositionCompletionBridge K P) := by
  obtain ⟨completionEquiv⟩ :=
    henselianCompletion_absoluteGaloisEquiv K P hfacts.2
      (NU.LocalTheory.decompositionField_place_rankOne K P.1 P.2)
  exact decompositionCompletionBridge_of_comparison
    (completionEquiv.trans (decompositionFieldGaloisEquiv K P))

/-- **Standard completion obligation, Blueprint T5.**  A Henselian
rank-one decomposition field has the same finite extensions as the completion,
compatibly with the chosen prolongation.  This is the only missing standard
step between BareRecovery's Henselian layer and the explicit T5 comparison. -/
private theorem henselianCompletion_comparison
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (hfacts :
      (NU.LocalTheory.decompositionField K P.1).fixingSubgroup =
          NU.LocalTheory.absoluteDecompositionGroup K P.1 ∧
        NU.LocalTheory.IsHenselianValuationIn
          (NU.LocalTheory.decompositionField K P.1) (AlgebraicClosure K)
          (P.1.comap
            (NU.LocalTheory.decompositionField K P.1).val.toRingHom)) :
    Nonempty (DecompositionCompletionBridge K P) := by
  exact henselianCompletion_finiteExtensionEquivalence K P hfacts

/-- Blueprint T5 derived from the proved decomposition-field/Henselian layer
of `BareRecovery.lean` and the isolated standard completion comparison. -/
private theorem decompositionCompletionBridge
    (K : Type*) [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    Nonempty (DecompositionCompletionBridge K P) := by
  exact henselianCompletion_comparison K P
    (henselianDecompositionField_facts K P)

/-- A prime subtype supplies the `Fact` instance required by `ZMod` and
`PadicInt` constructions used below. -/
private instance natPrimesFact (p : Nat.Primes) : Fact (p : ℕ).Prime :=
  ⟨p.2⟩

/-- The residue field of a number-field completion is finite.  Density of
the number field identifies every residue class with one from the localized
valuation ring. -/
private theorem completionResidueFinite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  let F := v.adicCompletion K
  let A := NU.LocalTheory.primeValuationSubring v
  let B := v.adicCompletionIntegers K
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Algebra (𝓞 K) A :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let eA := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A
  letI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_equiv ((𝓞 K) ⧸ v.asIdeal) eA.toEquiv
  let emb : K →+* F := algebraMap K F
  have hemb_mem (a : A) : emb (a : K) ∈ B := by
    rw [show B = v.adicCompletionIntegers K from rfl,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((a : K) : F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have ha : (a : K) ∈ (v.valuation K).valuationSubring := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact a.property
    exact ha
  let f : A →+* B := RingHom.codRestrict
    (emb.comp A.subtype) B hemb_mem
  have hfmax : IsLocalRing.maximalIdeal A ≤
      Ideal.comap f (IsLocalRing.maximalIdeal B) := by
    intro a ha
    rw [Ideal.mem_comap, B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v ((f a : B) : F) < Valued.v (1 : F)
    rw [map_one]
    have ha' : v.valuation K (a : K) < 1 := by
      have hA : A = (v.valuation K).valuationSubring :=
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
      let ea : A ≃+* (v.valuation K).valuationSubring :=
        RingEquiv.subringCongr
          (congrArg (fun W : ValuationSubring K => W.toSubring) hA)
      have hea : ea a ∈ IsLocalRing.maximalIdeal
          ((v.valuation K).valuationSubring) := by
        change a ∈ IsLocalRing.maximalIdeal A at ha
        simpa [ea] using ha
      exact (Valuation.mem_maximalIdeal_iff K
        (v := v.valuation K)).mp hea
    change Valued.v ((a : K) : F) < 1
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  letI : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 3 0).mp hfmax
  let rf : IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField B := IsLocalRing.ResidueField.map f
  have hrf : Function.Surjective rf := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    have hopen : Metric.ball (b : F) 1 ∈ nhds (b : F) :=
      Metric.ball_mem_nhds _ zero_lt_one
    obtain ⟨x, hx⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).mem_nhds
        hopen
    have hxclose : ‖algebraMap K F x - (b : F)‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hvclose : Valued.v (algebraMap K F x - (b : F)) < 1 :=
      Valued.toNormedField.norm_lt_one_iff.mp hxclose
    have hxcoe : (x : F) = algebraMap K F x := rfl
    have hvclose' : Valued.v ((x : F) - (b : F)) < 1 := by
      rw [hxcoe]
      exact hvclose
    have hxint : v.valuation K x ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      rw [show (x : F) = ((x : F) - (b : F)) + (b : F) by ring]
      exact Valuation.map_add_le _ hvclose'.le b.property
    let a : A := ⟨x, by
      rw [show A = (v.valuation K).valuationSubring from
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v]
      exact hxint⟩
    refine ⟨IsLocalRing.residue A a, ?_⟩
    rw [show rf = IsLocalRing.ResidueField.map f from rfl,
      IsLocalRing.ResidueField.map_residue]
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
      B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v (((f a : B) - b : B) : F) < Valued.v (1 : F)
    rw [map_one]
    change Valued.v ((x : F) - (b : F)) < 1
    exact hvclose'
  exact Finite.of_surjective rf hrf

/-- The canonical valuation relation on a number-field completion. -/
@[reducible] private noncomputable def completionValuativeRel
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion K) _)

/-- A number-field completion, with its canonical valuation relation, is a
nonarchimedean local field. -/
private theorem completionIsLocalField
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : IsDiscreteValuationRing (Valued.integer F) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : Finite (Valued.ResidueField F) := completionResidueFinite v
  letI : ProperSpace F :=
    (@Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      F _ _ _ _).2 ⟨inferInstance, inferInstance, inferInstance⟩
  letI : LocallyCompactSpace F := by infer_instance
  let vF := (Valued.v : Valuation F _)
  letI : vF.Compatible := Valuation.Compatible.ofValuation vF
  letI : IsValuativeTopology F :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle vF (by
      intro s
      exact Valued.is_topological_valuation s)
  letI : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vF).2 inferInstance
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

private theorem ringChar_eq_of_fieldHom
    {k : Type u} {l : Type v} [Field k] [Field l] (f : k →+* l) :
    ringChar k = ringChar l := by
  apply Nat.dvd_antisymm
  · apply ringChar.dvd
    apply f.injective
    simpa only [map_natCast, map_zero] using
      (CharP.cast_eq_zero l (ringChar l))
  · apply ringChar.dvd
    rw [← map_natCast f, CharP.cast_eq_zero k (ringChar k), map_zero]

/-- The canonical valuation relation on a completion has the arithmetic
residue characteristic of the underlying finite place. -/
private theorem completion_residueCharacteristic_eq
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    letI : ValuativeRel (v.adicCompletion K) := completionValuativeRel v
    ringChar (NU.LCFT.LocalResidueField (v.adicCompletion K)) =
      NU.LocalTheory.residueCharacteristic v := by
  let F := v.adicCompletion K
  letI : ValuativeRel F := completionValuativeRel v
  letI : (Valued.v : Valuation F _).Compatible :=
    Valuation.Compatible.ofValuation _
  have hring : NU.LCFT.RingOfIntegers F =
      (v.adicCompletionIntegers K).toSubring := by
    exact congrArg ValuationSubring.toSubring
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp
        (ValuativeRel.isEquiv (ValuativeRel.valuation F)
          (Valued.v : Valuation F _)))
  let er : NU.LCFT.RingOfIntegers F ≃+*
      v.adicCompletionIntegers K := RingEquiv.subringCongr hring
  letI : IsLocalHom er.toRingHom :=
    IsLocalHom.of_surjective er.toRingHom er.surjective
  let r1 : NU.LCFT.LocalResidueField F →+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    IsLocalRing.ResidueField.map er.toRingHom
  let A := NU.LocalTheory.primeValuationSubring v
  let B := v.adicCompletionIntegers K
  letI : Algebra (𝓞 K) A :=
    show Algebra (𝓞 K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) from
        inferInstance
  letI : IsLocalization.AtPrime A v.asIdeal :=
    show IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)
        v.asIdeal from inferInstance
  let emb : K →+* F := algebraMap K F
  have hemb_mem (a : A) : emb (a : K) ∈ B := by
    rw [show B = v.adicCompletionIntegers K from rfl,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((a : K) : F) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have ha : (a : K) ∈ (v.valuation K).valuationSubring := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact a.property
    exact ha
  let f : A →+* B := RingHom.codRestrict
    (emb.comp A.subtype) B hemb_mem
  have hfmax : IsLocalRing.maximalIdeal A ≤
      Ideal.comap f (IsLocalRing.maximalIdeal B) := by
    intro a ha
    rw [Ideal.mem_comap, B.valuation_lt_one_iff]
    apply (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation F _)).lt_iff_lt.mp
    change Valued.v ((f a : B) : F) < Valued.v (1 : F)
    rw [map_one]
    have ha' : v.valuation K (a : K) < 1 := by
      have hA : A = (v.valuation K).valuationSubring :=
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v
      let ea : A ≃+* (v.valuation K).valuationSubring :=
        RingEquiv.subringCongr
          (congrArg (fun W : ValuationSubring K => W.toSubring) hA)
      have hea : ea a ∈ IsLocalRing.maximalIdeal
          ((v.valuation K).valuationSubring) := by
        change a ∈ IsLocalRing.maximalIdeal A at ha
        simpa [ea] using ha
      exact (Valuation.mem_maximalIdeal_iff K
        (v := v.valuation K)).mp hea
    change Valued.v ((a : K) : F) < 1
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  letI : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 3 0).mp hfmax
  let r2 : IsLocalRing.ResidueField A →+*
      IsLocalRing.ResidueField B := IsLocalRing.ResidueField.map f
  have hr1 : ringChar (NU.LCFT.LocalResidueField F) =
      ringChar (IsLocalRing.ResidueField B) :=
    ringChar_eq_of_fieldHom r1
  have hr2 : ringChar (IsLocalRing.ResidueField A) =
      ringChar (IsLocalRing.ResidueField B) :=
    ringChar_eq_of_fieldHom r2
  calc
    ringChar (NU.LCFT.LocalResidueField F) =
        ringChar (IsLocalRing.ResidueField B) := hr1
    _ = ringChar (IsLocalRing.ResidueField A) := hr2.symm
    _ = NU.LocalTheory.residueCharacteristic v := rfl

/-- A chosen primitive root in the algebraic closure of a
characteristic-zero field. -/
private noncomputable def localCyclotomicRoot
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    AlgebraicClosure F :=
  Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure F) (ell : ℕ))

private theorem localCyclotomicRoot_spec
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    IsPrimitiveRoot (localCyclotomicRoot F ell) (ell : ℕ) :=
  Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure F) (ell : ℕ))

/-- The finite extension obtained by adjoining `mu_ell`. -/
private noncomputable def localCyclotomicExtension
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F {localCyclotomicRoot F ell}

private instance localCyclotomicExtension_finite
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    FiniteDimensional F (localCyclotomicExtension F ell) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact Algebra.IsIntegral.isIntegral x

private instance localCyclotomicExtension_isCyclotomic
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    IsCyclotomicExtension {(ell : ℕ)} F
      (localCyclotomicExtension F ell) := by
  exact (localCyclotomicRoot_spec F ell)
    |>.intermediateField_adjoin_isCyclotomicExtension F

private instance localCyclotomicExtension_isGalois
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    IsGalois F (localCyclotomicExtension F ell) :=
  IsCyclotomicExtension.isGalois {(ell : ℕ)} F _

private def localCyclotomicRootInExtension
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    localCyclotomicExtension F ell :=
  ⟨localCyclotomicRoot F ell,
    IntermediateField.subset_adjoin F {localCyclotomicRoot F ell}
      (Set.mem_singleton _)⟩

private theorem localCyclotomicRootInExtension_spec
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    IsPrimitiveRoot (localCyclotomicRootInExtension F ell)
      (ell : ℕ) := by
  apply IsPrimitiveRoot.of_map_of_injective
    (f := (localCyclotomicExtension F ell).val)
  · exact localCyclotomicRoot_spec F ell
  · exact (localCyclotomicExtension F ell).val.injective

/-- Adjoining a primitive `ell`-th root has degree strictly below `ell`. -/
private theorem localCyclotomicExtension_finrank_lt
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    Module.finrank F (localCyclotomicExtension F ell) < (ell : ℕ) := by
  rw [show localCyclotomicExtension F ell =
      IntermediateField.adjoin F {localCyclotomicRoot F ell} from rfl,
    IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral (localCyclotomicRoot F ell))]
  have hdvd : minpoly F (localCyclotomicRoot F ell) ∣
      Polynomial.cyclotomic (ell : ℕ) F := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      Polynomial.map_cyclotomic]
    exact (localCyclotomicRoot_spec F ell).isRoot_cyclotomic ell.2.pos
  calc
    (minpoly F (localCyclotomicRoot F ell)).natDegree ≤
        (Polynomial.cyclotomic (ell : ℕ) F).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd
        (Polynomial.cyclotomic_ne_zero (ell : ℕ) F)
    _ = (ell : ℕ).totient := Polynomial.natDegree_cyclotomic _ _
    _ = (ell : ℕ) - 1 := Nat.totient_prime ell.2
    _ < (ell : ℕ) := Nat.sub_one_lt ell.2.ne_zero

/-- Comparison of the chosen algebraic closure of the cyclotomic extension
with the ambient algebraic closure of the base. -/
private noncomputable def localCyclotomicClosureEquiv
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    AlgebraicClosure (localCyclotomicExtension F ell) ≃ₐ[
      localCyclotomicExtension F ell] AlgebraicClosure F :=
  intermediateFieldClosureEquiv F (localCyclotomicExtension F ell)

/-- Algebraically, the absolute Galois group after adjoining `mu_ell` is the
fixing subgroup of the cyclotomic field in the base absolute Galois group. -/
private noncomputable def localCyclotomicGaloisMulEquiv
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F ell) ≃*
      (localCyclotomicExtension F ell).fixingSubgroup :=
  intermediateFieldGaloisMulEquiv F (localCyclotomicExtension F ell)

/-- Restriction from the absolute Galois group of the cyclotomic extension
into the base absolute Galois group. -/
private noncomputable def localCyclotomicRestrictionHom
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F ell) →*
      Field.absoluteGaloisGroup F :=
  intermediateFieldRestrictionHom F (localCyclotomicExtension F ell)

private theorem localCyclotomicRestrictionHom_apply
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes)
    (sigma : Field.absoluteGaloisGroup
      (localCyclotomicExtension F ell))
    (x : AlgebraicClosure F) :
    (show AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F from
      localCyclotomicRestrictionHom F ell sigma) x =
      localCyclotomicClosureEquiv F ell
        ((show AlgebraicClosure (localCyclotomicExtension F ell) ≃ₐ[
            localCyclotomicExtension F ell]
              AlgebraicClosure (localCyclotomicExtension F ell) from sigma)
          ((localCyclotomicClosureEquiv F ell).symm x)) := by
  rfl

/-- Restriction along the chosen comparison of algebraic closures is
continuous for the two Krull topologies. -/
private theorem localCyclotomicRestrictionHom_continuous
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    Continuous (localCyclotomicRestrictionHom F ell) :=
  intermediateFieldRestrictionHom_continuous F
    (localCyclotomicExtension F ell)

private noncomputable def localCyclotomicRestrictionContinuousHom
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes) :
    Field.absoluteGaloisGroup (localCyclotomicExtension F ell) →ₜ*
      Field.absoluteGaloisGroup F :=
  ContinuousMonoidHom.mk (localCyclotomicRestrictionHom F ell)
    (localCyclotomicRestrictionHom_continuous F ell)

/-- Pullback of continuous additive characters as a linear map. -/
private def continuousCharacterPullLinearMap
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (n : ℕ) (f : G →ₜ* H) :
    NU.LocalTheory.ContinuousCharacter H n →ₗ[ZMod n]
      NU.LocalTheory.ContinuousCharacter G n where
  toFun := NU.LocalTheory.restrictCharacter n f
  map_add' a b := by
    ext g
    rfl
  map_smul' c a := by
    ext g
    simp only [RingHom.id_apply]
    let evH : NU.LocalTheory.ContinuousCharacter H n →+ ZMod n :=
      { toFun := fun chi => chi (Additive.ofMul (f (Additive.toMul g)))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let evG : NU.LocalTheory.ContinuousCharacter G n →+ ZMod n :=
      { toFun := fun chi => chi g
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hH : (c • a) (Additive.ofMul (f (Additive.toMul g))) =
        c * a (Additive.ofMul (f (Additive.toMul g))) := by
      simpa [evH] using ZMod.map_smul evH c a
    have hG : (c • NU.LocalTheory.restrictCharacter n f a) g =
        c * NU.LocalTheory.restrictCharacter n f a g := by
      simpa [evG] using ZMod.map_smul evG c
        (NU.LocalTheory.restrictCharacter n f a)
    change (c • a) (Additive.ofMul (f (Additive.toMul g))) =
      (c • NU.LocalTheory.restrictCharacter n f a) g
    rw [hH, hG]
    rfl

/-- Since the cyclotomic fixing subgroup has index below `ell`, restriction
of mod-`ell` characters to it is injective. -/
private theorem localCyclotomic_characterPull_injective
    (F : Type*) [Field F] [CharZero F] (ell : Nat.Primes)
    (hindex : (localCyclotomicExtension F ell).fixingSubgroup.index <
      (ell : ℕ)) :
    Function.Injective (continuousCharacterPullLinearMap (ell : ℕ)
      (localCyclotomicRestrictionContinuousHom F ell)) := by
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  let E := localCyclotomicExtension F ell
  let H := E.fixingSubgroup
  letI : H.Normal :=
    (InfiniteGalois.normal_iff_isGalois E).2 inferInstance
  intro a b hab
  let c : NU.LocalTheory.ContinuousCharacter
      (Field.absoluteGaloisGroup F) (ell : ℕ) := a - b
  have hpull : continuousCharacterPullLinearMap (ell : ℕ)
      (localCyclotomicRestrictionContinuousHom F ell) c = 0 := by
    rw [show c = a - b from rfl, map_sub, hab, sub_self]
  have hfix (tau : E.fixingSubgroup) :
      c (Additive.ofMul
        (show Field.absoluteGaloisGroup F from tau.1)) = 0 := by
    let sigma : Field.absoluteGaloisGroup E :=
      (localCyclotomicGaloisMulEquiv F ell).symm tau
    have hz := DFunLike.congr_fun hpull (Additive.ofMul sigma)
    change c (Additive.ofMul
      (localCyclotomicRestrictionContinuousHom F ell sigma)) = 0 at hz
    have hsigma : localCyclotomicRestrictionContinuousHom F ell sigma =
        (show Field.absoluteGaloisGroup F from tau.1) := by
      change localCyclotomicRestrictionHom F ell sigma = tau.1
      change ((localCyclotomicGaloisMulEquiv F ell) sigma).1 = tau.1
      rw [(localCyclotomicGaloisMulEquiv F ell).apply_symm_apply]
    rwa [hsigma] at hz
  have hc : c = 0 := by
    ext g
    cases g with
    | ofMul g =>
      have hgpow : g ^ H.index ∈ H := H.pow_index_mem g
      have hzpow := hfix (⟨g ^ H.index, hgpow⟩ : H)
      change c (H.index • Additive.ofMul g) = 0 at hzpow
      rw [map_nsmul, nsmul_eq_mul] at hzpow
      have hindexpos : 0 < H.index := by
        rw [← IntermediateField.finrank_eq_fixingSubgroup_index E]
        exact Module.finrank_pos
      have hcast : ((H.index : ℕ) : ZMod (ell : ℕ)) ≠ 0 := by
        intro hz
        exact (Nat.not_dvd_of_pos_of_lt hindexpos hindex)
          ((ZMod.natCast_eq_zero_iff H.index (ell : ℕ)).mp hz)
      exact (mul_eq_zero.mp hzpow).resolve_left hcast
  exact sub_eq_zero.mp hc

/-- The valuation ring of a nonarchimedean local field is complete for
its maximal-ideal adic topology.  Compactness turns a compatible family of
congruence classes into a point of their nested intersection. -/
private theorem localFieldIntegers_isAdicComplete
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (NU.LCFT.RingOfIntegers F))
      (NU.LCFT.RingOfIntegers F) := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (NU.LCFT.RingOfIntegers F) :=
    (Valued.isClosed_valuationSubring F).completeSpace_coe
  letI : CompactSpace (NU.LCFT.RingOfIntegers F) := inferInstance
  refine { prec' := ?_ }
  intro f hf
  let S n : Set (NU.LCFT.RingOfIntegers F) := f n +ᵥ
    (((IsLocalRing.maximalIdeal (NU.LCFT.RingOfIntegers F)) ^ n :
      Ideal (NU.LCFT.RingOfIntegers F)) : Set _)
  have hS n : S (n + 1) ⊆ S n := by
    apply (Set.vadd_set_subset_vadd_set_iff.mpr
      (Ideal.pow_le_pow_right n.le_succ)).trans
    simpa [S] using (hf n.le_succ).symm
  have hclosed n : IsClosed (S n) :=
    (IsNoetherianRing.isClosed_ideal
      ((IsLocalRing.maximalIdeal
        (NU.LCFT.RingOfIntegers F)) ^ n)).vadd (f n)
  obtain ⟨x, hx⟩ := (hclosed 0).isCompact
    |>.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) hclosed
  refine ⟨x, fun n => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hx n
  simpa [SModEq.sub_mem] using hy

/-- Away from the residue characteristic, Hensel's lemma makes the
principal-unit group uniquely rootable.  The derivative of `X^ell - u` at
`1` is the unit `ell`, while the principal-unit hypothesis is exactly the
required congruence modulo the maximal ideal. -/
private theorem localFieldPrincipalUnit_is_primeDivisible
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ell : Nat.Primes)
    (hchar : ringChar (NU.LCFT.LocalResidueField F) ≠ (ell : ℕ))
    (u : Units F) (hu : u ∈ NU.LCFT.principalUnitSubgroup F 1) :
    ∃ y : Units F, y ^ (ell : ℕ) = u := by
  let O := NU.LCFT.RingOfIntegers F
  let m := NU.LCFT.LocalMaximalIdeal F
  let k := NU.LCFT.LocalResidueField F
  letI : IsAdicComplete m O := localFieldIntegers_isAdicComplete F
  letI : HenselianRing O m := IsAdicComplete.henselianRing _ _
  obtain ⟨a, ha, hau⟩ := hu
  have hares : Ideal.Quotient.mk m (a : O) = 1 := by
    have h := congrArg Units.val ha
    change Ideal.Quotient.mk (m ^ 1) (a : O) = 1 at h
    rw [pow_one] at h
    exact h
  let f : Polynomial O :=
    Polynomial.X ^ (ell : ℕ) - Polynomial.C (a : O)
  have hf : f.Monic :=
    Polynomial.monic_X_pow_sub_C _ ell.2.ne_zero
  have heval : f.eval 1 ∈ m := by
    rw [show f.eval 1 = 1 - (a : O) by simp [f]]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [hares]
  have hellResidue : ((ell : ℕ) : k) ≠ 0 := by
    intro hz
    have hdvd : ringChar k ∣ (ell : ℕ) :=
      (CharP.cast_eq_zero_iff k (ringChar k) (ell : ℕ)).mp hz
    rcases (Nat.dvd_prime ell.2).mp hdvd with h | h
    · exact (CharP.prime_ringChar k).ne_one h
    · exact hchar h
  have hellUnit : IsUnit ((ell : ℕ) : O) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    apply hellResidue
    rw [show ((ell : ℕ) : k) =
        Ideal.Quotient.mk m ((ell : ℕ) : O) by
      exact (map_natCast (Ideal.Quotient.mk m) (ell : ℕ)).symm]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  have hderiv :
      IsUnit ((Ideal.Quotient.mk m) (f.derivative.eval 1)) := by
    have hdeval : f.derivative.eval 1 = ((ell : ℕ) : O) := by
      simp only [f, Polynomial.derivative_sub,
        Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, one_pow, mul_one]
    rw [hdeval]
    exact hellUnit.map _
  obtain ⟨b, hb, hbmod⟩ :=
    HenselianRing.is_henselian f hf 1 heval hderiv
  have hbpow : b ^ (ell : ℕ) = (a : O) := by
    have hzero : b ^ (ell : ℕ) - (a : O) = 0 := by
      simpa [f, Polynomial.IsRoot] using hb
    exact sub_eq_zero.mp hzero
  have hbnot : b ∉ m := by
    intro hbm
    have hbone : (1 : O) ∈ m := by
      have hsub := m.sub_mem hbm hbmod
      simpa [sub_sub_cancel] using hsub
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      ((Ideal.eq_top_iff_one m).mpr hbone)
  let bu : Units O := (IsLocalRing.notMem_maximalIdeal.mp hbnot).unit
  have hbu : (bu : O) = b :=
    (IsLocalRing.notMem_maximalIdeal.mp hbnot).unit_spec
  let y : Units F := NU.LCFT.ringUnitsToFieldUnits F bu
  refine ⟨y, ?_⟩
  apply Units.ext
  change (((bu : O) : F) ^ (ell : ℕ)) = (u : F)
  rw [hbu]
  exact (congrArg (fun z : O => (z : F)) hbpow).trans
    (congrArg Units.val hau)

/-- The spectral norm equips every finite extension of a nonarchimedean
local field with its canonical local-field topology and valuation class. -/
private theorem finiteExtension_localFieldStructure
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    ∃ vE : ValuativeRel E, ∃ tE : TopologicalSpace E,
      letI : ValuativeRel E := vE
      letI : TopologicalSpace E := tE
      ∃ hE : IsNonarchimedeanLocalField E,
        letI : IsNonarchimedeanLocalField E := hE
        ValuativeExtension F E := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := F)
      (Γ₀ := ValuativeRel.ValueGroupWithZero F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' :=
        ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F :=
    Valued.toNontriviallyNormedField F
      (ValuativeRel.ValueGroupWithZero F)
  let nE : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField F E
  letI : NontriviallyNormedField E := nE
  letI : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := F) (L := E))
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  let tE : TopologicalSpace E := inferInstance
  let vE : ValuativeRel E :=
    ValuativeRel.ofValuation (NormedField.valuation (K := E))
  refine ⟨vE, tE, ?_⟩
  letI : ValuativeRel E := vE
  letI : (NormedField.valuation (K := E)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : TopologicalSpace E := tE
  letI : Valued E NNReal := NormedField.toValued
  haveI htop : IsValuativeTopology E := by
    apply IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (NormedField.valuation (K := E))
    have hv : (Valued.v : Valuation E NNReal) =
        NormedField.valuation := rfl
    rw [← hv]
    exact Valued.is_topological_valuation
  haveI hloc : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete F E
  haveI hnontriv : ValuativeRel.IsNontrivial E := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := E))]
    infer_instance
  let hE : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hloc
      toIsNontrivial := hnontriv }
  refine ⟨hE, ?_⟩
  letI : IsNonarchimedeanLocalField E := hE
  constructor
  intro a b
  change NormedField.valuation (algebraMap F E a) ≤
      NormedField.valuation (algebraMap F E b) ↔ a ≤ᵥ b
  rw [NormedField.valuation_apply, NormedField.valuation_apply,
    ← NNReal.coe_le_coe]
  change spectralNorm F E (algebraMap F E a) ≤
      spectralNorm F E (algebraMap F E b) ↔ a ≤ᵥ b
  rw [spectralNorm_extends, spectralNorm_extends,
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F)]
  exact Valued.toNormedField.norm_le_iff

open NU.LCFT in
/-- A finite valuative extension has the same residue characteristic as its
base.  The map of valuation rings is local and therefore induces an
embedding of residue fields. -/
private theorem finiteValuativeExtension_residueChar
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [ValuativeRel F] [ValuativeRel E] [ValuativeExtension F E] :
    ringChar (LocalResidueField F) =
      ringChar (LocalResidueField E) := by
  letI : (ValuativeRel.valuation F).HasExtension
      (ValuativeRel.valuation E) := by
    constructor
    exact ValuativeRel.isEquiv _ _
  let i : RingOfIntegers F →+* RingOfIntegers E := algebraMap _ _
  letI : IsLocalHom i := inferInstance
  let rf : LocalResidueField F →+* LocalResidueField E :=
    IsLocalRing.ResidueField.map i
  symm
  apply (ringChar.eq_iff).2
  exact (RingHom.charP_iff_charP rf
    (ringChar (LocalResidueField F))).mp
      (ringChar.charP (LocalResidueField F))

open NU.LCFT in
/-- Every nonzero element of a local field, modulo `ell`-th powers away
from the residue characteristic, is a product of a valuation generator and
a residue-unit generator.  The remaining principal unit has an `ell`-th
root by `localFieldPrincipalUnit_is_primeDivisible`. -/
private theorem localField_tameUnitFactorization
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ell : Nat.Primes)
    (hchar : ringChar (LocalResidueField F) ≠ (ell : ℕ)) :
    ∃ pi tau : Units F, ∀ x : Units F,
      ∃ n : ℤ, ∃ a : ℕ, ∃ y : Units F,
        x = pi ^ n * tau ^ a * y ^ (ell : ℕ) := by
  let O := RingOfIntegers F
  let m := LocalMaximalIdeal F
  let res : O →+* LocalResidueField F := IsLocalRing.residue O
  let pi : Units F := (defaultUniformizer F).val
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator
    (α := Units (LocalResidueField F))
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective
    (g : LocalResidueField F)
  have hcnot : c ∉ m := by
    intro hcm
    have hzero : (g : LocalResidueField F) = 0 := by
      rw [← hc]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcm
    exact Units.ne_zero g hzero
  let cu : Units O := (IsLocalRing.notMem_maximalIdeal.mp hcnot).unit
  have hcu : (cu : O) = c :=
    (IsLocalRing.notMem_maximalIdeal.mp hcnot).unit_spec
  let tau : Units F := ringUnitsToFieldUnits F cu
  refine ⟨pi, tau, ?_⟩
  intro x
  let n : ℤ := normalizedValuation F x
  let w : Units F := x * pi ^ (-n)
  have hpi : normalizedValuation F pi = 1 :=
    (defaultUniformizer F).valuation_eq_one
  have hpiz : normalizedValuation F (pi ^ (-n)) = -n := by
    unfold normalizedValuation
    rw [map_zpow]
    change (-n) * normalizedValuation F pi = -n
    rw [hpi, mul_one]
  have hwval : normalizedValuation F w = 0 := by
    rw [show w = x * pi ^ (-n) by rfl,
      normalizedValuation_mul, hpiz]
    exact add_neg_cancel n
  have hwinvval : normalizedValuation F w⁻¹ = 0 := by
    unfold normalizedValuation
    rw [map_inv]
    change -normalizedValuation F w = 0
    rw [hwval, neg_zero]
  obtain ⟨cw, hcw⟩ :=
    (exists_normalizedValuationHom F).choose_spec.2 w |>.1 hwval.ge
  obtain ⟨dw, hdw⟩ :=
    (exists_normalizedValuationHom F).choose_spec.2 w⁻¹ |>.1
      hwinvval.ge
  let wu : Units O :=
    { val := cw
      inv := dw
      val_inv := by
        apply Subtype.ext
        change (cw : F) * (dw : F) = 1
        rw [hcw, hdw]
        simp
      inv_val := by
        apply Subtype.ext
        change (dw : F) * (cw : F) = 1
        rw [hcw, hdw]
        simp }
  have hwu : ringUnitsToFieldUnits F wu = w := by
    apply Units.ext
    exact hcw
  let rwunit : Units (LocalResidueField F) :=
    Units.map res.toMonoidHom wu
  obtain ⟨a, ha⟩ :=
    (Submonoid.mem_powers_iff rwunit g).mp (hg rwunit)
  have hcug : Units.map res.toMonoidHom cu = g := by
    apply Units.ext
    change res (cu : O) = (g : LocalResidueField F)
    rw [hcu]
    exact hc
  let ru : Units O := wu * (cu ^ a)⁻¹
  have hruResidue : Units.map res.toMonoidHom ru = 1 := by
    rw [show Units.map res.toMonoidHom ru =
        rwunit * (Units.map res.toMonoidHom cu ^ a)⁻¹ by
      simp [ru, rwunit]]
    rw [hcug, ← ha]
    simp
  let r : Units F := ringUnitsToFieldUnits F ru
  have hrprincipal : r ∈ principalUnitSubgroup F 1 := by
    refine ⟨ru, ?_, rfl⟩
    change integralUnitReduction F 1 ru = 1
    apply Units.ext
    change Ideal.Quotient.mk (m ^ 1) (ru : O) = 1
    rw [pow_one]
    exact congrArg Units.val hruResidue
  obtain ⟨y, hy⟩ := localFieldPrincipalUnit_is_primeDivisible
    F ell hchar r hrprincipal
  refine ⟨n, a, y, ?_⟩
  have hr : r = w * tau ^ (- (a : ℤ)) := by
    change ringUnitsToFieldUnits F ru = _
    rw [show ru = wu * (cu ^ a)⁻¹ by rfl, map_mul, map_inv,
      map_pow, hwu]
    simp [tau]
  rw [← hy] at hr
  rw [show w = x * pi ^ (-n) by rfl] at hr
  calc
    x = pi ^ n * (x * pi ^ (-n)) := by
      symm
      calc
        pi ^ n * (x * pi ^ (-n)) =
            x * (pi ^ n * pi ^ (-n)) := by ac_rfl
        _ = x := by
          rw [← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    _ = pi ^ n * (y ^ (ell : ℕ) * tau ^ (a : ℤ)) := by
      rw [hr]
      simp
    _ = pi ^ n * tau ^ a * y ^ (ell : ℕ) := by
      simp only [zpow_natCast]
      ac_rfl

/-- The valuation and residue generators span the tame Kummer quotient of
an arbitrary nonarchimedean local field. -/
private theorem localField_tameKummerQuotient_span
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ell : Nat.Primes)
    (hchar : ringChar (NU.LCFT.LocalResidueField F) ≠ (ell : ℕ)) :
    ∃ gens : Fin 2 → NU.LocalTheory.KummerQuotient F (ell : ℕ),
      Submodule.span (ZMod (ell : ℕ)) (Set.range gens) = ⊤ := by
  obtain ⟨pi, tau, hfactor⟩ :=
    localField_tameUnitFactorization F ell hchar
  let xpi := NU.LocalTheory.kummerQuotientClass (ell : ℕ) pi
  let xtau := NU.LocalTheory.kummerQuotientClass (ell : ℕ) tau
  let gens : Fin 2 → NU.LocalTheory.KummerQuotient F (ell : ℕ) :=
    ![xpi, xtau]
  have hspan :
      Submodule.span (ZMod (ell : ℕ)) (Set.range gens) = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨u, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Additive (Units F))
        ((ell : ℕ) : ℤ))).mkQ_surjective q
    cases u with
    | ofMul u =>
      obtain ⟨n, a, y, hu⟩ := hfactor u
      let S := Submodule.span (ZMod (ell : ℕ)) (Set.range gens)
      have hpi : xpi ∈ S := by
        apply Submodule.subset_span
        exact ⟨0, by simp [gens]⟩
      have htau : xtau ∈ S := by
        apply Submodule.subset_span
        exact ⟨1, by simp [gens]⟩
      change NU.LocalTheory.kummerQuotientClass (ell : ℕ) u ∈ S
      rw [hu]
      change ModN.mkQ (ell : ℕ)
        (n • Additive.ofMul pi + a • Additive.ofMul tau +
          (ell : ℕ) • Additive.ofMul y) ∈ S
      rw [map_add, map_add, map_zsmul, map_nsmul, map_nsmul]
      have hz : (ell : ℕ) •
          ModN.mkQ (ell : ℕ) (Additive.ofMul y) = 0 := by
        calc
          (ell : ℕ) • ModN.mkQ (ell : ℕ) (Additive.ofMul y) =
              ((ell : ℕ) : ZMod (ell : ℕ)) •
                ModN.mkQ (ell : ℕ) (Additive.ofMul y) :=
            (Nat.cast_smul_eq_nsmul (ZMod (ell : ℕ)) (ell : ℕ)
              (ModN.mkQ (ell : ℕ) (Additive.ofMul y))).symm
          _ = 0 := by simp
      rw [hz]
      exact S.add_mem (S.add_mem
        (S.toAddSubgroup.zsmul_mem hpi n)
        (S.toAddSubgroup.nsmul_mem htau a)) S.zero_mem
  exact ⟨gens, hspan⟩

private theorem localField_tameKummerQuotient_moduleFinite
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ell : Nat.Primes)
    (hchar : ringChar (NU.LCFT.LocalResidueField F) ≠ (ell : ℕ)) :
    Module.Finite (ZMod (ell : ℕ))
      (NU.LocalTheory.KummerQuotient F (ell : ℕ)) := by
  obtain ⟨gens, hspan⟩ :=
    localField_tameKummerQuotient_span F ell hchar
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range gens)

private theorem localField_tameKummerQuotient_finrank_le_two
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ell : Nat.Primes)
    (hchar : ringChar (NU.LCFT.LocalResidueField F) ≠ (ell : ℕ)) :
    Module.finrank (ZMod (ell : ℕ))
      (NU.LocalTheory.KummerQuotient F (ell : ℕ)) ≤ 2 := by
  letI : Module.Finite (ZMod (ell : ℕ))
      (NU.LocalTheory.KummerQuotient F (ell : ℕ)) :=
    localField_tameKummerQuotient_moduleFinite F ell hchar
  obtain ⟨gens, hspan⟩ :=
    localField_tameKummerQuotient_span F ell hchar
  exact finrank_le_of_span_eq_top hspan

/-- The rational residue prime bundled as `Nat.Primes`. -/
private noncomputable def residuePrime
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) : Nat.Primes :=
  ⟨NU.LocalTheory.residueCharacteristic v,
    residueCharacteristic_prime v⟩

/-- A rational finite place has norm equal to its residue characteristic. -/
private theorem rationalPrimeNorm_eq_residueCharacteristic
    (v : NU.Chebotarev.PrimeIdeal ℚ) :
    NU.Chebotarev.PrimeIdeal.norm v =
      NU.LocalTheory.residueCharacteristic v := by
  rw [NU.NeukirchUchida.LocalInvariants.residueCharacteristic_eq_absNorm_under]
  change Ideal.absNorm v.asIdeal = Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  let f : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.ringOfIntegersEquiv
  have hf : f.symm.toRingHom =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) := by
    exact RingHom.ext_int _ _
  have hmap : Ideal.map f.toRingHom v.asIdeal =
      Ideal.under ℤ v.asIdeal := by
    calc
      Ideal.map f.toRingHom v.asIdeal =
          Ideal.comap f.symm v.asIdeal := by
        simpa using Ideal.map_comap_of_equiv (I := v.asIdeal) f
      _ = Ideal.under ℤ v.asIdeal := by
        rw [Ideal.under_def]
        exact congrArg
          (fun g : ℤ →+* NumberField.RingOfIntegers ℚ =>
            Ideal.comap g v.asIdeal) hf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv v.asIdeal (Ideal.under ℤ v.asIdeal)
      f hmap.symm).toEquiv

/-- The residue prime is coprime to one less than the residue norm. -/
private theorem residueCharacteristic_coprime_norm_sub_one
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    (NU.LocalTheory.residueCharacteristic v).Coprime
      (NU.Chebotarev.PrimeIdeal.norm v - 1) := by
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hnorm : NU.Chebotarev.PrimeIdeal.norm v =
      NU.Chebotarev.PrimeIdeal.norm q ^
        v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    exact NU.Chebotarev.PrimeIdeal.norm_pow_inertiaDeg
      v q inferInstance
  have hq : NU.Chebotarev.PrimeIdeal.norm q =
      NU.LocalTheory.residueCharacteristic v := by
    rw [rationalPrimeNorm_eq_residueCharacteristic,
      NU.NeukirchUchida.LocalInvariants.residueCharacteristic_restrictFinitePlace]
  have hf : 0 <
      v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_pos v.asIdeal
      (NumberField.RingOfIntegers ℚ)
  rw [hnorm, hq]
  have hpow : (NU.LocalTheory.residueCharacteristic v ^
      v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)).Coprime
      (NU.LocalTheory.residueCharacteristic v ^
        v.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) - 1) :=
    (Nat.coprime_self_sub_right
      (pow_pos
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).pos
        _)).2 (Nat.coprime_one_right _)
  exact (Nat.coprime_pow_left_iff hf _ _).mp hpow

/-- The local degree `n = e f` attached to an ambient finite place. -/
private noncomputable def ambientLocalDegree
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) : ℕ :=
  ambientRamificationIndex P * ambientResidueDegree P

/-- The local degree `e(v/ℚ) f(v/ℚ)` of a finite place. -/
private noncomputable def finitePlaceLocalDegree
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) : ℕ :=
  let p := NU.LocalTheory.restrictFinitePlace ℚ v
  p.asIdeal.ramificationIdx' v.asIdeal *
    p.asIdeal.inertiaDeg' v.asIdeal

/-- In a commutative group, the subgroup of `p`-power torsion is
`ell`-divisible for distinct primes `p` and `ell`. -/
private theorem primePowerTorsion_is_primeDivisible
    {G : Type*} [CommGroup G]
    (p ell : Nat.Primes) (hne : ell ≠ p) (u : G)
    (hu : ∃ a : ℕ, u ^ ((p : ℕ) ^ a) = 1) :
    ∃ v : G, v ^ (ell : ℕ) = u := by
  obtain ⟨a, hua⟩ := hu
  let N := (p : ℕ) ^ a
  have hcop : (ell : ℕ).Coprime N := by
    exact (Nat.coprime_primes ell.2 p.2).2 (by
      intro h
      apply hne
      exact Subtype.ext h)
      |>.pow_right a
  letI : NeZero N := ⟨pow_ne_zero _ p.2.ne_zero⟩
  let e : (ZMod N)ˣ := (ZMod.unitOfCoprime (ell : ℕ) hcop)⁻¹
  let k : ℕ := (e : ZMod N).val
  have hmod : Nat.ModEq N ((ell : ℕ) * k) 1 := by
    apply (ZMod.natCast_eq_natCast_iff ((ell : ℕ) * k) 1 N).1
    rw [Nat.cast_mul]
    rw [show (k : ZMod N) = (e : ZMod N) by
      exact ZMod.natCast_zmod_val (e : ZMod N)]
    change ((ell : ℕ) : ZMod N) *
      (((ZMod.unitOfCoprime (ell : ℕ) hcop)⁻¹ : (ZMod N)ˣ) : ZMod N) =
        (1 : ℕ)
    rw [← ZMod.coe_unitOfCoprime (ell : ℕ) hcop, Units.mul_inv]
    simp
  have hord : orderOf u ∣ N := orderOf_dvd_of_pow_eq_one hua
  have hmod' : Nat.ModEq (orderOf u) ((ell : ℕ) * k) 1 :=
    Nat.ModEq.of_dvd hord hmod
  refine ⟨u ^ k, ?_⟩
  rw [← pow_mul, mul_comm k]
  exact (pow_eq_pow_iff_modEq.mpr hmod').trans (pow_one u)

/-- A finite product of `p`-adic integer groups is `ell`-divisible
when `ell ≠ p`. -/
private theorem padicVector_is_primeDivisible
    (p ell : Nat.Primes) (hne : ell ≠ p) (n : ℕ)
    (x : Multiplicative (Fin n → ℤ_[p])) :
    ∃ y, y ^ (ell : ℕ) = x := by
  have hcop : (p : ℕ).Coprime (ell : ℕ) :=
    (Nat.coprime_primes p.2 ell.2).2 (by
      intro h
      apply hne
      exact Subtype.ext h.symm)
  have hu : IsUnit ((ell : ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 hcop)
  let e : ℤ_[p]ˣ := hu.unit
  have he : (e : ℤ_[p]) = (ell : ℕ) := hu.unit_spec
  let z : Fin n → ℤ_[p] := fun i =>
    (e⁻¹ : ℤ_[p]ˣ) * (Multiplicative.toAdd x) i
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  apply Multiplicative.toAdd.injective
  change (ell : ℕ) • z = Multiplicative.toAdd x
  funext i
  change ((ell : ℕ) : ℤ_[p]) * z i = (Multiplicative.toAdd x) i
  dsimp [z]
  rw [← he]
  simp

/-- Products preserve topological additive equivalences. -/
private def continuousAddEquivProdCongr
    {A B C D : Type*}
    [Add A] [Add B] [Add C] [Add D]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ+ B) (f : C ≃ₜ+ D) :
    A × C ≃ₜ+ B × D :=
  ContinuousAddEquiv.mk'
    (Homeomorph.prodCongr e.toHomeomorph f.toHomeomorph)
    (fun x y => by
      apply Prod.ext
      · exact e.map_add x.1 y.1
      · exact f.map_add x.2 y.2)

/-- Every nonzero quotient of `ℤ_p` is finite.  This is the DVR
criterion: a nonzero ideal contains a power of the maximal ideal, whose
residue field is `ZMod p`. -/
private theorem padicInt_quotient_finite
    (p : Nat.Primes) (I : Ideal ℤ_[p]) (hI : I ≠ ⊥) :
    Finite (ℤ_[p] ⧸ I) := by
  letI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod (p : ℕ))
      PadicInt.residueField.toEquiv.symm
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal ℤ_[p]
      (inferInstance :
        (IsLocalRing.maximalIdeal ℤ_[p]).IsPrincipal) I hI
  exact ⟨n, hn ▸ le_rfl⟩

/-- The torsion submodule of a finite `ℤ_p`-module is a finite group.
The PID elementary-divisor theorem reduces it to finitely many nonzero
quotients of `ℤ_p`. -/
private theorem padicModule_torsion_finite
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Finite (Submodule.torsion ℤ_[p] M) := by
  let T := Submodule.torsion ℤ_[p] M
  letI : Module.Finite ℤ_[p] T := inferInstance
  obtain ⟨ι, fi, q, hq, e, ⟨equiv⟩⟩ :=
    Module.equiv_directSum_of_isTorsion
      (R := ℤ_[p]) (M := T)
      (Submodule.torsion_isTorsion (R := ℤ_[p]) (M := M))
  letI : Fintype ι := fi
  have hquot (i : ι) :
      Finite (ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i) := by
    apply padicInt_quotient_finite p
    exact fun h => pow_ne_zero (e i) (hq i).ne_zero
      (Submodule.span_singleton_eq_bot.mp h)
  letI (i : ι) : Finite (ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i) :=
    hquot i
  let de := DirectSum.linearEquivFunOnFintype ℤ_[p] ι
    (fun i => ℤ_[p] ⧸ ℤ_[p] ∙ q i ^ e i)
  exact Finite.of_injective (fun x => de (equiv x))
    (de.injective.comp equiv.injective)

/-- A finite torsion-free module over the complete PID `ℤ_p` is free.
This is the algebraic structure theorem needed after finite torsion has been
removed from the principal-unit pro-`p` group. -/
private theorem padicModule_free_of_finite_torsionFree
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M] :
    Module.Free ℤ_[p] M := by
  exact Module.free_of_finite_type_torsion_free'

/-- The torsion sequence of a finite `ℤ_p`-module splits.  The quotient by
torsion is torsion-free, hence free and projective, so its quotient map has a
linear section. -/
private theorem padicModule_torsionProdQuotientLinearEquiv
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Nonempty
      (M ≃ₗ[ℤ_[p]]
        Submodule.torsion ℤ_[p] M ×
          (M ⧸ Submodule.torsion ℤ_[p] M)) := by
  let Q := M ⧸ Submodule.torsion ℤ_[p] M
  letI : Module.Finite ℤ_[p] Q := inferInstance
  letI : Module.Free ℤ_[p] Q :=
    padicModule_free_of_finite_torsionFree p Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (P := Q) (Submodule.mkQ (Submodule.torsion ℤ_[p] M))
    (LinearMap.id (R := ℤ_[p]) (M := Q))
    (Submodule.Quotient.mk_surjective
      (Submodule.torsion ℤ_[p] M))
  exact ⟨(lequivProdOfRightSplitExact
    (Submodule.torsion ℤ_[p] M).injective_subtype
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hs).symm⟩

/-- Every linear map out of a finite torsion-free topological
`ℤ_p`-module is continuous.  A finite basis identifies its source with a
compact power of `ℤ_p`; compact-to-Hausdorff rigidity makes the coordinate
map continuous. -/
private theorem padicModule_linearMap_continuous_of_finite_torsionFree
    (p : Nat.Primes) (M N : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M]
    [AddCommGroup N] [Module ℤ_[p] N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousSMul ℤ_[p] N]
    (f : M →ₗ[ℤ_[p]] N) : Continuous f := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ_[p]) (M := M)
  let e : (Fin n → ℤ_[p]) ≃ M := b.equivFun.symm.toEquiv
  have he : Continuous e := by
    have hs : Continuous fun x : Fin n → ℤ_[p] =>
        ∑ i, x i • b i := by
      fun_prop
    convert hs using 1
    funext x
    exact b.equivFun_symm_apply x
  let h : (Fin n → ℤ_[p]) ≃ₜ M :=
    he.homeoOfEquivCompactToT2
  have hf : Continuous fun x : Fin n → ℤ_[p] =>
      ∑ i, x i • f (b i) := by
    fun_prop
  have hc := hf.comp h.symm.continuous
  convert hc using 1
  funext x
  change f x = ∑ i, (b.equivFun x) i • f (b i)
  calc
    f x = f (∑ i, (b.equivFun x) i • b i) := by
      congr 1
      symm
      rw [← b.equivFun_symm_apply,
        b.equivFun.symm_apply_apply]
    _ = ∑ i, f ((b.equivFun x) i • b i) := by rw [map_sum]
    _ = _ := by simp

/-- The algebraic torsion splitting of a finite compact `ℤ_p`-module
is automatically topological.  The finite torsion factor is discrete, maps
from the free quotient are continuous, and compact-to-Hausdorff rigidity
supplies the inverse continuity. -/
private theorem padicModule_torsionProdQuotientContinuousAddEquiv
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [CompactSpace M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Nonempty
      ((Submodule.torsion ℤ_[p] M ×
          (M ⧸ Submodule.torsion ℤ_[p] M)) ≃ₜ+ M) := by
  let T := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Finite T := padicModule_torsion_finite p M
  have hTfinite : (T : Set M).Finite := Set.toFinite _
  letI : IsClosed (T : Set M) := hTfinite.isClosed
  letI : CompactSpace Q := isCompact_univ_iff.mp (by
    have hcomp :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).image
        T.continuous_mkQ
    have hsurj : Function.Surjective T.mkQ :=
      Submodule.Quotient.mk_surjective T
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at hcomp
    exact hcomp)
  letI : Module.Finite ℤ_[p] Q := inferInstance
  letI : Module.Free ℤ_[p] Q :=
    padicModule_free_of_finite_torsionFree p Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (P := Q) (Submodule.mkQ T)
    (LinearMap.id (R := ℤ_[p]) (M := Q))
    (Submodule.Quotient.mk_surjective T)
  let e : (T × Q) ≃ₗ[ℤ_[p]] M :=
    lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hs
  let fT : T →ₗ[ℤ_[p]] M := e.toLinearMap.comp
    (LinearMap.inl ℤ_[p] T Q)
  let fQ : Q →ₗ[ℤ_[p]] M := e.toLinearMap.comp
    (LinearMap.inr ℤ_[p] T Q)
  have hfT : Continuous fT := continuous_of_discreteTopology
  have hfQ : Continuous fQ :=
    padicModule_linearMap_continuous_of_finite_torsionFree
      p Q M fQ
  have he : Continuous e := by
    have hc :=
      (hfT.comp continuous_fst).add (hfQ.comp continuous_snd)
    convert hc using 1
    funext x
    change e x = fT x.1 + fQ x.2
    calc
      e x = e ((x.1, 0) + (0, x.2)) := by
        congr 1
        ext <;> simp
      _ = e (x.1, 0) + e (0, x.2) := e.map_add _ _
      _ = fT x.1 + fQ x.2 := rfl
  let h : (T × Q) ≃ₜ M :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he
  exact ⟨ContinuousAddEquiv.mk' h
    (fun x y => e.map_add x y)⟩

/-- A finite torsion-free topological `ℤ_p`-module is topologically a finite
power of `ℤ_p`.  Continuity of a basis expansion and compact-to-Hausdorff
rigidity supply continuity of the inverse without a separate coordinate
argument. -/
private theorem padicModule_continuousAddEquivPi_of_finite_torsionFree
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] [Module.IsTorsionFree ℤ_[p] M] :
    Nonempty
      ((Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃ₜ+ M) := by
  letI : Module.Free ℤ_[p] M :=
    padicModule_free_of_finite_torsionFree p M
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ_[p]) (M := M)
  have hn : Module.finrank ℤ_[p] M = n := by
    simpa using Module.finrank_eq_card_basis b
  subst n
  let e : (Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃+ M :=
    b.equivFun.symm.toAddEquiv
  have he : Continuous e := by
    have hs : Continuous fun
        x : Fin (Module.finrank ℤ_[p] M) → ℤ_[p] =>
        ∑ i, x i • b i := by
      fun_prop
    convert hs using 1
    funext x
    exact b.equivFun_symm_apply x
  let h : (Fin (Module.finrank ℤ_[p] M) → ℤ_[p]) ≃ₜ M :=
    he.homeoOfEquivCompactToT2
  exact ⟨ContinuousAddEquiv.mk' h
    (fun x y => e.map_add x y)⟩

/-- Complete topological structure theorem for a finite compact
`ℤ_p`-module: it is the product of its finite torsion subgroup and a power
of `ℤ_p` whose rank is the rank of the torsion-free quotient. -/
private theorem padicModule_torsionProdFreeContinuousAddEquiv
    (p : Nat.Primes) (M : Type*)
    [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M] [CompactSpace M] [ContinuousSMul ℤ_[p] M]
    [Module.Finite ℤ_[p] M] :
    Nonempty
      ((Submodule.torsion ℤ_[p] M ×
          (Fin (Module.finrank ℤ_[p]
            (M ⧸ Submodule.torsion ℤ_[p] M)) → ℤ_[p])) ≃ₜ+ M) := by
  let T := Submodule.torsion ℤ_[p] M
  let Q := M ⧸ T
  letI : Finite T := padicModule_torsion_finite p M
  have hTfinite : (T : Set M).Finite := Set.toFinite _
  letI : IsClosed (T : Set M) := hTfinite.isClosed
  letI : Module.Finite ℤ_[p] Q := inferInstance
  obtain ⟨freeEquiv⟩ :=
    padicModule_continuousAddEquivPi_of_finite_torsionFree p Q
  obtain ⟨splitEquiv⟩ :=
    padicModule_torsionProdQuotientContinuousAddEquiv p M
  let leftEquiv : T ≃ₜ+ T := ContinuousAddEquiv.refl T
  exact ⟨(continuousAddEquivProdCongr leftEquiv freeEquiv).trans
    splitEquiv⟩

/-- The public deep-unit bridge package, specialized to the residue prime. -/
private abbrev LocalUnitDecompositionData
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :=
  NU.NeukirchUchida.Bridges.LocalUnitDecompositionData v (residuePrime v)
    (finitePlaceLocalDegree v)

/-- `Additive` commutes with a fourfold product. -/
private def additiveProdFourAddEquiv
    {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D] :
    Additive (A × B × C × D) ≃+
      Additive A × Additive B × Additive C × Additive D :=
  AddEquiv.refl _

/-- An additive homomorphism induces the expected linear map after
quotienting source and target by `n`. -/
private noncomputable def modNLinearMapOfAddHom
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (f : G →+ H) :
    ModN G n →ₗ[ZMod n] ModN H n :=
  ModN.liftEquiv'.symm
    ⟨(ModN.mkQ n).comp f, fun g => by
      change n • ModN.mkQ n (f g) = 0
      change ModN.mkQ n (n • f g) = 0
      change Submodule.Quotient.mk (n • f g) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨f g, by simp⟩⟩

@[simp] private theorem modNLinearMapOfAddHom_mkQ
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (f : G →+ H) (g : G) :
    modNLinearMapOfAddHom n f (ModN.mkQ n g) =
      ModN.mkQ n (f g) := by
  rfl

/-- Additively equivalent groups have linearly equivalent quotients modulo
`n`. -/
private noncomputable def modNLinearEquivOfAddEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (n : ℕ) (e : G ≃+ H) :
    ModN G n ≃ₗ[ZMod n] ModN H n :=
  let f := modNLinearMapOfAddHom n e.toAddMonoidHom
  let g := modNLinearMapOfAddHom n e.symm.toAddMonoidHom
  LinearEquiv.ofBijective f
    ⟨(show Function.LeftInverse g f by
        intro x
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range
            (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective x
        change ModN.mkQ n (e.symm (e x)) = ModN.mkQ n x
        rw [e.symm_apply_apply]).injective,
      (show Function.RightInverse g f by
        intro x
        obtain ⟨x, rfl⟩ :=
          (LinearMap.range
            (LinearMap.lsmul ℤ H (n : ℤ))).mkQ_surjective x
        change ModN.mkQ n (e (e.symm x)) = ModN.mkQ n x
        rw [e.apply_symm_apply]).surjective⟩

/-- Quotienting a product by `n` is the product of the quotients. -/
private noncomputable def modNProdLinearMap
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    ModN (A × B) n →ₗ[ZMod n] ModN A n × ModN B n :=
  ModN.liftEquiv'.symm
    ⟨{ toFun := fun x => (ModN.mkQ n x.1, ModN.mkQ n x.2)
       map_zero' := by simp
       map_add' := by intro x y; ext <;> simp },
     fun x => by
       apply Prod.ext
       · change n • ModN.mkQ n x.1 = 0
         rw [← map_nsmul]
         change Submodule.Quotient.mk (n • x.1) = 0
         rw [Submodule.Quotient.mk_eq_zero]
         exact ⟨x.1, by simp⟩
       · change n • ModN.mkQ n x.2 = 0
         rw [← map_nsmul]
         change Submodule.Quotient.mk (n • x.2) = 0
         rw [Submodule.Quotient.mk_eq_zero]
         exact ⟨x.2, by simp⟩⟩

@[simp] private theorem modNProdLinearMap_mkQ
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : A × B) :
    modNProdLinearMap (A := A) (B := B) n (ModN.mkQ n x) =
      (ModN.mkQ n x.1, ModN.mkQ n x.2) := rfl

private theorem modNProdLinearMap_bijective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    Function.Bijective
      (modNProdLinearMap (A := A) (B := B) n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (A × B) (n : ℤ))).mkQ_surjective x
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ (A × B) (n : ℤ))).mkQ_surjective y
    change (ModN.mkQ n x.1, ModN.mkQ n x.2) =
      (ModN.mkQ n y.1, ModN.mkQ n y.2) at hxy
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have h1 : ModN.mkQ n (x.1 - y.1) = 0 := by
      simpa using sub_eq_zero.mpr (congrArg Prod.fst hxy)
    have h2 : ModN.mkQ n (x.2 - y.2) = 0 := by
      simpa using sub_eq_zero.mpr (congrArg Prod.snd hxy)
    change Submodule.Quotient.mk _ = 0 at h1 h2
    rw [Submodule.Quotient.mk_eq_zero] at h1 h2
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨(a, b), by ext <;> simp_all⟩
  · intro x
    obtain ⟨a, ha⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ A (n : ℤ))).mkQ_surjective x.1
    obtain ⟨b, hb⟩ :=
      (LinearMap.range
        (LinearMap.lsmul ℤ B (n : ℤ))).mkQ_surjective x.2
    refine ⟨ModN.mkQ n (a, b), ?_⟩
    change (ModN.mkQ n a, ModN.mkQ n b) = x
    exact Prod.ext ha hb

private noncomputable def modNProdLinearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    ModN (A × B) n ≃ₗ[ZMod n] ModN A n × ModN B n :=
  LinearEquiv.ofBijective
    (modNProdLinearMap (A := A) (B := B) n)
    (modNProdLinearMap_bijective n)

/-- The product comparison iterated over four factors. -/
private noncomputable def modNFourLinearEquiv
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] (n : ℕ) :
    ModN (A × B × C × D) n ≃ₗ[ZMod n]
      ModN A n × ModN B n × ModN C n × ModN D n :=
  (modNProdLinearEquiv (A := A) (B := B × C × D) n).trans
    ((LinearEquiv.refl (ZMod n) (ModN A n)).prodCongr
      ((modNProdLinearEquiv (A := B) (B := C × D) n).trans
        ((LinearEquiv.refl (ZMod n) (ModN B n)).prodCongr
          (modNProdLinearEquiv (A := C) (B := D) n))))

/-- A divisible additive group has trivial quotient modulo `n`. -/
private theorem modN_subsingleton_of_divisible
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (hdiv : ∀ x : G, ∃ y : G, n • y = x) :
    Subsingleton (ModN G n) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ :=
    (LinearMap.range
      (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective a
  obtain ⟨y, rfl⟩ :=
    (LinearMap.range
      (LinearMap.lsmul ℤ G (n : ℤ))).mkQ_surjective b
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨z, hz⟩ := hdiv (x - y)
  exact ⟨z, by simpa using hz⟩

private theorem modN_finrank_zero_of_divisible
    {G : Type*} [AddCommGroup G] (p : Nat.Primes)
    (hdiv : ∀ x : G, ∃ y : G, (p : ℕ) • y = x) :
    Module.finrank (ZMod (p : ℕ))
      (ModN G (p : ℕ)) = 0 := by
  letI : Subsingleton (ModN G (p : ℕ)) :=
    modN_subsingleton_of_divisible (p : ℕ) hdiv
  exact Module.finrank_eq_zero_of_subsingleton _ _

/-- The valuation lattice contributes one dimension modulo `p`. -/
private theorem intMod_finrank (p : Nat.Primes) :
    Module.finrank (ZMod (p : ℕ)) (ModN ℤ (p : ℕ)) = 1 := by
  let b := Module.Free.chooseBasis ℤ ℤ
  calc
    Module.finrank (ZMod (p : ℕ)) (ModN ℤ (p : ℕ)) =
        Fintype.card (Module.Free.ChooseBasisIndex ℤ ℤ) :=
      Module.finrank_eq_card_basis (ModN.basis b)
    _ = Module.finrank ℤ ℤ := by
      symm
      exact Module.finrank_eq_card_chooseBasisIndex ℤ ℤ
    _ = 1 := Module.finrank_self ℤ

/-- The additive form of the multiplicative valuation lattice likewise
contributes one dimension. -/
private theorem additiveMultiplicativeIntMod_finrank
    (p : Nat.Primes) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive (Multiplicative ℤ)) (p : ℕ)) = 1 := by
  rw [(modNLinearEquivOfAddEquiv (p : ℕ)
    (AddEquiv.additiveMultiplicative ℤ)).finrank_eq]
  exact intMod_finrank p

/-- Multiplication by `n` is onto on `ZMod N` when `n` and `N` are
coprime. -/
private theorem zmod_is_nDivisible_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : ZMod N) : ∃ y : ZMod N, n • y = x := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime n hcop
  let y : ZMod N := (u⁻¹ : (ZMod N)ˣ) * x
  refine ⟨y, ?_⟩
  rw [nsmul_eq_mul]
  change (n : ZMod N) * y = x
  have hu : (u : ZMod N) = (n : ZMod N) :=
    ZMod.coe_unitOfCoprime n hcop
  rw [← hu]
  simp [y]

/-- The same divisibility in the additive form of a multiplicative cyclic
group. -/
private theorem additiveMultiplicativeZMod_is_nDivisible_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : Additive (Multiplicative (ZMod N))) :
    ∃ y, n • y = x := by
  obtain ⟨y, hy⟩ := zmod_is_nDivisible_of_coprime n N hcop
    (AddEquiv.additiveMultiplicative (ZMod N) x)
  refine ⟨(AddEquiv.additiveMultiplicative (ZMod N)).symm y, ?_⟩
  apply (AddEquiv.additiveMultiplicative (ZMod N)).injective
  simpa using hy

/-- A coprime power cannot kill a nontrivial element of a cyclic
`ZMod` group. -/
private theorem multiplicativeZMod_pow_eq_one_of_coprime
    (n N : ℕ) [NeZero N] (hcop : n.Coprime N)
    (x : Multiplicative (ZMod N)) (hx : x ^ n = 1) : x = 1 := by
  apply Multiplicative.toAdd.injective
  have hxadd := congrArg Multiplicative.toAdd hx
  change n • Multiplicative.toAdd x = 0 at hxadd
  have hsurj : Function.Surjective
      (fun z : ZMod N => n • z) := by
    intro z
    exact zmod_is_nDivisible_of_coprime n N hcop z
  have hinj : Function.Injective
      (fun z : ZMod N => n • z) :=
    Finite.injective_iff_surjective.mpr hsurj
  exact hinj (by simpa using hxadd)

/-- Coordinatewise reduction modulo `p` on a `p`-adic vector. -/
private noncomputable def padicVectorReductionAddHom
    (p : Nat.Primes) (d : ℕ) :
    (Fin d → ℤ_[p]) →+ (Fin d → ZMod (p : ℕ)) where
  toFun x i := PadicInt.toZMod (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Reduction modulo `p` descends to the quotient by `p`. -/
private noncomputable def padicVectorModLinearMap
    (p : Nat.Primes) (d : ℕ) :
    ModN (Fin d → ℤ_[p]) (p : ℕ) →ₗ[ZMod (p : ℕ)]
      (Fin d → ZMod (p : ℕ)) :=
  ModN.liftEquiv'.symm
    ⟨padicVectorReductionAddHom p d, fun x => by
      ext i
      change (p : ℕ) • PadicInt.toZMod (x i) = 0
      rw [← map_nsmul]
      simp⟩

@[simp] private theorem padicVectorModLinearMap_mkQ
    (p : Nat.Primes) (d : ℕ) (x : Fin d → ℤ_[p]) :
    padicVectorModLinearMap p d (ModN.mkQ (p : ℕ) x) =
      padicVectorReductionAddHom p d x := by
  rfl

/-- Coordinatewise reduction identifies a finite `p`-adic vector modulo
`p` with the corresponding vector over `ZMod p`. -/
private theorem padicVectorModLinearMap_bijective
    (p : Nat.Primes) (d : ℕ) :
    Function.Bijective (padicVectorModLinearMap p d) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Fin d → ℤ_[p])
        ((p : ℕ) : ℤ))).mkQ_surjective a
    obtain ⟨y, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Fin d → ℤ_[p])
        ((p : ℕ) : ℤ))).mkQ_surjective b
    apply sub_eq_zero.mp
    change ModN.mkQ (p : ℕ) x - ModN.mkQ (p : ℕ) y = 0
    rw [← map_sub]
    change Submodule.Quotient.mk (x - y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hred : ∀ i, PadicInt.toZMod (x i - y i) = 0 := by
      intro i
      have hi := congrFun hab i
      change PadicInt.toZMod (x i) = PadicInt.toZMod (y i) at hi
      simpa using sub_eq_zero.mpr hi
    have hdiv (i : Fin d) : (p : ℤ_[p]) ∣ x i - y i := by
      rw [← Ideal.mem_span_singleton,
        ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod]
      exact hred i
    choose z hz using hdiv
    refine ⟨z, ?_⟩
    funext i
    change ((p : ℕ) : ℤ) • z i = x i - y i
    change ((p : ℕ) : ℤ_[p]) * z i = x i - y i
    exact (hz i).symm
  · intro x
    choose y hy using fun i =>
      ZMod.ringHom_surjective PadicInt.toZMod (x i)
    refine ⟨ModN.mkQ (p : ℕ) y, ?_⟩
    ext i
    exact hy i

private noncomputable def padicVectorModLinearEquiv
    (p : Nat.Primes) (d : ℕ) :
    ModN (Fin d → ℤ_[p]) (p : ℕ) ≃ₗ[ZMod (p : ℕ)]
      (Fin d → ZMod (p : ℕ)) :=
  LinearEquiv.ofBijective (padicVectorModLinearMap p d)
    (padicVectorModLinearMap_bijective p d)

/-- A rank-`d` free `p`-adic lattice has mod-`p` dimension `d`. -/
private theorem padicVectorMod_finrank
    (p : Nat.Primes) (d : ℕ) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Fin d → ℤ_[p]) (p : ℕ)) = d := by
  rw [(padicVectorModLinearEquiv p d).finrank_eq]
  simp

/-- The norm-one unit sphere of a nonarchimedean local field is
compact. -/
private theorem localField_unitSphere_isCompact
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsCompact {x : Units F |
      ValuativeRel.valuation F (x : F) = 1} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himage :
      Units.val '' {x : Units F |
        ValuativeRel.valuation F (x : F) = 1} =
        {x : F | (ValuativeRel.valuation F).restrict x = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (ValuativeRel.valuation F).restrict_eq_one_iff.mpr hy
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        simp at hx
      let y : Units F := Units.mk0 x hx0
      exact ⟨y,
        (ValuativeRel.valuation F).restrict_eq_one_iff.mp hx, rfl⟩
  rw [himage]
  have hO : IsCompact (NU.LCFT.RingOfIntegers F : Set F) := by
    change IsCompact {x : F | x ∈ NU.LCFT.RingOfIntegers F}
    simpa only [Subtype.range_coe_subtype] using
      (isCompact_range (continuous_subtype_val : Continuous
        ((↑) : NU.LCFT.RingOfIntegers F → F)))
  apply IsCompact.of_isClosed_subset hO
    ((ValuativeRel.valuation F).isClosed_sphere 1)
  intro x hx
  exact (Valuation.mem_integer_iff _ _).mpr
    ((ValuativeRel.valuation F).restrict_eq_one_iff.mp hx).le

/-- A closed subgroup of local units all of whose elements have `p`-power
order is finite.  Baire gives an open bounded-exponent subgroup; that
subgroup and its compact quotient are both finite. -/
private theorem pPowerTorsion_finite_of_isClosed
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F]
    (p : Nat.Primes) (P : Subgroup (Units F))
    (hclosed : IsClosed (P : Set (Units F)))
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) : Finite P := by
  have hsubset : (P : Set (Units F)) ⊆
      {x : Units F | ValuativeRel.valuation F (x : F) = 1} := by
    intro u hu
    obtain ⟨a, ha⟩ := (hP u).1 hu
    have hN : (p : ℕ) ^ a ≠ 0 := pow_ne_zero _ p.2.ne_zero
    have hv := congrArg (ValuativeRel.valuation F)
      (congrArg Units.val ha)
    change ValuativeRel.valuation F
      ((u : F) ^ ((p : ℕ) ^ a)) =
        ValuativeRel.valuation F (1 : F) at hv
    rw [map_pow, map_one] at hv
    apply pow_left_injective hN
    simpa using hv
  have hcompact : IsCompact (P : Set (Units F)) :=
    IsCompact.of_isClosed_subset (localField_unitSphere_isCompact F)
      hclosed hsubset
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hcompact
  let H (a : ℕ) : Subgroup P :=
    (powMonoidHom ((p : ℕ) ^ a) : P →* P).ker
  have hHclosed (a : ℕ) : IsClosed (H a : Set P) := by
    exact isClosed_singleton.preimage
      (continuous_id.pow ((p : ℕ) ^ a))
  have hHcover : ⋃ a : ℕ, (H a : Set P) = Set.univ := by
    ext u
    simp only [Set.mem_iUnion, SetLike.mem_coe,
      Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := (hP (u : Units F)).1 u.2
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨a, ha⟩ :=
    nonempty_interior_of_iUnion_of_closed hHclosed hHcover
  have hHopen : IsOpen (H a : Set P) := by
    obtain ⟨x, hx⟩ := ha
    exact (H a).isOpen_of_mem_nhds
      (mem_interior_iff_mem_nhds.mp hx)
  letI : Finite (P ⧸ H a) :=
    (H a).quotient_finite_of_isOpen hHopen
  have hHa : Finite (H a) := by
    let emb : H a → rootsOfUnity ((p : ℕ) ^ a) F := fun x =>
      ⟨(x.1.1 : Units F), by
        rw [mem_rootsOfUnity]
        exact congrArg (fun z : P => (z : Units F)) x.2⟩
    exact Finite.of_injective emb (fun x y h => by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact congrArg
        (fun z : rootsOfUnity ((p : ℕ) ^ a) F =>
          ((z.1 : Units F) : F)) h)
  letI : Finite (H a) := hHa
  exact Finite.of_subgroup_quotient (H a)

/-- The root-of-unity correction, in a form usable before the local
character-rank definitions below. -/
private noncomputable def primitiveRootCorrection
    (F : Type*) [Field F] (p : Nat.Primes) : ℕ := by
  classical
  exact if ∃ z : F, IsPrimitiveRoot z (p : ℕ) then 1 else 0

/-- The kernel of multiplication by `p` on a finite `p`-power root
subgroup is the full group of `p`-th roots of unity. -/
private noncomputable def pPowerKernelEquivRoots
    (F : Type*) [Field F] (p : Nat.Primes)
    (P : Subgroup (Units F))
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) :
    (nsmulAddMonoidHom (p : ℕ) :
      Additive P →+ Additive P).ker ≃ rootsOfUnity (p : ℕ) F where
  toFun x := by
    refine ⟨(x.1.toMul : P).1, ?_⟩
    rw [mem_rootsOfUnity]
    have hx := x.2
    change (p : ℕ) • x.1 = 0 at hx
    have hxP : (x.1.toMul : P) ^ (p : ℕ) = 1 := by
      rw [← toMul_nsmul, hx]
      rfl
    exact congrArg Subtype.val hxP
  invFun z := by
    let u : Units F := z.1
    have huz : u ^ (p : ℕ) = 1 :=
      (mem_rootsOfUnity (p : ℕ) u).mp z.2
    have huP : u ∈ P := (hP u).2 ⟨1, by simpa using huz⟩
    let x : Additive P := Additive.ofMul ⟨u, huP⟩
    refine ⟨x, ?_⟩
    change (p : ℕ) • x = 0
    apply Additive.toMul.injective
    change (⟨u, huP⟩ : P) ^ (p : ℕ) = 1
    apply Subtype.ext
    exact huz
  left_inv x := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- For a finite `p`-power root subgroup, reduction modulo `p` has
rank one exactly when the field contains a primitive `p`-th root. -/
private theorem pPowerMod_finrank_of_finite
    (F : Type*) [Field F] (p : Nat.Primes)
    (P : Subgroup (Units F)) [Finite P]
    (hP : ∀ u : Units F, u ∈ P ↔ ∃ a : ℕ,
      u ^ ((p : ℕ) ^ a) = 1) :
    Module.finrank (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) =
        primitiveRootCorrection F p := by
  classical
  unfold primitiveRootCorrection
  let f : Additive P →+ Additive P :=
    nsmulAddMonoidHom (p : ℕ)
  let H : AddSubgroup (Additive P) :=
    (LinearMap.range (LinearMap.lsmul ℤ (Additive P)
      (((p : ℕ) : ℤ)))).toAddSubgroup
  letI : Finite (ModN (Additive P) (p : ℕ)) := Quotient.finite _
  letI : Module.Finite (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) := Module.Finite.of_finite
  have hH : H = f.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [f]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [f]⟩
  have hcardquot : Nat.card (ModN (Additive P) (p : ℕ)) =
      Nat.card f.ker := by
    calc
      Nat.card (ModN (Additive P) (p : ℕ)) = H.index := by
        exact (AddSubgroup.index_eq_card H).symm
      _ = f.range.index := by rw [hH]
      _ = Nat.card f.ker := AddSubgroup.index_range
  have hcardker : Nat.card f.ker =
      if ∃ z : F, IsPrimitiveRoot z (p : ℕ)
      then (p : ℕ) else 1 := by
    rw [Nat.card_congr (pPowerKernelEquivRoots F p P hP)]
    split_ifs with h
    · exact h.choose_spec.card_rootsOfUnity
    · letI : Subsingleton (rootsOfUnity (p : ℕ) F) :=
        ⟨fun x y => by
          have hxpow : (x.1 : Units F) ^ (p : ℕ) = 1 :=
            (mem_rootsOfUnity (p : ℕ) x.1).mp x.2
          have hypow : (y.1 : Units F) ^ (p : ℕ) = 1 :=
            (mem_rootsOfUnity (p : ℕ) y.1).mp y.2
          have hone (z : rootsOfUnity (p : ℕ) F)
              (hzpow : (z.1 : Units F) ^ (p : ℕ) = 1) : z = 1 := by
            have hdvd : orderOf z.1 ∣ (p : ℕ) :=
              orderOf_dvd_of_pow_eq_one hzpow
            rcases (Nat.dvd_prime p.2).mp hdvd with horder | horder
            · apply Subtype.ext
              exact orderOf_eq_one_iff.mp horder
            · exfalso
              apply h
              have hzprim : IsPrimitiveRoot z.1 (p : ℕ) := by
                simpa [horder] using IsPrimitiveRoot.orderOf z.1
              exact ⟨((z.1 : Units F) : F),
                IsPrimitiveRoot.coe_units_iff.mpr hzprim⟩
          rw [hone x hxpow, hone y hypow]⟩
      exact Nat.card_unique
  have hvcard : (p : ℕ) ^ Module.finrank (ZMod (p : ℕ))
      (ModN (Additive P) (p : ℕ)) = Nat.card f.ker := by
    rw [← hcardquot]
    simpa using (Module.natCard_eq_pow_finrank
      (K := ZMod (p : ℕ))
      (V := ModN (Additive P) (p : ℕ))).symm
  rw [hcardker] at hvcard
  split_ifs at hvcard ⊢
  · apply Nat.pow_right_injective p.2.two_le
    simpa using hvcard
  · apply Nat.pow_right_injective p.2.two_le
    simpa using hvcard

/-- In the product decomposition, the `p`-power torsion factor is a
closed subgroup.  The other three coordinates of a `p`-power torsion
unit vanish because they are respectively torsion-free, prime-to-`p`, and
torsion-free. -/
private theorem localUnitDecomposition_pPowerTorsion_isClosed
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    IsClosed (units.pPowerTorsion :
      Set (Units (v.adicCompletion K))) := by
  let F := v.adicCompletion K
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top
      (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let e := units.productEquiv
  have hcoords (u : Units F) :
      u ∈ units.pPowerTorsion ↔
        (e u).1 = 1 ∧ (e u).2.1 = 1 ∧ (e u).2.2.2 = 1 := by
    constructor
    · intro hu
      obtain ⟨a, ha⟩ :=
        (units.pPowerTorsion_spec u).1 hu
      let N : ℕ := (residuePrime v : ℕ) ^ a
      have hN : N ≠ 0 := pow_ne_zero _ (residuePrime v).2.ne_zero
      have hpow : (e u) ^ N = 1 := by
        rw [← map_pow, ha, map_one]
      have hvalpow : (e u).1 ^ N = 1 := by
        exact congrArg (fun x => x.1) hpow
      have hteichpow : (e u).2.1 ^ N = 1 := by
        exact congrArg (fun x => x.2.1) hpow
      have hfreepow : (e u).2.2.2 ^ N = 1 := by
        exact congrArg (fun x => x.2.2.2) hpow
      refine ⟨?_, ?_, ?_⟩
      · apply units.valuationEquiv.injective
        apply pow_left_injective hN
        simpa using congrArg units.valuationEquiv hvalpow
      · apply units.teichmullerEquiv.injective
        have hzpow :
            (units.teichmullerEquiv (e u).2.1) ^ N = 1 := by
          simpa using congrArg units.teichmullerEquiv hteichpow
        simpa using multiplicativeZMod_pow_eq_one_of_coprime
          N (NU.Chebotarev.PrimeIdeal.norm v - 1)
          ((residueCharacteristic_coprime_norm_sub_one v).pow_left a)
          (units.teichmullerEquiv (e u).2.1) hzpow
      · apply units.freePrincipalUnitsEquiv.injective
        apply pow_left_injective hN
        simpa using congrArg units.freePrincipalUnitsEquiv hfreepow
    · rintro ⟨hval, hteich, hfree⟩
      let cp : units.pPowerTorsion := (e u).2.2.1
      obtain ⟨a, ha⟩ :=
        (units.pPowerTorsion_spec (cp : Units F)).1 cp.2
      apply (units.pPowerTorsion_spec u).2
      refine ⟨a, ?_⟩
      apply e.injective
      rw [map_pow, map_one]
      apply Prod.ext
      · simpa [hval]
      · apply Prod.ext
        · simpa [hteich]
        · apply Prod.ext
          · apply Subtype.ext
            exact ha
          · simpa [hfree]
  have hset : (units.pPowerTorsion : Set (Units F)) =
      {u | (e u).1 = 1 ∧ (e u).2.1 = 1 ∧
        (e u).2.2.2 = 1} := by
    ext u
    exact hcoords u
  rw [hset]
  have he : Continuous e := e.continuous
  exact (isClosed_eq (continuous_fst.comp he)
    continuous_const).inter
      ((isClosed_eq (continuous_fst.comp
        (continuous_snd.comp he)) continuous_const).inter
      (isClosed_eq (continuous_snd.comp
        (continuous_snd.comp
          (continuous_snd.comp he))) continuous_const))

/-- The `p`-power torsion factor in a local-unit decomposition is
finite. -/
private theorem localUnitDecomposition_pPowerTorsion_finite
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Finite units.pPowerTorsion := by
  let F := v.adicCompletion K
  letI : CharZero F := charZero_of_injective_algebraMap
    (algebraMap K F).injective
  letI : ValuativeRel F := completionValuativeRel v
  letI : IsNonarchimedeanLocalField F := completionIsLocalField v
  exact pPowerTorsion_finite_of_isClosed F (residuePrime v)
    units.pPowerTorsion
    (localUnitDecomposition_pPowerTorsion_isClosed v units)
    units.pPowerTorsion_spec

/-- The `p`-power torsion factor contributes precisely the root-of-unity
correction modulo `p`. -/
private theorem localUnitDecomposition_pPowerTorsionMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Module.finrank (ZMod (residuePrime v : ℕ))
      (ModN (Additive units.pPowerTorsion)
        (residuePrime v : ℕ)) =
      primitiveRootCorrection (v.adicCompletion K) (residuePrime v) := by
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v units
  exact pPowerMod_finrank_of_finite
    (v.adicCompletion K) (residuePrime v)
    units.pPowerTorsion units.pPowerTorsion_spec

/-- The valuation factor contributes one dimension modulo the residue
prime. -/
private theorem localUnitDecomposition_valuationMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Module.finrank (ZMod (residuePrime v : ℕ))
      (ModN (Additive units.valuationFactor)
        (residuePrime v : ℕ)) = 1 := by
  rw [(modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    units.valuationEquiv.toMulEquiv.toAdditive).finrank_eq]
  exact additiveMultiplicativeIntMod_finrank (residuePrime v)

/-- The prime-to-`p` Teichmüller factor vanishes modulo the residue
prime. -/
private theorem localUnitDecomposition_teichmullerMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Module.finrank (ZMod (residuePrime v : ℕ))
      (ModN (Additive units.teichmullerFactor)
        (residuePrime v : ℕ)) = 0 := by
  have hnorm : 1 < NU.Chebotarev.PrimeIdeal.norm v := by
    have hne0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
      change Ideal.absNorm v.asIdeal ≠ 0
      exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
    have hne1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
      change Ideal.absNorm v.asIdeal ≠ 1
      exact fun h => v.isMaximal.ne_top
        (Ideal.absNorm_eq_one_iff.mp h)
    omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnorm).ne'⟩
  rw [(modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    units.teichmullerEquiv.toMulEquiv.toAdditive).finrank_eq]
  apply modN_finrank_zero_of_divisible
  exact additiveMultiplicativeZMod_is_nDivisible_of_coprime
    (residuePrime v : ℕ)
    (NU.Chebotarev.PrimeIdeal.norm v - 1)
    (residueCharacteristic_coprime_norm_sub_one v)

/-- The free principal-unit factor contributes the local degree modulo the
residue prime. -/
private theorem localUnitDecomposition_freeMod_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Module.finrank (ZMod (residuePrime v : ℕ))
      (ModN (Additive units.freePrincipalUnits)
        (residuePrime v : ℕ)) = finitePlaceLocalDegree v := by
  rw [(modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    units.freePrincipalUnitsEquiv.toMulEquiv.toAdditive).finrank_eq]
  exact padicVectorMod_finrank
    (residuePrime v) (finitePlaceLocalDegree v)

/-- The local-unit product decomposition descends to the corresponding
four-factor decomposition modulo the residue prime. -/
private noncomputable def localUnitDecomposition_kummerQuotientLinearEquiv
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    NU.LocalTheory.KummerQuotient
        (v.adicCompletion K) (residuePrime v : ℕ) ≃ₗ[
          ZMod (residuePrime v : ℕ)]
      ModN (Additive units.valuationFactor) (residuePrime v : ℕ) ×
      ModN (Additive units.teichmullerFactor) (residuePrime v : ℕ) ×
      ModN (Additive units.pPowerTorsion) (residuePrime v : ℕ) ×
      ModN (Additive units.freePrincipalUnits) (residuePrime v : ℕ) :=
  (modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    (units.productEquiv.toMulEquiv.toAdditive.trans
      additiveProdFourAddEquiv)).trans
    (modNFourLinearEquiv (residuePrime v : ℕ))

/-- Exact mod-`p` rank of the multiplicative group supplied by the local
unit decomposition. -/
private theorem localUnitDecomposition_kummerQuotient_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    Module.finrank (ZMod (residuePrime v : ℕ))
      (NU.LocalTheory.KummerQuotient
        (v.adicCompletion K) (residuePrime v : ℕ)) =
      1 + finitePlaceLocalDegree v +
        primitiveRootCorrection (v.adicCompletion K) (residuePrime v) := by
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top
      (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let k := ZMod (residuePrime v : ℕ)
  let V := ModN (Additive units.valuationFactor) (residuePrime v : ℕ)
  let T := ModN (Additive units.teichmullerFactor) (residuePrime v : ℕ)
  let P := ModN (Additive units.pPowerTorsion) (residuePrime v : ℕ)
  let L := ModN (Additive units.freePrincipalUnits) (residuePrime v : ℕ)
  letI : Finite units.pPowerTorsion :=
    localUnitDecomposition_pPowerTorsion_finite v units
  letI : Finite units.teichmullerFactor := Finite.of_equiv
    (Multiplicative
      (ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)))
    units.teichmullerEquiv.toEquiv.symm
  let eV := (modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    units.valuationEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
        (AddEquiv.additiveMultiplicative ℤ))
  letI : Module.Finite k V := Module.Finite.equiv eV.symm
  letI : Finite T := Quotient.finite _
  letI : Module.Finite k T := Module.Finite.of_finite
  letI : Finite P := Quotient.finite _
  letI : Module.Finite k P := Module.Finite.of_finite
  let d := finitePlaceLocalDegree v
  let eL := ((modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
    units.freePrincipalUnitsEquiv.toMulEquiv.toAdditive).trans
      (modNLinearEquivOfAddEquiv (residuePrime v : ℕ)
        (AddEquiv.additiveMultiplicative
          (Fin d → ℤ_[residuePrime v])))).trans
      (padicVectorModLinearEquiv (residuePrime v) d)
  letI : Module.Finite k L := Module.Finite.equiv eL.symm
  rw [(localUnitDecomposition_kummerQuotientLinearEquiv
    v units).finrank_eq]
  change Module.finrank k (V × T × P × L) = _
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    localUnitDecomposition_valuationMod_finrank v units,
    localUnitDecomposition_teichmullerMod_finrank v units,
    localUnitDecomposition_pPowerTorsionMod_finrank v units,
    localUnitDecomposition_freeMod_finrank v units]
  omega

/-- The multiplicative quotient of a local field modulo an away-from-`p`
prime is generated by its valuation and Teichmüller coordinates. -/
private theorem localUnitDecomposition_kummerQuotient_finrank_le_two
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v)
    (ell : Nat.Primes) (hne : ell ≠ residuePrime v) :
    Module.finrank (ZMod (ell : ℕ))
      (NU.LocalTheory.KummerQuotient (v.adicCompletion K) (ell : ℕ)) ≤ 2 := by
  let F := v.adicCompletion K
  have hnorm0 : NU.Chebotarev.PrimeIdeal.norm v ≠ 0 := by
    change Ideal.absNorm v.asIdeal ≠ 0
    exact (Ideal.absNorm_ne_zero_iff v.asIdeal).2 inferInstance
  have hnorm1 : NU.Chebotarev.PrimeIdeal.norm v ≠ 1 := by
    change Ideal.absNorm v.asIdeal ≠ 1
    exact fun h => v.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hnormgt : 1 < NU.Chebotarev.PrimeIdeal.norm v := by omega
  letI : NeZero (NU.Chebotarev.PrimeIdeal.norm v - 1) :=
    ⟨(Nat.sub_pos_of_lt hnormgt).ne'⟩
  let v0 : units.valuationFactor :=
    units.valuationEquiv.symm (Multiplicative.ofAdd (1 : ℤ))
  let t0 : units.teichmullerFactor :=
    units.teichmullerEquiv.symm
      (Multiplicative.ofAdd
        (1 : ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)))
  let vu : Units F := units.productEquiv.symm (v0, 1, 1, 1)
  let tu : Units F := units.productEquiv.symm (1, t0, 1, 1)
  let xv := NU.LocalTheory.kummerQuotientClass (ell : ℕ) vu
  let xt := NU.LocalTheory.kummerQuotientClass (ell : ℕ) tu
  let gens : Fin 2 → NU.LocalTheory.KummerQuotient F (ell : ℕ) :=
    ![xv, xt]
  have hspan : Submodule.span (ZMod (ell : ℕ)) (Set.range gens) = ⊤ := by
    apply top_unique
    intro q hq
    obtain ⟨u, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ (Additive (Units F))
        ((ell : ℕ) : ℤ))).mkQ_surjective q
    cases u with
    | ofMul u =>
      let c := units.productEquiv u
      let cv : units.valuationFactor := c.1
      let ct : units.teichmullerFactor := c.2.1
      let cp : units.pPowerTorsion := c.2.2.1
      let cf : units.freePrincipalUnits := c.2.2.2
      have hcp : ∃ a : ℕ,
          cp ^ ((residuePrime v : ℕ) ^ a) = 1 := by
        obtain ⟨a, ha⟩ :=
          (units.pPowerTorsion_spec (cp : Units F)).1 cp.property
        refine ⟨a, ?_⟩
        apply Subtype.ext
        exact ha
      obtain ⟨rp, hrp⟩ := primePowerTorsion_is_primeDivisible
        (residuePrime v) ell hne cp hcp
      obtain ⟨rfImage, hrfImage⟩ := padicVector_is_primeDivisible
        (residuePrime v) ell hne (finitePlaceLocalDegree v)
        (units.freePrincipalUnitsEquiv cf)
      let rf : units.freePrincipalUnits :=
        units.freePrincipalUnitsEquiv.symm rfImage
      have hrf : rf ^ (ell : ℕ) = cf := by
        apply units.freePrincipalUnitsEquiv.injective
        simpa [rf] using hrfImage
      let nv : ℤ := Multiplicative.toAdd (units.valuationEquiv cv)
      have hcv : cv = v0 ^ nv := by
        apply units.valuationEquiv.injective
        apply Multiplicative.toAdd.injective
        simp [v0, nv]
      let nt : ℕ :=
        (Multiplicative.toAdd (units.teichmullerEquiv ct)).val
      have hct : ct = t0 ^ nt := by
        apply units.teichmullerEquiv.injective
        rw [map_pow]
        have ht0 : units.teichmullerEquiv t0 =
            Multiplicative.ofAdd
              (1 : ZMod (NU.Chebotarev.PrimeIdeal.norm v - 1)) := by
          exact units.teichmullerEquiv.apply_symm_apply _
        rw [ht0]
        apply Multiplicative.toAdd.injective
        simpa [nt] using (ZMod.natCast_zmod_val
          (Multiplicative.toAdd (units.teichmullerEquiv ct))).symm
      let ru : Units F := units.productEquiv.symm (1, 1, rp, rf)
      have hu : u = vu ^ nv * tu ^ nt * ru ^ (ell : ℕ) := by
        apply units.productEquiv.injective
        rw [map_mul, map_mul, map_zpow, map_pow]
        have hvu : units.productEquiv vu = (v0, 1, 1, 1) := by
          simp [vu]
        have htu : units.productEquiv tu = (1, t0, 1, 1) := by
          simp [tu]
        have hru : units.productEquiv ru = (1, 1, rp, rf) := by
          simp [ru]
        have hruPow : units.productEquiv (ru ^ (ell : ℕ)) =
            (1, 1, rp, rf) ^ (ell : ℕ) := by
          rw [map_pow, hru]
        rw [hvu, htu, hruPow]
        change c = _
        ext <;> simp [cv, ct, cp, cf, hcv, hct, hrp, hrf]
      let S := Submodule.span (ZMod (ell : ℕ)) (Set.range gens)
      have hv : xv ∈ S := by
        apply Submodule.subset_span
        exact ⟨0, by simp [gens]⟩
      have ht : xt ∈ S := by
        apply Submodule.subset_span
        exact ⟨1, by simp [gens]⟩
      change NU.LocalTheory.kummerQuotientClass (ell : ℕ) u ∈ S
      rw [hu]
      change ModN.mkQ (ell : ℕ)
        (nv • Additive.ofMul vu + nt • Additive.ofMul tu +
          (ell : ℕ) • Additive.ofMul ru) ∈ S
      rw [map_add, map_add, map_zsmul, map_nsmul, map_nsmul]
      have hz : (ell : ℕ) •
          ModN.mkQ (ell : ℕ) (Additive.ofMul ru) = 0 := by
        calc
          (ell : ℕ) • ModN.mkQ (ell : ℕ) (Additive.ofMul ru) =
              ((ell : ℕ) : ZMod (ell : ℕ)) •
                ModN.mkQ (ell : ℕ) (Additive.ofMul ru) :=
            (Nat.cast_smul_eq_nsmul (ZMod (ell : ℕ)) (ell : ℕ)
              (ModN.mkQ (ell : ℕ) (Additive.ofMul ru))).symm
          _ = 0 := by simp
      rw [hz]
      exact S.add_mem (S.add_mem
        (S.toAddSubgroup.zsmul_mem hv nv)
        (S.toAddSubgroup.nsmul_mem ht nt)) S.zero_mem
  exact finrank_le_of_span_eq_top hspan

/-- **Residual for `ambientKummerOpenSubgroupTransport`.**  Construct the
continuous `ℤ_p`-module structure on the full principal-unit group of a
number-field completion from the cofinal deep-unit filtration, identify its
torsion with the `p`-power roots of unity, and prove that the torsion-free
quotient has rank `[K_v : ℚ_p]`.  The standalone
`deepUnitModule_localUnitDecomposition` supplies precisely this
filtration-to-module package. -/
private theorem ambientKummerPrincipalUnitDecomposition_residual
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Nonempty (LocalUnitDecompositionData v) := by
  exact
    NU.NeukirchUchida.Bridges.deepUnitModule_localUnitDecomposition
      v _ rfl _ rfl

/-- The complete-PID classification step for principal units: the cofinal
deep-unit lattice has finite torsion and a finite-rank torsion-free quotient,
which is topologically free over `ℤ_p`. -/
private theorem localUnitDecomposition_completePIDClassification
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Nonempty (LocalUnitDecompositionData v) := by
  exact ambientKummerPrincipalUnitDecomposition_residual v

/-- Resistant branch of `lem:units`: turn the complete deep-unit
filtration into the finite-torsion/free `Z_p` splitting, after the valuation
and Teichmüller factors have been removed. -/
private theorem localUnitDecomposition_torsionLatticeSplit
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Nonempty (LocalUnitDecompositionData v) := by
  exact localUnitDecomposition_completePIDClassification v

/-- **Arithmetic obligation, Blueprint `lem:units`.**  Derive the displayed
unit decomposition from the cofinal deep-unit filtration in
`NU.LCFT.FundamentalClass.DeepUnits`: quotient prime-to-`p` Teichmüller
torsion first, then split finite `p`-power torsion from the free
`Z_p`-lattice. -/
private theorem localUnitDecomposition_from_deepUnits
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    Nonempty (LocalUnitDecompositionData v) := by
  exact localUnitDecomposition_torsionLatticeSplit v

/-- Dimension of continuous additive mod-`ell` characters. -/
private noncomputable def continuousCharacterRank
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ell : Nat.Primes) : ℕ := by
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  exact Module.finrank (ZMod (ell : ℕ))
    (NU.LocalTheory.ContinuousCharacter G (ell : ℕ))

/-- Continuous mod-`ell` character rank is invariant under a
topological group equivalence. -/
private theorem continuousCharacterRank_equiv
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (ell : Nat.Primes) (e : G ≃ₜ* H) :
    continuousCharacterRank G ell = continuousCharacterRank H ell := by
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  exact (PacketTransport.pullCharacterLinearEquiv
    (ell : ℕ) e).finrank_eq.symm

/-- The two presentations of the absolute local degree agree
definitionally. -/
private theorem finitePlaceLocalDegree_ambientFinitePlace
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    finitePlaceLocalDegree (ambientFinitePlace P) = ambientLocalDegree P := by
  rfl

/-- The root-of-unity correction in Blueprint `lem:dim-at`. -/
private noncomputable def completionRootCorrection
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) : ℕ :=
  primitiveRootCorrection (v.adicCompletion K) (residuePrime v)

/-- Resistant branch of `lem:dim-at`: the Maschke/normal-basis
calculation after quotienting `p`-power torsion and adjoining `mu_p`. -/
private theorem pKummerDimension_maschkeNormalBasis
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    continuousCharacterRank
        (Field.absoluteGaloisGroup (v.adicCompletion K)) (residuePrime v) =
      1 + finitePlaceLocalDegree v + completionRootCorrection v := by
  simpa [continuousCharacterRank, completionRootCorrection,
    finitePlaceLocalDegree,
    NU.NeukirchUchida.Bridges.finitePlaceLocalDegree,
    primitiveRootCorrection,
    NU.NeukirchUchida.Bridges.primitiveRootCorrection] using
      (NU.NeukirchUchida.Bridges.completionCharacterRank_maschkeDescent
        v (residuePrime v) rfl units)

/-- **Arithmetic obligation, Blueprint `lem:dim-at`.**  Kummer theory,
inflation--restriction and the three-summand Delta-decomposition give
`1 + n + delta`.  The proof must quotient `mu_{p^infty}` before reducing
modulo `p`, then use Maschke, normal basis and integral character
idempotents. -/
private theorem pKummerDimension_at_completion
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v) :
    continuousCharacterRank
        (Field.absoluteGaloisGroup (v.adicCompletion K)) (residuePrime v) =
      1 + finitePlaceLocalDegree v + completionRootCorrection v := by
  exact pKummerDimension_maschkeNormalBasis v units

/-- The root-absent branch of away-prime Kummer theory: after adjoining
`mu_ell`, restriction is injective (the index divides `ell - 1`) and the
cyclotomic eigenspace has dimension at most the two local multiplicative
lines. -/
private theorem kummerDimension_away_without_roots
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v)
    (ell : Nat.Primes) (hne : ell ≠ residuePrime v)
    (hroots : ¬ ∃ zeta : v.adicCompletion K,
      IsPrimitiveRoot zeta (ell : ℕ)) :
    continuousCharacterRank
      (Field.absoluteGaloisGroup (v.adicCompletion K)) ell ≤ 2 := by
  classical
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  let F := v.adicCompletion K
  letI : CharZero F :=
    charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : ValuativeRel F := completionValuativeRel v
  let hF : IsNonarchimedeanLocalField F := completionIsLocalField v
  letI : IsNonarchimedeanLocalField F := hF
  let E := localCyclotomicExtension F ell
  obtain ⟨vE, tE, hE, hExt⟩ :=
    finiteExtension_localFieldStructure F E
  letI : ValuativeRel E := vE
  letI : TopologicalSpace E := tE
  letI : IsNonarchimedeanLocalField E := hE
  letI : ValuativeExtension F E := hExt
  have hcharF : ringChar (NU.LCFT.LocalResidueField F) ≠
      (ell : ℕ) := by
    rw [completion_residueCharacteristic_eq v]
    intro heq
    apply hne
    apply Subtype.ext
    exact heq.symm
  have hcharE : ringChar (NU.LCFT.LocalResidueField E) ≠
      (ell : ℕ) := by
    rw [← finiteValuativeExtension_residueChar F E]
    exact hcharF
  have hindex : E.fixingSubgroup.index < (ell : ℕ) := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index E]
    exact localCyclotomicExtension_finrank_lt F ell
  let zeta : E := localCyclotomicRootInExtension F ell
  have hzeta : IsPrimitiveRoot zeta (ell : ℕ) :=
    localCyclotomicRootInExtension_spec F ell
  letI : Module.Finite (ZMod (ell : ℕ))
      (NU.LocalTheory.KummerQuotient E (ell : ℕ)) :=
    localField_tameKummerQuotient_moduleFinite E ell hcharE
  letI : Module.Finite (ZMod (ell : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup E) (ell : ℕ)) :=
    Module.Finite.equiv (NU.LocalTheory.kummerEquiv zeta hzeta)
  change Module.finrank (ZMod (ell : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup F) (ell : ℕ)) ≤ 2
  calc
    Module.finrank (ZMod (ell : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup F) (ell : ℕ)) ≤
      Module.finrank (ZMod (ell : ℕ))
        (NU.LocalTheory.ContinuousCharacter
          (Field.absoluteGaloisGroup E) (ell : ℕ)) :=
      LinearMap.finrank_le_finrank_of_injective
        (localCyclotomic_characterPull_injective F ell hindex)
    _ = Module.finrank (ZMod (ell : ℕ))
        (NU.LocalTheory.KummerQuotient E (ell : ℕ)) :=
      (NU.LocalTheory.kummerEquiv zeta hzeta).finrank_eq.symm
    _ ≤ 2 := localField_tameKummerQuotient_finrank_le_two E ell hcharE

/-- **Arithmetic obligation, Blueprint `lem:dim-away`.**  Away from the
residue prime the principal units are `ell`-divisible, leaving at most the
valuation and residue-unit lines. -/
private theorem kummerDimension_away_from_completion
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K)
    (units : LocalUnitDecompositionData v)
    (ell : Nat.Primes) (hne : ell ≠ residuePrime v) :
    continuousCharacterRank
      (Field.absoluteGaloisGroup (v.adicCompletion K)) ell ≤ 2 := by
  classical
  by_cases hroots : ∃ zeta : v.adicCompletion K,
      IsPrimitiveRoot zeta (ell : ℕ)
  · obtain ⟨zeta, hzeta⟩ := hroots
    change Module.finrank (ZMod (ell : ℕ))
      (NU.LocalTheory.ContinuousCharacter
        (Field.absoluteGaloisGroup (v.adicCompletion K)) (ell : ℕ)) ≤ 2
    rw [← (NU.LocalTheory.kummerEquiv zeta hzeta).finrank_eq]
    exact localUnitDecomposition_kummerQuotient_finrank_le_two
      v units ell hne
  · exact kummerDimension_away_without_roots v units ell hne hroots

/-- The common bracket data used in the formal part of Blueprint `prop:p-n`.
The shared number is the transported character dimension and `index` is the
common open-subgroup index. -/
private structure KummerBracketComparison (n₁ n₂ : ℕ) where
  index : ℕ
  dimension : ℕ
  index_ge_three : 3 ≤ index
  source_lower : index * n₁ ≤ dimension
  source_upper : dimension ≤ index * n₁ + 2
  target_lower : index * n₂ ≤ dimension
  target_upper : dimension ≤ index * n₂ + 2

/-- Exact rank data attached to one transported open subgroup.  The two
correction terms are the possible local `p`-power root-of-unity lines. -/
private structure KummerOpenSubgroupDimensionData (n₁ n₂ : ℕ) where
  index : ℕ
  dimension : ℕ
  sourceCorrection : ℕ
  targetCorrection : ℕ
  index_ge_three : 3 ≤ index
  sourceCorrection_le_one : sourceCorrection ≤ 1
  targetCorrection_le_one : targetCorrection ≤ 1
  source_dimension : dimension = 1 + index * n₁ + sourceCorrection
  target_dimension : dimension = 1 + index * n₂ + targetCorrection

/-- The exact local Kummer rank formula gives the two width-two brackets
used in `prop:p-n`. -/
private def KummerOpenSubgroupDimensionData.toBracketComparison
    {n₁ n₂ : ℕ} (D : KummerOpenSubgroupDimensionData n₁ n₂) :
    KummerBracketComparison n₁ n₂ where
  index := D.index
  dimension := D.dimension
  index_ge_three := D.index_ge_three
  source_lower := by
    rw [D.source_dimension]
    omega
  source_upper := by
    rw [D.source_dimension]
    have := D.sourceCorrection_le_one
    omega
  target_lower := by
    rw [D.target_dimension]
    omega
  target_upper := by
    rw [D.target_dimension]
    have := D.targetCorrection_le_one
    omega

/-- The root-of-unity correction in the completion rank formula is either
zero or one. -/
private theorem completionRootCorrection_le_one
    {K : Type*} [Field K] [NumberField K]
    (v : NU.LocalTheory.FinitePlace K) :
    completionRootCorrection v ≤ 1 := by
  classical
  unfold completionRootCorrection primitiveRootCorrection
  split_ifs <;> omega

/-- Formal bracket-uniqueness step in Blueprint `prop:p-n`, given the two
Kummer dimension estimates and a common index at least three. -/
private theorem intrinsic_p_n_from_dimensions
    {p₁ p₂ : Nat.Primes} {n₁ n₂ : ℕ}
    (hp : p₁ = p₂) (C : KummerBracketComparison n₁ n₂) :
    p₁ = p₂ ∧ n₁ = n₂ := by
  refine ⟨hp, ?_⟩
  have hindex := C.index_ge_three
  rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
  · have hstep : C.index * n₁ + C.index ≤ C.index * n₂ := by
      simpa [Nat.mul_add] using
        Nat.mul_le_mul_left C.index (Nat.succ_le_iff.mpr hlt)
    have hcross : C.index * n₂ ≤ C.index * n₁ + 2 :=
      C.target_lower.trans C.source_upper
    omega
  · exact heq
  · have hstep : C.index * n₂ + C.index ≤ C.index * n₁ := by
      simpa [Nat.mul_add] using
        Nat.mul_le_mul_left C.index (Nat.succ_le_iff.mpr hgt)
    have hcross : C.index * n₁ ≤ C.index * n₂ + 2 :=
      C.source_lower.trans C.target_upper
    omega

/-! ### Order divisibility and the profinite-integer bridge -/

open Polynomial
open scoped KummerExtension

/-- Multiplicative order of an integer modulo a prime. -/
private noncomputable def residueMultiplicativeOrder
    (q : ℕ) (ell : Nat.Primes) : ℕ :=
  orderOf (q : ZMod (ell : ℕ))

/-- If a nonzero residue is not a `lambda`-th power modulo a prime `ell`,
then the `lambda`-adic valuations of its order and of `ell - 1` agree.  This
is the cyclic-group arithmetic core of the Kummer argument. -/
private theorem factorization_orderOf_eq_of_not_primePower
    (ell lambda : Nat.Primes) (b : ℕ)
    (hb : ¬(ell : ℕ) ∣ b)
    (hnonpower : ¬ ∃ x : ZMod (ell : ℕ),
      x ^ (lambda : ℕ) = (b : ZMod (ell : ℕ))) :
    (residueMultiplicativeOrder b ell).factorization (lambda : ℕ) =
      ((ell : ℕ) - 1).factorization (lambda : ℕ) := by
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  let u : (ZMod (ell : ℕ))ˣ :=
    Units.mk0 (b : ZMod (ell : ℕ)) hb0
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator
    (α := (ZMod (ell : ℕ))ˣ)
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff u g).mp (hg u)
  have hla : ¬(lambda : ℕ) ∣ a := by
    intro hadiv
    obtain ⟨k, rfl⟩ := hadiv
    apply hnonpower
    refine ⟨((g ^ k : (ZMod (ell : ℕ))ˣ) : ZMod (ell : ℕ)), ?_⟩
    change (((g ^ k) ^ (lambda : ℕ) : (ZMod (ell : ℕ))ˣ) :
      ZMod (ell : ℕ)) = (u : ZMod (ell : ℕ))
    congr 1
    calc
      (g ^ k) ^ (lambda : ℕ) = g ^ (k * (lambda : ℕ)) := by
        rw [pow_mul]
      _ = g ^ ((lambda : ℕ) * k) := by rw [mul_comm]
      _ = u := ha
  have hgorder : orderOf g = (ell : ℕ) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hg,
      Nat.card_eq_fintype_card, ZMod.card_units]
  have hgcd : (((ell : ℕ) - 1).gcd a).factorization
      (lambda : ℕ) = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hla ((Nat.dvd_gcd_iff.mp hdvd).2)
  have hfac := congrArg (fun f : ℕ →₀ ℕ => f (lambda : ℕ))
    (Nat.factorization_div
      (Nat.gcd_dvd_left ((ell : ℕ) - 1) a))
  change (((ell : ℕ) - 1) / (((ell : ℕ) - 1).gcd a)).factorization
      (lambda : ℕ) =
    ((ell : ℕ) - 1).factorization (lambda : ℕ) -
      (((ell : ℕ) - 1).gcd a).factorization (lambda : ℕ) at hfac
  change (orderOf (u : ZMod (ell : ℕ))).factorization
    (lambda : ℕ) = _
  rw [orderOf_units, ← ha, orderOf_pow, hgorder]
  exact hfac.trans (by rw [hgcd, Nat.sub_zero])

/-- A rational `n`-th root of a natural number is itself integral, hence its
absolute value supplies a natural `n`-th root. -/
private theorem exists_nat_pow_of_rat_pow
    {n q : ℕ} (hn : n ≠ 0) (c : ℚ) (hc : c ^ n = q) :
    ∃ d : ℕ, d ^ n = q := by
  have hcint : IsIntegral ℤ c := by
    refine ⟨X ^ n - C (q : ℤ), monic_X_pow_sub_C _ hn, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr hc
  let z : ℤ := Rat.ringOfIntegersEquiv ⟨c, hcint⟩
  have hz : (z : ℚ) = c :=
    Rat.ringOfIntegersEquiv_apply_coe ⟨c, hcint⟩
  refine ⟨z.natAbs, ?_⟩
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_pow]
  have habs : ((z.natAbs : ℕ) : ℚ) = |(z : ℚ)| := by
    calc
      ((z.natAbs : ℕ) : ℚ) = ((|z| : ℤ) : ℚ) := by
        have h := congrArg (fun x : ℤ => (x : ℚ))
          (Int.natCast_natAbs z)
        norm_num at h ⊢
      _ = |(z : ℚ)| := Int.cast_abs
  rw [habs, ← abs_pow, hz, hc]
  simp

/-- Raising an element of a finite group to `lambda ^ h` lowers the
`lambda`-adic valuation of its order by at most `h`. -/
private theorem factorization_orderOf_pow_ge_sub
    {G : Type*} [Group G] [Finite G]
    (x : G) (lambda : Nat.Primes) (h : ℕ) :
    (orderOf x).factorization (lambda : ℕ) - h ≤
      (orderOf (x ^ ((lambda : ℕ) ^ h))).factorization
        (lambda : ℕ) := by
  let d := orderOf x
  let k := (lambda : ℕ) ^ h
  have hd0 : d ≠ 0 := (orderOf_pos x).ne'
  have hk0 : k ≠ 0 := pow_ne_zero _ lambda.2.ne_zero
  have hgcd0 : d.gcd k ≠ 0 := Nat.gcd_ne_zero_left hd0
  have hfac := congrArg (fun f : ℕ →₀ ℕ => f (lambda : ℕ))
    (Nat.factorization_div (Nat.gcd_dvd_left d k))
  change (d / d.gcd k).factorization (lambda : ℕ) =
    d.factorization (lambda : ℕ) -
      (d.gcd k).factorization (lambda : ℕ) at hfac
  have hfac_le : (d.gcd k).factorization (lambda : ℕ) ≤ h := by
    have hle : (d.gcd k).factorization ≤ k.factorization :=
      (Nat.factorization_le_iff_dvd hgcd0 hk0).2
        (Nat.gcd_dvd_right d k)
    calc
      (d.gcd k).factorization (lambda : ℕ) ≤
          k.factorization (lambda : ℕ) := hle (lambda : ℕ)
      _ = h := by
        simp [k, Nat.factorization_pow, lambda.2.factorization]
  rw [orderOf_pow]
  change d.factorization (lambda : ℕ) - h ≤
    (d / d.gcd k).factorization (lambda : ℕ)
  rw [hfac]
  omega

/-- The finite-group order bound, transferred to a nonzero residue modulo a
prime. -/
private theorem factorization_residueOrder_pow_ge_sub
    (ell lambda : Nat.Primes) (b h : ℕ)
    (hb : ¬(ell : ℕ) ∣ b) :
    (residueMultiplicativeOrder b ell).factorization (lambda : ℕ) - h ≤
      (residueMultiplicativeOrder (b ^ ((lambda : ℕ) ^ h)) ell).factorization
        (lambda : ℕ) := by
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  let u : (ZMod (ell : ℕ))ˣ :=
    Units.mk0 (b : ZMod (ell : ℕ)) hb0
  have horder := factorization_orderOf_pow_ge_sub u lambda h
  rw [← orderOf_units, ← orderOf_units] at horder
  simpa [residueMultiplicativeOrder, u] using horder

/-- Extract the maximal `lambda`-power from `q`.  The residual base has no
rational `lambda`-th root, and at every prime not dividing it the extraction
costs at most `h` in the `lambda`-adic valuation of the residue order. -/
private theorem extract_primePower_with_order_bound
    (lambda : Nat.Primes) (q : ℕ) (hq : 1 < q) :
    ∃ h b : ℕ,
      q = b ^ ((lambda : ℕ) ^ h) ∧
      1 < b ∧
      (∀ c : ℚ, c ^ (lambda : ℕ) ≠ b) ∧
      ∀ ell : Nat.Primes, ¬(ell : ℕ) ∣ b →
        (residueMultiplicativeOrder b ell).factorization (lambda : ℕ) - h ≤
          (residueMultiplicativeOrder q ell).factorization
            (lambda : ℕ) := by
  have hextract : ∀ q : ℕ, 1 < q → ∃ h b : ℕ,
      q = b ^ ((lambda : ℕ) ^ h) ∧ 1 < b ∧
        ∀ c : ℚ, c ^ (lambda : ℕ) ≠ b := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hq
        by_cases hpow : ∃ d : ℕ, d ^ (lambda : ℕ) = q
        · obtain ⟨d, hdq⟩ := hpow
          have hd : 1 < d := by
            by_contra hnot
            have hdle : d ≤ 1 := Nat.le_of_not_gt hnot
            interval_cases d
            · simp [lambda.2.ne_zero] at hdq
              omega
            · simp at hdq
              omega
          have hdlt : d < q := by
            rw [← hdq]
            calc
              d = d ^ 1 := by simp
              _ < d ^ (lambda : ℕ) :=
                Nat.pow_lt_pow_right hd lambda.2.one_lt
          obtain ⟨h, b, hdb, hb, hbmax⟩ := ih d hdlt hd
          refine ⟨h + 1, b, ?_, hb, hbmax⟩
          calc
            q = d ^ (lambda : ℕ) := hdq.symm
            _ = (b ^ ((lambda : ℕ) ^ h)) ^ (lambda : ℕ) := by
              rw [hdb]
            _ = b ^ (((lambda : ℕ) ^ h) * (lambda : ℕ)) := by
              rw [pow_mul]
            _ = b ^ ((lambda : ℕ) ^ (h + 1)) := by rw [pow_succ]
        · refine ⟨0, q, by simp, hq, ?_⟩
          intro c hc
          obtain ⟨d, hd⟩ :=
            exists_nat_pow_of_rat_pow lambda.2.ne_zero c hc
          exact hpow ⟨d, hd⟩
  obtain ⟨h, b, hqb, hb, hbmax⟩ := hextract q hq
  refine ⟨h, b, hqb, hb, hbmax, ?_⟩
  intro ell hell
  simpa only [hqb] using
    factorization_residueOrder_pow_ge_sub ell lambda b h hell

/-- Divisibility by the enlarged prime-power modulus used after extracting
`q = b^(lambda^h)` implies divisibility by the originally requested modulus. -/
private theorem primePower_dvd_of_enlargedExponent
    (lambda : Nat.Primes) {m h n : ℕ}
    (hdvd : (lambda : ℕ) ^ (m + h) ∣ n) :
    (lambda : ℕ) ^ m ∣ n := by
  apply dvd_trans (b := (lambda : ℕ) ^ (m + h))
  · exact ⟨(lambda : ℕ) ^ h, by rw [pow_add]⟩
  · exact hdvd

/-- The three-case Chebotarev--Kummer assertion in Blueprint `lem:order`.
The odd case uses `Q(mu_{lambda^M}, b^(1/lambda))`; the two even cases use
respectively a quadratic extension and the normal quartic splitting field.
Every Chebotarev invocation is through
`NU.Chebotarev.chebotarev_dirichletDensity`. -/
private def OrderDivisibilityPrinciple : Prop :=
  ∀ q : ℕ, 1 < q → ∀ (lambda : Nat.Primes) (m : ℕ),
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * q ∧
        (lambda : ℕ) ^ m ∣ residueMultiplicativeOrder q ell}

/-- A Chebotarev class contains infinitely many finite primes.  This is the
positivity consequence of the proved Dirichlet-density theorem used in each
of the three cases of Blueprint `lem:order`. -/
private theorem frobeniusPrimeSet_mk_infinite
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (g : L ≃ₐ[K] L) :
    Set.Infinite (NU.Chebotarev.frobeniusPrimeSet
      (K := K) (L := L) (ConjClasses.mk g)) := by
  intro hfinite
  have hden := NU.Chebotarev.chebotarev_dirichletDensity
    (K := K) (L := L) (ConjClasses.mk g)
  have hzero :=
    NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfinite
  have heq :
      (((ConjClasses.mk g).carrier.ncard : ℝ) /
        (Nat.card (L ≃ₐ[K] L) : ℝ)) = 0 :=
    tendsto_nhds_unique hden hzero
  have hnum : (0 : ℝ) < ((ConjClasses.mk g).carrier.ncard : ℝ) := by
    exact_mod_cast ((Set.ncard_pos
      (s := (ConjClasses.mk g).carrier)).2
        (show (ConjClasses.mk g).carrier.Nonempty from
          ⟨g, ConjClasses.mem_carrier_mk⟩))
  have hdenom : (0 : ℝ) < Nat.card (L ≃ₐ[K] L) := by
    exact_mod_cast Nat.card_pos (α := L ≃ₐ[K] L)
  exact (div_pos hnum hdenom).ne' heq


/-- A rational prime ideal has norm equal to its residue characteristic. -/
private theorem norm_eq_residueCharacteristic_rat
    (v : NU.Chebotarev.PrimeIdeal ℚ) :
    NU.Chebotarev.PrimeIdeal.norm v =
      NU.LocalTheory.residueCharacteristic v := by
  rw [NU.NeukirchUchida.LocalInvariants.residueCharacteristic_eq_absNorm_under]
  change Ideal.absNorm v.asIdeal = Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  let f : NumberField.RingOfIntegers ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hf : f.symm.toRingHom =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) := by
    exact RingHom.ext_int _ _
  have hmap : Ideal.map f.toRingHom v.asIdeal =
      Ideal.under ℤ v.asIdeal := by
    calc
      Ideal.map f.toRingHom v.asIdeal = Ideal.comap f.symm v.asIdeal := by
        simpa using Ideal.map_comap_of_equiv (I := v.asIdeal) f
      _ = Ideal.under ℤ v.asIdeal := by
        rw [Ideal.under_def]
        exact congrArg (fun g : ℤ →+* NumberField.RingOfIntegers ℚ =>
          Ideal.comap g v.asIdeal) hf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv v.asIdeal (Ideal.under ℤ v.asIdeal) f hmap.symm).toEquiv

private theorem intCast_mem_ratPrime_iff_dvd
    (v : NU.Chebotarev.PrimeIdeal ℚ) (n : ℕ) :
    algebraMap ℤ (NumberField.RingOfIntegers ℚ) (n : ℤ) ∈ v.asIdeal ↔
      NU.LocalTheory.residueCharacteristic v ∣ n := by
  change ((n : ℤ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal ↔ _
  rw [Int.cast_mem_ideal_iff,
    ← NU.NeukirchUchida.LocalInvariants.residueCharacteristic_eq_absNorm_under v,
    Int.natCast_dvd_natCast]

set_option maxHeartbeats 800000 in
private theorem odd_kummer_raw
    (lambda : Nat.Primes) (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (H : Irreducible
      (X ^ (lambda : ℕ) - C
        (algebraMap ℚ (CyclotomicField ((lambda : ℕ) ^ M) ℚ) b))) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        (lambda : ℕ) ^ M ∣ (ell : ℕ) - 1 ∧
        ¬ ∃ x : ZMod (ell : ℕ),
          x ^ (lambda : ℕ) = (b : ZMod (ell : ℕ))} := by
  let N : ℕ := (lambda : ℕ) ^ M
  have hN : 0 < N := pow_pos lambda.2.pos M
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : NumberField F :=
    IsCyclotomicExtension.numberField {N} ℚ F
  letI : FiniteDimensional ℚ F :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ F
  letI : IsGalois ℚ F :=
    IsCyclotomicExtension.isGalois {N} ℚ F
  letI : Normal ℚ F := IsGalois.to_normal
  let a : F := algebraMap ℚ F b
  let pF : F[X] := X ^ (lambda : ℕ) - C a
  have HpF : Irreducible pF := by simpa [F, N, a, pF] using H
  letI : Fact (Irreducible pF) := ⟨HpF⟩
  let E := AdjoinRoot pF
  letI : Field E := AdjoinRoot.instField
  letI : Algebra F E := inferInstance
  letI : Algebra ℚ E := inferInstance
  letI : IsScalarTower ℚ F E := inferInstance
  let zetaN : F := IsCyclotomicExtension.zeta N ℚ F
  have hzetaN : IsPrimitiveRoot zetaN N :=
    IsCyclotomicExtension.zeta_spec N ℚ F
  let d : ℕ := (lambda : ℕ) ^ (M - 1)
  have hNfac : N = d * (lambda : ℕ) := by
    dsimp [N, d]
    conv_lhs => rw [show M = (M - 1) + 1 by omega]
    exact pow_succ _ _
  let zeta : F := zetaN ^ d
  have hzeta : IsPrimitiveRoot zeta (lambda : ℕ) := by
    exact hzetaN.pow hN hNfac
  have hroots : (primitiveRoots (lambda : ℕ) F).Nonempty := by
    refine ⟨zeta, (mem_primitiveRoots lambda.2.pos).2 hzeta⟩
  letI : Polynomial.IsSplittingField F E pF := by
    exact isSplittingField_AdjoinRoot_X_pow_sub_C hroots HpF
  let f : ℚ[X] := X ^ N - 1
  let g : ℚ[X] := X ^ (lambda : ℕ) - C (b : ℚ)
  have hf : f ≠ 0 := by
    simpa [f] using (X_pow_sub_C_ne_zero hN (1 : ℚ))
  have hg : g ≠ 0 := X_pow_sub_C_ne_zero lambda.2.pos (b : ℚ)
  have hmapg : g.map (algebraMap ℚ F) = pF := by
    simp [g, pF, a]
  letI : Polynomial.IsSplittingField F E (g.map (algebraMap ℚ F)) := by
    rw [hmapg]
    infer_instance
  letI : Polynomial.IsSplittingField ℚ F f := by
    simpa [f] using
      (IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ F)
  letI : Polynomial.IsSplittingField ℚ E (f * g) :=
    Polynomial.IsSplittingField.mul (F := ℚ) (K := F) E f g hf hg
  letI : FiniteDimensional ℚ E :=
    Polynomial.IsSplittingField.finiteDimensional E (f * g)
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : Normal ℚ E := Normal.of_isSplittingField (f * g)
  letI : IsGalois ℚ E := IsGalois.mk
  let eta : rootsOfUnity (lambda : ℕ) F := hzeta.toRootsOfUnity
  let sigmaF : E ≃ₐ[F] E := autAdjoinRootXPowSubC (lambda : ℕ) a eta
  let sigma : E ≃ₐ[ℚ] E := sigmaF.restrictScalars ℚ
  have hsigma_ne : sigma ≠ 1 := by
    intro hs
    have hr := congrArg (fun t : E ≃ₐ[ℚ] E => t (AdjoinRoot.root pF)) hs
    change sigmaF (AdjoinRoot.root pF) = AdjoinRoot.root pF at hr
    rw [autAdjoinRootXPowSubC_root] at hr
    have hr' : AdjoinRoot.of pF zeta * AdjoinRoot.root pF =
        AdjoinRoot.root pF := by
      simpa [eta, Algebra.smul_def, pF] using hr
    have hroot0 : AdjoinRoot.root pF ≠ 0 := by
      simpa [pF] using
        (root_X_pow_sub_C_ne_zero' lambda.2.pos
          (show a ≠ 0 by
            intro ha
            have hbQ : (b : ℚ) = 0 :=
              (algebraMap ℚ F).injective (by simpa [a] using ha)
            exact (show (b : ℚ) ≠ 0 by exact_mod_cast (show b ≠ 0 by omega)) hbQ))
    have hz1of : AdjoinRoot.of pF zeta = 1 := by
      apply mul_right_cancel₀ hroot0
      simpa using hr'
    have hz1 : algebraMap F E zeta = 1 := by
      change AdjoinRoot.of pF zeta = 1
      exact hz1of
    have : zeta = 1 := (algebraMap F E).injective hz1
    exact hzeta.ne_one lambda.2.one_lt this
  have hinf : Set.Infinite (NU.Chebotarev.frobeniusPrimeSet
      (K := ℚ) (L := E) (ConjClasses.mk sigma)) := by
    intro hfinite
    have hden := NU.Chebotarev.chebotarev_dirichletDensity
      (K := ℚ) (L := E) (ConjClasses.mk sigma)
    have hzero := NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfinite
    have heq : (((ConjClasses.mk sigma).carrier.ncard : ℝ) /
        (Nat.card (E ≃ₐ[ℚ] E) : ℝ)) = 0 := tendsto_nhds_unique hden hzero
    have hnum : (0 : ℝ) < ((ConjClasses.mk sigma).carrier.ncard : ℝ) := by
      exact_mod_cast ((Set.ncard_pos (s := (ConjClasses.mk sigma).carrier)).2
        (show (ConjClasses.mk sigma).carrier.Nonempty from
          ⟨sigma, ConjClasses.mem_carrier_mk⟩))
    have hdenom : (0 : ℝ) < Nat.card (E ≃ₐ[ℚ] E) := by
      exact_mod_cast Nat.card_pos (α := E ≃ₐ[ℚ] E)
    exact (div_pos hnum hdenom).ne' heq
  have hmod_for_prime : ∀ v ∈ NU.Chebotarev.frobeniusPrimeSet
      (K := ℚ) (L := E) (ConjClasses.mk sigma),
      NU.LocalTheory.residueCharacteristic v ≠ (lambda : ℕ) →
      ¬ NU.LocalTheory.residueCharacteristic v ∣ b →
      N ∣ NU.LocalTheory.residueCharacteristic v - 1 ∧
        (b : ZMod (NU.LocalTheory.residueCharacteristic v)) ^
          ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) ≠ 1 := by
    intro v hv hell hbprime
    rcases hv with ⟨hunr, P, hPv, hclass⟩
    let phi : E ≃ₐ[ℚ] E :=
      NU.Chebotarev.arithFrobeniusAt (K := ℚ) (L := E) P
    have hconj : IsConj phi sigma := by
      exact ConjClasses.mk_eq_mk_iff_isConj.mp hclass
    let r : (E ≃ₐ[ℚ] E) →* (F ≃ₐ[ℚ] F) :=
      AlgEquiv.restrictNormalHom F
    have hrsigma : r sigma = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap F E).injective
      change algebraMap F E ((sigma.restrictNormal F) x) =
        algebraMap F E x
      rw [AlgEquiv.restrictNormal_commutes]
      change sigmaF (algebraMap F E x) = algebraMap F E x
      exact sigmaF.commutes x
    have hrphi : r phi = 1 := by
      have hc := r.map_isConj hconj
      rw [hrsigma] at hc
      exact isConj_one_left.mp hc
    let Q : NU.Chebotarev.PrimeIdeal F :=
      NU.LocalTheory.restrictFinitePlace F P
    have hPQ : P.asIdeal.LiesOver Q.asIdeal := by
      refine ⟨?_⟩
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
    have hQv : Q.asIdeal.LiesOver v.asIdeal := by
      refine ⟨?_⟩
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
        Ideal.under_under, hPv.over]
    have hPunr : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers ℚ) P.asIdeal := hunr P hPv
    have hfrobQ : NU.Chebotarev.arithFrobeniusAt
        (K := ℚ) (L := F) Q = 1 := by
      rw [← NU.Chebotarev.arithFrobAt_restrict P Q hPQ hPunr]
      exact hrphi
    have hNnotQ : algebraMap ℤ (NumberField.RingOfIntegers F) (N : ℤ) ∉
        Q.asIdeal := by
      intro hNQ
      have htowerInt :
          algebraMap (NumberField.RingOfIntegers ℚ)
              (NumberField.RingOfIntegers F)
              (algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ)) =
            algebraMap ℤ (NumberField.RingOfIntegers F) (N : ℤ) := by
        apply NumberField.RingOfIntegers.coe_injective (K := F)
        simp
      have hNvUnder :
          algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ) ∈
            Q.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
        rw [Ideal.mem_under, htowerInt]
        exact hNQ
      have hNv : algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ) ∈
          v.asIdeal := by
        rw [← hQv.over] at hNvUnder
        exact hNvUnder
      have hell_dvd_N : NU.LocalTheory.residueCharacteristic v ∣ N :=
        (intCast_mem_ratPrime_iff_dvd v N).mp hNv
      have hell_dvd_lambda : NU.LocalTheory.residueCharacteristic v ∣
          (lambda : ℕ) :=
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).dvd_of_dvd_pow hell_dvd_N
      exact hell ((Nat.prime_dvd_prime_iff_eq
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v) lambda.2).mp hell_dvd_lambda)
    have hQunr : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers ℚ) Q.asIdeal := by
      letI : P.asIdeal.LiesOver Q.asIdeal := hPQ
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers ℚ) P.asIdeal := hPunr
      exact Algebra.IsUnramifiedAt.of_liesOver
        (NumberField.RingOfIntegers ℚ) Q.asIdeal P.asIdeal
    have hzact := NU.Chebotarev.arithFrobAt_apply_rootOfUnity
      v Q hQv hQunr N zetaN hzetaN.pow_eq_one hNnotQ
    have hzact' : zetaN =
        zetaN ^ NU.LocalTheory.residueCharacteristic v := by
      simpa [hfrobQ, norm_eq_residueCharacteristic_rat] using hzact
    have hpows : zetaN ^ NU.LocalTheory.residueCharacteristic v =
        zetaN ^ 1 := by simpa using hzact'.symm
    have hpowsU : hzetaN.toRootsOfUnity ^
        NU.LocalTheory.residueCharacteristic v =
        hzetaN.toRootsOfUnity ^ 1 := by
      apply rootsOfUnity.coe_injective
      simpa only [rootsOfUnity.coe_pow, hzetaN.val_toRootsOfUnity_coe] using hpows
    have hmodEq0 := (pow_eq_pow_iff_modEq).mp hpowsU
    have hmodEq : NU.LocalTheory.residueCharacteristic v ≡ 1
        [MOD N] := by
      rw [← Subgroup.orderOf_coe, ← orderOf_units,
        hzetaN.val_toRootsOfUnity_coe, ← hzetaN.eq_orderOf] at hmodEq0
      exact hmodEq0
    have hmodResult : N ∣ NU.LocalTheory.residueCharacteristic v - 1 :=
      (Nat.modEq_iff_dvd'
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).one_le).mp
        hmodEq.symm
    obtain ⟨tau, htau⟩ := isConj_iff.mp hconj
    let alpha : E := AdjoinRoot.root pF
    let beta : E := tau.symm alpha
    let xi : E := tau.symm (AdjoinRoot.of pF zeta)
    have hsigma_alpha : sigma alpha = AdjoinRoot.of pF zeta * alpha := by
      change sigmaF (AdjoinRoot.root pF) = _
      simpa [alpha, eta, Algebra.smul_def, pF] using
        (autAdjoinRootXPowSubC_root a eta)
    have hphi_beta : phi beta = xi * beta := by
      have happ := congrArg (fun s : E ≃ₐ[ℚ] E => s alpha) htau
      have happ' : tau (phi (tau.symm alpha)) = sigma alpha := by
        simpa using happ
      apply tau.injective
      rw [map_mul]
      change tau (phi (tau.symm alpha)) =
        tau (tau.symm (AdjoinRoot.of pF zeta)) * tau (tau.symm alpha)
      rw [tau.apply_symm_apply, tau.apply_symm_apply, happ', hsigma_alpha]
    have halpha_pow : alpha ^ (lambda : ℕ) = algebraMap ℚ E b := by
      calc
        alpha ^ (lambda : ℕ) = AdjoinRoot.of pF a := by
          simpa [alpha, pF] using root_X_pow_sub_C_pow (lambda : ℕ) a
        _ = algebraMap ℚ E b := by
          change algebraMap F E a = algebraMap ℚ E b
          simp [a, IsScalarTower.algebraMap_apply ℚ F E]
    have hbeta_pow : beta ^ (lambda : ℕ) = algebraMap ℚ E b := by
      change (tau.symm alpha) ^ (lambda : ℕ) = _
      rw [← map_pow, halpha_pow]
      exact tau.symm.commutes b
    have hzetaE : IsPrimitiveRoot (AdjoinRoot.of pF zeta : E)
        (lambda : ℕ) := by
      rw [← AdjoinRoot.algebraMap_eq]
      exact hzeta.map_of_injective (algebraMap F E).injective
    have hxi : IsPrimitiveRoot xi (lambda : ℕ) := by
      exact hzetaE.map_of_injective tau.symm.injective
    have hbetaInt : IsIntegral ℤ beta := by
      refine ⟨X ^ (lambda : ℕ) - C (b : ℤ),
        monic_X_pow_sub_C _ lambda.2.ne_zero, ?_⟩
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [hbeta_pow]
      simp
    have hrestrictP : NU.LocalTheory.restrictFinitePlace ℚ P = v := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal, hPv.over]
    have hcharP : NU.LocalTheory.residueCharacteristic P =
        NU.LocalTheory.residueCharacteristic v := by
      rw [← NU.NeukirchUchida.LocalInvariants.residueCharacteristic_restrictFinitePlace ℚ P,
        hrestrictP]
    let k := NumberField.RingOfIntegers E ⧸ P.asIdeal
    letI : Field k := Ideal.Quotient.field P.asIdeal
    letI : Fintype k := Fintype.ofFinite k
    have hringChar : ringChar k = NU.LocalTheory.residueCharacteristic v := by
      rw [Ideal.ringChar_quot,
        ← NU.NeukirchUchida.LocalInvariants.residueCharacteristic_eq_absNorm_under,
        hcharP]
    letI : CharP k (NU.LocalTheory.residueCharacteristic v) :=
      (ringChar.eq_iff).mp hringChar
    letI : P.asIdeal.LiesOver v.asIdeal := hPv
    have hnormPcoprime : (Ideal.absNorm P.asIdeal).Coprime (lambda : ℕ) := by
      rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.asIdeal]
      change (NU.Chebotarev.PrimeIdeal.norm v ^ _).Coprime (lambda : ℕ)
      rw [norm_eq_residueCharacteristic_rat]
      exact ((Nat.coprime_primes
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v)
        lambda.2).mpr hell).pow_left _
    have hnormP_ne_one : Ideal.absNorm P.asIdeal ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr P.isMaximal.ne_top
    let xiI : NumberField.RingOfIntegers E := hxi.toInteger
    let betaI : NumberField.RingOfIntegers E := ⟨beta, hbetaInt⟩
    let rxi : k := Ideal.Quotient.mk P.asIdeal xiI
    let rbeta : k := Ideal.Quotient.mk P.asIdeal betaI
    have hrxi : IsPrimitiveRoot rxi (lambda : ℕ) := by
      exact hxi.toInteger_isPrimitiveRoot.idealQuotient_mk
        hnormP_ne_one hnormPcoprime
    have hrxi_ne : rxi ≠ 1 := hrxi.ne_one lambda.2.one_lt
    have hbetaPowInt : betaI ^ (lambda : ℕ) =
        algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ) := by
      apply NumberField.RingOfIntegers.coe_injective (K := E)
      change beta ^ (lambda : ℕ) = _
      rw [hbeta_pow]
      simp
    have hrbeta_ne : rbeta ≠ 0 := by
      intro hrbeta0
      have hbzero : (b : k) = 0 := by
        calc
          (b : k) = Ideal.Quotient.mk P.asIdeal
              (algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ)) := by simp
          _ = Ideal.Quotient.mk P.asIdeal
              (betaI ^ (lambda : ℕ)) := by rw [hbetaPowInt]
          _ = rbeta ^ (lambda : ℕ) := by rw [map_pow]
          _ = 0 := by rw [hrbeta0, zero_pow lambda.2.ne_zero]
      exact hbprime ((CharP.cast_eq_zero_iff k
        (NU.LocalTheory.residueCharacteristic v) b).mp hbzero)
    have hcard : Nat.card (NumberField.RingOfIntegers ℚ ⧸
        P.asIdeal.under (NumberField.RingOfIntegers ℚ)) =
        NU.LocalTheory.residueCharacteristic v := by
      calc
        Nat.card (NumberField.RingOfIntegers ℚ ⧸
            P.asIdeal.under (NumberField.RingOfIntegers ℚ)) =
            Nat.card (NumberField.RingOfIntegers ℚ ⧸ v.asIdeal) := by
              rw [hPv.over]
        _ = Ideal.absNorm v.asIdeal := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        _ = NU.Chebotarev.PrimeIdeal.norm v := rfl
        _ = NU.LocalTheory.residueCharacteristic v :=
          norm_eq_residueCharacteristic_rat v
    have hfrobBeta := (IsArithFrobAt.arithFrobAt
      (NumberField.RingOfIntegers ℚ) (E ≃ₐ[ℚ] E) P.asIdeal) betaI
    have hquotAction : Ideal.Quotient.mk P.asIdeal (phi • betaI) =
        rbeta ^ NU.LocalTheory.residueCharacteristic v := by
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk P.asIdeal (phi • betaI) -
        (Ideal.Quotient.mk P.asIdeal betaI) ^
          NU.LocalTheory.residueCharacteristic v = 0
      rw [← map_pow, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers ℚ)
          (NumberField.RingOfIntegers E) phi) betaI -
        betaI ^ NU.LocalTheory.residueCharacteristic v ∈ P.asIdeal
      simpa only [hcard, phi, NU.Chebotarev.arithFrobeniusAt] using hfrobBeta
    have hactInt : phi • betaI = xiI * betaI := by
      apply Subtype.ext
      exact hphi_beta
    have hresAction : rxi * rbeta =
        rbeta ^ NU.LocalTheory.residueCharacteristic v := by
      rw [← map_mul, ← hactInt]
      exact hquotAction
    have hsubadd : NU.LocalTheory.residueCharacteristic v - 1 + 1 =
        NU.LocalTheory.residueCharacteristic v :=
      Nat.sub_add_cancel
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).one_le
    have hrbeta_power :
        rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) = rxi := by
      apply mul_right_cancel₀ hrbeta_ne
      calc
        rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) * rbeta =
            rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1 + 1) := by
              rw [pow_succ]
        _ = rbeta ^ NU.LocalTheory.residueCharacteristic v := by rw [hsubadd]
        _ = rxi * rbeta := hresAction.symm
    have hlambdaN : (lambda : ℕ) ∣ N := by
      exact ⟨d, by simpa [mul_comm] using hNfac⟩
    have hlambdaL : (lambda : ℕ) ∣
        NU.LocalTheory.residueCharacteristic v - 1 :=
      dvd_trans hlambdaN hmodResult
    have hmuldiv : (lambda : ℕ) *
        ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) =
          NU.LocalTheory.residueCharacteristic v - 1 :=
      Nat.mul_div_cancel' hlambdaL
    have hrbeta_lambda : rbeta ^ (lambda : ℕ) = (b : k) := by
      calc
        rbeta ^ (lambda : ℕ) = Ideal.Quotient.mk P.asIdeal
            (betaI ^ (lambda : ℕ)) := by rw [map_pow]
        _ = Ideal.Quotient.mk P.asIdeal
            (algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ)) := by
              rw [hbetaPowInt]
        _ = (b : k) := by simp
    have hbpowerK : (b : k) ^
        ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) =
          rxi := by
      calc
        (b : k) ^ ((NU.LocalTheory.residueCharacteristic v - 1) /
            (lambda : ℕ)) =
            (rbeta ^ (lambda : ℕ)) ^
              ((NU.LocalTheory.residueCharacteristic v - 1) /
                (lambda : ℕ)) := by rw [hrbeta_lambda]
        _ = rbeta ^ ((lambda : ℕ) *
              ((NU.LocalTheory.residueCharacteristic v - 1) /
                (lambda : ℕ))) := by rw [pow_mul]
        _ = rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) := by
              rw [hmuldiv]
        _ = rxi := hrbeta_power
    refine ⟨hmodResult, ?_⟩
    intro hbadPower
    letI : Algebra (ZMod (NU.LocalTheory.residueCharacteristic v)) k :=
      ZMod.algebra k (NU.LocalTheory.residueCharacteristic v)
    have hmapped := congrArg
      (algebraMap (ZMod (NU.LocalTheory.residueCharacteristic v)) k)
      hbadPower
    rw [map_pow, map_one] at hmapped
    have hbmap : algebraMap
        (ZMod (NU.LocalTheory.residueCharacteristic v)) k
        (b : ZMod (NU.LocalTheory.residueCharacteristic v)) = (b : k) := by
      simp
    rw [hbmap, hbpowerK] at hmapped
    exact hrxi_ne hmapped
  let toPrime : NU.Chebotarev.PrimeIdeal ℚ → Nat.Primes := fun v =>
    ⟨NU.LocalTheory.residueCharacteristic v,
      NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v⟩
  have htoPrime : Function.Injective toPrime := by
    intro v w hvw
    apply NU.NeukirchUchida.LocalInvariants.rationalFinitePlace_eq_of_residueCharacteristic_eq
    exact congrArg Subtype.val hvw
  let Cbad : ℕ := 2 * b * (lambda : ℕ)
  let D : Set Nat.Primes := {ell | (ell : ℕ) ∣ Cbad}
  have hCbad : 0 < Cbad := by
    dsimp [Cbad]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) lambda.2.pos
  have hDimage : ((fun ell : Nat.Primes => (ell : ℕ)) '' D).Finite := by
    apply (Set.finite_le_nat Cbad).subset
    rintro n ⟨ell, hell, rfl⟩
    exact Nat.le_of_dvd hCbad hell
  have hD : D.Finite := by
    apply Set.Finite.of_finite_image hDimage
    intro x _ y _ hxy
    exact Subtype.ext hxy
  let B : Set (NU.Chebotarev.PrimeIdeal ℚ) := toPrime ⁻¹' D
  have hB : B.Finite := hD.preimage htoPrime.injOn
  let S := NU.Chebotarev.frobeniusPrimeSet
    (K := ℚ) (L := E) (ConjClasses.mk sigma)
  have hSgood : (S \ B).Infinite := hinf.diff hB
  have himage : (toPrime '' (S \ B)).Infinite :=
    hSgood.image htoPrime.injOn
  apply himage.mono
  rintro ell ⟨v, ⟨hvS, hvB⟩, rfl⟩
  have hnotC : ¬ NU.LocalTheory.residueCharacteristic v ∣ Cbad := hvB
  have hell : NU.LocalTheory.residueCharacteristic v ≠ (lambda : ℕ) := by
    intro heq
    apply hnotC
    rw [heq]
    exact dvd_mul_left (lambda : ℕ) (2 * b)
  have hbprime : ¬ NU.LocalTheory.residueCharacteristic v ∣ b := by
    intro hdvd
    apply hnotC
    exact dvd_trans hdvd (dvd_mul_of_dvd_left (dvd_mul_left b 2) (lambda : ℕ))
  have hcoprimeTarget : ¬ NU.LocalTheory.residueCharacteristic v ∣ 2 * b := by
    intro hdvd
    apply hnotC
    exact dvd_mul_of_dvd_left hdvd (lambda : ℕ)
  obtain ⟨hmod, hpower⟩ := hmod_for_prime v hvS hell hbprime
  letI : Fact (NU.LocalTheory.residueCharacteristic v).Prime :=
    ⟨NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v⟩
  refine ⟨hcoprimeTarget, hmod, ?_⟩
  rintro ⟨x, hx⟩
  apply hpower
  have hx0 : x ≠ 0 := by
    intro hxzero
    have hbzero : (b : ZMod (NU.LocalTheory.residueCharacteristic v)) = 0 := by
      rw [← hx, hxzero, zero_pow lambda.2.ne_zero]
    exact hbprime ((ZMod.natCast_eq_zero_iff b
      (NU.LocalTheory.residueCharacteristic v)).mp hbzero)
  have hlambdaN : (lambda : ℕ) ∣ N := by
    exact ⟨d, by simpa [mul_comm] using hNfac⟩
  have hlambdaL : (lambda : ℕ) ∣
      NU.LocalTheory.residueCharacteristic v - 1 :=
    dvd_trans hlambdaN hmod
  have hmuldiv : (lambda : ℕ) *
      ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) =
        NU.LocalTheory.residueCharacteristic v - 1 :=
    Nat.mul_div_cancel' hlambdaL
  calc
    (b : ZMod (NU.LocalTheory.residueCharacteristic v)) ^
        ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) =
      (x ^ (lambda : ℕ)) ^
        ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ)) := by
          rw [hx]
    _ = x ^ ((lambda : ℕ) *
        ((NU.LocalTheory.residueCharacteristic v - 1) / (lambda : ℕ))) := by
          rw [pow_mul]
    _ = x ^ (NU.LocalTheory.residueCharacteristic v - 1) := by rw [hmuldiv]
    _ = 1 := ZMod.pow_card_sub_one_eq_one hx0


/-- The pure radical extension of odd prime degree is not normal over `ℚ`. -/
private theorem oddPrime_adjoinRoot_not_normal
    (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) (b : ℕ) (hb : b ≠ 0)
    (H : Irreducible (X ^ (p : ℕ) - C (b : ℚ))) :
    letI : Fact (Irreducible (X ^ (p : ℕ) - C (b : ℚ))) := ⟨H⟩
    ¬ Normal ℚ (AdjoinRoot (X ^ (p : ℕ) - C (b : ℚ))) := by
  let poly : ℚ[X] := X ^ (p : ℕ) - C (b : ℚ)
  letI : Fact (Irreducible poly) := ⟨by simpa [poly] using H⟩
  intro hnormal
  letI : Normal ℚ (AdjoinRoot poly) := by
    simpa [poly] using hnormal
  have hpoly0 : poly ≠ 0 := by
    exact (show Irreducible poly from Fact.out).ne_zero
  have hrootEval : aeval (AdjoinRoot.root poly) poly = 0 := by
    dsimp [poly]
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C,
      root_X_pow_sub_C_pow]
    have hmaps : AdjoinRoot.of (X ^ (p : ℕ) - C (b : ℚ)) =
        algebraMap ℚ (AdjoinRoot poly) := RingHom.ext_rat _ _
    rw [hmaps, sub_self]
  have hmin : minpoly ℚ (AdjoinRoot.root poly) = poly := by
    have hm := minpoly.eq_of_irreducible (show Irreducible poly from Fact.out)
      hrootEval
    have hmonic : poly.Monic := monic_X_pow_sub_C _ p.2.ne_zero
    simpa [hmonic.leadingCoeff] using hm.symm
  have hsplitsPoly : (poly.map (algebraMap ℚ (AdjoinRoot poly))).Splits := by
    have hs := (show Normal ℚ (AdjoinRoot poly) from inferInstance).splits
      (AdjoinRoot.root poly)
    rw [hmin] at hs
    exact hs
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hsplitsOne : ((X ^ (p : ℕ) - 1 : ℚ[X]).map
      (algebraMap ℚ (AdjoinRoot poly))).Splits := by
    exact splits_X_pow_sub_one_of_X_pow_sub_C
      (algebraMap ℚ (AdjoinRoot poly)) (p : ℕ) hbQ
        (by simpa [poly] using hsplitsPoly)
  have hcycIrr : Irreducible (cyclotomic (p : ℕ) ℚ) :=
    cyclotomic.irreducible_rat p.2.pos
  have hcycDvd : (cyclotomic (p : ℕ) ℚ).map
      (algebraMap ℚ (AdjoinRoot poly)) ∣
      (X ^ (p : ℕ) - 1 : ℚ[X]).map
        (algebraMap ℚ (AdjoinRoot poly)) :=
    Polynomial.map_dvd _ (cyclotomic.dvd_X_pow_sub_one (p : ℕ) ℚ)
  have hbig0 : (X ^ (p : ℕ) - 1 : ℚ[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero p.2.pos 1
  have hcycSplits : ((cyclotomic (p : ℕ) ℚ).map
      (algebraMap ℚ (AdjoinRoot poly))).Splits :=
    hsplitsOne.of_dvd (Polynomial.map_ne_zero hbig0) hcycDvd
  have hdegree := hcycIrr.natDegree_dvd_finrank hcycSplits
  have hfin : Module.finrank ℚ (AdjoinRoot poly) = (p : ℕ) := by
    calc
      Module.finrank ℚ (AdjoinRoot poly) = (AdjoinRoot.powerBasis hpoly0).dim :=
        (AdjoinRoot.powerBasis hpoly0).finrank
      _ = poly.natDegree := AdjoinRoot.powerBasis_dim hpoly0
      _ = (p : ℕ) := by exact natDegree_X_pow_sub_C
  rw [natDegree_cyclotomic, Nat.totient_prime p.2, hfin] at hdegree
  rcases (Nat.dvd_prime p.2).mp hdegree with h | h
  · have hpval : (p : ℕ) = 2 := by omega
    exact hp2 hpval
  · exact (Nat.ne_of_lt (Nat.sub_lt p.2.pos Nat.zero_lt_one)) h

private theorem oddPrime_not_pow_in_cyclotomic
    (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) (M : ℕ) (hM : 0 < M)
    (b : ℕ) (hb : b ≠ 0)
    (H : Irreducible (X ^ (p : ℕ) - C (b : ℚ))) :
    ∀ c : CyclotomicField ((p : ℕ) ^ M) ℚ,
      c ^ (p : ℕ) ≠
        algebraMap ℚ (CyclotomicField ((p : ℕ) ^ M) ℚ) b := by
  intro c hc
  let N : ℕ := (p : ℕ) ^ M
  have hN : 0 < N := pow_pos p.2.pos M
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : IsAbelianGalois ℚ F :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ F
  let poly : ℚ[X] := X ^ (p : ℕ) - C (b : ℚ)
  have hpoly : Irreducible poly := by simpa [poly] using H
  letI : Fact (Irreducible poly) := ⟨hpoly⟩
  let A := AdjoinRoot poly
  letI : Field A := AdjoinRoot.instField
  letI : Algebra ℚ A := inferInstance
  let cF : F := by simpa [F, N] using c
  have hcF : cF ^ (p : ℕ) = algebraMap ℚ F b := by
    simpa [cF, F, N] using hc
  have heval : eval₂ (algebraMap ℚ F) cF poly = 0 := by
    simp [poly, hcF]
  let emb : A →ₐ[ℚ] F :=
    AdjoinRoot.liftAlgHom poly (Algebra.ofId ℚ F) cF heval
  letI : IsAbelianGalois ℚ A := IsAbelianGalois.of_algHom emb
  have hnormal : Normal ℚ A := IsGalois.to_normal
  exact oddPrime_adjoinRoot_not_normal p hp2 b hb H hnormal


/-- Odd-prime cyclotomic--Kummer Chebotarev primes. -/
private theorem oddPrime_case
    (lambda : Nat.Primes) (hlambda : (lambda : ℕ) ≠ 2)
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ (lambda : ℕ) ≠ b) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        (lambda : ℕ) ^ M ∣ (ell : ℕ) - 1 ∧
        ¬ ∃ x : ZMod (ell : ℕ),
          x ^ (lambda : ℕ) = (b : ZMod (ell : ℕ))} := by
  have hrat : Irreducible
      (X ^ (lambda : ℕ) - C (b : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime lambda.2 hbmax
  have hnopow := oddPrime_not_pow_in_cyclotomic
    lambda hlambda M hM b (by omega) hrat
  have hfield : Irreducible
      (X ^ (lambda : ℕ) - C
        (algebraMap ℚ (CyclotomicField ((lambda : ℕ) ^ M) ℚ) b)) :=
    X_pow_sub_C_irreducible_of_prime lambda.2 hnopow
  exact odd_kummer_raw lambda M b hM hb hfield


/-- A positive nonsquare integer which is not twice a rational square has an
odd prime occurring to odd multiplicity.  This is the arithmetic input which
separates its quadratic field from every `2`-power cyclotomic field. -/
private theorem exists_oddPrime_odd_factorization
    (b : ℕ) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ¬ ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    ∃ p : Nat.Primes, (p : ℕ) ≠ 2 ∧ Odd (b.factorization (p : ℕ)) := by
  by_contra H
  push Not at H
  let d := Nat.floorRoot 2 b
  have hb0 : b ≠ 0 := by omega
  have hd0 : d ≠ 0 := (Nat.floorRoot_ne_zero).2 ⟨by omega, hb0⟩
  have hfac_away (p : ℕ) (hp2 : p ≠ 2) :
      2 * (d.factorization p) = b.factorization p := by
    rw [Nat.factorization_floorRoot]
    simp only [Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
    by_cases hp : p.Prime
    · have heven : Even (b.factorization p) :=
        Nat.not_odd_iff_even.mp (H ⟨p, hp⟩ hp2)
      obtain ⟨k, hk⟩ := heven
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime b hp]
  rcases (b.factorization 2).even_or_odd with heven | hodd
  · apply hbmax (d : ℚ)
    norm_cast
    apply Nat.eq_of_factorization_eq (pow_ne_zero 2 hd0) hb0
    intro p
    rw [Nat.factorization_pow]
    change 2 * d.factorization p = b.factorization p
    by_cases hp2 : p = 2
    · subst p
      obtain ⟨k, hk⟩ := heven
      rw [Nat.factorization_floorRoot]
      simp only [Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
      omega
    · exact hfac_away p hp2
  · apply hcase
    refine ⟨d, ?_⟩
    norm_cast
    apply Nat.eq_of_factorization_eq hb0
      (mul_ne_zero (by decide) (pow_ne_zero 2 hd0))
    intro p
    rw [Nat.factorization_mul (by decide) (pow_ne_zero 2 hd0),
      Nat.factorization_pow]
    change b.factorization p =
      (2 : ℕ).factorization p + 2 * d.factorization p
    by_cases hp2 : p = 2
    · subst p
      obtain ⟨k, hk⟩ := hodd
      rw [Nat.factorization_floorRoot]
      simp only [Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]
      norm_num [Nat.prime_two.factorization]
      omega
    · simp [Nat.prime_two.factorization, hp2, (hfac_away p hp2).symm]

/-- An odd valuation at an odd rational prime prevents an integer from
becoming a square in a `2`-power cyclotomic field: those fields are unramified
at that prime, so the extended valuation retains odd multiplicity. -/
private theorem no_square_in_twoPower_cyclotomic_of_oddFactor
    (M b : ℕ) (hb : 1 < b) (p : Nat.Primes)
    (hp2 : (p : ℕ) ≠ 2) (hpodd : Odd (b.factorization (p : ℕ))) :
    ∀ c : CyclotomicField (2 ^ M) ℚ,
      c ^ 2 ≠ algebraMap ℚ (CyclotomicField (2 ^ M) ℚ) b := by
  let N : ℕ := 2 ^ M
  have hN : 0 < N := pow_pos (by omega) M
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : NumberField F :=
    IsCyclotomicExtension.numberField {N} ℚ F
  letI : IsScalarTower ℤ ℚ F :=
    IsScalarTower.of_algebraMap_eq' (by ext; simp)
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  intro c hc
  let q : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)}
  letI : q.IsMaximal := by
    simpa [q] using Int.ideal_span_isMaximal_of_prime (p : ℕ)
  obtain ⟨P, hPmax, hPq⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers F) q
  have hq0 : q ≠ ⊥ := by
    intro hq
    have hp0 : (p.val : ℤ) = 0 :=
      Ideal.span_singleton_eq_bot.mp (by simpa [q] using hq)
    exact p.2.ne_zero (by exact_mod_cast hp0)
  have hP0 : P ≠ ⊥ := by
    intro hP
    apply hq0
    calc
      q = Ideal.under ℤ P := hPq.over
      _ = ⊥ := by
        rw [hP, Ideal.under_def]
        exact Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective ℤ
            (NumberField.RingOfIntegers F))
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    ⟨q, inferInstance, hq0⟩
  let w : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers F) :=
    ⟨P, hPmax.isPrime, hP0⟩
  letI : P.LiesOver q := hPq
  letI : w.asIdeal.LiesOver v.asIdeal := by
    simpa [v, w] using hPq
  have hpdvd : ¬(p : ℕ) ∣ N := by
    intro hdiv
    have hpdiv2 : (p : ℕ) ∣ 2 :=
      p.2.dvd_of_dvd_pow (by simpa [N] using hdiv)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp hpdiv2)
  have he : q.ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx q P hq0]
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      (p : ℕ) F P hpdvd
  have hmult : multiplicity q (Ideal.span {((b : ℕ) : ℤ)}) =
      b.factorization (p : ℕ) := by
    simpa [q] using
      (show multiplicity (Ideal.span {((p : ℕ) : ℤ)})
          (Ideal.span {((b : ℕ) : ℤ)}) = b.factorization (p : ℕ) by
        calc
          multiplicity (Ideal.span {((p : ℕ) : ℤ)})
              (Ideal.span {((b : ℕ) : ℤ)}) =
              multiplicity ((p : ℕ) : ℤ) ((b : ℕ) : ℤ) :=
            multiplicity_eq_of_emultiplicity_eq
              Ideal.emultiplicity_eq_emultiplicity_span
          _ = multiplicity (p : ℕ) b := by
            rw [← Int.multiplicity_natAbs (p : ℕ) (b : ℤ)]
            simp
          _ = b.factorization (p : ℕ) :=
            Nat.multiplicity_eq_factorization p.2 (by omega))
  have hvb : w.valuation F (algebraMap ℚ F b) =
      WithZero.exp (-(b.factorization (p : ℕ) : ℤ)) := by
    have hlie := v.intValuation_liesOver w (b : ℤ)
    rw [he, pow_one] at hlie
    calc
      w.valuation F (algebraMap ℚ F b) =
          w.intValuation (algebraMap ℤ
            (NumberField.RingOfIntegers F) (b : ℤ)) := by
        rw [← w.valuation_of_algebraMap (K := F)]
        congr 1
      _ = v.intValuation (b : ℤ) := hlie.symm
      _ = WithZero.exp (-(multiplicity q
          (Ideal.span {((b : ℕ) : ℤ)}) : ℤ)) := by
        simpa [v] using v.intValuation_eq_exp_neg_multiplicity
          (show (b : ℤ) ≠ 0 by
            exact_mod_cast (show b ≠ 0 by omega))
      _ = WithZero.exp (-(b.factorization (p : ℕ) : ℤ)) := by
        rw [hmult]
  have hsquare : (w.valuation F c) ^ 2 =
      WithZero.exp (-(b.factorization (p : ℕ) : ℤ)) := by
    calc
      (w.valuation F c) ^ 2 = w.valuation F (c ^ 2) := by rw [map_pow]
      _ = w.valuation F (algebraMap ℚ F b) := by
        rw [show c ^ 2 = algebraMap ℚ F b by simpa [F, N] using hc]
      _ = WithZero.exp (-(b.factorization (p : ℕ) : ℤ)) := hvb
  have hlog := congrArg WithZero.log hsquare
  rw [WithZero.log_pow, WithZero.log_exp] at hlog
  obtain ⟨k, hk⟩ := hpodd
  norm_num [nsmul_eq_mul] at hlog
  omega

/-- Quadratic cyclotomic--Kummer Chebotarev primes in the nonexceptional
case.  The odd valuation helper supplies irreducibility over the cyclotomic
base, after which the common Kummer--Frobenius construction applies verbatim. -/
private theorem twoPrime_nonexceptional_case
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ¬ ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        2 ^ M ∣ (ell : ℕ) - 1 ∧
        ¬ ∃ x : ZMod (ell : ℕ), x ^ 2 = (b : ZMod (ell : ℕ))} := by
  obtain ⟨p, hp2, hpodd⟩ :=
    exists_oddPrime_odd_factorization b hb hbmax hcase
  have hnopow :=
    no_square_in_twoPower_cyclotomic_of_oddFactor M b hb p hp2 hpodd
  have hfield : Irreducible
      (X ^ 2 - C
        (algebraMap ℚ (CyclotomicField (2 ^ M) ℚ) b)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hnopow
  exact odd_kummer_raw ⟨2, Nat.prime_two⟩ M b hM hb hfield

/-- The quadratic even-prime branch when the extracted base is not twice a
rational square.  This is one of the two isolated resistant Kummer cases. -/
private theorem twoPrime_nonexceptional_orderPrimes
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ¬ ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        2 ^ M ∣ residueMultiplicativeOrder b ell} := by
  have hraw :=
    twoPrime_nonexceptional_case M b hM hb hbmax hcase
  apply hraw.mono
  rintro ell ⟨hell, hmod, hnonpower⟩
  have hellb : ¬(ell : ℕ) ∣ b := by
    intro hdvd
    exact hell (dvd_trans hdvd (dvd_mul_left b 2))
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hellb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  have hlastPos : 0 < (ell : ℕ) - 1 :=
    Nat.sub_pos_of_lt ell.2.one_lt
  have hord0 : residueMultiplicativeOrder b ell ≠ 0 := by
    have hdvd := ZMod.orderOf_dvd_card_sub_one hb0
    exact (Nat.pos_of_dvd_of_pos hdvd hlastPos).ne'
  have hlast0 : (ell : ℕ) - 1 ≠ 0 := hlastPos.ne'
  have hvalLast : M ≤ ((ell : ℕ) - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hlast0).mp hmod
  have hfac := factorization_orderOf_eq_of_not_primePower
    ell (⟨2, Nat.prime_two⟩ : Nat.Primes) b hellb hnonpower
  refine ⟨hell,
    (Nat.prime_two.pow_dvd_iff_le_factorization hord0).mpr ?_⟩
  rw [hfac]
  exact hvalLast

/-- For a positive rational nonsquare `b`, the pure quartic polynomial
`X^4 - b` is irreducible.  After adjoining `sqrt b`, a hypothetical further
square root would have norm whose square is `-b`, contradicting positivity. -/
private theorem quartic_radical_irreducible
    (b : ℕ) (hb : 1 < b) (hbmax : ∀ c : ℚ, c ^ 2 ≠ b) :
    Irreducible (X ^ 4 - C (b : ℚ)) := by
  have hquad : Irreducible (X ^ 2 - C (b : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hbmax
  rw [show 4 = 2 * 2 by norm_num]
  apply X_pow_mul_sub_C_irreducible hquad
  intro E _ _ x hx
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro y hy
  have hxint : IsIntegral ℚ x := not_not.mp fun h ↦ by
    simpa only [degree_zero,
      degree_X_pow_sub_C (show 0 < 2 by norm_num) (b : ℚ),
      WithBot.natCast_ne_bot] using
        congr_arg degree (hx.symm.trans (dif_neg h))
  let L : IntermediateField ℚ E := IntermediateField.adjoin ℚ {x}
  letI : Algebra ℚ ↥L := IntermediateField.algebra' L
  have hnormgen : Algebra.norm ℚ
      (IntermediateField.AdjoinSimple.gen ℚ x) = -(b : ℚ) := by
    let pb := IntermediateField.adjoin.powerBasis hxint
    calc
      Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ x) =
          Algebra.norm ℚ pb.gen := by
        exact congrArg (Algebra.norm ℚ)
          (IntermediateField.adjoin.powerBasis_gen hxint).symm
      _ = (-1 : ℚ) ^ pb.dim * (minpoly ℚ pb.gen).coeff 0 :=
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
      _ = -(b : ℚ) := by
        have hnat0 : (X ^ 2 - C (b : ℚ)).natDegree = 2 :=
          natDegree_X_pow_sub_C
        have hnat : (X ^ 2 - (b : ℚ[X])).natDegree = 2 := by
          simpa using hnat0
        simp [pb, IntermediateField.minpoly_gen, hx, hnat]
  have hnorm := congrArg (Algebra.norm ℚ) hy
  rw [map_pow, hnormgen] at hnorm
  have hnonneg : 0 ≤ (Algebra.norm ℚ y) ^ 2 := sq_nonneg _
  have hbQ : (0 : ℚ) < b := by
    exact_mod_cast (show 0 < b by omega)
  nlinarith

/-- The real pure quartic field generated by a fourth root of a positive
integer is not normal.  Normality would force it to contain a root of
`X^2 + 1`, while its distinguished real embedding admits no such root. -/
private theorem quartic_adjoinRoot_not_normal
    (b : ℕ) (hb : 1 < b)
    (H : Irreducible (X ^ 4 - C (b : ℚ))) :
    letI : Fact (Irreducible (X ^ 4 - C (b : ℚ))) := ⟨H⟩
    ¬ Normal ℚ (AdjoinRoot (X ^ 4 - C (b : ℚ))) := by
  let poly : ℚ[X] := X ^ 4 - C (b : ℚ)
  letI : Fact (Irreducible poly) := ⟨by simpa [poly] using H⟩
  intro hnormal
  letI : Normal ℚ (AdjoinRoot poly) := by
    simpa [poly] using hnormal
  have hpoly0 : poly ≠ 0 :=
    (show Irreducible poly from Fact.out).ne_zero
  have hrootEval : aeval (AdjoinRoot.root poly) poly = 0 := by
    dsimp [poly]
    rw [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C,
      root_X_pow_sub_C_pow]
    have hmaps : AdjoinRoot.of (X ^ 4 - C (b : ℚ)) =
        algebraMap ℚ (AdjoinRoot poly) := RingHom.ext_rat _ _
    rw [hmaps, sub_self]
  have hmin : minpoly ℚ (AdjoinRoot.root poly) = poly := by
    have hm := minpoly.eq_of_irreducible
      (show Irreducible poly from Fact.out) hrootEval
    have hmonic : poly.Monic :=
      monic_X_pow_sub_C _ (by norm_num)
    simpa [hmonic.leadingCoeff] using hm.symm
  have hsplitsPoly :
      (poly.map (algebraMap ℚ (AdjoinRoot poly))).Splits := by
    have hs := (show Normal ℚ (AdjoinRoot poly) from inferInstance).splits
      (AdjoinRoot.root poly)
    rw [hmin] at hs
    exact hs
  have hbQ : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 by omega)
  have hsplitsOne : ((X ^ 4 - 1 : ℚ[X]).map
      (algebraMap ℚ (AdjoinRoot poly))).Splits := by
    exact splits_X_pow_sub_one_of_X_pow_sub_C
      (algebraMap ℚ (AdjoinRoot poly)) 4 hbQ
        (by simpa [poly] using hsplitsPoly)
  let plus : ℚ[X] := X ^ 2 + 1
  have hplusDvd : plus ∣ X ^ 4 - 1 := by
    refine ⟨X ^ 2 - 1, ?_⟩
    dsimp [plus]
    ring
  have hbig0 : (X ^ 4 - 1 : ℚ[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero (by norm_num) 1
  have hplusSplits :
      (plus.map (algebraMap ℚ (AdjoinRoot poly))).Splits :=
    hsplitsOne.of_dvd (Polynomial.map_ne_zero hbig0)
      (Polynomial.map_dvd _ hplusDvd)
  have hdegplus :
      (plus.map (algebraMap ℚ (AdjoinRoot poly))).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    have hp0 : plus ≠ 0 := by
      dsimp [plus]
      exact X_pow_add_C_ne_zero (by norm_num) 1
    rw [Polynomial.degree_eq_natDegree hp0]
    have hnat : plus.natDegree = 2 := by
      dsimp [plus]
      rw [show (1 : ℚ[X]) = C 1 by simp, natDegree_add_C]
      simp
    rw [hnat]
    norm_num
  obtain ⟨z, hz⟩ :=
    Splits.exists_eval_eq_zero hplusSplits hdegplus
  let r : ℝ := Real.sqrt (Real.sqrt (b : ℝ))
  have hbR : (0 : ℝ) ≤ b := by positivity
  have hsqrtR : 0 ≤ Real.sqrt (b : ℝ) := Real.sqrt_nonneg _
  have hr4 : r ^ 4 = (b : ℝ) := by
    dsimp [r]
    nlinarith [Real.sq_sqrt hbR, Real.sq_sqrt hsqrtR]
  have heval : eval₂ (algebraMap ℚ ℝ) r poly = 0 := by
    simp [poly, hr4]
  let emb : AdjoinRoot poly →ₐ[ℚ] ℝ :=
    AdjoinRoot.liftAlgHom poly (Algebra.ofId ℚ ℝ) r heval
  have hzR := congrArg emb hz
  have hsq : emb z ^ 2 + 1 = 0 := by
    simpa [plus, emb] using hzR
  nlinarith [sq_nonneg (emb z)]

/-- A positive nonsquare has no fourth root in a `2`-power cyclotomic
field.  Otherwise its irreducible pure quartic field would embed in an abelian
Galois extension and hence be normal, contrary to the preceding lemma. -/
private theorem no_fourthPower_in_twoPower_cyclotomic
    (M b : ℕ) (hb : 1 < b) (hbmax : ∀ c : ℚ, c ^ 2 ≠ b) :
    ∀ c : CyclotomicField (2 ^ M) ℚ,
      c ^ 4 ≠ algebraMap ℚ (CyclotomicField (2 ^ M) ℚ) b := by
  intro c hc
  let N : ℕ := 2 ^ M
  have hN : 0 < N := pow_pos (by omega) M
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : IsAbelianGalois ℚ F :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ F
  let poly : ℚ[X] := X ^ 4 - C (b : ℚ)
  have hpoly : Irreducible poly := by
    simpa [poly] using quartic_radical_irreducible b hb hbmax
  letI : Fact (Irreducible poly) := ⟨hpoly⟩
  let A := AdjoinRoot poly
  letI : Field A := AdjoinRoot.instField
  letI : Algebra ℚ A := inferInstance
  let cF : F := by simpa [F, N] using c
  have hcF : cF ^ 4 = algebraMap ℚ F b := by
    simpa [cF, F, N] using hc
  have heval : eval₂ (algebraMap ℚ F) cF poly = 0 := by
    simp [poly, hcF]
  let emb : A →ₐ[ℚ] F :=
    AdjoinRoot.liftAlgHom poly (Algebra.ofId ℚ F) cF heval
  letI : IsAbelianGalois ℚ A := IsAbelianGalois.of_algHom emb
  have hnormal : Normal ℚ A := IsGalois.to_normal
  exact quartic_adjoinRoot_not_normal b hb
    (quartic_radical_irreducible b hb hbmax) hnormal

/-- In the exceptional case `b = 2c²`, the cyclotomic field of level
`2^(M+2)` contains a square root of `b`.  Explicitly, a primitive eighth root
`ζ` supplies `sqrt 2 = ζ + ζ⁻¹`. -/
private theorem exists_squareRoot_in_exceptional_cyclotomic
    (M b : ℕ) (hM : 0 < M)
    (hcase : ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    ∃ a : CyclotomicField (2 ^ (M + 2)) ℚ,
      a ^ 2 = algebraMap ℚ (CyclotomicField (2 ^ (M + 2)) ℚ) b := by
  let N : ℕ := 2 ^ (M + 2)
  have hN : 0 < N := pow_pos (by omega) (M + 2)
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  let zetaN : F := IsCyclotomicExtension.zeta N ℚ F
  have hzetaN : IsPrimitiveRoot zetaN N :=
    IsCyclotomicExtension.zeta_spec N ℚ F
  let d : ℕ := 2 ^ (M - 1)
  have hNfac : N = d * 8 := by
    dsimp [N, d]
    conv_lhs => rw [show M + 2 = (M - 1) + 3 by omega]
    rw [pow_add]
    norm_num
  let zeta8 : F := zetaN ^ d
  have hzeta8 : IsPrimitiveRoot zeta8 8 :=
    hzetaN.pow hN hNfac
  have hzeta4 : zeta8 ^ 4 = -1 := by
    have hprim2 : IsPrimitiveRoot (zeta8 ^ 4) 2 :=
      hzeta8.pow (by norm_num) (by norm_num)
    exact hprim2.eq_neg_one_of_two_right
  have hzeta0 : zeta8 ≠ 0 := hzeta8.ne_zero (by norm_num)
  have hinv2 : (zeta8⁻¹) ^ 2 = -(zeta8 ^ 2) := by
    field_simp [hzeta0]
    rw [hzeta4]
    simp
  let s : F := zeta8 + zeta8⁻¹
  have hs : s ^ 2 = 2 := by
    dsimp [s]
    calc
      (zeta8 + zeta8⁻¹) ^ 2 =
          zeta8 ^ 2 + 2 + (zeta8⁻¹) ^ 2 := by
        field_simp [hzeta0]
        ring
      _ = 2 := by rw [hinv2]; ring
  obtain ⟨c, hc⟩ := hcase
  let a : F := s * algebraMap ℚ F c
  refine ⟨by simpa [F, N] using a, ?_⟩
  change a ^ 2 = algebraMap ℚ F b
  rw [mul_pow, hs]
  rw [← map_pow]
  calc
    (2 : F) * algebraMap ℚ F (c ^ 2) =
        algebraMap ℚ F (2 * c ^ 2) := by simp
    _ = algebraMap ℚ F b := by rw [← hc]

/-- The exceptional square root in the cyclotomic field is itself not a
square there; otherwise `b` would acquire a fourth root in an abelian
cyclotomic extension. -/
private theorem exceptional_cyclotomic_radical_data
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    ∃ a : CyclotomicField (2 ^ (M + 2)) ℚ,
      a ^ 2 = algebraMap ℚ (CyclotomicField (2 ^ (M + 2)) ℚ) b ∧
      ∀ x : CyclotomicField (2 ^ (M + 2)) ℚ, x ^ 2 ≠ a := by
  obtain ⟨a, ha⟩ :=
    exists_squareRoot_in_exceptional_cyclotomic M b hM hcase
  refine ⟨a, ha, ?_⟩
  intro x hx
  apply no_fourthPower_in_twoPower_cyclotomic (M + 2) b hb hbmax x
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by ring
    _ = a ^ 2 := by rw [hx]
    _ = algebraMap ℚ (CyclotomicField (2 ^ (M + 2)) ℚ) b := ha

set_option maxHeartbeats 800000 in
private theorem twoPrime_exceptional_kummer_raw
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (a : CyclotomicField (2 ^ (M + 2)) ℚ)
    (ha : a ^ 2 = algebraMap ℚ (CyclotomicField (2 ^ (M + 2)) ℚ) b)
    (H : Irreducible (X ^ 2 - C a)) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        2 ^ (M + 2) ∣ (ell : ℕ) - 1 ∧
        (b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 4) = -1} := by
  let N : ℕ := 2 ^ (M + 2)
  have hN : 0 < N := pow_pos (by omega) (M + 2)
  let F := CyclotomicField N ℚ
  letI : Field F := inferInstance
  letI : Algebra ℚ F := inferInstance
  letI : NeZero N := ⟨hN.ne'⟩
  letI : IsCyclotomicExtension {N} ℚ F :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : NumberField F :=
    IsCyclotomicExtension.numberField {N} ℚ F
  letI : FiniteDimensional ℚ F :=
    IsCyclotomicExtension.finiteDimensional {N} ℚ F
  letI : IsGalois ℚ F :=
    IsCyclotomicExtension.isGalois {N} ℚ F
  letI : Normal ℚ F := IsGalois.to_normal
  let aF : F := by simpa [F, N] using a
  have haF : aF ^ 2 = algebraMap ℚ F b := by
    simpa [aF, F, N] using ha
  let pF : F[X] := X ^ 2 - C aF
  have HpF : Irreducible pF := by simpa [F, N, aF, pF] using H
  letI : Fact (Irreducible pF) := ⟨HpF⟩
  let E := AdjoinRoot pF
  letI : Field E := AdjoinRoot.instField
  letI : Algebra F E := inferInstance
  letI : Algebra ℚ E := inferInstance
  letI : IsScalarTower ℚ F E := inferInstance
  let zetaN : F := IsCyclotomicExtension.zeta N ℚ F
  have hzetaN : IsPrimitiveRoot zetaN N :=
    IsCyclotomicExtension.zeta_spec N ℚ F
  let d2 : ℕ := 2 ^ (M + 1)
  have hNfac2 : N = d2 * 2 := by
    dsimp [N, d2]
    rw [show M + 2 = (M + 1) + 1 by omega, pow_succ]
  let zeta2 : F := zetaN ^ d2
  have hzeta2 : IsPrimitiveRoot zeta2 2 := hzetaN.pow hN hNfac2
  have hroots2 : (primitiveRoots 2 F).Nonempty := by
    refine ⟨zeta2, (mem_primitiveRoots (by norm_num)).2 hzeta2⟩
  letI : Polynomial.IsSplittingField F E pF := by
    exact isSplittingField_AdjoinRoot_X_pow_sub_C hroots2 HpF
  let d4 : ℕ := 2 ^ M
  have hNfac4 : N = d4 * 4 := by
    dsimp [N, d4]
    rw [pow_add]
    norm_num
  let zeta4 : F := zetaN ^ d4
  have hzeta4 : IsPrimitiveRoot zeta4 4 := hzetaN.pow hN hNfac4
  let alpha : E := AdjoinRoot.root pF
  have halpha2 : alpha ^ 2 = algebraMap F E aF := by
    change (AdjoinRoot.root pF) ^ 2 = AdjoinRoot.of pF aF
    simpa [pF] using root_X_pow_sub_C_pow 2 aF
  have halpha4F : alpha ^ 4 =
      algebraMap F E (algebraMap ℚ F b) := by
    calc
      alpha ^ 4 = (alpha ^ 2) ^ 2 := by ring
      _ = (algebraMap F E aF) ^ 2 := by rw [halpha2]
      _ = algebraMap F E (aF ^ 2) := by rw [map_pow]
      _ = algebraMap F E (algebraMap ℚ F b) := by rw [haF]
  have halpha4 : alpha ^ 4 = algebraMap ℚ E b := by
    rw [halpha4F, IsScalarTower.algebraMap_apply ℚ F E]
  let gF : F[X] := X ^ 4 - C (algebraMap ℚ F b)
  have hgF0 : gF ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
  letI : Polynomial.IsSplittingField F E gF := by
    constructor
    · dsimp [gF]
      simpa using X_pow_sub_C_splits_of_isPrimitiveRoot
        (hzeta4.map_of_injective (algebraMap F E).injective) halpha4F
    · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne hgF0,
        aeval_def]
      change eval₂ (algebraMap F E) alpha gF = 0
      simp [gF, halpha4, IsScalarTower.algebraMap_apply ℚ F E]
  let f : ℚ[X] := X ^ N - 1
  let g : ℚ[X] := X ^ 4 - C (b : ℚ)
  have hf : f ≠ 0 := by
    simpa [f] using (X_pow_sub_C_ne_zero hN (1 : ℚ))
  have hg : g ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) (b : ℚ)
  have hmapg : g.map (algebraMap ℚ F) = gF := by
    simp [g, gF]
  letI : Polynomial.IsSplittingField F E (g.map (algebraMap ℚ F)) := by
    rw [hmapg]
    infer_instance
  letI : Polynomial.IsSplittingField ℚ F f := by
    simpa [f] using
      (IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ F)
  letI : Polynomial.IsSplittingField ℚ E (f * g) :=
    Polynomial.IsSplittingField.mul (F := ℚ) (K := F) E f g hf hg
  letI : FiniteDimensional ℚ E :=
    Polynomial.IsSplittingField.finiteDimensional E (f * g)
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : Normal ℚ E := Normal.of_isSplittingField (f * g)
  letI : IsGalois ℚ E := IsGalois.mk
  let eta : rootsOfUnity 2 F := hzeta2.toRootsOfUnity
  let sigmaF : E ≃ₐ[F] E := autAdjoinRootXPowSubC 2 aF eta
  let sigma : E ≃ₐ[ℚ] E := sigmaF.restrictScalars ℚ
  have hsigma_ne : sigma ≠ 1 := by
    intro hs
    have hr := congrArg (fun t : E ≃ₐ[ℚ] E => t (AdjoinRoot.root pF)) hs
    change sigmaF (AdjoinRoot.root pF) = AdjoinRoot.root pF at hr
    rw [autAdjoinRootXPowSubC_root] at hr
    have hr' : AdjoinRoot.of pF zeta2 * AdjoinRoot.root pF =
        AdjoinRoot.root pF := by
      simpa [eta, Algebra.smul_def, pF] using hr
    have hroot0 : AdjoinRoot.root pF ≠ 0 := by
      simpa [pF] using
        (root_X_pow_sub_C_ne_zero' (by norm_num : 0 < 2)
          (show aF ≠ 0 by
            intro ha0
            have hb0 : algebraMap ℚ F b = 0 := by
              rw [← haF, ha0, zero_pow (by norm_num)]
            have hbQ : (b : ℚ) = 0 :=
              (algebraMap ℚ F).injective (by simpa using hb0)
            exact (show (b : ℚ) ≠ 0 by
              exact_mod_cast (show b ≠ 0 by omega)) hbQ))
    have hz1of : AdjoinRoot.of pF zeta2 = 1 := by
      apply mul_right_cancel₀ hroot0
      simpa using hr'
    have hz1 : algebraMap F E zeta2 = 1 := by
      change AdjoinRoot.of pF zeta2 = 1
      exact hz1of
    have : zeta2 = 1 := (algebraMap F E).injective hz1
    exact hzeta2.ne_one (by norm_num) this
  have hinf : Set.Infinite (NU.Chebotarev.frobeniusPrimeSet
      (K := ℚ) (L := E) (ConjClasses.mk sigma)) := by
    intro hfinite
    have hden := NU.Chebotarev.chebotarev_dirichletDensity
      (K := ℚ) (L := E) (ConjClasses.mk sigma)
    have hzero := NU.Chebotarev.finite_primeSet_hasDirichletDensity_zero hfinite
    have heq : (((ConjClasses.mk sigma).carrier.ncard : ℝ) /
        (Nat.card (E ≃ₐ[ℚ] E) : ℝ)) = 0 := tendsto_nhds_unique hden hzero
    have hnum : (0 : ℝ) < ((ConjClasses.mk sigma).carrier.ncard : ℝ) := by
      exact_mod_cast ((Set.ncard_pos (s := (ConjClasses.mk sigma).carrier)).2
        (show (ConjClasses.mk sigma).carrier.Nonempty from
          ⟨sigma, ConjClasses.mem_carrier_mk⟩))
    have hdenom : (0 : ℝ) < Nat.card (E ≃ₐ[ℚ] E) := by
      exact_mod_cast Nat.card_pos (α := E ≃ₐ[ℚ] E)
    exact (div_pos hnum hdenom).ne' heq
  have hmod_for_prime : ∀ v ∈ NU.Chebotarev.frobeniusPrimeSet
      (K := ℚ) (L := E) (ConjClasses.mk sigma),
      NU.LocalTheory.residueCharacteristic v ≠ 2 →
      ¬ NU.LocalTheory.residueCharacteristic v ∣ b →
      N ∣ NU.LocalTheory.residueCharacteristic v - 1 ∧
        (b : ZMod (NU.LocalTheory.residueCharacteristic v)) ^
          ((NU.LocalTheory.residueCharacteristic v - 1) / 4) = -1 := by
    intro v hv hell hbprime
    rcases hv with ⟨hunr, P, hPv, hclass⟩
    let phi : E ≃ₐ[ℚ] E :=
      NU.Chebotarev.arithFrobeniusAt (K := ℚ) (L := E) P
    have hconj : IsConj phi sigma := by
      exact ConjClasses.mk_eq_mk_iff_isConj.mp hclass
    let res : (E ≃ₐ[ℚ] E) →* (F ≃ₐ[ℚ] F) :=
      AlgEquiv.restrictNormalHom F
    have hrsigma : res sigma = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap F E).injective
      change algebraMap F E ((sigma.restrictNormal F) x) =
        algebraMap F E x
      rw [AlgEquiv.restrictNormal_commutes]
      change sigmaF (algebraMap F E x) = algebraMap F E x
      exact sigmaF.commutes x
    have hrphi : res phi = 1 := by
      have hc := res.map_isConj hconj
      rw [hrsigma] at hc
      exact isConj_one_left.mp hc
    let Q : NU.Chebotarev.PrimeIdeal F :=
      NU.LocalTheory.restrictFinitePlace F P
    have hPQ : P.asIdeal.LiesOver Q.asIdeal := by
      refine ⟨?_⟩
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal]
    have hQv : Q.asIdeal.LiesOver v.asIdeal := by
      refine ⟨?_⟩
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal,
        Ideal.under_under, hPv.over]
    have hPunr : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers ℚ) P.asIdeal := hunr P hPv
    have hfrobQ : NU.Chebotarev.arithFrobeniusAt
        (K := ℚ) (L := F) Q = 1 := by
      rw [← NU.Chebotarev.arithFrobAt_restrict P Q hPQ hPunr]
      exact hrphi
    have hNnotQ : algebraMap ℤ (NumberField.RingOfIntegers F) (N : ℤ) ∉
        Q.asIdeal := by
      intro hNQ
      have htowerInt :
          algebraMap (NumberField.RingOfIntegers ℚ)
              (NumberField.RingOfIntegers F)
              (algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ)) =
            algebraMap ℤ (NumberField.RingOfIntegers F) (N : ℤ) := by
        apply NumberField.RingOfIntegers.coe_injective (K := F)
        simp
      have hNvUnder :
          algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ) ∈
            Q.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
        rw [Ideal.mem_under, htowerInt]
        exact hNQ
      have hNv : algebraMap ℤ (NumberField.RingOfIntegers ℚ) (N : ℤ) ∈
          v.asIdeal := by
        rw [← hQv.over] at hNvUnder
        exact hNvUnder
      have hell_dvd_N : NU.LocalTheory.residueCharacteristic v ∣ N :=
        (intCast_mem_ratPrime_iff_dvd v N).mp hNv
      have hell_dvd_two : NU.LocalTheory.residueCharacteristic v ∣ 2 :=
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).dvd_of_dvd_pow
          (by simpa [N] using hell_dvd_N)
      exact hell ((Nat.prime_dvd_prime_iff_eq
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v)
        Nat.prime_two).mp hell_dvd_two)
    have hQunr : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers ℚ) Q.asIdeal := by
      letI : P.asIdeal.LiesOver Q.asIdeal := hPQ
      letI : Algebra.IsUnramifiedAt
          (NumberField.RingOfIntegers ℚ) P.asIdeal := hPunr
      exact Algebra.IsUnramifiedAt.of_liesOver
        (NumberField.RingOfIntegers ℚ) Q.asIdeal P.asIdeal
    have hzact := NU.Chebotarev.arithFrobAt_apply_rootOfUnity
      v Q hQv hQunr N zetaN hzetaN.pow_eq_one hNnotQ
    have hzact' : zetaN =
        zetaN ^ NU.LocalTheory.residueCharacteristic v := by
      simpa [hfrobQ, norm_eq_residueCharacteristic_rat] using hzact
    have hpows : zetaN ^ NU.LocalTheory.residueCharacteristic v =
        zetaN ^ 1 := by simpa using hzact'.symm
    have hpowsU : hzetaN.toRootsOfUnity ^
        NU.LocalTheory.residueCharacteristic v =
        hzetaN.toRootsOfUnity ^ 1 := by
      apply rootsOfUnity.coe_injective
      simpa only [rootsOfUnity.coe_pow, hzetaN.val_toRootsOfUnity_coe] using hpows
    have hmodEq0 := (pow_eq_pow_iff_modEq).mp hpowsU
    have hmodEq : NU.LocalTheory.residueCharacteristic v ≡ 1 [MOD N] := by
      rw [← Subgroup.orderOf_coe, ← orderOf_units,
        hzetaN.val_toRootsOfUnity_coe, ← hzetaN.eq_orderOf] at hmodEq0
      exact hmodEq0
    have hmodResult : N ∣ NU.LocalTheory.residueCharacteristic v - 1 :=
      (Nat.modEq_iff_dvd'
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).one_le).mp
        hmodEq.symm
    obtain ⟨tau, htau⟩ := isConj_iff.mp hconj
    let beta : E := tau.symm alpha
    let xi : E := tau.symm (AdjoinRoot.of pF zeta2)
    have hsigma_alpha : sigma alpha = AdjoinRoot.of pF zeta2 * alpha := by
      change sigmaF (AdjoinRoot.root pF) = _
      simpa [alpha, eta, Algebra.smul_def, pF] using
        (autAdjoinRootXPowSubC_root aF eta)
    have hphi_beta : phi beta = xi * beta := by
      have happ := congrArg (fun s : E ≃ₐ[ℚ] E => s alpha) htau
      have happ' : tau (phi (tau.symm alpha)) = sigma alpha := by
        simpa using happ
      apply tau.injective
      rw [map_mul]
      change tau (phi (tau.symm alpha)) =
        tau (tau.symm (AdjoinRoot.of pF zeta2)) * tau (tau.symm alpha)
      rw [tau.apply_symm_apply, tau.apply_symm_apply, happ', hsigma_alpha]
    have hbeta4 : beta ^ 4 = algebraMap ℚ E b := by
      change (tau.symm alpha) ^ 4 = _
      rw [← map_pow, halpha4]
      exact tau.symm.commutes b
    have hzetaE : IsPrimitiveRoot (AdjoinRoot.of pF zeta2 : E) 2 := by
      rw [← AdjoinRoot.algebraMap_eq]
      exact hzeta2.map_of_injective (algebraMap F E).injective
    have hxi : IsPrimitiveRoot xi 2 :=
      hzetaE.map_of_injective tau.symm.injective
    have hxi_neg : xi = -1 := hxi.eq_neg_one_of_two_right
    have hbetaInt : IsIntegral ℤ beta := by
      refine ⟨X ^ 4 - C (b : ℤ),
        monic_X_pow_sub_C _ (by norm_num), ?_⟩
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [hbeta4]
      simp
    have hrestrictP : NU.LocalTheory.restrictFinitePlace ℚ P = v := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [NU.LocalTheory.restrictFinitePlace_asIdeal, hPv.over]
    have hcharP : NU.LocalTheory.residueCharacteristic P =
        NU.LocalTheory.residueCharacteristic v := by
      rw [← NU.NeukirchUchida.LocalInvariants.residueCharacteristic_restrictFinitePlace ℚ P,
        hrestrictP]
    let k := NumberField.RingOfIntegers E ⧸ P.asIdeal
    letI : Field k := Ideal.Quotient.field P.asIdeal
    letI : Fintype k := Fintype.ofFinite k
    have hringChar : ringChar k = NU.LocalTheory.residueCharacteristic v := by
      rw [Ideal.ringChar_quot,
        ← NU.NeukirchUchida.LocalInvariants.residueCharacteristic_eq_absNorm_under,
        hcharP]
    letI : CharP k (NU.LocalTheory.residueCharacteristic v) :=
      (ringChar.eq_iff).mp hringChar
    letI : P.asIdeal.LiesOver v.asIdeal := hPv
    have hnormPcoprime : (Ideal.absNorm P.asIdeal).Coprime 2 := by
      rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.asIdeal]
      change (NU.Chebotarev.PrimeIdeal.norm v ^ _).Coprime 2
      rw [norm_eq_residueCharacteristic_rat]
      exact ((Nat.coprime_primes
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v)
        Nat.prime_two).mpr hell).pow_left _
    have hnormP_ne_one : Ideal.absNorm P.asIdeal ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr P.isMaximal.ne_top
    let xiI : NumberField.RingOfIntegers E := hxi.toInteger
    let betaI : NumberField.RingOfIntegers E := ⟨beta, hbetaInt⟩
    let rxi : k := Ideal.Quotient.mk P.asIdeal xiI
    let rbeta : k := Ideal.Quotient.mk P.asIdeal betaI
    have hrxi : IsPrimitiveRoot rxi 2 :=
      hxi.toInteger_isPrimitiveRoot.idealQuotient_mk
        hnormP_ne_one hnormPcoprime
    have hxiI_neg : xiI = -1 := by
      apply Subtype.ext
      exact hxi_neg
    have hrxi_neg : rxi = -1 := by
      change Ideal.Quotient.mk P.asIdeal xiI = -1
      rw [hxiI_neg, map_neg, map_one]
    have hbetaPowInt : betaI ^ 4 =
        algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ) := by
      apply NumberField.RingOfIntegers.coe_injective (K := E)
      change beta ^ 4 = _
      rw [hbeta4]
      simp
    have hrbeta_ne : rbeta ≠ 0 := by
      intro hrbeta0
      have hbzero : (b : k) = 0 := by
        calc
          (b : k) = Ideal.Quotient.mk P.asIdeal
              (algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ)) := by simp
          _ = Ideal.Quotient.mk P.asIdeal (betaI ^ 4) := by rw [hbetaPowInt]
          _ = rbeta ^ 4 := by rw [map_pow]
          _ = 0 := by rw [hrbeta0, zero_pow (by norm_num)]
      exact hbprime ((CharP.cast_eq_zero_iff k
        (NU.LocalTheory.residueCharacteristic v) b).mp hbzero)
    have hcard : Nat.card (NumberField.RingOfIntegers ℚ ⧸
        P.asIdeal.under (NumberField.RingOfIntegers ℚ)) =
        NU.LocalTheory.residueCharacteristic v := by
      calc
        Nat.card (NumberField.RingOfIntegers ℚ ⧸
            P.asIdeal.under (NumberField.RingOfIntegers ℚ)) =
            Nat.card (NumberField.RingOfIntegers ℚ ⧸ v.asIdeal) := by
              rw [hPv.over]
        _ = Ideal.absNorm v.asIdeal := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        _ = NU.Chebotarev.PrimeIdeal.norm v := rfl
        _ = NU.LocalTheory.residueCharacteristic v :=
          norm_eq_residueCharacteristic_rat v
    have hfrobBeta := (IsArithFrobAt.arithFrobAt
      (NumberField.RingOfIntegers ℚ) (E ≃ₐ[ℚ] E) P.asIdeal) betaI
    have hquotAction : Ideal.Quotient.mk P.asIdeal (phi • betaI) =
        rbeta ^ NU.LocalTheory.residueCharacteristic v := by
      rw [← sub_eq_zero]
      change Ideal.Quotient.mk P.asIdeal (phi • betaI) -
        (Ideal.Quotient.mk P.asIdeal betaI) ^
          NU.LocalTheory.residueCharacteristic v = 0
      rw [← map_pow, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers ℚ)
          (NumberField.RingOfIntegers E) phi) betaI -
        betaI ^ NU.LocalTheory.residueCharacteristic v ∈ P.asIdeal
      simpa only [hcard, phi, NU.Chebotarev.arithFrobeniusAt] using hfrobBeta
    have hactInt : phi • betaI = xiI * betaI := by
      apply Subtype.ext
      exact hphi_beta
    have hresAction : rxi * rbeta =
        rbeta ^ NU.LocalTheory.residueCharacteristic v := by
      rw [← map_mul, ← hactInt]
      exact hquotAction
    have hsubadd : NU.LocalTheory.residueCharacteristic v - 1 + 1 =
        NU.LocalTheory.residueCharacteristic v :=
      Nat.sub_add_cancel
        (NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v).one_le
    have hrbeta_power :
        rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) = rxi := by
      apply mul_right_cancel₀ hrbeta_ne
      calc
        rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) * rbeta =
            rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1 + 1) := by
              rw [pow_succ]
        _ = rbeta ^ NU.LocalTheory.residueCharacteristic v := by rw [hsubadd]
        _ = rxi * rbeta := hresAction.symm
    have hfourN : 4 ∣ N := ⟨d4, by simpa [mul_comm] using hNfac4⟩
    have hfourL : 4 ∣ NU.LocalTheory.residueCharacteristic v - 1 :=
      dvd_trans hfourN hmodResult
    have hmuldiv : 4 *
        ((NU.LocalTheory.residueCharacteristic v - 1) / 4) =
          NU.LocalTheory.residueCharacteristic v - 1 :=
      Nat.mul_div_cancel' hfourL
    have hrbeta4 : rbeta ^ 4 = (b : k) := by
      calc
        rbeta ^ 4 = Ideal.Quotient.mk P.asIdeal (betaI ^ 4) := by rw [map_pow]
        _ = Ideal.Quotient.mk P.asIdeal
            (algebraMap ℤ (NumberField.RingOfIntegers E) (b : ℤ)) := by
              rw [hbetaPowInt]
        _ = (b : k) := by simp
    have hbpowerK : (b : k) ^
        ((NU.LocalTheory.residueCharacteristic v - 1) / 4) = rxi := by
      calc
        (b : k) ^ ((NU.LocalTheory.residueCharacteristic v - 1) / 4) =
            (rbeta ^ 4) ^
              ((NU.LocalTheory.residueCharacteristic v - 1) / 4) := by
                rw [hrbeta4]
        _ = rbeta ^ (4 *
              ((NU.LocalTheory.residueCharacteristic v - 1) / 4)) := by
                rw [pow_mul]
        _ = rbeta ^ (NU.LocalTheory.residueCharacteristic v - 1) := by
              rw [hmuldiv]
        _ = rxi := hrbeta_power
    refine ⟨hmodResult, ?_⟩
    letI : Fact (NU.LocalTheory.residueCharacteristic v).Prime :=
      ⟨NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v⟩
    letI : Algebra (ZMod (NU.LocalTheory.residueCharacteristic v)) k :=
      ZMod.algebra k (NU.LocalTheory.residueCharacteristic v)
    apply (algebraMap
      (ZMod (NU.LocalTheory.residueCharacteristic v)) k).injective
    rw [map_pow, map_neg, map_one]
    have hbmap : algebraMap
        (ZMod (NU.LocalTheory.residueCharacteristic v)) k
        (b : ZMod (NU.LocalTheory.residueCharacteristic v)) = (b : k) := by
      simp
    rw [hbmap, hbpowerK, hrxi_neg]
  let toPrime : NU.Chebotarev.PrimeIdeal ℚ → Nat.Primes := fun v =>
    ⟨NU.LocalTheory.residueCharacteristic v,
      NU.NeukirchUchida.LocalInvariants.residueCharacteristic_prime v⟩
  have htoPrime : Function.Injective toPrime := by
    intro v w hvw
    apply NU.NeukirchUchida.LocalInvariants.rationalFinitePlace_eq_of_residueCharacteristic_eq
    exact congrArg Subtype.val hvw
  let Cbad : ℕ := 2 * b
  let D : Set Nat.Primes := {ell | (ell : ℕ) ∣ Cbad}
  have hCbad : 0 < Cbad := by
    dsimp [Cbad]
    exact Nat.mul_pos (by omega) (by omega)
  have hDimage : ((fun ell : Nat.Primes => (ell : ℕ)) '' D).Finite := by
    apply (Set.finite_le_nat Cbad).subset
    rintro n ⟨ell, hell, rfl⟩
    exact Nat.le_of_dvd hCbad hell
  have hD : D.Finite := by
    apply Set.Finite.of_finite_image hDimage
    intro x _ y _ hxy
    exact Subtype.ext hxy
  let B : Set (NU.Chebotarev.PrimeIdeal ℚ) := toPrime ⁻¹' D
  have hB : B.Finite := hD.preimage htoPrime.injOn
  let S := NU.Chebotarev.frobeniusPrimeSet
    (K := ℚ) (L := E) (ConjClasses.mk sigma)
  have hSgood : (S \ B).Infinite := hinf.diff hB
  have himage : (toPrime '' (S \ B)).Infinite :=
    hSgood.image htoPrime.injOn
  apply himage.mono
  rintro ell ⟨v, ⟨hvS, hvB⟩, rfl⟩
  have hnotC : ¬ NU.LocalTheory.residueCharacteristic v ∣ Cbad := hvB
  have hell : NU.LocalTheory.residueCharacteristic v ≠ 2 := by
    intro heq
    apply hnotC
    rw [heq]
    exact dvd_mul_right 2 b
  have hbprime : ¬ NU.LocalTheory.residueCharacteristic v ∣ b := by
    intro hdvd
    apply hnotC
    exact dvd_trans hdvd (dvd_mul_left b 2)
  have hcoprimeTarget :
      ¬ NU.LocalTheory.residueCharacteristic v ∣ 2 * b := hnotC
  obtain ⟨hmod, hpower⟩ := hmod_for_prime v hvS hell hbprime
  exact ⟨hcoprimeTarget, hmod, hpower⟩

/-- Exceptional Chebotarev primes make `b` a square but not a fourth
power.  The Frobenius calculation gives the sharper quartic Euler criterion
`b^((ell-1)/4) = -1`. -/
private theorem twoPrime_exceptional_case
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        2 ^ (M + 2) ∣ (ell : ℕ) - 1 ∧
        (∃ y : ZMod (ell : ℕ), y ^ 2 = (b : ZMod (ell : ℕ))) ∧
        ¬ ∃ x : ZMod (ell : ℕ), x ^ 4 = (b : ZMod (ell : ℕ))} := by
  obtain ⟨a, ha, hnot⟩ :=
    exceptional_cyclotomic_radical_data M b hM hb hbmax hcase
  have hfield : Irreducible (X ^ 2 - C a) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hnot
  have hraw := twoPrime_exceptional_kummer_raw M b hM hb a ha hfield
  apply hraw.mono
  rintro ell ⟨hell, hmod, hquarter⟩
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  have hellb : ¬(ell : ℕ) ∣ b := by
    intro hdvd
    exact hell (dvd_trans hdvd (dvd_mul_left b 2))
  have hell2 : (ell : ℕ) ≠ 2 := by
    intro heq
    apply hell
    rw [heq]
    exact dvd_mul_right 2 b
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hellb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  have hfourN : 4 ∣ 2 ^ (M + 2) := by
    refine ⟨2 ^ M, ?_⟩
    simp [pow_add, mul_comm]
  have hfour : 4 ∣ (ell : ℕ) - 1 := dvd_trans hfourN hmod
  have hfourMul : 4 * (((ell : ℕ) - 1) / 4) = (ell : ℕ) - 1 :=
    Nat.mul_div_cancel' hfour
  have hhalfMul : 2 * (((ell : ℕ) - 1) / 4) =
      ((ell : ℕ) - 1) / 2 := by
    obtain ⟨k, hk⟩ := hfour
    omega
  have hhalf : (b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 2) = 1 := by
    calc
      (b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 2) =
          (b : ZMod (ell : ℕ)) ^
            (2 * (((ell : ℕ) - 1) / 4)) := by rw [hhalfMul]
      _ = ((b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 4)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm _ _
      _ = (-1) ^ 2 := by rw [hquarter]
      _ = 1 := by ring
  have hellHalf : (ell : ℕ) / 2 = ((ell : ℕ) - 1) / 2 := by
    obtain ⟨k, hk⟩ := ell.2.odd_of_ne_two hell2
    omega
  have hsquare : IsSquare (b : ZMod (ell : ℕ)) :=
    (ZMod.euler_criterion (ell : ℕ) hb0).2 (by rwa [hellHalf])
  obtain ⟨y, hy⟩ := hsquare
  refine ⟨hell, hmod, ⟨y, by simpa [pow_two] using hy.symm⟩, ?_⟩
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    have hbzero : (b : ZMod (ell : ℕ)) = 0 := by
      rw [← hx, hxzero, zero_pow (by norm_num)]
    exact hb0 hbzero
  have hbad : (b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 4) = 1 := by
    calc
      (b : ZMod (ell : ℕ)) ^ (((ell : ℕ) - 1) / 4) =
          (x ^ 4) ^ (((ell : ℕ) - 1) / 4) := by rw [hx]
      _ = x ^ (4 * (((ell : ℕ) - 1) / 4)) := by rw [pow_mul]
      _ = x ^ ((ell : ℕ) - 1) := by rw [hfourMul]
      _ = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hneg : (-1 : ZMod (ell : ℕ)) ≠ 1 := by
    intro hneg
    have htwo : (2 : ZMod (ell : ℕ)) = 0 := by
      linear_combination -hneg
    have hdvd : (ell : ℕ) ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 (ell : ℕ)).mp htwo
    exact hell2 ((Nat.prime_dvd_prime_iff_eq ell.2 Nat.prime_two).mp hdvd)
  exact hneg (hquarter.symm.trans hbad)

/-- The exceptional quartic even-prime branch, where the extracted base is
twice a rational square.  This is the second isolated resistant Kummer case. -/
private theorem twoPrime_exceptional_orderPrimes
    (M b : ℕ) (hM : 0 < M) (hb : 1 < b)
    (hbmax : ∀ c : ℚ, c ^ 2 ≠ b)
    (hcase : ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2) :
    Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        2 ^ M ∣ residueMultiplicativeOrder b ell} := by
  have hraw := twoPrime_exceptional_case M b hM hb hbmax hcase
  apply hraw.mono
  rintro ell ⟨hell, hmod, ⟨y, hy⟩, hfourth⟩
  letI : Fact (ell : ℕ).Prime := ⟨ell.2⟩
  have hellb : ¬(ell : ℕ) ∣ b := by
    intro hdvd
    exact hell (dvd_trans hdvd (dvd_mul_left b 2))
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hellb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  have hy0 : y ≠ 0 := by
    intro hyzero
    apply hb0
    rw [← hy, hyzero, zero_pow (by norm_num)]
  have hyCast : (y.val : ZMod (ell : ℕ)) = y := by simp
  have hellY : ¬(ell : ℕ) ∣ y.val := by
    intro hdvd
    have hzero : (y.val : ZMod (ell : ℕ)) = 0 :=
      (ZMod.natCast_eq_zero_iff y.val (ell : ℕ)).2 hdvd
    exact hy0 (hyCast.symm.trans hzero)
  have hnonpower : ¬ ∃ x : ZMod (ell : ℕ),
      x ^ 2 = (y.val : ZMod (ell : ℕ)) := by
    rintro ⟨x, hx⟩
    apply hfourth
    refine ⟨x, ?_⟩
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (y.val : ZMod (ell : ℕ)) ^ 2 := by rw [hx]
      _ = y ^ 2 := by rw [hyCast]
      _ = (b : ZMod (ell : ℕ)) := hy
  have hfac := factorization_orderOf_eq_of_not_primePower ell
    (⟨2, Nat.prime_two⟩ : Nat.Primes) y.val hellY hnonpower
  change (orderOf (y.val : ZMod (ell : ℕ))).factorization 2 =
    ((ell : ℕ) - 1).factorization 2 at hfac
  have hlastPos : 0 < (ell : ℕ) - 1 :=
    Nat.sub_pos_of_lt ell.2.one_lt
  have hlast0 : (ell : ℕ) - 1 ≠ 0 := hlastPos.ne'
  have hvalLast : M + 2 ≤ ((ell : ℕ) - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hlast0).mp hmod
  have hordY0 : orderOf (y.val : ZMod (ell : ℕ)) ≠ 0 := by
    have hyCast0 : (y.val : ZMod (ell : ℕ)) ≠ 0 := by
      rwa [hyCast]
    have hdvd : orderOf (y.val : ZMod (ell : ℕ)) ∣ (ell : ℕ) - 1 :=
      ZMod.orderOf_dvd_card_sub_one hyCast0
    exact (Nat.pos_of_dvd_of_pos hdvd hlastPos).ne'
  have hpowY : 2 ^ (M + 1) ∣
      orderOf (y.val : ZMod (ell : ℕ)) := by
    apply (Nat.prime_two.pow_dvd_iff_le_factorization hordY0).mpr
    rw [hfac]
    omega
  have horderY : orderOf y =
      orderOf (y.val : ZMod (ell : ℕ)) := by
    rw [hyCast]
  have horderDvd : orderOf y ∣ 2 * orderOf (y ^ 2) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact pow_orderOf_eq_one (y ^ 2)
  have htwoPow : 2 * 2 ^ M ∣ 2 * orderOf (y ^ 2) := by
    rw [← pow_succ']
    exact dvd_trans (by simpa [horderY] using hpowY) horderDvd
  have hresult : 2 ^ M ∣ orderOf (y ^ 2) :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) htwoPow
  rw [hy] at hresult
  exact ⟨hell, hresult⟩

/-- **Arithmetic obligation, Blueprint `lem:order`.**  The certified
three-case Chebotarev--Kummer proof of `OrderDivisibilityPrinciple`. -/
private theorem orderDivisibility : OrderDivisibilityPrinciple := by
  intro q hq lambda m
  obtain ⟨h, b, hqb, hb, hbmax, horder⟩ :=
    extract_primePower_with_order_bound lambda q hq
  let M : ℕ := m + h + 1
  have hM : 0 < M := by simp [M]
  have hbase : Set.Infinite {ell : Nat.Primes |
      ¬(ell : ℕ) ∣ 2 * b ∧
        (lambda : ℕ) ^ M ∣ residueMultiplicativeOrder b ell} := by
    by_cases hlambda : (lambda : ℕ) = 2
    · have heq : lambda = (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
        Subtype.ext hlambda
      subst lambda
      by_cases hcase : ∃ c : ℚ, (b : ℚ) = 2 * c ^ 2
      · simpa using
          twoPrime_exceptional_orderPrimes M b hM hb hbmax hcase
      · simpa using
          twoPrime_nonexceptional_orderPrimes M b hM hb hbmax hcase
    · have hraw := oddPrime_case lambda hlambda M b hM hb hbmax
      apply hraw.mono
      rintro ell ⟨hell, hmod, hnonpower⟩
      have hellb : ¬(ell : ℕ) ∣ b := by
        intro hdvd
        exact hell (dvd_trans hdvd (dvd_mul_left b 2))
      have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
        intro hzero
        exact hellb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
      have hlastPos : 0 < (ell : ℕ) - 1 :=
        Nat.sub_pos_of_lt ell.2.one_lt
      have hord0 : residueMultiplicativeOrder b ell ≠ 0 := by
        have hdvd := ZMod.orderOf_dvd_card_sub_one hb0
        exact (Nat.pos_of_dvd_of_pos hdvd hlastPos).ne'
      have hlast0 : (ell : ℕ) - 1 ≠ 0 := hlastPos.ne'
      have hvalLast : M ≤ ((ell : ℕ) - 1).factorization
          (lambda : ℕ) :=
        (lambda.2.pow_dvd_iff_le_factorization hlast0).mp hmod
      have hfac := factorization_orderOf_eq_of_not_primePower
        ell lambda b hellb hnonpower
      refine ⟨hell, (lambda.2.pow_dvd_iff_le_factorization hord0).mpr ?_⟩
      rw [hfac]
      exact hvalLast
  apply hbase.mono
  rintro ell ⟨hell, hpowOrder⟩
  have hellb : ¬(ell : ℕ) ∣ b := by
    intro hdvd
    exact hell (dvd_trans hdvd (dvd_mul_left b 2))
  have hell2 : ¬(ell : ℕ) ∣ 2 := by
    intro hdvd
    exact hell (dvd_mul_of_dvd_left hdvd b)
  have hellq : ¬(ell : ℕ) ∣ q := by
    rw [hqb]
    intro hdvd
    exact hellb (ell.2.dvd_of_dvd_pow hdvd)
  have havoidq : ¬(ell : ℕ) ∣ 2 * q := by
    intro hdvd
    rcases ell.2.dvd_mul.mp hdvd with htwo | hqdiv
    · exact hell2 htwo
    · exact hellq hqdiv
  have hb0 : (b : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hellb ((ZMod.natCast_eq_zero_iff b (ell : ℕ)).mp hzero)
  have hq0 : (q : ZMod (ell : ℕ)) ≠ 0 := by
    intro hzero
    exact hellq ((ZMod.natCast_eq_zero_iff q (ell : ℕ)).mp hzero)
  have hlastPos : 0 < (ell : ℕ) - 1 :=
    Nat.sub_pos_of_lt ell.2.one_lt
  have hordb0 : residueMultiplicativeOrder b ell ≠ 0 := by
    have hdvd := ZMod.orderOf_dvd_card_sub_one hb0
    exact (Nat.pos_of_dvd_of_pos hdvd hlastPos).ne'
  have hordq0 : residueMultiplicativeOrder q ell ≠ 0 := by
    have hdvd := ZMod.orderOf_dvd_card_sub_one hq0
    exact (Nat.pos_of_dvd_of_pos hdvd hlastPos).ne'
  have hvalb : M ≤ (residueMultiplicativeOrder b ell).factorization
      (lambda : ℕ) :=
    (lambda.2.pow_dvd_iff_le_factorization hordb0).mp hpowOrder
  have hbound := horder ell hellb
  have hvalq : m ≤ (residueMultiplicativeOrder q ell).factorization
      (lambda : ℕ) := by
    omega
  exact ⟨havoidq,
    (lambda.2.pow_dvd_iff_le_factorization hordq0).mpr hvalq⟩

/-- A concrete product model of `zhat = product_p Z_p`. -/
private abbrev ProfiniteIntegers := ∀ p : Nat.Primes, ℤ_[p]

/-- The diagonal image of a natural number in `zhat`. -/
private def profiniteIntegerOfNat (n : ℕ) : ProfiniteIntegers :=
  fun _ => n

/-- The diagonal embedding of natural numbers into `zhat` is injective. -/
private theorem profiniteIntegerOfNat_injective :
    Function.Injective profiniteIntegerOfNat := by
  intro a b h
  have htwo := congrFun h (⟨2, Nat.prime_two⟩ : Nat.Primes)
  change (a : ℤ_[2]) = (b : ℤ_[2]) at htwo
  exact Nat.cast_injective htwo

/-- The profinite integer `-1` is not the diagonal image of a natural
number. -/
private theorem neg_one_ne_profiniteIntegerOfNat (j : ℕ) :
    (-1 : ProfiniteIntegers) ≠ profiniteIntegerOfNat j := by
  intro h
  have htwo := congrFun h (⟨2, Nat.prime_two⟩ : Nat.Primes)
  change (-1 : ℤ_[2]) = (j : ℤ_[2]) at htwo
  have hz : ((j + 1 : ℕ) : ℤ_[2]) = 0 := by
    push_cast
    rw [← htwo]
    ring
  exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) hz

/-- The diagonal embedding preserves multiplication. -/
private theorem profiniteIntegerOfNat_mul (a b : ℕ) :
    profiniteIntegerOfNat (a * b) =
      profiniteIntegerOfNat a * profiniteIntegerOfNat b := by
  funext p
  simp [profiniteIntegerOfNat]

/-- Multiplication by a positive natural number is injective on `zhat`. -/
private theorem profiniteIntegerOfNat_mul_injective
    {n : ℕ} (hn : n ≠ 0) :
    Function.Injective
      (fun x : ProfiniteIntegers => profiniteIntegerOfNat n * x) := by
  intro x y hxy
  funext p
  have hp := congrFun hxy p
  change (n : ℤ_[p]) * x p = (n : ℤ_[p]) * y p at hp
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn) hp

/-- **Arithmetic micro-obligation, Blueprint `lem:bridge`.**  This is the
intersection identity `b zhat ∩ Z = b Z`: if a diagonal natural number lies
in the principal ideal generated by `b`, then `b ∣ a` in `Z`. -/
private theorem profiniteInteger_nat_dvd_of_eq_mul
    (a b : ℕ) (x : ProfiniteIntegers)
    (h : profiniteIntegerOfNat a = profiniteIntegerOfNat b * x) :
    b ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    subst b
    have htwo := congrFun h (⟨2, Nat.prime_two⟩ : Nat.Primes)
    change (a : ℤ_[2]) = (0 : ℤ_[2]) * x ⟨2, Nat.prime_two⟩ at htwo
    simp only [zero_mul] at htwo
    exact ha (Nat.cast_injective htwo)
  apply (Nat.factorization_prime_le_iff_dvd hb ha).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let P : Nat.Primes := ⟨p, hp⟩
  let k := b.factorization p
  have hcoord := congrFun h P
  change (a : ℤ_[p]) = (b : ℤ_[p]) * x P at hcoord
  have hz : (a : ZMod (p ^ k)) =
      (b : ZMod (p ^ k)) * PadicInt.toZModPow k (x P) := by
    simpa using congrArg (PadicInt.toZModPow k) hcoord
  have hbpow : p ^ k ∣ b :=
    (hp.pow_dvd_iff_le_factorization hb).2 le_rfl
  have hbzero : (b : ZMod (p ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff b (p ^ k)).2 hbpow
  have hazero : (a : ZMod (p ^ k)) = 0 := by
    simpa [hbzero] using hz
  exact (hp.pow_dvd_iff_le_factorization ha).1
    ((ZMod.natCast_eq_zero_iff a (p ^ k)).1 hazero)

/-- Formal `zhat`-linear core of Blueprint `prop:q`: a unit carrying one
positive diagonal integer to another forces equality of the integers and is
itself one. -/
private theorem profinite_relation_rigid
    {f f' : ℕ} (hf : f ≠ 0) (_hf' : f' ≠ 0)
    (u : ProfiniteIntegersˣ)
    (h : profiniteIntegerOfNat f =
      profiniteIntegerOfNat f' * (u : ProfiniteIntegers)) :
    f = f' ∧ u = 1 := by
  have hdvd₁ : f' ∣ f :=
    profiniteInteger_nat_dvd_of_eq_mul f f' (u : ProfiniteIntegers) h
  have hinv : profiniteIntegerOfNat f' =
      profiniteIntegerOfNat f * (u⁻¹ : ProfiniteIntegersˣ) := by
    calc
      profiniteIntegerOfNat f' =
          profiniteIntegerOfNat f' *
            ((u : ProfiniteIntegers) * (u⁻¹ : ProfiniteIntegersˣ)) := by simp
      _ = (profiniteIntegerOfNat f' * (u : ProfiniteIntegers)) *
          (u⁻¹ : ProfiniteIntegersˣ) := by rw [mul_assoc]
      _ = profiniteIntegerOfNat f * (u⁻¹ : ProfiniteIntegersˣ) := by rw [h]
  have hdvd₂ : f ∣ f' :=
    profiniteInteger_nat_dvd_of_eq_mul f' f
      (u⁻¹ : ProfiniteIntegersˣ) hinv
  have hff : f = f' := Nat.dvd_antisymm hdvd₂ hdvd₁
  refine ⟨hff, ?_⟩
  apply Units.ext
  apply profiniteIntegerOfNat_mul_injective hf
  simpa [hff] using h.symm

/-- The inclusion of a contracted valuation ring into the original
valuation ring. -/
private def valuationComapInclusion
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : A.comap f →+* A where
  toFun x := ⟨f x, x.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- Inclusion into a valuation ring is a local homomorphism after contracting
the valuation ring to the source field. -/
private theorem valuationComapInclusion_isLocal
    {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (A : ValuationSubring E) : IsLocalHom (valuationComapInclusion f A) := by
  apply IsLocalHom.mk
  intro x hx
  have hfx0 : f (x : F) ≠ 0 := by
    intro hzero
    apply IsUnit.ne_zero hx
    apply Subtype.ext
    exact hzero
  have hx0 : (x : F) ≠ 0 := (map_ne_zero f).mp hfx0
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hyval : (y : E) = (f (x : F))⁻¹ := by
    apply mul_left_cancel₀ hfx0
    have hy' := congrArg Subtype.val hy
    change f (x : F) * (y : E) = 1 at hy'
    rw [hy', mul_inv_cancel₀ hfx0]
  let y' : A.comap f := ⟨(x : F)⁻¹, by
    change f ((x : F)⁻¹) ∈ A
    rw [map_inv₀, ← hyval]
    exact y.property⟩
  exact isUnit_iff_exists_inv.mpr ⟨y', by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0⟩

/-- Residue-field formation is natural for a commuting square of local
ring automorphisms. -/
private theorem residueMap_mapEquiv_commute
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (eA : A ≃+* A) (eB : B ≃+* B)
    (hcomm : ∀ x, f (eA x) = eB (f x)) :
    ∀ z, IsLocalRing.ResidueField.map f
        (IsLocalRing.ResidueField.mapEquiv eA z) =
      IsLocalRing.ResidueField.mapEquiv eB
        (IsLocalRing.ResidueField.map f z) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue]
  change IsLocalRing.residue B (f (eA x)) =
    IsLocalRing.residue B (eB (f x))
  rw [hcomm]

/-- Inclusion of nested finite Galois levels on the valuation rings cut
out by one absolute place. -/
private noncomputable def finiteLevelValuationMap
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M) :
    NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) →+*
      NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 M) := by
  let wL := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let wM := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 M
  let i : L.field →+* M.field :=
    (IntermediateField.inclusion hLM).toRingHom
  have hAL : NU.LocalTheory.primeValuationSubring wL =
      P.1.comap L.field.val.toRingHom :=
    NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
  have hAM : NU.LocalTheory.primeValuationSubring wM =
      P.1.comap M.field.val.toRingHom :=
    NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
  exact
    { toFun := fun x => ⟨i x, by
        rw [hAM, ValuationSubring.mem_comap]
        change (x : AlgebraicClosure K) ∈ P.1
        have hx : (x : L.field) ∈
            P.1.comap L.field.val.toRingHom := by
          rw [← hAL]
          exact x.property
        exact hx⟩
      map_zero' := by ext; simp [i]
      map_one' := by ext; simp [i]
      map_add' := fun x y => by ext; simp [i]
      map_mul' := fun x y => by ext; simp [i] }

private theorem finiteLevelValuationMap_isLocal
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M) :
    IsLocalHom (finiteLevelValuationMap P hLM) := by
  apply IsLocalHom.mk
  intro x hx
  let f := finiteLevelValuationMap P hLM
  have hfx0 : (f x : M.field) ≠ 0 := by
    intro hzero
    apply IsUnit.ne_zero hx
    apply Subtype.ext
    exact hzero
  have hx0 : (x : L.field) ≠ 0 := by
    intro hzero
    apply hfx0
    change (IntermediateField.inclusion hLM) (x : L.field) = 0
    rw [hzero, map_zero]
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hyval : (y : M.field) = (f x : M.field)⁻¹ := by
    apply mul_left_cancel₀ hfx0
    have hy' := congrArg Subtype.val hy
    change (f x : M.field) * (y : M.field) = 1 at hy'
    rw [hy', mul_inv_cancel₀ hfx0]
  have hyP : ((x : L.field)⁻¹ : AlgebraicClosure K) ∈ P.1 := by
    have hymem : (y : M.field) ∈
        P.1.comap M.field.val.toRingHom := by
      rw [← NU.LocalTheory.primeValuationSubring_centerFinitePlace
        (P.1.comap M.field.val.toRingHom)
        (NU.LocalTheory.absolutePlace_comap_nontrivial P.1 P.2 M)]
      exact y.property
    change (y : AlgebraicClosure K) ∈ P.1 at hymem
    have heq : (y : AlgebraicClosure K) =
        ((x : L.field)⁻¹ : AlgebraicClosure K) := by
      rw [hyval]
      rfl
    rwa [← heq]
  let y' : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) :=
    ⟨(x : L.field)⁻¹, by
      have hAL : NU.LocalTheory.primeValuationSubring
          (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) =
          P.1.comap L.field.val.toRingHom :=
        NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
      apply (ValuationSubring.ext_iff.mp hAL ((x : L.field)⁻¹)).mpr
      exact hyP⟩
  exact isUnit_iff_exists_inv.mpr ⟨y', by
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0⟩

/-- The valuation ring at a finite level is the contraction of the
absolute valuation ring, packaged as a ring equivalence. -/
private noncomputable def finiteLevelValuationEquivComap
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) ≃+*
      P.1.comap L.field.val.toRingHom := by
  have hA : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) =
        P.1.comap L.field.val.toRingHom :=
    NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
  exact
    { toFun := fun x => ⟨x, by rw [← hA]; exact x.property⟩
      invFun := fun x => ⟨x, by rw [hA]; exact x.property⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }

/-- Inclusion of a finite-level valuation ring into the absolute valuation
ring. -/
private noncomputable def finiteLevelAbsoluteValuationMap
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.primeValuationSubring
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) →+* P.1 :=
  (valuationComapInclusion L.field.val.toRingHom P.1).comp
    (finiteLevelValuationEquivComap P L).toRingHom

private theorem finiteLevelAbsoluteValuationMap_isLocal
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    IsLocalHom (finiteLevelAbsoluteValuationMap P L) := by
  let e := finiteLevelValuationEquivComap P L
  let f := valuationComapInclusion L.field.val.toRingHom P.1
  letI : IsLocalHom e.toRingHom :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  letI : IsLocalHom f := valuationComapInclusion_isLocal _ _
  exact RingHom.isLocalHom_comp f e.toRingHom

/-- Embedding of a finite residue field into the absolute residue field. -/
private noncomputable def finiteLevelAbsoluteResidueMap
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) →+*
      IsLocalRing.ResidueField P.1 := by
  letI : IsLocalHom (finiteLevelAbsoluteValuationMap P L) :=
    finiteLevelAbsoluteValuationMap_isLocal P L
  exact IsLocalRing.ResidueField.map (finiteLevelAbsoluteValuationMap P L)

private theorem finiteLevelAbsoluteResidueMap_residue
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K)
    (x : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)) :
    finiteLevelAbsoluteResidueMap P L (IsLocalRing.residue _ x) =
      IsLocalRing.residue P.1 (finiteLevelAbsoluteValuationMap P L x) := by
  letI : IsLocalHom (finiteLevelAbsoluteValuationMap P L) :=
    finiteLevelAbsoluteValuationMap_isLocal P L
  exact IsLocalRing.ResidueField.map_residue _ _

/-- The induced embedding of finite residue fields at nested Galois levels. -/
private noncomputable def finiteLevelResidueMap
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M) :
    NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) →+*
      NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 M) := by
  letI : IsLocalHom (finiteLevelValuationMap P hLM) :=
    finiteLevelValuationMap_isLocal P hLM
  exact IsLocalRing.ResidueField.map (finiteLevelValuationMap P hLM)

private theorem finiteLevelResidueMap_residue
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M)
    (x : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)) :
    finiteLevelResidueMap P hLM (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (finiteLevelValuationMap P hLM x) := by
  letI : IsLocalHom (finiteLevelValuationMap P hLM) :=
    finiteLevelValuationMap_isLocal P hLM
  exact IsLocalRing.ResidueField.map_residue _ _

/-- The residue-field automorphism induced by an absolute decomposition
group element at a finite Galois level. -/
private noncomputable def finiteLevelResidueAction
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) ≃+*
      NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) :=
  IsLocalRing.ResidueField.mapEquiv
    (stableValuationRingEquiv_matrix K L.field
      (NU.LocalTheory.absoluteRestriction L g)
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)
      (absoluteRestriction_stabilizes_place P g hg L))

/-- Finite-level residue actions commute with the residue embeddings between
nested Galois levels. -/
private theorem finiteLevelResidueAction_natural
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M) :
    ∀ z, finiteLevelResidueMap P hLM
        (finiteLevelResidueAction P g hg L z) =
      finiteLevelResidueAction P g hg M
        (finiteLevelResidueMap P hLM z) := by
  let eL := stableValuationRingEquiv_matrix K L.field
    (NU.LocalTheory.absoluteRestriction L g)
    (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)
    (absoluteRestriction_stabilizes_place P g hg L)
  let eM := stableValuationRingEquiv_matrix K M.field
    (NU.LocalTheory.absoluteRestriction M g)
    (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 M)
    (absoluteRestriction_stabilizes_place P g hg M)
  let f := finiteLevelValuationMap P hLM
  letI : IsLocalHom f := finiteLevelValuationMap_isLocal P hLM
  apply residueMap_mapEquiv_commute f eL eM
  intro x
  apply Subtype.ext
  change (IntermediateField.inclusion hLM)
      (NU.LocalTheory.absoluteRestriction L g (x : L.field)) =
    NU.LocalTheory.absoluteRestriction M g
      ((IntermediateField.inclusion hLM) (x : L.field))
  apply Subtype.ext
  exact (NU.LocalTheory.absoluteRestriction_apply L g (x : L.field)).trans
    (NU.LocalTheory.absoluteRestriction_apply M g
      ((IntermediateField.inclusion hLM) (x : L.field))).symm

/-- At the identity Galois level the induced residue action is the
identity. -/
private theorem finiteLevelResidueAction_trivialGaloisLevel
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1) :
    finiteLevelResidueAction P g hg
        (NU.LocalTheory.trivialGaloisLevel K) =
      RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [finiteLevelResidueAction,
    IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  apply congrArg (IsLocalRing.residue _)
  apply Subtype.ext
  change NU.LocalTheory.absoluteRestriction
      (NU.LocalTheory.trivialGaloisLevel K) g (x : _) = (x : _)
  rw [absoluteRestriction_trivialGaloisLevel]
  rfl

/-- Every finite level cut out by an absolute place has the same residue
characteristic as the absolute residue field. -/
private theorem absolutePlaceAtLevel_residueCharP
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K)
    (p : ℕ) [CharP (IsLocalRing.ResidueField P.1) p] :
    CharP (NU.LocalTheory.ResidueFieldAt
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)) p := by
  let w := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let A := P.1.comap L.field.val.toRingHom
  have hA : NU.LocalTheory.primeValuationSubring w = A :=
    NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
  let f := valuationComapInclusion L.field.val.toRingHom P.1
  letI : IsLocalHom f := valuationComapInclusion_isLocal _ _
  let rm := IsLocalRing.ResidueField.map f
  have hcharA : CharP (IsLocalRing.ResidueField A) p :=
    (rm.charP_iff_charP p).mpr inferInstance
  let eA : NU.LocalTheory.primeValuationSubring w ≃+* A :=
    { toFun := fun x => ⟨x, by rw [← hA]; exact x.property⟩
      invFun := fun x => ⟨x, by rw [hA]; exact x.property⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  let er := IsLocalRing.ResidueField.mapEquiv eA
  exact (er.toRingHom.charP_iff_charP p).mpr hcharA

/-- A root of unity has valuation zero, hence belongs to every valuation
subring of the ambient field. -/
private theorem rootOfUnity_mem_valuationSubring
    {F : Type*} [Field F] (A : ValuationSubring F)
    (n : ℕ) (hn : n ≠ 0) (x : F) (hx : x ^ n = 1) : x ∈ A := by
  rw [← A.valuationSubring_valuation,
    Valuation.mem_valuationSubring_iff]
  have hvpow : A.valuation x ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  have hv : A.valuation x = 1 := by
    apply pow_left_injective hn
    simpa using hvpow
  rw [hv]

/-- In residue characteristic `p`, a root of prime order `ell ≠ p` cannot
reduce to one unless it was already one. -/
private theorem rootOfPrimeOrder_eq_one_of_residue_eq_one
    {F : Type*} [Field F] (A : ValuationSubring F)
    (p ell : ℕ) [CharP (IsLocalRing.ResidueField A) p]
    (hp : p.Prime) (hell : ell.Prime) (hne : p ≠ ell)
    (zeta : F) (hpow : zeta ^ ell = 1)
    (hres : IsLocalRing.residue A
      (⟨zeta, rootOfUnity_mem_valuationSubring
        A ell hell.ne_zero zeta hpow⟩ : A) = 1) :
    zeta = 1 := by
  by_contra hzeta
  let zetaA : A :=
    ⟨zeta, rootOfUnity_mem_valuationSubring
      A ell hell.ne_zero zeta hpow⟩
  have hzetaA : zetaA ≠ 1 := by
    intro h
    exact hzeta (congrArg Subtype.val h)
  have hpowA : zetaA ^ ell = 1 := by
    apply Subtype.ext
    exact hpow
  have hresA : IsLocalRing.residue A zetaA = 1 := hres
  have hsumA : ∑ i ∈ Finset.range ell, zetaA ^ i = 0 := by
    have hgeom := mul_geom_sum zetaA ell
    rw [hpowA, sub_self] at hgeom
    rcases mul_eq_zero.mp hgeom with hdiff | hsum
    · exact (hzetaA (sub_eq_zero.mp hdiff)).elim
    · exact hsum
  have hcast : (ell : IsLocalRing.ResidueField A) = 0 := by
    have hm := congrArg (IsLocalRing.residue A) hsumA
    simpa [map_sum, hresA] using hm
  have hdvd : p ∣ ell := (CharP.cast_eq_zero_iff
    (IsLocalRing.ResidueField A) p ell).mp hcast
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hell).mp hdvd)

/-- The absolute residue field has the same characteristic as the finite
place obtained by restricting the absolute valuation. -/
private theorem ambientResidueField_charP
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    CharP (IsLocalRing.ResidueField P.1)
      (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)) := by
  let v := ambientFinitePlace P
  let A := P.1.comap (algebraMap K Omega)
  let p := NU.LocalTheory.residueCharacteristic v
  have hA : NU.LocalTheory.primeValuationSubring v = A :=
    primeValuationSubring_ambientFinitePlace P
  letI hcharA : CharP (IsLocalRing.ResidueField A) p := by
    rw [← hA]
    exact ringChar.charP _
  let f := valuationComapInclusion (algebraMap K Omega) P.1
  letI : IsLocalHom f := valuationComapInclusion_isLocal _ _
  let rm := IsLocalRing.ResidueField.map f
  exact (rm.charP_iff_charP p).mp hcharA

/-- If every away-prime cyclotomic scalar is `p^A`, then the
induced action on every finite residue level is the corresponding absolute
Frobenius power. -/
private theorem finiteLevelResidueAction_eq_primePower_of_cyclotomic
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (Aexp : ℕ)
    (hchi : ∀ ell : NU.LocalTheory.OddPrime,
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
          (ell : ℕ) →
        absoluteCyclotomicScalar K ell g =
          (NU.LocalTheory.residueCharacteristic
            (ambientFinitePlace P) ^ Aexp : ZMod (ell : ℕ)))
    (horder : OrderDivisibilityPrinciple)
    (L : NU.LocalTheory.GaloisLevel K) :
    ∀ x : NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L),
      finiteLevelResidueAction P g hg L x =
        x ^ (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ^ Aexp) := by
  let L0 := NU.LocalTheory.trivialGaloisLevel K
  let w0 := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L0
  let wL := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let k0 := NU.LocalTheory.ResidueFieldAt w0
  let kL := NU.LocalTheory.ResidueFieldAt wL
  letI : Finite k0 := residueFieldAt_finite_matrix w0
  letI : Finite kL := residueFieldAt_finite_matrix wL
  letI : Fintype k0 := Fintype.ofFinite k0
  letI : Fintype kL := Fintype.ofFinite kL
  have h0L : L0.LE L := by
    exact bot_le
  let iL : k0 →+* kL := finiteLevelResidueMap P h0L
  letI : Algebra k0 kL := iL.toAlgebra
  letI : Module k0 kL := @Algebra.toModule k0 kL _ _ iL.toAlgebra
  let tauL : kL ≃+* kL := finiteLevelResidueAction P g hg L
  let tauLAlg : kL ≃ₐ[k0] kL := AlgEquiv.ofRingEquiv (f := tauL) (by
    intro z
    change tauL (iL z) = iL z
    have hn := finiteLevelResidueAction_natural P g hg h0L z
    rw [finiteLevelResidueAction_trivialGaloisLevel] at hn
    exact hn.symm)
  obtain ⟨d, a, hd, _hdpos, _halt, ha, hmod⟩ :=
    finiteField_algEquiv_eq_pow_matrix tauLAlg
  have ha' : ∀ x : kL, tauL x = x ^ (Nat.card k0 ^ a) := by
    simpa [tauLAlg] using ha
  have hkLcard : Nat.card kL = Nat.card k0 ^ d := by
    rw [hd, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  letI : CharP (IsLocalRing.ResidueField P.1) p :=
    ambientResidueField_charP P
  letI : CharP k0 p := absolutePlaceAtLevel_residueCharP P L0 p
  obtain ⟨f, hp, hk0⟩ := FiniteField.card k0 p
  let fdeg : ℕ := f
  have hk0card : Nat.card k0 = p ^ fdeg := by
    simpa only [Nat.card_eq_fintype_card] using hk0
  have hprimeMod : ∀ lambda m : ℕ, lambda.Prime →
      lambda ^ m ∣ fdeg * d →
      Nat.ModEq (lambda ^ m) (fdeg * a) Aexp := by
    intro lambda m hlambda hlambdaDiv
    let lambdaP : Nat.Primes := ⟨lambda, hlambda⟩
    obtain ⟨ell, hellavoid, hellorder⟩ :=
      (horder p hp.one_lt lambdaP m).nonempty
    have hellTwo : (ell : ℕ) ≠ 2 := by
      intro heq
      apply hellavoid
      rw [heq]
      exact Nat.dvd_mul_right 2 p
    let ellOdd : NU.LocalTheory.OddPrime :=
      ⟨ell, ell.2.odd_of_ne_two hellTwo⟩
    have hellp : ¬(ell : ℕ) ∣ p := by
      intro hdiv
      exact hellavoid (dvd_mul_of_dvd_right hdiv 2)
    have haway : p ≠ (ell : ℕ) := by
      intro heq
      apply hellp
      rw [heq]
    let zeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure K) (ellOdd : ℕ)).choose
    let hzeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure K) (ellOdd : ℕ)).choose_spec
    let M := galoisLevelJoinElement L zeta
    have hLM : L.LE M := le_galoisLevelJoinElement L zeta
    have h0M : L0.LE M := le_trans h0L hLM
    let wM := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 M
    let kM := NU.LocalTheory.ResidueFieldAt wM
    letI : Finite kM := residueFieldAt_finite_matrix wM
    let iM : k0 →+* kM := finiteLevelResidueMap P h0M
    letI : Algebra k0 kM := iM.toAlgebra
    let tauM : kM ≃+* kM := finiteLevelResidueAction P g hg M
    let tauMAlg : kM ≃ₐ[k0] kM := AlgEquiv.ofRingEquiv (f := tauM) (by
      intro z
      change tauM (iM z) = iM z
      have hn := finiteLevelResidueAction_natural P g hg h0M z
      rw [finiteLevelResidueAction_trivialGaloisLevel] at hn
      exact hn.symm)
    obtain ⟨_, b, _, _, _, hb, _⟩ :=
      finiteField_algEquiv_eq_pow_matrix tauMAlg
    have hb' : ∀ x : kM, tauM x = x ^ (Nat.card k0 ^ b) := by
      simpa [tauMAlg] using hb
    let iLM : kL →+* kM := finiteLevelResidueMap P hLM
    have hpowersL : ∀ x : kL,
        x ^ (Nat.card k0 ^ a) = x ^ (Nat.card k0 ^ b) := by
      intro x
      apply iLM.injective
      calc
        iLM (x ^ (Nat.card k0 ^ a)) = iLM (tauL x) := by rw [ha' x]
        _ = tauM (iLM x) :=
          finiteLevelResidueAction_natural P g hg hLM x
        _ = (iLM x) ^ (Nat.card k0 ^ b) := hb' (iLM x)
        _ = iLM (x ^ (Nat.card k0 ^ b)) := by rw [map_pow]
    have habmod : Nat.ModEq d a b := hmod b hpowersL
    let zetaM : M.field := ⟨zeta, mem_galoisLevelJoinElement L zeta⟩
    have hzetaM : IsPrimitiveRoot zetaM (ell : ℕ) := by
      have hmapped : IsPrimitiveRoot
          (M.field.val.toMonoidHom zetaM) (ell : ℕ) := by
        simpa [zetaM] using hzeta
      exact hmapped.of_map_of_injective M.field.val.injective
    have hpowM : zetaM ^ (ell : ℕ) = 1 := hzetaM.pow_eq_one
    let AM := NU.LocalTheory.primeValuationSubring wM
    let zetaA : AM := ⟨zetaM,
      rootOfUnity_mem_valuationSubring AM (ell : ℕ) ell.2.ne_zero
        zetaM hpowM⟩
    let r : kM := IsLocalRing.residue AM zetaA
    letI : CharP kM p := absolutePlaceAtLevel_residueCharP P M p
    have hrpow : r ^ (ell : ℕ) = 1 := by
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue AM)
      apply Subtype.ext
      exact hpowM
    have hrne : r ≠ 1 := by
      intro hr
      have hzetaOne := rootOfPrimeOrder_eq_one_of_residue_eq_one
        AM p (ell : ℕ) hp ell.2 haway zetaM hpowM hr
      exact hzetaM.ne_one ell.2.one_lt hzetaOne
    have hrPrimitive : IsPrimitiveRoot r (ell : ℕ) := by
      refine ⟨hrpow, ?_⟩
      intro n hn
      have hord : orderOf r ∣ (ell : ℕ) :=
        orderOf_dvd_of_pow_eq_one hrpow
      rcases (Nat.dvd_prime ell.2).mp hord with hord | hord
      · exact (hrne (orderOf_eq_one_iff.mp hord)).elim
      · rw [← hord]
        exact orderOf_dvd_of_pow_eq_one hn
    have hspec : zeta ^ (absoluteCyclotomicScalar K ellOdd g).val =
        NU.LocalTheory.absoluteGaloisAlgEquiv g zeta := by
      change zeta ^
        (hzeta.autToPow K
          (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g) :
            ZMod (ell : ℕ)).val = _
      exact hzeta.autToPow_spec K
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g)
    have hscalarMod : (absoluteCyclotomicScalar K ellOdd g).val ≡
        p ^ Aexp [MOD (ell : ℕ)] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).1
      exact (ZMod.natCast_zmod_val _).trans (by
        simpa only [p, Nat.cast_pow] using hchi ellOdd haway)
    have hactAC : NU.LocalTheory.absoluteGaloisAlgEquiv g zeta =
        zeta ^ (p ^ Aexp) := by
      rw [← hspec]
      apply ((hzeta.isOfFinOrder ell.2.ne_zero).pow_eq_pow_iff_modEq).2
      simpa only [show (ell : ℕ) = orderOf zeta from hzeta.eq_orderOf]
        using hscalarMod
    have hfixM : NU.LocalTheory.absoluteRestriction M g zetaM =
        zetaM ^ (p ^ Aexp) := by
      apply Subtype.ext
      rw [NU.LocalTheory.absoluteRestriction_apply]
      exact hactAC
    have htauPower : tauM r = r ^ (p ^ Aexp) := by
      dsimp [tauM, r]
      rw [finiteLevelResidueAction,
        IsLocalRing.ResidueField.mapEquiv_apply,
        IsLocalRing.ResidueField.map_residue]
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue AM)
      apply Subtype.ext
      change NU.LocalTheory.absoluteRestriction M g zetaM =
        zetaM ^ (p ^ Aexp)
      exact hfixM
    have hpowerEq : r ^ (Nat.card k0 ^ b) = r ^ (p ^ Aexp) :=
      (hb' r).symm.trans htauPower
    have hmodEll : Nat.ModEq (ell : ℕ) (Nat.card k0 ^ b)
        (p ^ Aexp) := by
      have hm := ((hrPrimitive.isOfFinOrder ell.2.ne_zero).pow_eq_pow_iff_modEq).1
        hpowerEq
      simpa only [show (ell : ℕ) = orderOf r from hrPrimitive.eq_orderOf]
        using hm
    have hmodPowers : Nat.ModEq (ell : ℕ) (p ^ (fdeg * b))
        (p ^ Aexp) := by
      rw [hk0card] at hmodEll
      simpa only [pow_mul] using hmodEll
    have hpPowEq : (p : ZMod (ell : ℕ)) ^ (fdeg * b) =
        (p : ZMod (ell : ℕ)) ^ Aexp := by
      rw [← Nat.cast_pow, ← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodPowers
    have hpell : p.Coprime (ell : ℕ) :=
      (Nat.coprime_primes hp ell.2).2 haway
    let pu : (ZMod (ell : ℕ))ˣ := ZMod.unitOfCoprime p hpell
    have hpuPow : pu ^ (fdeg * b) = pu ^ Aexp := by
      apply Units.ext
      simpa [pu, ZMod.coe_unitOfCoprime] using hpPowEq
    have hexponent : Nat.ModEq (residueMultiplicativeOrder p ell)
        (fdeg * b) Aexp := by
      have hm := ((isOfFinOrder_of_finite pu).pow_eq_pow_iff_modEq).1
        hpuPow
      simpa [residueMultiplicativeOrder, pu, ZMod.coe_unitOfCoprime,
        ← orderOf_units] using hm
    have hlambdaExp : Nat.ModEq (lambda ^ m) (fdeg * b) Aexp :=
      Nat.ModEq.of_dvd hellorder hexponent
    have hlambdaAB : Nat.ModEq (lambda ^ m)
        (fdeg * a) (fdeg * b) :=
      Nat.ModEq.of_dvd hlambdaDiv (habmod.mul_left' fdeg)
    exact hlambdaAB.trans hlambdaExp
  have hfaA : Nat.ModEq (fdeg * d) (fdeg * a) Aexp := by
    by_cases hle : fdeg * a ≤ Aexp
    · apply (Nat.modEq_iff_dvd' hle).2
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro lambda m hlambda hlambdaDiv
      exact (Nat.modEq_iff_dvd' hle).1
        (hprimeMod lambda m hlambda hlambdaDiv)
    · have hle' : Aexp ≤ fdeg * a := le_of_not_ge hle
      apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' hle').2
      rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro lambda m hlambda hlambdaDiv
      exact (Nat.modEq_iff_dvd' hle').1
        (hprimeMod lambda m hlambda hlambdaDiv).symm
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP kL p := absolutePlaceAtLevel_residueCharP P L p
  letI : Algebra (ZMod p) kL := ZMod.algebra kL p
  have hfinrank : Module.finrank (ZMod p) kL = fdeg * d := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ Module.finrank (ZMod p) kL =
          Fintype.card (ZMod p) ^ Module.finrank (ZMod p) kL := by
        rw [ZMod.card]
      _ = Fintype.card kL := Module.card_eq_pow_finrank.symm
      _ = Nat.card kL := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card k0 ^ d := hkLcard
      _ = (p ^ fdeg) ^ d := by rw [hk0card]
      _ = p ^ (fdeg * d) := by rw [pow_mul]
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) kL
  have hfrob : frob ^ (fdeg * a) = frob ^ Aexp := by
    apply (pow_eq_pow_iff_modEq).2
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hfinrank]
    exact hfaA
  intro x
  calc
    finiteLevelResidueAction P g hg L x = x ^ (Nat.card k0 ^ a) :=
      ha' x
    _ = x ^ (p ^ (fdeg * a)) := by rw [hk0card, pow_mul]
    _ = x ^ (p ^ Aexp) := by
      have hx := DFunLike.congr_fun hfrob x
      rw [AlgEquiv.coe_pow, AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
        ZMod.card] at hx
      exact hx

/-- The scalar-one case of the finite-level Frobenius calculation. -/
private theorem finiteLevelResidueAction_eq_one_of_cyclotomic
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (hchi : ∀ ell : NU.LocalTheory.OddPrime,
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
          (ell : ℕ) →
        absoluteCyclotomicScalar K ell g = 1)
    (horder : OrderDivisibilityPrinciple)
    (L : NU.LocalTheory.GaloisLevel K) :
    finiteLevelResidueAction P g hg L = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  simpa using finiteLevelResidueAction_eq_primePower_of_cyclotomic
    P g hg 0 (fun ell haway => by simpa using hchi ell haway)
      horder L x

/-- Compatible finite-level Frobenius powers determine the action on the
absolute residue field. -/
private theorem actsAsPowerOnResidue_primePower_of_finiteLevelActions
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (Aexp : ℕ)
    (hlevels : ∀ (L : NU.LocalTheory.GaloisLevel K)
      (x : NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)),
      finiteLevelResidueAction P g hg L x =
        x ^ (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ^ Aexp)) :
    @ActsAsPowerOnResidue (AlgebraicClosure K)
      (Field.absoluteGaloisGroup K) _ _ (by
        change MulSemiringAction
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (AlgebraicClosure K)
        exact AlgEquiv.applyMulSemiringAction) P.1 g
          (NU.LocalTheory.residueCharacteristic
            (ambientFinitePlace P) ^ Aexp) := by
  intro x y hy
  let L := galoisLevelOfElement (x : AlgebraicClosure K)
  let w := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let xLval : L.field :=
    ⟨x, mem_galoisLevelOfElement (x : AlgebraicClosure K)⟩
  have hring : NU.LocalTheory.primeValuationSubring w =
      P.1.comap L.field.val.toRingHom :=
    NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _
  have hxLmem : xLval ∈ NU.LocalTheory.primeValuationSubring w := by
    rw [hring, ValuationSubring.mem_comap]
    exact x.property
  let xL : NU.LocalTheory.primeValuationSubring w := ⟨xLval, hxLmem⟩
  let eL := stableValuationRingEquiv_matrix K L.field
    (NU.LocalTheory.absoluteRestriction L g) w
    (absoluteRestriction_stabilizes_place P g hg L)
  let gxL : NU.LocalTheory.primeValuationSubring w := eL xL
  have hfinite : IsLocalRing.residue _ gxL =
      IsLocalRing.residue _ xL ^
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ^ Aexp) := by
    have hact := hlevels L (IsLocalRing.residue _ xL)
    rw [finiteLevelResidueAction,
      IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue] at hact
    exact hact
  have habs := congrArg (finiteLevelAbsoluteResidueMap P L) hfinite
  rw [finiteLevelAbsoluteResidueMap_residue, map_pow,
    finiteLevelAbsoluteResidueMap_residue] at habs
  have hxmap : finiteLevelAbsoluteValuationMap P L xL = x := by
    apply Subtype.ext
    rfl
  have hygmap : finiteLevelAbsoluteValuationMap P L gxL = y := by
    apply Subtype.ext
    exact (NU.LocalTheory.absoluteRestriction_apply L g xLval).trans hy.symm
  rwa [hxmap, hygmap] at habs

/-- The scalar-one case of the finite-level-to-absolute residue passage. -/
private theorem actsAsPowerOnResidue_one_of_finiteLevelActions
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (g : Field.absoluteGaloisGroup K)
    (hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (hlevels : ∀ L : NU.LocalTheory.GaloisLevel K,
      finiteLevelResidueAction P g hg L = RingEquiv.refl _) :
    @ActsAsPowerOnResidue (AlgebraicClosure K)
      (Field.absoluteGaloisGroup K) _ _ (by
        change MulSemiringAction
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (AlgebraicClosure K)
        exact AlgEquiv.applyMulSemiringAction) P.1 g 1 := by
  simpa using actsAsPowerOnResidue_primePower_of_finiteLevelActions
    P g hg 0 (fun L x => by rw [hlevels L]; simp)

section AmbientCorrespondence

variable {K₁ K₂ Omega G₁ G₂ : Type*}
  [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
  [Field Omega] [Algebra K₁ Omega] [Algebra K₂ Omega]
  [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [MulSemiringAction G₁ Omega] [MulSemiringAction G₂ Omega]

/-- Corresponding ambient places lie over the same rational prime.  This is a
formal consequence of the proved packet-profile recovery of residue
characteristic and rational-prime uniqueness. -/
theorem ambientRationalPrime_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientRationalPrime P₁ = ambientRationalPrime P₂ := by
  apply rationalFinitePlace_eq_of_residueCharacteristic_eq
  change NU.LocalTheory.residueCharacteristic
      (NU.LocalTheory.restrictFinitePlace ℚ (ambientFinitePlace P₁)) =
    NU.LocalTheory.residueCharacteristic
      (NU.LocalTheory.restrictFinitePlace ℚ (ambientFinitePlace P₂))
  rw [residueCharacteristic_restrictFinitePlace,
    residueCharacteristic_restrictFinitePlace]
  exact ambientResidueCharacteristic_preserved
    R₁ R₂ theta P₁ P₂ hmap

/-- The residue norm is the norm of the rational prime raised to the absolute
residue degree. -/
theorem ambientResidueNorm_eq_pow
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    ambientResidueNorm P =
      NU.Chebotarev.PrimeIdeal.norm (ambientRationalPrime P) ^
        ambientResidueDegree P := by
  let v := ambientFinitePlace P
  let q := ambientRationalPrime P
  letI : v.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  rw [ambientResidueNorm, ambientResidueDegree]
  change NU.Chebotarev.PrimeIdeal.norm v =
    NU.Chebotarev.PrimeIdeal.norm q ^
      q.asIdeal.inertiaDeg' v.asIdeal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact NU.Chebotarev.PrimeIdeal.norm_pow_inertiaDeg v q inferInstance

/-! ### Ambient assembly: `cor:chi`, `prop:inertia`, `prop:q`, and `lem:bridge` -/

/-- The absolute cyclotomic scalar written in a supplied ambient realization. -/
private noncomputable def ambientCyclotomicScalar
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (ell : NU.LocalTheory.OddPrime) (g : G) : ZMod (ell : ℕ) :=
  absoluteCyclotomicScalar K ell (R.galoisEquiv.symm g)

/-- Common-ambient form of Blueprint `cor:chi`, obtained from
`pointwiseCyclotomic_preserved` after the realization/decomposition-group
bookkeeping. -/
private theorem ambientPointwiseCyclotomic_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (ell : NU.LocalTheory.OddPrime)
    (haway : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace P₁) ≠ (ell : ℕ)) :
    ambientCyclotomicScalar R₂ ell (theta g) =
      ambientCyclotomicScalar R₁ ell g := by
  let A₁ := abstractPlace R₁ P₁
  let A₂ := abstractPlace R₂ P₂
  let alpha := abstractGaloisIso R₁ R₂ theta
  let ga : Field.absoluteGaloisGroup K₁ := R₁.galoisEquiv.symm g
  have hsource : Subgroup.map R₁.galoisEquiv.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) =
        NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 := by
    simpa [A₁, abstractPlace] using
      NU.LocalTheory.map_absoluteDecompositionGroup_ambient
        R₁.closureEquiv R₁.galoisEquiv.toMulEquiv R₁.action_compat A₁
  have hga : ga ∈ NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1 := by
    have hm : R₁.galoisEquiv ga ∈
        Subgroup.map R₁.galoisEquiv.toMulEquiv.toMonoidHom
          (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) := by
      rw [hsource]
      simpa [ga] using hg
    obtain ⟨x, hx, heq⟩ := hm
    have hxga : x = ga := R₁.galoisEquiv.injective heq
    simpa [hxga] using hx
  have hawayA : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace A₁) ≠ (ell : ℕ) := by
    rwa [ambientFinitePlace_abstractPlace R₁ P₁]
  have hc := pointwiseCyclotomic_preserved alpha A₁ A₂
    (map_abstractDecompositionGroup R₁ R₂ theta P₁ P₂ hmap)
    ga hga ell hawayA
  simpa [ambientCyclotomicScalar, alpha, ga, abstractGaloisIso] using hc

/-- An absolute decomposition group admits an ambient open normal level
whose intersection has index at least four.  The biquadratic quotient from
`LocalTheory` supplies the lower bound; profiniteness lets its open kernel be
refined by a normal level of the full absolute Galois group. -/
private theorem openNormal_inter_decomposition_index_ge_four
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    ∃ N : NU.LocalTheory.OpenNormalSubgroup
        (Field.absoluteGaloisGroup K),
      let D := NU.LocalTheory.absoluteDecompositionGroup K P.1
      let U := Subgroup.comap D.subtype N.toSubgroup
      4 ≤ U.index := by
  let D := NU.LocalTheory.absoluteDecompositionGroup K P.1
  obtain ⟨f, hf⟩ :=
    NU.LocalTheory.absoluteDecompositionGroup_has_biquadratic_quotient
      P.1 P.2
  have hopenKer : IsOpen (f.toMonoidHom.ker : Set D) := by
    change IsOpen
      (f ⁻¹' ({1} : Set (Multiplicative (ZMod 2 × ZMod 2))))
    exact (isOpen_discrete {1}).preimage f.continuous
  rw [isOpen_induced_iff] at hopenKer
  obtain ⟨O, hOopen, hO⟩ := hopenKer
  have honeO : (1 : Field.absoluteGaloisGroup K) ∈ O := by
    have h : (1 : D) ∈ Subtype.val ⁻¹' O := by
      rw [hO]
      exact f.toMonoidHom.ker.one_mem
    exact h
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  letI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) :=
    NU.LocalTheory.absoluteGaloisGroup_totallyDisconnectedSpace
  letI : CompactSpace D :=
    (NU.LocalTheory.absoluteDecompositionGroup_isClosed K P.1)
      |>.isClosedEmbedding_subtypeVal.compactSpace
  obtain ⟨N, hNO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hOopen honeO
  refine ⟨{
    toSubgroup := N.toSubgroup
    isOpen' := N.isOpen'
    normal' := N.isNormal' }, ?_⟩
  dsimp only
  let U := Subgroup.comap D.subtype N.toSubgroup
  have hUopen : IsOpen (U : Set D) :=
    N.isOpen'.preimage continuous_subtype_val
  letI : Finite (D ⧸ U) := U.quotient_finite_of_isOpen hUopen
  letI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUker : U ≤ f.toMonoidHom.ker := by
    intro g hg
    have hgO : (g : Field.absoluteGaloisGroup K) ∈ O := hNO hg
    have hgpre : g ∈ Subtype.val ⁻¹' O := hgO
    rw [hO] at hgpre
    exact hgpre
  have hindex : f.toMonoidHom.ker.index ≤ U.index :=
    Subgroup.index_antitone hUker
  have hker : f.toMonoidHom.ker.index = 4 := by
    rw [Subgroup.index_ker]
    have hrange : f.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr hf
    rw [hrange]
    norm_num [Nat.card_eq_fintype_card]
  rwa [hker] at hindex

/-- Swap the two presentations of an intersection of subgroups. -/
private noncomputable def subgroupIntersectionSwapEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    (D N : Subgroup G) :
    Subgroup.comap N.subtype D ≃ₜ* Subgroup.comap D.subtype N where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pull an absolute place back after rebasing it to the number field cut out
by an ambient open normal level. -/
private noncomputable def finiteLevelAbsolutePlace
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    NU.LocalTheory.AbsoluteFinitePlaceOf
      (NU.LocalTheory.galoisLevelOfOpenNormal K N).field :=
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
  let e := intermediateFieldClosureEquiv K L.field
  (NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension
    K L.field (AlgebraicClosure K) e).symm P

/-- The fixing subgroup of the field cut out by an open normal level is that
level itself. -/
private theorem fixingSubgroup_galoisLevelOfOpenNormal
    {K : Type*} [Field K] [NumberField K]
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    (NU.LocalTheory.galoisLevelOfOpenNormal K N).field.fixingSubgroup =
      N.toSubgroup := by
  rw [← NU.LocalTheory.levelKernel_galoisLevelOfOpenNormal K N]
  exact (IntermediateField.restrictNormalHom_ker
    (NU.LocalTheory.galoisLevelOfOpenNormal K N).field).symm

/-- The finite-level place transports back to the original ambient valuation
ring. -/
private theorem finiteLevelAbsolutePlace_ambient_val
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    (NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension K
      (NU.LocalTheory.galoisLevelOfOpenNormal K N).field
      (AlgebraicClosure K)
      (intermediateFieldClosureEquiv K
        (NU.LocalTheory.galoisLevelOfOpenNormal K N).field)
      (finiteLevelAbsolutePlace P N)).1 = P.1 := by
  change ((NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension K
      (NU.LocalTheory.galoisLevelOfOpenNormal K N).field
      (AlgebraicClosure K)
      (intermediateFieldClosureEquiv K
        (NU.LocalTheory.galoisLevelOfOpenNormal K N).field))
      ((NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension K
        (NU.LocalTheory.galoisLevelOfOpenNormal K N).field
        (AlgebraicClosure K)
        (intermediateFieldClosureEquiv K
          (NU.LocalTheory.galoisLevelOfOpenNormal K N).field)).symm P)).1 =
    P.1
  rw [Equiv.apply_symm_apply]

/-- The finite place underlying the rebased absolute place is the usual
center obtained by restricting the original absolute valuation to the
finite level. -/
private theorem ambientFinitePlace_finiteLevelAbsolutePlace
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    ambientFinitePlace (finiteLevelAbsolutePlace P N) =
      NU.LocalTheory.absolutePlaceAtLevel P.1 P.2
        (NU.LocalTheory.galoisLevelOfOpenNormal K N) := by
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
  let Q := finiteLevelAbsolutePlace P N
  let E := intermediateFieldClosureEquiv K L.field
  let A := P.1.comap L.field.val.toRingHom
  have hA : NU.LocalTheory.IsNontrivialValuation A :=
    NU.LocalTheory.absolutePlace_comap_nontrivial P.1 P.2 L
  have htransport :
      NU.LocalTheory.transportValuationSubring E.toRingEquiv Q.1 =
        P.1 := by
    simpa only [Q, E,
      NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension_val]
      using finiteLevelAbsolutePlace_ambient_val P N
  have hQ : NU.LocalTheory.primeValuationSubring
      (ambientFinitePlace Q) = A := by
    rw [primeValuationSubring_ambientFinitePlace]
    apply ValuationSubring.ext
    intro x
    change algebraMap L.field (AlgebraicClosure L.field) x ∈ Q.1 ↔
      L.field.val x ∈ P.1
    have hm := ValuationSubring.ext_iff.mp htransport (L.field.val x)
    have hpull : E.symm (L.field.val x) =
        algebraMap L.field (AlgebraicClosure L.field) x := by
      apply E.injective
      simp
    change E.symm (L.field.val x) ∈ Q.1 ↔ L.field.val x ∈ P.1 at hm
    rw [hpull] at hm
    exact hm
  apply (NU.LocalTheory.numberField_valuations A hA).unique
  · exact hQ.symm
  · exact (NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _).symm

/-- Restriction of the finite-level center is the original center. -/
private theorem restrictFinitePlace_finiteLevelAbsolutePlace
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    NU.LocalTheory.restrictFinitePlace K
        (ambientFinitePlace (finiteLevelAbsolutePlace P N)) =
      ambientFinitePlace P := by
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
  let w := ambientFinitePlace (finiteLevelAbsolutePlace P N)
  let A := P.1.comap (algebraMap K (AlgebraicClosure K))
  have hA : NU.LocalTheory.IsNontrivialValuation A :=
    ambientPlace_comap_nontrivial P
  have hw : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.restrictFinitePlace K w) = A := by
    rw [← primeValuationSubring_restrictFinitePlace K w]
    change (NU.LocalTheory.primeValuationSubring
      (ambientFinitePlace (finiteLevelAbsolutePlace P N))).comap
        (algebraMap K L.field) = A
    rw [ambientFinitePlace_finiteLevelAbsolutePlace P N]
    unfold NU.LocalTheory.absolutePlaceAtLevel
    rw [NU.LocalTheory.primeValuationSubring_centerFinitePlace]
    apply ValuationSubring.ext
    intro x
    rfl
  apply (NU.LocalTheory.numberField_valuations A hA).unique
  · exact hw.symm
  · exact (primeValuationSubring_ambientFinitePlace P).symm

/-- The absolute decomposition group over a finite level is exactly the
intersection of the original decomposition group with that level. -/
private noncomputable def finiteLevelDecompositionEquiv
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    NU.LocalTheory.absoluteDecompositionGroup
        (NU.LocalTheory.galoisLevelOfOpenNormal K N).field
        (finiteLevelAbsolutePlace P N).1 ≃ₜ*
      Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K P.1).subtype
        N.toSubgroup := by
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
  let Q := finiteLevelAbsolutePlace P N
  let E := intermediateFieldClosureEquiv K L.field
  let F := L.field.fixingSubgroup
  let e0 := intermediateFieldGaloisContinuousMulEquiv K L.field
  have hFN : F = N.toSubgroup :=
    fixingSubgroup_galoisLevelOfOpenNormal N
  let ec : F ≃ₜ* N.toSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hFN
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let eG : Field.absoluteGaloisGroup L.field ≃ₜ* N.toSubgroup :=
    e0.trans ec
  letI : MulSemiringAction (Field.absoluteGaloisGroup K)
      (AlgebraicClosure K) := by
    change MulSemiringAction
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (AlgebraicClosure K)
    exact AlgEquiv.applyMulSemiringAction
  letI : MulSemiringAction N.toSubgroup (AlgebraicClosure K) :=
    MulSemiringAction.compHom (AlgebraicClosure K) N.toSubgroup.subtype
  have hcompat : ∀ (g : Field.absoluteGaloisGroup L.field)
      (x : AlgebraicClosure L.field),
      E ((show AlgebraicClosure L.field ≃ₐ[L.field]
        AlgebraicClosure L.field from g) x) =
        eG g • E x := by
    intro g x
    change E
      ((show AlgebraicClosure L.field ≃ₐ[L.field]
        AlgebraicClosure L.field from g) x) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
        ((eG g : N.toSubgroup) : Field.absoluteGaloisGroup K)) (E x)
    have heG : ((eG g : N.toSubgroup) : Field.absoluteGaloisGroup K) =
        (intermediateFieldGaloisMulEquiv K L.field g).1 := by
      rfl
    rw [heG]
    change E
      ((show AlgebraicClosure L.field ≃ₐ[L.field]
        AlgebraicClosure L.field from g) x) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
        intermediateFieldRestrictionHom K L.field g) (E x)
    rw [intermediateFieldRestrictionHom_apply]
    simp [E]
  have hmap :=
    NU.LocalTheory.map_absoluteDecompositionGroup_ambientOfFiniteExtension
      K L.field (AlgebraicClosure K) N.toSubgroup E eG.toMulEquiv
      hcompat Q
  have hplace :
      (NU.LocalTheory.ambientAbsoluteFinitePlaceEquivOfFiniteExtension K
        L.field (AlgebraicClosure K) E Q).1 = P.1 :=
    finiteLevelAbsolutePlace_ambient_val P N
  rw [hplace] at hmap
  have hstab :
      NU.LocalTheory.ambientDecompositionGroup
          (G := N.toSubgroup) P.1 =
        Subgroup.comap N.toSubgroup.subtype
          (NU.LocalTheory.absoluteDecompositionGroup K P.1) := by
    ext g
    change ((g : Field.absoluteGaloisGroup K) • P.1 = P.1) ↔
      ((g : Field.absoluteGaloisGroup K) • P.1 = P.1)
    rfl
  rw [hstab] at hmap
  exact (PacketTransport.subgroupMapEquiv eG
    (NU.LocalTheory.absoluteDecompositionGroup L.field Q.1) _ hmap).trans
      (subgroupIntersectionSwapEquiv
        (NU.LocalTheory.absoluteDecompositionGroup K P.1) N.toSubgroup)

/-- The relative ramification-index/residue-degree product of a finite
level is the index of its intersection with the absolute decomposition
group. -/
private theorem finiteLevel_relativeDegree_eq_index
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
    let v := ambientFinitePlace P
    let w := ambientFinitePlace (finiteLevelAbsolutePlace P N)
    v.asIdeal.ramificationIdx' w.asIdeal *
        v.asIdeal.inertiaDeg' w.asIdeal =
      (Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K P.1).subtype
        N.toSubgroup).index := by
  let L := NU.LocalTheory.galoisLevelOfOpenNormal K N
  let v := ambientFinitePlace P
  let w := ambientFinitePlace (finiteLevelAbsolutePlace P N)
  let D := NU.LocalTheory.absoluteDecompositionGroup K P.1
  let U := Subgroup.comap D.subtype N.toSubgroup
  have hrestrict : NU.LocalTheory.restrictFinitePlace K w = v :=
    restrictFinitePlace_finiteLevelAbsolutePlace P N
  letI : w.asIdeal.LiesOver v.asIdeal := by
    constructor
    rw [← hrestrict, NU.LocalTheory.restrictFinitePlace_asIdeal]
  have hdecomp : NU.LocalTheory.decompositionGroup K w =
      MulAction.stabilizer (L.field ≃ₐ[K] L.field) w.asIdeal := by
    ext sigma
    change NU.LocalTheory.conjugateFinitePlace K sigma w = w ↔
      sigma • w.asIdeal = w.asIdeal
    constructor
    · intro h
      exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
    · intro h
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact h
  have hcard : Nat.card (NU.LocalTheory.decompositionGroup K w) =
      v.asIdeal.ramificationIdx' w.asIdeal *
        v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [hdecomp, Ideal.card_stabilizer_eq v.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx
        v.asIdeal w.asIdeal (L.field ≃ₐ[K] L.field),
      Ideal.inertiaDegIn_eq_inertiaDeg
        v.asIdeal w.asIdeal (L.field ≃ₐ[K] L.field),
      ← Ideal.ramificationIdx_eq_ramificationIdx'
        v.asIdeal w.asIdeal v.ne_bot,
      ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal]
  let r : D →* (L.field ≃ₐ[K] L.field) :=
    (NU.LocalTheory.absoluteRestriction L).comp D.subtype
  have hker : r.ker = U := by
    ext g
    change NU.LocalTheory.absoluteRestriction L g.1 = 1 ↔
      g.1 ∈ N.toSubgroup
    rw [← NU.LocalTheory.levelKernel_galoisLevelOfOpenNormal K N]
    rfl
  have hrange : r.range = NU.LocalTheory.finiteLevelImage L D := by
    ext sigma
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have himage : NU.LocalTheory.finiteLevelImage L D =
      NU.LocalTheory.decompositionGroup K w := by
    dsimp only [D]
    rw [NU.LocalTheory.absoluteDecompositionGroup_finiteImage
      P.1 P.2 L]
    exact congrArg (NU.LocalTheory.decompositionGroup K)
      (ambientFinitePlace_finiteLevelAbsolutePlace P N).symm
  calc
    v.asIdeal.ramificationIdx' w.asIdeal *
        v.asIdeal.inertiaDeg' w.asIdeal =
        Nat.card (NU.LocalTheory.decompositionGroup K w) := hcard.symm
    _ = Nat.card r.range := by rw [hrange, himage]
    _ = r.ker.index := (Subgroup.index_ker r).symm
    _ = U.index := by rw [hker]

/-- The absolute local degree at a finite level is the original local
degree multiplied by the decomposition-group index of that level. -/
private theorem finiteLevel_localDegree_eq_index_mul
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    let v := ambientFinitePlace P
    let w := ambientFinitePlace (finiteLevelAbsolutePlace P N)
    finitePlaceLocalDegree w =
      (Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K P.1).subtype
        N.toSubgroup).index * finitePlaceLocalDegree v := by
  let v := ambientFinitePlace P
  let w := ambientFinitePlace (finiteLevelAbsolutePlace P N)
  let q := NU.LocalTheory.restrictFinitePlace ℚ v
  have hrestrict : NU.LocalTheory.restrictFinitePlace K w = v :=
    restrictFinitePlace_finiteLevelAbsolutePlace P N
  have hq : NU.LocalTheory.restrictFinitePlace ℚ w = q := by
    apply rationalFinitePlace_eq_of_residueCharacteristic_eq
    rw [residueCharacteristic_restrictFinitePlace,
      residueCharacteristic_restrictFinitePlace]
    calc
      NU.LocalTheory.residueCharacteristic w =
          NU.LocalTheory.residueCharacteristic
            (NU.LocalTheory.restrictFinitePlace K w) :=
        (residueCharacteristic_restrictFinitePlace K w).symm
      _ = NU.LocalTheory.residueCharacteristic v := by rw [hrestrict]
  letI : w.asIdeal.LiesOver v.asIdeal := by
    constructor
    rw [← hrestrict, NU.LocalTheory.restrictFinitePlace_asIdeal]
  letI : v.asIdeal.LiesOver q.asIdeal := by
    constructor
    rfl
  have hrel : v.asIdeal.ramificationIdx' w.asIdeal *
      v.asIdeal.inertiaDeg' w.asIdeal =
        (Subgroup.comap
          (NU.LocalTheory.absoluteDecompositionGroup K P.1).subtype
          N.toSubgroup).index :=
    finiteLevel_relativeDegree_eq_index (K := K) P N
  have htower : finitePlaceLocalDegree w =
      finitePlaceLocalDegree v *
        (v.asIdeal.ramificationIdx' w.asIdeal *
          v.asIdeal.inertiaDeg' w.asIdeal) := by
    unfold finitePlaceLocalDegree
    dsimp only
    rw [hq,
      Ideal.ramificationIdx'_algebra_tower' q.asIdeal v.asIdeal w.asIdeal,
      Ideal.inertiaDeg'_algebra_tower q.asIdeal v.asIdeal w.asIdeal]
    ring
  change finitePlaceLocalDegree w =
    (Subgroup.comap
      (NU.LocalTheory.absoluteDecompositionGroup K P.1).subtype
      N.toSubgroup).index * finitePlaceLocalDegree v
  rw [htower, hrel]
  ring

/-- Passing to a finite ambient level does not change the residue
prime. -/
private theorem residuePrime_finiteLevelAbsolutePlace
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (N : NU.LocalTheory.OpenNormalSubgroup
      (Field.absoluteGaloisGroup K)) :
    residuePrime
        (ambientFinitePlace (finiteLevelAbsolutePlace P N)) =
      residuePrime (ambientFinitePlace P) := by
  apply Subtype.ext
  change NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace (finiteLevelAbsolutePlace P N)) =
    NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  calc
    _ = NU.LocalTheory.residueCharacteristic
        (NU.LocalTheory.restrictFinitePlace K
          (ambientFinitePlace (finiteLevelAbsolutePlace P N))) :=
      (residueCharacteristic_restrictFinitePlace K _).symm
    _ = _ := by rw [restrictFinitePlace_finiteLevelAbsolutePlace P N]

/-- A pair of finite ambient levels cutting out corresponding open
subgroups of the two absolute decomposition groups. -/
private structure CommonDecompositionOpenLevelData
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂) where
  sourceLevel : NU.LocalTheory.OpenNormalSubgroup
    (Field.absoluteGaloisGroup K₁)
  index : ℕ
  source_index :
    (Subgroup.comap
      (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1).subtype
      sourceLevel.toSubgroup).index = index
  target_index :
    (Subgroup.comap
      (NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1).subtype
      (sourceLevel.map alpha).toSubgroup).index = index
  index_ge_four : 4 ≤ index
  subgroupEquiv :
    Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1).subtype
        sourceLevel.toSubgroup ≃ₜ*
      Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1).subtype
        (sourceLevel.map alpha).toSubgroup

/-- Transport the index-four level through the full absolute-Galois
isomorphism.  Mapping the ambient normal level makes the two intersections
correspond literally, so their subgroup indices agree. -/
private theorem commonDecompositionOpenLevelData_exists
    {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂]
    (alpha : Field.absoluteGaloisGroup K₁ ≃ₜ*
      Field.absoluteGaloisGroup K₂)
    (P₁ : NU.LocalTheory.AbsoluteFinitePlaceOf K₁)
    (P₂ : NU.LocalTheory.AbsoluteFinitePlaceOf K₂)
    (hmap : Subgroup.map alpha.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1) :
    Nonempty (CommonDecompositionOpenLevelData alpha P₁ P₂) := by
  obtain ⟨N, hN⟩ := openNormal_inter_decomposition_index_ge_four P₁
  let D₁ := NU.LocalTheory.absoluteDecompositionGroup K₁ P₁.1
  let D₂ := NU.LocalTheory.absoluteDecompositionGroup K₂ P₂.1
  let U₁ := Subgroup.comap D₁.subtype N.toSubgroup
  let U₂ := Subgroup.comap D₂.subtype (N.map alpha).toSubgroup
  let eD := PacketTransport.subgroupMapEquiv alpha D₁ D₂ hmap
  have hmapU : Subgroup.map eD.toMulEquiv.toMonoidHom U₁ = U₂ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change alpha x.1 ∈ (N.map alpha).toSubgroup
      apply (NU.LocalTheory.OpenNormalSubgroup.mem_map alpha N x.1).2
      exact hx
    · intro hy
      change (y : Field.absoluteGaloisGroup K₂) ∈
        (N.map alpha).toSubgroup at hy
      let x : D₁ := eD.symm y
      refine ⟨x, ?_, ?_⟩
      · change alpha.symm (y : Field.absoluteGaloisGroup K₂) ∈
          N.toSubgroup
        apply (NU.LocalTheory.OpenNormalSubgroup.mem_map alpha N
          (alpha.symm y)).1
        simpa using hy
      · apply Subtype.ext
        exact congrArg Subtype.val (eD.apply_symm_apply y)
  let eU := PacketTransport.subgroupMapEquiv eD U₁ U₂ hmapU
  have hindex : U₂.index = U₁.index := by
    rw [← hmapU]
    exact Subgroup.index_map_equiv U₁ eD.toMulEquiv
  exact ⟨{
    sourceLevel := N
    index := U₁.index
    source_index := rfl
    target_index := hindex
    index_ge_four := hN
    subgroupEquiv := eU }⟩

/-- The geometric core of `prop:p-n`: a common open subgroup is cut out
at finite number-field levels on both sides, so T5 and the two local Kummer
rank formulas produce one shared character dimension. -/
private theorem ambientKummerOpenSubgroupDimensionData_exists
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    Nonempty
      (KummerOpenSubgroupDimensionData
        (ambientLocalDegree P₁) (ambientLocalDegree P₂)) := by
  let A₁ := abstractPlace R₁ P₁
  let A₂ := abstractPlace R₂ P₂
  let alpha := abstractGaloisIso R₁ R₂ theta
  have hmapA : Subgroup.map alpha.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1) =
      NU.LocalTheory.absoluteDecompositionGroup K₂ A₂.1 :=
    map_abstractDecompositionGroup R₁ R₂ theta P₁ P₂ hmap
  obtain ⟨C⟩ := commonDecompositionOpenLevelData_exists
    alpha A₁ A₂ hmapA
  let N₁ := C.sourceLevel
  let N₂ := C.sourceLevel.map alpha
  let L₁ := NU.LocalTheory.galoisLevelOfOpenNormal K₁ N₁
  let L₂ := NU.LocalTheory.galoisLevelOfOpenNormal K₂ N₂
  let Q₁ := finiteLevelAbsolutePlace A₁ N₁
  let Q₂ := finiteLevelAbsolutePlace A₂ N₂
  let w₁ := ambientFinitePlace Q₁
  let w₂ := ambientFinitePlace Q₂
  obtain ⟨B₁⟩ := decompositionCompletionBridge L₁.field Q₁
  obtain ⟨B₂⟩ := decompositionCompletionBridge L₂.field Q₂
  obtain ⟨units₁⟩ := localUnitDecomposition_from_deepUnits w₁
  obtain ⟨units₂⟩ := localUnitDecomposition_from_deepUnits w₂
  have hdim₁ := pKummerDimension_at_completion w₁ units₁
  have hdim₂ := pKummerDimension_at_completion w₂ units₂
  have hcorrection₁ := completionRootCorrection_le_one w₁
  have hcorrection₂ := completionRootCorrection_le_one w₂
  let eLevel₁ := finiteLevelDecompositionEquiv A₁ N₁
  let eLevel₂ := finiteLevelDecompositionEquiv A₂ N₂
  let eCompletion :
      Field.absoluteGaloisGroup (w₁.adicCompletion L₁.field) ≃ₜ*
        Field.absoluteGaloisGroup (w₂.adicCompletion L₂.field) :=
    ((((B₁.comparison.trans eLevel₁).trans C.subgroupEquiv).trans
      eLevel₂.symm).trans B₂.comparison.symm)
  have hpBase : residuePrime (ambientFinitePlace A₁) =
      residuePrime (ambientFinitePlace A₂) := by
    apply Subtype.ext
    exact residueCharacteristic_preserved alpha A₁ A₂ hmapA
  have hp : residuePrime w₁ = residuePrime w₂ := by
    calc
      residuePrime w₁ = residuePrime (ambientFinitePlace A₁) :=
        residuePrime_finiteLevelAbsolutePlace A₁ N₁
      _ = residuePrime (ambientFinitePlace A₂) := hpBase
      _ = residuePrime w₂ :=
        (residuePrime_finiteLevelAbsolutePlace A₂ N₂).symm
  have hrank : continuousCharacterRank
        (Field.absoluteGaloisGroup (w₁.adicCompletion L₁.field))
          (residuePrime w₁) =
      continuousCharacterRank
        (Field.absoluteGaloisGroup (w₂.adicCompletion L₂.field))
          (residuePrime w₂) := by
    calc
      _ = continuousCharacterRank
          (Field.absoluteGaloisGroup (w₁.adicCompletion L₁.field))
            (residuePrime w₂) := by rw [hp]
      _ = _ := continuousCharacterRank_equiv
        (residuePrime w₂) eCompletion
  have hlevelDegree₁ : finitePlaceLocalDegree w₁ =
      (Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1).subtype
        N₁.toSubgroup).index *
          finitePlaceLocalDegree (ambientFinitePlace A₁) :=
    finiteLevel_localDegree_eq_index_mul A₁ N₁
  have hlevelDegree₂ : finitePlaceLocalDegree w₂ =
      (Subgroup.comap
        (NU.LocalTheory.absoluteDecompositionGroup K₂ A₂.1).subtype
        N₂.toSubgroup).index *
          finitePlaceLocalDegree (ambientFinitePlace A₂) :=
    finiteLevel_localDegree_eq_index_mul A₂ N₂
  have hdegree₁ : finitePlaceLocalDegree w₁ =
      C.index * ambientLocalDegree P₁ := by
    calc
      _ = (Subgroup.comap
          (NU.LocalTheory.absoluteDecompositionGroup K₁ A₁.1).subtype
          N₁.toSubgroup).index *
            finitePlaceLocalDegree (ambientFinitePlace A₁) := hlevelDegree₁
      _ = C.index * finitePlaceLocalDegree (ambientFinitePlace A₁) := by
        rw [C.source_index]
      _ = C.index * finitePlaceLocalDegree (ambientFinitePlace P₁) := by
        rw [ambientFinitePlace_abstractPlace R₁ P₁]
      _ = C.index * ambientLocalDegree P₁ := by
        rw [finitePlaceLocalDegree_ambientFinitePlace]
  have hdegree₂ : finitePlaceLocalDegree w₂ =
      C.index * ambientLocalDegree P₂ := by
    calc
      _ = (Subgroup.comap
          (NU.LocalTheory.absoluteDecompositionGroup K₂ A₂.1).subtype
          N₂.toSubgroup).index *
            finitePlaceLocalDegree (ambientFinitePlace A₂) := hlevelDegree₂
      _ = C.index * finitePlaceLocalDegree (ambientFinitePlace A₂) := by
        rw [C.target_index]
      _ = C.index * finitePlaceLocalDegree (ambientFinitePlace P₂) := by
        rw [ambientFinitePlace_abstractPlace R₂ P₂]
      _ = C.index * ambientLocalDegree P₂ := by
        rw [finitePlaceLocalDegree_ambientFinitePlace]
  refine ⟨{
    index := C.index
    dimension := continuousCharacterRank
      (Field.absoluteGaloisGroup (w₁.adicCompletion L₁.field))
        (residuePrime w₁)
    sourceCorrection := completionRootCorrection w₁
    targetCorrection := completionRootCorrection w₂
    index_ge_three := le_trans (by omega : 3 ≤ 4) C.index_ge_four
    sourceCorrection_le_one := hcorrection₁
    targetCorrection_le_one := hcorrection₂
    source_dimension := ?_
    target_dimension := ?_ }⟩
  · calc
      _ = 1 + finitePlaceLocalDegree w₁ + completionRootCorrection w₁ :=
        hdim₁
      _ = 1 + C.index * ambientLocalDegree P₁ +
          completionRootCorrection w₁ := by rw [hdegree₁]
  · calc
      _ = continuousCharacterRank
          (Field.absoluteGaloisGroup (w₂.adicCompletion L₂.field))
            (residuePrime w₂) := hrank
      _ = 1 + finitePlaceLocalDegree w₂ + completionRootCorrection w₂ :=
        hdim₂
      _ = 1 + C.index * ambientLocalDegree P₂ +
          completionRootCorrection w₂ := by rw [hdegree₂]

/-- Resistant branch of `prop:p-n`: realize a common open subgroup of
index at least three on both local-completion sides and transport its
character dimension through the decomposition-group isomorphism. -/
private theorem ambientKummerOpenSubgroupTransport
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    Nonempty
      (KummerBracketComparison
        (ambientLocalDegree P₁) (ambientLocalDegree P₂)) := by
  obtain ⟨D⟩ := ambientKummerOpenSubgroupDimensionData_exists
    R₁ R₂ theta P₁ P₂ hmap
  exact ⟨D.toBracketComparison⟩

/-- **T5/dimension transport obligation.**  Using
`decompositionCompletionBridge`, `localUnitDecomposition_from_deepUnits`,
`pKummerDimension_at_completion`, and
`kummerDimension_away_from_completion`, transport one open subgroup of index
at least three across the decomposition-group isomorphism.  The result is
the exact input consumed by the formal bracket argument in Blueprint
`prop:p-n`. -/
private theorem ambientKummerBracketComparison
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    Nonempty
      (KummerBracketComparison
        (ambientLocalDegree P₁) (ambientLocalDegree P₂)) := by
  exact ambientKummerOpenSubgroupTransport
    R₁ R₂ theta P₁ P₂ hmap

/-- Blueprint `prop:p-n` in the common-ambient interface.  All arithmetic
content is in the dimension lemmas and comparison witness; this proof is the
formal bracket-uniqueness argument. -/
private theorem ambientLocalDegree_preserved_from_dimensions
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientLocalDegree P₁ = ambientLocalDegree P₂ := by
  obtain ⟨C⟩ := ambientKummerBracketComparison
    R₁ R₂ theta P₁ P₂ hmap
  have hchar := ambientResidueCharacteristic_preserved
    R₁ R₂ theta P₁ P₂ hmap
  have hp : residuePrime (ambientFinitePlace P₁) =
      residuePrime (ambientFinitePlace P₂) := by
    apply Subtype.ext
    exact hchar
  exact (intrinsic_p_n_from_dimensions hp C).2

/-- A residue power action determines the corresponding away-prime
cyclotomic scalar. -/
private theorem ambientCyclotomicScalar_eq_natCast_of_power
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (g : G) (N : ℕ)
    (hpower : ActsAsPowerOnResidue P.1 g N)
    (ell : NU.LocalTheory.OddPrime)
    (haway : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace P) ≠ (ell : ℕ)) :
    ambientCyclotomicScalar R ell g = (N : ZMod (ell : ℕ)) := by
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  letI : CharP (IsLocalRing.ResidueField P.1) p :=
    ambientResidueField_charP P
  have hrootPower : ∀ zeta : Omega, zeta ^ (ell : ℕ) = 1 →
      g • zeta = zeta ^ N := by
    intro zeta hpow
    have hzeta0 : zeta ≠ 0 := by
      intro hz
      rw [hz, zero_pow ell.1.2.ne_zero] at hpow
      exact zero_ne_one hpow
    have hgzpow : (g • zeta) ^ (ell : ℕ) = 1 := by
      change ((MulSemiringAction.toRingHom G Omega g) zeta) ^
        (ell : ℕ) = 1
      rw [← map_pow, hpow, map_one]
    have hzetaNpow : (zeta ^ N) ^ (ell : ℕ) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hpow, one_pow]
    let r : Omega := (g • zeta) * (zeta ^ N)⁻¹
    have hrpow : r ^ (ell : ℕ) = 1 := by
      dsimp [r]
      rw [mul_pow, inv_pow, hgzpow, hzetaNpow, inv_one, mul_one]
    let zetaA : P.1 := ⟨zeta,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero zeta hpow⟩
    let gzetaA : P.1 := ⟨g • zeta,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero _ hgzpow⟩
    let zetaNA : P.1 := ⟨zeta ^ N,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero _ hzetaNpow⟩
    let rA : P.1 := ⟨r,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero r hrpow⟩
    have hresgz : IsLocalRing.residue P.1 gzetaA =
        IsLocalRing.residue P.1 zetaNA := by
      have h := hpower zetaA gzetaA rfl
      have hzpow : zetaA ^ N = zetaNA := by
        apply Subtype.ext
        rfl
      change Ideal.Quotient.mk _ gzetaA =
        (Ideal.Quotient.mk _ zetaA) ^ N at h
      rw [← map_pow, hzpow] at h
      exact h
    have hrmul : rA * zetaNA = gzetaA := by
      apply Subtype.ext
      dsimp [rA, zetaNA, gzetaA, r]
      field_simp
    have hrres : IsLocalRing.residue P.1 rA = 1 := by
      have hm := congrArg (IsLocalRing.residue P.1) hrmul
      rw [map_mul, hresgz] at hm
      have hzpowRes : (IsLocalRing.residue P.1 zetaNA) ^
          (ell : ℕ) = 1 := by
        rw [← map_pow]
        apply congrArg (IsLocalRing.residue P.1)
        apply Subtype.ext
        exact hzetaNpow
      have hzres0 : IsLocalRing.residue P.1 zetaNA ≠ 0 := by
        intro hz
        rw [hz, zero_pow ell.1.2.ne_zero] at hzpowRes
        exact zero_ne_one hzpowRes
      exact mul_right_cancel₀ hzres0 (hm.trans (one_mul _).symm)
    have hrone : r = 1 :=
      rootOfPrimeOrder_eq_one_of_residue_eq_one P.1 p (ell : ℕ)
        (residueCharacteristic_prime (ambientFinitePlace P)) ell.1.2
        haway r hrpow hrres
    dsimp [r] at hrone
    apply mul_right_cancel₀ (inv_ne_zero (pow_ne_zero N hzeta0))
    simpa [hrone, hzeta0]
  let ga : Field.absoluteGaloisGroup K := R.galoisEquiv.symm g
  change absoluteCyclotomicScalar K ell ga = (N : ZMod (ell : ℕ))
  let zeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose
  let hzeta := (HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure K) (ell : ℕ)).choose_spec
  have hspec : zeta ^ (absoluteCyclotomicScalar K ell ga).val =
      NU.LocalTheory.absoluteGaloisAlgEquiv ga zeta := by
    change zeta ^
      (hzeta.autToPow K
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga) :
          ZMod (ell : ℕ)).val = _
    exact hzeta.autToPow_spec K
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
  have hact : NU.LocalTheory.absoluteGaloisAlgEquiv ga zeta =
      zeta ^ N := by
    apply R.closureEquiv.injective
    calc
      R.closureEquiv (NU.LocalTheory.absoluteGaloisAlgEquiv ga zeta) =
          R.galoisEquiv ga • R.closureEquiv zeta :=
        R.action_compat ga zeta
      _ = g • R.closureEquiv zeta := by
        rw [R.galoisEquiv.apply_symm_apply]
      _ = (R.closureEquiv zeta) ^ N := hrootPower _ (by
        rw [← map_pow, hzeta.pow_eq_one, map_one])
      _ = R.closureEquiv (zeta ^ N) := by rw [map_pow]
  have hpows : zeta ^ (absoluteCyclotomicScalar K ell ga).val =
      zeta ^ N := hspec.trans hact
  have hmod : (absoluteCyclotomicScalar K ell ga).val ≡
      N [MOD (ell : ℕ)] := by
    have hm := (pow_eq_pow_iff_modEq).mp
      (show hzeta.toRootsOfUnity ^
          (absoluteCyclotomicScalar K ell ga).val =
        hzeta.toRootsOfUnity ^ N by
        apply rootsOfUnity.coe_injective
        simpa only [rootsOfUnity.coe_pow,
          hzeta.val_toRootsOfUnity_coe] using hpows)
    rw [← Subgroup.orderOf_coe, ← orderOf_units,
      hzeta.val_toRootsOfUnity_coe, ← hzeta.eq_orderOf] at hm
    exact hm
  calc
    absoluteCyclotomicScalar K ell ga =
        ((absoluteCyclotomicScalar K ell ga).val :
          ZMod (ell : ℕ)) := (ZMod.natCast_zmod_val _).symm
    _ = (N : ZMod (ell : ℕ)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod

/-- An element acting trivially on the absolute residue field fixes every
prime-to-residue-characteristic root of unity. -/
private theorem ambientCyclotomicScalar_eq_one_of_inertia
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (g : G)
    (hI : ActsAsPowerOnResidue P.1 g 1)
    (ell : NU.LocalTheory.OddPrime)
    (haway : NU.LocalTheory.residueCharacteristic
      (ambientFinitePlace P) ≠ (ell : ℕ)) :
    ambientCyclotomicScalar R ell g = 1 := by
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  letI : CharP (IsLocalRing.ResidueField P.1) p :=
    ambientResidueField_charP P
  have hrootfix : ∀ zeta : Omega, zeta ^ (ell : ℕ) = 1 →
      g • zeta = zeta := by
    intro zeta hpow
    have hzeta0 : zeta ≠ 0 := by
      intro hz
      rw [hz, zero_pow (ell.1.2.ne_zero)] at hpow
      exact zero_ne_one hpow
    have hgzpow : (g • zeta) ^ (ell : ℕ) = 1 := by
      change ((MulSemiringAction.toRingHom G Omega g) zeta) ^
        (ell : ℕ) = 1
      rw [← map_pow, hpow, map_one]
    let r : Omega := (g • zeta) * zeta⁻¹
    have hrpow : r ^ (ell : ℕ) = 1 := by
      dsimp [r]
      rw [mul_pow, inv_pow, hgzpow, hpow, inv_one, mul_one]
    let zetaA : P.1 := ⟨zeta,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero zeta hpow⟩
    let gzetaA : P.1 := ⟨g • zeta,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero _ hgzpow⟩
    let rA : P.1 := ⟨r,
      rootOfUnity_mem_valuationSubring P.1 (ell : ℕ)
        ell.1.2.ne_zero r hrpow⟩
    have hresgz : IsLocalRing.residue P.1 gzetaA =
        IsLocalRing.residue P.1 zetaA := by
      have h := hI zetaA gzetaA rfl
      rw [pow_one] at h
      exact h
    have hrmul : rA * zetaA = gzetaA := by
      apply Subtype.ext
      dsimp [rA, zetaA, gzetaA, r]
      field_simp
    have hrres : IsLocalRing.residue P.1 rA = 1 := by
      have hm := congrArg (IsLocalRing.residue P.1) hrmul
      rw [map_mul, hresgz] at hm
      have hpowA : zetaA ^ (ell : ℕ) = 1 := by
        apply Subtype.ext
        exact hpow
      have hzpowRes : (IsLocalRing.residue P.1 zetaA) ^
          (ell : ℕ) = 1 := by
        rw [← map_pow, hpowA, map_one]
      have hzres0 : IsLocalRing.residue P.1 zetaA ≠ 0 := by
        intro hz
        rw [hz, zero_pow ell.1.2.ne_zero] at hzpowRes
        exact zero_ne_one hzpowRes
      exact mul_right_cancel₀ hzres0 (hm.trans (one_mul _).symm)
    have hrone : r = 1 :=
      rootOfPrimeOrder_eq_one_of_residue_eq_one P.1 p (ell : ℕ)
        (residueCharacteristic_prime (ambientFinitePlace P)) ell.1.2
        haway r hrpow hrres
    dsimp [r] at hrone
    apply mul_right_cancel₀ (inv_ne_zero hzeta0)
    simpa [hrone, hzeta0]
  let ga : Field.absoluteGaloisGroup K := R.galoisEquiv.symm g
  change absoluteCyclotomicScalar K ell ga = 1
  apply (absoluteCyclotomicScalar_eq_one_iff K ell ga).2
  intro zeta hpow
  apply R.closureEquiv.injective
  calc
    R.closureEquiv (NU.LocalTheory.absoluteGaloisAlgEquiv ga zeta) =
        R.galoisEquiv ga • R.closureEquiv zeta :=
      R.action_compat ga zeta
    _ = g • R.closureEquiv zeta := by
      rw [R.galoisEquiv.apply_symm_apply]
    _ = R.closureEquiv zeta := hrootfix _ (by
      rw [← map_pow, hpow, map_one])

/-- **Arithmetic obligation, Blueprint `prop:inertia`.**  T5 and
`lem:unram-cyc`, together with `orderDivisibility`, identify inertia with the
intersection of the kernels of all odd away-from-`p` cyclotomic characters. -/
private theorem ambientInertia_iff_cyclotomic
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (g : G)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (horder : OrderDivisibilityPrinciple) :
    ActsAsPowerOnResidue P.1 g 1 ↔
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
            (ell : ℕ) →
          ambientCyclotomicScalar R ell g = 1 := by
  constructor
  · intro hI ell haway
    exact ambientCyclotomicScalar_eq_one_of_inertia
      R P g hI ell haway
  · intro hchi
    let A := abstractPlace R P
    let ga : Field.absoluteGaloisGroup K := R.galoisEquiv.symm g
    have hsource : Subgroup.map R.galoisEquiv.toMulEquiv.toMonoidHom
        (NU.LocalTheory.absoluteDecompositionGroup K A.1) =
          NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 := by
      simpa [A, abstractPlace] using
        NU.LocalTheory.map_absoluteDecompositionGroup_ambient
          R.closureEquiv R.galoisEquiv.toMulEquiv R.action_compat A
    have hga : ga ∈ NU.LocalTheory.absoluteDecompositionGroup K A.1 := by
      have hm : R.galoisEquiv ga ∈
          Subgroup.map R.galoisEquiv.toMulEquiv.toMonoidHom
            (NU.LocalTheory.absoluteDecompositionGroup K A.1) := by
        rw [hsource]
        simpa [ga] using hg
      obtain ⟨x, hx, heq⟩ := hm
      have hxga : x = ga := R.galoisEquiv.injective heq
      simpa [hxga] using hx
    have hchiA (ell : NU.LocalTheory.OddPrime)
        (hawayA : NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace A) ≠ (ell : ℕ)) :
        absoluteCyclotomicScalar K ell ga = 1 := by
      have hawayP : NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ≠ (ell : ℕ) := by
        rwa [ambientFinitePlace_abstractPlace R P] at hawayA
      simpa [ambientCyclotomicScalar, ga] using hchi ell hawayP
    have hlevels (L : NU.LocalTheory.GaloisLevel K) :=
      finiteLevelResidueAction_eq_one_of_cyclotomic
        A ga hga hchiA horder L
    have hIA := actsAsPowerOnResidue_one_of_finiteLevelActions
      A ga hga hlevels
    let e : A.1 ≃+* P.1 := by
      simpa [A] using abstractPlaceValuationEquiv R P
    intro x y hy
    rw [pow_one]
    change IsLocalRing.residue P.1 y = IsLocalRing.residue P.1 x
    let xa : A.1 := e.symm x
    let ya : A.1 := e.symm y
    have hya : (ya : AlgebraicClosure K) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
          (xa : AlgebraicClosure K) := by
      apply R.closureEquiv.injective
      calc
        R.closureEquiv (ya : AlgebraicClosure K) = (y : Omega) := by
          simp [ya, e, abstractPlaceValuationEquiv]
        _ = g • (x : Omega) := hy
        _ = R.galoisEquiv ga •
            R.closureEquiv (xa : AlgebraicClosure K) := by
          simp [ga, xa, e, abstractPlaceValuationEquiv]
        _ = R.closureEquiv
            ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
              (xa : AlgebraicClosure K)) :=
          (R.action_compat ga (xa : AlgebraicClosure K)).symm
    have hresA : IsLocalRing.residue A.1 ya =
        IsLocalRing.residue A.1 xa := by
      have h := hIA xa ya hya
      rw [pow_one] at h
      exact h
    have hm := congrArg (IsLocalRing.ResidueField.mapEquiv e) hresA
    simp only [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue] at hm
    simpa [xa, ya] using hm

/-- Away-prime cyclotomic scalars equal to `p^A` force the corresponding
absolute residue Frobenius action. -/
private theorem ambientActsAsPrimePower_of_cyclotomic
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (g : G)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (Aexp : ℕ)
    (hchi : ∀ ell : NU.LocalTheory.OddPrime,
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ≠
          (ell : ℕ) →
        ambientCyclotomicScalar R ell g =
          (NU.LocalTheory.residueCharacteristic
            (ambientFinitePlace P) ^ Aexp : ZMod (ell : ℕ))) :
    ActsAsPowerOnResidue P.1 g
      (NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P) ^ Aexp) := by
  let A := abstractPlace R P
  let ga : Field.absoluteGaloisGroup K := R.galoisEquiv.symm g
  have hfiniteA : ambientFinitePlace A = ambientFinitePlace P := by
    simpa [A] using ambientFinitePlace_abstractPlace R P
  have hpchar : NU.LocalTheory.residueCharacteristic (ambientFinitePlace A) =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) :=
    congrArg NU.LocalTheory.residueCharacteristic hfiniteA
  have hsource : Subgroup.map R.galoisEquiv.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K A.1) =
        NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 := by
    simpa [A, abstractPlace] using
      NU.LocalTheory.map_absoluteDecompositionGroup_ambient
        R.closureEquiv R.galoisEquiv.toMulEquiv R.action_compat A
  have hga : ga ∈ NU.LocalTheory.absoluteDecompositionGroup K A.1 := by
    have hm : R.galoisEquiv ga ∈
        Subgroup.map R.galoisEquiv.toMulEquiv.toMonoidHom
          (NU.LocalTheory.absoluteDecompositionGroup K A.1) := by
      rw [hsource]
      simpa [ga] using hg
    obtain ⟨x, hx, heq⟩ := hm
    have hxga : x = ga := R.galoisEquiv.injective heq
    simpa [hxga] using hx
  have hchiA (ell : NU.LocalTheory.OddPrime)
      (hawayA : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace A) ≠ (ell : ℕ)) :
      absoluteCyclotomicScalar K ell ga =
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace A) ^ Aexp : ZMod (ell : ℕ)) := by
    have hawayP : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P) ≠ (ell : ℕ) := by
      rwa [hfiniteA] at hawayA
    rw [hfiniteA]
    simpa [ambientCyclotomicScalar, ga] using hchi ell hawayP
  have hlevels (L : NU.LocalTheory.GaloisLevel K)
      (x : NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel A.1 A.2 L)) :=
    finiteLevelResidueAction_eq_primePower_of_cyclotomic
      A ga hga Aexp hchiA orderDivisibility L x
  have hIA := actsAsPowerOnResidue_primePower_of_finiteLevelActions
    A ga hga Aexp hlevels
  let e : A.1 ≃+* P.1 := by
    simpa [A] using abstractPlaceValuationEquiv R P
  intro x y hy
  let xa : A.1 := e.symm x
  let ya : A.1 := e.symm y
  have hya : (ya : AlgebraicClosure K) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
        (xa : AlgebraicClosure K) := by
    apply R.closureEquiv.injective
    calc
      R.closureEquiv (ya : AlgebraicClosure K) = (y : Omega) := by
        simp [ya, e, abstractPlaceValuationEquiv]
      _ = g • (x : Omega) := hy
      _ = R.galoisEquiv ga •
          R.closureEquiv (xa : AlgebraicClosure K) := by
        simp [ga, xa, e, abstractPlaceValuationEquiv]
      _ = R.closureEquiv
          ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
            (xa : AlgebraicClosure K)) :=
        (R.action_compat ga (xa : AlgebraicClosure K)).symm
  have hresA : IsLocalRing.residue A.1 ya =
      IsLocalRing.residue A.1 xa ^
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace A) ^ Aexp) := hIA xa ya hya
  have hm := congrArg (IsLocalRing.ResidueField.mapEquiv e) hresA
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue, map_pow] at hm
  have hmapxa : IsLocalRing.ResidueField.mapEquiv e
      (IsLocalRing.residue A.1 xa) =
        IsLocalRing.residue P.1 (e xa) := by
    rw [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hexa : e xa = x := by simp [xa]
  have heya : e ya = y := by simp [ya]
  rw [hmapxa, hexa, hpchar] at hm
  change IsLocalRing.residue P.1 y =
    IsLocalRing.residue P.1 x ^
      (NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P) ^ Aexp)
  simpa [ya] using hm

/-- Cyclotomic-character transport preserves every natural absolute
Frobenius power on the two ambient residue fields. -/
private theorem ambientPrimePowerAction_preserved_from_chi
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (Aexp : ℕ) :
    ActsAsPowerOnResidue P₁.1 g
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P₁) ^ Aexp) ↔
      ActsAsPowerOnResidue P₂.1 (theta g)
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P₂) ^ Aexp) := by
  have hthetag : theta g ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  have hchar := ambientResidueCharacteristic_preserved
    R₁ R₂ theta P₁ P₂ hmap
  constructor
  · intro hpower
    apply ambientActsAsPrimePower_of_cyclotomic
      R₂ P₂ (theta g) hthetag Aexp
    intro ell haway₂
    have haway₁ : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P₁) ≠ (ell : ℕ) := by
      rwa [hchar]
    rw [hchi g hg ell haway₁,
      ambientCyclotomicScalar_eq_natCast_of_power
        R₁ P₁ g _ hpower ell haway₁]
    rw [Nat.cast_pow, hchar]
  · intro hpower
    apply ambientActsAsPrimePower_of_cyclotomic R₁ P₁ g hg Aexp
    intro ell haway₁
    have haway₂ : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P₂) ≠ (ell : ℕ) := by
      rwa [← hchar]
    rw [← hchi g hg ell haway₁,
      ambientCyclotomicScalar_eq_natCast_of_power
        R₂ P₂ (theta g) _ hpower ell haway₂]
    rw [Nat.cast_pow, hchar]

/-- Formal assembly of Blueprint `prop:inertia` from pointwise
cyclotomic-character preservation and the two kernel characterizations. -/
private theorem ambientInertia_preserved_from_chi
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) :
    ActsAsPowerOnResidue P₁.1 g 1 ↔
      ActsAsPowerOnResidue P₂.1 (theta g) 1 := by
  have hthetag : theta g ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  have hchar := ambientResidueCharacteristic_preserved
    R₁ R₂ theta P₁ P₂ hmap
  rw [ambientInertia_iff_cyclotomic R₁ P₁ g hg orderDivisibility,
    ambientInertia_iff_cyclotomic R₂ P₂ (theta g) hthetag
      orderDivisibility]
  constructor
  · intro hsource ell haway₂
    have haway₁ : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P₁) ≠ (ell : ℕ) := by
      rwa [hchar]
    rw [hchi g hg ell haway₁]
    exact hsource ell haway₁
  · intro htarget ell haway₁
    have haway₂ : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P₂) ≠ (ell : ℕ) := by
      rwa [← hchar]
    rw [← hchi g hg ell haway₁]
    exact htarget ell haway₂

/-- Blueprint `lem:bridge` micro-lemma: `N = 0` is impossible because the
putative power map sends `0` to `0^0 = 1`. -/
private theorem actsAsPowerOnResidue_ne_zero
    {Omega G : Type*} [Field Omega] [Group G]
    [MulSemiringAction G Omega]
    (W : ValuationSubring Omega) (g : G) (N : ℕ)
    (hpower : ActsAsPowerOnResidue W g N) : N ≠ 0 := by
  intro hN
  subst N
  have hzero := hpower (0 : W) (0 : W) (by simp)
  simpa using hzero

/-- The residue-tower facts used by the power-map classification.  They are
not consequences of an arbitrary ambient extension: they hold here because
the ambient field is an algebraic closure and the valuation is an absolute
place, so its residue field is `Fbar_p`. -/
private structure AmbientAlgebraicResidueTower
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) where
  residue_isAlgClosed : IsAlgClosed (IsLocalRing.ResidueField P.1)
  residue_charP : CharP (IsLocalRing.ResidueField P.1)
    (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P))

/-- The residue field of a valuation subring of an algebraically closed field
is algebraically closed. -/
private theorem valuationSubring_residue_isAlgClosed
    {Omega : Type*} [Field Omega] [IsAlgClosed Omega]
    (W : ValuationSubring Omega) :
    IsAlgClosed (IsLocalRing.ResidueField W) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue W) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective (IsLocalRing.residue W)
      IsLocalRing.residue_surjective p
  obtain ⟨q, hq, hdegree, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  have hpdegree : p.degree ≠ 0 := by
    intro hdegreeZero
    have hpNat : p.natDegree = 0 := by
      rw [Polynomial.natDegree]
      simp [hdegreeZero]
    have hpone : p = 1 := (hp.natDegree_eq_zero).mp hpNat
    exact hirr.not_isUnit (hpone.symm ▸ isUnit_one)
  have hqOmegaDegree :
      (q.map (algebraMap W Omega)).degree ≠ 0 := by
    rw [hqmonic.degree_map, hdegree]
    exact hpdegree
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (q.map (algebraMap W Omega)) hqOmegaDegree
  have hxIntegral : IsIntegral W x := by
    apply IsIntegral.of_aeval_monic hqmonic
    · intro hzero
      have hqone : q = 1 := (hqmonic.natDegree_eq_zero).mp hzero
      have hpone : p = 1 := by simpa [hqone] using hq.symm
      exact hirr.not_isUnit (hpone.symm ▸ isUnit_one)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hx]
      exact isIntegral_zero
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hxIntegral
  refine ⟨IsLocalRing.residue W y, ?_⟩
  rw [← hq]
  apply Polynomial.IsRoot.map
  apply Polynomial.IsRoot.of_map (f := algebraMap W Omega)
  · simpa [hy] using hx
  · intro a b hab
    exact Subtype.ext hab

/-- The field in an absolute-Galois action realization is algebraically
closed, independently of its chosen presentation. -/
private theorem ambientField_isAlgClosed
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G) :
    IsAlgClosed Omega := by
  constructor
  intro p
  have h := (IsAlgClosed.splits
    (p.map R.closureEquiv.symm.toRingEquiv.toRingHom)).map
      R.closureEquiv.toRingEquiv.toRingHom
  rw [Polynomial.map_map] at h
  have hc : R.closureEquiv.toRingEquiv.toRingHom.comp
      R.closureEquiv.symm.toRingEquiv.toRingHom = RingHom.id Omega := by
    ext x
    simp
  rw [hc, Polynomial.map_id] at h
  exact h

/-- The algebraic-closure and characteristic fields of the absolute residue
tower are already forced by an ambient realization. -/
private theorem ambientAlgebraicResidueTowerData
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) :
    AmbientAlgebraicResidueTower P where
  residue_isAlgClosed := by
    letI : IsAlgClosed Omega := ambientField_isAlgClosed R
    exact valuationSubring_residue_isAlgClosed P.1
  residue_charP := ambientResidueField_charP P

/-- Restricting the center of an absolute place from any finite Galois
level returns its original finite place. -/
private theorem restrictFinitePlace_absolutePlaceAtLevel
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.restrictFinitePlace K
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L) =
      ambientFinitePlace P := by
  let w := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let A := P.1.comap (algebraMap K (AlgebraicClosure K))
  have hA : NU.LocalTheory.IsNontrivialValuation A :=
    ambientPlace_comap_nontrivial P
  have hw : NU.LocalTheory.primeValuationSubring
      (NU.LocalTheory.restrictFinitePlace K w) = A := by
    rw [← primeValuationSubring_restrictFinitePlace K w]
    change (NU.LocalTheory.primeValuationSubring w).comap
      (algebraMap K L.field) = A
    rw [show NU.LocalTheory.primeValuationSubring w =
        P.1.comap L.field.val.toRingHom from
      NU.LocalTheory.primeValuationSubring_centerFinitePlace _ _]
    apply ValuationSubring.ext
    intro x
    rfl
  apply (NU.LocalTheory.numberField_valuations A hA).unique
  · exact hw.symm
  · exact (primeValuationSubring_ambientFinitePlace P).symm

/-- At every finite Galois level, a decomposition element realizes the
arithmetic Frobenius of the base residue field. -/
private theorem finiteLevelArithmeticFrobenius_exists
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    ∃ g : Field.absoluteGaloisGroup K,
      ∃ hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1,
        ∀ x : NU.LocalTheory.ResidueFieldAt
            (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L),
          finiteLevelResidueAction P g hg L x =
            x ^ ambientResidueNorm P := by
  let w := NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L
  let G := L.field ≃ₐ[K] L.field
  let R := 𝓞 K
  let S := 𝓞 L.field
  let p : Ideal R := w.asIdeal.under R
  letI : p.IsPrime := inferInstance
  letI : p.IsMaximal := inferInstance
  letI : w.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (R ⧸ p) := Fintype.ofFinite _
  letI : Fintype (S ⧸ w.asIdeal) := Fintype.ofFinite _
  let frob : (S ⧸ w.asIdeal) ≃ₐ[R ⧸ p] (S ⧸ w.asIdeal) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic _ _
  obtain ⟨sigma, hsigma⟩ :=
    Ideal.Quotient.stabilizerHom_surjective G p w.asIdeal frob
  have hpv : p = (ambientFinitePlace P).asIdeal := by
    change (NU.LocalTheory.restrictFinitePlace K w).asIdeal =
      (ambientFinitePlace P).asIdeal
    rw [restrictFinitePlace_absolutePlaceAtLevel P L]
  have hbaseCard : Fintype.card (R ⧸ p) = ambientResidueNorm P := by
    calc
      Fintype.card (R ⧸ p) = Nat.card (R ⧸ p) :=
        (Nat.card_eq_fintype_card).symm
      _ = Ideal.absNorm p := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      _ = Ideal.absNorm (ambientFinitePlace P).asIdeal := by rw [hpv]
      _ = ambientResidueNorm P := rfl
  have hfrob (z : S ⧸ w.asIdeal) :
      frob z = z ^ ambientResidueNorm P := by
    change z ^ Fintype.card (R ⧸ p) = _
    rw [hbaseCard]
  have hquot (a : S) :
      Ideal.Quotient.mk w.asIdeal (sigma.1 • a) =
        (Ideal.Quotient.mk w.asIdeal a) ^ ambientResidueNorm P := by
    have h := DFunLike.congr_fun hsigma
      (Ideal.Quotient.mk w.asIdeal a)
    rw [Ideal.Quotient.stabilizerHom_apply] at h
    exact h.trans (hfrob _)
  letI := NU.LocalTheory.finitePlaceAction K L.field
  let sigmaD : NU.LocalTheory.decompositionGroup K w :=
    ⟨sigma.1, by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact sigma.2⟩
  have himage : sigma.1 ∈ NU.LocalTheory.finiteLevelImage L
      (NU.LocalTheory.absoluteDecompositionGroup K P.1) := by
    rw [NU.LocalTheory.absoluteDecompositionGroup_finiteImage P.1 P.2 L]
    exact sigmaD.2
  obtain ⟨g, hg, hgL⟩ := himage
  refine ⟨g, hg, ?_⟩
  intro x
  let e := quotientEquivResidueFieldAt_matrix w
  obtain ⟨z, rfl⟩ := e.surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  let A := NU.LocalTheory.primeValuationSubring w
  letI hfrac : IsFractionRing S L.field := inferInstance
  let bA (b : S) : A := ⟨(b : L.field), by
    rw [NU.LocalTheory.mem_primeValuationSubring_iff]
    exact ⟨b, 1, (Ideal.ne_top_iff_one w.asIdeal).mp w.isPrime.ne_top, by
      simp only [NumberField.RingOfIntegers.coe_eq_algebraMap,
        map_one, mul_one]⟩⟩
  have he (b : S) :
      e (Ideal.Quotient.mk w.asIdeal b) =
        IsLocalRing.residue A (bA b) := by
    change (IsLocalization.AtPrime.equivQuotMaximalIdeal w.asIdeal
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L.field w))
        (Ideal.Quotient.mk w.asIdeal b) = _
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    apply congrArg (Ideal.Quotient.mk _)
    apply Subtype.ext
    change algebraMap S L.field b = (b : L.field)
    exact (NumberField.RingOfIntegers.coe_eq_algebraMap b).symm
  calc
    finiteLevelResidueAction P g hg L
        (e (Ideal.Quotient.mk w.asIdeal a)) =
        e (Ideal.Quotient.mk w.asIdeal (sigma.1 • a)) := by
      rw [he a, finiteLevelResidueAction,
        IsLocalRing.ResidueField.mapEquiv_apply,
        IsLocalRing.ResidueField.map_residue, he (sigma.1 • a)]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      change NU.LocalTheory.absoluteRestriction L g (a : L.field) =
        ((sigma.1 • a : S) : L.field)
      rw [hgL]
      rfl
    _ = e ((Ideal.Quotient.mk w.asIdeal a) ^ ambientResidueNorm P) :=
      congrArg e (hquot a)
    _ = (e (Ideal.Quotient.mk w.asIdeal a)) ^ ambientResidueNorm P := by
      rw [map_pow]

/-- The finite-level arithmetic-Frobenius condition on an element of an
absolute decomposition group. -/
private def IsFiniteLevelArithmeticFrobenius
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K)
    (g : NU.LocalTheory.absoluteDecompositionGroup K P.1) : Prop :=
  ∀ x : NU.LocalTheory.ResidueFieldAt
      (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L),
    finiteLevelResidueAction P g.1 g.2 L x =
      x ^ ambientResidueNorm P

/-- The finite-level residue action depends only on the restriction of the
absolute Galois element to that level. -/
private theorem finiteLevelResidueAction_eq_of_restriction_eq
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K)
    (g h : NU.LocalTheory.absoluteDecompositionGroup K P.1)
    (heq : NU.LocalTheory.absoluteRestriction L g.1 =
      NU.LocalTheory.absoluteRestriction L h.1) :
    finiteLevelResidueAction P g.1 g.2 L =
      finiteLevelResidueAction P h.1 h.2 L := by
  let eg := stableValuationRingEquiv_matrix K L.field
    (NU.LocalTheory.absoluteRestriction L g.1)
    (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)
    (absoluteRestriction_stabilizes_place P g.1 g.2 L)
  let eh := stableValuationRingEquiv_matrix K L.field
    (NU.LocalTheory.absoluteRestriction L h.1)
    (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)
    (absoluteRestriction_stabilizes_place P h.1 h.2 L)
  have he : eg = eh := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun heq (x : L.field)
  exact congrArg IsLocalRing.ResidueField.mapEquiv he

/-- At a fixed finite level, the arithmetic-Frobenius locus is closed in the
absolute decomposition group. -/
private theorem isClosed_isFiniteLevelArithmeticFrobenius
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    IsClosed {g : NU.LocalTheory.absoluteDecompositionGroup K P.1 |
      IsFiniteLevelArithmeticFrobenius P L g} := by
  let D := NU.LocalTheory.absoluteDecompositionGroup K P.1
  let r : D → (L.field ≃ₐ[K] L.field) := fun g =>
    NU.LocalTheory.absoluteRestriction L g.1
  let T : Set (L.field ≃ₐ[K] L.field) :=
    {sigma | ∃ g : D,
      IsFiniteLevelArithmeticFrobenius P L g ∧ r g = sigma}
  have hT : IsClosed T := Set.toFinite T |>.isClosed
  have hr : Continuous r := by
    exact (InfiniteGalois.restrictNormalHom_continuous L.field).comp
      continuous_subtype_val
  rw [show {g : D | IsFiniteLevelArithmeticFrobenius P L g} =
      r ⁻¹' T by
    ext g
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨h, hh, heq⟩
      intro x
      rw [finiteLevelResidueAction_eq_of_restriction_eq P L g h heq.symm]
      exact hh x]
  exact hT.preimage hr

/-- Finite-level arithmetic-Frobenius loci are nonempty. -/
private theorem isFiniteLevelArithmeticFrobenius_nonempty
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    (L : NU.LocalTheory.GaloisLevel K) :
    Set.Nonempty {g : NU.LocalTheory.absoluteDecompositionGroup K P.1 |
      IsFiniteLevelArithmeticFrobenius P L g} := by
  obtain ⟨g, hg, hpower⟩ := finiteLevelArithmeticFrobenius_exists P L
  exact ⟨⟨g, hg⟩, hpower⟩

/-- Arithmetic-Frobenius conditions descend along inclusions of finite
Galois levels. -/
private theorem isFiniteLevelArithmeticFrobenius_antitone
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K)
    {L M : NU.LocalTheory.GaloisLevel K} (hLM : L.LE M) :
    {g : NU.LocalTheory.absoluteDecompositionGroup K P.1 |
        IsFiniteLevelArithmeticFrobenius P M g} ⊆
      {g : NU.LocalTheory.absoluteDecompositionGroup K P.1 |
        IsFiniteLevelArithmeticFrobenius P L g} := by
  intro g hg x
  apply (finiteLevelResidueMap P hLM).injective
  calc
    finiteLevelResidueMap P hLM
        (finiteLevelResidueAction P g.1 g.2 L x) =
      finiteLevelResidueAction P g.1 g.2 M
        (finiteLevelResidueMap P hLM x) :=
      finiteLevelResidueAction_natural P g.1 g.2 hLM x
    _ = (finiteLevelResidueMap P hLM x) ^ ambientResidueNorm P :=
      hg _
    _ = finiteLevelResidueMap P hLM
        (x ^ ambientResidueNorm P) := by rw [map_pow]

/-- A common finite Galois overlevel, used to direct the Frobenius loci. -/
private noncomputable def residueSupGaloisLevel
    {K : Type*} [Field K] [NumberField K]
    (L M : NU.LocalTheory.GaloisLevel K) :
    NU.LocalTheory.GaloisLevel K where
  field := L.field ⊔ M.field
  finiteDimensional := L.field.finiteDimensional_sup M.field
  numberField := NumberField.of_module_finite K _
  isGalois := by infer_instance

/-- Compactness supplies one absolute decomposition element inducing the
base arithmetic Frobenius at every finite Galois level. -/
private theorem absoluteArithmeticFrobenius_exists
    {K : Type*} [Field K] [NumberField K]
    (P : NU.LocalTheory.AbsoluteFinitePlaceOf K) :
    ∃ g : Field.absoluteGaloisGroup K,
      ∃ hg : g ∈ NU.LocalTheory.absoluteDecompositionGroup K P.1,
        @ActsAsPowerOnResidue (AlgebraicClosure K)
          (Field.absoluteGaloisGroup K) _ _ (by
            change MulSemiringAction
              (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
              (AlgebraicClosure K)
            exact AlgEquiv.applyMulSemiringAction)
          P.1 g (ambientResidueNorm P) := by
  let D := NU.LocalTheory.absoluteDecompositionGroup K P.1
  let C : NU.LocalTheory.GaloisLevel K → Set D := fun L =>
    {g | IsFiniteLevelArithmeticFrobenius P L g}
  have hCnonempty (L : NU.LocalTheory.GaloisLevel K) :
      (C L).Nonempty := isFiniteLevelArithmeticFrobenius_nonempty P L
  have hCclosed (L : NU.LocalTheory.GaloisLevel K) :
      IsClosed (C L) := isClosed_isFiniteLevelArithmeticFrobenius P L
  have hCdirected : Directed (fun A B : Set D => A ⊇ B) C := by
    intro L M
    let N := residueSupGaloisLevel L M
    exact ⟨N,
      isFiniteLevelArithmeticFrobenius_antitone P le_sup_left,
      isFiniteLevelArithmeticFrobenius_antitone P le_sup_right⟩
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    NU.LocalTheory.absoluteGaloisGroup_compactSpace
  letI : CompactSpace D :=
    (NU.LocalTheory.absoluteDecompositionGroup_isClosed K P.1)
      |>.isClosedEmbedding_subtypeVal.compactSpace
  obtain ⟨g, hg⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hCdirected hCnonempty
      (fun L => (hCclosed L).isCompact) hCclosed
  have hlevels (L : NU.LocalTheory.GaloisLevel K)
      (x : NU.LocalTheory.ResidueFieldAt
        (NU.LocalTheory.absolutePlaceAtLevel P.1 P.2 L)) :
      finiteLevelResidueAction P g.1 g.2 L x =
        x ^ ambientResidueNorm P :=
    Set.mem_iInter.mp hg L x
  have hnorm : ambientResidueNorm P =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
        ambientResidueDegree P := by
    rw [ambientResidueNorm_eq_pow, norm_eq_residueCharacteristic_rat,
      ambientRationalPrime, residueCharacteristic_restrictFinitePlace]
  refine ⟨g.1, g.2, ?_⟩
  have hpower := actsAsPowerOnResidue_primePower_of_finiteLevelActions
    P g.1 g.2 (ambientResidueDegree P) (fun L x => by
      simpa only [hnorm] using hlevels L x)
  simpa only [hnorm] using hpower

/-- The residue norm is the residue characteristic to the absolute residue
degree. -/
private theorem ambientResidueNorm_eq_residueCharacteristic_pow
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    ambientResidueNorm P =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
        ambientResidueDegree P := by
  rw [ambientResidueNorm_eq_pow, norm_eq_residueCharacteristic_rat,
    ambientRationalPrime, residueCharacteristic_restrictFinitePlace]

/-- On a finite field of cardinality `p^f`, a `p^a`-power map can be
the identity only when `f` divides `a`. -/
private theorem finiteField_degree_dvd_of_frobenius_pow_eq
    {F : Type*} [Field F] [Finite F]
    (p f a : ℕ) (hp : p.Prime) [CharP F p]
    (hcard : Nat.card F = p ^ f)
    (hfix : ∀ x : F, x ^ (p ^ a) = x) : f ∣ a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype F := Fintype.ofFinite F
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F
  have hfrob : frob ^ a = 1 := by
    apply DFunLike.ext _ _
    intro x
    change (frob ^ a) x = x
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simpa using hfix x
  have hord : Module.finrank (ZMod p) F ∣ a := by
    rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) F]
    exact (orderOf_dvd_iff_pow_eq_one).2 hfrob
  have hfinrank : Module.finrank (ZMod p) F = f := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ Module.finrank (ZMod p) F =
          Fintype.card (ZMod p) ^ Module.finrank (ZMod p) F := by
            rw [ZMod.card]
      _ = Fintype.card F := Module.card_eq_pow_finrank.symm
      _ = Nat.card F := by rw [Nat.card_eq_fintype_card]
      _ = p ^ f := hcard
  rwa [hfinrank] at hord

/-- If an ambient decomposition element acts by a natural `p`-Frobenius
power, that exponent is divisible by the absolute residue degree. -/
private theorem ambientResidueDegree_dvd_powerExponent
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (g : G)
    (_hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (a : ℕ)
    (hpower : ActsAsPowerOnResidue P.1 g
      (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^ a)) :
    ambientResidueDegree P ∣ a := by
  let v := ambientFinitePlace P
  let p := NU.LocalTheory.residueCharacteristic v
  let fdeg := ambientResidueDegree P
  let A := P.1.comap (algebraMap K Omega)
  have hA : NU.LocalTheory.primeValuationSubring v = A :=
    primeValuationSubring_ambientFinitePlace P
  let eA : NU.LocalTheory.primeValuationSubring v ≃+* A :=
    { toFun := fun x => ⟨x, by rw [← hA]; exact x.property⟩
      invFun := fun x => ⟨x, by rw [hA]; exact x.property⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_mul' := fun x y => by ext; rfl }
  let er : NU.LocalTheory.ResidueFieldAt v ≃+*
      IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.mapEquiv eA
  let inc := valuationComapInclusion (algebraMap K Omega) P.1
  letI : IsLocalHom inc := valuationComapInclusion_isLocal _ _
  let rm := IsLocalRing.ResidueField.map inc
  let i : NU.LocalTheory.ResidueFieldAt v →+*
      IsLocalRing.ResidueField P.1 := rm.comp er.toRingHom
  have hi : Function.Injective i := i.injective
  have hfix : ∀ z : NU.LocalTheory.ResidueFieldAt v,
      z ^ (p ^ a) = z := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    apply hi
    have hires : i (IsLocalRing.residue
        (NU.LocalTheory.primeValuationSubring v) x) =
        IsLocalRing.residue P.1 (inc (eA x)) := by
      change rm (er (IsLocalRing.residue
        (NU.LocalTheory.primeValuationSubring v) x)) = _
      rw [IsLocalRing.ResidueField.mapEquiv_apply,
        IsLocalRing.ResidueField.map_residue,
        IsLocalRing.ResidueField.map_residue]
      rfl
    rw [map_pow, hires]
    symm
    apply hpower (inc (eA x)) (inc (eA x))
    let ga : Field.absoluteGaloisGroup K := R.galoisEquiv.symm g
    change algebraMap K Omega (x : K) =
      g • algebraMap K Omega (x : K)
    calc
      algebraMap K Omega (x : K) =
          R.closureEquiv (algebraMap K (AlgebraicClosure K) (x : K)) := by
        rw [R.closureEquiv.commutes]
      _ = R.closureEquiv
          (NU.LocalTheory.absoluteGaloisAlgEquiv ga
            (algebraMap K (AlgebraicClosure K) (x : K))) := by
        congr 1
        exact ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga).commutes
          (x : K)).symm
      _ = R.galoisEquiv ga •
          R.closureEquiv (algebraMap K (AlgebraicClosure K) (x : K)) :=
        R.action_compat ga
          (algebraMap K (AlgebraicClosure K) (x : K))
      _ = g • algebraMap K Omega (x : K) := by
        simp [ga]
  let k := NU.LocalTheory.ResidueFieldAt v
  letI : Finite k := residueFieldAt_finite_matrix v
  have hcard : Nat.card k = p ^ fdeg := by
    calc
      Nat.card k = Ideal.absNorm v.asIdeal :=
        (absNorm_eq_natCard_residueFieldAt_matrix v).symm
      _ = ambientResidueNorm P := rfl
      _ = p ^ fdeg :=
        ambientResidueNorm_eq_residueCharacteristic_pow P
  letI : CharP k p := ringChar.charP k
  exact finiteField_degree_dvd_of_frobenius_pow_eq p fdeg a
    (residueCharacteristic_prime v) hcard hfix

/-- Every ambient absolute decomposition group contains a lift of its
normalized arithmetic Frobenius. -/
private theorem ambientArithmeticFrobenius_exists
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) :
    ∃ g : G,
      ∃ hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1,
        ActsAsPowerOnResidue P.1 g (ambientResidueNorm P) := by
  let A := abstractPlace R P
  obtain ⟨ga, hga, hpowerA⟩ := absoluteArithmeticFrobenius_exists A
  have hsource : Subgroup.map R.galoisEquiv.toMulEquiv.toMonoidHom
      (NU.LocalTheory.absoluteDecompositionGroup K A.1) =
        NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 := by
    simpa [A, abstractPlace] using
      NU.LocalTheory.map_absoluteDecompositionGroup_ambient
        R.closureEquiv R.galoisEquiv.toMulEquiv R.action_compat A
  let g : G := R.galoisEquiv ga
  have hg : g ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 := by
    rw [← hsource]
    exact ⟨ga, hga, rfl⟩
  have hnorm : ambientResidueNorm A = ambientResidueNorm P := by
    unfold ambientResidueNorm
    rw [ambientFinitePlace_abstractPlace R P]
  let e : A.1 ≃+* P.1 := by
    simpa [A] using abstractPlaceValuationEquiv R P
  refine ⟨g, hg, ?_⟩
  intro x y hy
  let xa : A.1 := e.symm x
  let ya : A.1 := e.symm y
  have hya : (ya : AlgebraicClosure K) =
      (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
        (xa : AlgebraicClosure K) := by
    apply R.closureEquiv.injective
    calc
      R.closureEquiv (ya : AlgebraicClosure K) = (y : Omega) := by
        simp [ya, e, abstractPlaceValuationEquiv]
      _ = g • (x : Omega) := hy
      _ = R.galoisEquiv ga •
          R.closureEquiv (xa : AlgebraicClosure K) := by
        simp [g, xa, e, abstractPlaceValuationEquiv]
      _ = R.closureEquiv
          ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from ga)
            (xa : AlgebraicClosure K)) :=
        (R.action_compat ga (xa : AlgebraicClosure K)).symm
  have hresA : IsLocalRing.residue A.1 ya =
      IsLocalRing.residue A.1 xa ^ ambientResidueNorm A :=
    hpowerA xa ya hya
  have hm := congrArg (IsLocalRing.ResidueField.mapEquiv e) hresA
  rw [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue, map_pow] at hm
  have hmapxa : IsLocalRing.ResidueField.mapEquiv e
      (IsLocalRing.residue A.1 xa) =
        IsLocalRing.residue P.1 (e xa) := by
    rw [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hexa : e xa = x := by simp [xa]
  have heya : e ya = y := by simp [ya]
  rw [hmapxa, hexa] at hm
  change IsLocalRing.residue P.1 y =
    IsLocalRing.residue P.1 x ^ ambientResidueNorm P
  calc
    IsLocalRing.residue P.1 y =
        IsLocalRing.residue P.1 (e ya) :=
      congrArg (IsLocalRing.residue P.1) heya.symm
    _ = IsLocalRing.residue P.1 x ^ ambientResidueNorm A := hm
    _ = IsLocalRing.residue P.1 x ^ ambientResidueNorm P := by rw [hnorm]

/-- Pointwise transport of cyclotomic scalars forces equality of the two
absolute residue degrees.  Compactness supplies Frobenius lifts in both
directions, and finite-residue rigidity turns their transported prime-power
actions into the two divisibilities. -/
private theorem ambientResidueDegree_preserved_from_chi
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g) :
    ambientResidueDegree P₁ = ambientResidueDegree P₂ := by
  have hnorm₁ := ambientResidueNorm_eq_residueCharacteristic_pow P₁
  have hnorm₂ := ambientResidueNorm_eq_residueCharacteristic_pow P₂
  obtain ⟨g₁, hg₁, hfrob₁⟩ := ambientArithmeticFrobenius_exists R₁ P₁
  have htheta₁ : theta g₁ ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
    rw [← hmap]
    exact ⟨g₁, hg₁, rfl⟩
  have hpower₂ : ActsAsPowerOnResidue P₂.1 (theta g₁)
      (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂) ^
        ambientResidueDegree P₁) := by
    apply (ambientPrimePowerAction_preserved_from_chi
      R₁ R₂ theta P₁ P₂ hmap hchi g₁ hg₁
        (ambientResidueDegree P₁)).mp
    simpa only [hnorm₁] using hfrob₁
  have hdvd₂₁ : ambientResidueDegree P₂ ∣ ambientResidueDegree P₁ :=
    ambientResidueDegree_dvd_powerExponent R₂ P₂ (theta g₁)
      htheta₁ (ambientResidueDegree P₁) hpower₂
  obtain ⟨g₂, hg₂, hfrob₂⟩ := ambientArithmeticFrobenius_exists R₂ P₂
  let g₁' : G₁ := theta.symm g₂
  have hg₁' : g₁' ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 := by
    have hm : g₂ ∈ Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) := by
      rw [hmap]
      exact hg₂
    obtain ⟨g, hg, heq⟩ := hm
    have htheta' : theta.toMulEquiv g₁' = g₂ := by
      exact theta.apply_symm_apply g₂
    have hgeq : g = g₁' :=
      theta.toMulEquiv.injective (heq.trans htheta'.symm)
    rwa [← hgeq]
  have htheta' : theta g₁' = g₂ := by
    exact theta.apply_symm_apply g₂
  have hpower₁ : ActsAsPowerOnResidue P₁.1 g₁'
      (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ^
        ambientResidueDegree P₂) := by
    apply (ambientPrimePowerAction_preserved_from_chi
      R₁ R₂ theta P₁ P₂ hmap hchi g₁' hg₁'
        (ambientResidueDegree P₂)).mpr
    rw [htheta']
    simpa only [hnorm₂] using hfrob₂
  have hdvd₁₂ : ambientResidueDegree P₁ ∣ ambientResidueDegree P₂ :=
    ambientResidueDegree_dvd_powerExponent R₁ P₁ g₁' hg₁'
      (ambientResidueDegree P₂) hpower₁
  exact Nat.dvd_antisymm hdvd₁₂ hdvd₂₁

/-- A natural `p`-Frobenius exponent for one stabilized residue action is
unique. -/
private theorem actsAsPowerOnResidue_primePower_exponent_unique
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (P : AmbientAbsolutePlace K Omega)
    (tower : AmbientAlgebraicResidueTower P)
    (g : G)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (p a b : ℕ) (hp : 2 ≤ p)
    (ha : ActsAsPowerOnResidue P.1 g (p ^ a))
    (hb : ActsAsPowerOnResidue P.1 g (p ^ b)) : a = b := by
  let F := IsLocalRing.ResidueField P.1
  letI : IsAlgClosed F := tower.residue_isAlgClosed
  have hpowers : ∀ z : F, z ^ (p ^ a) = z ^ (p ^ b) := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    let gx : P.1 := ⟨g • (x : Omega), by
      have hm : g • (x : Omega) ∈ g • (P.1 : Set Omega) :=
        Set.smul_mem_smul_set x.property
      have hset : g • (P.1 : Set Omega) = (P.1 : Set Omega) := by
        change ((g • P.1 : ValuationSubring Omega) : Set Omega) =
          (P.1 : Set Omega)
        rw [show g • P.1 = P.1 from hg]
      rwa [hset] at hm⟩
    have hea := ha x gx rfl
    have heb := hb x gx rfl
    exact hea.symm.trans heb
  have hpoly : (Polynomial.X ^ (p ^ a) : Polynomial F) =
      Polynomial.X ^ (p ^ b) := by
    apply Polynomial.funext
    intro z
    simpa using hpowers z
  have hpow : p ^ a = p ^ b := by
    simpa using congrArg Polynomial.natDegree hpoly
  exact Nat.pow_right_injective hp hpow

/-- A weak but sufficient `zhat` coordinate: natural Frobenius actions get
their unique normalized exponent; every other action is sent to `-1`. -/
private noncomputable def ambientResidueCoordinateCandidate
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [MulSemiringAction G Omega]
    (P : AmbientAbsolutePlace K Omega) (g : G) : ProfiniteIntegers := by
  classical
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  let f := ambientResidueDegree P
  exact if h : ∃ a : ℕ, ActsAsPowerOnResidue P.1 g (p ^ a) then
    if hd : f ∣ h.choose then profiniteIntegerOfNat hd.choose else -1
  else -1

/-- The candidate coordinate has the two natural-power properties required
by `AmbientResidueCoordinateData`. -/
private theorem ambientResidueCoordinateCandidate_spec
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (tower : AmbientAlgebraicResidueTower P)
    (hnorm : ambientResidueNorm P =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
        ambientResidueDegree P) :
    (∀ (g : G),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 →
        ∀ a : ℕ, ActsAsPowerOnResidue P.1 g
            (NU.LocalTheory.residueCharacteristic
              (ambientFinitePlace P) ^ a) →
          profiniteIntegerOfNat (ambientResidueDegree P) *
              ambientResidueCoordinateCandidate P g =
            profiniteIntegerOfNat a) ∧
    (∀ (g : G),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 →
        ∀ j : ℕ,
          ambientResidueCoordinateCandidate P g =
              profiniteIntegerOfNat j →
            ActsAsPowerOnResidue P.1 g (ambientResidueNorm P ^ j)) := by
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  let f := ambientResidueDegree P
  have hp : 2 ≤ p := (residueCharacteristic_prime
    (ambientFinitePlace P)).two_le
  constructor
  · intro g hg a ha
    let hex : ∃ b : ℕ, ActsAsPowerOnResidue P.1 g
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ^ b) := ⟨a, ha⟩
    have hua : hex.choose = a :=
      actsAsPowerOnResidue_primePower_exponent_unique P tower g hg
        p hex.choose a hp hex.choose_spec ha
    have hd : ambientResidueDegree P ∣ hex.choose := by
      rw [hua]
      exact ambientResidueDegree_dvd_powerExponent R P g hg a ha
    rw [show ambientResidueCoordinateCandidate P g =
        profiniteIntegerOfNat hd.choose by
      simp only [ambientResidueCoordinateCandidate, dif_pos hex, dif_pos hd]]
    rw [← profiniteIntegerOfNat_mul, ← hd.choose_spec, hua]
  · intro g hg j hcoord
    by_cases he : ∃ a : ℕ, ActsAsPowerOnResidue P.1 g
        (NU.LocalTheory.residueCharacteristic
          (ambientFinitePlace P) ^ a)
    · have hd : ambientResidueDegree P ∣ he.choose :=
        ambientResidueDegree_dvd_powerExponent
          R P g hg he.choose he.choose_spec
      have hc : ambientResidueCoordinateCandidate P g =
          profiniteIntegerOfNat hd.choose := by
        simp [ambientResidueCoordinateCandidate, he, hd]
      have hj : hd.choose = j :=
        profiniteIntegerOfNat_injective (hc.symm.trans hcoord)
      have hN : ambientResidueNorm P ^ j = p ^ he.choose := by
        calc
          ambientResidueNorm P ^ j = (p ^ f) ^ j := by rw [hnorm]
          _ = p ^ (f * j) := by rw [pow_mul]
          _ = p ^ (f * hd.choose) := by rw [hj]
          _ = p ^ he.choose := by rw [← hd.choose_spec]
      rw [hN]
      exact he.choose_spec
    · have hc : ambientResidueCoordinateCandidate P g = -1 := by
        simp [ambientResidueCoordinateCandidate, he]
      exact (neg_one_ne_profiniteIntegerOfNat j
        (hc.symm.trans hcoord)).elim

/-- A stabilized ambient action makes its residue power map additive. -/
private theorem actsAsPowerOnResidue_additive
    {Omega G : Type*} [Field Omega] [Group G]
    [MulSemiringAction G Omega]
    (W : ValuationSubring Omega) (g : G) (N : ℕ)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup W)
    (hpower : ActsAsPowerOnResidue W g N) :
    ∀ z w : IsLocalRing.ResidueField W,
      (z + w) ^ N = z ^ N + w ^ N := by
  intro z w
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
  let gx : W := ⟨g • (x : Omega), by
    have hm : g • (x : Omega) ∈ g • (W : Set Omega) :=
      Set.smul_mem_smul_set x.property
    have hset : g • (W : Set Omega) = (W : Set Omega) := by
      change ((g • W : ValuationSubring Omega) : Set Omega) =
        (W : Set Omega)
      rw [show g • W = W from hg]
    rwa [hset] at hm⟩
  let gy : W := ⟨g • (y : Omega), by
    have hm : g • (y : Omega) ∈ g • (W : Set Omega) :=
      Set.smul_mem_smul_set y.property
    have hset : g • (W : Set Omega) = (W : Set Omega) := by
      change ((g • W : ValuationSubring Omega) : Set Omega) =
        (W : Set Omega)
      rw [show g • W = W from hg]
    rwa [hset] at hm⟩
  have hx := hpower x gx rfl
  have hy := hpower y gy rfl
  have hxy := hpower (x + y) (gx + gy) (by
    change (g • (x : Omega)) + (g • (y : Omega)) =
      g • ((x : Omega) + (y : Omega))
    exact (smul_add g (x : Omega) (y : Omega)).symm)
  change IsLocalRing.residue W (x + y) ^ N =
    IsLocalRing.residue W x ^ N + IsLocalRing.residue W y ^ N
  change IsLocalRing.residue W gx = IsLocalRing.residue W x ^ N at hx
  change IsLocalRing.residue W gy = IsLocalRing.residue W y ^ N at hy
  change IsLocalRing.residue W (gx + gy) =
    IsLocalRing.residue W (x + y) ^ N at hxy
  rw [← hxy, map_add, hx, hy]

/-- Lucas's theorem in the form needed here: an additive nonzero power map
on an algebraically closed field of characteristic `p` has `p`-power
exponent. -/
private theorem additive_power_exponent_eq_primePower
    {F : Type*} [Field F] [IsAlgClosed F]
    (p N : ℕ) [Fact p.Prime] [CharP F p]
    (hN : N ≠ 0)
    (hadd : ∀ z w : F, (z + w) ^ N = z ^ N + w ^ N) :
    ∃ a : ℕ, N = p ^ a := by
  have hpoly : (Polynomial.X + 1 : Polynomial F) ^ N =
      Polynomial.X ^ N + 1 := by
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    simpa using hadd x 1
  refine ⟨multiplicity p N,
    Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat
      (Nat.pos_of_ne_zero hN) ?_⟩
  intro i hi
  have hi' : 1 ≤ i ∧ i ≤ N - 1 := Finset.mem_Icc.mp hi
  have hiN : i < N := by omega
  have hc := congrArg (fun f : Polynomial F => f.coeff i) hpoly
  rw [Polynomial.coeff_X_add_one_pow, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, Polynomial.coeff_one,
    if_neg (ne_of_lt hiN), if_neg (by omega : i ≠ 0)] at hc
  simp only [add_zero] at hc
  rw [Nat.modEq_zero_iff_dvd]
  exact (CharP.cast_eq_zero_iff F p (N.choose i)).mp hc

/-- **Arithmetic micro-obligation, Blueprint `lem:bridge`.**  On the actual
absolute residue tower, additivity of the power map (equivalently Lucas's
theorem) forces every nonzero exponent to be a power of the residue
characteristic.  Stabilizer membership and the `Fbar_p` residue facts are
explicit, excluding the false arbitrary-ambient generalization. -/
private theorem actsAsPowerOnResidue_exponent_primePower
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega] [Group G]
    [MulSemiringAction G Omega]
    (P : AmbientAbsolutePlace K Omega)
    (tower : AmbientAlgebraicResidueTower P)
    (g : G)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (N : ℕ)
    (hpower : ActsAsPowerOnResidue P.1 g N) :
    ∃ a : ℕ, N =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^ a := by
  let p := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P)
  let F := IsLocalRing.ResidueField P.1
  letI : IsAlgClosed F := tower.residue_isAlgClosed
  letI : CharP F p := tower.residue_charP
  letI : Fact p.Prime := ⟨residueCharacteristic_prime (ambientFinitePlace P)⟩
  exact additive_power_exponent_eq_primePower p N
    (actsAsPowerOnResidue_ne_zero P.1 g N hpower)
    (actsAsPowerOnResidue_additive P.1 g N hg hpower)

/-- Injectivity of `zhat → Aut(Fbar_p)` in the finite-subfield form needed
by Blueprint `lem:bridge`: equality on every `F_{p^n}` determines the
Frobenius exponent. -/
private def ResidueFrobeniusInjectivity : Prop :=
  ∀ (p : Nat.Primes) (a b : ℕ),
    (∀ n : ℕ, 0 < n →
      Nat.ModEq ((p : ℕ) ^ n - 1) ((p : ℕ) ^ a) ((p : ℕ) ^ b)) →
    a = b

/-- **Arithmetic micro-obligation, Blueprint `lem:bridge`.**  The map
`zhat → Aut(Fbar_p)` is injective. -/
private theorem residueFrobenius_injective :
    ResidueFrobeniusInjectivity := by
  intro p a b h
  let n := max a b + 2
  have hn : 0 < n := by simp [n]
  have hp : 2 ≤ (p : ℕ) := p.2.two_le
  have haexp : a + 2 ≤ n := by simp [n]
  have hbexp : b + 2 ≤ n := by simp [n]
  have hapa : (p : ℕ) ^ (a + 2) ≤ (p : ℕ) ^ n :=
    Nat.pow_le_pow_right p.2.pos haexp
  have hbpb : (p : ℕ) ^ (b + 2) ≤ (p : ℕ) ^ n :=
    Nat.pow_le_pow_right p.2.pos hbexp
  have ha : (p : ℕ) ^ a < (p : ℕ) ^ n - 1 := by
    rw [pow_add, pow_two] at hapa
    have hpp : 4 ≤ (p : ℕ) * (p : ℕ) := by nlinarith
    have hfour : (p : ℕ) ^ a * 4 ≤
        (p : ℕ) ^ a * ((p : ℕ) * (p : ℕ)) :=
      Nat.mul_le_mul_left _ hpp
    have hpos : 0 < (p : ℕ) ^ a := pow_pos p.2.pos _
    have hgap : (p : ℕ) ^ a + 2 ≤ (p : ℕ) ^ a * 4 := by omega
    omega
  have hb : (p : ℕ) ^ b < (p : ℕ) ^ n - 1 := by
    rw [pow_add, pow_two] at hbpb
    have hpp : 4 ≤ (p : ℕ) * (p : ℕ) := by nlinarith
    have hfour : (p : ℕ) ^ b * 4 ≤
        (p : ℕ) ^ b * ((p : ℕ) * (p : ℕ)) :=
      Nat.mul_le_mul_left _ hpp
    have hpos : 0 < (p : ℕ) ^ b := pow_pos p.2.pos _
    have hgap : (p : ℕ) ^ b + 2 ≤ (p : ℕ) ^ b * 4 := by omega
    omega
  have heq : (p : ℕ) ^ a = (p : ℕ) ^ b := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      using h n hn
  exact Nat.pow_right_injective hp heq

/-- A chosen `zhat` coordinate on the unramified quotient, together with the
two residue-action equations needed by Blueprint `lem:bridge`. -/
private structure AmbientResidueCoordinateData
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega) where
  residueTower : AmbientAlgebraicResidueTower P
  coordinate : G → ProfiniteIntegers
  norm_eq_prime_pow :
    ambientResidueNorm P =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
        ambientResidueDegree P
  power_coordinate : ∀ (g : G),
    g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 →
      ∀ a : ℕ,
        ActsAsPowerOnResidue P.1 g
            (NU.LocalTheory.residueCharacteristic
              (ambientFinitePlace P) ^ a) →
          profiniteIntegerOfNat (ambientResidueDegree P) * coordinate g =
            profiniteIntegerOfNat a
  coordinate_power : ∀ (g : G),
    g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1 →
      ∀ j : ℕ, coordinate g = profiniteIntegerOfNat j →
        ActsAsPowerOnResidue P.1 g (ambientResidueNorm P ^ j)

/-- Remaining profinite branch of residue classification, after the
algebraic-closure, characteristic, and norm identities have been proved. -/
private theorem ambientResidueCoordinate_profiniteClassification
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (tower : AmbientAlgebraicResidueTower P)
    (hnorm : ambientResidueNorm P =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
        ambientResidueDegree P)
    (_hinjective : ResidueFrobeniusInjectivity) :
    Nonempty (AmbientResidueCoordinateData R P) := by
  have hspec := ambientResidueCoordinateCandidate_spec R P tower hnorm
  exact ⟨{
    residueTower := tower
    coordinate := ambientResidueCoordinateCandidate P
    norm_eq_prime_pow := hnorm
    power_coordinate := hspec.1
    coordinate_power := hspec.2 }⟩

/-- Resistant branch of T5 residue compatibility: classify the automorphism
of the algebraic residue field by its compatible finite-level Frobenius
exponents and package the resulting `zhat` coordinate. -/
private theorem ambientResidueCoordinate_frobeniusClassification
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (hinjective : ResidueFrobeniusInjectivity) :
    Nonempty (AmbientResidueCoordinateData R P) := by
  exact ambientResidueCoordinate_profiniteClassification R P
    (ambientAlgebraicResidueTowerData R P)
    (ambientResidueNorm_eq_residueCharacteristic_pow P) hinjective

/-- **T5/residue compatibility obligation, Blueprint T5 + `lem:bridge`.**
Construct the unramified `zhat` coordinate and compare its Frobenius action
with the actual ambient residue action.  The injectivity input is explicit. -/
private theorem ambientResidueCoordinateData_exists
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (hinjective : ResidueFrobeniusInjectivity) :
    Nonempty (AmbientResidueCoordinateData R P) := by
  exact ambientResidueCoordinate_frobeniusClassification
    R P hinjective

/-- Blueprint `lem:bridge`: characterize `ActsAsPowerOnResidue` by a natural
`zhat` coordinate.  The proof uses, in order, `N ≠ 0`, the `p`-power
classification, injectivity of Frobenius, and
`f zhat ∩ Z = f Z`. -/
private theorem actsAsPowerOnResidue_iff_coordinate_nat
    {K Omega G : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    [Group G] [TopologicalSpace G] [MulSemiringAction G Omega]
    (R : AbsoluteGaloisActionRealization K Omega G)
    (P : AmbientAbsolutePlace K Omega)
    (D : AmbientResidueCoordinateData R P)
    (g : G)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G) P.1)
    (N : ℕ) :
    ActsAsPowerOnResidue P.1 g N ↔
      ∃ j : ℕ, N = ambientResidueNorm P ^ j ∧
        D.coordinate g = profiniteIntegerOfNat j := by
  constructor
  · intro hpower
    have _hN : N ≠ 0 := actsAsPowerOnResidue_ne_zero P.1 g N hpower
    obtain ⟨a, ha⟩ :=
      actsAsPowerOnResidue_exponent_primePower P D.residueTower
        g hg N hpower
    have hcoord := D.power_coordinate g hg a (ha ▸ hpower)
    have hdvd : ambientResidueDegree P ∣ a :=
      profiniteInteger_nat_dvd_of_eq_mul a (ambientResidueDegree P)
        (D.coordinate g) hcoord.symm
    obtain ⟨j, haj⟩ := hdvd
    have hf : ambientResidueDegree P ≠ 0 := by
      let v := ambientFinitePlace P
      let p := ambientRationalPrime P
      letI : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
      exact (Ideal.inertiaDeg'_pos p.asIdeal v.asIdeal).ne'
    have hcoordinate : D.coordinate g = profiniteIntegerOfNat j := by
      apply profiniteIntegerOfNat_mul_injective hf
      calc
        profiniteIntegerOfNat (ambientResidueDegree P) * D.coordinate g =
            profiniteIntegerOfNat a := hcoord
        _ = profiniteIntegerOfNat (ambientResidueDegree P * j) := by
          rw [haj]
        _ = profiniteIntegerOfNat (ambientResidueDegree P) *
            profiniteIntegerOfNat j :=
          profiniteIntegerOfNat_mul _ _
    refine ⟨j, ?_, hcoordinate⟩
    calc
      N = NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^ a := ha
      _ = NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
          (ambientResidueDegree P * j) := by rw [haj]
      _ = (NU.LocalTheory.residueCharacteristic (ambientFinitePlace P) ^
          ambientResidueDegree P) ^ j := by rw [pow_mul]
      _ = ambientResidueNorm P ^ j := by rw [D.norm_eq_prime_pow]
  · rintro ⟨j, rfl, hcoordinate⟩
    exact D.coordinate_power g hg j hcoordinate

/-- Local classification data before the final `prop:q` assembly.  It
identifies both inertia quotients with `zhat`; `cyclotomic_rigidity` records
the one-modulus-at-a-time consequence of `lem:order`. -/
private structure AmbientUnramifiedLocalData
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega) where
  source : AmbientResidueCoordinateData R₁ P₁
  target : AmbientResidueCoordinateData R₂ P₂
  orientation : ProfiniteIntegersˣ
  coordinate_transport : ∀ (g : G₁),
    g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      target.coordinate (theta g) =
        (orientation : ProfiniteIntegers) * source.coordinate g
  cyclotomic_rigidity :
    (∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g) →
      profiniteIntegerOfNat (ambientResidueDegree P₁) =
        profiniteIntegerOfNat (ambientResidueDegree P₂) *
          (orientation : ProfiniteIntegers)

/-- Transport data on the two unramified quotients.  `orientation` is the
unit `u` with `Frob₁ ↦ Frob₂^u`; the last field is the relation
`f = f' u` obtained from cyclotomic characters and Blueprint `lem:order`. -/
private structure AmbientUnramifiedTransportData
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega) where
  source : AmbientResidueCoordinateData R₁ P₁
  target : AmbientResidueCoordinateData R₂ P₂
  orientation : ProfiniteIntegersˣ
  coordinate_transport : ∀ (g : G₁),
    g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      target.coordinate (theta g) =
        (orientation : ProfiniteIntegers) * source.coordinate g
  residueDegree_relation :
    profiniteIntegerOfNat (ambientResidueDegree P₁) =
      profiniteIntegerOfNat (ambientResidueDegree P₂) *
        (orientation : ProfiniteIntegers)

/-- Resistant local-field branch: compact Frobenius lifts and pointwise
cyclotomic transport identify the normalized natural coordinates.  The
resulting orientation is the unit `1`; its residue-degree relation is the
finite-residue divisibility calculation in
`ambientResidueDegree_preserved_from_chi`. -/
private theorem ambientUnramifiedLocalData_exists
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g)
    (_hinertia : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      (ActsAsPowerOnResidue P₁.1 g 1 ↔
        ActsAsPowerOnResidue P₂.1 (theta g) 1)) :
    Nonempty (AmbientUnramifiedLocalData R₁ R₂ theta P₁ P₂) := by
  classical
  let tower₁ := ambientAlgebraicResidueTowerData R₁ P₁
  let tower₂ := ambientAlgebraicResidueTowerData R₂ P₂
  have hnorm₁ := ambientResidueNorm_eq_residueCharacteristic_pow P₁
  have hnorm₂ := ambientResidueNorm_eq_residueCharacteristic_pow P₂
  have hspec₁ := ambientResidueCoordinateCandidate_spec
    R₁ P₁ tower₁ hnorm₁
  have hspec₂ := ambientResidueCoordinateCandidate_spec
    R₂ P₂ tower₂ hnorm₂
  let C₁ : AmbientResidueCoordinateData R₁ P₁ :=
    { residueTower := tower₁
      coordinate := ambientResidueCoordinateCandidate P₁
      norm_eq_prime_pow := hnorm₁
      power_coordinate := hspec₁.1
      coordinate_power := hspec₁.2 }
  let C₂ : AmbientResidueCoordinateData R₂ P₂ :=
    { residueTower := tower₂
      coordinate := ambientResidueCoordinateCandidate P₂
      norm_eq_prime_pow := hnorm₂
      power_coordinate := hspec₂.1
      coordinate_power := hspec₂.2 }
  have hf : ambientResidueDegree P₁ = ambientResidueDegree P₂ :=
    ambientResidueDegree_preserved_from_chi
      R₁ R₂ theta P₁ P₂ hmap hchi
  have hfne : ambientResidueDegree P₁ ≠ 0 := by
    let v := ambientFinitePlace P₁
    let p := ambientRationalPrime P₁
    letI : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
    exact (Ideal.inertiaDeg'_pos p.asIdeal v.asIdeal).ne'
  have htheta (g : G₁)
      (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup
        (G := G₁) P₁.1) :
      theta g ∈ NU.LocalTheory.ambientDecompositionGroup
        (G := G₂) P₂.1 := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  have hcoordinate (g : G₁)
      (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup
        (G := G₁) P₁.1) :
      C₂.coordinate (theta g) = C₁.coordinate g := by
    let p₁ := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁)
    let p₂ := NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂)
    by_cases he₁ : ∃ a : ℕ,
        ActsAsPowerOnResidue P₁.1 g (p₁ ^ a)
    · obtain ⟨a, ha⟩ := he₁
      have ha₂ : ActsAsPowerOnResidue P₂.1 (theta g) (p₂ ^ a) :=
        (ambientPrimePowerAction_preserved_from_chi
          R₁ R₂ theta P₁ P₂ hmap hchi g hg a).mp ha
      apply profiniteIntegerOfNat_mul_injective hfne
      calc
        profiniteIntegerOfNat (ambientResidueDegree P₁) *
            C₂.coordinate (theta g) =
          profiniteIntegerOfNat (ambientResidueDegree P₂) *
            C₂.coordinate (theta g) := by rw [hf]
        _ = profiniteIntegerOfNat a :=
          C₂.power_coordinate (theta g) (htheta g hg) a ha₂
        _ = profiniteIntegerOfNat (ambientResidueDegree P₁) *
            C₁.coordinate g := (C₁.power_coordinate g hg a ha).symm
    · have he₂ : ¬ ∃ a : ℕ,
          ActsAsPowerOnResidue P₂.1 (theta g) (p₂ ^ a) := by
        rintro ⟨a, ha⟩
        exact he₁ ⟨a,
          (ambientPrimePowerAction_preserved_from_chi
            R₁ R₂ theta P₁ P₂ hmap hchi g hg a).mpr ha⟩
      change ambientResidueCoordinateCandidate P₂ (theta g) =
        ambientResidueCoordinateCandidate P₁ g
      dsimp [p₁, p₂] at he₁ he₂
      simp only [ambientResidueCoordinateCandidate,
        dif_neg he₁, dif_neg he₂]
  exact ⟨{
    source := C₁
    target := C₂
    orientation := 1
    coordinate_transport := fun g hg => by
      simpa using hcoordinate g hg
    cyclotomic_rigidity := fun _ => by
      simpa [hf] }⟩

/-- Resistant procyclic branch of `prop:q`: consume the local quotient data
and specialize its cyclotomic rigidity statement to the transported packet
characters. -/
private theorem ambientUnramifiedTransport_from_localData
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g)
    (hinertia : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      (ActsAsPowerOnResidue P₁.1 g 1 ↔
        ActsAsPowerOnResidue P₂.1 (theta g) 1)) :
    Nonempty
      (AmbientUnramifiedTransportData R₁ R₂ theta P₁ P₂) := by
  obtain ⟨D⟩ := ambientUnramifiedLocalData_exists
    R₁ R₂ theta P₁ P₂ hmap hchi hinertia
  exact ⟨{
    source := D.source
    target := D.target
    orientation := D.orientation
    coordinate_transport := D.coordinate_transport
    residueDegree_relation := D.cyclotomic_rigidity hchi }⟩

/-- **Arithmetic/procyclic obligation, Blueprint `prop:q`.**  After
`cor:chi` and `prop:inertia`, identify both unramified quotients with
`zhat`, obtain the orientation unit `u`, and use `lem:order` one modulus at a
time to prove the displayed relation `f = f' u`. -/
private theorem ambientUnramifiedTransport_exists
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (hchi : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
        ambientCyclotomicScalar R₂ ell (theta g) =
          ambientCyclotomicScalar R₁ ell g)
    (hinertia : ∀ (g : G₁),
      g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      (ActsAsPowerOnResidue P₁.1 g 1 ↔
        ActsAsPowerOnResidue P₂.1 (theta g) 1)) :
    Nonempty
      (AmbientUnramifiedTransportData R₁ R₂ theta P₁ P₂) := by
  exact ambientUnramifiedTransport_from_localData
    R₁ R₂ theta P₁ P₂ hmap hchi hinertia

/-- The intrinsic character comparison attached to two corresponding
ambient decomposition groups.  The linear character equivalences come
straight from the restricted profinite isomorphism; the marked cyclotomic
and unramified coordinates are supplied by the packet determinant and
orientation chains. -/
private structure AmbientIntrinsicCharacterData
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega) where
  decompositionEquiv :
    NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 ≃ₜ*
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1
  characterEquiv : ∀ n : ℕ,
    NU.LocalTheory.ContinuousCharacter
        (NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) n ≃ₗ[ZMod n]
      NU.LocalTheory.ContinuousCharacter
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) n
  cyclotomic_preserved : ∀ (g : G₁),
    g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
      ∀ ell : NU.LocalTheory.OddPrime,
        NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ≠
            (ell : ℕ) →
          ambientCyclotomicScalar R₂ ell (theta g) =
            ambientCyclotomicScalar R₁ ell g
  unramified : AmbientUnramifiedTransportData R₁ R₂ theta P₁ P₂

/-- Certified intrinsic character identification: packet determinants give
pointwise cyclotomic compatibility, the cyclotomic kernel description gives
inertia compatibility, and the procyclic branch supplies orientation. -/
private theorem ambientIntrinsicCharacterData_exists
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    Nonempty (AmbientIntrinsicCharacterData R₁ R₂ theta P₁ P₂) := by
  let eD := PacketTransport.subgroupMapEquiv theta
    (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) hmap
  have hchi (g : G₁)
      (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
      (ell : NU.LocalTheory.OddPrime)
      (haway : NU.LocalTheory.residueCharacteristic
        (ambientFinitePlace P₁) ≠ (ell : ℕ)) :=
    ambientPointwiseCyclotomic_preserved
      R₁ R₂ theta P₁ P₂ hmap g hg ell haway
  have hinertia (g : G₁)
      (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) :=
    ambientInertia_preserved_from_chi
      R₁ R₂ theta P₁ P₂ hmap hchi g hg
  obtain ⟨D⟩ := ambientUnramifiedTransport_exists
    R₁ R₂ theta P₁ P₂ hmap hchi hinertia
  exact ⟨{
    decompositionEquiv := eD
    characterEquiv := fun n =>
      PacketTransport.pullCharacterLinearEquiv n eD
    cyclotomic_preserved := hchi
    unramified := D }⟩

/-- Corresponding decomposition groups have identical intrinsic finite
character dimensions.  The comparison is the literal pullback along the
restricted profinite isomorphism packaged with the packet/orientation data. -/
private theorem ambientDecomposition_character_finrank_eq
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (n : ℕ) [Fact n.Prime] :
    Module.finrank (ZMod n)
        (NU.LocalTheory.ContinuousCharacter
          (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) n) =
      Module.finrank (ZMod n)
        (NU.LocalTheory.ContinuousCharacter
          (NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) n) := by
  let eD := PacketTransport.subgroupMapEquiv theta
    (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) hmap
  exact (PacketTransport.pullCharacterLinearEquiv n eD).finrank_eq.symm

/-- Positivity of the absolute residue degree. -/
private theorem ambientResidueDegree_pos
    {K Omega : Type*} [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega]
    (P : AmbientAbsolutePlace K Omega) :
    0 < ambientResidueDegree P := by
  let v := ambientFinitePlace P
  let p := ambientRationalPrime P
  letI : v.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  exact Ideal.inertiaDeg'_pos p.asIdeal v.asIdeal

/-- Blueprint `prop:q`, formal `zhat`-linear conclusion.  Given the
unramified transport data, it proves `f = f'`, `q = q'`, `u = 1`, and equality
of every transported `zhat` coordinate. -/
private theorem ambientResidueNorm_orientation_from_transport
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hchar : NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) =
      NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂))
    (D : AmbientUnramifiedTransportData R₁ R₂ theta P₁ P₂) :
    ambientResidueDegree P₁ = ambientResidueDegree P₂ ∧
      ambientResidueNorm P₁ = ambientResidueNorm P₂ ∧
      D.orientation = 1 ∧
      ∀ (g : G₁),
        g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1 →
          D.target.coordinate (theta g) = D.source.coordinate g := by
  have hrigid := profinite_relation_rigid
    (ambientResidueDegree_pos P₁).ne'
    (ambientResidueDegree_pos P₂).ne'
    D.orientation D.residueDegree_relation
  refine ⟨hrigid.1, ?_, hrigid.2, ?_⟩
  · calc
      ambientResidueNorm P₁ =
          NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₁) ^
            ambientResidueDegree P₁ := D.source.norm_eq_prime_pow
      _ = NU.LocalTheory.residueCharacteristic (ambientFinitePlace P₂) ^
            ambientResidueDegree P₂ := by rw [hchar, hrigid.1]
      _ = ambientResidueNorm P₂ := D.target.norm_eq_prime_pow.symm
  · intro g hg
    rw [D.coordinate_transport g hg, hrigid.2]
    simp

/-- Formal assembly of the residue-norm rung from `cor:chi`,
`prop:inertia`, and `prop:q`. -/
private theorem ambientResidueNorm_assembly
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientResidueNorm P₁ = ambientResidueNorm P₂ := by
  obtain ⟨D⟩ := ambientIntrinsicCharacterData_exists
    R₁ R₂ theta P₁ P₂ hmap
  exact (ambientResidueNorm_orientation_from_transport
    R₁ R₂ theta P₁ P₂
      (ambientResidueCharacteristic_preserved R₁ R₂ theta P₁ P₂ hmap)
      D.unramified).2.1

/-- Formal cancellation step `e f = e' f`, `f > 0` in the L3 assembly. -/
private theorem ramificationIndex_eq_of_localDegree_residueDegree
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hn : ambientLocalDegree P₁ = ambientLocalDegree P₂)
    (hf : ambientResidueDegree P₁ = ambientResidueDegree P₂) :
    ambientRamificationIndex P₁ = ambientRamificationIndex P₂ := by
  unfold ambientLocalDegree at hn
  rw [hf] at hn
  exact Nat.eq_of_mul_eq_mul_right (ambientResidueDegree_pos P₂) hn

/-- Formal L3 ramification-index assembly from Blueprint `prop:p-n` and
`prop:q`. -/
private theorem ambientRamificationIndex_assembly
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientRamificationIndex P₁ = ambientRamificationIndex P₂ := by
  obtain ⟨D⟩ := ambientIntrinsicCharacterData_exists
    R₁ R₂ theta P₁ P₂ hmap
  have hq := ambientResidueNorm_orientation_from_transport
    R₁ R₂ theta P₁ P₂
      (ambientResidueCharacteristic_preserved R₁ R₂ theta P₁ P₂ hmap)
      D.unramified
  exact ramificationIndex_eq_of_localDegree_residueDegree P₁ P₂
    (ambientLocalDegree_preserved_from_dimensions
      R₁ R₂ theta P₁ P₂ hmap) hq.1

/-- Formal L4 assembly from Blueprint `lem:bridge` on both sides and
`prop:q` (`q = q'`, `u = 1`). -/
private theorem residuePowerAction_assembly
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (N : ℕ) :
    ActsAsPowerOnResidue P₁.1 g N ↔
      ActsAsPowerOnResidue P₂.1 (theta g) N := by
  obtain ⟨D⟩ := ambientIntrinsicCharacterData_exists
    R₁ R₂ theta P₁ P₂ hmap
  have htheta : theta g ∈
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1 := by
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  have hq := ambientResidueNorm_orientation_from_transport
    R₁ R₂ theta P₁ P₂
      (ambientResidueCharacteristic_preserved R₁ R₂ theta P₁ P₂ hmap)
      D.unramified
  rw [actsAsPowerOnResidue_iff_coordinate_nat
      R₁ P₁ D.unramified.source g hg N,
    actsAsPowerOnResidue_iff_coordinate_nat
      R₂ P₂ D.unramified.target (theta g) htheta N]
  constructor
  · rintro ⟨j, hN, hcoordinate⟩
    refine ⟨j, ?_, ?_⟩
    · simpa [hq.2.1] using hN
    · exact (hq.2.2.2 g hg).trans hcoordinate
  · rintro ⟨j, hN, hcoordinate⟩
    refine ⟨j, ?_, ?_⟩
    · simpa [hq.2.1] using hN
    · exact (hq.2.2.2 g hg).symm.trans hcoordinate

/-- **Hard rung: residue-field cardinality.**  The common-ambient
isomorphism preserves `|k_v|`.

Intended proof: at every auxiliary odd `ell` different from the recovered
residue characteristic, use the actual packet plane and its stabilizer at a
cofinal finite witness level.  On the tame inertia line, conjugation by an
unramified generator is multiplication by `|k_v|` modulo `ell`.  Transport of
`barePacketAction`, followed by variation of `ell` (and sufficiently deep
finite witnesses), identifies the positive integer `|k_v|`.  This is the
missing tame/unramified action calculation; it is not an appeal to an
unstructured profinite invariant. -/
theorem ambientResidueNorm_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientResidueNorm P₁ = ambientResidueNorm P₂ := by
  exact ambientResidueNorm_assembly R₁ R₂ theta P₁ P₂ hmap

/-- Residue-degree preservation is formal once the rational prime and residue
norm have been recovered. -/
theorem ambientResidueDegree_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientResidueDegree P₁ = ambientResidueDegree P₂ := by
  let q₁ := ambientRationalPrime P₁
  let q₂ := ambientRationalPrime P₂
  have hq : q₁ = q₂ := ambientRationalPrime_preserved
    R₁ R₂ theta P₁ P₂ hmap
  apply Nat.pow_right_injective
    (show 2 ≤ NU.Chebotarev.PrimeIdeal.norm q₁ by
      have h := NumberField.HeightOneSpectrum.one_lt_absNorm q₁
      change 1 < NU.Chebotarev.PrimeIdeal.norm q₁ at h
      omega)
  calc
    NU.Chebotarev.PrimeIdeal.norm q₁ ^ ambientResidueDegree P₁ =
        ambientResidueNorm P₁ := (ambientResidueNorm_eq_pow P₁).symm
    _ = ambientResidueNorm P₂ :=
      ambientResidueNorm_preserved R₁ R₂ theta P₁ P₂ hmap
    _ = NU.Chebotarev.PrimeIdeal.norm q₂ ^ ambientResidueDegree P₂ :=
      ambientResidueNorm_eq_pow P₂
    _ = NU.Chebotarev.PrimeIdeal.norm q₁ ^ ambientResidueDegree P₂ := by
      rw [hq]

/-- **Hard rung: inertia, wild inertia, and ramification index.**  The
absolute ramification index is preserved.

Intended proof: use the same cofinal packet witnesses to recover the inertia
kernel of the unramified procyclic quotient.  The already recovered residue
prime singles out wild inertia as the maximal normal pro-`p` part; the tame
cyclic quotient gives the prime-to-`p` part.  Comparing the finite inertia
images with the valuation-theoretic inertia groups, and then their indices,
recovers the full ramification index (including its wild factor). -/
theorem ambientRamificationIndex_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientRamificationIndex P₁ = ambientRamificationIndex P₂ := by
  exact ambientRamificationIndex_assembly R₁ R₂ theta P₁ P₂ hmap

/-- **Hard rung: inertia/wild-inertia recovery and residue action.**  After
transporting corresponding decomposition groups, the exact power by which an
element acts on residue classes is preserved.

Intended proof: the case `n = 1` first identifies inertia as the kernel of
the recovered unramified quotient.  The packet profile identifies the residue
prime; finite witness quotients then isolate wild inertia and the tame inertia
line.  The conjugation action on that line recovers the residue action, while
the compatible unramified cyclic quotients fix its orientation.  The final
normalization is the local-reciprocity convention uniformizer `↦` arithmetic
Frobenius.  No LCFT theorem is used in the present skeleton proof term: this
single rung is where a proved normalization bridge must eventually be
inserted. -/
theorem residuePowerAction_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1)
    (n : ℕ) :
    ActsAsPowerOnResidue P₁.1 g n ↔
      ActsAsPowerOnResidue P₂.1 (theta g) n := by
  exact residuePowerAction_assembly R₁ R₂ theta P₁ P₂ hmap g hg n

/-- Inertia-element preservation is the `n = 1` specialization of the
recovered residue action. -/
theorem ambientInertiaElement_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) :
    ActsAsPowerOnResidue P₁.1 g 1 ↔
      ActsAsPowerOnResidue P₂.1 (theta g) 1 :=
  residuePowerAction_preserved R₁ R₂ theta P₁ P₂ hmap g hg 1

/-- Arithmetic-Frobenius power preservation: combine exact residue-action
transport with the recovered equality of residue-field cardinalities. -/
theorem arithmeticFrobeniusPower_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1)
    (g : G₁)
    (hg : g ∈ NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) :
    ActsAsPowerOnResidue P₁.1 g (ambientResidueNorm P₁) ↔
      ActsAsPowerOnResidue P₂.1 (theta g) (ambientResidueNorm P₂) := by
  rw [ambientResidueNorm_preserved R₁ R₂ theta P₁ P₂ hmap]
  exact residuePowerAction_preserved R₁ R₂ theta P₁ P₂ hmap g hg _

/-- The complete invariant package required by interface (L3).  Its rational
prime component and the reduction from residue norm to residue degree are
proved; only the two explicitly named local-anabelian rungs above remain. -/
theorem ambientInvariants_preserved
    (R₁ : AbsoluteGaloisActionRealization K₁ Omega G₁)
    (R₂ : AbsoluteGaloisActionRealization K₂ Omega G₂)
    (theta : G₁ ≃ₜ* G₂)
    (P₁ : AmbientAbsolutePlace K₁ Omega)
    (P₂ : AmbientAbsolutePlace K₂ Omega)
    (hmap : Subgroup.map theta.toMulEquiv.toMonoidHom
        (NU.LocalTheory.ambientDecompositionGroup (G := G₁) P₁.1) =
      NU.LocalTheory.ambientDecompositionGroup (G := G₂) P₂.1) :
    ambientRationalPrime P₁ = ambientRationalPrime P₂ ∧
      ambientRamificationIndex P₁ = ambientRamificationIndex P₂ ∧
      ambientResidueDegree P₁ = ambientResidueDegree P₂ := by
  exact ⟨ambientRationalPrime_preserved R₁ R₂ theta P₁ P₂ hmap,
    ambientRamificationIndex_preserved R₁ R₂ theta P₁ P₂ hmap,
    ambientResidueDegree_preserved R₁ R₂ theta P₁ P₂ hmap⟩

end AmbientCorrespondence

end

end NU.NeukirchUchida.LocalInvariants
