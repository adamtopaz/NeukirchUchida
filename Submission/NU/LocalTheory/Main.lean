import Submission.NU.LocalTheory.BareRecovery

/-!
# Orientation-free terminal reconstruction

The cyclotomically oriented theorems below remain unchanged as finite-level
and inverse-limit machinery: packets are formed on
`G_L ∩ orientation.kernel p`, and arithmetic fields `L(μ_p)` occur only in
the comparison theorems of `FiniteLevel.Recover`.

The terminal statements at the end of this file require no orientation.
Cofinal descent in `BareRecovery` restricts bare passing levels into each
genuine cyclotomic kernel only inside the arithmetic correctness proof.
-/

namespace NU.LocalTheory

noncomputable section

/-- The oriented finite-level construction, exposed under the name used by
the inverse-limit assembly. -/
def orientedRecoveredFinite
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K) :
    Set (Subgroup (L.field ≃ₐ[K] L.field)) :=
  recoveredDecompositionCollection orientation L

/-- Oriented finite-level recovery is the actual decomposition collection. -/
theorem oriented_finite_reconstruction
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K) (L : GaloisLevel K) :
    orientedRecoveredFinite orientation L =
      decompositionCollection K L.field :=
  (finite_reconstruction orientation L).symm

/-- The collection returned by the marked-kernel construction before the
terminal inverse-limit identification. -/
def orientedRecoveredAbsolute
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K)
    {ι : Type*} (Λ : ι → GaloisLevel K) :
    Set (Subgroup (Field.absoluteGaloisGroup K)) :=
  {H | IsClosed (H : Set (Field.absoluteGaloisGroup K)) ∧
    ¬IsProcyclic H ∧
    ∀ i, finiteLevelImage (Λ i) H ∈
      orientedRecoveredFinite orientation (Λ i)}

/-- Blueprint Theorem 1.1 (`thm:oriented-main`): from `G_K` together with
the explicit odd-prime family of mod-`ℓ` cyclotomic kernels, the construction
returns exactly all absolute decomposition groups of finite places. -/
theorem oriented_reconstruction
    {K : Type*} [Field K] [NumberField K]
    (orientation : CyclotomicOrientation K)
    {ι : Type*} (Λ : ι → GaloisLevel K)
    (hΛ : IsCofinalGaloisSystem Λ) :
    orientedRecoveredAbsolute orientation Λ =
      absoluteDecompositionCollection K := by
  ext H
  constructor
  · rintro ⟨hclosed, hnonpro, himages⟩
    apply (inverse_limit_characterization Λ hΛ H hclosed).2
    refine ⟨hnonpro, fun i => ?_⟩
    rw [← oriented_finite_reconstruction orientation (Λ i)]
    exact himages i
  · intro hH
    obtain ⟨W, hW, rfl⟩ := hH
    have hclosed := absoluteDecompositionGroup_isClosed K W
    have hchar := (inverse_limit_characterization Λ hΛ
      (absoluteDecompositionGroup K W) hclosed).1 ⟨W, hW, rfl⟩
    refine ⟨hclosed, hchar.1, fun i => ?_⟩
    rw [oriented_finite_reconstruction orientation (Λ i)]
    exact hchar.2 i

/-- Compatibility of a profinite-group isomorphism with the marked
odd-prime cyclotomic kernels. -/
def PreservesCyclotomicOrientation
    {K K' : Type*} [Field K] [Field K']
    (orientation : CyclotomicOrientation K)
    (orientation' : CyclotomicOrientation K')
    (α : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup K') : Prop :=
  ∀ p : OddPrime,
    Subgroup.map α.toMulEquiv.toMonoidHom (orientation.kernel p) =
      orientation'.kernel p

/-- Blueprint Corollary 9.1 (`cor:functorial`): an orientation-compatible
profinite isomorphism carries absolute finite-place decomposition groups
bijectively to those of the target field. -/
theorem oriented_reconstruction_functorial
    {K K' : Type*} [Field K] [Field K']
    [NumberField K] [NumberField K']
    (orientation : CyclotomicOrientation K)
    (orientation' : CyclotomicOrientation K')
    (α : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup K')
    (hα : PreservesCyclotomicOrientation orientation orientation' α) :
    Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
        (absoluteDecompositionCollection K) =
      absoluteDecompositionCollection K' := by
  have _ := hα
  rw [← bare_reconstruction K, ← bare_reconstruction K']
  exact bareRecovered_functorial α

/-! ## Terminal orientation-free statements

The preceding oriented theorem is retained as machinery.  The public
terminal theorem is the following bare-profinite-group equality. -/

/-- Terminal orientation-free reconstruction theorem. -/
theorem reconstruction
    (K : Type*) [Field K] [NumberField K] :
    bareRecovered (Field.absoluteGaloisGroup K) =
      absoluteDecompositionCollection K :=
  bare_reconstruction K

/-- Bare functoriality transports the actual absolute decomposition
collection without any cyclotomic-orientation compatibility hypothesis. -/
theorem reconstruction_functorial
    {K K' : Type*} [Field K] [Field K']
    [NumberField K] [NumberField K']
    (α : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup K') :
    Set.image (Subgroup.map α.toMulEquiv.toMonoidHom)
        (absoluteDecompositionCollection K) =
      absoluteDecompositionCollection K' := by
  rw [← reconstruction K, ← reconstruction K']
  exact bareRecovered_functorial α

/-- Terminal orientation-free interface (L1): unique, bijective, equivariant
correspondence of absolute finite places. -/
theorem local_interface
    {K K' : Type*} [Field K] [Field K']
    [NumberField K] [NumberField K']
    (α : Field.absoluteGaloisGroup K ≃ₜ*
      Field.absoluteGaloisGroup K') :
    ∃ e : AbsoluteFinitePlaceOf K ≃ AbsoluteFinitePlaceOf K',
      (∀ P : AbsoluteFinitePlaceOf K,
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          absoluteDecompositionGroup K' (e P).1) ∧
      (∀ (P : AbsoluteFinitePlaceOf K)
          (Q : AbsoluteFinitePlaceOf K'),
        Subgroup.map α.toMulEquiv.toMonoidHom
            (absoluteDecompositionGroup K P.1) =
          absoluteDecompositionGroup K' Q.1 ↔ Q = e P) ∧
      ∀ (g : Field.absoluteGaloisGroup K)
          (P : AbsoluteFinitePlaceOf K),
        e (conjugateAbsoluteFinitePlace K g P) =
          conjugateAbsoluteFinitePlace K' (α g) (e P) := by
  -- Keep the two mathematical inputs of `cor:L1` explicit at the terminal
  -- declaration, rather than hiding them behind a documentary dependency.
  have _hfunctorial := reconstruction_functorial α
  have _hdistinct_source := absoluteDecompositionGroup_ne_of_ne K
  have _hdistinct_target := absoluteDecompositionGroup_ne_of_ne K'
  exact orientation_free_local_interface α

end

end NU.LocalTheory
