import Submission.NU.NeukirchUchida.CyclicStep

/-!
# Every finite quotient is induced by conjugation

Blueprint §6.  A regular kernel turns the restriction of the isomorphism
into a semilinear map, cyclic comparison gives a pointwise translate, and a
strict subspace-counting argument upgrades it to one global translate.
-/

open scoped NumberField

namespace NU.NeukirchUchida

noncomputable section

/-- There is an odd prime larger than any prescribed natural number.  The
strict inequality, not merely coprimality, is the input needed by
`lem:subspace-cover`. -/
theorem exists_oddPrime_gt (n : ℕ) :
    ∃ p : NU.LocalTheory.OddPrime, n < (p : ℕ) := by
  obtain ⟨q, hnq, hq⟩ := Nat.exists_infinite_primes (max (n + 1) 3)
  have hn : n < q := by omega
  have hq2 : q ≠ 2 := by omega
  exact ⟨⟨⟨q, hq⟩, hq.odd_of_ne_two hq2⟩, hn⟩

/-- Blueprint Lemma `lem:subspace-cover`: fewer than `p` proper linear
subspaces cannot cover a nonzero finite-dimensional `F_p`-space. -/
theorem subspace_cover
    (p : NU.LocalTheory.OddPrime)
    {V : Type*} [AddCommGroup V] [Module (ZMod (p : ℕ)) V]
    [FiniteDimensional (ZMod (p : ℕ)) V] [Nontrivial V]
    (m : ℕ) (U : Fin m → Submodule (ZMod (p : ℕ)) V)
    (hmp : m < (p : ℕ))
    (hcover : ∀ x : V, ∃ i, x ∈ U i) :
    ∃ i, U i = ⊤ := by
  by_contra h
  push Not at h
  have hcard : (Finset.univ : Finset (Fin m)).card <
      ENat.card (ZMod (p : ℕ)) := by
    rw [Finset.card_univ, Fintype.card_fin,
      ENat.card_eq_coe_fintype_card, ZMod.card]
    exact_mod_cast hmp
  have hproper := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
    (Finset.univ : Finset (Fin m)) U h hcard
  apply hproper.ne
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact Set.mem_iUnion₂.mpr
    ⟨i, Finset.mem_univ i, (show x ∈ (U i : Set V) from hi)⟩

/-- The agreement subspace `U_h = {x | tau(x) = rho(h)(x)}` from blueprint
§6.  Its carrier is the displayed equality, so it cannot be replaced by an
unrelated subspace. -/
def translateAgreementSubspace
    {k V G : Type*} [Semiring k] [AddCommMonoid V] [Module k V]
    [Group G]
    (tau : V →ₗ[k] V) (rho : G →* (V ≃ₗ[k] V)) (h : G) :
    Submodule k V where
  carrier := {x | tau x = rho h x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change tau x = rho h x at hx
    change tau y = rho h y at hy
    change tau (x + y) = rho h (x + y)
    rw [map_add, map_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change tau x = rho h x at hx
    change tau (r • x) = rho h (r • x)
    rw [map_smul, map_smul, hx]

/-- Defining membership equation for `U_h`. -/
@[simp]
theorem mem_translateAgreementSubspace_iff
    {k V G : Type*} [Semiring k] [AddCommMonoid V] [Module k V]
    [Group G]
    (tau : V →ₗ[k] V) (rho : G →* (V ≃ₗ[k] V))
    (h : G) (x : V) :
    x ∈ translateAgreementSubspace tau rho h ↔ tau x = rho h x :=
  Iff.rfl

/-- Embed `Gal(M/N)` into `Gal(M/F)` by restriction of scalars along
`F ≤ N ≤ M`. -/
noncomputable def regularKernelEmbedding
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    (M : GaloisOverfield N) :
    RegularKernelGroup N M →*
      relativeGaloisGroup F M.toExtension.field
        (hFN.trans M.toExtension.le_base) := by
  exact
    { toFun := fun a =>
        ⟨a.restrictScalars ℚ, by
          intro x
          let y : N.field := ⟨x.1, hFN x.2⟩
          change a ⟨x.1, M.toExtension.le_base (hFN x.2)⟩ =
            ⟨x.1, M.toExtension.le_base (hFN x.2)⟩
          exact a.commutes y⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        rfl }

/-- Defining equation for the kernel embedding. -/
@[simp]
theorem regularKernelEmbedding_apply
    (F N : NumberFieldInOmega) (hFN : F.field ≤ N.field)
    (M : GaloisOverfield N) (a : RegularKernelGroup N M) :
    (regularKernelEmbedding F N hFN M a).1 =
      AlgEquiv.restrictScalars ℚ a := by
  rfl

/-- The map `tau = sigma_M|_A` on a common regular kernel.  The equation
below pins it to the actual finite quotient induced by `theta`. -/
noncomputable def regularKernelTransport
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (M : GaloisOverfield N) :
    RegularKernelGroup N M ≃* RegularKernelGroup N M := by
  let E := M.toExtension.field
  let h₁M := h₁.trans M.toExtension.le_base
  let h₂M := h₂.trans M.toExtension.le_base
  let sigmaM := normalLevelQuotientIso theta E h₁M h₂M
  let emb₁ := regularKernelEmbedding F₁ N h₁ M
  let emb₂ := regularKernelEmbedding F₂ N h₂ M
  let forward : RegularKernelGroup N M →* RegularKernelGroup N M :=
    { toFun := fun a =>
        let y := sigmaM (emb₁ a)
        { y.1.toRingEquiv with
          commutes' := fun x => by
            obtain ⟨gamma, hgamma⟩ :=
              finiteQuotientMap_surjective F₁ E h₁M (emb₁ a)
            have hy : y = finiteQuotientMap F₂ E h₂M (theta gamma) := by
              dsimp [y, sigmaM]
              rw [← hgamma]
              exact normalLevelQuotientIso_comp_restriction
                theta E h₁M h₂M gamma
            have hgammaN : finiteQuotientMap F₁ N h₁ gamma = 1 := by
              apply Subtype.ext
              apply AlgEquiv.ext
              intro z
              apply N.field.val.injective
              calc
                N.field.val ((finiteQuotientMap F₁ N h₁ gamma).1 z) =
                    gamma.1 z.1 := finiteQuotientMap_apply F₁ N h₁ gamma z
                _ = gamma.1 (E.field.val
                    ⟨z.1, M.toExtension.le_base z.2⟩) := rfl
                _ = E.field.val
                    ((finiteQuotientMap F₁ E h₁M gamma).1
                      ⟨z.1, M.toExtension.le_base z.2⟩) :=
                    (finiteQuotientMap_apply F₁ E h₁M gamma _).symm
                _ = E.field.val
                    ((emb₁ a).1 ⟨z.1, M.toExtension.le_base z.2⟩) := by
                    rw [hgamma]
                _ = z.1 := by
                    rw [regularKernelEmbedding_apply]
                    exact congrArg E.field.val (a.commutes z)
                _ = N.field.val z := rfl
            have hthetaN :
                finiteQuotientMap F₂ N h₂ (theta gamma) = 1 := by
              have h := normalLevelQuotientIso_comp_restriction
                theta N h₁ h₂ gamma
              rw [hgammaN, map_one] at h
              exact h.symm
            apply E.field.val.injective
            calc
              E.field.val (y.1 (algebraMap N.field E.field x)) =
                  (theta gamma).1 (E.field.val
                    (algebraMap N.field E.field x)) := by
                    rw [hy]
                    exact finiteQuotientMap_apply F₂ E h₂M (theta gamma) _
              _ = (theta gamma).1 x.1 := rfl
              _ = N.field.val ((finiteQuotientMap F₂ N h₂
                    (theta gamma)).1 x) :=
                    (finiteQuotientMap_apply F₂ N h₂
                      (theta gamma) x).symm
              _ = x.1 := by rw [hthetaN]; rfl
              _ = E.field.val (algebraMap N.field E.field x) := rfl }
      map_one' := by
        apply AlgEquiv.ext
        intro x
        change (sigmaM (emb₁ 1)).1 x = x
        rw [map_one, map_one]
        rfl
      map_mul' := by
        intro a b
        apply AlgEquiv.ext
        intro x
        change (sigmaM (emb₁ (a * b))).1 x =
          ((sigmaM (emb₁ a)).1 * (sigmaM (emb₁ b)).1) x
        rw [map_mul, map_mul]
        rfl }
  have hforward (a : RegularKernelGroup N M) :
      emb₂ (forward a) = sigmaM (emb₁ a) := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    dsimp [emb₂]
    rw [regularKernelEmbedding_apply]
    rfl
  have hinj : Function.Injective forward := by
    intro a b hab
    have hemb : emb₂ (forward a) = emb₂ (forward b) := congrArg emb₂ hab
    rw [hforward, hforward] at hemb
    have h₁eq : emb₁ a = emb₁ b := sigmaM.injective hemb
    apply AlgEquiv.ext
    intro x
    have h := congrArg (fun z => z.1 x) h₁eq
    rw [regularKernelEmbedding_apply, regularKernelEmbedding_apply] at h
    exact h
  letI : Finite (RegularKernelGroup N M) :=
    Finite.of_injective (AlgEquiv.restrictScalarsHom ℚ)
      (AlgEquiv.restrictScalarsHom_injective ℚ)
  exact MulEquiv.ofBijective forward
    ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩

/-- Defining restriction equation for `tau`. -/
@[simp]
theorem regularKernelTransport_embedding
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (M : GaloisOverfield N) (a : RegularKernelGroup N M) :
    regularKernelEmbedding F₂ N h₂ M
        (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) =
      normalLevelQuotientIso theta M.toExtension.field
        (h₁.trans M.toExtension.le_base)
        (h₂.trans M.toExtension.le_base)
        (regularKernelEmbedding F₁ N h₁ M a) := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  rw [regularKernelEmbedding_apply]
  unfold regularKernelTransport
  rfl

/-- Blueprint equation `eq:tau-semilinear`: `tau` is semilinear with the
`theta_N` twist; it is not asserted to be `G`-linear. -/
theorem regularKernelTransport_semilinear
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (M : GaloisOverfield N)
    (hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a)
    (g : relativeGaloisGroup F₁ N h₁)
    (a : RegularKernelGroup N M) :
    regularKernelTransport F₁ F₂ N theta h₁ h₂ M
        (regularKernelConjugation N M hcomm g.1 a) =
      regularKernelConjugation N M hcomm
        (normalLevelQuotientIso theta N h₁ h₂ g).1
        (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) := by
  let E := M.toExtension.field
  let h₁M := h₁.trans M.toExtension.le_base
  let h₂M := h₂.trans M.toExtension.le_base
  let sigmaN := normalLevelQuotientIso theta N h₁ h₂
  let sigmaM := normalLevelQuotientIso theta E h₁M h₂M
  obtain ⟨gamma, hgamma⟩ := finiteQuotientMap_surjective F₁ N h₁ g
  let gM₁ := finiteQuotientMap F₁ E h₁M gamma
  let gM₂ := finiteQuotientMap F₂ E h₂M (theta gamma)
  have hgM₁ : AlgEquiv.restrictNormalHom N.field gM₁.1 = g.1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap N.field E.field).injective
    calc
      algebraMap N.field E.field
          ((AlgEquiv.restrictNormalHom N.field gM₁.1) x) =
        gM₁.1 (algebraMap N.field E.field x) :=
          AlgEquiv.restrictNormal_commutes gM₁.1 N.field x
      _ = algebraMap N.field E.field
          ((finiteQuotientMap F₁ N h₁ gamma).1 x) := by
        apply E.field.val.injective
        calc
          E.field.val (gM₁.1 (algebraMap N.field E.field x)) =
              gamma.1 x.1 :=
            finiteQuotientMap_apply F₁ E h₁M gamma _
          _ = N.field.val ((finiteQuotientMap F₁ N h₁ gamma).1 x) :=
            (finiteQuotientMap_apply F₁ N h₁ gamma x).symm
          _ = E.field.val (algebraMap N.field E.field
              ((finiteQuotientMap F₁ N h₁ gamma).1 x)) := rfl
      _ = algebraMap N.field E.field (g.1 x) := by rw [hgamma]
  have hgM₂ : AlgEquiv.restrictNormalHom N.field gM₂.1 = (sigmaN g).1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap N.field E.field).injective
    calc
      algebraMap N.field E.field
          ((AlgEquiv.restrictNormalHom N.field gM₂.1) x) =
        gM₂.1 (algebraMap N.field E.field x) :=
          AlgEquiv.restrictNormal_commutes gM₂.1 N.field x
      _ = algebraMap N.field E.field
          ((finiteQuotientMap F₂ N h₂ (theta gamma)).1 x) := by
        apply E.field.val.injective
        calc
          E.field.val (gM₂.1 (algebraMap N.field E.field x)) =
              (theta gamma).1 x.1 :=
            finiteQuotientMap_apply F₂ E h₂M (theta gamma) _
          _ = N.field.val
              ((finiteQuotientMap F₂ N h₂ (theta gamma)).1 x) :=
            (finiteQuotientMap_apply F₂ N h₂ (theta gamma) x).symm
          _ = E.field.val (algebraMap N.field E.field
              ((finiteQuotientMap F₂ N h₂ (theta gamma)).1 x)) := rfl
      _ = algebraMap N.field E.field ((sigmaN g).1 x) := by
        have h := normalLevelQuotientIso_comp_restriction
          theta N h₁ h₂ gamma
        rw [hgamma] at h
        rw [h]
  have hsigma_g : sigmaM gM₁ = gM₂ :=
    normalLevelQuotientIso_comp_restriction theta E h₁M h₂M gamma
  have hconj₁ : regularKernelEmbedding F₁ N h₁ M
      (regularKernelConjugation N M hcomm g.1 a) =
        gM₁ * regularKernelEmbedding F₁ N h₁ M a * gM₁⁻¹ := by
    apply Subtype.ext
    calc
      _ = (regularKernelConjugation N M hcomm g.1 a).restrictScalars ℚ :=
        regularKernelEmbedding_apply F₁ N h₁ M _
      _ = gM₁.1 * a.restrictScalars ℚ * gM₁.1⁻¹ := by
        apply AlgEquiv.ext
        intro x
        exact regularKernelConjugation_lift N M hcomm g.1
          gM₁.1 hgM₁ a x
      _ = gM₁.1 * (regularKernelEmbedding F₁ N h₁ M a).1 * gM₁.1⁻¹ := by
        rw [regularKernelEmbedding_apply]
      _ = (gM₁ * regularKernelEmbedding F₁ N h₁ M a * gM₁⁻¹).1 := rfl
  have hconj₂ : regularKernelEmbedding F₂ N h₂ M
      (regularKernelConjugation N M hcomm (sigmaN g).1
        (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a)) =
        gM₂ * regularKernelEmbedding F₂ N h₂ M
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) * gM₂⁻¹ := by
    apply Subtype.ext
    calc
      _ = (regularKernelConjugation N M hcomm (sigmaN g).1
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a)).restrictScalars ℚ :=
        regularKernelEmbedding_apply F₂ N h₂ M _
      _ = gM₂.1 * (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a).restrictScalars ℚ *
          gM₂.1⁻¹ := by
        apply AlgEquiv.ext
        intro x
        exact regularKernelConjugation_lift N M hcomm (sigmaN g).1
          gM₂.1 hgM₂ (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) x
      _ = gM₂.1 * (regularKernelEmbedding F₂ N h₂ M
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a)).1 * gM₂.1⁻¹ := by
        rw [regularKernelEmbedding_apply]
      _ = (gM₂ * regularKernelEmbedding F₂ N h₂ M
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) * gM₂⁻¹).1 := rfl
  have hemb : regularKernelEmbedding F₂ N h₂ M
      (regularKernelTransport F₁ F₂ N theta h₁ h₂ M
        (regularKernelConjugation N M hcomm g.1 a)) =
      regularKernelEmbedding F₂ N h₂ M
        (regularKernelConjugation N M hcomm (sigmaN g).1
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a)) := by
    calc
      _ = sigmaM (regularKernelEmbedding F₁ N h₁ M
          (regularKernelConjugation N M hcomm g.1 a)) :=
        regularKernelTransport_embedding F₁ F₂ N theta h₁ h₂ M _
      _ = sigmaM (gM₁ * regularKernelEmbedding F₁ N h₁ M a * gM₁⁻¹) := by
        rw [hconj₁]
      _ = gM₂ * sigmaM (regularKernelEmbedding F₁ N h₁ M a) * gM₂⁻¹ := by
        rw [map_mul, map_mul, map_inv, hsigma_g]
      _ = gM₂ * regularKernelEmbedding F₂ N h₂ M
          (regularKernelTransport F₁ F₂ N theta h₁ h₂ M a) * gM₂⁻¹ := by
        rw [regularKernelTransport_embedding]
      _ = _ := hconj₂.symm
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun z => z.1 x) hemb
  rw [regularKernelEmbedding_apply, regularKernelEmbedding_apply] at hx
  exact hx

/-- Blueprint equation `eq:tau-pointwise-translate`: cyclic comparison makes
`tau(lambda)` a left translate of every nonzero `lambda` (with a translate
that may initially depend on `lambda`). -/
theorem regularKernelTransport_pointwise_translate
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field]
    (p : NU.LocalTheory.OddPrime)
    (M : GaloisOverfield N)
    (hcomm : ∀ a b : RegularKernelGroup N M, a * b = b * a)
    (hExponent : ∀ a : RegularKernelGroup N M, a ^ (p : ℕ) = 1)
    (lambda : RegularKernelGroup N M) (hlambda : lambda ≠ 1) :
    ∃ h : N.field ≃ₐ[ℚ] N.field,
      regularKernelTransport F₁ F₂ N theta h₁ h₂ M lambda =
        regularKernelConjugation N M hcomm h lambda := by
  let E := M.toExtension.field
  letI : IsGalois ℚ E.field := M.isGaloisQ
  let tau := regularKernelTransport F₁ F₂ N theta h₁ h₂ M
  let H₁ : Subgroup (RegularKernelGroup N M) := Subgroup.zpowers lambda
  let K₁E : IntermediateField ℚ E.field :=
    (IntermediateField.fixedField H₁).restrictScalars ℚ
  let L₁field : IntermediateField ℚ Omega := IntermediateField.lift K₁E
  let L₁ : NumberFieldInOmega :=
    { field := L₁field
      finite := by
        letI : Module.Finite ℚ K₁E :=
          FiniteDimensional.left ℚ K₁E E.field
        exact Module.Finite.equiv
          (IntermediateField.liftAlgEquiv K₁E).toLinearEquiv }
  have hNL₁ : N.field ≤ L₁.field := by
    intro x hx
    apply (IntermediateField.mem_lift
      (⟨x, M.toExtension.le_base hx⟩ : E.field)).2
    change (⟨x, M.toExtension.le_base hx⟩ : E.field) ∈
      IntermediateField.fixedField H₁
    rw [IntermediateField.mem_fixedField_iff]
    intro a ha
    exact a.commutes ⟨x, hx⟩
  have hL₁E : L₁.field ≤ E.field := by
    exact IntermediateField.lift_le K₁E
  let K₁ : NumberFieldExtension F₁ :=
    { field := L₁
      le_base := h₁.trans hNL₁ }
  let L₂ := correspondingField theta K₁
  let thetaL := correspondingRestrictedIso theta K₁
  let KE := extensionOfLE F₁ E (h₁.trans M.toExtension.le_base)
  letI : IsGalois ℚ KE.field.field := by
    change IsGalois ℚ E.field
    infer_instance
  have hKE : KE.field = E := by rfl
  have hL₂E : L₂.field ≤ E.field := by
    have hcorrmono := correspondingField_mono theta K₁ KE hL₁E
    have hfixed := (normal_correspondingField_fixed theta KE).2
    rw [hKE] at hfixed
    exact hcorrmono.trans hfixed.symm.le
  let lambda₁ : relativeGaloisGroup L₁ E hL₁E :=
    ⟨lambda.restrictScalars ℚ, by
      intro x
      let xE : E.field := ⟨x.1, hL₁E x.2⟩
      have hxK : xE ∈ K₁E := by
        exact (IntermediateField.mem_lift xE).mp x.2
      have hxfix : xE ∈ IntermediateField.fixedField H₁ := hxK
      exact (IntermediateField.mem_fixedField_iff H₁ xE).mp hxfix
        lambda (Subgroup.mem_zpowers lambda)⟩
  have hgen₁ : Subgroup.zpowers lambda₁ = ⊤ := by
    apply top_unique
    intro g hg
    let gN : RegularKernelGroup N M :=
      { g.1.toRingEquiv with
        commutes' := fun x => by
          let xL : L₁.field := ⟨x.1, hNL₁ x.2⟩
          exact g.2 xL }
    have hgH : gN ∈ H₁ := by
      rw [← IntermediateField.fixingSubgroup_fixedField H₁]
      intro x
      have hxK : (x.1 : E.field) ∈ K₁E := x.2
      let xL : L₁.field :=
        ⟨x.1, (IntermediateField.mem_lift (x.1 : E.field)).mpr hxK⟩
      exact g.2 xL
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgH
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    change ((lambda.restrictScalars ℚ) ^ n) x = g.1 x
    have hpow : (lambda ^ n).restrictScalars ℚ =
        (lambda.restrictScalars ℚ) ^ n := by
      exact map_zpow (AlgEquiv.restrictScalarsHom ℚ) lambda n
    rw [← hpow, hn]
    rfl
  letI : IsCyclic (relativeGaloisGroup L₁ E hL₁E) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨lambda₁, hgen₁⟩
  let sigmaLE := normalLevelQuotientIso thetaL E hL₁E hL₂E
  letI : IsCyclic (relativeGaloisGroup L₂ E hL₂E) :=
    isCyclic_of_surjective sigmaLE.toMonoidHom sigmaLE.surjective
  have hpres : PreservesNormalLevel thetaL E hL₁E hL₂E :=
    normalLevel_fixed thetaL E hL₁E hL₂E
  obtain ⟨alpha, hfield, hiso⟩ := cyclic_quotient_is_conjugation
    L₁ L₂ E thetaL hL₁E hL₂E hpres
  obtain ⟨gamma, hgamma⟩ :=
    finiteQuotientMap_surjective L₁ E hL₁E lambda₁
  let gamma₁ : absoluteGaloisGroup F₁ := absoluteGaloisInclusion K₁ gamma
  have hgamma₁ : finiteQuotientMap F₁ E
      (h₁.trans M.toExtension.le_base) gamma₁ =
        regularKernelEmbedding F₁ N h₁ M lambda := by
    apply Subtype.ext
    have hgval := congrArg Subtype.val hgamma
    change AlgEquiv.restrictNormalHom E.field gamma.1 =
      lambda.restrictScalars ℚ at hgval ⊢
    exact hgval
  have hsigmaOrig := normalLevelQuotientIso_comp_restriction
    theta E (h₁.trans M.toExtension.le_base)
      (h₂.trans M.toExtension.le_base) gamma₁
  rw [hgamma₁] at hsigmaOrig
  have htauEmb := regularKernelTransport_embedding
    F₁ F₂ N theta h₁ h₂ M lambda
  have hsigmaL := normalLevelQuotientIso_comp_restriction
    thetaL E hL₁E hL₂E gamma
  rw [hgamma] at hsigmaL
  have hthetaGamma : (thetaL gamma).1 = theta gamma₁ :=
    correspondingRestrictedIso_apply theta K₁ gamma
  have hsigmaTau : (sigmaLE lambda₁).1 =
      (tau lambda).restrictScalars ℚ := by
    calc
      (sigmaLE lambda₁).1 =
          (finiteQuotientMap L₂ E hL₂E (thetaL gamma)).1 :=
        congrArg Subtype.val hsigmaL
      _ = (finiteQuotientMap F₂ E
          (h₂.trans M.toExtension.le_base) (theta gamma₁)).1 := by
        apply AlgEquiv.ext
        intro x
        apply E.field.val.injective
        calc
          E.field.val ((finiteQuotientMap L₂ E hL₂E
              (thetaL gamma)).1 x) =
              (thetaL gamma).1 (E.field.val x) :=
            finiteQuotientMap_apply L₂ E hL₂E (thetaL gamma) x
          _ = (theta gamma₁).1 (E.field.val x) := by rw [hthetaGamma]
          _ = E.field.val ((finiteQuotientMap F₂ E
              (h₂.trans M.toExtension.le_base) (theta gamma₁)).1 x) :=
            (finiteQuotientMap_apply F₂ E
              (h₂.trans M.toExtension.le_base) (theta gamma₁) x).symm
      _ = (normalLevelQuotientIso theta E
          (h₁.trans M.toExtension.le_base)
          (h₂.trans M.toExtension.le_base)
          (regularKernelEmbedding F₁ N h₁ M lambda)).1 := by
        exact congrArg Subtype.val hsigmaOrig.symm
      _ = (regularKernelEmbedding F₂ N h₂ M (tau lambda)).1 := by
        exact congrArg Subtype.val htauEmb.symm
      _ = (tau lambda).restrictScalars ℚ :=
        regularKernelEmbedding_apply F₂ N h₂ M (tau lambda)
  have hon := congrArg (fun e => e lambda₁) hiso
  have honVal := congrArg Subtype.val hon
  rw [finiteConjugationIso_apply] at honVal
  have hcyclic : (ambientRestriction E alpha)⁻¹ *
      lambda.restrictScalars ℚ * ambientRestriction E alpha =
        (tau lambda).restrictScalars ℚ := by
    calc
      (ambientRestriction E alpha)⁻¹ * lambda.restrictScalars ℚ *
          ambientRestriction E alpha =
          (finiteConjugationIso L₁ L₂ E hL₁E hL₂E alpha hfield
            lambda₁).1 := by rfl
      _ = (sigmaLE lambda₁).1 := by
        exact honVal
      _ = (tau lambda).restrictScalars ℚ := hsigmaTau
  let gtilde : E.field ≃ₐ[ℚ] E.field := ambientRestriction E alpha⁻¹
  let h : N.field ≃ₐ[ℚ] N.field := ambientRestriction N alpha⁻¹
  have hg : AlgEquiv.restrictNormalHom N.field gtilde = h := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap N.field E.field).injective
    calc
      algebraMap N.field E.field
          ((AlgEquiv.restrictNormalHom N.field gtilde) x) =
          gtilde (algebraMap N.field E.field x) :=
        AlgEquiv.restrictNormal_commutes gtilde N.field x
      _ = algebraMap N.field E.field (h x) := by
        apply E.field.val.injective
        calc
          E.field.val (gtilde (algebraMap N.field E.field x)) =
              alpha⁻¹ x.1 := ambientRestriction_apply E alpha⁻¹ _
          _ = N.field.val (h x) :=
            (ambientRestriction_apply N alpha⁻¹ x).symm
          _ = E.field.val (algebraMap N.field E.field (h x)) := rfl
  refine ⟨h, ?_⟩
  apply AlgEquiv.ext
  intro x
  have hreg := regularKernelConjugation_lift N M hcomm h gtilde hg lambda x
  rw [hreg]
  have hgtilde : gtilde = (ambientRestriction E alpha)⁻¹ := by
    dsimp [gtilde]
    rw [← map_inv]
  rw [hgtilde]
  have hinvsymm : ((ambientRestriction E alpha)⁻¹).symm =
      ambientRestriction E alpha := by
    change (ambientRestriction E alpha).symm.symm = _
    exact AlgEquiv.symm_symm _
  rw [hinvsymm]
  have hcyclicX := DFunLike.congr_fun hcyclic x
  exact hcyclicX.symm

/-- Blueprint Proposition `prop:finite-conjugacy`: on every common finite
normal level the quotient isomorphism is conjugation by one element of
`Gal(N/ℚ)`. -/
theorem finiteLevel_conjugacy
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field] :
    ∃ hN : N.field ≃ₐ[ℚ] N.field,
      ∀ g : relativeGaloisGroup F₁ N h₁,
        (normalLevelQuotientIso theta N h₁ h₂ g).1 =
          hN * g.1 * hN⁻¹ := by
  obtain ⟨p, hp⟩ :=
    exists_oddPrime_gt (Fintype.card (N.field ≃ₐ[ℚ] N.field))
  obtain ⟨M, hcomm, hdata⟩ := exists_regularKernelExtension N p
  letI : CommGroup (RegularKernelGroup N M) :=
    regularKernelCommGroup N M hcomm
  obtain ⟨hExponent, moduleA, hmodule⟩ := hdata
  letI : Module (ZMod (p : ℕ))
      (Additive (RegularKernelGroup N M)) := moduleA
  obtain ⟨hscalar, e, he, hcard⟩ := hmodule
  let tauMul : RegularKernelGroup N M ≃* RegularKernelGroup N M :=
    regularKernelTransport F₁ F₂ N theta h₁ h₂ M
  let tauAdd : Additive (RegularKernelGroup N M) ≃+
      Additive (RegularKernelGroup N M) := MulEquiv.toAdditive tauMul
  have htau_smul (r : ZMod (p : ℕ))
      (x : Additive (RegularKernelGroup N M)) :
      tauAdd (r • x) = r • tauAdd x := by
    apply Additive.toMul.injective
    change tauMul (Additive.toMul (r • x)) =
      Additive.toMul (r • Additive.ofMul (tauMul (Additive.toMul x)))
    calc
      tauMul (Additive.toMul (r • x)) =
          tauMul ((Additive.toMul x) ^ r.val) := by
            congr 1
            simpa using hscalar (Additive.toMul x) r
      _ = (tauMul (Additive.toMul x)) ^ r.val := map_pow tauMul _ _
      _ = Additive.toMul
          (r • Additive.ofMul (tauMul (Additive.toMul x))) :=
        (hscalar (tauMul (Additive.toMul x)) r).symm
  let tau : Additive (RegularKernelGroup N M) ≃ₗ[ZMod (p : ℕ)]
      Additive (RegularKernelGroup N M) :=
    { tauAdd with map_smul' := htau_smul }
  let tauV :
      MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field) ≃ₗ[ZMod (p : ℕ)]
        MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field) :=
    e.symm.trans (tau.trans e)
  let left (h : N.field ≃ₐ[ℚ] N.field) :
      MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field) →ₗ[ZMod (p : ℕ)]
        MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field) :=
    LinearMap.mulLeft (ZMod (p : ℕ)) (MonoidAlgebra.single h 1)
  have hpoint (x : MonoidAlgebra (ZMod (p : ℕ))
      (N.field ≃ₐ[ℚ] N.field)) (hx : x ≠ 0) :
      ∃ h : N.field ≃ₐ[ℚ] N.field, tauV x = left h x := by
    let lambda : RegularKernelGroup N M := Additive.toMul (e.symm x)
    have hlambda : lambda ≠ 1 := by
      intro hlambda
      apply hx
      apply e.symm.injective
      change e.symm x = e.symm 0
      apply Additive.toMul.injective
      simpa [lambda] using hlambda
    obtain ⟨h, hh⟩ := regularKernelTransport_pointwise_translate
      F₁ F₂ N theta h₁ h₂ p M hcomm hExponent lambda hlambda
    refine ⟨h, ?_⟩
    change e (Additive.ofMul (tauMul lambda)) =
      MonoidAlgebra.single h 1 * x
    rw [hh, he]
    simp [regularLeftTranslate, lambda]
  let U (h : N.field ≃ₐ[ℚ] N.field) :
      Submodule (ZMod (p : ℕ))
        (MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field)) :=
    LinearMap.ker (tauV.toLinearMap - left h)
  have hmem (h : N.field ≃ₐ[ℚ] N.field)
      (x : MonoidAlgebra (ZMod (p : ℕ)) (N.field ≃ₐ[ℚ] N.field)) :
      x ∈ U h ↔ tauV x = left h x := by
    change tauV x - left h x = 0 ↔ tauV x = left h x
    exact sub_eq_zero
  let enum := Fintype.equivFin (N.field ≃ₐ[ℚ] N.field)
  have hcover (x : MonoidAlgebra (ZMod (p : ℕ))
      (N.field ≃ₐ[ℚ] N.field)) :
      ∃ i : Fin (Fintype.card (N.field ≃ₐ[ℚ] N.field)),
        x ∈ U (enum.symm i) := by
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [hmem, hx]
      simp
    · obtain ⟨h, hh⟩ := hpoint x hx
      exact ⟨enum h, by simpa [enum] using (hmem h x).2 hh⟩
  obtain ⟨i, hi⟩ := subspace_cover p
    (Fintype.card (N.field ≃ₐ[ℚ] N.field))
    (fun i => U (enum.symm i)) hp hcover
  let hN : N.field ≃ₐ[ℚ] N.field := enum.symm i
  have hglobal (x : MonoidAlgebra (ZMod (p : ℕ))
      (N.field ≃ₐ[ℚ] N.field)) : tauV x = left hN x := by
    apply (hmem hN x).1
    change x ∈ U (enum.symm i)
    rw [hi]
    trivial
  have hglobalMul (a : RegularKernelGroup N M) :
      tauMul a = regularKernelConjugation N M hcomm hN a := by
    apply Additive.ofMul.injective
    apply e.injective
    calc
      e (Additive.ofMul (tauMul a)) =
          tauV (e (Additive.ofMul a)) := by
            simp [tauV, tau, tauAdd, tauMul]
      _ = left hN (e (Additive.ofMul a)) :=
        hglobal (e (Additive.ofMul a))
      _ = regularLeftTranslate p hN (e (Additive.ofMul a)) := by rfl
      _ = e (Additive.ofMul
          (regularKernelConjugation N M hcomm hN a)) := (he hN a).symm
  refine ⟨hN, ?_⟩
  intro g
  let a₀ : RegularKernelGroup N M := Additive.toMul
    (e.symm (MonoidAlgebra.single (1 : N.field ≃ₐ[ℚ] N.field) 1))
  have hs := regularKernelTransport_semilinear
    F₁ F₂ N theta h₁ h₂ M hcomm g a₀
  change tauMul (regularKernelConjugation N M hcomm g.1 a₀) =
    regularKernelConjugation N M hcomm
      (normalLevelQuotientIso theta N h₁ h₂ g).1 (tauMul a₀) at hs
  rw [hglobalMul, hglobalMul] at hs
  have hsE := congrArg (fun a => e (Additive.ofMul a)) hs
  rw [he, he, he, he] at hsE
  have hsingle :
      MonoidAlgebra.single (hN * g.1) (1 : ZMod (p : ℕ)) =
        MonoidAlgebra.single
          ((normalLevelQuotientIso theta N h₁ h₂ g).1 * hN) 1 := by
    simpa [regularLeftTranslate, a₀,
      MonoidAlgebra.single_mul_single] using hsE
  have hrel : hN * g.1 =
      (normalLevelQuotientIso theta N h₁ h₂ g).1 * hN :=
    Finsupp.single_left_injective one_ne_zero hsingle
  calc
    (normalLevelQuotientIso theta N h₁ h₂ g).1 =
        (normalLevelQuotientIso theta N h₁ h₂ g).1 * hN * hN⁻¹ := by
      group
    _ = hN * g.1 * hN⁻¹ := by rw [hrel]

/-- Equivalent automorphism form of `prop:finite-conjugacy`: a lift in
`G_ℚ` carries `F₂` onto `F₁` and induces the prescribed finite quotient
map. -/
theorem exists_finiteLevel_inducingAutomorphism
    (F₁ F₂ N : NumberFieldInOmega)
    (theta : absoluteGaloisGroup F₁ ≃ₜ* absoluteGaloisGroup F₂)
    (h₁ : F₁.field ≤ N.field) (h₂ : F₂.field ≤ N.field)
    [IsGalois ℚ N.field] :
    ∃ alpha : RationalAbsoluteGaloisGroup,
      ∃ hfield : conjugateField alpha F₂.field = F₁.field,
        finiteConjugationIso F₁ F₂ N h₁ h₂ alpha hfield =
          normalLevelQuotientIso theta N h₁ h₂ := by
  obtain ⟨hN, hinner⟩ := finiteLevel_conjugacy F₁ F₂ N theta h₁ h₂
  let sigmaN := normalLevelQuotientIso theta N h₁ h₂
  letI : IsGalois ℚ Omega := by
    letI : IsAlgClosure ℚ Omega :=
      ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
    exact ⟨⟩
  obtain ⟨alpha, halpha⟩ :=
    AlgEquiv.restrictNormalHom_surjective Omega hN⁻¹
  change ambientRestriction N alpha = hN⁻¹ at halpha
  have hforward (g : absoluteGaloisGroup F₂) :
      alpha * g.1 * alpha⁻¹ ∈ absoluteGaloisGroup F₁ := by
    let q₂ := finiteQuotientMap F₂ N h₂ g
    let q₁ := sigmaN.symm q₂
    have hq₂ : q₂.1 = hN * q₁.1 * hN⁻¹ := by
      rw [← hinner q₁]
      exact congrArg Subtype.val (sigmaN.apply_symm_apply q₂).symm
    have hg_res : ambientRestriction N g.1 = q₂.1 := rfl
    have hres : ambientRestriction N (alpha * g.1 * alpha⁻¹) = q₁.1 := by
      rw [map_mul, map_mul, map_inv, halpha, hg_res, hq₂]
      group
    intro x
    let y : N.field := ⟨x.1, h₁ x.2⟩
    calc
      (alpha * g.1 * alpha⁻¹) x.1 =
          N.field.val (ambientRestriction N (alpha * g.1 * alpha⁻¹) y) :=
        (ambientRestriction_apply N (alpha * g.1 * alpha⁻¹) y).symm
      _ = N.field.val (q₁.1 y) := by rw [hres]
      _ = x.1 := congrArg Subtype.val (q₁.2 x)
  have hbackward (g : absoluteGaloisGroup F₁) :
      alpha⁻¹ * g.1 * alpha ∈ absoluteGaloisGroup F₂ := by
    let q₁ := finiteQuotientMap F₁ N h₁ g
    let q₂ := sigmaN q₁
    have hq₂ : q₂.1 = hN * q₁.1 * hN⁻¹ := hinner q₁
    have hg_res : ambientRestriction N g.1 = q₁.1 := rfl
    have hres : ambientRestriction N (alpha⁻¹ * g.1 * alpha) = q₂.1 := by
      rw [map_mul, map_mul, map_inv, halpha, hg_res, hq₂]
      group
    intro x
    let y : N.field := ⟨x.1, h₂ x.2⟩
    calc
      (alpha⁻¹ * g.1 * alpha) x.1 =
          N.field.val (ambientRestriction N (alpha⁻¹ * g.1 * alpha) y) :=
        (ambientRestriction_apply N (alpha⁻¹ * g.1 * alpha) y).symm
      _ = N.field.val (q₂.1 y) := by rw [hres]
      _ = x.1 := congrArg Subtype.val (q₂.2 x)
  have hgroup : Subgroup.map (MulAut.conj alpha).toMonoidHom
      (absoluteGaloisGroup F₂) = absoluteGaloisGroup F₁ := by
    apply le_antisymm
    · rintro y ⟨g, hg, rfl⟩
      exact hforward ⟨g, hg⟩
    · intro y hy
      have hback := hbackward ⟨y, hy⟩
      refine ⟨alpha⁻¹ * y * alpha, hback, ?_⟩
      change alpha * (alpha⁻¹ * y * alpha) * alpha⁻¹ = y
      group
  letI : SMul RationalAbsoluteGaloisGroup (Set Omega) := Set.smulSet
  have hset : (conjugateField alpha F₂.field : Set Omega) =
      alpha • (F₂.field : Set Omega) := by
    ext x
    rw [show x ∈ (conjugateField alpha F₂.field : Set Omega) ↔
      alpha.symm x ∈ F₂.field from mem_conjugateField_iff alpha F₂.field x]
    simp only [Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  have hfix : (conjugateField alpha F₂.field).fixingSubgroup =
      F₁.field.fixingSubgroup := by
    change fixingSubgroup RationalAbsoluteGaloisGroup
        (conjugateField alpha F₂.field : Set Omega) =
      fixingSubgroup RationalAbsoluteGaloisGroup (F₁.field : Set Omega)
    rw [hset,
      SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj]
    exact hgroup
  have hfield : conjugateField alpha F₂.field = F₁.field := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup
        (conjugateField alpha F₂.field),
      ← InfiniteGalois.fixedField_fixingSubgroup F₁.field, hfix]
  refine ⟨alpha, hfield, ?_⟩
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [finiteConjugationIso_apply, halpha, inv_inv]
  exact (hinner g).symm

end

end NU.NeukirchUchida
