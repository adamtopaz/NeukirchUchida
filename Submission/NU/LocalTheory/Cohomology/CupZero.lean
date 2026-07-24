import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Instances.ZMod

/-!
# Explicit low-degree cup-zero relation

Following Blueprint §2.2 and representation choice §10.1(3–4), this file
uses no graded cup-product API.  `X_U^ℓ` is an explicit staged quotient and
`A_U^ℓ` consists of continuous additive characters; evaluation is introduced
before the cochain predicate.
-/

namespace NU.LocalTheory

noncomputable section

/-- The maximal elementary abelian `n`-quotient, presented as the mod-`n`
quotient of the topological abelianization.  Thus this is explicitly
`G / closure([G,G] Gⁿ)` in the compact/profinite cases used below. -/
abbrev ElementaryQuotient (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) :=
  ModN (Additive (TopologicalAbelianization G)) n

/-- Continuous additive `ZMod n`-valued characters of a topological group. -/
abbrev ContinuousCharacter (G : Type*) [Group G] [TopologicalSpace G]
    (n : ℕ) :=
  ContinuousAddMonoidHom (Additive G) (ZMod n)

/-- The canonical `ZMod n`-module structure on continuous characters. -/
instance continuousCharacterModule (G : Type*) [Group G] [TopologicalSpace G]
    (n : ℕ) : Module (ZMod n) (ContinuousCharacter G n) :=
  AddCommGroup.zmodModule (by
    intro f
    ext g
    simp)

private def characterEvaluationAt {G : Type*} [Group G] [TopologicalSpace G]
    (n : ℕ) (g : G) : Module.Dual (ZMod n) (ContinuousCharacter G n) where
  toFun a := a (Additive.ofMul g)
  map_add' a b := by simp
  map_smul' r a := by
    let ev : ContinuousCharacter G n →+ ZMod n :=
      { toFun := fun b => b (Additive.ofMul g)
        map_zero' := by simp
        map_add' := fun _ _ => by simp }
    simpa [ev] using ZMod.map_smul ev r a

private def rawEvaluation {G : Type*} [Group G] [TopologicalSpace G]
    (n : ℕ) : G →*
      Multiplicative (Module.Dual (ZMod n) (ContinuousCharacter G n)) where
  toFun g := Multiplicative.ofAdd (characterEvaluationAt n g)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [characterEvaluationAt]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext a
    simp [characterEvaluationAt]

private theorem character_kills_topologicalCommutator
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) (a : ContinuousCharacter G n) :
    Subgroup.topologicalClosure (commutator G) ≤
      (a.toAddMonoidHom.toMultiplicativeRight).ker := by
  apply Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker
        a.toAddMonoidHom.toMultiplicativeRight)
  change IsClosed {g : G | a (Additive.ofMul g) = 0}
  exact isClosed_singleton.preimage a.continuous

private theorem rawEvaluation_kills_topologicalCommutator
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) : Subgroup.topologicalClosure (commutator G) ≤
      (rawEvaluation n).ker := by
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply Multiplicative.toAdd.injective
  ext a
  exact MonoidHom.mem_ker.mp
    (character_kills_topologicalCommutator n a hg)

private def abelianizedEvaluation {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) :
    Additive (TopologicalAbelianization G) →+
      Module.Dual (ZMod n) (ContinuousCharacter G n) :=
  MonoidHom.toAdditiveLeft
    (QuotientGroup.lift (Subgroup.topologicalClosure (commutator G))
      (rawEvaluation n) (rawEvaluation_kills_topologicalCommutator n))

/-- The class of a group element in the elementary quotient. -/
def elementaryClass {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) (g : G) : ElementaryQuotient G n :=
  ModN.mkQ n (Additive.ofMul (QuotientGroup.mk g))

/-- Existence of the canonical evaluation pairing.  This theorem packages
the two quotient-lift arguments: continuous characters kill the closure of
the commutator and all `n`-th powers. -/
theorem exists_evaluationLinear {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) :
    ∃ e : ElementaryQuotient G n →ₗ[ZMod n]
        Module.Dual (ZMod n) (ContinuousCharacter G n),
      ∀ g a, e (elementaryClass n g) a = a (Additive.ofMul g) := by
  have htorsion : ∀ x : Additive (TopologicalAbelianization G),
      n • abelianizedEvaluation n x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), CharP.cast_eq_zero, zero_smul]
  let φ : {f : Additive (TopologicalAbelianization G) →+
      Module.Dual (ZMod n) (ContinuousCharacter G n) // ∀ x, n • f x = 0} :=
    ⟨abelianizedEvaluation n, htorsion⟩
  let e : ElementaryQuotient G n →ₗ[ZMod n]
      Module.Dual (ZMod n) (ContinuousCharacter G n) :=
    (ModN.liftEquiv').symm φ
  refine ⟨e, ?_⟩
  intro g a
  have he : ModN.liftEquiv' e = φ := (ModN.liftEquiv').apply_symm_apply φ
  have heq := DFunLike.congr_fun (congrArg Subtype.val he)
    (Additive.ofMul (QuotientGroup.mk g))
  change e (ModN.mkQ n (Additive.ofMul (QuotientGroup.mk g))) =
      abelianizedEvaluation n (Additive.ofMul (QuotientGroup.mk g)) at heq
  change e (ModN.mkQ n (Additive.ofMul (QuotientGroup.mk g))) a = _
  rw [heq]
  rfl

/-- Evaluation `X_G^n × A_G^n → ZMod n`. -/
noncomputable def evaluationLinear {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) :
    ElementaryQuotient G n →ₗ[ZMod n]
      Module.Dual (ZMod n) (ContinuousCharacter G n) :=
  (exists_evaluationLinear (G := G) n).choose

/-- Evaluation written as a scalar-valued function. -/
def evaluation {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) (x : ElementaryQuotient G n)
    (a : ContinuousCharacter G n) : ZMod n :=
  evaluationLinear n x a

@[simp]
theorem evaluation_elementaryClass {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) (g : G)
    (a : ContinuousCharacter G n) :
    evaluation n (elementaryClass n g) a = a (Additive.ofMul g) :=
  (exists_evaluationLinear (G := G) n).choose_spec g a

/-- Evaluate a continuous character on an element of the original group. -/
def continuousCharacterValue {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} (a : ContinuousCharacter G n) (g : G) : ZMod n :=
  a (Additive.ofMul g)

private theorem continuousCharacter_smul_apply
    {G : Type*} [Group G] [TopologicalSpace G] (n : ℕ)
    (r : ZMod n) (a : ContinuousCharacter G n) (g : G) :
    continuousCharacterValue (r • a) g =
      r * continuousCharacterValue a g := by
  change (r • a) (Additive.ofMul g) = r • a (Additive.ofMul g)
  let ev : ContinuousCharacter G n →+ ZMod n :=
    { toFun := fun b => b (Additive.ofMul g)
      map_zero' := by simp
      map_add' := fun _ _ => by simp }
  simpa [ev] using ZMod.map_smul ev r a

/-- Blueprint (2.3), `eq:cupzero-cochain`: the inhomogeneous cup cocycle is
an explicit continuous coboundary. -/
def CupZero {G : Type*} [Group G] [TopologicalSpace G] (n : ℕ)
    (a b : ContinuousCharacter G n) : Prop :=
  ∃ c : C(G, ZMod n), ∀ σ τ : G,
    continuousCharacterValue a σ * continuousCharacterValue b τ =
      c σ + c τ - c (σ * τ)

/-- Convert a continuous multiplicative homomorphism to its additive copy. -/
def additiveContinuousHom {H G : Type*} [Group H] [Group G]
    [TopologicalSpace H] [TopologicalSpace G]
    (f : ContinuousMonoidHom H G) :
    ContinuousAddMonoidHom (Additive H) (Additive G) where
  toFun h := Additive.ofMul (f (Additive.toMul h))
  map_zero' := by simp
  map_add' x y := by simp
  continuous_toFun := f.continuous

/-- Restriction of continuous characters. -/
def restrictCharacter {H G : Type*} [Group H] [Group G]
    [TopologicalSpace H] [TopologicalSpace G] (n : ℕ)
    (f : ContinuousMonoidHom H G) (a : ContinuousCharacter G n) :
    ContinuousCharacter H n :=
  a.comp (additiveContinuousHom f)

/-- Blueprint §2.2(1): cup-zero is functorial under restriction. -/
theorem CupZero.restrict {H G : Type*} [Group H] [Group G]
    [TopologicalSpace H] [TopologicalSpace G] {n : ℕ}
    (f : ContinuousMonoidHom H G) {a b : ContinuousCharacter G n}
    (h : CupZero n a b) :
    CupZero n (restrictCharacter n f a) (restrictCharacter n f b) := by
  rcases h with ⟨c, hc⟩
  refine ⟨c.comp f, ?_⟩
  intro σ τ
  change a (Additive.ofMul (f σ)) * b (Additive.ofMul (f τ)) =
    c (f σ) + c (f τ) - c (f (σ * τ))
  have hmap : f (σ * τ) = f σ * f τ := map_mul f σ τ
  rw [hmap]
  exact hc (f σ) (f τ)

/-- Cup-zero is preserved by simultaneous scalar changes. -/
theorem CupZero.smul {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} {a b : ContinuousCharacter G n} (h : CupZero n a b)
    (r s : ZMod n) : CupZero n (r • a) (s • b) := by
  rcases h with ⟨c, hc⟩
  let d : C(G, ZMod n) :=
    ⟨fun g => (r * s) * c g, continuous_const.mul c.continuous⟩
  refine ⟨d, ?_⟩
  intro σ τ
  rw [continuousCharacter_smul_apply, continuousCharacter_smul_apply]
  calc
    (r * continuousCharacterValue a σ) *
        (s * continuousCharacterValue b τ) =
      (r * s) * (continuousCharacterValue a σ *
        continuousCharacterValue b τ) := by ring
    _ = (r * s) * (c σ + c τ - c (σ * τ)) := by rw [hc]
    _ = d σ + d τ - d (σ * τ) := by
      change (r * s) * (c σ + c τ - c (σ * τ)) =
        (r * s) * c σ + (r * s) * c τ - (r * s) * c (σ * τ)
      ring

/-- Cochain-level additivity in the first variable. -/
theorem CupZero.add_left {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} {a₁ a₂ b : ContinuousCharacter G n}
    (h₁ : CupZero n a₁ b) (h₂ : CupZero n a₂ b) :
    CupZero n (a₁ + a₂) b := by
  rcases h₁ with ⟨c₁, hc₁⟩
  rcases h₂ with ⟨c₂, hc₂⟩
  let d : C(G, ZMod n) :=
    ⟨fun g => c₁ g + c₂ g, c₁.continuous.add c₂.continuous⟩
  refine ⟨d, ?_⟩
  intro σ τ
  change (continuousCharacterValue a₁ σ + continuousCharacterValue a₂ σ) *
      continuousCharacterValue b τ = _
  rw [add_mul, hc₁, hc₂]
  change (c₁ σ + c₁ τ - c₁ (σ * τ)) +
      (c₂ σ + c₂ τ - c₂ (σ * τ)) =
    (c₁ σ + c₂ σ) + (c₁ τ + c₂ τ) -
      (c₁ (σ * τ) + c₂ (σ * τ))
  abel

/-- Cochain-level additivity in the second variable. -/
theorem CupZero.add_right {G : Type*} [Group G] [TopologicalSpace G]
    {n : ℕ} {a b₁ b₂ : ContinuousCharacter G n}
    (h₁ : CupZero n a b₁) (h₂ : CupZero n a b₂) :
    CupZero n a (b₁ + b₂) := by
  rcases h₁ with ⟨c₁, hc₁⟩
  rcases h₂ with ⟨c₂, hc₂⟩
  let d : C(G, ZMod n) :=
    ⟨fun g => c₁ g + c₂ g, c₁.continuous.add c₂.continuous⟩
  refine ⟨d, ?_⟩
  intro σ τ
  change continuousCharacterValue a σ *
      (continuousCharacterValue b₁ τ + continuousCharacterValue b₂ τ) = _
  rw [mul_add, hc₁, hc₂]
  change (c₁ σ + c₁ τ - c₁ (σ * τ)) +
      (c₂ σ + c₂ τ - c₂ (σ * τ)) =
    (c₁ σ + c₂ σ) + (c₁ τ + c₂ τ) -
      (c₁ (σ * τ) + c₂ (σ * τ))
  abel

/-- The zero character is cup-zero in the first variable. -/
theorem cupZero_zero_left {G : Type*} [Group G] [TopologicalSpace G]
    (n : ℕ) (b : ContinuousCharacter G n) : CupZero n 0 b := by
  let c : C(G, ZMod n) := ⟨fun _ => 0, continuous_const⟩
  refine ⟨c, ?_⟩
  intro σ τ
  simp [continuousCharacterValue, c]

/-- The zero character is cup-zero in the second variable. -/
theorem cupZero_zero_right {G : Type*} [Group G] [TopologicalSpace G]
    (n : ℕ) (a : ContinuousCharacter G n) : CupZero n a 0 := by
  let c : C(G, ZMod n) := ⟨fun _ => 0, continuous_const⟩
  refine ⟨c, ?_⟩
  intro σ τ
  simp [continuousCharacterValue, c]

end

end NU.LocalTheory
