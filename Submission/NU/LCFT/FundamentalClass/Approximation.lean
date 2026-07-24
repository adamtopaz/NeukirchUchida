import Submission.NU.LCFT.Cohomology.AbstractReciprocity

/-!
# Complete filtered approximation

The filtration interface below encodes completeness without analytic infinite sums: compatible
approximations have a limit modulo every filtration term.  The two low-degree forms are exactly
what the fundamental-class construction uses.
-/

namespace NU.LCFT

noncomputable section

/--
**F01**, Lemma `lem:serre-approximation`: a complete separated decreasing filtration
`A = F 0 ⊇ F 1 ⊇ F 2 ⊇ ⋯`.

The last field is the elementwise form of surjectivity of the canonical map to the inverse
limit.  Together with `separated` it also gives uniqueness.  Requiring `F 0 = ⊤` is essential:
without it the approximation conclusions are refuted by the constant bottom filtration.
-/
structure CompleteSeparatedFiltration (A : Type*) [AddCommGroup A] where
  /-- Filtration terms. -/
  F : ℕ → AddSubgroup A
  /-- The blueprint's identity `A = F 0`. -/
  F_zero : F 0 = ⊤
  /-- The filtration is decreasing. -/
  antitone : Antitone F
  /-- The filtration is separated. -/
  separated : (⨅ n, F n) = ⊥
  /-- Every compatible system of representatives has a simultaneous lift. -/
  complete : ∀ x : ℕ → A,
    (∀ n, x (n + 1) - x n ∈ F n) → ∃ a, ∀ n, a - x n ∈ F n

namespace CompleteSeparatedFiltration

variable {G : Type} [Group G] [Fintype G]
variable {M : Rep ℤ G}

private lemma d0_mem_cocycles1 (b : M) :
    Inhomogeneous.d0 M b ∈ Inhomogeneous.cocycles1 M := by
  constructor
  · change Inhomogeneous.d1 M (Inhomogeneous.d0 M b) = 0
    ext g h
    simp [Inhomogeneous.d0, Inhomogeneous.d1]
  · change Inhomogeneous.d0 M b 1 = 0
    simp [Inhomogeneous.d0]

private lemma d1_mem_cocycles2_of_normalized (b : Inhomogeneous.C1 M)
    (hb : b 1 = 0) :
    Inhomogeneous.d1 M b ∈ Inhomogeneous.cocycles2 M := by
  constructor
  · change Inhomogeneous.d2 M (Inhomogeneous.d1 M b) = 0
    ext g h t
    simp [Inhomogeneous.d1, Inhomogeneous.d2, mul_assoc]
    abel
  · constructor
    · intro g
      simp [Inhomogeneous.d1, hb]
    · intro g
      simp [Inhomogeneous.d1, hb]

/--
**F01**, Lemma `lem:serre-approximation`: degree-one complete-filtered approximation.  The
primitive at stage `n` is required to lie in `F n`; this is the quotient statement
`H¹(G,F n/F (n+1)) = 0`, rather than an unconstrained correction in the ambient module.
-/
theorem serreApproximation_H1 (Φ : CompleteSeparatedFiltration M)
    (stable : ∀ n g x, x ∈ Φ.F n → M.ρ g x ∈ Φ.F n)
    (step : ∀ n (z : Inhomogeneous.C1 M), z ∈ Inhomogeneous.cocycles1 M →
      (∀ g, z g ∈ Φ.F n) →
      ∃ b : M, b ∈ Φ.F n ∧
        ∀ g, (z - Inhomogeneous.d0 M b) g ∈ Φ.F (n + 1)) :
    Subsingleton (Inhomogeneous.H1 M) := by
  have primitive (z : Inhomogeneous.C1 M) (hz : z ∈ Inhomogeneous.cocycles1 M) :
      ∃ a : M, Inhomogeneous.d0 M a = z := by
    let Stage (n : ℕ) := {a : M //
      (z - Inhomogeneous.d0 M a ∈ Inhomogeneous.cocycles1 M) ∧
        ∀ g, (z - Inhomogeneous.d0 M a) g ∈ Φ.F n}
    let initial : Stage 0 := ⟨0, by
      constructor
      · simpa using hz
      · intro g
        rw [Φ.F_zero]
        exact AddSubgroup.mem_top _⟩
    let correction (n : ℕ) (s : Stage n) : M :=
      (step n (z - Inhomogeneous.d0 M s.1) s.2.1 s.2.2).choose
    have correction_mem (n : ℕ) (s : Stage n) : correction n s ∈ Φ.F n :=
      (step n (z - Inhomogeneous.d0 M s.1) s.2.1 s.2.2).choose_spec.1
    have correction_spec (n : ℕ) (s : Stage n) :
        ∀ g, ((z - Inhomogeneous.d0 M s.1) -
          Inhomogeneous.d0 M (correction n s)) g ∈ Φ.F (n + 1) :=
      (step n (z - Inhomogeneous.d0 M s.1) s.2.1 s.2.2).choose_spec.2
    let next (n : ℕ) (s : Stage n) : Stage (n + 1) :=
      ⟨s.1 + correction n s, by
        have heq : z - Inhomogeneous.d0 M (s.1 + correction n s) =
            (z - Inhomogeneous.d0 M s.1) -
              Inhomogeneous.d0 M (correction n s) := by
          rw [map_add]
          abel
        rw [heq]
        constructor
        · exact (Inhomogeneous.cocycles1 M).sub_mem s.2.1
            (d0_mem_cocycles1 (correction n s))
        · exact correction_spec n s⟩
    let stages : (n : ℕ) → Stage n := fun n =>
      @Nat.rec (fun n => Stage n) initial (fun n s => next n s) n
    have stages_succ (n : ℕ) : (stages (n + 1)).1 =
        (stages n).1 + correction n (stages n) := by
      rfl
    have hdiff (n : ℕ) : (stages (n + 1)).1 - (stages n).1 ∈ Φ.F n := by
      rw [stages_succ]
      simpa using correction_mem n (stages n)
    obtain ⟨a, ha⟩ := Φ.complete (fun n => (stages n).1) hdiff
    refine ⟨a, ?_⟩
    apply funext
    intro g
    have hall : z g - Inhomogeneous.d0 M a g ∈ ⨅ n, Φ.F n := by
      rw [AddSubgroup.mem_iInf]
      intro n
      have hdelta : a - (stages n).1 ∈ Φ.F n := ha n
      have hd0 : Inhomogeneous.d0 M (a - (stages n).1) g ∈ Φ.F n := by
        change M.ρ g (a - (stages n).1) - (a - (stages n).1) ∈ Φ.F n
        exact (Φ.F n).sub_mem (stable n g _ hdelta) hdelta
      have hres := (stages n).2.2 g
      have heq : z g - Inhomogeneous.d0 M a g =
          (z - Inhomogeneous.d0 M (stages n).1) g -
            Inhomogeneous.d0 M (a - (stages n).1) g := by
        simp only [Inhomogeneous.d0, Pi.sub_apply, map_sub]
        abel
      rw [heq]
      exact (Φ.F n).sub_mem hres hd0
    rw [Φ.separated] at hall
    have hzero : z g - Inhomogeneous.d0 M a g = 0 := hall
    exact (sub_eq_zero.mp hzero).symm
  constructor
  intro x y
  apply sub_eq_zero.mp
  induction x - y using QuotientAddGroup.induction_on with
  | H zc =>
      apply (QuotientAddGroup.eq_zero_iff zc).2
      obtain ⟨a, ha⟩ := primitive zc zc.2
      exact ⟨a, ha⟩

/--
**F01**, Lemma `lem:serre-approximation`: degree-two complete-filtered approximation.  Here the
one-cochain primitive is pointwise `F n`-valued, exactly as required to form compatible
primitives in the finite quotients.
-/
theorem serreApproximation_H2 (Φ : CompleteSeparatedFiltration M)
    (stable : ∀ n g x, x ∈ Φ.F n → M.ρ g x ∈ Φ.F n)
    (step : ∀ n (z : Inhomogeneous.C2 M), z ∈ Inhomogeneous.cocycles2 M →
      (∀ g h, z g h ∈ Φ.F n) →
      ∃ b : Inhomogeneous.C1 M, (∀ g, b g ∈ Φ.F n) ∧
        ∀ g h, (z - Inhomogeneous.d1 M b) g h ∈ Φ.F (n + 1)) :
    Subsingleton (Inhomogeneous.H2 M) := by
  have primitive (z : Inhomogeneous.C2 M) (hz : z ∈ Inhomogeneous.cocycles2 M) :
      ∃ b : Inhomogeneous.C1 M, Inhomogeneous.d1 M b = z := by
    let Stage (n : ℕ) := {b : Inhomogeneous.C1 M //
      (z - Inhomogeneous.d1 M b ∈ Inhomogeneous.cocycles2 M) ∧
        ∀ g h, (z - Inhomogeneous.d1 M b) g h ∈ Φ.F n}
    let initial : Stage 0 := ⟨0, by
      constructor
      · simpa using hz
      · intro g h
        rw [Φ.F_zero]
        exact AddSubgroup.mem_top _⟩
    let rawCorrection (n : ℕ) (s : Stage n) : Inhomogeneous.C1 M :=
      (step n (z - Inhomogeneous.d1 M s.1) s.2.1 s.2.2).choose
    have rawCorrection_mem (n : ℕ) (s : Stage n) :
        ∀ g, rawCorrection n s g ∈ Φ.F n :=
      (step n (z - Inhomogeneous.d1 M s.1) s.2.1 s.2.2).choose_spec.1
    have rawCorrection_spec (n : ℕ) (s : Stage n) :
        ∀ g h, ((z - Inhomogeneous.d1 M s.1) -
          Inhomogeneous.d1 M (rawCorrection n s)) g h ∈ Φ.F (n + 1) :=
      (step n (z - Inhomogeneous.d1 M s.1) s.2.1 s.2.2).choose_spec.2
    let correction (n : ℕ) (s : Stage n) : Inhomogeneous.C1 M :=
      fun g => rawCorrection n s g - rawCorrection n s 1
    have correction_mem (n : ℕ) (s : Stage n) :
        ∀ g, correction n s g ∈ Φ.F n := by
      intro g
      exact (Φ.F n).sub_mem (rawCorrection_mem n s g) (rawCorrection_mem n s 1)
    have correction_normalized (n : ℕ) (s : Stage n) : correction n s 1 = 0 := by
      simp [correction]
    have raw_one_deeper (n : ℕ) (s : Stage n) :
        rawCorrection n s 1 ∈ Φ.F (n + 1) := by
      have h := rawCorrection_spec n s 1 1
      have hz11 : (z - Inhomogeneous.d1 M s.1) 1 1 = 0 := s.2.1.2.1 1
      have heq : (((z - Inhomogeneous.d1 M s.1) -
          Inhomogeneous.d1 M (rawCorrection n s)) 1 1) =
          - rawCorrection n s 1 := by
        change (z - Inhomogeneous.d1 M s.1) 1 1 -
            Inhomogeneous.d1 M (rawCorrection n s) 1 1 = _
        rw [hz11]
        simp [Inhomogeneous.d1]
      rw [heq] at h
      simpa using (Φ.F (n + 1)).neg_mem h
    have correction_spec (n : ℕ) (s : Stage n) :
        ∀ g h, ((z - Inhomogeneous.d1 M s.1) -
          Inhomogeneous.d1 M (correction n s)) g h ∈ Φ.F (n + 1) := by
      intro g h
      have hraw := rawCorrection_spec n s g h
      have hconst : M.ρ g (rawCorrection n s 1) ∈ Φ.F (n + 1) :=
        stable (n + 1) g _ (raw_one_deeper n s)
      have hd1corr : Inhomogeneous.d1 M (correction n s) g h =
          Inhomogeneous.d1 M (rawCorrection n s) g h -
            M.ρ g (rawCorrection n s 1) := by
        change M.ρ g (rawCorrection n s h - rawCorrection n s 1) -
            (rawCorrection n s (g * h) - rawCorrection n s 1) +
            (rawCorrection n s g - rawCorrection n s 1) =
          (M.ρ g (rawCorrection n s h) - rawCorrection n s (g * h) +
            rawCorrection n s g) - M.ρ g (rawCorrection n s 1)
        rw [map_sub]
        abel
      have heq : ((z - Inhomogeneous.d1 M s.1) -
          Inhomogeneous.d1 M (correction n s)) g h =
          ((z - Inhomogeneous.d1 M s.1) -
            Inhomogeneous.d1 M (rawCorrection n s)) g h +
            M.ρ g (rawCorrection n s 1) := by
        change (z - Inhomogeneous.d1 M s.1) g h -
            Inhomogeneous.d1 M (correction n s) g h =
          ((z - Inhomogeneous.d1 M s.1) g h -
            Inhomogeneous.d1 M (rawCorrection n s) g h) + _
        rw [hd1corr]
        abel
      rw [heq]
      exact (Φ.F (n + 1)).add_mem hraw hconst
    let next (n : ℕ) (s : Stage n) : Stage (n + 1) :=
      ⟨s.1 + correction n s, by
        have heq : z - Inhomogeneous.d1 M (s.1 + correction n s) =
            (z - Inhomogeneous.d1 M s.1) -
              Inhomogeneous.d1 M (correction n s) := by
          rw [map_add]
          abel
        rw [heq]
        constructor
        · exact (Inhomogeneous.cocycles2 M).sub_mem s.2.1
            (d1_mem_cocycles2_of_normalized _ (correction_normalized n s))
        · exact correction_spec n s⟩
    let stages : (n : ℕ) → Stage n := fun n =>
      @Nat.rec (fun n => Stage n) initial (fun n s => next n s) n
    have stages_succ (n : ℕ) : (stages (n + 1)).1 =
        (stages n).1 + correction n (stages n) := by
      rfl
    have hdiff (g : G) (n : ℕ) :
        (stages (n + 1)).1 g - (stages n).1 g ∈ Φ.F n := by
      rw [stages_succ]
      simpa using correction_mem n (stages n) g
    have hcomplete (g : G) : ∃ a, ∀ n, a - (stages n).1 g ∈ Φ.F n :=
      Φ.complete (fun n => (stages n).1 g) (hdiff g)
    let b : Inhomogeneous.C1 M := fun g => (hcomplete g).choose
    have hb (g : G) (n : ℕ) : b g - (stages n).1 g ∈ Φ.F n :=
      (hcomplete g).choose_spec n
    refine ⟨b, ?_⟩
    apply funext
    intro g
    apply funext
    intro h
    have hall : z g h - Inhomogeneous.d1 M b g h ∈ ⨅ n, Φ.F n := by
      rw [AddSubgroup.mem_iInf]
      intro n
      let delta : Inhomogeneous.C1 M := fun t => b t - (stages n).1 t
      have hd1 : Inhomogeneous.d1 M delta g h ∈ Φ.F n := by
        change M.ρ g (b h - (stages n).1 h) -
            (b (g * h) - (stages n).1 (g * h)) +
            (b g - (stages n).1 g) ∈ Φ.F n
        exact (Φ.F n).add_mem
          ((Φ.F n).sub_mem (stable n g _ (hb h n)) (hb (g * h) n)) (hb g n)
      have hres := (stages n).2.2 g h
      have hd1delta : Inhomogeneous.d1 M delta =
          Inhomogeneous.d1 M b - Inhomogeneous.d1 M (stages n).1 := by
        change Inhomogeneous.d1 M (b - (stages n).1) = _
        exact map_sub _ _ _
      have heq : z g h - Inhomogeneous.d1 M b g h =
          (z - Inhomogeneous.d1 M (stages n).1) g h -
            Inhomogeneous.d1 M delta g h := by
        change z g h - Inhomogeneous.d1 M b g h =
          (z g h - Inhomogeneous.d1 M (stages n).1 g h) -
            Inhomogeneous.d1 M delta g h
        have hd1delta_app : Inhomogeneous.d1 M delta g h =
            Inhomogeneous.d1 M b g h - Inhomogeneous.d1 M (stages n).1 g h := by
          rw [hd1delta]
          rfl
        rw [hd1delta_app]
        abel
      rw [heq]
      exact (Φ.F n).sub_mem hres hd1
    rw [Φ.separated] at hall
    have hzero : z g h - Inhomogeneous.d1 M b g h = 0 := hall
    exact (sub_eq_zero.mp hzero).symm
  constructor
  intro x y
  apply sub_eq_zero.mp
  induction x - y using QuotientAddGroup.induction_on with
  | H zc =>
      apply (QuotientAddGroup.eq_zero_iff zc).2
      obtain ⟨b, hb⟩ := primitive zc zc.2
      exact ⟨b, hb⟩

end CompleteSeparatedFiltration

end

end NU.LCFT
