import Submission.NU.NeukirchUchida.Main

/-!
# The Neukirch–Uchida theorem

Final assembly, following `~/sources/blueprints/neukirch_uchida_blueprint.tex`:
the pointed theorem (every isomorphism `G_{k₁} ≃ G_{k₂}` of absolute Galois
groups of number fields inside a fixed `Ω = closure of ℚ` is conjugation by a
unique `α ∈ G_ℚ` with `α(k₂) = k₁`) and the outer form. Consumes
`NU.LocalTheory`, `NU.Chebotarev`, `NU.LCFT` through the explicit interfaces
of the blueprint §1.2; the bare-local recognition grant (`warn:bare-local`)
is a named visible assumption. Campaign: `NU/NeukirchUchida/CAMPAIGN.md`.
-/
