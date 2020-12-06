import .preamble_results

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(J : model_with_corners 𝕜 F G) (J' : model_with_corners 𝕜 F' G')

section diffeomorph

variables (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
(N' : Type*) [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
(n : with_top ℕ)

/-- α and β are homeomorph, also called topological isomoph -/
structure diffeomorph extends M ≃ M' :=
(times_cont_mdiff_to_fun  : smooth I I' to_fun)
(times_cont_mdiff_inv_fun : smooth I' I inv_fun)

infix ` ≃ₘ `:50 := diffeomorph _ _
notation M ` ≃ₘ[` I `;` J `]` N := diffeomorph I J M N

namespace diffeomorph
instance : has_coe_to_fun (diffeomorph I I' M M') := ⟨λ _, M → M', λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : diffeomorph I I' M M') (x : M) : h x = h.to_equiv x := rfl

/-- Identity map is a diffeomorphism. -/
protected def refl : M ≃ₘ[I; I] M :=
{ smooth_to_fun := smooth_in_charts_id, smooth_inv_fun := smooth_in_charts_id, .. homeomorph.refl M }

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : diffeomorph I I' M M') (h₂ : diffeomorph I' J M' N) : M ≃ₘ[I | J] N :=
{ smooth_to_fun  := h₂.smooth_to_fun.comp h₁.smooth_to_fun,
  smooth_inv_fun := h₁.smooth_inv_fun.comp h₂.smooth_inv_fun,
  .. homeomorph.trans h₁.to_homeomorph h₂.to_homeomorph }

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ[I | J] N) : N ≃ₘ[J | I] M :=
{ smooth_to_fun  := h.smooth_inv_fun,
  smooth_inv_fun := h.smooth_to_fun,
  .. h.to_homeomorph.symm }

end diffeomorph

end diffeomorph