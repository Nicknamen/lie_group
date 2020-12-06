import .diffeomorph

open function set
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']

/-- local diffeomorphisms, defined on open subsets of the space -/
@[nolint has_inhabited_instance]
structure local_diffeomorph
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
extends local_homeomorph M M' :=
(smooth_to_fun      : smooth_in_charts_on I I' to_fun source)
(smooth_inv_fun     : smooth_in_charts_on I' I inv_fun target)

/-- A diffomorphism induces a local diffeomorphism on the whole space -/
def diffeomorph.to_local_diffeomorph
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
(e : diffeomorph I I' M M') :
  local_diffeomorph I I' M M' :=
{ smooth_to_fun  := by { simp only [smooth_in_charts_on], erw times_cont_mdiff_in_charts_on_univ, exact e.smooth_to_fun },
  smooth_inv_fun := by { simp only [smooth_in_charts_on], erw times_cont_mdiff_in_charts_on_univ, exact e.smooth_inv_fun },
  ..e.to_homeomorph.to_local_homeomorph }

namespace local_diffeomorph

variables {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F' G'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
(e : local_diffeomorph I I' M M') (e' : local_diffeomorph J J' N N')

instance : has_coe (local_diffeomorph I I' M M') (local_homeomorph M M') := ⟨local_diffeomorph.to_local_homeomorph⟩
instance : has_coe_to_fun (local_diffeomorph I I' M M') := ⟨_, λ e, e.to_local_equiv.to_fun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : local_diffeomorph I' I M' M :=
{ smooth_to_fun      := e.smooth_inv_fun,
  smooth_inv_fun     := e.smooth_to_fun,
  ..e.to_local_homeomorph.symm }

protected lemma smooth_in_charts_on : smooth_in_charts_on I I' e e.source := e.smooth_to_fun

lemma smooth_in_charts_on_symm : smooth_in_charts_on I' I e.symm e.target := e.smooth_inv_fun

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
diffeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps] lemma to_fun_eq_coe (e : local_diffeomorph I I' M M') : e.to_fun = e := rfl

@[simp, mfld_simps] lemma inv_fun_eq_coe (e : local_diffeomorph I I' M M') : e.inv_fun = e.symm := rfl

@[simp, mfld_simps] lemma coe_coe : (e.to_local_equiv : M → M') = e := rfl

@[simp, mfld_simps] lemma coe_coe_symm : (e.to_local_equiv.symm : M' → M) = e.symm := rfl

@[simp, mfld_simps] lemma map_source {x : M} (h : x ∈ e.source) : e x ∈ e.target :=
e.map_source' h

@[simp, mfld_simps] lemma map_target {x : M'} (h : x ∈ e.target) : e.symm x ∈ e.source :=
e.map_target' h

@[simp, mfld_simps] lemma left_inv {x : M} (h : x ∈ e.source) : e.symm (e x) = x :=
e.left_inv' h

@[simp, mfld_simps] lemma right_inv {x : M'} (h : x ∈ e.target) : e (e.symm x) = x :=
e.right_inv' h

lemma eq_of_local_equiv_eq {e e' : local_diffeomorph I I' M M'}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
begin
  cases e, cases e',
  dsimp at *,
  induction h,
  refl
end

lemma eventually_left_inverse (e : local_diffeomorph I I' M M') {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
filter.eventually.mono (mem_nhds_sets e.open_source hx) e.left_inv'

end local_diffeomorph