/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

/-

THIS FILE CONTAINS SCATTERED RESULTS TO BE CORRECTLY PLACED IN MATHLIB

-/

import .times_cont_mdiff
import tactic
import topology.algebra.module
import topology.algebra.continuous_functions

noncomputable theory

section prod

/-
To be placed into topology/contructions
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

@[inline, reducible] def map_diag (A : Type*) : (A → A×A) := (λ a : A, (a, a))

lemma continuous.map_diag : continuous (map_diag α) :=
continuous_id.prod_mk continuous_id

end prod

section

/-
To be placed into topology/local_homemorph
-/

namespace local_homeomorph

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {η : Type*} {ε : Type*}
[topological_space α] [topological_space β] [topological_space γ]
[topological_space δ] [topological_space η] [topological_space ε]
(e : local_homeomorph α β) (f : local_homeomorph β γ)
(e' : local_homeomorph δ η) (f' : local_homeomorph η ε)

end local_homeomorph

end

section preamble_results

section times_cont_diff

/-
To be placed into analysis/calculus/times_cont_diff
-/

variables  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{T : Type*} [normed_group T] [normed_space 𝕜 T]

end times_cont_diff

section

/-
To be placed into geometry/manifold/manifold
-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H]
  {H' : Type*} [topological_space H']

section smooth

/-
Not really sure where this should go. Either on geometry/manifold/times_cont_mdiff
or on a new file.
-/

/-- Smooth means C^∞. I truly believe this definition should exists as writing
`times_cont_mdiff I I' ⊤ f` makes everything unreadable and harder to understand for someone
who does not know Mathlib well. -/
def smooth (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]
(f: M → N) := times_cont_mdiff I I' ⊤ f

def smooth_on (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]
(f: M → N) (s : set M) := times_cont_mdiff_on I I' ⊤ f s

def smooth_in_charts (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]
(f: M → N) := times_cont_mdiff_in_charts I I' ⊤ f

def smooth_in_charts_on (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]
(f: M → N) (s : set M) := times_cont_mdiff_in_charts_on I I' ⊤ f s

variables {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{N : Type*} [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]

lemma smooth_in_charts_id : smooth_in_charts I I (id : M → M) :=
begin
  intros x y,
  rw [function.comp.left_id, set.preimage_id],
  unfold ext_chart_at,
  simp only [model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm, local_homeomorph.coe_coe,
    local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) (chart_mem_atlas H x) (chart_mem_atlas H y)).1,
  simp only [local_homeomorph.trans_to_local_equiv, local_homeomorph.coe_trans, local_homeomorph.symm_to_local_equiv] at h1,
  convert h1 using 1,
  unfold function.comp,
  ext1 z,
  rw set.mem_inter_eq,
  fsplit;
  simp only [local_equiv.trans_source, local_equiv.trans_target, and_imp, model_with_corners.to_local_equiv_coe_symm,
    set.mem_preimage, set.mem_range, local_homeomorph.coe_coe_symm, set.mem_inter_eq, local_equiv.symm_source,
    set.preimage_univ, model_with_corners.target, model_with_corners.source_eq, exists_imp_distrib, set.inter_univ],
  { intros w hw h2 h3, exact ⟨⟨h2, h3⟩, ⟨w, hw⟩⟩, },
  { intros h2 h3 w hw, use w, exacts [hw, h2, h3], }
end

lemma smooth_in_charts_const {n : N} : smooth_in_charts I I' (λ x : M, n) :=
begin
  intros x y,
  unfold function.comp,
  exact times_cont_diff_on_const,
end

lemma tangent_bundle_proj_smooth : smooth_in_charts I.tangent I (tangent_bundle.proj I M) :=
begin
  intros x y,
  simp only [function.comp] with mfld_simps,
  sorry,
end

end smooth

section composition

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{I : model_with_corners 𝕜 E H}
{I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

lemma smooth_on.comp {s : set M} {t : set M'} {f : M → M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s)
  (st : s ⊆ f ⁻¹' t) : smooth_on I I'' (g ∘ f) s :=
times_cont_mdiff_on.comp hg hf st

lemma times_cont_mdiff.comp {n : with_top ℕ} {f : M → M'} {g : M' → M''}
  (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff I I'' n (g ∘ f) :=
begin
  have hs : (set.univ ⊆ f ⁻¹' set.univ), by rw set.preimage_univ,
  have h := (times_cont_mdiff_on_univ.2 hg).comp (times_cont_mdiff_on_univ.2 hf) hs,
  exact times_cont_mdiff_on_univ.1 h,
end

lemma smooth.comp {f : M → M'} {g : M' → M''}
  (hg : smooth I' I'' g) (hf : smooth I I' f) :
  smooth I I'' (g ∘ f) := times_cont_mdiff.comp hg hf

lemma smooth_in_charts.comp {f : M → M'} {g : M' → M''}
  (hg : smooth_in_charts I' I'' g) (hf : smooth_in_charts I I' f) :
  smooth_in_charts I I'' (g ∘ f) := sorry

end composition

end

end preamble_results