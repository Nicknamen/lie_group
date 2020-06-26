/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

/-

THIS FILE CONTAINS SCATTERED RESULTS TO BE CORRECTLY PLACED IN MATHLIB

-/

import geometry.manifold.smooth_manifold_with_corners
import ..mathlib_times_cont_mdiff.src.geometry.manifold.times_cont_mdiff

noncomputable theory

section prod

/-
To be placed into topology/contructions
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

def map.diag (A : Type*) : (A → A×A) := (λ a : A, (a, a))

lemma continuous.map_diag : continuous (map.diag α) :=
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

lemma prod_symm :
  (e.prod e').symm = (e.symm.prod e'.symm) :=
by ext x : 1; simp

lemma prod_comp :
  (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
begin
  ext x : 1,
  { simp },
  { simp },
  { ext y,
    rcases y with ⟨a, b⟩,
    simp [local_equiv.trans_source],
    tauto, }
end

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

lemma times_cont_diff_on_fst
{s : set (E×F)} {n : with_top ℕ}: times_cont_diff_on 𝕜 n (prod.fst : E × F → E) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_fst

lemma times_cont_diff_on_snd
{s : set (E×F)} {n : with_top ℕ}: times_cont_diff_on 𝕜 n (prod.snd : E × F → F) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_snd

/-- The product map of two C^n maps is C^n. -/
lemma times_cont_diff_on.map_prod
{s : set E} {t : set T} {n : with_top ℕ} {f : E → F} {g : T → G}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g t) :
  times_cont_diff_on 𝕜 n (prod.map f g) (set.prod s t) :=
begin
    have hs : s.prod t ⊆ (prod.fst) ⁻¹' s :=
    begin
        rintros x ⟨h_x_1, h_x_2⟩,
        exact h_x_1,
    end,
    have ht :s.prod t ⊆ (prod.snd) ⁻¹' t :=
    begin
        rintros x ⟨h_x_1, h_x_2⟩,
        exact h_x_2,
    end,
    exact (hf.comp (times_cont_diff_on_fst) hs).prod (hg.comp (times_cont_diff_on_snd) ht),
    /- Inconsistent notation!!! This should rather be prod_mk. Ask this to Sebastien -/
end

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

@[simp] lemma model_with_corers_prod_coe
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  (I.prod I' : _ × _ → _ × _) = (prod.map I I') := rfl

  @[simp] lemma model_with_corers_prod_coe_symm
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  ((I.prod I').symm : _ × _ → _ × _) = (prod.map I.symm (I').symm) := rfl

lemma times_cont_diff_chart_prod
  {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
  {e : local_homeomorph H H} {e' : local_homeomorph H' H'}
  (h1 : (e ∈ (times_cont_diff_groupoid ⊤ I))) (h2 : (e' ∈ (times_cont_diff_groupoid ⊤ I'))) :
  (e.prod e') ∈ (times_cont_diff_groupoid ⊤ (I.prod I')) :=
begin
  cases h1 with h1 h1_symm,
  cases h2 with h2 h2_symm,
  simp only [] at h1 h1_symm h2 h2_symm,

  split;
  simp only [local_equiv.prod_source, local_homeomorph.prod_to_local_equiv],
  { have h3 := times_cont_diff_on.map_prod h1 h2,

    rw [← model_with_corners.image I _,
        ← model_with_corners.image I' _, set.prod_image_image_eq] at h3,
    rw ← model_with_corners.image (I.prod I') _,

    exact h3, },
  { have h3 := times_cont_diff_on.map_prod h1_symm h2_symm,

    rw [← model_with_corners.image I _,
        ← model_with_corners.image I' _, set.prod_image_image_eq] at h3,
    rw ← model_with_corners.image (I.prod I') _,

    exact h3, }
end

  section smooth

  /-
  Not really sure where this should go. Either on geometry/manifold/times_cont_mdiff
  or on a new file.
  -/

  /-- Smooth means C^∞. I truly believe this definition should exists as writing
  `times_cont_mdiff I I' ⊤ f` makes everything unreadable and harder to understand for someone
  who does not know Mathlib well. -/
  def smooth (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  {M : Type*} [topological_space M] [manifold H M] [smooth_manifold_with_corners I M]
  {N : Type*} [topological_space N] [manifold H' N] [smooth_manifold_with_corners I' N]
  (f: M → N) := times_cont_mdiff I I' ⊤ f

  def smooth_on (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  {M : Type*} [topological_space M] [manifold H M] [smooth_manifold_with_corners I M]
  {N : Type*} [topological_space N] [manifold H' N] [smooth_manifold_with_corners I' N]
  (f: M → N) (s : set M) := times_cont_mdiff_on I I' ⊤ f s

  variables {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
  {M : Type*} [topological_space M] [manifold H M] [smooth_manifold_with_corners I M]
  {N : Type*} [topological_space N] [manifold H' N] [smooth_manifold_with_corners I' N]

  lemma smooth_id : smooth I I (id : M → M) :=
  begin
    refine ⟨continuous_id, λ x y, _⟩,
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

  lemma smooth_const {n : N} : smooth I I' (λ x : M, n) :=
  begin
    refine ⟨continuous_const, _⟩,
    intros x y,
    unfold function.comp,
    exact times_cont_diff_on_const,
  end

  end smooth

section composition

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{I : model_with_corners 𝕜 E H}
{I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [manifold H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [manifold H' M'] [smooth_manifold_with_corners I' M']
{M'' : Type*} [topological_space M''] [manifold H'' M''] [smooth_manifold_with_corners I'' M'']

lemma smooth_on.comp {s : set M} {t : set M'} {f : M → M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s)
  (st : s ⊆ f ⁻¹' t) : smooth_on I I'' (g ∘ f) s :=
times_cont_mdiff_on.comp hg hf st

lemma times_cont_mdiff.comp {n : with_top ℕ} {f : M → M'} {g : M' → M''}
  (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff I I'' n (g ∘ f) :=
begin
  have hs : (set.univ ⊆ f ⁻¹' set.univ) := by rw set.preimage_univ,
  have h := times_cont_mdiff_on.comp (times_cont_mdiff_on_univ.2 hg) (times_cont_mdiff_on_univ.2 hf) hs,
  exact times_cont_mdiff_on_univ.1 h,
end

lemma smooth.comp {f : M → M'} {g : M' → M''}
  (hg : smooth I' I'' g) (hf : smooth I I' f) :
  smooth I I'' (g ∘ f) := by exact times_cont_mdiff.comp hg hf

end composition

end

end preamble_results