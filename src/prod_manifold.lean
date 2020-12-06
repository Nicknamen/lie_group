/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import .preamble_results

noncomputable theory

/-!
# Lie groups

We define product manifolds and prove smoothness of the classical maps associated with products.

## Main definitions and statements

* `smooth.prod_map`         : `prod_map` is always smooth.
* `smooth_fst`              : `prod.fst` is always smooth.
* `smooth_snd`              : `prod.snd` is always smooth.
* `smooth.prod_mk`          : `prod_mk` is always smooth.
* `smooth_iff_proj_smooth`  : A map is smooth iff its projections are.
-/

section prod_charted_space


section prod_charted_space

variables {H : Type*} [topological_space H]
{M : Type*} [topological_space M] [charted_space H M]
{H' : Type*} [topological_space H']
{M' : Type*} [topological_space M'] [charted_space H' M']
{x : M×M'}

/-@[simp] lemma chart_of_prod_eq_prod_of_charts_coe :
  (chart_at (H×H') x : M × M' → H × H') = (prod.map (chart_at H x.fst) (chart_at H' x.snd)) := rfl

@[simp] lemma chart_of_prod_eq_prod_of_charts_coe_symm :
  ((chart_at (H×H') x).symm : H × H' → M × M') = (prod.map (chart_at H x.fst).symm (chart_at H' x.snd).symm) := rfl

@[simp] lemma chart_of_prod_eq_prod_of_charts_coe_to_local_equiv_trans {α : Type*} {β : Type*}
  {e : local_equiv H α} {e' : local_equiv H' β} :
  (chart_at (H×H') x).to_local_equiv.trans (e.prod e') =
  (((chart_at H x.fst).to_local_equiv.trans e).prod ((chart_at H' x.snd).to_local_equiv.trans e')) :=
begin
  cases x,
  ext1,
  {refl,},
  { intro y, refl, },
  { ext1 z,
    cases z,
    simp only [local_homeomorph.prod_to_local_equiv, local_homeomorph.trans_to_local_equiv, set.prod_mk_mem_set_prod_eq,
      local_equiv.prod_source],
    fsplit,
    { rintro ⟨⟨h1, h2⟩, h3, h4⟩, exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, },
    { rintro ⟨⟨h1, h2⟩, h3, h4⟩, exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, } }
end

@[simp] lemma chart_of_prod_eq_prod_of_charts_coe_trans {α : Type*} {β : Type*} [topological_space α] [topological_space β]
{e : local_homeomorph H α} {e' : local_homeomorph H' β} :
(chart_at (H×H') x).trans (e.prod e') = ((chart_at H x.fst).trans e).prod ((chart_at H' x.snd).trans e') :=
/- Same proof as above! How can I use it?-/
begin
  cases x,
  ext1,
  {refl,},
  { intro y, refl, },
  { ext1 z,
    cases z,
    simp only [local_homeomorph.prod_to_local_equiv, local_homeomorph.trans_to_local_equiv, set.prod_mk_mem_set_prod_eq,
      local_equiv.prod_source],
    fsplit,
    { rintro ⟨⟨h1, h2⟩, h3, h4⟩, exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, },
    { rintro ⟨⟨h1, h2⟩, h3, h4⟩, exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, } }
end-/

end prod_charted_space

section smooth

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F' G'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

lemma smooth_in_charts.prod_map {f : M → M'} {g : N → N'} (hf : smooth_in_charts I I' f) (hg : smooth_in_charts J J' g) :
  smooth_in_charts (I.prod J) (I'.prod J') (prod.map f g) :=
begin
  intros x y,
  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe],
  have f_smooth_at := hf x.fst y.fst,
  have g_smooth_at := hg x.snd y.snd,
  clear hf hg,
  have h := f_smooth_at.map_prod g_smooth_at,
  clear f_smooth_at g_smooth_at,
  simp only [function.comp, ext_chart_at, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe] at h,
  convert h using 1,
  clear h,

  ext1 z,
  simp only [local_equiv.trans_source, local_equiv.trans_target, model_with_corners.to_local_equiv_coe_symm, set.mem_preimage,
    set.mem_range, set.mem_inter_eq, set.mem_prod,
    set.preimage_univ, model_with_corners.target, model_with_corners.source_eq, prod.map_mk, prod.exists, set.inter_univ],
  split,
  { rintro ⟨⟨⟨⟨a, b⟩, rfl⟩, h1, h2⟩, h3, h4⟩,
    rw prod.map_fst at h3,
    rw prod.map_snd at h4,
    exact ⟨⟨⟨⟨a, rfl⟩, h1⟩, h3⟩, ⟨⟨b, rfl⟩, h2⟩, h4⟩, },
  { rintro ⟨⟨⟨⟨h, hh⟩, h2⟩, h3⟩, ⟨⟨⟨g, hg⟩, h5⟩, h6⟩⟩,
    sorry,
    /-refine ⟨⟨⟨h, g, _⟩, ⟨h2, h5⟩⟩, ⟨h3, h6⟩⟩,
    { ext, exacts [hh, hg], }-/ }
end

lemma smooth_in_charts_fst : smooth_in_charts (I.prod J) I (@prod.fst M N) :=
begin
  intros x y,
  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm,
    model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J)) (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (y, x.snd))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans (chart_at (model_prod H G) (y, x.snd)).to_local_equiv).source ∩ set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (y, x.snd)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (y, x.snd)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  begin
    simp only [set.subset_univ, set.preimage_univ],
  end,
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_fst) h1 hs,
  simp only [function.comp, prod.map, model_with_corners_prod_coe_symm, local_homeomorph.trans_to_local_equiv,
    local_homeomorph.coe_trans, model_with_corners_prod_coe, local_homeomorph.symm_to_local_equiv] at h2,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [prod.map, set.mem_preimage, set.mem_range, set.mem_inter_eq, prod.exists],
  fsplit,
  { rintro ⟨⟨⟨⟨a, h_a⟩, b, h_b⟩, h1, h2⟩, h3, h4⟩,
    simp only [model_with_corners.to_local_equiv_coe_symm, model_with_corners_prod_coe_symm, prod.map_fst] at h1 h2,
    rw local_equiv.symm_target at h3,
    simp only [set.mem_univ, set.preimage_univ, model_with_corners.source_eq] at h4,
    cases z,
    simp only [prod.map_mk] at h_a h_b h1 h2 h3,
    refine ⟨⟨⟨h1, h2⟩, _⟩, _⟩,
    { simp only [set.mem_preimage, local_homeomorph.coe_coe_symm, local_equiv.symm_symm, prod.map_mk],
      refine ⟨h3, _⟩,
      apply local_homeomorph.map_target, /- WHY DID NOT SIMP DO IT BY ITSELF? IT TOOK ME TWO DAYS-/
      exact h2, },
    { use [a, b], ext1, exacts [h_a, h_b], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, w, g, rfl⟩,
    repeat {rw model_with_corners.left_inv at h1 h2},
    simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, model_with_corners.left_inv] at h3 h4,
    refine ⟨⟨_, _⟩,_⟩,
    { /-use [w.1, g],-/ sorry, },
    { simp only [model_with_corners.to_local_equiv_coe_symm, set.mem_preimage, model_with_corners_prod_coe_symm,
        model_with_corners.left_inv, prod.map_mk],
      exact ⟨h1, h2⟩, },
    { simp only [local_equiv.trans_source, local_homeomorph.prod_coe, local_homeomorph.prod_symm, prod_charted_space_chart_at,
 model_with_corners_prod_coe_symm, set.preimage_univ, model_with_corners.left_inv, model_with_corners.source_eq,
 prod.map_mk, set.inter_univ],
      exact h3, } }
end

lemma smooth_in_charts_snd : smooth_in_charts (I.prod J) J (@prod.snd M N) :=
begin
  intros x y,
  simp only [function.comp, ext_chart_at, prod.map, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, model_with_corners_prod_coe_symm, local_equiv.coe_trans, local_equiv.coe_trans_symm,
    model_with_corners.to_local_equiv_coe],
  have h1 := (has_groupoid.compatible (times_cont_diff_groupoid ⊤ (I.prod J)) (chart_mem_atlas (H×G) x) (chart_mem_atlas (H×G) (x.fst, y))).1,
  let s := (prod.map (I.symm) (J.symm) ⁻¹'
    ((chart_at (model_prod H G) x).to_local_equiv.symm.trans (chart_at (model_prod H G) (x.fst, y)).to_local_equiv).source ∩
  set.range (prod.map I J)),
  have hs : (s ⊆ (λ (x_1 : E × F), (I ((chart_at (model_prod H G) (x.fst, y)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).fst,
    J ((chart_at (model_prod H G) (x.fst, y)) (((chart_at (model_prod H G) x).symm) ((I.symm) x_1.fst, (J.symm) x_1.snd))).snd)) ⁻¹' (set.univ)) :=
  by simp only [set.subset_univ, set.preimage_univ],
  have h2 := times_cont_diff_on.comp (times_cont_diff.times_cont_diff_on times_cont_diff_snd) h1 hs,
  simp only [function.comp, prod.map, model_with_corners_prod_coe_symm, local_homeomorph.trans_to_local_equiv,
    local_homeomorph.coe_trans, model_with_corners_prod_coe, local_homeomorph.symm_to_local_equiv] at h2,
  convert h2 using 1,
  clear h1 hs h2,

  ext1 z,
  simp only [prod.map, set.mem_preimage, set.mem_range, set.mem_inter_eq, prod.exists],
  split,
  { rintro ⟨⟨⟨⟨a, h_a⟩, b, h_b⟩, h1, h2⟩, h3, h4⟩,
    simp only [model_with_corners.to_local_equiv_coe_symm, model_with_corners_prod_coe_symm, prod.map_fst] at h1 h2,
    rw local_equiv.symm_target at h3,
    simp only [set.mem_univ, set.preimage_univ, model_with_corners.source_eq] at h4,
    cases z,
    simp only [prod.map_mk] at h_a h_b h1 h2 h3,
    refine ⟨⟨⟨h1, h2⟩, ⟨_, h3⟩⟩, _⟩,
    { simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, prod.map_mk],
      apply local_homeomorph.map_target,
      exact h1, },
    { use [a, b], ext1, exacts [h_a, h_b], } },
  { rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, w, g, rfl⟩,
    repeat {rw model_with_corners.left_inv at h1 h2},
    simp only [local_homeomorph.coe_coe_symm, local_equiv.symm_symm, model_with_corners.left_inv] at h3 h4,
    sorry,
    /-refine ⟨⟨⟨⟨w, rfl⟩, ⟨g, rfl⟩⟩, _⟩, _⟩,
    { simp only [model_with_corners.to_local_equiv_coe_symm, set.mem_preimage, model_with_corners_prod_coe_symm,
        model_with_corners.left_inv, prod.map_mk],
        exact ⟨h1, h2⟩, },
    { cases x,
      simp only [model_with_corners.left_inv],
      refine ⟨h4, _⟩,
      simp only [model_with_corners.source_eq], }-/ }
end

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

lemma smooth_in_charts.prod_mk {f : M → M'} {g : M → N'} (hf : smooth_in_charts I I' f) (hg : smooth_in_charts I J' g) :
  smooth_in_charts I (I'.prod J') (λx, (f x, g x)) :=
begin
  intros x y,
  simp only [function.comp, model_with_corners_prod_to_local_equiv] with mfld_simps,
  let s := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹' (f ⁻¹' (ext_chart_at I' y.fst).source)),
  let t := ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm) ⁻¹' (g ⁻¹' (ext_chart_at J' y.snd).source)),
  let inter := s ∩ t,
  have hs : (inter ⊆ s) := by exact set.inter_subset_left s t,
  have ht : (inter ⊆ t) := by exact set.inter_subset_right s t,
  have f_smooth_at := times_cont_diff_on.mono (hf x y.fst) hs,
  have g_smooth_at := times_cont_diff_on.mono (hg x y.snd) ht,
  clear hf hg,
  have h := times_cont_diff_on.prod f_smooth_at g_smooth_at,
  clear f_smooth_at g_smooth_at,
  simp only [function.comp, ext_chart_at, model_with_corners.to_local_equiv_coe_symm, local_homeomorph.coe_coe_symm,
    local_homeomorph.coe_coe, local_equiv.coe_trans, local_equiv.coe_trans_symm, model_with_corners.to_local_equiv_coe] at h,

  convert h using 1,
  clear h,
  /- Why does unfold s not work? I don't want to use change. -/
  simp only [inter, s, t, function.comp] with mfld_simps,

  ext1 z,
  fsplit,
  { rintro ⟨⟨⟨w, rfl⟩, h1⟩, h2, h3⟩, exact ⟨⟨⟨⟨w, rfl⟩, h1⟩, h2⟩, ⟨⟨w, rfl⟩, h1⟩, h3⟩, },
  { rintro ⟨⟨⟨⟨w, rfl⟩, h1⟩, h2⟩, ⟨⟨v, h_v⟩, h3⟩, h4⟩, refine ⟨⟨⟨w, rfl⟩, h1⟩, h2, h4⟩, }
end

lemma smooth_in_charts_iff_proj_smooth_in_charts {f : M → M' × N'} :
  (smooth_in_charts I (I'.prod J') f) ↔ (smooth_in_charts I I' (prod.fst ∘ f)) ∧ (smooth_in_charts I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth_in_charts.comp smooth_in_charts_fst h, smooth_in_charts.comp smooth_in_charts_snd h⟩ },
  { rintro ⟨h_fst, h_snd⟩,
    have h := smooth_in_charts.prod_mk h_fst h_snd,
    simp only [prod.mk.eta] at h, /- What is simp doing? I would like to find a way to replace it. -/
    exact h, }
end

lemma smooth_in_charts.map_diag : smooth_in_charts I (I.prod I) (map.diag M) :=
  smooth_in_charts_id.prod_mk smooth_in_charts_id

end smooth

end prod_charted_space