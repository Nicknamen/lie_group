/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.real_instances
import algebra.group.prod
import .prod_manifold
import ..mathlib_times_cont_mdiff.src.geometry.manifold.times_cont_mdiff

noncomputable theory

/-!
# Lie groups

We define Lie groups.

## Main definitions and statements

* `Lie_add_group I G`         : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `Lie_group I G`             : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.

## Implementation notes
Note that this definition is temporary, as manifolds are not yet true manifolds, but really charted spaces.
Moreover a priori, a Lie group here is a manifold with corner.
The fact that it is infact corerless should be a theorem.
-/

section Lie_group

universes u v

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
class Lie_add_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
  (I : model_with_corners 𝕜 E E) (G : Type*) [topological_space G] [manifold E G]
  [smooth_manifold_with_corners I G] [add_group G] : Prop :=
  (smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))
  (smooth_neg : smooth I I (λ a:G, -a))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[to_additive Lie_add_group]
class Lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
  (I : model_with_corners 𝕜 E E) (G : Type*) [topological_space G] [manifold E G]
  [smooth_manifold_with_corners I G] [group G] : Prop :=
  (smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))
  (smooth_inv : smooth I I (λ a:G, a⁻¹))

 /- Why cannot I be made implicit? -/

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]  {I : model_with_corners 𝕜 E E}
{G : Type*} [topological_space G] [manifold E G] [smooth_manifold_with_corners I G] [group G] [Lie_group I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] [finite_dimensional 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [manifold H' M] [smooth_manifold_with_corners I' M]
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E''] [finite_dimensional 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M' : Type*} [topological_space M'] [manifold H'' M'] [smooth_manifold_with_corners I'' M']

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
Lie_group.smooth_mul

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
smooth_mul.comp (hf.prod_mk hg)

@[to_additive]
lemma smooth_mul_left (a : G) : smooth I I (λ b : G, a * b) :=
smooth_mul.comp (smooth_const.prod_mk smooth_id)

@[to_additive]
lemma smooth_mul_right (a : G) : smooth I I (λ b : G, b * a) :=
smooth_mul.comp (smooth_id.prod_mk smooth_const)

/- @[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s := by sorry -/

lemma smooth_pow : ∀ n : ℕ, smooth I I (λ a : G, a ^ n)
| 0 := by simpa using smooth_const
| (k+1) := show smooth I I (λ (a : G), a * a ^ k), from smooth_id.mul (smooth_pow _)

@[to_additive]
lemma smooth_inv : smooth I I (λ x : G, x⁻¹) :=
Lie_group.smooth_inv

@[to_additive]
lemma smooth.inv {f : M → G}
  (hf : smooth I' I f) : smooth I' I (λx, (f x)⁻¹) :=
smooth_inv.comp hf

/- @[to_additive]
lemma smooth_on.inv {f : M → G} {s : set M}
  (hf : smooth_on I' I f s) : smooth_on I' I (λx, (f x)⁻¹) s :=
smooth_inv.comp_smooth_on hf -/

/- Coercion to topological group -/
/- @[to_additive] - how does it work here? -/
instance to_topological_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
  (I : model_with_corners 𝕜 E E) (G : Type*) [topological_space G] [manifold E G]
  [smooth_manifold_with_corners I G] [group G] [h : Lie_group I G]: topological_group G :=
{
  continuous_mul := h.smooth_mul.1,
  continuous_inv := h.smooth_inv.1,
}

/- Instance of product group -/
@[to_additive]
instance prod_Lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]  {I : model_with_corners 𝕜 E E}
{G : Type*} [topological_space G] [manifold E G] [smooth_manifold_with_corners I G] [group G] [h : Lie_group I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] [finite_dimensional 𝕜 E']  {I' : model_with_corners 𝕜 E' E'}
{G' : Type*} [topological_space G'] [manifold E' G'] [smooth_manifold_with_corners I' G'] [group G'] [h' : Lie_group I' G'] :
Lie_group (I.prod I') (G×G') :=
{
  smooth_mul := ((smooth_fst.comp smooth_fst).mul (smooth_fst.comp smooth_snd)).prod_mk
    ((smooth_snd.comp smooth_fst).mul (smooth_snd.comp smooth_snd)),
  smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv,
}

end

end Lie_group