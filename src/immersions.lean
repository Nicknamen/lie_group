/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import .lie_group
import .local_diffeomorph

noncomputable theory

section

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


variables {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/- The most general definition of immersion, for functions that are not necessarily smooth. -/
structure immersion (f : M → M') : Prop :=
  (mdifferentiable : mdifferentiable I I' f)
  (injetive_mdiff_at_each_point : ∀ x : M, function.injective (mfderiv I I' f x))

structure times_cont_mdiff_immersion (n : with_top ℕ) (f : M → M') : Prop :=
  (times_cont_mdiff: times_cont_mdiff I I' n f)
  (injetive_mdiff_at_each_point : ∀ x : M, function.injective (mfderiv I I' f x))

structure smooth_immersion (f : M → M') : Prop :=
  (smooth : smooth I I' f)
  (injetive_mdiff_at_each_point : ∀ x : M, function.injective (mfderiv I I' f x))

structure times_cont_mdiff_embedding (n : with_top ℕ) (f : M → M')
  extends embedding f : Prop :=
  (times_cont_mdiff_immersion: times_cont_mdiff_immersion I I' n f)

structure smooth_embedding (f : M → M')
  extends embedding f : Prop :=
  (smooth_immersion : smooth_immersion I I' f)

/- Is it true that C^1 → mdifferentiable? -/
lemma smooth_immersion_is_immersion (f : M → M') :
  (smooth_immersion I I' f) → (immersion I I' f) :=
sorry

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

/- Note that the following definition is not the standard definition of submanifold, but it 
is the definition of subobject in the category of manifolds. -/
class is_times_cont_mdiff_submanifold {n : with_top ℕ} (s : set M) : Prop :=
(smooth_times_cont_mdiff_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, times_cont_mdiff I' I n f ∧ set.image f set.univ = s)))))

class is_smooth_submanifold (s : set M) : Prop :=
(smooth_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, (smooth I' I f) ∧ set.image f set.univ = s)))))

class is_immersed_submanifold (s : set M) : Prop :=
(immersed_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, immersion I' I f ∧ set.image f set.univ = s)))))

class is_times_cont_mdiff_immersed_submanifold {n : with_top ℕ} (s : set M) : Prop :=
(immersed_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, times_cont_mdiff_immersion I' I n f ∧ set.image f set.univ = s)))))

class is_smooth_immersed_submanifold (s : set M) : Prop :=
(immersed_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, smooth_immersion I' I f ∧ set.image f set.univ = s)))))

class is_times_cont_mdiff_emedded_submanifold {n : with_top ℕ} (s : set M) : Prop :=
(embedded_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, times_cont_mdiff_embedding I' I n f ∧ set.image f set.univ = s)))))

class is_smooth_embedded_submanifold (s : set M) : Prop :=
(embedded_image : ∃ E' [normed_group E'] [normed_space 𝕜 E'], (∃ H' [topological_space H'], (∃ I' : model_with_corners 𝕜 E' H',
(∃ N [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N],
(∃ f : N → M, smooth_embedding I' I f ∧ set.image f set.univ = s)))))

end

section

/- smooth subgroups -/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
(I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G] [Lie_group I G]
{G' : Type*} [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G'] [group G'] [Lie_group I' G']
{A : Type*} [topological_space A] [charted_space E A] [smooth_manifold_with_corners I A] [add_group A] [Lie_add_group I A]
{A' : Type*} [topological_space A'] [charted_space E' A'] [smooth_manifold_with_corners I' A'] [add_group A'] [Lie_add_group I' A']


class is_smooth_add_subgroup (s : set A) extends is_add_subgroup s, is_smooth_submanifold I s : Prop

class is_smooth_immersed_add_subgroup (s : set A) extends is_add_subgroup s, is_smooth_immersed_submanifold I s : Prop

class is_smooth_embedded_add_subgroup (s : set A) extends is_add_subgroup s, is_smooth_embedded_submanifold I s : Prop

@[to_additive is_smooth_add_subgroup]
class is_smooth_subgroup (s : set G) extends is_subgroup s, is_smooth_submanifold I s : Prop

@[to_additive is_smooth_immersed_add_subgroup]
class is_smooth_immersed_subgroup (s : set G) extends is_subgroup s, is_smooth_immersed_submanifold I s : Prop

@[to_additive is_smooth_embedded_add_subgroup]
class is_smooth_embedded_subgroup (s : set G) extends is_subgroup s, is_smooth_embedded_submanifold I s : Prop


/- lemma additive.is_smooth_add_subgroup
  {G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [add_group G] [Lie_add_group I G]
  (s : set G) : ∀ [is_smooth_subgroup I s], @is_smooth_add_subgroup 𝕜 _ E _ _ I (additive G) _ _ _ _ _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩-/

/-@[to_additive]-/
lemma smooth_subgroup_is_immersed (s : set G) [is_smooth_subgroup I s] : is_smooth_immersed_subgroup I s :=
begin
  sorry,
end

lemma subgroup_smooth_iff_closed (s : set G) [is_subgroup s] :
  is_smooth_embedded_subgroup I s ↔ is_closed s :=
begin
  sorry,
end

lemma nhd_of_one_generates_connected_Lie_group [connected_space G] (U : set G) [is_open U] :
  set.mem 1 U → subgroup.closure U = ⊤ :=
begin
  sorry,
end

def connected_component_of_id (G : Type*) [topological_space G] [group G] [topological_group G] :=
 connected_component (1 : G)

lemma connected_component_of_id_is_normal_subgroup [charted_space E G] [smooth_manifold_with_corners I G] [group G] [Lie_group I G] :
normal_subgroup (connected_component_of_id G) :=
begin
  sorry,
end

lemma Lie_group_hom_surj_at_id_imp_surj [connected_space G'] (f : Lie_group_morphism I I' G G') :
  function.surjective (mfderiv I I' f (1 : G)) → function.surjective f :=
begin
  sorry,
end

end

section

def continuous_sections {B : Type*} [topological_space B] {E : Type*} [topological_space E]
(F : Type*) [topological_space F] (p : E → B) /-[is_topological_fiber_bundle F p]-/ :=
{f : B → E // p ∘ f = id ∧ continuous f}

open set

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E_B : Type*} [normed_group E_B] [normed_space 𝕜 E_B]
{E_F : Type*} [normed_group E_F] [normed_space 𝕜 E_F]
{E_Z : Type*} [normed_group E_Z] [normed_space 𝕜 E_Z]
{H_B : Type*} [topological_space H_B] (I_B : model_with_corners 𝕜 E_B H_B)
{H_F : Type*} [topological_space H_F] (I_F : model_with_corners 𝕜 E_F H_F)
{H_Z : Type*} [topological_space H_Z] (I_Z : model_with_corners 𝕜 E_Z H_Z)
{B : Type*} [topological_space B] [charted_space H_B B] [smooth_manifold_with_corners I_B B]
{Z : Type*} [topological_space Z] [charted_space H_Z Z] [smooth_manifold_with_corners I_Z Z]
{F : Type*} [topological_space F] [charted_space H_F F] [smooth_manifold_with_corners I_F F]
(proj : Z → B)

variable (F)

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
structure smooth_bundle_trivialization extends local_times_diffeomorph I_Z (I_B.prod I_F) Z (B × F) ⊤ :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = set.prod base_set univ)
(proj_to_fun   : ∀ p ∈ source, (to_fun p).1 = proj p)

instance : has_coe_to_fun (smooth_bundle_trivialization I_B I_F I_Z F proj) := ⟨_, λ e, e.to_fun⟩

@[simp, mfld_simps] lemma smooth_bundle_trivialization.coe_coe (e : smooth_bundle_trivialization I_B I_F I_Z F proj) (x : Z) :
  e.to_local_diffeomorph x = e x := rfl

@[simp, mfld_simps] lemma smooth_bundle_trivialization.coe_mk (e : local_diffeomorph I_Z (I_B.prod I_F) Z (B × F)) (i j k l m) (x : Z) :
  (bundle_trivialization.mk e i j k l m : bundle_trivialization F proj) x = e x := rfl

variables {I_B} {I_F} {I_Z} {F} {proj}

def smooth_bundle_trivialization.to_bundle_trivialization (e : smooth_bundle_trivialization I_B I_F I_Z F proj) : bundle_trivialization F proj :=
{ base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := e.source_eq,
  target_eq := e.target_eq,
  proj_to_fun := e.proj_to_fun,
  .. e.to_local_diffeomorph.to_local_homeomorph }

instance smooth_bundle_triv_to_bunlde_triv : has_coe (smooth_bundle_trivialization I_B I_F I_Z F proj) (bundle_trivialization F proj) :=
⟨λ e, e.to_bundle_trivialization⟩

variables (I_B) (I_F) (I_Z) (F) (proj)

/-- A smooth fiber bundle with fiber F over a base B is a space projecting on B for which the
fibers are all diffeomorphic to F, such that the local situation around each point is a direct
product. -/
def is_smooth_fiber_bundle : Prop :=
∀ x : Z, ∃e : smooth_bundle_trivialization I_B I_F I_Z F proj, x ∈ e.source

instance smooth_fiber_bundle_is_topological_fiber_bundle : has_coe (is_smooth_fiber_bundle I_B I_F I_Z F proj) (is_topological_fiber_bundle F proj) :=
⟨λ h,
begin
  intro x,
  cases h x with e h_e,
  use [e, h_e],
end ⟩

variables {I_F} {F}

def smooth_sections /-[is_topological_fiber_bundle F proj]-/ :=
  {f : B → Z // proj ∘ f = id ∧ smooth I_B I_Z f}

instance : has_coe_to_fun (smooth_sections I_B I_Z proj) := ⟨_, subtype.val⟩

variables {f g : smooth_sections I_B I_Z proj}

namespace smooth_sections

variables {I_B} {I_F} {I_Z} {F} {proj}

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
subtype.eq $ funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨λ h, λ x, h ▸ rfl, ext⟩

end smooth_sections

end

section

open topological_space set

namespace basic_smooth_bundle_core

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
(Z : basic_smooth_bundle_core I M F)

/-- Local diffeomorphism version of the trivialization change. -/
def triv_change (i j : atlas H M) : local_diffeomorph (I.prod (model_with_corners_self 𝕜 F)) (I.prod (model_with_corners_self 𝕜 F)) (M × F) (M × F) :=
{ source      := set.prod (Z.to_topological_fiber_bundle_core.base_set i ∩ Z.to_topological_fiber_bundle_core.base_set j) univ,
  target      := set.prod (Z.to_topological_fiber_bundle_core.base_set i ∩ Z.to_topological_fiber_bundle_core.base_set j) univ,
  to_fun      := λp, ⟨p.1, Z.to_topological_fiber_bundle_core.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, Z.to_topological_fiber_bundle_core.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.to_topological_fiber_bundle_core.coord_change_comp, Z.to_topological_fiber_bundle_core.coord_change_self],
    { exact hx.1 },
    { simp only [mem_inter_eq, base_set, subtype.val_eq_coe],
      cases hx, cases j, cases i, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { assumption }, assumption }, assumption, }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.to_topological_fiber_bundle_core.coord_change_comp, Z.to_topological_fiber_bundle_core.coord_change_self],
    { exact hx.2 },
    { simp only [mem_inter_eq, base_set, subtype.val_eq_coe],
      cases hx, cases j, cases i, dsimp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { assumption }, assumption }, assumption, },
  end,
  open_source :=
    is_open_prod (is_open_inter (Z.to_topological_fiber_bundle_core.is_open_base_set i) (Z.to_topological_fiber_bundle_core.is_open_base_set j)) is_open_univ,
  open_target :=
    is_open_prod (is_open_inter (Z.to_topological_fiber_bundle_core.is_open_base_set i) (Z.to_topological_fiber_bundle_core.is_open_base_set j)) is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (Z.to_topological_fiber_bundle_core.coord_change_continuous i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (Z.to_topological_fiber_bundle_core.coord_change_continuous j i),
  smooth_to_fun := sorry,
  smooth_inv_fun := sorry,}

/-- Local trivialization of a smooth bundle created from core, as a local diffeomorphism. -/
def local_triv (i : atlas H M) : local_homeomorph Z.to_topological_fiber_bundle_core.total_space (M × F) := sorry

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv_ext (i :  atlas H M) : smooth_bundle_trivialization I (model_with_corners_self 𝕜 F) (I.prod (model_with_corners_self 𝕜 F)) F Z.to_topological_fiber_bundle_core.proj := sorry

end basic_smooth_bundle_core

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(F : Type*) [normed_group F] [normed_space 𝕜 F]
(Z : basic_smooth_bundle_core I M F)

def basic_smooth_bundle_core.total_space := Z.to_topological_fiber_bundle_core.total_space /- Not working! -/
def basic_smooth_bundle_core.proj : Z.to_topological_fiber_bundle_core.total_space → M := Z.to_topological_fiber_bundle_core.proj /- Not working! -/

/-- A smooth fiber bundle constructed from core is indeed a smooth fiber bundle. -/
theorem is_smooth_fiber_bundle_from_core : is_smooth_fiber_bundle I (model_with_corners_self 𝕜 F) (I.prod (model_with_corners_self 𝕜 F)) F Z.to_topological_fiber_bundle_core.proj :=
λx, ⟨Z.local_triv_ext (Z.to_topological_fiber_bundle_core.index_at (Z.to_topological_fiber_bundle_core.proj x)), by sorry⟩

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

lemma tangent_bundle_is_smooth_fiber_bundle :
  is_smooth_fiber_bundle I (model_with_corners_self 𝕜 E) I.tangent E (tangent_bundle.proj I M) :=
  is_smooth_fiber_bundle_from_core E _

end

section

namespace vector_bundle

variables (𝕜 : Type*) {B : Type*} (F : Type*) {Z : Type*}
  [topological_space B] [topological_space Z] [normed_field 𝕜]
  [topological_space F] [add_comm_group F] [module 𝕜 F] [topological_module 𝕜 F] (proj : Z → B)
  [∀ (x : B), add_comm_group {y : Z // proj y = x}] [∀ (x : B), module 𝕜 {y : Z // proj y = x}]
  [∀ (x : B), topological_module 𝕜 {y : Z // proj y = x}]

structure vector_bundle_trivialization extends bundle_trivialization F proj :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ (y : {y : Z // proj y = x}), (to_fun y).2))

def is_topological_vector_bundle : Prop :=
∀ x : Z, ∃e : vector_bundle_trivialization 𝕜 F proj, x ∈ e.source

variables {𝕜} {F} {proj}

def topological_vector_bundle.to_topological_fiber_bundle (V : is_topological_vector_bundle 𝕜 F proj)
: is_topological_fiber_bundle F proj :=
begin
  intro x,
  have V_triv := V x,
  cases V_triv with T h_T,
  use T.to_bundle_trivialization,
  exact h_T,
end

instance topological_vector_bundle_to_topological_bundle :
  has_coe (is_topological_vector_bundle 𝕜 F proj) (is_topological_fiber_bundle F proj) :=
⟨λ V, topological_vector_bundle.to_topological_fiber_bundle V⟩

end vector_bundle

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E_B : Type*} [normed_group E_B] [normed_space 𝕜 E_B]
{E_Z : Type*} [normed_group E_Z] [normed_space 𝕜 E_Z]
{H_B : Type*} [topological_space H_B] (I_B : model_with_corners 𝕜 E_B H_B)
{H_Z : Type*} [topological_space H_Z] (I_Z : model_with_corners 𝕜 E_Z H_Z)
{B : Type*} [topological_space B] [charted_space H_B B] [smooth_manifold_with_corners I_B B]
(F : Type*) [normed_group F] [normed_space 𝕜 F]
{Z : Type*} [topological_space Z] [charted_space H_Z Z] [smooth_manifold_with_corners I_Z Z]
(proj : Z → B)
[∀ (x : B), add_comm_group {y : Z // proj y = x}] [∀ (x : B), module 𝕜 {y : Z // proj y = x}]
[∀ (x : B), topological_module 𝕜 {y : Z // proj y = x}]

structure smooth_vector_bundle_trivialization extends smooth_bundle_trivialization I_B (model_with_corners_self 𝕜 F) I_Z F proj :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ (y : {y : Z // proj y = x}), (to_fun y).2))

def is_smooth_vector_bundle : Prop :=
∀ x : Z, ∃ e : smooth_vector_bundle_trivialization I_B I_Z F proj, x ∈ e.source

instance add_comm_group_section_of_vector_bundle [h : ∀ (x : B), add_comm_group {y : Z // proj y = x}] : add_comm_group (smooth_sections I_B I_Z proj) :=
{ add := λ f g, ⟨λ x, by exact
  ((⟨f x, congr_fun f.property.1 x⟩ : {y : Z // proj y = x}) + (⟨g x, congr_fun g.property.1 x⟩ : {y : Z // proj y = x}) : {y : Z // proj y = x}),
    begin
      ext,
      let sum := ((⟨f x, congr_fun f.property.1 x⟩ : {y : Z // proj y = x}) + (⟨g x, congr_fun g.property.1 x⟩ : {y : Z // proj y = x}) : {y : Z // proj y = x}),
      exact sum.property,
    end,
    begin
      sorry,
    end⟩,
  add_assoc :=
  begin
    sorry,
  end,
  zero := ⟨λ x : B, (h x).zero, by { ext, exact (h x).zero.property, },
  begin
    simp only [smooth, times_cont_mdiff],
    split,
    {
      sorry,
    },
    {
      sorry,
    }
  
  end⟩,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry, }
end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

def F : Π x : M, {y : tangent_bundle I M // tangent_bundle.proj I M y = x} → tangent_space I x :=
begin
  intro x,
  intro y,
  have f := (tangent_bundle_core I M).to_topological_fiber_bundle_core.local_triv,
  unfold tangent_space,
end

def G : Π x : M, tangent_space I x → {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
sorry,

instance add_comm_group_fiber_tangent_bundle : ∀ (x : M), add_comm_group {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ add := λ a b, G x (F x a + F x b),
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry, }

#check distrib_mul_action

instance vector_space_fiber_tangent_bundle : ∀ (x : M), module 𝕜 {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  one_smul := sorry,
  mul_smul := sorry,
  add_smul := sorry,
  zero_smul := sorry, }

instance topological_vector_space_fiber_tangent_bundle : ∀ (x : M), topological_module 𝕜 {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ continuous_smul := sorry, }

lemma tangent_bundle_is_smooth_vector_bundle :
  is_smooth_vector_bundle I I.tangent E (tangent_bundle.proj I M) :=
begin
  intro x,
  sorry,
end

end

end