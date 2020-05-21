/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov.
-/
import analysis.calculus.inverse
import analysis.normed_space.complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem.

* `implicit_function_of_complemented`: implicit function defined by `f (g z y) = z`, where
  `f : E → F` is a function strictly differentiable at `a` such that its defivative `f'`
  is surjective and has a `complemented` kernel;

* `implicit_function`: implicit function defined by `f (g z y) = z`, where `f : E → F` is a function
  with finitely dimensional codomain such that `f` is strictly differentiable at `a` and its
  defivative `f'` is surjective;

* `prod_implicit_function`: implicit function defined by `f (x, g(x, z)) = z`, where `f : E × F → G`
  is a strictly differentiable function with invertible derivative `∂f/∂y`.
-/

noncomputable theory

open_locale topological_space
open continuous_linear_map (fst snd subtype_val smul_right ker_prod)
open continuous_linear_equiv (of_bijective)

namespace has_strict_fderiv_at

section generic

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [complete_space F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E}

/-- An auxiliary lemma used to prove the Implicit function theorem for a map with a surjective
derivative `f' : E → F` with fixed projection `proj : E → ker f'`. This lemma states that
`x ↦ (f x, proj (x - a))` has derivative `x ↦ (f' x, proj x)`, and the latter map is a continuous
linear equivalence. -/
lemma implicit_aux_deriv_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  has_strict_fderiv_at (λ x, (f x, classical.some hker (x - a)))
    ((classical.some hker).equiv_prod_of_proj_ker_of_surjective (classical.some_spec hker) hf' :
      E →L[𝕜] F × f'.ker) a :=
hf.prod $ (classical.some hker).has_strict_fderiv_at.comp a ((has_strict_fderiv_at_id a).sub_const a)

section defs

variables (f f')

/-- A local homeomorphism between E` and `F × f'.ker` sending level surfaces of `f`
to horizontal subspaces. -/
def implicit_to_local_homeomorph_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  local_homeomorph E (F × f'.ker) :=
(implicit_aux_deriv_of_complemented hf hf' hker).to_local_homeomorph _

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  F → f'.ker → E :=
function.curry $ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).symm

end defs

@[simp] lemma implicit_to_local_homeomorph_of_complemented_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) (x : E) :
  (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_of_complemented_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤)
  (hker : f'.ker.complemented) (y : f'.ker) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker (y + a) = (f (y + a), y) :=
by simp only [implicit_to_local_homeomorph_of_complemented, to_local_homeomorph_coe,
  add_sub_cancel, classical.some_spec hker]

@[simp] lemma implicit_to_local_homeomorph_of_complemented_self
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker a = (f a, 0) :=
by simpa only [submodule.coe_zero, zero_add]
  using hf.implicit_to_local_homeomorph_of_complemented_ker hf' hker 0

lemma mem_implicit_to_local_homeomorph_of_complemented_source (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  a ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_of_complemented_target (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).target :=
by simpa only [implicit_to_local_homeomorph_of_complemented_self] using
  ((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).map_source $
    (hf.mem_implicit_to_local_homeomorph_of_complemented_source hf' hker))

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_of_complemented_eq (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  ∀ᶠ (p : F × f'.ker) in 𝓝 (f a, 0),
    f (hf.implicit_function_of_complemented f f' hf' hker p.1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker).eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_of_complemented_target hf' hker).mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function_of_complemented f f' hf' hker (f x)
    (hf.implicit_to_local_homeomorph_of_complemented f f' hf' hker x).snd = x :=
(hf.implicit_aux_deriv_of_complemented hf' hker).eventually_left_inverse

lemma to_implicit_function_of_complemented (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (hker : f'.ker.complemented) :
  has_strict_fderiv_at (hf.implicit_function_of_complemented f f' hf' hker (f a))
    (subtype_val f'.ker) 0 :=
begin
  have := (hf.implicit_aux_deriv_of_complemented hf' hker).to_local_inverse,
  simp only [sub_self, continuous_linear_map.map_zero] at this,
  convert this.comp 0
    ((has_strict_fderiv_at_const (f a) 0).prod $ has_strict_fderiv_at_id 0),
  ext x,
  simp [continuous_linear_equiv.eq_symm_apply, classical.some_spec hker]
end

end generic

section finite_dimensional

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] [finite_dimensional 𝕜 F]
  (f : E → F) (f' : E →L[𝕜] F) {a : E}

def implicit_to_local_homeomorph (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  local_homeomorph E (F × f'.ker) :=
by haveI := finite_dimensional.complete 𝕜 F; exact
hf.implicit_to_local_homeomorph_of_complemented f f' hf'
  f'.ker_complemented_of_finite_dimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  F → f'.ker → E :=
function.curry $ (hf.implicit_to_local_homeomorph f f' hf').symm

variables {f f'}

@[simp] lemma implicit_to_local_homeomorph_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) (x : E) :
  (hf.implicit_to_local_homeomorph f f' hf' x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_ker
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) (y : f'.ker) :
  hf.implicit_to_local_homeomorph f f' hf' (y + a) = (f (y + a), y) :=
by apply implicit_to_local_homeomorph_of_complemented_ker

@[simp] lemma implicit_to_local_homeomorph_self
  (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  hf.implicit_to_local_homeomorph f f' hf' a = (f a, 0) :=
by apply implicit_to_local_homeomorph_of_complemented_self

lemma mem_implicit_to_local_homeomorph_source (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) :
  a ∈ (hf.implicit_to_local_homeomorph f f' hf').source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_target (hf : has_strict_fderiv_at f f' a)
  (hf' : f'.range = ⊤) :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph f f' hf').target :=
by apply mem_implicit_to_local_homeomorph_of_complemented_target

/-- `implicit_function_of_complemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_eq (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  ∀ᶠ (p : F × f'.ker) in 𝓝 (f a, 0), f (hf.implicit_function f f' hf' p.1 p.2) = p.1 :=
by apply map_implicit_function_of_complemented_eq

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  ∀ᶠ x in 𝓝 a, hf.implicit_function f f' hf' (f x)
    (hf.implicit_to_local_homeomorph f f' hf' x).snd = x :=
by apply eq_implicit_function_of_complemented

lemma to_implicit_function (hf : has_strict_fderiv_at f f' a) (hf' : f'.range = ⊤) :
  has_strict_fderiv_at (hf.implicit_function f f' hf' (f a))
    (subtype_val f'.ker) 0 :=
by apply to_implicit_function_of_complemented

end finite_dimensional

/-!
### Implicit function theorem for `f : E × F → G`

Now we prove the implicit function theorem for a function `f : E × F → G` that has a derivative
`f' : E × F →L[𝕜] G` in the strict sense and the derivative `∂f/∂y : F →L[𝕜] G` is invertible.
-/

section product

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]

variables [cs : complete_space (E × F)] {f : E × F → G} (f' : E × F →L[𝕜] G) (f'inv : G →L[𝕜] F)
  {p : E × F} (hf : has_strict_fderiv_at f f' p)
  (hf'l : ∀ y : F, f'inv (f' (0, y)) = y) (hf'r : ∀ z : G, f' (0, f'inv z) = z)

/-- Formula for the derivative of an implicit function. -/
def prod_implicit_function_fderiv : (E × G) →L[𝕜] F :=
(f'inv.comp $ continuous_linear_map.snd 𝕜 E G -
      f'.comp ((continuous_linear_map.id 𝕜 E).prod_map 0))

variables {f' f'inv}

@[simp] lemma prod_implicit_function_fderiv_apply (x) :
  prod_implicit_function_fderiv f' f'inv x = f'inv (x.2 - f' (x.1, 0)) := rfl

include hf'r

lemma prod_implicit_fderiv_right_inverse (x : E) (z : G) :
  f' (x, f'inv z) = f' (x, 0) + z :=
by { conv_rhs { rw [← hf'r z] }, simp [← f'.map_add] }

include hf'l

variables (f' f'inv)

/-- Derivative of an auxiliary function used in the proof of the implicit function theorem. -/
def prod_implicit_function_aux_fderiv : (E × F) ≃L[𝕜] (E × G) :=
continuous_linear_equiv.equiv_of_inverse
  ((continuous_linear_map.fst 𝕜 E F).prod f')
  ((continuous_linear_map.fst 𝕜 E G).prod $ prod_implicit_function_fderiv f' f'inv)
  (λ ⟨x, y⟩, by simp [← continuous_linear_map.map_sub, hf'l])
  (λ ⟨x, z⟩, by simp [-continuous_linear_map.map_sub, prod_implicit_fderiv_right_inverse hf'r])

variables {f' f'inv}

include hf

lemma prod_implicit_function_aux_deriv :
  has_strict_fderiv_at (λ x : E × F, (x.1, f x))
    (prod_implicit_function_aux_fderiv f' f'inv hf'l hf'r : (E × F) →L[𝕜] E × G) p :=
has_strict_fderiv_at_fst.prod hf

include cs
variable (f)

/-- Implicit function `g` defined by an equation `f (x, g(x, z)) = z`. -/
def prod_implicit_function (x : E × G) : F :=
((hf.prod_implicit_function_aux_deriv hf'l hf'r).local_inverse _ _ _ x).2

lemma prod_implicit_function_def (x : E × G) :
  hf.prod_implicit_function f hf'l hf'r x =
    ((hf.prod_implicit_function_aux_deriv hf'l hf'r).local_inverse _ _ _ x).2 :=
rfl

lemma to_prod_implicit_function :
  has_strict_fderiv_at (hf.prod_implicit_function f hf'l hf'r)
    (prod_implicit_function_fderiv f' f'inv) (p.1, f p) :=
((hf.prod_implicit_function_aux_deriv hf'l hf'r).to_local_inverse).snd

lemma eventually_apply_fst_prod_implicit_function_eq :
  ∀ᶠ (x : E × G) in 𝓝 (p.1, f p), f (x.1, hf.prod_implicit_function f hf'l hf'r x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_right_inverse.mono $
  λ x hx, by { convert congr_arg prod.snd hx, convert prod.mk.eta,
    exact (congr_arg prod.fst hx).symm }

lemma eventually_prod_implicit_function_eq :
  ∀ᶠ (x : E × F) in 𝓝 p, hf.prod_implicit_function f hf'l hf'r (x.1, f x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_left_inverse.mono $
  λ x hx, congr_arg prod.snd hx

end product

end has_strict_fderiv_at
