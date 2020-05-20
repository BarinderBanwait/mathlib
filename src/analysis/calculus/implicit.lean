import analysis.calculus.inverse
/-! ### Implicit function theorem

Now we prove a version of the implicit function theorem. Suppose that `f : E → F` has derivative
`f' : E →L[𝕜] F` at `a` in the strict sense, and `f'inv : F →L[𝕜] E` is a right inverse of `f'`.
Then there is a local homeomorphism `local_homeomorph E (F × f'.ker)` sending `{x | f x = b}` to
`{(z, y) | z = b}`.

We also repack this `local_homeomorph` as a function `implicit_function : F → f'.ker → E`.  For a
fixed `z ≈ f a`, this function is a local homeomorphism between `f'.ker` and `{x | f x = z}`.

We use the following trick to deduce this theorem from the inverse function theorem. Consider the
function `φ : E → F × f'.ker` given by $$φ(x)=(f(x), x - a - {f'}⁻¹ (f' (x - a)))$$, where
$${f'}⁻¹$$ is a right inverse of `f'`. This function has an invertible derivative at `a`, hence by
the inverse function theorem it is a local homeomorphism.

In the next section we shall prove another version of this theorem dealing with a function `f : E ×
F → G` such that `∂f/∂y` is invertible.
-/

open continuous_linear_map (fst snd subtype_val smul_right)

namespace has_strict_fderiv_at

variables [cs : complete_space E] {f : E → F} {f' : E →L[𝕜] F} {f'inv : F →L[𝕜] E} {a : E}

/-- The map `φ : E → F × f'.ker` given by $$φ(x)=(f(x), x - a - {f'}⁻¹ (f' (x - a)))$$ has
derivative $$φ'(x)=\left(f'(x), x - {f'}⁻¹ (f' x)\right)$$ at `a`. We formulate this fact using much
longer formulas to reuse proofs of `x - {f'}⁻¹ (f' x) ∈ f'.ker` and of the fact that the derivative
is invertible. -/
lemma implicit_aux_has_fderiv (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  has_strict_fderiv_at
    (λ x, (f x, continuous_linear_map.proj_ker_of_right_inverse f' f'inv hf' (x - a)))
    (continuous_linear_equiv.equiv_of_right_inverse f' f'inv hf' : E →L[𝕜] (F × f'.ker)) a :=
hf.prod $ (continuous_linear_map.has_strict_fderiv_at _).comp a
  ((has_strict_fderiv_at_id a).sub_const a)

include cs

section defs

variables (f f' f'inv)

/-- A local homeomorphism between E` and `F × f'.ker` sending level surfaces of `f`
to horizontal subspaces. -/
def implicit_to_local_homeomorph (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') : local_homeomorph E (F × f'.ker) :=
(hf.implicit_aux_has_fderiv hf').to_local_homeomorph _

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicit_function (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') : F → f'.ker → E :=
function.curry $ (hf.implicit_aux_has_fderiv hf').local_inverse _ _ _

end defs

@[simp] lemma implicit_to_local_homeomorph_fst (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') (x : E) :
  ((hf.implicit_to_local_homeomorph f f' f'inv  hf').to_fun x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_ker_snd (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') (y : f'.ker) :
  ((hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun (y + a)).snd = y :=
by simpa only [implicit_to_local_homeomorph, to_local_homeomorph_to_fun, add_sub_cancel]
  using (continuous_linear_map.proj_ker_of_right_inverse_apply_idem _ _ hf' y)

@[simp] lemma implicit_to_local_homeomorph_self (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  (hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun a = (f a, 0) :=
prod.ext rfl $ by simpa using hf.implicit_to_local_homeomorph_ker_snd hf' 0

lemma mem_implicit_to_local_homeomorph_source (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  a ∈ (hf.implicit_to_local_homeomorph f f' f'inv hf').source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_target (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph f f' f'inv hf').target :=
by simpa only [implicit_to_local_homeomorph_self] using
  ((hf.implicit_to_local_homeomorph f f' f'inv hf').map_source $
    (hf.mem_implicit_to_local_homeomorph_source hf'))

/-- `implicit_function` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_eq (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  ∀ᶠ p in 𝓝 (f a, (0 : f'.ker)),
    f (hf.implicit_function f f' f'inv hf' (p : F × f'.ker).1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph f f' f'inv hf').eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_target hf').mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  ∀ᶠ x in 𝓝 a, hf.implicit_function f f' f'inv hf' (f x)
    ((hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun x).snd = x :=
(hf.implicit_aux_has_fderiv hf').eventually_left_inverse

/-- Derivative of the inverse function used to prove the implicit function theorem. -/
lemma to_implicit_function_aux (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  has_strict_fderiv_at (hf.implicit_to_local_homeomorph f f' f'inv hf').inv_fun
    (f'inv.coprod $ subtype_val f'.ker) (f a, 0) :=
hf.implicit_to_local_homeomorph_self hf' ▸
  (hf.implicit_aux_has_fderiv hf').to_local_inverse

lemma to_implicit_function (hf : has_strict_fderiv_at f f' a)
  (hf' : function.right_inverse f'inv f') :
  has_strict_fderiv_at (hf.implicit_function f f' f'inv hf' (f a)) (subtype_val f'.ker) 0 :=
begin
  have := (hf.to_implicit_function_aux hf').comp 0
    ((has_strict_fderiv_at_const (f a) 0).prod $ has_strict_fderiv_at_id 0),
  convert this,
  ext x,
  simp
end

end has_strict_fderiv_at

/-!
### Implicit function theorem for `f : E × F → G`

Now we prove the implicit function theorem for a function `f : E × F → G` that has a derivative
`f' : E × F →L[𝕜] G` in the strict sense and the derivative `∂f/∂y : F →L[𝕜] G` is invertible.
-/

namespace has_strict_fderiv_at

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

/-- Implicit function `g` defined by an equation `f (x, g(x, y)) = z`. -/
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
  ∀ᶠ x in 𝓝 (p.1, f p), f ((x : E × G).1, hf.prod_implicit_function f hf'l hf'r x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_right_inverse.mono $
  λ x hx, by { convert congr_arg prod.snd hx, convert prod.mk.eta,
    exact (congr_arg prod.fst hx).symm }

lemma eventually_prod_implicit_function_eq :
  ∀ᶠ x in 𝓝 p, hf.prod_implicit_function f hf'l hf'r ((x : E × F).1, f x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_left_inverse.mono $
  λ x hx, congr_arg prod.snd hx

end has_strict_fderiv_at
