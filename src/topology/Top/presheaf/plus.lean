import topology.Top.presheaf.cech

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables {X : Top.{v}}

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_limits.{v} C] [has_colimits.{v} C]

def plus_obj_obj (ℱ : X.presheaf C) (U : (opens X)ᵒᵖ) : C :=
colimit.{v} ((induced_functor (λ 𝒰 : covers_of (unop U), cover.of_sets 𝒰.val)).op ⋙ ℱ.cech_zero)

def plus_obj_map (ℱ : X.presheaf C) (U V : (opens X)ᵒᵖ) (h : U ⟶ V) : plus_obj_obj ℱ U ⟶ plus_obj_obj ℱ V :=
sorry

def plus_obj (ℱ : X.presheaf C) : X.presheaf C :=
{ obj := plus_obj_obj ℱ,
  map := plus_obj_map ℱ,
  map_id' := sorry,
  map_comp' := sorry }

end Top
