-- Copyright (c) 2018 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin, Reid Barton

import category_theory.yoneda
import category_theory.limits.functor_category
import category_theory.limits.types
import category_theory.adjunction
import category_theory.comma
import category_theory.punit

namespace category_theory
open category_theory.limits

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

-- TODO: How much of this should be generalized to a possibly large category?
variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

def presheaf := Cᵒᵖ ⥤ Type v₁
variables {C}

namespace presheaf

section simp
variable (X : presheaf C)

-- @[simp] lemma map_id {c : C} : X.map (𝟙 c) = 𝟙 (X.obj c) := X.map_id c

-- @[simp] lemma map_id' {c : C} :
-- X.map (@category.id C _ c) = 𝟙 (X.obj c) := functor.map_id X c

-- @[simp] lemma map_comp {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
-- X.map (g ≫ f) = (X.map g) ≫ (X.map f) := X.map_comp g f

-- @[simp] lemma map_comp' {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
-- X.map (@category.comp C _ _ _ _ f g) = (X.map g) ≫ (X.map f) := functor.map_comp X g f

end simp

set_option pp.universes true

instance : category.{(max u₁ v₁)} (presheaf C) := by dunfold presheaf; apply_instance

def eval : Cᵒᵖ ⥤ presheaf C ⥤ Type v₁ :=
evaluation _ _

section adjoints
variables {C} {D : Type u₂} [𝒟 : category.{v₁} D]
include 𝒟

def precompose (F : C ⥤ D) : presheaf D ⥤ presheaf C :=
{ obj := λ Y, F.op ⋙ Y,
  map := λ _ _ f, whisker_left _ f }

def left_kan_obj (F : C ⥤ D) : presheaf C → presheaf D :=
_

def left_kan_equiv (F : C ⥤ D) (X Y) : (left_kan_obj F X ⟶ Y) ≃ (X ⟶ (precompose F).obj Y) :=
_

def left_kan (F : C ⥤ D) : presheaf C ⥤ presheaf D :=
adjunction.left_adjoint_of_equiv (left_kan_equiv F) _

def right_kan (F : C ⥤ D) : presheaf C ⥤ presheaf D :=
{ obj := λ X, yoneda.op ⋙ (precompose F).op ⋙ yoneda.obj X,
map := λ _ _ α, whisker_left _ $ whisker_left _ $ yoneda.map α }

-- def right_kan_obj (F : C ⥤ D) : presheaf C → presheaf D :=
-- _

-- def right_kan_equiv (F : C ⥤ D) (X Y) : ((precompose F).obj X ⟶ Y) ≃ (X ⟶ right_kan_obj F Y) :=
-- _

def right_kan_adj (F : C ⥤ D) : adjunction (precompose F) (right_kan F) := _

end adjoints

def presheaf_equivalence : ess_surj (yoneda : presheaf C ⥤ presheaf (presheaf C)) :=
{ obj_preimage := λ X,
  { obj := λ c, _,
    map := _,
    map_id' := _,
    map_comp' := _ },
  iso' := _ }

section restriction_extension
variables {D : Type u₂} [𝒟 : category.{v₁} D]
include 𝒟

def restricted_yoneda (F : C ⥤ D) : D ⥤ presheaf C :=
{ obj := λ d, F.op ⋙ yoneda.obj d,
  map := λ d₁ d₂ g, whisker_left _ $ yoneda.map g }

@[simp] lemma restricted_yoneda_obj (F : C ⥤ D) (d : D) : (restricted_yoneda F).obj d = F.op ⋙ yoneda.obj d := rfl
@[simp] lemma restricted_yoneda_map (F : C ⥤ D) {d₁ d₂ : D} (g : d₁ ⟶ d₂) : (restricted_yoneda F).map g = (whisker_left _ $ yoneda.map g) := rfl

variables [has_colimits.{v} D]

def yoneda_extension (F : C ⥤ D) : presheaf C ⥤ D :=
{ obj := λ X, colimit (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F),
  map := λ X₁ X₂ f, colimit.pre (comma.fst.{v v v v} yoneda (functor.of.obj X₂) ⋙ F) (comma.map_right yoneda $ functor.of.map f),
  map_id' := λ X,
  begin
    erw functor.of.map_id, -- why doesn't this simplify automatically?
    erw colimit.pre_map'
      (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F)
      (comma.map_right_id.{v v v v} yoneda (functor.of.obj X)).hom,
    erw colimit.pre_id,
    erw ← colim.map_comp,
    erw ← colim.map_id,
    congr,
    tidy
  end,
  map_comp' := λ X₁ X₂ X₃ f g,
  begin
    erw colimit.pre_pre
      (comma.fst.{v v v v} yoneda (functor.of.obj X₃) ⋙ F)
      (comma.map_right yoneda (functor.of.map g))
      (comma.map_right yoneda (functor.of.map f)),
    congr
  end }

@[simp] lemma yoneda_extension_obj (F : C ⥤ D) (X : presheaf C) : (yoneda_extension F).obj X = colimit (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F) := rfl
@[simp] lemma yoneda_extension_map (F : C ⥤ D) {X₁ X₂ : presheaf C} (f : X₁ ⟶ X₂) :
(yoneda_extension F).map f = colimit.pre (comma.fst.{v v v v} yoneda (functor.of.obj X₂) ⋙ F) (comma.map_right yoneda $ functor.of.map f) := rfl

end restriction_extension

section map_comap
variables {D : Type v} [small_category D]

def comap (F : C ⥤ D) : presheaf D ⥤ presheaf C :=
restricted_yoneda (F ⋙ yoneda)

-- def comap_obj_obj (F : C ⥤ D) (Y : presheaf D) (c : C) : ((comap F).obj Y).obj c ≅ (F.op ⋙ Y).obj c :=
-- sorry

-- set_option pp.universes true

-- def comap_obj (F : C ⥤ D) (Y : presheaf D) : (map F).obj Y ≅ F.op ⋙ Y :=
-- nat_iso.of_components
--   (λ X, (yoneda_sections_small (F.obj X) Y))
--   (by { intros X₁ X₂ f,
--   have := (yoneda_lemma D).hom.naturality,
--   work_on_goal 1 { exact (F.op.obj X₁, Y) },
--   work_on_goal 1 { exact (F.op.obj X₂, Y) },
--   dsimp at this,
--   have foo := this (F.op.map f, 𝟙 Y),
--   dsimp [yoneda_evaluation] at foo,
--   simp at foo,
--   convert foo; delta ulift_functor; tidy, })

-- { hom :=
--   { app := λ X,
--   begin
--     refine _ ≫ (@yoneda_sections_small C _inst_1 X (functor.op F ⋙ Y)).hom,
--   end },
--   inv := _ }

lemma comap_map (F : C ⥤ D) {Y₁ Y₂ : presheaf D} (g : Y₁ ⟶ Y₂) : (comap F).map g = (whisker_left _ $ yoneda.map g) := rfl

def map' (F : C ⥤ D) : presheaf C ⥤ presheaf D :=
yoneda_extension (F ⋙ yoneda)

lemma map_obj (F : C ⥤ D) (X : presheaf C) :
(map' F).obj X = colimit (comma.fst.{v v v v} yoneda (functor.of.obj X) ⋙ F ⋙ yoneda) := rfl
lemma map_map (F : C ⥤ D) {X₁ X₂ : presheaf C} (f : X₁ ⟶ X₂) :
(map' F).map f = colimit.pre (comma.fst.{v v v v} yoneda (functor.of.obj X₂) ⋙ F ⋙ yoneda) (comma.map_right yoneda $ functor.of.map f) := rfl

end map_comap

end presheaf

end category_theory
