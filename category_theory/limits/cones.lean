-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.types
import category_theory.isomorphism
import category_theory.whiskering

open category_theory

universes u v
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables (J : Type v) [small_category J]

namespace category_theory.functor

def const (X : C) : J ⥤ C :=
{ obj := λ j, X,
  map' := λ j j' f, 𝟙 X }

instance const_coe : has_coe C (J ⥤ C) := ⟨ const J ⟩

@[simp] lemma const_obj (X : C) (j : J) : (X : J ⥤ C) j = X := rfl
@[simp] lemma const_map (X : C) {j j' : J} (f : j ⟶ j') : (X : J ⥤ C).map f = 𝟙 X := rfl

section
variables {J}
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def const_compose (X : C) (F : C ⥤ D) : (F X : J ⥤ D) ≅ (X : J ⥤ C) ⋙ F :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

end

end category_theory.functor

open category_theory

namespace category_theory.nat_trans

def const {X Y : C} (f : X ⟶ Y) : (X : J ⥤ C) ⟹ (Y : J ⥤ C) :=
{ app := λ j, f }

instance const_coe {X Y : C} : has_coe (X ⟶ Y) ((X : J ⥤ C) ⟹ (Y : J ⥤ C)) := ⟨ const J ⟩

end category_theory.nat_trans

variables {J}

open category_theory

namespace category_theory.limits

/-- A `c : cone F` is an object `c.X` and a natural transformation `c.π : c.X ⟹ F` from the constant `c.X` functor to `F`. -/
structure cone (F : J ⥤ C) :=
(X : C)
(π : (X : J ⥤ C) ⟹ F)

@[simp] lemma cone.w (F : J ⥤ C) (c : cone F) {j j' : J} (f : j ⟶ j') :
  c.π j ≫ F.map f = c.π j' :=
(c.π).naturality f



/-- A `c : cocone F` is an object `c.X` and a natural transformation `c.π : F ⟹ c.X` from `F` to the constant `c.X` functor. -/
structure cocone (F : J ⥤ C) :=
(X : C)
(ι : F ⟹ (X : J ⥤ C))

variable {F : J ⥤ C}

namespace cone
def extend (c : cone F) {X : C} (f : X ⟶ c.X) : cone F :=
{ X := X,
  π := (f : (X : J ⥤ C) ⟹ (c.X : J ⥤ C)) ⊟ c.π }

def postcompose {G : J ⥤ C} (c : cone F) (α : F ⟹ G) : cone G :=
{ X := c.X,
  π := c.π ⊟ α }

def whisker (c : cone F) {K : Type v} [small_category K] (E : K ⥤ J) : cone (E ⋙ F) :=
{ X := c.X,
  π := whisker_left E c.π }
end cone

namespace cocone
def extend (c : cocone F) {X : C} (f : c.X ⟶ X) : cocone F :=
{ X := X,
  ι := c.ι ⊟ (f : (c.X : J ⥤ C) ⟹ (X : J ⥤ C)) }

def precompose {G : J ⥤ C} (c : cocone F) (α : G ⟹ F) : cocone G :=
{ X := c.X,
  ι := α ⊟ c.ι }

def whisker (c : cocone F) {K : Type v} [small_category K] (E : K ⥤ J) : cocone (E ⋙ F) :=
{ X := c.X,
  ι := whisker_left E c.ι }
end cocone

structure cone_morphism (A B : cone F) : Type v :=
(hom : A.X ⟶ B.X)
(w' : Π j : J, hom ≫ (B.π j) = (A.π j) . obviously)

restate_axiom cone_morphism.w'
attribute [simp] cone_morphism.w

namespace cone_morphism

@[extensionality] lemma ext {A B : cone F} {f g : cone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  /- obviously' say: -/
  induction f,
  induction g,
  dsimp at w,
  induction w,
  refl,
end

end cone_morphism

instance cones (F : J ⥤ C) : category.{(max u v) v} (cone F) :=
{ hom  := λ A B, cone_morphism A B,
  comp := λ _ _ _ f g, { hom := f.hom ≫ g.hom },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cone F) : (𝟙 c : cone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) :
  cone_morphism c e).hom = (f : cone_morphism c d).hom ≫ (g : cone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cone F) ⥤ (cone (F ⋙ G)) :=
{ obj      := λ A,
  { X := G A.X,
    π := (functor.const_compose _ _).hom ⊟ whisker_right A.π G },
  map'     := λ X Y f,
  { hom := G.map f.hom,
    w' := begin intros, dsimp, erw [category.id_comp, ←functor.map_comp, cone_morphism.w, category.id_comp] end } }
end
end cones

structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w'  : Π j : J, (A.ι j) ≫ hom = (B.ι j) . obviously)

restate_axiom cocone_morphism.w'
attribute [simp] cocone_morphism.w

namespace cocone_morphism

@[extensionality] lemma ext {A B : cocone F} {f g : cocone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at w,
  induction w,
  refl,
end
end cocone_morphism

instance cocones (F : J ⥤ C) : category.{(max u v) v} (cocone F) :=
{ hom  := λ A B, cocone_morphism A B,
  comp := λ _ _ _ f g,
  { hom := f.hom ≫ g.hom,
    w' := begin intros j, rw ←category.assoc, rw ←cocone_morphism.w g, rw ←cocone_morphism.w f j end },
  id   := λ B, { hom := 𝟙 B.X } }

namespace cocones
@[simp] lemma id.hom   {F : J ⥤ C} (c : cocone F) : (𝟙 c : cocone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma comp.hom {F : J ⥤ C} {c d e : cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) :
  cocone_morphism c e).hom = (f : cocone_morphism c d).hom ≫ (g : cocone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

@[simp] def functoriality (F : J ⥤ C) (G : C ⥤ D) : (cocone F) ⥤ (cocone (F ⋙ G)) :=
{ obj := λ A,
  { X  := G A.X,
    ι  :=  whisker_right A.ι G ⊟ (functor.const_compose _ _).inv },
  map' := λ _ _ f,
  { hom := G.map f.hom,
    w'  := begin intros, dsimp, erw [category.comp_id, ←functor.map_comp, cocone_morphism.w, category.comp_id], end } }
end
end cocones

end category_theory.limits

namespace category_theory.functor

variables {D : Type u} [category.{u v} D]
variables {F : J ⥤ C} {G : J ⥤ C}

open category_theory.limits

def map_cone   (H : C ⥤ D) (c : cone F)   : cone (F ⋙ H)   := (cones.functoriality F H) c
def map_cocone (H : C ⥤ D) (c : cocone F) : cocone (F ⋙ H) := (cocones.functoriality F H) c
def map_cone_morphism   (H : C ⥤ D) {c c' : cone F}   (f : cone_morphism c c')   :
  cone_morphism   (H.map_cone c)   (H.map_cone c')   := (cones.functoriality F H).map f
def map_cocone_morphism (H : C ⥤ D) {c c' : cocone F} (f : cocone_morphism c c') :
  cocone_morphism (H.map_cocone c) (H.map_cocone c') := (cocones.functoriality F H).map f

end category_theory.functor