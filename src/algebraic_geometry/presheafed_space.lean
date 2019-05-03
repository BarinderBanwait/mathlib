-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.instances.Top.presheaf

universes v u

open category_theory
open category_theory.instances
open category_theory.instances.Top
open topological_space

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

namespace algebraic_geometry

structure PresheafedSpace :=
(X : Top.{v})
(𝒪 : X.presheaf C)

variables {C}

namespace PresheafedSpace

instance : has_coe_to_sort (PresheafedSpace.{v} C) :=
{ S := Type v, coe := λ F, F.X.α }

instance (F : PresheafedSpace.{v} C) : topological_space F := F.X.str

structure hom (F G : PresheafedSpace.{v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟶ f _* F.𝒪)

@[extensionality] lemma ext {F G : PresheafedSpace.{v} C} (α β : hom F G)
  (w : α.f = β.f) (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) F.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp at w,
  dsimp [presheaf.pushforward] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

def id (F : PresheafedSpace.{v} C) : hom F F :=
{ f := 𝟙 F.X,
  c := ((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _) }

def comp (F G H : PresheafedSpace.{v} C) (α : hom F G) (β : hom G H) : hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ≫ (whisker_left (opens.map β.f).op α.c) }

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

instance category_of_PresheafedSpaces : category (PresheafedSpace.{v} C) :=
{ hom  := hom,
  id   := id,
  comp := comp,
  -- I'm still grumpy about these proofs.
  -- When I turned the category of open sets upside down by hand,
  -- I could just leave these out.
  comp_id' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp, },
    { simp }
  end,
  id_comp' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [category.assoc],
      erw [category_theory.functor.map_id],
      simp, },
    { simp }
  end,
  assoc' := λ W X Y Z f g h,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [category.assoc],
      erw [category_theory.functor.map_id],
      simp, },
    { refl }
  end }
end
.

instance (X Y : PresheafedSpace.{v} C) : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X.X → Y.X,
  coe := λ f, f.f }

variables {C}

@[simp] lemma id_f (F : PresheafedSpace.{v} C) : ((𝟙 F) : F ⟶ F).f = 𝟙 F.X := rfl
@[simp] lemma comp_f {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).f = α.f ≫ β.f :=
rfl

-- We don't mark these as simp lemmas, because the innards are pretty unsightly.
lemma id_c (F : PresheafedSpace.{v} C) :
  ((𝟙 F) : F ⟶ F).c =
  (((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _)) :=
rfl
lemma comp_c {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) :=
rfl
end PresheafedSpace

end algebraic_geometry

open algebraic_geometry
variables {C}

namespace category_theory

variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c presheaf.pushforward

namespace functor

def map_presheaf (F : C ⥤ D) : PresheafedSpace.{v} C ⥤ PresheafedSpace.{v} D :=
{ obj := λ X, { X := X.X, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F } }.

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).X = X.X :=
rfl
@[simp] lemma map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F :=
rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).f = f.f :=
rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F :=
rfl

end functor

namespace nat_trans

def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ≫ ((functor.left_unitor _).inv) ≫
           (whisker_right (nat_trans.op (opens.map_id _).hom) _) },
  naturality' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [functor.map_id, category.id_comp, category.comp_id, category.assoc],
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      simp only [category.comp_id],
      exact (α.naturality _).symm, },
    { refl, }
  end }.

end nat_trans

end category_theory
