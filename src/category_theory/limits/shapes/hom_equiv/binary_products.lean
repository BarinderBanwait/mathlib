/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.binary_products

/-!
Constructing binary products from specified objects, and characterisations of the morphisms
out them.
-/

universes v u

open category_theory
open opposite

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

open walking_pair

section
local attribute [tidy] tactic.case_bash

/--
We characterise `F.cones` objectwise for a functor `F` on the walking pair. -/
def walking_pair_cones_equiv {Q : C} (F : discrete walking_pair.{v} ⥤ C) : (Q ⟶ F.obj left) × (Q ⟶ F.obj right) ≃ F.cones.obj (op Q) :=
iso.to_equiv
{ hom := λ f, { app := λ j, match j with | left := f.1 | right := f.2 end },
  inv := λ c, (c.app left, c.app right) }

def binary_product_nat_iso_of_hom_equiv
  {P : C} (F : discrete walking_pair.{v} ⥤ C)
  (h : Π (Q : C), (Q ⟶ P) ≃ (Q ⟶ F.obj left) × (Q ⟶ F.obj right))
  (n₁ : Π (Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ P), (h Q (f ≫ g)).1 = f ≫ (h Q' g).1)
  (n₂ : Π (Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ P), (h Q (f ≫ g)).2 = f ≫ (h Q' g).2) :
    yoneda.obj P ≅ F.cones :=
nat_iso.of_components (λ Q, ((h (unop Q)).trans (walking_pair_cones_equiv F)).to_iso) (by tidy)
end

/--
Show that `C` has binary products by providing a function `prod : C → C → C`, and for all `X Y : C`,
and all other objects `Q : C`, providing an equivalence `(Q ⟶ prod X Y) ≃ (Q ⟶ X) × (Q ⟶ Y)` which
is natural in `Q`.
-/
def has_binary_products_of_hom_equiv
  (prod : C → C → C)
  (hom_equiv : Π (X Y Q : C), (Q ⟶ prod X Y) ≃ (Q ⟶ X) × (Q ⟶ Y))
  (naturality₁ : Π (X Y Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ prod X Y),
    (hom_equiv X Y Q (f ≫ g)).1 = f ≫ (hom_equiv X Y Q' g).1)
  (naturality₂ : Π (X Y Q Q' : C) (f : Q ⟶ Q') (g : Q' ⟶ prod X Y),
    (hom_equiv X Y Q (f ≫ g)).2 = f ≫ (hom_equiv X Y Q' g).2) :
  has_binary_products.{v} C :=
{ has_limits_of_shape :=
  has_limits_of_shape.of_nat_iso (λ F,
    ⟨_, binary_product_nat_iso_of_hom_equiv F
          (hom_equiv (F.obj left) (F.obj right))
          (naturality₁ (F.obj left) (F.obj right))
          (naturality₂ (F.obj left) (F.obj right))⟩) }

example : has_binary_products.{v} (Type v) :=
has_binary_products_of_hom_equiv
  (λ X Y, X × Y)
  (λ X Y Q, iso.to_equiv
    { hom := λ f, (λ q, (f q).1, λ q, (f q).2),
      inv := λ p q, (p.1 q, p.2 q) })
  (by tidy) (by tidy)

end category_theory.limits
