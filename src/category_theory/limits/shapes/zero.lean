/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.terminal

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References
* https://en.wikipedia.org/wiki/Zero_morphism
-/

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms :=
[has_zero : Π X Y : C, has_zero (X ⟶ Y)]
(comp_zero' : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) . obviously)
(zero_comp' : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) . obviously)

attribute [instance] has_zero_morphisms.has_zero
restate_axiom has_zero_morphisms.comp_zero'
attribute [simp] has_zero_morphisms.comp_zero
restate_axiom has_zero_morphisms.zero_comp'
attribute [simp, reassoc] has_zero_morphisms.zero_comp

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object :=
(zero : C)
(unique_to : ∀ X : C, unique (zero ⟶ X))
(unique_from : ∀ X : C, unique (X ⟶ zero))

variables [has_zero_object.{v} C]

variables {C}

/-- We allow writing `0` to indicate the zero object in any category with a zero object. -/
instance [has_zero_object.{v} C] : has_zero C :=
{ zero := has_zero_object.zero.{v} C }

attribute [instance] has_zero_object.unique_to has_zero_object.unique_from

namespace has_zero_object
-- We now make some preliminary definitions in preparation for constructing an instance of
-- `has_zero_morphisms C`. They can all be private, as public versions have provided by the
-- `has_zero_morphisms` typeclass.

private def zero_morphism (X Y : C) :=
inhabited.default (X ⟶ 0) ≫ inhabited.default (0 ⟶ Y)

private def hom_has_zero {X Y : C} : has_zero (X ⟶ Y) :=
{ zero := zero_morphism X Y }

local attribute [instance] hom_has_zero -- in a moment these will be provided by `has_zero_morphism`

private lemma zero_morphism_comp {X Y Z : C} (f : Y ⟶ Z) : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
by { dsimp [has_zero.zero, zero_morphism], rw [category.assoc], congr, }
private lemma comp_zero_morphism {X Y Z : C} (f : X ⟶ Y) : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
by { dsimp [has_zero.zero, zero_morphism], rw [←category.assoc], congr, }

-- in a moment these will be deprecated by `has_zero_morphism.zero_comp` and `has_zero_morphism.comp_zero`.
local attribute [simp] zero_morphism_comp comp_zero_morphism

/-- A category with a zero object has zero morphisms. -/
instance : has_zero_morphisms.{v} C := {}

/-- A zero object is in particular initial. -/
instance has_initial_of_has_zero_object : has_initial.{v} C :=
has_initial_of_unique 0
/-- A zero object is in particular terminal. -/
instance has_terminal_of_has_zero_object : has_terminal.{v} C :=
has_terminal_of_unique 0

end has_zero_object

end category_theory.limits
