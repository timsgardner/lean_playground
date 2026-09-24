/-
# Functor Category Kindergarten

An exploration space for functors as objects and natural transformations as
morphisms, with a first look at vertical and horizontal composition and
whiskering.
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Elements

open CategoryTheory
open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace FunctorCategoryKindergarten

/-! ## Functors form a category

Fix categories `C` and `D`. The objects of `C ⥤ D` are functors, and a
morphism `F ⟶ G` in this category is a natural transformation.
-/

section FunctorCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F G : C ⥤ D)

#check C ⥤ D
#check F ⟶ G
#check (𝟙 F : F ⟶ F)

variable (α : F ⟶ G)
variable (X Y : C) (f : X ⟶ Y)

#check α.app X
#check α.naturality f

end FunctorCategory

/-! ## Vertical composition

Vertical composition composes two natural transformations with the same
source and target categories. At each object, it is just composition of the
component morphisms.
-/

section VerticalComposition

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F G H I : C ⥤ D}
variable (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I)
variable (X : C)

#check α ≫ β
#check NatTrans.vcomp α β
#check NatTrans.vcomp_app α β X
#check NatTrans.comp_app α β X
#check (α ≫ β) ≫ γ
#check Category.assoc α β γ

end VerticalComposition

/-! ## Whiskering

Whiskering composes a natural transformation with a fixed functor. Left
whiskering precomposes the functors; right whiskering postcomposes them.
-/

section Whiskering

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable (F : C ⥤ D) (G H : D ⥤ E)
variable (α : G ⟶ H)

#check Functor.whiskerLeft F α
#check (Functor.whiskerLeft F α).app

variable (G' H' : C ⥤ D) (β : G' ⟶ H')
variable (K : D ⥤ E)

#check Functor.whiskerRight β K
#check (Functor.whiskerRight β K).app

end Whiskering

/-! ## Horizontal composition

Horizontal composition combines transformations between composable functors.
The interchange law relates horizontal composition to vertical composition.
-/

section HorizontalComposition

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {F G G' : C ⥤ D} {H I I' : D ⥤ E}
variable (α : F ⟶ G) (β : H ⟶ I)

#check NatTrans.hcomp α β
#check α ◫ β
#check (α ◫ β).app
#check NatTrans.exchange

variable (α' : G ⟶ G') (β' : I ⟶ I')
#check (α ≫ α') ◫ (β ≫ β')

end HorizontalComposition

/-! ## The category of elements

For a functor `F : C ⥤ Type`, an object of `F.Elements` is an object `X : C`
together with an element `x : F.obj X`. A morphism `(X, x) ⟶ (Y, y)` is a map
`f : X ⟶ Y` for which `F.map f x = y`.
-/

section CategoryOfElements

variable {C : Type u₁} [Category.{v₁} C]
variable (F : C ⥤ Type u₃)
variable (X Y : C) (x : F.obj X) (y : F.obj Y) (f : X ⟶ Y)
variable (h : F.map f x = y)

#check F.Elements
#check Functor.elementsMk F X x
#check CategoryOfElements.homMk (Functor.elementsMk F X x)
  (Functor.elementsMk F Y y) f h
#check CategoryOfElements.map_snd
#check CategoryOfElements.π F

variable {G : C ⥤ Type u₃} (α : F ⟶ G)

#check CategoryOfElements.map α
#check (CategoryOfElements.map α).obj (Functor.elementsMk F X x)
#check CategoryOfElements.map_π α
#check CategoryOfElements.structuredArrowEquivalence F

end CategoryOfElements

/-! ## Isomorphisms in the functor category

An isomorphism `F ≅ G` in the functor category is a natural isomorphism:
natural transformations in both directions whose composites are identities.
These are the unit and counit used to package an equivalence of categories.
-/

section NaturalIsomorphisms

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F G : C ⥤ D) (e : F ≅ G)
variable (X : C)

#check F ≅ G
#check NatIso.ofComponents
#check e.hom
#check e.inv
#check e.hom.app X
#check e.hom_inv_id

end NaturalIsomorphisms

/-! ## Equivalences of categories

An equivalence packages a functor, an inverse up to natural isomorphism, and
the triangle identity. Mathlib also gives a functor-level criterion: a functor
is an equivalence when it is full, faithful, and essentially surjective.
-/

section Equivalences

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (e : C ≌ D)
variable (X : C) (Y : D)

#check C ≌ D
#check e.functor
#check e.inverse
#check e.unitIso
#check e.counitIso
#check e.functor_unitIso_comp X
#check e.functor.FullyFaithful
#check e.functor.Full
#check e.functor.Faithful
#check e.functor.EssSurj

end Equivalences

/-! ## Full, faithful, and essentially surjective

Fullness lifts each morphism between image objects; faithfulness says mapping
morphisms is injective; essential surjectivity says every target object is
isomorphic to an image object. Together these properties produce a bundled
equivalence.
-/

section EquivalenceCriterion

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

#check Functor.Full
#check Functor.Faithful
#check Functor.EssSurj
#check F.IsEquivalence

section GivenTheThreeProperties

variable [F.Full] [F.Faithful] [F.EssSurj]

#check F.map_surjective
#check F.map_injective
#check F.objPreimage
#check F.objObjPreimageIso

-- Supplying all three properties lets typeclass inference build `F.IsEquivalence`.
example : F.IsEquivalence := {}

-- Conversely, `F.asEquivalence` packages this functor-level criterion.
noncomputable example : C ≌ D := by
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end GivenTheThreeProperties

end EquivalenceCriterion

/-! ## A place to experiment

The identities above can be read componentwise. Next we can build small
examples in `Type`, then use them to see why whiskering and horizontal
composition are useful in larger diagrams, or visualize a type-valued functor
through its category of elements.
-/

-- TODO: define a pair of simple functors and a natural transformation between them.
-- TODO: compute the components of its whiskerings and horizontal composites.
-- TODO: describe the objects and morphisms of a small category of elements.

end FunctorCategoryKindergarten
