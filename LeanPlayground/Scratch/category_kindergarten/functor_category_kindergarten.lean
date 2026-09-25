/-
# Functor Category Kindergarten

An exploration space for functors as objects and natural transformations as
morphisms, with a first look at vertical and horizontal composition and
whiskering.
-/

import LeanPlayground.Scratch.category_kindergarten.common_tools
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
-- These next two imports let us use Fin n as a preorder category. So, Fin 1 is
-- the singleton category, Fin 2 is the walking arrow, etc
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Fintype.Order

open CategoryTheory
open CategoryTheory.Functor
open scoped CategoryKindergarten

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
-- NatTrans.vcomp_app α β X : (NatTrans.vcomp α β).app X = α.app X ≫ β.app X
#check NatTrans.comp_app α β X
-- NatTrans.comp_app α β X : (α ≫ β).app X = α.app X ≫ β.app X
#check (α ≫ β) ≫ γ
#check Category.assoc α β γ

/- `α ≫ β` is the same as `NatTrans.vcomp α β` -/
example : α ≫ β = NatTrans.vcomp α β  := by
  rfl


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

-- Whiskering produces a natural transformation *in E*.
--
-- Left whiskering takes a nat trans α : G ⟶ H and a functor F out of the
-- (shared) codomain of G and H, and returns the natural transformation from G ≫
-- F to H ≫ F, both of which composite functors are of course from the shared
-- domain of G and H to the codomain of F. So in this case, from C to E.
#check Functor.whiskerLeft F α
-- F.whiskerLeft α : F ⋙ G ⟶ F ⋙ H
#check (Functor.whiskerLeft F α).app
-- (F.whiskerLeft α).app : (X : C) → (F ⋙ G).obj X ⟶ (F ⋙ H).obj X

variable (G' H' : C ⥤ D) (β : G' ⟶ H')
variable (K : D ⥤ E)

-- Right whisker also gives us a natural transformation *in E*.
--
-- Right whiskering takes a nat trans β : G' ⟶ H' and a functor F into the
-- (shared) codomain of G' and H', and returns the natural transformation from F
-- ≫ G' to F ≫ H', both of which composite functors are from the domain of F to
-- the shared codomain of G' and H'. So in this case, from C to E.
#check Functor.whiskerRight β K
-- whiskerRight β K : G' ⋙ K ⟶ H' ⋙ K
#check (Functor.whiskerRight β K).app
-- (whiskerRight β K).app : (X : C) → (G' ⋙ K).obj X ⟶ (H' ⋙ K).obj X

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

#check NatTrans.exchange α α' β β'
-- NatTrans.exchange α α' β β' : (α ≫ α') ◫ (β ≫ β') = (α ◫ β) ≫ α' ◫ β'

-- Horizontal composition respects vertical composition in both arguments.
example : (α ≫ α') ◫ (β ≫ β') = (α ◫ β) ≫ (α' ◫ β') := by
  exact NatTrans.exchange α α' β β'

end HorizontalComposition

/-! ## The category of elements

For a functor `F : C ⥤ Type`, Lean defines `F.Elements` as the dependent pair
type `Σ X : C, F.obj X`. Thus an object truly is an ordered pair `(X, x)`,
where `X : C` and `x : F.obj X`; its components are available as `p.fst` and
`p.snd` (also written `p.1` and `p.2`). The type of the second component
depends on the first: `p.snd : F.obj p.fst`.

Lean represents a morphism `g : p ⟶ q` as a subtype, rather than as a bare
morphism in `C`. Its field `g.val : p.fst ⟶ q.fst` is the underlying morphism
in `C`, and its field `g.property` proves `F.map g.val p.snd = q.snd`. So it
is a wrapper around a morphism in `C`, carrying exactly the evidence that the
morphism transports the selected source element to the selected target element.
-/

section CategoryOfElements

variable {C : Type u₁} [Category.{v₁} C]
variable (F : C ⥤ Type u₃)
variable (X Y : C) (x : F.obj X) (y : F.obj Y) (f : X ⟶ Y)
variable (h : F.map f x = y)

-- Shared shorthand for the underlying function of a concrete-category morphism.
#check cchom
-- The category whose objects are pairs `(X, x)` with `x : F.obj X`.
#check F.Elements
-- Build the object `(X, x)` of that category.
#check Functor.elementsMk F X x
-- Build a morphism `(X, x) ⟶ (Y, y)` from `f`, using `h` as its compatibility proof.
#check CategoryOfElements.homMk (Functor.elementsMk F X x)
  (Functor.elementsMk F Y y) f h
-- Every element-category morphism satisfies its defining compatibility equation.
#check CategoryOfElements.map_snd
-- Forget the selected element, retaining only its object and morphism in `C`.
#check CategoryOfElements.π F

/- An element-category object is a dependent pair. Its first component is the
object of `C`; its second component is the chosen element of the functor. -/
variable (t : F.Elements)

-- The base object `X : C` chosen by `t`.
#check t.1
-- The element of `F.obj t.1` selected by `t`.
#check t.2
-- For the explicitly constructed pair, recover its base object `X`.
#check (Functor.elementsMk F X x).1
-- For the explicitly constructed pair, recover its chosen element `x`.
#check (Functor.elementsMk F X x).2

/- A morphism remembers both its underlying arrow in `C` and the equation
showing that it sends the source element to the target element. -/
variable {p q : F.Elements} (g : p ⟶ q)

-- The underlying map `p.1 ⟶ q.1` in the original category `C`.
-- It is the `val` field of the subtype representing `g`.
#check g.val
-- The proof that mapping `p.2` along `g.1` produces `q.2`.
#check g.property
-- Applying the projection functor to an element object returns its base object.
#check (CategoryOfElements.π F).obj p
-- Applying the projection functor to an element morphism returns its underlying map.
#check (CategoryOfElements.π F).map g

example : (CategoryOfElements.π F).obj (Functor.elementsMk F X x) = X := rfl
example : (CategoryOfElements.π F).map
    (CategoryOfElements.homMk (Functor.elementsMk F X x)
      (Functor.elementsMk F Y y) f h) = f := rfl

variable {G : C ⥤ Type u₃} (α : F ⟶ G)

-- A natural transformation induces a functor between its two categories of elements.
#check CategoryOfElements.map α
-- On `(X, x)`, that induced functor gives `(X, α.app X x)`.
#check (CategoryOfElements.map α).obj (Functor.elementsMk F X x)
#check α.app X x
-- (cchom (α.app X)) x : (fun X => X) (G.obj X)
example : (CategoryOfElements.map α).obj (Functor.elementsMk F X x) =
  (⟨X, α.app X x⟩ : G.Elements) := rfl

-- On morphisms, it retains the underlying map in `C` and transports its proof.
#check (CategoryOfElements.map α).map g
-- The induced functor commutes exactly with forgetting to `C`.
#check CategoryOfElements.map_π α
-- The category of elements is equivalent to the structured-arrow category `(*, F)`.
#check CategoryOfElements.structuredArrowEquivalence F

/- `CategoryOfElements.map α` applies `α` to the selected element, while
preserving the object and underlying morphism in `C`. -/
example : ((CategoryOfElements.map α).obj (Functor.elementsMk F X x)).1 = X := rfl
example : ((CategoryOfElements.map α).obj (Functor.elementsMk F X x)).2 = α.app X x := rfl
example : ((CategoryOfElements.map α).map g).1 = g.1 := rfl

/- The induced functor lies over `C`: forgetting an element before or after
applying `α` gives exactly the same functor to `C`. -/
example : CategoryOfElements.map α ⋙ CategoryOfElements.π G = CategoryOfElements.π F :=
  CategoryOfElements.map_π α

#check (Fin 1) ⥤ (Cᵒᵖ ⥤ Type v₁)


#check Functor.fromPUnit

/-
Riehl lemma 2.4.7, p. 68:

The category of elements can be reconstructed as a comma category up to
equivalence.

The following is closer to Riehl's lemma 2.4.7 than it might appear, but to see
why we need to dive into Lean's comma category machinery, which this isn't the
file for. -/
example (F : Cᵒᵖ ⥤ Type v₁) :
    F.Elementsᵒᵖ ≌ Comma yoneda (Functor.fromPUnit.{0} F) :=
  CategoryOfElements.costructuredArrowYonedaEquivalence F


/-
Riehl Example 2.4.6, p.67:

Another comma-family category turns up in relation to the category of elements:
using whiteboard notation, ∫C(c, -) is the slice category c/C under the object c
∈ C, and ∫C(-, c) is the slice category C/c over the object c ∈ C.   -/

open Opposite

-- The covariant representable sends X to the arrows c ⟶ X.
example (c : C) : (coyoneda.obj (op c)).Elements ≌ Under c := by
  let toUnder : (coyoneda.obj (op c)).Elements ⥤ Under c :=
    { obj := fun p => Under.mk p.2
      map := fun f => Under.homMk f.val f.property }
  let fromUnder : Under c ⥤ (coyoneda.obj (op c)).Elements :=
    { obj := fun p => ⟨p.right, p.hom⟩
      map := fun f => ⟨f.right, Under.w f⟩ }
  exact {
    functor := toUnder
    inverse := fromUnder
    unitIso := Iso.refl _
    counitIso := Iso.refl _
    functor_unitIso_comp := by
      intro X
      change toUnder.map (𝟙 X) ≫ 𝟙 (toUnder.obj X) = 𝟙 (toUnder.obj X)
      simp
  }

/- Developer note: The two equivalences use the same construction with arrows
reversed. For the presheaf `C(-, c)`, an element morphism from `(X, f)` to
`(Y, g)` uses an arrow `Y ⟶ X`, whereas an `Over c` morphism goes from `X`
to `Y`. This accounts for `Elementsᵒᵖ` in the second statement and for the
`op`/`unop` conversions in its explicit inverse functor. -/
-- The presheaf representable sends X to the arrows X ⟶ c.
example (c : C) : (yoneda.obj c).Elementsᵒᵖ ≌ Over c := by
  let toOver : (yoneda.obj c).Elementsᵒᵖ ⥤ Over c :=
    { obj := fun p => Over.mk (unop p).2
      map := fun f => Over.homMk f.unop.val.unop f.unop.property }
  let fromOver : Over c ⥤ (yoneda.obj c).Elementsᵒᵖ :=
    { obj := fun p => op ⟨op p.left, p.hom⟩
      map := fun {X Y} f => Quiver.Hom.op (CategoryOfElements.homMk
        (⟨op Y.left, Y.hom⟩ : (yoneda.obj c).Elements)
        (⟨op X.left, X.hom⟩ : (yoneda.obj c).Elements)
        f.left.op (Over.w f)) }
  exact {
    functor := toOver
    inverse := fromOver
    unitIso := Iso.refl _
    counitIso := Iso.refl _
    functor_unitIso_comp := by
      intro X
      change toOver.map (𝟙 X) ≫ 𝟙 (toOver.obj X) = 𝟙 (toOver.obj X)
      simp
  }

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
