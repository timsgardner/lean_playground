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
import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Yoneda
-- These next two imports let us use Fin n as a preorder category. So, Fin 1 is
-- the singleton category, Fin 2 is the walking arrow, etc
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Fintype.Order

open CategoryTheory
open Opposite
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

/- All well and good, but who cares?

Riehl Proposition 2.4.8, p. 68:

For a covariant set-valued functor, a universal element is an initial object
of its category of elements. Thus the functor is representable precisely when
that category has an initial object. Mathlib calls this `IsCorepresentable`.

Dually, a universal element of a contravariant set-valued functor is terminal
in the presheaf convention for the category of elements. In Mathlib this is
`F.Elementsᵒᵖ`, so the same object is initial in `F.Elements`. -/

open Limits

/-- An initial object `e = (X, x)` of `F.Elements` makes `F` corepresentable by
`X = e.1`. Concretely, its unique maps out of `e` give the natural equivalence
`(X ⟶ Y) ≃ F.obj Y`, sending `f` to `F.map f x`. -/
private def corepresentableByOfInitialElement {F : C ⥤ Type v₁} (e : F.Elements)
    (h : IsInitial e) : F.CorepresentableBy e.1 where
  -- For each `Y : C`, this field has the full type
  -- `homEquiv {Y : C} : (e.1 ⟶ Y) ≃ F.obj Y`.
  -- We build the equivalence by giving its two functions and proving they are inverse.
  homEquiv {Y} :=
    { -- `toFun : (e.1 ⟶ Y) → F.obj Y` transports `e.2` along `f`.
      toFun := fun f => F.map f e.2
      /- Given `y : F.obj Y`, initiality supplies `h.to ⟨Y, y⟩ : e ⟶ ⟨Y, y⟩`.
         A morphism in `F.Elements` is a subtype: its `.val` is an arrow
         `f : e.1 ⟶ Y`, and its `.property` proves `F.map f e.2 = y`.
         Thus `.val` gives the required inverse function
         `F.obj Y → (e.1 ⟶ Y)`. -/
      invFun := fun y => (h.to ⟨Y, y⟩).val
      -- `left_inv` says `invFun (toFun f) = f` for every `f : e.1 ⟶ Y`.
      -- Here that means `(h.to ⟨Y, F.map f e.2⟩).val = f`.
      left_inv := by
        intro f
        -- `f` itself is an element-category arrow to `(Y, F.map f e.2)`.
        -- By uniqueness, it is the arrow supplied by initiality.
        have k : (⟨f, rfl⟩ : e ⟶ ⟨Y, F.map f e.2⟩) = h.to _ := h.hom_ext _ _
        -- Equality of element-category arrows gives equality of their base arrows.
        exact (congrArg Subtype.val k).symm
      -- `right_inv` says `toFun (invFun y) = y` for every `y : F.obj Y`.
      -- Here that means `F.map (h.to ⟨Y, y⟩).val e.2 = y`.
      right_inv := by
        intro y
        -- The arrow to `(Y, y)` must send `e.2` to `y` by definition.
        exact (h.to ⟨Y, y⟩).property }
  -- The forward map respects composition because `F` is a functor.
  homEquiv_comp g f := by simp [Functor.map_comp]

/-- A longer version of `corepresentableByOfInitialElement`. The local `let`s
name the functions and objects being constructed; the `have`s name the facts
needed to turn those functions into a natural equivalence. -/
private def corepresentableByOfInitialElementExplicit {F : C ⥤ Type v₁}
    (e : F.Elements) (h : IsInitial e) : F.CorepresentableBy e.1 := by
  -- We seek an equivalence `(e.1 ⟶ Y) ≃ F.obj Y` for every object `Y`.
  -- First define its forward function for all `Y` at once. It applies `F.map f`
  -- to the distinguished element `e.2 : F.obj e.1`.
  let forward : ∀ Y : C, (e.1 ⟶ Y) → F.obj Y :=
    fun Y f => F.map f e.2

  -- For `y : F.obj Y`, the pair `(Y, y)` is an object of `F.Elements`.
  -- Since `e` is initial, `h.to ⟨Y, y⟩` is an arrow from `e` to that pair.
  -- Taking `.val` extracts its underlying arrow `e.1 ⟶ Y` in `C`.
  let backward : ∀ Y : C, F.obj Y → (e.1 ⟶ Y) :=
    fun Y y => (h.to (⟨Y, y⟩ : F.Elements)).val

  -- Left inverse: start with `f : e.1 ⟶ Y`, map `e.2` along `f`, then use
  -- initiality to recover the arrow. We must get back exactly `f`.
  have backward_forward : ∀ (Y : C) (f : e.1 ⟶ Y),
      backward Y (forward Y f) = f := by
    intro Y f
    -- This is the target object selected by `forward Y f`.
    let target : F.Elements := ⟨Y, forward Y f⟩
    -- The arrow `f` itself defines a morphism in `F.Elements` to `target`:
    -- its compatibility equation is true by the definition of `target`.
    let candidate : e ⟶ target := ⟨f, rfl⟩
    -- An initial object has only one morphism to a given target.
    have unique : candidate = h.to target := h.hom_ext _ _
    -- Forget the compatibility proofs to compare the underlying arrows.
    have underlying_equal : candidate.val = (h.to target).val :=
      congrArg Subtype.val unique
    -- Unfold `backward` and `forward` in the goal. The local `let`s for
    -- `target` and `candidate` unfold to the pair and arrow built above.
    change (h.to target).val = candidate.val
    exact underlying_equal.symm

  -- Right inverse: start with `y : F.obj Y`, take the underlying arrow of
  -- `h.to ⟨Y, y⟩`, then apply `F.map` to `e.2`. We must get back `y`.
  have forward_backward : ∀ (Y : C) (y : F.obj Y),
      forward Y (backward Y y) = y := by
    intro Y y
    let arrow : e ⟶ (⟨Y, y⟩ : F.Elements) := h.to _
    -- Every morphism in `F.Elements` carries a proof that it sends the
    -- selected source element to the selected target element.
    have compatible : F.map arrow.val e.2 = y := arrow.property
    -- Unfold `forward` and `backward`; `arrow` is the chosen initial map.
    change F.map arrow.val e.2 = y
    exact compatible

  -- Package the two functions and their inverse laws into an `Equiv` at `Y`.
  let equivAt (Y : C) : (e.1 ⟶ Y) ≃ F.obj Y :=
    { toFun := forward Y
      invFun := backward Y
      left_inv := backward_forward Y
      right_inv := forward_backward Y }

  -- The family `equivAt` must also be natural in `Y`: following `f` by `g`
  -- corresponds to applying `F.map g` after `equivAt Y f`.
  have naturality : ∀ {Y Y' : C} (g : Y ⟶ Y') (f : e.1 ⟶ Y),
      equivAt Y' (f ≫ g) = F.map g (equivAt Y f) := by
    intro Y Y' g f
    change F.map (f ≫ g) e.2 = F.map g (F.map f e.2)
    simp [Functor.map_comp]

  -- These are precisely the two fields of `F.CorepresentableBy e.1`.
  exact { homEquiv := fun {Y} => equivAt Y
          homEquiv_comp := by
            intro Y Y' g f
            exact naturality g f }


/-- I bet we can do this by yoneda tho. This follows Riehl's proof on p.69 -/
private noncomputable def corepresentableByOfInitialElementYoneda {F : C ⥤ Type v₁}
    (e : F.Elements) (h : IsInitial e) : F.CorepresentableBy e.1 := by
  have h_unique_mor : ∀ (d : C) (y : F.obj d), ∃! (f: e.1 ⟶ d), F.map f e.2 = y := by
    intro d y
    let underlyingMor := (h.to ⟨d, y⟩).val
    refine ⟨?_, ?_, ?_⟩
    · exact underlyingMor
    #check (h.to ⟨d,y⟩).property
    · simpa [underlyingMor] using
        (h.to ⟨d,y⟩).property
    · intro m hm
      have unique :
          -- ⟨m, hm⟩ below is a morphism in the category of elements F.Elements.
          (⟨m, hm⟩ : e ⟶ (⟨d, y⟩ : F.Elements)) = h.to ⟨d, y⟩ := h.hom_ext _ _
      -- `Subtype.val`, applied to a morphism in F.Elements (such as `unique`),
      -- returns the underlying morphism in C. In the case of `⟨m, hm⟩`, that's
      -- ↑⟨m, hm⟩ : e.fst ⟶ ⟨d, y⟩.fst
      -- ie, e.1 ⟶ d
      #check Subtype.val (⟨m, hm⟩ : e ⟶ (⟨d, y⟩ : F.Elements))
      #check congrArg Subtype.val unique
      exact congrArg Subtype.val unique
  -- the nat trans C(e.1, -) ⟶ F, looked up by e.2 in F(e.1)
  let η := coyonedaEquiv.symm e.2
  have η_iso : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro d
    rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    simp -- unnecessary, but you can park the cursor here to see a denoised goal
    simpa only [η, coyonedaEquiv_symm_app_apply] using h_unique_mor d
  letI : IsIso η := η_iso
  #check (Functor.CorepresentableBy.coyoneda (op e.1)).ofIso (asIso η)
  exact (Functor.CorepresentableBy.coyoneda (op e.1)).ofIso (asIso η)




/-- A covariant type-valued functor is corepresentable exactly when its category
of elements has an initial object. -/
theorem isCorepresentable_iff_hasInitial_elements (F : C ⥤ Type v₁) :
    F.IsCorepresentable ↔ HasInitial F.Elements := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact (corepresentableByOfInitialElement (initial F.Elements)
      initialIsInitial).isCorepresentable

-- For a presheaf, an initial element of `F.Elements` represents F. Taking
-- opposites expresses the same universal property as terminality.
private def representableByOfInitialElement {F : Cᵒᵖ ⥤ Type v₁} (e : F.Elements)
    (h : IsInitial e) : F.RepresentableBy e.1.unop where
  homEquiv {X} :=
    { toFun := fun f => F.map f.op e.2
      invFun := fun y => (h.to (⟨Opposite.op X, y⟩ : F.Elements)).val.unop
      left_inv := by
        intro f
        have k : (⟨f.op, rfl⟩ : e ⟶ ⟨Opposite.op X, F.map f.op e.2⟩) = h.to _ :=
          h.hom_ext _ _
        exact (congrArg (fun m : e ⟶ (⟨Opposite.op X, F.map f.op e.2⟩ : F.Elements) =>
          m.val.unop) k).symm
      right_inv := by
        intro y
        exact (h.to (⟨Opposite.op X, y⟩ : F.Elements)).property }
  homEquiv_comp f g := by simp [Functor.map_comp]

/-- A presheaf is representable exactly when the opposite of its Mathlib
category of elements has a terminal object. -/
theorem isRepresentable_iff_hasTerminal_elements_op (F : Cᵒᵖ ⥤ Type v₁) :
    F.IsRepresentable ↔ HasTerminal F.Elementsᵒᵖ := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI : HasTerminal F.Elementsᵒᵖ := h
    letI : HasInitial F.Elements := hasInitial_of_hasTerminal_op
    exact (representableByOfInitialElement (initial F.Elements)
      initialIsInitial).isRepresentable

/- Riehl Proposition 2.4.9, p. 69: the representations of a covariant functor
form either the empty category or a contractible groupoid. By Proposition
2.4.8, these are exactly the initial objects of its category of elements. -/

/-- The full subcategory of the category of elements consisting of universal
elements, equivalently representations of `F`. -/
abbrev UniversalElements (F : C ⥤ Type v₁) :=
  ObjectProperty.FullSubcategory (fun e : F.Elements => Nonempty (IsInitial e))

private theorem universalElements_unique_hom (F : C ⥤ Type v₁)
    (X Y : UniversalElements F) : Nonempty (Unique (X ⟶ Y)) := by
  obtain ⟨hX⟩ := X.property
  let f : X ⟶ Y := ObjectProperty.homMk (hX.to Y.obj)
  have : Subsingleton (X ⟶ Y) := ⟨by
    intro a b
    apply ObjectProperty.hom_ext
    exact hX.hom_ext a.hom b.hom⟩
  exact ⟨uniqueOfSubsingleton f⟩

/-- Every morphism between universal elements is invertible. -/
instance universalElements_isGroupoid (F : C ⥤ Type v₁) :
    IsGroupoid (UniversalElements F) := by
  letI : Groupoid (UniversalElements F) :=
    Groupoid.ofHomUnique (fun {X Y} =>
      Classical.choice (universalElements_unique_hom F X Y))
  infer_instance

/-- Universal elements exist precisely when the functor is corepresentable. -/
theorem universalElements_nonempty_iff_isCorepresentable (F : C ⥤ Type v₁) :
    Nonempty (UniversalElements F) ↔ F.IsCorepresentable := by
  constructor
  · rintro ⟨⟨e, ⟨he⟩⟩⟩
    exact (isCorepresentable_iff_hasInitial_elements F).2 he.hasInitial
  · intro h
    letI : HasInitial F.Elements := (isCorepresentable_iff_hasInitial_elements F).1 h
    exact ⟨⟨initial F.Elements, ⟨initialIsInitial⟩⟩⟩

/-- The representations of a covariant type-valued functor form either the
empty category or a category equivalent to the singleton category. The latter
is a contractible groupoid. -/
theorem universalElements_empty_or_contractible (F : C ⥤ Type v₁) :
    IsEmpty (UniversalElements F) ∨
      Nonempty (UniversalElements F ≌ Discrete PUnit) := by
  by_cases h : Nonempty (UniversalElements F)
  · right
    exact (equiv_punit_iff_unique (UniversalElements F)).2
      ⟨h, fun X Y => universalElements_unique_hom F X Y⟩
  · left
    exact ⟨fun X => h ⟨X⟩⟩

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
