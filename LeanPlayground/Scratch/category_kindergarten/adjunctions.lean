import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools


/- # Adjunctions

  `F ⊣ G` (type `\dashv`) for `F : C ⥤ D`, `G : D ⥤ C` is Mathlib's `Adjunction F G`.
  The structure itself is stored as unit/counit plus triangle identities:

    unit   : 𝟭 C ⟶ F ⋙ G
    counit : G ⋙ F ⟶ 𝟭 D
    left_triangle_components  X : F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X)
    right_triangle_components Y : unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y)

  The hom-set bijection is derived from those:

    adj.homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
      f ↦ unit.app X ≫ G.map f
      g ↦ F.map g ≫ counit.app Y

  ## Building one

  Two constructors, one per textbook definition.

  `Adjunction.mkOfHomEquiv` takes a `CoreHomEquiv F G`:

    homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g
    homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g

  Naturality is asked for in only one direction per variable (`symm` on the left,
  plain on the right); the other two follow.

  `Adjunction.mkOfUnitCounit` takes a `CoreUnitCounit F G`:

    unit   : 𝟭 C ⟶ F ⋙ G        (a `NatTrans`: give `app` and `naturality`)
    counit : G ⋙ F ⟶ 𝟭 D
    left_triangle :
      whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit = NatTrans.id (𝟭 C ⋙ F)
    right_triangle :
      whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G = NatTrans.id (G ⋙ 𝟭 C)

  These are the triangle identities stated on whole natural transformations.
  `ext X` reduces them to components, and these simp lemmas unfold the pieces:

    Functor.whiskerRight_app : (whiskerRight α F).app X = F.map (α.app X)
    Functor.whiskerLeft_app  : (whiskerLeft F α).app X  = α.app (F.obj X)
    Functor.associator_hom_app / _inv_app : component is 𝟙 _
    NatTrans.comp_app        : (α ≫ β).app X = α.app X ≫ β.app X
    NatTrans.id_app'         : (NatTrans.id F).app X = 𝟙 (F.obj X)

  What's left is the componentwise form from the top of this comment.

  ## Using one

  For `adj : F ⊣ G`:

    adj.homEquiv_unit X Y f   : adj.homEquiv X Y f = adj.unit.app X ≫ G.map f
    adj.homEquiv_counit X Y g : (adj.homEquiv X Y).symm g = F.map g ≫ adj.counit.app Y
    adj.homEquiv_naturality_left  / _left_symm  : precompose on the `X` side
    adj.homEquiv_naturality_right / _right_symm : postcompose on the `Y` side
    adj.unit_naturality f   : adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
    adj.counit_naturality f : F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f
    adj.left_triangle_components / adj.right_triangle_components   (both simp)

  ## Running example

  Currying in `Type`. For a fixed `A`,

    (- × A) ⊣ (A → -)          (X × A ⟶ Y) ≃ (X ⟶ (A → Y))

  Staying in `Type` (universe 0), as in `square_functor_representable.lean`.

  Morphisms in `Type` are a wrapper structure, not bare functions (see
  `typecat_conversions.lean`). Build one with `↾g` (`TypeCat.ofHom g`), apply one with
  plain `f x`, prove two equal with `ext`, and `TypeCat.homEquiv : (X ⟶ Y) ≃ (X → Y)`
  goes between the two. So `homEquiv` here is really `(X × A → Y) ≃ (X → A → Y)`
  with `↾` on both sides. -/

open CategoryTheory
open scoped CategoryKindergarten
set_option pp.categoryTheory.hideConcreteHom true


section

variable (A : Type)

/-- `X ↦ X × A`. -/
@[simps]
def prodRight : Type ⥤ Type where
  obj X := X × A
  map f := ↾(Prod.map f id)

/-- `Y ↦ (A → Y)`. -/
@[simps]
def expRight : Type ⥤ Type where
  obj Y := A → Y
  map g := ↾(fun h => g ∘ h)

/-- Currying, via the hom-set bijection. -/
def curryAdj : prodRight A ⊣ expRight A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sorry
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The same adjunction, via unit and counit. -/
def curryAdj' : prodRight A ⊣ expRight A :=
  Adjunction.mkOfUnitCounit
    { unit := sorry
      counit := sorry
      left_triangle := sorry
      right_triangle := sorry }

end
