import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools


/- # Adjunctions

  Throughout these notes, `F : C ⥤ D` and `G : D ⥤ C` are functors, `X`, `X'` are
  objects of `C`, and `Y`, `Y'` are objects of `D`.

  Mathlib writes "`F` is left adjoint to `G`" as `F ⊣ G` (typed `\dashv`), which is
  notation for the structure `Adjunction F G`. An `Adjunction F G` has four fields: a
  unit, a counit, and the two triangle identities, which are stated one component
  at a time.

    unit   : 𝟭 C ⟶ F ⋙ G
    counit : G ⋙ F ⟶ 𝟭 D
    left_triangle_components  X : F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X)
    right_triangle_components Y : unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y)

  The hom-set bijection is not a field. Mathlib defines it from the unit and the
  counit as `adj.homEquiv`:

    adj.homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
      forward:  f ↦ unit.app X ≫ G.map f
      backward: g ↦ F.map g ≫ counit.app Y

  ## Building an adjunction

  Mathlib has two constructors for `Adjunction F G`, one for each of the two
  textbook definitions of an adjunction. Each constructor takes an auxiliary
  structure whose fields are what you need to supply.

  The first textbook definition is a bijection of hom-sets that is natural in both
  `X` and `Y`. The constructor for it is `Adjunction.mkOfHomEquiv`, which takes a
  `CoreHomEquiv F G` with these three fields:

    homEquiv X Y : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g
    homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g

  Each naturality field is stated for one direction of the bijection only.
  Naturality in `X` is stated for the backward map `(homEquiv X Y).symm`, and
  naturality in `Y` is stated for the forward map `homEquiv X Y`. Mathlib proves the
  two remaining statements from these, so you do not supply them.

  The second textbook definition is a unit and a counit satisfying the triangle
  identities. The constructor for it is `Adjunction.mkOfUnitCounit`, which takes a
  `CoreUnitCounit F G` with these four fields:

    unit   : 𝟭 C ⟶ F ⋙ G
    counit : G ⋙ F ⟶ 𝟭 D
    left_triangle :
      whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit = NatTrans.id (𝟭 C ⋙ F)
    right_triangle :
      whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G = NatTrans.id (G ⋙ 𝟭 C)

  The `unit` and the `counit` are natural transformations, so you build each one by
  giving its components (the `app` field) and a proof that those components are
  natural (the `naturality` field).

  The fields `left_triangle` and `right_triangle` are the triangle identities stated
  as equations between whole natural transformations, rather than one component at
  a time as in `Adjunction`. To prove either of them, run `ext X` to reduce the
  equation to its component at `X`. Then simplify that component using these simp
  lemmas, which compute the component of each piece of the equation:

    Functor.whiskerRight_app : (whiskerRight α F).app X = F.map (α.app X)
    Functor.whiskerLeft_app  : (whiskerLeft F α).app X  = α.app (F.obj X)
    Functor.associator_hom_app : (associator F G H).hom.app X = 𝟙 _
    Functor.associator_inv_app : (associator F G H).inv.app X = 𝟙 _
    NatTrans.comp_app        : (α ≫ β).app X = α.app X ≫ β.app X
    NatTrans.id_app'         : (NatTrans.id F).app X = 𝟙 (F.obj X)

  After that simplification, the goal is the componentwise triangle identity, in
  the same form as `left_triangle_components` or `right_triangle_components` above.

  ## Using an adjunction

  For `adj : F ⊣ G`, the following lemmas are available. Here `f` and `g` are
  morphisms whose types are given with each lemma.

  These two lemmas unfold the hom-set bijection into the unit and the counit:

    adj.homEquiv_unit X Y f   : adj.homEquiv X Y f = adj.unit.app X ≫ G.map f
    adj.homEquiv_counit X Y g : (adj.homEquiv X Y).symm g = F.map g ≫ adj.counit.app Y

  These four lemmas say how the hom-set bijection interacts with composition. The
  `_left` lemmas cover precomposing with a morphism of `C`, and the `_right` lemmas
  cover postcomposing with a morphism of `D`:

    adj.homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
      adj.homEquiv X' Y (F.map f ≫ g) = f ≫ adj.homEquiv X Y g
    adj.homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
      (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g
    adj.homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
      adj.homEquiv X Y' (f ≫ g) = adj.homEquiv X Y f ≫ G.map g
    adj.homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
      (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g

  These two lemmas are the naturality squares of the unit and of the counit:

    adj.unit_naturality (f : X ⟶ X') :
      adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app X'
    adj.counit_naturality (f : Y ⟶ Y') :
      F.map (G.map f) ≫ adj.counit.app Y' = adj.counit.app Y ≫ f

  Finally, the fields `adj.left_triangle_components` and
  `adj.right_triangle_components` are both simp lemmas, so `simp` applies the
  triangle identities automatically.

  ## Running example: currying in `Type`

  Fix a type `A`. The functor `- × A` (sending `X` to `X × A`) is left adjoint to
  the functor `A → -` (sending `Y` to `A → Y`):

    (- × A) ⊣ (A → -)          (X × A ⟶ Y) ≃ (X ⟶ (A → Y))

  Below, `prodRight A` is the functor `- × A` and `expRight A` is the functor
  `A → -`. This file works only with types in universe 0, to match
  `square_functor_representable.lean`.

  A morphism `X ⟶ Y` in `Type` is not a plain function `X → Y`. It is a structure
  that wraps a plain function (see `typecat_conversions.lean` for the details). The
  following tools convert between morphisms and plain functions:

  - To build a morphism from a plain function `g : X → Y`, write `↾g`, which is
    notation for `TypeCat.ofHom g`.
  - To apply a morphism `f : X ⟶ Y` to an element `x : X`, write `f x`. Lean
    inserts the coercion from the morphism to its plain function.
  - To prove that two morphisms are equal, use `ext`, which reduces the equation to
    an equation of their values at an arbitrary element.
  - `TypeCat.homEquiv : (X ⟶ Y) ≃ (X → Y)` is the bijection between morphisms and
    plain functions.

  Because of this wrapping, the `homEquiv` field of `curryAdj` below is, in effect,
  the plain currying bijection `(X × A → Y) ≃ (X → A → Y)`, with `↾` wrapping the
  plain functions on each side into morphisms. -/

open CategoryTheory
open scoped CategoryKindergarten
set_option pp.categoryTheory.hideConcreteHom true


section

variable (A : Type)

/-- The functor `- × A`, which sends each type `X` to `X × A`. -/
@[simps]
def prodRight : Type ⥤ Type where
  obj X := X × A
  map f := ↾(Prod.map f id)

/-- The functor `A → -`, which sends each type `Y` to the function type `A → Y`. -/
@[simps]
def expRight : Type ⥤ Type where
  obj Y := A → Y
  map g := ↾(fun h => g ∘ h)

/-- The currying adjunction `(- × A) ⊣ (A → -)`, built from the hom-set bijection
with `Adjunction.mkOfHomEquiv`. -/
def curryAdj : prodRight A ⊣ expRight A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sorry
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The currying adjunction `(- × A) ⊣ (A → -)` again, this time built from a unit
and a counit with `Adjunction.mkOfUnitCounit`. -/
def curryAdj' : prodRight A ⊣ expRight A :=
  Adjunction.mkOfUnitCounit
    { unit := sorry
      counit := sorry
      left_triangle := sorry
      right_triangle := sorry }

end
