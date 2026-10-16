import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
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

  The statements of `left_triangle` and `right_triangle` use two operations on
  natural transformations, whiskering and the associator.

  Whiskering composes a natural transformation with a functor, producing a new
  natural transformation. For `α : H ⟶ K` a natural transformation between functors
  `H K : D ⥤ E`, and functors `F : C ⥤ D` and `L : E ⥤ E'`:

    whiskerLeft F α  : F ⋙ H ⟶ F ⋙ K     (the functor `F` is applied first)
    whiskerRight α L : H ⋙ L ⟶ K ⋙ L     (the functor `L` is applied last)

  For any three composable functors `P`, `Q`, `R`, the associator
  `Functor.associator P Q R : (P ⋙ Q) ⋙ R ≅ P ⋙ (Q ⋙ R)` is a natural isomorphism
  between the two ways of bracketing their composite.
  Every component of the associator is an identity morphism. The two bracketings are
  even equal by `rfl`, but they are written differently, and `≫` needs the target of
  its first argument to be written exactly like the source of its second.

  That mismatch is why the associator appears in `left_triangle`. The two whiskered
  natural transformations in `left_triangle` have these types:

    whiskerRight unit F  : 𝟭 C ⋙ F ⟶ (F ⋙ G) ⋙ F
    whiskerLeft F counit : F ⋙ (G ⋙ F) ⟶ F ⋙ 𝟭 D

  The target of the first is `(F ⋙ G) ⋙ F` and the source of the second is
  `F ⋙ (G ⋙ F)`, so `(associator F G F).hom` is placed between them to convert one
  bracketing into the other. In `right_triangle`, `(associator G F G).inv` does the
  same job in the opposite direction, from `G ⋙ (F ⋙ G)` to `(G ⋙ F) ⋙ G`. Because
  every component of the associator is an identity, the associator disappears once
  the triangle identities are reduced to components.

  The fields `left_triangle` and `right_triangle` are the triangle identities stated
  as equations between whole natural transformations, rather than one component at
  a time as in `Adjunction`. To prove either of them, first run `ext X` to reduce
  the equation to its component at `X`. In `Type`, `ext X` keeps going and also
  reduces to an arbitrary element; `ext X : 2` stops at the component, and
  `ext X ⟨x, a⟩` goes to an element and splits it when it is a pair.

  Next, compute the component of each piece of the equation. These simp lemmas do
  that:

    Functor.whiskerRight_app : (whiskerRight α F).app X = F.map (α.app X)
    Functor.whiskerLeft_app  : (whiskerLeft F α).app X  = α.app (F.obj X)
    Functor.associator_hom_app : (associator P Q R).hom.app X = 𝟙 _
    Functor.associator_inv_app : (associator P Q R).inv.app X = 𝟙 _
    NatTrans.comp_app        : (α ≫ β).app X = α.app X ≫ β.app X
    NatTrans.id_app'         : (NatTrans.id F).app X = 𝟙 (F.obj X)

  With these lemmas alone, the left triangle gets stuck at

    F.map (unit.app X) ≫ 𝟙 (((F ⋙ G) ⋙ F).obj X) ≫ counit.app (F.obj X) = 𝟙 ((𝟭 C ⋙ F).obj X)

  The `𝟙` left over from the associator should cancel by `Category.id_comp`, but it
  does not. The `𝟙` is written at the object `((F ⋙ G) ⋙ F).obj X`, while
  `counit.app (F.obj X)` starts at the object `(G ⋙ F).obj (F.obj X)`. These two
  objects are equal by definition but are written differently, and simp needs them
  to match as written. Plain `simp` gets stuck in the same place.

  The fix is to unfold every `(P ⋙ Q).obj X` into `Q.obj (P.obj X)` first, so that
  both objects are written `F.obj (G.obj (F.obj X))`. The lemma that does this,
  `Functor.comp_obj`, is ignored by `dsimp` in this version of Mathlib unless the
  option `backward.defeqAttrib.useBackward` is on. With the option on, this
  sequence reaches the componentwise triangle identity, in the same form as
  `left_triangle_components` or `right_triangle_components` above:

    set_option backward.defeqAttrib.useBackward true in
    ...
      ext X        -- in `Type`, use `ext X : 2` to stop at the component
      dsimp        -- computes the components and unfolds `⋙`
      simp only [Category.id_comp]

  Without the option, `erw [Category.id_comp]` after the simp lemmas also removes
  the `𝟙`, because `erw` compares the objects by definitional equality rather than
  as written.

  For a concrete adjunction such as the currying example below, none of this is
  necessary: both sides of each triangle identity compute to the identity, so
  `rfl` closes it directly.

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
    { homEquiv := by
        intro X Y
        constructor
        case toFun =>
          intro m1
          dsimp [prodRight] at m1
          dsimp [expRight]
          exact ↾(fun (x: X) (a: A) => m1 (x, a))
        case invFun =>
          dsimp [expRight, prodRight]
          intro m1
          exact ↾(fun (p: X × A) => m1 p.1 p.2)
        case left_inv =>
          dsimp [autoParam, Function.LeftInverse, prodRight]
          intro p
          rfl
        case right_inv =>
          dsimp [autoParam, Function.RightInverse, Function.LeftInverse, expRight]
          intro m
          rfl
      homEquiv_naturality_left_symm := by
        dsimp
        intro B C D f g
        dsimp [prodRight]
        rfl
      homEquiv_naturality_right := by
        cat_disch }

/-- The currying adjunction `(- × A) ⊣ (A → -)` again, this time built from a unit
and a counit with `Adjunction.mkOfUnitCounit`. -/
def curryAdj' : prodRight A ⊣ expRight A :=
  Adjunction.mkOfUnitCounit
    { unit := by
        constructor
        case app =>
          intro B
          apply TypeCat.ofHom
          dsimp
          intro b
          dsimp [Functor.comp, expRight, prodRight]
          exact (fun a => (b, a))
        case naturality =>
          dsimp [autoParam, prodRight, expRight]
          intro X Y f
          rfl
      counit := by
        constructor
        case app =>
          intro X
          dsimp [Functor.comp, prodRight, expRight]
          exact ↾(fun p => p.1 p.2) -- ie, eval
        case naturality =>
          dsimp [autoParam]
          intro X Y f
          dsimp [prodRight, expRight]
          rfl
      left_triangle := by
        cat_disch
      right_triangle := by
        cat_disch}

/- ## The induced monad: State

  Every adjunction `adj : F ⊣ G` gives a monad `adj.toMonad` on `C`. Its functor is
  `F ⋙ G`, its unit is the unit of the adjunction, and its multiplication is the
  counit, whiskered so that it fits between two copies of `G`:

    adj.toMonad.η = adj.unit
    adj.toMonad.μ = whiskerRight (whiskerLeft F adj.counit) G
      component at X:  G.map (adj.counit.app (F.obj X))

  Dually, `adj.toComonad` is a comonad on `D` with functor `G ⋙ F`, counit
  `adj.counit`, and comultiplication built from `adj.unit` in the same way.

  For the currying adjunction, `F ⋙ G` sends `X` to `A → X × A`. That is the state
  monad with state type `A`; Lean's `StateM A X` is this same type. Writing `T` for
  the monad:

    T.obj X   = A → X × A
    T.map f m = fun a => (f (m a).1, (m a).2)   -- change the result, keep the state
    η x       = fun a => (x, a)                 -- return `x`, leave the state alone
    μ m       = fun a => (m a).1 (m a).2        -- run `m`, then run the computation
                                                -- it returned on the new state

  Here `μ` is `G.map` of the counit, and the counit is evaluation `(f, a) ↦ f a`.
  So `μ` runs `m` to get a pair (computation, state) and evaluates the computation
  at the state.

  Bind is `μ` after `T.map`: `m >>= k = μ (T.map k m)`. Unfolding gives
  `fun a => k (m a).1 (m a).2`, which is `StateM`'s bind.

  The comonad `G ⋙ F` sends `Y` to `(A → Y) × A`, the store comonad. Its counit
  `ε (f, a) = f a` reads the stored value, and its comultiplication
  `δ (f, a) = (fun a' => (f, a'), a)` replaces the value at each position `a'` with
  the whole store focused on `a'`.

  `curryAdj` has no `@[simps]` attribute, so `dsimp` and `simp` do not unfold these
  components. They hold by `rfl`, as the examples below check. -/

/-- The state monad with state type `A`, induced by the currying adjunction. -/
abbrev stateMonad : Monad Type := (curryAdj A).toMonad

example (X : Type) : (stateMonad A).obj X = (A → X × A) := rfl
example (X : Type) : (stateMonad A).obj X = StateM A X := rfl

example (X Y : Type) (f : X ⟶ Y) (m : A → X × A) :
    (stateMonad A).map f m = fun a => (f (m a).1, (m a).2) := rfl

example (X : Type) (x : X) : (stateMonad A).η.app X x = fun a => (x, a) := rfl

example (X : Type) (m : A → (A → X × A) × A) :
    (stateMonad A).μ.app X m = fun a => (m a).1 (m a).2 := rfl

/-- Bind for `stateMonad A`, built from `μ` and `map`. -/
def stateBind {X Y : Type} (m : (stateMonad A).obj X) (k : X → (stateMonad A).obj Y) :
    (stateMonad A).obj Y :=
  (stateMonad A).μ.app Y ((stateMonad A).map (↾k) m)

example {X Y : Type} (m : A → X × A) (k : X → A → Y × A) :
    stateBind A m k = fun a => k (m a).1 (m a).2 := rfl

/-- `η` and `stateBind` agree with Lean's `pure` and `>>=` for `StateM A`. -/
example {X : Type} (x : X) : (stateMonad A).η.app X x = (pure x : StateM A X) := rfl
example {X Y : Type} (m : StateM A X) (k : X → StateM A Y) :
    stateBind A m k = (m >>= k) := rfl

/- ### Running the state monad on strings

  Take the state type to be `ℕ`, used to count how many operations have run, and
  let the results be strings. Each operation below builds a string and adds one
  to the count:

    greet   s = fun n => ("hello, " ++ s, n + 1)
    exclaim s = fun n => (s ++ "!", n + 1)

  `pipeline` greets `"world"`, then exclaims twice. Each step receives the
  previous step's string, and bind carries the count from one step to the next.
  Run from a count of `0`, it gives `("hello, world!!", 3)`: the final string, and
  the three operations it took to get there.

  Binding is `μ` after `map`, and the two can be run separately. `map exclaim`
  applied to `greet "world"` runs only the greeting. Its result is the computation
  `exclaim "hello, world"`, which has not run yet, and the count stands at `1`.
  `μ` runs that leftover computation, giving `("hello, world!", 2)`. -/

/-- Prepend `"hello, "`, counting one operation. -/
def greet (s : String) : (stateMonad ℕ).obj String := fun n => ("hello, " ++ s, n + 1)

/-- Append `"!"`, counting one operation. -/
def exclaim (s : String) : (stateMonad ℕ).obj String := fun n => (s ++ "!", n + 1)

/-- Greet `"world"`, then exclaim twice. -/
def pipeline : (stateMonad ℕ).obj String :=
  stateBind ℕ (greet "world") fun s =>
  stateBind ℕ (exclaim s) fun t =>
  exclaim t

#eval pipeline 0  -- ("hello, world!!", 3)
example : pipeline 0 = ("hello, world!!", 3) := rfl

/-- `map` changes the result and leaves the count alone. -/
example : (stateMonad ℕ).map (↾String.length) pipeline 0 = (14, 3) := rfl

/-- `map exclaim` without `μ`: the greeting has run, and the exclaim is left over
as the result. -/
def greetThenExclaim : (stateMonad ℕ).obj ((stateMonad ℕ).obj String) :=
  (stateMonad ℕ).map (↾exclaim) (greet "world")

example : (greetThenExclaim 0).2 = 1 := rfl
example : (greetThenExclaim 0).1 1 = ("hello, world!", 2) := rfl

#eval (stateMonad ℕ).μ.app String greetThenExclaim 0  -- ("hello, world!", 2)
example : (stateMonad ℕ).μ.app String greetThenExclaim 0 = ("hello, world!", 2) := rfl

/-- The store comonad with position type `A`, induced by the currying adjunction. -/
abbrev storeComonad : Comonad Type := (curryAdj A).toComonad

example (Y : Type) : (storeComonad A).obj Y = ((A → Y) × A) := rfl

example (Y : Type) (p : (A → Y) × A) : (storeComonad A).ε.app Y p = p.1 p.2 := rfl

example (Y : Type) (p : (A → Y) × A) :
    (storeComonad A).δ.app Y p = (fun a' => (p.1, a'), p.2) := rfl

end
