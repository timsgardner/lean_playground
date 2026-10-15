import Mathlib.CategoryTheory.Types.Basic

/- # Morphisms in `Type`: the three levels, with no coercions

A morphism `X ⟶ Y` in the category `Type` is *not* a function. Mathlib stacks
two wrapper structures on top of the plain function:

    level 1   X ⟶ Y               morphism (definitionally `TypeCat.Hom X Y`)
                │   ▲
         hom    │   │  ofHom          ConcreteCategory.homEquiv
                ▼   │
    level 2   TypeCat.Fun X Y     "bundled function": the `FC` of the
                │   ▲              `ConcreteCategory (Type u) TypeCat.Fun` instance
       .toFun   │   │  Fun.mk         TypeCat.Fun.homEquiv X Y
                ▼   │
    level 3   X → Y               plain function

  Step-by-step maps (four):
    `ConcreteCategory.hom`   : (X ⟶ Y) → TypeCat.Fun X Y
    `ConcreteCategory.ofHom` : TypeCat.Fun X Y → (X ⟶ Y)
    `TypeCat.Fun.toFun`      : TypeCat.Fun X Y → (X → Y)
    `TypeCat.Fun.mk`         : (X → Y) → TypeCat.Fun X Y

  The same steps as equivalences (two):
    `ConcreteCategory.homEquiv` : (X ⟶ Y) ≃ TypeCat.Fun X Y
    `TypeCat.Fun.homEquiv X Y`  : TypeCat.Fun X Y ≃ (X → Y)

  Shortcuts that go straight between levels 1 and 3:
    `TypeCat.homEquiv` : (X ⟶ Y) ≃ (X → Y)   -- the two equivalences composed
    `TypeCat.ofHom`    : (X → Y) → (X ⟶ Y)   -- notation `↾h`

  Why two wrappers? Level 2 is the generic interface: every concrete category
  (groups, rings, ...) has a type of bundled functions, here `TypeCat.Fun`, and
  general `ConcreteCategory` lemmas are stated in terms of it. Level 1 keeps
  morphisms from *being* that type, so that the category's `⟶` and its
  function-like structure stay separate.

  This file avoids coercions entirely: every conversion below is a named
  function applied by hand. Where coercions kick in is a separate topic. -/

open CategoryTheory

variable {X Y Z : Type}


/-! ## 1. The three types -/

-- Level 1 is literally the structure `TypeCat.Hom`.
example : (X ⟶ Y) = TypeCat.Hom X Y := rfl

-- `TypeCat.Hom` has one field, `hom'`, and its constructor `TypeCat.Hom.mk` is
-- *private*: you cannot write `TypeCat.Hom.mk g`. The only public way up from
-- level 2 to level 1 is `ConcreteCategory.ofHom`.
#check @TypeCat.Hom.hom'   -- the raw field: TypeCat.Hom X Y → TypeCat.Fun X Y

-- Level 2 is the structure `TypeCat.Fun`, one field `toFun`, public constructor.
#check @TypeCat.Fun.mk     -- (X → Y) → TypeCat.Fun X Y
#check @TypeCat.Fun.toFun  -- TypeCat.Fun X Y → (X → Y)


/-! ## 2. Going up: function → bundled function → morphism

Running example: boolean negation, lifted one level at a time. -/

def notFun : Bool → Bool := not                                  -- level 3

def notBundled : TypeCat.Fun Bool Bool := TypeCat.Fun.mk notFun  -- level 2

def notMor : Bool ⟶ Bool := ConcreteCategory.ofHom notBundled    -- level 1

-- The shortcut `TypeCat.ofHom` does both steps at once. It is *defined* as
-- `ConcreteCategory.ofHom (TypeCat.Fun.mk h)`, so this is `rfl`.
example : TypeCat.ofHom notFun = notMor := rfl


/-! ## 3. Going down: morphism → bundled function → function -/

example : TypeCat.Fun Bool Bool := ConcreteCategory.hom notMor            -- 1 → 2
example : Bool → Bool := (ConcreteCategory.hom notMor).toFun              -- 1 → 3

-- `TypeCat.Hom.hom` (dot notation: `notMor.hom`) is an abbreviation for
-- `ConcreteCategory.hom`, specialised to `Type`.
example : notMor.hom = ConcreteCategory.hom notMor := rfl

-- Evaluating a morphism at a point, fully explicitly: go down to level 3,
-- then apply.
example : (ConcreteCategory.hom notMor).toFun true = false := rfl


/-! ## 4. Round trips

Each up-then-down or down-then-up trip is the identity. All of these hold by
`rfl`; the named lemmas are what `simp` and `rw` use. -/

-- Between levels 2 and 3 (structure eta and projection-of-constructor).
example (h : X → Y) : (TypeCat.Fun.mk h).toFun = h := rfl
example (g : TypeCat.Fun X Y) : TypeCat.Fun.mk g.toFun = g := rfl

-- Between levels 1 and 2. These are fields of the `ConcreteCategory` class,
-- so they hold in every concrete category, not just `Type`.
example (g : TypeCat.Fun X Y) :
    ConcreteCategory.hom (ConcreteCategory.ofHom g) = g :=
  ConcreteCategory.hom_ofHom g
example (f : X ⟶ Y) :
    ConcreteCategory.ofHom (ConcreteCategory.hom f) = f :=
  ConcreteCategory.ofHom_hom f

-- Between levels 1 and 3, through the shortcut.
example (h : X → Y) :
    (ConcreteCategory.hom (TypeCat.ofHom h)).toFun = h := rfl
example (f : X ⟶ Y) :
    TypeCat.ofHom (ConcreteCategory.hom f).toFun = f := rfl


/-! ## 5. The same maps, packaged as equivalences

An `Equiv` `e : A ≃ B` is a structure with fields `e.toFun : A → B` and
`e.invFun : B → A` (plus the two round-trip proofs from section 4). Writing
`e a` or `e.symm b` is itself a coercion, so here we use the fields. -/

-- Levels 1 ≃ 2: the fields are exactly `hom` and `ofHom`.
example (f : X ⟶ Y) :
    ConcreteCategory.homEquiv.toFun f = ConcreteCategory.hom f := rfl
example (g : TypeCat.Fun X Y) :
    ConcreteCategory.homEquiv.invFun g = (ConcreteCategory.ofHom g : X ⟶ Y) := rfl

-- Levels 2 ≃ 3: the fields are exactly `.toFun` and `Fun.mk`.
-- (Note that `X` and `Y` are explicit arguments here.)
example (g : TypeCat.Fun X Y) :
    (TypeCat.Fun.homEquiv X Y).toFun g = g.toFun := rfl
example (h : X → Y) :
    (TypeCat.Fun.homEquiv X Y).invFun h = TypeCat.Fun.mk h := rfl

-- Levels 1 ≃ 3: `TypeCat.homEquiv` is literally the composite.
example : (TypeCat.homEquiv : (X ⟶ Y) ≃ (X → Y)) =
    ConcreteCategory.homEquiv.trans (TypeCat.Fun.homEquiv X Y) := rfl

example : TypeCat.homEquiv.toFun notMor = notFun := rfl
example : TypeCat.homEquiv.invFun notFun = notMor := rfl


/-! ## 6. Identity and composition at each level

Composition is defined at level 2 (`TypeCat.Fun.comp`) and computes to `∘` at
level 3. Watch the order: `f ≫ g` is "f then g", but `TypeCat.Fun.comp` and `∘`
take the *second* map first. -/

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) =
      TypeCat.Fun.comp (ConcreteCategory.hom g) (ConcreteCategory.hom f) := rfl

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ConcreteCategory.hom (f ≫ g)).toFun =
      (ConcreteCategory.hom g).toFun ∘ (ConcreteCategory.hom f).toFun := rfl

example : ConcreteCategory.hom (𝟙 X) = TypeCat.Fun.id X := rfl
example : (ConcreteCategory.hom (𝟙 X)).toFun = id := rfl


/-! ## 7. Proving two morphisms equal: peel one layer at a time

Each level has its own extensionality lemma, which moves the goal down one
level:

    `ConcreteCategory.ext` : hom f = hom g → f = g          (level 1 → 2)
    `TypeCat.Fun.ext`      : g.toFun = g'.toFun → g = g'    (level 2 → 3)
    `funext`               : (∀ x, h x = h' x) → h = h'    (level 3 → points)

(`TypeCat.Hom.ext` also does 1 → 2, but it is stated with the raw field
`hom'` rather than `ConcreteCategory.hom`.) -/

example : notMor ≫ notMor = 𝟙 Bool := by
  -- ⊢ notMor ≫ notMor = 𝟙 Bool
  apply ConcreteCategory.ext
  -- ⊢ ConcreteCategory.hom (notMor ≫ notMor) = ConcreteCategory.hom (𝟙 Bool)
  apply TypeCat.Fun.ext
  -- ⊢ (ConcreteCategory.hom (notMor ≫ notMor)).toFun
  --     = (ConcreteCategory.hom (𝟙 Bool)).toFun
  funext b
  -- ⊢ (ConcreteCategory.hom (notMor ≫ notMor)).toFun b
  --     = (ConcreteCategory.hom (𝟙 Bool)).toFun b
  cases b <;> rfl


/-! ## 8. Worked transport: lifting `Prod.map` to the squaring functor's action

The squaring functor needs, for each morphism `f : X ⟶ Y`, a morphism
`X × X ⟶ Y × Y`. `Prod.map` only works at level 3, so we go down, map, and
come back up. Each step is spelled out below. -/

def squareMap (f : X ⟶ Y) : X × X ⟶ Y × Y :=
  let f₂ : TypeCat.Fun X Y := ConcreteCategory.hom f               -- 1 → 2
  let f₃ : X → Y := f₂.toFun                                       -- 2 → 3
  let m₃ : X × X → Y × Y := Prod.map f₃ f₃                         -- work at 3
  let m₂ : TypeCat.Fun (X × X) (Y × Y) := TypeCat.Fun.mk m₃        -- 3 → 2
  ConcreteCategory.ofHom m₂                                        -- 2 → 1

-- With the shortcuts, the round trip is one line on each side.
def squareMap' (f : X ⟶ Y) : X × X ⟶ Y × Y :=
  TypeCat.ofHom (Prod.map (TypeCat.homEquiv.toFun f) (TypeCat.homEquiv.toFun f))

example (f : X ⟶ Y) : squareMap f = squareMap' f := rfl

-- `square.map` in `square_functor_representable.lean` is written
-- `↾(Prod.map f f)`. That passes the morphism `f` straight to `Prod.map`,
-- which expects a function, so a coercion inserts the 1 → 3 step. Which
-- coercion, and what it unfolds to, is the next topic.
