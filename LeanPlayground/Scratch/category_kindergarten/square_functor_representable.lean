import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools


/- The endofunctor X ↦ X × X on `Type` is representable.

  It's covariant, so in Mathlib's vocabulary it's *co*representable:
  `F.CorepresentableBy A` packages a bijection `(A ⟶ Y) ≃ F.obj Y`, natural in `Y`.
  The representing object is `Bool`.

  Staying in `Type` (universe 0) so `Bool` can be the representing object
  without `ULift` noise.

  Note: in this Mathlib, morphisms in `Type` are a wrapper structure, not bare
  functions. Build one with `TypeCat.ofHom (g : X → Y)` (notation `↾g`), apply
  one with plain `f x` (coercion), and `TypeCat.homEquiv : (X ⟶ Y) ≃ (X → Y)`
  goes between the two. -/

open CategoryTheory
open scoped CategoryKindergarten
set_option pp.categoryTheory.hideConcreteHom true


section

/-- type with \Mfh -/
abbrev 𝔥 := @TypeCat.homEquiv

variable (X Y : Type)

/-- The squaring endofunctor `X ↦ X × X`. -/
@[simps]
def square : Type ⥤ Type where
  obj X := X × X
  map {X Y} (f : X ⟶ Y) : X × X ⟶ Y × Y := ↾(Prod.map f f)
  map_id := by
    intro A
    ext p
    rfl
    rfl
  map_comp := by
    intro A B C f g
    rfl

def fwd {X: Type} (bf: Bool → X) : X × X := (bf true, bf false)

def bwd {X: Type} (bp: X × X) : (Bool → X) :=
  fun (b: Bool) => if b then bp.1 else bp.2

def square.corepresentableBy : square.CorepresentableBy Bool where
  homEquiv := by
    intro Z
    constructor
    case toFun =>
      intro bf
      exact fwd bf
    case invFun =>
      intro p
      exact ↾bwd p
    case left_inv =>
      dsimp [autoParam, Function.LeftInverse]
      intro bz
      ext b
      dsimp [fwd, bwd]
      cases b <;> simp
    case right_inv =>
      dsimp [autoParam,
             Function.RightInverse,
             Function.LeftInverse]
      intro ob
      rfl

  homEquiv_comp := by
    simp
    intro A B g f
    dsimp [fwd]
    rfl

instance : square.IsCorepresentable :=
  square.corepresentableBy.isCorepresentable

/-- `Bool` is the chosen representing object, up to isomorphism. -/
noncomputable def square.boolIsoCoreprX : Bool ≅ square.coreprX :=
  square.corepresentableBy.isoCoreprX

-- Universal elements, per Riehl, Def. 2.3.3 (p. 62): what `𝟙 X` corresponds to under the
-- (co)representation. Mathlib's `RepresentableBy` is the contravariant side (maps *into* `X`),
-- `CorepresentableBy` the covariant side (maps *out of* `X`).

/-- The universal element of a corepresentation: the image of `𝟙 X` in `F.obj X`. -/
def CategoryTheory.Functor.CorepresentableBy.element {𝓒 : Type u} [Category 𝓒] {F : 𝓒 ⥤ Type v} {X : 𝓒}
    (e : F.CorepresentableBy X) : F.obj X :=
  e.homEquiv (𝟙 X)

/-- The universal element of a representation: the image of `𝟙 X` in `F.obj (op X)`. -/
def CategoryTheory.Functor.RepresentableBy.element {𝓒 : Type u} [Category 𝓒] {F : 𝓒ᵒᵖ ⥤ Type v} {X : 𝓒}
    (e : F.RepresentableBy X) : F.obj (Opposite.op X) :=
  e.homEquiv (𝟙 X)

example : square.corepresentableBy.element = (true, false) := rfl

/-- `boolIsoCoreprX` carries the universal element from `Bool` to the generic `coreprx`. -/
theorem square.boolIsoCoreprX_universal :
    square.map square.boolIsoCoreprX.hom square.corepresentableBy.element = square.coreprx :=
  (square.corepresentableBy.homEquiv_eq _).symm.trans (Equiv.apply_symm_apply _ _)

end
