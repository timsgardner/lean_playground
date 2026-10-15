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
    #check 𝔥.symm fwd
    refine ⟨𝔥.symm (@fwd Z), bwd, ?_, ?_⟩

    sorry
  homEquiv_comp := by
    sorry

example : square.IsCorepresentable := by
  sorry

end
