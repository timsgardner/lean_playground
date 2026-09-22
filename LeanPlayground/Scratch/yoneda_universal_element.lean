/-
  From a natural transformation out of a covariant representable functor to
  the universal element it classifies, via the (co)Yoneda lemma.

  Setup: `F : C ⥤ Type v` a covariant functor and `X : C` an object such that
  `F` is corepresented by `X`, i.e. we have a chosen
  `e : F.CorepresentableBy X`, unfolding to a natural bijection
  `e.homEquiv : (X ⟶ Y) ≃ F.obj Y`. Equivalently (see `corepresentableByEquiv`)
  an isomorphism `coyoneda.obj (op X) ≅ F`, i.e. `Hom(X, -) ≅ F`.

  The (co)Yoneda lemma says precisely that natural transformations
  `Hom(X, -) ⟶ G` correspond bijectively to elements of `G.obj X`, for *any*
  target `G`. Specializing `G := F` and composing with `e.homEquiv`'s inverse
  direction recovers the classical fact: giving a natural transformation
  `η : Hom(X, -) ⟶ F` is the same as giving a single element `x : F.obj X`
  (its value at `𝟙 X`), and this `x` is exactly the "universal element" that
  makes `(X, x)` universal among pairs `(Y, y : F.obj Y)`.

  Dictionary (Riehl ↔ Mathlib):
    covariant representable functor `Hom(X, -)`   ↔  `coyoneda.obj (op X)`
    universal element of `F` at `X`               ↔  `Functor.coreprx` /
                                                       `e.homEquiv (𝟙 X)`
    "the universal arrow classifies nat. transf." ↔  `Functor.corepresentableByEquiv`,
                                                       `yonedaEquiv` (in `Cᵒᵖ`-form)
-/

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

universe v u

namespace CovariantYonedaDemo

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type v)

section GivenCorepresentation

/-!
### Starting from a corepresentation of `F`

Suppose `F` is already known to be corepresented by some object `X`, packaged
as `e : F.CorepresentableBy X`. The Yoneda lemma, specialized to `G := F`,
says precomposition with `e` sets up a bijection between natural
transformations `coyoneda.obj (op X) ⟶ F` and elements of `F.obj X`.
-/

variable {X : C} (e : F.CorepresentableBy X)

/-- The isomorphism `Hom(X, -) ≅ F` induced by the corepresentation `e`,
i.e. `F` really is (naturally) the covariant representable functor at `X`. -/
noncomputable def isoOfCorepresentableBy : coyoneda.obj (op X) ≅ F :=
  e.toIso

/-- Reading off the universal element of `F` at `X` directly from the
corepresentation: it is the image of the identity `𝟙 X` under the natural
bijection `Hom(X, -) ≃ F.obj -` at the object `X` itself. This is the point
`x₀ : F.obj X` such that every other `y : F.obj Y` factors uniquely as
`F.map f x₀` for a (unique) `f : X ⟶ Y`. -/
def universalElement : F.obj X :=
  e.homEquiv (𝟙 X)

/-- Every natural transformation `η : Hom(X, -) ⟶ F` arises this way: it is
determined by (and can be reconstructed from) the single element
`η.app X (𝟙 X) : F.obj X`. This is `yonedaEquiv`, unwound for the covariant
functor `coyoneda.obj (op X)` via `Coyoneda.objOpOp`/the corepresentable
package rather than stated for `Cᵒᵖ` directly. -/
example (η : coyoneda.obj (op X) ⟶ F) :
    ∃ x : F.obj X, ∀ {Y : C} (f : X ⟶ Y), η.app Y f = F.map f x :=
  ⟨η.app X (𝟙 X), fun {Y} f => by
    have := η.naturality_apply f (𝟙 X)
    simpa using this⟩

/-- Conversely, every element `x : F.obj X` assembles into a natural
transformation `Hom(X, -) ⟶ F`, namely `f ↦ F.map f x`, and this is exactly
`e.homEquiv.symm` transported along naturality (`homEquiv_symm_comp`). The
two directions are mutually inverse, which is the content of the Yoneda
lemma in the covariant case. -/
def natTransOfElement (x : F.obj X) : coyoneda.obj (op X) ⟶ F where
  app Y := TypeCat.ofHom fun f : X ⟶ Y => F.map f x
  naturality {Y Y'} g := by
    ext f
    simp

end GivenCorepresentation

section RecoveringUniversality

/-!
### Unpacking universality of the pair `(X, x₀)`

The universal element `x₀ := e.homEquiv (𝟙 X)` from the previous section
satisfies the universal property directly: given any `Y : C` and any
`y : F.obj Y`, there is a *unique* `f : X ⟶ Y` with `F.map f x₀ = y`, namely
`f := e.homEquiv.symm y`. This is precisely the comma-category universal
arrow for the composite `Hom(X, -) ⟶ F` being an isomorphism at the
identity component — the same phenomenon as in
`universal_comma_arrows_adjunction.lean`, specialized to `Type`-valued
functors instead of a general `G : D ⥤ C`.
-/

variable {X : C} (e : F.CorepresentableBy X)

/-- Existence: every `y : F.obj Y` is hit by the universal element after
applying `F` to the mediating morphism `e.homEquiv.symm y`. -/
theorem exists_mediating {Y : C} (y : F.obj Y) :
    ∃ f : X ⟶ Y, F.map f (universalElement F e) = y := by
  refine ⟨e.homEquiv.symm y, ?_⟩
  unfold universalElement
  rw [← e.homEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- Uniqueness: the mediating morphism is pinned down by `e.homEquiv`'s
injectivity, using `homEquiv_eq` to relate `F.map f x₀` back to `e.homEquiv f`. -/
theorem unique_mediating {Y : C} (f g : X ⟶ Y)
    (hf : F.map f (universalElement F e) = e.homEquiv g) : f = g := by
  apply e.homEquiv.injective
  rw [e.homEquiv_eq f]
  exact hf

end RecoveringUniversality

section FromNatTransToUniversalObject

/-!
### The other direction: starting from a nat. transf. and reading off the object

This is the shape of question the file title promises: given *only* a
covariant representable functor `Hom(X, -)` (packaged as `coyoneda.obj (op X)`)
together with a natural transformation `η : coyoneda.obj (op X) ⟶ F`, produce
the pair `(X, η.app X (𝟙 X))` and certify that it is universal — i.e. recover
`F.CorepresentableBy X` from `η`, granting that `η` is a natural
isomorphism (equivalently, that `F` is corepresented by `X` via `η`).
-/

variable {X : C} (η : coyoneda.obj (op X) ⟶ F) (hη : ∀ Y, Function.Bijective (η.app Y))

/-- The universal element extracted from `η`: evaluate at the identity. -/
def elementOfNatTrans : F.obj X :=
  η.app X (𝟙 X)

/-- When `η` is a natural isomorphism (`hη`), it assembles into a full
`F.CorepresentableBy X`, whose `homEquiv` at `Y` is literally `η.app Y`
packaged as an `Equiv` via its bijectivity, and whose naturality clause is
exactly `η.naturality`. -/
noncomputable def corepresentableByOfNatIso : F.CorepresentableBy X where
  homEquiv {Y} := Equiv.ofBijective (η.app Y) (hη Y)
  homEquiv_comp {Y Y'} g f := by
    have := η.naturality_apply g f
    simpa using this

/-- Sanity check: the universal element read off this reconstructed
corepresentation agrees with `elementOfNatTrans`. -/
example : (corepresentableByOfNatIso F η hη).homEquiv (𝟙 X) = elementOfNatTrans F η :=
  rfl

end FromNatTransToUniversalObject

end CovariantYonedaDemo
