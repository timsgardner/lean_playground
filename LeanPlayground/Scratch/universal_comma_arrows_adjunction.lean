/-
  Universal arrows and the comma-category characterization of adjunctions.

  A worked template for `Mathlib.CategoryTheory.Adjunction.Comma`: building
  an adjunction `F ⊣ G` out of a family of universal arrows, and unpacking
  an existing adjunction back into that comma-category data.

  Dictionary (Riehl ↔ Mathlib):
    comma category (A ↓ G)              ↔  StructuredArrow A G
    object (B, f : A ⟶ G B) of (A ↓ G)  ↔  StructuredArrow.mk (f : A ⟶ G.obj B)
    universal arrow from A to G         ↔  IsInitial (X : StructuredArrow A G)
    "F ⊣ G"                             ↔  Adjunction F G

-/

import Mathlib

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂

namespace UniversalArrowTemplate

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (G : D ⥤ C)

section ForwardDirection

/-!
### From a family of universal arrows to an adjunction

Suppose that for each `A : C` a construction elsewhere in the development
(a free-object construction, a Kan-extension formula, etc.) has already
produced a candidate object `F₀ A : D` together with a map
`η A : A ⟶ G.obj (F₀ A)`. The claim that `η A` is a universal arrow is
exactly the claim that the corresponding object of `StructuredArrow A G`
is initial.
-/

variable (F₀ : C → D) (η : ∀ A, A ⟶ G.obj (F₀ A))

/-- The candidate universal arrow from `A` to `G`, viewed as an object of
the comma category `StructuredArrow A G`. -/
def candidate (A : C) : StructuredArrow A G :=
  StructuredArrow.mk (η A)

/-- Repackaging the universal property of `η A` as initiality of
`candidate G F₀ η A`. The two arguments are precisely the classical
factorization and uniqueness clauses: `desc` produces, for every
`B : StructuredArrow A G`, the mediating morphism out of the candidate,
and `uniq` shows it is the only one. A morphism `candidate A ⟶ B` in
`StructuredArrow A G` is built with `StructuredArrow.homMk`, whose
underlying datum is a map `F₀ A ⟶ B.right` in `D` making the triangle
with `η A` and `B.hom` commute — this is where the freeness (or
Kan-extension universal property, or whatever produced `F₀`) actually
gets invoked. -/
def isInitialCandidate (A : C)
    (desc : ∀ B : StructuredArrow A G, candidate G F₀ η A ⟶ B)
    (uniq : ∀ (B : StructuredArrow A G) (m : candidate G F₀ η A ⟶ B),
      m = desc B) :
    IsInitial (candidate G F₀ η A) :=
  IsInitial.ofUniqueHom desc uniq

/-- Given initiality data at every `A`, we get the `HasInitial` instances
that `leftAdjointOfStructuredArrowInitials` and
`adjunctionOfStructuredArrowInitials` are stated against. -/
def hasInitialOfIsInitial
    (h : ∀ A, IsInitial (candidate G F₀ η A)) :
    ∀ A, HasInitial (StructuredArrow A G) :=
  fun A => (h A).hasInitial

variable (h : ∀ A, IsInitial (candidate G F₀ η A))

/-- The induced left adjoint, read off from the family of universal
arrows. -/
noncomputable def leftAdjoint : C ⥤ D :=
  haveI := hasInitialOfIsInitial G F₀ η h
  leftAdjointOfStructuredArrowInitials G

/-- The induced adjunction `leftAdjoint ⊣ G`. Once `isInitialCandidate`
is discharged at every object, the adjunction itself is free — it
directly follows from `adjunctionOfStructuredArrowInitials`. -/
noncomputable def adjunction : leftAdjoint G F₀ η h ⊣ G :=
  haveI := hasInitialOfIsInitial G F₀ η h
  adjunctionOfStructuredArrowInitials G

end ForwardDirection

section BackwardDirection

/-!
### From an adjunction back to universal arrows

Given an adjunction constructed some other way (e.g. via
`Adjunction.mkOfHomEquiv` from an explicit hom-set bijection),
`mkInitialOfLeftAdjoint` hands back the comma-category incarnation of the
unit at each `A` as an initial object of `StructuredArrow A G`. This is
the shape the data needs to be in to feed into comma-category or
Grothendieck-construction arguments phrased in terms of
`StructuredArrow`/`Comma` further downstream.
-/

variable {F : C ⥤ D} (adj : F ⊣ G)

/-- The unit of `adj` at `A`, repackaged as an initial object of the
comma category `StructuredArrow A G`. -/
def initialOfAdjunction (A : C) :
    IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
  mkInitialOfLeftAdjoint G adj A

end BackwardDirection

/-!
### A note on universes

`StructuredArrow A G` for `G : D ⥤ C` with `C : Type u₁`, `D : Type u₂`
lives at `max u₁ v₂` (see `instCategoryStructuredArrow`). For a
construction where `D` is large — a free-object functor landing in
`Type`-valued algebraic structures, say — worth checking that the
`HasInitial` instances above actually unify at that universe before
`isInitialCandidate` is fully written out; that is a cheaper failure
mode to catch early than after the fact.
-/

end UniversalArrowTemplate
