/-
# Riehl, *Category Theory in Context*, §4.2: The unit and counit as universal arrows

Section 4.1 defined an adjunction as a natural bijection between hom-sets. This section
shows that the same data can be repackaged in several other ways. The most important of
them is a pair of natural transformations, the unit and the counit, which satisfy two
equations called the triangle identities. Theorem 4.2.7 lists six equivalent presentations
of an adjunction, and most of this file is devoted to proving the equivalences among them.

The file follows the section in order.

* Part 0 recalls the notation for the components of the unit and counit.
* Part 1 constructs the unit and counit from a hom-set bijection (Lemmas 4.2.2 and 4.2.3).
* Part 2 computes them for free groups (Example 4.2.4).
* Part 3 states the triangle identities (Definition 4.2.5 and Remark 4.2.6).
* Parts 4 to 8 prove Theorem 4.2.7.
* Part 9 proves the fixed point formulae for Galois connections (Corollary 4.2.10).
* Part 10 restricts an adjunction to an equivalence (Lemma 4.2.11).
* Part 11 contains Riehl's Exercises 4.2.i to 4.2.iv.

Two conventions govern the exercises. A paragraph that begins "Suggested proof." recommends
a particular route, and the declarations it names are the ones to use. A sentence that
begins "For reference," mentions a related declaration for the sake of orientation, and the
exercise does not depend on it. Declarations whose proofs are already written are part of
the walkthrough, and only the occurrences of `sorry` are exercises.

Riehl writes composition in the applicative order, so that the book's `G ε_d · η_{G d}`
means `η_{G d}` followed by `G ε_d`. Lean's `≫` runs in diagrammatic order, and the same composite
is `adj.η (G.obj d) ≫ G.map (adj.ε d)`. Every composite below is written in Lean's order.

This file does not import the file for §4.1, which still contains open exercises. The one
result needed from §4.1 is Lemma 4.1.3, and Part 1 restates it with a proof.
-/

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import LeanPlayground.Scratch.category_kindergarten.check_diagrams
import LeanPlayground.Scratch.category_kindergarten.common_tools
import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget
import LeanPlayground.riehl.common

open CategoryTheory Limits Opposite
open scoped CategoryKindergarten

set_option pp.deepTerms true       -- don't elide deeply nested subterms
set_option linter.unusedTactic false

-- Shift-click a hypothesis or goal in the infoview to draw it as a diagram;
-- see `diagram_tools` for the available presenters. The output of `#check` cannot be
-- selected, so `check_diagrams` draws it instead: put the cursor on the `#check`.
show_panel_widgets [local ProofWidgets.SelectionPanel]

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ u

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]
variable {ℰ : Type u₃} [Category.{v₃} ℰ]

/-
## Part 0: Components of the unit and counit

The §4.1 file treated the fields `unit` and `counit` of `Adjunction` as a black box, and this
file opens the box. The statements below use the terms `adj.η c` and `adj.ε d` for the components
of the unit and the counit, together with the lemmas `adj.flat_eq` and `adj.sharp_eq`, which
express transposes through those components. These declarations live in `riehl/common.lean`.
The note above them in that file explains why `adj.η c` is preferable to `adj.unit.app c`, with
a worked example of a rewrite that fails on the latter.
-/

section Components

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)

/-
Exercise 0a. Riehl defines `η_c` to be the transpose of the identity morphism of `F c`.
In Mathlib the unit is a field, so this description becomes a theorem.

Suggested proof. Rewrite with `adj.flat_eq`, then with `G.map_id`, and then with
`Category.comp_id`. For reference, Mathlib's version is `Adjunction.homEquiv_id`.
-/
theorem flat_id (c : 𝒞) : (𝟙 (F.obj c)) ♭[adj] = adj.η c := by
  sorry

/-
Exercise 0b. Dually, `ε_d` is the transpose of the identity morphism of `G d`.

Suggested proof. Rewrite with `adj.sharp_eq`, then with `F.map_id`, and then with
`Category.id_comp`.
-/
theorem sharp_id (d : 𝒟) : (𝟙 (G.obj d)) ♯[adj] = adj.ε d := by
  sorry

end Components

/-
## Part 1: The unit and counit of a hom-set bijection

Riehl begins with an adjunction in the sense of Definition 4.1.1, which provides a natural
bijection

  `𝒟(F c, d) ≅ 𝒞(c, G d)`                                        (4.2.1)

Fixing `c`, the bijection (4.2.1) says that the object `F c` represents the functor
`𝒞(c, G -) : 𝒟 ⥤ Set`. By the Yoneda lemma, the natural isomorphism
`𝒟(F c, -) ≅ 𝒞(c, G -)` is determined by a single element of `𝒞(c, G F c)`, namely the
transpose of the identity morphism of `F c`. Riehl denotes that element `η_c`. Lemma 4.2.2
asserts that the morphisms `η_c` are the components of a natural transformation
`η : 𝟭 𝒞 ⟶ F ⋙ G`, called the unit of the adjunction. Lemma 4.2.3 asserts the dual statement
for the morphisms `ε_d`, which are the transposes of the identity morphisms of the objects
`G d`. They form a natural transformation `ε : G ⋙ F ⟶ 𝟭 𝒟`, called the counit.

An `adj : F ⊣ G` cannot serve as the starting point here, because its unit, its counit and
its triangle identities are already fields of the structure. Those fields would hand
over the conclusions without proof. This part therefore starts from a term
`e : Adjunction.CoreHomEquiv F G`, which the §4.1 file introduced as the Lean counterpart of
Definition 4.1.1. Its only data is the family of bijections `e.homEquiv c d`, and it carries
two naturality fields, `e.homEquiv_naturality_left_symm` and `e.homEquiv_naturality_right`.
Mathlib derives the other two naturality equations as the theorems
`e.homEquiv_naturality_left` and `e.homEquiv_naturality_right_symm`.

The notation `f ♭[adj]` applies only to an `Adjunction`, so the transpose of `f` is written
`e.homEquiv c d f` in this part, and the inverse transpose of `g` is written
`(e.homEquiv c d).symm g`.

The theorem `transposed_square_iff` below is Lemma 4.1.3 for `e`, in the layout of the
§4.1 file. It says that the square on the left commutes in `𝒟` if and only if the transposed
square on the right commutes in `𝒞`. Exercises 1a and 1b of the §4.1 file proved the same
statement for `adj`, and the proof here is the same proof.

[Diagram](assets/transposed_squares.svg)
-/
section HomSets

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (e : Adjunction.CoreHomEquiv F G)

/-- Lemma 4.1.3 for a hom-set bijection `e`. -/
theorem transposed_square_iff {c c' : 𝒞} {d d' : 𝒟} (h : c ⟶ c') (k : d ⟶ d')
    (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d') :
    CommSq f (F.map h) k g ↔ CommSq (e.homEquiv c d f) h (G.map k) (e.homEquiv c' d' g) := by
  constructor
  · intro sq
    refine ⟨?_⟩
    rw [← e.homEquiv_naturality_right, ← e.homEquiv_naturality_left, sq.w]
  · intro sq
    refine ⟨?_⟩
    apply (e.homEquiv c d').injective
    rw [e.homEquiv_naturality_right, e.homEquiv_naturality_left, sq.w]

/-- Riehl's `η_c`, defined as the transpose of the identity morphism of `F c`. -/
def unitAt (c : 𝒞) : c ⟶ G.obj (F.obj c) :=
  e.homEquiv c (F.obj c) (𝟙 (F.obj c))

/-- Riehl's `ε_d`, defined as the transpose of the identity morphism of `G d`. -/
def counitAt (d : 𝒟) : F.obj (G.obj d) ⟶ d :=
  (e.homEquiv (G.obj d) d).symm (𝟙 (G.obj d))

/-
Exercise 1a. The inverse transpose of `η_c` is the identity morphism of `F c`.

Suggested proof. The term `(e.homEquiv c (F.obj c)).symm_apply_apply (𝟙 (F.obj c))` is an
equation whose left-hand side is `(e.homEquiv c (F.obj c)).symm` applied to the transpose of
`𝟙 (F.obj c)`. That transpose is `unitAt e c` by definition, so `exact` accepts the term even
though `rw` would not see the connection.
-/
theorem homEquiv_symm_unitAt (c : 𝒞) :
    (e.homEquiv c (F.obj c)).symm (unitAt e c) = 𝟙 (F.obj c) := by
  sorry

/-
Exercise 1b. The transpose of `ε_d` is the identity morphism of `G d`.

Suggested proof. Use `Equiv.apply_symm_apply` in the same manner as Exercise 1a.
-/
theorem homEquiv_counitAt (d : 𝒟) :
    e.homEquiv (G.obj d) d (counitAt e d) = 𝟙 (G.obj d) := by
  sorry

/-
Exercise 1c. This exercise is the heart of Lemma 4.2.2. To prove that `η` is natural, Riehl
shows that the left-hand square below commutes for every morphism `h : c ⟶ c'`. By
Lemma 4.1.3, the left-hand square commutes if and only if the right-hand transposed square
does, and the right-hand square commutes for evident reasons. Riehl calls the morphism `f`.
This file calls the morphism `h` so that it matches the binder of `transposed_square_iff`.

[Diagram](assets/unit_naturality.svg)

Suggested proof. Instantiate `transposed_square_iff e h k f g` with `h := h`, `k := F.map h`,
`f := 𝟙 (F.obj c)` and `g := 𝟙 (F.obj c')`. The result is an equivalence between the
right-hand square of the diagram, which is stated in `𝒟`, and a square in `𝒞` whose top and
bottom sides are the transposes of identity morphisms. Those transposes are `unitAt e c` and
`unitAt e c'` by definition. Apply `.mp` to a proof of the square in `𝒟`, which can be
written `⟨by simp⟩`, and finish with `exact`.
-/
theorem unitAt_square {c c' : 𝒞} (h : c ⟶ c') :
    CommSq (unitAt e c) h (G.map (F.map h)) (unitAt e c') := by
  sorry

/-
Exercise 1d. Riehl leaves the proof of Lemma 4.2.3 to the reader. The square that expresses
naturality of `ε` at `k : d ⟶ d'` is on the left below, and its transpose is on the right.
In this direction the morphisms `ε_d` are already in the `𝒟` square, and the identity
morphisms appear after transposing, so the exercise is a mirror image of Exercise 1c.

[Diagram](assets/counit_naturality.svg)

Suggested proof. Rewrite the goal with `transposed_square_iff e (G.map k) k`, which turns it
into a square in `𝒞`. Then rewrite with `homEquiv_counitAt` twice, which replaces the top
and bottom sides with identity morphisms, and close the goal with `exact ⟨by simp⟩`.
-/
theorem counitAt_square {d d' : 𝒟} (k : d ⟶ d') :
    CommSq (counitAt e d) (F.map (G.map k)) k (counitAt e d') := by
  sorry

/-
Exercises 1e and 1f. These two exercises assemble the components into natural
transformations. A natural transformation has two fields, `app` and `naturality`, and the
field `naturality` asks for the equation `L.map h ≫ app c' = app c ≫ M.map h` between
functors `L` and `M`. The goal for `unitOf` therefore mentions `(𝟭 𝒞).map h` and
`(F ⋙ G).map h`, which are definitionally equal to `h` and `G.map (F.map h)`.

Suggested proof. Use the field `w` of the squares from Exercises 1c and 1d, and use `.symm`
wherever the two sides appear in the opposite order. The tactic `exact` sees through the
identity functor and the composite functor, so no rewriting is needed.
-/
def unitOf : 𝟭 𝒞 ⟶ F ⋙ G where
  app c := unitAt e c
  naturality c c' h := by
    sorry

def counitOf : G ⋙ F ⟶ 𝟭 𝒟 where
  app d := counitAt e d
  naturality d d' k := by
    sorry

/-
Exercise 1g. This exercise proves the assertion that the bijection is determined by `η_c`.
The transpose of any `f : F.obj c ⟶ d` is `η_c` followed by `G.map f`, which is formula
(4.2.8) of Theorem 4.2.7. Near the end of the proof of that theorem, Riehl records the
equation with the words "By naturality of the original bijection."

Suggested proof. Rewrite the goal with `unitAt`, which unfolds the definition, then with
`← e.homEquiv_naturality_right`, which collapses the right-hand side to the transpose of
`𝟙 (F.obj c) ≫ f`, and finally with `Category.id_comp`.
-/
theorem homEquiv_eq_unitAt {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) :
    e.homEquiv c d f = unitAt e c ≫ G.map f := by
  sorry

/-
Exercise 1h. The dual formula expresses the inverse transpose of `g : c ⟶ G.obj d` through
`ε_d`. This equation is formula (4.2.9).

Suggested proof. Follow Exercise 1g with `counitAt`, `← e.homEquiv_naturality_left_symm` and
`Category.comp_id`.
-/
theorem homEquiv_symm_eq_counitAt {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) :
    (e.homEquiv c d).symm g = F.map g ≫ counitAt e d := by
  sorry

end HomSets

/-
## Part 2: Example 4.2.4, free groups

Riehl's example is the adjunction between the free group functor and the forgetful functor
`U : Group ⥤ Set`. Elements of the free group `F(S)` are finite words in the elements of `S`
and their formal inverses, taken modulo the relations that cancel `s s⁻¹` and `s⁻¹ s`. The
component `η_S : S ⟶ U F(S)` of the unit sends `s` to the singleton word. The component
`ε_A : F U(A) ⟶ A` of the counit sends a word in the elements of the group `A` to the product
of its letters, computed in `A`.

Mathlib's category of groups is `GrpCat`. An object `A : GrpCat` coerces to a type, which the
infoview prints as `↑A`, and that type carries a group structure. The free group on a type
`S` is `FreeGroup S`, and the function `FreeGroup.of : S → FreeGroup S` sends an element to
the singleton word. The functor `GrpCat.free : Type u ⥤ GrpCat` sends `S` to `FreeGroup S`,
the functor `forget GrpCat : GrpCat ⥤ Type u` is Riehl's `U`, and the adjunction is
`GrpCat.adj : GrpCat.free ⊣ forget GrpCat`.

The notation `A →* B` denotes monoid homomorphisms from `A` to `B`. A term of that type
coerces to a function, and it satisfies the lemmas `map_mul` and `map_inv`. A morphism
`φ : A ⟶ B` in `GrpCat` has an underlying monoid homomorphism `φ.hom : A →* B`.

The domain of `ε_A` is the expression `(forget GrpCat ⋙ GrpCat.free).obj A`, which is
definitionally equal to the free group on the elements of `A`. The definition `evalWord`
below records the underlying homomorphism with the simple type `FreeGroup A →* A`, so that
`map_mul` and `map_inv` can find their way into statements about it.
-/
section FreeGroups

/-
Exercise 2a. The component of the unit at a set `S` sends `s` to the singleton word.

Suggested proof. Mathlib builds `GrpCat.adj` from a hom-set bijection, and the statement
holds by unfolding that construction, so `rfl` closes the goal.
-/
example (S : Type u) (s : S) : GrpCat.adj.η S s = FreeGroup.of s := by
  sorry

/-- Riehl's `ε_A`, as a monoid homomorphism that evaluates a word in the group `A`. -/
def evalWord (A : GrpCat.{u}) : FreeGroup A →* A :=
  (GrpCat.adj.ε A).hom

/-
Exercise 2b. The counit sends the singleton word on `a` to `a`. This fact is an instance of a
triangle identity, which Part 3 discusses in general. For the adjunction `GrpCat.adj`, the
identity says that `η` at the underlying set of `A`, followed by `U ε_A`, is the identity
function on that set. Applying both sides to `a` gives the statement of the exercise.

Suggested proof. Bind the triangle identity with
`have h := GrpCat.adj.right_triangle_components A`. The term `h` is an equation between two
morphisms in `Type u`. Apply both sides to `a` with `congrArg (fun φ => φ a) h`, and hand the
result to `exact`, which sees through the definition of `evalWord`.
-/
theorem evalWord_of (A : GrpCat.{u}) (a : A) : evalWord A (FreeGroup.of a) = a := by
  sorry

/-
Exercise 2c. The counit interprets a word with the multiplication and the inverses of `A`.
This exercise computes it on the word `a b⁻¹`.

Suggested proof. Rewrite with `map_mul`, then with `map_inv`, and then twice with
`evalWord_of`.
-/
example (A : GrpCat.{u}) (a b : A) :
    evalWord A (FreeGroup.of a * (FreeGroup.of b)⁻¹) = a * b⁻¹ := by
  sorry

end FreeGroups

/-
## Part 3: Definition 4.2.5 and Remark 4.2.6

Definition 4.2.5 (adjunctions II). An adjunction consists of an opposing pair of functors
`F : 𝒞 ⥤ 𝒟` and `G : 𝒟 ⥤ 𝒞`, together with natural transformations `η : 𝟭 𝒞 ⟶ F ⋙ G` and
`ε : G ⋙ F ⟶ 𝟭 𝒟` that satisfy the triangle identities. Evaluated at objects, the triangle
identities are the commutativity of the two triangles below.

[Diagram](assets/triangle_identities.svg)

Mathlib's structure `Adjunction` is exactly Definition 4.2.5. Its four fields are `unit`,
`counit`, `left_triangle_components` and `right_triangle_components`. The last two fields are
stated at objects, and the prefix `dsimp%` in their source code runs `dsimp` on the statement,
which removes occurrences of `𝟭` and `⋙` from the hidden arguments. That simplification is the
reason `rw [adj.left_triangle_components]` works on a goal written with `adj.η`, as the note in
`riehl/common.lean` explains.

Riehl's identities are equations between natural transformations, and they are written with
the whiskered transformations `F η`, `ε F`, `η G` and `G ε`. Lean's names for whiskering are
easy to misread, because Lean's composition runs in the opposite direction from Riehl's. The
diagram below shows a natural transformation `α : H ⟶ K` between functors `𝒞 ⥤ 𝒟`, together
with a functor `L` that follows it and a functor `M` that precedes it.

[Diagram](assets/whiskering.svg)

* `Functor.whiskerRight α L : H ⋙ L ⟶ K ⋙ L` has the component `L.map (α.app c)` at `c`. Riehl
  writes this transformation `L α`, with `L` on the left, because Riehl's notation applies
  `L` to `α`. Lean's name refers to the position of `L` in the composite `H ⋙ L`.
* `Functor.whiskerLeft M α : M ⋙ H ⟶ M ⋙ K` has the component `α.app (M.obj x)` at `x`. Riehl
  writes this transformation `α M`.

So Riehl's `F η` is Lean's `Functor.whiskerRight adj.unit F`, and Riehl's `ε F` is Lean's
`Functor.whiskerLeft F adj.counit`.
-/
section Whiskering

variable {ℬ : Type u₄} [Category.{v₄} ℬ]
variable {H K : 𝒞 ⥤ 𝒟} (α : H ⟶ K) (L : 𝒟 ⥤ ℰ) (M : ℬ ⥤ 𝒞)

/-
Exercises 3a and 3b. The components of whiskered transformations are as Riehl's notation
suggests. Both equations hold by definition.

Suggested proof. Use `rfl`.
-/
example (c : 𝒞) : (Functor.whiskerRight α L).app c = L.map (α.app c) := by
  sorry

example (x : ℬ) : (Functor.whiskerLeft M α).app x = α.app (M.obj x) := by
  sorry

end Whiskering

section Triangles

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)

/-
Mathlib also states the triangle identities as equations between natural transformations.
The two statements printed by the `#check` commands below contain an associator and two
unitors. Riehl's composites `(G ⋙ F) ⋙ G` and `G ⋙ (F ⋙ G)` are the same functor in Riehl's
setting, but in Lean they are different terms, and the associator mediates between them.
The formulations at objects avoid that bookkeeping, which is why the rest of this file uses
them. The two exercises below connect the formulations at objects with whiskering.
-/
#check @Adjunction.left_triangle
#check @Adjunction.right_triangle

/-
Exercises 3c and 3d. The composite `F η` followed by `ε F`, evaluated at `c`, is the identity
morphism of `F c`. The composite `η G` followed by `G ε`, evaluated at `d`, is the identity
morphism of `G d`.

Suggested proof. Each statement is one of the fields of `adj` up to the definitional
unfolding from Exercises 3a and 3b, so `exact` finishes each proof.
-/
theorem left_triangle_app (c : 𝒞) :
    (Functor.whiskerRight adj.unit F).app c ≫ (Functor.whiskerLeft F adj.counit).app c
      = 𝟙 (F.obj c) := by
  sorry

theorem right_triangle_app (d : 𝒟) :
    (Functor.whiskerLeft G adj.unit).app d ≫ (Functor.whiskerRight adj.counit G).app d
      = 𝟙 (G.obj d) := by
  sorry

/-
Remark 4.2.6. Together the triangle identities assert that the counit is a left inverse of
the unit modulo translation. The components `η_c : c ⟶ G F c` and `ε_d : F G d ⟶ d` lie in
different categories, so they cannot be composed directly. After applying `F` to the unit,
the morphism `F η_c : F c ⟶ F G F c` has the left inverse `ε_{F c}`. After applying `G` to the
counit, the morphism `G ε_d : G F G d ⟶ G d` has the right inverse `η_{G d}`.

Mathlib's vocabulary for one-sided inverses is `SplitMono` and `SplitEpi`. For a morphism
`f : X ⟶ Y`, a term of `SplitMono f` consists of a morphism `retraction : Y ⟶ X` and a proof
`id` of the equation `f ≫ retraction = 𝟙 X`. A term of `SplitEpi f` consists of a morphism
`section_ : Y ⟶ X` and a proof `id` of the equation `section_ ≫ f = 𝟙 Y`. The name `section_`
has a trailing underscore because `section` is a keyword.

Exercise 3e. Exhibit `F.map (adj.η c)` as a split monomorphism.

Exercise 3f. Exhibit `G.map (adj.ε d)` as a split epimorphism.

Suggested proof. Supply the inverses named in Remark 4.2.6, and supply the fields of `adj`
as the proofs of the equations.
-/
def unitSplitMono (c : 𝒞) : SplitMono (F.map (adj.η c)) where
  retraction := by
    sorry
  id := by
    sorry

def counitSplitEpi (d : 𝒟) : SplitEpi (G.map (adj.ε d)) where
  section_ := by
    sorry
  id := by
    sorry

end Triangles

/-
## Parts 4 to 8: Theorem 4.2.7

Theorem 4.2.7. Given a pair of functors `F : 𝒞 ⥤ 𝒟` and `G : 𝒟 ⥤ 𝒞`, the data of an adjunction
with `F ⊣ G` is equivalently encoded by any of the following:

 (i) a natural family of isomorphisms `𝒟(F c, d) ≅ 𝒞(c, G d)` for all `c` and `d`;
 (ii) natural transformations `η : 𝟭 𝒞 ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 𝒟` that satisfy the
   triangle identities;
 (iii) a natural transformation `η` such that the function that sends `f : F c ⟶ d` to `η_c`
   followed by `G f` is an isomorphism for all `c` and `d`;
 (iv) a natural transformation `ε` such that the function that sends `g : c ⟶ G d` to `F g`
   followed by `ε_d` is an isomorphism for all `c` and `d`;
 (v) a natural transformation `η` whose component `η_c` defines an initial object of the
   comma category `c ↓ G` for every `c`;
 (vi) a natural transformation `ε` whose component `ε_d` defines a terminal object of the
   comma category `F ↓ d` for every `d`.

The arrows in the diagram below are the implications that Riehl proves, and the parts of this
file follow them. Part 4 proves that (i) implies (ii). Part 5 proves that (ii) implies (iii)
and (iv). Part 6 proves that (iii) and (iv) each imply (i). Part 7 proves that (iii) is
equivalent to (v) and that (iv) is equivalent to (vi). Part 8 proves that the constructions
are inverse to one another, so that the six presentations carry the same information.

[Diagram](assets/theorem_4_2_7_roadmap.svg)

## Part 4: (i) implies (ii)

Riehl obtains the natural transformations from Lemmas 4.2.2 and 4.2.3, which are Exercises 1e
and 1f above. It remains to demonstrate the triangle identities. Riehl proves them with four
squares. By Lemma 4.1.3, the upper left square commutes because its transpose, the upper right
square, manifestly does. By the same lemma, the lower right square commutes because its
transpose, the lower left square, manifestly does.

[Diagram](assets/triangle_squares.svg)
-/
section TrianglesFromHomSets

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (e : Adjunction.CoreHomEquiv F G)

/-
Exercise 4a. The upper left square commutes.

Suggested proof. The binders of `transposed_square_iff e h k f g` take the values
`h := unitAt e c`, `k := 𝟙 (F.obj c)`, `f := 𝟙 (F.obj c)` and `g := counitAt e (F.obj c)`.
Rewrite the goal with `transposed_square_iff e (unitAt e c) (𝟙 (F.obj c))`, and then with
`homEquiv_counitAt`. The goal becomes the upper right square, whose top side is the transpose
of an identity morphism. Close it with `exact ⟨by simp [unitAt]⟩`.
-/
theorem left_triangle_square (c : 𝒞) :
    CommSq (𝟙 (F.obj c)) (F.map (unitAt e c)) (𝟙 (F.obj c)) (counitAt e (F.obj c)) := by
  sorry

/-
Exercise 4b. The lower right square commutes.

Suggested proof. This time the known square is the one in `𝒟`, so the equivalence is used
from left to right. The binders take the values `h := 𝟙 (G.obj d)`, `k := counitAt e d`,
`f := 𝟙 (F.obj (G.obj d))` and `g := counitAt e d`. Write
`have sq := (transposed_square_iff e h k f g).mp ⟨by simp⟩` with those values, then rewrite
`sq` with `homEquiv_counitAt`, and finish with `exact sq`. The top side of `sq` is the transpose
of an identity morphism, which is `unitAt e (G.obj d)` by definition.
-/
theorem right_triangle_square (d : 𝒟) :
    CommSq (unitAt e (G.obj d)) (𝟙 (G.obj d)) (G.map (counitAt e d)) (𝟙 (G.obj d)) := by
  sorry

/-
Exercises 4c and 4d. The squares of Exercises 4a and 4b have identity morphisms on two sides,
so they collapse to the triangle identities at objects.

Suggested proof. Take the field `w` of each square, use `.symm` if the two sides appear in
the opposite order, and clear the identity morphisms with `simpa using`.
-/
theorem left_triangle_eq (c : 𝒞) :
    F.map (unitAt e c) ≫ counitAt e (F.obj c) = 𝟙 (F.obj c) := by
  sorry

theorem right_triangle_eq (d : 𝒟) :
    unitAt e (G.obj d) ≫ G.map (counitAt e d) = 𝟙 (G.obj d) := by
  sorry

/-
Exercise 4e. Assemble the adjunction in the sense of Definition 4.2.5.

Suggested proof. Fill the two remaining fields with Exercises 4c and 4d, using `exact`. For
reference, Mathlib's corresponding construction is `Adjunction.mkOfHomEquiv`.
-/
def adjOfCore : F ⊣ G where
  unit := unitOf e
  counit := counitOf e
  left_triangle_components c := by
    sorry
  right_triangle_components d := by
    sorry

end TrianglesFromHomSets

/-
## Part 5: (ii) implies (iii) and (iv)

Now the triangle identities are hypotheses, so `adj : F ⊣ G` is the right starting point. The
definitions below are the formulas (4.2.8) and (4.2.9), which define transposition from the
unit and the counit.

[Diagram](assets/transpose_formulas.svg)

Riehl proves that (ii) implies (iii) and (iv) by showing that the triangle identities make
the two operations inverse to each other. The transpose of the transpose of `f : F c ⟶ d` is
the top composite in the first diagram below. Naturality of `ε` is the square on the right,
and the left triangle is a triangle identity, so the composite is `f`.

[Diagram](assets/sharp_of_flat_chase.svg)

The second diagram is the dual chase. The transpose of the transpose of `g : c ⟶ G d` is the
composite along the top and down the right side. Naturality of `η` is the square at the top,
and the lower triangle is the other triangle identity, so the composite is `g`.

[Diagram](assets/flat_of_sharp_chase.svg)
-/
section Transposes

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)

/-- Formula (4.2.8). -/
def flatOf {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) : c ⟶ G.obj d :=
  adj.η c ≫ G.map f

/-- Formula (4.2.9). -/
def sharpOf {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) : F.obj c ⟶ d :=
  F.map g ≫ adj.ε d

/-
Exercise 5a. The square on the right of the first diagram commutes.

Suggested proof. The term `adj.counit.naturality f` is the required equation up to
definitional unfolding, so `exact ⟨adj.counit.naturality f⟩` closes the goal.
-/
theorem counit_square {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) :
    CommSq (F.map (G.map f)) (adj.ε (F.obj c)) (adj.ε d) f := by
  sorry

/-
Exercise 5b. The square at the top of the second diagram commutes.

Suggested proof. Use `adj.unit.naturality g` with `.symm`.
-/
theorem unit_square {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) :
    CommSq (adj.η c) g (G.map (F.map g)) (adj.η (G.obj d)) := by
  sorry

/-
Exercise 5c. The transpose of the transpose of `f` is `f`. This exercise is the first diagram
chase, and the `calc` block below records it as three steps along the diagram. The first step
expands the definitions, the second applies the square, and the third applies the triangle.

Suggested proof. Prove the first step with `simp [sharpOf, flatOf]`, and prove the second step
with `rw [(counit_square adj f).w]`. For the third step, rewrite with `← Category.assoc`, then
with `adj.left_triangle_components`, and then with `Category.id_comp`.
-/
theorem sharpOf_flatOf {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) :
    sharpOf adj (flatOf adj f) = f := by
  calc
    sharpOf adj (flatOf adj f)
        = F.map (adj.η c) ≫ F.map (G.map f) ≫ adj.ε d := by
          sorry
    _ = F.map (adj.η c) ≫ adj.ε (F.obj c) ≫ f := by
          sorry
    _ = f := by
          sorry

/-
Exercise 5d. The transpose of the transpose of `g` is `g`. This exercise is the dual chase.

Suggested proof. Follow Exercise 5c with `unit_square` in the second step. In the third step,
rewrite with `Category.assoc`, then with `adj.right_triangle_components`, and then with
`Category.comp_id`.
-/
theorem flatOf_sharpOf {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) :
    flatOf adj (sharpOf adj g) = g := by
  calc
    flatOf adj (sharpOf adj g)
        = (adj.η c ≫ G.map (F.map g)) ≫ G.map (adj.ε d) := by
          sorry
    _ = (g ≫ adj.η (G.obj d)) ≫ G.map (adj.ε d) := by
          sorry
    _ = g := by
          sorry

/-
Exercise 5e. Package the two operations as a bijection. An `Equiv` has four fields: `toFun`,
`invFun`, and the proofs `left_inv` and `right_inv` that the two functions are mutually
inverse.

Suggested proof. Use Exercises 5c and 5d with `exact`.
-/
def transposeEquiv (c : 𝒞) (d : 𝒟) : (F.obj c ⟶ d) ≃ (c ⟶ G.obj d) where
  toFun := flatOf adj
  invFun := sharpOf adj
  left_inv f := by
    sorry
  right_inv g := by
    sorry

/-
Exercise 5f. The bijection of Exercise 5e is Mathlib's `adj.homEquiv c d`. This equation
closes the loop that the §4.1 file left open, because `homEquiv` is defined from the fields
`unit` and `counit` by these formulas.

Suggested proof. Begin with `ext f`, which reduces the goal to an equation between the images
of `f`. Finish with `exact (adj.flat_eq f).symm`.
-/
theorem transposeEquiv_eq_homEquiv (c : 𝒞) (d : 𝒟) :
    transposeEquiv adj c d = adj.homEquiv c d := by
  sorry

end Transposes

/-
## Part 6: (iii) and (iv) each imply (i)

Riehl observes that the functions in (4.2.8) and (4.2.9) are natural transformations whose
components are invertible. This part proves those assertions. Only a natural transformation
`η` is available in (iii), so the formula is restated as `flatVia η`. Similarly, `sharpVia ε`
is the formula in (iv).

The statement of (iii) says that the function `flatVia η` is an isomorphism of sets. In Lean,
this assumption is expressed with `Function.Bijective`, which is the conjunction of
`Function.Injective` and `Function.Surjective`. A term `h : Function.Bijective f` has the
components `h.injective` and `h.surjective`.

The bridge from a bijective function to an `Equiv` is `Equiv.ofBijective f h`. Its underlying
function is `f`. Its inverse is chosen by the axiom of choice, because the hypothesis `h` only
asserts that a preimage exists. For that reason, a definition that uses `Equiv.ofBijective`
must be marked `noncomputable`, and the inverse can be studied only through the two lemmas
in the warm-ups below.
-/
section Bijections

variable {X Y : Type u} (f : X → Y) (hf : Function.Bijective f)

/-
Warm-ups on `Equiv.ofBijective`. Each of the three statements is a single application of a
library lemma or of `rfl`.

Suggested proof. Use `rfl` for the first statement, `Equiv.ofBijective_apply_symm_apply f hf y`
for the second statement, and `Equiv.ofBijective_symm_apply_apply f hf x` for the third.
-/
example (x : X) : Equiv.ofBijective f hf x = f x := by
  sorry

example (y : Y) : f ((Equiv.ofBijective f hf).symm y) = y := by
  sorry

example (x : X) : (Equiv.ofBijective f hf).symm (f x) = x := by
  sorry

end Bijections

section FromUnit

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (η : 𝟭 𝒞 ⟶ F ⋙ G)

/-- The function of (4.2.8), defined from a natural transformation `η` alone. -/
def flatVia {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) : c ⟶ G.obj d :=
  η.app c ≫ G.map f

/-
Exercise 6a. The function `flatVia η` is natural in `d`. This fact uses only the functoriality
of `G`.

Suggested proof. Use `simp [flatVia]`.
-/
theorem flatVia_comp_right {c : 𝒞} {d d' : 𝒟} (f : F.obj c ⟶ d) (k : d ⟶ d') :
    flatVia η (f ≫ k) = flatVia η f ≫ G.map k := by
  sorry

/-
Exercise 6b. The function `flatVia η` is natural in `c`. This fact uses the naturality of `η`.

Suggested proof. Bind `have w := η.naturality h`, and apply `dsimp at w`, which replaces
`(𝟭 𝒞).map h` with `h` and `(F ⋙ G).map h` with `G.map (F.map h)`. Then rewrite the goal with
`flatVia` twice, with `G.map_comp`, with `← Category.assoc`, with `← w`, and with
`Category.assoc`.
-/
theorem flatVia_comp_left {c c' : 𝒞} {d : 𝒟} (h : c ⟶ c') (f : F.obj c' ⟶ d) :
    flatVia η (F.map h ≫ f) = h ≫ flatVia η f := by
  sorry

/-
Exercise 6c. Condition (iii) produces a term of `CoreHomEquiv F G`, which is condition (i).

Two naturality fields remain. The field `homEquiv_naturality_right` is Exercise 6a. The field
`homEquiv_naturality_left_symm` concerns the inverse bijection, which was produced by choice.

Suggested proof. For the field `homEquiv_naturality_left_symm`, start with
`rw [Equiv.symm_apply_eq]`, which moves the inverse to the other side of the equation. Then
close the goal with `simp [flatVia_comp_left, Equiv.ofBijective_apply_symm_apply]`.
-/
noncomputable def coreOfUnit
    (hη : ∀ (c : 𝒞) (d : 𝒟), Function.Bijective (flatVia η (c := c) (d := d))) :
    Adjunction.CoreHomEquiv F G where
  homEquiv c d := Equiv.ofBijective (flatVia η) (hη c d)
  homEquiv_naturality_left_symm h g := by
    sorry
  homEquiv_naturality_right f k := by
    sorry

/-
Exercise 6d. The unit of the bijection of Exercise 6c is the natural transformation that the
construction started from. This fact is one half of the statement that the constructions are
inverse.

Suggested proof. Use `change flatVia η (𝟙 (F.obj c)) = η.app c`, which restates the goal in
terms of the formula, and close the goal with `simp [flatVia]`.
-/
theorem unitAt_coreOfUnit
    (hη : ∀ (c : 𝒞) (d : 𝒟), Function.Bijective (flatVia η (c := c) (d := d))) (c : 𝒞) :
    unitAt (coreOfUnit η hη) c = η.app c := by
  sorry

end FromUnit

section FromCounit

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (ε : G ⋙ F ⟶ 𝟭 𝒟)

/-- The function of (4.2.9), defined from a natural transformation `ε` alone. -/
def sharpVia {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) : F.obj c ⟶ d :=
  F.map g ≫ ε.app d

/-
Exercises 6e to 6h are the duals of Exercises 6a to 6d, and their proofs follow the same
pattern. In this direction, the function `sharpVia ε` runs from `𝒞(c, G d)` to `𝒟(F c, d)`, so
the field `homEquiv` of the bijection is the inverse of `Equiv.ofBijective (sharpVia ε) _`.

Suggested proof. For Exercise 6f, use `ε.naturality k` and `dsimp at w` as in Exercise 6b, and
rewrite the goal with `sharpVia` twice, `F.map_comp`, `Category.assoc` twice, and `← w`. For the
field `homEquiv_naturality_right` in Exercise 6g, use `rw [Equiv.symm_apply_eq]` followed by
`simp [sharpVia_comp_right, Equiv.ofBijective_apply_symm_apply]`. For Exercise 6h, use
`change sharpVia ε (𝟙 (G.obj d)) = ε.app d` followed by `simp [sharpVia]`.
-/
theorem sharpVia_comp_left {c c' : 𝒞} {d : 𝒟} (h : c ⟶ c') (g : c' ⟶ G.obj d) :
    sharpVia ε (h ≫ g) = F.map h ≫ sharpVia ε g := by
  sorry

theorem sharpVia_comp_right {c : 𝒞} {d d' : 𝒟} (g : c ⟶ G.obj d) (k : d ⟶ d') :
    sharpVia ε (g ≫ G.map k) = sharpVia ε g ≫ k := by
  sorry

noncomputable def coreOfCounit
    (hε : ∀ (c : 𝒞) (d : 𝒟), Function.Bijective (sharpVia ε (c := c) (d := d))) :
    Adjunction.CoreHomEquiv F G where
  homEquiv c d := (Equiv.ofBijective (sharpVia ε) (hε c d)).symm
  homEquiv_naturality_left_symm h g := by
    sorry
  homEquiv_naturality_right f k := by
    sorry

theorem counitAt_coreOfCounit
    (hε : ∀ (c : 𝒞) (d : 𝒟), Function.Bijective (sharpVia ε (c := c) (d := d))) (d : 𝒟) :
    counitAt (coreOfCounit ε hε) d = ε.app d := by
  sorry

end FromCounit

/-
## Part 7: (iii) is equivalent to (v), and (iv) is equivalent to (vi)

The section title describes the unit and counit as universal arrows, and this part explains
the phrase. The comma category `c ↓ G` has as objects the pairs `(d, g)` with `d : 𝒟` and
`g : c ⟶ G d`. A morphism from `(d, g)` to `(d', g')` is a morphism `k : d ⟶ d'` such that `g`
followed by `G k` equals `g'`. To say that `(F c, η_c)` is an initial object of `c ↓ G` is to
say that for every object `(d, g)` there is a unique morphism `f : F c ⟶ d` such that `η_c`
followed by `G f` equals `g`. The picture is the triangle on the left below, in which the
dashed arrow is the unique morphism that exists. On the right is the same unique morphism,
which lives in `𝒟`.

[Diagram](assets/unit_universal.svg)

The condition says precisely that the function (4.2.8) is a bijection for each `d`. Riehl's
proof reaches the same conclusion through Proposition 2.4.8: the category `c ↓ G` is the
category of elements of the functor `𝒞(c, G -)`, and an element is universal if and only if
it is initial in the category of elements. The exercises below prove the two directions by
hand.

Lean construct: `StructuredArrow`. Mathlib's name for `c ↓ G` is `StructuredArrow c G`. It is
defined as `Comma (Functor.fromPUnit c) G`, a comma category of the kind that the §4.1 file
used in Exercise 4.1.v, with a one-object category on the left. The relevant API is as
follows.

* `StructuredArrow.mk g` is the object determined by a morphism `g : c ⟶ G.obj d`.
* For an object `X`, the term `X.right` is its object of `𝒟`, and the term
  `X.hom : c ⟶ G.obj X.right` is its morphism.
* For a morphism `φ : X ⟶ Y`, the term `φ.right : X.right ⟶ Y.right` is the underlying morphism
  of `𝒟`, and `StructuredArrow.w φ` is the equation `X.hom ≫ G.map φ.right = Y.hom`.
* `StructuredArrow.homMk k w` is the morphism with underlying morphism `k`, where `w` is a proof
  of the equation `X.hom ≫ G.map k = Y.hom`.
* `StructuredArrow.hom_ext φ ψ h` says that `φ = ψ` whenever `h` proves `φ.right = ψ.right`.

Lean construct: `CostructuredArrow`. The dual category `F ↓ d` is `CostructuredArrow F d`. Its
API exchanges `right` for `left`: `X.left` is an object of `𝒞`, `X.hom : F.obj X.left ⟶ d` is a
morphism, and `CostructuredArrow.w φ` is the equation `F.map φ.left ≫ Y.hom = X.hom`.

Lean construct: `IsInitial`. For an object `X`, a term `t : IsInitial X` is a proof that `X` is
initial. It is a structure that carries data, so a declaration that produces one is a `def`.
The API needed here has three pieces.

* `t.to Y : X ⟶ Y` is the morphism from `X` to any object `Y`.
* `t.hom_ext φ ψ` is the equation `φ = ψ` for any two morphisms `φ ψ : X ⟶ Y`.
* `IsInitial.ofUniqueHom h u` builds a term of `IsInitial X` from a family `h Y : X ⟶ Y` and a
  proof `u` that every `m : X ⟶ Y` equals `h Y`.

`IsTerminal` has the dual API, with `t.from Y : Y ⟶ X`, `t.hom_ext` and
`IsTerminal.ofUniqueHom`.
-/
section Universal

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞}

/-
Warm-ups on `StructuredArrow`. The first two statements hold by definition, and the third is
`StructuredArrow.w`. The fourth asks for a morphism, which `StructuredArrow.homMk k w` provides.
-/
example {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) : (StructuredArrow.mk g).right = d := by
  sorry

example {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) : (StructuredArrow.mk g).hom = g := by
  sorry

example {c : 𝒞} {X Y : StructuredArrow c G} (φ : X ⟶ Y) : X.hom ≫ G.map φ.right = Y.hom := by
  sorry

example {c : 𝒞} {d d' : 𝒟} (g : c ⟶ G.obj d) (g' : c ⟶ G.obj d') (k : d ⟶ d')
    (w : g ≫ G.map k = g') : StructuredArrow.mk g ⟶ StructuredArrow.mk g' := by
  sorry

/-
Warm-ups on `CostructuredArrow`, which are the duals of the warm-ups above.
-/
example {d : 𝒟} {c : 𝒞} (f : F.obj c ⟶ d) : (CostructuredArrow.mk f).left = c := by
  sorry

example {d : 𝒟} {X Y : CostructuredArrow F d} (φ : X ⟶ Y) : F.map φ.left ≫ Y.hom = X.hom := by
  sorry

/-
Warm-ups on `IsInitial`, stated in an arbitrary category.
-/
example {X Y : ℰ} (t : IsInitial X) : X ⟶ Y := by
  sorry

example {X Y : ℰ} (t : IsInitial X) (φ ψ : X ⟶ Y) : φ = ψ := by
  sorry

example {X : ℰ} (h : ∀ Y, X ⟶ Y) (u : ∀ (Y : ℰ) (m : X ⟶ Y), m = h Y) : IsInitial X := by
  sorry

variable (η : 𝟭 𝒞 ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 𝒟)

/-- The object `(F c, η_c)` of the comma category `c ↓ G`. -/
abbrev unitArrow (c : 𝒞) : StructuredArrow c G := StructuredArrow.mk (η.app c)

/-- The object `(G d, ε_d)` of the comma category `F ↓ d`. -/
abbrev counitArrow (d : 𝒟) : CostructuredArrow F d := CostructuredArrow.mk (ε.app d)

/-
Exercise 7a. If `(F c, η_c)` is initial, then `flatVia η` is surjective. Existence of a morphism
out of an initial object provides the preimage.

Suggested proof. Introduce `g`. The object `StructuredArrow.mk g` receives the morphism
`t.to (StructuredArrow.mk g)` from the initial object. The underlying morphism of `t.to _` is the
preimage, and `StructuredArrow.w` applied to `t.to _` is the proof that its image is `g`. Combine
them with `exact ⟨_, _⟩`.
-/
theorem surjective_of_isInitial {c : 𝒞} (t : IsInitial (unitArrow η c)) (d : 𝒟) :
    Function.Surjective (flatVia η (c := c) (d := d)) := by
  sorry

/-
Exercise 7b. If `(F c, η_c)` is initial, then `flatVia η` is injective. Uniqueness of a morphism
out of an initial object provides the equation.

Suggested proof. Introduce `f`, `f'` and the hypothesis `hf : flatVia η f = flatVia η f'`. Build
two morphisms from `unitArrow η c` to `StructuredArrow.mk (flatVia η f)`, namely
`StructuredArrow.homMk f rfl` and `StructuredArrow.homMk f' hf.symm`. The proofs `rfl` and
`hf.symm` work because `flatVia η f` unfolds to `η.app c ≫ G.map f`. Name the morphisms `φ` and
`ψ` with `let`, giving each its type. Then `t.hom_ext φ ψ` says `φ = ψ`, and
`congrArg (fun χ => χ.right) (t.hom_ext φ ψ)` says `f = f'`.
-/
theorem injective_of_isInitial {c : 𝒞} (t : IsInitial (unitArrow η c)) (d : 𝒟) :
    Function.Injective (flatVia η (c := c) (d := d)) := by
  sorry

/-
Exercise 7c. Condition (v) at `c` implies condition (iii) at `c`.

Suggested proof. Combine Exercises 7a and 7b with the anonymous constructor `⟨_, _⟩`, since
`Function.Bijective` is a conjunction whose first component is injectivity.
-/
theorem bijective_of_isInitial {c : 𝒞} (t : IsInitial (unitArrow η c)) (d : 𝒟) :
    Function.Bijective (flatVia η (c := c) (d := d)) := by
  sorry

/-- The morphism out of `F c` determined by an object of `c ↓ G`, when (iii) holds at `c`. -/
noncomputable def descOf {c : 𝒞}
    (hη : ∀ d : 𝒟, Function.Bijective (flatVia η (c := c) (d := d)))
    (Y : StructuredArrow c G) : F.obj c ⟶ Y.right :=
  (Equiv.ofBijective _ (hη Y.right)).symm Y.hom

/-
Exercise 7d. The morphism `descOf η hη Y` makes the triangle commute.

Suggested proof. Use `exact (Equiv.ofBijective _ (hη Y.right)).apply_symm_apply Y.hom`.
-/
theorem flatVia_descOf {c : 𝒞}
    (hη : ∀ d : 𝒟, Function.Bijective (flatVia η (c := c) (d := d)))
    (Y : StructuredArrow c G) : flatVia η (descOf η hη Y) = Y.hom := by
  sorry

/-
Exercise 7e. Condition (iii) at `c` implies condition (v) at `c`.

Suggested proof. Begin with
`refine IsInitial.ofUniqueHom
  (fun Y => StructuredArrow.homMk (descOf η hη Y) (flatVia_descOf η hη Y)) ?_`.
Introduce `Y` and `m`. Apply `StructuredArrow.hom_ext`, which reduces the goal to an equation
between morphisms of `𝒟`, and then apply `(hη Y.right).injective`, which reduces the goal to an
equation between their images under `flatVia η`. Finish with
`exact (StructuredArrow.w m).trans (flatVia_descOf η hη Y).symm`.
-/
noncomputable def isInitial_of_bijective {c : 𝒞}
    (hη : ∀ d : 𝒟, Function.Bijective (flatVia η (c := c) (d := d))) :
    IsInitial (unitArrow η c) := by
  sorry

/-
Exercises 7f to 7j are the duals of Exercises 7a to 7e. The object `(G d, ε_d)` of `F ↓ d` is
terminal when every `f : F c ⟶ d` factors uniquely through `ε_d`. In the diagram below, the
dashed arrow on the left is `F g`, and the dashed arrow on the right is the unique morphism
`g : c ⟶ G d`.

[Diagram](assets/counit_universal.svg)

Suggested proof. Follow the corresponding exercises, with `t.from` in place of `t.to`,
`CostructuredArrow` in place of `StructuredArrow`, and `left` in place of `right`.
-/
theorem surjective_of_isTerminal {d : 𝒟} (t : IsTerminal (counitArrow ε d)) (c : 𝒞) :
    Function.Surjective (sharpVia ε (c := c) (d := d)) := by
  sorry

theorem injective_of_isTerminal {d : 𝒟} (t : IsTerminal (counitArrow ε d)) (c : 𝒞) :
    Function.Injective (sharpVia ε (c := c) (d := d)) := by
  sorry

theorem bijective_of_isTerminal {d : 𝒟} (t : IsTerminal (counitArrow ε d)) (c : 𝒞) :
    Function.Bijective (sharpVia ε (c := c) (d := d)) := by
  sorry

/-- The morphism into `G d` determined by an object of `F ↓ d`, when (iv) holds at `d`. -/
noncomputable def codescOf {d : 𝒟}
    (hε : ∀ c : 𝒞, Function.Bijective (sharpVia ε (c := c) (d := d)))
    (X : CostructuredArrow F d) : X.left ⟶ G.obj d :=
  (Equiv.ofBijective _ (hε X.left)).symm X.hom

theorem sharpVia_codescOf {d : 𝒟}
    (hε : ∀ c : 𝒞, Function.Bijective (sharpVia ε (c := c) (d := d)))
    (X : CostructuredArrow F d) : sharpVia ε (codescOf ε hε X) = X.hom := by
  sorry

noncomputable def isTerminal_of_bijective {d : 𝒟}
    (hε : ∀ c : 𝒞, Function.Bijective (sharpVia ε (c := c) (d := d))) :
    IsTerminal (counitArrow ε d) := by
  sorry

/-
Exercise 7k. Conditions (v) and (vi) each give an adjunction.

Suggested proof. Apply `adjOfCore` to `coreOfUnit η _` or to `coreOfCounit ε _`, and supply the
required bijectivity with Exercise 7c or with its dual.

For reference, Mathlib's corresponding results live in `Mathlib.CategoryTheory.Adjunction.Comma`,
and the `#check` commands below print three of them. The first two are the forward directions
for an adjunction. The third is a stronger statement in which no functor `F` is given in
advance, since the universal arrows themselves determine `F`.
-/
noncomputable def adjOfInitialUnit (t : ∀ c : 𝒞, IsInitial (unitArrow η c)) : F ⊣ G := by
  sorry

noncomputable def adjOfTerminalCounit (t : ∀ d : 𝒟, IsTerminal (counitArrow ε d)) : F ⊣ G := by
  sorry

#check @mkInitialOfLeftAdjoint
#check @mkTerminalOfRightAdjoint
#check @isRightAdjoint_iff_hasInitial_structuredArrow

end Universal

/-
## Part 8: The constructions are inverse

The final paragraphs of Riehl's proof argue that the constructions undo one another. Starting
from a natural bijection, Riehl defines `η_c` as the transpose of the identity morphism and
obtains the new formula for transposition from (4.2.8). By naturality of the original bijection,
the new formula recovers the old one. Conversely, starting from a unit and counit, the formulas
define transposition, and the transposes of the identity morphisms recover the original pair.

In Lean, the two constructions are `adjOfCore` and `coreOfAdj`, where the latter is defined
below by forgetting everything except `adj.homEquiv`.
-/
section RoundTrip

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞}

/-
Exercise 8a. Every adjunction has an underlying hom-set bijection.

Suggested proof. Use `adj.homEquiv_naturality_left_symm` and `adj.homEquiv_naturality_right`.
Introduce the arguments of each field before applying the lemma, as the code below does.
-/
def coreOfAdj (adj : F ⊣ G) : Adjunction.CoreHomEquiv F G where
  homEquiv := adj.homEquiv
  homEquiv_naturality_left_symm := by
    intro c c' d h g
    sorry
  homEquiv_naturality_right := by
    intro c d d' f k
    sorry

/-
Exercise 8b. Starting from a hom-set bijection `e`, passing to an adjunction and transposing
recovers the original bijection. This fact is Riehl's "the new formula for adjoint transposition
recovers the old formula."

Suggested proof. Rewrite with `Adjunction.flat_eq`, then with `homEquiv_eq_unitAt`. Both sides are
now the same composite after unfolding, so `rfl` closes the goal.
-/
theorem adjOfCore_homEquiv (e : Adjunction.CoreHomEquiv F G) {c : 𝒞} {d : 𝒟}
    (f : F.obj c ⟶ d) : (adjOfCore e).homEquiv c d f = e.homEquiv c d f := by
  sorry

/-
Exercise 8c. Starting from an adjunction, passing to the hom-set bijection and returning recovers
the original adjunction. The lemma `Adjunction.ext` says that two adjunctions between the same
functors are equal when their units are equal, because the unit determines the counit.

Suggested proof. Apply `Adjunction.ext`, then use `ext c`, which reduces the goal to an equation
between components. Finish with `exact flat_id adj c`.
-/
theorem adjOfCore_coreOfAdj (adj : F ⊣ G) : adjOfCore (coreOfAdj adj) = adj := by
  sorry

end RoundTrip

/-
## Part 9: Corollary 4.2.10, fixed points of Galois connections

Corollary 4.2.10. If `A` and `B` are posets and `F : A ⥤ B` and `G : B ⥤ A` form a Galois
connection with `F ⊣ G`, then `F G F = F` and `G F G = G`. Riehl's proof runs as follows. The
unit and the counit give the inequalities `F a ≤ F G F a ≤ F a`, and in a poset two such
inequalities force equality.

The §4.1 file explained that a preorder is a category in which a morphism `x ⟶ y` is a proof of
`x ≤ y`. For a morphism `f`, the term `f.le` is the corresponding inequality, and `homOfLE h` is
the morphism that corresponds to the inequality `h`. In a partial order, the lemma
`le_antisymm` turns two inequalities into an equation.

For reference, Mathlib's general statements are `GaloisConnection.l_u_l_eq_l` and
`GaloisConnection.u_l_u_eq_u`.
-/
section Galois

variable {A : Type u₁} {B : Type u₂} [PartialOrder A] [PartialOrder B] {F : A ⥤ B} {G : B ⥤ A}

/-
Exercises 9a and 9b. The morphism `adj.ε (F.obj a)` proves `F G F a ≤ F a`, and the morphism
`F.map (adj.η a)` proves `F a ≤ F G F a`.

Suggested proof. Combine the two inequalities with `le_antisymm`. Exercise 9b uses the morphisms
`G.map (adj.ε b)` and `adj.η (G.obj b)`.
-/
theorem fixed_point_left (adj : F ⊣ G) (a : A) : F.obj (G.obj (F.obj a)) = F.obj a := by
  sorry

theorem fixed_point_right (adj : F ⊣ G) (b : B) : G.obj (F.obj (G.obj b)) = G.obj b := by
  sorry

/-
Riehl illustrates the corollary with the adjunction between direct image and inverse image along
a function `f : X → Y`. Mathlib's Galois connection between them is `Set.image_preimage`, and the
term `(Set.image_preimage (f := f)).adjunction` is the corresponding adjunction, whose functors
are built from `Set.image f` and `Set.preimage f`. In the §4.1 file, Example 4.1.8 proved the
Galois connection by hand.

Riehl's example uses the letter `A` for the domain of `f`, `B` for its codomain, `X` for a subset
of `A`, and `Y` for a subset of `B`. Since `A` and `B` already name the posets of this section,
the exercises below use `X` and `Y` for the types, and `S` and `T` for the subsets.

Exercises 9c and 9d. The fixed point formulae hold for direct and inverse image.

Suggested proof. Apply `fixed_point_left` or `fixed_point_right` to the adjunction above, with
`exact`. The object map of the functor unfolds to `Set.image f` by definition.
-/
theorem image_preimage_image {X Y : Type u} (f : X → Y) (S : Set X) :
    f '' (f ⁻¹' (f '' S)) = f '' S := by
  sorry

theorem preimage_image_preimage {X Y : Type u} (f : X → Y) (T : Set Y) :
    f ⁻¹' (f '' (f ⁻¹' T)) = f ⁻¹' T := by
  sorry

/-
Exercises 9e and 9f. Riehl remarks that the inclusions `S ⊆ f⁻¹(f(S))` and `f(f⁻¹(T)) ⊆ T` need
not be equalities. These two exercises exhibit counterexamples, which shows that the unit and
counit of this adjunction are not invertible in general.

Suggested proof. For Exercise 9e, take `f := fun _ => ()` and `S := {true}`. The element `false`
lies in the preimage of the image of `S` and does not lie in `S`. For Exercise 9f, take
`f := fun _ => true` and `T := {false}`. Begin each proof with `refine ⟨_, _, ?_⟩` and `intro h`.
-/
example : ∃ (f : Bool → Unit) (S : Set Bool), f ⁻¹' (f '' S) ≠ S := by
  sorry

example : ∃ (f : Unit → Bool) (T : Set Bool), f '' (f ⁻¹' T) ≠ T := by
  sorry

end Galois

/-
## Part 10: Lemma 4.2.11, the equivalence inside an adjunction

Lemma 4.2.11. Any pair of adjoint functors `F : 𝒞 ⥤ 𝒟` and `G : 𝒟 ⥤ 𝒞` restrict to define an
equivalence between the full subcategories spanned by those objects `c` and `d` for which the
components `η_c` and `ε_d`, respectively, are isomorphisms.

Riehl's proof has one step. If `η_c` is invertible, then so is `F η_c`, and `F η_c` is a right
inverse to `ε_{F c}`, which forces `ε_{F c}` to be invertible. A dual argument treats `ε_d`. At
that point the printed text says that `η_{F d}` is invertible. That expression does not typecheck,
because `d` is an object of `𝒟` and `F` is defined on `𝒞`. The component that the argument
produces is `η_{G d}`, and that is the statement of Exercise 10b.

The diagram below shows what the lemma constructs. Riehl names no notation for the two full
subcategories, and the diagram labels them `Fix(η)` and `Fix(ε)`.

[Diagram](assets/fixed_subcategories.svg)

Lean construct: `IsIso`. For a morphism `f`, the proposition `IsIso f` says that `f` has a
two-sided inverse. It is a type class, so a hypothesis written `[IsIso f]` is found automatically
by instance search, and the tactic `infer_instance` closes a goal of the form `IsIso _` when
instance search can derive it. Instance search knows that functors preserve isomorphisms and that
identity morphisms are isomorphisms. Two library lemmas express the two-out-of-three property:
`IsIso.of_isIso_comp_left f g` derives `IsIso g` from `IsIso f` and `IsIso (f ≫ g)`, and
`IsIso.of_isIso_comp_right f g` derives `IsIso f` from `IsIso g` and `IsIso (f ≫ g)`.

Lean construct: `ObjectProperty`. A term `P : ObjectProperty 𝒞` is a predicate on the objects of
`𝒞`. The type `P.FullSubcategory` is the full subcategory spanned by the objects that satisfy `P`.
Its API is as follows.

* An object `X` has the two fields `X.obj : 𝒞` and `X.property : P X.obj`.
* A morphism `f : X ⟶ Y` has an underlying morphism `f.hom : X.obj ⟶ Y.obj`.
* `ObjectProperty.homMk g` is the morphism whose underlying morphism is `g : X.obj ⟶ Y.obj`.
* `ObjectProperty.hom_ext` says that two morphisms are equal when their fields `hom` are equal.
* `P.ι : P.FullSubcategory ⥤ 𝒞` is the inclusion functor.
* `P.lift L hL` factors a functor `L : ℬ ⥤ 𝒞` through the full subcategory, given a proof `hL`
  that every object in the image of `L` satisfies `P`.
* `ObjectProperty.isIso_hom_iff f` says that `IsIso f.hom` is equivalent to `IsIso f`.

Lean construct: `Equivalence`. The notation `𝒞 ≌ 𝒟` denotes `Equivalence 𝒞 𝒟`, whose fields are
a functor, an inverse functor, the natural isomorphisms `unitIso` and `counitIso`, and a coherence
equation. Mathlib's `Adjunction.toEquivalence` builds such a term from an adjunction whose unit
and counit have invertible components, and the capstone below uses it.
-/
section Fixed

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)

/-
Warm-ups on `IsIso`.

Suggested proof. Use `infer_instance` for the first statement, and use the two library lemmas
above for the second and third statements.
-/
example {c c' : 𝒞} (f : c ⟶ c') [IsIso f] : IsIso (F.map f) := by
  sorry

example {c c' c'' : 𝒞} (f : c ⟶ c') (g : c' ⟶ c'') [IsIso f] [IsIso (f ≫ g)] : IsIso g := by
  sorry

example {c c' c'' : 𝒞} (f : c ⟶ c') (g : c' ⟶ c'') [IsIso g] [IsIso (f ≫ g)] : IsIso f := by
  sorry

/-
Exercise 10a. If `η_c` is invertible, then `ε_{F c}` is invertible.

Suggested proof. First establish the fact
`have : IsIso (F.map (adj.η c) ≫ adj.ε (F.obj c))`, by rewriting with
`adj.left_triangle_components` and then using `infer_instance`. Then finish with
`exact IsIso.of_isIso_comp_left (F.map (adj.η c)) _`.
-/
theorem isIso_counit_of_isIso_unit (c : 𝒞) [IsIso (adj.η c)] :
    IsIso (adj.ε (F.obj c)) := by
  sorry

/-
Exercise 10b. If `ε_d` is invertible, then `η_{G d}` is invertible.

Suggested proof. Follow Exercise 10a with `adj.right_triangle_components` and
`IsIso.of_isIso_comp_right`.
-/
theorem isIso_unit_of_isIso_counit (d : 𝒟) [IsIso (adj.ε d)] :
    IsIso (adj.η (G.obj d)) := by
  sorry

/-- The objects `c` at which `η_c` is an isomorphism. -/
def unitIsoAt : ObjectProperty 𝒞 := fun c => IsIso (adj.η c)

/-- The objects `d` at which `ε_d` is an isomorphism. -/
def counitIsoAt : ObjectProperty 𝒟 := fun d => IsIso (adj.ε d)

/-- The full subcategory labeled `Fix(η)` in the diagram. -/
abbrev FixedLeft := (unitIsoAt adj).FullSubcategory

/-- The full subcategory labeled `Fix(ε)` in the diagram. -/
abbrev FixedRight := (counitIsoAt adj).FullSubcategory

/-
Warm-ups on `FullSubcategory`.

Suggested proof. Use the fields and constructors listed in the API above.
-/
example (X : FixedLeft adj) : IsIso (adj.η X.obj) := by
  sorry

example {X Y : FixedLeft adj} (f : X ⟶ Y) : X.obj ⟶ Y.obj := by
  sorry

example {X Y : FixedLeft adj} (f : X.obj ⟶ Y.obj) : X ⟶ Y := by
  sorry

/-
Exercises 10c and 10d. The functors `F` and `G` carry the objects of one full subcategory into the
other. These are the facts that Riehl calls the verification that `F` and `G` restrict.

Suggested proof. Bring the hypothesis into instance search with
`have : IsIso (adj.η X.obj) := X.property`, and finish with Exercise 10a. Exercise 10d is dual.
-/
theorem counitIsoAt_map (X : FixedLeft adj) : counitIsoAt adj (F.obj X.obj) := by
  sorry

theorem unitIsoAt_map (Y : FixedRight adj) : unitIsoAt adj (G.obj Y.obj) := by
  sorry

/-- The restriction of `F` to the full subcategories. -/
def fixedF : FixedLeft adj ⥤ FixedRight adj :=
  (counitIsoAt adj).lift ((unitIsoAt adj).ι ⋙ F) (counitIsoAt_map adj)

/-- The restriction of `G` to the full subcategories. -/
def fixedG : FixedRight adj ⥤ FixedLeft adj :=
  (unitIsoAt adj).lift ((counitIsoAt adj).ι ⋙ G) (unitIsoAt_map adj)

/-
Warm-ups on the restricted functors. Both statements hold by definition.

Suggested proof. Use `rfl`.
-/
example (X : FixedLeft adj) : ((fixedF adj).obj X).obj = F.obj X.obj := by
  sorry

example {X Y : FixedLeft adj} (f : X ⟶ Y) : ((fixedF adj).map f).hom = F.map f.hom := by
  sorry

/-
Exercise 10e. The restricted functors are adjoint, with the same unit and counit. Every field of
this structure is an equation between morphisms of a full subcategory, so each proof begins by
passing to the underlying morphisms.

Suggested proof. In each of the four fields, begin with `apply ObjectProperty.hom_ext`. The
resulting goal is the corresponding fact about `adj`, which `exact` accepts by unfolding. The
relevant facts are `adj.unit.naturality f.hom`, `adj.counit.naturality f.hom`,
`adj.left_triangle_components X.obj` and `adj.right_triangle_components Y.obj`.
-/
def fixedAdj : fixedF adj ⊣ fixedG adj where
  unit :=
    { app := fun X => ObjectProperty.homMk (adj.η X.obj)
      naturality := by
        intro X Y f
        sorry
        }
  counit :=
    { app := fun Y => ObjectProperty.homMk (adj.ε Y.obj)
      naturality := by
        intro X Y f
        sorry
        }
  left_triangle_components X := by
    sorry
  right_triangle_components Y := by
    sorry

/-
Exercises 10f and 10g. The unit and counit of the restricted adjunction have invertible
components. Each statement is an `instance`, so that instance search can find it in the capstone.

Suggested proof. Rewrite with `← ObjectProperty.isIso_hom_iff`, which moves the goal to the
ambient category, and finish with `exact X.property` or `exact Y.property`.
-/
instance (X : FixedLeft adj) : IsIso ((fixedAdj adj).unit.app X) := by
  sorry

instance (Y : FixedRight adj) : IsIso ((fixedAdj adj).counit.app Y) := by
  sorry

/-
Exercise 10h. Lemma 4.2.11. An adjunction whose unit and counit have invertible components is an
equivalence, and the previous two exercises supply those hypotheses.

Suggested proof. Apply `Adjunction.toEquivalence` to `fixedAdj adj`, with dot notation.
-/
noncomputable def fixedEquivalence : FixedLeft adj ≌ FixedRight adj := by
  sorry

end Fixed

/-
## Part 11: Riehl's exercises

### Exercise 4.2.i

Riehl asks for an explanation of each step needed to convert the statement of Lemma 4.2.2 into the
statement of the dual Lemma 4.2.3. This is a prose exercise, and the comment block below is the
place for the answer. The Lean statements that follow it record the key facts of the translation.

Lean construct: the opposite adjunction. The opposite functor of `F : 𝒞 ⥤ 𝒟` is
`F.op : 𝒞ᵒᵖ ⥤ 𝒟ᵒᵖ`. The objects of `𝒞ᵒᵖ` have the form `op c`, and a morphism `f : c ⟶ c'` has an
opposite `f.op : op c' ⟶ op c`. The term `Adjunction.op adj` is an adjunction `G.op ⊣ F.op`, so
passing to opposite categories exchanges the roles of the left and right adjoints.

For reference, Mathlib's file `Adjunction/Basic.lean` uses the attribute `to_dual`, which transports
a theorem or definition to its dual version automatically. That attribute is a mechanized form of
the exercise.
-/
section Dual

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G)

/-
Exercise 4.2.i, part 1. Replace this paragraph with an explanation of each step. Say which category
plays which role, what happens to the functors `F` and `G`, what the bijection (4.2.1) becomes, and
why the component `η` of the new adjunction is the opposite of Riehl's `ε`.
-/

/-
Exercise 4.2.i, part 2. The adjunction `adj.op` has the expected form, its unit is the opposite of
the counit of `adj`, and its counit is the opposite of the unit of `adj`.

Suggested proof. Use `exact adj.op` for the first statement, and use `rfl` for the other two.
-/
example : G.op ⊣ F.op := by
  sorry

example (d : 𝒟) : adj.op.unit.app (op d) = (adj.ε d).op := by
  sorry

example (c : 𝒞) : adj.op.counit.app (op c) = (adj.η c).op := by
  sorry

/-
Exercise 4.2.i, part 3. Naturality of the unit of `adj.op` at `k.op` is the naturality of `ε` at
`k`, with the order of composition reversed. This exercise makes that translation explicit.

Suggested proof. The term `adj.op.unit.naturality k.op` is an equation in `𝒟ᵒᵖ` between two
opposite morphisms, up to definitional unfolding. The lemma `Quiver.Hom.op_inj` says that `.op` is
injective, so `Quiver.Hom.op_inj (adj.op.unit.naturality k.op)` is an equation in `𝒟`. Finish with
`.symm`.
-/
theorem counit_naturality_via_op {d d' : 𝒟} (k : d ⟶ d') :
    F.map (G.map k) ≫ adj.ε d' = adj.ε d ≫ k := by
  sorry

end Dual

/-
### Exercise 4.2.ii

Riehl asks the reader to pick a forgetful functor from Example 4.1.10 and to prove that it is a
right adjoint by defining its left adjoint, the unit and the counit, and by demonstrating that the
triangle identities hold. This file picks the first item of that example, the forgetful functor
`U : Set∗ ⥤ Set` from pointed sets, because every construction in it is short. The left adjoint
carries a set `X` to the pointed set `X₊` obtained by adjoining a new basepoint.

Lean construct: `Pointed`. An object `Y : Pointed` is a structure with a type `Y.X` and a basepoint
`Y.point : Y.X`, and `Y` coerces to the type `Y.X`. A morphism `k : Y ⟶ Z` is a structure with a
function `k.toFun : Y.X → Z.X` and a proof `k.map_point : k.toFun Y.point = Z.point`. The functor
`forget Pointed : Pointed ⥤ Type u` is Riehl's `U`.

Mathlib's left adjoint is `typeToPointed : Type u ⥤ Pointed`. It uses `Option X` for the set `X₊`,
with `none` as the basepoint and `some x` as the copy of `x`. A function `Option X → W` is defined
by giving its values on `none` and on `some x`, and the function `fun o => o.elim w₀ φ` sends
`none` to `w₀` and sends `some x` to `φ x`.

The category `Type u` wraps its morphisms in a structure in this version of Mathlib, as the §4.1
file explained. A function `φ : X → Y` becomes a morphism `↾φ : X ⟶ Y`.
-/
section PointedSets

/-
Warm-ups on `Pointed`. All of the statements hold by definition.

Suggested proof. Use `rfl`.
-/
example (X : Type u) : (typeToPointed.obj X : Type u) = Option X := by
  sorry

example (X : Type u) : (typeToPointed.obj X).point = none := by
  sorry

example {X Y : Type u} (f : X ⟶ Y) (x : Option X) :
    (typeToPointed.map f).toFun x = Option.map f x := by
  sorry

example (Y : Pointed.{u}) : (forget Pointed).obj Y = Y.X := by
  sorry

/-
Exercise 4.2.ii, part 1. Define the unit. Its component at `X` is the inclusion of `X` into `X₊`.

Suggested proof. Define the component as `↾(fun x => some x)`. For the field `naturality`, begin
with `ext x`, which reduces the equation between morphisms in `Type u` to an equation between
elements, and finish with `rfl`.
-/
def pointedUnit : 𝟭 (Type u) ⟶ typeToPointed ⋙ forget Pointed where
  app X := by
    sorry
  naturality X Y f := by
    sorry

/-
Exercise 4.2.ii, part 2. Define the counit. Its component at `Y` is the morphism `(Y.X)₊ ⟶ Y` that
sends the new basepoint to the basepoint of `Y` and sends each `some y` to `y`. This morphism is the
evaluation map that Riehl's footnote 5 describes.

Suggested proof. Define the component as the anonymous constructor
`⟨fun o => o.elim Y.point id, rfl⟩`, where `rfl` proves that the morphism preserves basepoints.
For the field `naturality`, begin with `ext o`, and then split into cases with
`cases o with | none => ... | some y => ...`. In the case `none`, the equation is
`k.map_point.symm`. In the case `some y`, the equation holds by `rfl`.
-/
def pointedCounit : forget Pointed ⋙ typeToPointed ⟶ 𝟭 Pointed where
  app Y := by
    sorry
  naturality Y Z k := by
    sorry

/-
Exercise 4.2.ii, part 3. Demonstrate the triangle identities.

Suggested proof. For the left triangle identity, begin with `ext o`, split `o` into cases, and close
each case with `rfl`. For the right triangle identity, begin with `ext y` and close the goal with
`rfl`.
-/
def pointedAdj : typeToPointed.{u} ⊣ forget Pointed where
  unit := pointedUnit
  counit := pointedCounit
  left_triangle_components X := by
    sorry
  right_triangle_components Y := by
    sorry

end PointedSets

/-
### Exercise 4.2.iii

Suppose that `F` and `G` are order-preserving functions between preorders. Riehl asks for a proof,
either by direct argument or by quoting a more general theorem, that the following are equivalent.

 (i) For all `a` and `b`, the inequality `F a ≤ b` holds if and only if `a ≤ G b`.
 (ii) For all `a`, the inequality `a ≤ G (F a)` holds, and for all `b`, the inequality `F (G b) ≤ b`
   holds.

Parts 1 and 2 below give the direct argument. Part 3 quotes the general theorem: the two
inequalities of (ii) are a unit and a counit, the triangle identities hold automatically in a
preorder, and Theorem 4.2.7 then provides (i).
-/
section Preorders

variable {A : Type u₁} {B : Type u₂} [Preorder A] [Preorder B] {F : A → B} {G : B → A}

/-
Exercise 4.2.iii, part 1. Condition (i) implies condition (ii).

Suggested proof. Apply the hypothesis `h` to `le_rfl` in each direction: the first component is
`fun a => (h a (F a)).mp le_rfl`, and the second is similar.
-/
theorem unit_counit_of_gc (h : ∀ a b, F a ≤ b ↔ a ≤ G b) :
    (∀ a, a ≤ G (F a)) ∧ (∀ b, F (G b) ≤ b) := by
  sorry

/-
Exercise 4.2.iii, part 2. Condition (ii) implies condition (i), by a direct argument.

Suggested proof. After `constructor` and `intro h`, the forward direction follows from
`(hη a).trans (hG h)`, and the reverse direction follows from `(hF h).trans (hε b)`.
-/
theorem gc_of_unit_counit (hF : Monotone F) (hG : Monotone G)
    (hη : ∀ a, a ≤ G (F a)) (hε : ∀ b, F (G b) ≤ b) (a : A) (b : B) :
    F a ≤ b ↔ a ≤ G b := by
  sorry

/-
Exercise 4.2.iii, part 3. Condition (ii) implies condition (i), by quoting Theorem 4.2.7.

The definition below provides the unit and the counit, and it provides no proofs. Every field that
is left out has a default proof, `cat_disch`, which succeeds because any two parallel morphisms in
a preorder are equal. That observation is the reason the triangle identities are automatic.

Suggested proof. For the fields `app`, use `homOfLE (hη a)` and `homOfLE (hε b)`. For the final
statement, use Mathlib's `Adjunction.gc`, which turns an adjunction between preorders into a Galois
connection, with `exact (adjOfUnitCounitLE hF hG hη hε).gc`.
-/
def adjOfUnitCounitLE (hF : Monotone F) (hG : Monotone G)
    (hη : ∀ a, a ≤ G (F a)) (hε : ∀ b, F (G b) ≤ b) : hF.functor ⊣ hG.functor where
  unit :=
    { app := fun a => by
        sorry
        }
  counit :=
    { app := fun b => by
        sorry
        }

example (hF : Monotone F) (hG : Monotone G)
    (hη : ∀ a, a ≤ G (F a)) (hε : ∀ b, F (G b) ≤ b) : GaloisConnection F G := by
  sorry

end Preorders

/-
### Exercise 4.2.iv

A strict morphism of adjunctions from `F ⊣ G` to `F' ⊣ G'` is a pair of functors `H : 𝒞 ⥤ 𝒞'` and
`K : 𝒟 ⥤ 𝒟'` such that the square of left adjoints and the square of right adjoints both commute,
which is to say that `K F = F' H` and `H G = G' K`, and that satisfy one additional condition. Riehl
asks for a proof that the following forms of the additional condition are equivalent.

 (i) `H η = η' H`, where `η` and `η'` are the respective units.
 (ii) `K ε = ε' K`, where `ε` and `ε'` are the respective counits.
 (iii) Transposition across the adjunctions commutes with application of `H` and `K`.

[Diagram](assets/morphism_of_adjunctions.svg)

This exercise departs from Riehl's statement in one respect. The equations `K F = F' H` and
`H G = G' K` are equations between functors, and in Lean such an equation makes the two sides of
`H η = η' H` have different types, which would force a cast called `eqToHom` into every statement.
The formulation below replaces the two equations with chosen isomorphisms

  `a c : K.obj (F.obj c) ≅ F'.obj (H.obj c)`  and  `b d : H.obj (G.obj d) ≅ G'.obj (K.obj d)`

that are natural in `c` and `d`. The hypotheses `ha` and `hb` record the naturality as squares.
Riehl's strict case is the case in which `a` and `b` are identity isomorphisms. The conditions (i),
(ii) and (iii) are then stated with `a` and `b` inserted wherever the types require them.

Condition (i) says that the triangle below commutes for every `c`. The top composite is `H η_c`
followed by `b_{F c}` and `G' a_c`.

[Diagram](assets/unit_compatible.svg)

Condition (ii) says that the following triangle commutes for every `d`.

[Diagram](assets/counit_compatible.svg)

Condition (iii) says that for every `f : F c ⟶ d`, applying `H` to the transpose of `f` and
following with `b_d` gives the transpose under `F' ⊣ G'` of the composite of the inverse of `a_c`
with `K f`.

Lean construct: `include`. A hypothesis declared with `variable` is added to a theorem only when
the statement of that theorem mentions it. The phrase `include hb in` before a theorem adds `hb`
even when only the proof needs it.

Lean construct: `CommSq.horiz_inv`. If `sq : CommSq i.hom l r j.hom` is a square whose top and
bottom sides are the forward morphisms of isomorphisms `i` and `j`, then `sq.horiz_inv` is the
square `CommSq i.inv r l j.inv`, which reverses the horizontal arrows and exchanges the vertical
sides.
-/
section Morphisms

variable {𝒞' : Type u₄} [Category.{v₄} 𝒞'] {𝒟' : Type u₅} [Category.{v₅} 𝒟']
  {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} {F' : 𝒞' ⥤ 𝒟'} {G' : 𝒟' ⥤ 𝒞'}
  (adj : F ⊣ G) (adj' : F' ⊣ G') {H : 𝒞 ⥤ 𝒞'} {K : 𝒟 ⥤ 𝒟'}
  (a : ∀ c : 𝒞, K.obj (F.obj c) ≅ F'.obj (H.obj c))
  (b : ∀ d : 𝒟, H.obj (G.obj d) ≅ G'.obj (K.obj d))

/-- Condition (i). -/
def UnitCompatible : Prop :=
  ∀ c : 𝒞, H.map (adj.η c) ≫ (b (F.obj c)).hom ≫ G'.map (a c).hom = adj'.η (H.obj c)

/-- Condition (ii). -/
def CounitCompatible : Prop :=
  ∀ d : 𝒟, F'.map (b d).inv ≫ (a (G.obj d)).inv ≫ K.map (adj.ε d) = adj'.ε (K.obj d)

/-- Condition (iii). -/
def TransposeCompatible : Prop :=
  ∀ (c : 𝒞) (d : 𝒟) (f : F.obj c ⟶ d),
    H.map (f ♭[adj]) ≫ (b d).hom = ((a c).inv ≫ K.map f) ♭[adj']

variable {adj adj' a b}
  (ha : ∀ {c c' : 𝒞} (h : c ⟶ c'),
    CommSq (a c).hom (K.map (F.map h)) (F'.map (H.map h)) (a c').hom)
  (hb : ∀ {d d' : 𝒟} (k : d ⟶ d'),
    CommSq (b d).hom (H.map (G.map k)) (G'.map (K.map k)) (b d').hom)

/-
Exercise 4.2.iv, part 1. Condition (i) implies condition (iii).

Suggested proof. After `intro c d f`, rewrite the goal with `adj.flat_eq`, then with `adj'.flat_eq`,
then with `← hu c`, which expands `η'` through condition (i). Rewrite with `H.map_comp`, with
`Category.assoc`, and with `← (hb f).w`, which moves `b` past `H (G f)`. The remaining goal cancels
`a_c` against its inverse, and `simp` closes it.
-/
include hb in
theorem transposeCompatible_of_unit (hu : UnitCompatible adj adj' a b) :
    TransposeCompatible adj adj' a b := by
  sorry

/-
Exercise 4.2.iv, part 2. Condition (iii) implies condition (i).

Suggested proof. After `intro c`, apply condition (iii) to the identity morphism with
`have h := ht c (F.obj c) (𝟙 (F.obj c))`. Rewrite `h` with `adj.flat_eq`, `adj'.flat_eq`,
`G.map_id`, `K.map_id` and `Category.comp_id` twice. Then rewrite the goal with
`← Category.assoc`, `h`, `Category.assoc` and `← G'.map_comp`, and close it with `simp`.
-/
theorem unit_of_transposeCompatible (ht : TransposeCompatible adj adj' a b) :
    UnitCompatible adj adj' a b := by
  sorry

/-
Exercise 4.2.iv, part 3. Condition (ii) implies condition (iii).

Suggested proof. After `intro c d f`, use `rw [← Equiv.symm_apply_eq]`, which transposes the
equation across `F' ⊣ G'`. Then rewrite with `adj'.sharp_eq`, with `← hc d`, with `F'.map_comp`,
with `Category.assoc`, and with `← F'.map_comp_assoc (b d).hom`, and cancel `b_d` with
`Iso.hom_inv_id`, `F'.map_id` and `Category.id_comp`. Next, bind the inverse naturality square
with the following lines.

    have sq : CommSq (a c).inv (F'.map (H.map (f ♭[adj]))) (K.map (F.map (f ♭[adj])))
        (a (G.obj d)).inv := (ha (f ♭[adj])).horiz_inv

Rewrite the goal with `← Category.assoc`, with `← sq.w`, with `Category.assoc`, with `← K.map_comp`,
with `← adj.sharp_eq`, and with `Equiv.symm_apply_apply`.
-/
include ha in
theorem transposeCompatible_of_counit (hc : CounitCompatible adj adj' a b) :
    TransposeCompatible adj adj' a b := by
  sorry

/-
Exercise 4.2.iv, part 4. Condition (iii) implies condition (ii).

Suggested proof. After `intro d`, apply condition (iii) to `adj.ε d` with
`have h := ht (G.obj d) d (adj.ε d)`. Establish the fact `(adj.ε d) ♭[adj] = 𝟙 (G.obj d)` in a
`have`, by rewriting with `← Equiv.eq_symm_apply`, `adj.sharp_eq`, `F.map_id` and
`Category.id_comp`. Rewrite `h` with that fact, with `H.map_id`, with `Category.id_comp`, with
`← Equiv.symm_apply_eq` and with `adj'.sharp_eq`. Then rewrite the goal with `← h`, with
`← F'.map_comp_assoc`, with `Iso.inv_hom_id`, with `F'.map_id` and with `Category.id_comp`.
-/
theorem counit_of_transposeCompatible (ht : TransposeCompatible adj adj' a b) :
    CounitCompatible adj adj' a b := by
  sorry

end Morphisms
