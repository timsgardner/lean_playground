/-
# Riehl, *Category Theory in Context*, §4.1: Adjoint functors
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.IsoCat
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Set.Lattice.Image
import LeanPlayground.Scratch.category_kindergarten.check_diagrams
import LeanPlayground.Scratch.category_kindergarten.common_tools
import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget

open CategoryTheory Opposite
open scoped CategoryKindergarten

-- set_option pp.categoryTheory.hideConcreteHom true
-- set_option pp.proofs true          -- print proof terms instead of ⋯
set_option pp.deepTerms true       -- don't elide deeply nested subterms
set_option linter.unusedTactic false

-- Shift-click a hypothesis or goal in the infoview to draw it as a diagram;
-- see `diagram_tools` for the available presenters. The output of `#check` cannot be
-- selected, so `check_diagrams` draws it instead: put the cursor on the `#check`.
show_panel_widgets [local ProofWidgets.SelectionPanel]

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]
variable {ℰ : Type u₃} [Category.{v₃} ℰ]

/-
Notation for transposes. `f ♭[adj]` is `adj.homEquiv _ _ f` and `g ♯[adj]` is
`(adj.homEquiv _ _).symm g`. The notation expands to exactly those terms, so the
Mathlib lemmas about `homEquiv` still apply with `rw` and `simp`, and the
delaborator below prints such terms back in this form in goals.
-/
section TransposeNotation
open Lean PrettyPrinter Delaborator SubExpr

notation:max f "♭[" adj "]" =>
  DFunLike.coe (CategoryTheory.Adjunction.homEquiv adj _ _) f
notation:max g "♯[" adj "]" =>
  DFunLike.coe (Equiv.symm (CategoryTheory.Adjunction.homEquiv adj _ _)) g

@[app_delab DFunLike.coe]
meta def delabAdjTranspose : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  let fn := e.appFn!.appArg!
  if fn.isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 6 delab
    let f ← withAppArg delab
    `($f ♭[$adj])
  else if fn.isAppOfArity ``Equiv.symm 3 &&
      (fn.getArg! 2).isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 2 <| withNaryArg 6 delab
    let g ← withAppArg delab
    `($g ♯[$adj])
  else failure

end TransposeNotation

-- Definition 4.1.1: Adjunctions I
/-
Riehl: an adjunction consists of a pair of functors `F : 𝒞 ⥤ 𝒟` and
`G : 𝒟 ⥤ 𝒞` together with a specified isomorphism

  `𝒟(F c, d) ≅ 𝒞(c, G d)`                                        (4.1.2)

for each `c : 𝒞` and `d : 𝒟`, which is natural in both variables. Then `F` is
left adjoint to `G`, and `G` is right adjoint to `F`. Riehl writes `f♯ : F c ⟶ d`
and `f♭ : c ⟶ G d` for a pair of morphisms that correspond under (4.1.2), and
calls them adjuncts or transposes of each other.

Mathlib's notation `F ⊣ G` stands for `Adjunction F G`, but the structure
`Adjunction` is not Definition 4.1.1. Its fields are a unit `𝟭 𝒞 ⟶ F ⋙ G`, a
counit `G ⋙ F ⟶ 𝟭 𝒟`, and the two triangle identities, which is Riehl's
Definition 4.2.5 (adjunctions II). Theorem 4.2.7 shows that the two
definitions determine each other, and Mathlib uses that equivalence in both
directions:

* An adjunction in the sense of Definition 4.1.1 is a term of
  `Adjunction.CoreHomEquiv F G`, and `Adjunction.mkOfHomEquiv` turns it into an
  `F ⊣ G`.
* Every `adj : F ⊣ G` has an isomorphism (4.1.2), `adj.homEquiv c d`. It is an
  `Equiv`, that is, a bijection between the types `F.obj c ⟶ d` and
  `c ⟶ G.obj d`. In Riehl's notation `f♯` and `f♭` are the two morphisms of a
  single corresponding pair, and Lean has no decorations, so we give the
  morphism on one side a plain name and reach the other side by applying the
  bijection. If `f : F.obj c ⟶ d` plays the role of `f♯`, then its transpose
  `f♭` is `adj.homEquiv c d f`. If `g : c ⟶ G.obj d` plays the role of `g♭`,
  then its transpose `g♯` is `(adj.homEquiv c d).symm g`. The notation at the
  top of this file abbreviates these as `f ♭[adj]` and `g ♯[adj]`, leaving `c`
  and `d` to be inferred, and we use it from here on.

Since we read §4.1 before §4.2, we will work with `homEquiv` and treat the
unit and counit as a black box until §4.2 opens it.
-/
#print Adjunction.CoreHomEquiv
#check @Adjunction.mkOfHomEquiv
#check @Adjunction.homEquiv

/-
Unpacking the weird diagram on 133 (pdf 153).

The diagram asserts a natural transformation from `𝒟(F-, -)` to `𝒞(-, G-)`.
These are both bifunctors `𝒞ᵒᵖ × D ⥤ Type` (or to `SET`, in Riehl; the uppercase
is probably size-theoretically significant).

"Natural in both variables" follows merely from having a natural transformation
between bifunctors.

The odd diamond shape of the diagram, with the nat trans 2-cell straddled by
`(F × 𝟭 𝒟) ≫ 𝒟(-, -)` above and `(𝟭 𝒞 × G) ≫ 𝒞(-, -)` below, expresses a commutativity
condition when either `d` or `c` (respectively) are held fixed.

What does that nat trans mean? Objects of the domain product category `𝒞ᵒᵖ × D` are
pairs `(c, d)` for some `c ∈ 𝒞` and `d ∈ 𝒟`.

Let `p1 ∈ 𝒞ᵒᵖ × 𝒟 := (c1, d1)` and `p2 := (c2, d2)`. A morphism `m ∈ 𝒞ᵒᵖ × 𝒟(p1, p2)` --
or, in Lean notation, `m : p1 ⟶ p2` -- is a pair `(h, k)` for some `h : c1 ⟶ c2` and
`k : d1 ⟶ d2`.

-/


-- So this sharp-flat notation thing doesn't drive me nuts:
structure SharpFlat {F : 𝒞 ⥤ 𝒟} {G: 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c : 𝒞} {d : 𝒟} where
  sharp : (F.obj c) ⟶ d
  flat : c ⟶ (G.obj d)
  h_sharp : sharp = flat ♯[adj]
  h_flat : flat = sharp ♭[adj]

namespace SharpFlat

def ofSharp
    {F : 𝒞 ⥤ 𝒟}
    {G: 𝒟 ⥤ 𝒞}
    (adj : F ⊣ G)
    {c : 𝒞}
    {d : 𝒟} (sharp: (F.obj c) ⟶ d)
    : SharpFlat adj (c := c) (d := d):=
  {
    sharp,
    flat := sharp ♭[adj],
    h_sharp := by simp
    h_flat := by simp
  }

def ofFlat
    {F : 𝒞 ⥤ 𝒟}
    {G: 𝒟 ⥤ 𝒞}
    (adj : F ⊣ G)
    {c : 𝒞}
    {d : 𝒟} (flat: c ⟶ G.obj d)
    : SharpFlat adj (c := c) (d := d):=
  {
    sharp := flat ♯[adj]
    flat,
    h_sharp := by simp
    h_flat := by simp
  }

end SharpFlat


-- def sharp {F : 𝒞 ⥤ 𝒟} {G: 𝒟 ⥤ 𝒞} {adj : F ⊣ G} {c : 𝒞} {d : 𝒟} (f_flat : F.obj c ⟶ d): 𝒞 × 𝒟 :=

--   (f_sharp, f_flat)

/-
Naturality in `𝒟`. Riehl: for any `f♯ : F c ⟶ d` and `k : d ⟶ d'`, the
transpose of `k · f♯ : F c ⟶ d'` is the composite of `f♭ : c ⟶ G d` with
`G k : G d ⟶ G d'`. Riehl writes composites right to left and Lean writes
them left to right, so `k · f♯` is `f ≫ k` and `G k · f♭` is
`f ♭[adj] ≫ G.map k`. Mathlib calls this
`Adjunction.homEquiv_naturality_right`, because it concerns the right-hand
argument `d` of `adj.homEquiv c d`.

In the diagram below, the left triangle lives in `𝒟` and commutes by
definition, since its diagonal is the composite `k · f♯`. The right triangle
lives in `𝒞`, and its diagonal is the transpose of that composite. Naturality
in `𝒟` is the statement that the right triangle also commutes.

[Diagram](assets/naturality_right.svg)
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c : 𝒞} {d d' : 𝒟}
    (f : F.obj c ⟶ d) (k : d ⟶ d') :
    (f ≫ k)♭[adj] = f ♭[adj] ≫ G.map k :=
  adj.homEquiv_naturality_right f k

/-
Naturality in `𝒞`. Riehl: for any `h : c' ⟶ c`, the transpose of
`f♯ · F h : F c' ⟶ d` is the composite of `h : c' ⟶ c` with `f♭ : c ⟶ G d`.
In Lean, `f♯ · F h` is `F.map h ≫ f` and its transpose is
`h ≫ f ♭[adj]`. Mathlib calls this
`Adjunction.homEquiv_naturality_left`.
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d : 𝒟}
    (h : c' ⟶ c) (f : F.obj c ⟶ d) :
    (F.map h ≫ f)♭[adj] = h ≫ f ♭[adj] :=
  adj.homEquiv_naturality_left h f

/-
The four naturality equations. For `adj : F ⊣ G`, Mathlib states naturality in
each variable twice, once for the bijection `adj.homEquiv` and once for its
inverse. Writing `f` for a morphism `F c ⟶ d` playing the role of `f♯`, and `g`
for a morphism `c ⟶ G d` playing the role of `g♭`, they are:

* `adj.homEquiv_naturality_left h f`: the transpose of `f♯ · F h` is `f♭ · h`,
  that is, `(F.map h ≫ f)♭[adj] = h ≫ f ♭[adj]`.
* `adj.homEquiv_naturality_right f k`: the transpose of `k · f♯` is `G k · f♭`,
  that is, `(f ≫ k)♭[adj] = f ♭[adj] ≫ G.map k`.
* `adj.homEquiv_naturality_left_symm h g`: the transpose of `g♭ · h` is
  `g♯ · F h`, that is, `(h ≫ g)♯[adj] = F.map h ≫ g ♯[adj]`.
* `adj.homEquiv_naturality_right_symm g k`: the transpose of `G k · g♭` is
  `k · g♯`, that is, `(g ≫ G.map k)♯[adj] = g ♯[adj] ≫ k`.

Because each `adj.homEquiv c d` is a bijection, the `_symm` form of each
equation says the same thing as the plain form, so in a proof you can use
whichever one matches the goal. The warm-ups below practice the `Equiv` moves
that let you pass between the two forms.

(E) Warm-ups on `Equiv`. For a bijection `e : α ≃ β`, the inverse is
`e.symm : β ≃ α`. The basic facts are that the two round trips are identities,
`Equiv.symm_apply_apply` and `Equiv.apply_symm_apply`; that an equation
involving `e.symm` can be moved to the other side, `Equiv.symm_apply_eq` and
`Equiv.eq_symm_apply`; and that `e` is injective, `Equiv.injective`. Each
warm-up is one line.
-/
example {α β : Type*} (e : α ≃ β) (a : α) : e.symm (e a) = a := by
  -- simp closes
  exact e.symm_apply_apply a

example {α β : Type*} (e : α ≃ β) (b : β) : e (e.symm b) = b := by
  -- simp closes
  exact e.apply_symm_apply b

example {α β : Type*} (e : α ≃ β) (a : α) (b : β) : e.symm b = a ↔ b = e a := by
  exact e.symm_apply_eq

example {α β : Type*} (e : α ≃ β) (a : α) (b : β) : a = e.symm b ↔ e a = b := by
  exact e.eq_symm_apply

example {α β : Type*} (e : α ≃ β) (a a' : α) (h : e a = e a') : a = a' := by
  exact e.injective h

-- Lemma 4.1.3: Naturality as a correspondence of commutative squares
/-
Riehl: consider functors `F : 𝒞 ⥤ 𝒟` and `G : 𝒟 ⥤ 𝒞` equipped with specified
isomorphisms `𝒟(F c, d) ≅ 𝒞(c, G d)` for all `c : 𝒞` and `d : 𝒟`. Naturality of
this collection of isomorphisms is equivalent to the assertion that, for any
morphisms with domains and codomains as displayed in (4.1.4), the left-hand
square commutes in `𝒟` if and only if the right-hand transposed square commutes
in `𝒞`.

In the notation of the exercises below, the data are morphisms `h : c ⟶ c'` in
`𝒞` and `k : d ⟶ d'` in `𝒟`, together with `f : F.obj c ⟶ d` and
`g : F.obj c' ⟶ d'`, whose transposes are `f♭ : c ⟶ G.obj d` and
`g♭ : c' ⟶ G.obj d'`. The square in `𝒟` has `f` on top, `F.map h` on the left,
`k` on the right, and `g` on the bottom. The transposed square in `𝒞` has `f♭`
on top, `h` on the left, `G.map k` on the right, and `g♭` on the bottom.

[Diagram](assets/transposed_squares.svg)

The statements below record these squares with Mathlib's `CommSq`. The
proposition `CommSq top left right bottom` says that the square with those four
sides commutes, and its arguments are listed in exactly that order. So the
square in `𝒟` is `CommSq f (F.map h) k g`, and the transposed square in `𝒞` is
`CommSq f♭ h (G.map k) g♭`. A `CommSq` is a structure with a single field `w`,
the equation `top ≫ right = left ≫ bottom`:

- from `sq : CommSq f (F.map h) k g`, the term `sq.w` is the equation
  `f ≫ k = F.map h ≫ g`;
- to prove a `CommSq`, use `refine ⟨?_⟩`, which leaves that equation as the
  goal, or write `⟨w⟩` for a proof `w` of the equation (`constructor` also
  works, but it wraps the goal in an `autoParam` that clutters the display);
- a square that commutes for trivial reasons, for instance because one side is
  an identity, can often be proved by `{}`, since the field `w` defaults to the
  tactic `cat_disch`.

In the infoview, shift-click the type of a `CommSq` hypothesis or goal and
choose "CommSq diagram" to see it drawn as a square. An equation of the form
`a ≫ b = c ≫ d` can be drawn the same way with "Commutative square".

Riehl leaves the proof as Exercise 4.1.i. Exercise 1 proves the forward
direction: if the bijections are natural, then the squares correspond. Exercise
2 proves the converse. Mathlib states the forward direction as
`Adjunction.homEquiv_naturality_left_square_iff`, but the point here is to
derive it from the two naturality equations.
-/

/-
Exercise 1a. If the square in `𝒟` commutes, then so does the transposed square
in `𝒞`. After `refine ⟨?_⟩`, rewrite the composites `f♭ ≫ G.map k` and
`h ≫ g♭` as transposes of composites in `𝒟`, using the two naturality lemmas
from right to left.

Mathlib's version is `CommSq.right_adjoint`, in the module
`Mathlib.CategoryTheory.LiftingProperties.Adjunction`, stated for an adjunction
`G ⊣ F` with the letters exchanged.
-/
theorem transposed_square_of_square {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (sq : CommSq f (F.map h) k g) :
    CommSq (f ♭[adj]) h (G.map k) (g ♭[adj]) := by
  refine ⟨?_⟩
  have h2 := adj.homEquiv_naturality_right f k
  have h3 := adj.homEquiv_naturality_left h g
  rw [← h2, ← h3, sq.w]

/-
Exercise 1b. Conversely, if the transposed square in `𝒞` commutes, then so does
the square in `𝒟`. After `refine ⟨?_⟩`, both sides of the goal are morphisms
`F.obj c ⟶ d'`, so it suffices to show that their transposes agree. Continue
with `apply (adj.homEquiv c d').injective`.
-/
theorem square_of_transposed_square {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (sq : CommSq (f ♭[adj]) h (G.map k) (g ♭[adj])) :
    CommSq f (F.map h) k g := by
  refine ⟨?_⟩
  apply (adj.homEquiv c d').injective
  calc
    (f ≫ k)♭[adj] = f ♭[adj] ≫ G.map k := by exact adj.homEquiv_naturality_right f k
    _ = h ≫ g ♭[adj] := by exact sq.w
    _ = (F.map h ≫ g)♭[adj] := by exact (adj.homEquiv_naturality_left h g).symm

/-
Exercise 2. The converse half of Lemma 4.1.3. In this section, `e` is a family
of bijections `e c d : (F.obj c ⟶ d) ≃ (c ⟶ G.obj d)` about which nothing is
assumed except the hypothesis `hsq`: for every configuration (4.1.4), the square
in `𝒟` commutes if and only if the transposed square in `𝒞` commutes. The task
is to show that `e` is natural in both variables, and hence defines an
adjunction.

The idea in both parts is to choose a square in which one side is an identity.
For naturality in `𝒟` (2a), take `h := 𝟙 c` and `g := f ≫ k`. The square in
`𝒟` then commutes for trivial reasons, so `hsq` makes the transposed square
commute, and that square is the naturality equation up to an identity. For
naturality in `𝒞` (2b), take `k := 𝟙 d` and work from the `𝒞` side instead.

To use `hsq`, write `have := (hsq h k f g).mp {}` (or `.mpr`) with the
morphisms you have chosen. Here `{}` proves the trivial square; if `cat_disch`
cannot close it, write `⟨by simp⟩` instead. The result is a `CommSq`, and
`this.w` is its equation.
-/
section Squares

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
  (hsq : ∀ {c c' : 𝒞} {d d' : 𝒟} (h : c ⟶ c') (k : d ⟶ d')
    (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d'),
    CommSq f (F.map h) k g ↔ CommSq (e c d f) h (G.map k) (e c' d' g))
include hsq

/-
Exercise 2a. The bijections `e` are natural in `𝒟`. For a morphism
`f : F.obj c ⟶ d` and a morphism `k : d ⟶ d'` in `𝒟`, the transpose of the
composite `f ≫ k` is the transpose of `f` followed by `G.map k`. This equation
is the field `homEquiv_naturality_right` of `Adjunction.CoreHomEquiv`.
-/
theorem nat_right_of_squares {c : 𝒞} {d d' : 𝒟} (f : F.obj c ⟶ d) (k : d ⟶ d') :
    e c d' (f ≫ k) = e c d f ≫ G.map k := by
  have h := (hsq (h := 𝟙 c) (g := f ≫ k) k f |>.mp {}).w
  simp at h
  exact h.symm

/-
Exercise 2b. The inverse bijections `(e c d).symm` are natural in `𝒞`. For a
morphism `h : c ⟶ c'` in `𝒞` and a morphism `g' : c' ⟶ G.obj d`, the inverse
transpose of the composite `h ≫ g'` is `F.map h` followed by the inverse
transpose of `g'`. This equation is the field `homEquiv_naturality_left_symm` of
`Adjunction.CoreHomEquiv`.

The names follow `hsq`, as in 2a: the objects are `hsq`'s `c`, `c'` and `d`, with
`d' := d` and `k := 𝟙 d`, and `h` is `hsq`'s `h`. The morphism `g'` is the
transposed bottom side `e c' d g`, so `hsq`'s `g` is `(e c' d).symm g'`.
-/
theorem nat_left_symm_of_squares {c c' : 𝒞} {d : 𝒟} (h : c ⟶ c') (g' : c' ⟶ G.obj d) :
    (e c d).symm (h ≫ g') = F.map h ≫ (e c' d).symm g' := by
  let φ := hsq (c := c) (c' := c') (d' := d) h (𝟙 d) (f := (e c d).symm (h ≫ g')) (g := (e c' d).symm g')
  conv at φ => rhs; simp
  simp at φ
  obtain ⟨h2⟩ := φ
  simp at h2
  exact h2

/-
Exercise 2c. The functor `F` is left adjoint to `G`, by an adjunction whose
bijections on hom-sets are the given `e`. Assemble it using
`Adjunction.mkOfHomEquiv` and a `CoreHomEquiv` whose three fields are `e` and
the results of 2a and 2b.
-/
def adjOfSquares : F ⊣ G := by
  apply Adjunction.mkOfHomEquiv
  constructor
  case homEquiv =>
    exact e
  case homEquiv_naturality_left_symm =>
    apply nat_left_symm_of_squares
    exact hsq
  case homEquiv_naturality_right =>
    apply nat_right_of_squares
    exact hsq

end Squares


/-
## Adjunctions between preorders

Riehl: an adjunction between preorders is called a (monotone) Galois connection.
Functors between preorders are order-preserving functions, and an adjunction
`F ⊣ G` between preorders `A` and `B` asserts that `F a ≤ b` if and only if
`a ≤ G b` for all `a : A` and `b : B`. Here `F` is the lower adjoint and `G` is
the upper adjoint.

Mathlib's `GaloisConnection l u` is exactly this condition,
`∀ a b, l a ≤ b ↔ a ≤ u b`, stated for functions `l` and `u` with no
monotonicity assumption (monotonicity follows; see `GaloisConnection.monotone_l`
and `GaloisConnection.monotone_u`).

A preorder `X` is a category in which `x ⟶ y` is `ULift (PLift (x ≤ y))`, so a
morphism is a proof of `x ≤ y`, packaged so that it lives in `Type`. A monotone
function `l` with proof `hl : Monotone l` becomes a functor `hl.functor`, whose
action on objects is `l` itself.

(P) Warm-ups on preorder categories. Each of the four facts below is used in
Exercise 3.
-/
section Preorders

variable {X : Type*} [Preorder X]

-- (P1) A proof of `x ≤ y` gives a morphism `x ⟶ y`. Use `homOfLE h`, or its
-- dot-notation form `h.hom`.
example {x y : X} (h : x ≤ y) : x ⟶ y := by
  exact h.hom

-- (P2) Conversely, a morphism `x ⟶ y` gives a proof of `x ≤ y`. Use
-- `leOfHom f`, or its dot-notation form `f.le`.
example {x y : X} (f : x ⟶ y) : x ≤ y := by
  exact leOfHom f

-- (P3) For Riehl, a preorder is a category with at most one morphism between
-- any two objects. In Lean this is a theorem about the construction above: a
-- morphism `x ⟶ y` is a proof of `x ≤ y`, wrapped in `ULift` and `PLift`, and
-- Lean regards any two proofs of the same proposition as equal, so any two
-- morphisms `x ⟶ y` are equal too. Mathlib records this as the instance
-- `CategoryTheory.Preorder.subsingleton_hom : Subsingleton (x ⟶ y)`, and
-- `Subsingleton.elim f g` turns that instance into the equation `f = g`.
example {x y : X} (f g : x ⟶ y) : f = g := by
  exact Subsingleton.elim f g

-- (P4) A monotone function `l : X → X` determines a functor `hl.functor : X ⥤ X`,
-- where `hl : Monotone l` is the proof of monotonicity. Mathlib defines it
-- (`Monotone.functor`) by two fields. On objects it is `l`. On morphisms it
-- sends `g : x ⟶ y` to `homOfLE (hl g.le) : l x ⟶ l y`: the morphism `g` gives
-- the proof `g.le : x ≤ y` (P2), monotonicity turns that into a proof of
-- `l x ≤ l y`, and `homOfLE` turns that back into a morphism (P1). Mathlib
-- writes no proofs of the functor laws: each law is an equation between two
-- morphisms with the same domain and codomain, so it holds by P3, and the
-- default proof `cat_disch` closes it. Since the object map is the field `l`,
-- the equation below holds by definition, and `rfl` proves it.
example {l : X → X} (hl : Monotone l) (x : X) : hl.functor.obj x = l x := by
  rfl

end Preorders

/-
Exercise 3. Every Galois connection is an adjunction in the sense of Definition
4.1.1. Precisely, if `l : X → Y` and `u : Y → X` form a Galois connection
`gc`, then the functor `gc.monotone_l.functor : X ⥤ Y` induced by `l` is left
adjoint to the functor `gc.monotone_u.functor : Y ⥤ X` induced by `u`.

Build the adjunction with `Adjunction.mkOfHomEquiv`. You only need to
supply the field `homEquiv`, a bijection `(l x ⟶ y) ≃ (x ⟶ u y)` for each `x`
and `y`. Its forward map sends a morphism `l x ⟶ y` to a morphism `x ⟶ u y`,
using `gc.le_u : l x ≤ y → x ≤ u y` together with P1 and P2; its inverse map
uses `gc.l_le : x ≤ u y → l x ≤ y` in the same way. The two remaining fields of
the bijection, `left_inv` and `right_inv`, say that composing the two maps in
either order gives back the morphism you started with; both hold by P3, since
the result and the original morphism have the same domain and codomain.

Leave out the two naturality fields of `CoreHomEquiv`. Each of them is an
equation between two morphisms with the same domain and codomain, so it holds
by P3, and the default proof `cat_disch` closes it without help. This is the
Lean form of Riehl's remark that every diagram in a preorder commutes.

Mathlib's version is `GaloisConnection.adjunction`.
-/
example {X Y : Type*} [Preorder X] [Preorder Y] {l : X → Y} {u : Y → X}
    (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor := by
  apply Adjunction.mkOfHomEquiv
  constructor
  case homEquiv =>
    intro x y
    constructor
    case toFun =>
      intro f
      exact (gc.le_u f.le).hom
    case invFun =>
      -- this is (almost) the same as above,
      -- but constructed with more apply
      intro g
      apply LE.le.hom
      apply gc.l_le
      exact g.le
      -- Equivalently, we could have just said
      -- exact (fun m => (gc.l_le m.le).hom)
    case left_inv =>
      simp [autoParam]
      intro bla
      simp
      -- The infoview doesn't do a great job showing it unless
      -- you look carefully, but the lhs of the goal `⋯.hom = bla` here
      -- has the structure `(<horrible stuff> : l x ≤ y).hom`. So it's a
      -- hom in a preorder category (which would also follow from the goal
      -- equation being even type correct, since we're comparing it to the
      -- known hom-in-a-preorder-category `bla`). Hom sets in preorder categories
      -- are Subsingletons -- they contain at most one element. So if we can
      -- even write the equation `<whatever> = bla`, it's automatically true
      -- by Subsingleton.elim.
      apply Subsingleton.elim
    case right_inv =>
      -- Exact same idea
      intro _
      apply Subsingleton.elim
  · cat_disch
  · cat_disch


-- Example 4.1.7: Floor and ceiling
/-
Riehl: the inclusion of posets `ℤ ↪ ℝ`, with the usual ordering `≤`, has both
left and right adjoints, namely the ceiling and floor functions. For any integer
`n` and real number `r`, `n ≤ r` if and only if `n ≤ ⌊r⌋`, so `⌊−⌋ : ℝ → ℤ` is
right adjoint to the inclusion. Dually, `r ≤ n` if and only if `⌈r⌉ ≤ n`, so
`⌈−⌉ : ℝ → ℤ` is left adjoint to the inclusion. Thus there is an adjoint triple
`⌈−⌉ ⊣ (ℤ ↪ ℝ) ⊣ ⌊−⌋`.

Nothing here is special to `ℝ`. Mathlib's floor and ceiling are defined for
any linearly ordered ring `α` with a `FloorRing` instance, and `ℝ` and `ℚ` are
both examples. We work in that generality, which keeps the real numbers out of
the imports. The inclusion `ℤ ↪ α` is the cast `(↑) : ℤ → α`.

Exercise 4. Prove both Galois connections. Each is one lemma about `Int.floor`
or `Int.ceil`; `exact?` will find them, or look for `Int.le_floor` and
`Int.ceil_le`.
-/
section Floor

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α]

theorem gc_cast_floor : GaloisConnection ((↑) : ℤ → α) Int.floor := by
  exact Int.gc_coe_floor

theorem gc_ceil_cast : GaloisConnection Int.ceil ((↑) : ℤ → α) := by
  exact Int.gc_ceil_coe

/-
An adjoint triple `⌈−⌉ ⊣ (ℤ ↪ α) ⊣ ⌊−⌋` requires the two adjunctions to share
the same middle functor. Here the inclusion becomes a functor twice, by
`Monotone.functor` (see P4), each time from a different proof that the cast is
monotone: `(gc_cast_floor).monotone_l`, from the connection in which the cast
is the lower adjoint, and `(gc_ceil_cast).monotone_u`, from the one in which
it is the upper adjoint. These two functors differ only in which proof they
were built from. Lean treats any two proofs of the same proposition as
definitionally equal, so the two functors are definitionally equal, and the
`example` below proves this by `rfl`. Hence the right adjoint of `ceilCastAdj`
and the left adjoint of `castFloorAdj` are the same functor.
-/
example : (gc_cast_floor (α := α)).monotone_l.functor =
    (gc_ceil_cast (α := α)).monotone_u.functor := rfl

def ceilCastAdj : (gc_ceil_cast (α := α)).monotone_l.functor ⊣
    (gc_ceil_cast (α := α)).monotone_u.functor :=
  gc_ceil_cast.adjunction

def castFloorAdj : (gc_cast_floor (α := α)).monotone_l.functor ⊣
    (gc_cast_floor (α := α)).monotone_u.functor :=
  gc_cast_floor.adjunction

end Floor


-- Example 4.1.8: Direct image, inverse image, and the dual image
/-
Riehl: consider a function `f : A → B` between sets. The subsets of `A` and the
subsets of `B` form posets `P A` and `P B`, ordered by inclusion, and `f`
induces direct image and inverse image functors `f_* : P A ⥤ P B` and
`f⁻¹ : P B ⥤ P A`. The inverse image is right adjoint to the direct image: for
`A' ⊆ A` and `B' ⊆ B`, `f(A') ⊆ B'` if and only if `A' ⊆ f⁻¹(B')`.

The inverse image has a further right adjoint `f_!`, which carries a subset
`A' ⊆ A` to the subset of elements of `B` whose fibers lie entirely in `A'`.
With this definition, `B' ⊆ f_!(A')` if and only if `f⁻¹(B') ⊆ A'`. These
functors define an adjoint triple `f_* ⊣ f⁻¹ ⊣ f_!`.

In Mathlib, `P A` is `Set A`, ordered by `⊆`. The direct image is
`Set.image f` (written `f '' s`), the inverse image is `Set.preimage f`
(written `f ⁻¹' t`), and `f_!` is `Set.kernImage f`, defined as
`{b | ∀ ⦃a⦄, f a = b → a ∈ s}`.

Exercise 5. Prove both Galois connections by working with elements, without
the library lemmas. A `GaloisConnection` is a statement `∀ s t, _ ↔ _`, so
begin with `intro s t` and `constructor`, which leaves one goal for each
direction of the `↔`. Each goal is an inclusion of sets, and an inclusion
`s ⊆ t` unfolds to `∀ x, x ∈ s → x ∈ t`, so it can be proved by introducing an
element. When the element belongs to an image `f '' s`, the pattern
`rintro _ ⟨a, ha, rfl⟩` introduces it in a usable form. An element of
`f '' s` is some `b` together with an `a`, a proof `ha : a ∈ s`, and a proof
that `f a = b`. The pattern names `a` and `ha`, and `rfl` replaces `b` by
`f a` everywhere. The library proofs of the two connections are
`Set.image_preimage` and `Set.preimage_kernImage`.
-/
section Image

-- first I want to nail down this f_! / Set.kernImage f, without
-- weird notation or an existing def.
abbrev f_scream {A B : Type*} (f : A → B) (A' : Set A): Set B :=
  { b : B | ∀ a : A, f a = b → a ∈ A'}
-- That is, it's the set of stuff in B only pointed to from A'.

-- So let f be the constant function from the terminal type * to the Nats (say),
-- sending *.unit to 0. The kernel image of f on * itself would be all the Nats.
-- The kernel image of its subset {} would be all the Nats except 0.
-- If f is the inclusion Fin 2 → Nat, f's kernel image on Fin 2 is all the nats.
-- f's kernel image on {0} is all the nats except 1.
-- f's kernel image on {} is all the nats except 1 and 0.

variable {A B : Type*} (f : A → B)

theorem gc_image_preimage : GaloisConnection (Set.image f) (Set.preimage f) := by
  intro sA sB
  constructor
  case mp =>
    intro h a ha
    simp at h
    simp
    exact h ha
  case mpr =>
    intro h1 b hb
    simp at hb
    obtain ⟨a, ha⟩ := hb
    have h2 := h1 ha.1
    simp at h2
    rw [← ha.2]
    exact h2

theorem gc_preimage_kernImage : GaloisConnection (Set.preimage f) (Set.kernImage f) := by
  intro sB sA
  constructor
  case mp =>
    intro h1
    unfold Set.kernImage
    unfold Set.preimage at h1
    intro b hb
    simp
    intro a ha
    apply h1
    simp
    rw [ha]
    exact hb
  case mpr =>
    intro h1
    unfold Set.kernImage at h1
    unfold Set.preimage
    intro a ha
    simp at ha
    have h2 := h1 ha
    simp at h2
    apply h2
    rfl

end Image


-- Example 4.1.9: Quantifiers
/-
Riehl: a predicate on `X` is a function `p : X → Ω`, where `Ω := {⊥, ⊤}` is the
set of truth values, ordered by implication. The set `Ω^X` of predicates on `X`
inherits the pointwise order: `p ≤ q` if and only if `p x` implies `q x` for
every `x`. Universal and existential quantification define functors
`∀_X, ∃_X : Ω^X ⥤ Ω`, and there is also a constant functor `Δ_X : Ω ⥤ Ω^X`.
These form an adjoint triple `∃_X ⊣ Δ_X ⊣ ∀_X`.

In Lean, `Ω` is `Prop`, whose order `p ≤ q` is implication `p → q`, and `Ω^X`
is `X → Prop` with the pointwise order. Both orders are defined so that they
unfold to the corresponding statements: for `p q : X → Prop`, the statement
`p ≤ q` is by definition `∀ x, p x → q x`. Because `intro` unfolds definitions
until it reaches a `∀` or an `→`, a proof of `p ≤ q` can begin with
`intro x hx`, which gives an element `x : X` and a proof `hx : p x`.

Exercise 6. Prove both Galois connections.
-/
section Quantifiers

variable (X : Type*)

theorem gc_exists_const :
    GaloisConnection (fun p : X → Prop => ∃ x, p x) (fun q _ => q) := by
  intro p b
  constructor
  · intro h
    simp at h
    simp
    intro x' qua
    exact h x' qua
  · simp
    intro h x' hx
    simp [LE.le] at h
    exact h x' hx

theorem gc_const_forall :
    GaloisConnection (fun (q : Prop) (_ : X) => q) (fun p => ∀ x, p x) := by
  intro p b
  constructor
  · simp [LE.le]
    intro h1 pp x
    exact h1 x pp
  · simp [LE.le]
    intro h1 x pp
    apply h1
    exact pp

-- you can compose them:
#check (gc_exists_const X).compose (gc_const_forall X)

end Quantifiers


-- Sidequest.

-- This isn't an exercise, but I want to prove adjunctions are transitive on
-- the basis of what we have so far, without resorting to .compose.

def adj_trans
    {F : 𝒞 ⥤ 𝒟}
    {G : 𝒟 ⥤ 𝒞}
    {H : 𝒟 ⥤ ℰ}
    {K : ℰ ⥤ 𝒟}
    (adjFG : F ⊣ G)
    (adjHK : H ⊣ K)
    : F ⋙ H ⊣ K ⋙ G := by
  -- Fix c ∈ 𝒞 and e ∈ ℰ and construct a bijection:
  -- ℰ((F ⋙ H) c, e) ≃ 𝒞(c, (K ⋙ G) e)
  let to_bij (c: 𝒞) (e: ℰ) : ((F ⋙ H).obj c ⟶ e) ≃ (c ⟶ (K ⋙ G).obj e) := by
    let φ := adjFG.homEquiv c (K.obj e)
    let ψ := adjHK.homEquiv (F.obj c) e
    convert! ψ.trans φ
  apply Adjunction.mkOfHomEquiv
  constructor
  case homEquiv =>
    exact to_bij
  -- The remaining naturality proofs are just noodling around
  -- with functoriality. Kind of boring.
  -- Still, notable that we don't need to appeal to the naturality
  -- of `adjFG` or of `adjHK`.
  case homEquiv_naturality_left_symm =>
    intro c c' e f g
    conv =>
      lhs
      unfold to_bij
      simp
    conv =>
      rhs
      unfold to_bij
      simp
      lhs
      change (F ⋙ H).map f
    -- you don't really need all this here, `convert!` closes
    simp only [Adjunction.homEquiv, Equiv.symm, Equiv.coe_fn_mk]
    simp only [Functor.comp_map, Functor.comp_obj]
    rw [Functor.map_comp]
    conv => rhs; rw [Functor.map_comp]; simp
    conv => lhs; simp
  case homEquiv_naturality_right =>
    intro c e e' f g
    unfold to_bij
    simp [Adjunction.homEquiv]


-- Exercises.

/-
## Exercise 4.1.ii

Riehl: define left and right adjoints to
  (i) `ob : Cat → Set` and
  (ii) `V : Quiver → Set`.
Does `V : Graph → Set` have a left or right adjoint?

### Part (i): `ob : Cat → Set`

The left adjoint of `ob` sends a set `X` to the discrete category on `X`, whose
only morphisms are identities, and the right adjoint sends `X` to the
codiscrete (or indiscrete) category on `X`, which has exactly one morphism
from any object to any other. A functor out of a discrete category is
determined by its action on objects, and so is a functor into a codiscrete
category. In both adjunctions, therefore, the functors in question correspond
exactly to functions between sets of objects.

In Mathlib, `ob` is the functor `Cat.objects`. The discrete category functor
is `typeToCat`, which sends `X` to the category `Discrete X`, and the
codiscrete category functor is `Codiscrete.functorToCat`, which sends `X` to
the category `Codiscrete X`. The exercises below take these three functors as
given. They ask for the bijections (4.1.2) and for proofs that the bijections
are natural, and these pieces are then assembled into adjunctions with
`Adjunction.mkOfHomEquiv`, as in Exercise 2c.

The two adjunctions are stated at different universe levels. For
`X : Type u`, the morphisms of `Discrete X` belong to `Type u`, so `typeToCat`
lands in `Cat.{u, u}`, while the morphisms of `Codiscrete X` belong to
`Type 0`, so
`Codiscrete.functorToCat` lands in `Cat.{0, u}`. Consequently, Riehl's adjoint
triple `discrete ⊣ ob ⊣ codiscrete` is stated here as two separate adjunctions,
with `ob` at a different universe level in each.

Two wrapper structures appear in what follows, and the first warm-ups
practise using them. A morphism `F : C ⟶ D` in `Cat` is not literally a
functor. It is a structure `Cat.Hom` whose single field is a functor
`F.toFunctor : C ⥤ D`. In the other direction, a functor `G : C ⥤ D` becomes a
morphism `G.toCatHom : Cat.of C ⟶ Cat.of D`. Two morphisms in `Cat` are equal
as soon as their underlying functors are equal, and the tactic `ext1` reduces
an equation between morphisms in `Cat` to an equation between their
underlying functors. Similarly, a morphism `X ⟶ Y` in `Type u` wraps a
function `X → Y`. A function `f : X → Y` becomes the morphism `↾f`, and a
morphism `X ⟶ Y` can be applied to an element `x : X` as though it were a
function.
-/
section Exercise_4_1_ii

universe u v

-- Warm-ups on morphisms in `Cat` and in `Type`.

example {C D : Cat.{v, u}} (F : C ⟶ D) : C ⥤ D := by
  sorry

example {C D : Type u} [Category.{v} C] [Category.{v} D] (G : C ⥤ D) :
    Cat.of C ⟶ Cat.of D := by
  sorry

example {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F.toFunctor = G.toFunctor) : F = G := by
  sorry

-- The function `ob F` sends an object `c` to `F c`.
example {C D : Cat.{v, u}} (F : C ⟶ D) (c : C) :
    Cat.objects.map F c = F.toFunctor.obj c := by
  sorry

example {X Y : Type u} (f : X → Y) (x : X) : (↾f) x = f x := by
  sorry

-- Two morphisms in `Type u` are equal if they agree on every element.
example {X Y : Type u} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  sorry

/-
Warm-ups on discrete categories. An object of `Discrete X` is a structure
`⟨x⟩` that wraps an element `x : X`, which the projection `.as` recovers. A
function `f : X → C` from `X` to the objects of a category `C` extends to a
functor `Discrete.functor f : Discrete X ⥤ C`, which sends `⟨x⟩` to `f x`. By
the lemma `Discrete.functor_ext`, two functors out of `Discrete X` are equal if
they agree on every object. Finally, for a function `f : X ⟶ Y`, the functor
`typeToCat.map f` sends `⟨x⟩` to `⟨f x⟩`.
-/

example {X : Type u} {C : Type*} [Category C] (f : X → C) (x : X) :
    (Discrete.functor f).obj ⟨x⟩ = f x := by
  sorry

example {X : Type u} {C : Type*} [Category C] (F G : Discrete X ⥤ C)
    (h : ∀ x, F.obj ⟨x⟩ = G.obj ⟨x⟩) : F = G := by
  sorry

example {X Y : Type u} (f : X ⟶ Y) (x : X) :
    (typeToCat.map f).toFunctor.obj ⟨x⟩ = ⟨f x⟩ := by
  sorry

/-
Warm-ups on codiscrete categories. As with `Discrete X`, an object of
`Codiscrete X` is a structure `⟨x⟩` that wraps an element `x : X`, which the
projection `.as` recovers. A function `f : C → X` from the objects of a
category `C` to `X` extends to a functor
`Codiscrete.functor f : C ⥤ Codiscrete X`, which sends `c` to `⟨f c⟩`.

Two functors into `Codiscrete X` that agree on every object are equal. Mathlib
has no lemma stating this fact, so the second warm-up below,
`codiscrete_functor_ext`, proves it. Start the proof with
`fapply CategoryTheory.Functor.ext`. (The bare name `Functor.ext` refers to an
unrelated lemma about the `Functor` type class.) This tactic leaves two goals.
The first asks that `F` and `G` agree on objects. The second asks that they
agree on morphisms, up to the `eqToHom` isomorphisms built from the equations
of the first goal. The second goal is wrapped in an `autoParam`, which
`intros` does not see through, so introduce its variables with
`intro c c' φ`. Then consider how many morphisms there are from one object of
`Codiscrete X` to another.
-/

example {C : Type*} [Category C] {X : Type*} (f : C → X) (c : C) :
    (Codiscrete.functor f).obj c = ⟨f c⟩ := by
  sorry

theorem codiscrete_functor_ext {C : Type*} [Category C] {X : Type*}
    (F G : C ⥤ Codiscrete X) (h : ∀ c, F.obj c = G.obj c) : F = G := by
  sorry

/-
Exercise 4.1.ii(i), left adjoint. The discrete category functor `typeToCat` is
left adjoint to `Cat.objects`. In the notation of Definition 4.1.1, the
bijection (4.1.2) is

  `Cat(Discrete X, C) ≅ Set(X, ob C)`.

Its two directions are named after Riehl's transposes, following the notation
introduced at the top of this file. The function `discFlat` sends a functor
`f` to its transpose `f♭`, which is the action of `f` on objects. The function
`discSharp` sends a function `g` to its transpose `g♯`, which is the functor
that `g` determines. The four theorems after these two definitions state that
`discFlat` and `discSharp` are inverse to each other and that they satisfy the
two naturality equations of `Adjunction.CoreHomEquiv`. The variables in the
naturality equations are named as in Exercises 2a and 2b.
-/

section DiscreteObjects

variable (X X' : Type u) (C C' : Cat.{u, u})

def discFlat (f : typeToCat.obj X ⟶ C) : X ⟶ Cat.objects.obj C :=
  sorry

def discSharp (g : X ⟶ Cat.objects.obj C) : typeToCat.obj X ⟶ C :=
  sorry

theorem discSharp_discFlat (f : typeToCat.obj X ⟶ C) :
    discSharp X C (discFlat X C f) = f := by
  sorry

theorem discFlat_discSharp (g : X ⟶ Cat.objects.obj C) :
    discFlat X C (discSharp X C g) = g := by
  sorry

variable {X X' C C'}

-- Naturality in the set `X`, the analogue of Exercise 2b.
theorem discSharp_comp (h : X ⟶ X') (g' : X' ⟶ Cat.objects.obj C) :
    discSharp X C (h ≫ g') = typeToCat.map h ≫ discSharp X' C g' := by
  sorry

-- Naturality in the category `C`, the analogue of Exercise 2a.
theorem discFlat_comp (f : typeToCat.obj X ⟶ C) (k : C ⟶ C') :
    discFlat X C' (f ≫ k) = discFlat X C f ≫ Cat.objects.map k := by
  sorry

def discreteObjectsAdj : typeToCat.{u} ⊣ Cat.objects.{u, u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X C :=
        { toFun := discFlat X C
          invFun := discSharp X C
          left_inv := discSharp_discFlat X C
          right_inv := discFlat_discSharp X C }
      homEquiv_naturality_left_symm := discSharp_comp
      homEquiv_naturality_right := discFlat_comp }

-- Mathlib's version of this adjunction.
#check Cat.typeToCatObjectsAdj

end DiscreteObjects

/-
Exercise 4.1.ii(i), right adjoint. The functor `Cat.objects` is left adjoint to
the codiscrete category functor `Codiscrete.functorToCat`. Here the bijection
(4.1.2) is

  `Set(ob C, X) ≅ Cat(C, Codiscrete X)`.

The function `codiscFlat` sends a function `f` from the objects of `C` to `X`
to the functor that `f` determines. The function `codiscSharp` sends a functor
`g` to the action of `g` on objects. In this adjunction `Cat.objects` is the
left adjoint, so in the naturality equation `codiscSharp_comp` the functor
applied to the morphism `h` is `Cat.objects`.
-/

section ObjectsCodiscrete

variable (C C' : Cat.{0, u}) (X X' : Type u)

def codiscFlat (f : Cat.objects.obj C ⟶ X) : C ⟶ Codiscrete.functorToCat.obj X :=
  sorry

def codiscSharp (g : C ⟶ Codiscrete.functorToCat.obj X) : Cat.objects.obj C ⟶ X :=
  sorry

theorem codiscSharp_codiscFlat (f : Cat.objects.obj C ⟶ X) :
    codiscSharp C X (codiscFlat C X f) = f := by
  sorry

theorem codiscFlat_codiscSharp (g : C ⟶ Codiscrete.functorToCat.obj X) :
    codiscFlat C X (codiscSharp C X g) = g := by
  sorry

variable {C C' X X'}

-- Naturality in the category `C`, the analogue of Exercise 2b.
theorem codiscSharp_comp (h : C ⟶ C') (g' : C' ⟶ Codiscrete.functorToCat.obj X) :
    codiscSharp C X (h ≫ g') = Cat.objects.map h ≫ codiscSharp C' X g' := by
  sorry

-- Naturality in the set `X`, the analogue of Exercise 2a.
theorem codiscFlat_comp (f : Cat.objects.obj C ⟶ X) (k : X ⟶ X') :
    codiscFlat C X' (f ≫ k) = codiscFlat C X f ≫ Codiscrete.functorToCat.map k := by
  sorry

def objectsCodiscreteAdj : Cat.objects.{0, u} ⊣ Codiscrete.functorToCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv C X :=
        { toFun := codiscFlat C X
          invFun := codiscSharp C X
          left_inv := codiscSharp_codiscFlat C X
          right_inv := codiscFlat_codiscSharp C X }
      homEquiv_naturality_left_symm := codiscSharp_comp
      homEquiv_naturality_right := codiscFlat_comp }

-- Mathlib's version of this adjunction.
#check Codiscrete.adj

end ObjectsCodiscrete

/-
### Part (ii): `V : Quiver → Set`

Riehl: a quiver consists of a set of vertices and a set of arrows, each arrow
having a source vertex and a target vertex, and a quiver homomorphism is a
function on vertices together with a function on arrows that preserves sources
and targets. The functor `V` sends a quiver to its set of vertices.

In Mathlib, a quiver structure on a type `Q` of vertices is an instance
`Quiver Q`, which supplies a type `a ⟶ b` of arrows for each pair of vertices
`a` and `b`. The category of quivers is `Quiv`. Unlike a morphism in `Cat`, a
morphism `F : Q ⟶ R` in `Quiv` is not wrapped in a structure: it is literally
a prefunctor `Q ⥤q R`. A prefunctor `F` consists of a function `F.obj` on
vertices and a function `F.map` on arrows, which sends an arrow `e : a ⟶ b` to
an arrow `F.map e : F.obj a ⟶ F.obj b`. A prefunctor `P : Q ⥤q R` between
types with quiver instances becomes a morphism
`P.toQuivHom : Quiv.of Q ⟶ Quiv.of R`. By the lemma `Prefunctor.ext`, two
prefunctors are equal if they agree on vertices and on arrows. After
`apply Prefunctor.ext`, the goal about arrows comes first and the goal about
vertices second. Mathlib does not define the functor `V`, so this file defines
it below as `quivVertices`.

The left adjoint of `V` should send a set `X` to the quiver whose vertices are
the elements of `X` and which has no arrows. Mathlib provides this quiver as
`Quiver.Empty X`, in which every type of arrows is `PEmpty`. The right adjoint
of `V` should also send `X` to a quiver whose vertices are the elements of
`X`. The type synonym `CodiscreteQuiver X` below carries that quiver, and
choosing its arrows is part of the exercise.

Unlike in part (i), the functors themselves are left to you, including their
`map_id` and `map_comp` fields. An arrow `e` in `Quiver.Empty X` has type
`PEmpty`, so the term `PEmpty.elim e` can be given any type, and in particular
it proves any goal.
-/

def quivVertices : Quiv.{v, u} ⥤ Type u where
  obj Q := Q
  map F := ↾F.obj

-- Warm-ups on quivers.

example {Q R : Quiv.{v, u}} (F : Q ⟶ R) (a : Q) : quivVertices.map F a = F.obj a := by
  sorry

example {X : Type u} {Q : Quiv.{u, u}} (F G : Quiv.of (Quiver.Empty X) ⟶ Q)
    (h : ∀ x, F.obj x = G.obj x) : F = G := by
  sorry

def CodiscreteQuiver (X : Type u) : Type u := X

instance (X : Type u) : Quiver.{v} (CodiscreteQuiver X) where
  Hom _ _ := sorry

def discreteQuiv : Type u ⥤ Quiv.{u, u} :=
  sorry

def codiscreteQuiv : Type u ⥤ Quiv.{v, u} :=
  sorry

def discreteQuivAdj : discreteQuiv.{u} ⊣ quivVertices.{u, u} :=
  sorry

def quivVerticesCodiscreteAdj : quivVertices.{u, v} ⊣ codiscreteQuiv.{u, v} :=
  sorry

/-
### The question about `Graph`

Riehl's `Graph` is the category of simple graphs. Its objects are sets of
vertices equipped with a symmetric adjacency relation under which no vertex is
adjacent to itself. Its morphisms are graph homomorphisms, which are functions
on vertices that carry adjacent vertices to adjacent vertices. Mathlib defines
the structure `SimpleGraph` but not this category, so answer the question in a
comment. Does `V : Graph → Set` have a left adjoint? Does it have a right
adjoint? For the right adjoint, suppose that `R X` is a candidate graph on a
set `X`. Ask which functions `V G → X` would then have to be graph
homomorphisms `G ⟶ R X`, and whether any graph `R X` can make all of them
homomorphisms.
-/

end Exercise_4_1_ii

/-
## Exercise 4.1.v

Riehl: use Lemma 4.1.3 to show that if `F : 𝒞 ⇄ 𝒟 : G` are adjoint functors,
with `F ⊣ G`, then the comma categories `F ↓ 𝒟` and `𝒞 ↓ G`, formed using `F`
and `G` and the identity functors on `𝒞` and `𝒟`, are isomorphic, via an
isomorphism that commutes with the forgetful functors to `𝒞 × 𝒟` defined in
Exercise 1.3.vi.

Riehl's Exercise 1.3.vi defines the comma category of a pair of functors with a
common codomain. Its objects are triples consisting of an object of each domain
and a morphism between their images, and a morphism from one triple to another
is a pair of morphisms making a square commute. Specialised to the two comma
categories of this exercise, the definition reads as follows.

- An object of `F ↓ 𝒟` is a triple `(c, d, f)` with `c : 𝒞`, `d : 𝒟` and
  `f : F.obj c ⟶ d`. A morphism from `(c, d, f)` to `(c', d', g)` is a pair
  `h : c ⟶ c'` and `k : d ⟶ d'` such that the square
  `CommSq f (F.map h) k g` commutes in `𝒟`.
- An object of `𝒞 ↓ G` is a triple `(c, d, f')` with `c : 𝒞`, `d : 𝒟` and
  `f' : c ⟶ G.obj d`. A morphism from `(c, d, f')` to `(c', d', g')` is a pair
  `h : c ⟶ c'` and `k : d ⟶ d'` such that the square
  `CommSq f' h (G.map k) g'` commutes in `𝒞`.

These are the two squares of the diagram (4.1.4), so the mathematical content of
the exercise is already in hand. The bijections (4.1.2) match the objects of the
two categories, and Lemma 4.1.3 says that a pair `(h, k)` is a morphism in one
category exactly when it is a morphism between the transposed objects in the
other.

[Diagram](assets/transposed_squares.svg)

Exercises 1a and 1b proved the two directions of Lemma 4.1.3 for an adjunction,
under the names `transposed_square_of_square` and
`square_of_transposed_square`.

In Mathlib, the comma category of `L : A ⥤ T` and `R : B ⥤ T` is `Comma L R`, so
`F ↓ 𝒟` is `Comma F (𝟭 𝒟)` and `𝒞 ↓ G` is `Comma (𝟭 𝒞) G`. An object `X` of
`Comma L R` is a structure with fields `X.left : A`, `X.right : B` and
`X.hom : L.obj X.left ⟶ R.obj X.right`, and it can be written `⟨c, d, f⟩`. A
morphism `φ : X ⟶ Y` is a structure with fields `φ.left`, `φ.right` and `φ.w`,
where `φ.w` is the equation `L.map φ.left ≫ Y.hom = X.hom ≫ R.map φ.right`.

Two small mismatches with the squares above need attention. First, the equation
`φ.w` runs in the opposite direction to the field `w` of a `CommSq`, which is
`top ≫ right = left ≫ bottom`. Passing between them therefore takes a `.symm`.
Second, the identity functors do not disappear by themselves: the type of `X.hom`
in `Comma F (𝟭 𝒟)` is literally `F.obj X.left ⟶ (𝟭 𝒟).obj X.right`, and `φ.w`
mentions `(𝟭 𝒟).map φ.right`. These terms are definitionally equal to
`X.right` and `φ.right`, so `exact` and `refine` accept them, but `rw` and `simp`
match syntactically and may not. For the same reason, the statements below write
`adj.homEquiv X.left X.right X.hom` in full. The notation `X.hom ♭[adj]` would
infer its objects from the type of `X.hom` and pick up a `(𝟭 𝒟).obj`, and `rw`
would then fail to match that term against a clean one. The infoview still prints
the full form as `X.hom ♭[adj]`.

Riehl's statement that the categories are isomorphic is stated in Exercise 4.1.v(e)
with Mathlib's structure `IsoCat`, which packages a pair of functors whose two
composites are equal to identity functors. It cannot be stated as an isomorphism in
`Cat`, because `Comma F (𝟭 𝒟)` lies in `Type (max u₁ u₂ v₂)` and `Comma (𝟭 𝒞) G`
lies in `Type (max u₁ u₂ v₁)`, so that the two categories are not objects of a
single `Cat` unless `v₁` and `v₂` agree. The structure `IsoCat` avoids this problem,
because `IsoCat C D` is defined for any two categories `C` and `D`, whatever their
universes.
-/
section Exercise_4_1_v

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞}

-- Warm-ups on objects of comma categories.

example (c : 𝒞) (d : 𝒟) (f : F.obj c ⟶ d) : (⟨c, d, f⟩ : Comma F (𝟭 𝒟)).left = c := by
  rfl

example (c : 𝒞) (d : 𝒟) (f : F.obj c ⟶ d) : (⟨c, d, f⟩ : Comma F (𝟭 𝒟)).hom = f := by
  rfl

example (c : 𝒞) (d : 𝒟) (f' : c ⟶ G.obj d) : (⟨c, d, f'⟩ : Comma (𝟭 𝒞) G).hom = f' := by
  rfl

example (X : Comma F (𝟭 𝒟)) : (⟨X.left, X.right, X.hom⟩ : Comma F (𝟭 𝒟)) = X := by
  rfl

-- Two objects with the same `left` and `right` are equal if their morphisms are.
example (c : 𝒞) (d : 𝒟) (f f₂ : F.obj c ⟶ d) (w : f = f₂) :
    (⟨c, d, f⟩ : Comma F (𝟭 𝒟)) = ⟨c, d, f₂⟩ := by
  simp
  exact w

/-
Warm-ups on morphisms of comma categories. The first two say that a morphism of
each comma category is a commutative square, and they are the place to practise
the `.symm` described above. In the infoview, shift-click the goal and choose
"CommSq diagram" to compare the square with the one in (4.1.4).
-/

example {X Y : Comma F (𝟭 𝒟)} (φ : X ⟶ Y) : CommSq X.hom (F.map φ.left) φ.right Y.hom := by
  let cs : CommSq _ _ _ _ := ⟨φ.w.symm⟩
  exact cs

example {X Y : Comma (𝟭 𝒞) G} (φ : X ⟶ Y) : CommSq X.hom φ.left (G.map φ.right) Y.hom := by
  let cs : CommSq _ _ _ _ := ⟨φ.w.symm⟩
  exact cs

/-
Conversely, a commutative square is a morphism of each comma category. The names
follow Exercises 1a and 1b, and `f'` and `g'` play the roles of the transposes of
`f` and `g`. Each definition can be given with the `where` syntax, by supplying
the fields `left`, `right` and `w`.
-/

def leftCommaHom {c c' : 𝒞} {d d' : 𝒟} {f : F.obj c ⟶ d} {g : F.obj c' ⟶ d'}
    (h : c ⟶ c') (k : d ⟶ d') (sq : CommSq f (F.map h) k g) :
    (⟨c, d, f⟩ : Comma F (𝟭 𝒟)) ⟶ ⟨c', d', g⟩ := by
  refine ⟨h, k, ?_⟩
  simp
  exact sq.flip.w

def rightCommaHom {c c' : 𝒞} {d d' : 𝒟} {f' : c ⟶ G.obj d} {g' : c' ⟶ G.obj d'}
    (h : c ⟶ c') (k : d ⟶ d') (sq : CommSq f' h (G.map k) g') :
    (⟨c, d, f'⟩ : Comma (𝟭 𝒞) G) ⟶ ⟨c', d', g'⟩ := by
  refine ⟨h, k, ?_⟩
  simp
  exact sq.flip.w

/-- Generalization -/
def commaSqHom
    {F: 𝒞 ⥤ ℰ}
    {G: 𝒟 ⥤ ℰ}
    {c c' : 𝒞}
    {d d' : 𝒟}
    {f : F.obj c ⟶ G.obj d}
    {g : F.obj c' ⟶ G.obj d'}
    {h : c ⟶ c'}
    {k : d ⟶ d'}
    (sq : CommSq f (F.map h) (G.map k) g)
    : (⟨c, d, f⟩ : Comma F G) ⟶ ⟨c', d', g⟩ := by
  exact ⟨h, k, sq.flip.w⟩



/-
Two morphisms of a comma category are equal if their `left` and `right` components
are equal, which is the lemma `Comma.hom_ext`. The tactic `ext` applies it and
leaves one goal for each component. Identities and composites are computed
componentwise.
-/

example {X Y : Comma F (𝟭 𝒟)} (φ ψ : X ⟶ Y) (hl : φ.left = ψ.left) (hr : φ.right = ψ.right) :
    φ = ψ := by
  ext
  · exact hl
  · exact hr

example {X Y Z : Comma F (𝟭 𝒟)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).left = φ.left ≫ ψ.left := by
  simp

example (X : Comma F (𝟭 𝒟)) : (𝟙 X : X ⟶ X).right = 𝟙 X.right := by
  simp

/-
Warm-ups on `eqToHom`, which appears in the second goal of
`CategoryTheory.Functor.ext`, as in the warm-up `codiscrete_functor_ext` of
Exercise 4.1.ii. Given an equation `w : X = Y` between objects, `eqToHom w` is the
corresponding morphism `X ⟶ Y`. The components of an `eqToHom` in a comma
category are again `eqToHom`s, by the simp lemmas `Comma.eqToHom_left` and
`Comma.eqToHom_right`.

If the two sides of `w` are definitionally equal, then `eqToHom w` is
definitionally equal to an identity morphism. In the second example below, `simp`
can see this because the two sides of `w` are syntactically the same, but the
point of the example is that `exact Category.id_comp p` also works. It is the
`exact` that continues to work when the two sides of `w` are equal only by
unfolding definitions.
-/

example {X Y : Comma F (𝟭 𝒟)} (w : X = Y) :
    (eqToHom w).left = eqToHom (congrArg Comma.left w) := by
  simp

example {a b : 𝒞} (w : a = a) (p : a ⟶ b) : eqToHom w ≫ p = p := by
  exact Category.id_comp p

/-
Exercise 4.1.v(a). Lemma 4.1.3 applied to the morphisms of the comma categories.
Here `transposed_comma_square` is `transposed_square_of_square` with `c := X.left`,
`c' := Y.left`, `d := X.right`, `d' := Y.right`, `h := φ.left`, `k := φ.right`,
`f := X.hom` and `g := Y.hom`.

In `untransposed_comma_square` the objects `X` and `Y` lie in `𝒞 ↓ G`, so `X.hom`
and `Y.hom` play the roles of the transposes `f♭` and `g♭`, and the `f` and `g` of
`square_of_transposed_square` are their inverse transposes. After applying that
lemma, the hypothesis it asks for contains a transpose of an inverse transpose,
which `Equiv.apply_symm_apply` removes.
-/

theorem transposed_comma_square (adj : F ⊣ G) {X Y : Comma F (𝟭 𝒟)} (φ : X ⟶ Y) :
    CommSq (adj.homEquiv X.left X.right X.hom) φ.left (G.map φ.right)
      (adj.homEquiv Y.left Y.right Y.hom) := by
  -- I don't want to waste time mucking with our dumb version, here's
  -- mathlib's
  exact (CommSq.mk φ.w.symm).right_adjoint adj

theorem untransposed_comma_square (adj : F ⊣ G) {X Y : Comma (𝟭 𝒞) G} (φ : X ⟶ Y) :
    CommSq ((adj.homEquiv X.left X.right).symm X.hom) (F.map φ.left) φ.right
      ((adj.homEquiv Y.left Y.right).symm Y.hom) := by
  exact (CommSq.mk φ.w.symm).left_adjoint adj

/-
Exercise 4.1.v(b). The two functors. The functor `commaTranspose adj` sends
`(c, d, f)` to `(c, d, f♭)`, and it sends a morphism `(h, k)` to the same pair
`(h, k)`, now regarded as a morphism between the transposed objects. The functor
`commaTransposeInv adj` does the same with the inverse transposes.

Use the `where` syntax with the fields `obj` and `map`. For `obj`, write the
transpose as `adj.homEquiv X.left X.right X.hom`, as explained above, and similarly
for the inverse transpose. For `map`, use `rightCommaHom` and `leftCommaHom` with
the results of Exercise 4.1.v(a). The fields `map_id` and `map_comp` can be omitted,
since their default tactic proves them.
-/

def commaTranspose (adj : F ⊣ G) : Comma F (𝟭 𝒟) ⥤ Comma (𝟭 𝒞) G  where
  obj cF1 := ⟨cF1.left, cF1.right, cF1.hom♭[adj]⟩
  map Φ := commaSqHom (transposed_comma_square adj Φ)

def commaTransposeInv (adj : F ⊣ G) : Comma (𝟭 𝒞) G ⥤ Comma F (𝟭 𝒟) where
  obj c1G := ⟨c1G.left, c1G.right, c1G.hom♯[adj]⟩
  map Φ := commaSqHom (untransposed_comma_square adj Φ)

/-
Exercise 4.1.v(c). The two functors are inverse to each other. Start each proof
with `fapply CategoryTheory.Functor.ext`, which leaves a goal about objects and
then a goal about morphisms.

The goal about objects follows from `Equiv.symm_apply_apply` or
`Equiv.apply_symm_apply`, and `simp [commaTranspose, commaTransposeInv]` closes it.

The goal about morphisms needs more care, and the order of the steps matters.
Introduce the variables with `intro X Y φ`, and use `ext` to reduce to one goal for
each component.

Each of these goals needs two calls to `simp`, and they must come in this order.
First call plain `simp`, with no arguments and without unfolding anything. You do not
need to name any lemma here, since `simp` already knows the ones it needs. Among
them are `Comma.eqToHom_left` and `Comma.eqToHom_right`, which turn each
`(eqToHom _).left` or `(eqToHom _).right` into an `eqToHom` in `𝒞` or `𝒟`. Then
unfold the definitions with `simp [commaTranspose, commaTransposeInv, commaSqHom]`,
adding `leftCommaHom` or `rightCommaHom` if your functors are defined with them. If
you unfold first, the plain `simp` lemmas above no longer fire, and the goal is stuck
with terms of the form `(eqToHom _).left`.

The goal that remains has the form `φ.left = eqToHom _ ≫ φ.left`
or the same with `right`. Here the two sides of the equation inside `eqToHom`
are definitionally equal but not syntactically so, which is the situation of the
second `eqToHom` warm-up: `simp` cannot remove it, but
`exact (Category.id_comp _).symm` closes the goal.
-/

theorem commaTranspose_comp_inv (adj : F ⊣ G) :
    commaTranspose adj ⋙ commaTransposeInv adj = 𝟭 _ := by
  fapply CategoryTheory.Functor.ext
  case h_obj =>
    intro X
    simp [commaTranspose, commaTransposeInv]
  case h_map =>
    intro X Y φ
    ext
    · simp [commaTranspose, commaTransposeInv]
      unfold eqToHom
      simp
      rfl
    · simp [commaTranspose, commaTransposeInv]
      unfold eqToHom
      simp
      rfl

theorem commaTransposeInv_comp (adj : F ⊣ G) :
    commaTransposeInv adj ⋙ commaTranspose adj = 𝟭 _ := by
  fapply CategoryTheory.Functor.ext
  case h_obj =>
    simp [commaTranspose, commaTransposeInv]
  case h_map =>
    intro X Y φ
    ext
    · simp [commaTranspose, commaTransposeInv]
      unfold eqToHom
      simp
      rfl
    · simp [commaTranspose, commaTransposeInv]
      unfold eqToHom
      simp
      rfl

/-
Exercise 4.1.v(d). The isomorphism commutes with the forgetful functors to
`𝒞 × 𝒟`. The projection functors `dom` and `cod` of Exercise 1.3.vi are
`Comma.fst` and `Comma.snd` in Mathlib, and the forgetful functor to the product
is their pairing, formed with `Functor.prod'`. It sends `(c, d, f)` to the pair
`(c, d)` and a morphism to the pair `(h, k)`.

Neither `commaTranspose` nor `commaTransposeInv` changes `c`, `d`, `h` or `k`, so
both sides of each equation below are built from the same data, and the proof
should need very little.
-/

abbrev commaForget (F: 𝒞 ⥤ ℰ) (G: 𝒟 ⥤ ℰ) : Comma F G ⥤ 𝒞 × 𝒟 :=
  (Comma.fst F G).prod' (Comma.snd F G)

  -- abbrev leftForget (F : 𝒞 ⥤ 𝒟) : Comma F (𝟭 𝒟) ⥤ 𝒞 × 𝒟 :=
  --   (Comma.fst F (𝟭 𝒟)).prod' (Comma.snd F (𝟭 𝒟))

  -- abbrev rightForget (G : 𝒟 ⥤ 𝒞) : Comma (𝟭 𝒞) G ⥤ 𝒞 × 𝒟 :=
  --   (Comma.fst (𝟭 𝒞) G).prod' (Comma.snd (𝟭 𝒞) G)

theorem commaTranspose_forget (adj : F ⊣ G) :
    commaTranspose adj ⋙ commaForget (𝟭 𝒞) G = commaForget F (𝟭 𝒟) := by
  fapply CategoryTheory.Functor.ext
  case h_obj =>
    simp [commaTranspose]
  case h_map =>
    intro X Y φ
    simp [commaTranspose]
    exact ⟨rfl, rfl⟩

theorem commaTransposeInv_forget (adj : F ⊣ G) :
    commaTransposeInv adj ⋙ commaForget F (𝟭 𝒟) = commaForget (𝟭 𝒞) G := by
  fapply CategoryTheory.Functor.ext
  case h_obj =>
    simp [commaTransposeInv]
  case h_map =>
    intro X Y φ
    simp [commaTransposeInv]
    exact ⟨rfl, rfl⟩

/-
Exercise 4.1.v(e). Riehl asks for an isomorphism of categories, which is a functor
with a strict two-sided inverse. The two composites must be equal to identity
functors, and it is not enough for them to be naturally isomorphic to identity
functors. Exercise 4.1.v(c) proved these two equations for `commaTranspose adj` and
`commaTransposeInv adj`, but as two separate theorems. This exercise assembles the
functors and the theorems into a single term that expresses Riehl's claim directly.

Mathlib's name for an isomorphism of categories is `IsoCat`. For categories `C` and
`D`, a term `e : IsoCat C D` is a structure with four fields:

- `e.functor : C ⥤ D` is the forward functor.
- `e.inverse : D ⥤ C` is the inverse functor.
- `e.unit_eq : 𝟭 C = e.functor ⋙ e.inverse` says that the composite on `C` is the
  identity functor.
- `e.counit_eq : e.inverse ⋙ e.functor = 𝟭 D` says that the composite on `D` is the
  identity functor.

The two equations are not oriented alike. The identity functor stands on the left of
`unit_eq` and on the right of `counit_eq`.

The structure `IsoCat C D` should be distinguished from an equivalence of categories
`C ≌ D`. The composites of an equivalence are only naturally isomorphic to identity
functors, whereas the composites of an `IsoCat` are equal to identity functors.
Isomorphism is therefore the stricter notion.

The three warm-ups below use `IsoCat` by itself, before any comma category appears.

The first warm-up constructs the identity isomorphism on `𝒞`. The composite
`𝟭 𝒞 ⋙ 𝟭 𝒞` is definitionally equal to `𝟭 𝒞`, so prove each of the two equations
with `rfl`.
-/

example : IsoCat 𝒞 𝒞 where
  functor := 𝟭 𝒞
  inverse := 𝟭 𝒞
  unit_eq := sorry
  counit_eq := sorry

/-
The second warm-up extracts an equation between objects from `unit_eq`. This requires
a Mathlib lemma that has not appeared in this file. If `h : H = K` is an equation
between functors and `x` is an object, then `Functor.congr_obj h x` is the equation
`H.obj x = K.obj x`. Apply `Functor.congr_obj` to `e.unit_eq` and `c`. The result is
the equation `(𝟭 𝒞).obj c = e.inverse.obj (e.functor.obj c)`, which is the goal with
its two sides exchanged, so finish with `.symm`.
-/

example (e : IsoCat 𝒞 𝒟) (c : 𝒞) : e.inverse.obj (e.functor.obj c) = c := by
  sorry

/-
The third warm-up introduces `IsoCat.objEquiv`. Every isomorphism of categories
restricts to a bijection between the objects of the two categories, and for
`e : IsoCat C D` this bijection is the term `e.objEquiv : C ≃ D`. Its forward function
is `e.functor.obj` and its inverse function is `e.inverse.obj`. The statement below
records the first of these facts, which holds by definition, so prove it with `rfl`.
-/

example (e : IsoCat 𝒞 𝒟) (c : 𝒞) : e.objEquiv c = e.functor.obj c := by
  sorry

/-
The next definition is the isomorphism that Riehl asks for. Replace `:= sorry` with
the `where` syntax and supply the four fields of `IsoCat` as follows:

- For `functor`, use `commaTranspose adj`.
- For `inverse`, use `commaTransposeInv adj`.
- For `unit_eq`, use `(commaTranspose_comp_inv adj).symm`. The `.symm` is needed
  because `commaTranspose_comp_inv` has the identity functor on the right, whereas
  `unit_eq` has the identity functor on the left.
- For `counit_eq`, use `commaTransposeInv_comp adj`, which already has the required
  orientation.
-/

def commaIsoCat (adj : F ⊣ G) : IsoCat (Comma F (𝟭 𝒟)) (Comma (𝟭 𝒞) G) :=
  sorry

/-
Riehl also requires the isomorphism to commute with the forgetful functors to
`𝒞 × 𝒟`, and the three theorems below address this requirement.

The theorem `commaIsoCat_forget` states the requirement for the forward functor of
`commaIsoCat adj`. Prove `commaIsoCat_forget` with `exact commaTranspose_forget adj`.
Lean accepts this term because `(commaIsoCat adj).functor` unfolds to
`commaTranspose adj`.

Exercise 4.1.v(d) proved a corresponding equation for the inverse functor, namely
`commaTransposeInv_forget`, by a separate argument. That separate argument was not
necessary, because an isomorphism of categories that commutes with two functors in
the forward direction also commutes with them in the inverse direction. The theorem
`inverse_forget_of_functor_forget` states this fact for an arbitrary `IsoCat`, with no
mention of comma categories. Prove `inverse_forget_of_functor_forget` by rewriting
the goal in four steps, in this order:

1. Use `rw [← h]` to replace `P` by `e.functor ⋙ Q`.
2. Use `rw [← Functor.assoc]` to regroup the goal, so that the composite
   `e.inverse ⋙ e.functor` appears.
3. Use `rw [e.counit_eq]` to replace that composite by the identity functor.
4. Use `rw [Functor.id_comp]` to remove the identity functor. The lemma
   `Functor.id_comp` states that composing a functor with an identity functor on the
   left leaves that functor unchanged. After this step, `rw` closes the goal.

The theorem `commaIsoCat_inverse_forget` is the special case for comma categories.
Prove `commaIsoCat_inverse_forget` by applying `inverse_forget_of_functor_forget` to
`commaIsoCat adj` and `commaIsoCat_forget adj`. This proof does not use
`commaTransposeInv_forget`.
-/

theorem commaIsoCat_forget (adj : F ⊣ G) :
    (commaIsoCat adj).functor ⋙ commaForget (𝟭 𝒞) G = commaForget F (𝟭 𝒟) := by
  sorry

theorem inverse_forget_of_functor_forget (e : IsoCat 𝒞 𝒟) {P : 𝒞 ⥤ ℰ} {Q : 𝒟 ⥤ ℰ}
    (h : e.functor ⋙ Q = P) : e.inverse ⋙ P = Q := by
  sorry

theorem commaIsoCat_inverse_forget (adj : F ⊣ G) :
    (commaIsoCat adj).inverse ⋙ commaForget F (𝟭 𝒟) = commaForget (𝟭 𝒞) G := by
  sorry

/-
The last three statements collect consequences of having a single term
`commaIsoCat adj`, and each statement has a one-line proof.

The theorem `commaIsoCat_objEquiv` says that the bijection on objects induced by
`commaIsoCat adj` sends a triple `(c, d, f)` to the triple whose third component is
the transpose of `f`. The isomorphism of categories therefore recovers the bijection
(4.1.2). Prove `commaIsoCat_objEquiv` with `rfl`.

The first example uses `Functor.IsIso`, a Mathlib class that has not appeared in this
file. For a functor `H : C ⥤ D`, the proposition `H.IsIso` says that `H` is full,
faithful and bijective on objects, which is the characterization of the functors that
underlie an isomorphism of categories. Mathlib registers the instance
`IsoCat.isIso_functor`, which provides `e.functor.IsIso` for every `e : IsoCat C D`.
Prove the first example with `infer_instance`.

The second example uses `IsoCat.toEquivalence`, which is also new to this file. For
`e : IsoCat C D`, the term `e.toEquivalence : C ≌ D` is the equivalence underlying
the isomorphism. Prove the second example by applying `IsoCat.toEquivalence` to
`commaIsoCat adj`.
-/

theorem commaIsoCat_objEquiv (adj : F ⊣ G) (X : Comma F (𝟭 𝒟)) :
    (commaIsoCat adj).objEquiv X = ⟨X.left, X.right, adj.homEquiv X.left X.right X.hom⟩ := by
  sorry

example (adj : F ⊣ G) : (commaIsoCat adj).functor.IsIso := by
  sorry

example (adj : F ⊣ G) : Comma F (𝟭 𝒟) ≌ Comma (𝟭 𝒞) G :=
  sorry

end Exercise_4_1_v
