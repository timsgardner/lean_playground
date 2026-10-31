/-
# Riehl, *Category Theory in Context*, §4.1: Adjoint functors
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Set.Lattice.Image
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
-- see `diagram_tools` for the available presenters.
show_panel_widgets [local ProofWidgets.SelectionPanel]

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]

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

Mathlib's version is `CommSq.right_adjoint`, stated for an adjunction `G ⊣ F`
with the letters exchanged.
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
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
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
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

end Quantifiers
