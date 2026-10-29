/-
# Riehl, *Category Theory in Context*, §4.1: Adjoint functors
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Set.Lattice.Image
import LeanPlayground.Scratch.category_kindergarten.common_tools

open CategoryTheory Opposite
open scoped CategoryKindergarten

-- set_option pp.categoryTheory.hideConcreteHom true
-- set_option pp.proofs true          -- print proof terms instead of ⋯
set_option pp.deepTerms true       -- don't elide deeply nested subterms
set_option linter.unusedTactic false

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
  then its transpose `g♯` is `(adj.homEquiv c d).symm g`.

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
  h_sharp : sharp = (adj.homEquiv c d).symm flat
  h_flat : flat = adj.homEquiv c d sharp

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
    flat := adj.homEquiv c d sharp,
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
    sharp := (adj.homEquiv c d).symm flat
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
`adj.homEquiv c d f ≫ G.map k`. Mathlib calls this
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
    adj.homEquiv c d' (f ≫ k) = adj.homEquiv c d f ≫ G.map k :=
  adj.homEquiv_naturality_right f k

/-
Naturality in `𝒞`. Riehl: for any `h : c' ⟶ c`, the transpose of
`f♯ · F h : F c' ⟶ d` is the composite of `h : c' ⟶ c` with `f♭ : c ⟶ G d`.
In Lean, `f♯ · F h` is `F.map h ≫ f` and its transpose is
`h ≫ adj.homEquiv c d f`. Mathlib calls this
`Adjunction.homEquiv_naturality_left`.
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d : 𝒟}
    (h : c' ⟶ c) (f : F.obj c ⟶ d) :
    adj.homEquiv c' d (F.map h ≫ f) = h ≫ adj.homEquiv c d f :=
  adj.homEquiv_naturality_left h f

/-
The four naturality equations. For `adj : F ⊣ G`, Mathlib states naturality in
each variable twice, once for the bijection `adj.homEquiv` and once for its
inverse. Writing `f` for a morphism `F c ⟶ d` playing the role of `f♯`, and `g`
for a morphism `c ⟶ G d` playing the role of `g♭`, they are:

* `adj.homEquiv_naturality_left h f`: the transpose of `f♯ · F h` is `f♭ · h`,
  that is, `adj.homEquiv c' d (F.map h ≫ f) = h ≫ adj.homEquiv c d f`.
* `adj.homEquiv_naturality_right f k`: the transpose of `k · f♯` is `G k · f♭`,
  that is, `adj.homEquiv c d' (f ≫ k) = adj.homEquiv c d f ≫ G.map k`.
* `adj.homEquiv_naturality_left_symm h g`: the transpose of `g♭ · h` is
  `g♯ · F h`, that is,
  `(adj.homEquiv c' d).symm (h ≫ g) = F.map h ≫ (adj.homEquiv c d).symm g`.
* `adj.homEquiv_naturality_right_symm g k`: the transpose of `G k · g♭` is
  `k · g♯`, that is,
  `(adj.homEquiv c d').symm (g ≫ G.map k) = (adj.homEquiv c d).symm g ≫ k`.

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
`k` on the right, and `g` on the bottom, so it commutes when
`f ≫ k = F.map h ≫ g`. The transposed square in `𝒞` has `f♭` on top, `h` on
the left, `G.map k` on the right, and `g♭` on the bottom, so it commutes when
`f♭ ≫ G.map k = h ≫ g♭`.

[Diagram](assets/transposed_squares.svg)

Riehl leaves the proof as Exercise 4.1.i. Exercise 1 proves the forward
direction: if the bijections are natural, then the squares correspond. Exercise
2 proves the converse. Mathlib states the forward direction as
`Adjunction.homEquiv_naturality_left_square_iff`, but the point here is to
derive it from the two naturality equations.
-/

/-
Exercise 1a. If the square in `𝒟` commutes, then so does the transposed square
in `𝒞`. Rewrite the composites `f♭ ≫ G.map k` and `h ≫ g♭` as transposes of
composites in `𝒟`, using the two naturality lemmas from right to left.
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (w : f ≫ k = F.map h ≫ g) :
    adj.homEquiv c d f ≫ G.map k = h ≫ adj.homEquiv c' d' g := by
  have h2 := adj.homEquiv_naturality_right f k
  have h3 := adj.homEquiv_naturality_left h g
  rw [← h2, ← h3, w]

/-
Exercise 1b. Conversely, if the transposed square in `𝒞` commutes, then so does
the square in `𝒟`. Both sides of the goal are morphisms `F.obj c ⟶ d'`, so it
suffices to show that their transposes agree. Begin with
`apply (adj.homEquiv c d').injective`.
-/
example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (w : adj.homEquiv c d f ≫ G.map k = h ≫ adj.homEquiv c' d' g) :
    f ≫ k = F.map h ≫ g := by
  apply (adj.homEquiv c d').injective
  calc
    (adj.homEquiv c d') (f ≫ k) = (adj.homEquiv c d) f ≫ G.map k := by exact adj.homEquiv_naturality_right f k
    _ = h ≫ (adj.homEquiv c' d') g := by exact w
    _ = (adj.homEquiv c d') (F.map h ≫ g) := by exact (adj.homEquiv_naturality_left h g).symm

/-
Exercise 2. The converse half of Lemma 4.1.3. In this section, `e` is a family
of bijections `e c d : (F.obj c ⟶ d) ≃ (c ⟶ G.obj d)` about which nothing is
assumed except the hypothesis `hsq`: for every configuration (4.1.4), the square
in `𝒟` commutes if and only if the transposed square in `𝒞` commutes. The task
is to show that `e` is natural in both variables, and hence defines an
adjunction.

The idea in both parts is to choose a square in which one side is an identity.
For naturality in `𝒟` (4a), take `h := 𝟙 c` and `g := f ≫ k`. The square in
`𝒟` then commutes for trivial reasons, so `hsq` makes the transposed square
commute, and that square is the naturality equation up to an identity. For
naturality in `𝒞` (4b), take `k := 𝟙 d` and work from the `𝒞` side instead.

To use `hsq`, write `have := (hsq h k f g).mp ?_` (or `.mpr`) with the
morphisms you have chosen, and prove the trivial square with `simp`.
-/
section Squares

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
  (hsq : ∀ {c c' : 𝒞} {d d' : 𝒟} (h : c ⟶ c') (k : d ⟶ d')
    (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d'),
    f ≫ k = F.map h ≫ g ↔ e c d f ≫ G.map k = h ≫ e c' d' g)
include hsq

-- Exercise 2a: naturality in `𝒟`, the field `homEquiv_naturality_right`.
theorem nat_right_of_squares {c : 𝒞} {d d' : 𝒟} (f : F.obj c ⟶ d) (k : d ⟶ d') :
    e c d' (f ≫ k) = e c d f ≫ G.map k := by
  sorry

-- Exercise 2b: naturality in `𝒞` for the inverse, the field
-- `homEquiv_naturality_left_symm`.
theorem nat_left_symm_of_squares {c' c : 𝒞} {d : 𝒟} (h : c' ⟶ c) (g : c ⟶ G.obj d) :
    (e c' d).symm (h ≫ g) = F.map h ≫ (e c d).symm g := by
  sorry

/-
Exercise 2c. Assemble an adjunction from `e`, using `Adjunction.mkOfHomEquiv`
and a `CoreHomEquiv` whose three fields are `e` and the results of 2a and 2b.
-/
def adjOfSquares : F ⊣ G :=
  sorry

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

(P) Warm-ups on preorder categories. `homOfLE h` (or `h.hom`) turns
`h : x ≤ y` into a morphism `x ⟶ y`, and `leOfHom f` (or `f.le`) turns a
morphism `f : x ⟶ y` back into `x ≤ y`. Any two morphisms `x ⟶ y` are equal,
because a proposition has at most one proof; the instance is
`CategoryTheory.Preorder.subsingleton_hom`, and `Subsingleton.elim` uses it.
-/
section Preorders

variable {X : Type*} [Preorder X]

example {x y : X} (h : x ≤ y) : x ⟶ y := by
  sorry

example {x y : X} (f : x ⟶ y) : x ≤ y := by
  sorry

example {x y : X} (f g : x ⟶ y) : f = g := by
  sorry

example {l : X → X} (hl : Monotone l) (x : X) : hl.functor.obj x = l x := by
  sorry

end Preorders

/-
Exercise 3. A Galois connection is an adjunction in the sense of Definition
4.1.1. Build the adjunction with `Adjunction.mkOfHomEquiv`. You only need to
supply the field `homEquiv`, a bijection `(l x ⟶ y) ≃ (x ⟶ u y)` for each `x`
and `y`: its two directions come from `gc.le_u` and `gc.l_le`, and its two
round-trip conditions hold because all morphisms with the same domain and
codomain are equal. Leave out both naturality fields. Their default proof
`cat_disch` closes them on its own, which is the Lean form of the observation
that every diagram in a preorder commutes, so naturality is automatic.

Mathlib's version is `GaloisConnection.adjunction`.
-/
example {X Y : Type*} [Preorder X] [Preorder Y] {l : X → Y} {u : Y → X}
    (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  sorry


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
  sorry

theorem gc_ceil_cast : GaloisConnection Int.ceil ((↑) : ℤ → α) := by
  sorry

/-
The inclusion appears in both Galois connections, once as a lower adjoint and
once as an upper adjoint, so it is turned into a functor twice, from two
different proofs that the cast is monotone. Since any two proofs of a
proposition are equal by definition, the two functors are equal by `rfl`, and
the two adjunctions below really do share their middle functor.
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
the library lemmas. After `intro` and `constructor`, each direction unfolds to a
statement about membership; `rintro _ ⟨a, ha, rfl⟩` is a convenient way to
introduce an element of an image. (The library versions are
`Set.image_preimage` and `Set.preimage_kernImage`, both in the namespace
`GaloisConnection`.)
-/
section Image

variable {A B : Type*} (f : A → B)

theorem gc_image_preimage : GaloisConnection (Set.image f) (Set.preimage f) := by
  sorry

theorem gc_preimage_kernImage : GaloisConnection (Set.preimage f) (Set.kernImage f) := by
  sorry

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
is `X → Prop` with the pointwise order. Both orders unfold by definition, so
`intro` sees through them: a proof of `p ≤ q` for `p q : X → Prop` can begin
with `intro x hx`.

Exercise 6. Prove both Galois connections.
-/
section Quantifiers

variable (X : Type*)

theorem gc_exists_const :
    GaloisConnection (fun p : X → Prop => ∃ x, p x) (fun q _ => q) := by
  sorry

theorem gc_const_forall :
    GaloisConnection (fun (q : Prop) (_ : X) => q) (fun p => ∀ x, p x) := by
  sorry

end Quantifiers
