import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import LeanPlayground.Scratch.category_kindergarten.common_tools

/-!
# Polynomial functors, W-types, and their algebras

This file lays out the polynomial-tree story using mathlib's own API from the
start, instead of rebuilding it by hand.

## The picture

There are four pieces, each of which mathlib already provides.

1. **Signature.** A `P : PFunctor` has
   - `P.A`, the *shapes* a node can have, and
   - `P.B a`, the *child positions* of a node with shape `a`.

2. **Layer.** Applying `P` to a type `X` gives `P X`, defined as
   `Σ a : P.A, P.B a → X`. A value `⟨a, children⟩ : P X` is one node: a shape
   plus one `X` in each child position. Nothing says what is inside the `X`s.

3. **Functor.** `X ↦ P X` is an endofunctor of `Type`. Its action on a
   function `f : X → Y` is `P.map f`, which keeps the shape and applies `f` to
   every child. `CategoryTheory.ofTypeFunctor` packages it as `Type ⥤ Type`.

4. **Algebras.** An algebra of that functor is a carrier `A` with a structure
   map `str : P A → A`. It says how to turn one node whose children are
   already `A`s into an `A`.

Trees enter as one particular algebra:

5. **W-type.** `P.W` is the type of finite trees whose nodes are layers of
   `P`. Its constructor `PFunctor.W.mk : P P.W → P.W` takes one node whose
   children are trees and makes it the root of a bigger tree. The pair
   `(P.W, W.mk)` is an algebra, and it is the **initial** one: for every
   algebra `A` there is exactly one algebra morphism `P.W → A`, and it is the
   fold `WType.elim`.

Mathlib provides 1 through 5 as data, but not the statement that `(P.W, W.mk)`
is initial. Proving that is the main job of this file.

## Mathlib names

| idea                       | mathlib                                 |
|----------------------------|-----------------------------------------|
| signature                  | `PFunctor`                              |
| shapes / positions         | `P.A` / `P.B`                           |
| one layer over `X`         | `P X` (that is, `P.Obj X`)              |
| map over children          | `P.map`                                 |
| endofunctor of `Type`      | `ofTypeFunctor P.Obj`                   |
| algebra                    | `Endofunctor.Algebra F`                 |
| trees                      | `P.W` (that is, `WType P.B`)            |
| build a tree from a layer  | `PFunctor.W.mk` (`WType.ofSigma`)       |
| split a tree into a layer  | `PFunctor.W.dest` (`WType.toSigma`)     |
| fold                       | `WType.elim`                            |
| Lambek's lemma             | `Endofunctor.Algebra.Initial.str_isIso` |
| substitution `P (Q X)`     | `PFunctor.comp`                         |

The last section, `WhyPolynomial`, explains the name: `P X` is literally a
polynomial `Σ_a X ^ (P.B a)` in `X`.
-/

namespace PolynomialFunctorsAndWTypes

open CategoryTheory
open CategoryTheory.Endofunctor
open scoped CategoryKindergarten

namespace PolyAlgebra

/-!
## The endofunctor

All polynomial functors here live in `Type`, so we fix the universes of
`P.A` and `P.B` to `0`.
-/

/-- The endofunctor `X ↦ P X` of `Type`.

Mathlib already has a `Functor` instance and a `LawfulFunctor` instance for
`P.Obj`. `ofTypeFunctor` turns that into a categorical functor, so we do not
have to prove the functor laws ourselves. -/
abbrev functor (P : PFunctor.{0, 0}) : Type ⥤ Type :=
  ofTypeFunctor P.Obj

/-- The functor sends `X` to the layer type `P X`. -/
example (P : PFunctor.{0, 0}) (X : Type) :
    (functor P).obj X = P X := rfl

/-- On a function `f`, the functor maps `f` over the children of a layer and
leaves its shape alone. -/
theorem functor_map_apply (P : PFunctor.{0, 0}) {X Y : Type}
    (f : X ⟶ Y) (layer : P X) :
    (functor P).map f layer = P.map f layer := rfl


/-!
## Trees as an algebra

`W.mk` takes one layer whose children are whole trees and makes it the root of
a new tree. That is a structure map `P P.W → P.W`, so trees form an algebra.
It does not compute anything: it only remembers the node. That is why it is
often called the *syntax* algebra.
-/

/-- The algebra of trees: carrier `P.W`, structure map `W.mk`. -/
def wAlgebra (P : PFunctor.{0, 0}) : Algebra (functor P) where
  a := P.W
  str := TypeCat.ofHom PFunctor.W.mk


/-!
## Folding

`WType.elim` is mathlib's fold. Given the structure map of an algebra, it
folds every child first and then applies the structure map at the root. We
give it a name in terms of algebras.
-/

/-- Fold a tree into the carrier of any algebra. -/
def fold (P : PFunctor.{0, 0}) (A : Algebra (functor P)) :
    P.W → A.a :=
  WType.elim A.a (fun layer : P A.a => A.str layer)

/-- The defining equation of the fold: fold the children, then apply `A.str`
at the root. -/
@[simp]
theorem fold_mk (P : PFunctor.{0, 0}) (A : Algebra (functor P))
    (layer : P P.W) :
    fold P A (PFunctor.W.mk layer) = A.str (P.map (fold P A) layer) := by
  rcases layer with ⟨shape, children⟩
  rfl


/-!
## Initiality

Existence: the fold is an algebra morphism `wAlgebra P ⟶ A`. The morphism
condition is the equation `fold_mk`.

Uniqueness: any algebra morphism `f : wAlgebra P ⟶ A` satisfies the same
equation, so by induction on trees it agrees with the fold.
-/

/-- The fold, packaged as an algebra morphism out of the tree algebra. -/
def foldHom (P : PFunctor.{0, 0}) (A : Algebra (functor P)) :
    wAlgebra P ⟶ A where
  f := TypeCat.ofHom (fold P A)
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    rcases layer with ⟨shape, children⟩
    rfl

/-- Every algebra morphism out of the tree algebra is the fold. -/
theorem hom_eq_foldHom (P : PFunctor.{0, 0}) (A : Algebra (functor P))
    (f : wAlgebra P ⟶ A) :
    f = foldHom P A := by
  apply Algebra.ext
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext tree
  change f.f tree = fold P A tree
  induction tree with
  | mk shape children ih =>
      -- The morphism law of `f` at this node:
      --   A.str ⟨shape, f ∘ children⟩ = f (mk shape children).
      have h := congrArg
        (fun g : P P.W ⟶ A.a => g ⟨shape, children⟩)
        f.h
      change A.str ⟨shape, fun p => f.f (children p)⟩ =
          f.f (WType.mk shape children) at h
      -- By induction, `f` agrees with the fold on every child.
      have hchildren :
          (fun p => f.f (children p)) = (fun p => fold P A (children p)) := by
        funext p
        exact ih p
      rw [hchildren] at h
      exact h.symm

/-- The tree algebra is the initial algebra of the polynomial functor. -/
def wAlgebraIsInitial (P : PFunctor.{0, 0}) :
    Limits.IsInitial (wAlgebra P) :=
  Limits.IsInitial.ofUniqueHom (foldHom P) (hom_eq_foldHom P)


/-!
## Consequences of initiality

**Fusion.** If `h : A ⟶ B` is an algebra morphism, then `h ∘ fold A` and
`fold B` are both algebra morphisms out of `wAlgebra P` into `B`. There is
only one such morphism, so they are equal. In practice, "fold, then
post-process" can be rewritten as a single fold.

**Lambek's lemma.** The structure map of an initial algebra is an
isomorphism. For trees, this says every tree is `W.mk` of exactly one layer.
Mathlib's `W.dest` is the inverse.
-/

/-- Fold fusion, as an equation of algebra morphisms. -/
theorem foldHom_comp (P : PFunctor.{0, 0}) {A B : Algebra (functor P)}
    (h : A ⟶ B) :
    foldHom P A ≫ h = foldHom P B :=
  hom_eq_foldHom P B _

/-- Fold fusion, as an equation of values. -/
theorem fold_fusion (P : PFunctor.{0, 0}) {A B : Algebra (functor P)}
    (h : A ⟶ B) (tree : P.W) :
    h.f (fold P A tree) = fold P B tree :=
  congrArg (fun g : wAlgebra P ⟶ B => g.f tree) (foldHom_comp P h)

/-- Lambek's lemma, obtained purely from initiality. -/
theorem mk_isIso (P : PFunctor.{0, 0}) :
    IsIso (wAlgebra P).str :=
  Algebra.Initial.str_isIso (wAlgebraIsInitial P)

/-- For trees, the inverse that Lambek's lemma promises is `W.dest`. -/
def mkIso (P : PFunctor.{0, 0}) : P P.W ≅ P.W where
  hom := TypeCat.ofHom PFunctor.W.mk
  inv := TypeCat.ofHom PFunctor.W.dest
  hom_inv_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    exact PFunctor.W.dest_mk layer
  inv_hom_id := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext tree
    exact PFunctor.W.mk_dest tree


/-!
## Induction from initiality

`hom_eq_foldHom` used Lean's `induction` to prove that the tree algebra is
initial. The converse also holds: initiality alone proves the induction
principle. So the two carry the same information, and "initial algebra" is a
way of saying "type with structural induction" without mentioning
constructors.

The argument, for an initial algebra `I` and a predicate `Q` on its carrier:

1. The elements that satisfy `Q` form an algebra `subalgebra Q`. Its structure
   map applies `I.str` and uses the induction step to show that the result
   still satisfies `Q`. This is the only place the step is used.
2. Forgetting the proofs, `Subtype.val : subalgebra Q ⟶ I`, is an algebra
   morphism.
3. Folding into `subalgebra Q` and then forgetting gives an algebra morphism
   `I ⟶ I`. `I` is initial, so this is `𝟙 I`, because an initial object has only
   one endomorphism.
4. So every `x` is the underlying element of `fold x : {x // Q x}`, and that
   element satisfies `Q`.

The theorem is stated for *any* initial algebra of `functor P`, not only for
`wAlgebra P`, so the proof cannot quietly use the inductive definition of
`P.W`.
-/

/-- If `Q` is closed under the structure map of `I`, the elements satisfying
`Q` form an algebra. -/
def subalgebra (P : PFunctor.{0, 0}) (I : Algebra (functor P)) (Q : I.a → Prop)
    (step : ∀ (shape : P.A) (children : P.B shape → I.a),
      (∀ p, Q (children p)) → Q (I.str ⟨shape, children⟩)) :
    Algebra (functor P) where
  a := {x : I.a // Q x}
  str := TypeCat.ofHom fun layer =>
    ⟨I.str (P.map Subtype.val layer),
      step layer.1 (fun p => (layer.2 p).1) (fun p => (layer.2 p).2)⟩

/-- Forgetting the proofs is an algebra morphism `subalgebra ⟶ I`. -/
def subalgebraVal (P : PFunctor.{0, 0}) (I : Algebra (functor P))
    (Q : I.a → Prop)
    (step : ∀ (shape : P.A) (children : P.B shape → I.a),
      (∀ p, Q (children p)) → Q (I.str ⟨shape, children⟩)) :
    subalgebra P I Q step ⟶ I where
  f := TypeCat.ofHom Subtype.val
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    rfl

/-- Induction for any initial algebra of a polynomial functor, proved from
initiality alone. -/
theorem induction_of_isInitial {P : PFunctor.{0, 0}} {I : Algebra (functor P)}
    (hI : Limits.IsInitial I) (Q : I.a → Prop)
    (step : ∀ (shape : P.A) (children : P.B shape → I.a),
      (∀ p, Q (children p)) → Q (I.str ⟨shape, children⟩))
    (x : I.a) : Q x := by
  let S := subalgebra P I Q step
  -- Fold into the subalgebra, then forget: an endomorphism of `I`, so `𝟙 I`.
  have hid : hI.to S ≫ subalgebraVal P I Q step = 𝟙 I := hI.hom_ext _ _
  -- At `x`, that says the fold of `x` has underlying element `x`.
  have hx : ((hI.to S).f x).1 = x :=
    congrArg (fun g : I ⟶ I => g.f x) hid
  exact hx ▸ ((hI.to S).f x).2

/-- Structural induction on trees, as a special case.

This goes through `wAlgebraIsInitial`, which was itself proved by induction,
so it is not a new proof that `P.W` has induction. What it shows is that
initiality is enough to get induction back. -/
theorem w_induction (P : PFunctor.{0, 0}) (Q : P.W → Prop)
    (step : ∀ (shape : P.A) (children : P.B shape → P.W),
      (∀ p, Q (children p)) → Q (PFunctor.W.mk ⟨shape, children⟩))
    (tree : P.W) : Q tree :=
  induction_of_isInitial (wAlgebraIsInitial P) Q step tree

end PolyAlgebra


/-!
## Example: binary trees

Leaves carry a `Leaf` payload and have no children. Branches carry a `Branch`
payload and have two children.
-/

namespace BinaryTreeExample

/-- The two kinds of node, with their payloads. -/
inductive Shape (Leaf Branch : Type) where
  | leaf (payload : Leaf)
  | branch (payload : Branch)

/-- The signature of binary trees. A leaf has no child positions (`Empty`),
and a branch has two (`Fin 2`). -/
def pfunctor (Leaf Branch : Type) : PFunctor.{0, 0} where
  A := Shape Leaf Branch
  B
    | .leaf _ => Empty
    | .branch _ => Fin 2

/-- Binary trees are the W-type of this signature. -/
abbrev Tree (Leaf Branch : Type) := (pfunctor Leaf Branch).W

variable {Leaf Branch : Type}

/-- A leaf: shape `.leaf payload`, and no children to supply. -/
def leaf (payload : Leaf) : Tree Leaf Branch :=
  WType.mk (Shape.leaf payload) (fun p => nomatch p)

/-- A branch: shape `.branch payload`, and a tree in each of the positions
`0` and `1`. -/
def branch (payload : Branch) (lhs rhs : Tree Leaf Branch) :
    Tree Leaf Branch :=
  WType.mk (Shape.branch payload) ![lhs, rhs]

/-- Build an algebra from what to do at a leaf and what to do at a branch.

At a branch, `children 0` and `children 1` are the already-computed results
for the left and right subtrees. -/
def algebra {C : Type} (onLeaf : Leaf → C) (onBranch : Branch → C → C → C) :
    Algebra (PolyAlgebra.functor (pfunctor Leaf Branch)) where
  a := C
  str := TypeCat.ofHom fun
    | ⟨.leaf payload, _⟩ => onLeaf payload
    | ⟨.branch payload, children⟩ =>
        onBranch payload (children (0 : Fin 2)) (children (1 : Fin 2))

/-- Count the leaves. -/
def leafCount (Leaf Branch : Type) :
    Algebra (PolyAlgebra.functor (pfunctor Leaf Branch)) :=
  algebra (fun _ => 1) (fun _ l r => l + r)

/-- Render a tree as a string. -/
def render (Leaf Branch : Type) [ToString Leaf] [ToString Branch] :
    Algebra (PolyAlgebra.functor (pfunctor Leaf Branch)) :=
  algebra (fun l => toString l)
    (fun b l r => s!"({b} {l} {r})")

/-- The example tree `branch "A" (leaf 0) (leaf 1)`. -/
def example1 : Tree Nat String :=
  branch "A" (leaf 0) (leaf 1)

-- The carrier `(leafCount Nat String).a` is `Nat`, but only after unfolding,
-- so we state the equation at type `Nat` explicitly.
example : @Eq Nat (PolyAlgebra.fold _ (leafCount Nat String) example1) 2 := rfl

example : PolyAlgebra.fold _ (render Nat String) example1 = "(A 0 1)" := rfl

/-- Folding with `W.mk` itself rebuilds the tree: the tree algebra's fold is
the identity. This follows from uniqueness, with no induction. -/
example (tree : Tree Nat String) :
    PolyAlgebra.fold _ (PolyAlgebra.wAlgebra _) tree = tree := by
  have h := PolyAlgebra.hom_eq_foldHom _ (PolyAlgebra.wAlgebra (pfunctor Nat String))
    (𝟙 _)
  exact (congrArg (fun g => g.f tree) h).symm

/-- The number of leaves, as a `Nat`. (The carrier of `leafCount` is `Nat`
only after unfolding, so we name the fold at type `Nat`.) -/
def numLeaves (tree : Tree Leaf Branch) : Nat :=
  PolyAlgebra.fold _ (leafCount Leaf Branch) tree

/-- Every tree has at least one leaf, proved with `w_induction`. The step
looks at one node, whose children are already known to satisfy the claim. -/
theorem one_le_numLeaves (tree : Tree Leaf Branch) : 1 ≤ numLeaves tree := by
  refine PolyAlgebra.w_induction _ (fun t => 1 ≤ numLeaves t) ?_ tree
  intro shape children ih
  unfold numLeaves
  rw [PolyAlgebra.fold_mk]
  cases shape with
  | leaf payload => exact le_refl 1
  | branch payload => exact Nat.le_add_right_of_le (ih (0 : Fin 2))

end BinaryTreeExample


/-!
## Example: the natural numbers

`ℕ` is the W-type of the polynomial `1 + X`. There are two shapes: `zero`, with
no positions, and `succ`, with one. A tree for this signature is a chain
`succ (succ (… zero))`.

An algebra for `1 + X` is a carrier with a point and a step map. A fold sends
`n` to `stepⁿ(point)`, which is primitive iteration.

The plan:

1. Make Lean's own `ℕ` an algebra, `natAlgebra`, with point `0` and step
   `Nat.succ`.
2. Show it is initial by transporting `wAlgebraIsInitial` along an algebra
   isomorphism `wAlgebra pfunctor ≅ natAlgebra`.
3. Read off Peano's axioms from initiality alone:
   - **induction**, from `induction_of_isInitial`;
   - **`succ` is injective** and **`0 ≠ succ n`**, from Lambek's lemma
     (`1 + ℕ ≅ ℕ`).

These facts are of course already true of `Nat`. The point is that they all
follow from the single universal property, so "initial algebra of `1 + X`" is
a complete description of the natural numbers.

Step 2 is not free. Proving that `toNat` and `ofNat` are inverse uses Lean's
recursion and induction on `Nat` once, to connect `Nat` to the W-type. After
that, step 3 uses only `natIsInitial`.
-/

namespace NatExample

/-- The two kinds of node. -/
inductive Shape where
  | zero
  | succ

/-- The signature `1 + X`: `zero` has no child positions, and `succ` has one. -/
def pfunctor : PFunctor.{0, 0} where
  A := Shape
  B
    | .zero => Empty
    | .succ => Unit

/-- Build a `(1 + X)`-algebra from a point and a step. -/
def algebra {C : Type} (zero : C) (succ : C → C) :
    Algebra (PolyAlgebra.functor pfunctor) where
  a := C
  str := TypeCat.ofHom fun
    | ⟨.zero, _⟩ => zero
    | ⟨.succ, children⟩ => succ (children ())

/-- Lean's natural numbers, as an algebra. -/
def natAlgebra : Algebra (PolyAlgebra.functor pfunctor) :=
  algebra (0 : Nat) Nat.succ

/-- Fold a `1 + X` tree into `ℕ`. -/
def toNat (tree : pfunctor.W) : Nat :=
  PolyAlgebra.fold _ natAlgebra tree

/-- Build the `1 + X` tree with `n` successors. -/
def ofNat : Nat → pfunctor.W
  | 0 => WType.mk Shape.zero (fun p => nomatch p)
  | n + 1 => WType.mk Shape.succ (fun _ => ofNat n)

/-- Uses induction on `Nat`. This is the one place we rely on it. -/
theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

/-- Uses `w_induction`. -/
theorem ofNat_toNat (tree : pfunctor.W) : ofNat (toNat tree) = tree := by
  refine PolyAlgebra.w_induction _ (fun t => ofNat (toNat t) = t) ?_ tree
  intro shape children ih
  cases shape with
  | zero => exact congrArg (WType.mk Shape.zero) (funext fun p => nomatch p)
  | succ => exact congrArg (WType.mk Shape.succ) (funext fun u => ih u)

/-- The tree algebra and `natAlgebra` are isomorphic algebras. The forward
map is `toNat`, which is the fold, so it is an algebra morphism. -/
def wAlgebraIsoNat : PolyAlgebra.wAlgebra pfunctor ≅ natAlgebra :=
  Algebra.isoMk
    (Equiv.toIso
      { toFun := toNat
        invFun := ofNat
        left_inv := ofNat_toNat
        right_inv := toNat_ofNat })
    (by
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      funext layer
      rcases layer with ⟨shape | shape, children⟩ <;> rfl)

/-- `(ℕ, 0, succ)` is the initial `(1 + X)`-algebra. -/
def natIsInitial : Limits.IsInitial natAlgebra :=
  Limits.IsInitial.ofIso (PolyAlgebra.wAlgebraIsInitial pfunctor) wAlgebraIsoNat


/-!
### Peano's axioms from initiality

From here on, everything uses only `natIsInitial`.
-/

/-- Induction on `ℕ`, from initiality. The `zero` shape has no children, so
its case needs no hypothesis. The `succ` shape has one child `n`, so its case
is `Q n → Q (n + 1)`. -/
theorem nat_induction (Q : Nat → Prop) (zero : Q 0)
    (succ : ∀ n, Q n → Q (n + 1)) (n : Nat) : Q n := by
  refine PolyAlgebra.induction_of_isInitial natIsInitial Q ?_ n
  intro shape children ih
  cases shape with
  | zero => exact zero
  | succ => exact succ (children ()) (ih ())

/-- Lambek's lemma for `ℕ`: the structure map `1 + ℕ → ℕ` is a bijection. -/
theorem natAlgebra_str_bijective :
    Function.Bijective natAlgebra.str :=
  (isIso_iff_bijective _).mp (Algebra.Initial.str_isIso natIsInitial)

/-- `succ` is injective: two `succ` layers with the same image are the same
layer, so their children agree. -/
theorem succ_injective : Function.Injective Nat.succ := by
  intro a b h
  have hlayer :
      (⟨Shape.succ, fun _ => a⟩ : pfunctor Nat) = ⟨Shape.succ, fun _ => b⟩ :=
    natAlgebra_str_bijective.1 h
  exact congrFun (eq_of_heq (Sigma.mk.inj hlayer).2) ()

/-- `0 ≠ succ n`: a `zero` layer and a `succ` layer have different shapes, so
they cannot have the same image. -/
theorem zero_ne_succ (n : Nat) : 0 ≠ n + 1 := by
  intro h
  have hlayer :
      (⟨Shape.zero, fun p => nomatch p⟩ : pfunctor Nat) =
        ⟨Shape.succ, fun _ => n⟩ :=
    natAlgebra_str_bijective.1 h
  exact Shape.noConfusion (congrArg Sigma.fst hlayer)

/-- Recursion on `ℕ`: from a point and a step in any type, the fold gives a
function out of `ℕ`. It is the unique algebra morphism, and the morphism
condition is the pair of equations below. -/
def natRec {C : Type} (zero : C) (succ : C → C) : Nat → C :=
  (natIsInitial.to (algebra zero succ)).f

/-- The morphism condition at a `zero` layer. -/
theorem natRec_zero {C : Type} (zero : C) (succ : C → C) :
    natRec zero succ 0 = zero :=
  congrArg (fun g => g ⟨Shape.zero, fun p => nomatch p⟩)
    (natIsInitial.to (algebra zero succ)).h.symm

/-- The morphism condition at a `succ` layer. -/
theorem natRec_succ {C : Type} (zero : C) (succ : C → C) (n : Nat) :
    natRec zero succ (n + 1) = succ (natRec zero succ n) :=
  congrArg (fun g => g ⟨Shape.succ, fun _ => n⟩)
    (natIsInitial.to (algebra zero succ)).h.symm

example : natRec (0 : Nat) (· + 2) 5 = 10 := rfl

end NatExample


/-!
## Example: lists, and `foldl` as a fold

Lists of `Elem` are the W-type of `1 + Elem · X`. There are two kinds of node:
`nil`, with no positions, and `cons head`, with one position for the tail.

An algebra for `1 + Elem · X` is a carrier `C` with a value for `nil` and a
map `Elem → C → C` for `cons`. The fold processes the tail first and then
combines it with the head, so the fold of a list is `foldr`:

    fold [x₁, x₂, x₃]  =  cons x₁ (cons x₂ (cons x₃ nil)).

### Why `foldl` does not fit directly

`foldl f z [x₁, x₂, x₃] = f (f (f z x₁) x₂) x₃`. It threads an accumulator
from the head towards the tail. At a `cons` node, the fold hands us the
already-computed result for the tail, but `foldl` cannot compute the tail
until it knows the accumulator coming in from the left. With carrier `C`,
the information flows the wrong way.

### The trick: fold into functions

Use the carrier `C → C` instead. The result for a list is "what `foldl` will
do with whatever accumulator it is given":

- `nil` leaves the accumulator alone: `id`.
- `cons head` receives the tail's function `rest`. Given an accumulator
  `acc`, it first takes `f acc head` and then passes that on to `rest`.

Folding builds this function, and applying it to `z` runs `foldl`. The fold
itself still goes tail-first, as every fold does. What it builds is a chain
of continuations that runs head-first once it is given `z`.
-/

namespace ListExample

/-- The two kinds of node. A `cons` node carries its head as payload. -/
inductive Shape (Elem : Type) where
  | nil
  | cons (head : Elem)

/-- The signature `1 + Elem · X`: `nil` has no child positions, and
`cons head` has one, for the tail. -/
def pfunctor (Elem : Type) : PFunctor.{0, 0} where
  A := Shape Elem
  B
    | .nil => Empty
    | .cons _ => Unit

/-- Lists, as the W-type of this signature. -/
abbrev WList (Elem : Type) := (pfunctor Elem).W

variable {Elem : Type}

/-- The empty list. -/
def nil : WList Elem :=
  WType.mk Shape.nil (fun p => nomatch p)

/-- Put `head` in front of `tail`. -/
def cons (head : Elem) (tail : WList Elem) : WList Elem :=
  WType.mk (Shape.cons head) (fun _ => tail)

/-- Build a `(1 + Elem · X)`-algebra from a value for `nil` and a step for
`cons`. At a `cons` node, `children ()` is the already-computed result for
the tail. -/
def algebra {C : Type} (onNil : C) (onCons : Elem → C → C) :
    Algebra (PolyAlgebra.functor (pfunctor Elem)) where
  a := C
  str := TypeCat.ofHom fun
    | ⟨.nil, _⟩ => onNil
    | ⟨.cons head, children⟩ => onCons head (children ())

/-- The fold of a list algebra is `foldr`. (The carrier of `algebra` is `C`
only after unfolding, so we name the fold at type `C`.) -/
def foldr {C : Type} (onNil : C) (onCons : Elem → C → C)
    (xs : WList Elem) : C :=
  PolyAlgebra.fold _ (algebra onNil onCons) xs

theorem foldr_nil {C : Type} (onNil : C) (onCons : Elem → C → C) :
    foldr onNil onCons (nil : WList Elem) = onNil := rfl

theorem foldr_cons {C : Type} (onNil : C) (onCons : Elem → C → C)
    (head : Elem) (tail : WList Elem) :
    foldr onNil onCons (cons head tail) =
      onCons head (foldr onNil onCons tail) := rfl

/-- Convert to Lean's `List`, by folding into the `List` algebra. -/
def toList (xs : WList Elem) : List Elem :=
  foldr [] List.cons xs

/-- `foldl`, as a fold into the carrier `C → C`. -/
def foldl {C : Type} (f : C → Elem → C) (init : C) (xs : WList Elem) : C :=
  foldr (C := C → C) id (fun head rest acc => rest (f acc head)) xs init

/-- At `nil`, the accumulator comes out unchanged. -/
theorem foldl_nil {C : Type} (f : C → Elem → C) (init : C) :
    foldl f init (nil : WList Elem) = init := rfl

/-- At `cons`, the head goes into the accumulator *before* the tail is
processed. This is the `foldl` equation, even though the fold underneath
handled the tail first. -/
theorem foldl_cons {C : Type} (f : C → Elem → C) (init : C)
    (head : Elem) (tail : WList Elem) :
    foldl f init (cons head tail) = foldl f (f init head) tail := rfl

/-- The rigged fold agrees with `List.foldl`.

The carrier is a function type, so the claim must hold for *every* starting
accumulator. The induction hypothesis for the tail is then used at the new
accumulator `f init head`. -/
theorem foldl_eq_list_foldl {C : Type} (f : C → Elem → C) (xs : WList Elem) :
    ∀ init, foldl f init xs = (toList xs).foldl f init := by
  refine PolyAlgebra.w_induction _
    (fun t => ∀ init, foldl f init t = (toList t).foldl f init) ?_ xs
  intro shape children ih init
  cases shape with
  | nil => rfl
  | cons head => exact ih () (f init head)

/-- The list `[1, 2, 3]`. -/
def example1 : WList Nat :=
  cons 1 (cons 2 (cons 3 nil))

example : toList example1 = [1, 2, 3] := rfl

-- Reading digits: `foldl` meets `1` first, `foldr` meets `3` first.
example : foldl (fun acc x => 10 * acc + x) 0 example1 = 123 := rfl
example : foldr 0 (fun x acc => 10 * acc + x) example1 = 321 := rfl

-- Consing onto the accumulator reverses the list.
example : foldl (fun acc x => x :: acc) [] example1 = [3, 2, 1] := rfl

end ListExample


/-!
## Why "polynomial"?

A layer is `P X = Σ a : P.A, (P.B a → X)`. Read the pieces arithmetically:

- `Σ a : P.A, ...` is a sum with one term per shape;
- a function type `P.B a → X` is the power `X ^ (P.B a)`, because choosing an
  `X` for each of `n` positions is choosing an element of `X × ⋯ × X`.

So

    P X  =  Σ_{a : P.A} X ^ (P.B a),

which is a polynomial in `X` with one monomial for each shape. Shapes that
have the same positions combine into a coefficient. For example, binary trees
have `Leaf` shapes with no positions and `Branch` shapes with two positions,
so their layer is

    Leaf · X⁰ + Branch · X²  =  Leaf + Branch · X².

Lists (`ListExample`) have `1 + Elem · X`.

This section makes that reading precise in four ways.

1. **Building blocks.** Constants, monomials, sums and products of polynomials
   are operations on signatures. In each case the layer of the result is the
   matching operation on layer types (`⊕` for `+`, `×` for `·`).
2. **Substitution.** Mathlib's `PFunctor.comp` substitutes one polynomial
   into another: `(P.comp Q) X ≃ P (Q X)`.
3. **The binary-tree signature is `Leaf + Branch · X²`.** Its layer is
   equivalent to `Leaf ⊕ Branch × X × X`, compatibly with `map`.
4. **Counting evaluates the polynomial.** When everything is finite,
   `card (P X) = Σ_a (card X) ^ (card (P.B a))`.
-/

namespace WhyPolynomial

/-!
### Building blocks
-/

/-- The monomial `C · X ^ N`: one shape for each `c : C`, and every shape has
the same positions `N`. -/
def monomial (C N : Type) : PFunctor.{0, 0} where
  A := C
  B := fun _ => N

/-- A layer of `C · X ^ N` is a coefficient `c : C` together with an `X` for
each position, that is, an element of `C × (N → X)`. -/
def monomialEquiv (C N X : Type) : monomial C N X ≃ C × (N → X) where
  toFun layer := (layer.1, layer.2)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The constant polynomial `C`, that is, `C · X⁰`. -/
abbrev const (C : Type) : PFunctor.{0, 0} := monomial C Empty

/-- The variable `X`, that is, `1 · X¹`. -/
abbrev var : PFunctor.{0, 0} := monomial Unit Unit

/-- `X⁰ = 1`: a layer of the constant polynomial is just its coefficient. -/
def constEquiv (C X : Type) : const C X ≃ C where
  toFun layer := layer.1
  invFun c := ⟨c, fun p => nomatch p⟩
  left_inv layer := by
    rcases layer with ⟨c, children⟩
    exact Sigma.ext rfl (heq_of_eq (funext fun p => nomatch p))
  right_inv _ := rfl

/-- `1 · X¹ = X`: a layer of the variable is a single child. -/
def varEquiv (X : Type) : var X ≃ X where
  toFun layer := layer.2 ()
  invFun x := ⟨(), fun _ => x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sum of two polynomials: a shape is a shape of `P` or a shape of `Q`,
and it keeps its own positions. -/
def sum (P Q : PFunctor.{0, 0}) : PFunctor.{0, 0} where
  A := P.A ⊕ Q.A
  B := Sum.elim P.B Q.B

/-- The product of two polynomials: a shape is a pair of shapes, and its
positions are those of the left factor *or* those of the right factor.

The sum of positions is where `X ^ m · X ^ n = X ^ (m + n)` comes from. -/
def prod (P Q : PFunctor.{0, 0}) : PFunctor.{0, 0} where
  A := P.A × Q.A
  B := fun shapes => P.B shapes.1 ⊕ Q.B shapes.2

instance : Add PFunctor.{0, 0} := ⟨sum⟩
instance : Mul PFunctor.{0, 0} := ⟨prod⟩

/-- `(P + Q) X = P X + Q X`. -/
def sumEquiv (P Q : PFunctor.{0, 0}) (X : Type) :
    (P + Q) X ≃ P X ⊕ Q X where
  toFun
    | ⟨.inl a, children⟩ => .inl ⟨a, children⟩
    | ⟨.inr b, children⟩ => .inr ⟨b, children⟩
  invFun
    | .inl ⟨a, children⟩ => ⟨.inl a, children⟩
    | .inr ⟨b, children⟩ => ⟨.inr b, children⟩
  left_inv := by
    rintro ⟨a | b, children⟩ <;> rfl
  right_inv := by
    rintro (⟨a, children⟩ | ⟨b, children⟩) <;> rfl

/-- `(P · Q) X = P X · Q X`. A child function on `P.B a ⊕ Q.B b` is the same
as a pair of child functions, one on `P.B a` and one on `Q.B b`. -/
def prodEquiv (P Q : PFunctor.{0, 0}) (X : Type) :
    (P * Q) X ≃ P X × Q X where
  toFun
    | ⟨(a, b), children⟩ =>
        (⟨a, fun p => children (.inl p)⟩, ⟨b, fun q => children (.inr q)⟩)
  invFun
    | (⟨a, lhs⟩, ⟨b, rhs⟩) => ⟨(a, b), Sum.elim lhs rhs⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, children⟩
    exact congrArg (Sigma.mk _) (Sum.elim_comp_inl_inr children)
  right_inv := by
    rintro ⟨⟨a, lhs⟩, ⟨b, rhs⟩⟩
    rfl


/-!
### Substitution

Polynomials can be substituted into each other, and so can signatures.
Mathlib calls this `PFunctor.comp`. A shape of `P.comp Q` is a `P`-shape with
a `Q`-shape in each of its positions, and its positions are the positions of
those inner `Q`-shapes. A layer of `P.comp Q` is a `P` layer whose children
are `Q` layers.
-/

/-- `(P ∘ Q) X = P (Q X)`. -/
def compEquiv (P Q : PFunctor.{0, 0}) (X : Type) :
    P.comp Q X ≃ P (Q X) where
  toFun := PFunctor.comp.get P Q
  invFun := PFunctor.comp.mk P Q
  left_inv _ := rfl
  right_inv _ := rfl


/-!
### Binary trees are `Leaf + Branch · X²`
-/

/-- The binary-tree signature, built out of polynomial pieces. -/
abbrev binaryPoly (Leaf Branch : Type) : PFunctor.{0, 0} :=
  const Leaf + const Branch * var * var

/-- A layer of `Leaf + Branch · X · X` is `Leaf ⊕ Branch × X × X`, which follows
from the building-block equivalences. -/
def binaryPolyEquiv (Leaf Branch X : Type) :
    binaryPoly Leaf Branch X ≃ Leaf ⊕ Branch × X × X :=
  (sumEquiv _ _ X).trans <|
    Equiv.sumCongr (constEquiv Leaf X) <|
      (prodEquiv _ _ X).trans <|
        (Equiv.prodCongr
          ((prodEquiv _ _ X).trans
            (Equiv.prodCongr (constEquiv Branch X) (varEquiv X)))
          (varEquiv X)).trans
        (Equiv.prodAssoc Branch X X)

/-- The hand-written signature `BinaryTreeExample.pfunctor` has the same layer. -/
def binaryLayerEquiv (Leaf Branch X : Type) :
    BinaryTreeExample.pfunctor Leaf Branch X ≃ Leaf ⊕ Branch × X × X where
  toFun
    | ⟨.leaf payload, _⟩ => .inl payload
    | ⟨.branch payload, children⟩ =>
        .inr (payload, children (0 : Fin 2), children (1 : Fin 2))
  invFun
    | .inl payload => ⟨.leaf payload, fun p => nomatch p⟩
    | .inr (payload, lhs, rhs) => ⟨.branch payload, ![lhs, rhs]⟩
  left_inv := by
    rintro ⟨shape | shape, children⟩
    · exact Sigma.ext rfl (heq_of_eq (funext fun p => nomatch p))
    · exact Sigma.ext rfl (heq_of_eq (funext fun p : Fin 2 => by
        fin_cases p <;> rfl))
  right_inv := by
    rintro (payload | ⟨payload, lhs, rhs⟩) <;> rfl

/-- The equivalence is natural: mapping `f` over the children of a layer
corresponds to applying `f` to both `X` components of `Leaf ⊕ Branch × X × X`.
So the two functors agree, not only their values at one `X`. -/
theorem binaryLayerEquiv_map {Leaf Branch X Y : Type} (f : X → Y)
    (layer : BinaryTreeExample.pfunctor Leaf Branch X) :
    binaryLayerEquiv Leaf Branch Y ((BinaryTreeExample.pfunctor Leaf Branch).map f layer) =
      Sum.map id (Prod.map id (Prod.map f f))
        (binaryLayerEquiv Leaf Branch X layer) := by
  rcases layer with ⟨shape | shape, children⟩ <;> rfl


/-!
### Counting evaluates the polynomial

If the shapes, the positions and `X` are all finite, then the number of
layers is the polynomial evaluated at `card X`:

    card (P X) = Σ_a (card X) ^ (card (P.B a)).
-/

instance (P : PFunctor.{0, 0}) [Fintype P.A] [∀ a, Fintype (P.B a)]
    [∀ a, DecidableEq (P.B a)] (X : Type) [Fintype X] : Fintype (P X) :=
  inferInstanceAs (Fintype (Σ a : P.A, P.B a → X))

theorem card_obj (P : PFunctor.{0, 0}) [Fintype P.A]
    [∀ a, Fintype (P.B a)] [∀ a, DecidableEq (P.B a)] (X : Type) [Fintype X] :
    Fintype.card (P X) = ∑ a, Fintype.card X ^ Fintype.card (P.B a) := by
  change Fintype.card (Σ a : P.A, P.B a → X) = _
  simp only [Fintype.card_sigma, Fintype.card_fun]

deriving instance Fintype for BinaryTreeExample.Shape

instance (Leaf Branch : Type) [Fintype Leaf] [Fintype Branch] :
    Fintype (BinaryTreeExample.pfunctor Leaf Branch).A :=
  inferInstanceAs (Fintype (BinaryTreeExample.Shape Leaf Branch))

instance (Leaf Branch : Type) :
    ∀ shape, Fintype ((BinaryTreeExample.pfunctor Leaf Branch).B shape)
  | .leaf _ => inferInstanceAs (Fintype Empty)
  | .branch _ => inferInstanceAs (Fintype (Fin 2))

instance (Leaf Branch : Type) :
    ∀ shape, DecidableEq ((BinaryTreeExample.pfunctor Leaf Branch).B shape)
  | .leaf _ => inferInstanceAs (DecidableEq Empty)
  | .branch _ => inferInstanceAs (DecidableEq (Fin 2))

/-- With 2 leaf payloads, 1 branch payload and 3 possible children, there are
`2 + 1 · 3² = 11` binary-tree layers. -/
example : Fintype.card (BinaryTreeExample.pfunctor Bool Unit (Fin 3)) = 11 := by
  rw [card_obj]
  rfl

/-- The same count read off from `Leaf ⊕ Branch × X × X`. -/
example : Fintype.card (BinaryTreeExample.pfunctor Bool Unit (Fin 3)) = 11 := by
  rw [Fintype.card_congr (binaryLayerEquiv Bool Unit (Fin 3))]
  rfl

end WhyPolynomial

end PolynomialFunctorsAndWTypes
