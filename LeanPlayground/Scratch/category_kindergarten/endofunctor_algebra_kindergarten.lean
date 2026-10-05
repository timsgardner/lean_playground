import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools




/-!
# Endofunctor algebras: doing arithmetic with syntax

Let `C` be a category. An *algebra* `(A, α)` of an endofunctor `F : C ⥤ C` is an
object `A : C` with a morphism `α : F A ⟶ A` of `C`. `A` is called the
*carrier*, `α` is called the *structure map*.

From `F` we form the *category of F-algebras*. Note that "F-algebra" here just
means the category of algebras of the endofunctor `F`. If we were looking at the
category of algebras of the endofunctor `G`, we would call it the "category of
G-algebras."

The category of F-algebras is defined as follows:
- Objects: algebras (`(A, α)`, `(B, β)`, etc) of `F`.
- Morphisms: morphisms `f: (A, α) ⟶ (B, β)` in the category of F-algebras are
  those morphisms `f: A ⟶ B` in `C` that make this square commute:

```
       F A  ─── F f ───→  F B
        │                  │
        α                  β
        │                  │
        ↓                  ↓
        A  ───── f ──────→ B
```

- The identity morphism for `(A, α)` is just `𝟙 A`.
- Composition is just composition of underlying morphisms in `C`. The
  commutativity condition for `C` morphisms being included in the category of
  F-algebras ensures this obeys the categorical composition law.

In this file, `F` is the endofunctor `layerF : Type ⥤ Type`, so we're examining the
*category of `layerF`-algebras*. The condition on its morphisms is that any morphism
`f : (A, α) ⟶ (B, β)` must make the following diagram commute:

```
layerF.obj A  ── layerF.map f ──→  layerF.obj B
      │                                │
      α                                β
      │                                │
      ↓                                ↓
      A  ─────────── f ─────────────→  B
```

The action of `layerF` on objects is to construct the inductive wrapper `Layer`, and
its action on morphisms is to apply `Layer.map`, so the diagram above translates to:

```
Layer A  ─── Layer.map f ───→  Layer B
   │                              │
   α                              β
   │                              │
   ↓                              ↓
   A  ────────── f ─────────────→ B
```



## The concrete task

We want to manipulate expressions such as `(x * 1) + (2 + 3)`. An expression is
a tree: the outer `+` has two children, its left child is a `*`, and so on.
There are several things we might do with that same tree:

* build it from its constructors;
* evaluate it after choosing a number for `x`;
* simplify it to `x + 5` by removing `* 1` and adding the two literals.

The common pattern is **bottom-up processing**. First process each child of a
node. Then do one operation at the parent, using the processed children. The
type `Layer X` below describes the input to that *parent operation*: a choice of
constructor, plus an `X` for each child position. For example,
`Layer.add left right : Layer X` is an addition node with two child results of
type `X`. A `Layer X` is only one node. A whole nested expression is an `Expr`.

Here are two choices for `X` at an addition node, followed by the operation that
relates them:

* `Layer Expr`: the children are expression trees. The parent can construct
  `Expr.add left right`, or inspect the trees to simplify the addition.
* `Layer Nat`: the children have been evaluated to numbers. The parent can
  return `left + right`.
* `Layer.map f`: if `f : X → Y`, apply `f` to the children of a `Layer X` to
  obtain a `Layer Y`. The constructor at the parent stays the same.

`layerF` packages `Layer` and `Layer.map` as an endofunctor on types. An
algebra for this functor consists of a carrier type `A` and a structure map
`Layer A → A`: instructions for handling **one** already-processed node. The
generic `fold` traverses an entire `Expr`, processing children recursively and
then calling that structure map at each parent. Thus `values x` gives a fold
into `Nat`, while `simplifiedSyntax` gives a fold back into `Expr`.

## What the categorical part adds

The `syntaxAlgebra` structure map assembles `Layer Expr → Expr` without
rewriting. `foldHom` packages a fold as an algebra morphism. The morphism law
says that folding after assembling one node equals processing its children first
and then interpreting that node. We prove every morphism out of `syntaxAlgebra`
is such a fold; this makes `syntaxAlgebra` an initial object in mathlib's
category `Endofunctor.Algebra layerF`.

Finally, `evaluateHom` says evaluation respects each local simplification rule.
Composing it with the simplification fold gives a morphism from syntax to
values. Initiality says this must be the ordinary evaluation fold, so
simplifying any expression preserves its value.

An endofunctor algebra supplies operations, not equations for those operations.
Associativity, distributivity, and the correctness of our rewrite rules are
separate facts. Here we prove only the rewrites implemented below.
-/

namespace EndofunctorAlgebraKindergarten

open CategoryTheory
open CategoryTheory.Endofunctor
open scoped CategoryKindergarten

/- A one-node description of the language. `X` is a placeholder for whatever
the traversal has produced at each child: syntax for construction and
simplification, or numbers for evaluation. The constructors `lit` and `var`
have no children; `add` and `mul` each have two. -/
inductive Layer (X : Type) where
  | lit : Nat → Layer X
  | var : Layer X
  | add : X → X → Layer X
  | mul : X → X → Layer X

/- This visits only the immediate child slots. It does not traverse an `Expr`
tree by itself. The recursive traversal happens in `fold` below. -/
def Layer.map {X Y : Type} (f : X → Y) : Layer X → Layer Y
  | .lit n => .lit n
  | .var => .var
  | .add a b => .add (f a) (f b)
  | .mul a b => .mul (f a) (f b)

example : Layer.map (fun n : Nat => n + 1) (Layer.add 2 3) = Layer.add 3 4 := rfl

/- An endofunctor must say what it does both to objects (`Type`s here) and to
arrows (functions here). `obj X := Layer X` gives the possible one-node inputs
for an operation returning an `X`. `map f` converts a layer with `X` children
to one with `Y` children. The final two fields prove that mapping an identity
or a composite behaves as a functor should. -/
def layerF : Type ⥤ Type where
  obj X := Layer X
  map f := TypeCat.ofHom (Layer.map f)
  map_id X := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer <;> rfl
  map_comp f g := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer <;> rfl

/- Now we define whole trees. Unlike `Layer X`, the `add` and `mul`
constructors of `Expr` contain more `Expr`s, so they can nest arbitrarily. -/
inductive Expr where
  | lit : Nat → Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, DecidableEq

/- Interpret one layer of *existing expression trees* by attaching a root
constructor. This is the syntax algebra, with carrier `Expr` and structure map
`Layer Expr → Expr`. It neither evaluates nor simplifies. -/
def syntaxAlgebra : Algebra layerF where
  a := Expr
  str := TypeCat.ofHom fun
    | .lit n => .lit n
    | .var => .var
    | .add a b => .add a b
    | .mul a b => .mul a b

/- Given *any* algebra `A`, interpret a whole expression in its carrier `A.a`.
For an addition, recursively fold both subexpressions, obtaining two `A.a`s;
then pass `Layer.add` of those results to `A.str`. This separates tree
traversal from the meaning assigned to each constructor. -/
def fold (A : Algebra layerF) : Expr → A.a
  | .lit n => A.str (.lit n)
  | .var => A.str .var
  | .add a b => A.str (.add (fold A a) (fold A b))
  | .mul a b => A.str (.mul (fold A a) (fold A b))

/- A morphism of algebras is a function between carriers that respects their
one-node operations. For `fold A`, mathlib's `Hom.h` field asks for

  `layerF.map (fold A) ≫ A.str = syntaxAlgebra.str ≫ fold A`.

At an addition layer, this means
`A.str (.add (fold A left) (fold A right)) = fold A (.add left right)`.
The equation follows directly from the recursive definition of `fold`. -/
def foldHom (A : Algebra layerF) : syntaxAlgebra ⟶ A where
  f := TypeCat.ofHom (fold A)
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer <;> rfl

/- Conversely, an algebra morphism from syntax to `A` has no freedom once
`A.str` is chosen. Its compatibility equation determines its result at each
constructor from its results on the children. Induction gives the unique fold. -/
theorem hom_eq_foldHom (A : Algebra layerF) (f : syntaxAlgebra ⟶ A) :
    f = foldHom A := by
  apply Algebra.ext
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext e
  change f.f e = fold A e
  induction e with
  | lit n =>
      have h := congrArg (fun g : Layer Expr ⟶ A.a => g (Layer.lit n)) f.h
      exact h.symm
  | var =>
      have h := congrArg (fun g : Layer Expr ⟶ A.a => g Layer.var) f.h
      exact h.symm
  | add a b ha hb =>
      have h := congrArg (fun g : Layer Expr ⟶ A.a => g (Layer.add a b)) f.h
      change A.str (.add (f.f a) (f.f b)) = f.f (.add a b) at h
      simpa only [fold, ← ha, ← hb] using h.symm
  | mul a b ha hb =>
      have h := congrArg (fun g : Layer Expr ⟶ A.a => g (Layer.mul a b)) f.h
      change A.str (.mul (f.f a) (f.f b)) = f.f (.mul a b) at h
      simpa only [fold, ← ha, ← hb] using h.symm

/- "Initial" means exactly one algebra morphism from `syntaxAlgebra` to every
other `layerF` algebra. The previous two declarations supplied existence
and uniqueness, respectively. -/
def syntaxIsInitial : CategoryTheory.Limits.IsInitial syntaxAlgebra :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom foldHom hom_eq_foldHom

/- An algebra with carrier `Nat`: choose a value for the variable, then
interpret addition and multiplication as ordinary natural-number operations.
For instance, with `x = 7`, processing `Layer.add 7 2` returns `9`. -/
def values (x : Nat) : Algebra layerF where
  a := Nat
  str := TypeCat.ofHom fun
    | .lit n => n
    | .var => x
    | .add a b => a + b
    | .mul a b => a * b

/- `values x` knows only how to process one layer. Folding it over a whole
tree gives the usual recursive evaluator. -/
def evaluate (x : Nat) : Expr → Nat := fold (values x)

@[simp] theorem evaluate_lit (x n : Nat) : evaluate x (.lit n) = n := rfl
@[simp] theorem evaluate_var (x : Nat) : evaluate x .var = x := rfl
@[simp] theorem evaluate_add (x : Nat) (a b : Expr) :
    evaluate x (.add a b) = evaluate x a + evaluate x b := rfl
@[simp] theorem evaluate_mul (x : Nat) (a b : Expr) :
    evaluate x (.mul a b) = evaluate x a * evaluate x b := rfl

/- These are the two parent operations for simplification. The fold below
handles recursion. When it calls `simplifyAdd a b`, both `a` and `b` are
already simplified subexpressions. The helper may inspect their outer
constructors to eliminate zero or combine two literals. -/
def simplifyAdd : Expr → Expr → Expr
  | .lit 0, b => b
  | a, .lit 0 => a
  | .lit m, .lit n => .lit (m + n)
  | a, b => .add a b

def simplifyMul : Expr → Expr → Expr
  | .lit 0, _ => .lit 0
  | _, .lit 0 => .lit 0
  | .lit 1, b => b
  | a, .lit 1 => a
  | .lit m, .lit n => .lit (m * n)
  | a, b => .mul a b

/- This algebra also has carrier `Expr`, but it handles addition and
multiplication differently from `syntaxAlgebra.str`: its structure map may
return one child or a folded literal instead of attaching the original root. -/
def simplifiedSyntax : Algebra layerF where
  a := Expr
  str := TypeCat.ofHom fun
    | .lit n => .lit n
    | .var => .var
    | .add a b => simplifyAdd a b
    | .mul a b => simplifyMul a b

/- Recursively simplify a whole tree by folding the local operations above. -/
def simplify : Expr → Expr := fold simplifiedSyntax

/- The syntax itself visibly changes. `#eval` shows the paper step
`(x * 1) + (2 + 3)  ↝  x + 5`. These rules do not distribute or reassociate. -/
example : simplify (.mul (.var) (.add (.lit 1) (.lit 0))) = .var := rfl

#eval simplify (.add (.mul .var (.lit 1)) (.add (.lit 2) (.lit 3)))

/- These two lemmas justify precisely the local rewrites above. -/
theorem evaluate_simplifyAdd (x : Nat) (a b : Expr) :
    evaluate x (simplifyAdd a b) = evaluate x a + evaluate x b := by
  cases a <;> cases b <;> try rfl
  all_goals
    simp only [simplifyAdd]
    split <;> simp_all

theorem evaluate_simplifyMul (x : Nat) (a b : Expr) :
    evaluate x (simplifyMul a b) = evaluate x a * evaluate x b := by
  cases a <;> cases b <;> try rfl
  all_goals
    simp only [simplifyMul]
    split <;> simp_all

/- This is an algebra morphism from the simplifying algebra to the evaluating
algebra. Its underlying function is `evaluate x`. The morphism condition says,
for every `layer : Layer Expr`, that

  evaluate x (simplifiedSyntax.str layer)
    = (values x).str (Layer.map (evaluate x) layer).

On the left, simplify one node and then evaluate it. On the right, evaluate
its children and then perform the corresponding arithmetic operation. The
two local lemmas above prove the addition and multiplication cases. -/
def evaluateHom (x : Nat) : simplifiedSyntax ⟶ values x where
  f := TypeCat.ofHom (evaluate x)
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer with
    | lit n => rfl
    | var => rfl
    | add a b => exact (evaluate_simplifyAdd x a b).symm
    | mul a b => exact (evaluate_simplifyMul x a b).symm

/- `forget` exposes the ordinary function underlying an algebra morphism.
The morphism still carries its compatibility proof in the algebra category. -/
example (x : Nat) :
    (Algebra.forget layerF).map (evaluateHom x) =
      TypeCat.ofHom (evaluate x) := rfl

/- There are two routes from syntax to numbers:

  syntaxAlgebra --foldHom simplifiedSyntax--> simplifiedSyntax
        |                                      |
  foldHom (values x)                       evaluateHom x
        |                                      |
        +---------------> values x <----------+

The top-right route simplifies and then evaluates; the left route evaluates
directly. Both are algebra morphisms with the same source and target.
Initiality makes them equal. Taking their underlying functions at `e` yields
the theorem below. -/
theorem evaluate_simplify (x : Nat) (e : Expr) :
    evaluate x (simplify e) = evaluate x e := by
  have h : foldHom simplifiedSyntax ≫ evaluateHom x = foldHom (values x) :=
    hom_eq_foldHom (values x) _
  exact congrArg (fun g : syntaxAlgebra ⟶ values x => g.f e) h

example (x : Nat) :
    evaluate x (simplify (.add (.mul .var (.lit 1)) (.add (.lit 2) (.lit 3)))) =
      x + 5 := by
  rw [evaluate_simplify]
  simp

/- The API also knows that an initial algebra's constructor map is an iso:
each expression can be peeled into exactly one outer layer of syntax. -/
example : IsIso syntaxAlgebra.str := Algebra.Initial.str_isIso syntaxIsInitial

def numListAlgebra : Algebra layerF where
  a := List Nat
  str := TypeCat.ofHom fun
    | .lit n => [n]
    | .var => []
    | .add a b => a ++ b
    | .mul a b => a ++ b

#eval fold numListAlgebra (.add (.mul .var (.lit 1)) (.add (.lit 2) (.lit 3)))
-- [1, 2, 3]

/- Simplification combines two literals into one, while `numListAlgebra`
records them separately. An algebra morphism would have to respect both
operations on the same layer, which is impossible. -/
theorem no_simplifiedSyntax_to_numListAlgebra :
    ¬ Nonempty (simplifiedSyntax ⟶ numListAlgebra) := by
  rintro ⟨f⟩
  have hLit (n : Nat) : f.f (.lit n) = [n] := by
    have h := congrArg (fun g : Layer Expr ⟶ List Nat => g (Layer.lit n)) f.h
    exact h.symm
  have hAdd := congrArg
    (fun g : Layer Expr ⟶ List Nat => g (Layer.add (.lit 2) (.lit 3))) f.h
  change List.append (f.f (.lit 2)) (f.f (.lit 3)) = f.f (.lit 5) at hAdd
  rw [hLit 2, hLit 3, hLit 5] at hAdd
  contradiction

/- Folding syntax into `numListAlgebra` collects literals in left-to-right
order and discards variables. -/
def numListHom : syntaxAlgebra ⟶ numListAlgebra := foldHom numListAlgebra

/- There is no algebra morphism in the reverse direction. The variable
case forces the empty list to map to `var`, while addition of two empty lists
would force `var + var` to equal `var`. -/
theorem no_numListAlgebra_to_syntaxAlgebra :
    ¬ Nonempty (numListAlgebra ⟶ syntaxAlgebra) := by
  rintro ⟨f⟩
  have hVar := congrArg (fun g : Layer (List Nat) ⟶ Expr => g Layer.var) f.h
  change Expr.var = f.f [] at hVar
  have hAdd := congrArg
    (fun g : Layer (List Nat) ⟶ Expr => g (Layer.add [] [])) f.h
  change Expr.add (f.f []) (f.f []) = f.f [] at hAdd
  rw [← hVar] at hAdd
  contradiction

/- This algebra records how many literal nodes occur, ignoring their values
and variables. Both binary constructors combine counts by addition. -/
def countAlgebra : Algebra layerF where
  a := Nat
  str := TypeCat.ofHom fun
    | .lit _ => 1
    | .var => 0
    | .add a b => a + b
    | .mul a b => a + b

/- List length respects the `numListAlgebra` operations, so it is an algebra
morphism into the literal-counting algebra. -/
def numListToCount : numListAlgebra ⟶ countAlgebra where
  f := TypeCat.ofHom List.length
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer with
    | lit n => rfl
    | var => rfl
    | add a b => exact List.length_append.symm
    | mul a b => exact List.length_append.symm

/- In the reverse direction, every literal would have to map from the same
count `1`, despite producing different singleton lists. -/
theorem no_countAlgebra_to_numListAlgebra :
    ¬ Nonempty (countAlgebra ⟶ numListAlgebra) := by
  rintro ⟨f⟩
  have hZero := congrArg (fun g : Layer Nat ⟶ List Nat => g (Layer.lit 0)) f.h
  have hOne := congrArg (fun g : Layer Nat ⟶ List Nat => g (Layer.lit 1)) f.h
  change [0] = f.f (1 : Nat) at hZero
  change [1] = f.f (1 : Nat) at hOne
  rw [← hZero] at hOne
  contradiction

/- The one-point algebra forgets every distinction between syntax layers. -/
def unitAlgebra : Algebra layerF where
  a := Unit
  str := TypeCat.ofHom fun _ => ()

/- Every list has the same image in the one-point algebra. -/
def numListToUnit : numListAlgebra ⟶ unitAlgebra where
  f := TypeCat.ofHom fun _ => ()
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer <;> rfl

/- A constant map on lists cannot be invertible: an inverse would make the
distinct lists `[]` and `[0]` equal. -/
theorem not_isIso_numListToUnit : ¬ IsIso numListToUnit := by
  intro h
  letI : IsIso numListToUnit := h
  have hId := IsIso.hom_inv_id numListToUnit
  have hNil := congrArg (fun g : numListAlgebra ⟶ numListAlgebra => g.f []) hId
  have hZero := congrArg (fun g : numListAlgebra ⟶ numListAlgebra => g.f [0]) hId
  change (inv numListToUnit).f () = [] at hNil
  change (inv numListToUnit).f () = [0] at hZero
  rw [hNil] at hZero
  contradiction


section branching

set_option pp.categoryTheory.hideConcreteHom true

inductive Branching (Op : Type) (A : Type) where
  | leaf : A → Branching Op A
  | branch : Op → Branching Op A → Branching Op A → Branching Op A

namespace Branching

-- inductive Frame (Op: Type) (A: Type) where
--   | leaf : A → Branching Op A
--   | branch : Op ⟶

def map {Op A B : Type} (f : A → B) :
    Branching Op A → Branching Op B
  | leaf a => leaf (f a)
  | branch op left right => branch op (map f left) (map f right)

def BranchingF (Op: Type) : Type ⥤ Type where
  obj A := Branching Op A
  map f := TypeCat.ofHom (Branching.map f)
  map_id X := by
    ext br
    change Branching.map (fun x : X => x) br = br
    induction br with
    | leaf a => rfl
    | branch op left right ihl ihr =>
        simp only [Branching.map, ihl, ihr]
  map_comp f g := by
    ext br; simp
    induction br with
    | leaf a => rfl
    | branch op left right ihl ihr =>
        simp only [Branching.map, ihl, ihr]

end Branching

end branching

section fold


/-! The list algebra is initial for the `Type ⥤ Type` endofunctor
`X ↦ Unit ⊕ (Elem × X)` (once you select an `Elem`).

To illustrate, we'll use `ListLayer` as a presentation of `Unit ⊕ (Elem × X)`
with more familiar constructors: `nil` and `cons`. But really we're talking about
a type, values of which are either:

- some distinguished sentinel value, conventionally `nil`, or
- an ordered pair.

 -/

/-! Our pedagogical presentation of `Unit ⊕ (Elem × X)`.
The suggestive names derive from -/
inductive ListLayer (Elem X : Type) where
  | nil
  | cons (head : Elem) (tailResult : X)


example (Elem X : Type) (bla: Unit ⊕ (Elem × X)): true := by
  #check Unit ⊕ (Elem × X)
  trivial

namespace ListLayer

abbrev CanonicalTarget (Elem X : Type) := Unit ⊕ (Elem × X)

/-! ListLayer is just a presentation of `Unit ⊕ (Elem × X)`.
First get the bijection between the types. -/

/-- Bijection between `ListLayer Elem X` and `Unit ⊕ (Elem × X)`.-/
def canonicalEquiv (Elem X : Type) :
    ListLayer Elem X ≃ CanonicalTarget Elem X where
  toFun
    | .nil => .inl ()
    | .cons e x => .inr (e, x)

  invFun
    | .inl () => .nil
    | .inr (e, x) => .cons e x

  left_inv := by
    intro l
    cases l <;> rfl

  right_inv := by
    intro s
    cases s with
    | inl u =>
        cases u
        rfl
    | inr p =>
        cases p
        rfl

/- The Iso is then immediate from the bijection. -/
def canonicalIso (Elem X : Type) :
    ListLayer Elem X ≅ CanonicalTarget Elem X :=
  (canonicalEquiv Elem X).toIso

end ListLayer

def listF (Elem : Type) : Type ⥤ Type where
  obj X := ListLayer Elem X

  /- Note that for cons pairs this retains the "head", and applies the function
  to the instance of the carrier type. Do not confuse this `map` -- which is
  just the functor's action on morphisms -- for `List.map`, which we will
  construct as its own algebra below.

  Notably, the implementation of this function is quite similar to `List.foldr`.
  We will return to this.-/
  map {X Y : Type} (f : X ⟶ Y) :=
    TypeCat.ofHom (fun (l : ListLayer Elem X) =>
      match l with
      | .nil =>
          (.nil : ListLayer Elem Y)
      | .cons head tailResult =>
          .cons head (f tailResult))

  map_id X := by
    ext layer
    cases layer <;> rfl

  map_comp f g := by
    ext layer
    cases layer <;> rfl

/- Now we construct the list algebra, which as we shall see is initial in the
category of algebras of `listF`.

The image of `List Elem` itself under `listF` (that is, `listF(List Elem)`) is
`ListLayer Elem (List Elem)`.

Non-nil values of `ListLayer Elem (List Elem)`, then, are pairs in
`Elem × (List Elem)`. For the structure map `str` to take such values back to
`List Elem`, we can interpret these values as cons pairs: the `Elem` is the
"head", the `(List Elem)` is the "tail".

Note that we *still* have not constructed anything clearly looping or recursive.
That awaits us in `listFold`, below.
-/
def listAlgebra (Elem : Type) : Algebra (listF Elem) where
  a := List Elem
  str := TypeCat.ofHom fun
    | .nil => []
    | .cons head tail => head :: tail

/- We now contruct `listFold`. This is actually a factory (or indexed family of
functions) that takes an algebra of `listF Elem`, and produces a function from
`List Elem` to the carrier set of that algebra.

Since `ListElem` is the carrier set of `listAlgebra`, this produced function is
a candidate morphism out of `listAlgebra` in the category of algebras for
`listF`. By the proof of the relevant commutativity condition given in
`listFoldHom.h`, it is in fact such a morphism.

`listFold`, then, can also be seen as a factory of algebra morphisms out of
`listF Elem`.

The action of the produced function on non-empty lists in `List Elem` can be
considered in steps.
1. Destructure the list into `head : Elem` and `tail : List Elem`.
2. *Recursively* construct the image of `tail` under `listFold A`, landing in
   the carrier `A.a` of the algebra `A`. The recursion thereby descends on the
   tail of the list in `List Elem`.
3. Construct a `ListLayer Elem A.a` from `head` and this value
   `(listFold A tail)` in `A.a`. This `ListLayer` is in `listF(A.a)`.
4. Use the structure map `A.str` to send this instance of `ListLayer Elem A.a`
   back to the carrier `A.a`.


 -/
def listFold {Elem : Type} (A : Algebra (listF Elem)) : List Elem → A.a
  | [] => A.str .nil
  | head :: tail => A.str (.cons head (listFold A tail))

def listFoldHom {Elem : Type} (A : Algebra (listF Elem)) : listAlgebra Elem ⟶ A where
  f := TypeCat.ofHom (listFold A)
  h := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext layer
    cases layer <;> rfl

/- This proof uses only induction on the constructors of a list. In particular,
it does not appeal to any pre-existing uniqueness theorem for `List.foldr`. -/
theorem list_hom_eq_foldHom {Elem : Type} (A : Algebra (listF Elem))
  (f : listAlgebra Elem ⟶ A) : f = listFoldHom A := by
  apply Algebra.ext
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext xs
  change f.f xs = listFold A xs
  induction xs with
  | nil =>
      have h := congrArg (fun g : ListLayer Elem (List Elem) ⟶ A.a => g .nil) f.h
      exact h.symm
    | cons head tail ih =>
      have h := congrArg (fun g : ListLayer Elem (List Elem) ⟶ A.a => g (.cons head tail)) f.h
      change A.str (.cons head (f.f tail)) = f.f (head :: tail) at h
      simpa only [listFold, ih] using h.symm

/- Equivalently, `listAlgebra Op` is initial: every target algebra receives
exactly one algebra morphism, namely `listFoldHom`. -/
def listIsInitial (Elem : Type) : CategoryTheory.Limits.IsInitial (listAlgebra Elem) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom listFoldHom list_hom_eq_foldHom

/- Normal list mapping is a fold whose carrier changes from `List Elem` to
`List OtherElem`. The `cons` case transforms the current head and receives an
already-mapped tail result. -/
def listMapAlgebra {Elem OtherElem : Type} (g : Elem → OtherElem) : Algebra (listF Elem) where
  a := List OtherElem
  str := TypeCat.ofHom fun
    | .nil => []
    | .cons head mappedTail => g head :: mappedTail

def listMap {Elem OtherElem : Type} (g : Elem → OtherElem) : List Elem → List OtherElem :=
  listFold (listMapAlgebra g)

#eval listMap (fun n : Nat => n + 1) [1, 2, 3]
-- [2, 3, 4]

/- A literal nested product has a different type at every possible list length.
`PairStack` supplies one uniform type and an explicit base case, while retaining
the intended right-nested-pair shape. -/
inductive PairStack (Elem : Type) where
  | base : PairStack Elem
  | pair : Elem → PairStack Elem → PairStack Elem
  deriving Repr

def pairStackAlgebra (Elem : Type) : Algebra (listF Elem) where
  a := PairStack Elem
  str := TypeCat.ofHom fun
    | .nil => .base
    | .cons head foldedTail => .pair head foldedTail

#eval listFold (pairStackAlgebra Nat) [1, 2, 3]
-- PairStack.pair 1 (PairStack.pair 2 (PairStack.pair 3 PairStack.base))

end fold


end EndofunctorAlgebraKindergarten
