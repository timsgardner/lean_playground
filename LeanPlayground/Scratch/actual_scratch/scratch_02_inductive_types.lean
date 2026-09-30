import Mathlib.Data.List.Basic

/-!
# Inductive types: things to build and things to prove

The definitions are provided so that the exercises can stay as open `example`s.
Try pattern matching and induction before reaching for automation. In the later
sections, pay attention to what an index tells you after you split a constructor.
-/

namespace InductiveTypesScratch

/-!
## Recursive data: binary trees

The values live at the leaves. In particular, every tree has at least one leaf.
-/

inductive Tree (α : Type) where
  | leaf (value : α)
  | branch (left right : Tree α)

namespace Tree

def map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .branch l r => .branch (map f l) (map f r)

def mirror : Tree α → Tree α
  | .leaf a => .leaf a
  | .branch l r => .branch (mirror r) (mirror l)

def leaves : Tree α → List α
  | .leaf a => [a]
  | .branch l r => leaves l ++ leaves r

end Tree

-- 1. The induction hypothesis has to be used once for each child.
example (t : Tree α) : Tree.mirror (Tree.mirror t) = t := by
  sorry

-- 2. Follow how `map` passes through both recursive branches. The order of
-- function composition matters here.
example (f : α → β) (g : β → γ) (t : Tree α) :
    Tree.map g (Tree.map f t) = Tree.map (g ∘ f) t := by
  sorry

-- 3. The branch case needs a list identity in addition to the two induction
-- hypotheses. See what `simp` knows about reversing an append.
example (t : Tree α) :
    (Tree.mirror t).leaves = t.leaves.reverse := by
  sorry

-- 4. There is no empty-tree case. Extract an actual leaf value without
-- assuming that `α` is inhabited.
example (t : Tree α) : ∃ a : α, a ∈ t.leaves := by
  sorry

/-!
## Inductively defined paths

`Walk step a b` records a finite path from `a` to `b`. Its last constructor
extends a path at the *end*, which affects the useful induction hypothesis.
-/

inductive Walk {α : Type} (step : α → α → Prop) : α → α → Prop where
  | here (a : α) : Walk step a a
  | snoc {a b c : α} : Walk step a b → step b c → Walk step a c

-- 5. Put one edge at the end of a zero-length path.
example {step : α → α → Prop} {a b : α} (h : step a b) :
    Walk step a b := by
  sorry

-- 6. Prove path concatenation. Induction on the *second* path fits `snoc`
-- particularly well; induction on the first needs a different setup.
example {step : α → α → Prop} {a b c : α}
    (p : Walk step a b) (q : Walk step b c) : Walk step a c := by
  sorry

-- 7. Translate every edge along a path. The vertex map does not have to be
-- injective, and the source and target types may differ.
example {step : α → α → Prop} {next : β → β → Prop}
    (f : α → β)
    (preserves : ∀ {x y}, step x y → next (f x) (f y))
    {a b : α} (p : Walk step a b) : Walk next (f a) (f b) := by
  sorry

-- 8. If every individual edge increases a measure, so does every path.
-- Use the induction hypothesis together with transitivity of `≤`.
example {step : α → α → Prop} (weight : α → Nat)
    (increases : ∀ {x y}, step x y → weight x ≤ weight y)
    {a b : α} (p : Walk step a b) : weight a ≤ weight b := by
  sorry

/-!
## Indexed data: length is part of the type

The `n` in `Vec α n` restricts which constructors can have that result type.
Several exercises need dependent case splits rather than an ordinary list proof.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (head : α) (tail : Vec α n) : Vec α (n + 1)

namespace Vec

def toList : Vec α n → List α
  | .nil => []
  | .cons a tail => a :: toList tail

def map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons a tail => .cons (f a) (map f tail)

def append : Vec α m → Vec α n → Vec α (m + n)
  | .nil, ys => by simpa using ys
  | .cons a xs, ys => by
      simpa [Nat.succ_add] using Vec.cons a (append xs ys)

end Vec

-- 9. Construct a vector of exactly three elements using only constructors.
example (a b c : α) : Vec α 3 := by
  sorry

-- 10. A vector of length zero has only one possible shape.
example (xs : Vec α 0) : xs = .nil := by
  sorry

-- 11. A positive length rules out `nil` and exposes the tail's exact length.
example {n : Nat} (xs : Vec α (n + 1)) :
    ∃ (a : α) (tail : Vec α n), xs = .cons a tail := by
  sorry

-- 12. The index arithmetic in `append` has already been handled by its
-- definition. Prove that its contents agree with ordinary list append.
example (xs : Vec α m) (ys : Vec α n) :
    (Vec.append xs ys).toList = xs.toList ++ ys.toList := by
  sorry

-- 13. Produce a vector whose length is the sum in the other order. This is
-- an exercise in transporting data across an equality of indices.
example (xs : Vec α (m + n)) : Vec α (n + m) := by
  sorry

/-!
## Typed syntax trees

An `Expr t` can only evaluate to a value of type `Ty.denote t`. The constructors
encode which operations are allowed at each type. The desugaring pass removes
`twice` while recursively visiting the rest of the expression.
-/

inductive Ty where
  | nat
  | bool

abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | num (n : Nat) : Expr .nat
  | boolean (b : Bool) : Expr .bool
  | add (left right : Expr .nat) : Expr .nat
  | twice (arg : Expr .nat) : Expr .nat
  | isZero (arg : Expr .nat) : Expr .bool
  | ite {t : Ty} (condition : Expr .bool)
      (yes no : Expr t) : Expr t

namespace Expr

def eval : Expr t → Ty.denote t
  | .num n => n
  | .boolean b => b
  | .add l r => eval l + eval r
  | .twice e => eval e + eval e
  | .isZero e => eval e == 0
  | .ite c yes no => if eval c then eval yes else eval no

def desugar : Expr t → Expr t
  | .num n => .num n
  | .boolean b => .boolean b
  | .add l r => .add (desugar l) (desugar r)
  | .twice e => .add (desugar e) (desugar e)
  | .isZero e => .isZero (desugar e)
  | .ite c yes no => .ite (desugar c) (desugar yes) (desugar no)

end Expr

-- 14. Build the specified Boolean expression and connect its syntax to its
-- meaning. The conditional chooses the opposite of the zero test.
example (n : Nat) :
    ∃ e : Expr .bool,
      e = .ite (.isZero (.twice (.num n))) (.boolean false) (.boolean true) ∧
      e.eval = !(n + n == 0) := by
  sorry

-- 15. Prove the pass preserves the meaning of every well-typed expression.
-- The dependent index changes between some induction cases; inspect each goal.
example {t : Ty} (e : Expr t) :
    (Expr.desugar e).eval = e.eval := by
  sorry

-- 16. Combine the previous semantic idea with a nested conditional. The
-- condition is itself an expression, not a Lean proposition.
example (c : Expr .bool) (x y : Expr .nat) :
    (Expr.ite c (.twice x) (.twice y)).eval =
      if c.eval then x.eval + x.eval else y.eval + y.eval := by
  sorry

end InductiveTypesScratch
