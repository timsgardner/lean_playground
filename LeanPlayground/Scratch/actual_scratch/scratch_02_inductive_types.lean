import Mathlib.Data.List.Basic

set_option pp.fieldNotation false

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
  induction t with
  | leaf a => dsimp only [Tree.mirror]
  | branch l r hli hri =>
      conv =>
        lhs
        congr
        dsimp only [Tree.mirror]
      dsimp only [Tree.mirror]
      rw [hli, hri]


-- 2. Follow how `map` passes through both recursive branches. The order of
-- function composition matters here.
example (f : α → β) (g : β → γ) (t : Tree α) :
    Tree.map g (Tree.map f t) = Tree.map (g ∘ f) t := by
  induction t with
  | leaf a =>
      dsimp only [Tree.map]
      rw [Function.comp]
  | branch l r hli hri =>
      dsimp only [Tree.map]
      rw [hli]
      rw [hri]


-- 3. The branch case needs a list identity in addition to the two induction
-- hypotheses. See what `simp` knows about reversing an append.
example (t : Tree α) :
    (Tree.mirror t).leaves = t.leaves.reverse := by
  induction t with
  | leaf a =>
      dsimp only [Tree.leaves]
      dsimp only [Tree.mirror]
      dsimp only [Tree.leaves]
      rfl
  | branch l r hl hr =>
      dsimp only [Tree.mirror]
      dsimp only [Tree.leaves]
      rw [hl]
      rw [hr]
      simp

-- 4. There is no empty-tree case. Extract an actual leaf value without
-- assuming that `α` is inhabited.
example (t : Tree α) : ∃ a : α, a ∈ t.leaves := by
  induction t with
  | leaf a =>
      refine ⟨?_, ?_⟩
      · exact a
      · dsimp only [Tree.leaves]
        simp
  | branch l r hl hr =>
      obtain ⟨a, ha⟩ := hl
      refine ⟨a, ?_⟩
      dsimp only [Tree.leaves]
      exact (Tree.leaves l).mem_append_left (Tree.leaves r) ha

/-!
## Inductively defined reachability

This declaration has a different result sort from `Tree α : Type`. Here `α` is
the type of vertices, and `canMove : α → α → Prop` is a binary relation:
`canMove x y` is the *proposition* that one move from `x` to `y` is allowed.
Once `canMove` is fixed, `CanReach canMove : α → α → Prop` is another binary
relation. In particular, `CanReach canMove a b : Prop` says that `a` can reach
`b` in finitely many moves. A term of that proposition is a proof of
reachability, rather than a list-valued path to compute with.

The endpoints `a` and `b` are *indices*: different choices give different
propositions in the family. The parameters `α` and `canMove` stay fixed.
`refl a` proves `CanReach canMove a a` with zero moves; it needs no proof of
`canMove a a`. Given `CanReach canMove a b` and `canMove b c`, `extend` proves
`CanReach canMove a c`. Thus the constructors describe exactly how proofs of
reachability are built. Because `extend` adds a move at the *end*, induction
gives a hypothesis about the earlier part of the route.
-/

inductive CanReach {α : Type} (canMove : α → α → Prop) : α → α → Prop where
  | refl (a : α) : CanReach canMove a a
  | extend {a b c : α} : CanReach canMove a b → canMove b c → CanReach canMove a c

-- 5. A single permitted move is enough for reachability: extend the
-- zero-move proof with that move.
example {canMove : α → α → Prop} {a b : α} (h : canMove a b) :
    CanReach canMove a b := by
      exact CanReach.extend (CanReach.refl a) h

-- 6. Prove reachability is transitive. Induction on the *second* proof fits `extend`
-- particularly well; induction on the first needs a different setup.
example {canMove : α → α → Prop} {a b c : α}
    (p : CanReach canMove a b) (q : CanReach canMove b c) : CanReach canMove a c := by
  induction q with
  | refl => exact p
  | extend path edge ih =>
      exact CanReach.extend ih edge

-- 7. Translate every permitted move along a route. The vertex map does not have to be
-- injective, and the source and target types may differ.
example {canMove : α → α → Prop} {canMove' : β → β → Prop}
    (f : α → β)
    (preserves : ∀ {x y}, canMove x y → canMove' (f x) (f y))
    {a b : α} (p : CanReach canMove a b) : CanReach canMove' (f a) (f b) := by
  induction p with
  | refl =>
      exact CanReach.refl (f a)
  | extend reach_ab move_bc a_ih =>
      have canMove'_bc := preserves move_bc
      exact CanReach.extend a_ih canMove'_bc


-- 8. If every permitted move increases a measure, so does reachability.
-- Use the induction hypothesis together with transitivity of `≤`.
example {canMove : α → α → Prop} (weight : α → Nat)
    (increases : ∀ {x y}, canMove x y → weight x ≤ weight y)
    {a b : α} (p : CanReach canMove a b) : weight a ≤ weight b := by
  induction p with
  | refl => simp -- the goal here is immediate from ≤
  | extend canReach_h canMove_h a_ih =>
      let thing := (increases canMove_h)
      exact Nat.le_trans a_ih thing

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

-- Writing the index as `n + m` lets the two equations reduce directly:
-- `n + 0 = n` and `n + (m + 1) = (n + m) + 1` by computation.
def append : Vec α m → Vec α n → Vec α (n + m)
  | .nil, ys => ys
  | .cons a xs, ys => .cons a (append xs ys)

end Vec

-- 9. Construct a vector of exactly three elements using only constructors.
example (a b c : α) : Vec α 3 := by
  exact Vec.nil |> Vec.cons c |> Vec.cons b |> Vec.cons a

-- 10. A vector of length zero has only one possible shape.
example (xs : Vec α 0) : xs = .nil := by
  cases xs
  · rfl

-- 11. A positive length rules out `nil` and exposes the tail's exact length.
example {n : Nat} (xs : Vec α (n + 1)) :
    ∃ (a : α) (tail : Vec α n), xs = .cons a tail := by
  cases xs with
  | cons a tail =>
      exact ⟨a, tail, rfl⟩

-- 12. The index arithmetic in `append` has already been handled by its
-- definition. Prove that its contents agree with ordinary list append.
example (xs : Vec α m) (ys : Vec α n) :
    (Vec.append xs ys).toList = xs.toList ++ ys.toList := by
  let xys := Vec.append xs ys
  induction xs with
  | nil =>
      dsimp only [Vec.append]
      simp [Vec.toList]
  | cons a tail tail_ih =>
      dsimp only [Vec.append]
      conv =>
        rhs
        dsimp only [Vec.toList]
        simp
      dsimp only [Vec.toList]
      simp at *
      exact tail_ih

-- 13. Transport the length index across commutativity, but keep the contents
-- unchanged. First consider what transport along an arbitrary index equality
-- does to `toList`; specializing immediately to `Nat.add_comm` obscures that.
example (xs : Vec α (m + n)) :
    ∃ ys : Vec α (n + m), ys.toList = xs.toList := by
  have toList_transport {i j : Nat} (h : i = j) (v : Vec α i) :
      (h ▸ v : Vec α j).toList = v.toList := by
    cases h
    rfl
  let h : m + n = n + m := Nat.add_comm m n
  exact ⟨h ▸ xs, toList_transport h xs⟩

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
