import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise

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

`Expr` is an indexed family in `Type`, like `Vec`: `Expr .nat` and `Expr .bool`
are different types of syntax trees. `Ty.denote` maps those indices to Lean's
`Nat` and `Bool`, so `eval` returns a value of the right type. For example,
`.add` only builds an `Expr .nat`, while `.isZero` builds an `Expr .bool` from
an `Expr .nat`. An `.ite` has a Boolean condition and two branches with the
same result index. For instance,
`Expr.ite (.boolean true) (.num 2) (.num 3) : Expr .nat`; replacing only its
last branch with `.boolean false` would be ill-typed.

The exercises use `change`, `rw`, and structural induction, as in the tree
section. If `e : Expr .bool`, a case split rules out the natural-number
constructors. For `e : Expr t` with an arbitrary `t`, induction considers all
constructors, specializes `t` in each case, and gives hypotheses for recursive
subexpressions. Those subexpressions may have different indices: the condition
of `.ite` is Boolean even when the whole expression is natural-number-valued.
No explicit index transport is needed here.

`desugar` replaces each `.twice e` with `.add e e` and visits every other
constructor recursively. The main question is whether that change of syntax
preserves what `eval` computes. Prove the small congruence lemma first so the
`.ite` case of the induction can use it directly.
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

-- 14. If the condition and both branches evaluate equally, the two
-- conditionals evaluate equally. Unfold only the outer `eval`, then rewrite
-- with the three hypotheses. This lemma will handle the `.ite` case below.
theorem Expr.eval_ite_congr {t : Ty}
    {c c' : Expr .bool} {yes yes' no no' : Expr t}
    (hc : c.eval = c'.eval)
    (hy : yes.eval = yes'.eval)
    (hn : no.eval = no'.eval) :
    (Expr.ite c yes no).eval = (Expr.ite c' yes' no').eval := by
  unfold eval
  rw [hc]
  rw [hy]
  rw [hn]


-- 15. This is the one structural-induction proof for the pass. In each case,
-- expose the outer `desugar` and `eval`. The recursive cases use their
-- induction hypotheses; for `.ite`, use `Expr.eval_ite_congr` with all three.
theorem Expr.eval_desugar {t : Ty} (e : Expr t) :
    (Expr.desugar e).eval = e.eval := by
  induction e with
  | num n => dsimp only [eval, desugar]
  | boolean b => dsimp only [eval, desugar]
  | add l r l_ih r_ih =>
      dsimp only [eval, desugar]
      rw [l_ih, r_ih]
  | twice a a_ih =>
      change eval (desugar a) + eval (desugar a) = eval a + eval a
      rw [a_ih]
  | isZero e e_ih =>
      dsimp [desugar]
      dsimp [eval]
      rw [e_ih]
  | ite c yes no c_ih yes_ih no_ih =>
      dsimp [desugar]
      exact Expr.eval_ite_congr c_ih yes_ih no_ih


-- 16. These syntax trees differ in two places, but evaluate the same. Reuse
-- both named lemmas rather than doing another induction or expanding the
-- entire expression. The condition and the branches can be handled separately.
example (c : Expr .bool) (x y : Expr .nat) :
    (Expr.ite (Expr.desugar c) (.twice (Expr.desugar x)) y).eval =
      (Expr.ite c (.add x x) y).eval := by
  have hc: (Expr.desugar c).eval = c.eval := by
    exact Expr.eval_desugar c
  have ht: (Expr.twice (Expr.desugar x)).eval = (Expr.add x x).eval := by
    dsimp [Expr.eval]
    rw [Expr.eval_desugar]
  exact Expr.eval_ite_congr hc ht rfl

/-!
## One-hole contexts

`OneHole s t` is an expression of result type `t` with exactly one missing
subexpression of type `s`. Each constructor records which child contains the
hole; all other children are fixed expressions. `plug` fills that hole.
-/

inductive Expr.OneHole (s : Ty) : Ty → Type where
  | hole : OneHole s s
  | addLeft (inner : OneHole s .nat) (right : Expr .nat) : OneHole s .nat
  | addRight (left : Expr .nat) (inner : OneHole s .nat) : OneHole s .nat
  | twice (inner : OneHole s .nat) : OneHole s .nat
  | isZero (inner : OneHole s .nat) : OneHole s .bool
  | iteCondition {t : Ty} (inner : OneHole s .bool)
      (yes no : Expr t) : OneHole s t
  | iteYes {t : Ty} (condition : Expr .bool)
      (inner : OneHole s t) (no : Expr t) : OneHole s t
  | iteNo {t : Ty} (condition : Expr .bool)
      (yes : Expr t) (inner : OneHole s t) : OneHole s t

def Expr.OneHole.plug : OneHole s t → Expr s → Expr t
  | .hole, replacement => replacement
  | .addLeft inner right, replacement =>
      .add (plug inner replacement) right
  | .addRight left inner, replacement =>
      .add left (plug inner replacement)
  | .twice inner, replacement =>
      .twice (plug inner replacement)
  | .isZero inner, replacement =>
      .isZero (plug inner replacement)
  | .iteCondition inner yes no, replacement =>
      .ite (plug inner replacement) yes no
  | .iteYes condition inner no, replacement =>
      .ite condition (plug inner replacement) no
  | .iteNo condition yes inner, replacement =>
      .ite condition yes (plug inner replacement)

/-- Replacing one subexpression by another with the same value preserves the
value of the whole typed expression. -/
theorem Expr.OneHole.eval_plug_congr (C : OneHole s t)
    {x y : Expr s} (h : x.eval = y.eval) :
    (C.plug x).eval = (C.plug y).eval := by
  induction C with
  | hole => exact h
  | addLeft inner right ih =>
      change (inner.plug x).eval + right.eval =
        (inner.plug y).eval + right.eval
      exact congrArg (fun z : Nat => z + right.eval) ih
  | addRight left inner ih =>
      change left.eval + (inner.plug x).eval =
        left.eval + (inner.plug y).eval
      exact congrArg (fun z : Nat => left.eval + z) ih
  | twice inner ih =>
      change (inner.plug x).eval + (inner.plug x).eval =
        (inner.plug y).eval + (inner.plug y).eval
      exact congrArg (fun z : Nat => z + z) ih
  | isZero inner ih =>
      change ((inner.plug x).eval == 0) = ((inner.plug y).eval == 0)
      exact congrArg (fun z : Nat => z == 0) ih
  | iteCondition inner yes no ih =>
      change (Expr.ite (inner.plug x) yes no).eval =
        (Expr.ite (inner.plug y) yes no).eval
      exact Expr.eval_ite_congr ih rfl rfl
  | iteYes condition inner no ih =>
      change (Expr.ite condition (inner.plug x) no).eval =
        (Expr.ite condition (inner.plug y) no).eval
      exact Expr.eval_ite_congr rfl ih rfl
  | iteNo condition yes inner ih =>
      change (Expr.ite condition yes (inner.plug x)).eval =
        (Expr.ite condition yes (inner.plug y)).eval
      exact Expr.eval_ite_congr rfl rfl ih

-- The hole is inside an addition, a zero test, and a conditional.
def Expr.nestedContext : OneHole .nat .bool :=
  .iteCondition (.isZero (.addLeft .hole (.num 1)))
    (.boolean true) (.boolean false)

example (n : Nat) :
    (Expr.nestedContext.plug (.twice (.num n))).eval =
      (Expr.nestedContext.plug (.add (.num n) (.num n))).eval := by
  apply Expr.OneHole.eval_plug_congr
  rfl

/-!
## Several typed holes

A `Template ι holeTy t` is a syntax tree of result type `t` whose holes have
names `i : ι`. The function `holeTy i` says which type of expression may fill
hole `i`; choosing `ι := Fin n` provides `n` possible names. Use a distinct
name at each position if those places should vary independently. Fixed subtrees
are ordinary expressions. This tree-shaped representation makes hole positions
explicit without maintaining paths into a changing tree.

A filling `ρ : ∀ i, Expr (holeTy i)` supplies an expression for each name.
The same template can be filled twice. If corresponding fillings evaluate
equally, the resulting whole expressions evaluate equally.
-/

inductive Expr.Template (ι : Type) (holeTy : ι → Ty) : Ty → Type where
  | hole (i : ι) : Template ι holeTy (holeTy i)
  | fixed {t : Ty} (e : Expr t) : Template ι holeTy t
  | add (left right : Template ι holeTy .nat) : Template ι holeTy .nat
  | twice (arg : Template ι holeTy .nat) : Template ι holeTy .nat
  | isZero (arg : Template ι holeTy .nat) : Template ι holeTy .bool
  | ite {t : Ty} (condition : Template ι holeTy .bool)
      (yes no : Template ι holeTy t) : Template ι holeTy t

def Expr.Template.fill : Template ι holeTy t →
    (∀ i, Expr (holeTy i)) → Expr t
  | .hole i, ρ => ρ i
  | .fixed e, _ => e
  | .add left right, ρ => .add (fill left ρ) (fill right ρ)
  | .twice arg, ρ => .twice (fill arg ρ)
  | .isZero arg, ρ => .isZero (fill arg ρ)
  | .ite condition yes no, ρ =>
      .ite (fill condition ρ) (fill yes ρ) (fill no ρ)

/-- Replacing any collection of holes by expressions with the same respective
values preserves the value of the entire typed expression. -/
theorem Expr.Template.eval_fill_congr (C : Template ι holeTy t)
    (ρ σ : ∀ i, Expr (holeTy i))
    (h : ∀ i, (ρ i).eval = (σ i).eval) :
    (C.fill ρ).eval = (C.fill σ).eval := by
  induction C with
  | hole i => exact h i
  | fixed e => rfl
  | add left right ihLeft ihRight =>
      change (left.fill ρ).eval + (right.fill ρ).eval =
        (left.fill σ).eval + (right.fill σ).eval
      rw [ihLeft, ihRight]
  | twice arg ih =>
      change (arg.fill ρ).eval + (arg.fill ρ).eval =
        (arg.fill σ).eval + (arg.fill σ).eval
      rw [ih]
  | isZero arg ih =>
      change ((arg.fill ρ).eval == 0) = ((arg.fill σ).eval == 0)
      rw [ih]
  | ite condition yes no ihCondition ihYes ihNo =>
      change (Expr.ite (condition.fill ρ) (yes.fill ρ) (no.fill ρ)).eval =
        (Expr.ite (condition.fill σ) (yes.fill σ) (no.fill σ)).eval
      exact Expr.eval_ite_congr ihCondition ihYes ihNo

-- `false` names a Nat hole and `true` names a Bool hole.
def Expr.twoHoleTypes : Bool → Ty
  | false => .nat
  | true => .bool

def Expr.twoHoleTemplate : Template Bool twoHoleTypes .nat :=
  .ite (.hole true) (.add (.hole false) (.fixed (.num 1)))
    (.fixed (.num 0))

def Expr.firstFilling (n : Nat) : (i : Bool) → Expr (twoHoleTypes i)
  | false => .twice (.num n)
  | true => .isZero (.num 0)

def Expr.secondFilling (n : Nat) : (i : Bool) → Expr (twoHoleTypes i)
  | false => .add (.num n) (.num n)
  | true => .boolean true

example (n : Nat) :
    (Expr.twoHoleTemplate.fill (Expr.firstFilling n)).eval =
      (Expr.twoHoleTemplate.fill (Expr.secondFilling n)).eval := by
  apply Expr.Template.eval_fill_congr
  intro i
  cases i <;> rfl

/-!
## Paths to subexpressions

`Path root focus` is data describing child choices from an expression of type
`root` down to a subexpression of type `focus`. The type indices rule out, for
example, treating the condition of an `.ite` as a natural-number expression.
They do not say which constructor the actual tree has, so `follow?` returns
`none` when a path asks for a child that is not there.
-/

inductive Expr.Path : Ty → Ty → Type where
  | here : Path t t
  | addLeft : Path .nat focus → Path .nat focus
  | addRight : Path .nat focus → Path .nat focus
  | twiceArg : Path .nat focus → Path .nat focus
  | isZeroArg : Path .nat focus → Path .bool focus
  | iteCondition {t : Ty} : Path .bool focus → Path t focus
  | iteYes {t : Ty} : Path t focus → Path t focus
  | iteNo {t : Ty} : Path t focus → Path t focus

def Expr.Path.follow? : Path root focus → Expr root → Option (Expr focus)
  | .here, e => some e
  | .addLeft rest, .add left _ => follow? rest left
  | .addLeft _, _ => none
  | .addRight rest, .add _ right => follow? rest right
  | .addRight _, _ => none
  | .twiceArg rest, .twice arg => follow? rest arg
  | .twiceArg _, _ => none
  | .isZeroArg rest, .isZero arg => follow? rest arg
  | .isZeroArg _, _ => none
  | .iteCondition rest, .ite condition _ _ => follow? rest condition
  | .iteCondition _, _ => none
  | .iteYes rest, .ite _ yes _ => follow? rest yes
  | .iteYes _, _ => none
  | .iteNo rest, .ite _ _ no => follow? rest no
  | .iteNo _, _ => none

-- From a natural-number expression: enter its conditional's yes branch,
-- then enter the left child of an addition.
def Expr.examplePath : Path .nat .nat :=
  .iteYes (.addLeft .here)

example :
    Expr.examplePath.follow?
      (.ite (.boolean true) (.add (.num 2) (.num 3)) (.num 0)) =
        some (.num 2) := by
  rfl

example : Expr.examplePath.follow? (.num 7) = none := by
  rfl

/-!
## Paths as ordinary lists of tokens

The earlier `Path root focus` encodes both endpoint types in its type. A plain
`List Token` is easier to assemble or store, but its tokens are not checked
against one another until traversal. The endpoint type is also unknown in
advance, so lookup returns `Σ t, Expr t`: a dependent pair whose first part
selects the type of the expression in its second part. For example, the path
`.iteYes (.addLeft .here)` above is the token list `[.iteYes, .addLeft]` here.
-/

inductive Expr.Token where
  | addLeft
  | addRight
  | twiceArg
  | isZeroArg
  | iteCondition
  | iteYes
  | iteNo

def Expr.Token.child? (tok : Token) (e : Expr t) : Option (Σ u : Ty, Expr u) :=
  match tok, e with
  | .addLeft, .add left _ => some ⟨.nat, left⟩
  | .addRight, .add _ right => some ⟨.nat, right⟩
  | .twiceArg, .twice arg => some ⟨.nat, arg⟩
  | .isZeroArg, .isZero arg => some ⟨.nat, arg⟩
  | .iteCondition, .ite condition _ _ => some ⟨.bool, condition⟩
  | .iteYes, .ite _ yes _ => some ⟨t, yes⟩
  | .iteNo, .ite _ _ no => some ⟨t, no⟩
  | _, _ => none

def Expr.followTokens? (path : List Token) (e : Expr t) :
    Option (Σ u : Ty, Expr u) :=
  match path with
  | [] => some ⟨t, e⟩
  | tok :: rest => do
      let ⟨_, child⟩ ← tok.child? e
      followTokens? rest child

example :
    Expr.followTokens? [.iteYes, .addLeft]
      (.ite (.boolean true) (.add (.num 2) (.num 3)) (.num 0)) =
        some ⟨.nat, .num 2⟩ := by
  rfl

example : Expr.followTokens? [.iteYes, .addLeft] (.num 7) = none := by
  rfl

/-!
## First syntactic differences

Compare matching constructors recursively. At the first mismatch on each
route, record the token path to that node and stop descending along that route.
The resulting paths may have different lengths, but none extends another.
`[]` is the path to the root, so `[[]]` means the roots differ, while `[]`
means the trees are syntactically identical.
-/

def Expr.firstDifferencePaths : Expr t → Expr t → List (List Token)
  | .num n, .num m => if n = m then [] else [[]]
  | .boolean b, .boolean c => if b = c then [] else [[]]
  | .add l r, .add l' r' =>
      (firstDifferencePaths l l').map (fun p => .addLeft :: p) ++
      (firstDifferencePaths r r').map (fun p => .addRight :: p)
  | .twice e, .twice e' =>
      (firstDifferencePaths e e').map (fun p => .twiceArg :: p)
  | .isZero e, .isZero e' =>
      (firstDifferencePaths e e').map (fun p => .isZeroArg :: p)
  | .ite c y n, .ite c' y' n' =>
      (firstDifferencePaths c c').map (fun p => .iteCondition :: p) ++
      (firstDifferencePaths y y').map (fun p => .iteYes :: p) ++
      (firstDifferencePaths n n').map (fun p => .iteNo :: p)
  | _, _ => [[]]

example : Expr.firstDifferencePaths (.num 2) (.num 2) = [] := by
  rfl

example : Expr.firstDifferencePaths (.num 2) (.twice (.num 1)) = [[]] := by
  rfl

example :
    Expr.firstDifferencePaths
      (.add (.num 1) (.twice (.num 2)))
      (.add (.num 3) (.twice (.num 4))) =
        [[.addLeft], [.addRight, .twiceArg]] := by
  rfl

-- A constructor mismatch is reported where it occurs; the children of that
-- mismatched pair are not compared.
example :
    Expr.firstDifferencePaths
      (.add (.num 1) (.num 2))
      (.add (.twice (.num 1)) (.num 3)) =
        [[.addLeft], [.addRight]] := by
  rfl

/-! A node is a stopping point when constructors differ, or matching literal
constructors carry different values. Matching compound constructors are not
stopping points: comparison proceeds into their children. -/
def Expr.HeadMismatch : Expr t → Expr t → Prop
  | .num n, .num m => n ≠ m
  | .boolean b, .boolean c => b ≠ c
  | .add _ _, .add _ _ => False
  | .twice _, .twice _ => False
  | .isZero _, .isZero _ => False
  | .ite _ _ _, .ite _ _ _ => False
  | _, _ => True

/-- A path ends at the first mismatch on its route through two trees. -/
def Expr.FirstMismatch : Expr t → Expr t → List Token → Prop
  | x, y, [] => HeadMismatch x y
  | .add l _, .add l' _, .addLeft :: rest => FirstMismatch l l' rest
  | .add _ r, .add _ r', .addRight :: rest => FirstMismatch r r' rest
  | .twice e, .twice e', .twiceArg :: rest => FirstMismatch e e' rest
  | .isZero e, .isZero e', .isZeroArg :: rest => FirstMismatch e e' rest
  | .ite c _ _, .ite c' _ _, .iteCondition :: rest => FirstMismatch c c' rest
  | .ite _ y _, .ite _ y' _, .iteYes :: rest => FirstMismatch y y' rest
  | .ite _ _ n, .ite _ _ n', .iteNo :: rest => FirstMismatch n n' rest
  | _, _, _ => False

theorem Expr.mem_firstDifferencePaths_iff (x y : Expr t) (p : List Token) :
    p ∈ firstDifferencePaths x y ↔ FirstMismatch x y p := by
  induction x generalizing p with
  | num n =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch]
  | boolean b =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch]
  | add l r ihl ihr =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch, ihl, ihr]
  | twice e ih =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch, ih]
  | isZero e ih =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch, ih]
  | ite c yes no ihc ihy ihn =>
      cases y <;> cases p with
      | nil => simp [firstDifferencePaths, FirstMismatch, HeadMismatch]
      | cons tok rest => cases tok <;> simp [firstDifferencePaths, FirstMismatch, ihc, ihy, ihn]
/-- The order in which child positions are visited at a branching node. -/
def Expr.Token.rank : Token → Nat
  | .addLeft => 0
  | .addRight => 1
  | .twiceArg => 0
  | .isZeroArg => 0
  | .iteCondition => 0
  | .iteYes => 1
  | .iteNo => 2

/-- Strict left-to-right order on paths that diverge before either ends. -/
def Expr.PathBefore : List Token → List Token → Prop
  | a :: p, b :: q => a.rank < b.rank ∨ (a = b ∧ PathBefore p q)
  | _, _ => False

private theorem Expr.pairwise_prepend (tok : Token)
    {paths : List (List Token)} (h : paths.Pairwise PathBefore) :
    (paths.map (fun p => tok :: p)).Pairwise PathBefore := by
  exact List.Pairwise.map (fun p => tok :: p)
    (fun _ _ hab => by simpa [PathBefore] using hab) h

private theorem Expr.pairwise_prepend_append (a b : Token)
    (hab : a.rank < b.rank)
    {left right : List (List Token)}
    (hl : left.Pairwise PathBefore) (hr : right.Pairwise PathBefore) :
    ((left.map (fun p => a :: p)) ++
      (right.map (fun p => b :: p))).Pairwise PathBefore := by
  rw [List.pairwise_append]
  refine ⟨pairwise_prepend a hl, pairwise_prepend b hr, ?_⟩
  intro p hp q hq
  obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
  exact Or.inl hab

private theorem Expr.pairwise_prepend_append_three (a b c : Token)
    (hab : a.rank < b.rank) (hac : a.rank < c.rank) (hbc : b.rank < c.rank)
    {first second third : List (List Token)}
    (hf : first.Pairwise PathBefore) (hs : second.Pairwise PathBefore)
    (ht : third.Pairwise PathBefore) :
    (((first.map (fun p => a :: p)) ++
      (second.map (fun p => b :: p))) ++
      (third.map (fun p => c :: p))).Pairwise PathBefore := by
  rw [List.pairwise_append]
  refine ⟨pairwise_prepend_append a b hab hf hs, pairwise_prepend c ht, ?_⟩
  intro p hp q hq
  obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
    exact Or.inl hac
  · obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
    exact Or.inl hbc

theorem Expr.pairwise_firstDifferencePaths (x y : Expr t) :
    (firstDifferencePaths x y).Pairwise PathBefore := by
  induction x with
  | num n =>
      cases y <;> simp [firstDifferencePaths]; split_ifs <;> simp
  | boolean b =>
      cases y <;> simp [firstDifferencePaths]; split_ifs <;> simp
  | add l r ihl ihr =>
      cases y with
      | add l' r' =>
          simpa only [firstDifferencePaths] using
            pairwise_prepend_append .addLeft .addRight (by decide) (ihl l') (ihr r')
      | num n => simp [firstDifferencePaths]
      | twice a => simp [firstDifferencePaths]
      | ite c yes no => simp [firstDifferencePaths]
  | twice e ih =>
      cases y with
      | twice e' =>
          simpa only [firstDifferencePaths] using pairwise_prepend .twiceArg (ih e')
      | num n => simp [firstDifferencePaths]
      | add l r => simp [firstDifferencePaths]
      | ite c yes no => simp [firstDifferencePaths]
  | isZero e ih =>
      cases y with
      | isZero e' =>
          simpa only [firstDifferencePaths] using pairwise_prepend .isZeroArg (ih e')
      | boolean b => simp [firstDifferencePaths]
      | ite c yes no => simp [firstDifferencePaths]
  | ite c yes no ihc ihy ihn =>
      cases y with
      | ite c' yes' no' =>
          simpa only [firstDifferencePaths, List.append_assoc] using
            pairwise_prepend_append_three .iteCondition .iteYes .iteNo
              (by decide) (by decide) (by decide) (ihc c') (ihy yes') (ihn no')
      | num n => simp [firstDifferencePaths]
      | boolean b => simp [firstDifferencePaths]
      | add l r => simp [firstDifferencePaths]
      | twice a => simp [firstDifferencePaths]
      | isZero a => simp [firstDifferencePaths]

private theorem Expr.PathBefore.not_prefixes {p q : List Token}
    (h : PathBefore p q) : ¬ p <+: q ∧ ¬ q <+: p := by
  induction p generalizing q with
  | nil => cases q <;> simp [PathBefore] at h
  | cons a p ih =>
      cases q with
      | nil => simp [PathBefore] at h
      | cons b q =>
          change a.rank < b.rank ∨ (a = b ∧ PathBefore p q) at h
          rcases h with hab | ⟨rfl, hrest⟩
          · have hne : a ≠ b := by
              intro heq
              subst b
              exact (Nat.lt_irrefl _) hab
            constructor
            · intro hp
              exact hne (List.cons_prefix_cons.mp hp).1
            · intro hp
              exact hne (List.cons_prefix_cons.mp hp).1.symm
          · obtain ⟨hleft, hright⟩ := ih hrest
            constructor
            · intro hp
              exact hleft (List.cons_prefix_cons.mp hp).2
            · intro hp
              exact hright (List.cons_prefix_cons.mp hp).2

/-- No path appears twice in the list of first differences. -/
theorem Expr.nodup_firstDifferencePaths (x y : Expr t) :
    (firstDifferencePaths x y).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (pairwise_firstDifferencePaths x y).imp (fun h heq => by
    subst_eqs
    exact (PathBefore.not_prefixes h).1 (List.prefix_refl _))

/-- No returned path points inside another returned mismatch. -/
theorem Expr.firstDifferencePaths_prefix_free (x y : Expr t)
    {p q : List Token} (hp : p ∈ firstDifferencePaths x y)
    (hq : q ∈ firstDifferencePaths x y) (hne : p ≠ q) : ¬ p <+: q := by
  have hpair : (firstDifferencePaths x y).Pairwise
      (fun p q => ¬ p <+: q ∧ ¬ q <+: p) :=
    (pairwise_firstDifferencePaths x y).imp (fun h => PathBefore.not_prefixes h)
  letI : Std.Symm (fun p q : List Token => ¬ p <+: q ∧ ¬ q <+: p) :=
    ⟨fun _ _ h => ⟨h.2, h.1⟩⟩
  exact (hpair.forall hp hq hne).1

/-- The output is empty precisely when the expressions are syntactically equal. -/
theorem Expr.firstDifferencePaths_eq_nil_iff (x y : Expr t) :
    firstDifferencePaths x y = [] ↔ x = y := by
  induction x with
  | num n => cases y <;> simp [firstDifferencePaths]
  | boolean b => cases y <;> simp [firstDifferencePaths]
  | add l r ihl ihr => cases y <;> simp [firstDifferencePaths, ihl, ihr]
  | twice e ih => cases y <;> simp [firstDifferencePaths, ih]
  | isZero e ih => cases y <;> simp [firstDifferencePaths, ih]
  | ite c yes no ihc ihy ihn =>
      cases y <;> simp [firstDifferencePaths, ihc, ihy, ihn]


/-!
## Evaluation at the first differences

At a listed path, both lookups must succeed at the same type, and the two
subexpressions found there must evaluate equally. This is a property of the
whole original trees and their automatically discovered first mismatches.
The existential `u` packages the type found at a path: a condition can have
type `.bool` even when the whole expression has type `.nat`.
-/

/-- The two trees have equal values at the subexpressions reached by `path`. -/
def Expr.EvalAgreeAt (path : List Token) (x y : Expr t) : Prop :=
  ∃ (u : Ty) (a b : Expr u),
    followTokens? path x = some ⟨u, a⟩ ∧
    followTokens? path y = some ⟨u, b⟩ ∧
    a.eval = b.eval

private theorem Expr.eval_eq_of_agree_root (x y : Expr t)
    (h : EvalAgreeAt [] x y) : x.eval = y.eval := by
  obtain ⟨u, a, b, ha, hb, he⟩ := h
  simp only [followTokens?] at ha hb
  cases ha
  cases hb
  exact he

/-- If every first syntactic difference preserves value, so does the whole
expression. Paths below a first mismatch are deliberately irrelevant. -/
theorem Expr.eval_eq_of_firstDifferencePaths_agree (x y : Expr t)
    (h : ∀ path ∈ firstDifferencePaths x y, EvalAgreeAt path x y) :
    x.eval = y.eval := by
  induction x with
  | num n =>
      cases y with
      | num m =>
          by_cases hnm : n = m
          · subst m; rfl
          · exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths, hnm]))
      | add l r =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | twice a =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c yes no =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
  | boolean b =>
      cases y with
      | boolean c =>
          by_cases hbc : b = c
          · subst c; rfl
          · exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths, hbc]))
      | isZero a =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c yes no =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
  | add l r ihl ihr =>
      cases y with
      | num m =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | twice a =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c yes no =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | add l' r' =>
          have hl : ∀ p ∈ firstDifferencePaths l l', EvalAgreeAt p l l' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.addLeft :: p) (by simp [firstDifferencePaths, hp]))
          have hr : ∀ p ∈ firstDifferencePaths r r', EvalAgreeAt p r r' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.addRight :: p) (by simp [firstDifferencePaths, hp]))
          change l.eval + r.eval = l'.eval + r'.eval
          rw [ihl l' hl, ihr r' hr]
  | twice e ih =>
      cases y with
      | num m =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | add l r =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c yes no =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | twice e' =>
          have he : ∀ p ∈ firstDifferencePaths e e', EvalAgreeAt p e e' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.twiceArg :: p) (by simp [firstDifferencePaths, hp]))
          change e.eval + e.eval = e'.eval + e'.eval
          rw [ih e' he]
  | isZero e ih =>
      cases y with
      | boolean b =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c yes no =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | isZero e' =>
          have he : ∀ p ∈ firstDifferencePaths e e', EvalAgreeAt p e e' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.isZeroArg :: p) (by simp [firstDifferencePaths, hp]))
          change (e.eval == 0) = (e'.eval == 0)
          rw [ih e' he]
  | ite c yes no ihc ihy ihn =>
      cases y with
      | num m =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | boolean b =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | add l r =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | twice e =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | isZero e =>
          exact eval_eq_of_agree_root _ _ (h [] (by simp [firstDifferencePaths]))
      | ite c' yes' no' =>
          have hc : ∀ p ∈ firstDifferencePaths c c', EvalAgreeAt p c c' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.iteCondition :: p) (by simp [firstDifferencePaths, hp]))
          have hy : ∀ p ∈ firstDifferencePaths yes yes', EvalAgreeAt p yes yes' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.iteYes :: p) (by simp [firstDifferencePaths, hp]))
          have hn : ∀ p ∈ firstDifferencePaths no no', EvalAgreeAt p no no' := by
            intro p hp
            simpa [EvalAgreeAt, followTokens?, Token.child?] using
              (h (Token.iteNo :: p) (by simp [firstDifferencePaths, hp]))
          exact eval_ite_congr (ihc c' hc) (ihy yes' hy) (ihn no' hn)

end InductiveTypesScratch
