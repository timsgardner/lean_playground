import Batteries.Tactic.Init
set_option pp.fieldNotation false

/-!
# Parameters and indices

In `inductive T (p : P) : I → Sort u`, the arguments before the colon are
*parameters* and the ones after are *indices*.

* A parameter is fixed for the whole declaration. Every constructor returns
  `T p ...` with exactly that `p`.
* An index may be chosen differently by each constructor. That is how a family
  can be inhabited at some index values and empty at others.

The difference shows up in the recursor: its motive takes the indices as
arguments, but not the parameters. Many exercises below ask for a proof
written with `.rec` directly, so that you have to choose the motive yourself.
-/

namespace ParamsIndices

/-!
## Recursors and motives

### What a recursor is

For every `inductive` declaration of a type `T`, Lean generates a constant
`T.rec` called the *recursor* of `T`. The recursor is the only primitive means
of using a value of `T`. The tactics `cases` and `induction`, the `match`
syntax, and definitions by structural recursion are all elaborated into
applications of `T.rec`.

The recursor expresses one principle. Suppose a result can be produced for each
constructor of `T`, and, in the case of a constructor with arguments of type
`T`, the result may already be assumed for those arguments. Then the result can
be produced for every value of `T`.

### What the motive is

The *motive* is the result being produced, stated as a function of the value
being eliminated. If the goal is to prove `∀ n : Nat, n + 0 = n`, then the
motive is `fun n => n + 0 = n`, and the conclusion of the recursor at a
particular number `t` is `motive t`, which reduces to `t + 0 = t`.

The motive has codomain `Sort u` for an arbitrary universe `u`. When `motive t`
is a proposition, an application of the recursor is a proof by induction. When
`motive t` is a type such as `Nat`, an application of the recursor is a function
defined by recursion. One recursor serves both purposes.

(One restriction applies. If `T` itself lives in `Prop`, then the motive must
usually land in `Prop` as well. Lean allows a motive into an arbitrary
`Sort u` only for certain `Prop`-valued types, such as `Eq`, from which no
information beyond the fact of inhabitation can be extracted.)

### How the declaration determines the recursor's type

The type of `T.rec` is a single chain of arrows. Its arguments appear in the
following order, and each argument is determined by the declaration of `T` as
described.

1. **The parameters of `T`**, as implicit arguments. Every constructor uses the
   parameters unchanged, so the parameters are fixed once, before anything
   else, and every later argument is stated relative to them.

2. **The motive**, as an implicit argument. The motive takes one argument for
   each index of `T`, followed by a value of `T` at those indices, and returns a
   `Sort u`. If `T` has no indices, then the motive has type `T → Sort u`.

3. **One case for each constructor of `T`**, in the order in which the
   constructors are declared. These arguments are called *minor premises*.
   The case for a constructor `c` is a function type built in three steps:
   * The case takes every argument of `c`, in the order in which `c` takes
     those arguments.
   * Next, for every argument `x` of `c` whose type is `T` itself (possibly at
     other indices), the case takes one additional hypothesis of type
     `motive x`, with the indices of `x` supplied first. These hypotheses are
     the *induction hypotheses*. Lean places all of them after all of the
     constructor's own arguments.
   * The case returns the motive applied to the indices that `c` produces and to
     `c` applied to its arguments.

4. **The indices of `T`**, as implicit arguments.

5. **The value being eliminated**, of type `T` at those indices. This argument
   is called the *major premise*.

The result type is the motive applied to the indices and to the major premise.

### The rule applied to `Nat`

The declaration of `Nat` has no parameters and no indices, and has two
constructors.

    inductive Nat where
      | zero : Nat
      | succ (n : Nat) : Nat

* The motive has type `Nat → Sort u`, because `Nat` has no indices.
* The constructor `zero` takes no arguments, so the case for `zero` takes no
  arguments and no induction hypotheses. The case for `zero` is simply a value
  of type `motive zero`.
* The constructor `succ` takes one argument `n`, and the type of `n` is `Nat`.
  The case for `succ` therefore takes `n`, then one induction hypothesis of type
  `motive n`, and returns `motive (succ n)`.

The result is exactly the type that `#check @Nat.rec` prints:

    Nat.rec : {motive : Nat → Sort u} →
      motive Nat.zero →                                -- case for `zero`
      ((n : Nat) → motive n → motive (Nat.succ n)) →   -- case for `succ`
      (t : Nat) → motive t                             -- major premise

### How changes to the declaration change the recursor

* A constructor argument whose type is not `T` contributes an argument to the
  case but no induction hypothesis. In
  `| node : Tree → Nat → Tree → Tree`, the case for `node` takes a left subtree
  `l`, a number `k`, and a right subtree `r`, followed by the two induction
  hypotheses `motive l` and `motive r`. The number `k` receives no induction
  hypothesis.
* A constructor with two arguments of type `T` produces two induction
  hypotheses, as `node` shows. A constructor with no arguments of type `T`
  produces none, so its case is a base case.
* Adding a constructor adds a case. Removing every constructor leaves no cases,
  and the recursor then produces `motive t` from `t` alone. This is why a value
  of an empty type proves anything.
* Adding an index adds an argument to the motive. For
  `inductive Vec (α : Type) : Nat → Type`, the motive has type
  `(n : Nat) → Vec α n → Sort u`. The case for `nil : Vec α 0` must produce
  `motive 0 nil`. The case for `cons` must produce `motive (n + 1) (cons a n v)`,
  and the induction hypothesis for `v : Vec α n` has type `motive n v`.
* Adding a parameter adds an implicit argument before the motive and leaves the
  motive's type unchanged. For `Vec`, the type `α` is fixed before the motive
  is chosen, so the motive is never asked to vary `α`.

### How the recursor computes

The recursor applied to a constructor reduces to the case for that constructor,
with the induction hypotheses replaced by recursive applications of the
recursor. For `Nat`, writing `z` for the case for `zero` and `s` for the case
for `succ`:

    Nat.rec z s Nat.zero      ≡  z
    Nat.rec z s (Nat.succ n)  ≡  s n (Nat.rec z s n)

These two equations are the definition of the recursor's behaviour. Lean
applies them whenever it evaluates an expression or checks that two terms are
definitionally equal.

#### A function written with the recursor

Consider the function that doubles a number, written first with `match`:

    def double : Nat → Nat
      | 0     => 0
      | n + 1 => double n + 2

The same function written as a direct application of the recursor is
`doubleRec` below. The motive is `fun _ => Nat`, because the result is a number
regardless of the input. Each `match` arm becomes one case:

* The arm `| 0 => 0` becomes the case for `zero`, so `z` is `0`.
* The arm `| n + 1 => double n + 2` becomes the case for `succ`, so `s` is
  `fun n ih => ih + 2`. The recursive call `double n` in the `match` version
  does not appear in `s`. The induction hypothesis `ih` stands in its place.

The recursor, not the case `s`, performs the recursion. The case `s` describes
only a single step: given `n` and the result `ih` for `n`, the case `s` returns
the result for `n + 1`.

#### Evaluating the function

The computation of `doubleRec 2` applies the two equations repeatedly. In the
following trace, `2` is written `succ (succ zero)`.

    doubleRec 2
      ≡ Nat.rec 0 s (succ (succ zero))
      ≡ s (succ zero) (Nat.rec 0 s (succ zero))           -- succ equation
      ≡ (Nat.rec 0 s (succ zero)) + 2                     -- unfold s
      ≡ (s zero (Nat.rec 0 s zero)) + 2                   -- succ equation
      ≡ ((Nat.rec 0 s zero) + 2) + 2                      -- unfold s
      ≡ (0 + 2) + 2                                       -- zero equation
      ≡ 4

At each step that uses the `succ` equation, the argument `ih` of `s` is
instantiated with the recursor applied to the predecessor. This is the
recursive call that the `match` version wrote explicitly.

#### A proof written with the recursor

The same structure governs proofs. In `doubleRec_eq` below, the motive is
`fun n => doubleRec n = n + n`, so the induction hypothesis `ih` in the case
for `succ` has type `doubleRec n = n + n`. The case for `succ` must produce
`doubleRec (n + 1) = (n + 1) + (n + 1)`. By the `succ` equation, the left side
`doubleRec (n + 1)` reduces to `doubleRec n + 2`, and the goal then follows from
`ih` by arithmetic. The `induction` tactic produces exactly this case: the
hypothesis that the tactic names `ih` is the argument `ih` of the case for
`succ`.
-/

def doubleRec : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 2)

-- Lean evaluates `doubleRec 3` by the two equations, so `rfl` suffices.
example : doubleRec 3 = 6 := rfl

theorem doubleRec_eq (n : Nat) : doubleRec n = n + n :=
  Nat.rec (motive := fun n => doubleRec n = n + n)
    rfl
    (fun n ih => by
      show doubleRec n + 2 = (n + 1) + (n + 1)  -- the `succ` equation, by `show`
      omega)
    n

/-!

### Why parameters and indices behave differently

A single application of the recursor must handle every constructor at once.
Different constructors may produce different indices, as `nil` produces `0`
while `cons` produces `n + 1`. The motive therefore has to be stated for an
arbitrary index, and so the motive takes the indices as arguments. Every
constructor produces the same parameters, so the parameters can be fixed before
the motive is chosen, and the motive does not take the parameters as arguments.

### Choosing the motive

Lean usually infers the motive. The tactics `cases` and `induction` construct
the motive from the goal by replacing every occurrence of the major premise,
and of its indices, with bound variables. When the goal mentions a specific
index such as `5`, the inferred motive can fail to be useful, and the motive
must instead be written explicitly with `(motive := ...)`.
-/

/-!
## The same shape, two ways

Both types have one constructor with no arguments. The only difference is
where the `Nat` sits.
-/

inductive Tagged (n : Nat) : Type where
  | mk : Tagged n

inductive AtZero : Nat → Type where
  | mk : AtZero 0

-- Before running these, predict each motive's type. Which one takes a `Nat`?
#check @Tagged.rec
#check @AtZero.rec

-- 1. A parameter can't make any instance empty.
example (n : Nat) : Tagged n := by
  exact Tagged.mk

-- 2. An index can.
example : AtZero 5 → False := fun h =>
  AtZero.rec (motive := fun n _ => n = 5 → False) (fun h0 => nomatch h0) h rfl

-- 3. Splitting on a value of an indexed type tells you the index.
-- Prove this once with `cases`, then once with `AtZero.rec`.
example (n : Nat) (h : AtZero n) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases h

example (n : Nat) (h : AtZero n) : n = 0 := by
  cases h
  rfl

-- 4. Splitting on a parameterized value tells you nothing about the
-- parameter. Prove that the claim corresponding to 3 is false for `Tagged`.
example : ¬ ∀ n, Tagged n → n = 0 := sorry

/-!
## Parameters must not vary

Uncomment the declaration below and read the error message.
-/

-- inductive Bad (n : Nat) : Type where
--   | mk : Bad 0

/-!
## Automatic promotion

When an argument after the colon is the same variable in every constructor's
result type, Lean silently turns it into a parameter. Before running each
`#check`, predict which arguments the motive takes.
-/

inductive Same {α : Type} : α → α → Prop where
  | refl (a : α) : Same a a

inductive Step : Nat → Nat → Prop where
  | next (a : Nat) : Step a (a + 1)

inductive Diag : Nat → Nat → Prop where
  | zero : Diag 0 0
  | succ : Diag a b → Diag (a + 1) (b + 1)

#check @Same.rec
#check @Step.rec
#check @Diag.rec

/-!
## Two equalities

`EqP` is Lean's `Eq`: the left side is a parameter and the right side is an
index. `EqI` has both sides as indices. Without the `set_option`, Lean would
promote the left side and `EqI` would turn into `EqP`.
-/

inductive EqP {α : Type} (a : α) : α → Prop where
  | refl : EqP a a

set_option inductive.autoPromoteIndices false in
inductive EqI {α : Type} : α → α → Prop where
  | refl (a : α) : EqI a a

-- Compare the two motives, and compare the arguments that `refl` takes in
-- each one.
#check @EqP.rec
#check @EqI.rec

variable {α : Type}

/-
Use only `.rec` and `refl` in this section: no `cases`, `match`, or `rw`.
Write each `.rec` with an explicit `(motive := fun ... => ...)`.
-/

-- 5. Symmetry. Which side of `h` stays fixed, and what does the motive
-- receive?
theorem EqP.symm' {a b : α} (h : EqP a b) : EqP b a := sorry

theorem EqI.symm' {a b : α} (h : EqI a b) : EqI b a := sorry

-- 6. Substitution. With `EqP`, the motive can just be `P`. With `EqI`, the
-- motive must hold for every pair of endpoints, so the hypothesis `ha` about
-- the left endpoint has to become part of the motive.
theorem EqP.subst' {P : α → Prop} {a b : α} (h : EqP a b) (ha : P a) : P b :=
  sorry

theorem EqI.subst' {P : α → Prop} {a b : α} (h : EqI a b) (ha : P a) : P b :=
  sorry

-- 7. Transitivity. Do the recursion on `h₂`. The `EqI` version needs the same
-- trick as 6.
theorem EqP.trans' {a b c : α} (h₁ : EqP a b) (h₂ : EqP b c) : EqP a c :=
  sorry

theorem EqI.trans' {a b c : α} (h₁ : EqI a b) (h₂ : EqI b c) : EqI a c :=
  sorry

-- 8. The two equalities prove the same statements.
theorem EqP.toEqI {a b : α} (h : EqP a b) : EqI a b := sorry

theorem EqI.toEqP {a b : α} (h : EqI a b) : EqP a b := sorry

/-!
## Where `cases` fails

`cases` has to solve the index equation that a constructor imposes. When both
sides of an equation are compound terms, there's no variable to substitute,
and it gives up. The recursor has no such problem, because the left side is a
parameter and can be any term.
-/

-- 9. Try `cases h` first and read the error. Then prove it with `EqP.rec`.
example (f g : Nat → Nat) (x y : Nat) (P : Nat → Prop)
    (h : EqP (f x) (g y)) (hf : P (f x)) : P (g y) := sorry

-- 10. The same situation with Lean's own `Eq`. Try `cases h`, then use
-- `Eq.rec` the same way as in 9. (`rw [← h]` and `h ▸ hf` also work, and both
-- are built on `Eq.rec`.)
example (f g : Nat → Nat) (x y : Nat) (P : Nat → Prop)
    (h : f x = g y) (hf : P (f x)) : P (g y) := sorry

end ParamsIndices
