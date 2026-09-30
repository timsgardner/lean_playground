/-
# Toy World

Toy world for reviewing very basic Lean maneuvers without tactic-mashing.
-/

import Mathlib.Util.TermReduce
import Mathlib.Tactic.Conv

/-- A toy copy of the natural numbers. It is distinct from both `Nat` and `Y`. -/
inductive X where
  | mk (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A second, distinct toy copy of the natural numbers. -/
inductive Y where
  | mk (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! `X` and `Y` are both in bijection with `Nat`. -/

def X.toNat : X → Nat
  | .mk n => n

def Nat.toX : Nat → X
  | n => .mk n

def Y.toNat : Y → Nat
  | .mk n => n

def Nat.toY : Nat → Y
  | n => .mk n

example (n : Nat) : (Nat.toX n).toNat = n := by rfl
example (x : X) : Nat.toX x.toNat = x := by cases x <;> rfl
example (n : Nat) : (Nat.toY n).toNat = n := by rfl
example (y : Y) : Nat.toY y.toNat = y := by cases y <;> rfl

/-! A concrete function to manipulate. -/

def f : X → Y
  | .mk n => .mk (n + 1)

/-! The partition of `Y` by the parity of its underlying natural number. -/

def Y.isEven (y : Y) : Bool := y.toNat % 2 == 0
def Y.isOdd  (y : Y) : Bool := !y.isEven

example (y : Y) : y.isEven || y.isOdd = true := by
  simp [Y.isOdd]

example (y : Y) : ¬ (y.isEven = true ∧ y.isOdd = true) := by
  simp [Y.isOdd]

/-! A few basic experiments. -/

example (x : X) : (fun x' => f x') x = f x := by
  rfl

example : f (.mk 4) = .mk 5 := by
  rfl

example : (f (.mk 4)).isOdd = true := by
  rfl

/-! Beta-reduction practice: reduce the lambdas and the local `let` by hand. -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x := by
  -- Could just use simp here, but let's see what the term version looks like.
  -- These lets aren't really necessary, but they align the names for our
  -- proof.
  let g : X → Y := f
  let x': X := x
  let y : Y := g x'
  let result : Y := (fun z : Y => z) y
  let coolResult := Eq.refl result -- type: result = result
  exact coolResult

/-! We can also dispense of the tactics altogether. -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x :=
  let g : X → Y := f
  let x': X := x
  let y : Y := g x'
  let result : Y := (fun z : Y => z) y
  let coolResult := Eq.refl result -- type: result = result
  coolResult

/-! And dispense of the intermediate let bindings -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x :=
  Eq.refl (f x)


/- Now let's look at targeted beta reductions -/
section TargetedReduction

/- Let's look at conv -/

example (x : X) :
    ((fun z : Y => z) (f x), f x) = (f x, f x) := by
  conv in ((fun z : Y => z) (f x)) =>
    dsimp only


/-! ## `conv` practice

Useful navigation vocabulary includes
`conv in`, `conv_lhs`, `conv_rhs`, `arg`, `lhs`, `rhs`, and `enter`.
-/

variable (observe : Y → Nat)
variable (combine : Y → Y → Y)

-- 1. There are two nested beta redexes underneath `observe`, but reducing them
-- no longer finishes the proof. After exposing `f x`, use `h` at precisely the
-- needed occurrence.
example (x : X) (y : Y) (h : f x = y) :
    observe ((fun y : Y => y) ((fun x' : X => f x') x)) =
      observe y := by
  conv =>
    lhs
    congr
    rhs
    simp
    apply h


-- 2. Navigate to the second argument on the right-hand side and rewrite only
-- there. The hypothesis points in the opposite direction from the rewrite you
-- need.
example (a b : Y) (h : a = b) :
    combine a a = combine a b := by
  conv =>
    rhs
    congr
    {
      rfl
    }
    {
      rw [← h]
    }

-- 3. Enter beneath a lambda binder, then into the first component of the pair.
-- Beta reduction exposes `g x`, but `h x` is still needed to reach `k x`.
example (g k : X → Y) (h : ∀ x, g x = k x) :
    (fun x : X =>
      ((fun y : Y => y) (g x), (fun y : Y => y) (f x))) =
    (fun x : X => (k x, f x)) := by
  conv =>
    lhs
    intro x -- duck into the lambda
    lhs
    rhs
    apply h

-- Same example, different path
example (g k : X → Y) (h : ∀ x, g x = k x) :
    (fun x : X =>
      ((fun y : Y => y) (g x), (fun y : Y => y) (f x))) =
    (fun x : X => (k x, f x)) := by
  -- we don't really need to substitute id but it cleans things
  conv in (occs := *) (fun y => y) =>
    change id
  conv in id _ =>
    change (g x)
    apply h


-- 4. This time the expression to transform is inside a hypothesis rather than
-- the target. Normalize only the indicated lambda application in `h`, then
-- chain the resulting equality with `k`.
example (a b c : Y)
    (h : combine a ((fun y : Y => y) b) = c)
    (k : c = a) :
    combine a b = a := by
  conv at h =>
    lhs
    arg 2
    change b
  conv at h in c =>
    rw [k]
  exact h


-- 5. The occurrence to rewrite is the first argument of an inner application
-- on the right. The other occurrences should be left alone.
example (a b : Y) (h : a = b) :
    combine a (combine a b) = combine a (combine b b) := by
    conv =>
      rhs
      rhs
      arg 1
      rw [← h]

end TargetedReduction
