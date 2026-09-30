
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
