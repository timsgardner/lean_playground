import Mathlib

#check Even
#check Odd
#check Even 4
#check Odd 5

def hello := "world"


#eval String.append "Hello " "Lean!"

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

#check add1


def joinStringsWith (s1: String) (s2: String) (s3: String): String :=
  String.append (String.append s2 s1) s3


structure Point where
  x : Float
  y : Float


def origin : Point := { x := 0.0, y := 0.0 }


def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }


def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))


def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }


structure PPoint (α : Type) where
  x : α
  y : α


def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }


def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }


#check replaceX natOrigin


inductive Sign where
  | pos
  | neg


def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)


def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _y :: ys => Nat.succ (length α ys)


theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide


theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a


def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by decide)


theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp


variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩


-- def makeLess (n : Int) : { m : Int // m < n } :=
--   ⟨n - 1, Int.sub_one_lt n⟩
