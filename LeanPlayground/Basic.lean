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


def makeLess (n : Int) : { m : Int // m < n } :=
  ⟨n - 1, sub_one_lt n⟩

-- `{ x : Nat // 0 < x }` is sugar for `Subtype (fun x => 0 < x)`, a structure with
-- fields `val : Nat` and `property : 0 < val`. The `⟨_, _⟩` below is the anonymous
-- constructor filling in those two fields: a value, plus a *proof* it satisfies the
-- predicate. Lean checks the proof at compile time, so a `PosNat` can never wrap a
-- non-positive number — the type itself is the verification.
def PosNat := { x : Nat // 0 < x }

def two : PosNat := ⟨2, by decide⟩

-- ⟨0, by decide⟩ would fail here: `decide` can't prove `0 < 0`, so this won't compile.
-- def zero : PosNat := ⟨0, by decide⟩

-- Same proof obligation (0 < 3), but built as a direct term instead of a tactic:
-- `Nat.succ_pos 2 : 0 < Nat.succ 2`, and `Nat.succ 2` reduces to `3` definitionally.
def three : PosNat := ⟨3, Nat.succ_pos 2⟩

-- as a theorem, without the anonymous constructor
theorem four_is_positive : 0 < 4 :=
  Nat.succ_pos 3

def four : PosNat :=
  Subtype.mk 4 four_is_positive

-- directly as a record
theorem five_is_positive : 0 < 5 :=
  Nat.succ_pos 4

def five : PosNat :=
  {
    val := 5
    property := five_is_positive
  }



def makeLessPlain (n : Int) : Int :=
  n - 1

theorem makeLessPlain_spec (n : Int) : makeLessPlain n < n :=
  sub_one_lt n


-- Inductive stuff

theorem my_zero_add (n : Nat) : 0 + n = n :=
  Nat.rec
    (show 0 + 0 = 0 from rfl)
    (fun k ih =>
      show 0 + Nat.succ k = Nat.succ k from
        congrArg Nat.succ ih)
    n

#print my_zero_add
