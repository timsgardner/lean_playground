import Std.Data.HashMap

/-!
# Muffins

Identity (`MuffinId`) is separated from data (`Muffin`).

* `MuffinId` is unforgeable: its constructor is private, and new ids come only
  from a `MuffinSupply` via `MuffinId.fresh`.
* `Muffin` is plain data with structural, lawful equality. Two snapshots of the
  same muffin are related by `Muffin.SameAs`, not by `=` or `==`.
* A `Bakery` holds its current stock, keyed by identity. It does not own the
  supply; the supply lives in whatever monad the top-level program runs in.

Note: `private` scopes to the file. In a real project, put the `MuffinId`
section in its own module so that no other code can construct ids.
-/

/-! ## Identity -/

structure MuffinId where
  private mk ::
  val : Nat
  deriving DecidableEq, Hashable, Repr

instance : ToString MuffinId := ⟨fun i => s!"#{i.val}"⟩

structure MuffinSupply where
  private next : Nat

def MuffinSupply.init : MuffinSupply := ⟨0⟩

/-- The only way to obtain a new `MuffinId`. Usable in any monad carrying a `MuffinSupply`. -/
def MuffinId.fresh [Monad m] [MonadStateOf MuffinSupply m] : m MuffinId :=
  modifyGetThe MuffinSupply fun s => (⟨s.next⟩, ⟨s.next + 1⟩)

/-! ## Data -/

inductive Flavor where
  | blueberry | bran | corn
  deriving DecidableEq, Hashable, Repr

instance : ToString Flavor where
  toString
    | .blueberry => "blueberry"
    | .bran      => "bran"
    | .corn      => "corn"

structure Muffin where
  id      : MuffinId
  flavor  : Flavor
  frosted : Bool := false
  deriving DecidableEq, Hashable, Repr

instance : ToString Muffin where
  toString m := s!"{if m.frosted then "frosted " else ""}{m.flavor}{m.id}"

/-- Two snapshots denote the same muffin. A domain relation, not data equality. -/
def Muffin.SameAs (a b : Muffin) : Prop := a.id = b.id

instance : DecidableRel Muffin.SameAs :=
  fun a b => inferInstanceAs (Decidable (a.id = b.id))

def Muffin.bake [Monad m] [MonadStateOf MuffinSupply m] (f : Flavor) : m Muffin :=
  return { id := ← MuffinId.fresh, flavor := f }

def Muffin.frost (mf : Muffin) : Muffin := { mf with frosted := true }

theorem Muffin.frost_sameAs (mf : Muffin) : mf.frost.SameAs mf := rfl

/-! ## Bakeries -/

/-- A place that makes muffins and holds its current stock.
Invariant (maintained by every operation below, not yet enforced by the type):
every key of `stock` equals the `id` of the muffin stored at that key. -/
structure Bakery where
  name  : String
  stock : Std.HashMap MuffinId Muffin := {}

def Bakery.bakeBatch [Monad m] [MonadStateOf MuffinSupply m]
    (b : Bakery) (f : Flavor) (n : Nat) : m Bakery := do
  let mut stock := b.stock
  for _ in [0:n] do
    let mf ← Muffin.bake f
    stock := stock.insert mf.id mf
  pure { b with stock }

/-- Selling moves a muffin out of the bakery. -/
def Bakery.sell (b : Bakery) (f : Flavor) : Option (Muffin × Bakery) := do
  let (k, mf) ← b.stock.toList.find? (·.2.flavor == f)
  pure (mf, { b with stock := b.stock.erase k })

/-- Replaces every snapshot in stock with its frosted version. -/
def Bakery.frostAll (b : Bakery) : Bakery :=
  { b with stock := b.stock.map fun _ mf => mf.frost }

def Bakery.describe (b : Bakery) : String :=
  s!"{b.name}: {b.stock.toList.map (·.2)}"

/-! ## A program -/

def main : IO Unit := do
  let prog : StateT MuffinSupply IO Unit := do
    let mut joes  : Bakery := { name := "Joe's" }
    let mut annas : Bakery := { name := "Anna's" }
    joes  ← joes.bakeBatch .blueberry 3      -- ids 0, 1, 2
    annas ← annas.bakeBatch .bran 2          -- ids 3, 4
    annas := annas.frostAll
    IO.println joes.describe
    IO.println annas.describe
    match joes.sell .blueberry with
    | some (mf, joes') =>
        joes := joes'
        IO.println s!"sold {mf} from {joes.name}; {joes.stock.size} left"
        -- `mf` goes out of scope after this branch; nothing else retains it.
    | none =>
        IO.println s!"{joes.name} is out of blueberry"
  prog.run' .init
