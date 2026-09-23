import Mathlib

namespace DependentTypesKindergarten

/-!
# Dependent Types Kindergarten

A scratch file for experimenting with:
- `Type` as a term
- dependent functions (`(x : α) → β x`)
- sigma types (`Sigma`)
- subtypes
- equality and transport
- heterogeneous collections
-/

-- === MARKER: TYPES_AS_VALUES START ===

#check Type
#check Nat
#check Bool
#check Empty

def someTypes : Array Type :=
  #[Nat, Bool, String, Empty]

#check someTypes

-- === MARKER: TYPES_AS_VALUES END ===


-- === MARKER: DEPENDENT_FUNCTIONS START ===

/-- A family of types indexed by a natural number. -/
def VecType (n : Nat) : Type :=
  Fin n → Bool

#check VecType
#check VecType 3

/-- The result type depends on `n`. -/
def makeDefault (n : Nat) : VecType n :=
  fun _ => false

-- === MARKER: DEPENDENT_FUNCTIONS END ===


-- === MARKER: SIGMA START ===

/--
An arbitrary type packaged together with a value of that type.
-/
def AnyValue : Type :=
  Sigma fun T : Type => T

def aNat : AnyValue :=
  ⟨Nat, 37⟩

def aBool : AnyValue :=
  ⟨Bool, true⟩

def aString : AnyValue :=
  ⟨String, "hello"⟩

def mixed : Array AnyValue :=
  #[aNat, aBool, aString]

#check aNat
#check mixed

/-- Unpack a sigma and recover the dependent relationship. -/
def forgetValue (x : AnyValue) : Type :=
  match x with
  | ⟨T, _⟩ => T

-- Try inspecting these in the infoview:
#check Sigma
#check Sigma.fst
#check Sigma.snd

-- === MARKER: SIGMA END ===


-- === MARKER: INDEXED_SIGMA START ===

/--
Package a length together with an array known to have that length.

For now we use `Fin n → α` as a simple vector representation.
-/
def SomeVec (α : Type) : Type :=
  Sigma fun n : Nat => Fin n → α

def threeBools : SomeVec Bool :=
  ⟨3, fun
    | ⟨0, _⟩ => true
    | ⟨1, _⟩ => false
    | ⟨2, _⟩ => true⟩

-- === MARKER: INDEXED_SIGMA END ===


-- === MARKER: SUBTYPES START ===

def PositiveNat : Type :=
  {n : Nat // 0 < n}

def five : PositiveNat :=
  ⟨5, by decide⟩

#check five.val
#check five.property

-- Compare:
--   Sigma fun n : Nat => ...
-- with:
--   {n : Nat // ...}

-- === MARKER: SUBTYPES END ===


-- === MARKER: TRANSPORT START ===

/--
If `A = B`, a value of `A` can be transported to a value of `B`.
-/
def transport
    {A B : Type}
    (h : A = B)
    (x : A) : B :=
  h ▸ x

#check Eq.subst
#check Eq.rec
#check cast

-- === MARKER: TRANSPORT END ===


-- === MARKER: EXERCISES START ===

-- Exercise 1:
-- Write a function that extracts the type from an `AnyValue`.

-- Exercise 2:
-- Construct:
--
--   Sigma fun n : Nat => Fin n
--
-- What information does one value of this type contain?

-- Exercise 3:
-- Make a sigma whose second component is `Fin n → String`.

-- Exercise 4:
-- Pattern-match on a sigma and see exactly what Lean puts
-- into the local context.

-- Exercise 5:
-- Compare `Sigma fun n : Nat => Fin n` with
-- `Subtype fun n : Nat => n > 0`.

-- === MARKER: EXERCISES END ===

end DependentTypesKindergarten
