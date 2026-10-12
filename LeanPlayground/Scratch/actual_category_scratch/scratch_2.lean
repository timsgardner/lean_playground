import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Check

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

section explicitVersion

-- partitions of A indexed by elements of B
def IndexedPartitions (A B : Type) : Type :=
  {F : B → Set A // ∀ a : A, ∃! b : B, a ∈ F b}

namespace IndexedPartitions

/-- the `B`-index of the cell containing `a` -/
noncomputable def index {A B: Type} (P : IndexedPartitions A B) (a : A) : B :=
  (P.2 a).exists.choose

section
variable (A B: Type)
variable (P : IndexedPartitions A B)
#check P.val
-- ↑P : B → Set A
-- same thing:
#check P.1
-- ↑P : B → Set A
#check P.index
-- index A B P : A → B
#check P.2
-- P.property : ∀ (a : A), ∃! b, a ∈ ↑P b
-- same thing:
#check P.property
-- P.property : ∀ (a : A), ∃! b, a ∈ ↑P b
-- same thing again:
#check P.prop
-- Subtype.prop P : ∀ (a : A), ∃! b, a ∈ ↑P b


#check @IndexedPartitions.index
#print IndexedPartitions

variable (cell: Set.range P.val)
#check cell
#check cell.val
-- ↑part : Set A
#check cell.property
-- part.property : ↑part ∈ Set.range ↑P
end

def Cell {A B: Type} (P: IndexedPartitions A B) : Set (Set A) := Set.range P.val

/-- look up the cell of an `A`.

The `val` slot gets the index of `a`, then pushes it back to cell so indexed.
The `prop` slot is a proof that this `val` is indeed in the range of `↑P`,
which goes from `B` to `Set A`. Here `P.val` is an implicit argument.
-/
def toCell (P: IndexedPartitions A B) (a: A) : Cell P :=
  ⟨P.val (P.index a), Set.mem_range_self (P.index a)⟩

/-- `to_cell` does indeed look up the cell of an `a` -/
theorem mem_index
    (P : IndexedPartitions A B)
    (a : A)
    : a ∈ (toCell P a).val :=
  (P.prop a).exists.choose_spec

/-- you can't be in more than one cell -/
theorem cell_mem_unique {A B : Type}
    (p: IndexedPartitions A B)
    (a: A)
    (c c': Cell p)
    (ha: a ∈ c.val)
    (ha': a ∈ c'.val)
    : c = c' := by
  obtain ⟨b, hb⟩ := c.property
  obtain ⟨b', hb'⟩ := c'.property
  rw [← hb] at ha
  rw [← hb'] at ha'
  #check p.property
  #check p.property a
  have hbb : b = b' := by
    apply (p.property a).unique
    exact ha
    exact ha'
  apply Subtype.ext
  rw [← hb, ← hb', hbb]

noncomputable def toForwardFunction {A B : Type} (P : IndexedPartitions A B) : A → B :=
  fun a => P.index a

theorem index_eq_iff
    (P: IndexedPartitions A B)
    {a: A}
    {b: B}
    : P.index a = b ↔ a ∈ P.val b := by
  constructor
  · intro h
    subst h
    #check mem_index P a
    exact mem_index P a
  · intro h
    exact (P.prop a).unique (mem_index P a) h

/-
For the injective direction, we want to show that
no two distinct IndexedPartitions A B map to the same
function A -> B via toForwardFunction.

In other words, we sant to show that if two IndexedPartitions
A B *do* map to the same function A -> B via toForwardFunction,
they are the same IndexedPartitions.
-/

theorem forward_function_bij {A B : Type}
    : Function.Bijective (@toForwardFunction A B) := by
  refine ⟨?inj, ?surj⟩
  case inj =>
    intro p p' h
    apply Subtype.ext
    funext b
    ext a
    #check congrFun h a
    have h' : p.index a = p'.index a := congrFun h a
    rw [← index_eq_iff p, ← index_eq_iff p', h']
  case surj =>
    intro f
    let p : IndexedPartitions A B :=
      ⟨fun b => {a | f a = b}, by
        intro a
        refine ⟨f a, ?mem, ?uniq⟩
        case mem => rfl
        case uniq =>
          intro b hb
          exact hb.symm⟩
    refine ⟨p, funext fun a => ?_⟩
    apply (index_eq_iff p).mpr
    rfl

end IndexedPartitions

end explicitVersion
