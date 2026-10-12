import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Check

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

section explicitVersion

/-- a partition of `A` into cells indexed by elements of `B`.

`@[ext]` generates the equality conditions
* `IndexedPartition.ext : x.lookupCell = y.lookupCell → x = y`
* `IndexedPartition.ext_iff : x = y ↔ x.lookupCell = y.lookupCell`

Two partitions are equal iff their `lookupCell` functions are equal;
`partition_property` is a proof, so it adds no condition (proof irrelevance). -/
@[ext]
structure IndexedPartition (A B: Type) where
  lookupCell : B → Set A
  partition_property: ∀ a, ∃! b, a ∈ lookupCell b

namespace IndexedPartition

/-- the `B`-index of the cell containing `a` -/
noncomputable def index {A B: Type} (P : IndexedPartition A B) (a : A) : B :=
  (P.partition_property a).exists.choose

section
variable (A B: Type)
variable (P : IndexedPartition A B)
#check P.lookupCell
-- P.lookupCell : B → Set A
-- same thing (first field):
#check P.1
-- P.lookupCell : B → Set A
#check P.index
-- P.index : A → B
#check P.partition_property
-- P.partition_property : ∀ (a : A), ∃! b, a ∈ P.lookupCell b
-- same thing (second field):
#check P.2


#check @IndexedPartition.index
#print IndexedPartition

variable (cell: Set.range P.lookupCell)
#check cell
-- cell : (Set.range P.lookupCell).Elem
#check cell.val
-- cell.val : Set A
#check cell.property
-- cell.property : cell.val ∈ Set.range P.lookupCell
end

def Cell {A B: Type} (P: IndexedPartition A B) : Set (Set A) := Set.range P.lookupCell

/--
The cell containing `a`, as an element of `Cell P`. This is a subtype instance
(element of `Set (Set A)`), so it is constructed as a `⟨val, prop⟩` pair.

The `val` is `P.lookupCell (P.index a)`: first find the index of the cell
containing `a`, then look that cell up up that index. The `prop` is a proof that
this set is in the range of `P.lookupCell`. -/
def toCell (P: IndexedPartition A B) (a: A) : Cell P :=
  ⟨P.lookupCell (P.index a), Set.mem_range_self (P.index a)⟩

/-- `to_cell` does indeed look up the cell of an `a` -/
theorem mem_index
    (P : IndexedPartition A B)
    (a : A)
    : a ∈ (toCell P a).val :=
  (P.partition_property a).exists.choose_spec

/-- you can't be in more than one cell -/
theorem cell_mem_unique {A B : Type}
    (p: IndexedPartition A B)
    (a: A)
    (c c': Cell p)
    (ha: a ∈ c.val)
    (ha': a ∈ c'.val)
    : c = c' := by
  obtain ⟨b, hb⟩ := c.property
  obtain ⟨b', hb'⟩ := c'.property
  rw [← hb] at ha
  rw [← hb'] at ha'
  have hbb : b = b' := by
    apply (p.partition_property a).unique
    exact ha
    exact ha'
  apply Subtype.ext
  rw [← hb, ← hb', hbb]

/-- `` -/


noncomputable def toForwardFunction {A B : Type} (P : IndexedPartition A B) : A → B :=
  fun a => P.index a

theorem index_eq_iff
    (P: IndexedPartition A B)
    {a: A}
    {b: B}
    : P.index a = b ↔ a ∈ P.lookupCell b := by
  constructor
  · intro h
    subst h
    exact mem_index P a
  · intro h
    exact (P.partition_property a).unique (mem_index P a) h

/-
For the injective direction, we want to show that
no two distinct IndexedPartition A B map to the same
function A -> B via toForwardFunction.

In other words, we sant to show that if two IndexedPartition
A B *do* map to the same function A -> B via toForwardFunction,
they are the same IndexedPartition.
-/

theorem forward_function_bij {A B : Type}
    : Function.Bijective (@toForwardFunction A B) := by
  refine ⟨?inj, ?surj⟩
  case inj =>
    intro p p' h
    apply IndexedPartition.ext
    funext b
    ext a
    have h' : p.index a = p'.index a := congrFun h a
    rw [← index_eq_iff p, ← index_eq_iff p', h']
  case surj =>
    intro f
    let p : IndexedPartition A B :=
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

end IndexedPartition

end explicitVersion
