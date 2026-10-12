import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic.Check

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

namespace explicitVersion

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

/-! ### Bridge to `Setoid`

Forget the labels: `a ~ a'` iff they lie in the same cell. -/

/-- the equivalence relation "lies in the same cell" -/
noncomputable def toSetoid(P : IndexedPartition A B) : Setoid A :=
  Setoid.ker P.index

theorem toSetoid_rel_iff
    (P : IndexedPartition A B)
    (a a' : A)
    : (toSetoid P) a a' ↔ P.index a = P.index a' := by
  apply Setoid.ker_def

/-- the unlabelled partition is the labelled one minus the empty cell -/
theorem classes_toSetoid
    (P : IndexedPartition A B)
    : (toSetoid P).classes = Cell P \ {∅} := by
  ext sA
  have helper : ∀ y : A, {x | toSetoid P x y} = P.lookupCell (P.index y) := by
    intro a
    ext a'
    rw [@Set.mem_setOf_eq, toSetoid_rel_iff, (index_eq_iff P)]
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := h
    simp
    constructor
    · rw [helper]
      apply Set.mem_range_self
    · intro hempty
      let bla := Setoid.refl' (toSetoid P) y
      rw [(helper y)] at hempty
      set c := P.lookupCell (P.index y)
      have h : y ∈ c := by
        apply mem_index
      rw [hempty] at h
      exact h
  · intro h
    simp at h
    #check Set.mem_singleton_iff
    obtain ⟨⟨b, rfl⟩, hne⟩ := h
    rw [← Set.mem_singleton_iff] at hne
    change P.lookupCell b ≠ ∅ at hne
    -- get a point
    rw [← Set.nonempty_iff_ne_empty] at hne
    obtain ⟨y, hy⟩ := hne
    #check index_eq_iff
    let hb := (index_eq_iff P).mpr hy
    have hmem := Setoid.mem_classes (toSetoid P) y
    rw [helper, hb] at hmem
    exact hmem

/-- if no cell is empty, the cells form a `Setoid.IsPartition` -/
theorem isPartition_cell
    (P : IndexedPartition A B)
    (hne : ∀ b, (P.lookupCell b).Nonempty)
    : Setoid.IsPartition (Cell P) := by
  unfold Cell
  unfold Setoid.IsPartition
  constructor
  · rintro ⟨b, hb⟩
    have blort := hne b
    exact (Set.nonempty_iff_ne_empty.mp blort) hb
  · intro a
    conv =>
      congr
      intro sA
    refine ⟨?set_a, ?case_2, ?case_3⟩
    case set_a =>
      exact P.lookupCell (P.index a)
    case case_2 =>
      simp
      apply mem_index
    case case_3 =>
      simp
      intro b h
      have h1 : a ∈ P.lookupCell (P.index a) := mem_index P a
      have h2 : b = (P.index a) := by
        apply (P.partition_property a).unique
        exact h
        exact h1
      rw [h2]

/-- the cells cover `A` -/
theorem sUnion_cell
    (P : IndexedPartition A B)
    : ⋃₀ Cell P = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro a
  apply Set.mem_sUnion.mpr
  refine ⟨?sA, ?_⟩
  · exact P.lookupCell (P.index a)
  · constructor
    · exact Set.mem_range_self (P.index a)
    · exact (index_eq_iff P).mp rfl


end IndexedPartition

end explicitVersion

/-! ## The same development, restructured

Everything above, organised around one lemma (`index_eq_iff`) and the
equivalence `IndexedPartition A B ≃ (A → B)`. Theorem names match the
explicit version where they correspond, so the two can be compared side by side. -/

namespace elegantVersion

/-- a partition of `A` into cells indexed by elements of `B`.

`@[ext]` generates `IndexedPartition.ext : x.lookupCell = y.lookupCell → x = y`;
`partition_property` is a proof, so it adds no condition (proof irrelevance). -/
@[ext]
structure IndexedPartition (A B : Type) where
  lookupCell : B → Set A
  partition_property : ∀ a, ∃! b, a ∈ lookupCell b

namespace IndexedPartition

variable {A B : Type} (P : IndexedPartition A B)

/-- the `B`-index of the cell containing `a` -/
noncomputable def index (a : A) : B :=
  (P.partition_property a).exists.choose

theorem mem_lookupCell_index (a : A) : a ∈ P.lookupCell (P.index a) :=
  (P.partition_property a).exists.choose_spec

/-- The key lemma: `index` and `lookupCell` determine each other.
Everything below is a consequence of this. -/
@[simp] theorem index_eq_iff {a : A} {b : B} : P.index a = b ↔ a ∈ P.lookupCell b := by
  have ha : a ∈ P.lookupCell (P.index a) := P.mem_lookupCell_index a
  constructor
  · -- `a` is in the cell at its own index, and that index is `b`
    -- ⊢ a ∈ P.lookupCell b
    intro h  -- h : P.index a = b
    rw [← h] -- ⊢ a ∈ P.lookupCell (P.index a)
    exact ha
  · -- `a` is in cell `b` and in cell `P.index a`; cells don't overlap, so the indices agree
    -- ⊢ a ∈ P.lookupCell b → P.index a = b
    intro hb -- hb : a ∈ P.lookupCell b
    -- ⊢ P.index a = b
    exact (P.partition_property a).unique ha hb

/-! ### Indexed partitions are functions -/

/-- The partition of `A` into the fibers of `f`: cell `b` is `{a | f a = b}`.
  We'll use this as invFun in the bijection. -/
def ofFun (f : A → B) : IndexedPartition A B where
  lookupCell b := f ⁻¹' {b}
  partition_property a := by
    -- ⊢ ∃! b, a ∈ f ⁻¹' {b}
    refine ⟨f a, ?mem, ?uniq⟩
    · -- ⊢ a ∈ f ⁻¹' {f a}, i.e. f a = f a
      rfl
    · -- ⊢ ∀ b, a ∈ f ⁻¹' {b} → b = f a
      intro b hb -- hb : a ∈ f ⁻¹' {b}, i.e. f a = b
      exact hb.symm

/-- `B`-indexed partitions of `A` are the same thing as functions `A → B`:
forward, send `a` to the index of its cell; backward, take fibers. -/
noncomputable def equivFun : IndexedPartition A B ≃ (A → B) where
  toFun P := P.index
  invFun f := ofFun f
  left_inv P := by
    dsimp only
    -- ⊢ ofFun P.index = P
    ext b a
    -- ⊢ a ∈ (ofFun P.index).lookupCell b ↔ a ∈ P.lookupCell b
    -- the left side unfolds to `P.index a = b`, so this is `index_eq_iff`
    exact P.index_eq_iff
  right_inv f := by
    dsimp only
    -- ⊢ (ofFun f).index = f
    funext a
    -- ⊢ (ofFun f).index a = f a
    rw [index_eq_iff]
    -- ⊢ a ∈ (ofFun f).lookupCell (f a), which unfolds to `f a = f a`
    rfl

theorem forward_function_bij : Function.Bijective (@equivFun A B) :=
  equivFun.bijective

/-! ### Cells -/

def Cell : Set (Set A) := Set.range P.lookupCell

/-- the cell containing `a` -/
def toCell (a : A) : P.Cell := ⟨P.lookupCell (P.index a), a |> P.index |> Set.mem_range_self⟩

theorem mem_toCell (a : A) : a ∈ (P.toCell a).val := P.mem_lookupCell_index a

/-- you can't be in more than one cell -/
theorem cell_mem_unique {a : A} {c c' : P.Cell} (ha : a ∈ c.val) (ha' : a ∈ c'.val) :
    c = c' := by
  obtain ⟨_, b, rfl⟩ := c
  obtain ⟨_, b', rfl⟩ := c'
  obtain rfl := (P.partition_property a).unique ha ha'
  rfl

/-- the cells cover `A` -/
theorem sUnion_cell : ⋃₀ P.Cell = Set.univ :=
  Set.eq_univ_of_forall fun a => ⟨_, ⟨P.index a, rfl⟩, P.mem_lookupCell_index a⟩

/-! ### Bridge to `Setoid`

Forget the labels: `a ~ a'` iff they lie in the same cell. -/

noncomputable def toSetoid : Setoid A := Setoid.ker P.index

/-- the equivalence class of `a` is its cell -/
theorem setOf_rel (a : A) : {x | P.toSetoid x a} = P.lookupCell (P.index a) := by
  ext; exact P.index_eq_iff

/-- the unlabelled partition is the labelled one minus the empty cell -/
theorem classes_toSetoid : P.toSetoid.classes = P.Cell \ {∅} := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    rw [setOf_rel]
    exact ⟨⟨_, rfl⟩, Set.nonempty_iff_ne_empty.mp ⟨a, P.mem_lookupCell_index a⟩⟩
  · rintro ⟨⟨b, rfl⟩, hne⟩
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    exact ⟨a, by rw [setOf_rel, (P.index_eq_iff).mpr ha]⟩

/-- if no cell is empty, the cells form a `Setoid.IsPartition` -/
theorem isPartition_cell (hne : ∀ b, (P.lookupCell b).Nonempty) :
    Setoid.IsPartition P.Cell := by
  have : P.Cell \ {∅} = P.Cell :=
    Set.sdiff_singleton_eq_self fun ⟨b, hb⟩ => (hne b).ne_empty hb
  rw [← this, ← classes_toSetoid]
  exact Setoid.isPartition_classes _

end IndexedPartition

end elegantVersion
