import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Check

set_option pp.deepTerms true
set_option pp.proofs true

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

/-- look up the cell of an `A`-/
def to_cell (P: IndexedPartitions A B) (a: A) : Cell P :=
  ⟨P.val (P.index a), Set.mem_range_self (P.index a)⟩

/-- `to_cell` does indeed look up the cell of an `a` -/
theorem mem_index (P : IndexedPartitions A B) (a : A) : a ∈ (to_cell P a).val :=
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
  fun a => (P.property a).exists.choose

theorem mem_forward {A B : Type}
    (P: IndexedPartitions A B)
    (a: A)
    : a ∈ P.val (toForwardFunction P a) := by
  unfold toForwardFunction
  exact (P.property a).exists.choose_spec

theorem forward_eq {A B : Type} (P : IndexedPartitions A B) {a : A} {b : B}
    (h : a ∈ P.val b) : toForwardFunction P a = b :=
  (P.property a).unique (mem_forward P a) h

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
    refine ⟨?p_to_p', ?p'_to_p⟩
    case p_to_p' =>
      intro ha
      have blort : a ∈ p'.val (p'.toForwardFunction a) := by
        apply mem_forward




    case p'_to_p =>
  case surj =>
    sorry





end IndexedPartitions




noncomputable example : (A → B) ≃ IndexedPartitions A B := by
  let toFun : (f: A → B) → IndexedPartitions A B :=
    fun f => by
      refine ⟨(fun b =>  f⁻¹' {b}), ?_⟩
      intro a
      refine ⟨?_, ?_⟩
      · apply f
        exact a
      · simp
        refine ⟨by trivial, ?_⟩
        intro b h
        exact h.symm
  let invFun : (IndexedPartitions A B) → (A → B) :=
    fun ips => by
      intro a
      have h : ∃! (b : B), a ∈ (ips.1 b) := ips.2 a
      exact h.exists.choose

  -- refine
  --   { toFun := toFun
  --     invFun := ?invFun
  --     left_inv := ?left_inv
  --     right_inv := ?right_inv }
  -- case invFun =>
  --   intro a
  --   let F : B → Set A := a.1
  --   let ah : ∀ a' : A, ∃! b : B, a' ∈ F b := a.2
  --   exact fun a' => (ah a').choose
  -- case left_inv =>

end explicitVersion
