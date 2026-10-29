/-
# Benchmarks: a scalable family of shapes

Grids give a family of diagrams whose size is controlled by one number, which
makes them a convenient stress test for the decision procedures and the chase
search. They are a test load, not a design target.

`Grid m n` has the vertices `(i, j)` with `i < m`, `j < n`, an arrow right from
`(i, j)` to `(i, j + 1)` and an arrow down from `(i, j)` to `(i + 1, j)`. Every
unit square is a face. The definitions ending in `Bench` are the workloads that
`scripts/diagram_bench.py` times; each is stated for a grid with `k` squares on a
side.
-/

import LeanPlayground.diagrams.decide
import LeanPlayground.diagrams.search

open CategoryTheory Quiver

namespace Diagrams.Bench

/-- The direction of a grid arrow. -/
inductive Dir | right | down
  deriving DecidableEq

/-- The vertices of an `m × n` grid. -/
def Grid (m n : ℕ) : Type := Fin m × Fin n

variable {m n : ℕ}

instance : DecidableEq (Grid m n) := inferInstanceAs (DecidableEq (Fin m × Fin n))
instance : Fintype (Grid m n) := inferInstanceAs (Fintype (Fin m × Fin n))

/-- The vertex one step in direction `d`, if it is in the grid. -/
def next : Dir → Grid m n → Option (Grid m n)
  | .right, a => if h : a.2.val + 1 < n then some (a.1, ⟨a.2.val + 1, h⟩) else none
  | .down, a => if h : a.1.val + 1 < m then some (⟨a.1.val + 1, h⟩, a.2) else none

instance : Quiver (Grid m n) := ⟨fun a b => {d : Dir // next d a = some b}⟩

instance (a b : Grid m n) : DecidableEq (a ⟶ b) :=
  inferInstanceAs (DecidableEq {d : Dir // next d a = some b})

/-- All vertices, row by row. -/
def vertices (m n : ℕ) : List (Grid m n) :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => (i, j)

theorem mem_vertices (a : Grid m n) : a ∈ vertices m n := by
  obtain ⟨i, j⟩ := a
  exact List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩⟩

/-- The arrow out of `a` in direction `d`, if there is one. -/
def arrowsFrom (a : Grid m n) (d : Dir) : List (Total (Grid m n)) :=
  match h : next d a with
  | some b => [⟨a, b, ⟨d, h⟩⟩]
  | none => []

theorem mem_arrowsFrom {a b : Grid m n} {d : Dir} (h : next d a = some b) :
    (⟨a, b, ⟨d, h⟩⟩ : Total (Grid m n)) ∈ arrowsFrom a d := by
  unfold arrowsFrom
  split
  · rename_i b' h'
    obtain rfl : b = b' := Option.some_inj.1 (h.symm.trans h')
    exact List.mem_singleton_self _
  · rename_i h'
    exact absurd (h.symm.trans h') (by simp)

instance : FinShape (Grid m n) where
  vertices := vertices m n
  mem_vertices := mem_vertices
  arrows := (vertices m n).flatMap fun a => arrowsFrom a .right ++ arrowsFrom a .down
  mem_arrows := by
    rintro ⟨a, b, d, h⟩
    simp only [List.mem_flatMap, List.mem_append]
    refine ⟨a, mem_vertices a, ?_⟩
    cases d
    · exact Or.inl (mem_arrowsFrom h)
    · exact Or.inr (mem_arrowsFrom h)

/-! ## Faces -/

/-- A unit square, named by its top-left corner. -/
structure Cell (m n : ℕ) where
  /-- The row of the top-left corner. -/
  i : ℕ
  /-- The column of the top-left corner. -/
  j : ℕ
  hi : i + 1 < m
  hj : j + 1 < n

/-- The unit square at `c`: right then down, against down then right. -/
def square (c : Cell m n) : Face (Grid m n) :=
  let a : Grid m n := (⟨c.i, by have := c.hi; omega⟩, ⟨c.j, by have := c.hj; omega⟩)
  let r : Grid m n := (⟨c.i, by have := c.hi; omega⟩, ⟨c.j + 1, c.hj⟩)
  let d : Grid m n := (⟨c.i + 1, c.hi⟩, ⟨c.j, by have := c.hj; omega⟩)
  let x : Grid m n := (⟨c.i + 1, c.hi⟩, ⟨c.j + 1, c.hj⟩)
  have ar : next .right a = some r := by simp [a, r, next, c.hj]
  have rx : next .down r = some x := by simp [r, x, next, c.hi]
  have ad : next .down a = some d := by simp [a, d, next, c.hi]
  have dx : next .right d = some x := by simp [d, x, next, c.hj]
  ⟨a, x, (Quiver.Hom.toPath (V := Grid m n) (⟨_, ar⟩ : a ⟶ r)).comp
      (Quiver.Hom.toPath (V := Grid m n) (⟨_, rx⟩ : r ⟶ x)),
    (Quiver.Hom.toPath (V := Grid m n) (⟨_, ad⟩ : a ⟶ d)).comp
      (Quiver.Hom.toPath (V := Grid m n) (⟨_, dx⟩ : d ⟶ x))⟩

/-- All unit squares. -/
def cells (m n : ℕ) : List (Cell m n) :=
  (List.range m).flatMap fun i => (List.range n).filterMap fun j =>
    if h : i + 1 < m ∧ j + 1 < n then some ⟨i, j, h.1, h.2⟩ else none

/-! ## Walks -/

/-- The edges of the walk from `a` in the directions `ds`, stopping at the edge of
the grid. -/
def walk : Grid m n → List Dir → List (Total (Grid m n))
  | _, [] => []
  | a, d :: ds =>
    match h : next d a with
    | some b => ⟨a, b, ⟨d, h⟩⟩ :: walk b ds
    | none => []

/-! ## Workloads, for a grid with `k` squares on a side -/

/-- The top-left corner. -/
def origin (k : ℕ) : Grid (k + 1) (k + 1) := (0, 0)

/-- The bottom-right corner. -/
def far (k : ℕ) : Grid (k + 1) (k + 1) := (Fin.last k, Fin.last k)

/-- Reachability from corner to corner. -/
abbrev reachBench (k : ℕ) : Prop := ReachIn (⊤ : Subshape (Grid (k + 1) (k + 1))) (origin k) (far k)

/-- Acyclicity of the whole grid. -/
abbrev acyclicBench (k : ℕ) : Prop := AcyclicOn (⊤ : Subshape (Grid (k + 1) (k + 1)))

/-- The last arrow: down into the bottom-right corner. -/
def lastU (k : ℕ) : Grid (k + 1) (k + 1) := (⟨k - 1, by omega⟩, Fin.last k)

/-- All arrows except the last one. -/
def allButLast (k : ℕ) : Subshape (Grid (k + 1) (k + 1)) :=
  fun a b => {_f | ¬ (a = lastU k ∧ b = far k)}

instance (k : ℕ) {a b : Grid (k + 1) (k + 1)} {f : a ⟶ b} : Decidable (f ∈ allButLast k a b) :=
  inferInstanceAs (Decidable (¬ (a = lastU k ∧ b = far k)))

/-- The top-left corner of the last square. -/
def lastCell (k : ℕ) : Grid (k + 1) (k + 1) := (⟨k - 1, by omega⟩, ⟨k - 1, by omega⟩)

/-- Adding the last arrow: the last square is a minimal obligation. -/
abbrev minObligationBench (k : ℕ) : Prop :=
  IsMinObligation (allButLast k) (lastU k) (far k) (lastCell k) (far k)

instance (k : ℕ) : Decidable (minObligationBench k) :=
  inferInstanceAs (Decidable (IsMinObligation (allButLast k) (lastU k) (far k) (lastCell k) (far k)))

/-- The arrows with both ends in columns `≤ c`, and those with both ends in
columns `≥ c`. -/
def leftOf (k c : ℕ) : Subshape (Grid (k + 1) (k + 1)) := fun a b => {_f | a.2.val ≤ c ∧ b.2.val ≤ c}
def rightOf (k c : ℕ) : Subshape (Grid (k + 1) (k + 1)) := fun a b => {_f | c ≤ a.2.val ∧ c ≤ b.2.val}

instance (k c : ℕ) {a b : Grid (k + 1) (k + 1)} {f : a ⟶ b} : Decidable (f ∈ leftOf k c a b) :=
  inferInstanceAs (Decidable (a.2.val ≤ c ∧ b.2.val ≤ c))

instance (k c : ℕ) {a b : Grid (k + 1) (k + 1)} {f : a ⟶ b} : Decidable (f ∈ rightOf k c a b) :=
  inferInstanceAs (Decidable (c ≤ a.2.val ∧ c ≤ b.2.val))

/-- The two halves of the grid, glued along the middle column, satisfy the chain
condition. -/
abbrev chainBench (k : ℕ) : Prop := Chain (leftOf k (k / 2)) (rightOf k (k / 2))

/-- The path along the top and down the right side. -/
def topRight (k : ℕ) : List (Total (Grid (k + 1) (k + 1))) :=
  walk (origin k) (List.replicate k .right ++ List.replicate k .down)

/-- The path down the left side and along the bottom. -/
def leftBottom (k : ℕ) : List (Total (Grid (k + 1) (k + 1))) :=
  walk (origin k) (List.replicate k .down ++ List.replicate k .right)

/-- The chase search, from the top-right path to the left-bottom path, with every
square as a face. The chase needs `k * k` steps. -/
def searchBench (k : ℕ) : Bool :=
  (bfs square (cells (k + 1) (k + 1)) (origin k) (leftBottom k) (k * k + 1)
    [(topRight k, [])] [topRight k]).isSome

end Diagrams.Bench
