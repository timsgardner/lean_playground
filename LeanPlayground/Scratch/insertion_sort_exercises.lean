import Mathlib

namespace AlgoExercises

-- === MARKER: INSERTION_SORT DEFINITIONS START ===

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insertSorted x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (insertionSort xs)

-- === MARKER: INSERTION_SORT DEFINITIONS END ===


-- === MARKER: BASIC COMPUTE CHECKS START ===

#eval insertionSort [3, 1, 4, 1, 5, 2]
-- expected: [1, 1, 2, 3, 4, 5]

#eval insertionSort []
-- expected: []

#eval insertionSort [10, 9, 8]
-- expected: [8, 9, 10]

-- === MARKER: BASIC COMPUTE CHECKS END ===


-- === MARKER: MEMBERSHIP PROOFS START ===

theorem mem_insertSorted_iff
    (x y : Nat) (ys : List Nat) :
    x ∈ insertSorted y ys ↔ x = y ∨ x ∈ ys := by
  induction ys with
  | nil => simp [insertSorted]
  | cons z zs ih =>
    simp only [insertSorted]
    split_ifs with h
    · simp
    · simp only [List.mem_cons, ih]
      tauto

theorem mem_insertionSort_iff
    (x : Nat) (xs : List Nat) :
    x ∈ insertionSort xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons y ys ih =>
    simp only [insertionSort]
    rw [mem_insertSorted_iff]
    constructor
    · rintro (xIsY | xInYs)
      · rw [<- xIsY]
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        exact ih.mp xInYs
    · intro xInYYs
      rw [ih]
      exact List.mem_cons.mp xInYYs


-- === MARKER: MEMBERSHIP PROOFS END ===


-- === MARKER: SORTEDNESS PROOFS START ===

abbrev SortedNatList (xs : List Nat) : Prop :=
  List.Pairwise (fun a b => a ≤ b) xs

theorem insertSorted_sorted
    (x : Nat) (xs : List Nat) :
    SortedNatList xs →
    SortedNatList (insertSorted x xs) := by
      intro xsSorted
      induction xs with
      | nil =>
          simp [insertSorted, SortedNatList]
      | cons head tail tail_ih =>
        simp [insertSorted]
        split_ifs with h
        · rewrite [SortedNatList]
          apply List.pairwise_cons_cons_iff_of_trans.mpr
          constructor
          · exact h
          · exact xsSorted
        · have head_le_xtail : ∀ z ∈ insertSorted x tail, head <= z := by
            · intro z z_in_xtail
              have hz_cases : z = x ∨ z ∈ tail := by
                exact (mem_insertSorted_iff z x tail).mp z_in_xtail
              rcases hz_cases with rfl | z_in_tail
              · omega
              · exact (List.pairwise_cons.mp xsSorted).left z z_in_tail
          apply List.Pairwise.cons
          · exact head_le_xtail
          · exact tail_ih xsSorted.tail


theorem insertionSort_sorted
    (xs : List Nat) :
    SortedNatList (insertionSort xs) := by
  sorry

-- === MARKER: SORTEDNESS PROOFS END ===

end AlgoExercises
