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
  sorry

theorem mem_insertionSort_iff
    (x : Nat) (xs : List Nat) :
    x ∈ insertionSort xs ↔ x ∈ xs := by
  sorry

-- === MARKER: MEMBERSHIP PROOFS END ===


-- === MARKER: SORTEDNESS PROOFS START ===

theorem insertSorted_sorted
    (x : Nat) (xs : List Nat) :
    List.SortedLE xs →
    List.SortedLE (insertSorted x xs) := by
  sorry

theorem insertionSort_sorted
    (xs : List Nat) :
    List.SortedLE (insertionSort xs) := by
  sorry

-- === MARKER: SORTEDNESS PROOFS END ===


-- === MARKER: FINAL CORRECTNESS THEOREM START ===

theorem insertionSort_correct
    (xs : List Nat) :
    List.SortedLE (insertionSort xs)
      ∧ ∀ x : Nat, x ∈ insertionSort xs ↔ x ∈ xs := by
  constructor
  · exact insertionSort_sorted xs
  · intro x
    exact mem_insertionSort_iff x xs

-- === MARKER: FINAL CORRECTNESS THEOREM END ===

end AlgoExercises
