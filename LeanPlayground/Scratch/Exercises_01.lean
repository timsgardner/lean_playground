import Mathlib

section Logic

variable (P Q R : Prop)

-- 1. Extract the left side of an `And`.
theorem ex1 (h : P ∧ Q) : P := by
  sorry

-- 2. Extract the right side of an `And`.
theorem ex2 (h : P ∧ Q) : Q := by
  sorry

-- 3. Build an `And`.
theorem ex3 (hp : P) (hq : Q) : P ∧ Q := by
  sorry

-- 4. Swap an `And`.
theorem ex4 (h : P ∧ Q) : Q ∧ P := by
  sorry

-- 5. Compose implications.
theorem ex5 (hpq : P → Q) (hqr : Q → R) : P → R := by
  sorry

-- 6. Use an implication.
theorem ex6 (hp : P) (hpq : P → Q) : Q := by
  sorry

-- 7. Swap an `Or`.
theorem ex7 (h : P ∨ Q) : Q ∨ P := by
  sorry

-- 8. Distribute `And` over `Or`.
theorem ex8 (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  sorry

-- 9. Prove a curried form.
theorem ex9 : (P ∧ Q → R) → P → Q → R := by
  sorry

-- 10. Prove an uncurried form.
theorem ex10 : (P → Q → R) → P ∧ Q → R := by
  sorry

end Logic
