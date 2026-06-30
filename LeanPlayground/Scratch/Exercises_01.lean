import Mathlib

section Logic

variable (P Q R : Prop)

-- 1. Extract the left side of an `And`.
theorem ex1 (h : P ∧ Q) : P :=
  h.left

-- 2. Extract the right side of an `And`.
theorem ex2 (h : P ∧ Q) : Q :=
  h.right

-- 3. Build an `And`.
theorem ex3 (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, hq⟩

-- 4. Swap an `And`.
theorem ex4 (h : P ∧ Q) : Q ∧ P :=
  have hp := h.left
  have hq := h.right
  ⟨hq, hp⟩

-- 5. Compose implications.
theorem ex5 (hpq : P → Q) (hqr : Q → R) : P → R :=
  hqr ∘ hpq

-- 6. Use an implication.
theorem ex6 (hp : P) (hpq : P → Q) : Q :=
  hpq hp

-- 7. Swap an `Or`.
theorem ex7 (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

-- 8. Distribute `And` over `Or`.
theorem ex8 (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) :=
  match h with
  | ⟨hp, Or.inl hq⟩ => Or.inl ⟨hp, hq⟩
  | ⟨hp, Or.inr hr⟩ => Or.inr ⟨hp, hr⟩

-- 9. Prove a curried form.
theorem ex9 : (P ∧ Q → R) → P → Q → R :=
  fun impl_pqr p q =>
    impl_pqr ⟨p, q⟩

-- 10. Prove an uncurried form.
theorem ex10 : (P → Q → R) → P ∧ Q → R :=
  fun pqr ⟨p, q⟩ => pqr p q

end Logic
