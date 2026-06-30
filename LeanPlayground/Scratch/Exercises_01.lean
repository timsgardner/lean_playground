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

/-
=================================================
 Tactic Logic
-/

section TacticLogic

variable (P Q R S : Prop)

-- Use mainly: intro, exact, apply
theorem tac1 (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  exact hqr (hpq hp)

-- Use mainly: intro, exact
theorem tac2 (h : P → Q → R) : Q → P → R := by
  intro q p
  exact h p q

-- Use: cases, apply/exact
theorem tac3 (h : (P → Q) ∧ (Q → R)) : P → R := by
  cases h with
  | intro p_to_q q_to_r =>
      exact q_to_r ∘ p_to_q

-- Use: intro, cases, constructor
theorem tac4 : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro pqr
  cases pqr with
  | intro p qr =>
    cases qr with
    | intro q r =>
      constructor
      · constructor
        · exact p
        · exact q
      · exact r


-- Use: intro, cases, constructor
theorem tac5 : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro pqr
  obtain ⟨⟨p, q⟩, r⟩ := pqr
  exact ⟨p, q, r⟩


-- Use: cases, left, right, exact
theorem tac6 : P ∨ Q → Q ∨ P := by
  intro pq
  cases pq with
  | inl p => exact Or.inr p
  | inr q => exact Or.inl q


-- Use: intro, cases, exact
theorem tac7 : (P ∨ Q) → (P → R) → (Q → R) → R := by
  intro pq p_to_r q_to_r
  cases pq with
  | inl p =>
    apply p_to_r
    exact p
  | inr q =>
    apply q_to_r
    exact q


-- Use: intro, cases, left, right, constructor
theorem tac8 : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro pqr
  obtain ⟨p, qr⟩ := pqr
  cases qr with
  | inl q =>
    left
    exact ⟨p, q⟩
  | inr r =>
    right
    exact ⟨p, r⟩

-- Use: intro, cases, left, right, constructor
theorem tac9 : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro pqpr
  cases pqpr with
  | inl pq =>
    obtain ⟨p, q⟩ := pq
    constructor
    · exact p
    · constructor
      · exact q
  | inr pr =>
    obtain ⟨p, r⟩ := pr
    constructor
    · exact p
    · right
      exact r

theorem tac9_rcases : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro pqpr
  rcases pqpr with ⟨p, q⟩ | ⟨p, r⟩
  · constructor
    · exact p
    · left
      exact q
  · constructor
    · exact p
    · right
      exact r

theorem tac9_rintro : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  rintro (⟨p, q⟩ | ⟨p, r⟩)
  · exact ⟨p, Or.inl q⟩
  · exact ⟨p, Or.inr r⟩

-- Use: intro, cases, exact
theorem tac10 : (P → R) ∧ (Q → S) → P ∧ Q → R ∧ S := by
  rintro ⟨p_to_r, q_to_s⟩
  rintro ⟨p, q⟩
  exact ⟨p_to_r p, q_to_s q⟩


end TacticLogic
