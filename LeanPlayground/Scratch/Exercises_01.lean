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

/-
=================================================
 Tactic Negation
-/

section TacticNegation

variable (P Q R : Prop)

-- Remember: ¬P means P → False.
-- Use: intro, exact
theorem neg1 (hp : P) : ¬¬P := by
  intro hnp
  exact hnp hp

-- Use: intro, exact
theorem neg2 (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  intro p
  exact hnq (hpq p)

-- Use: intro, exact
theorem neg3 (h : P ∧ ¬P) : Q := by
  obtain ⟨p, np⟩ := h
  exact absurd p np


-- Use: exfalso, exact
theorem neg4 (hp : P) (hnp : ¬P) : Q := by
  exfalso
  exact hnp hp

-- Use: intro, cases
theorem neg5 : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro hpq
  constructor
  · intro p
    exact hpq (Or.inl p)
  · intro q
    exact hpq (Or.inr q)

-- Use: intro, cases, exact
theorem neg6 : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  rintro ⟨np, nq⟩
  rintro (p|q)
  · exact np p
  · exact nq q

-- Classical. Use: classical, by_contra
theorem neg7 : ¬¬P → P := by
  intro nnp
  by_contra
  exact nnp this

-- Classical. Use: classical, by_cases
theorem neg8 : (P → Q) → (¬P ∨ Q) := by
  intro pq
  by_cases p : P
  · exact Or.inr (pq p)
  · exact Or.inl p


end TacticNegation


/-
=================================================
 Quantifier Logic
-/

section QuantifierLogic

variable {α β : Type}
variable (P Q R : α → Prop)
variable (S : β → Prop)
variable (T : α → β → Prop)

-- 1. Use a universal hypothesis.
theorem quant1
    (h : ∀ x : α, P x)
    (a : α) :
    P a := by
  exact h a

-- 2. Prove a universal statement.
theorem quant2
    (h : ∀ x : α, P x → Q x) :
    (∀ x : α, P x) → ∀ x : α, Q x := by
  intro px x
  have pxqx := h x
  apply pxqx
  exact px x

-- 3. Universal distributes over conjunction, forward direction.
theorem quant3 :
    (∀ x : α, P x ∧ Q x) → (∀ x : α, P x) ∧ (∀ x : α, Q x) := by
  intro pxqx
  constructor
  · intro x
    exact (pxqx x).left
  · intro x
    exact (pxqx x).right

-- 4. Universal distributes over conjunction, backward direction.
theorem quant4 :
    (∀ x : α, P x) ∧ (∀ x : α, Q x) → ∀ x : α, P x ∧ Q x := by
  rintro ⟨u_px, u_qx⟩
  intro x
  exact ⟨u_px x, u_qx x⟩

-- 5. Existential gives a witness and a proof.
theorem quant5 :
    (∃ x : α, P x ∧ Q x) → ∃ x : α, P x := by
  intro e_px_qx
  rcases e_px_qx with ⟨x, ⟨px, qx⟩⟩
  exists x

-- 6. Existential distributes over disjunction, forward direction.
theorem quant6 :
    (∃ x : α, P x ∨ Q x) → (∃ x : α, P x) ∨ (∃ x : α, Q x) := by
  intro e_px_qx
  rcases e_px_qx with ⟨x, px | qx⟩
  left
  · exists x
  right
  · exists x

-- 7. Existential distributes over disjunction, backward direction.
theorem quant7 :
    (∃ x : α, P x) ∨ (∃ x : α, Q x) → ∃ x : α, P x ∨ Q x := by
  intro stuff
  rcases stuff with e_px | e_qx
  · rcases e_px with ⟨x, px⟩
    exists x
    exact Or.inl px
  · rcases e_qx with ⟨x, qx⟩
    exists x
    exact Or.inr qx


-- 8. Move a universal implication across an existential.
theorem quant8
    (h : ∀ x : α, P x → Q x) :
    (∃ x : α, P x) → ∃ x : α, Q x := by
  intro e_px
  obtain ⟨x, px⟩ := e_px
  exists x
  exact (h x) px

-- 9. Reuse the same witness.
theorem quant9
    (h : ∃ x : α, P x ∧ Q x) :
    ∃ x : α, Q x ∧ P x := by
  obtain ⟨x, ⟨px, qx⟩⟩ := h
  exists x

-- 10. Swap order of universal quantifiers.
theorem quant10 :
    (∀ x : α, ∀ y : β, T x y) → ∀ y : β, ∀ x : α, T x y := by
  rintro hi there marty
  exact hi marty there

-- 11. Swap order of existential quantifiers.
theorem quant11 :
    (∃ x : α, ∃ y : β, T x y) → ∃ y : β, ∃ x : α, T x y := by
  rintro ⟨x, y, txy⟩
  exists y
  exists x

-- 12. Universal plus existential.
theorem quant12
    (h : ∀ x : α, P x → Q x)
    (ex : ∃ x : α, P x) :
    ∃ x : α, Q x := by
  rcases ex with ⟨x, px⟩
  exists x
  exact (h x) px

end QuantifierLogic



/-
=================================================
 Natural numbers: basic induction
=================================================
-/

section NatBasic

-- Hint: induction on `n`; `simp` should close the base case and simplify the step.
theorem nat1 (n : Nat) : n + 0 = n := by
  induction n with
  | zero => simp
  | succ k ih => simp

-- Hint: this one may be closed by `simp`, but try induction on `n` first.
theorem nat2 (n : Nat) : 0 + n = n := by
  induction n with
  | zero => simp
  | succ k ih => simp

-- Hint: induction on `n`; in the step case, use the induction hypothesis with `rw`.
theorem nat3 (m n : Nat) : Nat.succ (m + n) = Nat.succ m + n := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- rw [Nat.add_succ, Nat.add_succ, ih]
    rw [Nat.add_succ]
    rewrite [Nat.add_succ]
    rewrite [ih]
    rfl

-- Hint: induction on `c` or on `a`; `simp` plus the induction hypothesis should be enough.
theorem nat4 (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rewrite [Nat.add_assoc]
    rfl

-- Hint: induction on `b`; use `simp` in the base case. In the step case, rewrite by the induction hypothesis.
theorem nat5 (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ k ih =>
    rewrite [Nat.add_left_comm]
    rewrite [Nat.add_assoc]
    rewrite [Nat.add_comm b 1]
    rfl
    -- have nxt := congrArg (· + 1) ih
    -- -- get: k + 1 + b = b + (k + 1)
    -- conv =>
    --   rhs
    --   rewrite [<- Nat.add_assoc]
    -- conv =>
    --   lhs
    --   rewrite [<- Nat.add_right_comm]
    -- exact nxt




-- Hint: use `intro h`; then `exact Nat.succ.inj h`, or try `cases h`.
theorem nat6 (a b : Nat) : Nat.succ a = Nat.succ b → a = b := by
  intro h
  exact Nat.succ.inj h

end NatBasic


/-
=================================================
 Natural numbers: multiplication
=================================================
-/

section NatMul

-- Hint: induction on `n`; `simp` should do most of the work.
theorem nat7 (n : Nat) : n * 0 = 0 := by
  simp

-- Hint: this is probably `simp`, but try induction if you want to see the recursion.
theorem nat8 (n : Nat) : 0 * n = 0 := by
  simp

-- Hint: `simp`; or unfold multiplication by induction on `n`.
theorem nat9 (n : Nat) : n * 1 = n := by
  simp

-- Hint: `simp`; if doing manually, induction on `n`.
theorem nat10 (n : Nat) : 1 * n = n := by
  simp

-- this is stupid and boring

end NatMul


/-
=================================================
 Natural numbers: inequalities
=================================================
-/

section NatIneq

-- Hint: `exact Nat.zero_le n`, or just try `omega`.
theorem nat14 (n : Nat) : 0 ≤ n := by
  omega

-- Hint: `exact Nat.succ_pos n`, or try `omega`.
theorem nat15 (n : Nat) : 0 < Nat.succ n := by
  omega

-- Hint: after `intro h`, `omega` works. For a manual proof, use `Nat.le_trans`.
theorem nat16 (a b c : Nat) : a ≤ b → a ≤ b + c := by
  omega

-- Hint: after `intro h`, use `exact Nat.add_le_add_right h c`, or try `omega`.
theorem nat17 (a b c : Nat) : a ≤ b → a + c ≤ b + c := by
  omega

-- Hint: after `intro h`, use `exact Nat.add_lt_add_right h c`, or try `omega`.
theorem nat18 (a b c : Nat) : a < b → a + c < b + c := by
  omega

-- Hint: `intro h`; `omega` is fine here. Manually, combine `a ≤ a + c` with transitivity.
theorem nat19 (a b c : Nat) : a + c ≤ b → a ≤ b := by
  omega

-- Hint: this is meant to be an `omega` exercise.
theorem nat20 (a b c : Nat) : a ≤ b → b ≤ c → a + 1 ≤ c + 1 := by
  omega


end NatIneq


/-
=================================================
 Natural numbers: parity and existentials
=================================================
-/

section NatParity

def MyEven (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

-- Hint: use `use 0`; then simplify.
theorem nat21 : MyEven 0 := by
  sorry

-- Hint: use `use 1`; then simplify.
theorem nat22 : MyEven 2 := by
  sorry

-- Hint: start with `intro h`; unpack with `rcases h with ⟨k, hk⟩`.
-- Then choose a witness related to `k + 1`.
theorem nat23 (n : Nat) : MyEven n → MyEven (n + 2) := by
  sorry

-- Hint: unpack both hypotheses with `rcases`.
-- The witness should be built from the two existing witnesses.
theorem nat24 (m n : Nat) : MyEven m → MyEven n → MyEven (m + n) := by
  sorry

-- Hint: unpack the evenness hypothesis.
-- The witness should involve `3 * k`, but you may need arithmetic cleanup by `ring` or `omega`.
theorem nat25 (n : Nat) : MyEven n → MyEven (3 * n) := by
  sorry

end NatParity


/-
=================================================
 Natural numbers: divisibility
=================================================
-/

section NatDivides

-- Hint: divisibility means "there exists a multiplier".
-- Use `use 1` or `use n`; then simplify.
theorem nat26 (n : Nat) : n ∣ n := by
  sorry

-- Hint: use `use n`; then simplify.
theorem nat27 (n : Nat) : 1 ∣ n := by
  sorry

-- Hint: start with `intro h`; unpack using `rcases h with ⟨k, hk⟩`.
-- Then produce a witness involving `k * c`.
theorem nat28 (a b c : Nat) : a ∣ b → a ∣ b * c := by
  sorry

-- Hint: unpack both divisibility hypotheses.
-- The witness should be the sum of the two witnesses.
theorem nat29 (a b c : Nat) : a ∣ b → a ∣ c → a ∣ b + c := by
  sorry

-- Hint: unpack both divisibility hypotheses.
-- Substitute or rewrite using the equalities you get.
theorem nat30 (a b c : Nat) : a ∣ b → b ∣ c → a ∣ c := by
  sorry

-- Hint: unpack both hypotheses.
-- The witness should multiply the two witnesses.
-- Arithmetic cleanup may need `ring`, `nlinarith`, or careful `rw`/`simp`.
theorem nat31 (a b c d : Nat) : a ∣ b → c ∣ d → a * c ∣ b * d := by
  sorry

end NatDivides
