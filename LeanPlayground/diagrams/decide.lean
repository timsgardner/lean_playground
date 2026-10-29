/-
# Deciding the shape conditions

The theorems about adding an arrow and pasting have hypotheses about the shape
alone: reachability, acyclicity, obligations and their minimality, shared
vertices, and the chain condition. On a finite shape all of them are decidable,
so `decide` proves them. This file supplies the decision procedures.

The core is reachability. `reachSet S a` starts from `{a}` and repeatedly adds the
targets of arrows of `S` leaving the current set. Each round either changes
nothing, and then the set is closed under arrows of `S`, or it adds a vertex,
which can happen at most `Fintype.card W` times. So after that many rounds the set
is closed, and it is exactly the set of vertices reachable from `a`
(`reachIn_iff_mem_reachSet`). The other conditions are built from reachability
with finite quantifiers.

For shapes too large for the kernel to decide comfortably, two certificates need
no finiteness at all: a rank that every arrow increases proves acyclicity
(`acyclicOn_of_rank`), and a set closed under arrows proves non-reachability
(`not_reachIn_of_closed`).
-/

import LeanPlayground.diagrams.finite
import LeanPlayground.diagrams.extend
import LeanPlayground.diagrams.paste
import Mathlib.Data.Fintype.Card

open CategoryTheory Quiver

namespace Diagrams

universe v₁ u₁

variable {W : Type u₁} [Quiver.{v₁} W] {S T : Subshape W}

/-! ## Certificates -/

/-- Along a path within `S`, a rank that every arrow of `S` increases goes up,
unless the path is empty. -/
theorem rank_lt_of_within (r : W → ℕ) (hr : ∀ (a b : W) (f : a ⟶ b), f ∈ S a b → r a < r b)
    {a b : W} {p : Path a b} (hp : Within S p) : p.length = 0 ∨ r a < r b := by
  induction hp with
  | nil => exact Or.inl rfl
  | @cons b c p f _ hf ih =>
    right
    rcases ih with h | h
    · obtain rfl := Path.eq_of_length_zero p h
      exact hr _ _ f hf
    · exact h.trans (hr _ _ f hf)

/-- **Rank certificate.** If some rank goes up along every arrow of `S`, then `S`
is acyclic. -/
theorem acyclicOn_of_rank (r : W → ℕ) (hr : ∀ (a b : W) (f : a ⟶ b), f ∈ S a b → r a < r b) :
    AcyclicOn S := by
  rintro a b ⟨p, hp⟩ ⟨q, hq⟩
  rcases rank_lt_of_within r hr hp with h | h
  · exact Path.eq_of_length_zero p h
  rcases rank_lt_of_within r hr hq with h' | h'
  · exact (Path.eq_of_length_zero q h').symm
  · exact absurd (h.trans h') (lt_irrefl _)

/-- A set closed under arrows of `S` contains everything reachable from it. -/
theorem mem_of_reachIn_of_closed (X : W → Prop)
    (hX : ∀ (a b : W) (f : a ⟶ b), f ∈ S a b → X a → X b) {a b : W} (ha : X a)
    (h : ReachIn S a b) : X b := by
  obtain ⟨p, hp⟩ := h
  induction hp with
  | nil => exact ha
  | cons _ hf ih => exact hX _ _ _ hf ih

/-- **Closed-set certificate.** If a set closed under arrows of `S` contains `v`
but not `u`, there is no path from `v` to `u` within `S`. -/
theorem not_reachIn_of_closed (X : W → Prop)
    (hX : ∀ (a b : W) (f : a ⟶ b), f ∈ S a b → X a → X b) {u v : W} (hv : X v) (hu : ¬ X u) :
    ¬ ReachIn S v u :=
  fun h => hu (mem_of_reachIn_of_closed X hX hv h)

/-- Paths within `S ⊓ T` are the paths lying in both. -/
theorem within_inf_iff {a b : W} {p : Path a b} : Within (S ⊓ T) p ↔ Within S p ∧ Within T p := by
  induction p with
  | nil => exact ⟨fun _ => ⟨.nil, .nil⟩, fun _ => .nil⟩
  | cons p f ih =>
    rw [within_cons_iff, within_cons_iff, within_cons_iff, ih]
    exact ⟨fun ⟨⟨h₁, h₂⟩, h₃, h₄⟩ => ⟨⟨h₁, h₃⟩, h₂, h₄⟩, fun ⟨⟨h₁, h₃⟩, h₂, h₄⟩ => ⟨⟨h₁, h₂⟩, h₃, h₄⟩⟩

/-- The chain condition, in terms of reachability within `S ⊓ T`. -/
theorem chain_iff : Chain S T ↔ ∀ s s' : W, Shared S T s → Shared S T s' →
    ReachIn (S ⊓ T) s s' ∨ ReachIn (S ⊓ T) s' s := by
  simp only [Chain, Common, ReachIn, within_inf_iff]

/-! ## Reachability -/

section Reach

variable [FinShape W] [Fintype W] [DecidableEq W] (S)
  [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]

/-- One round: add the targets of the arrows of `S` leaving `X`. -/
def reachStep (X : Finset W) : Finset W :=
  X ∪ (((FinShape.arrows : List (Total W)).filter fun e =>
    decide (e.hom ∈ S e.left e.right) && decide (e.left ∈ X)).map (·.right)).toFinset

/-- The vertices reached from `a` after `n` rounds. -/
def reachIter (a : W) : ℕ → Finset W
  | 0 => {a}
  | n + 1 => reachStep S (reachIter a n)

/-- The vertices reachable from `a` within `S`. -/
def reachSet (a : W) : Finset W := reachIter S a (Fintype.card W)

variable {S}

omit [Fintype W] in
theorem subset_reachStep (X : Finset W) : X ⊆ reachStep S X := Finset.subset_union_left

omit [Fintype W] in
theorem mem_reachStep_of {X : Finset W} {a b : W} {f : a ⟶ b} (hf : f ∈ S a b) (ha : a ∈ X) :
    b ∈ reachStep S X := by
  simp only [reachStep, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨arrow f, ⟨FinShape.mem_arrows _, hf, ha⟩, rfl⟩

omit [Fintype W] in
theorem mem_reachStep {X : Finset W} {b : W} (h : b ∈ reachStep S X) :
    b ∈ X ∨ ∃ e : Total W, e.hom ∈ S e.left e.right ∧ e.left ∈ X ∧ e.right = b := by
  simp only [reachStep, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨e, ⟨_, he, hx⟩, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, he, hx, rfl⟩

omit [Fintype W] in
theorem self_mem_reachIter (a : W) : ∀ n, a ∈ reachIter S a n
  | 0 => Finset.mem_singleton_self a
  | n + 1 => subset_reachStep _ (self_mem_reachIter a n)

omit [Fintype W] in
/-- Everything reached in some round is reachable. -/
theorem reachIn_of_mem_reachIter {a : W} : ∀ n {b : W}, b ∈ reachIter S a n → ReachIn S a b
  | 0, b, h => by
    rw [reachIter, Finset.mem_singleton] at h
    subst h
    exact ReachIn.refl _
  | n + 1, b, h => by
    rcases mem_reachStep h with h | ⟨e, he, hx, rfl⟩
    · exact reachIn_of_mem_reachIter n h
    · exact (reachIn_of_mem_reachIter n hx).trans ⟨e.hom.toPath, Within.toPath he⟩

omit [Fintype W] in
/-- A set that a round leaves unchanged contains everything reachable from it. -/
theorem mem_of_reachIn {X : Finset W} (hX : reachStep S X = X) {a b : W} (ha : a ∈ X)
    (h : ReachIn S a b) : b ∈ X :=
  mem_of_reachIn_of_closed (· ∈ X) (fun _ _ _ hf hx => hX ▸ mem_reachStep_of hf hx) ha h

omit [Fintype W] in
theorem reachIter_stable_from {a : W} {k : ℕ} (h : reachStep S (reachIter S a k) = reachIter S a k) :
    ∀ m, k ≤ m → reachIter S a m = reachIter S a k := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [reachIter, ih, h]

omit [Fintype W] in
/-- Each round either changes nothing or adds a vertex. -/
theorem reachIter_stable_or_card (a : W) : ∀ n,
    (∃ k ≤ n, reachStep S (reachIter S a k) = reachIter S a k) ∨ n + 1 ≤ (reachIter S a n).card
  | 0 => Or.inr (by simp [reachIter])
  | n + 1 => by
    rcases reachIter_stable_or_card a n with ⟨k, hk, h⟩ | hc
    · exact Or.inl ⟨k, hk.trans n.le_succ, h⟩
    · by_cases h : reachStep S (reachIter S a n) = reachIter S a n
      · exact Or.inl ⟨n, n.le_succ, h⟩
      · right
        have hss : reachIter S a n ⊂ reachIter S a (n + 1) :=
          Finset.ssubset_iff_subset_ne.2 ⟨subset_reachStep _, Ne.symm h⟩
        have := Finset.card_lt_card hss
        omega

/-- After `Fintype.card W` rounds, a further round changes nothing. -/
theorem reachStep_reachSet (a : W) : reachStep S (reachSet S a) = reachSet S a := by
  rcases reachIter_stable_or_card (S := S) a (Fintype.card W) with ⟨k, hk, h⟩ | hc
  · rw [reachSet, reachIter_stable_from h _ hk, h]
  · exact absurd (Finset.card_le_univ (reachIter S a (Fintype.card W))) (by omega)

/-- `reachSet S a` is exactly the set of vertices reachable from `a` within `S`. -/
theorem reachIn_iff_mem_reachSet {a b : W} : ReachIn S a b ↔ b ∈ reachSet S a :=
  ⟨mem_of_reachIn (reachStep_reachSet a) (self_mem_reachIter a _),
    reachIn_of_mem_reachIter _⟩

instance {a b : W} : Decidable (ReachIn S a b) :=
  decidable_of_iff _ reachIn_iff_mem_reachSet.symm

instance : Decidable (AcyclicOn S) :=
  inferInstanceAs (Decidable (∀ a b : W, ReachIn S a b → ReachIn S b a → a = b))

instance {u v x y : W} : Decidable (IsObligation S u v x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance {u v x y : W} : Decidable (IsMinObligation S u v x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Reach

/-! ## Shared vertices and the chain condition -/

section Shared

variable [FinShape W] [Fintype W] [DecidableEq W]

instance {R : Subshape W} [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ R a b)] {v : W} :
    Decidable (Touches R v) :=
  decidable_of_iff _ (FinShape.exists_arrow (P := fun {a b} f => f ∈ R a b ∧ (a = v ∨ b = v))).symm

instance [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]
    [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ T a b)] {v : W} : Decidable (Shared S T v) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]
    [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ T a b)] : Decidable (Chain S T) :=
  decidable_of_iff _ chain_iff.symm

end Shared

end Diagrams
