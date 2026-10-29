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

end Reach

/-! ## Fast reachability

`reachList S a` explores from `a` with a worklist, visiting each vertex once and
looking at the arrows leaving it (`OutArrows.out`), using lists only. The result is then checked to be closed under
arrows of `S`; when it is, it is exactly the set of vertices reachable from `a`.
The check succeeds whenever the fuel suffices, which it always does, but
correctness does not depend on that: if the check failed, `reachList` would fall
back to `reachSet`.
-/

section FastReach

variable [FinShape W] [OutArrows W] [DecidableEq W] (S)
  [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]

/-- The targets of the arrows of `S` leaving `x`. -/
def succs (x : W) : List W :=
  ((OutArrows.out x).filter fun e =>
    decide (e.left = x) && decide (e.hom ∈ S e.left e.right)).map (·.right)

/-- The elements of `l` not in `seen`, without repetitions. -/
def fresh (seen l : List W) : List W :=
  l.foldl (fun acc y => if y ∈ seen ∨ y ∈ acc then acc else acc ++ [y]) []

/-- Worklist exploration: pop a vertex, push its unvisited successors. -/
def explore : ℕ → List W → List W → List W
  | 0, _, visited => visited
  | _, [], visited => visited
  | fuel + 1, x :: work, visited =>
    let new := fresh visited (succs S x)
    explore fuel (work ++ new) (visited ++ new)

/-- `X` is closed under arrows of `S`. -/
def isClosed (X : List W) : Bool :=
  (FinShape.arrows : List (Total W)).all fun e =>
    !(decide (e.hom ∈ S e.left e.right) && decide (e.left ∈ X)) || decide (e.right ∈ X)

/-- The vertices reachable from `a` within `S`, as a list. -/
def reachList [Fintype W] (a : W) : List W :=
  let R := explore S ((FinShape.vertices : List W).length + 1) [a] [a]
  if isClosed S R then R else (FinShape.vertices : List W).filter (· ∈ reachSet S a)

variable {S}

omit [FinShape W] in
theorem reachIn_of_mem_succs {x y : W} (h : y ∈ succs S x) : ReachIn S x y := by
  simp only [succs, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, ⟨_, rfl, he⟩, rfl⟩ := h
  exact ⟨e.hom.toPath, Within.toPath he⟩

omit [Quiver W] [FinShape W] in
theorem mem_of_mem_foldl_fresh {seen : List W} {y : W} : ∀ (l acc : List W),
    y ∈ l.foldl (fun acc y => if y ∈ seen ∨ y ∈ acc then acc else acc ++ [y]) acc →
      y ∈ acc ∨ y ∈ l
  | [], _, h => Or.inl h
  | z :: l, acc, h => by
    rw [List.foldl_cons] at h
    rcases mem_of_mem_foldl_fresh l _ h with h | h
    · split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_singleton.1 h ▸ List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [Quiver W] [FinShape W] in
theorem mem_of_mem_fresh {seen l : List W} {y : W} (h : y ∈ fresh seen l) : y ∈ l :=
  (mem_of_mem_foldl_fresh l [] h).resolve_left (by simp)

omit [FinShape W] in
theorem subset_explore : ∀ (fuel : ℕ) (work visited : List W), visited ⊆ explore S fuel work visited
  | 0, _, _ => List.Subset.refl _
  | _ + 1, [], _ => List.Subset.refl _
  | fuel + 1, _ :: _, _ =>
    fun _ hx => subset_explore fuel _ _ (List.mem_append_left _ hx)

omit [FinShape W] in
/-- Everything `explore` visits is reachable, if everything it starts from is. -/
theorem reachIn_of_mem_explore {a : W} : ∀ (fuel : ℕ) (work visited : List W),
    (∀ v ∈ work, ReachIn S a v) → (∀ v ∈ visited, ReachIn S a v) →
      ∀ v ∈ explore S fuel work visited, ReachIn S a v
  | 0, _, _, _, hv => hv
  | _ + 1, [], _, _, hv => hv
  | fuel + 1, x :: work, visited, hw, hv => by
    have hnew : ∀ v ∈ fresh visited (succs S x), ReachIn S a v := fun v h =>
      (hw x (List.mem_cons_self ..)).trans (reachIn_of_mem_succs (mem_of_mem_fresh h))
    refine reachIn_of_mem_explore fuel _ _ ?_ ?_
    · intro v h
      rcases List.mem_append.1 h with h | h
      · exact hw v (List.mem_cons_of_mem _ h)
      · exact hnew v h
    · intro v h
      rcases List.mem_append.1 h with h | h
      · exact hv v h
      · exact hnew v h

omit [OutArrows W] in
theorem mem_of_isClosed {X : List W} (hX : isClosed S X = true) {a b : W} {f : a ⟶ b}
    (hf : f ∈ S a b) (ha : a ∈ X) : b ∈ X := by
  simp only [isClosed, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq] at hX
  rcases hX (arrow f) (FinShape.mem_arrows _) with (h | h) | h
  · exact absurd hf h
  · exact absurd ha h
  · exact h

variable [Fintype W]

/-- `reachList S a` is exactly the list of vertices reachable from `a` within `S`. -/
theorem reachIn_iff_mem_reachList {a b : W} : ReachIn S a b ↔ b ∈ reachList S a := by
  unfold reachList
  dsimp only
  split_ifs with hc
  · refine ⟨fun h => mem_of_reachIn_of_closed (· ∈ _) (fun _ _ _ hf hx => mem_of_isClosed hc hf hx)
      (subset_explore _ _ _ (List.mem_singleton_self a)) h, fun h => ?_⟩
    exact reachIn_of_mem_explore _ _ _ (by simpa using ReachIn.refl a)
      (by simpa using ReachIn.refl a) b h
  · simp [FinShape.mem_vertices, ← reachIn_iff_mem_reachSet]

instance {a b : W} : Decidable (ReachIn S a b) :=
  decidable_of_iff _ reachIn_iff_mem_reachList.symm

end FastReach

/-! ## Acyclicity, obligations and minimality -/

section Derived

variable [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W]
  [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]

omit [OutArrows W] [Fintype W] [DecidableEq W] [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)] in
/-- `S` is acyclic exactly when no arrow of `S` has a path back, except a loop. This
needs one reachability question per arrow, not one per pair of vertices. -/
theorem acyclicOn_iff_arrows : AcyclicOn S ↔ ∀ e ∈ (FinShape.arrows : List (Total W)),
    e.hom ∈ S e.left e.right → ReachIn S e.right e.left → e.left = e.right := by
  constructor
  · intro h e _ he hback
    exact h _ _ ⟨e.hom.toPath, Within.toPath he⟩ hback
  · intro h a b ⟨p, hp⟩ hba
    induction hp with
    | nil => rfl
    | @cons c d p f hp hf ih =>
      obtain rfl : c = d := h (arrow f) (FinShape.mem_arrows _) hf (hba.trans ⟨p, hp⟩)
      exact ih hba

instance : Decidable (AcyclicOn S) :=
  decidable_of_iff _ acyclicOn_iff_arrows.symm

instance {u v x y : W} : Decidable (IsObligation S u v x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Minimality only needs to look at the vertices reachable from `x`, and the
vertices reachable from `v`. -/
theorem isMinObligation_iff {u v x y : W} : IsMinObligation S u v x y ↔
    IsObligation S u v x y ∧ ∀ x₀ ∈ reachList S x, ReachIn S x₀ u →
      ∀ y₀ ∈ reachList S v, ReachIn S y₀ y → ReachIn S x₀ y₀ → x₀ = x ∧ y₀ = y := by
  simp only [IsMinObligation, IsObligation, ← reachIn_iff_mem_reachList]
  constructor
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x₀ hx₀ hu y₀ hy₀ hy hxy => h x₀ y₀ ⟨hu, hy₀, hxy⟩ hx₀ hy⟩
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x₀ y₀ ⟨hu, hy₀, hxy⟩ hx₀ hy => h x₀ hx₀ hu y₀ hy₀ hy hxy⟩

instance {u v x y : W} : Decidable (IsMinObligation S u v x y) :=
  haveI : ∀ a b : W, Decidable (ReachIn S a b) := fun _ _ => inferInstance
  decidable_of_iff _ isMinObligation_iff.symm

end Derived

/-! ## Shared vertices and the chain condition -/

section Shared

variable [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W]

instance {R : Subshape W} [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ R a b)] {v : W} :
    Decidable (Touches R v) :=
  decidable_of_iff _ (FinShape.exists_arrow (P := fun {a b} f => f ∈ R a b ∧ (a = v ∨ b = v))).symm

instance [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]
    [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ T a b)] {v : W} : Decidable (Shared S T v) :=
  inferInstanceAs (Decidable (_ ∧ _))

omit [OutArrows W] [Fintype W] in
/-- The chain condition only needs to look at pairs of shared vertices. -/
theorem chain_iff_shared [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]
    [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ T a b)] :
    Chain S T ↔ ∀ s ∈ (FinShape.vertices : List W).filter (Shared S T ·),
      ∀ s' ∈ (FinShape.vertices : List W).filter (Shared S T ·),
        ReachIn (S ⊓ T) s s' ∨ ReachIn (S ⊓ T) s' s := by
  rw [chain_iff]
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h s ⟨_, hs⟩ s' ⟨_, hs'⟩ => h s s' hs hs',
    fun h s s' hs hs' => h s ⟨FinShape.mem_vertices s, hs⟩ s' ⟨FinShape.mem_vertices s', hs'⟩⟩

instance [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]
    [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ T a b)] : Decidable (Chain S T) :=
  decidable_of_iff _ chain_iff_shared.symm

end Shared

end Diagrams
