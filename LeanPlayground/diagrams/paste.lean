/-
# Pasting commutative diagrams

Riehl (1.6.10) pastes two commutative squares along a common edge to get a
commutative rectangle. This file proves a general version of that pasting step,
for two subshapes `S` and `T` of one shape.

A vertex is *shared* when it is an endpoint of an arrow of `S` and of an arrow of
`T`. The main theorem, `CommutesOn.paste`, says that if `G` commutes on `S` and on
`T`, then it commutes on `S ⊔ T`, provided that

* `S ⊔ T` is acyclic, and
* any two shared vertices are joined, in one direction or the other, by a path
  lying in both `S` and `T` (the *chain condition*, `Chain S T`).

The chain condition holds when `S` and `T` are glued along a common path, as in
the rectangle. Some condition of this kind is needed. Gluing two subshapes along
two vertices with no path between them can produce a diagram that does not
commute, even though each piece does: the arrows `a ⟶ s ⟶ b` and `a ⟶ s' ⟶ b`,
with `a ⟶ s`, `a ⟶ s'` in `S` and `s ⟶ b`, `s' ⟶ b` in `T`.

The proof first brings every path into a normal form (`normalize`): it is equal
to a path in one piece, or to a path in one piece followed by a path in the other,
with the switch at a shared vertex. Then it compares normal forms. Internally the
two pieces are indexed by `Bool`, so that "the other piece" is `!i`.
-/

import LeanPlayground.diagrams.core

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

/-! ## Pieces -/

section Pieces

variable (S T : Subshape W)

/-- `v` is an endpoint of some arrow of `R`. -/
def Touches (R : Subshape W) (v : W) : Prop :=
  ∃ (a b : W) (f : a ⟶ b), f ∈ R a b ∧ (a = v ∨ b = v)

/-- `v` is an endpoint of an arrow of `S` and of an arrow of `T`. -/
def Shared (v : W) : Prop := Touches S v ∧ Touches T v

/-- A path lying in both `S` and `T`. -/
def Common {a b : W} (p : Path a b) : Prop := Within S p ∧ Within T p

/-- Any two shared vertices are joined, in one direction or the other, by a path
lying in both `S` and `T`. -/
def Chain : Prop :=
  ∀ s s' : W, Shared S T s → Shared S T s' →
    (∃ c : Path s s', Common S T c) ∨ (∃ c : Path s' s, Common S T c)

/-- The two pieces, indexed by `Bool`. -/
def piece : Bool → Subshape W
  | true => S
  | false => T

variable {S T}

theorem piece_le (i : Bool) : piece S T i ≤ S ⊔ T := by
  cases i
  · exact le_sup_right
  · exact le_sup_left

theorem Common.within {a b : W} {c : Path a b} (hc : Common S T c) (i : Bool) :
    Within (piece S T i) c := by
  cases i
  · exact hc.2
  · exact hc.1

theorem shared_of {i : Bool} {v : W} (h₁ : Touches (piece S T i) v)
    (h₂ : Touches (piece S T (!i)) v) : Shared S T v := by
  cases i
  · exact ⟨h₂, h₁⟩
  · exact ⟨h₁, h₂⟩

theorem eq_not_of_ne {i j : Bool} (h : j ≠ i) : j = !i := by
  revert h; cases i <;> cases j <;> decide

/-- A nonempty path within `R` touches `R` at its end. -/
theorem Within.touches_end {R : Subshape W} {a b : W} {p : Path a b} (hp : Within R p) :
    p.length = 0 ∨ Touches R b := by
  cases hp with
  | nil => exact Or.inl (by simp)
  | cons _ hf => exact Or.inr ⟨_, _, _, hf, Or.inr rfl⟩

/-- A nonempty path within `R` touches `R` at its start. -/
theorem Within.touches_start {R : Subshape W} {a b : W} {p : Path a b} (hp : Within R p) :
    p.length = 0 ∨ Touches R a := by
  induction hp with
  | nil => exact Or.inl (by simp)
  | @cons b c p f _ hf ih =>
    right
    rcases ih with h | h
    · obtain rfl := Path.eq_of_length_zero p h
      exact ⟨_, _, f, hf, Or.inl rfl⟩
    · exact h

end Pieces

/-! ## Normal forms -/

section Paste

variable {G : W ⥤q C} {S T : Subshape W}

/-- A path in one piece between shared vertices can be replaced by a path lying
in both pieces. -/
theorem bridge (hcomm : ∀ i, CommutesOn G (piece S T i)) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) {s s' : W} (hs : Shared S T s) (hs' : Shared S T s')
    {i : Bool} {p : Path s s'} (hp : Within (piece S T i) p) :
    ∃ c : Path s s', Common S T c ∧ eval G c = eval G p := by
  rcases hchain s s' hs hs' with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, hc, hcomm i c p (hc.within i) hp⟩
  · obtain rfl := hacyc s s' ⟨p, hp.mono (piece_le i)⟩ ⟨c, hc.1.mono le_sup_left⟩
    exact ⟨.nil, ⟨.nil, .nil⟩, hcomm i _ p .nil hp⟩

variable (G S T) in
/-- `φ` is the composite of a path lying in one piece. -/
def IsSingle {a b : W} (φ : G.obj a ⟶ G.obj b) : Prop :=
  ∃ i, ∃ q : Path a b, Within (piece S T i) q ∧ eval G q = φ

variable (G S T) in
/-- `φ` is the composite of a path in one piece followed by a path in the other,
switching at a shared vertex. -/
def IsTwo {a b : W} (φ : G.obj a ⟶ G.obj b) : Prop :=
  ∃ i, ∃ s, Shared S T s ∧ ∃ (q₁ : Path a s) (q₂ : Path s b),
    Within (piece S T i) q₁ ∧ Within (piece S T (!i)) q₂ ∧ eval G q₁ ≫ eval G q₂ = φ

/-- Every path within `S ⊔ T` is equal to a normal form. -/
theorem normalize (hcomm : ∀ i, CommutesOn G (piece S T i)) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) {a b : W} {p : Path a b} (hp : Within (S ⊔ T) p) :
    IsSingle G S T (eval G p) ∨ IsTwo G S T (eval G p) := by
  induction hp with
  | nil => exact Or.inl ⟨true, .nil, .nil, rfl⟩
  | @cons b c p f _ hf ih =>
    obtain ⟨k, hk⟩ : ∃ k, f ∈ piece S T k b c :=
      (mem_sup.1 hf).elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
    rcases ih with ⟨i, q, hq, he⟩ | ⟨i, s, hs, q₁, q₂, hq₁, hq₂, he⟩
    · by_cases hki : k = i
      · subst hki
        exact Or.inl ⟨k, q.cons f, hq.cons hk, by rw [eval_cons, eval_cons, he]⟩
      · rcases hq.touches_end with h0 | ht
        · exact Or.inl ⟨k, q.cons f, (Within.of_length_zero h0).cons hk,
            by rw [eval_cons, eval_cons, he]⟩
        · obtain rfl := eq_not_of_ne hki
          refine Or.inr ⟨i, _, shared_of ht ⟨_, _, f, hk, Or.inl rfl⟩, q, f.toPath, hq,
            Within.toPath hk, ?_⟩
          rw [eval_cons, ← he, eval_toPath]
    · by_cases hki : k = !i
      · subst hki
        exact Or.inr ⟨i, s, hs, q₁, q₂.cons f, hq₁, hq₂.cons hk,
          by rw [eval_cons, eval_cons, ← he, Category.assoc]⟩
      · have hk' : k = i := by
          have := eq_not_of_ne hki; rwa [Bool.not_not] at this
        subst hk'
        obtain ⟨c, hc, hce⟩ : ∃ c : Path s _, Within (piece S T k) c ∧ eval G c = eval G q₂ := by
          rcases hq₂.touches_end with h0 | ht
          · exact ⟨q₂, Within.of_length_zero h0, rfl⟩
          · obtain ⟨c, hc, hce⟩ :=
              bridge hcomm hchain hacyc hs (shared_of ⟨_, _, f, hk, Or.inl rfl⟩ ht) hq₂
            exact ⟨c, hc.within k, hce⟩
        exact Or.inl ⟨k, (q₁.comp c).cons f, (hq₁.comp hc).cons hk,
          by rw [eval_cons, eval_cons, eval_comp, hce, ← he]⟩

/-! ## Comparing normal forms -/

/-- A composite around a cycle is the identity, so it agrees with a path of length
zero. -/
theorem cycle_eq (hcomm : ∀ i, CommutesOn G (piece S T i)) (hacyc : AcyclicOn (S ⊔ T))
    {a b s : W} {q : Path a b} (h0 : q.length = 0) {i j : Bool} {q₁ : Path a s}
    {q₂ : Path s b} (hq₁ : Within (piece S T i) q₁) (hq₂ : Within (piece S T j) q₂) :
    eval G q₁ ≫ eval G q₂ = eval G q := by
  obtain rfl := Path.eq_of_length_zero q h0
  obtain rfl := hacyc a s ⟨q₁, hq₁.mono (piece_le i)⟩ ⟨q₂, hq₂.mono (piece_le j)⟩
  have hq : eval G q = 𝟙 _ := by
    rw [hcomm true q .nil (Within.of_length_zero h0) .nil, eval_nil]
  rw [hcomm i q₁ q hq₁ (Within.of_length_zero h0), hcomm j q₂ q hq₂ (Within.of_length_zero h0),
    hq, Category.comp_id]

theorem single_single (hcomm : ∀ i, CommutesOn G (piece S T i)) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) {a b : W} {i j : Bool} {q q' : Path a b}
    (hq : Within (piece S T i) q) (hq' : Within (piece S T j) q') : eval G q = eval G q' := by
  by_cases hij : j = i
  · subst hij; exact hcomm _ q q' hq hq'
  obtain rfl := eq_not_of_ne hij
  rcases hq.touches_start with h0 | ha
  · exact hcomm _ q q' (Within.of_length_zero h0) hq'
  rcases hq.touches_end with h0 | hb
  · exact hcomm _ q q' (Within.of_length_zero h0) hq'
  rcases hq'.touches_start with h0 | ha'
  · exact hcomm _ q q' hq (Within.of_length_zero h0)
  rcases hq'.touches_end with h0 | hb'
  · exact hcomm _ q q' hq (Within.of_length_zero h0)
  obtain ⟨c, hc, hce⟩ := bridge hcomm hchain hacyc (shared_of ha ha') (shared_of hb hb') hq
  rw [← hce]
  exact hcomm _ c q' (hc.within _) hq'

theorem single_two (hcomm : ∀ i, CommutesOn G (piece S T i)) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) {a b s : W} {i j : Bool} (hs : Shared S T s)
    {q : Path a b} (hq : Within (piece S T i) q) {q₁ : Path a s} {q₂ : Path s b}
    (hq₁ : Within (piece S T j) q₁) (hq₂ : Within (piece S T (!j)) q₂) :
    eval G q = eval G q₁ ≫ eval G q₂ := by
  rcases hq.touches_start with h0 | ha
  · exact (cycle_eq hcomm hacyc h0 hq₁ hq₂).symm
  rcases hq.touches_end with h0 | hb
  · exact (cycle_eq hcomm hacyc h0 hq₁ hq₂).symm
  by_cases hij : j = i
  · -- Both start in piece `i`; compare at the end.
    subst hij
    rcases hq₂.touches_end with h0 | hb₂
    · rw [← eval_comp]
      exact hcomm _ q _ hq (hq₁.comp (Within.of_length_zero h0))
    · obtain ⟨c, hc, hce⟩ := bridge hcomm hchain hacyc hs (shared_of hb hb₂) hq₂
      rw [← hce, ← eval_comp]
      exact hcomm _ q _ hq (hq₁.comp (hc.within _))
  · -- Both end in piece `i`; compare at the start.
    obtain rfl := eq_not_of_ne hij
    rw [Bool.not_not] at hq₂
    rcases hq₁.touches_start with h0 | ha₁
    · rw [← eval_comp]
      exact hcomm _ q _ hq ((Within.of_length_zero h0).comp hq₂)
    · obtain ⟨c, hc, hce⟩ := bridge hcomm hchain hacyc (shared_of ha ha₁) hs hq₁
      rw [← hce, ← eval_comp]
      exact hcomm _ q _ hq ((hc.within _).comp hq₂)

/-- Two normal forms that switch in the same direction, with a common path from the
first switch point to the second, agree. -/
theorem two_two_same (hcomm : ∀ i, CommutesOn G (piece S T i)) {a b s s' : W} {i : Bool}
    {q₁ : Path a s} {q₂ : Path s b} {q₁' : Path a s'} {q₂' : Path s' b}
    (hq₁ : Within (piece S T i) q₁) (hq₂ : Within (piece S T (!i)) q₂)
    (hq₁' : Within (piece S T i) q₁') (hq₂' : Within (piece S T (!i)) q₂')
    {c : Path s s'} (hc : Common S T c) :
    eval G q₁ ≫ eval G q₂ = eval G q₁' ≫ eval G q₂' := by
  rw [hcomm _ q₂ (c.comp q₂') hq₂ ((hc.within _).comp hq₂'), eval_comp, ← Category.assoc,
    ← eval_comp, hcomm _ (q₁.comp c) q₁' (hq₁.comp (hc.within _)) hq₁']

theorem two_two (hcomm : ∀ i, CommutesOn G (piece S T i)) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) {a b s s' : W} {i j : Bool}
    (hs : Shared S T s) (hs' : Shared S T s')
    {q₁ : Path a s} {q₂ : Path s b} {q₁' : Path a s'} {q₂' : Path s' b}
    (hq₁ : Within (piece S T i) q₁) (hq₂ : Within (piece S T (!i)) q₂)
    (hq₁' : Within (piece S T j) q₁') (hq₂' : Within (piece S T (!j)) q₂') :
    eval G q₁ ≫ eval G q₂ = eval G q₁' ≫ eval G q₂' := by
  by_cases hij : j = i
  · subst hij
    rcases hchain s s' hs hs' with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact two_two_same hcomm hq₁ hq₂ hq₁' hq₂' hc
    · exact (two_two_same hcomm hq₁' hq₂' hq₁ hq₂ hc).symm
  obtain rfl := eq_not_of_ne hij
  rw [Bool.not_not] at hq₂'
  -- The first form ends in `!i`, the second in `i`; make one of them single.
  rcases hq₁.touches_start with h0 | ha
  · rw [← eval_comp]
    exact single_two hcomm hchain hacyc hs' ((Within.of_length_zero h0).comp hq₂) hq₁'
      (by rwa [Bool.not_not])
  rcases hq₁'.touches_start with h0 | ha'
  · rw [← eval_comp (p := q₁')]
    exact (single_two hcomm hchain hacyc hs ((Within.of_length_zero h0).comp hq₂') hq₁
      hq₂).symm
  obtain ⟨c, hc, hce⟩ := bridge hcomm hchain hacyc (shared_of ha ha') hs hq₁
  rw [← hce, ← eval_comp]
  exact single_two hcomm hchain hacyc hs' ((hc.within _).comp hq₂) hq₁' (by rwa [Bool.not_not])

/-! ## The pasting theorem -/

/-- **Pasting.** If `G` commutes on `S` and on `T`, `S ⊔ T` is acyclic, and the
shared vertices satisfy the chain condition, then `G` commutes on `S ⊔ T`. -/
theorem CommutesOn.paste (hS : CommutesOn G S) (hT : CommutesOn G T) (hchain : Chain S T)
    (hacyc : AcyclicOn (S ⊔ T)) : CommutesOn G (S ⊔ T) := by
  have hcomm : ∀ i, CommutesOn G (piece S T i) := fun i => by
    cases i
    · exact hT
    · exact hS
  intro a b p q hp hq
  rcases normalize hcomm hchain hacyc hp with
    ⟨i, p', hp', hpe⟩ | ⟨i, s, hs, p₁, p₂, hp₁, hp₂, hpe⟩ <;>
  rcases normalize hcomm hchain hacyc hq with
    ⟨j, q', hq', hqe⟩ | ⟨j, s', hs', q₁, q₂, hq₁, hq₂, hqe⟩ <;>
  rw [← hpe, ← hqe]
  · exact single_single hcomm hchain hacyc hp' hq'
  · exact single_two hcomm hchain hacyc hs' hp' hq₁ hq₂
  · exact (single_two hcomm hchain hacyc hs hq' hp₁ hp₂).symm
  · exact two_two hcomm hchain hacyc hs hs' hp₁ hp₂ hq₁ hq₂

/-- Under the chain and acyclicity hypotheses, `G` commutes on `S ⊔ T` if and only
if it commutes on `S` and on `T`. -/
theorem commutesOn_sup_iff (hchain : Chain S T) (hacyc : AcyclicOn (S ⊔ T)) :
    CommutesOn G (S ⊔ T) ↔ CommutesOn G S ∧ CommutesOn G T :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩,
    fun ⟨hS, hT⟩ => hS.paste hT hchain hacyc⟩

end Paste

end Diagrams
