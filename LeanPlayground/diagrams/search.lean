/-
# Searching for chases

A chase rewrites one path into another, one face at a time. To search for one,
this file works with paths as lists of edges (`Path.edges`), where rewriting is
plain list surgery.

* A `ChaseStep` names a face, a direction, and a position in the edge list. A list
  of steps is a *script*: a chase in flat form.
* `applyStep` checks that the chosen side of the face occurs at that position,
  starting at the right vertex, and replaces it by the other side. `replay` runs a
  whole script.
* `chase_of_replay`: if replaying a script turns the edges of `p` into the edges of
  `q`, then some chase joins `p` to `q`. So a script is a certificate for a chase.
* `findChase` searches breadth-first for a script, up to a number of rounds, and
  `chaseCheck` runs the search and checks its answer by `replay`. Only the check
  is trusted: `eq_of_chaseCheck` turns `chaseCheck ... = true`, proved by
  `decide`, into the equation `eval G p = eval G q`.
-/

import LeanPlayground.diagrams.chase
import LeanPlayground.diagrams.finite

open CategoryTheory Quiver

namespace Diagrams

universe w v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

open PathEdges

/-! ## Paths as edge lists -/

/-- The vertex where a path that starts at `a` and has edges `l` ends. -/
def lastVertex (a : W) (l : List (Total W)) : W := (l.getLast?.map (·.right)).getD a

/-- A path ends where its edges say it does. -/
theorem target_eq_lastVertex {a : W} : ∀ {b : W} (p : Path a b), b = lastVertex a p.edges
  | _, .nil => rfl
  | _, .cons p f => by simp [lastVertex]

/-- Any path splits after its first `n` edges. -/
theorem exists_split {a : W} : ∀ {b : W} (p : Path a b) (n : ℕ),
    ∃ (c : W) (p₁ : Path a c) (p₂ : Path c b),
      p = p₁.comp p₂ ∧ p₁.edges = p.edges.take n ∧ p₂.edges = p.edges.drop n
  | _, .nil, n => ⟨a, .nil, .nil, rfl, by simp, by simp⟩
  | _, .cons p f, n => by
    by_cases hn : n ≤ p.length
    · obtain ⟨c, p₁, p₂, rfl, h₁, h₂⟩ := exists_split p n
      refine ⟨c, p₁, p₂.cons f, rfl, ?_, ?_⟩
      · rw [h₁, edges_cons, List.take_append_of_le_length (by simpa using hn)]
      · rw [edges_cons, h₂, edges_cons, List.drop_append_of_le_length (by simpa using hn)]
    · refine ⟨_, p.cons f, .nil, rfl, ?_, ?_⟩
      · rw [List.take_of_length_le (by simp; omega)]
      · rw [edges_nil, List.drop_of_length_le (by simp; omega)]

/-! ## Steps on edge lists -/

variable {Φ : Type w} (faces : Φ → Face W)

/-- One step of a script: apply face `face`, forwards or backwards, to the edges
starting at position `pos`. -/
structure ChaseStep (Φ : Type w) where
  /-- The face applied. -/
  face : Φ
  /-- Whether the face is applied from `rhs` to `lhs`. -/
  backward : Bool
  /-- The number of edges before the rewritten stretch. -/
  pos : ℕ

variable [DecidableEq W] [DecidableEq (Total W)]

/-- Apply one step to a path that starts at `a` and has edges `l`, if the step
fits there. -/
def applyStep (a : W) (l : List (Total W)) (s : ChaseStep Φ) : Option (List (Total W)) :=
  let φ := faces s.face
  let src := (φ.side s.backward).edges
  if s.pos ≤ l.length ∧ lastVertex a (l.take s.pos) = φ.src ∧ (l.drop s.pos).take src.length = src
  then some (l.take s.pos ++ (φ.side (!s.backward)).edges ++ l.drop (s.pos + src.length))
  else none

/-- Run a script on a path that starts at `a` and has edges `l`. -/
def replay (a : W) : List (Total W) → List (ChaseStep Φ) → Option (List (Total W))
  | l, [] => some l
  | l, s :: ss => (applyStep faces a l s).bind fun l' => replay a l' ss

variable {faces}

/-- A step that fits a path is a step of a chase. -/
theorem applyStep_sound {a b : W} {p : Path a b} {s : ChaseStep Φ} {l' : List (Total W)}
    (h : applyStep faces a p.edges s = some l') :
    ∃ q : Path a b, q.edges = l' ∧ Nonempty (Step faces p q) := by
  unfold applyStep at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hn, hv, hm⟩ := hc
  cases h
  set φ := faces s.face with hφ
  obtain ⟨c, pre, rest, rfl, hpre, hrest⟩ := exists_split p s.pos
  have hlen : pre.edges.length = s.pos := by rw [hpre, List.length_take]; omega
  rw [edges_comp, List.take_left' hlen] at hv
  rw [edges_comp, List.drop_left' hlen] at hm
  obtain rfl : c = φ.src := (target_eq_lastVertex pre).trans hv
  obtain ⟨d, mid, post, rfl, hmid, hpost⟩ := exists_split rest (φ.side s.backward).edges.length
  rw [hm] at hmid
  obtain rfl : d = φ.tgt := (target_eq_lastVertex mid).trans
    (hmid ▸ (target_eq_lastVertex (φ.side s.backward)).symm)
  obtain rfl : mid = φ.side s.backward := Path.eq_of_edges hmid
  refine ⟨pre.comp ((φ.side (!s.backward)).comp post), ?_,
    ⟨⟨s.face, s.backward, pre, post, rfl, rfl⟩⟩⟩
  simp only [edges_comp, List.take_left' hlen, List.append_assoc]
  rw [← hlen, List.drop_length_add_append, List.drop_left]

/-- A script that turns the edges of `p` into some edges is a chase from `p` to
the path with those edges. -/
theorem replay_sound {a b : W} : ∀ (ss : List (ChaseStep Φ)) {p : Path a b} {l' : List (Total W)},
    replay faces a p.edges ss = some l' → ∃ q : Path a b, q.edges = l' ∧ Nonempty (Chase faces p q)
  | [], p, _, h => by cases h; exact ⟨p, rfl, ⟨.refl p⟩⟩
  | s :: ss, p, l', h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨l₁, h₁, h₂⟩ := h
    obtain ⟨q₁, rfl, ⟨st⟩⟩ := applyStep_sound h₁
    obtain ⟨q, hq, ⟨c⟩⟩ := replay_sound ss h₂
    exact ⟨q, hq, ⟨.cons st c⟩⟩

/-- **Scripts are certificates.** If replaying a script turns the edges of `p`
into the edges of `q`, then some chase joins `p` to `q`. -/
theorem chase_of_replay {a b : W} {p q : Path a b} {ss : List (ChaseStep Φ)}
    (h : replay faces a p.edges ss = some q.edges) : Nonempty (Chase faces p q) := by
  obtain ⟨q', hq', hc⟩ := replay_sound ss h
  rwa [Path.eq_of_edges hq'] at hc

/-! ## Breadth-first search

The search reports a script as a list of steps `(k, backward, pos)`, where `k` is
the position of the face in the list `names` of faces to try. A script of numbers
can be written into a proof term by a tactic without knowing anything about the
type of face names; `toSteps` turns it back into a script of `ChaseStep`s.
-/

/-- A step of a script, with the face given by its position in a list of faces. -/
abbrev IdxStep : Type := ℕ × Bool × ℕ

/-- The script of `ChaseStep`s that a script of `IdxStep`s denotes, given the list
of faces its indices refer to. Steps with an index out of range are dropped. -/
def toSteps (names : List Φ) (steps : List IdxStep) : List (ChaseStep Φ) :=
  steps.filterMap fun s => (names[s.1]?).map fun φ => ⟨φ, s.2.1, s.2.2⟩

variable (faces)

/-- All steps that fit a path starting at `a` with edges `l`, using the faces in
`names`, with the edges they produce. -/
def neighbors (names : List Φ) (a : W) (l : List (Total W)) :
    List (IdxStep × List (Total W)) :=
  names.zipIdx.flatMap fun (φ, k) => [false, true].flatMap fun bwd =>
    (List.range (l.length + 1)).filterMap fun n =>
      (applyStep faces a l ⟨φ, bwd, n⟩).map fun l' => ((k, bwd, n), l')

/-- Breadth-first search from a frontier of edge lists, each with the reversed
script that reached it, for `target`, for up to `fuel` rounds. -/
def bfs (names : List Φ) (a : W) (target : List (Total W)) :
    ℕ → List (List (Total W) × List IdxStep) → List (List (Total W)) → Option (List IdxStep)
  | 0, _, _ => none
  | fuel + 1, frontier, seen =>
    match frontier.find? (·.1 == target) with
    | some (_, script) => some script.reverse
    | none =>
      let next := (frontier.flatMap fun x =>
        (neighbors faces names a x.1).map fun y => (y.2, y.1 :: x.2)).foldl
          (fun acc y => if y.1 ∈ seen ∨ acc.any (·.1 == y.1) then acc else acc ++ [y]) []
      bfs names a target fuel next (seen ++ next.map (·.1))

/-- Search for a script from `p` to `q`, using the faces in `names`, for up to
`fuel` rounds. -/
def findChase (names : List Φ) (fuel : ℕ) {a b : W} (p q : Path a b) : Option (List IdxStep) :=
  bfs faces names a q.edges fuel [(p.edges, [])] [p.edges]

/-- Check a script from `p` to `q` by replaying it. -/
def replayCheck (names : List Φ) {a b : W} (p q : Path a b) (steps : List IdxStep) : Bool :=
  replay faces a p.edges (toSteps names steps) == some q.edges

/-- Search for a script from `p` to `q`, and check the answer by replaying it. -/
def chaseCheck (names : List Φ) (fuel : ℕ) {a b : W} (p q : Path a b) : Bool :=
  match findChase faces names fuel p q with
  | some steps => replayCheck faces names p q steps
  | none => false

variable {faces}

/-- A script that replays correctly gives a chase. This is what a tactic uses after
finding the script outside the kernel. -/
theorem chase_of_replayCheck {names : List Φ} {a b : W} {p q : Path a b} {steps : List IdxStep}
    (h : replayCheck faces names p q steps = true) : Nonempty (Chase faces p q) :=
  chase_of_replay (beq_iff_eq.1 h)

/-- A successful check gives a chase. -/
theorem chase_of_chaseCheck {names : List Φ} {fuel : ℕ} {a b : W} {p q : Path a b}
    (h : chaseCheck faces names fuel p q = true) : Nonempty (Chase faces p q) := by
  unfold chaseCheck at h
  split at h
  · exact chase_of_replayCheck h
  · exact absurd h Bool.false_ne_true

/-- **Search, then replay.** If the faces hold in `G` and the check succeeds, the
two paths have the same composite. -/
theorem eq_of_chaseCheck {G : W ⥤q C} (hF : ∀ φ, (faces φ).Holds G) {names : List Φ}
    {fuel : ℕ} {a b : W} {p q : Path a b} (h : chaseCheck faces names fuel p q = true) :
    eval G p = eval G q :=
  let ⟨c⟩ := chase_of_chaseCheck h
  c.sound' hF

end Diagrams
