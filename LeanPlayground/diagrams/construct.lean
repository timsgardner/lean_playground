/-
# Commutative by construction

A diagram is built by adding its arrows one at a time. When an arrow `e` is added,
the faces that `e` completes (those whose other arrows are already present) supply
the equations `e` owes: a face with `e` on one side, `α ≫ e ≫ β = γ`, is an
cell at its source and target (`cellHolds_of_face`). If those
cells cover every cell `e` creates, the diagram still commutes
(`CommutesOn.cons`, from `CommutesOn.sup_single_of_cover`). No search for chases is
involved: each equation comes from a face.

A *build* is a list of steps, each an arrow together with the faces it completes,
the last arrow first. `buildOK` checks a build: every face use has the right shape,
the new arrow closes no cycle, and the faces cover every cell. These are
questions about the shape alone. `commutesOn_of_build` turns a checked build, and
the equations of the faces, into `CommutesOn G (ofList arrows)`.

The check never searches the graph. It carries one reachability bitmask per vertex
through the build (`MasksOK`), updated as each arrow arrives (`addMasks`, by
`reachIn_cons_iff`). Coverage is then decided per start vertex, with bitwise
operations (`coversOK`): if the new arrow's source already reaches its target,
the one pair `(source, target)` is checked; otherwise each start compares the ends
that need a face with the ends its face uses cover.
-/

import LeanPlayground.diagrams.decide

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C] {G : W ⥤q C}

open PathEdges

/-! ## Adding one arrow to a listed subshape -/

/-- Adding an arrow to a subshape given by a list. -/
theorem CommutesOn.cons {A : List (Total W)} (hS : CommutesOn G (ofList A)) {u v : W} (e : u ⟶ v)
    (huv : ¬ ReachIn (ofList A) v u)
    (hcov : ∀ x y, Closes (ofList A) u v x y →
      ∃ x' y', ReachIn (ofList A) x x' ∧ ReachIn (ofList A) y' y ∧
        CellHolds (ofList A) e G x' y') :
    CommutesOn G (ofList (arrow e :: A)) := by
  rw [ofList_cons, sup_comm]
  exact hS.sup_single_of_cover huv hcov

theorem within_ofList_iff {A : List (Total W)} {a b : W} {p : Path a b} :
    Within (ofList A) p ↔ ∀ x ∈ p.edges, x ∈ A := by
  rw [within_iff_edges]
  rfl

/-- **A face gives a cell.** If one side of a face that holds in `G` is
`α ≫ e ≫ β`, with `e` at position `n`, and the rest of the face lies in `A`, then
the cell that `e` closes at the face's source and target holds. -/
theorem cellHolds_of_face {A : List (Total W)} {φ : Face W} (hφ : φ.Holds G) {u v : W}
    (e : u ⟶ v) (s : Bool) (n : ℕ) (he : (φ.side s).edges[n]? = some (arrow e))
    (hα : ∀ x ∈ (φ.side s).edges.take n, x ∈ A)
    (hβ : ∀ x ∈ (φ.side s).edges.drop (n + 1), x ∈ A)
    (hγ : ∀ x ∈ (φ.side (!s)).edges, x ∈ A) :
    CellHolds (ofList A) e G φ.src φ.tgt := by
  obtain ⟨c, α, rest, hsplit, hαe, hreste⟩ := exists_split (φ.side s) n
  obtain ⟨d, mid, β, rfl, hmid, hβe⟩ := exists_split rest 1
  obtain ⟨hn, hx⟩ := List.getElem?_eq_some_iff.1 he
  have hdrop : (φ.side s).edges.drop n = arrow e :: (φ.side s).edges.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hn, hx]
  rw [hreste, hdrop] at hmid hβe
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at hmid hβe
  -- The middle path has the single edge `e`, so it is `e`.
  cases mid with
  | nil => simp at hmid
  | cons m f =>
    rw [edges_cons] at hmid
    obtain ⟨hm, hf⟩ := List.append_inj' (hmid.trans (List.nil_append _).symm) rfl
    obtain ⟨rfl, rfl, hfe⟩ := arrow_eq_arrow.1 (List.singleton_inj.1 hf)
    obtain rfl := eq_of_heq hfe
    obtain rfl := Path.eq_of_length_zero m (by simpa using congrArg List.length hm)
    obtain rfl : m = .nil := Path.eq_of_edges hm
    refine ⟨⟨α, β, φ.side (!s), ?_, ?_, ?_⟩, ?_⟩
    · rw [within_ofList_iff, hαe]; exact hα
    · rw [within_ofList_iff, hβe]; exact hβ
    · rw [within_ofList_iff]; exact hγ
    · have := hφ.side s (!s)
      rw [hsplit] at this
      simpa using this

/-! ## Builds -/

/-- A face used by a step: its position in the list of faces, the side that contains
the new arrow, and the arrow's position in that side. -/
structure FaceUse where
  /-- The position of the face in the list of faces. -/
  face : ℕ
  /-- The side containing the new arrow: `false` for `lhs`, `true` for `rhs`. -/
  side : Bool
  /-- The position of the new arrow in that side. -/
  pos : ℕ
  deriving DecidableEq, Repr

section Check

variable [FinShape W] [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W]
  [DecidableEq (Total W)]

/-- A face use fits: the face exists, the new arrow `e` sits at the stated position
of the stated side, and the rest of the face lies in `A`. -/
def faceUseOK (faces : List (Face W)) (A : List (Total W)) (e : Total W) (c : FaceUse) : Bool :=
  match faces[c.face]? with
  | none => false
  | some φ =>
    decide ((φ.side c.side).edges[c.pos]? = some e) &&
      ((φ.side c.side).edges.take c.pos).all (fun x => decide (x ∈ A)) &&
      ((φ.side c.side).edges.drop (c.pos + 1)).all (fun x => decide (x ∈ A)) &&
      (φ.side (!c.side)).edges.all (fun x => decide (x ∈ A))

open NumShape

/-! ### Reachability masks

A build keeps, for each vertex, the bitmask of the vertices it reaches through the
arrows added so far (`MasksOK`). Adding an arrow `u ⟶ v` that closes no cycle
updates each mask by one rule: a vertex that reaches `u` now also reaches
everything `v` reaches (`reachIn_cons_iff`). So no step searches the graph. -/

/-- `R` lists, for each vertex index, the bitmask of the vertices reachable from it
through the arrows `A`. -/
def MasksOK (A : List (Total W)) (R : List ℕ) : Prop :=
  ∀ (x : W) (j : ℕ), (R.getD (index x) 0).testBit j = true ↔ ∃ b, index b = j ∧ ReachIn (ofList A) x b

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
theorem MasksOK.reachIn_iff {A : List (Total W)} {R : List ℕ} (hR : MasksOK A R) {a b : W} :
    ReachIn (ofList A) a b ↔ (R.getD (index a) 0).testBit (index b) = true := by
  rw [hR]
  exact ⟨fun h => ⟨b, rfl, h⟩, fun ⟨_, hc, h⟩ => index_injective hc ▸ h⟩

/-- The masks with no arrows: each vertex reaches itself. -/
def initMasks : List ℕ := (List.range (size W)).map (1 <<< ·)

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
theorem masksOK_init : MasksOK ([] : List (Total W)) (initMasks (W := W)) := by
  intro x j
  rw [initMasks, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (index_lt x)]
  simp only [Option.map_some, Option.getD_some, Nat.one_shiftLeft, Nat.testBit_two_pow,
    decide_eq_true_eq, ofList_nil]
  constructor
  · rintro rfl; exact ⟨x, rfl, ReachIn.refl x⟩
  · rintro ⟨b, rfl, p, hp⟩
    cases hp with
    | nil => rfl
    | cons _ hf => exact hf.elim

omit [FinShape W] [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
/-- **Reachability after adding an arrow.** If `v` does not reach `u`, a path that
uses the new arrow `e : u ⟶ v` uses it once: it reaches `u`, crosses `e`, and
continues from `v` through old arrows. -/
theorem reachIn_cons_iff {A : List (Total W)} {u v : W} (e : u ⟶ v)
    (huv : ¬ ReachIn (ofList A) v u) {x y : W} :
    ReachIn (ofList (arrow e :: A)) x y ↔
      ReachIn (ofList A) x y ∨ (ReachIn (ofList A) x u ∧ ReachIn (ofList A) v y) := by
  constructor
  · rintro ⟨p, hp⟩
    induction hp with
    | nil => exact .inl (ReachIn.refl x)
    | @cons b c p f hp hf ih =>
      rcases List.mem_cons.1 (mem_ofList.1 hf) with hfe | hfA
      · obtain ⟨rfl, rfl, hfe⟩ := arrow_eq_arrow.1 hfe
        rcases ih with hxb | ⟨_, hvb⟩
        · exact .inr ⟨hxb, ReachIn.refl _⟩
        · exact absurd hvb huv
      · have hf' : ReachIn (ofList A) b c := ⟨f.toPath, .cons .nil hfA⟩
        rcases ih with hxb | ⟨hxu, hvb⟩
        · exact .inl (hxb.trans hf')
        · exact .inr ⟨hxu, hvb.trans hf'⟩
  · have hsub : ofList A ≤ ofList (arrow e :: A) := fun _ _ _ hf =>
      mem_ofList.2 (List.mem_cons_of_mem _ (mem_ofList.1 hf))
    rintro (h | ⟨hxu, hvy⟩)
    · exact h.mono hsub
    · exact ((hxu.mono hsub).trans ⟨e.toPath, .cons .nil (by simp)⟩).trans (hvy.mono hsub)

/-- The masks after adding the arrow `e`. -/
def addMasks (R : List ℕ) (e : Total W) : List ℕ :=
  R.map fun m => if m.testBit (index e.left) then m ||| R.getD (index e.right) 0 else m

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
theorem masksOK_add {A : List (Total W)} {R : List ℕ} (hR : MasksOK A R) (e : Total W)
    (huv : ¬ ReachIn (ofList A) e.right e.left) : MasksOK (e :: A) (addMasks R e) := by
  intro x j
  have hget : (addMasks R e).getD (index x) 0 =
      if (R.getD (index x) 0).testBit (index e.left) then
        R.getD (index x) 0 ||| R.getD (index e.right) 0 else R.getD (index x) 0 := by
    rw [addMasks, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h : R[index x]? <;> simp [List.getD_eq_getElem?_getD, h]
  have hcons := fun b => reachIn_cons_iff (A := A) e.hom huv (x := x) (y := b)
  change _ ↔ ∃ b, index b = j ∧ ReachIn (ofList (arrow e.hom :: A)) x b
  simp only [hcons, hget]
  split_ifs with hxu
  · rw [Nat.testBit_or, Bool.or_eq_true, hR, hR]
    rw [← hR.reachIn_iff] at hxu
    constructor
    · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
      · exact ⟨b, hb, .inl h⟩
      · exact ⟨b, hb, .inr ⟨hxu, h⟩⟩
    · rintro ⟨b, hb, h | ⟨_, h⟩⟩
      · exact .inl ⟨b, hb, h⟩
      · exact .inr ⟨b, hb, h⟩
  · rw [hR]
    rw [← hR.reachIn_iff] at hxu
    constructor
    · rintro ⟨b, hb, h⟩; exact ⟨b, hb, .inl h⟩
    · rintro ⟨b, hb, h | ⟨h, _⟩⟩
      · exact ⟨b, hb, h⟩
      · exact absurd h hxu

/-! ### Steps -/

/-- The face use `c` lies below the pair `(x, y)`, by the masks `R`. -/
def coveredBy (faces : List (Face W)) (R : List ℕ) (x y : W) (c : FaceUse) : Bool :=
  match faces[c.face]? with
  | none => false
  | some φ => (R.getD (index x) 0).testBit (index φ.src) && (R.getD (index φ.tgt) 0).testBit (index y)

/-- For each face use, the index of its source and the mask of what its target
reaches. -/
def useMasks (faces : List (Face W)) (R : List ℕ) : List FaceUse → List (ℕ × ℕ)
  | [] => []
  | c :: cs =>
    match faces[c.face]? with
    | some φ => (index φ.src, R.getD (index φ.tgt) 0) :: useMasks faces R cs
    | none => useMasks faces R cs

/-- The ends covered from a start whose reach is `mx`: the vertices reachable from
the target of a face use whose source `mx` contains, as a bitmask. -/
def coverMask (mx : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (s, m) :: l => (if mx.testBit s then m else 0) ||| coverMask mx l

/-- The face uses cover every cell that adding `e` closes, by the masks `R`.

If the source of `e` already reaches its target, every cell lies above the one at
`(e.left, e.right)`, so that pair alone is checked. Otherwise, for each start (each
mask `mx` in `R`) that reaches the source, the ends needing a face (reachable from
both the start and the target of `e`) must lie inside the ends the faces cover
from it (`coverMask`). -/
def coversOK (faces : List (Face W)) (R : List ℕ) (e : Total W) (uses : List FaceUse) : Bool :=
  if (R.getD (index e.left) 0).testBit (index e.right) then
    uses.any (coveredBy faces R e.left e.right)
  else
    let mv := R.getD (index e.right) 0
    let um := useMasks faces R uses
    R.all fun mx => !mx.testBit (index e.left) || (mx &&& mv &&& coverMask mx um == mx &&& mv)

/-- Adding `e` to `A`, whose masks are `R`, with the face uses `uses`, is a valid
step: it closes no cycle, the uses fit, and they cover every cell. -/
def stepOK (faces : List (Face W)) (A : List (Total W)) (R : List ℕ) (e : Total W)
    (uses : List FaceUse) : Bool :=
  !(R.getD (index e.right) 0).testBit (index e.left) &&
    uses.all (faceUseOK faces A e) &&
    coversOK faces R e uses

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
theorem testBit_coverMask {faces : List (Face W)} {R : List ℕ} {mx j : ℕ} :
    ∀ {uses : List FaceUse}, (coverMask mx (useMasks faces R uses)).testBit j = true →
      ∃ c ∈ uses, ∃ φ, faces[c.face]? = some φ ∧ mx.testBit (index φ.src) = true ∧
        (R.getD (index φ.tgt) 0).testBit j = true
  | [], h => by simp [useMasks, coverMask] at h
  | c :: cs, h => by
    simp only [useMasks] at h
    split at h
    · rename_i φ hφ
      simp only [coverMask, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · split_ifs at h with hs
        · exact ⟨c, List.mem_cons_self, φ, hφ, hs, h⟩
        · simp at h
      · obtain ⟨c', hc', rest⟩ := testBit_coverMask h
        exact ⟨c', List.mem_cons_of_mem _ hc', rest⟩
    · obtain ⟨c', hc', rest⟩ := testBit_coverMask h
      exact ⟨c', List.mem_cons_of_mem _ hc', rest⟩

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
/-- **The coverage check is sound**: every cell is covered by a face use. -/
theorem covered_of_coversOK {faces : List (Face W)} {A : List (Total W)} {R : List ℕ}
    (hR : MasksOK A R) {e : Total W} {uses : List FaceUse} (h : coversOK faces R e uses = true)
    {x y : W} (hxy : Closes (ofList A) e.left e.right x y) :
    ∃ c ∈ uses, coveredBy faces R x y c = true := by
  obtain ⟨hxu, hvy, hxy'⟩ := hxy
  unfold coversOK at h
  split_ifs at h with huv
  · -- The source reaches the target: the cell at `(e.left, e.right)` covers all.
    obtain ⟨c, hc, hcov⟩ := List.any_eq_true.1 h
    refine ⟨c, hc, ?_⟩
    unfold coveredBy at hcov ⊢
    split at hcov
    · exact absurd hcov Bool.false_ne_true
    · simp only [Bool.and_eq_true, ← hR.reachIn_iff] at hcov ⊢
      exact ⟨hxu.trans hcov.1, hcov.2.trans hvy⟩
  · -- The mask of `x` is in `R`, since `x` reaches something.
    have hxu' := hR.reachIn_iff.1 hxu
    have hmem : R.getD (index x) 0 ∈ R := by
      rw [List.getD_eq_getElem?_getD] at hxu' ⊢
      cases hget : R[index x]? with
      | none => simp [hget] at hxu'
      | some m => exact List.mem_of_getElem? hget
    have hx := List.all_eq_true.1 h _ hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hx
    rcases hx with hx | hx
    · exact absurd hxu' (by rw [hx]; exact Bool.false_ne_true)
    · -- `y` needs a face from `x`, so it lies in the covered ends.
      have hbit := congrArg (Nat.testBit · (index y)) hx
      simp only [Nat.testBit_and] at hbit
      rw [hR.reachIn_iff.1 hxy', hR.reachIn_iff.1 hvy, Bool.true_and, Bool.true_and] at hbit
      obtain ⟨c, hc, φ, hφ, hsrc, htgt⟩ := testBit_coverMask hbit
      refine ⟨c, hc, ?_⟩
      unfold coveredBy
      simp only [hφ, hsrc, htgt, Bool.and_self]

/-! ### Builds -/

/-- Check a build, listed last arrow first, returning the masks of its arrows, or
`none` if a step fails. -/
def checkBuild (faces : List (Face W)) : List (Total W × List FaceUse) → Option (List ℕ)
  | [] => some (initMasks (W := W))
  | (e, uses) :: rest =>
    match checkBuild faces rest with
    | none => none
    | some R => if stepOK faces (rest.map (·.1)) R e uses then some (addMasks R e) else none

/-- A build is valid: each step is valid on top of the arrows of the later steps. -/
def buildOK (faces : List (Face W)) (steps : List (Total W × List FaceUse)) : Bool :=
  (checkBuild faces steps).isSome

omit [FinShape W] [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W] in
theorem cellHolds_of_faceUseOK {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G)
    {A : List (Total W)} {e : Total W} {c : FaceUse} (h : faceUseOK faces A e c = true)
    {φ : Face W} (hφ : faces[c.face]? = some φ) : CellHolds (ofList A) e.hom G φ.src φ.tgt := by
  simp only [faceUseOK, hφ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨he, hα⟩, hβ⟩, hγ⟩ := h
  exact cellHolds_of_face (hF φ (List.mem_of_getElem? hφ)) e.hom c.side c.pos he hα hβ hγ

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] in
/-- A checked build commutes on its arrows, and its masks are their reachability. -/
theorem commutesOn_of_checkBuild {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G) :
    ∀ (steps : List (Total W × List FaceUse)) (R : List ℕ), checkBuild faces steps = some R →
      CommutesOn G (ofList (steps.map (·.1))) ∧ MasksOK (steps.map (·.1)) R
  | [], R, h => by
    simp only [checkBuild, Option.some.injEq] at h
    subst h
    exact ⟨by simpa using commutesOn_bot, masksOK_init⟩
  | (e, uses) :: rest, R', h => by
    simp only [checkBuild] at h
    split at h
    · exact absurd h (by simp)
    · rename_i R hrest
      split_ifs at h with hstep
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hS, hR⟩ := commutesOn_of_checkBuild hF rest R hrest
      simp only [stepOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hstep
      obtain ⟨⟨huv, huses⟩, hcov⟩ := hstep
      have huv' : ¬ ReachIn (ofList (rest.map (·.1))) e.right e.left := by
        rw [hR.reachIn_iff, huv]; exact Bool.false_ne_true
      refine ⟨?_, masksOK_add hR e huv'⟩
      show CommutesOn G (ofList (arrow e.hom :: rest.map (·.1)))
      refine hS.cons e.hom huv' fun x y hxy => ?_
      obtain ⟨c, hc, hcx⟩ := covered_of_coversOK hR hcov hxy
      unfold coveredBy at hcx
      split at hcx
      · exact absurd hcx Bool.false_ne_true
      · rename_i φ hφ
        simp only [Bool.and_eq_true, ← hR.reachIn_iff] at hcx
        exact ⟨φ.src, φ.tgt, hcx.1, hcx.2, cellHolds_of_faceUseOK hF (huses c hc) hφ⟩

omit [FinShape W] [OutArrows W] [Fintype W] [DecidableEq W] in
/-- **Commutative by construction.** A valid build whose faces hold in `G` makes `G`
commute on the subshape of its arrows. -/
theorem commutesOn_of_build {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G)
    (steps : List (Total W × List FaceUse)) (h : buildOK faces steps = true) :
    CommutesOn G (ofList (steps.map (·.1))) := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 h
  exact (commutesOn_of_checkBuild hF steps R hR).1

omit [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
/-- A subshape listing every arrow is the whole shape. -/
theorem commutes_of_commutesOn_ofList {A : List (Total W)} (h : CommutesOn G (ofList A))
    (hA : ∀ e ∈ (FinShape.arrows : List (Total W)), e ∈ A) : Commutes G :=
  commutesOn_top_iff.1 (h.mono fun _ _ f _ => hA (arrow f) (FinShape.mem_arrows _))

end Check

/-! ## Builds from an order of arrows -/

section Order

variable [FinShape W] [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W]
  [DecidableEq (Total W)]

/-- The build that adds the arrows at the positions `order` of `FinShape.arrows`, in
turn, each with its list of face uses. The build lists the last arrow first. -/
def stepsOf (order : List ℕ) (uses : List (List FaceUse)) : List (Total W × List FaceUse) :=
  ((order.zip uses).filterMap fun (k, us) =>
    ((FinShape.arrows : List (Total W))[k]?).map (·, us)).reverse

/-- The data a build search needs, as numbers: the source and target indices of
each arrow, and each face's sides as lists of arrow positions. -/
def buildData (faces : List (Face W)) : List (ℕ × ℕ) × List (List ℕ × List ℕ) :=
  ((FinShape.arrows : List (Total W)).map fun e => (NumShape.index e.left, NumShape.index e.right),
    faces.map fun φ => (φ.lhs.edges.map arrowIdx, φ.rhs.edges.map arrowIdx))

omit [OutArrows W] [Fintype W] [DecidableEq W] in
/-- **Commutative by construction, from an order.** -/
theorem commutes_of_order {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G)
    (order : List ℕ) (uses : List (List FaceUse))
    (h : buildOK faces (stepsOf order uses) = true)
    (hall : ∀ e ∈ (FinShape.arrows : List (Total W)), e ∈ (stepsOf order uses).map (·.1)) :
    Commutes G :=
  commutes_of_commutesOn_ofList (commutesOn_of_build hF _ h) hall

end Order

end Diagrams
