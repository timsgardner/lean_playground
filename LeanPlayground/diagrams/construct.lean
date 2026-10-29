/-
# Commutative by construction

A diagram is built by adding its arrows one at a time. When an arrow `e` is added,
the faces that `e` completes (those whose other arrows are already present) supply
the equations `e` owes: a face with `e` on one side, `α ≫ e ≫ β = γ`, is an
obligation at its source and target (`obligationHolds_of_face`). If those
obligations cover every obligation `e` creates, the diagram still commutes
(`CommutesOn.cons`, from `CommutesOn.sup_single_of_cover`). No search for chases is
involved: each equation comes from a face.

A *build* is a list of steps, each an arrow together with the faces it completes,
the last arrow first. `buildOK` checks a build: every face use has the right shape,
the new arrow closes no cycle, and the faces cover every obligation. These are
questions about the shape alone, decided by the procedures in `decide`.
`commutesOn_of_build` turns a checked build, and the equations of the faces, into
`CommutesOn G (ofList arrows)`.
-/

import LeanPlayground.diagrams.decide
import LeanPlayground.diagrams.search

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C] {G : W ⥤q C}

open PathEdges

/-! ## Adding one arrow to a listed subshape -/

/-- Adding an arrow to a subshape given by a list. -/
theorem CommutesOn.cons {A : List (Total W)} (hS : CommutesOn G (ofList A)) {u v : W} (e : u ⟶ v)
    (huv : ¬ ReachIn (ofList A) v u)
    (hcov : ∀ x y, IsObligation (ofList A) u v x y →
      ∃ x' y', ReachIn (ofList A) x x' ∧ ReachIn (ofList A) y' y ∧
        ObligationHolds (ofList A) e G x' y') :
    CommutesOn G (ofList (arrow e :: A)) := by
  rw [ofList_cons, sup_comm]
  exact hS.sup_single_of_cover huv hcov

theorem within_ofList_iff {A : List (Total W)} {a b : W} {p : Path a b} :
    Within (ofList A) p ↔ ∀ x ∈ p.edges, x ∈ A := by
  rw [within_iff_edges]
  rfl

/-- **A face gives an obligation.** If one side of a face that holds in `G` is
`α ≫ e ≫ β`, with `e` at position `n`, and the rest of the face lies in `A`, then
the obligation for `e` at the face's source and target holds. -/
theorem obligationHolds_of_face {A : List (Total W)} {φ : Face W} (hφ : φ.Holds G) {u v : W}
    (e : u ⟶ v) (s : Bool) (n : ℕ) (he : (φ.side s).edges[n]? = some (arrow e))
    (hα : ∀ x ∈ (φ.side s).edges.take n, x ∈ A)
    (hβ : ∀ x ∈ (φ.side s).edges.drop (n + 1), x ∈ A)
    (hγ : ∀ x ∈ (φ.side (!s)).edges, x ∈ A) :
    ObligationHolds (ofList A) e G φ.src φ.tgt := by
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

/-- The face use `c` lies below the pair `(x, y)`. -/
def coveredBy (faces : List (Face W)) (A : List (Total W)) (x y : W) (c : FaceUse) : Bool :=
  match faces[c.face]? with
  | none => false
  | some φ => decide (ReachIn (ofList A) x φ.src) && decide (ReachIn (ofList A) φ.tgt y)

/-- Adding `e` to `A`, with the face uses `uses`, is a valid step. -/
def stepOK (faces : List (Face W)) (A : List (Total W)) (e : Total W) (uses : List FaceUse) : Bool :=
  !(decide (ReachIn (ofList A) e.right e.left)) &&
    uses.all (faceUseOK faces A e) &&
    decide (∀ x y : W, IsObligation (ofList A) e.left e.right x y →
      uses.any (coveredBy faces A x y) = true)

/-- A build is valid: each step is valid on top of the arrows of the later steps. -/
def buildOK (faces : List (Face W)) : List (Total W × List FaceUse) → Bool
  | [] => true
  | (e, uses) :: rest => buildOK faces rest && stepOK faces (rest.map (·.1)) e uses

omit [FinShape W] [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W] in
theorem obligationHolds_of_faceUseOK {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G)
    {A : List (Total W)} {e : Total W} {c : FaceUse} (h : faceUseOK faces A e c = true)
    {φ : Face W} (hφ : faces[c.face]? = some φ) : ObligationHolds (ofList A) e.hom G φ.src φ.tgt := by
  simp only [faceUseOK, hφ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨he, hα⟩, hβ⟩, hγ⟩ := h
  exact obligationHolds_of_face (hF φ (List.mem_of_getElem? hφ)) e.hom c.side c.pos he hα hβ hγ

/-- **Commutative by construction.** A valid build whose faces hold in `G` makes `G`
commute on the subshape of its arrows. -/
theorem commutesOn_of_build {faces : List (Face W)} (hF : ∀ φ ∈ faces, φ.Holds G) :
    ∀ steps : List (Total W × List FaceUse), buildOK faces steps = true →
      CommutesOn G (ofList (steps.map (·.1)))
  | [], _ => by simpa using commutesOn_bot
  | (e, uses) :: rest, h => by
    simp only [buildOK, Bool.and_eq_true] at h
    obtain ⟨hrest, hstep⟩ := h
    have hS := commutesOn_of_build hF rest hrest
    simp only [stepOK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, List.all_eq_true] at hstep
    obtain ⟨⟨huv, huses⟩, hcov⟩ := hstep
    show CommutesOn G (ofList (arrow e.hom :: rest.map (·.1)))
    refine hS.cons e.hom huv fun x y hxy => ?_
    obtain ⟨c, hc, hcx⟩ := List.any_eq_true.1 (hcov x y hxy)
    unfold coveredBy at hcx
    split at hcx
    · exact absurd hcx Bool.false_ne_true
    · rename_i φ hφ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcx
      exact ⟨φ.src, φ.tgt, hcx.1, hcx.2, obligationHolds_of_faceUseOK hF (huses c hc) hφ⟩

omit [OutArrows W] [NumShape W] [Fintype W] [DecidableEq W] [DecidableEq (Total W)] in
/-- A subshape listing every arrow is the whole shape. -/
theorem commutes_of_commutesOn_ofList {A : List (Total W)} (h : CommutesOn G (ofList A))
    (hA : ∀ e ∈ (FinShape.arrows : List (Total W)), e ∈ A) : Commutes G :=
  commutesOn_top_iff.1 (h.mono fun _ _ f _ => hA (arrow f) (FinShape.mem_arrows _))

end Check

end Diagrams
