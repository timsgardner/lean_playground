/-
# Front end: building diagrams and reading off equations

Two tactics connect the framework to goals stated in a diagram's own morphisms.

* `diagram_build faces using hF` proves `Commutes G` by construction. It adds the
  arrows in the order of `FinShape.arrows`; for each arrow it uses the faces that
  arrow completes (those whose other arrows came earlier). The resulting build is
  checked by the kernel (`commutes_of_order`). `hF` says the faces hold in `G`.
* `diagram_eq h` proves an equation between composites of the diagram's
  morphisms, such as `f ≫ j ≫ ℓ = g ≫ k ≫ m`, from `h : Commutes G`. It matches
  each factor to an arrow of the shape whose image under `G` is that morphism,
  which turns each side into a path, and applies `h`.
-/

import LeanPlayground.diagrams.construct
import LeanPlayground.diagrams.tactics

open CategoryTheory Quiver Lean Meta Elab Tactic

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C] {G : W ⥤q C}

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

/-- For each arrow position, in order, the faces it completes: those containing it
once, whose other arrows all come earlier. -/
def Search.faceUses (numArrows : ℕ) (faces : List (List ℕ × List ℕ)) : List (List FaceUse) :=
  (List.range numArrows).map fun k =>
    (faces.zipIdx.filterMap fun ((lhs, rhs), i) =>
      let all := lhs ++ rhs
      if all.count k == 1 && all.all (· ≤ k) then
        match lhs.idxOf? k with
        | some n => some ⟨i, false, n⟩
        | none => (rhs.idxOf? k).map fun n => ⟨i, true, n⟩
      else none)

/-! ## Evaluation -/

unsafe def evalBuildDataImpl (e : Expr) : MetaM (List (ℕ × ℕ) × List (List ℕ × List ℕ)) := do
  let pairT ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  let listNat ← mkAppM ``List #[mkConst ``Nat]
  let ty ← mkAppM ``Prod #[← mkAppM ``List #[pairT],
    ← mkAppM ``List #[← mkAppM ``Prod #[listNat, listNat]]]
  evalExpr (List (ℕ × ℕ) × List (List ℕ × List ℕ)) ty e

/-- Evaluate a build's data with compiled code. -/
@[implemented_by evalBuildDataImpl]
opaque evalBuildData (e : Expr) : MetaM (List (ℕ × ℕ) × List (List ℕ × List ℕ))

unsafe def evalBoolImpl (e : Expr) : MetaM Bool := evalExpr Bool (mkConst ``Bool) e

/-- Evaluate a Boolean with compiled code. -/
@[implemented_by evalBoolImpl] opaque evalBool (e : Expr) : MetaM Bool

/-- The term `FaceUse.mk i s n`. -/
def faceUseExpr (c : FaceUse) : Expr :=
  mkApp3 (mkConst ``FaceUse.mk) (mkNatLit c.face) (toExpr c.side) (mkNatLit c.pos)

/-! ## `diagram_build` -/

/-- Prove `Commutes G` by construction from the faces `faces`, given `hF` saying
they hold in `G`. -/
elab "diagram_build " faces:term:max " using " hF:term : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (W, G) := (match ty.getAppFnArgs with
    | (``Commutes, #[W, _, _, _, G]) => some (W, G)
    | _ => none) | throwError "diagram_build: the goal is not `Commutes G`"
  let _ := G
  let facesE ← Term.elabTermEnsuringType faces (← mkAppM ``List #[← mkAppOptM ``Face #[W, none]])
  let (arrows, faceData) ← evalBuildData (← mkAppM ``buildData #[facesE])
  let n := arrows.length
  let uses := Search.faceUses n faceData
  let order := List.range n
  let orderE := toExpr order
  let usesE ← mkListLit (← mkAppM ``List #[mkConst ``FaceUse])
    (← uses.mapM fun us => mkListLit (mkConst ``FaceUse) (us.map faceUseExpr))
  let stepsE ← mkAppOptM ``stepsOf #[W, none, none, orderE, usesE]
  let okE ← mkAppM ``buildOK #[facesE, stepsE]
  unless ← evalBool okE do
    throwError "diagram_build: the faces do not cover every obligation when the arrows \
      are added in the order of `FinShape.arrows`"
  let orderStx ← Term.exprToSyntax orderE
  let usesStx ← Term.exprToSyntax usesE
  evalTactic (← `(tactic| exact commutes_of_order (faces := $faces) $hF $orderStx $usesStx
    (by decide +kernel) (by decide +kernel)))

/-! ## `diagram_eq` -/

/-- The factors of a composite `a ≫ b ≫ …`, in order, with identities dropped. -/
partial def factors (e : Expr) : MetaM (List Expr) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, f, g]) => return (← factors f) ++ (← factors g)
  | (``CategoryStruct.id, _) => return []
  | _ => return [e]

/-- Match `fs` to a path of arrows starting at `start`, using `arrows`, a list of
pairs of an arrow (as a `Total` term) and its image under `G`. Returns the arrows. -/
partial def matchPath (arrows : List (Expr × Expr × Expr)) (start : Option Expr) :
    List Expr → MetaM (Option (List Expr))
  | [] => return some []
  | f :: fs => do
    for (e, src, img) in arrows do
      let srcOK ← match start with
        | none => pure true
        | some v => withNewMCtxDepth (isDefEq v src)
      if srcOK && (← withNewMCtxDepth (isDefEq img f)) then
        let tgt ← whnfD (← mkAppM ``Total.right #[e])
        if let some rest ← matchPath arrows (some tgt) fs then
          return some (e :: rest)
    return none

/-- Read the arrows of a finite shape, each as a `Total` term with its source and
its image under `G`. -/
partial def shapeArrows (W G : Expr) : MetaM (List (Expr × Expr × Expr)) := do
  let rec go (l : Expr) : MetaM (List Expr) := do
    let l ← whnfD l
    match l.getAppFnArgs with
    | (``List.cons, #[_, x, rest]) => return x :: (← go rest)
    | _ => return []
  let list ← go (← mkAppOptM ``FinShape.arrows #[W, none, none])
  list.mapM fun e => do
    let src ← whnfD (← mkAppM ``Total.left #[e])
    let hom ← mkAppM ``Total.hom #[e]
    let img ← whnfD (← mkAppOptM ``Prefunctor.map #[none, none, none, none, G, none, none, hom])
    return (e, src, img)

/-- The path, as an expression, through the arrows `es` (given as `Total` terms). -/
def pathExpr (es : List Expr) : MetaM Expr := do
  match es with
  | [] => throwError "diagram_eq: an empty side is not supported"
  | e :: rest =>
    let mut p ← mkAppM ``Quiver.Hom.toPath #[← mkAppM ``Total.hom #[e]]
    for e in rest do
      p ← mkAppM ``Quiver.Path.comp #[p, ← mkAppM ``Quiver.Hom.toPath #[← mkAppM ``Total.hom #[e]]]
    return p

/-- Prove an equation between composites of the morphisms of a commuting diagram,
given `h : Commutes G`. -/
elab "diagram_eq " h:term : tactic => withMainContext do
  let hE ← Term.elabTerm h none
  let hTy ← whnfR (← instantiateMVars (← inferType hE))
  let some (W, G) := (match hTy.getAppFnArgs with
    | (``Commutes, #[W, _, _, _, G]) => some (W, G)
    | _ => none) | throwError "diagram_eq: the hypothesis is not `Commutes G`"
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType').eq?
    | throwError "diagram_eq: the goal is not an equation: {← goal.getType}"
  let arrows ← shapeArrows W G
  let some ps ← matchPath arrows none (← factors lhs)
    | throwError "diagram_eq: the left side is not a path in the diagram"
  let some qs ← matchPath arrows none (← factors rhs)
    | throwError "diagram_eq: the right side is not a path in the diagram"
  let pStx ← Term.exprToSyntax (← pathExpr ps)
  let qStx ← Term.exprToSyntax (← pathExpr qs)
  evalTactic (← `(tactic| (
    have hpq := $h $pStx $qStx
    simp only [eval_comp, eval_toPath, Category.assoc] at hpq ⊢
    exact hpq)))

end Diagrams
