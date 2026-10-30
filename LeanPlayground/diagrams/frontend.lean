/-
# Front end: building diagrams and reading off equations

Two tactics connect the framework to goals stated in a diagram's own morphisms.

* `diagram_build faces using hF` proves `Commutes G` by construction. It searches
  for an order of the arrows in which the faces cover every cell (`Order`); for
  each arrow it uses the faces that arrow completes (those whose other arrows came
  earlier). The resulting build is checked by the kernel (`commutes_of_order`).
  `hF` says the faces hold in `G`.
* `diagram_eq h` proves an equation between composites of the diagram's
  morphisms, such as `f ≫ j ≫ ℓ = g ≫ k ≫ m`, from `h : Commutes G`. It matches
  each factor to an arrow of the shape whose image under `G` is that morphism,
  which turns each side into a path, and applies `h`.
-/

import LeanPlayground.diagrams.graph
import LeanPlayground.diagrams.order
import Mathlib.Data.Fin.VecNotation

open CategoryTheory Quiver Lean Meta Elab Tactic

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C] {G : W ⥤q C}

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
  let ends := arrows.toArray
  let shape : Order.Shape := ⟨ends.foldl (fun m (a, b) => max m (max a b + 1)) 0, ends,
    (List.range ends.size).toArray⟩
  let faceArr : Array Order.FaceData := faceData.toArray.map fun (l, r) => (l.toArray, r.toArray)
  let some order := shape.findOrder faceArr
    | throwError "diagram_build: no order of the arrows was found in which the faces cover \
        every cell"
  let uses := (shape.faceUses faceArr order).map fun us =>
    us.map fun (i, side, pos) => (⟨i, side, pos⟩ : FaceUse)
  let orderE := toExpr order
  let usesE ← mkListLit (← mkAppM ``List #[mkConst ``FaceUse])
    (← uses.mapM fun us => mkListLit (mkConst ``FaceUse) (us.map faceUseExpr))
  let stepsE ← mkAppOptM ``stepsOf #[W, none, none, orderE, usesE]
  let okE ← mkAppM ``buildOK #[facesE, stepsE]
  unless ← evalBool okE do
    throwError "diagram_build: the build found does not pass its check"
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

/-- `diagram_eq` for any shape with a list of arrows: matches the goal's factors to
the images of the arrows under `G`. -/
def diagramEqGeneric (h : Term) (W G : Expr) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType').eq?
    | throwError "diagram_eq: the goal is not an equation: {← goal.getType}"
  let arrows ← shapeArrows W G
  -- Explain why a side is not a path: a factor that is no arrow of the diagram, or
  -- factors that are arrows but do not form a path.
  let explain (side : String) (fs : List Expr) : TacticM Unit := do
    for f in fs do
      unless ← arrows.anyM (fun (_, _, img) => withNewMCtxDepth (isDefEq img f)) do
        throwError "diagram_eq: the {side} side is not a path in the diagram: {f} is not \
          one of its morphisms"
    throwError "diagram_eq: the {side} side is not a path in the diagram"
  let fl ← factors lhs
  let fr ← factors rhs
  let some ps ← matchPath arrows none fl | explain "left" fl; return
  let some qs ← matchPath arrows none fr | explain "right" fr; return
  let pStx ← Term.exprToSyntax (← pathExpr ps)
  let qStx ← Term.exprToSyntax (← pathExpr qs)
  evalTactic (← `(tactic| (
    have hpq := $h $pStx $qStx
    simp only [eval_comp, eval_toPath, Category.assoc] at hpq ⊢
    exact hpq)))

/-! ## Terms for graphs

The builders below write the terms for a graph (`Shape n E`) and its diagram
directly, without asking the elaborator to check the definitional equalities that
hold by computation: that an arrow's listed ends are its ends, that a listed
morphism has the type its listed ends require, and that a face holds once its
equation is bracketed to the left. The kernel checks all of them when the proof is
added. -/

namespace GraphTerm

/-- A natural number literal. -/
def lit (k : ℕ) : Expr := mkRawNatLit k

/-- A proof of `i < n` by evaluation. -/
def ltProof (i n : ℕ) : Expr :=
  mkApp3 (.const ``of_decide_eq_true [])
    (mkApp4 (.const ``LT.lt [0]) (.const ``Nat []) (.const ``instLTNat []) (lit i) (lit n))
    (mkApp2 (.const ``Nat.decLt []) (lit i) (lit n))
    (mkApp2 (.const ``Eq.refl [1]) (.const ``Bool []) (.const ``Bool.true []))

/-- The pair type `ℕ × ℕ`. -/
def pairT : Expr := mkApp2 (.const ``Prod [0, 0]) (.const ``Nat []) (.const ``Nat [])

/-- The data of a graph with its diagram in a category, as terms. -/
structure Data where
  /-- The number of vertices. -/
  n : ℕ
  /-- The ends of the arrows. -/
  ends : Array (ℕ × ℕ)
  /-- The term `E : List (ℕ × ℕ)`. -/
  E : Expr

namespace Data

variable (d : Data)

/-- The vertex `i` as an element of `Fin n`. -/
def fin (i : ℕ) : Expr := mkApp3 (.const ``Fin.mk []) (lit d.n) (lit i) (ltProof i d.n)

/-- The shape `Shape n E`. -/
def shape : Expr := mkApp2 (.const ``Diagrams.Shape []) (lit d.n) d.E

/-- The vertex `i` of the shape. -/
def vert (i : ℕ) : Expr := mkApp3 (.const ``Diagrams.Shape.vert []) (lit d.n) d.E (d.fin i)

/-- Arrow `k`, between the vertices `E` lists for it. -/
def arr (k : ℕ) : Expr :=
  let (a, b) := d.ends[k]!
  let finK := mkApp3 (.const ``Fin.mk []) (mkApp2 (.const ``List.length [0]) pairT d.E) (lit k)
    (ltProof k d.ends.size)
  let pair := mkApp4 (.const ``Prod.mk [0, 0]) (.const ``Nat []) (.const ``Nat []) (lit a) (lit b)
  mkApp6 (.const ``Diagrams.Shape.arr []) (lit d.n) d.E (d.fin a) (d.fin b) finK
    (mkApp2 (.const ``Eq.refl [1]) pairT pair)

/-- The path through the arrows `ks`, which must chain. -/
def path (ks : Array ℕ) : MetaM Expr := do
  let mut p ← mkAppOptM ``Quiver.Path.nil #[d.shape, none, d.vert d.ends[ks[0]!]!.1]
  for k in ks do
    p ← mkAppM ``Quiver.Path.cons #[p, d.arr k]
  return p

end Data

/-- The composite `f₁ ≫ f₂ ≫ … ≫ fₖ`, associated to the left. -/
def compLeft (fs : Array Expr) : MetaM Expr := do
  let mut t := fs[0]!
  for f in fs[1:] do
    t ← mkAppM ``CategoryStruct.comp #[t, f]
  return t

/-- A proof that `e` equals `e'`, two composites with the same factors, by
reassociation and dropping identities. -/
def reassoc (e e' : Expr) : TermElabM Expr := do
  if e == e' then return ← mkEqRefl e
  let ty ← mkEq e e'
  let stx ← `(by simp only [CategoryTheory.Category.assoc, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id])
  let p ← Term.elabTerm stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars p

end GraphTerm

open GraphTerm

/-! ## `comm_diagram`: a commuting diagram from equations -/

/-- The objects and morphisms of a diagram being read from equations: objects and
morphisms are identified up to definitional equality, in order of appearance. -/
structure Reading where
  /-- The objects. -/
  objs : Array Expr := #[]
  /-- The morphisms, with the indices of their source and target. -/
  mors : Array (Expr × ℕ × ℕ) := #[]
  /-- The category, its category instance, and the universe levels of its objects
  and of its homs, once known. -/
  cat : Option (Expr × Expr × Level × Level) := none
  /-- The quiver instance of the category and the universe levels of `Quiver.Hom`,
  read from the type of a morphism. -/
  hom : Option (Expr × List Level) := none

/-- The index of an object, adding it if it is new. -/
def Reading.object (r : Reading) (X : Expr) : MetaM (Reading × ℕ) := do
  for i in [0:r.objs.size] do
    if r.objs[i]! == X then return (r, i)
  for i in [0:r.objs.size] do
    if ← isDefEq r.objs[i]! X then return (r, i)
  return ({ r with objs := r.objs.push X }, r.objs.size)

/-- The index of a morphism, adding it (and its ends) if it is new. -/
def Reading.morphism (r : Reading) (f : Expr) : MetaM (Reading × ℕ) := do
  let ty ← whnfR (← instantiateMVars (← inferType f))
  let (``Quiver.Hom, #[C, instQ, X, Y]) := ty.getAppFnArgs
    | throwError "comm_diagram: {f} is not a morphism"
  let r := if r.hom.isSome then r else { r with hom := some (instQ, ty.getAppFn.constLevels!) }
  for i in [0:r.mors.size] do
    if r.mors[i]!.1 == f then return (r, i)
  for i in [0:r.mors.size] do
    if ← isDefEq r.mors[i]!.1 f then return (r, i)
  let r ← match r.cat with
    | some _ => pure r
    | none => do
      let some uC := (← getLevel C).dec | throwError "comm_diagram: unexpected universe"
      let some vC := (← getLevel ty).dec | throwError "comm_diagram: unexpected universe"
      let inst ← synthInstance (mkApp (.const ``CategoryTheory.Category [vC, uC]) C)
      pure { r with cat := some (C, inst, uC, vC) }
  let (r, a) ← r.object X
  let (r, b) ← r.object Y
  return ({ r with mors := r.mors.push (f, a, b) }, r.mors.size)

/-- Read the morphisms of a composite, as indices, with the factors. -/
def Reading.path (r : Reading) (e : Expr) : MetaM (Reading × Array ℕ × Array Expr) := do
  let mut r := r
  let mut out := #[]
  let fs := (← factors e).toArray
  for f in fs do
    let (r', i) ← r.morphism f
    r := r'
    out := out.push i
  return (r, out, fs)

/-- `comm_diagram [h₁, …, hₖ]` proves that the diagram formed by the morphisms in the
equations `hᵢ` commutes. Each `hᵢ` is an equation between composites; its morphisms
are the arrows, their domains and codomains the objects, and the equations are the
faces. The result is a proof of `Commutes (toPrefunctor obj mors _)`, whose type
lists the objects and morphisms; `diagram_eq` reads equations off it. -/
elab "comm_diagram " "[" hs:term,* "]" : term => do
  let hs := hs.getElems
  let mut r : Reading := {}
  let mut faces : Array (Array ℕ × Array ℕ) := #[]
  let mut evidence : Array (Expr × Array Expr × Array Expr) := #[]
  for h in hs do
    let e ← Term.elabTerm h none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← instantiateMVars (← whnfR (← inferType e))
    let some (_, lhs, rhs) := ty.eq?
      | throwErrorAt h "comm_diagram: {h} is not an equation"
    let (r₁, l, fl) ← r.path lhs
    let (r₂, rr, fr) ← r₁.path rhs
    r := r₂
    if l.isEmpty || rr.isEmpty then
      throwErrorAt h "comm_diagram: a side of {h} is an identity, which is not supported"
    faces := faces.push (l, rr)
    evidence := evidence.push (e, fl, fr)
  let some (C, inst, uC, vC) := r.cat | throwError "comm_diagram: no equations"
  let n := r.objs.size
  let ends := r.mors.map fun (_, a, b) => (a, b)
  let shape : Order.Shape := ⟨n, ends, (List.range ends.size).toArray⟩
  let showPath (p : Array ℕ) : MetaM MessageData := do
    let parts ← p.toList.mapM fun i => ppExpr r.mors[i]!.1
    return MessageData.joinSep (parts.map toMessageData) " ≫ "
  unless shape.acyclic do
    throwError "comm_diagram: the morphisms contain a cycle, which is not supported"
  let (found, exhaustive) := shape.searchOrder faces
  let some order := found
    | match shape.explainFailure faces with
      | some (_, (l, rr)) =>
        throwError "comm_diagram: the equations do not make the diagram commute{
          if exhaustive then m!"" else m!" (as far as the search went)"}. These two \
          parallel routes are related by no equation:\n  {← showPath l}\n  {← showPath rr}"
      | none => throwError "comm_diagram: the equations do not make the diagram commute"
  let uses := shape.faceUses faces order
  -- The graph and its diagram, as terms.
  let E ← mkListLit pairT (ends.toList.map fun (a, b) =>
    mkApp4 (.const ``Prod.mk [0, 0]) (.const ``Nat []) (.const ``Nat []) (lit a) (lit b))
  let d : Data := ⟨n, ends, E⟩
  let finT := mkApp (.const ``Fin []) (lit n)
  let objLvl := uC
  let mut obj := mkApp (.const ``Matrix.vecEmpty [objLvl]) C
  for i in [0:n] do
    let X := r.objs[n - 1 - i]!
    obj := mkApp4 (.const ``Matrix.vecCons [objLvl]) C (lit i) X obj
  let some (instQ, homLvls) := r.hom | throwError "comm_diagram: no morphisms"
  let hom (A B : Expr) : Expr := mkApp4 (.const ``Quiver.Hom homLvls) C instQ A B
  let innerFam (a : Expr) : MetaM Expr := withLocalDeclD `b finT fun b =>
    mkLambdaFVars #[b] (hom (mkApp obj a) (mkApp obj b))
  let outerFam ← withLocalDeclD `a finT fun a => do
    mkLambdaFVars #[a] (mkApp2 (.const ``Sigma [0, vC]) finT (← innerFam a))
  let entryT := mkApp2 (.const ``Sigma [0, vC]) finT outerFam
  let entries ← r.mors.toList.mapM fun (f, a, b) => do
    let inner := mkApp4 (.const ``Sigma.mk [0, vC]) finT (← innerFam (d.fin a)) (d.fin b) f
    return mkApp4 (.const ``Sigma.mk [0, vC]) finT outerFam (d.fin a) inner
  let mors ← mkListLit entryT entries
  let hE := mkApp2 (.const ``Eq.refl [1]) (mkApp (.const ``List [0]) pairT) E
  let G := mkAppN (.const ``Diagrams.toPrefunctor [vC, uC]) #[C, inst, lit n, E, obj, mors, hE]
  -- The faces, and their proofs from the equations.
  let instQW ← instantiateMVars
    (← synthInstance (mkApp (.const ``Quiver [← mkFreshLevelMVar, 0]) d.shape))
  let faceT ← mkAppOptM ``Diagrams.Face #[d.shape, instQW]
  let faceEs ← faces.mapM fun (l, rr) => do
    mkAppM ``Diagrams.Face.mk #[d.vert ends[l[0]!]!.1, d.vert ends[l.back!]!.2, ← d.path l,
      ← d.path rr]
  let facesE ← mkListLit faceT faceEs.toList
  let mut proofs : Array Expr := #[]
  for i in [0:faces.size] do
    let (e, fl, fr) := evidence[i]!
    let some (α, lhs, rhs) := (← instantiateMVars (← whnfR (← inferType e))).eq? | unreachable!
    let ll ← compLeft fl
    let rl ← compLeft fr
    let pl ← reassoc lhs ll
    let pr ← reassoc rhs rl
    -- `ll = rl`, from `lhs = rhs`.
    let homU ← getLevel α
    let e' := mkApp6 (.const ``Eq.trans [homU]) α ll rhs rl
      (mkApp6 (.const ``Eq.trans [homU]) α ll lhs rhs (mkApp4 (.const ``Eq.symm [homU]) α lhs ll pl) e) pr
    let holds ← mkAppOptM ``Diagrams.holds_of_evalNE #[none, none, none, none, G, faceEs[i]!]
    proofs := proofs.push (mkApp holds e')
  let mut chain := mkConst ``True.intro
  for p in proofs.reverse do
    chain ← mkAppM ``And.intro #[p, chain]
  let hF ← mkAppOptM ``Diagrams.forall_of_allHold #[none, none, none, none, G, facesE, chain]
  -- The build, checked by the kernel.
  let usesS ← `([$(← uses.toArray.mapM fun us => do
      `([$(← us.toArray.mapM fun (i, side, pos) => do
          let sideS ← if side then `(true) else `(false)
          `((⟨$(Syntax.mkNumLit (toString i)), $sideS, $(Syntax.mkNumLit (toString pos))⟩ :
            Diagrams.FaceUse))),*])),*])
  let orderS ← `([$(order.toArray.map fun k => Syntax.mkNumLit (toString k)),*])
  let term ← `(Diagrams.commutes_of_order (G := $(← Term.exprToSyntax G))
      (faces := $(← Term.exprToSyntax facesE)) $(← Term.exprToSyntax hF) $orderS $usesS
      (by decide +kernel) (by decide +kernel))
  Term.elabTerm term none

/-! ## `diagram_eq` -/

/-- Read a vertex number from a term `Fin.mk n i _` or a numeral. -/
def finVal (e : Expr) : MetaM ℕ := do
  match e.getAppFnArgs with
  | (``Fin.mk, #[_, i, _]) => if let some k := i.rawNatLit? then return k else
      if let some k := (← (evalNat i).run) then return k
      else throwError "diagram_eq: unreadable vertex {e}"
  | _ => do
    let v ← whnf (← mkAppM ``Fin.val #[e])
    if let some k := v.rawNatLit? then return k
    if let some k := (← (evalNat v).run) then return k
    throwError "diagram_eq: unreadable vertex {e}"

/-- `diagram_eq` for a diagram built by `comm_diagram`: the morphisms are read from
the diagram's type, and the definitional equalities are left to the kernel. -/
def diagramEqGraph (hD G : Expr) : TacticM Unit := withMainContext do
  let (``Diagrams.toPrefunctor, #[_, _, nE, E, _, mors, _]) := G.getAppFnArgs | failure
  let some n := (← (evalNat nE).run) | failure
  -- The listed morphisms, with their ends.
  let mut ms : Array (Expr × ℕ × ℕ) := #[]
  let endsOf (m : Array (Expr × ℕ × ℕ)) : Array (ℕ × ℕ) := m.map fun (_, a, b) => (a, b)
  let mut l := mors
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, x, rest]) =>
      let (``Sigma.mk, #[_, _, a, inner]) := x.getAppFnArgs | failure
      let (``Sigma.mk, #[_, _, b, f]) := inner.getAppFnArgs | failure
      ms := ms.push (f, ← finVal a, ← finVal b)
      l := rest
    | _ => break
  let d : Data := ⟨n, endsOf ms, E⟩
  let goal ← getMainGoal
  let some (α, lhs, rhs) := (← goal.getType').eq?
    | throwError "diagram_eq: the goal is not an equation: {← goal.getType}"
  let find (side : String) (f : Expr) : MetaM ℕ := do
    if let some k := ms.findIdx? (fun (g, _, _) => g == f) then return k
    for k in [0:ms.size] do
      let (g, _, _) := ms[k]!
      if ← isDefEq g f then return k
    throwError "diagram_eq: the {side} side is not a path in the diagram: {f} is not one \
      of its morphisms"
  let readSide (side : String) (e : Expr) : MetaM (Array ℕ × Array Expr) := do
    let fs := (← factors e).toArray
    if fs.isEmpty then throwError "diagram_eq: the {side} side is an identity"
    let ks ← fs.mapM (find side)
    for i in [1:ks.size] do
      let (_, _, t) := ms[ks[i-1]!]!
      let (_, s', _) := ms[ks[i]!]!
      unless t == s' do
        throwError "diagram_eq: the {side} side is not a path in the diagram"
    return (ks, fs)
  let (pk, pf) ← readSide "left" lhs
  let (qk, qf) ← readSide "right" rhs
  let ll ← compLeft pf
  let rl ← compLeft qf
  let pl ← liftM <| reassoc lhs ll
  let pr ← liftM <| reassoc rhs rl
  let mid ← mkAppM ``Diagrams.Commutes.evalNE_eq #[hD, ← d.path pk, ← d.path qk]
  let u ← getLevel α
  -- `lhs = ll = rl = rhs`; the middle step is `mid`, whose type is `ll = rl` by
  -- unfolding, which the kernel checks.
  let proof := mkApp6 (.const ``Eq.trans [u]) α lhs ll rhs pl
    (mkApp6 (.const ``Eq.trans [u]) α ll rl rhs mid (mkApp4 (.const ``Eq.symm [u]) α rhs rl pr))
  goal.assign proof
  replaceMainGoal []

/-- Prove an equation between composites of the morphisms of a commuting diagram,
given `h : Commutes G`: both sides must be paths in the diagram. -/
elab "diagram_eq " h:term : tactic => withMainContext do
  let hE ← Term.elabTerm h none
  let hTy ← whnfR (← instantiateMVars (← inferType hE))
  let some (W, G) := (match hTy.getAppFnArgs with
    | (``Commutes, #[W, _, _, _, G]) => some (W, G)
    | _ => none) | throwError "diagram_eq: the hypothesis is not `Commutes G`"
  if G.isAppOf ``Diagrams.toPrefunctor then
    diagramEqGraph hE G
  else
    diagramEqGeneric h W G

end Diagrams
