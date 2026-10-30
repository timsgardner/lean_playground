/-
# Drawing commuting diagrams

A presenter that draws a commuting diagram built by `comm_diagram` in the infoview,
in the style of Mathlib's commutative squares and triangles
(`Mathlib.Tactic.Widget.CommDiag`), which lay diagrams out with Penrose. Morphism
labels are set apart from objects: they have no box, and are a little smaller.

To see a diagram, put `show_panel_widgets [local ProofWidgets.SelectionPanel]` near
the top of a file. With the cursor in a proof after `let D := comm_diagram [...]`,
shift-click `D` (or its value) in the infoview, and choose "Commuting diagram".

The layout is computed from the diagram's canonical faces: around each face, one
side goes right and then down, and the other goes down and then right, as in a
square drawn on a blackboard; a side of one arrow is a diagonal. Positions are
propagated along the arrows, and an arrow that spans exactly one grid step gets a
Penrose positioning predicate. Other arrows are left for Penrose to place.
-/

import LeanPlayground.diagrams.frontend
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.PenroseDiagram

open Lean Meta ProofWidgets Mathlib.Tactic.Widget
open scoped ProofWidgets.Jsx

namespace Diagrams.Draw

/-- A direction on the grid: right is `(1, 0)`, down is `(0, 1)`. -/
abbrev Dir := Int × Int

/-- Directions for the arrows, from the faces: one side of each face goes right
then down, the other down then right; a side of one arrow is a diagonal. Arrows in
no face go right. -/
def directions (m : ℕ) (faces : Array Order.FaceData) : Array Dir := Id.run do
  let mut dirs : Array (Option Dir) := Array.replicate m none
  for (l, r) in faces do
    let n := l.size
    for i in [0:n] do
      let d : Dir := if n == 1 then (1, 1) else if i + 1 == n then (0, 1) else (1, 0)
      if dirs[l[i]!]!.isNone then dirs := dirs.set! l[i]! (some d)
    let n := r.size
    for i in [0:n] do
      let d : Dir := if n == 1 then (1, 1) else if i == 0 then (0, 1) else (1, 0)
      if dirs[r[i]!]!.isNone then dirs := dirs.set! r[i]! (some d)
  return dirs.map (·.getD (1, 0))

/-- Grid positions for the vertices, propagated along the arrows from their
directions. A vertex whose preferred cell is taken moves down to the next free
cell; each further component starts to the right of those before it. -/
def positions (n : ℕ) (ends : Array (ℕ × ℕ)) (dirs : Array Dir) : Array Dir := Id.run do
  let mut pos : Array (Option Dir) := Array.replicate n none
  let mut taken : Array Dir := #[]
  let free (taken : Array Dir) (p : Dir) : Dir := Id.run do
    let mut q := p
    while taken.contains q do q := (q.1, q.2 + 1)
    return q
  for start in [0:n] do
    if pos[start]!.isSome then continue
    let x := taken.foldl (fun m (a, _) => max m (a + 2)) 0
    let p := free taken (x, 0)
    pos := pos.set! start (some p)
    taken := taken.push p
    let mut changed := true
    while changed do
      changed := false
      for k in [0:ends.size] do
        let (a, b) := ends[k]!
        let (dx, dy) := dirs[k]!
        match pos[a]!, pos[b]! with
        | some (x, y), none =>
          let q := free taken (x + dx, y + dy)
          pos := pos.set! b (some q); taken := taken.push q; changed := true
        | none, some (x, y) =>
          let q := free taken (x - dx, y - dy)
          pos := pos.set! a (some q); taken := taken.push q; changed := true
        | _, _ => pure ()
  return pos.map (·.getD (0, 0))

/-- The Penrose positioning predicate for an arrow from `p` to `q`, if they are one
grid step apart. -/
def predicate (p q : Dir) : Option String :=
  match q.1 - p.1, q.2 - p.2 with
  | 1, 0 => some "IsRightHorizontal"
  | -1, 0 => some "IsLeftHorizontal"
  | 0, 1 => some "IsDownVertical"
  | 0, -1 => some "IsUpVertical"
  | 1, 1 => some "IsRightDownDiagonal"
  | 1, -1 => some "IsRightUpDiagonal"
  | -1, 1 => some "IsLeftDownDiagonal"
  | -1, -1 => some "IsLeftUpDiagonal"
  | _, _ => none

/-- The Penrose substance program for a diagram with `n` vertices, arrows with
`ends`, and `faces`: vertices are `O0, O1, …` and arrows `M0, M1, …`. -/
def substance (n : ℕ) (ends : Array (ℕ × ℕ)) (faces : Array Order.FaceData) : String :=
  let dirs := directions ends.size faces
  let pos := positions n ends dirs
  let objs := ", ".intercalate ((List.range n).map (s!"O{·}"))
  let cells := (List.range ends.size).map fun k =>
    let (a, b) := ends[k]!
    s!"Cell M{k} := MakeCell(O{a}, O{b})"
  let preds := (List.range ends.size).filterMap fun k =>
    let (a, b) := ends[k]!
    (predicate pos[a]! pos[b]!).map (s!"{·}(M{k})")
  "\n".intercalate ([s!"Object {objs}"] ++ cells ++ preds ++ ["AutoLabel All"])

/-- Mathlib's Penrose domain program for commutative diagrams. -/
def dsl : String :=
  include_str "../../.lake/packages/mathlib/widget/src/penrose/commutative.dsl"

/-- Mathlib's Penrose style program for commutative diagrams, with morphism labels
set apart from objects: an object keeps its box, while a morphism's label has no
border and interrupts its arrow, as in tikz-cd. -/
def sty : String :=
  (include_str "../../.lake/packages/mathlib/widget/src/penrose/commutative.sty") ++
  "
forall Cell f {
    override f.textBox.strokeWidth = 0
    override f.textBox.fillColor = theme.background
}
"

/-- A Penrose diagram from a substance program whose objects `O0, O1, …` are labelled
by `objs` and whose arrows `M0, M1, …` by `mors`. Objects are drawn as Lean prints
them; morphism labels a little smaller and lighter. -/
def penroseHtml (sub : String) (objs : Array (Option Expr)) (mors : Array Expr) :
    MetaM ProofWidgets.Html := do
  let mut embeds : Array (String × ProofWidgets.Html) := #[]
  for i in [0:objs.size] do
    if let some X := objs[i]! then
      embeds := embeds.push (s!"O{i}", jsx%{<InteractiveCode fmt={← Widget.ppExprTagged X} />})
  for k in [0:mors.size] do
    embeds := embeds.push (s!"M{k}",
      jsx%{<span style={json% {fontSize: "85%", opacity: 0.8}}>
        <InteractiveCode fmt={← Widget.ppExprTagged mors[k]!} />
      </span>})
  return jsx%{<PenroseDiagram embeds={embeds} dsl={dsl} sty={sty} sub={sub} />}

/-- The diagram `e`, built by `comm_diagram`, as Html. -/
def diagramHtml (e : Expr) : MetaM ProofWidgets.Html := do
  let some dv ← readDiagram e
    | throwError "Not a commuting diagram built by comm_diagram, or its value is not visible."
  let ends := dv.ms.map fun (_, a, b) => (a, b)
  let shape : Order.Shape := ⟨dv.n, ends, (List.range ends.size).toArray⟩
  let faces := shape.inferFaces
  -- Each vertex is labelled by the domain or codomain of a morphism at it.
  let mut objs : Array (Option Expr) := Array.replicate dv.n none
  for (f, a, b) in dv.ms do
    let some (A, B) := homType? (← whnfR (← inferType f)) | continue
    if objs[a]!.isNone then objs := objs.set! a (some A)
    if objs[b]!.isNone then objs := objs.set! b (some B)
  penroseHtml (substance dv.n ends faces) objs (dv.ms.map (·.1))

/-- Draw a commuting diagram built by `comm_diagram`. -/
@[expr_presenter]
def commDiagramPresenter : ExprPresenter where
  userName := "Commuting diagram"
  layoutKind := .block
  present e := diagramHtml e

/-! ## Path equations

An equation `p₁ = p₂` between composites is drawn as two paths from a common source
to a common target, one arrow per factor (bracketing and identities are ignored):
`p₁` goes right along the top row and then down, and `p₂` goes down and then right
along the bottom row, as a square is drawn. When both sides are single morphisms
they are drawn as two curved arrows. -/

/-- The drawing of an equation between composites: a substance program, the objects
of its vertices, and the morphisms of its arrows. `e` is the equation, or a proof of
it. -/
def equationDrawing (e : Expr) : MetaM (String × Array (Option Expr) × Array Expr) := do
  let e ← instantiateMVars e
  let ty ← if e.isAppOfArity ``Eq 3 then pure e else whnfR (← instantiateMVars (← inferType e))
  let some (_, lhs, rhs) := ty.eq? | throwError "Not an equation."
  let some (S, T) := homType? (← whnfR (← inferType lhs))
    | throwError "Not an equation between morphisms."
  let fl := (← factors lhs).toArray
  let fr := (← factors rhs).toArray
  if fl.isEmpty || fr.isEmpty then throwError "A side of the equation is an identity."
  let m := fl.size
  let n := fr.size
  -- Vertices: 0 is the source, `1, …, m-1` lie on the left side, `m, …, m+n-2` on the
  -- right side, and `m+n-1` is the target.
  let tgt := m + n - 1
  let lv (i : ℕ) : ℕ := if i == m then tgt else i
  let rv (j : ℕ) : ℕ := if j == 0 then 0 else if j == n then tgt else m - 1 + j
  let mut pos : Array Dir := Array.replicate (tgt + 1) (0, 0)
  for i in [1:m] do pos := pos.set! i (i, 0)
  for j in [1:n] do pos := pos.set! (m - 1 + j) ((j : Int) - 1, 1)
  pos := pos.set! tgt <| if m == 1 && n == 1 then (1, 0)
    else if n ≥ 2 then ((n : Int) - 1, 1) else ((m : Int) - 1, 1)
  -- Objects: the source, then the codomain of each factor.
  let mut objs : Array (Option Expr) := Array.replicate (tgt + 1) none
  objs := (objs.set! 0 (some S)).set! tgt (some T)
  for i in [0:m - 1] do
    if let some (_, B) := homType? (← whnfR (← inferType fl[i]!)) then
      objs := objs.set! (lv (i + 1)) (some B)
  for j in [0:n - 1] do
    if let some (_, B) := homType? (← whnfR (← inferType fr[j]!)) then
      objs := objs.set! (rv (j + 1)) (some B)
  let ends := (Array.range m).map (fun i => (lv i, lv (i + 1))) ++
    (Array.range n).map (fun j => (rv j, rv (j + 1)))
  let cells := (List.range ends.size).map fun k =>
    let (a, b) := ends[k]!
    s!"Cell M{k} := MakeCell(O{a}, O{b})"
  let preds := (List.range ends.size).filterMap fun k =>
    let (a, b) := ends[k]!
    (predicate pos[a]! pos[b]!).map (s!"{·}(M{k})")
  let curves := if m == 1 && n == 1 then ["IsCurvedLeft(M0)", "IsCurvedRight(M1)"] else []
  let objNames := ", ".intercalate ((List.range (tgt + 1)).map (s!"O{·}"))
  let sub := "\n".intercalate ([s!"Object {objNames}"] ++ cells ++ preds ++ curves ++ ["AutoLabel All"])
  return (sub, objs, fl ++ fr)

/-- An equation between composites, as Html. -/
def equationHtml (e : Expr) : MetaM ProofWidgets.Html := do
  let (sub, objs, mors) ← equationDrawing e
  penroseHtml sub objs mors

/-- Draw an equation between composites as two paths. -/
@[expr_presenter]
def pathEquationPresenter : ExprPresenter where
  userName := "Path equation"
  layoutKind := .block
  present e := equationHtml e

end Diagrams.Draw
