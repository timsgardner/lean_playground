/-
# Drawing commuting diagrams

A presenter that draws a commuting diagram built by `comm_diagram` in the infoview,
in the style of Mathlib's commutative squares and triangles
(`Mathlib.Tactic.Widget.CommDiag`), which lay diagrams out with Penrose.

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

open Lean Meta ProofWidgets Mathlib.Tactic.Widget

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
  let mut embeds : ExprEmbeds := #[]
  for i in [0:dv.n] do
    if let some X := objs[i]! then embeds := embeds.push (s!"O{i}", X)
  for k in [0:dv.ms.size] do
    embeds := embeds.push (s!"M{k}", dv.ms[k]!.1)
  mkCommDiag (substance dv.n ends faces) embeds

/-- Draw a commuting diagram built by `comm_diagram`. -/
@[expr_presenter]
def commDiagramPresenter : ExprPresenter where
  userName := "Commuting diagram"
  layoutKind := .block
  present e := diagramHtml e

end Diagrams.Draw
