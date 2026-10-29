/-
# Build orders and canonical faces

A build adds a diagram's arrows one at a time, and the order is an internal
choice: it decides whether the declared faces cover every cell each arrow
closes, but not what is proved. This module chooses the order, so that nothing
the user sees depends on the order in which arrows are written. It works on
plain data (arrow numbers and reachability bitmasks) and runs outside the
kernel; whatever it chooses is then checked by the kernel (`buildOK`), so a
wrong choice can only make a declaration fail, never prove something false.

* `findOrder` searches for an order in which the faces cover every cell. The
  coverage test (`coveredStep`) mirrors the kernel's `coversOK` exactly.
  Arrows that close no cell go first; otherwise arrows are tried by rank, with
  backtracking (memoized on the set of arrows added) as a fallback.
* `inferFaces` chooses faces for a shape declared without them. It builds in a
  canonical order that always closes the smallest available cell next, takes the
  minimal cells as faces, and then drops every face that the others imply,
  largest first. The result depends only on the shape and the arrow names.

Ties are broken by `rank`, the position of each arrow's name in sorted order,
never by declaration order. A commutative diagram has no unique irredundant set
of faces in general (a square with a diagonal has three), so some fixed rule for
ties is unavoidable; smallest-first picks the regions of a drawing.
-/

import Std.Data.HashSet

namespace Diagrams.Order

/-- A shape as plain data: the number of vertices, the source and target of each
arrow, and a rank per arrow for breaking ties. -/
structure Shape where
  /-- The number of vertices. -/
  n : Nat
  /-- The source and target of each arrow. -/
  ends : Array (Nat × Nat)
  /-- The rank of each arrow, for breaking ties. -/
  rank : Array Nat

/-- A face as plain data: its two sides, as arrow numbers. -/
abbrev FaceData := Array Nat × Array Nat

/-- The arrows added so far, as a bitmask, and for each vertex the bitmask of
the vertices it reaches through them. -/
structure State where
  /-- The reach of each vertex (each vertex reaches itself). -/
  reach : Array Nat
  /-- The arrows added, as a bitmask. -/
  added : Nat

/-- Whether arrow `k` has been added. -/
def State.has (st : State) (k : Nat) : Bool := st.added.testBit k

/-- The perimeter of a face: the number of arrows on its two sides. -/
def perimeter (φ : FaceData) : Nat := φ.1.size + φ.2.size

/-- Faces, with the faces containing each arrow, for quick lookup. -/
structure Faces where
  /-- The faces. -/
  data : Array FaceData
  /-- For each arrow, the faces containing it. -/
  byArrow : Array (List Nat)

/-- Index faces by their arrows, for a shape with `m` arrows. -/
def Faces.mk' (m : Nat) (data : Array FaceData) : Faces :=
  ⟨data, (List.range data.size).foldl (fun acc i =>
    ((data[i]!.1 ++ data[i]!.2).toList.eraseDups).foldl
      (fun acc a => if a < m then acc.modify a (i :: ·) else acc) acc)
    (Array.replicate m [])⟩

/-- The faces that adding `k` completes: those containing `k` once, all of whose
other arrows are present. -/
def State.completes (st : State) (faces : Faces) (k : Nat) : List Nat :=
  faces.byArrow[k]!.filter fun i =>
    let all := faces.data[i]!.1 ++ faces.data[i]!.2
    all.count k == 1 && all.all fun a => a == k || st.has a

namespace Shape

variable (s : Shape)

/-- The number of arrows. -/
def size : Nat := s.ends.size

/-- The source of arrow `k`. -/
def src (k : Nat) : Nat := s.ends[k]!.1

/-- The target of arrow `k`. -/
def tgt (k : Nat) : Nat := s.ends[k]!.2

/-- Sort arrows by rank. -/
def sortByRank (l : List Nat) : List Nat := l.mergeSort fun a b => s.rank[a]! ≤ s.rank[b]!

/-- The state with no arrows. -/
def init : State := ⟨(Array.range s.n).map (1 <<< ·), 0⟩

/-- Add arrow `k`: a vertex that reached its source now also reaches everything
its target reaches. -/
def add (st : State) (k : Nat) : State :=
  let mv := st.reach[s.tgt k]!
  ⟨st.reach.map fun m => if m.testBit (s.src k) then m ||| mv else m, st.added ||| (1 <<< k)⟩


/-- The source and target of a face. -/
def faceEnds (φ : FaceData) : Nat × Nat := (s.src φ.1[0]!, s.tgt φ.1.back!)


/-- Adding `k` closes no cycle, and the faces it completes cover every cell it
closes. This mirrors the kernel's check (`stepOK`, `coversOK`). -/
def coveredStep (st : State) (faces : Faces) (k : Nat) : Bool :=
  let u := s.src k
  let v := s.tgt k
  if st.reach[v]!.testBit u then false else
  let uses := (st.completes faces k).map fun i =>
    let (a, b) := s.faceEnds faces.data[i]!
    (a, st.reach[b]!)
  if st.reach[u]!.testBit v then
    uses.any fun (a, mt) => st.reach[u]!.testBit a && mt.testBit v
  else
    let mv := st.reach[v]!
    st.reach.all fun mx =>
      !mx.testBit u ||
        let cover := uses.foldl (fun c (a, mt) => if mx.testBit a then c ||| mt else c) 0
        (mx &&& mv &&& cover) == (mx &&& mv)

/-- Adding `k` closes some cell. -/
def closesCell (st : State) (k : Nat) : Bool :=
  let mv := st.reach[s.tgt k]!
  st.reach.any fun mx => mx.testBit (s.src k) && (mx &&& mv) != 0

/-- The bits of `a` not in `b`. -/
def diff (a b : Nat) : Nat := a ^^^ (a &&& b)

/-- The full set of arrows, as a bitmask. -/
def full : Nat := (1 <<< s.size) - 1

/-! ## Searching for an order -/

/-- The arrows not yet added, in order of preference: those that close no cell,
then the rest, each by rank. Whether each can be added is tested lazily. -/
def preferred (st : State) : List Nat :=
  let rest := (List.range s.size).filter fun k => !st.has k
  let (quiet, loud) := rest.partition (!s.closesCell st ·)
  s.sortByRank quiet ++ s.sortByRank loud

/-- The arrows that can be added next with every cell covered, in order of
preference. -/
def candidates (st : State) (faces : Faces) : List Nat :=
  (s.preferred st).filter (s.coveredStep st faces)

/-- Depth-first search for a complete order, memoizing the sets of added arrows
from which no order succeeds, within a budget of expansions. -/
partial def dfs (faces : Faces) (st : State) (acc : List Nat) :
    StateM (Std.HashSet Nat × Nat) (Option (List Nat)) := do
  if st.added == s.full then return some acc.reverse
  let (failed, budget) ← get
  if failed.contains st.added || budget == 0 then return none
  set (failed, budget - 1)
  for k in s.preferred st do
    if s.coveredStep st faces k then
      if let some o ← dfs faces (s.add st k) (k :: acc) then return some o
  modify fun (f, b) => (f.insert st.added, b)
  return none

/-- Search for an order of all the arrows in which the faces cover every cell.
Returns the order if one is found, and otherwise whether the search was
exhaustive (so that no such order exists) rather than cut off by the budget. -/
def searchOrder (faces : Array FaceData) (budget : Nat := 10000) : Option (List Nat) × Bool :=
  let faces := Faces.mk' s.size faces
  let (o, _, left) := (s.dfs faces s.init []).run ({}, budget) |> fun (o, st) => (o, st.1, st.2)
  (o, left > 0)

/-- An order of all the arrows in which the faces cover every cell, if the search
finds one. -/
def findOrder (faces : Array FaceData) (budget : Nat := 10000) : Option (List Nat) :=
  (s.searchOrder faces budget).1

/-- For an order, the faces each arrow completes, as `(face, side, position)`:
the side containing the arrow (`false` for the left) and its position there. -/
def faceUses (faces : Array FaceData) (order : List Nat) : List (List (Nat × Bool × Nat)) :=
  let faces := Faces.mk' s.size faces
  let step := fun (st, out) k =>
    let us := (st.completes faces k).map fun i =>
      let (l, r) := faces.data[i]!
      match l.idxOf? k with
      | some p => (i, false, p)
      | none => (i, true, (r.idxOf? k).getD 0)
    (s.add st k, us :: out)
  ((order.foldl step (s.init, [])).2).reverse

/-! ## Cells and paths -/

/-- Shortest paths from `x` through the added arrows, trying arrows by rank: for
each vertex, the arrows of a path from `x`, if there is one. -/
def pathsFrom (st : State) (x : Nat) : Array (Option (List Nat)) := Id.run do
  let arrows := s.sortByRank ((List.range s.size).filter (st.has ·))
  let mut paths : Array (Option (List Nat)) := (Array.replicate s.n none).set! x (some [])
  let mut queue := #[x]
  let mut i := 0
  while i < queue.size do
    let w := queue[i]!
    i := i + 1
    let p := paths[w]!.getD []
    for a in arrows do
      if s.src a == w && paths[s.tgt a]!.isNone then
        paths := paths.set! (s.tgt a) (some (p ++ [a]))
        queue := queue.push (s.tgt a)
  return paths

/-- The minimal cells that adding `k` closes, as pairs `(x, y)`. If the source
already reaches the target, that pair is the only one. Otherwise `(x, y)` is
minimal when neither end can move inwards: no other end `y₀` of `x` reaches `y`,
and no other start `x₀` reached from `x` has `y` as an end. -/
def minimalCells (st : State) (k : Nat) : List (Nat × Nat) :=
  let u := s.src k
  let v := s.tgt k
  if st.reach[u]!.testBit v then [(u, v)] else
  let mv := st.reach[v]!
  let starts := (List.range s.n).filter fun x => st.reach[x]!.testBit u
  let startMask := starts.foldl (fun m x => m ||| (1 <<< x)) 0
  let bits (m : Nat) : List Nat := (List.range s.n).filter m.testBit
  starts.flatMap fun x =>
    let ends := st.reach[x]! &&& mv
    -- Ends reached strictly beyond another end of `x`.
    let beyond := (bits ends).foldl (fun c y₀ => c ||| diff st.reach[y₀]! (1 <<< y₀)) 0
    -- Ends of a start strictly inside `x`.
    let inner := (bits (diff (st.reach[x]! &&& startMask) (1 <<< x))).foldl
      (fun c x₀ => c ||| (st.reach[x₀]! &&& mv)) 0
    (bits (diff (diff ends beyond) inner)).map (x, ·)

/-- The face of a cell that adding `k` closes at `(x, y)`: the new path through `k`
on the left, the shortest old path on the right, with shortest paths chosen by
rank. -/
def cellFace (st : State) (k x y : Nat) : Option FaceData := do
  let fromX := s.pathsFrom st x
  let α ← fromX[s.src k]!
  let γ ← fromX[y]!
  let β ← (s.pathsFrom st (s.tgt k))[y]!
  return ((α ++ [k] ++ β).toArray, γ.toArray)


/-! ## Canonical faces -/

/-- Shortest distances through the added arrows: `d[a][b]`, or more than the
number of arrows when `b` is not reachable from `a`. -/
def distances (st : State) : Array (Array Nat) := Id.run do
  let inf := s.size + 1
  let mut out : Array (List Nat) := Array.replicate s.n []
  for k in [0:s.size] do
    if st.has k then out := out.modify (s.src k) (s.tgt k :: ·)
  let mut res := #[]
  for a in [0:s.n] do
    let mut d := (Array.replicate s.n inf).set! a 0
    let mut queue := #[a]
    let mut i := 0
    while i < queue.size do
      let w := queue[i]!
      i := i + 1
      for t in out[w]! do
        if d[t]! == inf then
          d := d.set! t (d[w]! + 1)
          queue := queue.push t
    res := res.push d
  return res

/-- Every arrow can be added without closing a cycle: the shape is acyclic. (A
cycle would be closed by whichever of its arrows came last.) -/
def acyclic : Bool :=
  ((List.range s.size).foldl (fun (st, ok) k =>
    (s.add st k, ok && !st.reach[s.tgt k]!.testBit (s.src k))) (s.init, true)).2

/-- The canonical order: at each step, an arrow that closes no cell (by rank) if
there is one; otherwise the arrow closing the smallest cell, measured by its
perimeter (by rank among equals). -/
partial def canonicalOrder : State → List Nat → List Nat
  | st, acc =>
    let rest := (List.range s.size).filter fun k =>
      !st.has k && !st.reach[s.tgt k]!.testBit (s.src k)
    if rest.isEmpty then acc.reverse else
    match s.sortByRank (rest.filter (!s.closesCell st ·)) with
    | k :: _ => canonicalOrder (s.add st k) (k :: acc)
    | [] =>
      let d := s.distances st
      let score (k : Nat) : Nat :=
        (s.minimalCells st k).foldl (fun m (x, y) =>
          min m (d[x]![s.src k]! + 1 + d[s.tgt k]![y]! + d[x]![y]!)) (4 * s.size + 4)
      let best := (s.sortByRank rest).foldl (fun b k =>
        let sc := score k
        match b with
        | some (_, sc') => if sc < sc' then some (k, sc) else b
        | none => some (k, sc)) none
      match best with
      | some (k, _) => canonicalOrder (s.add st k) (k :: acc)
      | none => acc.reverse

/-- Compare faces: smaller perimeter first, then by the ranks of their arrows. -/
def faceLT (φ ψ : FaceData) : Bool :=
  let key (χ : FaceData) := (χ.1 ++ χ.2).toList.map (s.rank[·]!)
  perimeter φ < perimeter ψ ||
    (perimeter φ == perimeter ψ && compare (key φ) (key ψ) == .lt)

/-- Faces for a shape declared without them: the minimal cells closed along the
canonical order, with every face that the others imply dropped (largest first),
in canonical order. -/
def inferFaces : Array FaceData := Id.run do
  let order := s.canonicalOrder s.init []
  let mut faces : Array FaceData := #[]
  let mut st := s.init
  for k in order do
    for (x, y) in s.minimalCells st k do
      if let some φ := s.cellFace st k x y then faces := faces.push φ
    st := s.add st k
  -- Drop faces implied by the others, largest first. The test is a greedy search
  -- with a small budget: a face it keeps may still be redundant, but a face it
  -- drops is not needed.
  let mut kept := faces.toList
  for φ in (faces.toList.mergeSort fun a b => s.faceLT b a) do
    let others := kept.filter (· != φ)
    if (s.findOrder others.toArray (2 * s.size + 2)).isSome then kept := others
  return (kept.mergeSort fun a b => s.faceLT a b).toArray

/-! ## Explaining a failure -/

/-- When no order is found: follow the preferred candidates until none is left,
then report the first remaining arrow (by rank) that closes no cycle, with a cell
it closes that no face covers, as `(arrow, face of the cell)`. -/
partial def explainFailure (faces : Array FaceData) : Option (Nat × FaceData) :=
  let faces := Faces.mk' s.size faces
  let rec go (st : State) : Option (Nat × FaceData) :=
    match s.candidates st faces with
    | k :: _ => go (s.add st k)
    | [] =>
      let rest := s.sortByRank ((List.range s.size).filter fun k =>
        !st.has k && !st.reach[s.tgt k]!.testBit (s.src k))
      rest.findSome? fun k =>
        let uses := (st.completes faces k).map fun i =>
          s.faceEnds faces.data[i]!
        (s.minimalCells st k).findSome? fun (x, y) =>
          if uses.any (fun (a, b) => st.reach[x]!.testBit a && st.reach[b]!.testBit y) then none
          else (s.cellFace st k x y).map (k, ·)
  go s.init

end Shape

end Diagrams.Order
