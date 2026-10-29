/-
# Certificates and the tactics that find them

`decide` makes the kernel run a whole decision procedure by rewriting terms, which
is slow. This file splits the work. A tactic runs the search as ordinary compiled
code, and writes its answer into the proof as a *certificate*. The kernel only
checks the certificate, in one pass.

| Goal | Certificate | Check | Tactic |
|---|---|---|---|
| `AcyclicOn S` | a rank for each vertex, packed into one number | every arrow of `S` goes up in rank (`rankCheck`) | `diagram_acyclic` |
| `¬ ReachIn S v u` | a fence: a bitmask closed under arrows of `S`, containing `v` but not `u` | `fenceCheck` | `diagram_unreachable` |
| `Nonempty (Chase faces p q)` | a chase script | replaying it turns `p` into `q` (`replayCheck`) | `find_chase` |

The checks are Boolean functions, proved sound once (`acyclicOn_of_rankCheck`,
`not_reachIn_of_fenceCheck`, `chase_of_replayCheck`). The searches are not trusted:
a wrong certificate makes the check fail, never a false proof.

To find a certificate, a tactic asks Lean to evaluate the shape's arrows, as pairs
of vertex indices, with compiled code (`Lean.Meta.evalExpr`). So the shape must be
given by computable definitions, which concrete shapes are.
-/

import LeanPlayground.diagrams.decide
import LeanPlayground.diagrams.search

open CategoryTheory Quiver Lean Meta Elab Tactic

namespace Diagrams

universe w v₁ u₁

variable {W : Type u₁} [Quiver.{v₁} W]

/-! ## Certificate checks -/

section Checks

variable [FinShape W] [NumShape W] (S : Subshape W) [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)]

open NumShape

/-- Field number `i`, `w` bits wide, of the packed number `R`. -/
def field (w R i : ℕ) : ℕ := (R >>> (i * w)) % 2 ^ w

/-- Every arrow of `S` goes up in the rank packed in `R`, with fields `w` bits wide. -/
def rankCheck (w R : ℕ) : Bool :=
  (FinShape.arrows : List (Total W)).all fun e =>
    !(decide (e.hom ∈ S e.left e.right)) ||
      decide (field w R (index e.left) < field w R (index e.right))

/-- The bitmask `X` is a fence from `v` to `u`: closed under arrows of `S`,
containing `v` but not `u`. -/
def fenceCheck (X : ℕ) (v u : W) : Bool :=
  X.testBit (index v) && !X.testBit (index u) && closedMask S X

/-- The arrows of `S`, as pairs of vertex indices. -/
def arrowPairs : List (ℕ × ℕ) :=
  ((FinShape.arrows : List (Total W)).filter fun e => decide (e.hom ∈ S e.left e.right)).map
    fun e => (index e.left, index e.right)

variable {S}

/-- **Rank certificate.** -/
theorem acyclicOn_of_rankCheck {w R : ℕ} (h : rankCheck S w R = true) : AcyclicOn S :=
  acyclicOn_of_rank (fun a => field w R (index a)) fun a b f hf => by
    simp only [rankCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    rcases h (arrow f) (FinShape.mem_arrows _) with h | h
    · exact absurd hf h
    · exact h

/-- **Fence certificate.** -/
theorem not_reachIn_of_fenceCheck {X : ℕ} {v u : W} (h : fenceCheck S X v u = true) :
    ¬ ReachIn S v u := by
  simp only [fenceCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hv, hu⟩, hc⟩ := h
  exact not_reachIn_of_closed (fun w => X.testBit (index w) = true)
    (fun _ _ _ hf hx => mem_of_closedMask hc hf hx) hv (by rw [hu]; exact Bool.false_ne_true)

/-- The position of an arrow in the arrow list of the shape. -/
def arrowIdx [DecidableEq (Total W)] (e : Total W) : ℕ :=
  (FinShape.arrows : List (Total W)).idxOf e

/-- The data a chase search needs, as numbers: for each listed face, its two sides
as lists of arrow positions together with the indices of its source and target;
the index of the start vertex; the arrow positions of `p` and `q`; and the index of
the target of each arrow. -/
def chaseData [DecidableEq (Total W)] {Φ : Type*} (faces : Φ → Face W) (names : List Φ)
    {a b : W} (p q : Path a b) :
    List (List ℕ × List ℕ × ℕ × ℕ) × ℕ × List ℕ × List ℕ × List ℕ :=
  (names.map fun φ => ((faces φ).lhs.edges.map arrowIdx, (faces φ).rhs.edges.map arrowIdx,
      index (faces φ).src, index (faces φ).tgt),
    index a, p.edges.map arrowIdx, q.edges.map arrowIdx,
    (FinShape.arrows : List (Total W)).map fun e => index e.right)

end Checks

/-! ## Searches, as compiled code -/

namespace Search

/-- Ranks from a topological sort of `n` vertices with the given arrows, or `none`
if there is a cycle (a loop counts as a cycle). -/
def topoRanks (n : ℕ) (pairs : List (ℕ × ℕ)) : Option (Array ℕ) := Id.run do
  let mut indeg : Array ℕ := Array.replicate n 0
  let mut succ : Array (List ℕ) := Array.replicate n []
  for (a, b) in pairs do
    indeg := indeg.modify b (· + 1)
    succ := succ.modify a (b :: ·)
  let mut queue : List ℕ := (List.range n).filter fun i => indeg[i]! == 0
  let mut rank : Array ℕ := Array.replicate n 0
  let mut count := 0
  for _ in [0:n] do
    match queue with
    | [] => break
    | x :: rest =>
      queue := rest
      rank := rank.set! x count
      count := count + 1
      for y in succ[x]! do
        indeg := indeg.modify y (· - 1)
        if indeg[y]! == 0 then queue := y :: queue
  return if count == n then some rank else none

/-- Pack `values` into one number, `w` bits per value. -/
def pack (w : ℕ) (values : Array ℕ) : ℕ :=
  values.foldr (fun v acc => (acc <<< w) ||| v) 0

/-- The vertices reachable from `start`, as a bitmask. -/
def reachBits (n start : ℕ) (pairs : List (ℕ × ℕ)) : ℕ := Id.run do
  let mut succ : Array (List ℕ) := Array.replicate n []
  for (a, b) in pairs do
    succ := succ.modify a (b :: ·)
  let mut seen : Array Bool := (Array.replicate n false).set! start true
  let mut stack : List ℕ := [start]
  for _ in [0:n + pairs.length + 1] do
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      for y in succ[x]! do
        if !seen[y]! then
          seen := seen.set! y true
          stack := y :: stack
  return (List.range n).foldl (fun m i => if seen[i]! then m ||| (1 <<< i) else m) 0

/-- Breadth-first search for a chase script, on paths given as arrays of arrow
positions, with a hash set of visited paths. `faces` lists each face's two sides
and the indices of its source and target; `right` gives the index of the target of
each arrow; `start` is the index of the paths' common start. Each side is indexed by
its first arrow, so at each position only the faces that can start there are
tried. -/
def chaseScript (faces : Array (List ℕ × List ℕ × ℕ × ℕ)) (right : Array ℕ) (start : ℕ)
    (p q : List ℕ) (maxStates : ℕ) : Option (List IdxStep) := Id.run do
  -- The side each step rewrites from, indexed by its first arrow; empty sides apart.
  let mut byFirst : Std.HashMap ℕ (List (ℕ × Bool)) := {}
  let mut emptySides : List (ℕ × Bool) := []
  for k in [0:faces.size] do
    let (lhs, rhs, _, _) := faces[k]!
    for (side, bwd) in [(lhs, false), (rhs, true)] do
      match side with
      | [] => emptySides := (k, bwd) :: emptySides
      | x :: _ => byFirst := byFirst.insert x ((k, bwd) :: byFirst.getD x [])
  let target := q.toArray
  let vertexAt (l : Array ℕ) (n : ℕ) : ℕ := if n = 0 then start else right[l[n - 1]!]!
  let mut seen : Std.HashSet (Array ℕ) := Std.HashSet.emptyWithCapacity.insert p.toArray
  let mut frontier : Array (Array ℕ × List IdxStep) := #[(p.toArray, [])]
  let mut explored := 0
  while !frontier.isEmpty && explored < maxStates do
    let mut next : Array (Array ℕ × List IdxStep) := #[]
    for (l, script) in frontier do
      if l == target then return some script.reverse
      explored := explored + 1
      for n in [0:l.size + 1] do
        let candidates := (if n < l.size then byFirst.getD l[n]! [] else []) ++ emptySides
        for (k, bwd) in candidates do
          let (lhs, rhs, src, _) := faces[k]!
          let (from_, to_) := if bwd then (rhs, lhs) else (lhs, rhs)
          if vertexAt l n == src && (l.extract n (n + from_.length)).toList == from_ then
            let l' := l.extract 0 n ++ to_.toArray ++ l.extract (n + from_.length) l.size
            if !seen.contains l' then
              seen := seen.insert l'
              next := next.push (l', (k, bwd, n) :: script)
    frontier := next
  return none

end Search

/-! ## Evaluating shape data -/

unsafe def evalPairsImpl (e : Expr) : MetaM (List (ℕ × ℕ)) := do
  evalExpr (List (ℕ × ℕ)) (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]) e

/-- Evaluate an expression of type `List (ℕ × ℕ)` with compiled code. -/
@[implemented_by evalPairsImpl] opaque evalPairs (e : Expr) : MetaM (List (ℕ × ℕ))

unsafe def evalNatImpl (e : Expr) : MetaM ℕ := evalExpr ℕ (mkConst ``Nat) e

/-- Evaluate an expression of type `ℕ` with compiled code. -/
@[implemented_by evalNatImpl] opaque evalNat (e : Expr) : MetaM ℕ

/-- The type of `chaseData`'s value. -/
abbrev ChaseData : Type := List (List ℕ × List ℕ × ℕ × ℕ) × ℕ × List ℕ × List ℕ × List ℕ

unsafe def evalChaseDataImpl (e : Expr) : MetaM ChaseData :=
  evalExpr ChaseData (mkConst ``ChaseData) e

/-- Evaluate an expression of type `ChaseData` with compiled code. -/
@[implemented_by evalChaseDataImpl] opaque evalChaseData (e : Expr) : MetaM ChaseData

/-- The number of vertices of the shape `W`, and the arrows of `S` as index pairs. -/
def shapeData (W S : Expr) : MetaM (ℕ × List (ℕ × ℕ)) := do
  let n ← evalNat (← mkAppOptM ``NumShape.size #[W, none, none])
  let pairs ← evalPairs (← mkAppOptM ``arrowPairs #[W, none, none, none, S, none])
  return (n, pairs)

/-! ## Tactics -/

/-- Prove `AcyclicOn S` on a finite numbered shape: a topological sort, run as
compiled code, gives ranks; the kernel checks that every arrow goes up. -/
elab "diagram_acyclic" : tactic => do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (W, S) := (match ty.getAppFnArgs with
    | (``AcyclicOn, #[W, _, S]) => some (W, S)
    | _ => none) | throwError "diagram_acyclic: the goal is not `AcyclicOn S`"
  let (n, pairs) ← shapeData W S
  let some ranks := Search.topoRanks n pairs
    | throwError "diagram_acyclic: the subshape has a cycle"
  let w := Nat.log2 n + 1
  let R := Search.pack w ranks
  evalTactic (← `(tactic| exact acyclicOn_of_rankCheck (w := $(quote w)) (R := $(quote R)) (by decide +kernel)))

/-- Prove `¬ ReachIn S v u` on a finite numbered shape: the vertices reachable from
`v`, found by compiled code, form a fence; the kernel checks that it is closed and
leaves out `u`. -/
elab "diagram_unreachable" : tactic => do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some body := ty.not? | throwError "diagram_unreachable: the goal is not `¬ ReachIn S v u`"
  let some (W, S, v, u) := (match body.getAppFnArgs with
    | (``ReachIn, #[W, _, S, v, u]) => some (W, S, v, u)
    | _ => none) | throwError "diagram_unreachable: the goal is not `¬ ReachIn S v u`"
  let (n, pairs) ← shapeData W S
  let iv ← evalNat (← mkAppOptM ``NumShape.index #[W, none, none, v])
  let iu ← evalNat (← mkAppOptM ``NumShape.index #[W, none, none, u])
  let X := Search.reachBits n iv pairs
  if X.testBit iu then
    throwError "diagram_unreachable: there is a path"
  evalTactic (← `(tactic| exact not_reachIn_of_fenceCheck (X := $(quote X)) (by decide +kernel)))

/-- Prove `Nonempty (Chase faces p q)` by searching for a chase script with compiled
code, using the faces in `names` and visiting at most `limit` paths; the kernel
replays the script. -/
elab "find_chase " names:term:max limit:num : tactic => do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some chase := (match ty.getAppFnArgs with
    | (``Nonempty, #[c]) => some c
    | _ => none) | throwError "find_chase: the goal is not `Nonempty (Chase faces p q)`"
  let (``Chase, args) := chase.getAppFnArgs
    | throwError "find_chase: the goal is not `Nonempty (Chase faces p q)`"
  let faces := args[3]!
  let p := args[6]!
  let q := args[7]!
  let namesE ← Term.elabTerm names none
  let dataE ← mkAppOptM ``chaseData
    #[none, none, none, none, none, none, faces, namesE, none, none, p, q]
  let (fs, start, ps, qs, right) ← evalChaseData dataE
  let some steps := Search.chaseScript fs.toArray right.toArray start ps qs limit.getNat
    | throwError "find_chase: no chase found after visiting {limit.getNat} paths"
  let stepsStx ← Term.exprToSyntax (toExpr steps)
  evalTactic (← `(tactic| exact chase_of_replayCheck (names := $names) (steps := $stepsStx) (by decide +kernel)))

end Diagrams
