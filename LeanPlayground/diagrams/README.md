# Commutative diagrams

This directory is a small framework for reasoning about commutative diagrams in
Lean. It makes the informal practice of Riehl's §1.6 ("The art of the diagram
chase") precise. A diagram is drawn as arrows, its faces are said to commute,
and the whole diagram is concluded to commute by pasting faces together or
chasing around them. The aim is to support those moves directly, rather than
rewriting long composites by hand.

## The model

A **diagram** in a category `C` is a prefunctor `G : W ⥤q C` out of a quiver `W`,
its **shape**. A shape has vertices and arrows only: no composition, no
equations, no faces, no layout. The composite of a path `p` in `W` is
`eval G p`.

A **subshape** `S : Subshape W` is a choice of some arrows of `W`. Subshapes form
a lattice, with `≤`, `⊔`, `⊥` and `⊤`. `G` **commutes on** `S`, written
`CommutesOn G S`, when any two parallel paths built from arrows of `S` have the
same composite. Every result is stated relative to subshapes of one ambient
shape, in the form "if `G` commutes on these subshapes, it commutes on a larger
one". Proofs therefore compose: a large diagram is handled by starting from the
empty subshape, adding arrows, and pasting pieces.

The ambient shape may contain cycles. The theorems assume acyclicity only of the
subshapes on which they conclude commutativity. A commuting cycle forces its
arrows to be isomorphisms, so the acyclic case covers commutative diagrams as
they are used in practice.

A **face** names two parallel paths. A **chase** is a recorded sequence of face
applications, each made inside a longer path, that rewrites one path into
another. Chases are data: they can be inspected, reversed, composed and
whiskered, and replayed as a proof of the equation between their endpoints.

## Files

| File | Contents |
|---|---|
| `core.lean` | The interface: `eval`, `Subshape`, `single`, `Within`, `ReachIn`, `AcyclicOn`, `CommutesOn`, `Commutes`, `Face`, and basic facts. |
| `extend.lean` | Adding one arrow `e` to a subshape `S`: the cells it closes, and extending a cell that holds to the cells outside it. |
| `minimal.lean` | Minimal cells: every cell lies outside one, so they suffice; and none can be dropped (a counter-model in types). |
| `paste.lean` | Pasting two commuting subshapes into their union. |
| `chase.lean` | Steps and chases; soundness and completeness; `ChasesOn`. |
| `chase_growth.lean` | Adding an arrow and pasting, restated for chases. |
| `finite.lean` | The computational view: `arrow`, `FinShape`, `ofList`, decidable membership, `Path.edges`. |
| `decide.lean` | Decision procedures: `ReachIn`, `AcyclicOn`, cells and minimality, `Shared`, `Chain`; rank and closed-set certificates. |
| `search.lean` | Chase scripts on edge lists, `replay` with its soundness theorem, and a breadth-first chase search checked by replay. |
| `tactics.lean` | Certificate checks (`rankCheck`, `fenceCheck`, `replayCheck`) and the tactics that find certificates with compiled code: `diagram_acyclic`, `diagram_unreachable`, `find_chase`. |
| `order.lean` | Choosing the build order (search, mirroring the kernel's check) and canonical faces of a graph; plain data, outside the kernel. |
| `construct.lean` | Commutative by construction: builds (arrows added in turn, each with the faces it completes), `buildOK`, `commutesOn_of_build`, `commutes_of_order`. |
| `graph.lean` | Graphs as data: `Shape n E` (vertices `Fin n`, arrows listed by their ends in `E`) with its instances proved once; a diagram of a graph from objects and a list of morphisms (`toPrefunctor`); `evalNE`. Objects are held in a Braun tree (`Braun`, `objOf`), so that the kernel looks a vertex up in logarithmic time. |
| `glue.lean` | Why a glued diagram commutes, proved once (`commutes_of_glue`): each piece commutes inside it, by path lifting (`CommutesOn.of_embed`), and the pieces paste. The hypotheses are conditions on numbers (`GlueOK`, decided by evaluation; the chain condition is certified by one path through the shared vertices, `chainCert`) and that the glued diagram has each piece's objects and morphisms (`HasPiece`, by `rfl`). |
| `widget.lean` | The "Commuting diagram" presenter: draws a diagram value in the infoview, with a layout computed from its faces. |
| `frontend.lean` | `comm_diagram [h₁, …]` (build a commuting diagram from equations and diagrams, inside a proof), `glue D₁ D₂` (glue two diagrams along what they share), `diagram_eq D` (prove an equation whose sides are paths in `D`), and `diagram_build` (prove `Commutes G` by construction for any finite shape). |
| `examples/examples.lean` | Worked examples: the five-object undercount, Riehl's rectangle by hand, and diagrams built inside proofs (rectangle, naturality squares, cube, gluing). Diagrams are in `examples/assets/` (SVG, with tikz-cd source). |

`core` is imported by everything. `extend`, `paste`, `chase` and `finite` each
import only `core`; `chase_growth` imports `extend`, `paste` and `chase`, and
`decide` imports `finite`, `extend` and `paste`; `minimal` imports `extend`;
`search` imports `chase` and `finite`; `tactics` imports `decide` and `search`;
`construct` imports `decide`; `graph` imports `construct`; `glue` imports
`graph`; `frontend` imports `glue` and `order`; and `widget` imports `frontend` and Mathlib's diagram
widgets. The front end does not depend on the chase layer.

## Workflow

A commutative diagram is built inside a proof, from equations that are already
known, and then used to prove equations:

```lean
example (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : f ≫ j ≫ l = g ≫ k ≫ m := by
  let D := comm_diagram [hL, hR]   -- build: the two squares make the rectangle commute
  diagram_eq D                     -- use: both sides are paths in D
```

**Building.** `comm_diagram [h₁, …]` reads each equation `hᵢ` between composites.
Its morphisms become the arrows of a graph, their domains and codomains the
vertices, and the equations its faces. It then proves that the graph commutes, by
construction: the arrows are added one at a time, in an order it chooses
(`order.lean`), and each arrow's new cells must be covered by the faces it
completes. The kernel checks this. If the equations leave two parallel routes
unrelated, building fails and names them. The result is a value of type
`CommDiagram C` (`graph.lean`): the graph, its objects and morphisms, and the proof
that it commutes. Bind it with `let`, so that its morphisms stay visible; in the
infoview it displays as `⟪diagram f, h, g, …⟫`. An `hᵢ` may also be a diagram built
earlier: its morphisms and its commutativity are included, which glues diagrams
along shared morphisms or extends a diagram with new arrows and equations.

**Gluing.** `glue D₁ D₂` glues two diagrams built earlier along what they share:
an object of both becomes one vertex, and a morphism of both becomes one arrow
(up to definitional equality). The result commutes when the pieces paste: any two
objects they share are joined by a route of shared morphisms, and the glued
diagram has no cycle. Some such condition is needed. Two commuting squares that
share only two opposite corners give two routes between those corners that no
equation relates, and `glue` reports that pair of objects. Its result is a
`CommDiagram` like any other, so it can be glued again or used by `diagram_eq`.

Neither piece is checked again. The proof that the result commutes is one theorem,
`commutes_of_glue` (`glue.lean`). Its hypotheses about the graphs (where each
piece's vertices and arrows sit in the glued graph, the chain condition, a rank
that every arrow raises) mention only numbers, so the kernel decides them. Its
hypotheses about objects and morphisms hold by `rfl`. `comm_diagram [D₁, D₂, h, …]`
also glues, and can add equations, but it checks the whole result from scratch.

Kernel time that gluing adds on top of building the two pieces, for two k × k grids
of squares that share a column:

| k | `glue D₁ D₂` | `comm_diagram [D₁, D₂]` |
|---|---|---|
| 2 | 0.13 s | 0.37 s |
| 3 | 0.33 s | 1.5 s |
| 4 | 0.75 s | 3.9 s |
| 5 | 0.96 s | 8.9 s |

The cost of gluing grows with the size of the pieces, roughly in proportion. Three
choices keep it there. Lookups by position go through Braun trees, which take
logarithmic time, instead of lists. Every comparison is between one side and a list
written out by the elaborator, never between two diagrams' lookups; the kernel
would otherwise compare the two diagrams' containers entry by entry before
evaluating either lookup. The chain condition is checked on a certificate, one path
of shared arrows through all the shared vertices, instead of by a reachability
search for each pair.

**Drawing.** With `show_panel_widgets [local ProofWidgets.SelectionPanel]` in the
file, shift-click a diagram in the infoview and choose "Commuting diagram"
(`widget.lean`). It is drawn with Mathlib's Penrose style for commutative
diagrams, laid out from its faces: around each face one side goes right then down
and the other down then right.

**Using.** `diagram_eq D` proves a goal `p₁ = p₂` when `p₁` and `p₂` are paths in
`D`: each side is split at `≫` (ignoring bracketing and identities), and each
factor must be one of `D`'s morphisms, up to definitional equality. Parallelism
is automatic, since the two sides of an equation have the same type.

The graph is plain data (`Shape n E` in `graph.lean`): its instances are proved
once for all graphs, and nothing is declared per diagram. The builders write the
terms directly and leave the definitional checks (that a listed morphism has the
type its ends require, that a face holds once its equation is bracketed to the
left) to the kernel.

A face is an equation between two parallel composites, not a region of a drawing.
A region whose boundary zigzags (more than one source and sink around it)
contains no pair of parallel paths and asserts nothing.

## Main results

**Basic facts** (`core`):
- `CommutesOn.mono`: commuting on `T` implies commuting on any `S ≤ T`.
- `commutesOn_bot`: every diagram commutes on the empty subshape.
- `CommutesOn.map`: functors preserve commutativity (Riehl, Lemma 1.6.5).
- `CommutesOn.of_map`: faithful functors reflect it (Riehl, Lemma 1.6.20).

**Adding an arrow** (`extend`, `minimal`). A new arrow `e : u ⟶ v` *closes a
cell* at a pair `(x, y)` (`Closes`) when there are paths `x ⇝ u`, `v ⇝ y` and
`x ⇝ y` within `S`: the new path through `e` is parallel to an old one. A
`ClosedCell S e x y` carries such paths, and its `face` states the equation they
must satisfy; `CellHolds` says some such equation holds. A cell that holds
implies every cell outside it (`CellHolds.extend`).
- `commutesOn_sup_single_iff`: in a finite shape with `S` acyclic and no path
  `v ⇝ u`, `G` commutes on `S ⊔ single e` if and only if the equation holds at
  each minimal cell.
- `CommutesOn.sup_single_of_cover`: the same, with any family of checked
  cells such that every cell lies outside one of them.
- `closesMin_necessary`: no minimal cell can be dropped. For each one there
  is a diagram of types in which every other equation holds and that one fails.
- `UndercountExample.two_regions_not_enough` (in `examples`): a five-object diagram where a planar
  drawing shows two new regions, but three checks are needed.

**Pasting** (`paste`).
- `CommutesOn.paste`: if `G` commutes on `S` and on `T`, `S ⊔ T` is acyclic, and
  any two vertices shared by `S` and `T` are joined by a path lying in both
  (`Chain S T`), then `G` commutes on `S ⊔ T`. Gluing along a common path, as in
  Riehl's rectangle (1.6.10), satisfies the chain condition.

**Chases** (`chase`).
- `Chase.sound`: a chase proves the equation between its endpoints, assuming
  only the faces it uses (`Chase.used`).
- `Chase.complete`: if the equation holds in every diagram where the faces hold,
  some chase proves it. The proof uses a free model, `freeDiagram`: the category
  of paths modulo "joined by a chase".
- `chasesOn_iff`: chases join the parallel paths within `S` exactly when every
  diagram in which the faces hold commutes on `S`.
- `RectExample.rectangle` (in `examples`): Riehl's rectangle, proved by replaying a two-step chase.

**Chases, growing** (`chase_growth`).
- `ChasesOn.paste`, `ChasesOn.sup_single` and `ChasesOn.sup_single_minimal` are
  chase-level versions of the two growth steps. They prove that the chases
  exist, by working in the free model; they do not construct them.

**Deciding shape conditions** (`decide`). On a shape with `FinShape`, `NumShape`,
decidable equality and decidable subshape membership, `decide` proves reachability and its
failure, acyclicity, cells and their minimality, shared vertices and the
chain condition. `reachIn_iff_testBit` is the core: a depth-first search over vertex
indices with a bitmask for the visited set, checked to be closed under arrows. Without
finiteness, `acyclicOn_of_rank` and `not_reachIn_of_closed` turn a rank or a
closed set into the same conclusions.

**Searching for chases** (`search`). A `ChaseStep` names a face, a direction and a
position in a path's edge list; a list of steps is a script, a chase in flat
form. `chase_of_replay` says that if replaying a script turns the edges of `p`
into those of `q`, some chase joins them, so a script is a certificate.
`findChase` searches breadth-first for a script, and `chaseCheck` checks the
answer by replay. Only the check is trusted: `eq_of_chaseCheck` turns
`chaseCheck … = true`, proved by `decide`, into `eval G p = eval G q`.
`RectExample.rectangle_by_search` proves Riehl's rectangle this way.

## Conventions

- `CommutesOn`, `Commutes` and `ChasesOn` use strict implicit binders `∀ ⦃a b⦄`,
  as Mathlib does for similar definitions. A proof by `fun` must bind the two
  vertices, as in `fun _ _ p q hp hq => …`.
- `ReachIn` and the model in `extend` are `abbrev`s, so that `rw` can see
  through them.
- Proof internals live in sub-namespaces (`Paste`, `NecessityModel`); the top
  level of `Diagrams` holds the interface.
- A finite concrete shape provides `FinShape` and decidable equality on its
  vertices and arrows. The arrow instance must be stated once per shape, as
  `inferInstanceAs (DecidableEq (KHom a b))`, because instance search does not
  see through the `Quiver` instance. The kernel then evaluates `decide` on
  membership and `Within`.
- A concrete shape is an inductive type of arrows, as in `UndercountExample.KHom` and
  `RectExample.H`. A diagram on it is built by pattern matching, which keeps its
  arrows readable in goals (`G.map .f` reduces to `f`).

## Complexity and certificates

Proofs by `decide` make the kernel run a decision procedure by rewriting terms. The
procedures in `decide.lean` are written for that evaluator: reachability runs on
vertex indices (`NumShape`) with the visited set as a bitmask (bitwise arithmetic
on number literals is native in the kernel), a stack as worklist, and vertices
recovered from indices so that computed values never pile up as expressions.

For larger shapes, the tactics in `tactics.lean` split the work. They find a
*certificate* with compiled code, and the kernel only checks it, in one pass over
the arrows (via `decide +kernel`):

| Goal | Certificate | Tactic |
|---|---|---|
| `AcyclicOn S` | a rank per vertex, packed into one number | `diagram_acyclic` |
| `¬ ReachIn S v u` | a fence: a closed bitmask containing `v` but not `u` | `diagram_unreachable` |
| `Nonempty (Chase faces p q)` | a chase script, checked by replay | `find_chase` |

A wrong certificate makes the check fail; it can never give a false proof. The
proofs use only the standard axioms.

Measured on the benchmark grids (`bench/`), with `k` squares per side:

| Workload | 81 vertices | 1089 vertices |
|---|---|---|
| reachability, `decide` | 0.4 s | 6 s |
| acyclicity, `diagram_acyclic` | 0.08 s | 1.1 s |
| non-reachability, `diagram_unreachable` | 0.1 s | 1.2 s |
| chase search, `find_chase` | 2.9 s | — |

The chase search remains exponential: it explores the paths reachable from `p` by
face rewrites, which on a grid is every corner-to-corner path (12,870 at `k = 8`).
Its replay in the kernel is cheap (0.7 s at `k = 8`); the search itself runs in
Lean's interpreter, since tactic code from imported modules is not compiled to
native code. Checking a large diagram should go through the growth theorems,
which need only local chases, one per cell.

`bench/bench.py` times the workloads under hard wall-clock and memory limits.

The commutativity-by-construction check (`buildOK`) involves no search. It
carries a reachability bitmask per vertex through the build, so each arrow costs
bitwise operations on one mask per vertex. A grid of squares, built with
`comm_diagram` from one equation per square and then used by `diagram_eq` to prove
the corner-to-corner equation, timing the whole proof (Lean's startup excluded;
measured with `Elab.async false` and `trace.profiler`):

| Grid | Morphisms | Equations | Whole proof | Kernel checks |
|---|---|---|---|---|
| 4 × 4 objects | 24 | 9 | 0.6 s | 0.4 s |
| 6 × 6 objects | 60 | 25 | 3.0 s | 2.6 s |
| 8 × 8 objects | 112 | 49 | 10.2 s | 9.3 s |

Almost all the time is the kernel: the build check (5.5 s at 8 × 8), the check
that every arrow is in the build (1.7 s), and the final check of the proof term,
including each face against its equation (2.1 s). `diagram_eq` takes 0.16 s.

## Not yet done

- `diagram_eq` for subshapes (`CommutesOn`), for sides that are identities, and
  for rewriting inside a goal rather than closing it.
- Proving that the order search is complete: whether faces that make a diagram
  commute always admit an order in which each cell is covered by a single face.
  (The search is exhaustive over orders, but a cell might in principle need
  several faces at once.) Likewise, the canonical faces a glued diagram
  contributes are pruned by a greedy test, which may keep a redundant face.
- `comm_diagram` takes arrows only from equations: an arrow that appears in no
  equation cannot be added on its own.
- Cheaper conditions on numbers for gluing. At k = 4 they take about 0.3 s of the
  0.75 s above, mostly in the overhead of each evaluation step (type class
  instances for `%`, `/` and `=` on numbers, and `Decidable` instances). A single
  Boolean check written with the primitive operations on numbers, with one
  soundness theorem, would reduce that.
- Faster kernel checks for graphs: the build check and the check that every arrow
  is in the build evaluate the generic arrow list of `Shape n E`; a check stated
  on arrow numbers directly would be cheaper.
- Local chase search through the growth theorems, and faster global search
  (bidirectional, or native compilation of the search code).
- Drawing a recorded chase in the infoview, one step at a time.
- Riehl's remaining §1.6 moves as theorems: inverting isomorphisms (1.6.12–13),
  initial and terminal objects (1.6.17), mono and epi cancellation (1.6.22).
- A full 2-categorical version, in which faces are natural transformations
  rather than equalities. It is deferred until an argument needs pasting
  diagrams of 2-cells.

## Background

The face-and-chase layer follows the idea of a *computad* (Street, 1976), also
called a *polygraph* (Burroni, 1993). A computad presents a diagram as vertices,
arrows, and 2-cells between parallel paths, and a diagram chase is a composite of
2-cells. Here the 2-cells stand for equalities, which is the case needed for
commutative diagrams in an ordinary category.
