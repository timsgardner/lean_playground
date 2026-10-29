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
| `order.lean` | Choosing the build order (search, mirroring the kernel's check) and canonical inferred faces; plain data, outside the kernel. |
| `construct.lean` | Commutative by construction: builds (arrows added in turn, each with the faces it completes), `buildOK`, `commutesOn_of_build`. |
| `frontend.lean` | The tactics `diagram_build` (prove `Commutes G` by construction) and `diagram_eq` (read off an equation in the diagram's own morphisms). |
| `command.lean` | The `diagram_shape` command: declare a shape, its faces, its diagrams, and their commutativity theorem. |
| `examples/examples.lean` | Worked examples: the five-object undercount, Riehl's rectangle and cube, inferred faces. Diagrams are in `examples/assets/` (SVG, with tikz-cd source). |

`core` is imported by everything. `extend`, `paste`, `chase` and `finite` each
import only `core`; `chase_growth` imports `extend`, `paste` and `chase`, and
`decide` imports `finite`, `extend` and `paste`; `search` imports `chase` and
`finite`; `tactics` imports `decide` and `search`; `construct` imports `decide`
and `search`; `frontend` imports `construct` and `tactics`; and `command` imports
`frontend`.

## Workflow

Declare a diagram with `diagram_shape`, giving its arrows and its faces:

```lean
diagram_shape Rect where
  arrows (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a') (h : b ⟶ b') (l : c ⟶ c')
    (k : a' ⟶ b') (m : b' ⟶ c')
  faces (L : f h = g k) (R : j l = h m)
```

This generates the shape and its instances, `Rect.diagram f j g h l k m` (the
diagram with those morphisms, in any category), and

```lean
Rect.commutes f j g h l k m (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) :
  Commutes (Rect.diagram f j g h l k m)
```

Any equation between parallel composites then follows in one line:

```lean
example … : f ≫ j ≫ l = g ≫ k ≫ m := by diagram_eq (Rect.commutes f j g h l k m hL hR)
```

The diagram commutes *by construction*. Its arrows are added one at a time, in
an order the command chooses (`order.lean`): the order of declaration never
matters. When an arrow `e` is added, a face with `e` on one side,
`α ≫ e ≫ β = γ`, and its other arrows already present, is exactly a cell
that `e` closes (`cellHolds_of_face`). `Rect.commutes` is valid when the cells
given by faces cover every cell each arrow closes; the kernel checks that by
deciding questions about the shape. No chase search is involved. `diagram_eq`
matches each factor of a composite to an arrow whose image is that morphism,
turning each side into a path. `examples/examples.lean` declares Riehl's commutative cube
the same way.

A face is an equation assumed between two parallel composites, not a region of a
drawing. A region whose boundary zigzags (more than one source and sink around
it) contains no pair of parallel paths and so asserts nothing; `Zigzag` in
`examples/examples.lean` is such a diagram. Face names are optional: `(f h = g k)` becomes
`face1`, with hypothesis `h1`.

The `faces` block itself is optional. Without it, the faces are inferred, and the
command reports them. They depend only on the shape and the arrow names: the
arrows are added in a canonical order that always closes the smallest available
cell next, the minimal cells closed become the faces (each needed at its step,
by `closesMin_necessary`), and any face that the others imply is dropped. For
the rectangle and the cube the inferred faces are the squares; for a square with
a diagonal, the two triangles. A commutative diagram has no unique irredundant
set of faces in general (the square with a diagonal has three), so ties are
broken by the smallest cell and then by name.

When the declared faces leave some cell uncovered in every order of the arrows,
the command names an arrow and a cell it closes that no face covers.

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
bitwise operations on one mask per vertex. A grid of squares declared with
`diagram_shape`, timing the command alone (Lean's startup excluded; measured with
`Elab.async false` and `trace.profiler`):

| Grid | Arrows | Faces | Command, faces declared | Command, faces inferred |
|---|---|---|---|---|
| 4 × 4 vertices | 24 | 9 | — | 2.1 s |
| 6 × 6 vertices | 60 | 25 | 8.3 s | 11.2 s |
| 8 × 8 vertices | 112 | 49 | 22.7 s | — |

With faces declared at 8 × 8, about half the time is the generated instances and
definitions, and the `commutes` theorem takes about 10 s.

The `commutes` theorem is the kernel check of the build (3.8 s at 8 × 8) and one
`simp` proof per face hypothesis (3.8 s). The instances are dominated by their
`decide` proofs over the vertex and arrow lists (`FinShape`, `NumArrows`,
`OutArrows`).

## Not yet done

- `diagram_eq` for subshapes (`CommutesOn`), for sides that are identities, and
  for rewriting inside a goal rather than closing it.
- Proving that the order search is complete: whether faces that make a diagram
  commute always admit an order in which each cell is covered by a single face.
  (The search is exhaustive over orders, but a cell might in principle need
  several faces at once.) Likewise, pruning of inferred faces uses a greedy
  test, which may keep a redundant face.
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
