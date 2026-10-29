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
| `extend.lean` | Adding one arrow `e` to a subshape `S`, the obligations it creates, and why none can be dropped. |
| `paste.lean` | Pasting two commuting subshapes into their union. |
| `chase.lean` | Steps and chases; soundness and completeness; `ChasesOn`. |
| `chase_growth.lean` | Adding an arrow and pasting, restated for chases. |
| `examples.lean` | The five-object undercount example and Riehl's rectangle. |

`core` is imported by everything. `extend`, `paste` and `chase` each import
only `core`; `chase_growth` imports all three, and `examples` imports `extend`
and `chase`.

## Main results

**Basic facts** (`core`):
- `CommutesOn.mono`: commuting on `T` implies commuting on any `S ≤ T`.
- `commutesOn_bot`: every diagram commutes on the empty subshape.
- `CommutesOn.map`: functors preserve commutativity (Riehl, Lemma 1.6.5).
- `CommutesOn.of_map`: faithful functors reflect it (Riehl, Lemma 1.6.20).

**Adding an arrow** (`extend`). For a new arrow `e : u ⟶ v`, a pair `(x, y)` is an
*obligation* (`IsObligation`) when there are paths `x ⇝ u`, `v ⇝ y` and `x ⇝ y`
within `S`. An `Obligation S e x y` carries such paths, and its `face` states the
equation they must satisfy; `ObligationHolds` says some such equation holds.
- `commutesOn_sup_single_iff`: in a finite shape with `S` acyclic and no path
  `v ⇝ u`, `G` commutes on `S ⊔ single e` if and only if the equation holds at
  each minimal obligation.
- `CommutesOn.sup_single_of_cover`: the same, with any family of checked
  obligations that every obligation lies above.
- `isMinObligation_necessary`: no minimal obligation can be dropped. For each one there
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

## Conventions

- `CommutesOn`, `Commutes` and `ChasesOn` use strict implicit binders `∀ ⦃a b⦄`,
  as Mathlib does for similar definitions. A proof by `fun` must bind the two
  vertices, as in `fun _ _ p q hp hq => …`.
- `ReachIn` and the model in `extend` are `abbrev`s, so that `rw` can see
  through them.
- Proof internals live in sub-namespaces (`Paste`, `NecessityModel`); the top
  level of `Diagrams` holds the interface.
- A concrete shape is an inductive type of arrows, as in `UndercountExample.KHom` and
  `RectExample.H`. A diagram on it is built by pattern matching, which keeps its
  arrows readable in goals (`G.map .f` reduces to `f`).

## Not yet done

- Decision procedures for the shape conditions (reachability, acyclicity,
  obligations, the chain condition) on finite shapes. The plan is a meta-level
  search that emits certificates for the kernel to check cheaply.
- A chase-search tactic that closes or rewrites goals stated in a diagram's own
  morphisms, and returns the chase it found.
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
