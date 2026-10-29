/-
# Declaring diagrams

The command `diagram_shape` declares a finite shape, its faces, and the diagrams
of that shape, from a list of arrows and faces. The objects are the ends of the
arrows, in order of first appearance.

```lean
diagram_shape Rect where
  arrows (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a') (h : b ⟶ b') (l : c ⟶ c')
    (k : a' ⟶ b') (m : b' ⟶ c')
  faces (L : f h = g k) (R : j l = h m)
```

It generates, in the namespace `Rect`:

* the vertex type `Rect` and the arrow type `Rect.Hom`, with the `Quiver`,
  `FinShape`, `NumShape`, `OutArrows` and decidable-equality instances;
* `Rect.Hom.path`, an arrow as a path of length one;
* the face names `Rect.Face`, the faces `Rect.face`, and their list `Rect.faces`;
* `Rect.diagram f j g h l k m`, the diagram in a category `D` with those arrows;
* `Rect.commutes f j g h l k m hL hR : Commutes (Rect.diagram f j g h l k m)`, from
  one hypothesis per face (here `hL : f ≫ h = g ≫ k` and `hR : j ≫ l = h ≫ m`),
  proved by construction (`commutes_of_order`).

A face is an equation assumed between two parallel composites, each written as a
sequence of arrow names. It need not be a region of a drawing. The name is
optional: `(f h = g k)` gives the face `face1` and the hypothesis `h1`.

Without a `faces` block, the faces are inferred: adding the arrows in declared
order, each arrow's minimal cells become the faces, and the command reports
them. They are the fewest equations that make the diagram commute when built in
that order (`closesMin_necessary`).

When the declared faces do not suffice in the declared order, the command names
the first equation that no face covers.

Equations between composites of the diagram then follow by
`diagram_eq (Rect.commutes …)`.
-/

import LeanPlayground.diagrams.frontend

open Lean Elab Command CategoryTheory

namespace Diagrams

/-- An arrow of a declared diagram: `(f : a ⟶ b)`. -/
declare_syntax_cat diagramArrow
syntax "(" ident " : " ident " ⟶ " ident ")" : diagramArrow

/-- A face of a declared diagram: `(L : f h = g k)`, two composites of arrows. -/
declare_syntax_cat diagramFace
syntax "(" ident " : " ident+ " = " ident+ ")" : diagramFace
syntax "(" ident+ " = " ident+ ")" : diagramFace

/-- Declare a finite shape, its faces, and its diagrams; see the module docstring. -/
syntax (name := diagramShape) "diagram_shape " ident " where "
  &"arrows" diagramArrow+ (&"faces" diagramFace+)? : command

/-- `ns.n`, as an identifier. -/
private def qual (ns : Name) (n : Name) : Ident := mkIdent (ns ++ n)

/-! ## Cells at declaration time

Plain computations on arrow indices, used to infer the faces of a shape and to
explain a build that fails. Arrow `i` runs between the vertex indices `ends[i]`. -/

namespace Declare

/-- For each vertex, a path from `x` using the arrows `prior`, as a list of arrow
indices, found breadth first. -/
def pathsFrom (n : ℕ) (ends : Array (ℕ × ℕ)) (prior : List ℕ) (x : ℕ) :
    Array (Option (List ℕ)) := Id.run do
  let mut paths : Array (Option (List ℕ)) := (Array.replicate n none).set! x (some [])
  let mut queue := #[x]
  let mut i := 0
  while i < queue.size do
    let w := queue[i]!
    i := i + 1
    let p := paths[w]!.getD []
    for a in prior do
      let (s, t) := ends[a]!
      if s == w && paths[t]!.isNone then
        paths := paths.set! t (some (p ++ [a]))
        queue := queue.push t
  return paths

/-- The minimal cells of adding arrow `k` to the arrows `prior`, as
`(x, y, lhs, rhs)` with `lhs = α ++ [k] ++ β` and `rhs = γ`, and `reach a b`, a path
from `a` to `b` within `prior`.

If the source `u` of `k` already reaches its target `v`, the only minimal
cell is `(u, v)`: every other lies above it. Otherwise a cell `(x, y)`
is minimal when neither end can move inwards on its own; if some cell lies
strictly below `(x, y)`, so does one with a single end moved. -/
def cells (n : ℕ) (ends : Array (ℕ × ℕ)) (prior : List ℕ) (k : ℕ) :
    (ℕ → ℕ → Option (List ℕ)) × List (ℕ × ℕ × List ℕ × List ℕ) :=
  let paths := (List.range n).toArray.map (pathsFrom n ends prior)
  let reach (a b : ℕ) := paths[a]![b]!
  let (u, v) := ends[k]!
  match reach u v with
  | some γ => (reach, [(u, v, [k], γ)])
  | none =>
    let isObl (x y : ℕ) := (reach x u).isSome && (reach v y).isSome && (reach x y).isSome
    let isMin (x y : ℕ) := isObl x y &&
      (List.range n).all (fun x₀ => x₀ == x || (reach x x₀).isNone || !isObl x₀ y) &&
      (List.range n).all (fun y₀ => y₀ == y || (reach y₀ y).isNone || !isObl x y₀)
    (reach, (List.range n).flatMap fun x => (List.range n).filterMap fun y =>
      if isMin x y then
        match reach x u, reach v y, reach x y with
        | some α, some β, some γ => some (x, y, α ++ [k] ++ β, γ)
        | _, _, _ => none
      else none)

end Declare

/-- `a ≫ b ≫ …` for the given arrow names. -/
private def compTerm (as : Array Ident) : MacroM Term := do
  let mut t : Term := as.back!
  for a in as.pop.reverse do
    t ← `(CategoryTheory.CategoryStruct.comp $a $t)
  return t

elab_rules : command
  | `(diagram_shape $N where arrows $arrs* $[faces $fs*]?) => do
    let ns := N.getId
    let Hom := qual ns `Hom
    let vertex (o : Ident) : Ident := qual ns o.getId
    let arrowsData ← arrs.mapM fun a => match a with
      | `(diagramArrow| ($f : $s ⟶ $t)) => pure (f, s, t)
      | _ => throwUnsupportedSyntax
    -- The objects, in order of first appearance.
    let mut objs : Array Ident := #[]
    for (_, s, t) in arrowsData do
      for o in [s, t] do
        unless objs.any (·.getId == o.getId) do objs := objs.push o
    let arrowName (f : Ident) : Ident := qual (ns ++ `Hom) f.getId
    -- Vertices and arrows.
    let vCtors ← objs.mapM fun o => `(Lean.Parser.Command.ctor| | $o:ident)
    elabCommand (← `(inductive $N:ident where $vCtors:ctor* deriving DecidableEq))
    let hCtors ← arrowsData.mapM fun (f, s, t) =>
      `(Lean.Parser.Command.ctor| | $f:ident : $Hom $(vertex s) $(vertex t))
    elabCommand (← `(inductive $Hom : $N → $N → Type where $hCtors:ctor* deriving DecidableEq))
    elabCommand (← `(instance : Quiver $N := ⟨$Hom⟩))
    elabCommand (← `(instance (x y : $N) : DecidableEq (x ⟶ y) :=
      inferInstanceAs (DecidableEq ($Hom x y))))
    -- Finite-shape instances.
    let verts := objs.map vertex
    let arrowTerms ← arrowsData.mapM fun (f, _, _) => `(arrow $(arrowName f))
    let idxId := qual ns `Hom.idx
    let idxAlts ← (arrowsData.zipIdx).mapM fun ((f, _, _), i) =>
      `(Lean.Parser.Term.matchAltExpr| | $(arrowName f) => $(Syntax.mkNumLit (toString i)))
    elabCommand (← `(/-- The position of an arrow in the declaration. -/
      def $idxId {x y : $N} (e : $Hom x y) : ℕ := match e with $idxAlts:matchAlt*))
    let atAlts ← (arrowTerms.zipIdx).mapM fun (t, i) =>
      `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkNumLit (toString i)) => $t)
    elabCommand (← `(instance : NumArrows $N where
      arrowIndex e := $idxId e.hom
      arrowAt i := match i with $atAlts:matchAlt* | _ => $(arrowTerms.back!)
      arrowAt_index := fun ⟨_, _, e⟩ => by cases e <;> rfl))
    elabCommand (← `(instance : FinShape $N where
      vertices := [$verts,*]
      mem_vertices x := by cases x <;> decide
      arrows := [$arrowTerms,*]
      mem_arrows := fun ⟨_, _, e⟩ => by cases e <;> decide))
    let indexAlts ← (objs.zipIdx).mapM fun (o, i) =>
      `(Lean.Parser.Term.matchAltExpr| | $(vertex o) => $(Syntax.mkNumLit (toString i)))
    let vertexAlts ← (objs.zipIdx).mapM fun (o, i) =>
      `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkNumLit (toString i)) => $(vertex o))
    let lastV := vertex objs.back!
    elabCommand (← `(instance : NumShape $N where
      size := $(Syntax.mkNumLit (toString objs.size))
      index x := match x with $indexAlts:matchAlt*
      index_lt x := by cases x <;> decide
      vertexAt i := match i with $vertexAlts:matchAlt* | _ => $lastV
      vertexAt_index x := by cases x <;> rfl))
    let outAlts ← objs.mapM fun o => do
      let outs ← (arrowsData.filter fun (_, s, _) => s.getId == o.getId).mapM fun (f, _, _) =>
        `(arrow $(arrowName f))
      `(Lean.Parser.Term.matchAltExpr| | $(vertex o) => [$outs,*])
    elabCommand (← `(instance : OutArrows $N where
      out x := match x with $outAlts:matchAlt*
      mem_out := fun ⟨_, _, e⟩ => by cases e <;> decide))
    let pathId := qual ns `Hom.path
    elabCommand (← `(/-- An arrow, as a path of length one. -/
      def $pathId {x y : $N} (e : $Hom x y) : Quiver.Path x y := Quiver.Hom.toPath (V := $N) e))
    -- The diagram of the shape, from morphisms of a category.
    let objBinders ← objs.mapM fun o => `(bracketedBinder| {$(mkIdent o.getId) : D})
    let arrBinders ← arrowsData.mapM fun (f, s, t) =>
      `(bracketedBinder| ($(mkIdent f.getId) : $(mkIdent s.getId) ⟶ $(mkIdent t.getId)))
    let objAlts ← objs.mapM fun o =>
      `(Lean.Parser.Term.matchAltExpr| | $(vertex o) => $(mkIdent o.getId))
    let mapAlts ← arrowsData.mapM fun (f, _, _) =>
      `(Lean.Parser.Term.matchAltExpr| | $(arrowName f) => $(mkIdent f.getId))
    let diagramId := qual ns `diagram
    let arrVars : Array Term := arrowsData.map fun (f, _, _) => mkIdent f.getId
    elabCommand (← `(/-- The diagram of this shape with the given arrows. -/
      def $diagramId {D : Type _} [CategoryTheory.Category D] $objBinders* $arrBinders* :
          $N ⥤q D where
        obj x := match x with $objAlts:matchAlt*
        map {x y} (e : $Hom x y) := match e with $mapAlts:matchAlt*))
    -- Faces: as declared, or inferred as the minimal cells of each arrow.
    let ends : Array (ℕ × ℕ) := arrowsData.map fun (_, s, t) =>
      (objs.findIdx (·.getId == s.getId), objs.findIdx (·.getId == t.getId))
    let arrowIdx (a : Ident) : CommandElabM ℕ := do
      let some i := arrowsData.findIdx? (·.1.getId == a.getId)
        | throwErrorAt a "diagram_shape: unknown arrow {a.getId}"
      return i
    let arrowId (i : ℕ) : Ident := mkIdent arrowsData[i]!.1.getId
    let showSide (as : Array ℕ) : String :=
      " ≫ ".intercalate (as.toList.map fun i => arrowsData[i]!.1.getId.toString)
    let unnamed (i : ℕ) : Name × Ident :=
      (Name.mkSimple s!"face{i + 1}", mkIdent (Name.mkSimple s!"h{i + 1}"))
    let mut facesData : Array (Name × Ident × Array ℕ × Array ℕ) := #[]
    match fs with
    | some fs =>
      for fc in fs do
        let (n, lhs, rhs) ← match fc with
          | `(diagramFace| ($n : $lhs* = $rhs*)) => pure ((n.getId, mkIdent (.mkSimple
              ("h" ++ n.getId.toString))), lhs, rhs)
          | `(diagramFace| ($lhs* = $rhs*)) => pure (unnamed facesData.size, lhs, rhs)
          | _ => throwUnsupportedSyntax
        facesData := facesData.push (n.1, n.2, ← lhs.mapM arrowIdx, ← rhs.mapM arrowIdx)
    | none =>
      for k in [0:arrowsData.size] do
        let (_, obl) := Declare.cells objs.size ends (List.range k) k
        for (_, _, lhs, rhs) in obl do
          let n := unnamed facesData.size
          facesData := facesData.push (n.1, n.2, lhs.toArray, rhs.toArray)
      logInfo <| if facesData.isEmpty then m!"diagram_shape: no faces needed"
        else m!"diagram_shape: inferred faces\n{"\n".intercalate (facesData.toList.map
          fun (_, h, l, r) => s!"{h.getId} : {showSide l} = {showSide r}")}"
    -- For each arrow, in declared order, the faces it completes: those containing it
    -- once, all of whose other arrows come earlier.
    let completed (k : ℕ) : List ℕ := (List.range facesData.size).filter fun i =>
      let (_, _, l, r) := facesData[i]!
      let all := l ++ r
      all.count k == 1 && all.all (· ≤ k)
    -- Explain a failed build: a cycle, or a cell no completed face covers.
    for k in [0:arrowsData.size] do
      let (reach, obl) := Declare.cells objs.size ends (List.range k) k
      let (u, v) := ends[k]!
      if (reach v u).isSome then
        throwError "diagram_shape: arrow {arrowsData[k]!.1.getId} closes a cycle"
      for (x, y, lhs, rhs) in obl do
        let covered := (completed k).any fun i =>
          let (_, _, l, _) := facesData[i]!
          let src := ends[l[0]!]!.1
          let tgt := ends[l.back!]!.2
          (reach x src).isSome && (reach tgt y).isSome
        unless covered do
          throwError "diagram_shape: adding {arrowsData[k]!.1.getId} closes the cell\n  \
            {showSide lhs.toArray} = {showSide rhs.toArray}\nwhich no face it completes covers. \
            Either the faces do not imply it, so it must be added as a face, or the faces \
            that imply it contain arrows declared after {arrowsData[k]!.1.getId}, and \
            another order of the arrows avoids it."
    let FaceT := qual ns `Face
    let fCtors ← facesData.mapM fun (n, _) => `(Lean.Parser.Command.ctor| | $(mkIdent n):ident)
    elabCommand (← `(inductive $FaceT where $fCtors:ctor* deriving DecidableEq))
    let pathOf (as : Array ℕ) : CommandElabM Term := do
      let mut t ← `($pathId $(arrowName (arrowId as[0]!)))
      for a in as[1:] do
        t ← `(Quiver.Path.comp $t ($pathId $(arrowName (arrowId a))))
      return t
    let faceAlts ← facesData.mapM fun (n, _, lhs, rhs) => do
      `(Lean.Parser.Term.matchAltExpr|
        | $(qual (ns ++ `Face) n) => ⟨_, _, $(← pathOf lhs), $(← pathOf rhs)⟩)
    let faceId := qual ns `face
    elabCommand (← `(/-- The faces of the shape. -/
      def $faceId : $FaceT → Diagrams.Face $N := fun n => match n with $faceAlts:matchAlt*))
    let facesId := qual ns `faces
    let faceNames := facesData.map fun (n, _) => qual (ns ++ `Face) n
    elabCommand (← `(/-- All faces of the shape. -/
      def $facesId : List (Diagrams.Face $N) := [$faceNames,*].map $faceId))
    let hypBinders ← facesData.mapM fun (_, h, lhs, rhs) => do
      let lhsT ← liftMacroM <| compTerm (lhs.map arrowId)
      let rhsT ← liftMacroM <| compTerm (rhs.map arrowId)
      `(bracketedBinder| ($h : $lhsT = $rhsT))
    -- Each face case is proved by its own hypothesis.
    let caseTacs ← facesData.mapM fun (n, h, _) =>
      `(tactic| case $(mkIdent n):ident =>
        simpa [Diagrams.Face.Holds, $faceId:ident, $pathId:ident, $diagramId:ident] using $h)
    let faceTac ← `(tactic| (cases n; $[$caseTacs]*))
    -- The build: arrows in declared order, each with the faces it completes.
    let mut usesTerms : Array Term := #[]
    for k in [0:arrowsData.size] do
      let mut us : Array Term := #[]
      for i in completed k do
        let (_, _, l, r) := facesData[i]!
        let (side, pos) := match l.idxOf? k with
          | some n => (false, n)
          | none => (true, (r.idxOf? k).getD 0)
        let sideT ← if side then `(true) else `(false)
        us := us.push (← `(⟨$(Syntax.mkNumLit (toString i)), $sideT,
          $(Syntax.mkNumLit (toString pos))⟩))
      usesTerms := usesTerms.push (← `([$us,*]))
    let order ← `([$((List.range arrowsData.size).toArray.map fun k => Syntax.mkNumLit (toString k)),*])
    let commutesId := qual ns `commutes
    elabCommand (← `(/-- The diagram commutes, given the equations of its faces. -/
      theorem $commutesId {D : Type _} [CategoryTheory.Category D] $objBinders* $arrBinders*
          $hypBinders* : Diagrams.Commutes ($diagramId $arrVars*) := by
        have hn : ∀ n : $FaceT, ($faceId n).Holds ($diagramId $arrVars*) := by
          intro n
          $faceTac:tactic
        have hF : ∀ φ ∈ $facesId, φ.Holds ($diagramId $arrVars*) :=
          List.forall_mem_map.2 fun n _ => hn n
        exact Diagrams.commutes_of_order hF $order [$usesTerms,*]
          (by decide +kernel) (by decide +kernel)))

end Diagrams
