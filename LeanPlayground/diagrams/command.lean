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
  proved by `diagram_build`.

A face is written as two sequences of arrow names, each read as a composite in
order. Equations between composites of the diagram then follow by
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

/-- Declare a finite shape, its faces, and its diagrams; see the module docstring. -/
syntax (name := diagramShape) "diagram_shape " ident " where "
  &"arrows" diagramArrow+ (&"faces" diagramFace+)? : command

/-- `ns.n`, as an identifier. -/
private def qual (ns : Name) (n : Name) : Ident := mkIdent (ns ++ n)

/-- `a ≫ b ≫ …` for the given arrow names. -/
private def compTerm (as : Array Ident) : MacroM Term := do
  let mut t : Term := as.back!
  for a in as.pop.reverse do
    t ← `($a ≫ $t)
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
    -- Faces, and commutativity by construction.
    let some fs := fs | return
    let facesData ← fs.mapM fun fc => match fc with
      | `(diagramFace| ($n : $lhs* = $rhs*)) => pure (n, lhs, rhs)
      | _ => throwUnsupportedSyntax
    let FaceT := qual ns `Face
    let fCtors ← facesData.mapM fun (n, _, _) => `(Lean.Parser.Command.ctor| | $n:ident)
    elabCommand (← `(inductive $FaceT where $fCtors:ctor* deriving DecidableEq))
    let pathOf (as : Array Ident) : CommandElabM Term := do
      let mut t ← `($pathId $(arrowName as[0]!))
      for a in as[1:] do
        t ← `(Quiver.Path.comp $t ($pathId $(arrowName a)))
      return t
    let faceAlts ← facesData.mapM fun (n, lhs, rhs) => do
      `(Lean.Parser.Term.matchAltExpr|
        | $(qual (ns ++ `Face) n.getId) => ⟨_, _, $(← pathOf lhs), $(← pathOf rhs)⟩)
    let faceId := qual ns `face
    elabCommand (← `(/-- The faces of the shape. -/
      def $faceId : $FaceT → Diagrams.Face $N := fun n => match n with $faceAlts:matchAlt*))
    let facesId := qual ns `faces
    let faceNames := facesData.map fun (n, _, _) => qual (ns ++ `Face) n.getId
    elabCommand (← `(/-- All faces of the shape. -/
      def $facesId : List (Diagrams.Face $N) := [$faceNames,*].map $faceId))
    let hypIds : Array Ident :=
      facesData.map fun (n, _, _) => mkIdent (Name.mkSimple ("h" ++ n.getId.toString))
    let hypBinders ← (facesData.zip hypIds).mapM fun ((_, lhs, rhs), h) => do
      let lhsT ← liftMacroM <| compTerm (lhs.map fun a => mkIdent a.getId)
      let rhsT ← liftMacroM <| compTerm (rhs.map fun a => mkIdent a.getId)
      `(bracketedBinder| ($h : $lhsT = $rhsT))
    let attempts ← hypIds.mapM fun h =>
      `(Lean.Parser.Tactic.tacticSeq| simpa [Diagrams.Face.Holds, $faceId:ident, $pathId:ident, $diagramId:ident]
          using $h)
    -- The build: arrows in declared order, each with the faces it completes.
    let arrowIdx (a : Ident) : Option ℕ := arrowsData.findIdx? (·.1.getId == a.getId)
    let mut usesTerms : Array Term := #[]
    for k in [0:arrowsData.size] do
      let mut us : Array Term := #[]
      for ((_, lhs, rhs), i) in facesData.zipIdx do
        let lIdx := lhs.filterMap arrowIdx
        let rIdx := rhs.filterMap arrowIdx
        let all := lIdx ++ rIdx
        if all.count k == 1 && all.all (· ≤ k) then
          let (side, pos) := match lIdx.idxOf? k with
            | some n => (false, n)
            | none => (true, (rIdx.idxOf? k).getD 0)
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
          cases n <;> first $[| $attempts]*
        have hF : ∀ φ ∈ $facesId, φ.Holds ($diagramId $arrVars*) :=
          List.forall_mem_map.2 fun n _ => hn n
        exact Diagrams.commutes_of_order hF $order [$usesTerms,*]
          (by decide +kernel) (by decide +kernel)))

end Diagrams
