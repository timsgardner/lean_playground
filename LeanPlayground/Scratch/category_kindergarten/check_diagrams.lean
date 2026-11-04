/-
# Category Kindergarten: Diagrams for `#check`

The selection panel of `diagram_tools` can only draw what is shown in the goal
view, because the infoview offers no way to select part of a message. This module
draws the output of `#check` instead. When the type of the checked term is, or
concludes with, something that one of the presenters can draw, placing the cursor
on the `#check` shows the drawing in a panel of the infoview. The message that
`#check` prints is unchanged, and a `#check` of anything else behaves as usual.

For a term whose type has hypotheses, as in `#check transposed_square_of_square`,
each hypothesis that can be drawn is drawn too, followed by the conclusion, so the
panel shows the statement as a picture. Both the `#check` command and Mathlib's
`#check` tactic are covered, so this also works inside a proof, where the local
hypotheses are in scope. Importing this module is all that is needed.
-/

import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget
import Mathlib.Tactic.Check
import ProofWidgets.Component.HtmlDisplay

open Lean Meta Elab Command ProofWidgets Mathlib.Tactic.Widget

namespace CheckDiagrams

/-- Draw the proposition `p` with the first presenter that applies to it. The
order matters for an equation `f ≫ g = i ≫ h`, which is drawn as a square in
preference to two paths. -/
meta def draw? (p : Expr) : MetaM (Option ProofWidgets.Html) := do
  let presenters := [commSqPresenter, commutativeSquarePresenter,
    commutativeTrianglePresenter, Diagrams.Draw.pathEquationPresenter]
  for presenter in presenters do
    try return some (← presenter.present p) catch _ => pure ()
  return none

/-- A drawing with a caption above it. -/
meta def captioned (caption : String) (html : ProofWidgets.Html) : ProofWidgets.Html :=
  .element "div" #[("style", json% { marginBottom: "1em" })]
    #[.element "div" #[] #[.text caption], html]

/-- The drawings of the hypotheses and the conclusion of `type`, in order. Returns
`none` if nothing can be drawn. -/
meta def drawType? (type : Expr) : MetaM (Option ProofWidgets.Html) :=
  forallTelescope type fun xs conclusion => do
    let mut parts : Array ProofWidgets.Html := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        if let some html ← draw? t then
          parts := parts.push (captioned s!"Hypothesis {← x.fvarId!.getUserName}" html)
    if let some html ← draw? conclusion then
      parts := parts.push (if xs.isEmpty then html else captioned "Conclusion" html)
    return if parts.isEmpty then none else some (.element "div" #[] parts)

/-- The type of the term given to `#check`. As in `#check` itself, an identifier
naming a constant gives the constant's own type, in which the implicit arguments
remain binders. -/
meta def checkedType (term : Term) : TermElabM Expr := do
  if let `($_:ident) := term then
    try return (← getConstInfo (← realizeGlobalConstNoOverload term)).type catch _ => pure ()
  let e ← Term.withoutErrToSorry <| Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  instantiateMVars (← inferType e)

/-- Show the drawing of the type of `term`, if there is one, in a panel attached
to `stx`. Elaborating `term` a second time must not report anything, since `#check`
has already done so, and a failure here only means that there is no drawing. -/
meta def showDrawing (stx : Syntax) (term : Term) : TermElabM Unit := do
  let saved ← saveState
  let html? ← try drawType? (← checkedType term) catch _ => pure none
  saved.restore
  if let some html := html? then
    Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.rpcEncode html) }) stx

@[command_elab Lean.Parser.Command.check]
meta def elabCheckWithDrawing : CommandElab := fun stx => do
  elabCheck stx
  match stx with
  | `(#check $term) => withoutModifyingEnv <| runTermElabM fun _ => showDrawing stx term
  | _ => pure ()

/-- Run Mathlib's `#check` tactic, which prints the message, and then show the
drawing. The implementation of that tactic is private to its module, so it is found
in the table of elaborators. Declining the syntax with `throwUnsupportedSyntax`
would also reach it, but would discard the panel. -/
@[tactic Mathlib.Tactic.«tactic#check__»]
meta def evalCheckWithDrawing : Tactic.Tactic := fun stx => do
  let entries := Tactic.tacticElabAttribute.getEntries (← getEnv) stx.getKind
  let some original := entries.find? (·.declName != `CheckDiagrams.evalCheckWithDrawing)
    | throwUnsupportedSyntax
  original.value stx
  if let `(tactic| #check $term) := stx then
    Tactic.withMainContext <| showDrawing stx term

end CheckDiagrams
