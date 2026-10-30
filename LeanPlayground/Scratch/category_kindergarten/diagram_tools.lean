/-
# Category Kindergarten: Diagram Tools

Infoview support for reading commutative squares as pictures.

Mathlib's `Mathlib.Tactic.Widget.CommDiag` already draws an equation of the form
`f ≫ g = i ≫ h` as a square, and an equation `f ≫ g = h` as a triangle. This
module adds a presenter that draws a `CommSq top left right bottom` as a square
in the same style, so that a hypothesis or goal stated with `CommSq` can be
viewed as the diagram it describes.

To see a diagram, put `show_panel_widgets [local SelectionPanel]` near the top
of a file (or wrap a proof in `with_panel_widgets [SelectionPanel] ...`). Then,
with the cursor inside a proof, shift-click the type of a hypothesis or of the
goal in the infoview. The selection panel offers the available presenters, among
them "CommSq diagram", "Commutative square", and "Commutative triangle".
-/

import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.SelectionPanel

open CategoryTheory ProofWidgets Lean Meta Mathlib.Tactic.Widget

/-- If `e` is `CommSq top left right bottom`, or a proof of one (such as a
hypothesis `sq`), return its four sides. -/
meta def commSqSides? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  -- A goal after `have` or `let` is wrapped in metadata, which the infoview hides.
  let e := (← instantiateMVars e).consumeMData
  let ty ← if e.isAppOfArity ``CommSq 10 then pure e
    else pure (← instantiateMVars (← inferType e)).consumeMData
  -- `CommSq {C} [Category C] {W X Y Z} top left right bottom`
  unless ty.isAppOfArity ``CommSq 10 do return none
  let args := ty.getAppArgs
  return some (args[6]!, args[7]!, args[8]!, args[9]!)

/-- Draw `CommSq top left right bottom` as a square, with `top` along the top,
`left` down the left side, `right` down the right side, and `bottom` along the
bottom. Selecting either the proposition or a proof of it (a hypothesis `sq`)
works. -/
@[expr_presenter]
meta def commSqPresenter : ExprPresenter where
  userName := "CommSq diagram"
  layoutKind := .block
  present e := do
    let some (top, left, right, bottom) ← commSqSides? e
      | throwError "Not a CommSq."
    let some (A, B) := homType? (← inferType top) | throwError "Not a CommSq."
    let some (D, C) := homType? (← inferType bottom) | throwError "Not a CommSq."
    -- Mathlib's square layout is `A f B / i g / D h C`.
    mkCommDiag subSquare
      #[("A", A), ("B", B), ("C", C), ("D", D),
        ("f", top), ("g", right), ("h", bottom), ("i", left)]
