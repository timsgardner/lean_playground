import Mathlib.CategoryTheory.Adjunction.Basic

/-
Notation for transposes. `f ♭[adj]` is `adj.homEquiv _ _ f` and `g ♯[adj]` is
`(adj.homEquiv _ _).symm g`. The notation expands to exactly those terms, so the
Mathlib lemmas about `homEquiv` still apply with `rw` and `simp`, and the
delaborator below prints such terms back in this form in goals.
-/
section TransposeNotation
open Lean PrettyPrinter Delaborator SubExpr

notation:max f "♭[" adj "]" =>
  DFunLike.coe (CategoryTheory.Adjunction.homEquiv adj _ _) f
notation:max g "♯[" adj "]" =>
  DFunLike.coe (Equiv.symm (CategoryTheory.Adjunction.homEquiv adj _ _)) g

@[app_delab DFunLike.coe]
meta def delabAdjTranspose : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  let fn := e.appFn!.appArg!
  if fn.isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 6 delab
    let f ← withAppArg delab
    `($f ♭[$adj])
  else if fn.isAppOfArity ``Equiv.symm 3 &&
      (fn.getArg! 2).isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 2 <| withNaryArg 6 delab
    let g ← withAppArg delab
    `($g ♯[$adj])
  else failure

end TransposeNotation
