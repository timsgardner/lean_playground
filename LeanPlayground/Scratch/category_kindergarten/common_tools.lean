/-
# Category Kindergarten: Common Tools

Small conventions shared by the category-kindergarten exploration files.
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Lean.PrettyPrinter.Delaborator.Basic

/-! ## Concrete-category morphisms

For a morphism in a concrete category, `ConcreteCategory.hom` exposes its
underlying function. Open the `CategoryKindergarten` scope to use `cchom` as a
short name for it.
-/

namespace CategoryKindergarten

scoped notation "cchom" => CategoryTheory.ConcreteCategory.hom

end CategoryKindergarten




open Lean PrettyPrinter Delaborator SubExpr

register_option pp.categoryTheory.hideConcreteHom : Bool := {
  defValue := false
  descr := "Pretty-print ConcreteCategory.hom f as f"
}

@[app_delab CategoryTheory.ConcreteCategory.hom]
meta def delabConcreteCategoryHom : Delab := do
  unless pp.categoryTheory.hideConcreteHom.get (← getOptions) do
    failure
  withAppArg delab
