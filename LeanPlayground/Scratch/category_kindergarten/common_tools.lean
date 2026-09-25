/-
# Category Kindergarten: Common Tools

Small conventions shared by the category-kindergarten exploration files.
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-! ## Concrete-category morphisms

For a morphism in a concrete category, `ConcreteCategory.hom` exposes its
underlying function. Open the `CategoryKindergarten` scope to use `cchom` as a
short name for it.
-/

namespace CategoryKindergarten

scoped notation "cchom" => CategoryTheory.ConcreteCategory.hom

end CategoryKindergarten
