/-
# Riehl, *Category Theory in Context*, §4.1: Adjoint functors
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools

open CategoryTheory Opposite
open scoped CategoryKindergarten

-- set_option pp.categoryTheory.hideConcreteHom true
-- set_option pp.proofs true          -- print proof terms instead of ⋯
set_option pp.deepTerms true       -- don't elide deeply nested subterms
set_option linter.unusedTactic false

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]

-- Definition 4.1.1: Adjunctions I
