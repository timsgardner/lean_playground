/-
# Riehl, *Category Theory in Context*, §3.1: Universal cones
-/

import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools

open CategoryTheory
open scoped CategoryKindergarten

set_option pp.categoryTheory.hideConcreteHom true

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒥 : Type u₂} [Category.{v₂} 𝒥]
variable (F : 𝒞 ⥤ 𝒥)

-- Definition 3.1.1: Constant functor
#print Functor.const
