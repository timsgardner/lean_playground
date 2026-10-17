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

-- Definition 3.1.1: Constant functor and constant diagram functor
#print Functor.const
/-
Strictly speaking, `Functor.const 𝒥` is what Riehl (in the 2nd edition) calls the
"constant diagram functor" or sometimes the "diagonal functor," which sends
objects to their constant functor and morphisms to their constant natural
transformations in the functor category. So the signature of `Functor.const 𝒥`
is `𝒞 ⥤ (𝒥 ⥤ 𝒞)`, that is, its codomain is the *functor category* `𝒥 ⥤ 𝒞`,
in which objects are functors `𝒥 ⥤ 𝒞` and morphisms are natural transformations
between those functors. The constant diagram functor, then, sends an object
`c : 𝒞` to the constant functor `(Functor.const 𝒥).obj c : 𝒥 ⥤ 𝒞` (Riehl's `Δc`),
and sends a morphism `f : c₁ ⟶ c₂` in `𝒞` to a natural transformation from
`(Functor.const 𝒥).obj c₁` to `(Functor.const 𝒥).obj c₂` in which every
component is defined to be the morphism `f`.
-/

/-
A natural transformation `α : G ⟶ H` between functors `𝒥 ⥤ 𝒞` is a structure
whose component at `j : 𝒥` is the morphism `α.app j : G.obj j ⟶ H.obj j`.
So "every component of `(Functor.const 𝒥).map f` is `f`" says
`((Functor.const 𝒥).map f).app j = f` for all `j`.
-/
example {c₁ c₂ : 𝒞} (f : c₁ ⟶ c₂) (j : 𝒥) :
    ((Functor.const 𝒥).map f).app j = f := rfl

-- The same statement via the simp lemma `Functor.const_map_app`.
example {c₁ c₂ : 𝒞} (f : c₁ ⟶ c₂) (j : 𝒥) :
    ((Functor.const 𝒥).map f).app j = f := by
  simp

-- Likewise `Δc` sends every object of `𝒥` to `c`.
example {c : 𝒞} (j : 𝒥) : ((Functor.const 𝒥).obj c).obj j = c := rfl
