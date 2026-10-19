/-
# Riehl, *Category Theory in Context*, §3.1: Universal cones
-/

import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools

open CategoryTheory Opposite
open scoped CategoryKindergarten

set_option pp.categoryTheory.hideConcreteHom true

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒥 : Type u₂} [Category.{v₂} 𝒥]
variable (F : 𝒥 ⥤ 𝒞)

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

-- Definition 3.1.2: Cone
/-
Riehl: a cone over a diagram `F : 𝒥 ⥤ 𝒞` with summit `c : 𝒞` is a natural
transformation `λ : Δc ⇒ F`, i.e. a term of
`(Functor.const 𝒥).obj c ⟶ F`.

Mathlib's `Cone F` bundles the summit with the cone: a `Cone F` is a structure
with a field `pt : 𝒞` (the summit) and a field `π : (Functor.const 𝒥).obj pt ⟶ F`.
So Riehl's "cone over `F` with summit `c`" is the type of `π` for `pt := c`, and
`Cone F` is the type of pairs of a summit and such a cone.
-/
#print Limits.Cone

/-
Riehl's explicit description: the legs `λ j : c ⟶ F.obj j`, subject to the
triangle `λ j ≫ F.map f = λ k` for every `f : j ⟶ k`. Mathlib has the triangle
as `Limits.Cone.w`.
-/
example (K : Limits.Cone F) {j k : 𝒥} (f : j ⟶ k) :
    K.π.app j ≫ F.map f = K.π.app k := K.w f

/-- Riehl's explicit description is enough to define a cone: legs together with
commuting triangles give the natural transformation `Δc ⇒ F`. -/
def coneOfLegs (c : 𝒞) (leg : ∀ j : 𝒥, c ⟶ F.obj j)
    (triangle : ∀ {j k : 𝒥} (f : j ⟶ k), leg j ≫ F.map f = leg k) :
    (Functor.const 𝒥).obj c ⟶ F where
  app := leg
  naturality := by
    intro j k f
    exact (Category.id_comp _).trans (triangle f).symm


-- Definition 3.1.5: Limits and colimits I
/-
Riehl's `Cone(−, F) := Hom(Δ(−), F) : 𝒞ᵒᵖ ⥤ Set` is Mathlib's `F.cones`,
literally defined as `(Functor.const 𝒥).op ⋙ yoneda.obj F`.

Recall that `yoneda.obj F` is `Hom(-, F)` (or `Nat(-, F)`), where the Hom is
taken in the functor category `𝒥 ⥤ 𝒞`, so it is a functor
`(𝒥 ⥤ 𝒞)ᵒᵖ ⥤ Type`. Precomposing with `Δ(−)ᵒᵖ : 𝒞ᵒᵖ ⥤ (𝒥 ⥤ 𝒞)ᵒᵖ` yields
`Hom(Δ(−), F) : 𝒞ᵒᵖ ⥤ Type`. This sends an object `c` of `𝒞ᵒᵖ` to
`Hom(Δ(c), F)`, the set of *natural transformations* from `Δ(c)` to `F`. Such
a nat trans is a morphism `Δ(c) ⟶ F` in the functor category `𝒥 ⥤ 𝒞`, and its
components are all morphisms out of `c` in `𝒞` (not `𝒞ᵒᵖ`) into the image of
the diagram `F`. This can be pictured as a radial pattern from `c` to the
image of `F`, hence a "cone."
-/
#print Functor.cones

example : F.cones = (Functor.const 𝒥).op ⋙ yoneda.obj F := rfl

-- On objects: the functor `F.cones` sends `op c` (the image of `c : 𝒞` in `𝒞ᵒᵖ`)
-- to the set `Cone(c, F)` of natural transformations `Δc ⇒ F`.
example (c : 𝒞) : F.cones.obj (op c) = ((Functor.const 𝒥).obj c ⟶ F) := rfl

-- On morphisms: the functor `F.cones` sends `f.op : op d ⟶ op c` (the image of
-- `f : c ⟶ d` in `𝒞ᵒᵖ`) to the function `Cone(d, F) → Cone(c, F)` that sends a
-- cone `μ` with summit `d` to the cone with summit `c` whose `j`-th leg is
-- `f ≫ μ.app j`: first `f`, then the old leg.
-- Diagram: assets/cones_functor_on_morphisms.svg
example {c d : 𝒞} (f : c ⟶ d) (μ : (Functor.const 𝒥).obj d ⟶ F) (j : 𝒥) :
    (F.cones.map f.op μ).app j = f ≫ μ.app j := rfl

/-
A limit of `F` is a representation of `Cone(−, F)`. In Mathlib the cone together
with its universal property is `Limits.IsLimit t` for a `t : Limits.Cone F`, and
this is equivalent to `F.cones` being represented by `t.pt`.
-/
#print Limits.IsLimit

example (t : Limits.Cone F) (h : Limits.IsLimit t) : F.cones.RepresentableBy t.pt :=
  h.representableBy

-- The natural isomorphism `C(−, lim F) ≅ Cone(−, F)` (up to a `ULift`).
#check @Limits.IsLimit.natIso

/-
Dually, `Cone(F, −) := Hom(F, Δ(−)) : 𝒞 ⥤ Set` is `F.cocones`, and a colimit is a
corepresentation of it.
-/
#print Functor.cocones

example : F.cocones = Functor.const 𝒥 ⋙ coyoneda.obj (op F) := rfl

example (t : Limits.Cocone F) (h : Limits.IsColimit t) : F.cocones.CorepresentableBy t.pt :=
  h.corepresentableBy

#check @Limits.IsColimit.natIso
