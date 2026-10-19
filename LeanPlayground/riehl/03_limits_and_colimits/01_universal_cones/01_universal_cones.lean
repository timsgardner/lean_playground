/-
# Riehl, *Category Theory in Context*, §3.1: Universal cones
-/

import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.HasLimits
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

/-
On morphisms: the functor `F.cones` sends `f.op : op d ⟶ op c` (the image of
`f : c ⟶ d` in `𝒞ᵒᵖ`) to the function `Cone(d, F) → Cone(c, F)` that sends a
cone `μ` with summit `d` to the cone with summit `c` whose `j`-th leg is
`f ≫ μ.app j`: first `f`, then the old leg.

[Diagram](assets/cones_functor_on_morphisms.svg)
-/
example {c d : 𝒞} (f : c ⟶ d) (μ : (Functor.const 𝒥).obj d ⟶ F) (j : 𝒥) :
    (F.cones.map f.op μ).app j = f ≫ μ.app j := rfl

/-
A limit of `F` is a representation of `Cone(−, F)`. Unpacked, that is two
pieces of data:
* a *representing object* `lim F : 𝒞`, and
* a natural isomorphism `𝒞(−, lim F) ≅ Cone(−, F)` of functors `𝒞ᵒᵖ ⥤ Set`.

`lim F` is Riehl's notation for the representing object. It is an object of `𝒞`
(the summit of the limit cone), not a cone. By the Yoneda lemma the natural
isomorphism is determined by where it sends `𝟙 (lim F)`: an element of
`Cone(lim F, F)`, namely the *universal cone* `λ : Δ(lim F) ⇒ F`. At an object
`c`, the isomorphism sends `g : c ⟶ lim F` to the cone with legs `g ≫ λ j`
(the action of `F.cones` on `g.op`, as above). That it is a bijection is the
universal property: every cone over `F` with summit `c` has the form `g ≫ λ`
for exactly one `g : c ⟶ lim F`.

Mathlib splits this up differently:
* `Limits.Cone F` is just the bundle of a summit `pt` and a cone `π`.
* `Limits.IsLimit t`, for `t : Limits.Cone F`, says that `t` is universal. Its
  fields `lift`, `fac` and `uniq` are the universal property spelled out:
  existence and uniqueness of the factorization `g`. Here `t.pt` plays the role
  of `lim F` and `t.π` the role of `λ`.
* `Limits.HasLimit F` is the proposition that some such `t` exists.

So the pair (`lim F`, isomorphism) corresponds to a pair (`t`, `h : IsLimit t`).
-/
#print Limits.IsLimit

-- The same thing phrased as "`F.cones` is represented by `t.pt`", where the
-- data is an equivalence `(X ⟶ t.pt) ≃ Cone(X, F)` natural in `X`.
example (t : Limits.Cone F) (h : Limits.IsLimit t) : F.cones.RepresentableBy t.pt :=
  h.representableBy

/-
The *universal element*. A representation of a functor `G : 𝒞ᵒᵖ ⥤ Set` is the
same as a universal element: a pair `(Y, u)` of an object `Y` and an element
`u ∈ G(Y)` such that every element of every `G(c)` is `G(g.op) u` for exactly
one `g : c ⟶ Y`. For `G = Cone(−, F)` this is `(lim F, λ)`, the limit object
together with the universal cone `λ ∈ Cone(lim F, F)`.

In Lean, for a limit cone `t` with `h : IsLimit t`, the universal element is
`t.π`, which is literally an element of `F.cones.obj (op t.pt)`. For the chosen
limit it is `(Limits.limit.cone F).π`.
-/
example (t : Limits.Cone F) : F.cones.obj (op t.pt) := t.π

-- The representation sends `𝟙 t.pt` to the universal element...
example (t : Limits.Cone F) (h : Limits.IsLimit t) :
    h.representableBy.homEquiv (𝟙 t.pt) = t.π := by
  show (Functor.const 𝒥).map (𝟙 t.pt) ≫ t.π = t.π
  simp

-- ...and `g : c ⟶ t.pt` to the image of the universal element under `F.cones`
-- acting on `g.op`, i.e. the cone whose `j`-th leg is `g ≫ t.π.app j`.
example (t : Limits.Cone F) (h : Limits.IsLimit t) {c : 𝒞} (g : c ⟶ t.pt) :
    h.representableBy.homEquiv g = F.cones.map g.op t.π := rfl

example (t : Limits.Cone F) (h : Limits.IsLimit t) {c : 𝒞} (g : c ⟶ t.pt) (j : 𝒥) :
    (h.representableBy.homEquiv g).app j = g ≫ t.π.app j := rfl

/-
The natural isomorphism `𝒞(−, lim F) ≅ Cone(−, F)`, with `t.pt` for `lim F`.
It is stated up to `ULift`: hom-sets of `𝒞` live in `Type v₁` while `F.cones`
takes values in `Type (max u₂ v₁)`, so the left side is lifted to match.
-/
#check @Limits.IsLimit.natIso

/-
Translating the notation `lim F` into Lean: given `[Limits.HasLimit F]`, the
representing object is `Limits.limit F : 𝒞`, a chosen one (noncomputably) out of
the possibly many limit cones. The universal cone `λ` is `Limits.limit.cone F`,
whose summit is `limit F` by definition, and `Limits.limit.isLimit F` is the
proof that it is universal. Its legs are `Limits.limit.π F j : limit F ⟶ F.obj j`,
and the factorization `g : c ⟶ lim F` of a cone `s` is `Limits.limit.lift F s`.
-/
example [Limits.HasLimit F] : (Limits.limit.cone F).pt = Limits.limit F := rfl

noncomputable example [Limits.HasLimit F] : Limits.IsLimit (Limits.limit.cone F) :=
  Limits.limit.isLimit F

#check @Limits.limit.π
#check @Limits.limit.lift

/-
Dually, `Cone(F, −) := Hom(F, Δ(−)) : 𝒞 ⥤ Set` is `F.cocones`, and a colimit is a
corepresentation of it.
-/
#print Functor.cocones

example : F.cocones = Functor.const 𝒥 ⋙ coyoneda.obj (op F) := rfl

example (t : Limits.Cocone F) (h : Limits.IsColimit t) : F.cocones.CorepresentableBy t.pt :=
  h.corepresentableBy

#check @Limits.IsColimit.natIso


-- Definition 3.1.6: Limits and colimits II
/-
A limit is a terminal object in the category of cones over `F`: objects are
cones over `F` with any summit, and a morphism from a cone `λ : Δc ⇒ F` to a
cone `μ : Δd ⇒ F` is a morphism `f : c ⟶ d` such that `μ j ⋅ f = λ j` for all
`j` (each leg of the domain cone factors through the corresponding leg of the
codomain cone along `f`).

Riehl presents this as the category of elements `∫Cone(−, F)`. Mathlib gives the
category of cones directly: `Limits.Cone F` is a category whose morphisms are
`Limits.ConeMorphism`s, bundling `f` with the commuting triangles.
-/
#print Limits.ConeMorphism

example {A B : Limits.Cone F} (f : A ⟶ B) (j : 𝒥) :
    f.hom ≫ B.π.app j = A.π.app j := f.w j

/-
Riehl's category of elements is, in general, the comma category `(Δ ↓ F)`;
Mathlib records this for cones as an equivalence with `CostructuredArrow`.
-/
#check @Limits.Cone.equivCostructuredArrow

/-
Terminality unpacks to the universal property from before. For a cone `t` to be
terminal, every cone `s` needs a unique morphism `s ⟶ t`: that is `lift`, which
makes the legs of `s` factor through those of `t` (`fac`), together with its
uniqueness (`uniq`). In Mathlib, `IsLimit t` and `IsTerminal t` are equivalent,
and so a limit exists iff the category of cones has a terminal object.
-/
#check @Limits.Cone.isLimitEquivIsTerminal

example (t : Limits.Cone F) : Limits.IsLimit t ≃ Limits.IsTerminal t :=
  Limits.Cone.isLimitEquivIsTerminal t

example : Limits.HasLimit F ↔ Limits.HasTerminal (Limits.Cone F) :=
  Limits.hasLimit_iff_hasTerminal_cone F

-- The unique morphism from any cone `s` to a limit cone `t`.
example (t : Limits.Cone F) (h : Limits.IsLimit t) (s : Limits.Cone F) : s ⟶ t :=
  h.liftConeMorphism s

example (t : Limits.Cone F) (h : Limits.IsLimit t) (s : Limits.Cone F) (m : s ⟶ t) :
    m = h.liftConeMorphism s := h.uniq_cone_morphism

/-
Dually, a colimit is an initial object in the category of cocones under `F`,
where a morphism `λ ⟶ μ` of cocones with nadirs `c`, `d` is `f : c ⟶ d` with
`μ j = λ j ⋅ f`.
-/
example {A B : Limits.Cocone F} (f : A ⟶ B) (j : 𝒥) :
    A.ι.app j ≫ f.hom = B.ι.app j := f.w j

#check @Limits.Cocone.isColimitEquivIsInitial
#check @Limits.hasColimit_iff_hasInitial_cocone
