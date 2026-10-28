/-
# Riehl, *Category Theory in Context*, §3.1: Universal cones
-/

import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Discrete.SumsProducts
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic
import LeanPlayground.Scratch.category_kindergarten.common_tools
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Tactic.Check
import Mathlib.CategoryTheory.IsoCat
import Mathlib.CategoryTheory.Category.Cat.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open CategoryTheory Limits Opposite
open scoped CategoryKindergarten

-- set_option pp.categoryTheory.hideConcreteHom true
-- set_option pp.proofs true          -- print proof terms instead of ⋯
set_option pp.deepTerms true       -- don't elide deeply nested subterms
set_option linter.unusedTactic false

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
#print Cone

/-
Riehl's explicit description: the legs `λ j : c ⟶ F.obj j`, subject to the
triangle `λ j ≫ F.map f = λ k` for every `f : j ⟶ k`. Mathlib has the triangle
as `Cone.w`.
-/
example (K : Cone F) {j k : 𝒥} (f : j ⟶ k) :
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
* `Cone F` is just the bundle of a summit `pt` and a cone `π`.
* `IsLimit t`, for `t : Cone F`, says that `t` is universal. Its
  fields `lift`, `fac` and `uniq` are the universal property spelled out:
  existence and uniqueness of the factorization `g`. Here `t.pt` plays the role
  of `lim F` and `t.π` the role of `λ`.
* `HasLimit F` is the proposition that some such `t` exists.

So the pair (`lim F`, isomorphism) corresponds to a pair (`t`, `h : IsLimit t`).
-/
#print IsLimit

-- The same thing phrased as "`F.cones` is represented by `t.pt`", where the
-- data is an equivalence `(X ⟶ t.pt) ≃ Cone(X, F)` natural in `X`.
example (t : Cone F) (h : IsLimit t) : F.cones.RepresentableBy t.pt :=
  h.representableBy

/-
The *universal element*. A representation of a functor `G : 𝒞ᵒᵖ ⥤ Set` is the
same as a universal element: a pair `(Y, u)` of an object `Y` and an element
`u ∈ G(Y)` such that every element of every `G(c)` is `G(g.op) u` for exactly
one `g : c ⟶ Y`. For `G = Cone(−, F)` this is `(lim F, λ)`, the limit object
together with the universal cone `λ ∈ Cone(lim F, F)`.

In Lean, for a limit cone `t` with `h : IsLimit t`, the universal element is
`t.π`, which is literally an element of `F.cones.obj (op t.pt)`. For the chosen
limit it is `(limit.cone F).π`.
-/
example (t : Cone F) : F.cones.obj (op t.pt) := t.π

-- The representation sends `𝟙 t.pt` to the universal element...
example (t : Cone F) (h : IsLimit t) :
    h.representableBy.homEquiv (𝟙 t.pt) = t.π := by
  show (Functor.const 𝒥).map (𝟙 t.pt) ≫ t.π = t.π
  simp

-- ...and `g : c ⟶ t.pt` to the image of the universal element under `F.cones`
-- acting on `g.op`, i.e. the cone whose `j`-th leg is `g ≫ t.π.app j`.
example (t : Cone F) (h : IsLimit t) {c : 𝒞} (g : c ⟶ t.pt) :
    h.representableBy.homEquiv g = F.cones.map g.op t.π := rfl

example (t : Cone F) (h : IsLimit t) {c : 𝒞} (g : c ⟶ t.pt) (j : 𝒥) :
    (h.representableBy.homEquiv g).app j = g ≫ t.π.app j := rfl

/-
The natural isomorphism `𝒞(−, lim F) ≅ Cone(−, F)`, with `t.pt` for `lim F`.
It is stated up to `ULift`: hom-sets of `𝒞` live in `Type v₁` while `F.cones`
takes values in `Type (max u₂ v₁)`, so the left side is lifted to match.
-/
#check @IsLimit.natIso

/-
Translating the notation `lim F` into Lean: given `[HasLimit F]`, the
representing object is `limit F : 𝒞`, a chosen one (noncomputably) out of
the possibly many limit cones. The universal cone `λ` is `limit.cone F`,
whose summit is `limit F` by definition, and `limit.isLimit F` is the
proof that it is universal. Its legs are `limit.π F j : limit F ⟶ F.obj j`,
and the factorization `g : c ⟶ lim F` of a cone `s` is `limit.lift F s`.
-/
example [HasLimit F] : (limit.cone F).pt = limit F := rfl

noncomputable example [HasLimit F] : IsLimit (limit.cone F) :=
  limit.isLimit F

#check @limit.π
#check @limit.lift

/-
Dually, `Cone(F, −) := Hom(F, Δ(−)) : 𝒞 ⥤ Set` is `F.cocones`, and a colimit is a
corepresentation of it.
-/
#print Functor.cocones

example : F.cocones = Functor.const 𝒥 ⋙ coyoneda.obj (op F) := rfl

example (t : Cocone F) (h : IsColimit t) : F.cocones.CorepresentableBy t.pt :=
  h.corepresentableBy

#check @IsColimit.natIso


-- Definition 3.1.6: Limits and colimits II
/-
A limit is a terminal object in the category of cones over `F`: objects are
cones over `F` with any summit, and a morphism from a cone `λ : Δc ⇒ F` to a
cone `μ : Δd ⇒ F` is a morphism `f : c ⟶ d` such that `μ j ⋅ f = λ j` for all
`j` (each leg of the domain cone factors through the corresponding leg of the
codomain cone along `f`).

Riehl presents this as the category of elements `∫Cone(−, F)`. Mathlib gives the
category of cones directly: `Cone F` is a category whose morphisms are
`ConeMorphism`s, bundling `f` with the commuting triangles.
-/
#print ConeMorphism

example {A B : Cone F} (f : A ⟶ B) (j : 𝒥) :
    f.hom ≫ B.π.app j = A.π.app j := f.w j

/-
Riehl's category of elements is, in general, the comma category `(Δ ↓ F)`;
Mathlib records this for cones as an equivalence with `CostructuredArrow`.
-/
#check @Cone.equivCostructuredArrow

/-
Terminality unpacks to the universal property from before. For a cone `t` to be
terminal, every cone `s` needs a unique morphism `s ⟶ t`: that is `lift`, which
makes the legs of `s` factor through those of `t` (`fac`), together with its
uniqueness (`uniq`). In Mathlib, `IsLimit t` and `IsTerminal t` are equivalent,
and so a limit exists iff the category of cones has a terminal object.
-/
#check @Cone.isLimitEquivIsTerminal

example (t : Cone F) : IsLimit t ≃ IsTerminal t :=
  Cone.isLimitEquivIsTerminal t

example : HasLimit F ↔ HasTerminal (Cone F) :=
  hasLimit_iff_hasTerminal_cone F

-- The unique morphism from any cone `s` to a limit cone `t`.
example (t : Cone F) (h : IsLimit t) (s : Cone F) : s ⟶ t :=
  h.liftConeMorphism s

example (t : Cone F) (h : IsLimit t) (s : Cone F) (m : s ⟶ t) :
    m = h.liftConeMorphism s := h.uniq_cone_morphism

/-
Dually, a colimit is an initial object in the category of cocones under `F`,
where a morphism `λ ⟶ μ` of cocones with nadirs `c`, `d` is `f : c ⟶ d` with
`μ j = λ j ⋅ f`.
-/
example {A B : Cocone F} (f : A ⟶ B) (j : 𝒥) :
    A.ι.app j ≫ f.hom = B.ι.app j := f.w j

#check @Cocone.isColimitEquivIsInitial
#check @hasColimit_iff_hasInitial_cocone


-- Definition 3.1.9: Products
/-
A *product* is a limit of a diagram indexed by a discrete category, one with
only identity morphisms. Such a diagram is just a family of objects `F j`
indexed by `j ∈ 𝒥`. A cone over it is a family of legs `λ j : c ⟶ F j` subject
to no further constraints, because the triangles only involve identity
morphisms. The limit is written `∏ⱼ F j`, its legs are the *projections*
`π k : ∏ⱼ F j ⟶ F k`, and the universal property says that composition with the
projections is a natural isomorphism
  `𝒞(c, ∏ⱼ F j) ≅ ∏ₖ 𝒞(c, F k) ≅ Cone(c, F)`.

First, "no further constraints". For a general diagram, each `f : j ⟶ k` in
`𝒥` puts a morphism `F.map f : F j ⟶ F k` between the endpoints of the legs
`λ j` and `λ k`, and the cone must make the triangle `λ j ≫ F.map f = λ k`
commute. In a discrete `𝒥` there are no morphisms between distinct objects, so
the image of `F` has no morphisms between the endpoints of distinct legs, and
no commutativity condition relates one leg to another. The only morphisms left
are identities `f = 𝟙 j`, whose triangles `λ j ≫ 𝟙 = λ j` hold automatically.
So any family of legs is a cone.
-/
variable [IsDiscrete 𝒥] in
def coneOfDiscreteLegs (c : 𝒞) (leg : ∀ j : 𝒥, c ⟶ F.obj j) :
    (Functor.const 𝒥).obj c ⟶ F :=
  coneOfLegs F c leg fun {j k} f => by
    obtain rfl := IsDiscrete.eq_of_hom f
    obtain rfl : f = 𝟙 j := Subsingleton.elim _ _
    simp

/-
Mathlib indexes products by a type `β` and a family of objects `f : β → 𝒞` (a
plain function, not a functor), that is, by the discrete category `Discrete β`
and the diagram `Discrete.functor f`. A `Fan f` is by definition a
`Cone` over that diagram (a summit together with legs), and `Fan.mk P p`
builds one from a summit `P` and legs `p b : P ⟶ f b`.
-/
example {β : Type*} (f : β → 𝒞) : Fan f = Cone (Discrete.functor f) := rfl

#print Fan.mk

/-
The second isomorphism: over a discrete diagram, cones with summit `c` are the
same as families of legs, so `Cone(c, F) ≅ ∏ₖ 𝒞(c, F k)`.

Matching Riehl's notation to the code:
* The diagram `F` is `Discrete.functor f : Discrete β ⥤ 𝒞`. An object of
  `Discrete β` is an index `b : β` wrapped as `⟨b⟩` (unwrapped by `.as`), and
  `F k` is `(Discrete.functor f).obj ⟨b⟩`, which is `f b` by definition.
* `Cone(c, F)` is the left side `(Discrete.functor f).cones.obj (op c)`: the
  functor `Cone(−, F)` from Definition 3.1.5, evaluated at `c`. It unfolds to
  the natural transformations `Δc ⇒ F`, i.e.
  `(Functor.const (Discrete β)).obj c ⟶ Discrete.functor f`. The summit `c` is
  fixed here, unlike in `Fan f` above, which bundles a summit `pt` with
  its legs.
* `∏ₖ 𝒞(c, F k)`, the product of the hom-sets, is the right side
  `∀ b, c ⟶ f b`: an element is a choice of leg `c ⟶ f b` for every `b`.
* Left to right (`toFun`) takes a cone `μ` to its legs `μ.app ⟨b⟩`. Right to
  left (`invFun`) assembles legs `p` into a natural transformation with
  `Discrete.natTrans`, which needs no naturality proof because `Discrete β` has
  only identity morphisms.
-/
def coneEquivFamily {β : Type*} (f : β → 𝒞) (c : 𝒞) :
    (Discrete.functor f).cones.obj (op c) ≃ (∀ b, c ⟶ f b) where
  toFun μ b := μ.app ⟨b⟩
  invFun p := Discrete.natTrans fun j => p j.as
  left_inv _ := NatTrans.ext (funext fun _ => rfl)
  right_inv _ := rfl

/-
The product itself. `[HasProduct f]` says that the diagram
`Discrete.functor f` has a limit (`HasProduct f` is `HasLimit (Discrete.functor
f)`), and Mathlib's product is the chosen limit cone from §3.1.5:
* `piObj f`, written `∏ᶜ f` (the notation is in the `Limits` namespace),
  is the *summit* of that limit cone, i.e. `limit (Discrete.functor f)`.
  This is Riehl's `∏ⱼ F j`.
* `Pi.π f b : ∏ᶜ f ⟶ f b` are the *legs* of that limit cone, i.e.
  `limit.π (Discrete.functor f) ⟨b⟩`. These are Riehl's projections
  `π k`.
* Packaged as a fan, `Fan.mk (∏ᶜ f) (Pi.π f)`, this cone is a limit cone:
  `productIsProduct`.
* `Pi.lift p`, for legs `p b : c ⟶ f b` of another cone with summit `c`,
  is the unique map `c ⟶ ∏ᶜ f` through which those legs factor
  (`Pi.lift_comp_π`, `Pi.hom_ext`).

The first isomorphism, `𝒞(c, ∏ⱼ F j) ≅ ∏ₖ 𝒞(c, F k)`, is `(π k)_*`: it sends
`g` to the family `(g ≫ π k)ₖ`, with inverse `Pi.lift`.
-/
example {β : Type*} (f : β → 𝒞) [HasProduct f] : ∏ᶜ f = limit (Discrete.functor f) := rfl

example {β : Type*} (f : β → 𝒞) [HasProduct f] (b : β) :
    Pi.π f b = limit.π (Discrete.functor f) ⟨b⟩ := rfl

noncomputable example {β : Type*} (f : β → 𝒞) [HasProduct f] :
    IsLimit (Fan.mk (∏ᶜ f) (Pi.π f)) :=
  productIsProduct f

noncomputable def homToProductEquivFamily {β : Type*} (f : β → 𝒞) [HasProduct f] (c : 𝒞) :
    (c ⟶ ∏ᶜ f) ≃ ∀ b, c ⟶ f b where
  toFun g b := g ≫ Pi.π f b
  invFun p := Pi.lift p
  left_inv _ := Pi.hom_ext _ _ fun b => Pi.lift_comp_π _ b
  right_inv p := funext fun b => Pi.lift_comp_π p b

/-
Products are limits in the sense of §3.1.5, not just objects that happen to
coincide: Riehl's isomorphism for products *is* the limit representation.

Fix `g : c ⟶ ∏ᶜ f`. There are two ways to turn it into a cone over
`Discrete.functor f` with summit `c`:
1. Riehl's product-specific composite
   `𝒞(c, ∏ⱼ F j) ≅ ∏ₖ 𝒞(c, F k) ≅ Cone(c, F)`: `homToProductEquivFamily` sends `g` to
   the family of legs `(g ≫ Pi.π f b)_b`, and `coneEquivFamily.symm`
   assembles that family into a natural transformation.
2. The general theory of limits: `productIsProduct f` says the product fan is a
   limit cone, so `IsLimit.representableBy` gives a representation of
   `(Discrete.functor f).cones` by `∏ᶜ f`. Its `homEquiv` sends `g` to the
   universal cone with its legs precomposed with `g`, i.e.
   `(Discrete.functor f).cones.map g.op` applied to the product fan's legs, as
   in §3.1.5.

The example says the two routes give the same cone for every `g`. Two natural
transformations are equal when their components are (`NatTrans.ext`), and at
each index `b` both sides unfold to `g ≫ Pi.π f b`, so each component is
`rfl`. Comparing the forward maps is enough, since two equivalences with the
same forward function are equal; naturality in `c` comes along with
`representableBy`.
-/
example {β : Type*} (f : β → 𝒞) [HasProduct f] (c : 𝒞) (g : c ⟶ ∏ᶜ f) :
    (coneEquivFamily f c).symm (homToProductEquivFamily f c g) =
      (productIsProduct f).representableBy.homEquiv g :=
  NatTrans.ext (funext fun _ => rfl)


/-
## Practice: categorical products vs. cartesian products

Before Example 3.1.10, a few exercises connecting the categorical product of
3.1.9 to the products you already know, working in the category `Type w` of
types and functions. (Every `sorry` below is yours to fill in.)

In `Type w` a morphism `X ⟶ Y` is a function wrapped as a morphism: `↾φ` (that
is, `TypeCat.ofHom φ`) turns `φ : X → Y` into `X ⟶ Y`, and a morphism
`h : X ⟶ Y` can be applied to `x : X` as `h x`.
-/
universe w

/-
Exercise 1. Binary products first: the cartesian product `X × Y`, with
`Prod.fst` and `Prod.snd` as legs, is a binary product in `Type w`.

Mathlib's binary products have their own small API, parallel to `Fan`:
* A `BinaryFan X Y` is a cone over the two-object discrete diagram `X, Y`
  (indexed by `WalkingPair`, which has two objects `left` and `right`). It has a
  summit `pt` and two legs `fst : pt ⟶ X` and `snd : pt ⟶ Y`.
* `BinaryFan.mk fst snd` builds one from its two legs.
* `BinaryFan.IsLimit.mk` proves one is a limit, given: a `lift` that turns any
  pair of maps `f : T ⟶ X`, `g : T ⟶ Y` into a map `T ⟶ pt`; the two laws
  `lift f g ≫ fst = f` and `lift f g ≫ snd = g`; and uniqueness of `lift f g`.
  (Try `apply BinaryFan.IsLimit.mk` and look at the goals.)
-/
example (X Y : Type w) :
    IsLimit (BinaryFan.mk (P := X × Y) (↾Prod.fst) (↾Prod.snd)) := by
  apply BinaryFan.IsLimit.mk
  case lift =>
    intro T tx ty
    exact ↾(fun x => (tx x, ty x))
  case hl₁ =>
    intro T tx ty
    rfl
  · intro T tx ty
    conv =>
      lhs
      simp
    rfl
  · intro T tx ty tfanpt
    simp
    intro hx hy
    ext tt
    unfold BinaryFan.mk at tfanpt
    simp at tfanpt
    rw [← hx, ← hy]
    rfl


/-
Exercise 2. The bridge: a pair is a dependent function out of `Bool`.

Package `X` and `Y` as a family indexed by `Bool`: `fun b => cond b X Y` sends
`true` to `X` and `false` to `Y`. An element `p : ∀ b : Bool, cond b X Y` is a
function whose *output type depends on its input*: `p true : X` and
`p false : Y`. That is exactly the data of a pair, one element of `X` and one
of `Y`.

(2a) Show this as an equivalence of types. Hint: to define a function out of
`Bool` whose output type depends on the input, use `match b with | true => …
| false => …`; to prove two such functions equal, `funext b` and then
`cases b`.
-/
example (X Y : Type w) : (∀ b : Bool, cond b X Y) ≃ X × Y := by
  let toFun : (∀ b : Bool, cond b X Y) → X × Y :=
    (fun b => (b true, b false))
  let invFun : X × Y → (∀ b : Bool, cond b X Y) :=
    (fun p b =>
      match b with
      | true => p.1
      | false => p.2)
  constructor
  case toFun => exact toFun
  case invFun => exact invFun
  case left_inv =>
    show (Function.LeftInverse invFun toFun)
    intro df
    simp only [invFun, toFun]
    ext b
    cases b <;> simp
  case right_inv =>
    -- same idea, yada yada
    cat_disch

theorem beetle {A B: Type w} (f: A → B) (a: A) :
    (cchom (↾ f)) a = f a := by
  cat_disch

/-
(2b) The same bridge, categorically: `X × Y` with legs `Prod.fst` (at `true`)
and `Prod.snd` (at `false`) is a product, in the `Fan` sense of 3.1.9, of the
`Bool`-indexed family. Use `apply Fan.IsLimit.mk`, and expect `cases` on the
index `j : Bool` in the laws.
-/
example (X Y : Type w) :
    IsLimit
      (Fan.mk
        (f := fun b => cond b X Y)
        (X × Y) -- the summit
        (fun b => match b with
          | true => ↾Prod.fst
          | false => ↾Prod.snd)) := by
  apply Fan.IsLimit.mk
  case lift =>
    intro fan
    apply TypeCat.ofHom
    intro fan_pt
    dsimp [Fan.mk]
    #check TypeCat.homEquiv (fan.proj true)
    let true_fn := TypeCat.homEquiv (fan.proj true)
    let false_fn := TypeCat.homEquiv (fan.proj false)
    exact (true_fn fan_pt, false_fn fan_pt)
  · cat_disch
  · simp
    intro bf m1 true_fn false_fn
    change bf.pt ⟶ (X × Y) at m1
    ext bf_pt
    · simp
      conv => rhs; change TypeCat.homEquiv (bf.proj true) bf_pt; simp
      rw [← false_fn]
      rfl
    · simp
      rw [←true_fn]
      rfl


/-
Exercise 3. The general case: for any index type `β` and family `X : β → Type w`,
the dependent function type `∀ b, X b`, with the evaluation maps `x ↦ x b` as
legs, is a product of the family `X`. Exercise 2 is the case `β := Bool`.
Hint: `Fan.IsLimit.mk` asks for a `lift` and the two laws; given a cone `s`,
what function `s.pt → ∀ b, X b` do its legs determine?
-/
def dep_fan_is_limit {β : Type w} (X : β → Type w) :
    IsLimit (Fan.mk (∀ b, X b) (fun b => ↾(fun x => x b))) := by
  apply Fan.IsLimit.mk
  case lift =>
    intro fan
    apply TypeCat.ofHom
    change fan.pt → ∀ b, X b
    intro spt b
    exact (fan.proj b) spt
  · cat_disch
  case uniq =>
    intro fan mpt hb
    unfold id
    conv =>
      rhs
      congr
      intro fpt b
      lhs
      arg 1
      erw [← hb]
      simp
    rfl

/-
Exercise 4. Mathlib's chosen product `∏ᶜ X` (the summit of *some* limit cone,
picked by `HasProduct`) is isomorphic in `Type w` to the dependent function type.
Try it with `Pi.lift` and `Pi.π`, or derive it from Exercise 3 and essential
uniqueness of limits (Prop. 3.1.7, `IsLimit.conePointUniqueUpToIso`).
-/
noncomputable def productIsoPiType {β : Type w} (X : β → Type w) : ∏ᶜ X ≅ (∀ b : β, X b) := by
  -- Going through lift directly is too confusing at this point.
  -- Extract the map to `∏ᶜ` by making a cone with summit `(∀ b : β, X b)`
  -- and lifting to `∏ᶜ`.
  -- `X` induces the diagram. The legs are indexed by `β` -- but don't confuse
  -- this with a bijection between leg endpoints and `β`, or even legs and `β`.
  -- What does it mean to have this cone? The annoying / confusing part here
  -- is the semantic redundancy.
  -- For every `b` in `β`, we can make a morphism `(∀ b : β, X b) ⟶ X b`
  -- that "closes over" `b` and takes any dependent function
  -- `df : (∀ b : β, X b)` to its action on that `b`, that is, to `df b`.
  let prod_cone : Fan X := Fan.mk _ (Pi.π X)
  have prod_cone_is_limit : IsLimit prod_cone := by
    apply productIsProduct
  let dep_cone : Fan X := Fan.mk (∀ b : β, X b) (fun b => ↾(fun df => df b))
  have dep_cone_is_limit : IsLimit dep_cone := by
    apply dep_fan_is_limit
  exact IsLimit.conePointUniqueUpToIso prod_cone_is_limit dep_cone_is_limit


def pointEquiv (Z : Type w) : (PUnit.{w + 1} ⟶ Z) ≃ Z :=
  TypeCat.homEquiv.trans (Equiv.punitArrowEquiv Z)

#check TypeCat.homEquiv.trans

example
    (A B γ : Type)
    (e : (A → B) ≃ γ)
    : True := by
  #check (TypeCat.homEquiv.trans e)
  -- TypeCat.homEquiv.trans e : (A ⟶ B) ≃ γ
  trivial

/-
Exercise 5. Riehl's trick from Example 3.1.10: probe the product with the point.
Maps `PUnit ⟶ Z` in `Type w` are the same as elements of `Z`, so taking
`c := PUnit` in `homToProductEquivFamily` says the elements of `∏ᶜ X` are exactly the
families `(x b)_b` with `x b : X b`. Build this as an equivalence of types.
-/
noncomputable example {β : Type w} (X : β → Type w) : (∏ᶜ X : Type w) ≃ (∀ b, X b) := by
  calc
    ∏ᶜ X ≃ (PUnit ⟶ ∏ᶜ X) := (pointEquiv (∏ᶜ X)).symm
    _ ≃ ((b : β) → PUnit.{w + 1} ⟶ X b) := homToProductEquivFamily (f := X) (c := PUnit)
    _ ≃ (∀ b, X b) := Equiv.piCongrRight (fun b => pointEquiv (X b))


-- Definition 3.1.11: Terminal objects
/-
A terminal object is a limit of the empty diagram. A cone over an empty diagram
is just its summit, and any morphism of summits is a cone morphism, since every
leg, triangle and naturality square is indexed by some `j : 𝒥` and there are
none (`isEmptyElim j` discharges each). So the category of cones is isomorphic
to `𝒞`, and a terminal cone is a terminal object of `𝒞`.
-/
section EmptyDiagram

variable [IsEmpty 𝒥]

/-- Any object is the summit of a (unique) cone over the empty diagram. -/
def emptyCone (c : 𝒞) : Cone F where
  pt := c
  π := { app := fun j => isEmptyElim j, naturality := fun j => isEmptyElim j }

/-- Any morphism of summits is a morphism of empty cones. -/
def emptyConeHom {s t : Cone F} (f : s.pt ⟶ t.pt) : s ⟶ t where
  hom := f
  w j := isEmptyElim j

/-- Every cone is the empty cone on its summit: there is no other data. -/
theorem emptyCone_pt (s : Cone F) : emptyCone F s.pt = s := by
  cases s with | mk pt π =>
  show Cone.mk pt _ = Cone.mk pt π
  congr
  ext j; exact isEmptyElim j

/-
`Cone F ≅ 𝒞` as an isomorphism of categories (Riehl §1.3: functors whose
composites *equal* the identities; Mathlib's `IsoCat`). `Functor.IsIso` is the
criterion "fully faithful and bijective on objects", and `asIsomorphism`
builds the `IsoCat` from it.
-/
theorem forget_isIso : (Cone.forget F).IsIso where
  faithful := ⟨fun h => by ext; exact h⟩
  full := ⟨fun f => ⟨emptyConeHom F f, rfl⟩⟩
  bijective_obj :=
    ⟨fun s t h => by rw [← emptyCone_pt F s, ← emptyCone_pt F t]; exact congrArg _ h,
     fun c => ⟨emptyCone F c, rfl⟩⟩

noncomputable def conesIsoCat : IsoCat (Cone F) 𝒞 :=
  have := forget_isIso F
  (Cone.forget F).asIsomorphism

/-- A limit of the empty diagram is an object with a unique map from everywhere
(Definition 1.6.14), and conversely. -/
def isLimitEquivUnique (t : Cone F) : IsLimit t ≃ ∀ c : 𝒞, Unique (c ⟶ t.pt) where
  toFun ht c :=
    { default := ht.lift (emptyCone F c)
      uniq m := ht.uniq (emptyCone F c) m (fun j => isEmptyElim j) }
  invFun h :=
    { lift s := (h s.pt).default
      fac _ j := isEmptyElim j
      uniq s m _ := (h s.pt).uniq m }
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end EmptyDiagram

/-
The Mathlib point: rather than proving this, Mathlib takes 3.1.11 as the
*definition*. `IsTerminal X` is literally `IsLimit` of the empty cone on `X`
(over `Functor.empty 𝒞 : Discrete PEmpty ⥤ 𝒞`), and Definition 1.6.14 is the
theorem `isTerminalEquivUnique`. In practice: `IsTerminal.ofUniqueHom` to prove
terminality, `IsTerminal.from` and `IsTerminal.hom_ext` to use it. The chosen
terminal object `⊤_ 𝒞` is the chosen limit of the empty diagram.
-/
example (X : 𝒞) : IsTerminal X = IsLimit (asEmptyCone X) := rfl

example [HasTerminal 𝒞] : (⊤_ 𝒞) = limit (Functor.empty.{0} 𝒞) := rfl

example : IsTerminal (PUnit.{w + 1} : Type w) :=
  IsTerminal.ofUniqueHom (fun _ => ↾(fun _ => PUnit.unit)) (fun _ _ => rfl)


-- Example 3.1.12: The terminal category
/-
Riehl's `𝟙`, one object and only its identity, is `Discrete PUnit`, and it is
terminal in `Cat`: every category has exactly one functor to it, sending every
object to the point and every morphism to the identity. Uniqueness is an
equality of *functors*, which holds because a functor into `𝟙` has no choice on
objects (`Unique`) or on morphisms (`IsDiscrete`: hom-sets are subsingletons).
Mathlib proves exactly that, `Cat.isTerminalOfUniqueOfIsDiscrete`, and
specializes it to `Discrete PUnit`.

Fun fact: Riehl wrote this one herself. The file
`Mathlib/CategoryTheory/Category/Cat/Terminal.lean` is copyright Emily Riehl,
with authors Robin Carlier and Emily Riehl.

Mathlib's `Cat.{v, u}` is the category of categories with objects in `Type u`
and morphisms in `Type v`, so Riehl's `Cat` and `CAT` are both instances of it
at different universe levels.
-/
example : IsTerminal (Cat.of (Discrete PUnit)) := Cat.isTerminalDiscretePUnit

#check @Cat.isTerminalOfUniqueOfIsDiscrete


-- Definition 3.1.13: Equalizers
/-
An equalizer is a limit of a diagram indexed by the parallel pair `• ⇉ •`.

In Mathlib:
* The indexing category is `WalkingParallelPair`, with objects `zero` and `one`
  and morphisms `WalkingParallelPairHom`: `left, right : zero ⟶ one` plus
  identities.
* A diagram of that shape is `parallelPair f g : WalkingParallelPair ⥤ 𝒞`, for
  `f g : A ⟶ B`. It sends `zero ↦ A`, `one ↦ B`, `left ↦ f`, `right ↦ g`.
* A `Fork f g` is by definition a `Cone (parallelPair f g)`.

In the diagram below, the top row is the indexing category `WalkingParallelPair`
with its identity morphisms omitted, and the bottom row is its image under the
functor `parallelPair f g`. The dotted arrows record what the functor does on
objects: `(parallelPair f g).obj .zero = A` and `(parallelPair f g).obj .one =
B`. On morphisms it sends the upper arrow to the upper arrow and the lower to
the lower, so that `(parallelPair f g).map .left = f` and
`(parallelPair f g).map .right = g`. All four equations hold by `rfl`.

[Diagram](assets/parallel_pair.svg)

Riehl writes composition right to left (`f a` for "first `a`, then `f`"). The
discussion below instead uses Lean's left-to-right notation throughout
(`a ≫ f`), so its equations are reversed relative to hers.

A cone over this diagram with summit `C` consists of a pair of morphisms
`a : C ⟶ A` and `b : C ⟶ B` (the components of the natural transformation at
`zero` and at `one`) such that `a ≫ f = b` and `a ≫ g = b`. These two equations are
the naturality conditions for the two non-identity morphisms `left` and
`right` of the indexing category. For instance, naturality at `left` says
`𝟙 C ≫ b = a ≫ f`, since the constant functor sends `left` to `𝟙 C` and
`parallelPair f g` sends it to `f`. The naturality conditions for the identity
morphisms hold automatically. Together, the two equations imply `a ≫ f = a ≫ g`,
and they force `b` to equal that common composite. A cone over `f, g` is
therefore determined by the single morphism `a`, subject to the condition
`a ≫ f = a ≫ g`.

The diagram below draws such a cone `π` as what it literally is in Lean, a
natural transformation from the constant functor at `c` to `parallelPair f g`.
The top row is the constant functor applied to `zero ⇉ one`: both objects go to
`c`, and both `left` and `right` go to the identity of `c`. The bottom row is
`parallelPair f g`, as above. The vertical arrows are the two components
`π.app .zero` and `π.app .one`, and the naturality squares are the upper square
(for `left`) and the lower square (for `right`). `π.naturality .left` is the
equation of the upper square, `𝟙 c ≫ π.app .one = π.app .zero ≫ f`.

[Diagram](assets/cone_over_parallel_pair.svg)

Mathlib's fork API is built around that observation. For a fork `t`, the leg
`t.ι` is the component at `zero` (Riehl's `a`), and `t.condition` is the
equation `t.ι ≫ f = t.ι ≫ g`. The component at `one` (Riehl's `b`) is still
part of the data, but it equals `t.ι ≫ f`. This is the upper naturality square
again, in the form `t.w .left : t.π.app .zero ≫ f = t.π.app .one`. This is the
`Cone.w` from the start of the file, which every cone provides for each arrow
of its index category, with the identity `𝟙 t.pt` already removed.
Conversely, `Fork.ofι a h` builds a fork from a morphism `a` and a proof
`h : a ≫ f = a ≫ g`, supplying `a ≫ f` as the component at `one`.

The first diagram below labels the parts of an arbitrary fork `t` by their Lean
names. Its summit is the field `t.pt`, and its two legs are the components of
the natural transformation `t.π`. The leg at `zero` has the abbreviation `t.ι`.
The leg at `one` is dotted because it is determined by the other arrows: it
equals `t.ι ≫ f`, and also `t.ι ≫ g`. The second diagram shows the fork that
`Fork.ofι a h` builds, with summit `c`, leg `a`, and `a ≫ f` as the dotted
component at `one`.

[Diagram](assets/fork_fields.svg)

[Diagram](assets/fork_of_iota.svg)
-/
#print WalkingParallelPairHom

example {A B : 𝒞} (f g : A ⟶ B) : Fork f g = Cone (parallelPair f g) := rfl

example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) : t.ι = t.π.app .zero := rfl

example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) :
    t.π.app .one = t.ι ≫ f := (t.w .left).symm

/-
The equalizer is a limit cone over `f, g`. Call its summit `E` and its
components `h : E ⟶ A` and `q : E ⟶ B`, so that `h ≫ f = q = h ≫ g`. Riehl's
equalizer diagram leaves out `q`, for the reason just given. The diagram below
includes it, together with a second cone `(a, b)` with summit `C`, so that it
matches the general picture of a cone: one leg to each object of the diagram.

[Diagram](assets/equalizer_universal_property.svg)

In the diagram, the dashed arrow `k` is the unique factorization, and the dotted
arrows `b` and `q` are the components at `one`, which are determined by the
other arrows.

The universal property of the limit cone says that for every cone `(a, b)` with
summit `C` there is a unique morphism `k : C ⟶ E` through which both legs
factor, that is, `k ≫ h = a` and `k ≫ q = b`. The second equation follows from
the first: `k ≫ q = k ≫ h ≫ f = a ≫ f = b`. So, as Riehl states it, the
universal property asserts that every `a : C ⟶ A` with `a ≫ f = a ≫ g` factors
uniquely through `h`.

`Fork.IsLimit.mk` asks for exactly this reduced form: a function `lift`
producing `k` from each fork `s`, a proof of the factorization
`lift s ≫ t.ι = s.ι` at `zero` only, and a proof of uniqueness.

Given `[HasEqualizer f g]`, Mathlib's chosen equalizer has summit
`equalizer f g` and leg `equalizer.ι f g : equalizer f g ⟶ A`. For `a : C ⟶ A`
and `w : a ≫ f = a ≫ g`, the factorization `k` is `equalizer.lift a w`.
-/
#check @Fork.IsLimit.mk
#check @equalizer.ι
#check @equalizer.lift

/-
Exercise 1. Riehl's main claim: a cone over `parallelPair f g` with summit `c`
is the same as a morphism `a : c ⟶ A` with `a ≫ f = a ≫ g`. Prove it as an
equivalence of types.

The first type in the equivalence,
`(Functor.const WalkingParallelPair).obj c ⟶ parallelPair f g`,
is Riehl's `Cone(c, F)` from 3.1.5: the type of natural
transformations `Δc ⇒ parallelPair f g`, as in `coneEquivFamily` for 3.1.9. An
element `π` of it is a plain natural transformation, with only the fields
`π.app` (its components) and `π.naturality` (its naturality squares). It is not
a `Fork`, or even a `Cone`, so `ι`, `condition` and `w` are not available for
it. The equation `π.app zero ≫ f = π.app zero ≫ g` has to be
derived from the naturality squares, and that derivation is Riehl's argument.
* `toFun`: take the leg at `zero`; the condition comes from the naturality
  squares at `left` and at `right` (`π.naturality .left`, after `simp`).
* `invFun`: assemble a natural transformation. You may build it by hand, or
  borrow the one inside `Fork.ofι`.
* `left_inv`: compare components with `ext j`, then `cases j`. At `one`, this
  is Riehl's "`b` is necessarily equal to this common composite".
-/
def coneEquivEqualizing {A B : 𝒞} (f g : A ⟶ B) (c : 𝒞) :
    ((Functor.const WalkingParallelPair).obj c ⟶ parallelPair f g) ≃
      {a : c ⟶ A // a ≫ f = a ≫ g} := by
  constructor
  case toFun =>
    intro π
    constructor
    case val =>
      exact π.app .zero
    case property =>
      calc
        π.app .zero ≫ f = π.app .one := by
          have hl := π.naturality .left
          simp at hl
          exact hl.symm
        _ =  π.app .zero ≫ g := by
          have hr := π.naturality .right
          simp at hr
          exact hr
  case invFun =>
    intro x
    -- x.1 is the "a" morphism c ⟶ A.
    -- x.2 is the proof that a ≫ f = a ≫ g.
    -- Fork.ofι makes a cone over the parallel pair diagram
    -- (parallelPair f g).
    -- The legs of this cone compose the natural transformation
    -- we want here.
    exact (Fork.ofι x.1 x.2).π
  case left_inv =>
    intro nat_trans
    simp
    ext j
    cases j
    case zero =>
      rfl
    case one =>
      simp
      have hl := nat_trans.naturality .left
      simp at hl
      simp [hl]
  case right_inv =>
    intro x
    rfl

/-
Warm-ups before Exercises 2–4. Each group below practices one piece of API on
its own, so that the later exercises only have to combine pieces you have
already used. All of them are short; most are one line.

(W1) Reading off a fork. For `a : c ⟶ A` and `w : a ≫ f = a ≫ g`, the fork
`Fork.ofι a w` has summit `c` and leg `a`, and both facts hold by definition.
For an arbitrary fork `t`, the equalizing equation is the field `t.condition`.
The last warm-up in this group shows that the equation survives precomposition:
anything that factors through the leg of a fork also equalizes `f` and `g`. You
will need `Category.assoc` to move the parentheses.
-/
example {A B : 𝒞} {f g : A ⟶ B} {c : 𝒞} (a : c ⟶ A) (w : a ≫ f = a ≫ g) :
    (Fork.ofι a w).pt = c := by
  rfl

example {A B : 𝒞} {f g : A ⟶ B} {c : 𝒞} (a : c ⟶ A) (w : a ≫ f = a ≫ g) :
    (Fork.ofι a w).ι = a := by
  rfl

example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) : t.ι ≫ f = t.ι ≫ g := by
    exact t.condition

example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) {c : 𝒞} (k : c ⟶ t.pt) :
    (k ≫ t.ι) ≫ f = (k ≫ t.ι) ≫ g := by
   repeat rw [Category.assoc]
   rw [t.condition]



/-
(W2) `Fork.IsLimit.mk` on the smallest example. Every morphism equalizes `f`
with itself, so the identity `𝟙 A` is a fork over the pair `f, f`, and it is in
fact an equalizer: a fork `s` over `f, f` factors through `𝟙 A` by its own leg
`s.ι`, and in no other way. Prove this with `Fork.IsLimit.mk`. Start with
`apply Fork.IsLimit.mk` (or `refine Fork.IsLimit.mk _ ?lift ?fac ?uniq`) and
look at the three goals; the categorical simp lemmas `Category.comp_id` and
`Category.id_comp` do the rest. No elements and no subtypes appear here, only
the shape of the universal property.
-/
example {A B : 𝒞} (f : A ⟶ B) :
    IsLimit (Fork.ofι (f := f) (g := f) (𝟙 A) rfl) := by
  apply Fork.IsLimit.mk
  case lift =>
    intro fork
    simp
    exact fork.ι
  case fac =>
    simp
  case uniq =>
    simp

/-
(W3) Morphisms in `Type w` against their elements. Recall that `↾φ` wraps a
function `φ : X → Y` as a morphism `X ⟶ Y`, and that a morphism `h : X ⟶ Y` can
be applied to `x : X` as `h x`. The first two warm-ups below hold by definition.
The next two move between an equation of morphisms and an equation of their
values: `ConcreteCategory.congr_hom h s` turns `h : φ = ψ` into `φ s = ψ s`, and
`ext s` turns the goal `φ = ψ` into `φ s = ψ s` for an arbitrary `s`.
-/
example {X Y : Type w} (φ : X → Y) (x : X) : (↾φ : X ⟶ Y) x = φ x := by
  -- simp closes here
  rw [ConcreteCategory.hom_ofHom]
  rfl

example {X Y Z : Type w} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : X) :
    (φ ≫ ψ) x = ψ (φ x) := by
  apply ConcreteCategory.comp_apply

example {S T : Type w} {φ ψ : S ⟶ T} (h : φ = ψ) (s : S) : φ s = ψ s := by
  apply ConcreteCategory.congr_hom
  exact h

example {S T : Type w} {φ ψ : S ⟶ T} (h : ∀ s, φ s = ψ s) : φ = ψ := by
  ext s
  simp
  apply h

/-
(W4) Forks in `Type w`, elementwise. The first warm-up combines (W1) and (W3):
the equation `t.condition` of morphisms gives, at each element `x` of the
summit, an equation of values. The second uses that to send each element of the
summit into the subtype `{x // f x = g x}`. The third is about maps into the
subtype: two of them are equal as soon as they agree after `Subtype.val`. Here
`ext c` does more than in (W3): for maps into a subtype it also applies
`Subtype.ext`, so the goal it leaves is an equation of underlying values.
-/
example {X Y : Type w} {f g : X → Y} (t : Fork (↾f) (↾g)) (x : t.pt) :
    f (t.ι x) = g (t.ι x) := by
  change (t.ι ≫ ↾f) x = (t.ι ≫ ↾g) x
  rw [t.condition]


example {X Y : Type w} {f g : X → Y} (t : Fork (↾f) (↾g)) :
    t.pt ⟶ {x // f x = g x} := by
  apply TypeCat.ofHom
  intro pt
  refine ⟨t.ι pt, ?_⟩
  change (t.ι ≫ ↾f) pt = (t.ι ≫ ↾g) pt
  rw [t.condition]

example {X Y : Type w} {f g : X → Y} {T : Type w} (k l : T ⟶ {x // f x = g x})
    (h : k ≫ ↾Subtype.val = l ≫ ↾Subtype.val) : k = l := by
  ext c
  exact ConcreteCategory.congr_hom h c

/-
Exercise 2. Equalizers in `Type w`: the equalizer of `f g : X → Y` is the
subtype `{x // f x = g x}`, with leg the inclusion `Subtype.val`.

You will need to apply an equation of morphisms to an element: from
`h : φ = ψ` with `φ ψ : S ⟶ T` in `Type w`, `ConcreteCategory.congr_hom h s`
gives `φ s = ψ s`. For uniqueness, `ext c` reduces an equality of maps into
the subtype to an equality of underlying values, as in (W4).
-/
example {X Y : Type w} (f g : X → Y) :
    IsLimit
      (Fork.ofι
        (f := ↾f)
        (g := ↾g)
        (P := {x // f x = g x})
        (↾Subtype.val) -- This is ι
        (by ext x; exact x.2)) := by
  constructor
  case lift =>
    intro cone
    change Fork (↾f) (↾g) at cone
    change cone.pt ⟶ { x // f x = g x }
    apply TypeCat.ofHom
    intro cpt
    refine ⟨cone.ι cpt, ?_⟩
    exact ConcreteCategory.congr_hom cone.condition cpt
  case fac =>
    intro cone j
    dsimp only [id_eq]
    cases j
    · ext cpt
      rfl
    · rw [← cone.w .left]
      rfl
  case uniq =>
    intro cone m h
    rw [id_eq, id_eq]
    ext cpt
    simp
    have h2 := h .zero
    simp at h2
    conv => rhs; lhs; congr; arg 1; rw [← h2]
    rfl





/-
Exercise 3 (Riehl's Exercise 3.1.iv). The leg of any equalizer is a
monomorphism: if `k ≫ t.ι = l ≫ t.ι` then `k = l`. Use only the universal
property; no elements here. (`Mono` is a one-field structure; look at what its
field asks for.)
-/
example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) (ht : IsLimit t) : Mono t.ι := by
  constructor
  intro c m1 m2 h
  apply ht.hom_ext
  intro j
  cases j
  case zero =>
    simp
    exact h
  case one =>
    simp
    rw [←Category.assoc, h, Category.assoc]

-- here's another way to do it
example {A B : 𝒞} {f g : A ⟶ B} (t : Fork f g) (ht : IsLimit t) : Mono t.ι := by
  exact Fork.IsLimit.mono ht

/-
Exercise 4 (Example 3.1.14). In the category of groups, the equalizer of
`φ ψ : G →* H` is the subgroup `{x | φ x = ψ x}`, Mathlib's `φ.eqLocus ψ`, with
leg its inclusion. With `ψ := 1` this is the kernel of `φ`.

This is Exercise 2 again, plus proving that your `lift` is a group
homomorphism. Morphisms in `GrpCat` are wrapped monoid homs: `GrpCat.ofHom`
wraps, and `GrpCat.of G` is `G` as an object. Build the lift's underlying
monoid hom as a structure with fields `toFun`, `map_one'`, `map_mul'`.
-/
example {G H : Type u₁} [Group G] [Group H] (φ ψ : G →* H) :
    IsLimit (Fork.ofι (f := GrpCat.ofHom φ) (g := GrpCat.ofHom ψ)
      (P := GrpCat.of (φ.eqLocus ψ)) (GrpCat.ofHom (φ.eqLocus ψ).subtype)
      (by ext x; exact x.2)) := by
  -- A fork `s` over `φ, ψ` has a leg `s.ι` whose values all lie in the
  -- equalizing subgroup, as in (W4).
  have mem : ∀ (s : Fork (GrpCat.ofHom φ) (GrpCat.ofHom ψ)) (c : s.pt),
      φ (s.ι c) = ψ (s.ι c) := fun s c =>
    ConcreteCategory.congr_hom s.condition c
  apply Fork.IsLimit.mk
  case lift =>
    intro s
    apply GrpCat.ofHom
    exact
      { toFun := fun c => ⟨s.ι c, mem s c⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp }
  case fac =>
    intro s
    ext c
    rfl
  case uniq =>
    intro s m h
    ext c
    -- `ext` stops at elements of the subgroup; `Subtype.ext` reduces to the
    -- underlying elements of `G`, where `h` applies.
    exact Subtype.ext (ConcreteCategory.congr_hom h c)


-- Definition 3.1.15: Pullbacks
/-
A pullback is a limit of a cospan, which is a diagram indexed by the poset
category `• → • ← •`, consisting of two non-identity morphisms with a common
codomain.

In Mathlib:
* The indexing category is `WalkingCospan`, with objects `left`, `one` and
  `right`, and non-identity morphisms `WalkingCospan.Hom.inl : left ⟶ one` and
  `WalkingCospan.Hom.inr : right ⟶ one`.
* A diagram of that shape is `cospan f g : WalkingCospan ⥤ 𝒞`, for
  `f : B ⟶ A` and `g : C ⟶ A`. It sends `left ↦ B`, `one ↦ A`, `right ↦ C`,
  `inl ↦ f` and `inr ↦ g`.
* A `PullbackCone f g` is by definition a `Cone (cospan f g)`.

In the diagram below, the top row is the indexing category `WalkingCospan` with
its identity morphisms omitted, and the bottom row is its image under the
functor `cospan f g`. The dotted arrows record what the functor does on objects,
and on morphisms it sends `inl` to `f` and `inr` to `g`. All five equations
hold by `rfl`.

[Diagram](assets/cospan.svg)

Two things about `WalkingCospan` differ from `WalkingParallelPair`, and both show
up in goals. First, Mathlib does not define `WalkingCospan` as its own inductive
type. It is a special case of the indexing category for "wide" pullbacks, which
has one object for each element of `Option J` (here `J := WalkingPair`):
`one` is `none`, `left` is `some WalkingPair.left`, and `right` is
`some WalkingPair.right`. The names `WalkingCospan.left` and so on are
abbreviations for these, so a `cases` on an object of `WalkingCospan` produces
goals that mention `none` and `some WalkingPair.left` instead. They are equal to
the short names by definition, so `change` can restore the short names.

Second, the morphisms `inl` and `inr` have to be written out in full as
`WalkingCospan.Hom.inl` and `WalkingCospan.Hom.inr`. The shorthand `.inl`, which
worked for `.left` in the fork section, fails here. Lean resolves `.inl` by
unfolding the expected type `left ⟶ one` and looking for `inl` in the namespace
of the type it finds. For `WalkingParallelPair` that type is
`WalkingParallelPairHom`, which really has a constructor `left`. For
`WalkingCospan` it is `WidePullbackShape.Hom`, whose constructor is called
`term`, and `WalkingCospan.Hom.inl` is only an abbreviation for `term .left`
that lives in a different namespace.

A cone over this diagram with summit `D` consists of a triple of morphisms
`b : D ⟶ B`, `a : D ⟶ A` and `c : D ⟶ C`, one for each object of the indexing
category, such that `b ≫ f = a` and `c ≫ g = a`. These two equations are the
naturality conditions for the two non-identity morphisms `inl` and `inr`. For
instance, naturality at `inl` says `𝟙 D ≫ a = b ≫ f`, since the constant
functor sends `inl` to `𝟙 D` and `cospan f g` sends it to `f`. As Riehl puts
it, the leg `a` asserts that `b ≫ f` and `c ≫ g` have a common composite. Thus
the data of a cone over `f, g` may be described more concisely as a pair of
morphisms `b : D ⟶ B` and `c : D ⟶ C` such that `b ≫ f = c ≫ g`, that is, a
commutative square. (Riehl writes this equation as `f b = g c`.)

Mathlib's pullback cone API is built around that description. For a pullback
cone `t`, the leg `t.fst` is the component at `left` (Riehl's `b`), the leg
`t.snd` is the component at `right` (Riehl's `c`), and `t.condition` is the
equation `t.fst ≫ f = t.snd ≫ g`. The component at `one` (Riehl's `a`) is still
part of the data, but it equals `t.fst ≫ f`. This is the naturality square at
`inl` again, in the form `t.w WalkingCospan.Hom.inl : t.π.app .left ≫ f =
t.π.app .one`. Conversely, `PullbackCone.mk b c w` builds a pullback cone from
morphisms `b` and `c` and a proof `w : b ≫ f = c ≫ g`, supplying `b ≫ f` as the
component at `one`.

The diagram below labels the parts of an arbitrary pullback cone `t` by their
Lean names, laid out as Mathlib draws pullback squares. The component at `one`
is dotted because it is determined by the other arrows: it equals `t.fst ≫ f`,
and also `t.snd ≫ g`.

[Diagram](assets/pullback_cone_fields.svg)

The diagrams in this file follow Mathlib's convention for pullback squares, used
for instance in the docstring of `IsPullback`: `fst` runs horizontally along the
top, `snd` runs vertically down the left side, `f` runs down the right side, and
`g` runs along the bottom. Riehl's square (3.1.16) is the transpose of this one,
with the leg into `B` drawn vertically and the leg into `C` horizontally.
-/
example {A B C : 𝒞} (f : B ⟶ A) (g : C ⟶ A) :
    PullbackCone f g = Cone (cospan f g) := rfl

example {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) :
    t.fst = t.π.app .left := rfl

example {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) :
    t.snd = t.π.app .right := rfl

/-
The pullback is a limit cone over `f, g`. Call its summit `P` and its legs
`h : P ⟶ B` and `k : P ⟶ C`, so that `h ≫ f = k ≫ g`. The universal property of
the limit cone says that for every commutative square `b ≫ f = c ≫ g` with
summit `D`, there is a unique morphism `l : D ⟶ P` through which both legs
factor, that is, `l ≫ h = b` and `l ≫ k = c`. (The leg at `one` factors as well,
but that follows from the factorization of `b`, as it did for forks.)

The diagram below shows this with Lean's names, for a limit cone `t` with summit
`P` and an arbitrary pullback cone `s`. The dashed arrow is the unique
factorization, which `PullbackCone.IsLimit.mk` calls `lift s`. The symbol `⌟` in
the corner marks the square as a pullback, that is, a limit cone, and not
merely a commutative square.

[Diagram](assets/pullback_universal_property.svg)

`PullbackCone.IsLimit.mk` asks for exactly this reduced form, for a cone of the
form `PullbackCone.mk h k w`: a function `lift` producing `l` from each pullback
cone `s`, a proof `fac_left` of `lift s ≫ h = s.fst`, a proof `fac_right` of
`lift s ≫ k = s.snd`, and a proof `uniq` that any `m` satisfying both
factorizations equals `lift s`. Compared with `Fork.IsLimit.mk` there are two
factorization goals instead of one, because a pullback cone has two independent
legs.

Given `[HasPullback f g]`, Mathlib's chosen pullback has summit `pullback f g`
(Riehl's fiber product `B ×_A C`) and legs `pullback.fst f g : pullback f g ⟶ B`
and `pullback.snd f g : pullback f g ⟶ C`. For `b : D ⟶ B`, `c : D ⟶ C` and
`w : b ≫ f = c ≫ g`, the factorization `l` is `pullback.lift b c w`.

Riehl's symbol `⌟` also has a Mathlib counterpart. `IsPullback h k f g` is the
proposition that the square `h ≫ f = k ≫ g` commutes and that the pullback cone
it defines is a limit. Unlike `IsLimit`, which is data (it contains the `lift`
function), `IsPullback` is a `Prop`, so it says only that the square is a
pullback. `IsPullback.of_isLimit` produces it from an `IsLimit`.
-/
#check @PullbackCone.IsLimit.mk
#check @pullback.fst
#check @pullback.lift
#check @IsPullback.of_isLimit
#check @PullbackCone.mk

/-
(P1) Reading off a cospan and a pullback cone. The first two warm-ups below are
the equations of the cospan diagram, and the next three are the parts of
`PullbackCone.mk b c w`; all five hold by definition. The sixth is the leg at
`one` of an arbitrary pullback cone. The last shows that the square survives
precomposition, as in (W1): anything that maps into the summit of a pullback
cone gives another commutative square.
-/
example {A B C : 𝒞} (f : B ⟶ A) (g : C ⟶ A) : (cospan f g).obj .one = A := by
  rfl

example {A B C : 𝒞} (f : B ⟶ A) (g : C ⟶ A) :
    (cospan f g).map WalkingCospan.Hom.inr = g := by
  rfl

example {A B C D : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) : (PullbackCone.mk b c w).pt = D := by
  rfl

example {A B C D : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) : (PullbackCone.mk b c w).snd = c := by
  rfl

example {A B C D : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) : (PullbackCone.mk b c w).π.app .one = b ≫ f := by
  #check (PullbackCone.mk b c w).π.app
  rfl

example {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) :
    t.π.app .one = t.fst ≫ f := by
  simp

example {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) {D : 𝒞}
    (l : D ⟶ t.pt) : (l ≫ t.fst) ≫ f = (l ≫ t.snd) ≫ g := by
  simp
  rw [t.condition]

/-
Exercise 1. Riehl's main claim: a cone over `cospan f g` with summit `D` is the
same as a commutative square `b ≫ f = c ≫ g` with summit `D`. As in Exercise 1
for equalizers, `π` below is a plain natural transformation, so `t.fst`,
`t.condition` and `t.w` are not available for it, and its equations have to be
derived from the naturality squares `π.naturality WalkingCospan.Hom.inl` and
`π.naturality WalkingCospan.Hom.inr` (after `simp`, as before).

The two lemmas are the two halves of Riehl's argument: the legs at `left` and
`right` form a commutative square, and the leg at `one` is forced to equal the
common composite. They are named theorems, not examples, so that the capstone
below can use them.
-/
theorem cospanCone_square {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} {D : 𝒞}
    (π : (Functor.const WalkingCospan).obj D ⟶ cospan f g) :
    π.app .left ≫ f = π.app .right ≫ g := by
  have hl :=  π.naturality WalkingCospan.Hom.inl
  simp at hl
  have hr := π.naturality WalkingCospan.Hom.inr
  simp at hr
  rw [←hl, hr]

theorem cospanCone_one {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} {D : 𝒞}
    (π : (Functor.const WalkingCospan).obj D ⟶ cospan f g) :
    π.app .one = π.app .left ≫ f := by
  let blort :=  π.naturality WalkingCospan.Hom.inl
  simp at blort
  exact blort

/-
Optional capstone: the same claim packaged as an equivalence of types, in the
shape of `coneEquivEqualizing`. Here the commutative square is a subtype of
pairs.

This def asserts an iso (bijection) between:
- the set of natural transformations between
  a) the constant functor typed `WalkingCospan ⥤ 𝒞` on `D`
  and
  b) the functor `cospan f g : WalkingCospan ⥤ 𝒞`,
on the one hand, and
- the set of morphism pairs `p` pairing morphisms
  `D` to `B` (`p.1`) and from `D` to `C` (`p.2`)
  such that the square
  D --p.1--> B
  |          |
  p.2        f
  v          v
  C ---g---> A
  commutes,
on the other hand.

We are evidently allowed to use the Pullback api.

For `invFun`, borrow the natural transformation inside
`PullbackCone.mk`. For `left_inv`, compare components with `ext j`. The goal
then shows `toFun` and `invFun` as unapplied `fun` expressions, and
`dsimp only` evaluates them, leaving
`(PullbackCone.mk (π.app .left) (π.app .right) _).π.app j = π.app j`. Then
split with `rcases j with _ | _ | _`. As explained above, the three goals will
mention `none`, `some WalkingPair.left` and `some WalkingPair.right` instead of
`.one`, `.left` and `.right`. The last two hold by `rfl`. The `none` goal is
`cospanCone_one` read backwards: `exact` accepts it, because `exact` compares
up to definitional equality and `none` is `.one` by definition.
-/
def coneEquivSquare {A B C : 𝒞} (f : B ⟶ A) (g : C ⟶ A) (D : 𝒞) :
    ((Functor.const WalkingCospan).obj D ⟶ cospan f g) ≃
      {p : (D ⟶ B) × (D ⟶ C) // p.1 ≫ f = p.2 ≫ g} := by
  let pb_cone (p: {p : (D ⟶ B) × (D ⟶ C) // p.1 ≫ f = p.2 ≫ g}) : PullbackCone f g :=
      PullbackCone.mk p.val.1 p.val.2
  constructor
  case toFun =>
    exact fun μ => ⟨(μ.app .left, μ.app .right), cospanCone_square μ⟩
  case invFun =>
    exact fun p => (pb_cone p).π
  case left_inv =>
    dsimp only [autoParam]
    intro μ
    conv =>
      lhs
      beta_reduce
    ext j
    dsimp only [pb_cone]
    -- using match .one => ?one because rcases intializes it to "none",
    -- which is confusing
    match j with
    | .one => ?one
    | .left => ?left
    | .right => ? right
    case one =>
      simp
      let blort := (μ.naturality WalkingCospan.Hom.inl).symm
      simp at blort
      exact blort
    case left =>
      simp
    case right =>
      simp
  case right_inv =>
    dsimp only [autoParam]
    intro p
    beta_reduce
    rfl

/-
(P2) `PullbackCone.IsLimit.mk` on the smallest example. Given a cospan
`f : B ⟶ A` and `g : C ⟶ A` with a pullback `P`, the leg `P ⟶ C` is called the
pullback of `f` along `g`. It is the leg opposite `f` in the square, and it
transports `f` from the codomain `A` to the new codomain `C`. (Exercise 4 below
uses this phrase in the same sense.)

Here `g` is the identity `𝟙 A`. Pulling `f` back along an identity changes
nothing, in the sense that the pullback is `B` itself and the pullback of `f`
is `f` itself. Explicitly, the square with summit `B` and legs `𝟙 B : B ⟶ B`
and `f : B ⟶ A`, over the cospan `f, 𝟙 A`, is a pullback:

  B --𝟙 B--> B
  |          |
  f          f
  v          v
  A --𝟙 A--> A

A cone `s` over `f, 𝟙 A` factors through this square by its own leg
`s.fst : s.pt ⟶ B`, and in no other way. Prove this with `PullbackCone.IsLimit.mk`,
and look at each of the four goals before closing it. One of them needs `s.condition`;
`simp` will not find it on its own, but `simpa using s.condition` will. No elements
appear here, only the shape of the universal property.
-/
example {A B : 𝒞} (f : B ⟶ A) :
    IsLimit (PullbackCone.mk (f := f) (g := 𝟙 A) (𝟙 B) f (by simp)) := by
  apply PullbackCone.IsLimit.mk
  case lift =>
    intro cone
    exact cone.fst
  case fac_left =>
    intro cone
    simp
  case fac_right =>
    intro cone
    exact cone.condition.trans (Category.comp_id cone.snd)
  case uniq =>
    intro cone m h1 h2
    cat_disch -- it's obvious

/-
Exercise 2. Pullbacks in `Type w`: the pullback of `f : B → A` and `g : C → A`
is the subtype `{p : B × C // f p.1 = g p.2}` of pairs on which the two maps
agree, with legs the two projections. (Mathlib calls this type
`Types.PullbackObj`.) This is Exercise 2 for equalizers again, with a pair in
place of a single element.

For `lift`, send `x : s.pt` to the pair `(s.fst x, s.snd x)` together with a
proof that it lies in the subtype, obtained from `s.condition` as in (W4). For
uniqueness, `ext x` does even more than before: it applies `Subtype.ext` and
then `Prod.ext`, so it leaves two goals, one for each component of the pair.
These goals display with some noise (`.toFun` applied to `x`), and `simp`
cleans them up to `(↑(m x)).1 = s.fst x` (with `ConcreteCategory.hom` around
`m` and `s.fst`). That is exactly what `ConcreteCategory.congr_hom h x` says for
the hypothesis `h : m ≫ fst = s.fst`. The `simp` is only for reading: `exact`
accepts `congr_hom h x` without it.
-/
example {A B C : Type w} (f : B → A) (g : C → A) :
    IsLimit
      (PullbackCone.mk
        (f := ↾f)
        (g := ↾g)
        (W := {p : B × C // f p.1 = g p.2})
        (↾(fun p => p.val.1)) -- This is fst
        (↾(fun p => p.val.2)) -- This is snd
        (by ext p; exact p.2)) := by
  apply PullbackCone.IsLimit.mk
  case lift =>
    intro (cone : PullbackCone _ _); apply TypeCat.ofHom; intro pt
    let val : B × C := (cone.fst pt, cone.snd pt)
    refine ⟨val, ?_⟩
    unfold val; simp
    change (cone.fst ≫ ↾f) pt = (cone.snd ≫ ↾g) pt
    apply ConcreteCategory.congr_hom
    exact cone.condition
  case fac_left =>
    aesop_cat
  case fac_right =>
    aesop_cat
  case uniq =>
    intro cone m h1 h2
    ext ptx; simp
    case fst =>
      rw [←h1]
      rfl
    case snd =>
      simp
      rw [← h2]
      rfl

/-
Exercise 3 (the fiber, (3.1.17)). In a category with a terminal object `*`, a
morphism `a : * ⟶ A` is called a *point* of `A`, and the summit of a pullback of
`f : B ⟶ A` along a point `a` is called the *fiber* of `f` over `a`. In `Type w`
the terminal object is `PUnit` (shown after Definition 3.1.11), and a point
`* ⟶ A` is the *constant function* at an element `a : A`. The fiber should then
be the set of elements of `B` that `f` sends to `a`, that is, the subtype
`{b // f b = a}`. This is the situation of Riehl's Example 3.1.18, where the
fiber of `ρ : ℝ → S¹` over `1` is `ℤ`.

The example asserts exactly this. The cospan consists of `f : B → A` and the
constant function `fun _ => a : PUnit → A`. The cone over it has summit
`{b // f b = a}`, leg `Subtype.val` into `B`, and the unique map into `PUnit`.
It commutes because every element `b` of the subtype satisfies `f b = a`, which
is the proof `b.2` passed to `PullbackCone.mk`. The claim is that this cone is a
limit. Unfolded, the claim says that for every type `X`, every function
`k : X → B` with `f (k x) = a` for all `x`, and the unique map `X → PUnit`,
there is exactly one function `X → {b // f b = a}` whose composite with
`Subtype.val` is `k`. (Its composite with the map into `PUnit` agrees
automatically, since there is only one map into `PUnit`.) In other words, a
function into `B` that lands in the fiber factors uniquely through the fiber.

The diagram below shows the square, laid out as Mathlib draws pullback squares,
with each arrow labeled by the Lean function that the example passes to
`PullbackCone.mk`.

[Diagram](assets/fiber_pullback.svg)

The proof follows Exercise 2, but now one of the factorizations is a map into
`PUnit`, and `ext x` in the uniqueness goal leaves a single goal again. As in
Exercise 2, `simp` makes that goal readable, and it needs only the
factorization through the inclusion.
-/
example {A B : Type w} (f : B → A) (a : A) :
    IsLimit
      (PullbackCone.mk
        (f := ↾f)
        (g := ↾(fun _ : PUnit.{w + 1} => a))
        (W := {b : B // f b = a})
        (↾Subtype.val)           -- fst
        (↾(fun _ => PUnit.unit)) -- snd
        (by ext b; exact b.2))   -- eq
        := by
  apply PullbackCone.IsLimit.mk
  case lift =>
    intro cone
    apply TypeCat.ofHom
    intro ptx
    refine ⟨cone.fst ptx, ?_⟩
    change (cone.fst ≫ ↾f) ptx = a
    rw [cone.condition]
    rfl
  case fac_left =>
    intro cone; rfl
  case fac_right =>
    intro cone; rfl
  case uniq =>
    intro cone m h1 h2
    ext ptx; simp
    rw [←h1]
    rfl


/-
Worked example (Example 3.1.18, solved). Riehl's example in the category of
spaces: the fiber of `ρ : ℝ → S¹`, `t ↦ e^{2πit}`, over the point `1` is the
discrete subspace `ℤ ⊂ ℝ`. This is Exercise 3 again, now in `TopCat`, where
the objects are topological spaces and the morphisms are continuous maps.

What the statement means, informally. Picture `ρ` as wrapping the real line
around a circle of circumference `1`, like thread around a spool: `t` and
`t + 1` land on the same point, and `t` is sent to the point a fraction `t` of
the way around (the "angle measured in turns"). The fiber over the starting
point consists of the reals that land there, which are exactly the integers.
As a set, this is just Exercise 3. The new content is that the fiber, as a
space, is `ℤ` with the discrete topology: each integer is isolated from the
others, with no other points of the fiber nearby, exactly as `ℤ` sits inside
`ℝ`.

The universal property makes this precise without any topology vocabulary. A
cone over the cospan amounts to a space `X` and a continuous map
`k : X → ℝ` whose values all land on the starting point, that is, a continuous
map into `ℝ` taking only integer values. The theorem says that such a map is
the same thing as a continuous map `X → ℤ`. The content is that the
continuity is not lost: a continuous real-valued function that only takes
integer values cannot jump from one integer to another, so it is locally
constant, and a locally constant function into `ℤ` is continuous for the
discrete topology. For instance, if `X` is an interval, `k` must be constant.
The discrete topology is also the only one the fiber could carry. For the
inclusion of the fiber into `ℝ` to be continuous, the preimage of the open
interval `(n - 1/2, n + 1/2)` must be open, and that preimage is the single
point `{n}`. So every point of the fiber is open, which is what discrete means.

Mathlib's `AddCircle (1 : ℝ)` is the quotient `ℝ/ℤ`, and the quotient map
`t ↦ (t : AddCircle 1)` is Riehl's `ρ` up to the homeomorphism `ℝ/ℤ ≅ S¹`,
`[t] ↦ e^{2πit}`, which sends the class `0` to the point `1`. With that
translation, the square to prove a pullback in `TopCat` is

  ℤ ──Int.cast──> ℝ
  │               │
  !               ρ
  ↓               ↓
  * ──── 0 ────> ℝ/ℤ

where `!` is the unique map to the one-point space `PUnit`.

The proof follows Exercise 3. Two facts carry the weight.

* `circleFiber_spec`: for a cone `s`, every point `x` of its summit is sent by
  `s.fst` to an integer. The commutativity of `s`, evaluated at `x`, says that
  `ρ (s.fst x) = 0` in `ℝ/ℤ`, and `AddCircle.coe_eq_zero_iff` translates this
  into `∃ n : ℤ, n • 1 = s.fst x`. The lift sends `x` to that integer, chosen
  with `Exists.choose` (so the definition is `noncomputable`; the integer is
  in fact unique, but nothing here needs that).
* Continuity of the lift. This is the only genuinely topological step, and it
  is what "`ℤ` is a subspace of `ℝ`" means: `Int.cast : ℤ → ℝ` is an embedding
  (`Int.isClosedEmbedding_coe_real`), and a map into the domain of an embedding
  is continuous if and only if its composite with the embedding is
  (`IsEmbedding.continuous_iff`). The composite here is `s.fst`, which is
  continuous because `s` is a cone in `TopCat`.

The two factorizations and uniqueness are then as in Exercise 3. The
factorization through `PUnit` holds by `ext` alone, since any two maps into a
one-point space agree. Uniqueness uses injectivity of `Int.cast` to reduce an
equation of integers to an equation of reals, which the factorization
hypothesis for `m` supplies.
-/
section CircleFiber

/-- Riehl's `ρ`, with the circle modeled as `ℝ/ℤ`. -/
def circleρ : TopCat.of ℝ ⟶ TopCat.of (AddCircle (1 : ℝ)) :=
  TopCat.ofHom ⟨fun t => (t : AddCircle (1 : ℝ)), continuous_quotient_mk'⟩

/-- The point `1 ∈ S¹`, which is the class `0` in `ℝ/ℤ`. -/
def circleBase : TopCat.of PUnit.{1} ⟶ TopCat.of (AddCircle (1 : ℝ)) :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

/-- The inclusion `ℤ ⊂ ℝ`. It is continuous because `ℤ` is discrete. -/
def intToReal : TopCat.of ℤ ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨Int.cast, continuous_of_discreteTopology⟩

def intToPoint : TopCat.of ℤ ⟶ TopCat.of PUnit.{1} :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The square commutes: every integer maps to `0` in `ℝ/ℤ`. -/
theorem circleFiber_w : intToReal ≫ circleρ = intToPoint ≫ circleBase := by
  ext n
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by rw [zsmul_one]; rfl⟩

/-- The leg of any cone over the cospan takes integer values. -/
theorem circleFiber_spec (s : PullbackCone circleρ circleBase) (x : s.pt) :
    ∃ n : ℤ, (n : ℝ) = s.fst x := by
  have h := ConcreteCategory.congr_hom s.condition x
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  rw [zsmul_one] at hn
  exact ⟨n, hn⟩

noncomputable def circleFiberIsLimit :
    IsLimit (PullbackCone.mk intToReal intToPoint circleFiber_w) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => TopCat.ofHom ⟨fun x => (circleFiber_spec s x).choose, ?_⟩) ?_ ?_ ?_
  -- continuity of the lift: its composite with the embedding `ℤ ⊂ ℝ` is `s.fst`
  · exact (Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff).2
      (s.fst.hom.continuous.congr fun x => (circleFiber_spec s x).choose_spec.symm)
  -- fac_left: the chosen integer is the value of `s.fst`
  · intro s
    ext x
    exact (circleFiber_spec s x).choose_spec
  -- fac_right: maps into `PUnit` agree
  · intro s
    ext x
  -- uniq: compare in `ℝ`, where `m` and the lift both agree with `s.fst`
  · intro s m h₁ _
    ext x
    apply Int.cast_injective (α := ℝ)
    exact (ConcreteCategory.congr_hom h₁ x).trans (circleFiber_spec s x).choose_spec.symm

/-- The same fact in the form preferred by Mathlib. -/
theorem circleFiber_isPullback : IsPullback intToReal intToPoint circleρ circleBase :=
  IsPullback.of_isLimit circleFiberIsLimit

end CircleFiber

/-
Exercise 4 (Riehl's Exercise 3.1.v). The pullback of a monomorphism is a
monomorphism: if `f : B ⟶ A` is a monomorphism and `t` is a pullback of `f`
along `g : C ⟶ A`, then the leg `t.snd : t.pt ⟶ C` is a monomorphism. Use only
the universal property; no elements here.

The diagram below shows the setup. The square is the pullback cone `t`, and the
tailed arrow marks `f` as a monomorphism. The two parallel arrows `k` and `l`
are the test morphisms from the definition of a monomorphism: to show that
`t.snd` is a monomorphism, one shows that any two such morphisms with
`k ≫ t.snd = l ≫ t.snd` are equal.

[Diagram](assets/pullback_of_mono.svg)

The argument: given `k l : D ⟶ t.pt` with `k ≫ t.snd = l ≫ t.snd`, it suffices
by uniqueness of factorizations to show that `k` and `l` also agree after
`t.fst`. For that, cancel `f`. `PullbackCone.IsLimit.hom_ext ht` reduces
`k = l` to the two equations after `t.fst` and after `t.snd`, and
`cancel_mono f` turns an equation `x ≫ f = y ≫ f` into `x = y` (as an `iff`, so
use it with `rw [← cancel_mono f]`). `Category.assoc` and `t.condition` do the
rest.
-/
example {A B C : 𝒞} {f : B ⟶ A} {g : C ⟶ A} [hmf : Mono f] (t : PullbackCone f g)
    (ht : IsLimit t) : Mono t.snd := by
  constructor
  intro D k l hkl_snd
  apply PullbackCone.IsLimit.hom_ext ht (h₁ := hkl_snd)
  rw [← cancel_mono f]
  rw [Category.assoc, Category.assoc, t.condition]
  rw [← Category.assoc, hkl_snd]
  simp


/-
## Pullbacks as a property: `IsPullback`

The exercises above prove universal properties the hard way, by building an
`IsLimit` for a specific cone. Mathlib packages the result of such a proof in
three different ways, according to what one wants to say.

* `IsPullback fst snd f g` is the proposition that the commutative square formed
  by `fst : P ⟶ B`, `snd : P ⟶ C`, `f : B ⟶ A` and `g : C ⟶ A` is a pullback.
  It extends `CommSq fst snd f g`, which records only the equation
  `w : fst ≫ f = snd ≫ g`, by the assertion that the pullback cone built from
  the square is a limit. The proposition itself is a statement about the four
  morphisms, and so are the main lemmas about it (`lift`, `hom_ext`, `flip` and
  the pasting lemmas below): their statements contain no `Cone`, no `π.app` and
  no `WalkingCospan`. The cone has not disappeared, since `IsPullback` is
  defined in terms of it, and `h.cone` and `h.isLimit` recover it together with
  its `IsLimit` when the general theory of limits is needed. But when working
  with a pullback square one rarely has to unfold that far. It is also a `Prop`:
  the `IsLimit` inside it is wrapped in `Nonempty`, so `IsPullback` says only
  that a limit structure exists, and any two proofs of it are equal. This is the
  form in which Mathlib usually states theorems about pullbacks, and it is the
  subject of the exercises below.
* `HasPullback f g` is an abbreviation for `HasLimit (cospan f g)`. It says that
  some limit cone over the cospan exists, and given this instance,
  `pullback f g` with `pullback.fst` and `pullback.snd` is a fixed choice of
  one. This is the form to use in a category that is known to have pullbacks
  when no specific construction is at hand.
* `LimitCone F` bundles a cone over any diagram `F` together with an `IsLimit`
  for it. It is the most literal version of "a cone with a proof that it is a
  limit", but it has no API specific to pullbacks.

A remark on reading `IsPullback`: its arguments are the two legs out of the
summit, `fst` and then `snd`, followed by the two morphisms of the cospan, `f`
and then `g`, where `fst` and `f` share the corner `B`. In Mathlib's pictures,
which the diagrams in this file follow, the four arguments are read off the
square in a fixed order: `fst` along the top, `snd` down the left side, `f` down
the right side and `g` along the bottom. Transposing the square, which is how
Riehl draws it, exchanges the roles of the two legs, and corresponds to
`IsPullback.flip`.
-/
section IsPullbackAPI

/-
Throughout this section, the variables below name the four morphisms of a
square, arranged as in the diagram. Most exercises also take a hypothesis
`h : IsPullback fst snd f g`, which says that this square commutes and is a
pullback. The variables alone say neither.

[Diagram](assets/is_pullback_variables.svg)
-/
variable {P B C A : 𝒞} {fst : P ⟶ B} {snd : P ⟶ C} {f : B ⟶ A} {g : C ⟶ A}

/-
(I1) Translating in and out. The first example passes from a limit pullback
cone, the form in which Exercises 2 to 4 were stated, to `IsPullback`; the
relevant theorem is `IsPullback.of_isLimit`. The second goes back: from
`h : IsPullback fst snd f g` it recovers the `IsLimit` that the proposition
asserts to exist. The field `h.isLimit` does this. Lean will then complain that
the example must be marked `noncomputable`. The reason is that `h` only says
that an `IsLimit` exists, and extracting a specific one from a `Nonempty`
requires the axiom of choice, which has no executable content. The third
example is the commutativity of the square, which `IsPullback` inherits from
`CommSq` as the field `w`.
-/
example {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) (ht : IsLimit t) :
    IsPullback t.fst t.snd f g := by
  apply IsPullback.of_isLimit ht

noncomputable example (h : IsPullback fst snd f g) : IsLimit (PullbackCone.mk fst snd h.w) := by
  exact h.isLimit

example (h : IsPullback fst snd f g) : fst ≫ f = snd ≫ g := by
  exact h.w

/-
(I2) The universal property through `IsPullback`. For a commutative square
`w : b ≫ f = c ≫ g` with summit `D`, the factorization `D ⟶ P` is
`h.lift b c w`, and the lemmas `h.lift_fst : h.lift b c w ≫ fst = b` and
`h.lift_snd` say that it is a factorization. Both are `simp` lemmas, and they
come with `reassoc` variants (`h.lift_fst_assoc`), which rewrite
`h.lift b c w ≫ fst ≫ k` for any further morphism `k`. So `simp` can simplify
the left side of the first example below without help, and what remains is `w`.

The second example is uniqueness. The diagram below shows both examples: the
outer square with summit `D` is the commutative square `w`, the dashed arrow is
`h.lift b c w`, and the solid arrow `m` beside it is the morphism that the
second example proves equal to it.

[Diagram](assets/is_pullback_lift.svg)

Two morphisms into `P` are equal as soon as they agree after `fst` and after
`snd`; this is `h.hom_ext`. Applying it leaves
two goals, and in each the `lift` side is handled by the lemmas above.
-/
example (h : IsPullback fst snd f g) {D : 𝒞} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) : h.lift b c w ≫ fst ≫ f = c ≫ g := by
  simp
  exact w

example (h : IsPullback fst snd f g) {D : 𝒞} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) (m : D ⟶ P) (hb : m ≫ fst = b) (hc : m ≫ snd = c) :
    m = h.lift b c w := by
  apply h.hom_ext
  case h₀ =>
    simp
    exact hb
  case h₁ =>
    simp
    exact hc

/-
(I3) Exercise 4 again, now stated with `IsPullback`. The argument is the same
as before, with `h.hom_ext` in place of `PullbackCone.IsLimit.hom_ext ht` and
`h.w` in place of `t.condition`. It is stated as a theorem so that (I4) can use
it.
-/
theorem mono_snd_of_isPullback (h : IsPullback fst snd f g) [Mono f] : Mono snd := by
  constructor
  intro D k l hkl
  apply h.hom_ext
  case h₀ =>
    rw [← cancel_mono f];
    simp
    rw [h.w, ←Category.assoc, hkl]
    simp
  case h₁ =>
    exact hkl

/-
(I4) Symmetry. The pullback of a monomorphism `g` along `f` is also a
monomorphism, where this time the relevant leg is `fst`. There is no need to
repeat the argument: `h.flip : IsPullback snd fst g f` is the same square with
the roles of the two legs exchanged, and (I3) applies to it. A one-line term
proof is possible.
-/
theorem mono_fst_of_isPullback (h : IsPullback fst snd f g) [Mono g] : Mono fst := by
  exact mono_snd_of_isPullback h.flip

/-
(I5) The pasting lemma. If two pullback squares are stacked so that the bottom
edge of the upper square is the top edge of the lower square, then the outer
rectangle is a pullback. In the diagram below, the upper square is
`IsPullback a p q b`, the lower square is `IsPullback b r s c`, and the outer
rectangle, whose vertical edges are the composites `p ≫ r` and `q ≫ s`, is
`IsPullback a (p ≫ r) (q ≫ s) c`.

[Diagram](assets/pullback_pasting.svg)

Mathlib proves this as `IsPullback.paste_vert`. Prove it without that lemma,
using only `IsPullback.paste_horiz` and `IsPullback.flip`. Here is the statement
of `paste_horiz`, for squares placed side by side:

  X₁₁ - h₁₁ -> X₁₂ - h₁₂ -> X₁₃
   |            |            |
  v₁₁          v₁₂          v₁₃
   ↓            ↓            ↓
  X₂₁ - h₂₁ -> X₂₂ - h₂₂ -> X₂₃

  (s : IsPullback h₁₁ v₁₁ v₁₂ h₂₁) (t : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) :
    IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)

Transposing a vertical stack of squares gives a horizontal row of squares, and
this is the whole idea. The work is in matching the arguments, and `#check` on
the flipped hypotheses shows what they have become.
-/
example {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : 𝒞} {a : X₁₁ ⟶ X₁₂} {b : X₂₁ ⟶ X₂₂} {c : X₃₁ ⟶ X₃₂}
    {p : X₁₁ ⟶ X₂₁} {q : X₁₂ ⟶ X₂₂} {r : X₂₁ ⟶ X₃₁} {s : X₂₂ ⟶ X₃₂}
    (top : IsPullback a p q b) (bot : IsPullback b r s c) :
    IsPullback a (p ≫ r) (q ≫ s) c := by
  exact (IsPullback.paste_horiz (top.flip) (bot.flip)).flip

/-
(I6) Uniqueness up to isomorphism. Any two pullbacks of the same cospan have
isomorphic summits. Given pullback squares `h` with summit `P` and `h'` with
summit `P'` over the same `f` and `g`, each summit carries a commutative square,
so each factors through the other: `hom := h'.lift fst snd h.w` and
`inv := h.lift fst' snd' h'.w`, as in the diagram below.

[Diagram](assets/pullback_uniqueness_iso.svg)

The composite `hom ≫ inv : P ⟶ P` and the identity both factor the square
`fst, snd` through `P`, so they are equal by `h.hom_ext`; the same argument with
`h'` handles `inv ≫ hom`. Construct the isomorphism with `where` syntax, filling
the fields `hom`, `inv`, `hom_inv_id` and `inv_hom_id`. The definition must be
marked `noncomputable`, for the reason given in (I1): `lift` is defined from
`h.isLimit`.

Mathlib's version of this construction is `IsPullback.isoIsPullback`, and the
special case in which `h'` is the chosen pullback of `[HasPullback f g]` is
`IsPullback.isoPullback`. The last example is a fact about the latter that
`simp` knows. Given `[HasPullback f g]`, Mathlib has a chosen pullback square
with summit `pullback f g` and legs `pullback.fst f g` and `pullback.snd f g`,
and `h.isoPullback : P ≅ pullback f g` compares the square `h` with it. The
example says that the comparison respects the legs into `B`: going from `P` to
`pullback f g` by `h.isoPullback.hom` and then on to `B` by `pullback.fst f g`
is the same as going directly by `fst`. That is, the triangle at the top of the
diagram below commutes. (The analogous statement for `snd` is
`h.isoPullback_hom_snd`.)

[Diagram](assets/iso_pullback_fst.svg)
-/
noncomputable def isoOfIsPullback {P' : 𝒞} {fst' : P' ⟶ B} {snd' : P' ⟶ C}
    (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : P ≅ P' := by
  -- eh, this is busywork. We already know limits over the same diagram are iso.
  apply IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

example (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst f g = fst := by
  simp

/-
(I7) Finding the library's version of a fact. Exercise (P2) proved that pulling
back along an identity changes nothing. Mathlib has this fact as a lemma about
`IsPullback`. Find it with `exact?` and replace the `exact?` call with the term
it suggests. (Searching for it with `lean_loogle` or the documentation search
for `IsPullback` and `𝟙` would also work.)
-/
example (f : B ⟶ A) : IsPullback (𝟙 B) f f (𝟙 A) := by
  exact IsPullback.of_id_fst

end IsPullbackAPI

/-
## Example 3.1.19: a pullback of abelian groups

Riehl's example takes place in `Ab`, the category of abelian groups, which
Mathlib calls `AddCommGrpCat`. Very little group theory is needed, because
every group in sight is `ℤ`, and the morphisms `ℤ → ℤ` of abelian groups are
exactly the maps "multiply by a fixed integer". (Riehl derives this from the
fact that `ℤ` represents the forgetful functor `Ab → Set`: a homomorphism out of
`ℤ` is determined by where it sends `1`, and `1` may be sent anywhere. Warm-up
(Z2) below is this fact.) So the morphism `n : ℤ → ℤ` in Riehl's notation is
multiplication by `n`, which this section calls `mulBy n`.

Riehl's claim: for integers `n` and `m`, not both zero, the pullback of the
cospan `n, m` is `ℤ` again, with legs `b` and `a` chosen so that `m a = n b`
is the least common multiple of `n` and `m`. The square (3.1.20), drawn in
Mathlib's layout, which here agrees with Riehl's, is

[Diagram](assets/int_pullback.svg)

Concretely, write `g` for the greatest common divisor of `n` and `m`, and set
`a := n / g` and `b := m / g`, so that `n = a g` and `m = b g`. Then
`n b = a b g = m a`, and this common value is `lcm(n, m)` (up to sign).

Why it is a pullback. A cone with summit `X` consists of two homomorphisms
`x, y : X → ℤ` with `n x = m y`. (Riehl describes the elements of the pullback
as pairs of integers `(x, y)` with `n x = m y`.) Dividing by `g`, which is
allowed because `g ≠ 0`, gives `a x = b y`. The lift must be a homomorphism
`z : X → ℤ` with `b z = x` and `a z = y`, and the trick for writing it down is
Bézout's identity. Since `a` and `b` have no common factor, there are integers
`p` and `q` with `p a + q b = 1`. The lift is `z := p y + q x`. Indeed,

  `b z = p (b y) + q b x = p (a x) + q b x = (p a + q b) x = x`,

and similarly `a z = y`. Uniqueness is the same computation run backwards: if
`b z' = x` and `a z' = y`, then `z' = (p a + q b) z' = p y + q x`.

All of the number theory, finding `g`, `a`, `b`, `p` and `q` from `n` and `m`,
is packaged in `intPullback_data` below, which is provided with its proof. The
exercises are the rest.

A tool for the algebra: `linear_combination`. Every equation in this section
is a polynomial identity that follows from some hypotheses by adding multiples
of them. `linear_combination e₁ * h₁ + e₂ * h₂` proves a goal `lhs = rhs` by
checking, with `ring`, that `lhs - rhs` equals `e₁ * (lhs₁ - rhs₁) + e₂ *
(lhs₂ - rhs₂)`. Finding the coefficients is the same work as writing the
displayed calculation above. If the coefficients are wrong, the error message
shows the polynomial that failed to vanish, which usually points to the fix.

A trap: applying a morphism of `AddCommGrpCat` to an element can be written in
several ways (`f x`, `f.hom x`, `(ConcreteCategory.hom f) x`) that are equal by
definition but displayed differently. `ring` and `linear_combination` treat the
different spellings as different unknowns, and then fail with a residue that
looks as if it should cancel. The cure is to state hypotheses and goals in one
spelling, with type ascriptions on `have` and with `change`. The skeleton of
(Z5) does this.
-/
section IntPullback

/-- Multiplication by `k`, as an endomorphism of `ℤ` in `Ab`. -/
def mulBy (k : ℤ) : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom (AddMonoidHom.mulLeft k)

/-
(Z1) Warm-up: `mulBy k` really is multiplication by `k`. This holds by
definition.
-/
example (k x : ℤ) : mulBy k x = k * x := by
  sorry

/-
(Z2) Warm-up: Riehl's remark that a homomorphism `ℤ → ℤ` is determined by where
it sends `1`. Start with `ext1` and look at the goal: Mathlib's extensionality
lemma for homomorphisms out of `ℤ` already reduces the equation to the value
at `1`.
-/
example (φ ψ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (h : φ 1 = ψ 1) : φ = ψ := by
  sorry

/-
(Z3) Dividing by the gcd. From `n x = m y` with `n = a g`, `m = b g` and
`g ≠ 0`, deduce `a x = b y`. Since `g ≠ 0`, it suffices to prove
`g * (a * x) = g * (b * y)`: `apply mul_left_cancel₀ hg` reduces the goal to
this. Then finish with `linear_combination`, using `h`, `hn` and `hm`. To find
the coefficients, expand `g a x - g b y` and rewrite it in terms of
`n x - m y`, `n - a g` and `m - b g`.
-/
theorem cancel_gcd {n m a b g x y : ℤ} (hn : n = a * g) (hm : m = b * g) (hg : g ≠ 0)
    (h : n * x = m * y) : a * x = b * y := by
  sorry

/-
(Z4) The square (3.1.20) commutes. After `ext`, the goal is the equation at the
element `1` (as in (Z2)); `change n * (b * 1) = m * (a * 1)` restates it
readably. Then rewrite with `hn` and `hm` and finish with `ring`.
-/
theorem mulBy_square {n m a b g : ℤ} (hn : n = a * g) (hm : m = b * g) :
    mulBy b ≫ mulBy n = mulBy a ≫ mulBy m := by
  sorry

/-
(Z5) The main exercise: the square is a pullback. The lift is given, as
`p • s.snd + q • s.fst` built from the underlying additive maps, which is the
homomorphism `z = p y + q x` from the explanation above. The three remaining
goals are the two factorizations and uniqueness. In each, `ext x` reduces to an
equation of integers. The skeleton states the needed hypotheses and the goal in
one uniform spelling, as the trap above requires; what is left is a
`linear_combination` in each case, with coefficients read off from the
displayed calculations.
-/
noncomputable def intPullbackIsLimit {n m a b g p q : ℤ} (hn : n = a * g) (hm : m = b * g)
    (hg : g ≠ 0) (hpq : p * a + q * b = 1) :
    IsLimit (PullbackCone.mk (mulBy b) (mulBy a) (mulBy_square hn hm)) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom (p • s.snd.hom + q • s.fst.hom)) ?_ ?_ ?_
  · -- fac_left: `b z = x`
    intro s
    ext x
    have h : a * s.fst x = b * s.snd x :=
      cancel_gcd hn hm hg (ConcreteCategory.congr_hom s.condition x)
    change b * (p * s.snd x + q * s.fst x) = s.fst x
    sorry
  · -- fac_right: `a z = y`
    intro s
    ext x
    have h : a * s.fst x = b * s.snd x :=
      cancel_gcd hn hm hg (ConcreteCategory.congr_hom s.condition x)
    change a * (p * s.snd x + q * s.fst x) = s.snd x
    sorry
  · -- uniq: any `k` with `b k = x` and `a k = y` is `p y + q x`
    intro s k hb ha
    ext x
    have hb' : b * k x = s.fst x := ConcreteCategory.congr_hom hb x
    have ha' : a * k x = s.snd x := ConcreteCategory.congr_hom ha x
    change k x = p * s.snd x + q * s.fst x
    sorry

/-- The number theory, provided: `g = gcd(n, m)`, `a = n / g`, `b = m / g`, and
Bézout coefficients `p`, `q` for `a`, `b`. Bézout's identity for `n` and `m`,
`gcd(n, m) = n * gcdA + m * gcdB` (`Int.gcd_eq_gcd_ab`), becomes `1 = gcdA * a +
gcdB * b` after dividing by `g`. -/
theorem intPullback_data (n m : ℤ) (h : n ≠ 0 ∨ m ≠ 0) :
    ∃ a b g p q : ℤ, n = a * g ∧ m = b * g ∧ g ≠ 0 ∧ p * a + q * b = 1 := by
  have hg : (Int.gcd n m : ℤ) ≠ 0 := by
    rw [Int.natCast_ne_zero, ne_eq, Int.gcd_eq_zero_iff]
    tauto
  have hn : n = n / Int.gcd n m * Int.gcd n m :=
    (Int.ediv_mul_cancel (Int.gcd_dvd_left n m)).symm
  have hm : m = m / Int.gcd n m * Int.gcd n m :=
    (Int.ediv_mul_cancel (Int.gcd_dvd_right n m)).symm
  refine ⟨n / Int.gcd n m, m / Int.gcd n m, Int.gcd n m, Int.gcdA n m, Int.gcdB n m,
    hn, hm, hg, ?_⟩
  apply mul_left_cancel₀ hg
  linear_combination (Int.gcd_eq_gcd_ab n m).symm - Int.gcdA n m * hn - Int.gcdB n m * hm

/-
(Z6) Example 3.1.19 itself: for `n` and `m` not both zero, the cospan `n, m`
has a pullback with summit `ℤ`. Combine `intPullback_data` (take it apart with
`obtain ⟨a, b, g, p, q, hn, hm, hg, hpq⟩ := ...`), `intPullbackIsLimit`, and
`IsPullback.of_isLimit`.
-/
theorem example_3_1_19 (n m : ℤ) (h : n ≠ 0 ∨ m ≠ 0) :
    ∃ a b : ℤ, IsPullback (mulBy b) (mulBy a) (mulBy n) (mulBy m) := by
  sorry

end IntPullback
