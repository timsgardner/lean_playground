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

open CategoryTheory Limits Opposite
open scoped CategoryKindergarten

-- set_option pp.categoryTheory.hideConcreteHom true
set_option pp.proofs true          -- print proof terms instead of ⋯
set_option pp.deepTerms true       -- don't elide deeply nested subterms

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

noncomputable def homProductEquiv {β : Type*} (f : β → 𝒞) [HasProduct f] (c : 𝒞) :
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
   `𝒞(c, ∏ⱼ F j) ≅ ∏ₖ 𝒞(c, F k) ≅ Cone(c, F)`: `homProductEquiv` sends `g` to
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
    (coneEquivFamily f c).symm (homProductEquiv f c g) =
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
noncomputable example {β : Type w} (X : β → Type w) : ∏ᶜ X ≅ (∀ b : β, X b) := by
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

/-
Exercise 5. Riehl's trick from Example 3.1.10: probe the product with the point.
Maps `PUnit ⟶ Z` in `Type w` are the same as elements of `Z`, so taking
`c := PUnit` in `homProductEquiv` says the elements of `∏ᶜ X` are exactly the
families `(x b)_b` with `x b : X b`. Build this as an equivalence of types.
-/
example {β : Type w} (X : β → Type w) : (∏ᶜ X : Type w) ≃ (∀ b, X b) :=
  sorry
