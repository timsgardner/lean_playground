import LeanPlayground.Scratch.actual_category_scratch.scratch_4.induced_eq
import Mathlib.CategoryTheory.Types.Basic

set_option pp.proofs.withType true
set_option backward.defeqAttrib.useBackward true

show_panel_widgets [local ProofWidgets.SelectionPanel]

/-! # Basic moves in the induced category of a family of equations

The setting throughout: an index type `I`, two functions `a b : I → C`, and a family of
equations `e i : a i = b i`. The category `InducedCategory C a` has the indices as
objects, and a morphism `i ⟶ k` in it is a morphism `a i ⟶ a k` of `C`, wrapped in a
structure with one field, `hom`. The family `e` lets each such morphism be retyped as a
morphism `b i ⟶ b k`, the transported morphism `transportHom e f`.

Each section below shows one move, as a few `example`s. -/

open CategoryTheory InducedEq

variable {I : Type*} {C : Type*} [Category C] {a b : I → C} (e : ∀ i, a i = b i)

/-! ## 1. Morphisms in and out

A morphism `a i ⟶ a k` of `C` becomes a morphism `i ⟶ k` of the induced category with
`InducedCategory.homMk`, and `.hom` gets it back. The two are inverse by definition. -/

example {i k : InducedCategory C a} (f : a i ⟶ a k) : i ⟶ k :=
  InducedCategory.homMk f

example {i k : InducedCategory C a} (f : a i ⟶ a k) :
    (InducedCategory.homMk f : i ⟶ k).hom = f :=
  rfl

/-! ## 2. The transported morphism

For `f : i ⟶ k`, `transportHom e f : b i ⟶ b k`. The equations used, `e i` and `e k`, are read
off from the type of `f`, so they are never written at the point of use. -/

example {i k : InducedCategory C a} (f : i ⟶ k) : b i ⟶ b k :=
  transportHom e f

/-- By definition, the transported morphism is the `hom` sandwiched between the equations. -/
example {i k : InducedCategory C a} (f : i ⟶ k) :
    transportHom e f = eqToHom (e i).symm ≫ f.hom ≫ eqToHom (e k) :=
  rfl

/-! ## 3. Transport respects composition and identities

`transportHom_comp` and `transportHom_id` are `simp` lemmas, so the transport of a
composite of any length is split into the transports of its pieces, and no `eqToHom`
appears. -/

example {i k l m : InducedCategory C a} (f : i ⟶ k) (g : k ⟶ l) (h : l ⟶ m) :
    transportHom e (f ≫ g ≫ h) = transportHom e f ≫ transportHom e g ≫ transportHom e h := by
  simp

example {i k : InducedCategory C a} (f : i ⟶ k) :
    transportHom e (𝟙 i ≫ f ≫ 𝟙 k) = transportHom e f := by
  simp

/-! ## 4. The square

Each morphism `f` has a commuting square: going along `f.hom` and then down by `e k` is
going down by `e i` and then along the transported morphism. -/

example {i k : InducedCategory C a} (f : i ⟶ k) :
    f.hom ≫ eqToHom (e k) = eqToHom (e i) ≫ transportHom e f :=
  square e f

/-! ## 5. Transport as a functor

`transport e : InducedCategory C a ⥤ InducedCategory C b` does not move objects, and
sends each morphism `f` to the morphism whose `hom` is `transportHom e f`. Because it is
a functor, composites and identities are handled by `Functor.map_comp` and
`Functor.map_id`, like for any functor. -/

example (i : InducedCategory C a) : (transport e).obj i = i :=
  rfl

example {i k : InducedCategory C a} (f : i ⟶ k) : ((transport e).map f).hom = transportHom e f :=
  rfl

example {i k l : InducedCategory C a} (f : i ⟶ k) (g : k ⟶ l) :
    (transport e).map (f ≫ g) = (transport e).map f ≫ (transport e).map g :=
  (transport e).map_comp f g

/-! ## 6. Transporting a whole functor

A functor `G` into `InducedCategory C a` can be transported all at once, by composing
with `transport e`. The result has the same objects as `G`, by definition, so the two can
be compared without any `eqToHom` between objects. -/

example {J : Type*} [Category J] (G : J ⥤ InducedCategory C a) (j : J) :
    (G ⋙ transport e).obj j = G.obj j :=
  rfl

example {J : Type*} [Category J] (G : J ⥤ InducedCategory C a) {j j' : J} (f : j ⟶ j') :
    ((G ⋙ transport e).map f).hom = transportHom e (G.map f) :=
  rfl

/-! ## 7. A concrete instance

In the category of types, take `a n := Fin (0 + n)` and `b n := Fin n`. For a variable
`n`, `0 + n` is not `n` by definition, so `Fin (0 + n)` and `Fin n` are different types;
`Nat.zero_add n` proves them equal. A function `Fin (0 + n) → Fin (0 + m)` is a morphism
`n ⟶ m` of the induced category, and its transported morphism is a function `Fin n → Fin m`. -/

section Concrete

/-- The family of equations `Fin (0 + n) = Fin n`. -/
theorem finEq (n : ℕ) : Fin (0 + n) = Fin n := congrArg Fin (Nat.zero_add n)

/-- The identity of `Fin (0 + n)`, as a morphism of the induced category. Its transported morphism
is the identity of `Fin n`: `transportHom_id` applies with no reasoning about `0 + n`. -/
example (n : InducedCategory (Type) (fun n : ℕ => Fin (0 + n))) :
    transportHom finEq (𝟙 n) = 𝟙 (Fin n) := by
  simp

end Concrete
