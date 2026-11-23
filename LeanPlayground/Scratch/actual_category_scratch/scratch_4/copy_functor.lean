import LeanPlayground.Scratch.actual_category_scratch.scratch_4.sandwiches
import LeanPlayground.Scratch.actual_category_scratch.scratch_4.heq_calc
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering

set_option pp.proofs.withType true

show_panel_widgets [local ProofWidgets.SelectionPanel]

/-! # Copying a functor along equations of objects

Given a functor `F : J ⥤ C`, a function `b : J → C`, and an equation `e j : F.obj j = b j`
for each `j`, there is a functor `copyObjEq F b e` with objects `b j`, whose action on a
morphism `f` is `F.map f` retyped along the equations: `sandwich (e _) (e _) (F.map f)`.
It is the equality version of Mathlib's `Functor.copyObj`, which takes isomorphisms
`F.obj j ≅ b j` instead.

Here it is built from `ObjEq` instead of directly:

* `F` and `e` together are a functor `toObjEq F b e : J ⥤ ObjEq C`, sending `j` to the
  equation `e j` and `f` to the morphism with top side `F.map f`. Its functor laws are
  those of `F`, since the top side is the only data of a morphism of `ObjEq C`.
* `copyObjEq F b e` is `toObjEq F b e ⋙ ObjEq.cod`. Its functor laws are inherited from
  `toObjEq` and `cod`, so the bookkeeping `sandwich_id` and `sandwich_comp` is done once,
  in `cod`, and never mentioned here.
* `F` is `toObjEq F b e ⋙ ObjEq.dom` by definition, so whiskering `ObjEq.domIsoCod`
  gives the isomorphism `F ≅ copyObjEq F b e`, with no naturality to prove. -/

open CategoryTheory

#check rfl

namespace CopyObjEq

variable {J : Type*} [Category J] {C : Type*} [Category C]

/-- `sandwich_heq`, stated with `HEqR` for use in `calc`. -/
theorem sandwich_heqR {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) : sandwich p q f ≍ᵣ f :=
  sandwich_heq p q f

/-- `F`, together with the equations `e j : F.obj j = b j`, as a functor into equations. -/
@[simps]
def toObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) : J ⥤ ObjEq C where
  obj j := ⟨F.obj j, b j, e j⟩
  map f := ⟨F.map f⟩
  map_id j := ObjEq.hom_ext (F.map_id j)
  map_comp f g := ObjEq.hom_ext (F.map_comp f g)

/-- The copy of `F` with objects `b j`: the right-hand sides of the equations. -/
def copyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) : J ⥤ C :=
  toObjEq F b e ⋙ ObjEq.cod

@[simp] theorem copyObjEq_obj (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) (j : J) :
    (copyObjEq F b e).obj j = b j := rfl

@[simp] theorem copyObjEq_map (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j)
    {j k : J} (f : j ⟶ k) :
    (copyObjEq F b e).map f = sandwich (e j) (e k) (F.map f) := rfl

/-- `F` is isomorphic to its copy, with components `eqToHom (e j)`. -/
def isoCopyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) :
    F ≅ copyObjEq F b e :=
  Functor.isoWhiskerLeft (toObjEq F b e) ObjEq.domIsoCod

/-! ## Copying is compatible with the operations on equations

These are equations between functors whose objects agree by definition. `Functor.ext`
would insert `eqToHom`s between `(copyObjEq F b e).obj j` and `b j`, which are equal by
definition but not syntactically, and `simp` cannot remove those. `Functor.hext` asks
instead for the maps to agree up to `HEq`, and `sandwich_heq` says that a sandwich is
`HEq` to the morphism inside it. This is the situation `HEq` is suited to: the objects
agree by definition, so nothing has to be transported back. -/

/-- Copying along `rfl` gives `F` back. -/
theorem copyObjEq_rfl (F : J ⥤ C) : copyObjEq F F.obj (fun _ => rfl) = F :=
  Functor.hext (fun _ => rfl) fun j _ f => sandwich_heq (rfl : F.obj j = F.obj j) rfl (F.map f)

/-- Copying twice is copying once, along the composite equations. Both sides of the map
equation are sandwiches of `F.map f`. -/
theorem copyObjEq_copyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j)
    (b' : J → C) (e' : ∀ j, b j = b' j) :
    copyObjEq (copyObjEq F b e) b' e' = copyObjEq F b' (fun j => (e j).trans (e' j)) :=
  Functor.hext (fun _ => rfl) fun j k f => by
    -- Unfolded, the two maps are these sandwiches of `F.map f`.
    show sandwich (e' j) (e' k) (sandwich (e j) (e k) (F.map f))
      ≍ sandwich ((e j).trans (e' j)) ((e k).trans (e' k)) (F.map f)
    exact HEqR.toHEq <| calc
      sandwich (e' j) (e' k) (sandwich (e j) (e k) (F.map f))
      _ ≍ᵣ sandwich (e j) (e k) (F.map f) := sandwich_heqR _ _ _
      _ ≍ᵣ F.map f := sandwich_heqR _ _ _
      _ ≍ᵣ sandwich ((e j).trans (e' j)) ((e k).trans (e' k)) (F.map f) :=
          (sandwich_heqR _ _ _).symm

/-- Copying, then applying `G`, is applying `G`, then copying along the images of the
equations. On maps this is `map_sandwich`. -/
theorem copyObjEq_comp {D : Type*} [Category D] (F : J ⥤ C) (b : J → C)
    (e : ∀ j, F.obj j = b j) (G : C ⥤ D) :
    copyObjEq F b e ⋙ G
      = copyObjEq (F ⋙ G) (fun j => G.obj (b j)) (fun j => congrArg G.obj (e j)) :=
  Functor.hext (fun _ => rfl) fun j k f => heq_of_eq (map_sandwich G (e j) (e k) (F.map f))

end CopyObjEq
