import LeanPlayground.Scratch.actual_category_scratch.scratch_4.sandwiches
import Mathlib.CategoryTheory.NatIso

set_option pp.proofs.withType true

show_panel_widgets [local ProofWidgets.SelectionPanel]

/-! # Copying a functor along equations of objects, by `obtain rfl`

The same construction and results as `copy_functor_subst.lean`, with each
`have h : F.obj = b := funext e; subst h` written as the single line
`obtain rfl : F.obj = b := funext e`. When `obtain` (that is, `rcases`) matches an equation
against the pattern `rfl`, it calls `subst` on it, so the two files do the same thing.

As in `copy_functor_subst.lean`, there is no `ObjEq`. Given a functor
`F : J ⥤ C`, a function `b : J → C`, and an equation `e j : F.obj j = b j` for each `j`,
`copyObjEq F b e` has objects `b j` and sends a morphism `f` to
`sandwich (e _) (e _) (F.map f)`.

Here the functor is written down directly, and its proof obligations are discharged by
substitution. `subst` needs an equation with a variable on one side, and it replaces that
variable everywhere. The hypothesis `e` is a family of equations `e j : F.obj j = b j`, one
for each `j`, and none of them qualifies: `b j` is `b` applied to `j`, not a variable. So
`funext e : F.obj = b` first combines the family into a single equation between functions.
In each of the proof obligations below, `b` is a variable, so this equation has a variable
on its right-hand side. `subst` on it replaces `b` by `F.obj` everywhere, which turns each
equation `e j` into a proof of `F.obj j = F.obj j`. Since any two proofs of the same
equation are equal, every sandwich is then `sandwich rfl rfl`, and `simp` removes it with
`sandwich_rfl`. This is the J rule: a statement about an arbitrary
`b` and arbitrary equations `F.obj j = b j` holds once it holds for `b := F.obj` and
`rfl`. -/

open CategoryTheory

namespace CopyObtain

variable {J : Type*} [Category J] {C : Type*} [Category C]

/-- The copy of `F` with objects `b j`. -/
def copyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) : J ⥤ C where
  obj := b
  map f := sandwich (e _) (e _) (F.map f)
  map_id j := by
    obtain rfl : F.obj = b := funext e
    simp
  map_comp f g := by
    obtain rfl : F.obj = b := funext e
    simp

@[simp] theorem copyObjEq_obj (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) (j : J) :
    (copyObjEq F b e).obj j = b j := rfl

@[simp] theorem copyObjEq_map (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j)
    {j k : J} (f : j ⟶ k) :
    (copyObjEq F b e).map f = sandwich (e j) (e k) (F.map f) := rfl

/-- `F` is isomorphic to its copy, with components `eqToHom (e j)`. -/
def isoCopyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j) :
    F ≅ copyObjEq F b e :=
  NatIso.ofComponents (fun j => eqToIso (e j)) fun f => by
    obtain rfl : F.obj = b := funext e
    simp

/-! ## Copying is compatible with the operations on equations

`copyObjEq_rfl` is the base case: there `b` is `F.obj` already, not a variable, so there
is nothing to substitute. Its objects agree with those of `F` by definition, and each map
is a sandwich of `F.map f`, which `sandwich_heq` relates to `F.map f`. The other two
results substitute their way down to the base case. -/

/-- Copying along `rfl` gives `F` back. -/
theorem copyObjEq_rfl (F : J ⥤ C) : copyObjEq F F.obj (fun _ => rfl) = F :=
  Functor.hext (fun _ => rfl) fun j _ f => sandwich_heq (rfl : F.obj j = F.obj j) rfl (F.map f)

/-- Copying twice is copying once, along the composite equations. After substituting
`b` and `b'`, all three copies are copies along `rfl`. -/
theorem copyObjEq_copyObjEq (F : J ⥤ C) (b : J → C) (e : ∀ j, F.obj j = b j)
    (b' : J → C) (e' : ∀ j, b j = b' j) :
    copyObjEq (copyObjEq F b e) b' e' = copyObjEq F b' (fun j => (e j).trans (e' j)) := by
  obtain rfl : F.obj = b := funext e
  obtain rfl : F.obj = b' := funext e'
  simp only [copyObjEq_rfl]

/-- Copying, then applying `G`, is applying `G`, then copying along the images of the
equations. After substituting `b`, both copies are copies along `rfl`. The right-hand side
is written with `fun j => G.obj (F.obj j)` rather than `(F ⋙ G).obj`, so `copyObjEq_rfl`
does not rewrite it, but it is that instance of `copyObjEq_rfl` by definition. -/
theorem copyObjEq_comp {D : Type*} [Category D] (F : J ⥤ C) (b : J → C)
    (e : ∀ j, F.obj j = b j) (G : C ⥤ D) :
    copyObjEq F b e ⋙ G
      = copyObjEq (F ⋙ G) (fun j => G.obj (b j)) (fun j => congrArg G.obj (e j)) := by
  obtain rfl : F.obj = b := funext e
  rw [copyObjEq_rfl]
  exact (copyObjEq_rfl (F ⋙ G)).symm

end CopyObtain
