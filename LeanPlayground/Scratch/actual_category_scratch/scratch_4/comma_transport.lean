import LeanPlayground.Scratch.actual_category_scratch.scratch_4.induced_eq
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Products.Basic

set_option pp.proofs.withType true
set_option backward.defeqAttrib.useBackward true

show_panel_widgets [local ProofWidgets.SelectionPanel]

/-! # The comma bijection, by transport

The direct comma version of the bijection between natural transformations `L ⟶ R` and
lifts of `Δ` through `P : Comma L R ⥤ 𝒞 × 𝒞`, redone with the transport functors of
`induced_eq.lean`. It is self-contained, so that `Lift` can be an `abbrev`: as a plain
`def`, a coercion `↑F` out of it does not type-check at the transparency that `simp` and
`dsimp` work at, and they refuse to touch any term containing it.

The hard direction is `fromNatTrans (toNatTrans F) = F`, an equation of functors into
`Comma L R` whose objects differ: `⟨c, c, component F c⟩` on the left and `F c` on the
right. It is proved by transporting once and coming back once:

* `F` copied along the equations `F c = ⟨c, c, component F c⟩` (`copy` in
  `induced_eq.lean`) has the same objects as `fromNatTrans (toNatTrans F)`, so the two
  functors are compared on morphisms alone, with no `eqToHom`. On morphisms the
  comparison is `map_left_eq` and `map_right_eq`.
* `copy_eq` says the copy is `F`. -/

open CategoryTheory InducedEq

namespace CommaTransport

variable {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟] {L R : 𝒞 ⥤ 𝒟}

/-- Send an object of `Comma L R` to its pair of legs. -/
def commaProjProd (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ 𝒞 × 𝒞 :=
  (Comma.fst L R).prod' (Comma.snd L R)

/-- Lifts of `Δ` through `commaProjProd L R`. -/
abbrev Lift (L R : 𝒞 ⥤ 𝒟) :=
  {F : 𝒞 ⥤ Comma L R // F ⋙ commaProjProd L R = Functor.diag 𝒞}

/-- An object of `Comma L R` is its legs and its morphism, with the morphism retyped along
any equations for the legs. -/
theorem comma_eq_mk (X : Comma L R) {a b : 𝒞} (hl : X.left = a) (hr : X.right = b) :
    X = ⟨a, b, sandwich (congrArg L.obj hl) (congrArg R.obj hr) X.hom⟩ := by
  cases X
  subst hl hr
  simp

namespace Lift

def fromNatTrans (α : L ⟶ R) : Lift L R :=
  ⟨{obj := fun c => ⟨c, c, α.app c⟩,
    map := fun f => ⟨f, f, by cat_disch⟩},
  by cat_disch⟩

theorem obj_left_eq (F : Lift L R) (c : 𝒞) : (F.val.obj c).left = c := by
  simpa [commaProjProd] using congrArg (fun G => (G.obj c).1) F.property

theorem obj_right_eq (F : Lift L R) (c : 𝒞) : (F.val.obj c).right = c := by
  simpa [commaProjProd] using congrArg (fun G => (G.obj c).2) F.property

/-- Since `F ⋙ P = Δ`, the left leg of `F m` is `m`, retyped. -/
theorem map_left_eq (F : Lift L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    sandwich (obj_left_eq F c₁) (obj_left_eq F c₂) (F.val.map m).left = m := by
  have h : (F.val.map m).left
      = eqToHom (obj_left_eq F c₁) ≫ m ≫ eqToHom (obj_left_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property) m
  simp [sandwich, h]

/-- Since `F ⋙ P = Δ`, the right leg of `F m` is `m`, retyped. -/
theorem map_right_eq (F : Lift L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    sandwich (obj_right_eq F c₁) (obj_right_eq F c₂) (F.val.map m).right = m := by
  have h : (F.val.map m).right
      = eqToHom (obj_right_eq F c₁) ≫ m ≫ eqToHom (obj_right_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.snd 𝒞 𝒞) F.property) m
  simp [sandwich, h]

/-- The component at `c`: `(F c).hom`, retyped along the images of the two equations. -/
def component (F : Lift L R) (c : 𝒞) : L.obj c ⟶ R.obj c :=
  sandwich (congrArg L.obj (obj_left_eq F c)) (congrArg R.obj (obj_right_eq F c))
    (F.val.obj c).hom

def toNatTrans (F : Lift L R) : L ⟶ R where
  app := component F
  naturality c₁ c₂ m := by
    conv_lhs => rw [← F.map_left_eq m]
    conv_rhs => rw [← F.map_right_eq m]
    -- Both sides are now one sandwich, of the two sides of the square `F m`.
    simp only [component, map_sandwich, sandwich_comp]
    exact congrArg _ (F.val.map m).w

theorem toNatTrans_fromNatTrans (α : L ⟶ R) : toNatTrans (fromNatTrans α) = α := by
  ext c
  simp [toNatTrans, component, fromNatTrans, sandwich]

/-- Each object `F c` is `⟨c, c, component F c⟩`, the object of
`fromNatTrans (toNatTrans F)` at `c`. -/
theorem obj_eq (F : Lift L R) (c : 𝒞) : F.val.obj c = ⟨c, c, component F c⟩ :=
  comma_eq_mk (F.val.obj c) (obj_left_eq F c) (obj_right_eq F c)

/-- `fromNatTrans (toNatTrans F)` is `F` copied along `obj_eq F`: the two functors have
the same objects, so they are compared on morphisms, leg by leg. -/
theorem fromNatTrans_toNatTrans_eq_copy (F : Lift L R) :
    (fromNatTrans (toNatTrans F)).val = copy F.val _ (obj_eq F) := by
  refine Functor.hext (fun _ => rfl) fun c₁ c₂ m => heq_of_eq ?_
  apply Comma.hom_ext
  -- Each leg of the copied map is `Comma.fst` (or `Comma.snd`) applied to a sandwich of
  -- `F m`, which `map_sandwich` turns into a sandwich of the leg of `F m`. That is `m`, by
  -- `map_left_eq` (or `map_right_eq`), and `m` is the leg of the left-hand map. The steps
  -- agree by definition, so they are chained as terms.
  · exact (F.map_left_eq m).symm.trans
      (map_sandwich (Comma.fst L R) (obj_eq F c₁) (obj_eq F c₂) (F.val.map m)).symm
  · exact (F.map_right_eq m).symm.trans
      (map_sandwich (Comma.snd L R) (obj_eq F c₁) (obj_eq F c₂) (F.val.map m)).symm

/-- Going from a lift of `Δ` to `α` and back gives the lift: transport once, compare, and
come back once. -/
theorem fromNatTrans_toNatTrans (F : Lift L R) : fromNatTrans (toNatTrans F) = F :=
  Subtype.ext ((fromNatTrans_toNatTrans_eq_copy F).trans (copy_eq _ _ _))

end Lift

end CommaTransport
