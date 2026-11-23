import LeanPlayground.Scratch.actual_category_scratch.scratch_4.sandwiches
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Products.Basic

/-! # Controlled test: direct approach, plain setup

One cell of a 2×2 comparison; see `README.md` in this directory. The four files share
all their text except the setup lines and the proof of the hard round trip
`fromNatTrans (toNatTrans F) = F`.

* Setup (plain): `Lift` is a plain `def`, and `backward.defeqAttrib.useBackward` is off.
* Approach (direct): the hard round trip uses `Functor.ext`, whose `eqToHom`s are pushed through the comma projections with `Comma.eqToHom_left` and `_right`. -/

set_option pp.proofs.withType true

open CategoryTheory

namespace Controlled.DirectPlain

variable {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]

/-- Send an object of `Comma L R` to its pair of legs. -/
def commaProjProd (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ 𝒞 × 𝒞 :=
  (Comma.fst L R).prod' (Comma.snd L R)

/-- Lifts of `Δ` through `commaProjProd L R`. -/
def Lift (L R : 𝒞 ⥤ 𝒟) :=
  {F : 𝒞 ⥤ Comma L R // F ⋙ commaProjProd L R = Functor.diag 𝒞}

namespace Lift

variable {L R : 𝒞 ⥤ 𝒟}

def fromNatTrans (α : L ⟶ R) : Lift L R :=
  ⟨{obj := fun c => ⟨c, c, α.app c⟩,
    map := fun f => ⟨f, f, by cat_disch⟩},
  by cat_disch⟩

theorem obj_left_eq (F : Lift L R) (c : 𝒞) : (F.val.obj c).left = c := by
  have h := congrArg (fun G => (G.obj c).1) F.property
  simpa [commaProjProd] using h

theorem obj_right_eq (F : Lift L R) (c : 𝒞) : (F.val.obj c).right = c := by
  have h := congrArg (fun G => (G.obj c).2) F.property
  simpa [commaProjProd] using h

/-- The component at `c`: `(F c).hom`, retyped along the images of the two equations. -/
def component (F : Lift L R) (c : 𝒞) : L.obj c ⟶ R.obj c :=
  sandwich (congrArg L.obj (obj_left_eq F c)) (congrArg R.obj (obj_right_eq F c))
    (F.val.obj c).hom

/-- Since `F ⋙ P = Δ`, the left leg of `F m` is `m`, retyped. -/
theorem map_left_eq (F : Lift L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    m = sandwich (obj_left_eq F c₁) (obj_left_eq F c₂) (F.val.map m).left := by
  have h : (F.val.map m).left
      = eqToHom (obj_left_eq F c₁) ≫ m ≫ eqToHom (obj_left_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property) m
  simp [sandwich, h]

/-- Since `F ⋙ P = Δ`, the right leg of `F m` is `m`, retyped. -/
theorem map_right_eq (F : Lift L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    m = sandwich (obj_right_eq F c₁) (obj_right_eq F c₂) (F.val.map m).right := by
  have h : (F.val.map m).right
      = eqToHom (obj_right_eq F c₁) ≫ m ≫ eqToHom (obj_right_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.snd 𝒞 𝒞) F.property) m
  simp [sandwich, h]

def toNatTrans (F : Lift L R) : L ⟶ R where
  app := F.component
  naturality c₁ c₂ m := by
    conv_lhs => rw [F.map_left_eq m]
    conv_rhs => rw [F.map_right_eq m]
    simp only [component, map_sandwich, sandwich_comp]
    exact congrArg _ (F.val.map m).w

/-- Going from `α` to a lift of `Δ` and back gives `α`. -/
theorem toNatTrans_fromNatTrans (α : L ⟶ R) : toNatTrans (fromNatTrans α) = α := by
  ext c
  simp [toNatTrans, component, fromNatTrans, sandwich]

/-- An object of `Comma L R` is determined by its legs and its morphism: retyping
`X.hom` along `X.left = a` and `X.right = b` gives back `X`. -/
theorem comma_mk_sandwich (X : Comma L R) {a b : 𝒞} (hl : X.left = a) (hr : X.right = b) :
    (⟨a, b, sandwich (congrArg L.obj hl) (congrArg R.obj hr) X.hom⟩ : Comma L R) = X := by
  cases X
  subst hl hr
  simp

/-- Going from a lift of `Δ` to `α` and back gives the lift. -/
theorem fromNatTrans_toNatTrans (F : Lift L R) : fromNatTrans (toNatTrans F) = F := by
  apply Subtype.ext
  fapply CategoryTheory.Functor.ext
  · intro c
    exact comma_mk_sandwich (F.val.obj c) (obj_left_eq F c) (obj_right_eq F c)
  · intro c₁ c₂ m
    apply Comma.hom_ext
    · rw [Comma.comp_left, Comma.comp_left]
      erw [Comma.eqToHom_left, Comma.eqToHom_left]
      exact F.map_left_eq m
    · rw [Comma.comp_right, Comma.comp_right]
      erw [Comma.eqToHom_right, Comma.eqToHom_right]
      exact F.map_right_eq m

end Lift

/-- Natural transformations `L ⟶ R` are in bijection with lifts of `Δ`. -/
def bij {L R : 𝒞 ⥤ 𝒟} : (L ⟶ R) ≃ Lift L R where
  toFun := Lift.fromNatTrans
  invFun := Lift.toNatTrans
  left_inv := Lift.toNatTrans_fromNatTrans
  right_inv := Lift.fromNatTrans_toNatTrans

end Controlled.DirectPlain
