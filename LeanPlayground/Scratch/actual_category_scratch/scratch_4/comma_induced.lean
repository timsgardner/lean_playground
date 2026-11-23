import LeanPlayground.Scratch.actual_category_scratch.scratch_4.induced_eq
import LeanPlayground.Scratch.actual_category_scratch.scratch_4.nat_trans_lifts

set_option pp.proofs.withType true

show_panel_widgets [local ProofWidgets.SelectionPanel]

/-! # The comma natural transformation, with `InducedEq`

A test of `induced_eq.lean` on the direct comma proof. For a lift `F` of `Δ` through
`P : Comma L R ⥤ 𝒞 × 𝒞`, the left legs `(F c).left` are equal to `c`, and so are the right
legs. These are two families of equations indexed by the objects of `𝒞`, and neither can
be removed by `subst`, because the other side is `c` itself rather than a variable.

The left legs of the comma morphisms `F m` form a functor `legsL F` from `𝒞` into the
induced category over `c ↦ (F c).left`. The one fact that uses `F ⋙ P = Δ` on morphisms is
`bottom_legsL`: the bottom side of `(legsL F).map m` is `m`. -/

open CategoryTheory InducedEq

namespace CommaInduced

variable {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟] {L R : 𝒞 ⥤ 𝒟}

theorem obj_left_eq (F : NatTransFunctor L R) (c : 𝒞) : (F.val.obj c).left = c := by
  simpa [commaProjProd] using congrArg (fun G => (G.obj c).1) F.property

theorem obj_right_eq (F : NatTransFunctor L R) (c : 𝒞) : (F.val.obj c).right = c := by
  simpa [commaProjProd] using congrArg (fun G => (G.obj c).2) F.property

/-- The left legs of `F`, as a functor into the induced category over `c ↦ (F c).left`. -/
@[simps]
def legsL (F : NatTransFunctor L R) : 𝒞 ⥤ InducedCategory 𝒞 (fun c => (F.val.obj c).left) where
  obj c := c
  map m := InducedCategory.homMk (F.val.map m).left
  map_id c := InducedCategory.hom_ext (by simp)
  map_comp f g := InducedCategory.hom_ext (by simp)

/-- The right legs of `F`, likewise. -/
@[simps]
def legsR (F : NatTransFunctor L R) : 𝒞 ⥤ InducedCategory 𝒞 (fun c => (F.val.obj c).right) where
  obj c := c
  map m := InducedCategory.homMk (F.val.map m).right
  map_id c := InducedCategory.hom_ext (by simp)
  map_comp f g := InducedCategory.hom_ext (by simp)

/-- Retyping `eqToHom p ≫ g ≫ eqToHom q.symm` along `p` and `q` gives back `g`. -/
theorem sandwich_eqToHom_cancel {C : Type*} [Category C] {X X' Y Y' : C}
    (p : X = X') (q : Y = Y') (g : X' ⟶ Y') :
    sandwich p q (eqToHom p ≫ g ≫ eqToHom q.symm) = g := by
  cases p
  cases q
  simp [sandwich]

/-- Since `F ⋙ P = Δ`, the bottom side of the left leg of `F m` is `m`. The endpoints
`c₁` and `c₂` are given explicitly, so that they are written as `c₁` and `c₂` rather than
as `(legsL F).obj c₁` and `(legsL F).obj c₂`. -/
theorem bottom_left_leg (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    bottom (i := c₁) (k := c₂) (obj_left_eq F) (InducedCategory.homMk (F.val.map m).left) = m := by
  have h : (F.val.map m).left
      = eqToHom (obj_left_eq F c₁) ≫ m ≫ eqToHom (obj_left_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property) m
  show sandwich (obj_left_eq F c₁) (obj_left_eq F c₂) (F.val.map m).left = m
  rw [h]
  exact sandwich_eqToHom_cancel _ _ m

/-- Since `F ⋙ P = Δ`, the bottom side of the right leg of `F m` is `m`. -/
theorem bottom_right_leg (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    bottom (i := c₁) (k := c₂) (obj_right_eq F) (InducedCategory.homMk (F.val.map m).right)
      = m := by
  have h : (F.val.map m).right
      = eqToHom (obj_right_eq F c₁) ≫ m ≫ eqToHom (obj_right_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.snd 𝒞 𝒞) F.property) m
  show sandwich (obj_right_eq F c₁) (obj_right_eq F c₂) (F.val.map m).right = m
  rw [h]
  exact sandwich_eqToHom_cancel _ _ m

/-- The same fact, stated with the functor of left legs: `legsL F ⋙ cod` is the identity
on morphisms. -/
theorem bottom_legsL (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    bottom (obj_left_eq F) ((legsL F).map m) = m :=
  bottom_left_leg F m

/-- Likewise for the right legs. -/
theorem bottom_legsR (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    bottom (obj_right_eq F) ((legsR F).map m) = m :=
  bottom_right_leg F m

/-- The component at `c`: `(F c).hom`, retyped along the images of the two equations. -/
def component (F : NatTransFunctor L R) (c : 𝒞) : L.obj c ⟶ R.obj c :=
  sandwich (congrArg L.obj (obj_left_eq F c)) (congrArg R.obj (obj_right_eq F c))
    (F.val.obj c).hom

def toNatTrans (F : NatTransFunctor L R) : L ⟶ R where
  app := component F
  naturality c₁ c₂ m := by
    -- Write `m` as the bottom side of its left leg on the left, and of its right leg on
    -- the right; then both sides are one sandwich, of the two sides of the square `F m`.
    conv_lhs => rw [← bottom_left_leg F m]
    conv_rhs => rw [← bottom_right_leg F m]
    simp only [component, bottom, InducedCategory.homMk_hom, map_sandwich, sandwich_comp]
    exact congrArg _ (F.val.map m).w

theorem toNatTrans_fromNatTrans (α : L ⟶ R) :
    toNatTrans (NatTransFunctor.fromNatTrans α) = α := by
  ext c
  simp [toNatTrans, component, NatTransFunctor.fromNatTrans, sandwich]

end CommaInduced
