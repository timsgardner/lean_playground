import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.CategoryTheory.Products.Basic
import LeanPlayground.Scratch.category_kindergarten.check_diagrams
import LeanPlayground.Scratch.category_kindergarten.common_tools
import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget

set_option pp.proofs.withType true

/-
  What each import brings in:

    Category.Basic         `Category`, `X ⟶ Y`, `𝟙 X`, `f ≫ g`, `Category.assoc`
    Functor.Basic          `C ⥤ D`, `F.obj`, `F.map`, `𝟭 C`, `F ⋙ G`
    NatTrans               `NatTrans F G`, `α.app X`, `α.naturality`
    Functor.Category       the functor category: `α : F ⟶ G`, `α ≫ β`, `NatTrans.comp_app`
    Functor.FullyFaithful  `F.Faithful` (`map_injective`), `F.Full` (`map_surjective`),
                           `F.FullyFaithful`
    Comma.Basic            `Comma L R`, with fields `left`, `right`, `hom`, and
                           morphisms `CommaMorphism` (fields `left`, `right`, `w`)
    Logic.Function.Basic   `Function.Injective`, `Function.Surjective`,
                           `Function.Bijective` and their API
    check_diagrams         our infoview diagrams: `#check` draws squares/triangles; with
                           the selection panel below, shift-click a goal or hypothesis
                           (equations `f ≫ g = i ≫ h`, `CommSq`, `comm_diagram`) to draw it
-/

open CategoryTheory

show_panel_widgets [local ProofWidgets.SelectionPanel]

/- Mathlib convention: `u` for the universe of objects, `v` for the universe of
  morphisms (hom-sets). `Category.{v₁} 𝒞` says the hom-sets of `𝒞` live in `Type v₁`. -/
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

/- Three categories, enough for a comma category `Comma L R` with
  `L : 𝒜 ⥤ 𝒞` and `R : ℬ ⥤ 𝒞`. -/
variable {𝒜 : Type u₁} [Category.{v₁} 𝒜]
variable {ℬ : Type u₂} [Category.{v₂} ℬ]
variable {𝒞 : Type u₃} [Category.{v₃} 𝒞]
variable {𝒟 : Type u₄} [Category.{v₄} 𝒟]

example (F : 𝒞 ⥤ 𝒟) [F.Faithful] {X Y : 𝒞} :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  F.map_injective

/-! ## Sandwiches

`sandwich p q f` is the morphism `f : X ⟶ Y` retyped as a morphism `X' ⟶ Y'`, along
equations `p : X = X'` and `q : Y = Y'`. It is `eqToHom p.symm ≫ f ≫ eqToHom q`, but
naming it lets us state how such transported morphisms compose and map, once, instead
of pushing individual `eqToHom`s around in every proof. -/

def sandwich {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) : X' ⟶ Y' :=
  eqToHom p.symm ≫ f ≫ eqToHom q

section Sandwich

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Transporting along reflexivity does nothing. -/
@[simp]
theorem sandwich_rfl {X Y : C} (f : X ⟶ Y) : sandwich rfl rfl f = f := by
  simp [sandwich]

/-- Two sandwiches that meet at the same object compose to the sandwich of the
composite. -/
theorem sandwich_comp {X X' Y Y' Z Z' : C} (p : X = X') (q : Y = Y') (r : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sandwich p q f ≫ sandwich q r g = sandwich p r (f ≫ g) := by
  simp [sandwich]

/-- A functor carries a sandwich to the sandwich of the image. -/
theorem map_sandwich (G : C ⥤ D) {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) :
    G.map (sandwich p q f) = sandwich (congrArg G.obj p) (congrArg G.obj q) (G.map f) := by
  simp [sandwich, eqToHom_map]

end Sandwich

/-- Gives a functor from `Comma L R` to pairs of its first and second
(left and right) projections. -/
def commaProjProd (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ 𝒞 × 𝒞 :=
  (Comma.fst L R).prod' (Comma.snd L R)

def NatTransFunctor (L R: 𝒞 ⥤ 𝒟) :=
  {F : 𝒞 ⥤ Comma L R // F ⋙ commaProjProd L R = Functor.diag 𝒞}

/-! ## Lifts of `Δ` through `P` and the natural transformations they determine

Here `P = commaProjProd L R : Comma L R ⥤ 𝒞 × 𝒞` and `Δ = Functor.diag 𝒞`. A lift of
`Δ` through `P` is a functor `F : 𝒞 ⥤ Comma L R` with `F ⋙ P = Δ`; these are the
elements of `NatTransFunctor L R`. -/

namespace NatTransFunctor

variable {L R : 𝒞 ⥤ 𝒟}

def fromNatTrans (α : L ⟶ R) : NatTransFunctor L R :=
  ⟨{obj := fun c => ⟨c, c, α.app c⟩,
    map := fun f => ⟨f, f, by cat_disch⟩},
  by cat_disch⟩

theorem obj_left_eq (F : NatTransFunctor L R) (c : 𝒞) : (F.val.obj c).left = c := by
  have h := congrArg (fun G => (G.obj c).1) F.property
  simpa [commaProjProd] using h

theorem obj_right_eq (F : NatTransFunctor L R) (c : 𝒞) : (F.val.obj c).right = c := by
  have h := congrArg (fun G => (G.obj c).2) F.property
  simpa [commaProjProd] using h

/-- The component at `c` of the natural transformation that `F` determines: the
morphism `(F c).hom : L (F c).left ⟶ R (F c).right`, retyped along
`(F c).left = c` and `(F c).right = c`. -/
def component (F : NatTransFunctor L R) (c : 𝒞) : L.obj c ⟶ R.obj c :=
  sandwich (congrArg L.obj (obj_left_eq F c)) (congrArg R.obj (obj_right_eq F c))
    (F.val.obj c).hom

/-- Since `F ⋙ P = Δ`, the left leg of the comma morphism `F m` is `m`, retyped. -/
theorem map_left_eq (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    m = sandwich (obj_left_eq F c₁) (obj_left_eq F c₂) (F.val.map m).left := by
  -- Stating the type explicitly gives `eqToHom`s whose endpoints are written as
  -- `(F c).left`, not through `⋙`, so that `simp` can merge them below.
  have h : (F.val.map m).left
      = eqToHom (obj_left_eq F c₁) ≫ m ≫ eqToHom (obj_left_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property) m
  simp [sandwich, h]

/-- Since `F ⋙ P = Δ`, the right leg of the comma morphism `F m` is `m`, retyped. -/
theorem map_right_eq (F : NatTransFunctor L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    m = sandwich (obj_right_eq F c₁) (obj_right_eq F c₂) (F.val.map m).right := by
  -- Stating the type explicitly gives `eqToHom`s whose endpoints are written as
  -- `(F c).right`, not through `⋙`, so that `simp` can merge them below.
  have h : (F.val.map m).right
      = eqToHom (obj_right_eq F c₁) ≫ m ≫ eqToHom (obj_right_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.snd 𝒞 𝒞) F.property) m
  simp [sandwich, h]

def toNatTrans (F : NatTransFunctor L R) : L ⟶ R where
  app := F.component
  naturality c₁ c₂ m := by
    -- Write `m` as the left leg of `F m` on the left side of the goal, and as the
    -- right leg on the right side.
    conv_lhs => rw [F.map_left_eq m]
    conv_rhs => rw [F.map_right_eq m]
    -- Each side is now one sandwich of a composite in `𝒟`, and those two
    -- composites are the two sides of the commuting square of `F m`.
    simp only [component, map_sandwich, sandwich_comp, (F.val.map m).w]

/-- An object of `Comma L R` is determined by its legs and its morphism: retyping
`X.hom` along `X.left = a` and `X.right = b` gives back `X`. -/
theorem comma_mk_sandwich (X : Comma L R) {a b : 𝒞} (hl : X.left = a) (hr : X.right = b) :
    (⟨a, b, sandwich (congrArg L.obj hl) (congrArg R.obj hr) X.hom⟩ : Comma L R) = X := by
  cases X
  subst hl hr
  simp

/-- Going from `α` to a lift of `Δ` and back gives `α`. -/
theorem toNatTrans_fromNatTrans (α : L ⟶ R) : toNatTrans (fromNatTrans α) = α := by
  ext c
  simp [toNatTrans, component, fromNatTrans, sandwich]

/-- Going from a lift of `Δ` to `α` and back gives the lift. -/
theorem fromNatTrans_toNatTrans (F : NatTransFunctor L R) :
    fromNatTrans (toNatTrans F) = F := by
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

end NatTransFunctor

/-- Natural transformations `L ⟶ R` are in bijection with the functors
`S : 𝒞 ⥤ Comma L R` such that `S ⋙ P = Δ`. -/
def nat_trans_functor_bij {L R : 𝒞 ⥤ 𝒟} : (L ⟶ R) ≃ NatTransFunctor L R where
  toFun := NatTransFunctor.fromNatTrans
  invFun := NatTransFunctor.toNatTrans
  left_inv := NatTransFunctor.toNatTrans_fromNatTrans
  right_inv := NatTransFunctor.fromNatTrans_toNatTrans


end
