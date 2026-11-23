import LeanPlayground.Scratch.actual_category_scratch.scratch_4.induced_eq
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Products.Basic
open CategoryTheory InducedEq
set_option backward.defeqAttrib.useBackward true
namespace ProbeC_tuned
variable {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟] {L R : 𝒞 ⥤ 𝒟}

def commaProjProd (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ 𝒞 × 𝒞 := (Comma.fst L R).prod' (Comma.snd L R)
abbrev Lift (L R : 𝒞 ⥤ 𝒟) := {F : 𝒞 ⥤ Comma L R // F ⋙ commaProjProd L R = Functor.diag 𝒞}

theorem obj_left_eq (F : Lift L R) (c : 𝒞) : (F.val.obj c).left = c := by
  simpa [commaProjProd] using congrArg (fun G => (G.obj c).1) F.property

@[simps]
def legsL (F : Lift L R) : 𝒞 ⥤ InducedCategory 𝒞 (fun c => (F.val.obj c).left) where
  obj c := c
  map m := InducedCategory.homMk (F.val.map m).left
  map_id c := InducedCategory.hom_ext (by simp)
  map_comp f g := InducedCategory.hom_ext (by simp)

-- the naive proof: unfold, normalize endpoints with dsimp, then rewrite with h
example (F : Lift L R) {c₁ c₂ : 𝒞} (m : c₁ ⟶ c₂) :
    bottom (obj_left_eq F) ((legsL F).map m) = m := by
  have h : (F.val.map m).left
      = eqToHom (obj_left_eq F c₁) ≫ m ≫ eqToHom (obj_left_eq F c₂).symm := by
    simpa [commaProjProd] using
      Functor.congr_hom (congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property) m
  dsimp only [bottom, sandwich, legsL_obj, legsL_map, InducedCategory.homMk_hom]
  simp [h]
end ProbeC_tuned
