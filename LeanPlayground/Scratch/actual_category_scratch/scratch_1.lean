import Mathlib.CategoryTheory.HomCongr

open CategoryTheory
open CategoryTheory.Functor

/-
  This scratch pokes at hom transport along isos.

  The key import is `Mathlib.CategoryTheory.HomCongr`.

  That module is short and sweet. It substantiates the sense in which
  isomorphism establishes categorical "indistinguishability," and what we mean
  when we say we're "transporting" a morphism "along" isos.

  The crucial abstraction is to see pairs of isos as establishing bijections
  between hom-sets.

  The network of transports can be visualized as a grid:
-/
/-
  a ── μ ≅ ──▶  a' ── η ≅ ──▶  c ──▶ ...
  │             │              │
  f             f'             f''
  │             │              │
  ↓             ↓              ↓
  b ── μ' ≅ ─▶  b' ── η' ≅ ─▶  c' ──▶ ...
  │             │              │
  g             g'             g''
  │             │              │
  ↓             ↓              ↓
  d ── μ'' ≅ ─▶ d' ── η'' ≅ ─▶ e ──▶ ...
-/
/-
  By the bijection, the horizontal direction can be run forwards or backwards.
-/

universe u₁ v₁ u₂ v₂ u₃ v₃

section scratch_1

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F G : C ⥤ D)


/- Riehl's lemma 1.5.10 -/
theorem existsUnique_hom_comp_of_iso (a a' b b': C)
    (f  : a ⟶ b)
    (μ  : a ⟶ a') [IsIso μ]
    (μ' : b ⟶ b') [IsIso μ']:
    ∃! f' : a' ⟶ b', μ ≫ f' = f ≫ μ' := by
  -- refine ⟨inv μ ≫ f ≫ μ', ?_, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact inv μ ≫ f ≫ μ'
  #check IsIso.hom_inv_id_assoc μ (f ≫ μ')
  · exact IsIso.hom_inv_id_assoc μ (f ≫ μ') -- simp also works here
  · intro f' hf'
    have h := congrArg (fun side => inv μ  ≫ side) hf'
    rw [IsIso.inv_hom_id_assoc] at h
    exact h

-- but there's an existing mathlib thing that sweeps this up

#check Iso.homCongr
/- CategoryTheory.Iso.homCongr.{v, u} {C : Type u} [Category.{v, u} C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
(X ⟶ Y) ≃ (X₁ ⟶ Y₁)
-/

section ejemple

variable (a a' b b' :C)
variable (f : a ⟶ b)
variable (μ : a ⟶ a') [IsIso μ]
variable (μ': b ⟶ b') [IsIso μ']

-- existsUnique_hom_comp_of_iso
example : ∃! f' : a' ⟶ b', μ ≫ f' = f ≫ μ' := by
  let f': a' ⟶ b' := Iso.homCongr (asIso μ) (asIso μ') f
  refine ⟨f', ?_, ?_⟩ <;> cat_disch

example : ∃! f' : a' ⟶ b', (inv μ) ≫ f ≫ μ' = f' := by
  let f': a' ⟶ b' := Iso.homCongr (asIso μ) (asIso μ') f
  refine ⟨f', ?_, ?_⟩ <;> cat_disch

-- etc

end ejemple




#check Iso.isoCongr

def isoCongr {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ≅ X₂) (g : Y₁ ≅ Y₂) : (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂) where
  toFun := fun h =>
    f.symm.trans <| h.trans <| g
  invFun := fun h =>
    f.trans <| h.trans <| g.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

end scratch_1
