import Mathlib

/-
Some basic but non-trivial facts about isomorphisms in an arbitrary category.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- The inverse of an isomorphism is unique: if `g` and `g'` both act as
two-sided inverses to `f`, then `g = g'`. -/
theorem inverse_unique {X Y : C} (f : X ⟶ Y) (g g' : Y ⟶ X)
    (hg : f ≫ g = 𝟙 X)
    (hh' : g' ≫ f = 𝟙 Y) : g = g' := by
  calc g = 𝟙 Y ≫ g := by rw [Category.id_comp]
    _ = (g' ≫ f) ≫ g := by rw [hh']
    _ = g' ≫ (f ≫ g) := by rw [Category.assoc]
    _ = g' ≫ 𝟙 X := by rw [hg]
    _ = g' := by rw [Category.comp_id]

/-- A hand-rolled "is an isomorphism" predicate, avoiding Mathlib's `IsIso`
so the composition proof below is done by hand. -/
def IsIsoHand {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y

/-- Identities are isomorphisms. -/
theorem isIsoHand_id (X : C) : IsIsoHand (𝟙 X) :=
  ⟨𝟙 X, Category.id_comp _, Category.id_comp _⟩

/-- Isomorphisms are closed under composition, with inverse `g ≫ g'`
reversed appropriately: if `f : X ⟶ Y` and `h : Y ⟶ Z` are isomorphisms
then so is `f ≫ h`. -/
theorem isIsoHand_comp {X Y Z : C} (f : X ⟶ Y) (h : Y ⟶ Z)
    (hf : IsIsoHand f) (hh : IsIsoHand h) : IsIsoHand (f ≫ h) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  obtain ⟨k, hhk, hkh⟩ := hh
  refine ⟨k ≫ g, ?_, ?_⟩
  · calc (f ≫ h) ≫ (k ≫ g) = f ≫ (h ≫ k) ≫ g := by rw [Category.assoc, Category.assoc]
      _ = f ≫ 𝟙 Y ≫ g := by rw [hhk]
      _ = f ≫ g := by rw [Category.id_comp]
      _ = 𝟙 X := hfg
  · calc (k ≫ g) ≫ (f ≫ h) = k ≫ (g ≫ f) ≫ h := by rw [Category.assoc, Category.assoc]
      _ = k ≫ 𝟙 Y ≫ h := by rw [hgf]
      _ = k ≫ h := by rw [Category.id_comp]
      _ = 𝟙 Z := hkh

/-- Sanity check: our hand-rolled notion agrees with Mathlib's `IsIso`. -/
theorem isIsoHand_iff_isIso {X Y : C} (f : X ⟶ Y) : IsIsoHand f ↔ IsIso f := by
  constructor
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨⟨g, hfg, hgf⟩⟩
  · intro hf
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
