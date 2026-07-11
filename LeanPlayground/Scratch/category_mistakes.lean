/-
The universal property of `foldr`, two ways.

REVISION 3 — adapted to the ConcreteCategory refactor of `Category (Type u)`:
in this Mathlib, `X ⟶ Y` for types is a one-field structure around `X → Y`,
not a bare function. Consequences:
  * construct homs with `ConcreteCategory.ofHom`
      [MED — dual of `ConcreteCategory.hom`, which the error output
       confirms exists; fallback name: `TypeCat.ofHom`]
  * apply homs via `ConcreteCategory.hom f` (FunLike-coerced)
      [HIGH — exact spelling from the elaborator's own coercions]
  * hom equalities via the `ext` tactic instead of `funext`
      [MED — fallback: `apply ConcreteCategory.hom_ext`]
STILL UNCOMPILED on my end; the `simp` calls in the initiality proof are
the least-tested part.
-/
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra

open CategoryTheory

universe u

/-! ### Part 1: elementary universal property [HIGH]
Unchanged — no category theory involved, so the refactor can't touch it. -/

theorem foldr_universal {α β : Type u} (f : α → β → β) (e : β)
    (h : List α → β) :
    h = List.foldr f e ↔ h [] = e ∧ ∀ a as, h (a :: as) = f a (h as) := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨hnil, hcons⟩
    funext as
    induction as with
    | nil => exact hnil
    | cons a as ih => rw [hcons, ih, List.foldr_cons]

/-! ### Part 2: `List A` as the initial algebra of `F X = Option (A × X)` -/

namespace ListInitialAlgebra

variable (A : Type u)

/-- The list base functor `F X = 1 + A × X`, encoded as `Option (A × X)`.
Functor laws are left to the autoparam discharger, which the
ConcreteCategory refactor is designed to feed. If it chokes, supply
`map_id := by intro X; ext x; cases x <;> rfl` (or `<;> simp`) and the
analogous `map_comp`. -/
def listF : Type u ⥤ Type u where
  obj X := Option (A × X)
  map {X Y} g := ConcreteCategory.ofHom
    ⟨fun x => Option.map (Prod.map id (ConcreteCategory.hom g)) x⟩
  map_id := by intro X; ext x; cases x <;> rfl
  map_comp := by intro X Y Z f g; ext x; cases x <;> rfl

/-- `List A` as an algebra: `none ↦ []`, `some (a, as) ↦ a :: as`. -/
def listAlg : Endofunctor.Algebra (listF A) where
  a := List A
  str := ConcreteCategory.ofHom
    ⟨fun x => match x with | none => [] | some (a, as) => a :: as⟩

/-- The catamorphism: `foldr` as an algebra morphism to any algebra `B`;
step and seed are both read off `B.str`. -/
def foldHom (B : Endofunctor.Algebra (listF A)) : listAlg A ⟶ B where
  f := ConcreteCategory.ofHom
    ⟨List.foldr (fun a b => ConcreteCategory.hom B.str (some (a, b)))
      (ConcreteCategory.hom B.str none)⟩
  h := by
    ext x
    -- fallback if `rfl` no longer reduces through the hom wrappers:
    --   rcases x with _ | ⟨a, as⟩ <;> simp [listF, listAlg]
    rcases x with _ | ⟨a, as⟩ <;> rfl

/-- `(List A, [nil, cons])` is the initial algebra of `listF A`:
existence is `foldHom`, uniqueness is `foldr_universal` replayed against
the algebra-morphism square. -/
def listAlgIsInitial : Limits.IsInitial (listAlg A) :=
  Limits.IsInitial.ofUniqueHom (foldHom A) fun B m => by
    apply Endofunctor.Algebra.Hom.ext
    ext (as : List A)
    -- Pointwise consequences of the square `m.h`, one per constructor.
    -- `simpa` should split `hom (f ≫ g) x` via `ConcreteCategory.comp_apply`
    -- and collapse `hom (ofHom _)`.
    have hnil :
        ConcreteCategory.hom m.f [] = ConcreteCategory.hom B.str none := by
      have h := congrArg (fun (g : (listF A).obj (List A) ⟶ B.a) =>
        ConcreteCategory.hom g (none : Option (A × List A))) m.h
      simp [listF, listAlg] at h
      exact h.symm
    have hcons : ∀ (a : A) (as : List A),
        ConcreteCategory.hom m.f (a :: as)
          = ConcreteCategory.hom B.str
              (some (a, ConcreteCategory.hom m.f as)) := by
      intro a as
      have h := congrArg (fun (g : (listF A).obj (List A) ⟶ B.a) =>
        ConcreteCategory.hom g (some (a, as))) m.h
      simp [listF, listAlg] at h
      exact h.symm
    induction as with
    | nil => exact hnil
    | cons a as ih =>
      change ConcreteCategory.hom m.f (a :: as) = ConcreteCategory.hom (foldHom A B).f (a :: as)
      have ih' : ConcreteCategory.hom m.f as = ConcreteCategory.hom (foldHom A B).f as := by
        simpa using ih
      rw [hcons a as, ih']
      rfl

/-- Lambek's lemma, specialized: `Option (A × List A) ≅ List A` via the
structure map. -/
example : IsIso (listAlg A).str :=
  Endofunctor.Algebra.Initial.str_isIso (listAlgIsInitial A)

end ListInitialAlgebra
