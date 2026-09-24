import Mathlib.CategoryTheory.Yoneda

open CategoryTheory
open Opposite

universe u v w

section

variable (C : Type u) [Category.{v} C]

/-- Structures introduced to bridge between Riehl's usage (p. 51, p. 62)
and the Lean category API. -/
structure Corepresentation where
  functor : C ⥤ Type v
  obj : C
  corep : functor.CorepresentableBy obj

structure Representation where
  functor : Cᵒᵖ ⥤ Type v
  obj : C
  rep : functor.RepresentableBy obj

/- `Element` is an associated type: the type of a universal element depends
on which representation package we were given. -/
class HasUniversalElement (S : Type w) where
  Element : S → Type v
  universalElement : (s : S) → Element s

instance : HasUniversalElement (Corepresentation (C := C)) where
  Element R := R.functor.obj R.obj
  universalElement R := R.corep.homEquiv (𝟙 R.obj)

instance : HasUniversalElement (Representation (C := C)) where
  Element R := R.functor.obj (op R.obj)
  universalElement R := R.rep.homEquiv (𝟙 R.obj)

def universalElement {S : Type w} [h : HasUniversalElement S] (s : S) :
    h.Element s :=
  h.universalElement s

/-- Let `u := hu.homEquiv (𝟙 A) : F.obj A` and
`v := hv.homEquiv (𝟙 B) : F.obj B`. These are the universal elements selected
by the two corepresentations. There is exactly one isomorphism `φ : A ≅ B`
such that applying `F` to `φ` carries `u` to `v`, i.e. `F(φ)(u) = v`.

The theorem statement spells out `u` and `v` as images of identity morphisms
because that is how `CorepresentableBy` stores its universal elements. -/
theorem existsUnique_iso_of_universalElements
    {F : C ⥤ Type v} {A B : C}
    (hu : F.CorepresentableBy A) (hv : F.CorepresentableBy B) :
    ∃! φ : A ≅ B,
      F.map φ.hom (hu.homEquiv (𝟙 A)) = hv.homEquiv (𝟙 B) := by
  let φ := hu.uniqueUpToIso hv
  refine ⟨φ, ?_, ?_⟩
  · dsimp [φ]
    rw [← hu.homEquiv_eq]
    change hu.homEquiv (hu.homEquiv.symm (hv.homEquiv (𝟙 B))) = _
    exact Equiv.apply_symm_apply _ _
  · intro ψ hψ
    apply Iso.ext
    apply hu.homEquiv.injective
    rw [hu.homEquiv_eq]
    exact hψ.trans (Equiv.apply_symm_apply _ _).symm

/-- The fixed-object specialization of `existsUnique_iso_of_universalElements`.

Let `u := hu.homEquiv (𝟙 A)` and `v := hv.homEquiv (𝟙 A)`. If both are
universal elements for `F` at the same object `A`, there is exactly one
automorphism `σ : A ≅ A` for which `F(σ)(u) = v`. In particular, universal
elements at a fixed representing object need not be equal, but they are
related by a unique symmetry of that object. -/
theorem existsUnique_aut_of_universalElements
    {F : C ⥤ Type v} {A : C}
    (hu hv : F.CorepresentableBy A) :
    ∃! σ : A ≅ A,
      F.map σ.hom (hu.homEquiv (𝟙 A)) = hv.homEquiv (𝟙 A) :=
  existsUnique_iso_of_universalElements C hu hv

end
