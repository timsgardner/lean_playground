import LeanPlayground.Scratch.category_kindergarten.check_diagrams
import LeanPlayground.Scratch.category_kindergarten.common_tools
import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget
import Mathlib.CategoryTheory.EqToHom

set_option pp.proofs.withType true

show_panel_widgets [local ProofWidgets.SelectionPanel]

open CategoryTheory

/-! # Sandwiches

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

/-- Retyping an identity along the same equation at both ends gives an identity. -/
@[simp]
theorem sandwich_id {X X' : C} (p : X = X') : sandwich p p (𝟙 X) = 𝟙 X' := by
  simp [sandwich]

/-- Retyping twice is retyping along the composite equations. -/
theorem sandwich_sandwich {X X' X'' Y Y' Y'' : C} (p : X = X') (q : Y = Y')
    (p' : X' = X'') (q' : Y' = Y'') (f : X ⟶ Y) :
    sandwich p' q' (sandwich p q f) = sandwich (p.trans p') (q.trans q') f := by
  simp [sandwich]

/-- A functor carries a sandwich to the sandwich of the image. -/
theorem map_sandwich (G : C ⥤ D) {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) :
    G.map (sandwich p q f) = sandwich (congrArg G.obj p) (congrArg G.obj q) (G.map f) := by
  simp [sandwich, eqToHom_map]

/-- Remark: a sandwich "is" `f`, but only up to heterogeneous equality, since
`sandwich p q f : X' ⟶ Y'` and `f : X ⟶ Y` have different types and so cannot be
compared with `=`. This is Mathlib's `conj_eqToHom_iff_heq` in sandwich form. `HEq`
cannot be used with `rw`, so the lemmas above are the ones to compute with. -/
theorem sandwich_heq {X X' Y Y' : C} (p : X = X') (q : Y = Y') (f : X ⟶ Y) :
    sandwich p q f ≍ f := by
  cases p
  cases q
  simp [sandwich]

end Sandwich

/-! # The category of equations between objects

An object of `ObjEq C` is an equation `p : X = X'` between objects of `C`. A morphism
from `p : X = X'` to `q : Y = Y'` is a morphism `top : X ⟶ Y` of `C`, and nothing else.
Each morphism has a bottom side `sandwich p q top : X' ⟶ Y'`, and the square

```
          top
    X ─────────▶ Y
    │            │
eqToHom p    eqToHom q
    ▼            ▼
    X' ────────▶ Y'
       bottom
```

always commutes. So the square is derived from `top`, not extra data.

The domain functor `dom : ObjEq C ⥤ C` acts on morphisms by `top`, and the codomain
functor `cod` acts by `bottom`, that is, by sandwiching. That `cod` is a functor is
`sandwich_id` and `sandwich_comp`. The squares are the naturality squares of a natural
isomorphism `dom ≅ cod` with components `eqToHom p`. Up to equality there is only one
`X'` with `X = X'`, so `ObjEq C` is equivalent to `C` itself. -/

/-- An equation `eq : src = tgt` between objects of `C`. -/
structure ObjEq (C : Type*) where
  src : C
  tgt : C
  eq : src = tgt

namespace ObjEq

variable {C : Type*} [Category C]

/-- A morphism of equations is just a morphism between their left-hand sides. It is
wrapped in a structure so that Lean does not confuse it with a morphism of `C`. -/
@[ext]
structure Hom (p q : ObjEq C) where
  top : p.src ⟶ q.src

instance : Category (ObjEq C) where
  Hom := Hom
  id p := ⟨𝟙 p.src⟩
  comp f g := ⟨f.top ≫ g.top⟩

@[ext]
theorem hom_ext {p q : ObjEq C} {f g : p ⟶ q} (h : f.top = g.top) : f = g :=
  Hom.ext h

@[simp] theorem id_top (p : ObjEq C) : Hom.top (𝟙 p) = 𝟙 p.src := rfl

@[simp] theorem comp_top {p q r : ObjEq C} (f : p ⟶ q) (g : q ⟶ r) :
    (f ≫ g).top = f.top ≫ g.top := rfl

/-! ## The bottom side and the square -/

/-- The bottom side of the square of `f`: its top side, retyped along the equations. -/
def bottom {p q : ObjEq C} (f : p ⟶ q) : p.tgt ⟶ q.tgt :=
  sandwich p.eq q.eq f.top

/-- The square of `f` commutes. -/
theorem square {p q : ObjEq C} (f : p ⟶ q) :
    f.top ≫ eqToHom q.eq = eqToHom p.eq ≫ bottom f := by
  simp [bottom, sandwich]

/-- The bottom side is the only one that makes the square commute. -/
theorem square_iff {p q : ObjEq C} (f : p ⟶ q) (g : p.tgt ⟶ q.tgt) :
    f.top ≫ eqToHom q.eq = eqToHom p.eq ≫ g ↔ g = bottom f := by
  obtain ⟨X, X', p⟩ := p
  obtain ⟨Y, Y', q⟩ := q
  subst p q
  simp [bottom, sandwich, eq_comm]

@[simp] theorem bottom_id (p : ObjEq C) : bottom (𝟙 p) = 𝟙 p.tgt :=
  sandwich_id p.eq

@[simp] theorem bottom_comp {p q r : ObjEq C} (f : p ⟶ q) (g : q ⟶ r) :
    bottom (f ≫ g) = bottom f ≫ bottom g :=
  (sandwich_comp p.eq q.eq r.eq f.top g.top).symm

/-! ## The domain and codomain functors -/

/-- Send an equation to its left-hand side, and a morphism to its top side. -/
@[simps]
def dom : ObjEq C ⥤ C where
  obj p := p.src
  map f := f.top

/-- Send an equation to its right-hand side, and a morphism to its bottom side. That
this is a functor is `sandwich_id` and `sandwich_comp`. -/
@[simps]
def cod : ObjEq C ⥤ C where
  obj p := p.tgt
  map f := bottom f

/-- The equations themselves form a natural isomorphism `dom ≅ cod`; its naturality
squares are the squares of the morphisms. -/
def domIsoCod : (dom : ObjEq C ⥤ C) ≅ cod :=
  NatIso.ofComponents (fun p => eqToIso p.eq) (fun f => square f)

/-! ## `ObjEq C` is equivalent to `C` -/

/-- Send `X` to the equation `rfl : X = X`. -/
@[simps]
def refl : C ⥤ ObjEq C where
  obj X := ⟨X, X, rfl⟩
  map f := ⟨f⟩

/-- Every equation `p : X = X'` is isomorphic to `rfl : X = X`, by the identity of `X`
as top side. -/
def isoRefl (p : ObjEq C) : p ≅ refl.obj p.src where
  hom := ⟨𝟙 p.src⟩
  inv := ⟨𝟙 p.src⟩
  hom_inv_id := hom_ext (Category.id_comp _)
  inv_hom_id := hom_ext (Category.id_comp _)

/-- `dom` is an equivalence, with inverse `refl`. -/
def equivalence : ObjEq C ≌ C where
  functor := dom
  inverse := refl
  unitIso := NatIso.ofComponents isoRefl fun f =>
    -- Both sides have top side `f.top`, composed with an identity on one side or the other.
    hom_ext ((Category.comp_id f.top).trans (Category.id_comp f.top).symm)
  counitIso := Iso.refl _
  -- Every morphism involved has top side an identity.
  functor_unitIso_comp _ := Category.comp_id _

/-! ## Functors act on equations -/

variable {D : Type*} [Category D]

/-- A functor `G : C ⥤ D` sends an equation `p` to `congrArg G.obj p`. -/
@[simps]
def map (G : C ⥤ D) : ObjEq C ⥤ ObjEq D where
  obj p := ⟨G.obj p.src, G.obj p.tgt, congrArg G.obj p.eq⟩
  map f := ⟨G.map f.top⟩

/-- Applying `G` and then taking bottom sides is taking bottom sides and then applying
`G`. This is `map_sandwich`. -/
theorem bottom_map (G : C ⥤ D) {p q : ObjEq C} (f : p ⟶ q) :
    bottom ((map G).map f) = G.map (bottom f) :=
  (map_sandwich G p.eq q.eq f.top).symm

end ObjEq
