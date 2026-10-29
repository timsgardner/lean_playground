/-
# Examples

Worked examples for the diagrams framework.

* `UndercountExample`: a five-object diagram where adding one arrow creates three
  minimal obligations, although a planar drawing shows only two new regions next
  to the arrow. By `isMinObligation_necessary`, checking the two regions is not
  enough.
* `RectExample`: Riehl's rectangle (1.6.10), proved by replaying the recorded
  two-step chase `f ◁ R`, then `L ▷ m`.
-/

import LeanPlayground.diagrams.extend
import LeanPlayground.diagrams.chase
import LeanPlayground.diagrams.finite

open CategoryTheory Quiver

namespace Diagrams

universe v₂ u₂

/-! ## An example where a drawing undercounts

Take objects `s, u, v, t, y` with arrows `s ⟶ u`, `s ⟶ v`, `u ⟶ t`, `v ⟶ t`,
`u ⟶ y`, `v ⟶ y`, and add a new arrow `u ⟶ v`. Drawn in the plane with the new
arrow between `t` and `y`, it borders two regions, which give the obligations
`(u, t)` and `(u, y)`. But `(s, v)` is a minimal obligation too: the new path
`s ⟶ u ⟶ v` is parallel to the old arrow `s ⟶ v`. By `isMinObligation_necessary`, the
two regions alone do not make the diagram commute.
-/

namespace UndercountExample

/-- The five objects. -/
inductive K | s | u | v | t | y
  deriving DecidableEq

/-- The six old arrows and the new arrow `uv`. -/
inductive KHom : K → K → Type
  | su : KHom .s .u
  | sv : KHom .s .v
  | ut : KHom .u .t
  | vt : KHom .v .t
  | uy : KHom .u .y
  | vy : KHom .v .y
  | uv : KHom .u .v
  deriving DecidableEq

instance : Quiver K := ⟨KHom⟩

instance (a b : K) : DecidableEq (a ⟶ b) := inferInstanceAs (DecidableEq (KHom a b))

instance : FinShape K where
  vertices := [.s, .u, .v, .t, .y]
  mem_vertices a := by cases a <;> decide
  arrows := [arrow KHom.su, arrow KHom.sv, arrow KHom.ut, arrow KHom.vt, arrow KHom.uy,
    arrow KHom.vy, arrow KHom.uv]
  mem_arrows := fun ⟨_, _, f⟩ => by cases f <;> decide

/-- Whether an arrow is one of the six old ones. -/
def KHom.old {a b : K} : KHom a b → Bool
  | .uv => false
  | _ => true

/-- The subshape of old arrows. -/
def oldArrows : Subshape K := fun a b => {f : a ⟶ b | KHom.old f = true}

instance {a b : K} {f : a ⟶ b} : Decidable (f ∈ oldArrows a b) :=
  inferInstanceAs (Decidable (KHom.old f = true))

/-- The old arrows are the arrows of the shape other than `uv`. -/
example : oldArrows = ofList (FinShape.arrows.filter (· != arrow KHom.uv)) := by
  funext a b; ext f; cases f <;> decide

/-- Membership of a path in a subshape is decidable. -/
example : Within oldArrows
    ((Quiver.Hom.toPath (V := K) KHom.su).comp (Quiver.Hom.toPath (V := K) KHom.ut)) := by
  decide

example : ¬ Within oldArrows
    ((Quiver.Hom.toPath (V := K) KHom.su).comp (Quiver.Hom.toPath (V := K) KHom.uv)) := by
  decide

/-- The new arrow. -/
def uv : K.u ⟶ K.v := KHom.uv

/-- An arrow, as a path of length one. -/
def KHom.path {a b : K} (f : KHom a b) : Path a b := Quiver.Hom.toPath (V := K) f

theorem KHom.within {a b : K} (f : KHom a b) (h : f.old = true := by rfl) :
    Within oldArrows f.path := Within.toPath h

theorem KHom.reach {a b : K} (f : KHom a b) (h : f.old = true := by rfl) :
    ReachIn oldArrows a b := ⟨f.path, f.within h⟩

/-- Reachability along old arrows, as a table. -/
def R : K → K → Bool
  | .s, _ => true
  | .u, b => b == .u || b == .t || b == .y
  | .v, b => b == .v || b == .t || b == .y
  | .t, b => b == .t
  | .y, b => b == .y

theorem R_of_reachIn {a b : K} : ReachIn oldArrows a b → R a b = true
  | ⟨_, hp⟩ => by
    induction hp with
    | nil => cases a <;> rfl
    | @cons b c p f _ hf ih =>
      cases f
      all_goals first
        | exact absurd hf Bool.false_ne_true
        | (revert ih; cases a <;> decide)

theorem hW {a b : K} (f : a ⟶ b) : f ∈ oldArrows a b ∨ IsArrow uv f := by
  cases f
  all_goals first
    | exact Or.inl (show KHom.old _ = true from rfl)
    | exact Or.inr .refl

theorem uv_not_old : uv ∉ oldArrows K.u K.v := Bool.false_ne_true

/-- Decide minimality of an obligation from the reachability table. -/
macro "min_obl_by_table" : tactic => `(tactic| (
  rintro x₀ y₀ ⟨h₁, h₂, h₃⟩ h₄ h₅
  have r₁ := R_of_reachIn h₁; have r₂ := R_of_reachIn h₂; have r₃ := R_of_reachIn h₃
  have r₄ := R_of_reachIn h₄; have r₅ := R_of_reachIn h₅
  clear h₁ h₂ h₃ h₄ h₅
  revert r₁ r₂ r₃ r₄ r₅
  cases x₀ <;> cases y₀ <;> decide))

/-- `(s, v)` is a minimal obligation for the new arrow `u ⟶ v`. -/
theorem minObl_sv : IsMinObligation oldArrows K.u K.v K.s K.v :=
  ⟨⟨KHom.su.reach, ReachIn.refl _, KHom.sv.reach⟩, by min_obl_by_table⟩

/-- The two obligations that a planar drawing shows are minimal too. -/
theorem minObl_ut : IsMinObligation oldArrows K.u K.v K.u K.t :=
  ⟨⟨ReachIn.refl _, KHom.vt.reach, KHom.ut.reach⟩, by min_obl_by_table⟩

theorem minObl_uy : IsMinObligation oldArrows K.u K.v K.u K.y :=
  ⟨⟨ReachIn.refl _, KHom.vy.reach, KHom.uy.reach⟩, by min_obl_by_table⟩

/-- There is a diagram of shape `K`, commuting on the old arrows, for which the
equations at `(u, t)` and `(u, y)` hold, yet the whole diagram does not
commute. -/
theorem two_regions_not_enough :
    ∃ G : K ⥤q Type, CommutesOn G oldArrows ∧
      ObligationHolds oldArrows uv G .u .t ∧ ObligationHolds oldArrows uv G .u .y ∧
        ¬ Commutes G := by
  obtain ⟨G, hG, hother, hfail⟩ := isMinObligation_necessary hW uv_not_old minObl_sv
  refine ⟨G, hG, ?_, ?_, fun h => hfail ?_⟩
  · exact ⟨⟨.nil, KHom.vt.path, KHom.ut.path, .nil, KHom.vt.within, KHom.ut.within⟩,
      hother _ _ minObl_ut.1 (by decide) .nil KHom.vt.within KHom.ut.within⟩
  · exact ⟨⟨.nil, KHom.vy.path, KHom.uy.path, .nil, KHom.vy.within, KHom.uy.within⟩,
      hother _ _ minObl_uy.1 (by decide) .nil KHom.vy.within KHom.uy.within⟩
  · exact ⟨⟨KHom.su.path, .nil, KHom.sv.path, KHom.su.within, .nil, KHom.sv.within⟩,
      CommutesOn.eq_of_sup_single (h.commutesOn _) KHom.su.within .nil KHom.sv.within⟩

end UndercountExample

/-! ## Example: Riehl's rectangle (1.6.10)

```
        f         j
   a ──────▶ b ──────▶ c
   │         │         │
 g │    L    │ h   R   │ ℓ
   ▼         ▼         ▼
   a'──────▶ b'──────▶ c'
        k         m
```
-/

namespace RectExample

/-- The six objects. -/
inductive V | a | b | c | a' | b' | c'
  deriving DecidableEq

/-- The seven arrows. -/
inductive H : V → V → Type
  | f : H .a .b
  | j : H .b .c
  | g : H .a .a'
  | h : H .b .b'
  | l : H .c .c'
  | k : H .a' .b'
  | m : H .b' .c'
  deriving DecidableEq

instance : Quiver V := ⟨H⟩

instance (x y : V) : DecidableEq (x ⟶ y) := inferInstanceAs (DecidableEq (H x y))

instance : FinShape V where
  vertices := [.a, .b, .c, .a', .b', .c']
  mem_vertices x := by cases x <;> decide
  arrows := [arrow H.f, arrow H.j, arrow H.g, arrow H.h, arrow H.l, arrow H.k, arrow H.m]
  mem_arrows := fun ⟨_, _, e⟩ => by cases e <;> decide

/-- An arrow, as a path of length one. -/
def H.path {x y : V} (e : H x y) : Path x y := Quiver.Hom.toPath (V := V) e

/-- The names of the two faces. -/
inductive Cell | L | R
  deriving DecidableEq

/-- The two squares. -/
def squares : Cell → Face V
  | .L => ⟨.a, .b', H.f.path.comp H.h.path, H.g.path.comp H.k.path⟩
  | .R => ⟨.b, .c', H.j.path.comp H.l.path, H.h.path.comp H.m.path⟩

/-- The chase around the rectangle: apply `R` after `f`, then `L` before `m`. -/
def outer :
    Chase squares (H.f.path.comp (H.j.path.comp H.l.path))
      (H.g.path.comp (H.k.path.comp H.m.path)) :=
  .cons ⟨.R, false, H.f.path, .nil, rfl, rfl⟩ <|
  .cons ⟨.L, false, .nil, H.m.path, rfl, rfl⟩ <|
  .refl _

/-- The chase uses `R`, then `L`. -/
example : outer.used = [.R, .L] := rfl

variable {D : Type u₂} [Category.{v₂} D] {A B E A' B' E' : D}

/-- The rectangle in `D` with the given sides. -/
def diagram (f : A ⟶ B) (j : B ⟶ E) (g : A ⟶ A') (h : B ⟶ B') (l : E ⟶ E')
    (k : A' ⟶ B') (m : B' ⟶ E') : V ⥤q D where
  obj
    | .a => A | .b => B | .c => E
    | .a' => A' | .b' => B' | .c' => E'
  map {x y} (e : H x y) := match e with
    | .f => f | .j => j | .g => g | .h => h | .l => l | .k => k | .m => m

/-- Two commutative squares give a commutative rectangle, by replaying the
recorded chase. -/
theorem rectangle (f : A ⟶ B) (j : B ⟶ E) (g : A ⟶ A') (h : B ⟶ B') (l : E ⟶ E')
    (k : A' ⟶ B') (m : B' ⟶ E') (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) :
    f ≫ j ≫ l = g ≫ k ≫ m := by
  have := outer.sound (G := diagram f j g h l k m) (by
    intro φ _
    cases φ
    · simpa [Face.Holds, squares, H.path, diagram] using hL
    · simpa [Face.Holds, squares, H.path, diagram] using hR)
  simpa [H.path, diagram] using this

end RectExample

end Diagrams
