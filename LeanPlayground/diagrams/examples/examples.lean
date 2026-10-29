/-
# Examples

Worked examples for the diagrams framework.

* `UndercountExample`: a five-object diagram where adding one arrow creates three
  minimal cells, although a planar drawing shows only two new regions next
  to the arrow. By `closesMin_necessary`, checking the two regions is not
  enough. The shape conditions are all proved by `decide`.
* `RectExample`: Riehl's rectangle (1.6.10), built by hand on each layer: a
  recorded chase, the chase search, and commutativity by construction.
* `Rect` and `Cube`: the rectangle and Riehl's commutative cube (§1.6), declared
  with `diagram_shape`. Their equations follow in one line from the generated
  `commutes` theorems.
-/

import LeanPlayground.diagrams.minimal
import LeanPlayground.diagrams.chase
import LeanPlayground.diagrams.decide
import LeanPlayground.diagrams.tactics
import LeanPlayground.diagrams.command

open CategoryTheory Quiver

namespace Diagrams

universe v₂ u₂

/-! ## An example where a drawing undercounts

Take objects `s, u, v, t, y` with arrows `s ⟶ u`, `s ⟶ v`, `u ⟶ t`, `v ⟶ t`,
`u ⟶ y`, `v ⟶ y`, and add a new arrow `u ⟶ v`. In the drawing below, `u` sits
above `v`, with `t` to the left and `y` to the right, so the new arrow runs down
the middle and borders two regions: the triangle `u ⟶ t ⟵ v` on its left and
the triangle `u ⟶ y ⟵ v` on its right. These give the cells `(u, t)` and
`(u, y)`. But `(s, v)` is a minimal cell too: the new path
`s ⟶ u ⟶ v` is parallel to the old arrow `s ⟶ v`. By `closesMin_necessary`, the
two regions alone do not make the diagram commute.

[Diagram](assets/undercount.svg)
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

instance : NumShape K where
  size := 5
  index | .s => 0 | .u => 1 | .v => 2 | .t => 3 | .y => 4
  index_lt a := by cases a <;> decide
  vertexAt | 0 => .s | 1 => .u | 2 => .v | 3 => .t | _ => .y
  vertexAt_index a := by cases a <;> rfl

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

theorem hW {a b : K} (f : a ⟶ b) : f ∈ oldArrows a b ∨ IsArrow uv f := by
  cases f
  all_goals first
    | exact Or.inl (show KHom.old _ = true from rfl)
    | exact Or.inr .refl

theorem uv_not_old : uv ∉ oldArrows K.u K.v := Bool.false_ne_true

/-- `(s, v)` is a minimal cell for the new arrow `u ⟶ v`. -/
theorem minObl_sv : ClosesMin oldArrows K.u K.v K.s K.v := by decide

/-- The two cells that a planar drawing shows are minimal too. -/
theorem minObl_ut : ClosesMin oldArrows K.u K.v K.u K.t := by decide

theorem minObl_uy : ClosesMin oldArrows K.u K.v K.u K.y := by decide

/-- These three are all the minimal cells. -/
example (a b : K) : ClosesMin oldArrows K.u K.v a b ↔
    (a, b) = (K.s, K.v) ∨ (a, b) = (K.u, K.t) ∨ (a, b) = (K.u, K.y) := by
  revert a b; decide

/-- The old arrows are acyclic, and the new arrow closes no cycle. -/
example : AcyclicOn oldArrows ∧ ¬ ReachIn oldArrows K.v K.u := by decide

/-- The same facts by certificate: a rank for each vertex, and a fence around
everything reachable from `v`. -/
example : AcyclicOn oldArrows := by diagram_acyclic
example : ¬ ReachIn oldArrows K.v K.u := by diagram_unreachable

/-- There is a diagram of shape `K`, commuting on the old arrows, for which the
equations at `(u, t)` and `(u, y)` hold, yet the whole diagram does not
commute. -/
theorem two_regions_not_enough :
    ∃ G : K ⥤q Type, CommutesOn G oldArrows ∧
      CellHolds oldArrows uv G .u .t ∧ CellHolds oldArrows uv G .u .y ∧
        ¬ Commutes G := by
  obtain ⟨G, hG, hother, hfail⟩ := closesMin_necessary hW uv_not_old minObl_sv
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

[Diagram](assets/rectangle.svg)
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

instance : NumShape V where
  size := 6
  index | .a => 0 | .b => 1 | .c => 2 | .a' => 3 | .b' => 4 | .c' => 5
  index_lt x := by cases x <;> decide
  vertexAt | 0 => .a | 1 => .b | 2 => .c | 3 => .a' | 4 => .b' | _ => .c'
  vertexAt_index x := by cases x <;> rfl

instance : FinShape V where
  vertices := [.a, .b, .c, .a', .b', .c']
  mem_vertices x := by cases x <;> decide
  arrows := [arrow H.f, arrow H.j, arrow H.g, arrow H.h, arrow H.l, arrow H.k, arrow H.m]
  mem_arrows := fun ⟨_, _, e⟩ => by cases e <;> decide

/-- An arrow, as a path of length one. -/
def H.path {x y : V} (e : H x y) : Path x y := Quiver.Hom.toPath (V := V) e

/-- The two squares, as subshapes. -/
def leftSquare : Subshape V := ofList [arrow H.f, arrow H.g, arrow H.h, arrow H.k]
def rightSquare : Subshape V := ofList [arrow H.j, arrow H.h, arrow H.l, arrow H.m]

/-- The squares meet along the edge `h`, so they satisfy the chain condition, and
their union is acyclic: the hypotheses of `CommutesOn.paste`. -/
example : Chain leftSquare rightSquare ∧ AcyclicOn (leftSquare ⊔ rightSquare) := by
  unfold leftSquare rightSquare; decide

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

/-- The search finds the chase around the rectangle, and the kernel checks it by
replaying the script it found. -/
example : chaseCheck squares [.L, .R] 3 (H.f.path.comp (H.j.path.comp H.l.path))
    (H.g.path.comp (H.k.path.comp H.m.path)) = true := by decide

/-- With only the face `L` available, the search finds no chase around the
rectangle: the outer equation needs both faces. -/
example : chaseCheck squares [.L] 3 (H.f.path.comp (H.j.path.comp H.l.path))
    (H.g.path.comp (H.k.path.comp H.m.path)) = false := by decide

/-- The search run as compiled code by the `find_chase` tactic, with only the
replay of its script checked by the kernel. -/
example : Nonempty (Chase squares (H.f.path.comp (H.j.path.comp H.l.path))
    (H.g.path.comp (H.k.path.comp H.m.path))) := by
  find_chase [Cell.L, Cell.R] 100

/-- Riehl's rectangle again, with the chase found by search rather than written
by hand. -/
theorem rectangle_by_search (f : A ⟶ B) (j : B ⟶ E) (g : A ⟶ A') (h : B ⟶ B')
    (l : E ⟶ E') (k : A' ⟶ B') (m : B' ⟶ E') (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) :
    f ≫ j ≫ l = g ≫ k ≫ m := by
  have := eq_of_chaseCheck (G := diagram f j g h l k m) (faces := squares) (names := [.L, .R])
    (fuel := 3)
    (p := H.f.path.comp (H.j.path.comp H.l.path)) (q := H.g.path.comp (H.k.path.comp H.m.path))
    (fun φ => by
      cases φ
      · simpa [Face.Holds, squares, H.path, diagram] using hL
      · simpa [Face.Holds, squares, H.path, diagram] using hR)
    (by decide)
  simpa [H.path, diagram] using this

/-- The rectangle commutes by construction: adding the arrows `f, j, g, h, l, k, m`
in turn, `k` completes the square `L` and `m` completes `R`, and those two squares
supply every equation the arrows owe. -/
theorem rectangle_commutes (f : A ⟶ B) (j : B ⟶ E) (g : A ⟶ A') (h : B ⟶ B') (l : E ⟶ E')
    (k : A' ⟶ B') (m : B' ⟶ E') (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) :
    Commutes (diagram f j g h l k m) := by
  have hF : ∀ φ ∈ [squares .L, squares .R], φ.Holds (diagram f j g h l k m) := by
    intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · simpa [Face.Holds, squares, H.path, diagram] using hL
    · simpa [Face.Holds, squares, H.path, diagram] using hR
  exact commutes_of_commutesOn_ofList (commutesOn_of_build hF
    [(arrow H.m, [⟨1, true, 1⟩]), (arrow H.k, [⟨0, true, 1⟩]), (arrow H.l, []), (arrow H.h, []),
      (arrow H.g, []), (arrow H.j, []), (arrow H.f, [])] (by decide +kernel)) (by decide)

/-- The same, with the build found by the `diagram_build` tactic, and equations
read off with `diagram_eq`. -/
example (f : A ⟶ B) (j : B ⟶ E) (g : A ⟶ A') (h : B ⟶ B') (l : E ⟶ E')
    (k : A' ⟶ B') (m : B' ⟶ E') (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) :
    f ≫ j ≫ l = g ≫ k ≫ m := by
  have hF : ∀ φ ∈ [squares .L, squares .R], φ.Holds (diagram f j g h l k m) := by
    intro φ hφ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · simpa [Face.Holds, squares, H.path, diagram] using hL
    · simpa [Face.Holds, squares, H.path, diagram] using hR
  have hD : Commutes (diagram f j g h l k m) := by
    diagram_build [squares .L, squares .R] using hF
  diagram_eq hD

end RectExample

/-! ## Declared diagrams

The rectangle ([Diagram](assets/rectangle.svg)) and the cube
([Diagram](assets/cube.svg)). -/

diagram_shape Rect where
  arrows (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a') (h : b ⟶ b') (l : c ⟶ c')
    (k : a' ⟶ b') (m : b' ⟶ c')
  faces (L : f h = g k) (R : j l = h m)

example {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c')
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : f ≫ j ≫ l = g ≫ k ≫ m := by
  diagram_eq (Rect.commutes f j g h l k m hL hR)

-- Riehl's commutative cube: its six faces make it commute.
diagram_shape Cube where
  arrows (x₁ : o ⟶ X) (y₁ : o ⟶ Y) (z₁ : o ⟶ Z)
    (y₂ : X ⟶ XY) (z₂ : X ⟶ XZ) (x₂ : Y ⟶ XY) (z₃ : Y ⟶ YZ) (x₃ : Z ⟶ XZ) (y₃ : Z ⟶ YZ)
    (z₄ : XY ⟶ T) (y₄ : XZ ⟶ T) (x₄ : YZ ⟶ T)
  faces (Bot : x₁ y₂ = y₁ x₂) (Fr : x₁ z₂ = z₁ x₃) (Lt : y₁ z₃ = z₁ y₃)
    (Top : x₃ y₄ = y₃ x₄) (Bk : x₂ z₄ = z₃ x₄) (Rt : y₂ z₄ = z₂ y₄)

example {D : Type*} [Category D] {o X Y Z XY XZ YZ T : D}
    (x₁ : o ⟶ X) (y₁ : o ⟶ Y) (z₁ : o ⟶ Z) (y₂ : X ⟶ XY) (z₂ : X ⟶ XZ) (x₂ : Y ⟶ XY)
    (z₃ : Y ⟶ YZ) (x₃ : Z ⟶ XZ) (y₃ : Z ⟶ YZ) (z₄ : XY ⟶ T) (y₄ : XZ ⟶ T) (x₄ : YZ ⟶ T)
    (hBot : x₁ ≫ y₂ = y₁ ≫ x₂) (hFr : x₁ ≫ z₂ = z₁ ≫ x₃) (hLt : y₁ ≫ z₃ = z₁ ≫ y₃)
    (hTop : x₃ ≫ y₄ = y₃ ≫ x₄) (hBk : x₂ ≫ z₄ = z₃ ≫ x₄) (hRt : y₂ ≫ z₄ = z₂ ≫ y₄) :
    x₁ ≫ y₂ ≫ z₄ = z₁ ≫ y₃ ≫ x₄ := by
  diagram_eq (Cube.commutes x₁ y₁ z₁ y₂ z₂ x₂ z₃ x₃ y₃ z₄ y₄ x₄ hBot hFr hLt hTop hBk hRt)

/-! ### Inferred faces

Without a `faces` block, `diagram_shape` infers the faces, as the minimal
cells of adding the arrows in declared order. -/

-- The rectangle again: the inferred faces are its two squares.
/--
info: diagram_shape: inferred faces
h1 : g ≫ k = f ≫ h
h2 : h ≫ m = j ≫ l
-/
#guard_msgs in
diagram_shape RectInferred where
  arrows (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a') (h : b ⟶ b') (l : c ⟶ c')
    (k : a' ⟶ b') (m : b' ⟶ c')

-- A square `s ⇉ t` through `a` and `b`, with a vertex `m` inside mapping to both.
-- The cell `s → a ← m → b ← s` is a zigzag: its boundary is not two parallel paths,
-- so it asserts nothing. The faces are the cell `m ⇉ t` and the outer square, which
-- the inner cell does not imply. [Diagram](assets/zigzag.svg)
/--
info: diagram_shape: inferred faces
h1 : q ≫ y = p ≫ x
h2 : w ≫ y = u ≫ x
-/
#guard_msgs in
diagram_shape Zigzag where
  arrows (p : s ⟶ a) (q : s ⟶ b) (u : m ⟶ a) (w : m ⟶ b) (x : a ⟶ t) (y : b ⟶ t)

-- In this order, `m` arrives before `h`, so its equation is the outer rectangle,
-- which neither square gives until `h` is present. The arrows are numbered in
-- declared order: [Diagram](assets/rectangle_bad_order.svg)
/--
error: diagram_shape: adding m closes the cell
  g ≫ k ≫ m = f ≫ j ≫ l
which no face it completes covers. Either the faces do not imply it, so it must be added as a face, or the faces that imply it contain arrows declared after m, and another order of the arrows avoids it.
-/
#guard_msgs in
diagram_shape RectBadOrder where
  arrows (f : a ⟶ b) (j : b ⟶ c) (l : c ⟶ c') (g : a ⟶ a') (k : a' ⟶ b') (m : b' ⟶ c')
    (h : b ⟶ b')
  faces (L : f h = g k) (R : j l = h m)

-- The cube, with faces inferred.
diagram_shape CubeInferred where
  arrows (x₁ : o ⟶ X) (y₁ : o ⟶ Y) (z₁ : o ⟶ Z)
    (y₂ : X ⟶ XY) (z₂ : X ⟶ XZ) (x₂ : Y ⟶ XY) (z₃ : Y ⟶ YZ) (x₃ : Z ⟶ XZ) (y₃ : Z ⟶ YZ)
    (z₄ : XY ⟶ T) (y₄ : XZ ⟶ T) (x₄ : YZ ⟶ T)

end Diagrams
