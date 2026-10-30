/-
# Examples

Worked examples for the diagrams framework.

* `UndercountExample`: a five-object diagram where adding one arrow creates three
  minimal cells, although a planar drawing shows only two new regions next
  to the arrow. By `closesMin_necessary`, checking the two regions is not
  enough. The shape conditions are all proved by `decide`.
* `RectExample`: Riehl's rectangle (1.6.10), built by hand on each layer: a
  recorded chase, the chase search, and commutativity by construction.
* Diagrams built inside proofs with `comm_diagram`, from equations already known,
  and equations read off them with `diagram_eq`: the rectangle, naturality squares,
  Riehl's commutative cube, a square with a diagonal, gluing and extending diagrams,
  and the error messages when building or reading fails.
-/

import LeanPlayground.diagrams.minimal
import LeanPlayground.diagrams.chase
import LeanPlayground.diagrams.decide
import LeanPlayground.diagrams.tactics
import LeanPlayground.diagrams.widget

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

/-! ## Diagrams built inside proofs

`comm_diagram [h₁, …]` builds a commuting diagram from equations between composites
that are already known, as a value of type `CommDiagram C`; bind it with `let`.
`diagram_eq D` then proves any equation whose two sides are paths in the diagram
`D`. No diagram is declared beforehand. In the infoview a diagram displays as
`⟪diagram f, g, …⟫`; to draw it, shift-click `D` and choose "Commuting diagram". -/

show_panel_widgets [local ProofWidgets.SelectionPanel]

-- The rectangle ([Diagram](assets/rectangle.svg)): two squares make the outer
-- rectangle commute.
example {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c')
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : f ≫ j ≫ l = g ≫ k ≫ m := by
  let D := comm_diagram [hL, hR]
  diagram_eq D

-- The bracketing and identities of the goal do not matter.
example {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c')
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : (f ≫ j) ≫ l = g ≫ (k ≫ 𝟙 _) ≫ m := by
  let D := comm_diagram [hL, hR]
  diagram_eq D

-- Naturality squares: the composite of two natural transformations is natural.
example {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ α.app Y ≫ β.app Y = (α.app X ≫ β.app X) ≫ H.map f := by
  let D := comm_diagram [α.naturality f, β.naturality f]
  diagram_eq D

-- Riehl's commutative cube ([Diagram](assets/cube.svg)): its six faces make it
-- commute, so the paths through opposite corners agree.
example {D : Type*} [Category D] {o X Y Z XY XZ YZ T : D}
    (x₁ : o ⟶ X) (y₁ : o ⟶ Y) (z₁ : o ⟶ Z) (y₂ : X ⟶ XY) (z₂ : X ⟶ XZ) (x₂ : Y ⟶ XY)
    (z₃ : Y ⟶ YZ) (x₃ : Z ⟶ XZ) (y₃ : Z ⟶ YZ) (z₄ : XY ⟶ T) (y₄ : XZ ⟶ T) (x₄ : YZ ⟶ T)
    (hBot : x₁ ≫ y₂ = y₁ ≫ x₂) (hFr : x₁ ≫ z₂ = z₁ ≫ x₃) (hLt : y₁ ≫ z₃ = z₁ ≫ y₃)
    (hTop : x₃ ≫ y₄ = y₃ ≫ x₄) (hBk : x₂ ≫ z₄ = z₃ ≫ x₄) (hRt : y₂ ≫ z₄ = z₂ ≫ y₄) :
    x₁ ≫ y₂ ≫ z₄ = z₁ ≫ y₃ ≫ x₄ := by
  let D := comm_diagram [hBot, hFr, hLt, hTop, hBk, hRt]
  diagram_eq D

-- A square with a diagonal: two triangles make the square commute.
example {D : Type*} [Category D] {a b c d : D} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ d)
    (k : d ⟶ c) (e : a ⟶ c) (h₁ : f ≫ g = e) (h₂ : h ≫ k = e) : f ≫ g = h ≫ k := by
  let D := comm_diagram [h₁, h₂]
  diagram_eq D

/-! ### Gluing and extending diagrams

`glue D₁ D₂` glues two diagrams along the objects and morphisms they share. Neither
piece is checked again: the result commutes by one theorem, whose conditions on the
graphs the kernel decides. A diagram can also be given to `comm_diagram`, together
with other diagrams and equations, which extends it. -/

-- Two squares, built separately, glued along the shared edge `h`.
example {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c')
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : f ≫ j ≫ l = g ≫ k ≫ m := by
  let D₁ := comm_diagram [hL]
  let D₂ := comm_diagram [hR]
  let D := glue D₁ D₂
  diagram_eq D

-- Three squares in a row: a glued diagram can be glued again.
example {D : Type*} [Category D] {a b c d a' b' c' d' : D} (f : a ⟶ b) (j : b ⟶ c)
    (r : c ⟶ d) (g : a ⟶ a') (h : b ⟶ b') (l : c ⟶ c') (t : d ⟶ d') (k : a' ⟶ b')
    (m : b' ⟶ c') (s : c' ⟶ d') (h₁ : f ≫ h = g ≫ k) (h₂ : j ≫ l = h ≫ m)
    (h₃ : r ≫ t = l ≫ s) : f ≫ j ≫ r ≫ t = g ≫ k ≫ m ≫ s := by
  let D₁ := comm_diagram [h₁]
  let D₂ := comm_diagram [h₂]
  let D₃ := comm_diagram [h₃]
  let D := glue (glue D₁ D₂) D₃
  diagram_eq D

-- A diagram extended by a new arrow `p` and the triangle it closes.
example {D : Type*} [Category D] {a b c a' b' c' e : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c') (n : c' ⟶ e) (p : b' ⟶ e)
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) (hT : m ≫ n = p) :
    f ≫ j ≫ l ≫ n = g ≫ k ≫ p := by
  let D₁ := comm_diagram [hL, hR]
  let D := comm_diagram [D₁, hT]
  diagram_eq D

/-! ### When building or reading fails -/

-- The equations must make the whole diagram commute. Here the outer rectangle and
-- the left square are given, but nothing relates the two routes from `b` to `c'`.
section
variable {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
  (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c')
  (hL : f ≫ h = g ≫ k) (hO : f ≫ j ≫ l = g ≫ k ≫ m)
/--
error: comm_diagram: the equations do not make the diagram commute. These two parallel routes are related by no equation:
  h ≫ m
  j ≫ l
-/
#guard_msgs in
#check comm_diagram [hL, hO]
end

-- Two squares that share only two opposite corners do not glue: the route through
-- each square from `a` to `d` is related to the other by no equation.
section
variable {D : Type*} [Category D] {a b c d x y : D} (f : a ⟶ x) (g : x ⟶ d) (f' : a ⟶ y)
  (g' : y ⟶ d) (p : a ⟶ b) (q : b ⟶ d) (p' : a ⟶ c) (q' : c ⟶ d)
  (h₁ : f ≫ g = p ≫ q) (h₂ : f' ≫ g' = p' ≫ q')
/--
error: glue: the diagrams share the objects a and d, but no route of morphisms common to both joins them, so the glued diagram need not commute. To relate the routes by an equation h, use comm_diagram [D₁, D₂, h].
-/
#guard_msgs (error, drop info) in
#check glue (comm_diagram [h₁]) (comm_diagram [h₂])
end

-- Both sides of the goal must be paths in the diagram.
/--
error: diagram_eq: the right side is not a path in the diagram: n is not one of its morphisms
-/
#guard_msgs in
example {D : Type*} [Category D] {a b c a' b' c' : D} (f : a ⟶ b) (j : b ⟶ c) (g : a ⟶ a')
    (h : b ⟶ b') (l : c ⟶ c') (k : a' ⟶ b') (m : b' ⟶ c') (n : a ⟶ c')
    (hL : f ≫ h = g ≫ k) (hR : j ≫ l = h ≫ m) : f ≫ j ≫ l = n := by
  let D := comm_diagram [hL, hR]
  diagram_eq D

end Diagrams
