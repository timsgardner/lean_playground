/-
# Diagram tools: a test bench

Each example below puts a square or a triangle into the infoview. To check a
presenter, place the cursor on the line marked `-- cursor here`, then
shift-click the type of the named hypothesis or of the goal in the infoview.
The selection panel lists the presenters that apply; pick the one named in the
comment. The examples use distinct object names `A B C D` so that a misplaced
corner or edge is easy to spot.
-/

import LeanPlayground.Scratch.category_kindergarten.diagram_tools

open CategoryTheory

show_panel_widgets [local ProofWidgets.SelectionPanel]

variable {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}

/-
Test 1: "CommSq diagram" on the hypothesis `sq`. Expect `A` at the top left,
`B` at the top right, `C` at the bottom left, and `D` at the bottom right, with
`top : A ⟶ B` along the top, `left : A ⟶ C` down the left side,
`right : B ⟶ D` down the right side, and `bottom : C ⟶ D` along the bottom.
-/
example (top : A ⟶ B) (left : A ⟶ C) (right : B ⟶ D) (bottom : C ⟶ D)
    (sq : CommSq top left right bottom) : top ≫ right = left ≫ bottom := by
  -- cursor here
  exact sq.w

/-
Test 2: "CommSq diagram" on the goal. Expect the same square as in Test 1.
-/
example (top : A ⟶ B) (left : A ⟶ C) (right : B ⟶ D) (bottom : C ⟶ D)
    (w : top ≫ right = left ≫ bottom) : CommSq top left right bottom := by
  -- cursor here
  exact ⟨w⟩

/-
Test 3: Mathlib's "Commutative square" on the hypothesis `w`, an equation
`top ≫ right = left ≫ bottom`. Expect the same square as in Test 1.
-/
example (top : A ⟶ B) (left : A ⟶ C) (right : B ⟶ D) (bottom : C ⟶ D)
    (w : top ≫ right = left ≫ bottom) : CommSq top left right bottom := by
  -- cursor here
  exact ⟨w⟩

/-
Test 4: Mathlib's "Commutative triangle" on the hypothesis `w`, an equation
`f ≫ g = h`. Expect `f : A ⟶ B` and `g : B ⟶ C` along two sides, and
`h : A ⟶ C` along the third.
-/
example (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (w : f ≫ g = h) : f ≫ g = h := by
  -- cursor here
  exact w

/-
Test 5: "CommSq diagram" on a square whose sides are composites and functor
images, the shape that appears in Lemma 4.1.3. Expect `F.obj A` top left,
`F.obj B` top right, and `F.map u`, `F.map v`, `p ≫ q`, `r` as the top, left,
right, and bottom sides. "Commutative square" on the goal should draw the same
square.
-/
example {𝒟 : Type*} [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {X Y : 𝒟}
    (u : A ⟶ B) (v : A ⟶ C) (p : F.obj B ⟶ X) (q : X ⟶ Y) (r : F.obj C ⟶ Y)
    (sq : CommSq (F.map u) (F.map v) (p ≫ q) r) : F.map u ≫ p ≫ q = F.map v ≫ r := by
  -- cursor here
  exact sq.w
