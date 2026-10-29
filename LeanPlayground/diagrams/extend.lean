/-
# Adding one arrow to a commuting diagram

Riehl (§1.6) observes that commutativity of a diagram can usually be checked
one minimal subdiagram at a time. This file makes one precise version of that
observation, phrased as an inductive step: if a diagram commutes on a subshape
`S`, and we add one more arrow `e : u ⟶ v`, which equations must we check so
that it commutes on `S ⊔ single e`?

The new arrow *closes a cell* at a pair of vertices `(x, y)` (`Closes`) when
there are paths `x ⇝ u`, `v ⇝ y` and `x ⇝ y` within `S`: then the new path
`x ⇝ u ⟶ v ⇝ y` is parallel to an old one, and the two must agree. A cell with
its witness paths is a `ClosedCell`; `CellHolds` says that some witness of the
cell at `(x, y)` holds in `G`. A cell that holds implies every cell outside it,
by whiskering (`CellHolds.extend`). So `G` commutes on `S ⊔ single e` as soon as
every cell lies outside one that holds (`CommutesOn.sup_single_of_cover`).

The minimal cells, which are exactly the ones needed, are in `minimal`.
-/

import LeanPlayground.diagrams.core

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

/-! ## Cells -/

/-- A new arrow `u ⟶ v` closes a cell at `(x, y)` when it creates a path from `x`
to `y` parallel to one within `S`. -/
def Closes (S : Subshape W) (u v x y : W) : Prop :=
  ReachIn S x u ∧ ReachIn S v y ∧ ReachIn S x y

/-- A cell is minimal when no other cell lies below (inside) it: one at `(x₀, y₀)`
with `x ⇝ x₀` and `y₀ ⇝ y`. -/
def ClosesMin (S : Subshape W) (u v x y : W) : Prop :=
  Closes S u v x y ∧
    ∀ x₀ y₀, Closes S u v x₀ y₀ → ReachIn S x x₀ → ReachIn S y₀ y → x₀ = x ∧ y₀ = y

/-- A cell closed by the new arrow `e` at `(x, y)`, with its witnesses: paths `α` into
the source of `e`, `β` out of its target, and a parallel path `γ`, all within `S`. -/
structure ClosedCell (S : Subshape W) {u v : W} (_e : u ⟶ v) (x y : W) where
  /-- The path into the source of `e`. -/
  α : Path x u
  /-- The path out of the target of `e`. -/
  β : Path v y
  /-- The old path the new one must agree with. -/
  γ : Path x y
  hα : Within S α
  hβ : Within S β
  hγ : Within S γ

namespace ClosedCell

variable {S : Subshape W} {u v : W} {e : u ⟶ v} {x y : W}

/-- The face a cell states: the new path `α ⟶ e ⟶ β` against `γ`. -/
def face (o : ClosedCell S e x y) : Face W := ⟨x, y, o.α.comp (e.toPath.comp o.β), o.γ⟩

/-- The cell's equation holds in `G`. -/
abbrev Holds (G : W ⥤q C) (o : ClosedCell S e x y) : Prop :=
  eval G o.α ≫ G.map e ≫ eval G o.β = eval G o.γ

theorem holds_iff_face {G : W ⥤q C} (o : ClosedCell S e x y) : o.Holds G ↔ o.face.Holds G := by
  simp [face, Face.Holds]

/-- A witnessed cell is a cell. -/
theorem closes (o : ClosedCell S e x y) : Closes S u v x y :=
  ⟨⟨o.α, o.hα⟩, ⟨o.β, o.hβ⟩, ⟨o.γ, o.hγ⟩⟩

end ClosedCell

/-- The equation holds at `(x, y)`: some cell there holds in `G`. When `G`
commutes on `S`, one instance is as good as all of them (see `CellHolds.extend`). -/
def CellHolds (S : Subshape W) {u v : W} (e : u ⟶ v) (G : W ⥤q C) (x y : W) : Prop :=
  ∃ o : ClosedCell S e x y, o.Holds G

/-! ## Adding the arrow -/

section Extend

variable {G : W ⥤q C} {S : Subshape W} {u v : W} {e : u ⟶ v}

/-- Since there is no path from `v` back to `u`, a path within `S ⊔ single e`
uses `e` at most once. So its composite is either that of a path within `S`, or
of the form `α ≫ e ≫ β` for paths `α` and `β` within `S`. -/
theorem eval_old_or_new (huv : ¬ ReachIn S v u) {a b : W} {p : Path a b}
    (hp : Within (S ⊔ single e) p) :
    (∃ q : Path a b, Within S q ∧ eval G p = eval G q) ∨
    (∃ (α : Path a u) (β : Path v b), Within S α ∧ Within S β ∧
      eval G p = eval G α ≫ G.map e ≫ eval G β) := by
  induction hp with
  | nil => exact Or.inl ⟨.nil, .nil, rfl⟩
  | @cons b c p f _ hf ih =>
    rcases mem_sup.1 hf with hf | hf
    · rcases ih with ⟨q, hq, h⟩ | ⟨α, β, hα, hβ, h⟩
      · exact Or.inl ⟨q.cons f, hq.cons hf, by rw [eval_cons, eval_cons, h]⟩
      · exact Or.inr ⟨α, β.cons f, hα, hβ.cons hf, by simp [h]⟩
    · obtain ⟨⟩ : IsArrow e f := hf
      rcases ih with ⟨q, hq, h⟩ | ⟨_, β, _, hβ, _⟩
      · exact Or.inr ⟨q, .nil, hq, .nil, by simp [h]⟩
      · exact absurd ⟨β, hβ⟩ huv

/-- **Extending a cell.** If a cell closed by `e` at `(x', y')` holds, then every
cell closed by `e` at a pair `(x, y)` outside it holds, whatever its witness paths.
The cell is whiskered by paths `x ⇝ x'` and `y' ⇝ y` (Riehl's Lemma 1.6.11), and
the old paths are then exchanged for the given ones, since `G` commutes on `S`. -/
theorem CellHolds.extend {x y x' y' : W} (h : CellHolds S e G x' y') (hD : CommutesOn G S)
    (hx : ReachIn S x x') (hy : ReachIn S y' y) {α : Path x u} {β : Path v y}
    {γ : Path x y} (hα : Within S α) (hβ : Within S β) (hγ : Within S γ) :
    eval G α ≫ G.map e ≫ eval G β = eval G γ := by
  obtain ⟨ρ, hρ⟩ := hx
  obtain ⟨σ, hσ⟩ := hy
  obtain ⟨⟨α', β', γ', hα', hβ', hγ'⟩, h⟩ := h
  rw [hD α (ρ.comp α') hα (hρ.comp hα'), hD β (β'.comp σ) hβ (hβ'.comp hσ),
    hD γ (ρ.comp (γ'.comp σ)) hγ (hρ.comp (hγ'.comp hσ))]
  simp only [eval_comp, Category.assoc]
  rw [← h]
  simp only [Category.assoc]

/-- If `G` commutes on `S`, and every cell lies above one whose equation
has been checked, then `G` commutes on `S ⊔ single e`. -/
theorem CommutesOn.sup_single_of_cover (hD : CommutesOn G S) (huv : ¬ ReachIn S v u)
    (hcov : ∀ x y, Closes S u v x y →
      ∃ x' y', ReachIn S x x' ∧ ReachIn S y' y ∧ CellHolds S e G x' y') :
    CommutesOn G (S ⊔ single e) := by
  have key : ∀ {x y : W} {α : Path x u} {β : Path v y} {γ : Path x y},
      Within S α → Within S β → Within S γ → eval G α ≫ G.map e ≫ eval G β = eval G γ := by
    intro x y α β γ hα hβ hγ
    obtain ⟨x', y', hx, hy, h⟩ := hcov x y ⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩⟩
    exact h.extend hD hx hy hα hβ hγ
  intro a b p q hp hq
  rcases eval_old_or_new (G := G) huv hp with ⟨p', hp', h₁⟩ | ⟨α, β, hα, hβ, h₁⟩ <;>
  rcases eval_old_or_new (G := G) huv hq with ⟨q', hq', h₂⟩ | ⟨α', β', hα', hβ', h₂⟩ <;>
  rw [h₁, h₂]
  · exact hD _ _ hp' hq'
  · exact (key hα' hβ' hp').symm
  · exact key hα hβ hq'
  · rw [hD α α' hα hα', hD β β' hβ hβ']

/-- Conversely, if `G` commutes on `S ⊔ single e`, the equation holds at every
cell. -/
theorem CommutesOn.eq_of_sup_single (h : CommutesOn G (S ⊔ single e)) {x y : W}
    {α : Path x u} {β : Path v y} {γ : Path x y}
    (hα : Within S α) (hβ : Within S β) (hγ : Within S γ) :
    eval G α ≫ G.map e ≫ eval G β = eval G γ := by
  have := h (α.comp (e.toPath.comp β)) γ
    ((hα.mono le_sup_left).comp
      ((Within.toPath (mem_sup.2 (Or.inr (mem_single_self e)))).comp (hβ.mono le_sup_left)))
    (hγ.mono le_sup_left)
  simpa using this

end Extend

end Diagrams
