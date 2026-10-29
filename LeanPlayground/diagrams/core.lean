/-
# Diagrams and commutativity

This file is the interface for the commutative-diagram development. Everything
else is stated in its terms.

A *diagram* in a category `C` is a prefunctor `G : W ⥤q C` from a quiver `W`, its
*shape*. Riehl (Definition 1.6.4) asks for a functor out of a category; a
prefunctor out of a quiver is the same thing as a functor out of the free
category on that quiver, which is how diagrams are usually drawn: as arrows,
with the commutativity conditions stated separately.

The composite of a path `p` in `W` is `eval G p`. A diagram *commutes on* a
subshape `S` (a choice of some arrows of `W`) when any two parallel paths built
from arrows of `S` have the same composite. Working with subshapes of one
ambient shape lets results compose: the theorems elsewhere have the form "if `G`
commutes on `S`, then `G` commutes on a larger subshape", so a proof that a
large diagram commutes can be assembled from the empty subshape, by adding
arrows (`extend`) and pasting (`paste`).

The basic facts here are:

* `CommutesOn.mono`: commuting on `T` implies commuting on any `S ≤ T`;
* `commutesOn_bot`: every diagram commutes on the empty subshape;
* `CommutesOn.map`: functors preserve commutativity (Riehl, Lemma 1.6.5);
* `CommutesOn.of_map`: faithful functors reflect it (Riehl, Lemma 1.6.20).

A `Face` names two parallel paths, and `Face.Holds G` says they have the same
composite. Faces are the vocabulary shared by cells (`extend`) and chases
(`chase`).
-/

import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {W : Type u₁} [Quiver.{v₁} W]
variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

/-! ## Composites of paths -/

/-- The composite in `C` of the image of a path under `G`. -/
def eval (G : W ⥤q C) {a : W} : ∀ {b : W}, Path a b → (G.obj a ⟶ G.obj b)
  | _, .nil => 𝟙 _
  | _, .cons p f => eval G p ≫ G.map f

section Eval

variable (G : W ⥤q C)

@[simp] theorem eval_nil (a : W) : eval G (Path.nil : Path a a) = 𝟙 _ := rfl

@[simp] theorem eval_cons {a b c : W} (p : Path a b) (f : b ⟶ c) :
    eval G (p.cons f) = eval G p ≫ G.map f := rfl

@[simp] theorem eval_comp {a b : W} (p : Path a b) : ∀ {d : W} (q : Path b d),
    eval G (p.comp q) = eval G p ≫ eval G q
  | _, .nil => by simp
  | _, .cons q f => by rw [Path.comp_cons, eval_cons, eval_cons, eval_comp p q, Category.assoc]

@[simp] theorem eval_toPath {a b : W} (f : a ⟶ b) : eval G f.toPath = G.map f := by
  simp [Quiver.Hom.toPath]

/-- The composite of a path in the image of a functor is the image of its
composite. -/
@[simp] theorem eval_map (F : C ⥤ D) {a b : W} (p : Path a b) :
    eval (G ⋙q F.toPrefunctor) p = F.map (eval G p) := by
  induction p with
  | nil => simp; rfl
  | cons p f ih => simp [ih]; rfl

end Eval

/-! ## Subshapes -/

/-- A subshape of `W` chooses some of the arrows between each pair of vertices.
This is Mathlib's `WideSubquiver W`, restated as an `abbrev` so that it inherits
the lattice structure of `∀ a b, Set (a ⟶ b)`: `S ≤ T`, `S ⊔ T`, `⊥` and `⊤`. -/
abbrev Subshape (W : Type u₁) [Quiver.{v₁} W] : Type (max u₁ v₁) := ∀ a b : W, Set (a ⟶ b)

theorem mem_sup {S T : Subshape W} {a b : W} {f : a ⟶ b} :
    f ∈ (S ⊔ T) a b ↔ f ∈ S a b ∨ f ∈ T a b := Iff.rfl

/-- `IsArrow e f` says that `f` is the arrow `e`. Matching on a proof of it
identifies the endpoints of `f` with those of `e`. -/
inductive IsArrow {u v : W} (e : u ⟶ v) : ∀ {a b : W}, (a ⟶ b) → Prop
  | refl : IsArrow e e

/-- The subshape consisting of the single arrow `e`. -/
def single {u v : W} (e : u ⟶ v) : Subshape W := fun _ _ => {f | IsArrow e f}

theorem mem_single_self {u v : W} (e : u ⟶ v) : e ∈ single e u v := IsArrow.refl

/-- A path lies within `S` when each of its arrows does. -/
inductive Within (S : Subshape W) {a : W} : ∀ {b : W}, Path a b → Prop
  | nil : Within S .nil
  | cons {b c : W} {p : Path a b} {f : b ⟶ c} : Within S p → f ∈ S b c → Within S (p.cons f)

namespace Within

variable {S T : Subshape W}

theorem toPath {a b : W} {f : a ⟶ b} (hf : f ∈ S a b) : Within S f.toPath := nil.cons hf

theorem comp {a b c : W} {p : Path a b} {q : Path b c} (hp : Within S p) (hq : Within S q) :
    Within S (p.comp q) := by
  induction hq with
  | nil => simpa using hp
  | cons _ hf ih => rw [Path.comp_cons]; exact ih.cons hf

theorem mono (h : S ≤ T) {a b : W} {p : Path a b} (hp : Within S p) : Within T p := by
  induction hp with
  | nil => exact nil
  | cons _ hf ih => exact ih.cons (h _ _ hf)

theorem top {a b : W} (p : Path a b) : Within ⊤ p := by
  induction p with
  | nil => exact nil
  | cons _ _ ih => exact ih.cons trivial

/-- A path of length zero lies within every subshape. -/
theorem of_length_zero {a b : W} {p : Path a b} (h : p.length = 0) : Within S p := by
  cases p with
  | nil => exact nil
  | cons p f => simp at h

end Within

/-- There is a path from `a` to `b` within `S`. -/
abbrev ReachIn (S : Subshape W) (a b : W) : Prop := ∃ p : Path a b, Within S p

namespace ReachIn

variable {S T : Subshape W}

theorem refl (a : W) : ReachIn S a a := ⟨.nil, .nil⟩

theorem trans {a b c : W} : ReachIn S a b → ReachIn S b c → ReachIn S a c
  | ⟨p, hp⟩, ⟨q, hq⟩ => ⟨p.comp q, hp.comp hq⟩

theorem mono (h : S ≤ T) {a b : W} : ReachIn S a b → ReachIn T a b
  | ⟨p, hp⟩ => ⟨p, hp.mono h⟩

end ReachIn

/-- `S` has no cycles through distinct vertices. -/
def AcyclicOn (S : Subshape W) : Prop := ∀ a b : W, ReachIn S a b → ReachIn S b a → a = b

theorem AcyclicOn.mono {S T : Subshape W} (h : S ≤ T) (hT : AcyclicOn T) : AcyclicOn S :=
  fun a b hab hba => hT a b (hab.mono h) (hba.mono h)

/-! ## Commutativity -/

/-- `G` commutes on `S`: parallel paths within `S` have the same composite. -/
def CommutesOn (G : W ⥤q C) (S : Subshape W) : Prop :=
  ∀ ⦃a b : W⦄ (p q : Path a b), Within S p → Within S q → eval G p = eval G q

/-- `G` commutes: any two parallel paths have the same composite. -/
def Commutes (G : W ⥤q C) : Prop := ∀ ⦃a b : W⦄ (p q : Path a b), eval G p = eval G q

variable {G : W ⥤q C} {S T : Subshape W}

theorem commutesOn_top_iff : CommutesOn G ⊤ ↔ Commutes G :=
  ⟨fun h _ _ p q => h p q (.top p) (.top q), fun h _ _ p q _ _ => h p q⟩

theorem Commutes.commutesOn (h : Commutes G) (S : Subshape W) : CommutesOn G S :=
  fun _ _ p q _ _ => h p q

theorem CommutesOn.mono (h : S ≤ T) (hT : CommutesOn G T) : CommutesOn G S :=
  fun _ _ p q hp hq => hT p q (hp.mono h) (hq.mono h)

/-- Every diagram commutes on the empty subshape, whose only paths are empty. -/
theorem commutesOn_bot : CommutesOn G ⊥ := by
  intro a b p q hp hq
  cases hp with
  | nil => cases hq with
    | nil => rfl
    | cons _ hf => exact hf.elim
  | cons _ hf => exact hf.elim

/-- Functors preserve commutative diagrams (Riehl, Lemma 1.6.5). -/
theorem CommutesOn.map (F : C ⥤ D) (h : CommutesOn G S) :
    CommutesOn (G ⋙q F.toPrefunctor) S := fun _ _ p q hp hq => by
  rw [eval_map, eval_map, h p q hp hq]

/-- Faithful functors reflect commutative diagrams (Riehl, Lemma 1.6.20). -/
theorem CommutesOn.of_map (F : C ⥤ D) [F.Faithful] (h : CommutesOn (G ⋙q F.toPrefunctor) S) :
    CommutesOn G S := fun _ _ p q hp hq =>
  F.map_injective (by rw [← eval_map, ← eval_map]; exact h p q hp hq)

/-! ## Faces -/

/-- A face of a shape: two parallel paths, `lhs` and `rhs`, that the face says
have the same composite. -/
structure Face (W : Type u₁) [Quiver.{v₁} W] where
  /-- The common source of the two paths. -/
  src : W
  /-- The common target of the two paths. -/
  tgt : W
  /-- The side a forward step rewrites from. -/
  lhs : Path src tgt
  /-- The side a forward step rewrites to. -/
  rhs : Path src tgt

namespace Face

/-- The two sides of a face, indexed by `Bool`: `false` is `lhs`, `true` is `rhs`. -/
def side (φ : Face W) : Bool → Path φ.src φ.tgt
  | false => φ.lhs
  | true => φ.rhs

/-- The face holds in `G`: its two sides have the same composite. -/
def Holds (G : W ⥤q C) (φ : Face W) : Prop := eval G φ.lhs = eval G φ.rhs

theorem Holds.side {G : W ⥤q C} {φ : Face W} (h : φ.Holds G) (b c : Bool) :
    eval G (φ.side b) = eval G (φ.side c) := by
  cases b <;> cases c
  · rfl
  · exact h
  · exact h.symm
  · rfl

end Face

end Diagrams
