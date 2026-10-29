/-
# Minimal cells

When an arrow `e : u ⟶ v` is added to a subshape `S`, the cells it closes that
must be checked are the *minimal* ones (`ClosesMin`): no other cell lies inside
them.

* They suffice: in a finite acyclic shape every cell lies outside a minimal one
  (`exists_closesMin_below`), so `G` commutes on `S ⊔ single e` if and only if
  the equation holds at each minimal cell (`commutesOn_sup_single_iff`).
* They are needed: `closesMin_necessary` gives, for each minimal cell, a diagram
  of types commuting on `S` for which the equation holds at every other cell and
  fails at that one. The `examples` apply this to a five-object diagram where a
  planar drawing shows two new regions but three checks are needed.
-/

import LeanPlayground.diagrams.extend
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Finite.Prod
import Mathlib.Order.WellFounded

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

section Minimal

variable {G : W ⥤q C} {S : Subshape W} {u v : W} {e : u ⟶ v}

/-- In a finite acyclic shape, every cell lies above a minimal one. -/
theorem exists_closesMin_below [Finite W] (hacyc : AcyclicOn S) {x y : W} (h : Closes S u v x y) :
    ∃ x' y', ReachIn S x x' ∧ ReachIn S y' y ∧ ClosesMin S u v x' y' := by
  -- `r p q` says that the pair `p` lies strictly below the pair `q`.
  let r : W × W → W × W → Prop := fun p q => ReachIn S q.1 p.1 ∧ ReachIn S p.2 q.2 ∧ p ≠ q
  have : IsTrans (W × W) r := ⟨fun p q w ⟨h1, h2, hpq⟩ ⟨h3, h4, _⟩ =>
    ⟨h3.trans h1, h2.trans h4, fun hpw => hpq (by
      subst hpw
      exact Prod.ext (hacyc _ _ h3 h1) (hacyc _ _ h2 h4))⟩⟩
  have : Std.Irrefl r := ⟨fun p ⟨_, _, h⟩ => h rfl⟩
  let s : Set (W × W) := {p | Closes S u v p.1 p.2 ∧ ReachIn S x p.1 ∧ ReachIn S p.2 y}
  obtain ⟨m, ⟨hm, hxm, hmy⟩, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min s
    ⟨(x, y), h, ReachIn.refl x, ReachIn.refl y⟩
  refine ⟨m.1, m.2, hxm, hmy, hm, fun x₀ y₀ h₀ hx₀ hy₀ => ?_⟩
  by_cases heq : (x₀, y₀) = m
  · exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  · exact absurd ⟨hx₀, hy₀, heq⟩ (hmin (x₀, y₀) ⟨h₀, hxm.trans hx₀, hy₀.trans hmy⟩)

/-- **Adding one arrow.** Let `G` commute on a subshape `S` of a finite shape,
with `S` acyclic, and let `e : u ⟶ v` be an arrow with no path from `v` back to
`u` within `S`. Then `G` commutes on `S ⊔ single e` if and only if the equation
holds at each minimal cell. -/
theorem commutesOn_sup_single_iff [Finite W] (hD : CommutesOn G S) (hacyc : AcyclicOn S)
    (huv : ¬ ReachIn S v u) :
    CommutesOn G (S ⊔ single e) ↔ ∀ x y, ClosesMin S u v x y → CellHolds S e G x y := by
  constructor
  · intro h x y ⟨⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩⟩, _⟩
    exact ⟨⟨α, β, γ, hα, hβ, hγ⟩, h.eq_of_sup_single hα hβ hγ⟩
  · intro h
    refine hD.sup_single_of_cover huv fun x y hxy => ?_
    obtain ⟨x', y', hx, hy, hmin⟩ := exists_closesMin_below hacyc hxy
    exact ⟨x', y', hx, hy, h x' y' hmin⟩

end Minimal

/-! ## No minimal cell can be dropped

Fix a minimal cell `(x, y)`. In a shape whose arrows are those of `S` and
the new arrow `e`, we build a diagram of types that commutes on `S`, for which
the equation holds at every other cell but fails at `(x, y)`. So the check
at `(x, y)` cannot be deduced from checks elsewhere.

The model imitates the morphisms out of `x` in the free category on the shape,
with every cell other than `(x, y)` imposed as a relation. Over a vertex `b`
there is an "old" element `false` when `x ⇝ b`, and a "new" element `true` when
`v ⇝ b`. The two become identified (the element `true` disappears) as soon as
some imposed cell reachable from `x` lies below `b`; that is the condition
`Coll`.
-/

/-- Transport a function along a proof that `f` is the arrow `e`. -/
def IsArrow.transport {u v : W} {X : W → Sort*} {e : u ⟶ v} {a b : W} {f : a ⟶ b}
    (h : IsArrow e f) (g : X u → X v) : X a → X b := by
  cases h; exact g

theorem IsArrow.transport_self {u v : W} {X : W → Sort*} {e : u ⟶ v} (h : IsArrow e e)
    (g : X u → X v) : h.transport g = g := by
  cases h; rfl

namespace NecessityModel

variable (S : Subshape W) (u v x y : W)

/-- Some cell other than `(x, y)`, reachable from `x`, lies below `b`. -/
def Coll (b : W) : Prop :=
  ∃ x₁ y₁, Closes S u v x₁ y₁ ∧ (x₁, y₁) ≠ (x, y) ∧ ReachIn S x x₁ ∧ ReachIn S y₁ b

/-- The value of the model at `b`: `false` stands for the old path from `x`,
`true` for the new one. -/
abbrev M (b : W) : Type :=
  {t : Bool // (t = false → ReachIn S x b) ∧ (t = true → ReachIn S v b ∧ ¬ Coll S u v x y b)}

variable {S u v x y}

theorem Coll.reach {b : W} : Coll S u v x y b → ReachIn S x b
  | ⟨_, _, ⟨_, _, h₁⟩, _, hx, hy⟩ => hx.trans (h₁.trans hy)

theorem Coll.mono {b c : W} (h : ReachIn S b c) : Coll S u v x y b → Coll S u v x y c
  | ⟨x₁, y₁, ho, hne, hx, hy⟩ => ⟨x₁, y₁, ho, hne, hx, hy.trans h⟩

open Classical in
/-- Along a path to `b`, the new element survives unless it is identified with
the old one at `b`. -/
noncomputable def clamp {a b : W} (h : ReachIn S a b) (s : M S u v x y a) : M S u v x y b :=
  if hc : Coll S u v x y b then ⟨false, fun _ => hc.reach, by simp⟩
  else ⟨s.1, fun hs => (s.2.1 hs).trans h, fun hs => ⟨(s.2.2 hs).1.trans h, hc⟩⟩

open Classical in
theorem clamp_val {a b : W} (h : ReachIn S a b) (s : M S u v x y a) :
    (clamp h s).1 = if Coll S u v x y b then false else s.1 := by
  unfold clamp; by_cases hc : Coll S u v x y b <;> simp [hc]

open Classical in
/-- The new arrow sends everything to the new element, if it is still there. -/
noncomputable def newFun (_ : M S u v x y u) : M S u v x y v :=
  if hc : Coll S u v x y v then ⟨false, fun _ => hc.reach, by simp⟩
  else ⟨true, by simp, fun _ => ⟨ReachIn.refl v, hc⟩⟩

open Classical in
theorem newFun_val (s : M S u v x y u) :
    (newFun s).1 = if Coll S u v x y v then false else true := by
  unfold newFun; by_cases hc : Coll S u v x y v <;> simp [hc]

variable (e : u ⟶ v) (hW : ∀ {a b : W} (f : a ⟶ b), f ∈ S a b ∨ IsArrow e f)

variable (x y) in
open Classical in
/-- The model diagram: arrows of `S` act by `clamp`, and `e` by `newFun`. -/
noncomputable abbrev model : W ⥤q Type where
  obj := M S u v x y
  map {a b} f := TypeCat.ofHom <|
    if hf : f ∈ S a b then clamp ⟨f.toPath, .toPath hf⟩
    else ((hW f).resolve_left hf).transport (X := M S u v x y) newFun

variable {e hW}

theorem model_map_of_mem {a b : W} {f : a ⟶ b} (hf : f ∈ S a b) (s : M S u v x y a) :
    (model x y e hW).map f s = clamp ⟨f.toPath, .toPath hf⟩ s := by
  simp [model, hf]

theorem model_map_new (he : e ∉ S u v) (s : M S u v x y u) :
    (model x y e hW).map e s = newFun s := by
  simp only [model, he, dite_false]
  rw [IsArrow.transport_self]
  rfl

open Classical in
/-- The composite of a path within `S` acts by `clamp`. -/
theorem eval_model_val {a b : W} {p : Path a b} (hp : Within S p) (s : M S u v x y a) :
    (eval (model x y e hW) p s).1 = if Coll S u v x y b then false else s.1 := by
  induction hp with
  | nil =>
    rw [eval_nil, types_id_apply]
    by_cases hc : Coll S u v x y a
    · cases hs : s.1
      · simp
      · exact absurd hc (s.2.2 hs).2
    · simp [hc]
  | @cons b c p f hp hf ih =>
    rw [eval_cons, types_comp_apply, model_map_of_mem hf, clamp_val, ih]
    split_ifs with h₁ h₂
    · rfl
    · exact absurd (h₂.mono ⟨f.toPath, .toPath hf⟩) h₁
    · rfl

theorem model_commutesOn : CommutesOn (model x y e hW) S := fun _ _ _ _ hp hq =>
  ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (by rw [eval_model_val hp, eval_model_val hq])

/-- In the model, the equation holds at every cell other than `(x, y)`. -/
theorem model_eq_of_ne (he : e ∉ S u v) {x' y' : W} (ho : Closes S u v x' y')
    (hne : (x', y') ≠ (x, y)) {α : Path x' u} {β : Path v y'} {γ : Path x' y'}
    (_hα : Within S α) (hβ : Within S β) (hγ : Within S γ) :
    eval (model x y e hW) α ≫ (model x y e hW).map e ≫ eval (model x y e hW) β =
      eval (model x y e hW) γ := by
  refine ConcreteCategory.hom_ext _ _ fun s => Subtype.ext ?_
  rw [types_comp_apply, types_comp_apply, eval_model_val hβ, model_map_new he, newFun_val,
    eval_model_val hγ]
  by_cases hc : Coll S u v x y y'
  · simp [hc]
  · have hcv : ¬ Coll S u v x y v := fun h => hc (h.mono ⟨β, hβ⟩)
    cases hs : s.1
    · exact absurd ⟨x', y', ho, hne, s.2.1 hs, ReachIn.refl y'⟩ hc
    · simp [hc, hcv]

/-- In the model, the equation fails at the minimal cell `(x, y)`. -/
theorem model_not_check (he : e ∉ S u v) (hmin : ClosesMin S u v x y) :
    ¬ CellHolds S e (model x y e hW) x y := by
  rintro ⟨⟨α, β, γ, hα, hβ, hγ⟩, h⟩
  have hy : ¬ Coll S u v x y y := fun ⟨x₁, y₁, ho, hne, hx, hy⟩ => by
    obtain ⟨rfl, rfl⟩ := hmin.2 x₁ y₁ ho hx hy
    exact hne rfl
  have hv : ¬ Coll S u v x y v := fun h => hy (h.mono ⟨β, hβ⟩)
  let s : M S u v x y x := ⟨false, fun _ => ReachIn.refl x, by simp⟩
  have h' : (eval (model x y e hW) β ((model x y e hW).map e
      (eval (model x y e hW) α s))).1 = (eval (model x y e hW) γ s).1 := by
    rw [← types_comp_apply, ← types_comp_apply, h]
  rw [eval_model_val hβ, model_map_new he, newFun_val, eval_model_val hγ] at h'
  simp [hy, hv, s] at h'

end NecessityModel

open NecessityModel in
/-- **No minimal cell can be dropped.** Suppose every arrow of the shape
lies in `S` or is the new arrow `e`, which is not in `S`. For each minimal
cell `(x, y)` there is a diagram of types, commuting on `S`, for which the
equation holds at every other cell but fails at `(x, y)`. -/
theorem closesMin_necessary {S : Subshape W} {u v x y : W} {e : u ⟶ v}
    (hW : ∀ {a b : W} (f : a ⟶ b), f ∈ S a b ∨ IsArrow e f)
    (he : e ∉ S u v) (hmin : ClosesMin S u v x y) :
    ∃ G : W ⥤q Type, CommutesOn G S ∧
      (∀ x' y', Closes S u v x' y' → (x', y') ≠ (x, y) →
        ∀ {α : Path x' u} {β : Path v y'} {γ : Path x' y'},
          Within S α → Within S β → Within S γ →
            eval G α ≫ G.map e ≫ eval G β = eval G γ) ∧
      ¬ CellHolds S e G x y :=
  ⟨model x y e hW, model_commutesOn,
    fun _ _ ho hne _ _ _ hα hβ hγ => model_eq_of_ne he ho hne hα hβ hγ,
    model_not_check he hmin⟩

end Diagrams
