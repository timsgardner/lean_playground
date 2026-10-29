/-
# Category Kindergarten: Adding one arrow to a commuting diagram

Riehl (§1.6) observes that commutativity of a diagram can usually be checked
one minimal subdiagram at a time. This file makes one precise version of that
observation, phrased as an inductive step: if a diagram commutes on a subshape
`S`, and we add one more arrow `e : u ⟶ v`, which equations must we check so
that it commutes on `S ⊔ single e`?

A pair of vertices `(x, y)` is an *obligation* when there are paths `x ⇝ u`,
`v ⇝ y` and `x ⇝ y` within `S`, because then the new path `x ⇝ u ⟶ v ⇝ y` is
parallel to an old one. The obligation at `(x, y)` implies the obligation at
any pair `(x', y')` with paths `x' ⇝ x` and `y ⇝ y'`, by whiskering. The main
theorem, `commutesOn_sup_single_iff`, says that when the shape is finite, `S` is
acyclic, and there is no path `v ⇝ u` within `S`, the diagram commutes on
`S ⊔ single e` if and only if the equation holds at each *minimal* obligation.

Conversely, `minObl_necessary` shows that no minimal obligation can be dropped:
for each one there is a diagram of types, commuting on `S`, for which the
equation holds at every other obligation and fails at that one. The closing
example, `Example.two_regions_not_enough`, applies this to a five-object diagram
where a planar drawing shows two new regions but three checks are needed.
-/

import LeanPlayground.Scratch.category_kindergarten.diagram_core
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Finite.Prod
import Mathlib.Order.WellFounded

open CategoryTheory Quiver

namespace Diagrams

universe v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

/-! ## Obligations -/

section Obligations

variable (S : Subshape W)

/-- `(x, y)` is an obligation for a new arrow `u ⟶ v` when that arrow creates a
path from `x` to `y` parallel to one within `S`. -/
def Obl (u v x y : W) : Prop := ReachIn S x u ∧ ReachIn S v y ∧ ReachIn S x y

/-- An obligation is minimal when no other obligation lies below it. -/
def MinObl (u v x y : W) : Prop :=
  Obl S u v x y ∧
    ∀ x₀ y₀, Obl S u v x₀ y₀ → ReachIn S x x₀ → ReachIn S y₀ y → x₀ = x ∧ y₀ = y

variable (G : W ⥤q C) {u v : W} (e : u ⟶ v)

/-- The equation at `(x, y)`: some path from `x` to `y` through the new arrow has
the same composite as some path within `S`. When `G` commutes on `S`, one
instance is as good as all of them (see `whisker`). -/
def Check (x y : W) : Prop :=
  ∃ (α : Path x u) (β : Path v y) (γ : Path x y), Within S α ∧ Within S β ∧ Within S γ ∧
    eval G α ≫ G.map e ≫ eval G β = eval G γ

end Obligations

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

/-- Whiskering: the equation at `(x', y')` implies the equation at any pair
`(x, y)` with paths `x ⇝ x'` and `y' ⇝ y`. This is Riehl's Lemma 1.6.11. -/
theorem whisker (hD : CommutesOn G S) {x y x' y' : W} (hx : ReachIn S x x')
    (hy : ReachIn S y' y) (h : Check S G e x' y') {α : Path x u} {β : Path v y}
    {γ : Path x y} (hα : Within S α) (hβ : Within S β) (hγ : Within S γ) :
    eval G α ≫ G.map e ≫ eval G β = eval G γ := by
  obtain ⟨ρ, hρ⟩ := hx
  obtain ⟨σ, hσ⟩ := hy
  obtain ⟨α', β', γ', hα', hβ', hγ', h⟩ := h
  rw [hD α (ρ.comp α') hα (hρ.comp hα'), hD β (β'.comp σ) hβ (hβ'.comp hσ),
    hD γ (ρ.comp (γ'.comp σ)) hγ (hρ.comp (hγ'.comp hσ))]
  simp only [eval_comp, Category.assoc]
  rw [← h]
  simp only [Category.assoc]

/-- If `G` commutes on `S`, and every obligation lies above one whose equation
has been checked, then `G` commutes on `S ⊔ single e`. -/
theorem CommutesOn.sup_single_of_cover (hD : CommutesOn G S) (huv : ¬ ReachIn S v u)
    (hcov : ∀ x y, Obl S u v x y →
      ∃ x' y', ReachIn S x x' ∧ ReachIn S y' y ∧ Check S G e x' y') :
    CommutesOn G (S ⊔ single e) := by
  have key : ∀ {x y : W} {α : Path x u} {β : Path v y} {γ : Path x y},
      Within S α → Within S β → Within S γ → eval G α ≫ G.map e ≫ eval G β = eval G γ := by
    intro x y α β γ hα hβ hγ
    obtain ⟨x', y', hx, hy, h⟩ := hcov x y ⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩⟩
    exact whisker hD hx hy h hα hβ hγ
  intro a b p q hp hq
  rcases eval_old_or_new (G := G) huv hp with ⟨p', hp', h₁⟩ | ⟨α, β, hα, hβ, h₁⟩ <;>
  rcases eval_old_or_new (G := G) huv hq with ⟨q', hq', h₂⟩ | ⟨α', β', hα', hβ', h₂⟩ <;>
  rw [h₁, h₂]
  · exact hD _ _ hp' hq'
  · exact (key hα' hβ' hp').symm
  · exact key hα hβ hq'
  · rw [hD α α' hα hα', hD β β' hβ hβ']

/-- Conversely, if `G` commutes on `S ⊔ single e`, the equation holds at every
obligation. -/
theorem CommutesOn.eq_of_sup_single (h : CommutesOn G (S ⊔ single e)) {x y : W}
    {α : Path x u} {β : Path v y} {γ : Path x y}
    (hα : Within S α) (hβ : Within S β) (hγ : Within S γ) :
    eval G α ≫ G.map e ≫ eval G β = eval G γ := by
  have := h (α.comp (e.toPath.comp β)) γ
    ((hα.mono le_sup_left).comp
      ((Within.toPath (mem_sup.2 (Or.inr (mem_single_self e)))).comp (hβ.mono le_sup_left)))
    (hγ.mono le_sup_left)
  simpa using this

/-! ## Minimal obligations -/

/-- In a finite acyclic shape, every obligation lies above a minimal one. -/
theorem exists_minObl_below [Finite W] (hacyc : AcyclicOn S) {x y : W} (h : Obl S u v x y) :
    ∃ x' y', ReachIn S x x' ∧ ReachIn S y' y ∧ MinObl S u v x' y' := by
  -- `r p q` says that the pair `p` lies strictly below the pair `q`.
  let r : W × W → W × W → Prop := fun p q => ReachIn S q.1 p.1 ∧ ReachIn S p.2 q.2 ∧ p ≠ q
  have : IsTrans (W × W) r := ⟨fun p q w ⟨h1, h2, hpq⟩ ⟨h3, h4, _⟩ =>
    ⟨h3.trans h1, h2.trans h4, fun hpw => hpq (by
      subst hpw
      exact Prod.ext (hacyc _ _ h3 h1) (hacyc _ _ h2 h4))⟩⟩
  have : Std.Irrefl r := ⟨fun p ⟨_, _, h⟩ => h rfl⟩
  let s : Set (W × W) := {p | Obl S u v p.1 p.2 ∧ ReachIn S x p.1 ∧ ReachIn S p.2 y}
  obtain ⟨m, ⟨hm, hxm, hmy⟩, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min s
    ⟨(x, y), h, ReachIn.refl x, ReachIn.refl y⟩
  refine ⟨m.1, m.2, hxm, hmy, hm, fun x₀ y₀ h₀ hx₀ hy₀ => ?_⟩
  by_cases heq : (x₀, y₀) = m
  · exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  · exact absurd ⟨hx₀, hy₀, heq⟩ (hmin (x₀, y₀) ⟨h₀, hxm.trans hx₀, hy₀.trans hmy⟩)

/-- **Adding one arrow.** Let `G` commute on a subshape `S` of a finite shape,
with `S` acyclic, and let `e : u ⟶ v` be an arrow with no path from `v` back to
`u` within `S`. Then `G` commutes on `S ⊔ single e` if and only if the equation
holds at each minimal obligation. -/
theorem commutesOn_sup_single_iff [Finite W] (hD : CommutesOn G S) (hacyc : AcyclicOn S)
    (huv : ¬ ReachIn S v u) :
    CommutesOn G (S ⊔ single e) ↔ ∀ x y, MinObl S u v x y → Check S G e x y := by
  constructor
  · intro h x y ⟨⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩⟩, _⟩
    exact ⟨α, β, γ, hα, hβ, hγ, h.eq_of_sup_single hα hβ hγ⟩
  · intro h
    refine hD.sup_single_of_cover huv fun x y hxy => ?_
    obtain ⟨x', y', hx, hy, hmin⟩ := exists_minObl_below hacyc hxy
    exact ⟨x', y', hx, hy, h x' y' hmin⟩

end Extend

/-! ## No minimal obligation can be dropped

Fix a minimal obligation `(x, y)`. In a shape whose arrows are those of `S` and
the new arrow `e`, we build a diagram of types that commutes on `S`, for which
the equation holds at every other obligation but fails at `(x, y)`. So the check
at `(x, y)` cannot be deduced from checks elsewhere.

The model imitates the morphisms out of `x` in the free category on the shape,
with every obligation other than `(x, y)` imposed as a relation. Over a vertex `b`
there is an "old" element `false` when `x ⇝ b`, and a "new" element `true` when
`v ⇝ b`. The two become identified (the element `true` disappears) as soon as
some imposed obligation reachable from `x` lies below `b`; that is the condition
`Coll`.
-/

section Sharp

variable (S : Subshape W) (u v x y : W)

/-- Some obligation other than `(x, y)`, reachable from `x`, lies below `b`. -/
def Coll (b : W) : Prop :=
  ∃ x₁ y₁, Obl S u v x₁ y₁ ∧ (x₁, y₁) ≠ (x, y) ∧ ReachIn S x x₁ ∧ ReachIn S y₁ b

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

/-- Transport a function along a proof that `f` is the arrow `e`. -/
def IsArrow.transport {X : W → Sort*} {e : u ⟶ v} {a b : W} {f : a ⟶ b}
    (h : IsArrow e f) (g : X u → X v) : X a → X b := by
  cases h; exact g

theorem IsArrow.transport_self {X : W → Sort*} {e : u ⟶ v} (h : IsArrow e e)
    (g : X u → X v) : h.transport g = g := by
  cases h; rfl

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

theorem model_commutesOn : CommutesOn (model x y e hW) S := fun _ _ hp hq =>
  ConcreteCategory.hom_ext _ _ fun s => Subtype.ext (by rw [eval_model_val hp, eval_model_val hq])

/-- In the model, the equation holds at every obligation other than `(x, y)`. -/
theorem model_eq_of_ne (he : e ∉ S u v) {x' y' : W} (ho : Obl S u v x' y')
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

/-- In the model, the equation fails at the minimal obligation `(x, y)`. -/
theorem model_not_check (he : e ∉ S u v) (hmin : MinObl S u v x y) :
    ¬ Check S (model x y e hW) e x y := by
  rintro ⟨α, β, γ, hα, hβ, hγ, h⟩
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

/-- **No minimal obligation can be dropped.** Suppose every arrow of the shape
lies in `S` or is the new arrow `e`, which is not in `S`. For each minimal
obligation `(x, y)` there is a diagram of types, commuting on `S`, for which the
equation holds at every other obligation but fails at `(x, y)`. -/
theorem minObl_necessary (hW : ∀ {a b : W} (f : a ⟶ b), f ∈ S a b ∨ IsArrow e f)
    (he : e ∉ S u v) (hmin : MinObl S u v x y) :
    ∃ G : W ⥤q Type, CommutesOn G S ∧
      (∀ x' y', Obl S u v x' y' → (x', y') ≠ (x, y) →
        ∀ {α : Path x' u} {β : Path v y'} {γ : Path x' y'},
          Within S α → Within S β → Within S γ →
            eval G α ≫ G.map e ≫ eval G β = eval G γ) ∧
      ¬ Check S G e x y :=
  ⟨model x y e hW, model_commutesOn,
    fun _ _ ho hne _ _ _ hα hβ hγ => model_eq_of_ne he ho hne hα hβ hγ,
    model_not_check he hmin⟩

end Sharp

/-! ## An example where a drawing undercounts

Take objects `s, u, v, t, y` with arrows `s ⟶ u`, `s ⟶ v`, `u ⟶ t`, `v ⟶ t`,
`u ⟶ y`, `v ⟶ y`, and add a new arrow `u ⟶ v`. Drawn in the plane with the new
arrow between `t` and `y`, it borders two regions, which give the obligations
`(u, t)` and `(u, y)`. But `(s, v)` is a minimal obligation too: the new path
`s ⟶ u ⟶ v` is parallel to the old arrow `s ⟶ v`. By `minObl_necessary`, the
two regions alone do not make the diagram commute.
-/

namespace Example

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

instance : Quiver K := ⟨KHom⟩

/-- Whether an arrow is one of the six old ones. -/
def KHom.old {a b : K} : KHom a b → Bool
  | .uv => false
  | _ => true

/-- The subshape of old arrows. -/
def oldArrows : Subshape K := fun a b => {f : a ⟶ b | KHom.old f = true}

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
theorem minObl_sv : MinObl oldArrows K.u K.v K.s K.v :=
  ⟨⟨KHom.su.reach, ReachIn.refl _, KHom.sv.reach⟩, by min_obl_by_table⟩

/-- The two obligations that a planar drawing shows are minimal too. -/
theorem minObl_ut : MinObl oldArrows K.u K.v K.u K.t :=
  ⟨⟨ReachIn.refl _, KHom.vt.reach, KHom.ut.reach⟩, by min_obl_by_table⟩

theorem minObl_uy : MinObl oldArrows K.u K.v K.u K.y :=
  ⟨⟨ReachIn.refl _, KHom.vy.reach, KHom.uy.reach⟩, by min_obl_by_table⟩

/-- There is a diagram of shape `K`, commuting on the old arrows, for which the
equations at `(u, t)` and `(u, y)` hold, yet the whole diagram does not
commute. -/
theorem two_regions_not_enough :
    ∃ G : K ⥤q Type, CommutesOn G oldArrows ∧
      Check oldArrows G uv .u .t ∧ Check oldArrows G uv .u .y ∧ ¬ Commutes G := by
  obtain ⟨G, hG, hother, hfail⟩ := minObl_necessary hW uv_not_old minObl_sv
  refine ⟨G, hG, ?_, ?_, fun h => hfail ?_⟩
  · exact ⟨.nil, KHom.vt.path, KHom.ut.path, .nil, KHom.vt.within, KHom.ut.within,
      hother _ _ minObl_ut.1 (by decide) .nil KHom.vt.within KHom.ut.within⟩
  · exact ⟨.nil, KHom.vy.path, KHom.uy.path, .nil, KHom.vy.within, KHom.uy.within,
      hother _ _ minObl_uy.1 (by decide) .nil KHom.vy.within KHom.uy.within⟩
  · exact ⟨KHom.su.path, .nil, KHom.sv.path, KHom.su.within, .nil, KHom.sv.within,
      CommutesOn.eq_of_sup_single (h.commutesOn _) KHom.su.within .nil KHom.sv.within⟩

end Example

end Diagrams
