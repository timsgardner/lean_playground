/-
# Gluing commuting diagrams

Two commuting diagrams `D₁` and `D₂` are glued by identifying some vertices of `D₂`
with vertices of `D₁`, and some arrows of `D₂` with arrows of `D₁`, where the
objects and morphisms agree. The result commutes when the two pieces paste
(`CommutesOn.paste`): the shared vertices are joined by common paths, and the
whole is acyclic. Both conditions are about the glued graph alone, so for concrete
diagrams they are decided by evaluation.

The proof that the glued diagram commutes is proved once, for all diagrams:

* each piece commutes inside the glued diagram, because commutativity transports
  along a map of quivers that is injective on vertices (`CommutesOn.of_embed`, by
  lifting paths);
* the two pieces paste;
* an arrow of `D₂` identified with an arrow of `D₁` also remains as a parallel
  copy with the same image, which does not affect commutativity
  (`Commutes.of_commutesOn_of_parallel`).
-/

import LeanPlayground.diagrams.graph

open CategoryTheory Quiver

namespace Diagrams

universe v u

/-! ## Transporting commutativity -/

section Transport

variable {W₁ W : Type*} [Quiver W₁] [Quiver W] {C : Type u} [Category.{v} C]

/-- The composite of a path through a composite prefunctor. -/
theorem eval_comp_mapPath (φ : W₁ ⥤q W) (G : W ⥤q C) {a : W₁} :
    ∀ {b : W₁} (p : Path a b), eval (φ ⋙q G) p = eval G (φ.mapPath p)
  | _, .nil => rfl
  | _, .cons p f => by
    rw [eval_cons, eval_comp_mapPath φ G p, Prefunctor.mapPath_cons, eval_cons]; rfl

/-- Prefunctors with equal objects and heterogeneously equal maps are equal. -/
theorem prefunctor_ext_heq {F G : W₁ ⥤q W} (hobj : ∀ a, F.obj a = G.obj a)
    (hmap : ∀ {a b} (f : a ⟶ b), HEq (F.map f) (G.map f)) : F = G := by
  obtain ⟨Fo, Fm⟩ := F
  obtain ⟨Go, Gm⟩ := G
  obtain rfl : Fo = Go := funext hobj
  congr
  funext a b f
  exact eq_of_heq (hmap f)

variable {φ : W₁ ⥤q W} {S : Subshape W}

/-- Every arrow of `S` is the image of an arrow of `W₁`. -/
def Covers (φ : W₁ ⥤q W) (S : Subshape W) : Prop :=
  ∀ {a b : W} (g : a ⟶ b), g ∈ S a b →
    ∃ (a' b' : W₁) (f : a' ⟶ b'), φ.obj a' = a ∧ φ.obj b' = b ∧ HEq (φ.map f) g

/-- A nonempty path within `S` starts at the image of a vertex. -/
theorem Within.start_mem_range (hS : Covers φ S) {a : W} :
    ∀ {b : W} {p : Path a b}, Within S p → p.length = 0 ∨ ∃ x, φ.obj x = a
  | _, _, .nil => .inl rfl
  | _, _, .cons (p := p) hp hf => by
    rcases Within.start_mem_range hS hp with h0 | hx
    · obtain rfl := Path.eq_of_length_zero p h0
      obtain ⟨a', _, _, ha, _, _⟩ := hS _ hf
      exact .inr ⟨a', ha⟩
    · exact .inr hx

/-- **Lifting paths.** If `φ` is injective on vertices and every arrow of `S` is an
image, a path within `S` from `φ x` is the image of a path from `x`. -/
theorem Within.lift (hinj : Function.Injective φ.obj) (hS : Covers φ S) {x : W₁} :
    ∀ {b : W} {p : Path (φ.obj x) b}, Within S p →
      ∃ (y : W₁) (p₁ : Path x y), φ.obj y = b ∧ HEq (φ.mapPath p₁) p
  | _, _, .nil => ⟨x, .nil, rfl, HEq.rfl⟩
  | _, _, .cons (p := p) (f := f) hp hf => by
    obtain ⟨y, p₁, hy, hp₁⟩ := Within.lift hinj hS hp
    obtain ⟨a', b', g, ha, hb, hg⟩ := hS f hf
    obtain rfl := hinj (ha.trans hy.symm)
    subst hy hb
    obtain rfl := eq_of_heq hp₁
    obtain rfl := eq_of_heq hg
    exact ⟨b', p₁.cons g, rfl, HEq.rfl⟩

/-- **Commutativity transports along an embedding.** If `φ` is injective on
vertices, every arrow of `S` is the image of an arrow of `W₁`, and `φ ⋙q G`
commutes, then `G` commutes on `S`. -/
theorem CommutesOn.of_embed {G : W ⥤q C} (hinj : Function.Injective φ.obj) (hS : Covers φ S)
    (hC : Commutes (φ ⋙q G)) : CommutesOn G S := by
  intro a b p q hp hq
  -- If both paths are empty they are equal; otherwise `a` is an image.
  have hstart : (p.length = 0 ∧ q.length = 0) ∨ ∃ x, φ.obj x = a := by
    rcases hp.start_mem_range hS with hp0 | hx
    · rcases hq.start_mem_range hS with hq0 | hx
      · exact .inl ⟨hp0, hq0⟩
      · exact .inr hx
    · exact .inr hx
  rcases hstart with ⟨hp0, hq0⟩ | ⟨x, rfl⟩
  · obtain rfl := Path.eq_of_length_zero p hp0
    rw [Path.eq_nil_of_length_zero p hp0, Path.eq_nil_of_length_zero q hq0]
  · obtain ⟨y, p₁, hy, hp₁⟩ := hp.lift hinj hS
    obtain ⟨y', q₁, hy', hq₁⟩ := hq.lift hinj hS
    obtain rfl := hinj (hy.trans hy'.symm)
    subst hy
    rw [← eq_of_heq hp₁, ← eq_of_heq hq₁, ← eval_comp_mapPath, ← eval_comp_mapPath]
    exact hC p₁ q₁

/-- **Parallel copies.** If `G` commutes on `S`, and every arrow outside `S` has a
parallel arrow in `S` with the same image, then `G` commutes. -/
theorem Commutes.of_commutesOn_of_parallel {G : W ⥤q C} (hS : CommutesOn G S)
    (hpar : ∀ {a b : W} (f : a ⟶ b), f ∉ S a b → ∃ g : a ⟶ b, g ∈ S a b ∧ G.map g = G.map f) :
    Commutes G := by
  -- Every path has a path within `S` with the same composite.
  have key : ∀ {a b : W} (p : Path a b), ∃ p' : Path a b, Within S p' ∧ eval G p' = eval G p := by
    intro a b p
    induction p with
    | nil => exact ⟨.nil, .nil, rfl⟩
    | cons p f ih =>
      obtain ⟨p', hp', he⟩ := ih
      by_cases hf : f ∈ S _ _
      · exact ⟨p'.cons f, hp'.cons hf, by rw [eval_cons, eval_cons, he]⟩
      · obtain ⟨g, hg, hge⟩ := hpar f hf
        exact ⟨p'.cons g, hp'.cons hg, by rw [eval_cons, eval_cons, he, hge]⟩
  intro a b p q
  obtain ⟨p', hp', hpe⟩ := key p
  obtain ⟨q', hq', hqe⟩ := key q
  rw [← hpe, ← hqe]
  exact hS p' q' hp' hq'

end Transport

/-! ## The glued diagram -/

section Glue

variable {C : Type u} [Category.{v} C]

/-- Which vertices and arrows of `D₂` are identified with vertices and arrows of
`D₁`. -/
structure Gluing (D₁ D₂ : CommDiagram C) where
  /-- The vertex of `D₁` that a vertex of `D₂` is identified with, if any. -/
  vert : Fin D₂.n → Option (Fin D₁.n)
  /-- The arrow of `D₁` that an arrow of `D₂` is identified with, if any. -/
  arr : Fin D₂.mors.length → Option (Fin D₁.mors.length)

namespace Gluing

variable {D₁ D₂ : CommDiagram C} (σ : Gluing D₁ D₂)

/-- Identified objects agree. -/
def ObjEq : Prop := ∀ a j, σ.vert a = some j → D₂.obj a = D₁.obj j

/-- Distinct vertices of `D₂` are identified with distinct vertices of `D₁`. -/
def VertInj : Prop := ∀ a a' j, σ.vert a = some j → σ.vert a' = some j → a = a'

/-- The vertex of the glued diagram for a vertex of `D₂`: the vertex of `D₁` it is
identified with, or a new vertex. -/
def ρ (a : Fin D₂.n) : Fin (D₁.n + D₂.n) :=
  match σ.vert a with
  | some j => Fin.castAdd D₂.n j
  | none => Fin.natAdd D₁.n a

/-- An identified arrow of `D₂` runs between the vertices identified with the ends of
the arrow of `D₁`. -/
def ArrEnds : Prop := ∀ k k₁, σ.arr k = some k₁ →
  σ.ρ (D₂.mors[k]).1 = Fin.castAdd D₂.n (D₁.mors[k₁]).1 ∧
    σ.ρ (D₂.mors[k]).2.1 = Fin.castAdd D₂.n (D₁.mors[k₁]).2.1

/-- Identified morphisms agree. -/
def MorEq : Prop := ∀ k k₁, σ.arr k = some k₁ → HEq (D₂.mors[k]).2.2 (D₁.mors[k₁]).2.2

end Gluing

namespace Glue

variable {D₁ D₂ : CommDiagram C} (σ : Gluing D₁ D₂)

/-- The objects of the glued diagram: those of `D₁`, then those of `D₂`. -/
def obj (k : Fin (D₁.n + D₂.n)) : C :=
  if h : k.val < D₁.n then D₁.obj ⟨k, h⟩ else D₂.obj ⟨k - D₁.n, by omega⟩

theorem obj_castAdd (j : Fin D₁.n) : obj (D₂ := D₂) (Fin.castAdd D₂.n j) = D₁.obj j := by
  simp [obj]

variable {σ}

theorem obj_ρ (hobj : σ.ObjEq) (a : Fin D₂.n) : obj (σ.ρ a) = D₂.obj a := by
  unfold Gluing.ρ
  split
  · rename_i j h
    rw [obj_castAdd, hobj a j h]
  · simp [obj]

variable (σ)

/-- An arrow of `D₁`, in the glued diagram. -/
def left (x : Σ a b : Fin D₁.n, D₁.obj a ⟶ D₁.obj b) :
    Σ a b : Fin (D₁.n + D₂.n), obj a ⟶ obj b :=
  ⟨Fin.castAdd D₂.n x.1, Fin.castAdd D₂.n x.2.1,
    cast (by rw [obj_castAdd, obj_castAdd]) x.2.2⟩

/-- An arrow of `D₂`, in the glued diagram. -/
def right (hobj : σ.ObjEq) (x : Σ a b : Fin D₂.n, D₂.obj a ⟶ D₂.obj b) :
    Σ a b : Fin (D₁.n + D₂.n), obj a ⟶ obj b :=
  ⟨σ.ρ x.1, σ.ρ x.2.1, cast (by rw [obj_ρ hobj, obj_ρ hobj]) x.2.2⟩

/-- The morphisms of the glued diagram: those of `D₁`, then all those of `D₂`. -/
def mors (hobj : σ.ObjEq) : List (Σ a b : Fin (D₁.n + D₂.n), obj a ⟶ obj b) :=
  D₁.mors.map (left (D₂ := D₂)) ++ D₂.mors.map (right σ hobj)

/-- The ends of the glued diagram, in closed form. -/
theorem endsOf_mors (hobj : σ.ObjEq) :
    endsOf (mors σ hobj) = D₁.E ++ D₂.mors.map fun x => ((σ.ρ x.1).val, (σ.ρ x.2.1).val) := by
  rw [← D₁.ends]
  simp [mors, endsOf, left, right, Function.comp_def]

variable {σ}

theorem length_mors (hobj : σ.ObjEq) :
    (mors σ hobj).length = D₁.mors.length + D₂.mors.length := by
  simp [mors]

theorem mors_getElem_left (hobj : σ.ObjEq) {k : ℕ} (hk : k < D₁.mors.length)
    (h : k < (mors σ hobj).length) :
    (mors σ hobj)[k] = left (D₂ := D₂) D₁.mors[k] := by
  simp only [mors]
  rw [List.getElem_append_left (by simpa using hk), List.getElem_map]

theorem mors_getElem_right (hobj : σ.ObjEq) {k : ℕ} (hk : k < D₂.mors.length)
    (h : D₁.mors.length + k < (mors σ hobj).length) :
    (mors σ hobj)[D₁.mors.length + k] = right σ hobj D₂.mors[k] := by
  simp only [mors]
  rw [List.getElem_append_right (by simp), List.getElem_map]
  simp

/-- The ends of an arrow of a diagram, read from its listed morphism. -/
theorem ends_mors (D : CommDiagram C) (k : ℕ) (h : k < D.E.length) :
    D.E[k] = ((D.mors[k]'(by rw [← length_endsOf D.ends]; exact h)).1.val,
      (D.mors[k]'(by rw [← length_endsOf D.ends]; exact h)).2.1.val) :=
  (ends_getElem D.ends ⟨k, h⟩).symm

theorem ends_left (hobj : σ.ObjEq) {k : ℕ} (hk : k < D₁.E.length)
    (h : k < (endsOf (mors σ hobj)).length) : (endsOf (mors σ hobj))[k] = D₁.E[k] := by
  simp only [endsOf_mors]
  rw [List.getElem_append_left hk]

theorem length_E (D : CommDiagram C) : D.E.length = D.mors.length := length_endsOf D.ends

theorem ends_right (hobj : σ.ObjEq) {k : ℕ} (hk : k < D₂.mors.length)
    (h : D₁.mors.length + k < (endsOf (mors σ hobj)).length) :
    (endsOf (mors σ hobj))[D₁.mors.length + k] =
      ((σ.ρ D₂.mors[k].1).val, (σ.ρ D₂.mors[k].2.1).val) := by
  simp only [endsOf_mors]
  rw [List.getElem_append_right (by rw [length_E]; omega)]
  simp [length_E]

/-- The glued shape. -/
abbrev Sh (hobj : σ.ObjEq) := Shape (D₁.n + D₂.n) (endsOf (mors σ hobj))

/-- The glued diagram, as a prefunctor. -/
def G (hobj : σ.ObjEq) : Sh hobj ⥤q C := toPrefunctor obj (mors σ hobj) rfl

theorem G_map_heq (hobj : σ.ObjEq) {a b : Sh hobj} (e : a ⟶ b) :
    HEq ((G hobj).map e) ((mors σ hobj)[e.val.val]'(by
      have := e.val.isLt; simpa [endsOf] using this)).2.2 := by
  simp only [G, toPrefunctor]
  exact cast_heq _ _

theorem toPrefunctor_map_heq (D : CommDiagram C) {a b : Shape D.n D.E} (e : a ⟶ b) :
    HEq ((toPrefunctor D.obj D.mors D.ends).map e)
      (D.mors[e.val.val]'(length_lt_of_endsOf D.ends e.val)).2.2 := by
  simp only [toPrefunctor]
  exact cast_heq _ _

/-! ### The embedding of `D₁` -/

/-- `D₁` embeds in the glued diagram. -/
def φ₁ (hobj : σ.ObjEq) : Shape D₁.n D₁.E ⥤q Sh hobj where
  obj a := Shape.vert (Fin.castAdd D₂.n (Shape.num a))
  map {a b} e := ⟨⟨e.val.val, by
      have := length_lt_of_endsOf D₁.ends e.val
      rw [length_endsOf rfl, length_mors]; omega⟩, by
    have h := e.property
    simp only [Fin.getElem_fin] at h ⊢
    rw [ends_left hobj e.val.isLt]
    exact h⟩

theorem φ₁_comp (hobj : σ.ObjEq) : φ₁ hobj ⋙q G hobj = toPrefunctor D₁.obj D₁.mors D₁.ends := by
  refine prefunctor_ext_heq (fun a => obj_castAdd _) fun {a b} e => ?_
  refine (G_map_heq hobj _).trans (HEq.trans ?_ (toPrefunctor_map_heq D₁ e).symm)
  have hk : e.val.val < D₁.mors.length := length_lt_of_endsOf D₁.ends e.val
  exact (congr_arg_heq (fun x => x.2.2) (mors_getElem_left hobj hk _)).trans (cast_heq _ _)

/-! ### The map from `D₂` -/

theorem num_ends (D : CommDiagram C) {a b : Shape D.n D.E} (e : a ⟶ b) :
    (D.mors[e.val.val]'(length_lt_of_endsOf D.ends e.val)).1 = Shape.num a ∧
      (D.mors[e.val.val]'(length_lt_of_endsOf D.ends e.val)).2.1 = Shape.num b := by
  have h := e.property
  rw [Fin.getElem_fin, ends_mors] at h
  exact ⟨Fin.ext (congrArg Prod.fst h), Fin.ext (congrArg Prod.snd h)⟩

/-- The index, in the glued diagram, of an arrow of `D₂`: its partner in `D₁` if it is
identified, its copy otherwise. -/
def idx₂ (k : Fin D₂.mors.length) : ℕ :=
  match σ.arr k with
  | some k₁ => k₁.val
  | none => D₁.mors.length + k.val

variable (σ) in
theorem idx₂_lt (hobj : σ.ObjEq) (k : Fin D₂.mors.length) :
    idx₂ (σ := σ) k < (endsOf (mors σ hobj)).length := by
  rw [length_endsOf rfl, length_mors]
  unfold idx₂
  split
  · rename_i k₁ _; have := k₁.isLt; omega
  · have := k.isLt; omega

theorem ends_idx₂ (hobj : σ.ObjEq) (hends : σ.ArrEnds) (k : Fin D₂.mors.length) :
    (endsOf (mors σ hobj))[idx₂ (σ := σ) k]'(idx₂_lt σ hobj k) =
      ((σ.ρ D₂.mors[k].1).val, (σ.ρ D₂.mors[k].2.1).val) := by
  rcases h : σ.arr k with _ | k₁
  · simp only [idx₂, h]
    exact ends_right hobj k.isLt _
  · simp only [idx₂, h]
    obtain ⟨h₁, h₂⟩ := hends k k₁ h
    rw [ends_left hobj (by rw [length_E]; exact k₁.isLt), ends_mors, h₁, h₂]
    rfl

theorem mors_idx₂_heq (hobj : σ.ObjEq) (hmor : σ.MorEq) (k : Fin D₂.mors.length)
    (hi : idx₂ (σ := σ) k < (mors σ hobj).length) :
    HEq ((mors σ hobj)[idx₂ (σ := σ) k]'hi).2.2 (D₂.mors[k]).2.2 := by
  suffices key : ∀ (i : ℕ) (hi : i < (mors σ hobj).length), i = idx₂ (σ := σ) k →
      HEq ((mors σ hobj)[i]'hi).2.2 (D₂.mors[k]).2.2 from key _ hi rfl
  intro i hi hik
  rcases h : σ.arr k with _ | k₁
  · obtain rfl : i = D₁.mors.length + k.val := by rw [hik, idx₂, h]
    exact (congr_arg_heq (fun x => x.2.2) (mors_getElem_right hobj k.isLt _)).trans (cast_heq _ _)
  · obtain rfl : i = k₁.val := by rw [hik, idx₂, h]
    exact (congr_arg_heq (fun x => x.2.2) (mors_getElem_left hobj k₁.isLt _)).trans
      ((cast_heq _ _).trans (hmor k k₁ h).symm)

/-- `D₂` maps to the glued diagram: an identified arrow to its partner in `D₁`, any
other arrow to its copy. -/
def φ₂ (hobj : σ.ObjEq) (hends : σ.ArrEnds) : Shape D₂.n D₂.E ⥤q Sh hobj where
  obj a := Shape.vert (σ.ρ (Shape.num a))
  map {a b} e :=
    ⟨⟨idx₂ (σ := σ) ⟨e.val.val, length_lt_of_endsOf D₂.ends e.val⟩, idx₂_lt σ hobj _⟩, by
      obtain ⟨ha, hb⟩ := num_ends D₂ e
      have := ends_idx₂ hobj hends ⟨e.val.val, length_lt_of_endsOf D₂.ends e.val⟩
      simp only [Fin.getElem_fin] at this ha hb ⊢
      rw [this]
      exact Prod.ext (congrArg (fun x => (σ.ρ x).val) ha) (congrArg (fun x => (σ.ρ x).val) hb)⟩

theorem φ₂_comp (hobj : σ.ObjEq) (hends : σ.ArrEnds) (hmor : σ.MorEq) :
    φ₂ hobj hends ⋙q G hobj = toPrefunctor D₂.obj D₂.mors D₂.ends := by
  refine prefunctor_ext_heq (fun a => obj_ρ hobj _) fun {a b} e => ?_
  exact (G_map_heq hobj _).trans ((mors_idx₂_heq hobj hmor _ _).trans
    (toPrefunctor_map_heq D₂ e).symm)

/-! ### The two pieces, and pasting them -/

theorem length_mors_E (hobj : σ.ObjEq) :
    (endsOf (mors σ hobj)).length = D₁.mors.length + D₂.mors.length := by
  rw [length_endsOf rfl, length_mors]

theorem mors_heq_of_eq (hobj : σ.ObjEq) {i j : ℕ} (hij : i = j) (hi : i < (mors σ hobj).length)
    (hj : j < (mors σ hobj).length) :
    HEq ((mors σ hobj)[i]'hi).2.2 ((mors σ hobj)[j]'hj).2.2 := by
  subst hij; rfl

variable (σ) in
/-- The arrows of `D₁` in the glued diagram. -/
def T₁ (hobj : σ.ObjEq) : Subshape (Sh hobj) := fun _ _ => {e | e.val.val < D₁.mors.length}

variable (σ) in
/-- The images of the arrows of `D₂`: partners of identified arrows, copies of the
others. -/
def T₂ (hobj : σ.ObjEq) : Subshape (Sh hobj) :=
  fun _ _ => {e | ∃ k : Fin D₂.mors.length, idx₂ (σ := σ) k = e.val.val}

instance (hobj : σ.ObjEq) {a b : Sh hobj} (e : a ⟶ b) : Decidable (e ∈ T₁ σ hobj a b) :=
  inferInstanceAs (Decidable (e.val.val < D₁.mors.length))

instance (hobj : σ.ObjEq) {a b : Sh hobj} (e : a ⟶ b) : Decidable (e ∈ T₂ σ hobj a b) :=
  inferInstanceAs (Decidable (∃ k : Fin D₂.mors.length, idx₂ (σ := σ) k = e.val.val))

theorem φ₁_injective (hobj : σ.ObjEq) : Function.Injective (φ₁ hobj).obj := fun _ _ h =>
  Fin.castAdd_injective D₁.n D₂.n h

theorem ρ_injective (hinj : σ.VertInj) : Function.Injective σ.ρ := by
  intro a a' h
  unfold Gluing.ρ at h
  rcases ha : σ.vert a with _ | j <;> rcases ha' : σ.vert a' with _ | j' <;>
    simp only [ha, ha'] at h
  · exact Fin.natAdd_injective D₂.n D₁.n h
  · have := congrArg Fin.val h; have := j'.isLt; simp at *; omega
  · have := congrArg Fin.val h; have := j.isLt; simp at *; omega
  · obtain rfl := Fin.castAdd_injective D₁.n D₂.n h
    exact hinj a a' j ha ha'

theorem φ₂_injective (hobj : σ.ObjEq) (hinj : σ.VertInj) (hends : σ.ArrEnds) :
    Function.Injective (φ₂ hobj hends).obj := fun _ _ h => ρ_injective hinj h

theorem covers₁ (hobj : σ.ObjEq) : Covers (φ₁ hobj) (T₁ σ hobj) := by
  intro x y e he
  have he' : e.val.val < D₁.mors.length := he
  have hk : e.val.val < D₁.E.length := by rw [length_E]; exact he'
  have hends := e.property
  simp only [Fin.getElem_fin] at hends
  rw [ends_left hobj hk, ends_mors] at hends
  refine ⟨Shape.vert (D₁.mors[e.val.val]'he').1, Shape.vert (D₁.mors[e.val.val]'he').2.1,
    ⟨⟨e.val.val, hk⟩, by simp only [Fin.getElem_fin]; rw [ends_mors]; rfl⟩,
    Fin.ext (congrArg Prod.fst hends), Fin.ext (congrArg Prod.snd hends), ?_⟩
  exact Shape.arrow_heq _ _ (Fin.ext (congrArg Prod.fst hends))
    (Fin.ext (congrArg Prod.snd hends)) rfl

theorem covers₂ (hobj : σ.ObjEq) (hends : σ.ArrEnds) : Covers (φ₂ hobj hends) (T₂ σ hobj) := by
  intro x y e he
  have he' : ∃ k : Fin D₂.mors.length, idx₂ (σ := σ) k = e.val.val := he
  obtain ⟨k, hk⟩ := he'
  have hE := e.property
  simp only [Fin.getElem_fin] at hE
  have key : ∀ (i : ℕ) (hi : i < (endsOf (mors σ hobj)).length), i = e.val.val →
      (endsOf (mors σ hobj))[i] = ((Shape.num x).val, (Shape.num y).val) := by
    rintro i hi rfl; exact hE
  have h₂ := (ends_idx₂ hobj hends k).symm.trans (key _ _ hk)
  simp only [Fin.getElem_fin] at h₂
  have hk' : k.val < D₂.E.length := by rw [length_E]; exact k.isLt
  refine ⟨Shape.vert (D₂.mors[k]).1, Shape.vert (D₂.mors[k]).2.1,
    ⟨⟨k.val, hk'⟩, by simp only [Fin.getElem_fin]; rw [ends_mors]; rfl⟩,
    Fin.ext (congrArg Prod.fst h₂), Fin.ext (congrArg Prod.snd h₂), ?_⟩
  exact Shape.arrow_heq _ _ (Fin.ext (congrArg Prod.fst h₂)) (Fin.ext (congrArg Prod.snd h₂))
    (Fin.ext hk)

theorem parallel (hobj : σ.ObjEq) (hends : σ.ArrEnds) (hmor : σ.MorEq) {a b : Sh hobj}
    (e : a ⟶ b) (he : e ∉ (T₁ σ hobj ⊔ T₂ σ hobj) a b) :
    ∃ g : a ⟶ b, g ∈ (T₁ σ hobj ⊔ T₂ σ hobj) a b ∧ (G hobj).map g = (G hobj).map e := by
  rw [mem_sup, not_or] at he
  obtain ⟨h₁, h₂⟩ := he
  have h₁' : ¬ e.val.val < D₁.mors.length := h₁
  have h₂' : ¬ ∃ k : Fin D₂.mors.length, idx₂ (σ := σ) k = e.val.val := h₂
  have h0 := length_mors_E hobj
  have hlt : e.val.val < D₁.mors.length + D₂.mors.length := by have := e.val.isLt; omega
  -- `e` is the copy of an arrow `k` of `D₂`, which is identified, since otherwise `e`
  -- would be its image.
  let k : Fin D₂.mors.length := ⟨e.val.val - D₁.mors.length, by omega⟩
  have hek : e.val.val = D₁.mors.length + k.val := by simp only [k]; omega
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, σ.arr k = some k₁ := by
    rcases h : σ.arr k with _ | k₁
    · exact absurd ⟨k, by rw [idx₂, h, hek]⟩ h₂'
    · exact ⟨k₁, rfl⟩
  have hidx : idx₂ (σ := σ) k = k₁.val := by rw [idx₂, hk₁]
  -- The partner of `k` runs between the same vertices.
  have hE := e.property
  simp only [Fin.getElem_fin] at hE
  have key : ∀ (i : ℕ) (hi : i < (endsOf (mors σ hobj)).length), i = e.val.val →
      (endsOf (mors σ hobj))[i] = ((Shape.num a).val, (Shape.num b).val) := by
    rintro i hi rfl; exact hE
  have hk1lt : k₁.val < (endsOf (mors σ hobj)).length := by have := k₁.isLt; omega
  have hpar : (endsOf (mors σ hobj))[k₁.val] = ((Shape.num a).val, (Shape.num b).val) := by
    have h₂ := ends_idx₂ hobj hends k
    simp only [Fin.getElem_fin] at h₂
    have h₃ := ends_right hobj k.isLt (by omega)
    have h₄ : ∀ (i : ℕ) (hi : i < (endsOf (mors σ hobj)).length), i = k₁.val →
        (endsOf (mors σ hobj))[i] = (endsOf (mors σ hobj))[k₁.val] := by
      rintro i hi rfl; rfl
    rw [← h₄ _ (idx₂_lt σ hobj k) hidx, h₂, ← h₃]
    exact key _ _ hek.symm
  refine ⟨⟨⟨k₁.val, hk1lt⟩, hpar⟩, mem_sup.2 (Or.inl k₁.isLt), ?_⟩
  -- Both arrows carry the morphism of `k`.
  have hm : (mors σ hobj).length = D₁.mors.length + D₂.mors.length := length_mors hobj
  refine eq_of_heq ((G_map_heq hobj _).trans ?_)
  refine (mors_heq_of_eq hobj hidx.symm (by omega) (by omega)).trans
    ((mors_idx₂_heq hobj hmor k (by omega)).trans ?_)
  refine HEq.symm ((G_map_heq hobj e).trans ((mors_heq_of_eq hobj hek (by omega) (by omega)).trans ?_))
  exact (congr_arg_heq (fun x => x.2.2) (mors_getElem_right hobj k.isLt _)).trans (cast_heq _ _)

/-- **Gluing commutes.** If identified objects and morphisms agree, identified
vertices are distinct, identified arrows have matching ends, and the two pieces
paste (their shared vertices are joined by common paths, and the whole is
acyclic), then the glued diagram commutes. -/
theorem commutes (hobj : σ.ObjEq) (hinj : σ.VertInj) (hends : σ.ArrEnds) (hmor : σ.MorEq)
    (hchain : Chain (T₁ σ hobj) (T₂ σ hobj)) (hacyc : AcyclicOn (T₁ σ hobj ⊔ T₂ σ hobj)) :
    Commutes (G hobj) := by
  have h₁ : CommutesOn (G hobj) (T₁ σ hobj) :=
    CommutesOn.of_embed (φ₁_injective hobj) (covers₁ hobj) (by rw [φ₁_comp]; exact D₁.commutes)
  have h₂ : CommutesOn (G hobj) (T₂ σ hobj) :=
    CommutesOn.of_embed (φ₂_injective hobj hinj hends) (covers₂ hobj hends)
      (by rw [φ₂_comp hobj hends hmor]; exact D₂.commutes)
  exact Commutes.of_commutesOn_of_parallel (h₁.paste h₂ hchain hacyc)
    (fun e he => parallel hobj hends hmor e he)

end Glue

/-- **Gluing.** The diagram obtained from `D₁` and `D₂` by identifying the vertices
and arrows given by `σ`, provided that identified objects and morphisms agree,
identified vertices are distinct, identified arrows have matching ends, and the two
pieces paste. Its vertices are those of `D₁` followed by those of `D₂`; its
morphisms are those of `D₁` followed by those of `D₂`. It commutes by
`Glue.commutes`. -/
def CommDiagram.glue (D₁ D₂ : CommDiagram C) (σ : Gluing D₁ D₂) (hobj : σ.ObjEq)
    (hinj : σ.VertInj) (hends : σ.ArrEnds) (hmor : σ.MorEq)
    (hchain : Chain (Glue.T₁ σ hobj) (Glue.T₂ σ hobj))
    (hacyc : AcyclicOn (Glue.T₁ σ hobj ⊔ Glue.T₂ σ hobj)) : CommDiagram C where
  n := D₁.n + D₂.n
  E := endsOf (Glue.mors σ hobj)
  obj := Glue.obj
  mors := Glue.mors σ hobj
  ends := rfl
  commutes := Glue.commutes hobj hinj hends hmor hchain hacyc

end Glue

end Diagrams
