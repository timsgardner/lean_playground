/-
# Gluing commuting diagrams

Two commuting diagrams are glued into one whose graph contains both: its arrows are
those of the two pieces, and an arrow the pieces share appears once. The glued
diagram commutes when the pieces paste (`CommutesOn.paste`): any two vertices that
both pieces touch are joined by a path of shared arrows, and the whole is acyclic.

`glue D₁ D₂` (in `frontend.lean`) builds the glued diagram, identifying objects and
morphisms of `D₂` with those of `D₁` up to definitional equality. This file proves,
once for all diagrams, that the result commutes (`commutes_of_glue`). The theorem
has hypotheses of two kinds.

* Conditions on numbers only (`GlueOK`): where each piece's vertices and arrows sit
  in the glued graph, and the pasting conditions. They are decided by evaluation.
* The glued diagram has each piece's objects and morphisms at those places
  (`HasPiece`). For concrete diagrams both sides unfold to the same list, so this
  holds by `rfl`.

Each piece commutes inside the glued diagram because commutativity transports along
a map of quivers that is injective on vertices (`CommutesOn.of_embed`, by lifting
paths).
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

end Transport

/-! ## Pieces of a diagram -/

section Pieces

variable {C : Type u} [Category.{v} C] {n : ℕ} {E : List (ℕ × ℕ)}

/-- The arrows whose numbers are listed in `am`. -/
def arrowsIn (am : List ℕ) : Subshape (Shape n E) := fun _ _ => {e | e.val.val ∈ am}

/-- Membership is decided by one bit test in the bitmask of `am`. -/
instance (am : List ℕ) {a b : Shape n E} (e : a ⟶ b) : Decidable (e ∈ arrowsIn am a b) :=
  decidable_of_iff ((setBits 0 am).testBit e.val.val = true) (by
    rw [testBit_setBits]; simp [arrowsIn])

theorem getD_of_lt {α : Type*} {l : List α} {k : ℕ} (d : α) (h : k < l.length) :
    l.getD k d = l[k] :=
  (List.getElem_eq_getD d).symm

/-- No number occurs twice in `l`, and none is in the bitmask `m`. One pass, with a
bit test per entry. -/
def nodupBits : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: l, m => !m.testBit x && nodupBits l (setBits m [x])

theorem nodup_of_nodupBits : ∀ (l : List ℕ) (m : ℕ), nodupBits l m = true →
    l.Nodup ∧ ∀ x ∈ l, m.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: l, m, h => by
    simp only [nodupBits, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hl⟩ := h
    obtain ⟨hnd, hm⟩ := nodup_of_nodupBits l _ hl
    have hm' : ∀ y ∈ l, m.testBit y = false ∧ y ≠ x := fun y hy => by
      have h2 : ¬ (m.testBit y = true ∨ y ∈ [x]) := by
        rw [← testBit_setBits]; simp [hm y hy]
      simp only [List.mem_singleton, not_or, Bool.not_eq_true] at h2
      exact h2
    refine ⟨List.nodup_cons.2 ⟨fun hxl => (hm' x hxl).2 rfl, hnd⟩, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact (hm' y hy).1

/-- The graph with `n₀` vertices and ends `E₀` sits in the graph with `n` vertices and
ends `E`: vertex `i` is vertex `vm[i]`, distinct vertices stay distinct, and arrow `k`
is arrow `am[k]`, which runs between the corresponding vertices. -/
def GraphEmbeds (n₀ : ℕ) (E₀ : List (ℕ × ℕ)) (n : ℕ) (E : List (ℕ × ℕ)) (vm am : List ℕ) :
    Prop :=
  vm.length = n₀ ∧ (∀ i ∈ vm, i < n) ∧ nodupBits vm 0 = true ∧ am.length = E₀.length ∧
    (∀ j ∈ am, j < E.length) ∧
    am.map (Braun.ofList E).get? =
      E₀.map fun p => ((Braun.ofList vm).get? p.1).bind fun a =>
        ((Braun.ofList vm).get? p.2).map fun b => (a, b)

instance {n₀ : ℕ} {E₀ : List (ℕ × ℕ)} {vm am : List ℕ} :
    Decidable (GraphEmbeds n₀ E₀ n E vm am) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ### A certificate for the chain condition

The chain condition asks that any two vertices both pieces touch be joined by a path
of arrows in both. Since the glued graph is acyclic, those vertices then lie, in
order, on one such path. The certificate is that path: a start `s₀` and a list `cp`
of arrows, which must form a walk of arrows in both pieces through every vertex both
pieces touch. -/

/-- The vertices of the walk from `s` along the arrows `cp` of `E`, if it is one. -/
def walkVerts (E : List (ℕ × ℕ)) : ℕ → List ℕ → Option (List ℕ)
  | s, [] => some [s]
  | s, j :: cp =>
    match E[j]? with
    | some p => if p.1 = s then (walkVerts E p.2 cp).map (s :: ·) else none
    | none => none

/-- The ends of the arrows of `E` whose numbers, counted from `j`, are in the bitmask
`m`. -/
def touchList (m : ℕ) : List (ℕ × ℕ) → ℕ → List ℕ
  | [], _ => []
  | p :: E, j => if m.testBit j then p.1 :: p.2 :: touchList m E (j + 1) else touchList m E (j + 1)

/-- The walk from `s₀` along `cp` uses arrows of both pieces, and passes through every
vertex that both pieces touch. -/
def chainCert (E : List (ℕ × ℕ)) (am₁ am₂ : List ℕ) (s₀ : ℕ) (cp : List ℕ) : Bool :=
  match walkVerts E s₀ cp with
  | some vs =>
    cp.all (fun j => (setBits 0 am₁).testBit j && (setBits 0 am₂).testBit j) &&
      (touchList (setBits 0 am₁) E 0).all fun v =>
        !(setBits 0 (touchList (setBits 0 am₂) E 0)).testBit v || (setBits 0 vs).testBit v
  | none => false

theorem mem_touchList {m : ℕ} : ∀ (E : List (ℕ × ℕ)) (j k : ℕ) (hk : k < E.length),
    m.testBit (j + k) = true → E[k].1 ∈ touchList m E j ∧ E[k].2 ∈ touchList m E j
  | [], _, _, hk, _ => absurd hk (by simp)
  | p :: E, j, 0, _, h => by
    simp only [Nat.add_zero] at h
    simp [touchList, h]
  | p :: E, j, k + 1, hk, h => by
    have ih := mem_touchList E (j + 1) k (by simpa using hk) (by rw [← h]; congr 1; omega)
    simp only [touchList, List.getElem_cons_succ]
    split_ifs <;> simp [ih]

theorem walkVerts_head {E : List (ℕ × ℕ)} : ∀ {s : ℕ} {cp vs : List ℕ},
    walkVerts E s cp = some vs → ∃ vs', vs = s :: vs'
  | s, [], vs, h => by simp only [walkVerts, Option.some.injEq] at h; exact ⟨[], h.symm⟩
  | s, j :: cp, vs, h => by
    simp only [walkVerts] at h
    split at h
    · split_ifs at h
      obtain ⟨vs', _, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨vs', rfl⟩
    · exact absurd h (by simp)

theorem reach_of_walk (hEn : ∀ p ∈ E, p.1 < n ∧ p.2 < n) {am₁ am₂ : List ℕ} :
    ∀ (cp : List ℕ) (s : ℕ) (vs : List ℕ), walkVerts E s cp = some vs →
      (∀ j ∈ cp, j ∈ am₁ ∧ j ∈ am₂) →
      ∀ (i k : ℕ) (hik : i ≤ k) (hk : k < vs.length) (ha : vs[i] < n) (hb : vs[k] < n),
        ReachIn (arrowsIn (n := n) (E := E) am₁ ⊓ arrowsIn am₂)
          (Shape.vert ⟨vs[i], ha⟩) (Shape.vert ⟨vs[k], hb⟩)
  | [], s, vs, h, _, i, k, hik, hk, ha, hb => by
    simp only [walkVerts, Option.some.injEq] at h
    subst h
    obtain rfl : k = 0 := by simpa using hk
    obtain rfl : i = 0 := by omega
    exact ⟨.nil, .nil⟩
  | j :: cp, s, vs, h, hcp, i, k, hik, hk, ha, hb => by
    simp only [walkVerts] at h
    split at h
    · rename_i p hp
      split_ifs at h with hps
      obtain ⟨vs', hvs', rfl⟩ := Option.map_eq_some_iff.1 h
      have ih := reach_of_walk hEn cp p.2 vs' hvs' (fun j' hj' => hcp j' (List.mem_cons_of_mem _ hj'))
      obtain ⟨hj, hjp⟩ := List.getElem?_eq_some_iff.1 hp
      obtain ⟨hp₁, hp₂⟩ := hEn p (hjp ▸ List.getElem_mem hj)
      obtain ⟨vs'', rfl⟩ := walkVerts_head hvs'
      rcases i with _ | i
      · rcases k with _ | k
        · exact ⟨.nil, .nil⟩
        · -- One arrow from `s` to `p.2`, then the rest of the walk.
          let e : (Shape.vert ⟨s, by simpa using ha⟩ : Shape n E) ⟶ Shape.vert ⟨p.2, hp₂⟩ :=
            ⟨⟨j, hj⟩, by simp only [Fin.getElem_fin]; rw [hjp]; exact Prod.ext hps rfl⟩
          have he : e ∈ (arrowsIn am₁ ⊓ arrowsIn am₂) _ _ :=
            ⟨(hcp j List.mem_cons_self).1, (hcp j List.mem_cons_self).2⟩
          exact (show ReachIn _ _ _ from ⟨e.toPath, Within.toPath he⟩).trans
            (ih 0 k (Nat.zero_le _) (by simpa using hk) hp₂ hb)
      · rcases k with _ | k
        · omega
        · exact ih i k (by omega) (by simpa using hk) ha hb
    · exact absurd h (by simp)

/-- An arrow of `arrowsIn am` touches only vertices listed by `touchList`. -/
theorem touches_mem {am : List ℕ} {v : Shape n E} (h : Touches (arrowsIn am) v) :
    (Shape.num v).val ∈ touchList (setBits 0 am) E 0 := by
  obtain ⟨a, b, e, he, hv⟩ := h
  have hbit : (setBits 0 am).testBit (0 + e.val.val) = true := by
    rw [Nat.zero_add, testBit_setBits]; exact Or.inr he
  have hmem := mem_touchList E 0 e.val.val e.val.isLt hbit
  rw [show E[e.val.val] = _ from e.property] at hmem
  rcases hv with rfl | rfl
  · exact hmem.1
  · exact hmem.2

theorem chain_of_chainCert (hEn : ∀ p ∈ E, p.1 < n ∧ p.2 < n) {am₁ am₂ : List ℕ} {s₀ : ℕ}
    {cp : List ℕ} (h : chainCert E am₁ am₂ s₀ cp = true) :
    Chain (arrowsIn (n := n) (E := E) am₁) (arrowsIn am₂) := by
  unfold chainCert at h
  split at h
  · rename_i vs hvs
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hcp, htouch⟩ := h
    have hcp' : ∀ j ∈ cp, j ∈ am₁ ∧ j ∈ am₂ := fun j hj => by
      have := hcp j hj
      simp only [testBit_setBits, Nat.zero_testBit, Bool.false_eq_true, false_or] at this
      exact this
    have hon : ∀ v : Shape n E, Shared (arrowsIn am₁) (arrowsIn am₂) v →
        (Shape.num v).val ∈ vs := by
      rintro v ⟨h₁, h₂⟩
      have := htouch _ (touches_mem h₁)
      have h₂' := touches_mem h₂
      simp only [Bool.or_eq_true, Bool.not_eq_true', testBit_setBits, Nat.zero_testBit,
        Bool.false_eq_true, false_or] at this
      rcases this with h | h
      · exact absurd ((testBit_setBits _ 0).2 (Or.inr h₂')) (by rw [h]; simp)
      · exact h
    rw [chain_iff]
    intro s s' hs hs'
    obtain ⟨i, hi, his⟩ := List.getElem_of_mem (hon s hs)
    obtain ⟨k, hk, hks⟩ := List.getElem_of_mem (hon s' hs')
    have ha : vs[i] < n := his ▸ (Shape.num s).isLt
    have hb : vs[k] < n := hks ▸ (Shape.num s').isLt
    have es : (Shape.vert ⟨vs[i], ha⟩ : Shape n E) = s := Fin.ext his
    have es' : (Shape.vert ⟨vs[k], hb⟩ : Shape n E) = s' := Fin.ext hks
    rcases le_total i k with hik | hki
    · left
      rw [← es, ← es']
      exact reach_of_walk hEn cp s₀ vs hvs hcp' i k hik hk ha hb
    · right
      rw [← es, ← es']
      exact reach_of_walk hEn cp s₀ vs hvs hcp' k i hki hi hb ha
  · exact absurd h (by simp)

/-- The conditions on numbers for gluing two graphs into the graph with `n` vertices
and ends `E`: each sits in it, every arrow comes from one of them (tested on
bitmasks), the walk from `s₀` along `cp` certifies the chain condition, and every arrow
raises the rank `rk`, so that the graph is acyclic. -/
def GlueOK (n₁ : ℕ) (E₁ : List (ℕ × ℕ)) (n₂ : ℕ) (E₂ : List (ℕ × ℕ)) (n : ℕ)
    (E : List (ℕ × ℕ)) (vm₁ am₁ vm₂ am₂ rk : List ℕ) (s₀ : ℕ) (cp : List ℕ) : Prop :=
  GraphEmbeds n₁ E₁ n E vm₁ am₁ ∧ GraphEmbeds n₂ E₂ n E vm₂ am₂ ∧
    (∀ j < E.length, ((setBits 0 am₁).testBit j || (setBits 0 am₂).testBit j) = true) ∧
    chainCert E am₁ am₂ s₀ cp = true ∧
    E.all (fun p => ((Braun.ofList rk).get? p.1).getD 0 < ((Braun.ofList rk).get? p.2).getD 0) =
      true

instance {n₁ n₂ : ℕ} {E₁ E₂ : List (ℕ × ℕ)} {vm₁ am₁ vm₂ am₂ rk : List ℕ} {s₀ : ℕ}
    {cp : List ℕ} : Decidable (GlueOK n₁ E₁ n₂ E₂ n E vm₁ am₁ vm₂ am₂ rk s₀ cp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The object at vertex number `i`, if there is one. -/
def objAt (obj : Fin n → C) (i : ℕ) : Option C :=
  if h : i < n then some (obj ⟨i, h⟩) else none

/-- A listed morphism, with its objects in place of the numbers of its ends. -/
def homOf {obj : Fin n → C} (x : Σ a b : Fin n, obj a ⟶ obj b) : Σ X Y : C, X ⟶ Y :=
  ⟨obj x.1, obj x.2.1, x.2.2⟩

theorem heq_of_homOf_eq {n' : ℕ} {obj : Fin n → C} {obj' : Fin n' → C}
    {x : Σ a b : Fin n, obj a ⟶ obj b} {y : Σ a b : Fin n', obj' a ⟶ obj' b}
    (h : homOf x = homOf y) : HEq x.2.2 y.2.2 := by
  have key : ∀ {X X' Y Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'},
      (⟨X, Y, f⟩ : Σ X Y : C, X ⟶ Y) = ⟨X', Y', g⟩ → HEq f g := by
    intro X X' Y Y' f g h
    cases h
    rfl
  exact key h

/-- The diagram with objects `obj` has the objects of `D` at the vertex numbers `vm`,
and the morphisms `Ms` of `D` are, at the arrow numbers `am`, among the morphisms
`MsU` of the diagram. Each side is compared with the lists `Xs` and `Ms` written out,
so that each check evaluates one side and compares the result with a list entry. -/
def HasPiece (D : CommDiagram C) (obj : Fin n → C) (vm am : List ℕ) (Xs : List C)
    (Ms MsU : List (Σ X Y : C, X ⟶ Y)) : Prop :=
  (List.range D.n).map (objAt D.obj) = Xs.map some ∧ vm.map (objAt obj) = Xs.map some ∧
    D.mors.map homOf = Ms ∧ am.map (fun j => MsU[j]?) = Ms.map some

theorem toPrefunctor_map_heq (obj : Fin n → C) (mors : List (Σ a b : Fin n, obj a ⟶ obj b))
    (hE : endsOf mors = E) {a b : Shape n E} (e : a ⟶ b) :
    HEq ((toPrefunctor obj mors hE).map e) (mors[e.val.val]'(length_lt_of_endsOf hE e.val)).2.2 := by
  simp only [toPrefunctor]
  exact cast_heq _ _

/-- The ends of an arrow of a diagram, read from its listed morphism. -/
theorem ends_mors (D : CommDiagram C) (k : ℕ) (h : k < D.E.length) :
    D.E[k] = ((D.mors[k]'(by rw [← length_endsOf D.ends]; exact h)).1.val,
      (D.mors[k]'(by rw [← length_endsOf D.ends]; exact h)).2.1.val) :=
  (ends_getElem D.ends ⟨k, h⟩).symm

namespace Piece

variable {D : CommDiagram C} {vm am : List ℕ} (hg : GraphEmbeds D.n D.E n E vm am)
include hg

theorem vm_lt (i : Fin D.n) : i.val < vm.length := by rw [hg.1]; exact i.isLt

theorem am_lt (k : Fin D.E.length) : k.val < am.length := by rw [hg.2.2.2.1]; exact k.isLt

/-- The vertex of the glued graph for a vertex of the piece. -/
def vert (i : Fin D.n) : Fin n :=
  ⟨vm[i.val]'(vm_lt hg i), hg.2.1 _ (List.getElem_mem _)⟩

/-- The number, in the glued graph, of an arrow of the piece. -/
def arrNum (k : Fin D.E.length) : Fin E.length :=
  ⟨am[k.val]'(am_lt hg k), hg.2.2.2.2.1 _ (List.getElem_mem _)⟩

theorem ends_arrNum (k : Fin D.E.length) (a b : Fin D.n) (h : D.E[k] = (a.val, b.val)) :
    E[arrNum hg k] = ((vert hg a).val, (vert hg b).val) := by
  have := congrArg (·[k.val]?) hg.2.2.2.2.2
  simp only [Fin.getElem_fin] at h
  simp only [List.getElem?_map, List.getElem?_eq_getElem (am_lt hg k),
    List.getElem?_eq_getElem k.isLt, Option.map_some, h, Braun.get?_ofList,
    List.getElem?_eq_getElem (vm_lt hg a), List.getElem?_eq_getElem (vm_lt hg b),
    Option.bind_some] at this
  rw [List.getElem?_eq_getElem (by exact (arrNum hg k).isLt)] at this
  exact Option.some.inj (Option.some.inj this)

/-- The piece, mapped into the glued graph. -/
def φ : Shape D.n D.E ⥤q Shape n E where
  obj a := Shape.vert (vert hg (Shape.num a))
  map e := ⟨arrNum hg e.val, ends_arrNum hg e.val _ _ e.property⟩

theorem φ_injective : Function.Injective (φ hg).obj := by
  intro a a' h
  have h' : vm[(Shape.num a).val]'(vm_lt hg _) = vm[(Shape.num a').val]'(vm_lt hg _) :=
    congrArg Fin.val h
  exact Fin.ext (((nodup_of_nodupBits vm 0 hg.2.2.1).1.getElem_inj_iff).1 h')

theorem covers : Covers (φ hg) (arrowsIn am) := by
  intro x y e he
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem (show e.val.val ∈ am from he)
  have hkE : k < D.E.length := by rw [← hg.2.2.2.1]; exact hk
  have hkm : k < D.mors.length := by rw [← length_endsOf D.ends]; exact hkE
  let a := (D.mors[k]'hkm).1
  let b := (D.mors[k]'hkm).2.1
  have hab : D.E[(⟨k, hkE⟩ : Fin D.E.length)] = (a.val, b.val) := ends_mors D k hkE
  have h₁ := ends_arrNum hg ⟨k, hkE⟩ a b hab
  have h₁' : E[e.val.val]? = some ((vert hg a).val, (vert hg b).val) := by
    rw [← hke, List.getElem?_eq_getElem (by exact (arrNum hg ⟨k, hkE⟩).isLt)]
    exact congrArg some h₁
  have h₂ : E[e.val.val]? = some ((Shape.num x).val, (Shape.num y).val) := by
    rw [List.getElem?_eq_getElem e.val.isLt]
    exact congrArg some e.property
  have h₃ := Option.some.inj (h₁'.symm.trans h₂)
  have hx : vert hg a = Shape.num x := Fin.ext (congrArg Prod.fst h₃)
  have hy : vert hg b = Shape.num y := Fin.ext (congrArg Prod.snd h₃)
  refine ⟨Shape.vert a, Shape.vert b, ⟨⟨k, hkE⟩, hab⟩, hx, hy, ?_⟩
  exact Shape.arrow_heq _ _ hx hy (Fin.ext hke)

theorem comp {obj : Fin n → C} {mors : List (Σ a b : Fin n, obj a ⟶ obj b)}
    (hE : endsOf mors = E) {Xs : List C} {Ms MsU : List (Σ X Y : C, X ⟶ Y)}
    (hU : mors.map homOf = MsU) (hp : HasPiece D obj vm am Xs Ms MsU) :
    φ hg ⋙q toPrefunctor obj mors hE = toPrefunctor D.obj D.mors D.ends := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hp
  refine prefunctor_ext_heq (fun a => ?_) fun {a b} e => ?_
  · have k₁ := congrArg (·[(Shape.num a).val]?) h₁
    have k₂ := congrArg (·[(Shape.num a).val]?) h₂
    have hlt : vm[(Shape.num a).val]'(vm_lt hg _) < n := (vert hg _).isLt
    simp only [List.getElem?_map, List.getElem?_range (Shape.num a).isLt,
      List.getElem?_eq_getElem (vm_lt hg _), Option.map_some, objAt, Fin.is_lt, hlt,
      dite_true] at k₁ k₂
    exact Option.some.inj (Option.some.inj (k₂.trans k₁.symm))
  · have hk : e.val.val < am.length := am_lt hg e.val
    have hkm : e.val.val < D.mors.length := length_lt_of_endsOf D.ends e.val
    have hj : am[e.val.val] < mors.length := by
      rw [← length_endsOf hE]; exact (arrNum hg e.val).isLt
    have k₃ := congrArg (·[e.val.val]?) h₃
    have k₄ := congrArg (·[e.val.val]?) h₄
    have k₅ := congrArg (·[am[e.val.val]]?) hU
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hkm,
      Option.map_some, List.getElem?_eq_getElem hj] at k₃ k₄ k₅
    rw [← k₃, Option.map_some, Option.some.injEq] at k₄
    have key : homOf mors[am[e.val.val]] = homOf D.mors[e.val.val] := Option.some.inj (k₅.trans k₄)
    exact (toPrefunctor_map_heq obj mors hE _).trans
      ((heq_of_homOf_eq key).trans (toPrefunctor_map_heq _ _ _ e).symm)

end Piece

/-- A piece of a diagram commutes inside it. -/
theorem commutesOn_piece {D : CommDiagram C} {obj : Fin n → C}
    {mors : List (Σ a b : Fin n, obj a ⟶ obj b)} (hE : endsOf mors = E) {vm am : List ℕ}
    {Xs : List C} {Ms MsU : List (Σ X Y : C, X ⟶ Y)} (hg : GraphEmbeds D.n D.E n E vm am)
    (hU : mors.map homOf = MsU) (hp : HasPiece D obj vm am Xs Ms MsU) :
    CommutesOn (toPrefunctor obj mors hE) (arrowsIn am) :=
  CommutesOn.of_embed (Piece.φ_injective hg) (Piece.covers hg)
    (by rw [Piece.comp hg hE hU hp]; exact D.commutes)

/-- **Gluing commutes.** A diagram made of two commuting pieces, which sit in it as
`GlueOK` describes and paste, commutes. -/
theorem commutes_of_glue {obj : Fin n → C} {mors : List (Σ a b : Fin n, obj a ⟶ obj b)}
    (hE : endsOf mors = E) (D₁ D₂ : CommDiagram C) (vm₁ am₁ vm₂ am₂ rk : List ℕ) (s₀ : ℕ)
    (cp : List ℕ) (h : GlueOK D₁.n D₁.E D₂.n D₂.E n E vm₁ am₁ vm₂ am₂ rk s₀ cp)
    (Xs₁ Xs₂ : List C) (Ms₁ Ms₂ MsU : List (Σ X Y : C, X ⟶ Y)) (hU : mors.map homOf = MsU)
    (h₁ : HasPiece D₁ obj vm₁ am₁ Xs₁ Ms₁ MsU) (h₂ : HasPiece D₂ obj vm₂ am₂ Xs₂ Ms₂ MsU) :
    Commutes (toPrefunctor obj mors hE) := by
  obtain ⟨g₁, g₂, hall, hcert, hrank⟩ := h
  have hEn : ∀ p ∈ E, p.1 < n ∧ p.2 < n := by
    subst hE
    intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp
    exact ⟨x.1.isLt, x.2.1.isLt⟩
  have hchain := chain_of_chainCert hEn hcert
  have hacyc : AcyclicOn (arrowsIn (n := n) (E := E) am₁ ⊔ arrowsIn am₂) := by
    refine acyclicOn_of_rank (fun a => rk[(Shape.num a).val]?.getD 0) fun a b e _ => ?_
    have h := List.all_eq_true.1 hrank _ (List.getElem_mem e.val.isLt)
    rw [show E[e.val.val] = _ from e.property] at h
    simp only [Braun.get?_ofList, decide_eq_true_eq] at h
    exact h
  have hS := (commutesOn_piece hE g₁ hU h₁).paste (commutesOn_piece hE g₂ hU h₂) hchain hacyc
  have htop : (⊤ : Subshape (Shape n E)) ≤ arrowsIn am₁ ⊔ arrowsIn am₂ := fun a b e _ => by
    have h := hall e.val.val e.val.isLt
    rw [Bool.or_eq_true, testBit_setBits, testBit_setBits] at h
    simpa [mem_sup, arrowsIn] using h
  exact commutesOn_top_iff.1 fun a b p q hp hq => hS p q (hp.mono htop) (hq.mono htop)

end Pieces

end Diagrams
