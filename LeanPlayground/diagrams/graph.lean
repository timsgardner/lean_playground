/-
# Graphs as data

A diagram need not be a declared type. `Shape n E` is the quiver whose vertices are
`Fin n` and whose arrows are listed by their ends in `E : List (ℕ × ℕ)`: arrow `k`
runs from vertex `(E[k]).1` to vertex `(E[k]).2`. Because `n` and `E` are plain data,
a graph can be written down, or computed, inside a proof.

The instances the decision procedures need (`FinShape`, `NumShape`, decidable
equality of arrows) are proved here once, for every graph.

A diagram of shape `Shape n E` in a category `C` is given by objects
`obj : Fin n → C` and a list of morphisms, each bundled with the indices of its ends,
whose ends are `E` (`toPrefunctor`). For a concrete list, the image of each arrow
reduces by definition to the morphism listed for it.
-/

import LeanPlayground.diagrams.construct

open CategoryTheory Quiver

namespace Diagrams

universe v u

/-- The quiver with vertices `Fin n` and arrows listed by their ends in `E`. -/
def Shape (n : ℕ) (_E : List (ℕ × ℕ)) : Type := Fin n

namespace Shape

variable {n : ℕ} {E : List (ℕ × ℕ)}

/-- A vertex, given by its number. -/
def vert (i : Fin n) : Shape n E := i

/-- The number of a vertex. -/
def num (a : Shape n E) : Fin n := a

instance : Quiver (Shape n E) :=
  ⟨fun a b => { k : Fin E.length // E[k] = ((a : Fin n).val, (b : Fin n).val) }⟩

instance : DecidableEq (Shape n E) := inferInstanceAs (DecidableEq (Fin n))

instance : Fintype (Shape n E) := inferInstanceAs (Fintype (Fin n))

instance (a b : Shape n E) : DecidableEq (a ⟶ b) := fun x y =>
  decidable_of_iff (x.val = y.val) Subtype.ext_iff.symm

/-- The arrow number `k` of `E`, between the vertices it lists. -/
def arrowOf (k : Fin E.length) (h : E[k].1 < n ∧ E[k].2 < n) :
    (vert ⟨E[k].1, h.1⟩ : Shape n E) ⟶ vert ⟨E[k].2, h.2⟩ :=
  ⟨k, rfl⟩

/-- The arrow number `k` from `i` to `j`, given that `E` lists those ends for it. -/
def arr (i j : Fin n) (k : Fin E.length) (h : E[k] = (i.val, j.val)) :
    (vert i : Shape n E) ⟶ vert j :=
  ⟨k, h⟩

/-- Two arrows with equal ends and the same number are equal. -/
theorem arrow_heq {a b a' b' : Shape n E} (e : a ⟶ b) (e' : a' ⟶ b') (ha : a = a') (hb : b = b')
    (hk : e.val = e'.val) : HEq e e' := by
  subst ha hb
  exact heq_of_eq (Subtype.ext hk)

/-- Two bundled arrows with the same number are equal: an arrow's number determines
its ends. -/
theorem total_ext {e e' : Total (Shape n E)} (h : e.hom.val = e'.hom.val) : e = e' := by
  obtain ⟨a, b, k, hk⟩ := e
  obtain ⟨a', b', k', hk'⟩ := e'
  simp only at h
  subst h
  have ha : a = a' := Fin.ext (by have := congrArg Prod.fst (hk.symm.trans hk'); simpa using this)
  have hb : b = b' := Fin.ext (by have := congrArg Prod.snd (hk.symm.trans hk'); simpa using this)
  subst ha hb
  rfl

instance (priority := high) : DecidableEq (Total (Shape n E)) := fun e e' =>
  decidable_of_iff (e.hom.val = e'.hom.val) ⟨total_ext, fun h => h ▸ rfl⟩

/-- All arrows of the graph, in the order of `E`. Entries of `E` whose ends are not
vertices are not arrows. -/
def arrowList : List (Total (Shape n E)) :=
  (List.finRange E.length).filterMap fun k =>
    if h : E[k].1 < n ∧ E[k].2 < n then some ⟨_, _, arrowOf k h⟩ else none

theorem mem_arrowList (e : Total (Shape n E)) : e ∈ (arrowList : List (Total (Shape n E))) := by
  obtain ⟨a, b, k, hk⟩ := e
  have h : E[k].1 < n ∧ E[k].2 < n := by
    rw [hk]; exact ⟨(a : Fin n).isLt, (b : Fin n).isLt⟩
  refine List.mem_filterMap.2 ⟨k, List.mem_finRange k, ?_⟩
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact congrArg some (total_ext rfl)

instance : FinShape (Shape n E) where
  vertices := List.finRange n
  mem_vertices a := List.mem_finRange (a : Fin n)
  arrows := arrowList
  mem_arrows := mem_arrowList

instance [NeZero n] : NumShape (Shape n E) where
  size := n
  index a := (a : Fin n).val
  index_lt a := (a : Fin n).isLt
  vertexAt i := if h : i < n then vert ⟨i, h⟩ else vert ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  vertexAt_index a := dite_eq_left_of_eq_true (eq_true (num a).isLt)

end Shape

/-! ## Diagrams of a graph -/

section Interpretation

variable {C : Type u} [Category.{v} C] {n : ℕ} {E : List (ℕ × ℕ)}

/-- The ends of a list of morphisms bundled with the indices of their ends. -/
def endsOf {obj : Fin n → C} (mors : List (Σ a b : Fin n, obj a ⟶ obj b)) : List (ℕ × ℕ) :=
  mors.map fun x => (x.1.val, x.2.1.val)

theorem length_endsOf {obj : Fin n → C} {mors : List (Σ a b : Fin n, obj a ⟶ obj b)}
    (hE : endsOf mors = E) : E.length = mors.length := by
  subst hE; simp [endsOf]

theorem length_lt_of_endsOf {obj : Fin n → C} {mors : List (Σ a b : Fin n, obj a ⟶ obj b)}
    (hE : endsOf mors = E) (k : Fin E.length) : k.val < mors.length :=
  k.isLt.trans_eq (length_endsOf hE)

theorem ends_getElem {obj : Fin n → C} {mors : List (Σ a b : Fin n, obj a ⟶ obj b)}
    (hE : endsOf mors = E) (k : Fin E.length) :
    ((mors[k.val]'(length_lt_of_endsOf hE k)).1.val,
      (mors[k.val]'(length_lt_of_endsOf hE k)).2.1.val) = E[k] := by
  subst hE
  show _ = (List.map _ mors)[k.val]
  rw [List.getElem_map]

/-- The diagram of shape `Shape n E` with objects `obj` and the morphisms `mors`,
whose ends are `E`. Arrow `k` goes to the morphism `mors[k]`, transported along the
equality of its listed ends with the arrow's ends; for a concrete list the transport
reduces away. -/
def toPrefunctor (obj : Fin n → C) (mors : List (Σ a b : Fin n, obj a ⟶ obj b))
    (hE : endsOf mors = E) : Shape n E ⥤q C where
  obj a := obj (Shape.num a)
  map {a b} e :=
    let x := mors[e.val.val]'(length_lt_of_endsOf hE e.val)
    have h : (x.1.val, x.2.1.val) = ((Shape.num a).val, (Shape.num b).val) :=
      (ends_getElem hE e.val).trans e.property
    have h₁ : x.1 = Shape.num a := Fin.ext (congrArg Prod.fst h)
    have h₂ : x.2.1 = Shape.num b := Fin.ext (congrArg Prod.snd h)
    cast (congrArg₂ (fun i j => obj i ⟶ obj j) h₁ h₂) x.2.2

end Interpretation

/-! ## Lists of faces that hold -/

section AllHold

variable {W : Type*} [Quiver W] {C : Type u} [Category.{v} C]

/-- Every face of a list holds in `G`, as a conjunction, so that a proof can be
given face by face. -/
def AllHold (G : W ⥤q C) : List (Face W) → Prop
  | [] => True
  | φ :: l => φ.Holds G ∧ AllHold G l

theorem forall_of_allHold {G : W ⥤q C} : ∀ {l : List (Face W)}, AllHold G l → ∀ φ ∈ l, φ.Holds G
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, ⟨h₀, h⟩, _, hφ => by
    rcases List.mem_cons.1 hφ with rfl | hφ
    · exact h₀
    · exact forall_of_allHold h _ hφ

end AllHold

/-! ## Composites without identities

`eval` composes a path starting from an identity, so the composite of a path of one
arrow is `𝟙 _ ≫ G.map f`, which is equal but not definitionally equal to
`G.map f`. `evalNE` composes a nonempty path without the identity, associating to
the left: the composite of `f, g, h` is `(G.map f ≫ G.map g) ≫ G.map h`. An
equation between such composites can then be checked against the images of the
arrows by definitional unfolding alone. -/

section EvalNE

variable {W : Type*} [Quiver W] {C : Type u} [Category.{v} C] (G : W ⥤q C)

/-- The composite of a path, without a leading identity, associated to the left. -/
def evalNE {a : W} : ∀ {b : W}, Path a b → (G.obj a ⟶ G.obj b)
  | _, .nil => 𝟙 _
  | _, .cons .nil f => G.map f
  | _, .cons (.cons p g) f => evalNE (.cons p g) ≫ G.map f

theorem evalNE_eq_eval {a : W} : ∀ {b : W} (p : Path a b), evalNE G p = eval G p
  | _, .nil => rfl
  | _, .cons .nil f => by simp [evalNE]
  | _, .cons (.cons p g) f => by simp only [evalNE, evalNE_eq_eval (.cons p g), eval_cons]

variable {G}

/-- A face holds when its two sides have equal composites without identities. -/
theorem holds_of_evalNE (φ : Face W) (h : evalNE G φ.lhs = evalNE G φ.rhs) : φ.Holds G := by
  rw [Face.Holds, ← evalNE_eq_eval, ← evalNE_eq_eval, h]

/-- In a commuting diagram, parallel paths have equal composites without identities. -/
theorem Commutes.evalNE_eq (hC : Commutes G) {a b : W} (p q : Path a b) :
    evalNE G p = evalNE G q := by
  rw [evalNE_eq_eval, evalNE_eq_eval]; exact hC p q

end EvalNE

/-! ## Commuting diagrams as values -/

/-- A commuting diagram in `C`, as a value: a graph (`n` vertices, arrows listed by
their ends in `E`), objects for its vertices, a morphism for each arrow, and a
proof that the diagram commutes. `comm_diagram` builds one from equations; bind
it with `let`, so that its morphisms stay visible to `diagram_eq` and to further
gluing. -/
structure CommDiagram (C : Type u) [Category.{v} C] where
  /-- The number of vertices. -/
  n : ℕ
  /-- The ends of the arrows. -/
  E : List (ℕ × ℕ)
  /-- The object at each vertex. -/
  obj : Fin n → C
  /-- The morphism of each arrow, with the vertices of its ends. -/
  mors : List (Σ a b : Fin n, obj a ⟶ obj b)
  /-- The listed ends are `E`. -/
  ends : endsOf mors = E
  /-- The diagram commutes. -/
  commutes : Commutes (toPrefunctor obj mors ends)

end Diagrams
