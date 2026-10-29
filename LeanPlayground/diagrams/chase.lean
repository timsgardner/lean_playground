/-
# Recorded diagram chases

A diagram chase rewrites one path into another, one face at a time. This file
makes faces and chases into data, in the style of a computad: a *face* names two
parallel paths of the shape, a *step* applies one face (forwards or backwards)
inside a longer path, and a *chase* is a list of steps whose endpoints line up.

Recording the chase, instead of only the equation it proves, keeps the
information about the proof: which faces were used, where, and in what order.
The record can be inspected (`Chase.used`), and turned into the equation it
proves by `Chase.sound`. That needs only the faces the chase actually uses.

Chases compose like the 2-cells of a free 2-category: `Chase.trans` composes them
vertically, `Chase.symm` reverses one (faces stand for equalities, so every step
can be undone), and `Chase.whiskerLeft` and `Chase.whiskerRight` put a chase in
context, which is Riehl's Lemma 1.6.11.

Chases are also *complete*: if every diagram in which the faces hold satisfies
`eval G p = eval G q`, then some chase joins `p` to `q` (`Chase.complete`). The
proof builds a free model, the category of paths modulo "joined by a chase", in
which the faces hold and nothing else does. So a chase is a lossless record:
every consequence of the faces has one. `ChasesOn faces S` says that chases join
every pair of parallel paths within `S`; by soundness and completeness it means
exactly that `G` commutes on `S` for every `G` in which the faces hold
(`chasesOn_iff`).

The file ends with Riehl's rectangle (1.6.10): the two-step chase `f ◁ R`, then
`L ▷ m`, recovers the outer equation from the two squares.
-/

import LeanPlayground.diagrams.core
import Mathlib.CategoryTheory.Quotient

open CategoryTheory Quiver

namespace Diagrams

universe w v₁ v₂ u₁ u₂

variable {W : Type u₁} [Quiver.{v₁} W] {C : Type u₂} [Category.{v₂} C]

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

/-! ## Steps and chases -/

variable {Φ : Type w} (faces : Φ → Face W)

/-- One step of a chase from `p` to `q`: the face `face` is applied, forwards
or backwards, between the context paths `pre` and `post`. -/
structure Step {a b : W} (p q : Path a b) where
  /-- The face applied. -/
  face : Φ
  /-- Whether the face is applied from `rhs` to `lhs`. -/
  backward : Bool
  /-- The part of the path before the rewritten stretch. -/
  pre : Path a (faces face).src
  /-- The part of the path after the rewritten stretch. -/
  post : Path (faces face).tgt b
  hp : p = pre.comp (((faces face).side backward).comp post)
  hq : q = pre.comp (((faces face).side (!backward)).comp post)

/-- A chase from `p` to `q`: a list of steps whose endpoints line up. -/
inductive Chase {a b : W} : Path a b → Path a b → Type (max w u₁ v₁)
  | refl (p : Path a b) : Chase p p
  | cons {p q r : Path a b} : Step faces p q → Chase q r → Chase p r

variable {faces}

namespace Step

variable {a b : W} {p q : Path a b}

/-- Undo a step: apply the same face in the other direction. -/
def symm (s : Step faces p q) : Step faces q p where
  face := s.face
  backward := !s.backward
  pre := s.pre
  post := s.post
  hp := s.hq
  hq := by rw [Bool.not_not]; exact s.hp

/-- Put a step after a path `r`. -/
def whiskerLeft {x : W} (r : Path x a) (s : Step faces p q) :
    Step faces (r.comp p) (r.comp q) where
  face := s.face
  backward := s.backward
  pre := r.comp s.pre
  post := s.post
  hp := by rw [Path.comp_assoc]; exact congrArg r.comp s.hp
  hq := by rw [Path.comp_assoc]; exact congrArg r.comp s.hq

/-- Put a step before a path `r`. -/
def whiskerRight {y : W} (s : Step faces p q) (r : Path b y) :
    Step faces (p.comp r) (q.comp r) where
  face := s.face
  backward := s.backward
  pre := s.pre
  post := s.post.comp r
  hp := (congrArg (·.comp r) s.hp).trans (by simp only [Path.comp_assoc])
  hq := (congrArg (·.comp r) s.hq).trans (by simp only [Path.comp_assoc])

/-- A step preserves the composite, provided its face holds. -/
theorem sound {G : W ⥤q C} (s : Step faces p q) (h : (faces s.face).Holds G) :
    eval G p = eval G q := by
  rw [congrArg (eval G) s.hp, congrArg (eval G) s.hq, eval_comp, eval_comp, eval_comp,
    eval_comp, h.side s.backward (!s.backward)]

end Step

namespace Chase

variable {a b : W}

/-- The faces a chase uses, in order, with repetitions. -/
def used : ∀ {p q : Path a b}, Chase faces p q → List Φ
  | _, _, refl _ => []
  | _, _, cons s c => s.face :: c.used

/-- The number of steps in a chase. -/
def length : ∀ {p q : Path a b}, Chase faces p q → ℕ
  | _, _, refl _ => 0
  | _, _, cons _ c => c.length + 1

/-- Vertical composition: one chase followed by another. -/
def trans : ∀ {p q r : Path a b}, Chase faces p q → Chase faces q r → Chase faces p r
  | _, _, _, refl _, d => d
  | _, _, _, cons s c, d => cons s (c.trans d)

/-- A chase run backwards. -/
def symm : ∀ {p q : Path a b}, Chase faces p q → Chase faces q p
  | _, _, refl _ => refl _
  | _, _, cons s c => c.symm.trans (cons s.symm (refl _))

/-- Put a chase after a path `t`. -/
def whiskerLeft {x : W} (t : Path x a) :
    ∀ {p q : Path a b}, Chase faces p q → Chase faces (t.comp p) (t.comp q)
  | _, _, refl _ => refl _
  | _, _, cons s c => cons (s.whiskerLeft t) (c.whiskerLeft t)

/-- Put a chase before a path `t`. -/
def whiskerRight {y : W} (t : Path b y) :
    ∀ {p q : Path a b}, Chase faces p q → Chase faces (p.comp t) (q.comp t)
  | _, _, refl _ => refl _
  | _, _, cons s c => cons (s.whiskerRight t) (c.whiskerRight t)

/-- A chase proves the equation between its endpoints, given that the faces it
uses hold. -/
theorem sound {G : W ⥤q C} {p q : Path a b} (c : Chase faces p q)
    (h : ∀ φ ∈ c.used, (faces φ).Holds G) : eval G p = eval G q := by
  induction c with
  | refl _ => rfl
  | cons s c ih =>
    exact (s.sound (h _ (List.mem_cons_self ..))).trans
      (ih fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

/-- A chase proves the equation between its endpoints, given that all faces hold. -/
theorem sound' {G : W ⥤q C} {p q : Path a b} (c : Chase faces p q)
    (h : ∀ φ, (faces φ).Holds G) : eval G p = eval G q :=
  c.sound fun φ _ => h φ


/-! ### Bookkeeping -/

@[simp] theorem used_refl (p : Path a b) : (refl p : Chase faces p p).used = [] := rfl

@[simp] theorem used_cons {p q r : Path a b} (s : Step faces p q) (c : Chase faces q r) :
    (cons s c).used = s.face :: c.used := rfl

@[simp] theorem used_trans : ∀ {p q r : Path a b} (c : Chase faces p q) (d : Chase faces q r),
    (c.trans d).used = c.used ++ d.used
  | _, _, _, refl _, _ => rfl
  | _, _, _, cons s c, d => by simp [trans, used_trans c d]

@[simp] theorem Step.symm_face {p q : Path a b} (s : Step faces p q) : s.symm.face = s.face := rfl

@[simp] theorem used_symm : ∀ {p q : Path a b} (c : Chase faces p q), c.symm.used = c.used.reverse
  | _, _, refl _ => rfl
  | _, _, cons s c => by simp [symm, used_symm c]

@[simp] theorem used_whiskerLeft {x : W} (t : Path x a) :
    ∀ {p q : Path a b} (c : Chase faces p q), (c.whiskerLeft t).used = c.used
  | _, _, refl _ => rfl
  | _, _, cons s c => by simp [whiskerLeft, used_whiskerLeft t c]; rfl

@[simp] theorem used_whiskerRight {y : W} (t : Path b y) :
    ∀ {p q : Path a b} (c : Chase faces p q), (c.whiskerRight t).used = c.used
  | _, _, refl _ => rfl
  | _, _, cons s c => by simp [whiskerRight, used_whiskerRight t c]; rfl

/-- The length of a chase is the number of faces it uses, counted with repetition. -/
theorem length_eq_length_used : ∀ {p q : Path a b} (c : Chase faces p q), c.length = c.used.length
  | _, _, refl _ => rfl
  | _, _, cons _ c => by simp [length, length_eq_length_used c]

/-! ### Renaming faces -/

variable {Ψ : Type*} {faces' : Ψ → Face W}

/-- A step that uses the faces `faces' ∘ f` uses the faces `faces'`. -/
def _root_.Diagrams.Step.comap (f : Φ → Ψ) {p q : Path a b} (s : Step (faces' ∘ f) p q) :
    Step faces' p q :=
  ⟨f s.face, s.backward, s.pre, s.post, s.hp, s.hq⟩

/-- A chase that uses the faces `faces' ∘ f` uses the faces `faces'`. -/
def comap (f : Φ → Ψ) : ∀ {p q : Path a b}, Chase (faces' ∘ f) p q → Chase faces' p q
  | _, _, refl _ => refl _
  | _, _, cons s c => cons (s.comap f) (c.comap f)

@[simp] theorem used_comap (f : Φ → Ψ) :
    ∀ {p q : Path a b} (c : Chase (faces' ∘ f) p q), (c.comap f).used = c.used.map f
  | _, _, refl _ => rfl
  | _, _, cons s c => by simp [comap, used_comap f c]; rfl

end Chase

/-- If all faces hold, and every pair of parallel paths within `S` is joined by a
chase, then `G` commutes on `S`. -/
theorem CommutesOn.of_chases {G : W ⥤q C} {S : Subshape W} (h : ∀ φ, (faces φ).Holds G)
    (hc : ∀ {a b : W} (p q : Path a b), Within S p → Within S q → Nonempty (Chase faces p q)) :
    CommutesOn G S := fun _ _ p q hp hq =>
  let ⟨c⟩ := hc p q hp hq
  c.sound' h

/-! ## Completeness -/

/-- The chase that applies one face, from its `lhs` to its `rhs`. -/
def Chase.ofFace (φ : Φ) : Chase faces (faces φ).lhs (faces φ).rhs :=
  .cons ⟨φ, false, .nil, .nil, by simp [Face.side], by simp [Face.side]⟩ (.refl _)

section Free

variable (faces)

/-- Two paths are related when some chase joins them. -/
def chaseRel : HomRel (Paths W) := fun _ _ p q => Nonempty (Chase faces p q)

instance : Congruence (chaseRel faces) where
  equivalence := ⟨fun p => ⟨.refl p⟩, fun ⟨c⟩ => ⟨c.symm⟩, fun ⟨c⟩ ⟨d⟩ => ⟨c.trans d⟩⟩
  comp_left f _ _ := fun ⟨c⟩ => ⟨c.whiskerLeft f⟩
  comp_right g := fun ⟨c⟩ => ⟨c.whiskerRight g⟩

/-- The free model of the faces: paths modulo "joined by a chase". -/
abbrev FreeCat : Type u₁ := CategoryTheory.Quotient (chaseRel faces)

/-- The free diagram: each arrow goes to the class of its one-arrow path. -/
def freeDiagram : W ⥤q FreeCat faces :=
  Paths.of W ⋙q (Quotient.functor (chaseRel faces)).toPrefunctor

theorem eval_paths_of : ∀ {a b : W} (p : Path a b), eval (Paths.of W) p = p
  | _, _, .nil => rfl
  | _, _, .cons p f => by rw [eval_cons, eval_paths_of p]; rfl

theorem eval_freeDiagram {a b : W} (p : Path a b) :
    eval (freeDiagram faces) p = (Quotient.functor (chaseRel faces)).map p := by
  unfold freeDiagram
  rw [eval_map, eval_paths_of]
  rfl

/-- In the free model, two paths have the same composite exactly when a chase
joins them. -/
theorem freeDiagram_eq_iff {a b : W} (p q : Path a b) :
    eval (freeDiagram faces) p = eval (freeDiagram faces) q ↔ Nonempty (Chase faces p q) := by
  rw [eval_freeDiagram, eval_freeDiagram]
  exact Quotient.functor_map_eq_iff (chaseRel faces) (X := a) (Y := b) p q

/-- Every face holds in the free model. -/
theorem freeDiagram_holds (φ : Φ) : (faces φ).Holds (freeDiagram faces) :=
  (freeDiagram_eq_iff faces _ _).2 ⟨Chase.ofFace φ⟩

end Free

/-- **Completeness.** If the equation between `p` and `q` holds in every diagram
in which the faces hold, then some chase joins `p` to `q`. -/
theorem Chase.complete {a b : W} {p q : Path a b}
    (h : ∀ (D : Type u₁) [Category.{max u₁ v₁} D] (G : W ⥤q D),
      (∀ φ, (faces φ).Holds G) → eval G p = eval G q) :
    Nonempty (Chase faces p q) :=
  (freeDiagram_eq_iff faces p q).1 (h _ (freeDiagram faces) (freeDiagram_holds faces))

/-- Soundness and completeness together. -/
theorem nonempty_chase_iff {a b : W} {p q : Path a b} :
    Nonempty (Chase faces p q) ↔
      ∀ (D : Type u₁) [Category.{max u₁ v₁} D] (G : W ⥤q D),
        (∀ φ, (faces φ).Holds G) → eval G p = eval G q :=
  ⟨fun ⟨c⟩ _ _ _ hG => c.sound' hG, Chase.complete⟩

/-! ## Chasing on a subshape -/

variable (faces) in
/-- Chases join every pair of parallel paths within `S`. -/
def ChasesOn (S : Subshape W) : Prop :=
  ∀ ⦃a b : W⦄ (p q : Path a b), Within S p → Within S q → Nonempty (Chase faces p q)

variable {S T : Subshape W}

/-- If chases join the parallel paths within `S`, then any diagram in which the
faces hold commutes on `S`. -/
theorem ChasesOn.commutesOn (h : ChasesOn faces S) {G : W ⥤q C} (hG : ∀ φ, (faces φ).Holds G) :
    CommutesOn G S := fun _ _ p q hp hq =>
  let ⟨c⟩ := h p q hp hq
  c.sound' hG

/-- Chases join the parallel paths within `S` exactly when the free model commutes
on `S`. -/
theorem chasesOn_iff_free : ChasesOn faces S ↔ CommutesOn (freeDiagram faces) S :=
  ⟨fun h => h.commutesOn (freeDiagram_holds faces),
    fun h _ _ p q hp hq => (freeDiagram_eq_iff faces p q).1 (h p q hp hq)⟩

/-- Chases join the parallel paths within `S` exactly when every diagram in which
the faces hold commutes on `S`. -/
theorem chasesOn_iff : ChasesOn faces S ↔
    ∀ (D : Type u₁) [Category.{max u₁ v₁} D] (G : W ⥤q D),
      (∀ φ, (faces φ).Holds G) → CommutesOn G S :=
  ⟨fun h _ _ _ hG => h.commutesOn hG,
    fun h => chasesOn_iff_free.2 (h _ (freeDiagram faces) (freeDiagram_holds faces))⟩

theorem ChasesOn.mono (h : S ≤ T) (hT : ChasesOn faces T) : ChasesOn faces S :=
  fun _ _ p q hp hq => hT p q (hp.mono h) (hq.mono h)

theorem chasesOn_bot : ChasesOn faces ⊥ :=
  chasesOn_iff_free.2 commutesOn_bot

theorem ChasesOn.comap {Ψ : Type*} {faces' : Ψ → Face W} (f : Φ → Ψ)
    (h : ChasesOn (faces' ∘ f) S) : ChasesOn faces' S := fun _ _ p q hp hq =>
  let ⟨c⟩ := h p q hp hq
  ⟨c.comap f⟩

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
-/

namespace RectExample

/-- The six objects. -/
inductive V | a | b | c | a' | b' | c'

/-- The seven arrows. -/
inductive H : V → V → Type
  | f : H .a .b
  | j : H .b .c
  | g : H .a .a'
  | h : H .b .b'
  | l : H .c .c'
  | k : H .a' .b'
  | m : H .b' .c'

instance : Quiver V := ⟨H⟩

/-- An arrow, as a path of length one. -/
def H.path {x y : V} (e : H x y) : Path x y := Quiver.Hom.toPath (V := V) e

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

end RectExample

end Diagrams
