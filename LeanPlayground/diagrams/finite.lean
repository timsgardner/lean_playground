/-
# Finite shapes and computable subshapes

The theorems in `core`, `extend` and `paste` are about arbitrary shapes. To decide
their hypotheses, or to search for chases, we need to compute on shapes. This
file supplies the computational view.

* `arrow f` bundles an arrow with its endpoints, as an element of Mathlib's
  `Quiver.Total W`. Arrows between different vertices can then be compared, and
  `Quiver.Total W` has decidable equality when vertices and arrows do.
* `FinShape W` lists all vertices and all arrows of a finite shape.
* `ofList A` is the subshape of the arrows in a list `A`. Growing a subshape is
  then list manipulation: `ofList_append` and `ofList_cons` turn `++` and `::`
  into `⊔` and `⊔ single`.
* Membership in `ofList`, `single`, `⊔`, `⊓`, `⊥` and `⊤` is decidable.
* `Path.edges p` lists the arrows of a path, from start to end. A path is
  determined by its endpoints and its edges (`Quiver.Path.eq_of_edges`), so paths
  have decidable equality, and `Within S p` is decidable.
-/

import LeanPlayground.diagrams.core
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.EquivFin

open CategoryTheory Quiver

namespace Diagrams

universe v₁ u₁

variable {W : Type u₁} [Quiver.{v₁} W]

/-! ## Arrows as data -/

/-- The arrow `f`, bundled with its endpoints. -/
abbrev arrow {a b : W} (f : a ⟶ b) : Total W := ⟨a, b, f⟩

theorem arrow_eq_arrow {a b a' b' : W} {f : a ⟶ b} {g : a' ⟶ b'} :
    arrow f = arrow g ↔ a = a' ∧ b = b' ∧ HEq f g := by
  simp [arrow, Total.mk.injEq]

theorem arrow_inj {a b : W} {f g : a ⟶ b} : arrow f = arrow g ↔ f = g := by
  simp

theorem isArrow_iff {u v a b : W} {e : u ⟶ v} {f : a ⟶ b} : IsArrow e f ↔ arrow f = arrow e := by
  constructor
  · rintro ⟨⟩; rfl
  · intro h
    obtain ⟨rfl, rfl, h⟩ := arrow_eq_arrow.1 h
    cases eq_of_heq h
    exact .refl

instance [DecidableEq W] [∀ a b : W, DecidableEq (a ⟶ b)] : DecidableEq (Total W)
  | ⟨a, b, f⟩, ⟨a', b', f'⟩ =>
    if ha : a = a' then
      if hb : b = b' then by
        subst ha hb
        exact decidable_of_iff (f = f') (by simp [Total.mk.injEq])
      else isFalse (by simp [Total.mk.injEq, hb])
    else isFalse (by simp [Total.mk.injEq, ha])

/-! ## Finite shapes -/

/-- A finite shape: complete lists of its vertices and arrows. -/
class FinShape (W : Type u₁) [Quiver.{v₁} W] where
  /-- All vertices. -/
  vertices : List W
  mem_vertices : ∀ a, a ∈ vertices
  /-- All arrows, with their endpoints. -/
  arrows : List (Total W)
  mem_arrows : ∀ e : Total W, e ∈ arrows

/-- For each vertex, a list containing at least the arrows leaving it. Shapes that
can list these directly make reachability much cheaper; every finite shape has the
default instance, which lists all arrows for every vertex. -/
class OutArrows (W : Type u₁) [Quiver.{v₁} W] where
  /-- A list containing the arrows leaving `a`. -/
  out : W → List (Total W)
  mem_out : ∀ e : Total W, e ∈ out e.left

instance (priority := 100) [FinShape W] : OutArrows W :=
  ⟨fun _ => FinShape.arrows, FinShape.mem_arrows⟩

namespace FinShape

variable [FinShape W]

/-- The vertices of a finite shape form a `Fintype`. -/
instance (priority := 100) fintype [DecidableEq W] : Fintype W :=
  Fintype.ofList vertices mem_vertices

theorem forall_vertex {P : W → Prop} : (∀ a, P a) ↔ ∀ a ∈ vertices, P a :=
  ⟨fun h a _ => h a, fun h a => h a (mem_vertices a)⟩

theorem exists_vertex {P : W → Prop} : (∃ a, P a) ↔ ∃ a ∈ vertices, P a :=
  ⟨fun ⟨a, h⟩ => ⟨a, mem_vertices a, h⟩, fun ⟨a, _, h⟩ => ⟨a, h⟩⟩

theorem forall_arrow {P : ∀ {a b : W}, (a ⟶ b) → Prop} :
    (∀ (a b : W) (f : a ⟶ b), P f) ↔ ∀ e ∈ (arrows : List (Total W)), P e.hom :=
  ⟨fun h e _ => h _ _ e.hom, fun h _ _ f => h (arrow f) (mem_arrows _)⟩

theorem exists_arrow {P : ∀ {a b : W}, (a ⟶ b) → Prop} :
    (∃ (a b : W) (f : a ⟶ b), P f) ↔ ∃ e ∈ (arrows : List (Total W)), P e.hom :=
  ⟨fun ⟨_, _, f, h⟩ => ⟨arrow f, mem_arrows _, h⟩, fun ⟨e, _, h⟩ => ⟨_, _, e.hom, h⟩⟩

/-- Quantifiers over the vertices of a finite shape are decidable. -/
instance decidableForallVertex {P : W → Prop} [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff _ forall_vertex.symm

instance decidableExistsVertex {P : W → Prop} [DecidablePred P] : Decidable (∃ a, P a) :=
  decidable_of_iff _ exists_vertex.symm

end FinShape

/-! ## Subshapes from lists -/

/-- The subshape consisting of the arrows in `A`. -/
def ofList (A : List (Total W)) : Subshape W := fun _ _ => {f | arrow f ∈ A}

variable {A B : List (Total W)} {S T : Subshape W}

@[simp] theorem mem_ofList {a b : W} {f : a ⟶ b} : f ∈ ofList A a b ↔ arrow f ∈ A := Iff.rfl

@[simp] theorem mem_single {u v a b : W} {e : u ⟶ v} {f : a ⟶ b} :
    f ∈ single e a b ↔ arrow f = arrow e := isArrow_iff

@[simp] theorem ofList_nil : ofList ([] : List (Total W)) = ⊥ := by
  funext a b; ext f; simp

@[simp] theorem ofList_append : ofList (A ++ B) = ofList A ⊔ ofList B := by
  funext a b; ext f; simp

@[simp] theorem ofList_cons {u v : W} (e : u ⟶ v) :
    ofList (arrow e :: A) = single e ⊔ ofList A := by
  funext a b; ext f; simp

theorem ofList_arrows [FinShape W] : ofList (FinShape.arrows : List (Total W)) = ⊤ := by
  funext a b; ext f; simp [FinShape.mem_arrows]

/-! ## Decidable membership -/

section Decidable

variable {a b : W} {f : a ⟶ b}

instance [DecidableEq (Total W)] : Decidable (f ∈ ofList A a b) :=
  inferInstanceAs (Decidable (arrow f ∈ A))

instance [DecidableEq (Total W)] {u v : W} {e : u ⟶ v} : Decidable (f ∈ single e a b) :=
  decidable_of_iff _ mem_single.symm

instance [Decidable (f ∈ S a b)] [Decidable (f ∈ T a b)] : Decidable (f ∈ (S ⊔ T) a b) :=
  decidable_of_iff _ mem_sup.symm

instance [Decidable (f ∈ S a b)] [Decidable (f ∈ T a b)] : Decidable (f ∈ (S ⊓ T) a b) :=
  inferInstanceAs (Decidable (f ∈ S a b ∧ f ∈ T a b))

instance : Decidable (f ∈ (⊥ : Subshape W) a b) := isFalse fun h => h

instance : Decidable (f ∈ (⊤ : Subshape W) a b) := isTrue trivial

end Decidable

/-! ## Paths as lists of edges -/

/-- The arrows of a path, from start to end. -/
def _root_.Quiver.Path.edges {a : W} : ∀ {b : W}, Path a b → List (Total W)
  | _, .nil => []
  | _, .cons p f => p.edges ++ [arrow f]

namespace PathEdges

variable {a b c : W}

@[simp] theorem edges_nil : (Path.nil : Path a a).edges = [] := rfl

@[simp] theorem edges_cons (p : Path a b) (f : b ⟶ c) : (p.cons f).edges = p.edges ++ [arrow f] :=
  rfl

@[simp] theorem edges_toPath (f : a ⟶ b) : f.toPath.edges = [arrow f] := rfl

@[simp] theorem edges_comp (p : Path a b) : ∀ {c} (q : Path b c),
    (p.comp q).edges = p.edges ++ q.edges
  | _, .nil => by simp
  | _, .cons q f => by simp [edges_comp p q]

@[simp] theorem length_edges : ∀ {b} (p : Path a b), p.edges.length = p.length
  | _, .nil => rfl
  | _, .cons p f => by simp [length_edges p]

end PathEdges

open PathEdges

/-- A path is determined by its endpoints and its edges. -/
theorem _root_.Quiver.Path.eq_of_edges {a : W} :
    ∀ {b : W} {p q : Path a b}, p.edges = q.edges → p = q
  | _, .nil, .nil, _ => rfl
  | _, .nil, .cons q g, h => by simp at h
  | _, .cons p f, .nil, h => by simp at h
  | _, .cons p f, .cons q g, h => by
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    obtain ⟨rfl, -, hfg⟩ := arrow_eq_arrow.1 (List.singleton_inj.1 h₂)
    cases eq_of_heq hfg
    exact congrArg (·.cons f) (Quiver.Path.eq_of_edges h₁)

theorem within_cons_iff {a b c : W} {p : Path a b} {f : b ⟶ c} :
    Within S (p.cons f) ↔ Within S p ∧ f ∈ S b c :=
  ⟨fun h => by cases h with | cons hp hf => exact ⟨hp, hf⟩, fun ⟨hp, hf⟩ => hp.cons hf⟩

/-- A path lies within `S` exactly when each of its edges does. -/
theorem within_iff_edges {a : W} : ∀ {b : W} {p : Path a b},
    Within S p ↔ ∀ e ∈ p.edges, e.hom ∈ S e.left e.right
  | _, .nil => by simp [Within.nil]
  | _, .cons p f => by simp [within_cons_iff, within_iff_edges (p := p), or_imp, forall_and]

instance [DecidableEq (Total W)] {a b : W} : DecidableEq (Path a b) := fun p q =>
  decidable_of_iff (p.edges = q.edges) ⟨Path.eq_of_edges, congrArg _⟩

instance {a b : W} {p : Path a b} [∀ (a b : W) (f : a ⟶ b), Decidable (f ∈ S a b)] :
    Decidable (Within S p) :=
  decidable_of_iff _ within_iff_edges.symm

end Diagrams
