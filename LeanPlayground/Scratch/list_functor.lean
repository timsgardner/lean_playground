import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.List.FinRange

open CategoryTheory

namespace ListFunctorYoneda

universe u

local notation "cchom" => ConcreteCategory.hom

def blort (a: Nat) : Nat -> Nat := fun b => a + b

/-- The covariant list functor on types. -/
def ListF : Type u ⥤ Type u where
  obj X := List X
  map f := TypeCat.ofHom (List.map f)
  map_id X := by
    ext xs
    simp
  map_comp f g := by
    ext xs
    simp [List.map_map]

/-- The data classified by co-Yoneda at input length `n`: a list of valid
input positions, allowing deletion, reordering, and duplication. -/
abbrev PositionList (n : Nat) := List (Fin n)

/-- A family of positional operations, one for each possible input length. -/
abbrev PositionScheme := (n : Nat) → PositionList n

/-- Erase bounds after a scheme has selected valid positions. This lets the
permissive list draw API handle length-preserving maps without transporting
along an equality of lengths. -/
def PositionScheme.toLoose
    (scheme : PositionScheme) : Nat → List Nat :=
  fun n => (scheme n).map Fin.val

/-- Draw from a list using its scheme-selected valid positions. -/
def PositionScheme.draw
    (scheme : PositionScheme)
    {α : Type u}
    (xs : List α) : List α :=
  (scheme.toLoose xs.length).filterMap fun i => xs[i]?

/-- The permissive draw recovers ordinary mapping when every position is a
valid member of `Fin xs.length`. -/
theorem PositionScheme.draw_eq_positions
    (scheme : PositionScheme)
    {α : Type u}
    (xs : List α) :
    scheme.draw xs = (scheme xs.length).map (fun i => xs[i]) := by
  unfold PositionScheme.draw PositionScheme.toLoose
  rw [List.filterMap_map]
  calc
    List.filterMap ((fun i => xs[i]?) ∘ Fin.val) (scheme xs.length) =
        (scheme xs.length).filterMap (some ∘ fun i => xs[i]) := by
      apply List.filterMap_congr
      intro i _
      change xs[i]? = some xs[i]
      exact List.getElem?_eq_getElem i.isLt
    _ = (scheme xs.length).map (fun i => xs[i]) := by
      rw [List.filterMap_eq_map]

/-- Every position scheme is natural with respect to mapping the elements. -/
theorem PositionScheme.draw_map
    (scheme : PositionScheme)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (scheme.draw xs).map f = scheme.draw (xs.map f) := by
  unfold PositionScheme.draw
  rw [List.length_map]
  simp [List.map_filterMap]

/-- A scheme represents an operation when it gives that operation's output on
every list. -/
def PositionScheme.Represents
    (scheme : PositionScheme)
    (operation : ∀ {α : Type u}, List α → List α) : Prop :=
  ∀ {α : Type u} (xs : List α), operation xs = scheme.draw xs

/-- An operation represented by positions is automatically natural. -/
theorem PositionScheme.Represents.natural
    {scheme : PositionScheme}
    {operation : ∀ {α : Type u}, List α → List α}
    (h : scheme.Represents operation)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (operation xs).map f = operation (xs.map f) := by
  calc
    (operation xs).map f = (scheme.draw xs).map f :=
      congrArg (fun ys => ys.map f) (h xs)
    _ = scheme.draw (xs.map f) := scheme.draw_map f xs
    _ = operation (xs.map f) := (h (xs.map f)).symm

/-- A represented operation packaged as a natural transformation of `ListF`. -/
def PositionScheme.natTransOfRepresents
    (scheme : PositionScheme)
    (operation : ∀ {α : Type u}, List α → List α)
    (h : scheme.Represents operation) : ListF ⟶ ListF where
  app X := TypeCat.ofHom fun xs : List X => operation xs
  naturality {X Y} f := by
    ext xs
    exact (h.natural (cchom f) xs).symm

/- Co-Yoneda says that a natural operation from `Fin n`-indexed inputs to
lists is determined by its value on the identity input. That value is exactly
a `List (Fin n)`, which is our `PositionList n`. -/

noncomputable def yonedaDrawAt
    (n : Nat)
    (positions : PositionList n) :
    coyoneda.obj (Opposite.op (Fin n)) ⟶ ListF :=
  (coyonedaEquiv (C := Type) (X := Fin n) (F := ListF)).symm positions

/-- The co-Yoneda transformation classified by `positions` maps a tuple by
reading exactly those positions. -/
theorem yonedaDrawAt_apply
    (n : Nat)
    (positions : PositionList n)
    (X : Type)
    (f : Fin n → X) :
    cchom ((yonedaDrawAt n positions).app X) (TypeCat.ofHom f) =
      positions.map f := by
  exact coyonedaEquiv_symm_app_apply
    (C := Type) (X := Fin n) (F := ListF) positions X (TypeCat.ofHom f)

/-- Evaluating the scheme's co-Yoneda transformation at a list's indexing map
is the same as `PositionScheme.draw`. -/
theorem PositionScheme.draw_eq_yoneda
    (scheme : PositionScheme)
    (X : Type)
    (xs : List X) :
    scheme.draw xs =
      cchom ((yonedaDrawAt xs.length (scheme xs.length)).app X)
        (TypeCat.ofHom fun i => xs[i]) := by
  rw [scheme.draw_eq_positions]
  exact (yonedaDrawAt_apply xs.length (scheme xs.length) X
    (fun i => xs[i])).symm

/-- Reverse selects all positions in descending order. -/
def reverseScheme : PositionScheme :=
  fun n => (List.finRange n).reverse

theorem reverseScheme_represents_reverse
    {α : Type u}
    (xs : List α) :
    xs.reverse = reverseScheme.draw xs := by
  rw [PositionScheme.draw_eq_positions]
  change xs.reverse = (List.finRange xs.length).reverse.map (fun i => xs[i])
  rw [List.map_reverse]
  exact (congrArg List.reverse (List.map_getElem_finRange xs)).symm

theorem reverse_natural
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    xs.reverse.map f = (xs.map f).reverse :=
  PositionScheme.Represents.natural reverseScheme_represents_reverse f xs

/-- Take selects the first `k` valid positions. -/
def takeScheme (k : Nat) : PositionScheme :=
  fun n => (List.finRange n).take k

theorem takeScheme_represents_take
    (k : Nat)
    {α : Type u}
    (xs : List α) :
    xs.take k = (takeScheme k).draw xs := by
  rw [PositionScheme.draw_eq_positions]
  change xs.take k = ((List.finRange xs.length).take k).map (fun i => xs[i])
  rw [List.map_take]
  exact (congrArg (List.take k) (List.map_getElem_finRange xs)).symm

theorem take_natural
    (k : Nat)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (xs.take k).map f = (xs.map f).take k :=
  PositionScheme.Represents.natural (takeScheme_represents_take k) f xs

/-- Drop selects the positions remaining after the first `k`. -/
def dropScheme (k : Nat) : PositionScheme :=
  fun n => (List.finRange n).drop k

theorem dropScheme_represents_drop
    (k : Nat)
    {α : Type u}
    (xs : List α) :
    xs.drop k = (dropScheme k).draw xs := by
  rw [PositionScheme.draw_eq_positions]
  change xs.drop k = ((List.finRange xs.length).drop k).map (fun i => xs[i])
  rw [List.map_drop]
  exact (congrArg (List.drop k) (List.map_getElem_finRange xs)).symm

theorem drop_natural
    (k : Nat)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (xs.drop k).map f = (xs.map f).drop k :=
  PositionScheme.Represents.natural (dropScheme_represents_drop k) f xs

end ListFunctorYoneda
