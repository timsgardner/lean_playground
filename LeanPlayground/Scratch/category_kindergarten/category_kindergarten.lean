import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.List.FinRange
import ProofWidgets.Extra.CheckHighlight
import ProofWidgets.Demos.Graph.ExprGraph
import Mathlib.CategoryTheory.Functor.Currying


open CategoryTheory
open Opposite

universe u v


local notation "cchom" => ConcreteCategory.hom

/- Categories -/

section Categories

variable {C : Type u} [Category.{v} C]

variable (X Y Z : C)

#check X
#check X ⟶ Y
#check 𝟙 X


variable (f : X ⟶ Y)
variable (g : Y ⟶ Z)

#check f
#check g
#check f ≫ g


#check Category.id_comp
#check Category.comp_id
#check Category.assoc

example (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  exact Category.id_comp f

end Categories


universe u₁ v₁ u₂ v₂

/- Functors -/

section Functors

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (F : C ⥤ D)

#check F

variable (X Y Z : C)
variable (f : X ⟶ Y)
variable (g : Y ⟶ Z)

#check F.obj X
#check F.map f
#check F.map_id X
#check F.map_comp f g


def myIdentityFunctor (C : Type u) [Category.{v} C] : C ⥤ C where
  obj X := X
  map f := f
  map_id X := rfl
  map_comp f g := rfl

#check myIdentityFunctor C


#check (myIdentityFunctor C).obj X
#check (myIdentityFunctor C).map f

end Functors

/- Nat Trans -/
section NatTrans

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F G : C ⥤ D)

variable (η : NatTrans F G)

variable (X Y : C)
variable (f : X ⟶ Y)

#check η.app X
#check η.naturality f

def myIdNatTrans (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)

  naturality {X Y} f := by -- by simp works here fine, too
    calc
      F.map f ≫ 𝟙 (F.obj Y)
          = F.map f := Category.comp_id (F.map f)
      _   = 𝟙 (F.obj X) ≫ F.map f := (Category.id_comp (F.map f)).symm

end NatTrans


section TypesKindergarten

/- TypeCat.Hom wraps a TypeCat.Fun, which wraps a function between types -/

#check Nat ⟶ String
#print TypeCat.Hom
#print TypeCat.Fun


-- turns a function into a TypeCat morphism
#check TypeCat.ofHom

-- make a morphism out of a function
def increment : Nat ⟶ Nat :=
  TypeCat.ofHom (fun n => n + 1)

-- extract the underlying function
#check TypeCat.Hom.hom increment

#check (TypeCat.Hom.hom increment).toFun

-- or through the concrete-category api
#check ConcreteCategory.hom increment

-- run it
#eval increment 41
-- 42
-- concrete-category morphisms have a CoeFun instance, so this applies the morphism directly

#check TypeCat.homEquiv
-- well, evidently they're equivalent

-- morphism composition is function composition

def double : Nat ⟶ Nat :=
  TypeCat.ofHom (fun n => 2 * n)

#check increment ≫ double
-- increment ≫ double : Nat ⟶ Nat

#eval (increment ≫ double) 10
-- 22

/- here's the theorem saying morphism comp in TypeCat is ordinary function comp:
-/

#check types_comp
#check types_comp_apply


/- now make a genuine functor. Let's make a product pair thingy

F(X) = X × X

on a function f: X -> Y:

(x1​,x2​)↦(f(x1​),f(x2​)).

The signature below means that, once the universe level `u` has been ground,
`PairSelf.{u}` is an endofunctor on the category of types in `Type u`.

-/

def PairSelf : Type u ⥤ Type u where
  obj X := X × X

  map {X Y} f :=
    TypeCat.ofHom (fun p =>
      (f p.1,
       f p.2))

  map_id X := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext p

    /- change says, bet this is equal to the current goal. dsimp may also work,
    but change is more revealing here. -/

    change
      ((𝟙 X) p.1,
       (𝟙 X) p.2) = p

    apply Prod.ext
    · exact types_id_apply X p.1
    · exact types_id_apply X p.2


  /- there's much simpler ways to do this, but this is explicit -/

  map_comp {X Y Z} f g := by
    set mapFG : (X × X) ⟶ (Z × Z) :=
      ↾fun p =>
        ((f ≫ g) p.1,
         (f ≫ g) p.2)

    set mapF : (X × X) ⟶ (Y × Y) :=
      ↾fun p =>
        (f p.1,
         f p.2)

    set mapG : (Y × Y) ⟶ (Z × Z) :=
      ↾fun p =>
        (g p.1,
         g p.2)

    -- now our previously nasty goal looks like this:
    show mapFG = mapF ≫ mapG

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext p

    apply Prod.ext
    · exact types_comp_apply f g p.1
    · exact types_comp_apply f g p.2

#check PairSelf

#check PairSelf.obj Nat
#check PairSelf.map increment


#eval (PairSelf.map increment) (10, 20)
-- (11, 21)

/- we're already in a position to use this dopey functor to prove something
about a program. consider two implementations of a pair-processing program: -/

def fusedProgram : (Nat × Nat) ⟶ (Nat × Nat) :=
  PairSelf.map (increment ≫ double)

def stagedProgram : (Nat × Nat) ⟶ (Nat × Nat) :=
  PairSelf.map increment ≫ PairSelf.map double

theorem fused_eq_staged :
    fusedProgram = stagedProgram := by
  exact PairSelf.map_comp increment double


/- Now let's try Option. -/

def OptionF : Type u ⥤ Type u where
  obj X := Option X

  map {X Y} f :=
    ↾fun ox => Option.map f ox

  map_id X := by
    set mappedId : Option X ⟶ Option X :=
      (↾fun ox => Option.map (𝟙 X) ox)

    set optionId := 𝟙 (Option X)

    show mappedId = optionId

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext ox
    -- Option lets us use cases
    cases ox with
      | none => rfl
      | some x =>
          change some ((𝟙 X) x) = some x
          apply congrArg some
          exact types_id_apply X x

  map_comp {X Y Z} f g := by
    set mappedFG := (↾fun ox => Option.map (f ≫ g) ox)
    set mappedF := (↾fun ox => Option.map f ox)
    set mappedG := (↾fun ox => Option.map g ox)

    show mappedFG = mappedF ≫ mappedG

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext ox

    cases ox with
      | none => rfl
      | some x =>
          apply congrArg some
          exact types_comp_apply f g x

set_option pp.all true in
#print OptionF


/- On to nat trans.

SomeNat is a nat trans from the identity functor to OptionF: -/

def SomeNat : NatTrans (Functor.id (Type u)) OptionF where
  app X :=
    ↾fun x => some x

  naturality {X Y} f := by
    set someX : X ⟶ Option X :=
      ↾fun x => some x

    set someY : Y ⟶ Option Y :=
      ↾fun y => some y

    set mappedF : Option X ⟶ Option Y :=
      ↾fun ox => Option.map f ox

    show f ≫ someY = someX ≫ mappedF

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x

    -- rfl would close here, but that's cheating

    change
      (f ≫ someY) x = (someX ≫ mappedF) x

    rw [types_comp_apply f someY x]
    rw [types_comp_apply someX mappedF x]

    dsimp [someX, someY, mappedF]


def FstNat : NatTrans PairSelf (Functor.id (Type u)) where
  app X :=
    ↾fun p => p.1

  naturality {X Y} f := by
    set fstX : X × X ⟶ X :=
      ↾fun p => p.1

    set fstY : Y × Y ⟶ Y :=
      ↾fun p => p.1

    set mappedF : X × X ⟶ Y × Y :=
      ↾fun p => (f p.1, f p.2)

    show mappedF ≫ fstY = fstX ≫ f

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext p

    change
      (mappedF ≫ fstY) p =
      (fstX ≫ f) p

    rw [types_comp_apply mappedF fstY p]
    rw [types_comp_apply fstX f p]

    rfl

/- this fails because we can't infer the category etc

#check FstNat ≫ SomeNat
-/

-- but  this works:
#check (FstNat ≫ SomeNat : PairSelf ⟶ OptionF)

def FirstSome : PairSelf ⟶ OptionF :=
  FstNat ≫ SomeNat


#synth Category (Type u)
#synth Category (Type u ⥤ Type u)

#synth Quiver (Type u ⥤ Type u)
#synth CategoryStruct (Type u ⥤ Type u)

set_option pp.all true in
#check FirstSome

/- Anyway, now we can look at FirstSome as a theorem-producing object. -/

#check FirstSome.app
#check FirstSome.naturality

/-

So here's the commutative diagram for FirstSome. The outer rectangle is the
naturality square for FirstSome. The middle horizontal is the result of the
identity functor. The composed side verticals are FirstSome.app X and
FirstSome.app Y.

PairSelf.obj X  ─── PairSelf.map f ───▶  PairSelf.obj Y
      │                                      │
   FstNat.app X                           FstNat.app Y
      │                                      │
      ▼                                      ▼
     X            ─────── f ─────────▶       Y
      │                                      │
  SomeNat.app X                          SomeNat.app Y
      │                                      │
      ▼                                      ▼
 OptionF.obj X  ───── OptionF.map f ───▶ OptionF.obj Y


Side-note on ↾: it wraps a Lean function as a morphism in the type category.
Morphisms in a concrete category also have a `CoeFun` instance, so once wrapped
they can be applied directly like functions.

For example:
-/

def increment' : Nat ⟶ Nat :=
  ↾fun n => n + 1

#eval increment' 10
-- 11



theorem FirstSome_naturality_apply
    {X Y : Type u}
    (f : X ⟶ Y)
    (p : X × X) :
    FirstSome.app Y ((PairSelf.map f) p)
      =
    OptionF.map f ((FirstSome.app X) p) := by

  have h :=
    congrArg
      (fun k : PairSelf.obj X ⟶ OptionF.obj Y => k p)
      (FirstSome.naturality f)

  rw [types_comp_apply] at h

  exact h


/- Prove that FstNat is a split epi, without using Mathlib's IsSplitEpi API for
now.  -/

/- Start by defining the section -/
def DiagNat : NatTrans (Functor.id (Type u)) PairSelf where
  app X :=
    ↾fun x => (x, x)

  naturality {X Y} f := by
    rfl


/-- Says that DiagNat ≫ FstNat is the identity morphism in the functor category
[Type u, Type u] on the *object*  of that functor category that is the *identity
functor* in the category Type u.-/

@[reassoc]
theorem FstNat_has_section :
    DiagNat ≫ FstNat = 𝟙 (Functor.id (Type u)) := by
  -- prove equality of natural transformations
  rfl


#checkh FstNat_has_section_assoc

/- we now have everything to establish the split epi -/

def FstNat_splitEpi :
    SplitEpi
      (C := Type u ⥤ Type u)
      FstNat where
  section_ := DiagNat
  id := FstNat_has_section


/- Lists -/

/-- For this functor Lean can infer all the laws after we specify obj and map.
But we're doing it by hand anyway because it builds character-/

def ListF : Type u ⥤ Type u where
  obj X := List X
  map {X Y} f := ↾(List.map f)
  map_id X := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext xs
    have hid : (cchom (𝟙 X): X -> X) = id := by
      rfl
    rw [hid]
    dsimp
    rw [List.map_id_fun]
    rfl
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.ext_apply
    intro xs
    simp only [ConcreteCategory.coe_comp, TypeCat.ofHom_apply, types_comp_apply]
    exact List.map_map.symm

def HeadNat : NatTrans ListF OptionF where
  app X :=
    ↾fun xs : List X =>
      match xs with
      | [] => none
      | x :: _ => some x

  naturality {X Y} f := by
    set headX : ListF.obj X ⟶ OptionF.obj X :=
      ↾fun xs : List X =>
        match xs with
        | [] => none
        | x :: _ => some x

    set headY : ListF.obj Y ⟶ OptionF.obj Y :=
      ↾fun ys : List Y =>
        match ys with
        | [] => none
        | x :: _ => some x

    apply ConcreteCategory.ext_apply
    intro xs
    rw [types_comp_apply]
    rw [types_comp_apply]
    cases xs <;> rfl

#check (HeadNat).naturality

#checkh ConcreteCategory.ext_apply

def TailNat : NatTrans ListF ListF where
  app X :=
    ↾fun xs : List X =>
      match xs with
      | [] => []
      | _ :: tail => tail

  naturality {X Y} f := by
    set tailY : (ListF.obj Y) ⟶ (ListF.obj Y) :=
      ↾fun ys : List Y =>
        match ys with
        | [] => []
        | head :: tail => tail

    set tailX : (ListF.obj X) ⟶ (ListF.obj X) :=
      ↾fun xs : List X =>
        match xs with
        | [] => []
        | head :: tail => tail

    apply ConcreteCategory.ext_apply
    intro xs
    rw [types_comp_apply]
    rw [types_comp_apply]
    cases xs <;> rfl


def ListPairF : Type u ⥤ Type u where
  obj X := List X × List X
  map f :=
    ↾fun p => (List.map f p.1, List.map f p.2)

  /- These next two auto-implement if you leave them out-/

  map_id X := by
    apply ConcreteCategory.ext_apply
    intro xs
    rw [types_id_apply (List X × List X) xs]
    rw [TypeCat.ofHom_apply]
    rw [types_id X]
    rw [List.map_id]
    rw [List.map_id]

  map_comp {X Y Z} f g := by
    apply ConcreteCategory.ext_apply
    intro xs
    -- can't be bothered
    simp


#check (ListPairF).map_comp

#check ListPairF.obj Nat

example (p: ListPairF.obj Nat): True := by
  dsimp [ListPairF] at p
  #check p
  trivial


def AppendNat : NatTrans ListPairF ListF where
  app X :=
    ↾fun p : List X × List X =>
      p.1 ++ p.2

  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro xs
    rw [@types_comp_apply]
    simp

    have hpair :
        cchom (ListPairF.map f) xs =
          (List.map (cchom f) xs.1,
           List.map (cchom f) xs.2) := by
      rfl

    rw [hpair]

    have hlist :
        cchom (ListF.map f) (xs.1 ++ xs.2) =
          List.map (cchom f) (xs.1 ++ xs.2) := by
      rfl

    rw [hlist]
    simp

def OptionToListNat : NatTrans OptionF ListF where
  app X :=
    ↾fun ox : Option X =>
      match ox with
      | none => []
      | some x => [x]

  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro ox
    dsimp
    cases ox <;> rfl


@[reassoc]
theorem OptionToList_head :
    OptionToListNat ≫ HeadNat = 𝟙 OptionF := by
  ext X ox
  cases ox <;> rfl


/- So OptionToListNat has a retraction, making it a split mono in the functor
category, and OptionF a retract of ListF. -/

def OptionToListNat_splitMono :
    SplitMono
      (C := Type u ⥤ Type u)
      OptionToListNat where
  retraction := HeadNat
  id := OptionToList_head


/- The composite in the other order is *not* the identity: heads forgets the
tail. Witnessed at X = Nat by the list [0, 1], which comes back as [0]. -/

theorem head_OptionToList_ne_id :
    HeadNat.{u} ≫ OptionToListNat.{u} ≠ 𝟙 ListF.{u} := by
  intro h
  -- ULift lets us build the witness at an arbitrary universe u
  let a : ULift.{u} Bool := ULift.up true
  let b : ULift.{u} Bool := ULift.up false
  have happ :=
    congrArg
      (fun η : ListF.{u} ⟶ ListF.{u} =>
        cchom (NatTrans.app η (ULift.{u} Bool)) [a, b]) h
  -- both sides are definitionally plain list expressions: [a] = [a, b]
  have hbad : ([a] : List (ULift.{u} Bool)) = [a, b] := happ
  simp at hbad

/- Permutations: a *fixed positional* rearrangement is natural, because it
depends only on length and position, never on the elements. -/

def ReverseNat : NatTrans ListF ListF where
  app X := ↾fun xs : List X => xs.reverse

  naturality {X Y} f :=
    ConcreteCategory.ext_apply fun xs =>
      show (List.map (cchom f : X → Y) xs).reverse =
            List.map (cchom f : X → Y) xs.reverse
      from List.map_reverse.symm


--List.map_reverse.symm


/- Reversing twice is the identity, so ReverseNat is an isomorphism of functors
(a self-inverse automorphism of ListF). -/

@[reassoc]
theorem ReverseNat_involutive :
    ReverseNat ≫ ReverseNat = 𝟙 ListF := by
  ext X xs
  exact List.reverse_reverse xs

/-- Applying the natural transformation twice recovers a concrete list. -/
example :
    cchom (ReverseNat.app Nat)
        (cchom (ReverseNat.app Nat) [1, 2, 3]) = [1, 2, 3] := by
  have h := congrArg
    (fun η : ListF ⟶ ListF => cchom (NatTrans.app η Nat) [1, 2, 3])
    ReverseNat_involutive
  exact h

def ReverseNat_iso : ListF.{u} ≅ ListF.{u} where
  hom := ReverseNat
  inv := ReverseNat
  hom_inv_id := ReverseNat_involutive
  inv_hom_id := ReverseNat_involutive


-- more general

abbrev PositionalList := List Nat

def PositionalList.draw
  (pl: PositionalList)
  {α : Type u}
  (xs : List α) : List α :=
  pl.filterMap fun i => xs[i]?

theorem PositionalList.draw_map
    (pl: PositionalList)
    {α : Type u}
    (f : α -> β)
    (xs: List α) :
    (pl.draw xs).map f = pl.draw (xs.map f) := by
  simp [PositionalList.draw]
  simp [List.map_filterMap]

/- Coercing valid `Fin xs.length` positions to naturals lets permissive draw
recover ordinary mapping over those positions. -/
theorem PositionalList.draw_fin_positions
    {α : Type u}
    (xs : List α)
    (positions : List (Fin xs.length)) :
    PositionalList.draw (positions.map Fin.val) xs =
      positions.map (fun i => xs[i]) := by
  unfold PositionalList.draw
  rw [List.filterMap_map]
  calc
    List.filterMap ((fun i => xs[i]?) ∘ Fin.val) positions =
        positions.filterMap (some ∘ fun i => xs[i]) := by
      apply List.filterMap_congr
      intro i _
      change xs[i]? = some xs[i]
      exact List.getElem?_eq_getElem i.isLt
    _ = positions.map (fun i => xs[i]) := by
      rw [List.filterMap_eq_map]


/-- If the set of elements in one list is a subset of the set of
elements in another list, it can be formed by a draw from the other list.-/
theorem PositionalList.subset_existence
    (sub: List α)
    (sup: List α)
    (h: List.Subset sub sup):
    ∃ pl: PositionalList, pl.draw sup = sub := by
  classical
  refine ⟨sub.map (fun a => sup.idxOf a), ?_⟩
  unfold PositionalList.draw
  rw [List.filterMap_map]
  calc
  _ = sub.filterMap some := by
    apply List.filterMap_congr
    intro a ha
    exact List.getElem?_idxOf (h ha)
  _ = sub := List.filterMap_some


/- A position scheme chooses positions from the length of its input. This can
describe operations such as tail and reverse, unlike a fixed positional list. -/

abbrev PositionScheme := Nat → PositionalList

def PositionScheme.draw
    (scheme : PositionScheme)
    {α : Type u}
    (xs : List α) : List α :=
  (scheme xs.length).draw xs

theorem PositionScheme.draw_map
    (scheme : PositionScheme)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (scheme.draw xs).map f = scheme.draw (xs.map f) := by
  rw [PositionScheme.draw, PositionScheme.draw, List.length_map]
  exact PositionalList.draw_map (scheme xs.length) f xs

def PositionScheme.Represents
    (scheme : PositionScheme)
    (operation : ∀ {α : Type u}, List α → List α) : Prop :=
  ∀ {α : Type u} (xs : List α), operation xs = scheme.draw xs

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

def PositionScheme.natTransOfRepresents
    (scheme : PositionScheme)
    (operation : ∀ {α : Type u}, List α → List α)
    (h : scheme.Represents operation) : NatTrans ListF ListF where
  app X := ↾fun xs : List X => operation xs
  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro xs
    exact (h.natural (cchom f) xs).symm

def PositionScheme.natTrans
    (scheme : PositionScheme) : NatTrans ListF ListF where
  app X := ↾fun xs : List X => scheme.draw xs
  naturality {X Y} f := by
    apply ConcreteCategory.ext_apply
    intro xs
    change scheme.draw (List.map (cchom f : X → Y) xs) =
      List.map (cchom f : X → Y) (scheme.draw xs)
    exact (scheme.draw_map (cchom f) xs).symm

def DuplicateHeadScheme : PositionScheme :=
  fun _ => [0, 0]

def DuplicateHeadNat : ListF ⟶ ListF :=
  DuplicateHeadScheme.natTrans

example : cchom (DuplicateHeadNat.app Nat) [10, 20] = [10, 10] := by
  rfl

example : cchom (DuplicateHeadNat.app Nat) [] = [] := by
  rfl


def ReversePositionScheme : PositionScheme :=
  fun n => (List.finRange n).reverse.map Fin.val

theorem ReversePositionScheme_represents_reverse
    {α : Type u}
    (xs : List α) :
    xs.reverse = ReversePositionScheme.draw xs := by
  symm
  unfold PositionScheme.draw ReversePositionScheme PositionalList.draw
  rw [List.filterMap_map]
  rw [List.filterMap_reverse]
  congr
  calc
    _ = (List.finRange xs.length).map (fun i => xs[i]) := by
      rw [← List.filterMap_eq_map]
      apply List.filterMap_congr
      intro i _
      change xs[i]? = some xs[i]
      exact List.getElem?_eq_getElem i.isLt
    _ = xs := List.map_getElem_finRange xs

def ReverseNatByPosition : ListF ⟶ ListF :=
  ReversePositionScheme.natTransOfRepresents List.reverse
    ReversePositionScheme_represents_reverse

def TakePositionScheme (k : Nat) : PositionScheme :=
  fun n => ((List.finRange n).take k).map Fin.val

theorem TakePositionScheme_represents_take
    (k : Nat)
    {α : Type u}
    (xs : List α) :
    xs.take k = (TakePositionScheme k).draw xs := by
  symm
  unfold PositionScheme.draw TakePositionScheme
  rw [PositionalList.draw_fin_positions]
  change ((List.finRange xs.length).take k).map (fun i => xs[i]) = xs.take k
  rw [List.map_take]
  exact congrArg (List.take k) (List.map_getElem_finRange xs)

theorem take_natural_by_scheme
    (k : Nat)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (xs.take k).map f = (xs.map f).take k :=
  PositionScheme.Represents.natural
    (TakePositionScheme_represents_take k) f xs

def DropPositionScheme (k : Nat) : PositionScheme :=
  fun n => ((List.finRange n).drop k).map Fin.val

theorem DropPositionScheme_represents_drop
    (k : Nat)
    {α : Type u}
    (xs : List α) :
    xs.drop k = (DropPositionScheme k).draw xs := by
  symm
  unfold PositionScheme.draw DropPositionScheme
  rw [PositionalList.draw_fin_positions]
  change ((List.finRange xs.length).drop k).map (fun i => xs[i]) = xs.drop k
  rw [List.map_drop]
  exact congrArg (List.drop k) (List.map_getElem_finRange xs)

theorem drop_natural_by_scheme
    (k : Nat)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (xs.drop k).map f = (xs.map f).drop k :=
  PositionScheme.Represents.natural
    (DropPositionScheme_represents_drop k) f xs

theorem ReverseNatByPosition_eq_ReverseNat :
    ReverseNatByPosition = ReverseNat := by
  ext X xs
  rfl

/- Co-Yoneda describes the fixed-length version of a positional draw. A list
of positions in `Fin n` determines a natural transformation from maps out of
`Fin n` to lists. This demonstration lives in `Type`, where `Fin n` is an
object without a universe lift. -/

noncomputable def YonedaDrawAt
    (n : Nat)
    (positions : List (Fin n)) :
    coyoneda.obj (Opposite.op (Fin n)) ⟶ ListF :=
  (coyonedaEquiv (C := Type) (X := Fin n) (F := ListF)).symm positions

theorem yonedaDrawAt_value
    (n : Nat)
    (positions : List (Fin n)) :
    coyonedaEquiv (C := Type) (X := Fin n) (F := ListF)
      (YonedaDrawAt n positions) = positions := by
  exact Equiv.apply_symm_apply
    (coyonedaEquiv (C := Type) (X := Fin n) (F := ListF)) positions

theorem yonedaDrawAt_apply
    (n : Nat)
    (positions : List (Fin n))
    (X : Type)
    (f : Fin n → X) :
    cchom ((YonedaDrawAt n positions).app X) (TypeCat.ofHom f) =
      positions.map f := by
  exact coyonedaEquiv_symm_app_apply
    (C := Type) (X := Fin n) (F := ListF) positions X (TypeCat.ofHom f)

/- This is the common data behind the two viewpoints: at each input length,
choose a list of valid positions. -/
abbrev YonedaPositionScheme := (n : Nat) → List (Fin n)

def YonedaPositionScheme.toPositionScheme
    (scheme : YonedaPositionScheme) : PositionScheme :=
  fun n => (scheme n).map Fin.val

def YonedaPositionScheme.Represents
    (scheme : YonedaPositionScheme)
    (operation : ∀ {α : Type u}, List α → List α) : Prop :=
  scheme.toPositionScheme.Represents operation

theorem YonedaPositionScheme.Represents.natural
    {scheme : YonedaPositionScheme}
    {operation : ∀ {α : Type u}, List α → List α}
    (h : scheme.Represents operation)
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    (operation xs).map f = operation (xs.map f) :=
  PositionScheme.Represents.natural h f xs

noncomputable def YonedaPositionScheme.yonedaAt
    (scheme : YonedaPositionScheme)
    (n : Nat) :
    coyoneda.obj (Opposite.op (Fin n)) ⟶ ListF :=
  YonedaDrawAt n (scheme n)

theorem YonedaPositionScheme.draw_eq_yonedaAt
    (scheme : YonedaPositionScheme)
    (X : Type)
    (xs : List X) :
    scheme.toPositionScheme.draw xs =
      cchom ((scheme.yonedaAt xs.length).app X)
        (TypeCat.ofHom fun i => xs[i]) := by
  unfold YonedaPositionScheme.toPositionScheme
  rw [PositionScheme.draw, PositionalList.draw_fin_positions]
  exact (yonedaDrawAt_apply xs.length (scheme xs.length) X
    (fun i => xs[i])).symm

def ReverseYonedaPositionScheme : YonedaPositionScheme :=
  fun n => (List.finRange n).reverse

def TakeYonedaPositionScheme (k : Nat) : YonedaPositionScheme :=
  fun n => (List.finRange n).take k

def DropYonedaPositionScheme (k : Nat) : YonedaPositionScheme :=
  fun n => (List.finRange n).drop k

example : ReverseYonedaPositionScheme.toPositionScheme = ReversePositionScheme :=
  rfl

example (k : Nat) :
    (TakeYonedaPositionScheme k).toPositionScheme = TakePositionScheme k :=
  rfl

example (k : Nat) :
    (DropYonedaPositionScheme k).toPositionScheme = DropPositionScheme k :=
  rfl

theorem ReverseYonedaPositionScheme_represents_reverse
    {α : Type u}
    (xs : List α) :
    xs.reverse = ReverseYonedaPositionScheme.toPositionScheme.draw xs :=
  ReversePositionScheme_represents_reverse xs

/- The raw co-Yoneda proof below exposes the naturality square. Once that
structure has been packaged as a position scheme, this is the ergonomic form. -/
theorem reverse_natural_yoneda_short
    {α β : Type u}
    (f : α → β)
    (xs : List α) :
    xs.reverse.map f = (xs.map f).reverse :=
  YonedaPositionScheme.Represents.natural
    ReverseYonedaPositionScheme_represents_reverse f xs

noncomputable def ReverseYonedaAt (n : Nat) :=
  YonedaDrawAt n (List.finRange n).reverse

theorem reverseYonedaAt_apply
    (n : Nat)
    (X : Type)
    (g : Fin n → X) :
    cchom ((ReverseYonedaAt n).app X) (TypeCat.ofHom g) =
      ((List.finRange n).map g).reverse := by
  change cchom ((YonedaDrawAt n (List.finRange n).reverse).app X)
    (TypeCat.ofHom g) = _
  rw [yonedaDrawAt_apply, List.map_reverse]

/- The middle equality below is the naturality square of `ReverseYonedaAt`,
evaluated at the position-indexing map of `xs`. -/
theorem reverse_natural_yoneda
    (X Y : Type)
    (f : X → Y)
    (xs : List X) :
    (xs.map f).reverse = xs.reverse.map f := by
  let index : Fin xs.length → X := fun i => xs[i]
  have hX :
      cchom ((ReverseYonedaAt xs.length).app X) (TypeCat.ofHom index) =
        xs.reverse := by
    rw [reverseYonedaAt_apply]
    dsimp [index]
    exact congrArg List.reverse (List.map_getElem_finRange xs)
  have hY :
      cchom ((ReverseYonedaAt xs.length).app Y)
        (TypeCat.ofHom fun i => f (index i)) =
        (xs.map f).reverse := by
    rw [reverseYonedaAt_apply]
    congr 1
    calc
      (List.finRange xs.length).map (fun i => f (index i)) =
          ((List.finRange xs.length).map (fun i => xs[i])).map f := by
        dsimp [index]
        simp only [List.map_map]
        rfl
      _ = xs.map f :=
        congrArg (List.map f) (List.map_getElem_finRange xs)
  have hmap :
      cchom ((ReverseYonedaAt xs.length).app Y)
        (TypeCat.ofHom fun i => f (index i)) =
        List.map f
          (cchom ((ReverseYonedaAt xs.length).app X) (TypeCat.ofHom index)) := by
    have h := congrArg
      (fun k : (coyoneda.obj (Opposite.op (Fin xs.length))).obj X ⟶ ListF.obj Y =>
        cchom k (TypeCat.ofHom index))
      ((ReverseYonedaAt xs.length).naturality (TypeCat.ofHom f))
    rw [types_comp_apply, types_comp_apply] at h
    exact h
  exact hY.symm.trans (hmap.trans (congrArg (List.map f) hX))

end TypesKindergarten


section YonedaTime

variable (C: Type u) [Category.{v} C]
variable (C₂: Type u) [Category.{v} C₂]

#check yoneda (C:= C)

example
  (X Y A B Z : C)
  (f : A ⟶ B)
  (g : X ⟶ Y)
  (f2 : Z ⟶ A)
  (F : Cᵒᵖ ⥤ Type v)
  (h : Nonempty (F.obj (op A))): true := by
  -- functor; Y : C ⥤ Cᵒᵖ ⥤ Type v
  let yon := yoneda (C := C)
  -- presheaf; presheafA : Cᵒᵖ ⥤ Type v.
  -- This is the hom functor C(-, A).
  let presheafA := yon.obj A
  /-
  The hom functor C(-, A) can also be approached by currying Mathlib's canonical
  hom bifunctor.

  Functor.hom gives us the hom bifunctor of type `Cᵒᵖ × C ⥤ Type v`.

  To curry this to match `yon`, we need to first flip it to be

  `C × Cᵒᵖ ⥤ Type v`.

  We can do that by composing with Prod.swap.
  -/
  let homSwapped := CategoryTheory.Prod.swap C Cᵒᵖ ⋙ Functor.hom C
  let curriedHom := Functor.curry.obj homSwapped
  have uncurried_yon_eq_homSwapped : Functor.uncurry.obj yon = homSwapped := by
    dsimp [yon, homSwapped]
    exact CategoryTheory.Functor.ext
      (F := CategoryTheory.Functor.uncurry.obj (yoneda (C := C)))
      (G := CategoryTheory.Prod.swap C Cᵒᵖ ⋙ CategoryTheory.Functor.hom C) (by simp)

  -- now we can observe that they're the same functor:
  have curriedHom_eq_yon : curriedHom = yon := by
    dsimp [curriedHom]
    rw [← uncurried_yon_eq_homSwapped]
    exact Functor.curry_obj_uncurry_obj yon

  -- and of course therefore equivalent / iso:
  have curriedHom_iso_yon : curriedHom ≅ yon :=
    eqToIso curriedHom_eq_yon

  -- nat trans from Hom(-, A) to Hom(-, B)
  let nat_trans_hom_AB := yon.map f
  -- it really is a nat trans:
  change NatTrans (yon.obj A) (yon.obj B) at nat_trans_hom_AB

  -- component of that nat trans between hom functors at Y.
  let component_Y := nat_trans_hom_AB.app (op Y)

  -- component_Y is a function (Y -> A) -> (Y -> B)
  change (Y ⟶ A) ⟶ (Y ⟶ B) at component_Y

  -- it acts by post composing f
  have component_Y_is_postcomp_f : component_Y = ↾fun h : Y ⟶ A ↦ h ≫ f := by
    rfl

  -- because nat_trans_hom_AB is a nat trans, we get naturality with other
  -- components

  let component_X := nat_trans_hom_AB.app (op X)
  change (X ⟶ A) ⟶ (X ⟶ B) at component_X

  -- Hom(-, B)
  let presheafB := yon.obj B

  /-
                 presheafA.map (op g)
                     Hom(g, A)
    Hom(Y, A) ------------------------> Hom(X, A)
       │                                  │
       │ component_Y                      │ component_X
       │  Hom(Y, f)                       │  Hom(X, f)
       ↓                                  ↓
    Hom(Y, B) ------------------------> Hom(X, B)
                 presheafB.map (op g)
                      Hom(g, B)

    Here `g : X ⟶ Y`, so mapping `op g : op Y ⟶ op X` in either
    presheaf is precomposition by `g`.

    `presheafA.map (op g)` is Hom(g, A).
    `presheafB.map (op g)` is Hom(g, B).
  -/
  have _ : presheafA.map (op g) ≫ component_X = component_Y ≫ presheafB.map (op g) := by
    apply nat_trans_hom_AB.naturality (op g)

  /-
    In the diagram above, note that we've used yoneda to get Hom(-, A) and
    Hom(-, B), but this gives us a naturality condition that applies to
    morphisms between any X and Y in C.
  -/



  #check yonedaEquiv (F := F) (X := A)

  let yonRHS := F.obj (op A)
  -- pick a witness out of the set F.obj (op A)
  let rhs : yonRHS := Classical.choice h

  -- can look the nat trans up
  let the_nat_trans := (yonedaEquiv (F := F) (X := A)).symm rhs

  #check the_nat_trans.app
  -- the_nat_trans.app : (X : Cᵒᵖ) → (yoneda.obj A).obj X ⟶ F.obj X
  --
  -- ie, for any X in Cᵒᵖ the domain is a function C(X, A) -> F(X). This is the
  -- component of the nat trans at X.


  #check the_nat_trans.app (op Z)
  -- the_nat_trans.app (op Z) : (yoneda.obj A).obj (op Z) ⟶ F.obj (op Z)
  --
  -- ie, C(Z, A) -> F(Z)
  --
  -- Whiteboard Yoneda lemma tells us that, for the nat trans looked up by the
  -- element rhs, notated α^rhs, the result of applying its component at Z,
  -- notated (a^rhs)_Z, to some element f of its codomain C(Z, A) -- that is, a
  -- morphism f: Z ⟶ A in C -- is the same as calling F(f) on rhs. That is,
  -- (a^rhs)_Z(f) = F(f)(rhs).

  -- here we want to use f2 : Z ⟶ A.

  have _ : the_nat_trans.app (op Z) f2 = F.map (op f2) rhs := by
    rfl

  trivial

/-- Structures introduced to bridge between Riehl's usage (p. 51, p. 62)
and the Lean category API. We'll exercise these in the example below. -/

structure Corepresentation where
  functor: C ⥤ Type v
  obj: C
  corep: functor.CorepresentableBy obj

structure Representation where
  functor: Cᵒᵖ ⥤ Type v
  obj: C
  rep: functor.RepresentableBy obj

/- `Element` is an associated type: the type of a universal element depends
on which representation package we were given. -/
class HasUniversalElement (S : Type w) where
  Element : S → Type v
  universalElement : (s : S) → Element s

instance : HasUniversalElement (Corepresentation (C := C)) where
  Element R := R.functor.obj R.obj
  universalElement R := R.corep.homEquiv (𝟙 R.obj)

instance : HasUniversalElement (Representation (C := C)) where
  Element R := R.functor.obj (op R.obj)
  universalElement R := R.rep.homEquiv (𝟙 R.obj)

def universalElement {S : Type w} [h : HasUniversalElement S] (s : S) :
    h.Element s :=
  h.universalElement s

/-- Let `u := hu.homEquiv (𝟙 A) : F.obj A` and
`v := hv.homEquiv (𝟙 B) : F.obj B`. These are the universal elements selected
by the two corepresentations. There is exactly one isomorphism `φ : A ≅ B`
such that applying `F` to `φ` carries `u` to `v`, i.e. `F(φ)(u) = v`.

The theorem statement spells out `u` and `v` as images of identity morphisms
because that is how `CorepresentableBy` stores its universal elements. -/
theorem existsUnique_iso_of_universalElements
    {F : C ⥤ Type v} {A B : C}
    (hu : F.CorepresentableBy A) (hv : F.CorepresentableBy B) :
    ∃! φ : A ≅ B,
      F.map φ.hom (hu.homEquiv (𝟙 A)) = hv.homEquiv (𝟙 B) := by
  let φ := hu.uniqueUpToIso hv
  refine ⟨φ, ?_, ?_⟩
  · dsimp [φ]
    rw [← hu.homEquiv_eq]
    change hu.homEquiv (hu.homEquiv.symm (hv.homEquiv (𝟙 B))) = _
    exact Equiv.apply_symm_apply _ _
  · intro ψ hψ
    apply Iso.ext
    apply hu.homEquiv.injective
    rw [hu.homEquiv_eq]
    exact hψ.trans (Equiv.apply_symm_apply _ _).symm

/-- The fixed-object specialization of `existsUnique_iso_of_universalElements`.

Let `u := hu.homEquiv (𝟙 A)` and `v := hv.homEquiv (𝟙 A)`. If both are
universal elements for `F` at the same object `A`, there is exactly one
automorphism `σ : A ≅ A` for which `F(σ)(u) = v`. In particular, universal
elements at a fixed representing object need not be equal, but they are
related by a unique symmetry of that object. -/
theorem existsUnique_aut_of_universalElements
    {F : C ⥤ Type v} {A : C}
    (hu hv : F.CorepresentableBy A) :
    ∃! σ : A ≅ A,
      F.map σ.hom (hu.homEquiv (𝟙 A)) = hv.homEquiv (𝟙 A) :=
  existsUnique_iso_of_universalElements C hu hv



-- Let's start a new example to look at representations and universal
-- properties. We'll use coyoneda for covariance, since it's a bit simpler.
example
(X Y Z A B D : C)
  (F: C ⥤ Type v)
  -- Assume A represents F. This α is both the statement that A reprsents F, ie,
  -- that there is a nat iso Hom(A, -) ≅ F, and also that iso itself.
  (α : coyoneda.obj (op A) ≅ F)
  : true := by

  -- Get the universal element. We can do it a couple ways.
  -- The whiteboard approach: just run the bijection forward.
  -- This is u = α_A(1_A) in Riehl-speak
  let u := (α.app A).hom (𝟙 A)

  -- can also get it this way
  have _ : u = α.hom.app A (𝟙 A) :=
    coyonedaEquiv_apply α.hom

  /-
  On p.62, Riehl defines a *universal property* _of_ an object `A` in `C` as
  being "expressed" by

  - a representable functor `F`, and
  - a universal element `u ∈ F(A)`

  such that `u` defines a natural isomorphism `C(A, -) ≅ F` or `C(-, A) ≅ F`, as
  appropriate.

  In other words, `F` and `u` as in the example below. The tricky bit is just
  that these two are discussed as together constituting a universal property
  *of* A.

  Let's look at the related Lean equipment. There isn't a *direct* equivalent,
  but we can make our own structure that adheres to Riehl's definition closely.
  -/

  let F_corep_A : F.CorepresentableBy A :=
    Functor.corepresentableByEquiv.symm α

  -- can look up u from this
  have _ : F_corep_A.homEquiv (𝟙 A) = u := by
    rfl

  /- If you've forgotten that an F.CorepresentableBy A has A as the
  representing object, you can extract it using implicit arguments
  -/

  let universalElementOfCorep :=
    fun {A : C} (h : F.CorepresentableBy A) =>
      h.homEquiv (𝟙 A)

  have _ : universalElementOfCorep F_corep_A = u := by
    rfl

  -- Still, this isn't closely tracking Riehl. We want our own structure
  -- for that.
  let corep : Corepresentation (C := C) := {
    functor := F
    obj := A
    corep := F_corep_A
  }

  -- The typeclass selects the covariant/corepresentable implementation.
  have _ : universalElement corep = u := by
    rfl

  /- Our Corepresentation and Representation structures capture the data of both
  Riehl's "representation" on p. 51 and "universal property" on p. 62, as far as
  I can tell.
  -/

  /- Say we know that a functor is corepresentable, but we don't have a specific
  corepresenting object on hand, or a specific universal element. Corepresenting
  objects are only unique up to isomorphism -- there can still be many of them.
  You can also have multiple universal elements. You can get a chosen representative
  via `F.coreprX`
  -/

  -- evidently this establishes that F is corepresentable to F.coreprX's satisfaction
  letI : F.IsCorepresentable := F_corep_A.isCorepresentable

  -- this just gives us some object in C, and the assurance that it corepresents F
  #check F.coreprX

  -- any two objects that corepresent the same functor are iso
  have _ : A ≅ F.coreprX := by
   exact F_corep_A.isoCoreprX

  -- we can get a unique automorphism A ≅ A from two corepresenting objects
  let canonicalAut : A ≅ A :=
    F_corep_A.uniqueUpToIso F_corep_A

  trivial





/-
  Here we're going to take a look at
-/



end YonedaTime
