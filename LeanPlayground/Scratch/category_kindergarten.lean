import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.FinRange
import ProofWidgets.Extra.CheckHighlight
import ProofWidgets.Demos.Graph.ExprGraph

open CategoryTheory

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

def ReverseNatByPosition : ListF ⟶ ListF :=
  ReversePositionScheme.natTrans

theorem ReversePositionScheme_draw
    {α : Type u}
    (xs : List α) :
    ReversePositionScheme.draw xs = xs.reverse := by
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

theorem ReverseNatByPosition_eq_ReverseNat :
    ReverseNatByPosition = ReverseNat := by
  ext X xs
  exact ReversePositionScheme_draw xs




end TypesKindergarten
