import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Types.Basic

open CategoryTheory

universe u v

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
#eval (ConcreteCategory.hom increment) 41
-- 42
-- think there must be some coercion going on here

#check TypeCat.homEquiv
-- well, evidently they're equivalent

-- morphism composition is function composition

def double : Nat ⟶ Nat :=
  TypeCat.ofHom (fun n => 2 * n)

#check increment ≫ double
-- increment ≫ double : Nat ⟶ Nat

#eval (ConcreteCategory.hom (increment ≫ double)) 10
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
      (ConcreteCategory.hom f p.1,
       ConcreteCategory.hom f p.2))

  map_id X := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext p

    /- change says, bet this is equal to the current goal. dsimp may also work,
    but change is more revealing here. -/

    change
      ((ConcreteCategory.hom (𝟙 X)) p.1,
       (ConcreteCategory.hom (𝟙 X)) p.2) = p

    apply Prod.ext
    · exact types_id_apply X p.1
    · exact types_id_apply X p.2


  /- there's much simpler ways to do this, but this is explicit -/

  map_comp {X Y Z} f g := by
    set mapFG : (X × X) ⟶ (Z × Z) :=
      ↾fun p =>
        ((ConcreteCategory.hom (f ≫ g)) p.1,
         (ConcreteCategory.hom (f ≫ g)) p.2)

    set mapF : (X × X) ⟶ (Y × Y) :=
      ↾fun p =>
        ((ConcreteCategory.hom f) p.1,
         (ConcreteCategory.hom f) p.2)

    set mapG : (Y × Y) ⟶ (Z × Z) :=
      ↾fun p =>
        ((ConcreteCategory.hom g) p.1,
         (ConcreteCategory.hom g) p.2)

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


#eval (ConcreteCategory.hom (PairSelf.map increment)) (10, 20)
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


/- Now let's try Option.

So we don't keep writing ConcereteCategory.hom, we can introduce some local
notation. -/

local notation "cchom" => ConcreteCategory.hom

def OptionF : Type u ⥤ Type u where
  obj X := Option X

  map {X Y} f :=
    ↾fun ox => Option.map (cchom f) ox

  map_id X := by
    set mappedId : Option X ⟶ Option X :=
      (↾fun ox => Option.map (cchom (𝟙 X)) ox)

    set optionId := 𝟙 (Option X)

    show mappedId = optionId

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext ox
    -- Option lets us use cases
    cases ox with
      | none => rfl
      | some x =>
          change some ((cchom (𝟙 X)) x) = some x
          apply congrArg some
          exact types_id_apply X x

  map_comp {X Y Z} f g := by
    set mappedFG := (↾fun ox => Option.map (cchom (f ≫ g)) ox)
    set mappedF := (↾fun ox => Option.map (cchom f) ox)
    set mappedG := (↾fun ox => Option.map (cchom g) ox)

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
      ↾fun ox => Option.map (cchom f) ox

    show f ≫ someY = someX ≫ mappedF

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x

    -- rfl would close here, but that's cheating

    change
      cchom (f ≫ someY) x = cchom (someX ≫ mappedF) x

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
      ↾fun p => (cchom f p.1, cchom f p.2)

    show mappedF ≫ fstY = fstX ≫ f

    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext p

    change
      cchom (mappedF ≫ fstY) p =
      cchom (fstX ≫ f) p

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


Side-note on ↾ vs cchom: they go in opposite directions.

↾ wraps a lean function as a morphism in the type category.

cchom takes a morphism in the type category and extracts the underlying
function.

Another side-note: morphisms in a concrete category have a `CoeFun` instance,
and can therefore be applied directly like a function.

For example:
-/

def increment' : Nat ⟶ Nat :=
  ↾fun n => n + 1

#eval increment' 10
-- 11

/-
Which also means we didn't really need to spam `cchom` everywhere.
-/


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
  rw [types_comp_apply] at h

  exact h


/- Prove that FstNat is a split epi, without using Mathlib's IsSplitEpi API for
now.  -/

/- Start by defining the section -/
def DiagNat : NatTrans (Functor.id (Type u)) PairSelf where
  app X :=
    ↾fun x => (x, x)

  naturality {X Y} f := by
    rw [Functor.id_map]
    sorry


theorem FstNat_has_section :
    DiagNat ≫ FstNat = 𝟙 (Functor.id (Type u)) := by
  -- prove equality of natural transformations
  sorry

end TypesKindergarten
