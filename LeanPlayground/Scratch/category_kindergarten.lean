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

end TypesKindergarten
