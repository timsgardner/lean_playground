/-
# Toy World

Toy world for reviewing very basic Lean maneuvers without tactic-mashing.
-/

import Mathlib.Util.TermReduce
import Mathlib.Tactic.Conv
import Mathlib.CategoryTheory.Functor.Category

/-- A toy copy of the natural numbers. It is distinct from both `Nat` and `Y`. -/
inductive X where
  | mk (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A second, distinct toy copy of the natural numbers. -/
inductive Y where
  | mk (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! `X` and `Y` are both in bijection with `Nat`. -/

def X.toNat : X → Nat
  | .mk n => n

def Nat.toX : Nat → X
  | n => .mk n

def Y.toNat : Y → Nat
  | .mk n => n

def Nat.toY : Nat → Y
  | n => .mk n

example (n : Nat) : (Nat.toX n).toNat = n := by rfl
example (x : X) : Nat.toX x.toNat = x := by cases x <;> rfl
example (n : Nat) : (Nat.toY n).toNat = n := by rfl
example (y : Y) : Nat.toY y.toNat = y := by cases y <;> rfl

/-! A concrete function to manipulate. -/

def f : X → Y
  | .mk n => .mk (n + 1)

/-! The partition of `Y` by the parity of its underlying natural number. -/

def Y.isEven (y : Y) : Bool := y.toNat % 2 == 0
def Y.isOdd  (y : Y) : Bool := !y.isEven

example (y : Y) : y.isEven || y.isOdd = true := by
  simp [Y.isOdd]

example (y : Y) : ¬ (y.isEven = true ∧ y.isOdd = true) := by
  simp [Y.isOdd]

/-! A few basic experiments. -/

example (x : X) : (fun x' => f x') x = f x := by
  rfl

example : f (.mk 4) = .mk 5 := by
  rfl

example : (f (.mk 4)).isOdd = true := by
  rfl

/-! Beta-reduction practice: reduce the lambdas and the local `let` by hand. -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x := by
  -- Could just use simp here, but let's see what the term version looks like.
  -- These lets aren't really necessary, but they align the names for our
  -- proof.
  let g : X → Y := f
  let x': X := x
  let y : Y := g x'
  let result : Y := (fun z : Y => z) y
  let coolResult := Eq.refl result -- type: result = result
  exact coolResult

/-! We can also dispense of the tactics altogether. -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x :=
  let g : X → Y := f
  let x': X := x
  let y : Y := g x'
  let result : Y := (fun z : Y => z) y
  let coolResult := Eq.refl result -- type: result = result
  coolResult

/-! And dispense of the intermediate let bindings -/

example (x : X) :
    (fun g : X → Y =>
      (fun x' : X =>
        let y := g x'
        (fun z : Y => z) y) x)
      f
    = f x :=
  Eq.refl (f x)


/- Now let's look at targeted beta reductions -/
section TargetedReduction

/- Let's look at conv -/

example (x : X) :
    ((fun z : Y => z) (f x), f x) = (f x, f x) := by
  conv in ((fun z : Y => z) (f x)) =>
    dsimp only


/-! ## `conv` practice

Useful navigation vocabulary includes
`conv in`, `conv_lhs`, `conv_rhs`, `arg`, `lhs`, `rhs`, and `enter`.
-/

variable (observe : Y → Nat)
variable (combine : Y → Y → Y)

-- 1. There are two nested beta redexes underneath `observe`, but reducing them
-- no longer finishes the proof. After exposing `f x`, use `h` at precisely the
-- needed occurrence.
example (x : X) (y : Y) (h : f x = y) :
    observe ((fun y : Y => y) ((fun x' : X => f x') x)) =
      observe y := by
  conv =>
    lhs
    congr
    rhs
    simp
    apply h


-- 2. Navigate to the second argument on the right-hand side and rewrite only
-- there. The hypothesis points in the opposite direction from the rewrite you
-- need.
example (a b : Y) (h : a = b) :
    combine a a = combine a b := by
  conv =>
    rhs
    congr
    {
      rfl
    }
    {
      rw [← h]
    }

-- 3. Enter beneath a lambda binder, then into the first component of the pair.
-- Beta reduction exposes `g x`, but `h x` is still needed to reach `k x`.
example (g k : X → Y) (h : ∀ x, g x = k x) :
    (fun x : X =>
      ((fun y : Y => y) (g x), (fun y : Y => y) (f x))) =
    (fun x : X => (k x, f x)) := by
  conv =>
    lhs
    intro x -- duck into the lambda
    lhs
    rhs
    apply h

-- Same example, different path
example (g k : X → Y) (h : ∀ x, g x = k x) :
    (fun x : X =>
      ((fun y : Y => y) (g x), (fun y : Y => y) (f x))) =
    (fun x : X => (k x, f x)) := by
  -- we don't really need to substitute id but it cleans things
  conv in (occs := *) (fun y => y) =>
    change id
  conv in id _ =>
    change (g x)
    apply h


-- 4. This time the expression to transform is inside a hypothesis rather than
-- the target. Normalize only the indicated lambda application in `h`, then
-- chain the resulting equality with `k`.
example (a b c : Y)
    (h : combine a ((fun y : Y => y) b) = c)
    (k : c = a) :
    combine a b = a := by
  conv at h =>
    lhs
    arg 2
    change b
  conv at h in c =>
    rw [k]
  exact h


-- 5. The occurrence to rewrite is the first argument of an inner application
-- on the right. The other occurrences should be left alone.
example (a b : Y) (h : a = b) :
    combine a (combine a b) = combine a (combine b b) := by
    conv =>
      rhs
      rhs
      arg 1
      rw [← h]

-- let's try `beta%`
example (x: X):
    ∀ (p : X × X), (fun x': X => (x', x')) x = p → p = (x, x) := by
  intro p h
  conv at h =>
    lhs
    change (beta% ((fun x' : X => (x', x')) x))
  rw [h]

-- whnf is similar in this case
example (x: X):
    ∀ (p : X × X), (fun x': X => (x', x')) x = p → p = (x, x) := by
  intro p h
  conv at h =>
    lhs
    whnf
  rw [h]


end TargetedReduction


section CalcPractice

/-!
## `calc` practice

These are deliberately left open. Each proof is intended to have a meaningful
multi-step `calc` chain; try not to discharge the whole goal with `simp`.
-/

variable (observe : Y → Nat)
variable (combine : Y → Y → Y)

-- 1. Both arguments of `combine` have to move. Choose intermediate terms that
-- change only one argument at a time.
example (a b c : Y) (hab : a = b) (hbc : b = c) :
    observe (combine a b) = observe (combine c c) := by
  calc
    observe (combine a b)
      = observe (combine b b) := by rw [← hab]
    _ = observe (combine c b) := by rw [hbc]
    _ = observe (combine c c) := by rw [hbc]


-- 2. Mix definitional computation with substitution and then a small piece of
-- arithmetic normalization. A useful chain passes through `n + 1` and
-- `(m + 2) + 1`.
example (n m : Nat) (h : n = m + 2) :
    (f (.mk n)).toNat = m + 3 := by
  calc
    (f (.mk n)).toNat
      = n + 1 := by rfl
    _ = m + 2 + 1 := by rw [h]
    _ = m + 3 := by rfl


-- 3. A `calc` chain need not consist solely of equalities. Lean has to compose
-- `≤`, `<`, and `≤` in the right order here.
example (a b c d : Nat)
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    a < d := by
  calc
    a ≤ b := hab
    _ < c := hbc
    _ ≤ d := hcd

-- 4. Build an iff chain. The hypotheses supply the interesting changes, while
-- the surrounding propositional structure requires smaller local arguments.
example (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ R) :
    (P ∧ (Q ∨ False)) ↔ (R ∧ R) := by
  calc
    (P ∧ (Q ∨ False))
      ↔ P ∧ Q := by simp
    _ ↔ Q ∧ Q := by rw [hPQ]
    _ ↔ R ∧ R := by rw [hQR]

-- 5. First expose an arbitrary input. At each line of the pointwise `calc`,
-- transport an equality through `observe`; finally rebuild function equality.
example (g k l : X → Y)
    (hgk : ∀ x, g x = k x)
    (hkl : ∀ x, k x = l x) :
    (fun x => observe (g x)) = (fun x => observe (l x)) := by
  funext x
  calc
    observe (g x)
      = observe (k x) := by rw [hgk]
    _ = observe (l x) := by rw [hkl]


-- 6. The equality needed for the first argument points forward, while the one
-- needed for the second points backward. This rewards careful choice of the
-- middle expression rather than indiscriminate rewriting.
example (a b c d : Y)
    (hab : a = b) (hcb : c = b) (hcd : c = d) :
    combine a d = combine b b := by
  calc
    combine a d
      = combine a c := by rw [hcd]
    _ = combine b c := by rw [← hab]
    _ = combine b b := by rw [hcb]



end CalcPractice


namespace PrefixRelationCalcPractice

/-!
## `calc` with custom relations written in prefix form

The names `Reaches a b` and `StrictlyReaches a b` are ordinary function
applications, not notation. The `Trans` instances tell `calc` which kinds of
adjacent steps it may compose and what relation the resulting chain has.
-/

def Reaches (a b : Nat) : Prop := a ≤ b

def StrictlyReaches (a b : Nat) : Prop := a < b

instance : Trans Reaches Reaches Reaches where
  trans := Nat.le_trans

instance : Trans Reaches StrictlyReaches StrictlyReaches where
  trans := Nat.lt_of_le_of_lt

instance : Trans StrictlyReaches Reaches StrictlyReaches where
  trans := Nat.lt_of_lt_of_le

-- 1. Write every relation in prefix form. On later lines, the continuation
-- placeholder belongs in the first argument position: `Reaches _ c`.
example (a b c d : Nat)
    (hab : Reaches a b) (hbc : Reaches b c) (hcd : Reaches c d) :
    Reaches a d := by
  calc
    Reaches a b := hab
    Reaches _ c := hbc
    Reaches _ d := hcd

-- 2. The first custom instance preserves `Reaches`; the next two ensure that
-- once the chain becomes strict, the final result remains strict.
example (a b c d : Nat)
    (hab : Reaches a b)
    (hbc : StrictlyReaches b c)
    (hcd : Reaches c d) :
    StrictlyReaches a d := by
  calc
    Reaches a b := hab
    StrictlyReaches _ c := hbc
    Reaches _ d := hcd

-- 3. Equality composes with arbitrary relations using generic `Trans`
-- instances from Lean's prelude. Thus a chain can enter and leave our custom
-- relation through equality steps without extra instances here.
example (a b c d : Nat)
    (hab : Eq a b) (hbc : Reaches b c) (hcd : Eq c d) :
    Reaches a d := by
  calc
    Eq a b := hab
    Reaches _ c := hbc
    Eq _ d := hcd

end PrefixRelationCalcPractice


namespace CategoryCalcPractice

/-!
## `calc` in category-theoretic proofs

These remain open for practice. The first exercise uses a custom prefix
relation on objects; the others calculate with equalities of morphisms.
-/

open CategoryTheory

universe v v₁ u u₁

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

/-- There is at least one morphism from `A` to `B`. -/
def HasArrow (A B : C) : Prop := Nonempty (A ⟶ B)

instance : Trans (HasArrow (C := C)) (HasArrow (C := C)) (HasArrow (C := C)) where
  trans
    | ⟨f⟩, ⟨g⟩ => ⟨f ≫ g⟩

-- 1. Composition makes `HasArrow` transitive. Use it as a prefix relation in
-- a `calc` chain through all four objects.
example (hWX : HasArrow W X) (hXY : HasArrow X Y) (hYZ : HasArrow Y Z) :
    HasArrow W Z := by
  calc
    HasArrow W X := hWX
    HasArrow _ Y := hXY
    HasArrow _ Z := hYZ

-- 2. Normalize the identities and reassociate the composition in several
-- visible stages. This is intentionally more work than `simp` would require.
example (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (((𝟙 W) ≫ f) ≫ g) ≫ h = f ≫ (g ≫ (h ≫ 𝟙 Z)) := by
  -- actually simp does close this. but let's ignore that
  calc
    (((𝟙 W) ≫ f) ≫ g) ≫ h
      = (f ≫ g) ≫ h := by simp
    _ = (f ≫ g) ≫ (h ≫ 𝟙 Z) := by simp
    _ = f ≫ (g ≫ (h ≫ 𝟙 Z)) := by simp

-- 3. Change one morphism at a time, while also changing the association of
-- the composite. The hypotheses themselves are only about individual arrows.
example (f f' : W ⟶ X) (g g' : X ⟶ Y) (h h' : Y ⟶ Z)
    (hf : f = f') (hg : g = g') (hh : h = h') :
    (f ≫ g) ≫ h = f' ≫ (g' ≫ h') := by
  calc
    (f ≫ g) ≫ h
      = (f' ≫ g) ≫ h := by rw [hf]
    _ = (f' ≫ g') ≫ h := by rw [hg]
    _ = (f' ≫ g') ≫ h' := by rw [hh]
    _ = f' ≫ (g' ≫ h') := by simp

variable {D : Type u₁} [Category.{v₁} D]

-- 4. Combine functoriality (`map_comp`, `map_id`) with the category laws.
-- Useful landmarks are `F.map (f ≫ g)` and `F.map f ≫ F.map g`.
example (F : C ⥤ D) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (((𝟙 W) ≫ f) ≫ (g ≫ h)) =
      (𝟙 (F.obj W)) ≫ (F.map f ≫ (F.map g ≫ F.map h)) := by
  calc
    F.map (((𝟙 W) ≫ f) ≫ (g ≫ h))
      = (F.map ((𝟙 W) ≫ f)) ≫ F.map (g ≫ h) := F.map_comp ((𝟙 W) ≫ f) (g ≫ h) -- by simp is fine too
    _ = (F.map (𝟙 W) ≫ F.map f) ≫ F.map (g ≫ h) := by simp
    _ = (F.map (𝟙 W) ≫ F.map f) ≫ F.map g ≫ F.map h := by simp
    _ = (𝟙 (F.obj W)) ≫ F.map f ≫ F.map g ≫ F.map h := by simp
-- or whatever

-- 5. Prove naturality of a composite transformation by calculating through
-- the naturality equations for `α` and `β`, with associativity steps between
-- them. Avoid invoking the naturality theorem for `α ≫ β` directly.
example (F G H : C ⥤ D) (α : F ⟶ G) (β : G ⟶ H) (f : X ⟶ Y) :
    F.map f ≫ (α ≫ β).app Y = (α ≫ β).app X ≫ H.map f := by
  -- `simp` works for each step of this `calc`, and for the top level,
  -- but let's be more explicit
  calc
    F.map f ≫ (α ≫ β).app Y
      = F.map f ≫ α.app Y ≫ β.app Y := by rw [(α.vcomp_app' β)]
    _ = α.app X ≫ G.map f ≫ β.app Y := by
          rw [← Category.assoc, (α.naturality f), Category.assoc]
    _ = α.app X ≫ β.app X ≫ H.map f := by rw [(β.naturality f)]
    _ = (α ≫ β).app X ≫ H.map f := by rw [← Category.assoc, (α.vcomp_app' β)]

end CategoryCalcPractice
