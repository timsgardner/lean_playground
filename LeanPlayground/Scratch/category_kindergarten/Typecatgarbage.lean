import Mathlib

/-!
# Transport-garbage exercises

Each section is built to produce a specific kind of unreadable goal. Every
`sorry` is a target. The "Strategy" comment names the tool the section is
meant to exercise; no solutions are included.

Diagnostic to keep at hand: put `set_option pp.coercions false in` (or
`set_option pp.explicit true in`) in front of an `example` to see the real
head constants. Head constants decide whether a simp lemma can fire.

Written against the post-2025 `ConcreteCategory` API. Some lemma names may
differ in your Mathlib; `#check`, `exact?`, `rw?` and `simp?` will find them.
-/

open CategoryTheory

universe u

/-! ## Exercise 1: an uninstrumented coercion

Strategy: `@[coe]`, `@[norm_cast]`, `push_cast`.

World W2 is `Evn` (even naturals, stored by their half). World W1 is `ℕ`.
`Evn.toNat` is `to-w1`; `Evn.ofNat` is a `to-w2`-style construction.

Work through it in two passes:
1. Try the `example`s with the file as written. Hover over the goals.
2. Tag `Evn.toNat` with `@[coe]`, prove the transport lemmas, tag them
   (`@[simp]` or `@[norm_cast]`), and redo the `example`s. `norm_cast` rejects
   a lemma whose shape is wrong for it; that rejection tells you something.
-/

namespace Ex1

structure Evn where
  half : ℕ

/-- `to-w1`. Deliberately NOT tagged `@[coe]`. -/
def Evn.toNat (a : Evn) : ℕ := 2 * a.half

instance : Coe Evn ℕ := ⟨Evn.toNat⟩

/-- A `to-w2`-style construction: the even "shadow" `2n` of a natural `n`. -/
def Evn.ofNat (n : ℕ) : Evn := ⟨n⟩

def Evn.add (a b : Evn) : Evn := ⟨a.half + b.half⟩
def Evn.mul (a b : Evn) : Evn := ⟨2 * a.half * b.half⟩

instance : Add Evn := ⟨Evn.add⟩
instance : Mul Evn := ⟨Evn.mul⟩

-- Transport lemmas. Proving them forces you to unfold `+` and `*` through the
-- instances; note what those goals look like, and consider stating `rfl`
-- lemmas such as `Evn.add_def : a + b = Evn.add a b` first.
theorem Evn.toNat_add (a b : Evn) : ((a + b : Evn) : ℕ) = (a : ℕ) + b := by
  sorry

theorem Evn.toNat_mul (a b : Evn) : ((a * b : Evn) : ℕ) = (a : ℕ) * b := by
  sorry

theorem Evn.toNat_ofNat (n : ℕ) : ((Evn.ofNat n : Evn) : ℕ) = 2 * n := by
  sorry

theorem Evn.toNat_inj {a b : Evn} : (a : ℕ) = (b : ℕ) ↔ a = b := by
  sorry

/-- The nested sexpr shape, written with explicit function names. -/
example (a b : Evn) :
    Evn.toNat (Evn.ofNat (Evn.toNat a + Evn.toNat b) * a)
      = 2 * ((a : ℕ) + b) * a := by
  sorry

/-- A W1 fact used to prove a W2 fact. -/
example (a b c d : Evn) (h : (a : ℕ) * b = (c : ℕ) + d) :
    ((a * b + c : Evn) : ℕ) = 2 * (c : ℕ) + d := by
  sorry

/-- An equality in W2, proved by moving the whole problem to W1. -/
example (a b c : Evn) : (a + b) * c = a * c + b * c := by
  sorry

end Ex1

/-! ## Exercise 2: a functor without projection lemmas

Strategy: `@[simps]`.

`diag` is defined with no generated lemmas, so `simp` cannot reduce
`diag.map` or `diag.obj`; only `rfl`, `dsimp only [diag]` and `change` see
through them. Do the examples once as written, then add `@[simps]` to `diag`
and redo them with `simp`.

If your Mathlib has made morphisms in `Type` a structure rather than plain
functions, the `map` field below needs wrapping (`TypeCat.ofHom` or `↾`).
-/

namespace Ex2

def diag : Type u ⥤ Type u where
  obj X := X × X
  map f := fun p => (f p.1, f p.2)

example {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X × X) :
    (diag.map g (diag.map f p) : Z × Z).1 = g (f p.1) := by
  sorry

/-- Composite functors: `(F ⋙ G).map f` versus `G.map (F.map f)`. These are
defeq, which is why `rfl` closes goals that `rw` cannot touch. -/
example {X Y : Type u} (f : X ⟶ Y) (p : (X × X) × (X × X)) :
    ((diag ⋙ diag).map f p : (Y × Y) × (Y × Y)).2.1 = f p.2.1 := by
  sorry

end Ex2

/-! ## Exercise 3: `.toFun` leakage in a concrete category

Strategy: restore the `⇑` normal form (`toFun_eq_coe`-style lemmas), then
work at the morphism level (`ConcreteCategory.congr_hom`, `elementwise_of%`,
`comp_apply`).

The first goal is stated in the broken normal form on purpose. The statement
mixes `DFunLike.coe` (the outer application) with `.toFun` (the inner one).
-/

namespace Ex3

variable {M N P : MonCat.{u}}

example (f1 f2 : M ⟶ N) (f : N ⟶ P) (h : f1 ≫ f = f2 ≫ f) (x : M) :
    (ConcreteCategory.hom f) ((ConcreteCategory.hom f1).toFun x) =
      (ConcreteCategory.hom f) ((ConcreteCategory.hom f2).toFun x) := by
  sorry

/-- The same fact, deeper. Try it once by rewriting the goal and once by
normalizing a specialized copy of `h` with `simpa using`. -/
example {Q : MonCat.{u}} (f1 f2 : M ⟶ N) (f : N ⟶ P) (g : P ⟶ Q)
    (h : f1 ≫ f = f2 ≫ f) (x y : M) :
    ConcreteCategory.hom (f ≫ g) ((ConcreteCategory.hom f1).toFun (x * y)) =
      ConcreteCategory.hom g
        (ConcreteCategory.hom f (ConcreteCategory.hom f2 x * (ConcreteCategory.hom f2).toFun y)) := by
  sorry

end Ex3

/-! ## Exercise 4: faithfulness moves the problem to `Type`

Strategy: `Functor.map_injective` for a faithful functor, then `ext`.

Prove the first example via `apply (forget MonCat).map_injective` and look at
what `forget` did to the goal. Then find the idiomatic one-step `ext` lemma
and compare the two goal states.
-/

namespace Ex4

variable {M N : MonCat.{u}}

example (f g : M ⟶ N) (h : ∀ x, ConcreteCategory.hom f x = ConcreteCategory.hom g x) :
    f = g := by
  sorry

example (f g : M ⟶ N) (h : ∀ x, ConcreteCategory.hom f x = ConcreteCategory.hom g x) :
    (forget MonCat).map f = (forget MonCat).map g := by
  sorry

end Ex4

/-! ## Exercise 5: round trips through an isomorphism

Strategy: `Functor.map_comp` and `Functor.map_id` as fmap fusion, plus the
elementwise cancellation lemmas (`Iso.hom_inv_id_apply`, `types_comp_apply`).
-/

namespace Ex5

example {X Y : Type u} (F : Type u ⥤ Type u) (e : X ≅ Y) (y : F.obj Y) :
    F.map e.hom (F.map e.inv y) = y := by
  sorry

example {X Y : Type u} (F G : Type u ⥤ Type u) (e : X ≅ Y) (y : G.obj (F.obj Y)) :
    G.map (F.map e.hom) (G.map (F.map e.inv) y) = y := by
  sorry

/-- Combines Exercise 2 and Exercise 5: the round trip runs through a functor
with no projection lemmas. -/
example {X Y : Type u} (e : X ≅ Y) (p : Y × Y) :
    Ex2.diag.map e.hom (Ex2.diag.map e.inv p) = p := by
  sorry

end Ex5

/-! ## Exercise 6: unit/counit round trips through an equivalence

Strategy: naturality and unit/counit simp lemmas on `Equivalence`, and
`Functor.comp_map` to reconcile `(F ⋙ G).map f` with `G.map (F.map f)`.
-/

namespace Ex6

variable {C D : Type*} [Category C] [Category D]

example (e : C ≌ D) {a b : C} (f g : a ⟶ b)
    (h : e.functor.map f = e.functor.map g) :
    e.inverse.map (e.functor.map f) ≫ (e.unitIso.app b).inv =
      (e.unitIso.app a).inv ≫ g := by
  sorry

/-- The nested shape: up to W2, back down to W1, up again. -/
example (e : C ≌ D) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    e.functor.map (e.inverse.map (e.functor.map f) ≫ (e.unitIso.app b).inv ≫ g) =
      e.functor.map f ≫ e.functor.map g := by
  sorry

end Ex6
