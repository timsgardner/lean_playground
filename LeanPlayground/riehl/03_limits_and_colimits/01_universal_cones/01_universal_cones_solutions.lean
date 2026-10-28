/-
# Solutions to selected exercises in `01_universal_cones.lean`

Spoilers. This file imports the exercise file and reuses its definitions
(`mulBy`, `intPullback_data`). Each solved declaration carries a `_sol` suffix
so that it does not clash with the `sorry`'d one it solves.
-/
import LeanPlayground.riehl.«03_limits_and_colimits».«01_universal_cones».«01_universal_cones»

open CategoryTheory Limits

universe v₁ u₁

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-! ## Example 3.1.19: exercises (Z1)–(Z6) -/

section IntPullbackSolutions

-- (Z1)
example (k x : ℤ) : mulBy k x = k * x := rfl

-- (Z2): `ext1` applies `AddMonoidHom.ext_int`, leaving the value at `1`
example (φ ψ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (h : φ 1 = ψ 1) : φ = ψ := by
  ext1
  exact h

-- (Z3): `g a x - g b y = (n x - m y) - x (n - a g) + y (m - b g)`
theorem cancel_gcd_sol {n m a b g x y : ℤ} (hn : n = a * g) (hm : m = b * g) (hg : g ≠ 0)
    (h : n * x = m * y) : a * x = b * y := by
  apply mul_left_cancel₀ hg
  linear_combination h - x * hn + y * hm

-- (Z4)
theorem mulBy_square_sol {n m a b g : ℤ} (hn : n = a * g) (hm : m = b * g) :
    mulBy b ≫ mulBy n = mulBy a ≫ mulBy m := by
  ext
  change n * (b * 1) = m * (a * 1)
  rw [hn, hm]
  ring

-- (Z5): each `linear_combination` is the displayed calculation in the exercise
-- comment, with `h : a x = b y` and `hpq : p a + q b = 1`
noncomputable def intPullbackIsLimit_sol {n m a b g p q : ℤ} (hn : n = a * g)
    (hm : m = b * g) (hg : g ≠ 0) (hpq : p * a + q * b = 1) :
    IsLimit (PullbackCone.mk (mulBy b) (mulBy a) (mulBy_square_sol hn hm)) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom (p • s.snd.hom + q • s.fst.hom)) ?_ ?_ ?_
  · intro s
    ext x
    have h : a * s.fst x = b * s.snd x :=
      cancel_gcd_sol hn hm hg (ConcreteCategory.congr_hom s.condition x)
    change b * (p * s.snd x + q * s.fst x) = s.fst x
    linear_combination (-p) * h + s.fst x * hpq
  · intro s
    ext x
    have h : a * s.fst x = b * s.snd x :=
      cancel_gcd_sol hn hm hg (ConcreteCategory.congr_hom s.condition x)
    change a * (p * s.snd x + q * s.fst x) = s.snd x
    linear_combination q * h + s.snd x * hpq
  · intro s k hb ha
    ext x
    have hb' : b * k x = s.fst x := ConcreteCategory.congr_hom hb x
    have ha' : a * k x = s.snd x := ConcreteCategory.congr_hom ha x
    change k x = p * s.snd x + q * s.fst x
    linear_combination p * ha' + q * hb' - k x * hpq

-- (Z6)
theorem example_3_1_19_sol (n m : ℤ) (h : n ≠ 0 ∨ m ≠ 0) :
    ∃ a b : ℤ, IsPullback (mulBy b) (mulBy a) (mulBy n) (mulBy m) := by
  obtain ⟨a, b, g, p, q, hn, hm, hg, hpq⟩ := intPullback_data n m h
  exact ⟨a, b, IsPullback.of_isLimit (intPullbackIsLimit_sol hn hm hg hpq)⟩

end IntPullbackSolutions

/-! ## The `IsPullback` API: exercises (I1)–(I7) -/

section IsPullbackAPISolutions

variable {P B C A : 𝒞} {fst : P ⟶ B} {snd : P ⟶ C} {f : B ⟶ A} {g : C ⟶ A}

-- (I1)
example {f : B ⟶ A} {g : C ⟶ A} (t : PullbackCone f g) (ht : IsLimit t) :
    IsPullback t.fst t.snd f g :=
  IsPullback.of_isLimit ht

noncomputable example (h : IsPullback fst snd f g) : IsLimit (PullbackCone.mk fst snd h.w) :=
  h.isLimit

example (h : IsPullback fst snd f g) : fst ≫ f = snd ≫ g :=
  h.w

-- (I2)
example (h : IsPullback fst snd f g) {D : 𝒞} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) : h.lift b c w ≫ fst ≫ f = c ≫ g := by
  simpa using w

example (h : IsPullback fst snd f g) {D : 𝒞} (b : D ⟶ B) (c : D ⟶ C)
    (w : b ≫ f = c ≫ g) (m : D ⟶ P) (hb : m ≫ fst = b) (hc : m ≫ snd = c) :
    m = h.lift b c w := by
  apply h.hom_ext <;> simp [hb, hc]

-- (I3)
theorem mono_snd_of_isPullback_sol (h : IsPullback fst snd f g) [Mono f] : Mono snd := by
  constructor
  intro D k l hkl
  apply h.hom_ext _ hkl
  rw [← cancel_mono f, Category.assoc, Category.assoc, h.w, reassoc_of% hkl]

-- (I4)
theorem mono_fst_of_isPullback_sol (h : IsPullback fst snd f g) [Mono g] : Mono fst :=
  mono_snd_of_isPullback_sol h.flip

-- (I5)
example {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : 𝒞} {a : X₁₁ ⟶ X₁₂} {b : X₂₁ ⟶ X₂₂} {c : X₃₁ ⟶ X₃₂}
    {p : X₁₁ ⟶ X₂₁} {q : X₁₂ ⟶ X₂₂} {r : X₂₁ ⟶ X₃₁} {s : X₂₂ ⟶ X₃₂}
    (top : IsPullback a p q b) (bot : IsPullback b r s c) :
    IsPullback a (p ≫ r) (q ≫ s) c :=
  (top.flip.paste_horiz bot.flip).flip

-- (I6)
noncomputable def isoOfIsPullback_sol {P' : 𝒞} {fst' : P' ⟶ B} {snd' : P' ⟶ C}
    (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : P ≅ P' where
  hom := h'.lift fst snd h.w
  inv := h.lift fst' snd' h'.w
  hom_inv_id := by apply h.hom_ext <;> simp
  inv_hom_id := by apply h'.hom_ext <;> simp

example (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst f g = fst := by
  simp

-- (I7)
example (f : B ⟶ A) : IsPullback (𝟙 B) f f (𝟙 A) :=
  IsPullback.id_horiz f

end IsPullbackAPISolutions

/-! ## Definition 3.1.21 and Example 3.1.22: exercises (T1)–(T5) -/

section InverseLimitSolutions

open Opposite

variable {X : ℕ → 𝒞} (f : ∀ n, X (n + 1) ⟶ X n)

-- (T1)
example : (Functor.ofOpSequence f).obj (op 3) = X 3 := rfl

example : (Functor.ofOpSequence f).map (homOfLE (show 0 ≤ 2 by omega)).op = f 1 ≫ f 0 := rfl

example (n : ℕ) :
    (Functor.ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op = f n :=
  Functor.ofOpSequence_map_homOfLE_succ f n

-- (T2)
def towerCone_sol (c : 𝒞) (leg : ∀ n, c ⟶ X n) (w : ∀ n, leg (n + 1) ≫ f n = leg n) :
    Cone (Functor.ofOpSequence f) where
  pt := c
  π := NatTrans.ofOpSequence (fun n => leg n) (fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.id_comp _).trans (w n).symm)

end InverseLimitSolutions

section InverseLimitOfTypesSolutions

open Opposite

universe w

variable {X : ℕ → Type w} (f : ∀ n, X (n + 1) → X n)

-- (T3)
def towerTypeIsLimit_sol : IsLimit (towerTypeCone f) where
  lift s := ↾(fun p => ⟨fun n => s.π.app (op n) p, fun n => by
    have := ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_add_right n 1)).op) p
    simp at this
    exact this⟩)
  fac s j := by
    rfl
  uniq s m h := by
    ext p
    apply Subtype.ext
    funext n
    exact ConcreteCategory.congr_hom (h (op n)) p

variable (A : Type w)

-- (T4a)
theorem trunc_compat_sol {x : ∀ n, Fin (n + 1) → A}
    (hx : ∀ n, truncRestrict A n (x (n + 1)) = x n) (n : ℕ) (i : Fin (n + 1)) :
    x n i = x i (Fin.last i) := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · rw [show x (n + 1) j.castSucc = x n j from congrFun (hx n) j, ih j]
      simp only [Fin.val_castSucc]

-- (T4b)
def truncEquiv_sol :
    (ℕ → A) ≃ towerLimitType (X := fun n => Fin (n + 1) → A) (truncRestrict A) where
  toFun a := ⟨fun n i => a i, fun n => rfl⟩
  invFun x k := x.1 k (Fin.last k)
  left_inv a := rfl
  right_inv x := by
    apply Subtype.ext
    funext n i
    exact (trunc_compat_sol A x.2 n i).symm

end InverseLimitOfTypesSolutions

section InitialObjectSolutions

universe v₂ u₂

variable {J : Type u₂} [Category.{v₂} J] {i : J} (hi : IsInitial i) (G : J ⥤ 𝒞)

-- (T5)
def initialCone_sol : Cone G where
  pt := G.obj i
  π := { app j := G.map (hi.to j)
         naturality j k u := by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
             ← G.map_comp]
           congr 1
           exact hi.hom_ext _ _ }

def initialConeIsLimit_sol : IsLimit (initialCone_sol hi G) where
  lift s := s.π.app i
  fac s j := by
    simp [initialCone_sol]
  uniq s m h := by
    rw [← h i]
    simp only [initialCone_sol, hi.hom_ext (hi.to i) (𝟙 i), G.map_id]
    exact (Category.comp_id m).symm

end InitialObjectSolutions
