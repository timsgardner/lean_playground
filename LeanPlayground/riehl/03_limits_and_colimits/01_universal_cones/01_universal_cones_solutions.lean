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
