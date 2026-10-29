/-
# Solutions to the exercises in `01_adjoint_functors.lean`

Spoilers. This file imports the exercise file. Each solved declaration carries a
`_sol` suffix so that it does not clash with the `sorry`'d one it solves.
-/
import LeanPlayground.riehl.«04_adjunctions».«01_adjoint_functors».«01_adjoint_functors»

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [Category.{v₂} 𝒟]

/-! ## (E) Warm-ups on `Equiv` -/

example {α β : Type*} (e : α ≃ β) (a : α) : e.symm (e a) = a := e.symm_apply_apply a

example {α β : Type*} (e : α ≃ β) (b : β) : e (e.symm b) = b := e.apply_symm_apply b

example {α β : Type*} (e : α ≃ β) (a : α) (b : β) : e.symm b = a ↔ b = e a :=
  e.symm_apply_eq

example {α β : Type*} (e : α ≃ β) (a : α) (b : β) : a = e.symm b ↔ e a = b :=
  e.eq_symm_apply

example {α β : Type*} (e : α ≃ β) (a a' : α) (h : e a = e a') : a = a' := e.injective h

/-! ## Exercise 1: Lemma 4.1.3, forward direction -/

example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (w : f ≫ k = F.map h ≫ g) :
    adj.homEquiv c d f ≫ G.map k = h ≫ adj.homEquiv c' d' g := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left, w]

example {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c c' : 𝒞} {d d' : 𝒟}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d')
    (w : adj.homEquiv c d f ≫ G.map k = h ≫ adj.homEquiv c' d' g) :
    f ≫ k = F.map h ≫ g := by
  apply (adj.homEquiv c d').injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, w]

/-! ## Exercise 2: Lemma 4.1.3, converse -/

section Squares

variable {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
  (hsq : ∀ {c c' : 𝒞} {d d' : 𝒟} (h : c ⟶ c') (k : d ⟶ d')
    (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d'),
    f ≫ k = F.map h ≫ g ↔ e c d f ≫ G.map k = h ≫ e c' d' g)
include hsq

theorem nat_right_of_squares_sol {c : 𝒞} {d d' : 𝒟} (f : F.obj c ⟶ d) (k : d ⟶ d') :
    e c d' (f ≫ k) = e c d f ≫ G.map k := by
  have := (hsq (𝟙 c) k f (f ≫ k)).mp (by simp)
  rw [this, Category.id_comp]

theorem nat_left_symm_of_squares_sol {c' c : 𝒞} {d : 𝒟} (h : c' ⟶ c) (g : c ⟶ G.obj d) :
    (e c' d).symm (h ≫ g) = F.map h ≫ (e c d).symm g := by
  have := (hsq h (𝟙 d) ((e c' d).symm (h ≫ g)) ((e c d).symm g)).mpr (by simp)
  rw [← this, Category.comp_id]

def adjOfSquares_sol : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun h g => nat_left_symm_of_squares_sol e hsq h g
      homEquiv_naturality_right := fun f k => nat_right_of_squares_sol e hsq f k }

end Squares

/-! ## (P) Warm-ups on preorder categories -/

section Preorders

variable {X : Type*} [Preorder X]

example {x y : X} (h : x ≤ y) : x ⟶ y := homOfLE h

example {x y : X} (f : x ⟶ y) : x ≤ y := leOfHom f

example {x y : X} (f g : x ⟶ y) : f = g := Subsingleton.elim f g

example {l : X → X} (hl : Monotone l) (x : X) : hl.functor.obj x = l x := rfl

end Preorders

/-! ## Exercise 3: a Galois connection is an adjunction -/

example {X Y : Type*} [Preorder X] [Preorder Y] {l : X → Y} {u : Y → X}
    (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => (gc.le_u f.le).hom
          invFun := fun g => (gc.l_le g.le).hom
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ } }

/-! ## Exercise 4: floor and ceiling -/

section Floor

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α]

theorem gc_cast_floor_sol : GaloisConnection ((↑) : ℤ → α) Int.floor :=
  fun _ _ => Int.le_floor.symm

theorem gc_ceil_cast_sol : GaloisConnection Int.ceil ((↑) : ℤ → α) :=
  fun _ _ => Int.ceil_le

end Floor

/-! ## Exercise 5: image, preimage, and `kernImage` -/

section Image

variable {A B : Type*} (f : A → B)

theorem gc_image_preimage_sol : GaloisConnection (Set.image f) (Set.preimage f) := by
  intro s t
  constructor
  · intro h a ha
    exact h ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h ha

theorem gc_preimage_kernImage_sol :
    GaloisConnection (Set.preimage f) (Set.kernImage f) := by
  intro t s
  constructor
  · intro h b hb a hab
    exact h (show f a ∈ t from hab ▸ hb)
  · intro h a ha
    exact h ha rfl

end Image

/-! ## Exercise 6: quantifiers -/

section Quantifiers

variable (X : Type*)

theorem gc_exists_const_sol :
    GaloisConnection (fun p : X → Prop => ∃ x, p x) (fun q _ => q) := by
  intro p q
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx

theorem gc_const_forall_sol :
    GaloisConnection (fun (q : Prop) (_ : X) => q) (fun p => ∀ x, p x) := by
  intro q p
  constructor
  · intro h hq x
    exact h x hq
  · intro h x hq
    exact h hq x

end Quantifiers
