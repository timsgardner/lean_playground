import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Types.Basic

/- Ramming monos and epis through my head -/
/- Now on top of Mathlib's category theory API. Rough translation from the
  hand-rolled version:

    Object, Hom A B          ~> objects `X : 𝒞`, morphisms `X ⟶ Y`
    comp f g  (f then g)     ~> `f ≫ g` (same arrow order)
    Hom.id A                 ~> `𝟙 A`
    comp_assoc etc.          ~> `Category.assoc`, `Category.id_comp`, `Category.comp_id`
    mono m                   ~> `Mono m`  (field: `right_cancellation`)
    epi e                    ~> `Epi e`   (field: `left_cancellation`)
    MorphismGraph            ~> a `Quiver` (multidigraph)
    Path, Path.compose       ~> `Quiver.Path`, `composePath`
-/

open CategoryTheory

section
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

universe v u

variable {𝒞 : Type u} [Category.{v} 𝒞]

/- Exercises: reprove these basics by hand from `Mono.mk`/`Epi.mk`,
  `right_cancellation`/`left_cancellation`, and the category laws. Mathlib already
  has them (`mono_comp`, `mono_of_mono`, `IsSplitMono.mono`, and the epi duals),
  so anything that finds those for you is cheating: `inferInstance`, `aesop_cat`,
  or bare `simp` (which knows `cancel_mono` etc.). Bookkeeping with lemmas you
  name yourself, like `simp only [Category.assoc]`, is fine. -/

example (X : 𝒞) : Mono (𝟙 X) := by
  sorry

example
    {X Y Z : 𝒞}
    {m : X ⟶ Y} {n : Y ⟶ Z}
    (hm : Mono m)
    (hn : Mono n)
    : Mono (m ≫ n) := by
  refine ⟨?_⟩
  intro c g1 g2 h1
  #check (hn.right_cancellation (g1 ≫ m) (g2 ≫ m))
  #check (hm.right_cancellation g1 g2)
  apply  (hm.right_cancellation g1 g2)
  apply (hn.right_cancellation (g1 ≫ m) (g2 ≫ m))
  rw [Category.assoc, Category.assoc]
  exact h1

example
    {X Y Z : 𝒞}
    {m : X ⟶ Y} {n : Y ⟶ Z}
    (h : Mono (m ≫ n))
    : Mono m := by
  refine ⟨?_⟩
  intro c f1 f2 heq
  apply h.right_cancellation
  rw [← Category.assoc, heq, Category.assoc]

/-- A morphism with a left inverse (a retraction) is mono. -/
example
    {X Y : 𝒞}
    {m : X ⟶ Y}
    (r : Y ⟶ X)
    (h : m ≫ r = 𝟙 X)
    : Mono m := by
  refine ⟨?_⟩
  intro c f1 f2 heq
  have heq2 := heq =≫ r
  rw [Category.assoc, Category.assoc, h, Category.comp_id, Category.comp_id] at heq2
  exact heq2

example (X : 𝒞) : Epi (𝟙 X) := by
  constructor
  intro c f1 f2
  repeat rw [Category.id_comp]
  tauto

example
    {X Y Z : 𝒞}
    {e : X ⟶ Y} {d : Y ⟶ Z}
    (he : Epi e)
    (hd : Epi d)
    : Epi (e ≫ d) := by
  constructor
  intro c f1 f2 heq
  apply hd.left_cancellation f1 f2
  simp only [Category.assoc] at heq
  exact he.left_cancellation (d ≫ f1) (d ≫ f2) heq

example
    {X Y Z : 𝒞}
    {e : X ⟶ Y} {d : Y ⟶ Z}
    (h : Epi (e ≫ d))
    : Epi d := by
  constructor
  intro c f1 f2 heq
  have heq2 := e ≫= heq
  apply h.left_cancellation
  simpa only [Category.assoc]

/-- A morphism with a right inverse (a section) is epi. -/
example
    {X Y : 𝒞}
    {e : X ⟶ Y}
    (s : Y ⟶ X)
    (h : s ≫ e = 𝟙 Y)
    : Epi e := by
  constructor
  intro c f1 f2 heq
  replace heq := s ≫= heq
  simp only [← Category.assoc, h, Category.id_comp] at heq
  exact heq

/- Contrapositives. To show something is *not* mono, exhibit two different
  maps it fails to tell apart; or reduce to something already known not to be. -/

example
    {A X Y : 𝒞}
    {m : X ⟶ Y}
    (f g : A ⟶ X)
    (hne : f ≠ g)
    (heq : f ≫ m = g ≫ m)
    : ¬ Mono m := by
  intro hm
  replace heq := hm.right_cancellation f g heq
  absurd hne heq
  tauto

example
    {X Y Z : 𝒞}
    {e : X ⟶ Y}
    (f g : Y ⟶ Z)
    (hne : f ≠ g)
    (heq : e ≫ f = e ≫ g)
    : ¬ Epi e := by
  intro he
  replace heq := he.left_cancellation f g heq
  absurd hne heq
  tauto

/-- If `m` isn't mono, nothing you put after it makes it mono. -/
example
    {X Y Z : 𝒞}
    {m : X ⟶ Y} {n : Y ⟶ Z}
    (h : ¬ Mono m)
    : ¬ Mono (m ≫ n) := by
  intro hmn
  have h_mono_m := CategoryTheory.mono_of_mono m n
  absurd h h_mono_m
  tauto

/-- If `d` isn't epi, nothing you put before it makes it epi. -/
example
    {X Y Z : 𝒞}
    {e : X ⟶ Y} {d : Y ⟶ Z}
    (h : ¬ Epi d)
    : ¬ Epi (e ≫ d) := by
  intro hed
  have h_epi_d := CategoryTheory.epi_of_epi e d
  absurd h h_epi_d
  tauto

example
    {X Y Z : 𝒞}
    {m : X ⟶ Y} {n : Y ⟶ Z}
    (hm : Mono m)
    (h : ¬ Mono (m ≫ n))
    : ¬ Mono n := by
  intro hmn
  have h_mono_mn := CategoryTheory.mono_comp m n
  absurd h h_mono_mn
  tauto

/-- A non-mono has no retraction. -/
example
    {X Y : 𝒞}
    {m : X ⟶ Y}
    (h : ¬ Mono m)
    (r : Y ⟶ X)
    : m ≫ r ≠ 𝟙 X := by
  intro hid
  absurd h ?_
  constructor
  · intro c f1 f2 heq
    replace heq := heq =≫ r
    simp [hid] at heq
    exact heq
  · tauto

/-- A non-epi has no section. -/
example
    {X Y : 𝒞}
    {e : X ⟶ Y}
    (h : ¬ Epi e)
    (s : Y ⟶ X)
    : s ≫ e ≠ 𝟙 Y := by
  intro hid
  absurd h ?_
  constructor
  · intro c f1 f2 heq
    replace heq := s ≫= heq
    simp [← Category.assoc, hid] at heq
    tauto
  · tauto

/- Sections and retractions. If `m ≫ r = 𝟙 X`, then `r` is a retraction of `m`
  and `m` is a section of `r`: same equation, two names. -/

/-- A retraction is epi. -/
example
    {X Y : 𝒞}
    (m : X ⟶ Y)
    (r : Y ⟶ X)
    (h : m ≫ r = 𝟙 X)
    : Epi r := by
  constructor
  intro c f1 f2 heq
  replace heq := m ≫= heq
  simp [← Category.assoc, h] at heq
  tauto

/-- A section is mono. -/
example
    {X Y : 𝒞}
    (s : Y ⟶ X)
    (e : X ⟶ Y)
    (h : s ≫ e = 𝟙 Y)
    : Mono s := by
  constructor
  intro c f1 f2 heq
  replace heq := heq =≫ e
  simp [Category.assoc, h] at heq
  tauto

/-- A left inverse and a right inverse of the same morphism are equal. -/
example
    {X Y : 𝒞}
    (m : X ⟶ Y)
    (r s : Y ⟶ X)
    (hr : m ≫ r = 𝟙 X)
    (hs : s ≫ m = 𝟙 Y)
    : r = s := by
  replace hr := s ≫= hr
  rw [← Category.assoc, hs] at hr -- 𝟙 Y ≫ r = s ≫ 𝟙 X
  simp only [Category.id_comp, Category.comp_id] at hr
  exact hr

/-- Retractions compose, in the opposite order. -/
example
    {X Y Z : 𝒞}
    (m : X ⟶ Y) (n  : Y ⟶ Z)
    (r : Y ⟶ X) (r' : Z ⟶ Y)
    (hr : m ≫ r = 𝟙 X)
    (hr' : n ≫ r' = 𝟙 Y)
    : (m ≫ n) ≫ (r' ≫ r) = 𝟙 X := by
  conv =>
    lhs
    rw [Category.assoc]
    rhs
    rw [← Category.assoc]
  -- ⊢ m ≫ (n ≫ r') ≫ r = 𝟙 X
  simp only [hr', Category.id_comp]
  exact hr

/-- If `m ≫ n` has a retraction, so does `m`. -/
example
    {X Y Z : 𝒞}
    (m : X ⟶ Y) (n : Y ⟶ Z)
    (r : Z ⟶ X)
    (h : (m ≫ n) ≫ r = 𝟙 X)
    : ∃ r' : Y ⟶ X, m ≫ r' = 𝟙 X := by
  refine ⟨?r2, ?h2⟩
  case r2 =>
    exact n ≫ r
  case h2 =>
    simp only [← Category.assoc, h]

-- helper so we don't have to keep doing this
theorem mid_assoc_eq
    {U W X Y Z : 𝒞}
    {f1: U ⟶ W}
    {f2: W ⟶ X}
    {f3: X ⟶ Y}
    {f4: Y ⟶ Z}
    : f1 ≫ f2 ≫ f3 ≫ f4 = f1 ≫ (f2 ≫ f3) ≫ f4 := by
  simp

/-- A section-retraction pair gives an idempotent. -/
example
    {X Y : 𝒞}
    (m : X ⟶ Y)
    (r : Y ⟶ X)
    (h : m ≫ r = 𝟙 X)
    : (r ≫ m) ≫ (r ≫ m) = r ≫ m := by
  simp [mid_assoc_eq, h, Category.id_comp]


/- Isos. `IsIso f` says `∃ g, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y`; build one with
  `⟨⟨g, h1, h2⟩⟩`. Given `IsIso f`, use `inv f`, `IsIso.hom_inv_id f`, and
  `IsIso.inv_hom_id f` (these are fine to use). -/

example
    {X Y : 𝒞}
    (f : X ⟶ Y)
    (hf : IsIso f)
    : Mono f := by
  constructor
  intro c f1 f2 heq
  replace heq := heq =≫ inv f
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at heq
  exact heq

example
    {X Y : 𝒞}
    (f : X ⟶ Y)
    (hf : IsIso f)
    : Epi f := by
  constructor
  intro c f1 f2 heq
  replace heq := inv f ≫= heq
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at heq
  exact heq

/-- Mono plus a section is iso. -/
example
    {X Y : 𝒞}
    (m : X ⟶ Y)
    (hm : Mono m)
    (s : Y ⟶ X)
    (h : s ≫ m = 𝟙 Y)
    : IsIso m := by
  constructor
  refine ⟨?bla, ?gra⟩
  case bla =>
    exact s
  case gra =>
    constructor
    · replace h :=  m ≫= h
      simp only [Category.comp_id] at h
      conv at h =>
        rhs
        rw [← Category.id_comp m]
      conv at h =>
        lhs
        rw [← Category.assoc]
      apply hm.right_cancellation (m ≫ s) (𝟙 X)
      exact h
    · tauto

/-- Epi plus a retraction is iso. -/
example
    {X Y : 𝒞}
    (e : X ⟶ Y)
    (he : Epi e)
    (r : Y ⟶ X)
    (h : e ≫ r = 𝟙 X)
    : IsIso e := by
  constructor
  constructor
  case w =>
    exact r
  case h =>
    constructor
    · tauto
    · replace h := h =≫ e
      simp [Category.assoc] at h
      apply he.left_cancellation
      simp
      exact h

/--
/-- A retraction of an iso is its inverse. -/
example
    {X Y : 𝒞}
    (f : X ⟶ Y)
    (hf : IsIso f)
    (r : Y ⟶ X)
    (h : f ≫ r = 𝟙 X)
    : r = inv f := by
  sorry

example
    {X Y Z : 𝒞}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f)
    (hg : IsIso g)
    : IsIso (f ≫ g) := by
  sorry

/-- If `m ≫ n` is iso and `n` is mono, then `m` is iso. -/
example
    {X Y Z : 𝒞}
    (m : X ⟶ Y) (n : Y ⟶ Z)
    (h : IsIso (m ≫ n))
    (hn : Mono n)
    : IsIso m := by
  sorry


/- The example diagram. `f2` and `g2` are parallel arrows from B to C.

    A1 --f1--+                         +--i1--> E1
             |                         |
             v                         |
             B ==f2,g2==> C --m--> D --+
             ^                         |
             |                         |
    A2 --g1--+                         +--i2--> E2
-/

/- The diagram in an arbitrary category. Each arrow's type records its endpoints
  (`f1 : A1 ⟶ B`), so no separate hypotheses about where arrows go are needed. -/
namespace Abstract

variable
  {A1 A2 B C D E1 E2 : 𝒞}
  (f1 : A1 ⟶ B) (g1 : A2 ⟶ B)
  (f2 g2 : B ⟶ C)
  (m : C ⟶ D)
  (i1 : D ⟶ E1) (i2 : D ⟶ E2)

example
    (h_mono : Mono m)
    (h_eq : f2 ≫ m = g2 ≫ m)
    : f2 = g2 :=
  h_mono.right_cancellation f2 g2 h_eq

example
    (h_mono : Mono m)
    (h_neq : f2 ≠ g2)
    : f2 ≫ m ≠ g2 ≫ m :=
  fun h_eq => h_neq (h_mono.right_cancellation f2 g2 h_eq)

/- Telling arrows apart through the diagram. -/

/-- No mono needed for this direction: why? -/
example
    (h : f2 ≫ m ≠ g2 ≫ m)
    : f2 ≠ g2 := by
  sorry

/-- Same idea, longer composite. -/
example
    (h : f1 ≫ f2 ≫ m ≠ f1 ≫ g2 ≫ m)
    : f2 ≠ g2 := by
  sorry

example
    (hm : Mono m)
    (hi : Mono i1)
    (hne : f2 ≠ g2)
    : f2 ≫ m ≫ i1 ≠ g2 ≫ m ≫ i1 := by
  sorry

/-- On the other side, the epi does the work. -/
example
    (he : Epi f1)
    (hne : f2 ≠ g2)
    : f1 ≫ f2 ≠ f1 ≫ g2 := by
  sorry

/-- Epi on the left, mono on the right. -/
example
    (he : Epi f1)
    (hm : Mono m)
    (hne : f2 ≠ g2)
    : f1 ≫ f2 ≫ m ≠ f1 ≫ g2 ≫ m := by
  sorry

/-- A retraction is enough; nobody said `Mono m`. -/
example
    (r : D ⟶ C)
    (hr : m ≫ r = 𝟙 C)
    (hne : f2 ≠ g2)
    : f2 ≫ m ≠ g2 ≫ m := by
  sorry

/-- The parallel pair is a witness: if `m` can't tell them apart, it isn't mono. -/
example
    (hne : f2 ≠ g2)
    (heq : f2 ≫ m = g2 ≫ m)
    : ¬ Mono m := by
  sorry

end Abstract

/- The same diagram as concrete data: a quiver, and the free category on it. -/
namespace Concrete

inductive Ob
  | A1 | A2 | B | C | D | E1 | E2
deriving DecidableEq

/-- The arrows, as an indexed family: a multidigraph. -/
inductive Arrow : Ob → Ob → Type
  | f1 : Arrow .A1 .B
  | g1 : Arrow .A2 .B
  | f2 : Arrow .B .C
  | g2 : Arrow .B .C
  | m  : Arrow .C .D
  | i1 : Arrow .D .E1
  | i2 : Arrow .D .E2

instance : Quiver Ob := ⟨Arrow⟩

/- `Paths Ob` is the free category on the quiver: morphisms are paths of arrows,
  composition is concatenation. `Paths.of Ob` sends each arrow to a length-1 path. -/

def f2 : (Paths.of Ob).obj .B ⟶ (Paths.of Ob).obj .C := (Paths.of Ob).map Arrow.f2
def g2 : (Paths.of Ob).obj .B ⟶ (Paths.of Ob).obj .C := (Paths.of Ob).map Arrow.g2
def m  : (Paths.of Ob).obj .C ⟶ (Paths.of Ob).obj .D := (Paths.of Ob).map Arrow.m

/-- In a free category every morphism is mono: paths cancel on the right. -/
theorem paths_mono {X Y : Paths Ob} (p : X ⟶ Y) : Mono p :=
  ⟨fun _ _ h => Quiver.Path.comp_inj_left.1 h⟩

example : f2 ≫ m ≠ g2 ≫ m :=
  fun h_eq => by
    have := (paths_mono m).right_cancellation f2 g2 h_eq
    simp [f2, g2, Quiver.Hom.toPath] at this
    cases this

/-- Exercise: every morphism is epi too. Hint: `Quiver.Path.comp_inj_right`. -/
theorem paths_epi {X Y : Paths Ob} (p : X ⟶ Y) : Epi p := by
  sorry

/-- Exercise: so `f2` is mono and epi, but not an iso: mono + epi ≠ iso in general.
  Hint: an inverse `k` would make `f2 ≫ k` the empty path. Compare lengths with
  `Quiver.Path.length_comp`. In `Paths`, `≫` is `Quiver.Path.comp` and `𝟙` is
  `Quiver.Path.nil` by definition, but lemmas won't fire until you `change` the
  goal or hypothesis into that form. -/
example : ¬ IsIso f2 := by
  sorry

end Concrete

/- Concrete non-monos and non-epis live in `Type`, where morphisms are functions
  (built with `TypeCat.ofHom`), mono means injective and epi means surjective. The
  helper lemmas below handle the `Type` API so the exercises are pure mono/epi logic. -/
namespace InType

open TypeCat

/-- Collapse both booleans to the one point. Not injective, so not mono. -/
def toUnit : Bool ⟶ PUnit.{1} := ofHom fun _ => PUnit.unit
/-- Pick out `true` and `false`. Not surjective, so not epi. -/
def pickT : PUnit.{1} ⟶ Bool := ofHom fun _ => true
def pickF : PUnit.{1} ⟶ Bool := ofHom fun _ => false
def constT : Bool ⟶ Bool := ofHom fun _ => true

theorem pickT_ne_pickF : pickT ≠ pickF := fun h => by
  have := congrArg (fun f => f PUnit.unit) h
  simp [pickT, pickF] at this

theorem pickT_toUnit_eq : pickT ≫ toUnit = pickF ≫ toUnit := by
  ext

theorem id_ne_constT : 𝟙 Bool ≠ constT := fun h => by
  have := congrArg (fun f => f false) h
  simp [constT] at this

theorem pickT_id_eq : pickT ≫ 𝟙 Bool = pickT ≫ constT := by
  ext
  rfl

/-- `pickT` is a section of `toUnit`. -/
theorem pickT_toUnit_id : pickT ≫ toUnit = 𝟙 PUnit.{1} := by
  ext

/-- Exercise. -/
example : ¬ Mono toUnit := by
  sorry

/-- Exercise. -/
example : ¬ Epi pickT := by
  sorry

/-- Exercise: `toUnit` is epi (it has a section) but not iso. -/
example : Epi toUnit ∧ ¬ IsIso toUnit := by
  sorry

/- Exercises: in `Type`, mono means injective and epi means surjective. Mathlib has
  these (`mono_iff_injective`, `epi_iff_surjective`), so don't use them. Useful API:
    `ofHom (fun x => ...)`        builds a morphism from a function
    `types_comp_apply`            `(f ≫ g) x = g (f x)`  (`ofHom_apply` likewise)
    `types_congr_hom h x`         turns `h : f = g` into `f x = g x`
    `ext x`                       proves two morphisms equal pointwise
  `simp` is fine here for evaluating morphisms at points. -/

/-- Hint for →: to test injectivity at `a b : X`, map the one-point type in twice,
  once picking `a` and once picking `b`. -/
theorem my_mono_iff_injective {X Y : Type} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  sorry

/-- Hint for →: map `Y` into `Prop` twice: once to `True`, once to "is in the image
  of `f`". These agree after `f`. -/
theorem my_epi_iff_surjective {X Y : Type} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  sorry

end InType

end section
