import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.PathCategory.Basic

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


/- The example diagram. `f2` and `g2` are parallel arrows from B to C.

    A1 --f1--+                         +--i1--> E1
             |                         |
             v                         |
             B ==f2,g2==> C --m--> D --+
             ^                         |
             |                         |
    A2 --g1--+                         +--i2--> E2
-/

/- In any category: the signatures are the types, so there's nothing to spell out. -/
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

end Concrete

end section
