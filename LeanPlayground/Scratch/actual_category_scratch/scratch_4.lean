import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Logic.Function.Basic
import Mathlib.CategoryTheory.Products.Basic
import LeanPlayground.Scratch.category_kindergarten.check_diagrams
import LeanPlayground.Scratch.category_kindergarten.common_tools
import LeanPlayground.Scratch.category_kindergarten.diagram_tools
import LeanPlayground.diagrams.widget

set_option pp.proofs.withType true

/-
  What each import brings in:

    Category.Basic         `Category`, `X ⟶ Y`, `𝟙 X`, `f ≫ g`, `Category.assoc`
    Functor.Basic          `C ⥤ D`, `F.obj`, `F.map`, `𝟭 C`, `F ⋙ G`
    NatTrans               `NatTrans F G`, `α.app X`, `α.naturality`
    Functor.Category       the functor category: `α : F ⟶ G`, `α ≫ β`, `NatTrans.comp_app`
    Functor.FullyFaithful  `F.Faithful` (`map_injective`), `F.Full` (`map_surjective`),
                           `F.FullyFaithful`
    Comma.Basic            `Comma L R`, with fields `left`, `right`, `hom`, and
                           morphisms `CommaMorphism` (fields `left`, `right`, `w`)
    Logic.Function.Basic   `Function.Injective`, `Function.Surjective`,
                           `Function.Bijective` and their API
    check_diagrams         our infoview diagrams: `#check` draws squares/triangles; with
                           the selection panel below, shift-click a goal or hypothesis
                           (equations `f ≫ g = i ≫ h`, `CommSq`, `comm_diagram`) to draw it
-/

open CategoryTheory

show_panel_widgets [local ProofWidgets.SelectionPanel]

/- Mathlib convention: `u` for the universe of objects, `v` for the universe of
  morphisms (hom-sets). `Category.{v₁} 𝒞` says the hom-sets of `𝒞` live in `Type v₁`. -/
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

/- Three categories, enough for a comma category `Comma L R` with
  `L : 𝒜 ⥤ 𝒞` and `R : ℬ ⥤ 𝒞`. -/
variable {𝒜 : Type u₁} [Category.{v₁} 𝒜]
variable {ℬ : Type u₂} [Category.{v₂} ℬ]
variable {𝒞 : Type u₃} [Category.{v₃} 𝒞]
variable {𝒟 : Type u₄} [Category.{v₄} 𝒟]

example (F : 𝒞 ⥤ 𝒟) [F.Faithful] {X Y : 𝒞} :
    Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  F.map_injective

/-! ## Sandwiches

`sandwich p q f` is the morphism `f : X ⟶ Y` retyped as a morphism `X' ⟶ Y'`, along
equations `p : X = X'` and `q : Y = Y'`. It is `eqToHom p.symm ≫ f ≫ eqToHom q`, but
naming it lets us state how such transported morphisms compose and map, once, instead
of pushing individual `eqToHom`s around in every proof. -/

def sandwich {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) : X' ⟶ Y' :=
  eqToHom p.symm ≫ f ≫ eqToHom q

section Sandwich

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Transporting along reflexivity does nothing. -/
@[simp]
theorem sandwich_rfl {X Y : C} (f : X ⟶ Y) : sandwich rfl rfl f = f := by
  simp [sandwich]

/-- Two sandwiches that meet at the same object compose to the sandwich of the
composite. -/
theorem sandwich_comp {X X' Y Y' Z Z' : C} (p : X = X') (q : Y = Y') (r : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sandwich p q f ≫ sandwich q r g = sandwich p r (f ≫ g) := by
  simp [sandwich]

/-- A functor carries a sandwich to the sandwich of the image. -/
theorem map_sandwich (G : C ⥤ D) {X X' Y Y' : C} (p : X = X') (q : Y = Y')
    (f : X ⟶ Y) :
    G.map (sandwich p q f) = sandwich (congrArg G.obj p) (congrArg G.obj q) (G.map f) := by
  simp [sandwich, eqToHom_map]

/-- Remark: a sandwich "is" `f`, but only up to heterogeneous equality, since
`sandwich p q f : X' ⟶ Y'` and `f : X ⟶ Y` have different types and so cannot be
compared with `=`. This is Mathlib's `conj_eqToHom_iff_heq` in sandwich form. `HEq`
cannot be used with `rw`, so the lemmas above are the ones to compute with. -/
theorem sandwich_heq {X X' Y Y' : C} (p : X = X') (q : Y = Y') (f : X ⟶ Y) :
    sandwich p q f ≍ f := by
  cases p
  cases q
  simp [sandwich]

end Sandwich

/-! # Natural transformations as functors into the arrow category

An object of the arrow category `Arrow 𝒟` is a morphism of `𝒟`, and a morphism of
`Arrow 𝒟` is a commuting square. The functors `Arrow.leftFunc` and `Arrow.rightFunc`
send an arrow to its domain and its codomain. A natural transformation `α : L ⟶ R` is
then a functor `𝒞 ⥤ Arrow 𝒟`, sending `c` to the arrow `α.app c` and `m` to the
naturality square of `α` at `m`, whose composites with `leftFunc` and `rightFunc` are
`L` and `R`.

The equations say that the ends of `S c` are `L c` and `R c`, which are objects of `𝒟`,
so the sandwiches retype along equations in `𝒟` directly. -/

section ArrowVersion

/-- Functors `𝒞 ⥤ Arrow 𝒟` whose domain part is `L` and whose codomain part is `R`. -/
def ArrowLift (L R : 𝒞 ⥤ 𝒟) :=
  {S : 𝒞 ⥤ Arrow 𝒟 // S ⋙ Arrow.leftFunc = L ∧ S ⋙ Arrow.rightFunc = R}

namespace ArrowLift

variable {L R : 𝒞 ⥤ 𝒟}

def fromNatTrans (α : L ⟶ R) : ArrowLift L R :=
  ⟨{obj := fun c => Arrow.mk (α.app c),
    map := fun m => Arrow.homMk (L.map m) (R.map m)},
  by constructor <;> cat_disch⟩

theorem obj_left_eq (S : ArrowLift L R) (c : 𝒞) : (S.val.obj c).left = L.obj c :=
  congrArg (fun G => G.obj c) S.property.1

theorem obj_right_eq (S : ArrowLift L R) (c : 𝒞) : (S.val.obj c).right = R.obj c :=
  congrArg (fun G => G.obj c) S.property.2

/-- The component at `c`: the arrow `S c`, retyped along `(S c).left = L c` and
`(S c).right = R c`. -/
def component (S : ArrowLift L R) (c : 𝒞) : L.obj c ⟶ R.obj c :=
  sandwich (obj_left_eq S c) (obj_right_eq S c) (S.val.obj c).hom

/-! In this version the equations are `S ⋙ leftFunc = L` and `S ⋙ rightFunc = R`, and
`L` and `R` are variables. So in a proof about an arbitrary `S`, both equations can be
substituted away with `obtain ⟨S, rfl, rfl⟩ := S`. After that, every sandwich is
`sandwich rfl rfl`, which `sandwich_rfl` removes, and no transport is left. -/

def toNatTrans (S : ArrowLift L R) : L ⟶ R where
  app := S.component
  naturality c₁ c₂ m := by
    obtain ⟨S, rfl, rfl⟩ := S
    -- With `L = S ⋙ leftFunc` and `R = S ⋙ rightFunc`, this is the square `S m`.
    simp [component, Arrow.w]

/-- Going from `α` to a functor into `Arrow 𝒟` and back gives `α`. -/
theorem toNatTrans_fromNatTrans (α : L ⟶ R) : toNatTrans (fromNatTrans α) = α := by
  ext c
  simp [toNatTrans, component, fromNatTrans, sandwich]

/-- Going from a functor into `Arrow 𝒟` to `α` and back gives the functor. -/
theorem fromNatTrans_toNatTrans (S : ArrowLift L R) :
    fromNatTrans (toNatTrans S) = S := by
  obtain ⟨S, rfl, rfl⟩ := S
  unfold toNatTrans component
  simp only [sandwich_rfl]
  -- What is left is `Arrow.mk (S c).hom = S c` and its analogue on morphisms,
  -- which hold by structure eta.
  rfl

end ArrowLift

/-- Natural transformations `L ⟶ R` are in bijection with the functors
`S : 𝒞 ⥤ Arrow 𝒟` such that `S ⋙ Arrow.leftFunc = L` and `S ⋙ Arrow.rightFunc = R`. -/
def nat_trans_arrow_bij {L R : 𝒞 ⥤ 𝒟} : (L ⟶ R) ≃ ArrowLift L R where
  toFun := ArrowLift.fromNatTrans
  invFun := ArrowLift.toNatTrans
  left_inv := ArrowLift.toNatTrans_fromNatTrans
  right_inv := ArrowLift.fromNatTrans_toNatTrans

end ArrowVersion

/-! # Cancelling a functor that is injective on objects and faithful

If `H` is injective on objects and faithful, then `F ⋙ H` determines `F`. This is the
one place where the comma version below has to transport along equations of objects;
it is a general fact, proved once here. -/

theorem functor_eq_of_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (H : D ⥤ E) [H.Faithful] (hH : Function.Injective H.obj) {F₁ F₂ : C ⥤ D}
    (h : F₁ ⋙ H = F₂ ⋙ H) : F₁ = F₂ := by
  fapply CategoryTheory.Functor.ext
  · intro c
    exact hH (congrArg (fun G => G.obj c) h)
  · intro c₁ c₂ m
    apply H.map_injective
    simpa [eqToHom_map] using Functor.congr_hom h m

/-! # Natural transformations as functors into a comma category, via the arrow category

`commaToArrow L R : Comma L R ⥤ Arrow 𝒟` forgets the legs of an object `(a, b, f)` and
keeps the arrow `f : L a ⟶ R b`. Composing with it turns a lift of `Δ` through `P` into
an `ArrowLift L R`, and everything about the comma version is read off from the arrow
version. The only extra input is that `commaToArrow` together with `P` loses no
information, so that the cancellation lemma above applies. -/

section CommaVersion

/-- Gives a functor from `Comma L R` to pairs of its first and second
(left and right) projections. -/
def commaProjProd (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ 𝒞 × 𝒞 :=
  (Comma.fst L R).prod' (Comma.snd L R)

def NatTransFunctor (L R : 𝒞 ⥤ 𝒟) :=
  {F : 𝒞 ⥤ Comma L R // F ⋙ commaProjProd L R = Functor.diag 𝒞}

/-- The arrow underlying an object of `Comma L R`. -/
def commaToArrow (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ Arrow 𝒟 where
  obj X := Arrow.mk X.hom
  map f := Arrow.homMk (L.map f.left) (R.map f.right) f.w

/-- `commaToArrow` and `P` together: an object goes to its arrow and its legs. -/
def commaToArrowProj (L R : 𝒞 ⥤ 𝒟) : Comma L R ⥤ Arrow 𝒟 × (𝒞 × 𝒞) :=
  (commaToArrow L R).prod' (commaProjProd L R)

/-- A comma morphism is determined by its legs. -/
instance (L R : 𝒞 ⥤ 𝒟) : (commaToArrowProj L R).Faithful where
  map_injective {_ _} f g h := by
    -- The `𝒞 × 𝒞` component of `h` says the legs agree.
    have h' := congrArg Prod.snd h
    exact Comma.hom_ext f g (congrArg Prod.fst h') (congrArg Prod.snd h')

/-- A comma object is determined by its arrow and its legs. -/
theorem commaToArrowProj_injective (L R : 𝒞 ⥤ 𝒟) :
    Function.Injective (commaToArrowProj L R).obj := by
  rintro ⟨a, b, f⟩ ⟨a', b', f'⟩ h
  simp only [commaToArrowProj, commaToArrow, commaProjProd, Functor.prod'_obj,
    Comma.fst_obj, Comma.snd_obj, Prod.mk.injEq] at h
  obtain ⟨hf, rfl, rfl⟩ := h
  obtain ⟨_, _, hf⟩ := (Arrow.mk_eq_mk_iff f f').1 hf
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  rw [hf]

namespace NatTransFunctor

variable {L R : 𝒞 ⥤ 𝒟}

def fromNatTrans (α : L ⟶ R) : NatTransFunctor L R :=
  ⟨{obj := fun c => ⟨c, c, α.app c⟩,
    map := fun f => ⟨f, f, by cat_disch⟩},
  by cat_disch⟩

/-- A lift of `Δ`, composed with `commaToArrow`, is a functor into `Arrow 𝒟` over `L`
and `R`. -/
def toArrowLift (F : NatTransFunctor L R) : ArrowLift L R :=
  ⟨F.val ⋙ commaToArrow L R, by
    -- `F ⋙ fst` and `F ⋙ snd` are the two components of `F ⋙ P = Δ`.
    have h₁ : F.val ⋙ Comma.fst L R = 𝟭 𝒞 :=
      congrArg (· ⋙ CategoryTheory.Prod.fst 𝒞 𝒞) F.property
    have h₂ : F.val ⋙ Comma.snd L R = 𝟭 𝒞 :=
      congrArg (· ⋙ CategoryTheory.Prod.snd 𝒞 𝒞) F.property
    -- `commaToArrow ⋙ leftFunc` is `fst ⋙ L` by definition, and likewise on the right.
    exact ⟨show (F.val ⋙ Comma.fst L R) ⋙ L = L by rw [h₁]; rfl,
      show (F.val ⋙ Comma.snd L R) ⋙ R = R by rw [h₂]; rfl⟩⟩

def toNatTrans (F : NatTransFunctor L R) : L ⟶ R :=
  F.toArrowLift.toNatTrans

/-- The two `fromNatTrans` agree, by definition. -/
theorem fromNatTrans_toArrowLift (α : L ⟶ R) :
    (fromNatTrans α).toArrowLift = ArrowLift.fromNatTrans α :=
  rfl

/-- Going from `α` to a lift of `Δ` and back gives `α`. -/
theorem toNatTrans_fromNatTrans (α : L ⟶ R) : toNatTrans (fromNatTrans α) = α := by
  rw [toNatTrans, fromNatTrans_toArrowLift, ArrowLift.toNatTrans_fromNatTrans]

/-- Going from a lift of `Δ` to `α` and back gives the lift. -/
theorem fromNatTrans_toNatTrans (F : NatTransFunctor L R) :
    fromNatTrans (toNatTrans F) = F := by
  apply Subtype.ext
  apply functor_eq_of_comp_eq _ (commaToArrowProj_injective L R)
  -- After `commaToArrow`, this is the arrow version's round trip.
  have hA : (fromNatTrans (toNatTrans F)).val ⋙ commaToArrow L R
      = F.val ⋙ commaToArrow L R := by
    have := ArrowLift.fromNatTrans_toNatTrans F.toArrowLift
    rw [← fromNatTrans_toArrowLift] at this
    exact congrArg Subtype.val this
  -- After `P`, both sides are `Δ`.
  have hP : (fromNatTrans (toNatTrans F)).val ⋙ commaProjProd L R
      = F.val ⋙ commaProjProd L R :=
    (fromNatTrans (toNatTrans F)).property.trans F.property.symm
  change ((_ ⋙ commaToArrow L R).prod' (_ ⋙ commaProjProd L R))
    = ((F.val ⋙ commaToArrow L R).prod' (F.val ⋙ commaProjProd L R))
  rw [hA, hP]

end NatTransFunctor

/-- Natural transformations `L ⟶ R` are in bijection with the functors
`S : 𝒞 ⥤ Comma L R` such that `S ⋙ P = Δ`. -/
def nat_trans_functor_bij {L R : 𝒞 ⥤ 𝒟} : (L ⟶ R) ≃ NatTransFunctor L R where
  toFun := NatTransFunctor.fromNatTrans
  invFun := NatTransFunctor.toNatTrans
  left_inv := NatTransFunctor.toNatTrans_fromNatTrans
  right_inv := NatTransFunctor.fromNatTrans_toNatTrans

end CommaVersion


end
