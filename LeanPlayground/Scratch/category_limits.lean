/-
  Limits in Mathlib — exercise set
  --------------------------------
  Progression: cones → terminal objects → uniqueness of limits →
  binary products → equalizers → pullbacks → (bonus) limits in Type.

  Replace each `sorry`. Hints follow each exercise; the final comment of
  each exercise names the bundled Mathlib result to diff against when done.

  API STATUS — checked against the current Mathlib documentation and
  source on 2026-07-11. All names below are current unless explicitly
  marked deprecated. `pullback.fst` and `pullback.snd` take their two
  morphisms explicitly: `pullback.fst f g` and `pullback.snd f g`.
-/
import Mathlib

open CategoryTheory CategoryTheory.Limits

universe v u

namespace LimitsExercises

variable {C : Type u} [Category.{v} C]

/-! ### Exercise 1 — cones are natural transformations

The commuting-triangle condition on a cone's legs is not a separate axiom:
it falls out of naturality of `c.π`, because the source of `c.π` is a
*constant* functor. Recover it by hand.
-/


example {C : Type*} [Category C]
    {X Y : C} (f : X ⟶ Y) :
    f ≫ 𝟙 Y = f := by
  exact Category.comp_id f


theorem cone_w {J : Type*} [Category J] {F : J ⥤ C} (c : Cone F)
    {j j' : J} (f : j ⟶ j') :
    c.π.app j ≫ F.map f = c.π.app j' := by
  let cone_const_func := ((Functor.const J).obj c.pt)
  have to_id : cone_const_func.map f = 𝟙 c.pt := by
    exact Functor.const_obj_map J c.pt f
  have hnat : c.π.app j ≫ F.map f = cone_const_func.map f ≫ c.π.app j' := by
      · exact (c.π.naturality f).symm
  conv_lhs => rw[hnat]
  conv_lhs => rw[to_id]
  exact Category.id_comp (c.π.app j')


/- Hints:
   • Start from `c.π.naturality f`  [✓]
   • `(Functor.const J).obj c.pt` maps every morphism to an identity;
     the relevant simp lemma is `Functor.const_obj_map`  [✓]
   • Finish with `Category.id_comp`  [✓]
   Compare against: `CategoryTheory.Limits.Cone.w`  [✓] -/


/-! ### Exercise 2 — terminal objects are unique up to iso

`IsTerminal X` is literally `IsLimit` of the empty cone on `X`, but the
derived API is friendlier. Build the iso by hand.
-/

def isTerminalIso {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) :
    X ≅ Y where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/- Hints:
   • `IsTerminal.from : IsTerminal X → (Y : C) → (Y ⟶ X)`  [✓]
     (so `hY.from X : X ⟶ Y`)
   • Any two morphisms into a terminal object agree:
     `IsTerminal.hom_ext`  [✓]
   Compare against: `IsTerminal.uniqueUpToIso`  [✓] -/




/-! ### Exercise 3 — any two limit cones have isomorphic points

The same argument as Exercise 2, one level up: run the universal property
in both directions, then use uniqueness to collapse the round trips.
-/

def limitConeIso {J : Type*} [Category J] {F : J ⥤ C} {s t : Cone F}
    (hs : IsLimit s) (ht : IsLimit t) : s.pt ≅ t.pt where
  hom := ht.lift s
  inv := hs.lift t
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/- Hints:
   • `IsLimit.hom_ext hs : (∀ j, f ≫ s.π.app j = g ≫ s.π.app j) → f = g`  [✓]
     Apply it with g := 𝟙 s.pt; `Category.id_comp` handles the right side.
   • The factorization lemma is `IsLimit.fac`  [✓]:
     `hs.fac t j : hs.lift t ≫ s.π.app j = t.π.app j`.
     Reassociate with `Category.assoc`, then apply `fac` twice.
   Compare against: `IsLimit.conePointUniqueUpToIso`  [✓] -/


/-! ### Exercise 4 — braiding for binary products -/

section Products
variable [HasBinaryProducts C]

def prodBraiding (X Y : C) : X ⨯ Y ≅ Y ⨯ X where
  hom := prod.lift prod.snd prod.fst
  inv := sorry
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/- Hints:
   • `prod.hom_ext : f ≫ prod.fst = g ≫ prod.fst →
                     f ≫ prod.snd = g ≫ prod.snd → f = g`  [✓]
   • simp set: `prod.lift_fst`, `prod.lift_snd`, `Category.assoc`  [✓]
     A plain `simp` after `apply prod.hom_ext` will likely close both goals;
     for a more explicit route, `ext` also fires the hom_ext lemma.  [✓]
   Compare against: `prod.braiding`  [✓] -/


/-! ### Exercise 5 — the terminal object is a unit for the product -/

variable [HasTerminal C]

def prodTerminalIso (X : C) : X ⨯ ⊤_ C ≅ X where
  hom := prod.fst
  inv := prod.lift (𝟙 X) (terminal.from X)
  hom_inv_id := by
    sorry
  inv_hom_id := by
    sorry

/- Hints:
   • One direction is a `prod.hom_ext` computation as in Exercise 4.
   • For the second leg you need that any two maps to `⊤_ C` agree:
     `terminal.hom_ext`  [✓]. There is also a
     `Subsingleton (X ⟶ ⊤_ C)` instance, and `terminal.comp_from`  [✓]
     is a simp lemma collapsing `f ≫ terminal.from _`.
   Compare against: `prod.rightUnitor`  [✓] -/

end Products


/-! ### Exercise 6 — the equalizer of `f` with itself is trivial

If both parallel arrows coincide, `𝟙 X` already equalizes them, so the
equalizer inclusion must be invertible.
-/

section Equalizers
variable {X Y : C} (f : X ⟶ Y) [HasEqualizer f f]

theorem isIso_equalizer_ι_self : IsIso (equalizer.ι f f) := by
  sorry

/- Hints:
   • Candidate inverse: `equalizer.lift (𝟙 X) rfl`  [✓]
     (`equalizer.lift k h : W ⟶ equalizer f g` given `h : k ≫ f = k ≫ g`)
   • `IsIso` is a Prop-class wrapping an existential; provide
     `⟨⟨inverse, proof₁, proof₂⟩⟩` or use `IsIso.mk`.  [✓]
   • One triangle is `equalizer.lift_ι`  [✓]; the other needs
     `equalizer.hom_ext`  [✓] — morphisms into an equalizer are determined
     by their composite with `ι`.
   Compare against: the instance `equalizer.ι_of_self`  [✓] -/

end Equalizers


/-! ### Exercise 7 — pullbacks preserve monos

The classical stability result: pulling back a mono along anything yields
a mono. This is the exercise that actually exercises `pullback.condition`.
-/

section Pullbacks
variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

theorem mono_pullback_fst [Mono g] : Mono (pullback.fst f g) := by
  constructor
  intro W u v h
  apply pullback.hom_ext
  · exact h
  · sorry

/- Hints:
   • Goal: `u ≫ pullback.snd f g = v ≫ pullback.snd f g`.
     Postcompose with `g` and cancel: `rw [← cancel_mono g]`  [✓]
   • `pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g`  [✓]
     rewrite backwards through it (mind `Category.assoc`), then use the
     reassociated hypothesis. The current Mathlib proof uses:
       `rw [← cancel_mono g, Category.assoc, Category.assoc,
            ← pullback.condition]`
       `apply reassoc_of% h`  [✓]
   Compare against: the instance `pullback.fst_of_mono`  [✓] -/

end Pullbacks


/-! ### Exercise 8 (bonus) — a concrete limit in `Type`

Everything above was formal; ground it once. Show `PUnit` is terminal in
`Type u` by exhibiting the universal property directly.
-/

def punitIsTerminal : IsTerminal (PUnit.{u + 1} : Type u) := by
  sorry

/- Hints:
   • `IsTerminal.ofUniqueHom`  [✓] wants a chosen map `∀ Y, Y ⟶ PUnit`
     and a proof it's the only one; in `Type`, morphisms are bare
     functions, so `funext` + `Subsingleton.elim` (or matching on
     `PUnit.unit`) finishes it.
   • Alternatively `IsTerminal.ofUnique`  [✓] if a `Unique (Y ⟶ PUnit)`
     instance is easier to hand over.
   Compare against: `CategoryTheory.Limits.Types.isTerminalPUnit`  [✓]
     (`isTerminalPunit` is retained only as a deprecated alias.) -/

end LimitsExercises
