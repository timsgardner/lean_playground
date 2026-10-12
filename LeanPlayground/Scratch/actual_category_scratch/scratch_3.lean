import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic.Check

section
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

/- Ramming monos and epis through my head -/

@[ext]
structure Object where
  payload: String

/-- Black-box morphisms: no constructor, no eta, no ext. -/
axiom Morphism : Type
axiom Morphism.dom : Morphism → Object
axiom Morphism.cod : Morphism → Object

def composable (f g : Morphism) : Prop := f.cod = g.dom

/-- Arrow order: `comp f g` is f then g. Total; only meaningful when composable. -/
axiom comp : Morphism → Morphism → Morphism
axiom comp_dom {f g : Morphism} (h : composable f g) : (comp f g).dom = f.dom
axiom comp_cod {f g : Morphism} (h : composable f g) : (comp f g).cod = g.cod

def mono (m : Morphism) : Prop :=
  ∀ f g : Morphism,
    composable f m → composable g m →
    f.dom = g.dom →
    comp f m = comp g m → f = g

theorem mono_comp_cancels
  (f g m : Morphism)
  (h_mono : mono m)
  (hf : composable f m)
  (hg : composable g m)
  (h_same_dom : f.dom = g.dom)
  : comp f m = comp g m → f = g :=
  h_mono f g hf hg h_same_dom


end section
