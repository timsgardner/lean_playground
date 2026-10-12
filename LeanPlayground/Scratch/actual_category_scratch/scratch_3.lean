import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic.Check

section
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.coercions false

/- Ramming monos and epis through my head -/
/- Start with a very naive hand-rolled toy category theory -/

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

def Hom (A X : Object) : Set Morphism := { f | f.dom = A ∧ f.cod = X }

/-- Elegant, but too fancy for this file as more than a sidenote. We're trying
  to avoid thought. -/
def mono' (m: Morphism) : Prop :=
  ∀ Z : Object, Set.InjOn (fun f => comp f m) (Hom Z m.dom)

def mono (m : Morphism) : Prop :=
  ∀ (A: Object)
    (f g : Morphism),
      (f ∈ (Hom A m.dom) ∧ g ∈ (Hom A m.dom)) →
        (comp f m) = (comp g m) → f = g

theorem mono_comp_cancels
    (f g m : Morphism)
    (h_mono: mono m)
    (h_sig: {f, g} ⊆ (Hom f.dom m.dom))
    (h_comp_eq :(comp f m) = (comp g m))
    : f = g := by
  apply (h_mono f.dom)
  constructor
  · apply h_sig
    simp
  · apply h_sig
    simp
  exact h_comp_eq




end section
