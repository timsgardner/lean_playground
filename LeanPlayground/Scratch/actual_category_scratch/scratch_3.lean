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
  name: String
deriving DecidableEq

/-- Morphisms carry a name tag so parallel arrows are distinguishable. -/
@[ext]
structure Morphism where
  name: String
  dom: Object
  cod: Object
deriving DecidableEq

@[simp]
def composable (f g : Morphism) : Prop := f.cod = g.dom

/-- Arrow order: `comp f g` is f then g. Requires a proof of composability. -/
axiom comp (f g : Morphism) (h : composable f g) : Morphism
axiom comp_dom {f g : Morphism} (h : composable f g) : (comp f g h).dom = f.dom
axiom comp_cod {f g : Morphism} (h : composable f g) : (comp f g h).cod = g.cod

def Hom (A X : Object) : Set Morphism := { f | f.dom = A ∧ f.cod = X }

/-- Membership in `Hom A m.dom` supplies the composability proof (`.2`). -/
def mono (m : Morphism) : Prop :=
  ∀ (A: Object)
    (f g : Morphism)
    (hf : f ∈ (Hom A m.dom))
    (hg : g ∈ (Hom A m.dom)),
      (comp f m hf.2) = (comp g m hg.2) → f = g

theorem mono_comp_cancels
    (f g m : Morphism)
    (h_mono: mono m)
    (hf : f ∈ (Hom f.dom m.dom))
    (hg : g ∈ (Hom f.dom m.dom))
    (h_comp_eq : (comp f m hf.2) = (comp g m hg.2))
    : f = g :=
  h_mono f.dom f g hf hg h_comp_eq

structure Comps (dom cod: Object) where
  path: List Morphism
  h_path_composes: List.IsChain composable path
  h_nempty: path ≠ []
  h_dom_cod:
    (path.head h_nempty).dom = dom
    ∧ (path.getLast h_nempty).cod = cod

-- theorem path_cons_cod_dom
--   (path: List Morphism)
--   (h_path_composes: List.IsChain composable path)

def Comps.head (c: Comps dom cod) : Morphism :=
  c.path.head c.h_nempty

def Comps.tail (c: Comps dom cod) : Option (Comps (c.head.cod) cod) :=
  match h : c.path with
  | [] => absurd h c.h_nempty
  | [_] => none
  | m :: n :: rest => by
      have h_tail : n :: rest = c.path.tail := by
        rw [h]
        simp

      refine some {
        path := n :: rest
        h_path_composes := ?chain
        h_nempty := ?ne
        h_dom_cod := ?dc
      }

      case chain =>
        have h2 := (List.IsChain.tail c.h_path_composes)
        rw [← h_tail] at h2
        exact h2

      case ne =>
        simp

      case dc =>
        simp
        refine ⟨?_, ?_⟩
        · have hc : List.IsChain composable (m :: n :: rest) := by
            rw [← h]
            exact c.h_path_composes
          have h2 : n.dom = m.cod := by
            rw [List.isChain_cons_cons] at hc
            simp at hc
            exact hc.1.symm
          obtain ⟨_, _⟩ := c.h_dom_cod
          calc
            n.dom = m.cod := h2
            _ = c.head.cod := by
              unfold Comps.head
              have : (c.path.head c.h_nempty = m) := by simp [h]
              rw [this]
        · conv =>
            lhs
            congr
            congr
            rw [h_tail]
          simp [c.h_dom_cod]


def Comps.cons
    (m_head: Morphism)
    (c: Comps dom cod)
    (h: m_head.cod = dom)
    : (Comps m_head.dom cod) := by
  let path := m_head :: c.path
  refine {
    path := path,
    h_path_composes := ?chain
    h_nempty := ?ne
    h_dom_cod := ?dc
  }
  case chain =>
    rw [List.isChain_cons]
    constructor
    · intro m2 h2
      rw [Option.mem_def] at h2
      simp [List.head?_eq_some_head c.h_nempty] at h2
      simp
      rw [h]
      obtain ⟨h3, _⟩ := c.h_dom_cod
      rw [← h3, ← h2]
    · exact c.h_path_composes

  case ne =>
    simp

  case dc =>
    simp [path]
    rw [(List.getLast_cons c.h_nempty)]
    simp [c.h_dom_cod]






-- def Comps.compose {dom cod : Object} (c: Comps dom cod) : Morphism :=



/- slight yak-shave detour, a bit out of keeping with the
deliberately underengineered style of this file -/

/-- A finite multidigraph of morphisms; objects are implied by the edges. -/
structure MorphismGraph where
  edges: Finset Morphism

def MorphismGraph.homs (G : MorphismGraph) (A B : Object) : Finset Morphism :=
  G.edges.filter (fun f => f.dom = A ∧ f.cod = B)


/- An example graph. `f2` and `g2` are parallel arrows from B to C.

    A1 --f1--+                         +--i1--> E1
             |                         |
             v                         |
             B ==f2,g2==> C --m--> D --+
             ^                         |
             |                         |
    A2 --g1--+                         +--i2--> E2
-/
namespace Example

def A1 : Object := ⟨"A1"⟩
def A2 : Object := ⟨"A2"⟩
def B  : Object := ⟨"B"⟩
def C  : Object := ⟨"C"⟩
def D  : Object := ⟨"D"⟩
def E1 : Object := ⟨"E1"⟩
def E2 : Object := ⟨"E2"⟩

def f1 : Morphism := ⟨"f1", A1, B⟩
def g1 : Morphism := ⟨"g1", A2, B⟩
def m  : Morphism := ⟨"m", C, D⟩
def i1 : Morphism := ⟨"i1", D, E1⟩
def i2 : Morphism := ⟨"i2", D, E2⟩

/-- `f2` and `g2` are left abstract: all we know is that they are parallel
  arrows from B to C. -/
def G (f2 g2 : Morphism) : MorphismGraph := ⟨{f1, g1, f2, g2, m, i1, i2}⟩

example (f2 g2 : Morphism) : m ∈ (G f2 g2).homs C D := by
  simp [G, MorphismGraph.homs, m]

example
    (f2 g2 : Morphism)
    (hf2 : f2 ∈ Hom B C)
    (hg2 : g2 ∈ Hom B C)
    (h_mono : mono m)
    (h_eq : comp f2 m hf2.2 = comp g2 m hg2.2)
    : f2 = g2 :=
  h_mono B f2 g2 hf2 hg2 h_eq

example
  (f2 g2 : Morphism)
  (hfg : {f2, g2} ⊆ (Hom B C))
  (h_mono : mono m)
  (hfg_neq : f2 != g2)
  :=





end Example




end section
