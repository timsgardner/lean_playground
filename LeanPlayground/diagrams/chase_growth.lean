/-
# Growing a diagram, chase by chase

`extend` and `paste` prove that a diagram commutes on a larger
subshape. This file proves the same two growth steps for chases: if chases join
the parallel paths within the smaller subshapes, then chases join them within the
larger one, using the faces of the pieces together with any new faces the step
requires.

* `ChasesOn.paste`: chases on `S` from faces `F₁` and chases on `T` from faces `F₂`
  give chases on `S ⊔ T` from `F₁` and `F₂` together, under the hypotheses of
  `CommutesOn.paste`.
* `ChasesOn.sup_single`: chases on `S`, together with one new face for each of a
  covering family of obligations, give chases on `S ⊔ single e`.
* `ChasesOn.sup_single_minimal`: the same, with one face for each minimal
  obligation, in a finite shape with `S` acyclic.

Each proof works in the free model of the combined faces (`freeDiagram`), where it
applies the corresponding theorem about commutativity, then turns the result back
into chases by completeness (`chasesOn_iff_free`). So these theorems give the
existence of the chases; constructing them is the job of a chase search.
-/

import LeanPlayground.diagrams.chase
import LeanPlayground.diagrams.extend
import LeanPlayground.diagrams.paste

open CategoryTheory Quiver

namespace Diagrams

universe w w' v₁ u₁

variable {W : Type u₁} [Quiver.{v₁} W]

/-! ## Pasting -/

/-- **Pasting chases.** If chases from `faces₁` join the parallel paths within `S`,
and chases from `faces₂` join those within `T`, then chases from both join those
within `S ⊔ T`, provided `S ⊔ T` is acyclic and the shared vertices satisfy the
chain condition. -/
theorem ChasesOn.paste {Φ₁ : Type w} {Φ₂ : Type w'} {faces₁ : Φ₁ → Face W}
    {faces₂ : Φ₂ → Face W} {S T : Subshape W} (h₁ : ChasesOn faces₁ S) (h₂ : ChasesOn faces₂ T)
    (hchain : Chain S T) (hacyc : AcyclicOn (S ⊔ T)) :
    ChasesOn (Sum.elim faces₁ faces₂) (S ⊔ T) := by
  rw [chasesOn_iff_free]
  have hG := freeDiagram_holds (Sum.elim faces₁ faces₂)
  exact CommutesOn.paste (h₁.commutesOn fun φ => hG (.inl φ))
    (h₂.commutesOn fun φ => hG (.inr φ)) hchain hacyc

/-! ## Adding an arrow -/

variable {S : Subshape W} {u v : W} {e : u ⟶ v}

/-- **Adding an arrow, for chases.** Suppose chases from `faces` join the parallel
paths within `S`, there is no path `v ⇝ u` within `S`, and every obligation lies
above one of the obligations `obl ψ`, located at `pts ψ`. Then chases from `faces`
together with the faces of the `obl ψ` join the parallel paths within
`S ⊔ single e`. -/
theorem ChasesOn.sup_single {Φ : Type w} {faces : Φ → Face W} {Ψ : Type w'}
    (hS : ChasesOn faces S) (huv : ¬ ReachIn S v u) (pts : Ψ → W × W)
    (obl : ∀ ψ, Obligation S e (pts ψ).1 (pts ψ).2)
    (hcov : ∀ x y, IsObligation S u v x y →
      ∃ ψ, ReachIn S x (pts ψ).1 ∧ ReachIn S (pts ψ).2 y) :
    ChasesOn (Sum.elim faces fun ψ => (obl ψ).face) (S ⊔ single e) := by
  rw [chasesOn_iff_free]
  have hG := freeDiagram_holds (Sum.elim faces fun ψ => (obl ψ).face)
  refine CommutesOn.sup_single_of_cover (hS.commutesOn fun φ => hG (.inl φ)) huv
    fun x y hxy => ?_
  obtain ⟨ψ, hx, hy⟩ := hcov x y hxy
  exact ⟨_, _, hx, hy, obl ψ, (obl ψ).holds_iff_face.2 (hG (.inr ψ))⟩

variable (S u v) in
/-- The minimal obligations for a new arrow `u ⟶ v`, as pairs of vertices. -/
def MinObligations : Type u₁ := {p : W × W // IsMinObligation S u v p.1 p.2}

/-- Witness paths for a minimal obligation, chosen once and for all. -/
noncomputable def MinObligations.obligation (o : MinObligations S u v) (e : u ⟶ v) :
    Obligation S e o.1.1 o.1.2 :=
  let ho := o.2.1
  ⟨ho.1.choose, ho.2.1.choose, ho.2.2.choose,
    ho.1.choose_spec, ho.2.1.choose_spec, ho.2.2.choose_spec⟩

/-- **Adding an arrow, with one face per minimal obligation.** In a finite shape,
with `S` acyclic and no path `v ⇝ u` within `S`, chases on `S` together with one
face for each minimal obligation give chases on `S ⊔ single e`. -/
theorem ChasesOn.sup_single_minimal [Finite W] {Φ : Type w} {faces : Φ → Face W}
    (hS : ChasesOn faces S) (hacyc : AcyclicOn S) (huv : ¬ ReachIn S v u) :
    ChasesOn (Sum.elim faces fun o : MinObligations S u v => (o.obligation e).face)
      (S ⊔ single e) :=
  hS.sup_single huv (fun o : MinObligations S u v => o.1) (fun o => o.obligation e)
    fun _ _ hxy =>
    let ⟨x', y', hx, hy, hmin⟩ := exists_isMinObligation_below hacyc hxy
    ⟨⟨(x', y'), hmin⟩, hx, hy⟩

end Diagrams
