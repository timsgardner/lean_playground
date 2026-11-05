import Mathlib.CategoryTheory.Adjunction.Basic

/-
Notation for transposes. `f ♭[adj]` is `adj.homEquiv _ _ f` and `g ♯[adj]` is
`(adj.homEquiv _ _).symm g`. The notation expands to exactly those terms, so the
Mathlib lemmas about `homEquiv` still apply with `rw` and `simp`, and the
delaborator below prints such terms back in this form in goals.
-/
section TransposeNotation
open Lean PrettyPrinter Delaborator SubExpr

notation:max f "♭[" adj "]" =>
  DFunLike.coe (CategoryTheory.Adjunction.homEquiv adj _ _) f
notation:max g "♯[" adj "]" =>
  DFunLike.coe (Equiv.symm (CategoryTheory.Adjunction.homEquiv adj _ _)) g

@[app_delab DFunLike.coe]
meta def delabAdjTranspose : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  let fn := e.appFn!.appArg!
  if fn.isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 6 delab
    let f ← withAppArg delab
    `($f ♭[$adj])
  else if fn.isAppOfArity ``Equiv.symm 3 &&
      (fn.getArg! 2).isAppOfArity ``CategoryTheory.Adjunction.homEquiv 9 then
    let adj ← withAppFn <| withAppArg <| withNaryArg 2 <| withNaryArg 6 delab
    let g ← withAppArg delab
    `($g ♯[$adj])
  else failure

end TransposeNotation

/-
Components of the unit and counit.

For `adj : F ⊣ G`, the field `adj.unit` is a natural transformation `𝟭 𝒞 ⟶ F ⋙ G`, and the
field `adj.counit` is a natural transformation `G ⋙ F ⟶ 𝟭 𝒟`. Riehl writes `η` and `ε` for
these transformations.

The component `adj.unit.app c` has the type `(𝟭 𝒞).obj c ⟶ (F ⋙ G).obj c`. That type is
definitionally equal to `c ⟶ G.obj (F.obj c)`, but it is a different expression, and the
difference has a practical consequence. The composition `≫` and the functor application
`F.map` carry the domain and codomain of their arguments as hidden implicit arguments, and
Lean fills those arguments in from the type of the morphism it is given. When a statement
mentions `F.map (adj.unit.app c)`, the hidden domain is the expression `(𝟭 𝒞).obj c`.
Mathlib's lemmas about adjunctions are stated with the hidden domain `c`. The two terms are
printed identically in the infoview, and `exact` accepts one for the other, but `rw` compares
them syntactically and reports that it cannot find the pattern.

The left triangle identity gives an example. Consider the following goal.

    F.map (adj.unit.app c) ≫ adj.counit.app (F.obj c) = 𝟙 (F.obj c)

The term `adj.left_triangle_components c` proves this goal with `exact`, because `exact` checks
definitional equality and unfolds `(𝟭 𝒞).obj c` to `c`. The tactic
`rw [adj.left_triangle_components]` fails on the same goal, and its error message displays a
pattern and a target that look identical.

    Did not find an occurrence of the pattern
      F.map (adj.unit.app ?X) ≫ adj.counit.app (F.obj ?X)
    in the target expression
      F.map (adj.unit.app c) ≫ adj.counit.app (F.obj c) = 𝟙 (F.obj c)

The option `set_option pp.explicit true` reveals the difference. With the instance arguments
omitted, the term in the goal and the term with the clean type are as follows.

    @Functor.map … F ((𝟭 𝒞).obj c) ((F ⋙ G).obj c) (adj.unit.app c)
    @Functor.map … F c (G.obj (F.obj c)) (adj.η c)

The two definitions below remove the problem at its source. The term `adj.η c` is the component
of the unit at `c`, and its stated type is exactly `c ⟶ G.obj (F.obj c)`, so `F.map (adj.η c)`
has the clean hidden arguments. The term `adj.ε d` is the component of the counit at `d`. The
keyword `abbrev` declares a definition that Lean unfolds freely, so that `adj.η c` and
`adj.unit.app c` are interchangeable for `exact`, and Mathlib's lemmas can rewrite a term that
is stated with `adj.η`. With `adj.η` in place of `adj.unit.app`, the rewrite above succeeds.
A goal that already has the unclean form can be repaired in place with `change`, by restating
the goal with `adj.η` and `adj.ε`.

One asymmetry remains. The tactic `rw` locates a pattern by its head symbol, so a rewrite whose
left-hand side is literally `adj.η c` will not find an occurrence of `adj.unit.app c`. The lemmas
`flat_eq` and `sharp_eq` below are therefore versions of Mathlib's `Adjunction.homEquiv_unit` and
`Adjunction.homEquiv_counit` whose right-hand sides are written with `adj.η` and `adj.ε`, so that
a goal stays in one form after they are applied. Because the lemmas live in the namespace
`CategoryTheory.Adjunction`, they can be called with dot notation, as `adj.flat_eq f` and
`adj.sharp_eq g`.
-/
section UnitCounitComponents

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [CategoryTheory.Category.{v₁} 𝒞]
variable {𝒟 : Type u₂} [CategoryTheory.Category.{v₂} 𝒟]

namespace CategoryTheory.Adjunction

/-- Riehl's `η_c`, the component of the unit at `c`. -/
abbrev η {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) (c : 𝒞) : c ⟶ G.obj (F.obj c) :=
  adj.unit.app c

/-- Riehl's `ε_d`, the component of the counit at `d`. -/
abbrev ε {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) (d : 𝒟) : F.obj (G.obj d) ⟶ d :=
  adj.counit.app d

/-- Formula (4.2.8): the transpose of `f : F c ⟶ d` is `η_c` followed by `G f`. -/
theorem flat_eq {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c : 𝒞} {d : 𝒟} (f : F.obj c ⟶ d) :
    f ♭[adj] = adj.η c ≫ G.map f :=
  adj.homEquiv_unit c d f

/-- Formula (4.2.9): the transpose of `g : c ⟶ G d` is `F g` followed by `ε_d`. -/
theorem sharp_eq {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {c : 𝒞} {d : 𝒟} (g : c ⟶ G.obj d) :
    g ♯[adj] = F.map g ≫ adj.ε d :=
  adj.homEquiv_counit c d g

end CategoryTheory.Adjunction

end UnitCounitComponents
