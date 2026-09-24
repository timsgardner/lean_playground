/-
# Limits Kindergarten

An exploration space for cones, limits, colimits, and familiar examples in
`Type`. The sections below start with the general API, then move toward
standard shapes such as terminal objects, products, equalizers, and
pullbacks.
-/

import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace LimitsKindergarten

/-! ## Cones and cocones

A cone over `F : J ⥤ C` has a point and a compatible family of maps from that
point to the objects of `F`. A cocone reverses the direction of those maps.
The compatibility equations are bundled as naturality.
-/

section Cones

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]
variable (F : J ⥤ C)

#check Cone F
#check Cocone F
#check Cone.pt
#check Cone.π
#check Cone.w
#check Cocone.ι
#check Cocone.w

end Cones

/-! ## The universal properties

`IsLimit c` says that every other cone has a unique map to `c` commuting with
the legs. `IsColimit` is the dual statement for cocones.
-/

section UniversalProperties

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]
variable {F : J ⥤ C}
variable (c : Cone F) (cc : Cocone F)

#check IsLimit c
#check IsColimit cc
#check IsLimit.lift
#check IsLimit.fac
#check IsLimit.hom_ext
#check IsColimit.desc
#check IsColimit.fac
#check IsColimit.hom_ext

end UniversalProperties

/-! ## Chosen limits and colimits

When a diagram is known to have a limit or colimit, typeclass inference gives
access to a chosen cone or cocone and its universal property.
-/

section ChosenLimits

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]
variable (F : J ⥤ C) [HasLimit F] [HasColimit F]
variable (j : J)

#check limit F
#check limit.π F j
#check limit.isLimit F
#check colimit F
#check colimit.ι F j
#check colimit.isColimit F

end ChosenLimits

/-! ## Familiar shapes

Terminal objects, binary products, equalizers, and pullbacks are limits of
small indexing diagrams. We'll unpack that relationship as we work through
examples.
-/

section FamiliarShapes

variable {C : Type u'} [Category.{v'} C]

#check IsTerminal
#check HasTerminal
#check HasBinaryProducts
#check HasEqualizer
#check HasPullback

end FamiliarShapes

/-! ## First stop: `Type`

The category of types is a useful place to make limits concrete: its morphisms
are functions, and many universal constructions can be described by ordinary
products, subtypes, or quotients.
-/

section TypeCategory

variable {J : Type u} [Category.{v} J]
variable (F : J ⥤ Type u')

#check F.obj
#check F.map

-- TODO: describe the limit of a diagram of types as compatible families.
-- TODO: compare the categorical coproduct with a disjoint sum of types.

end TypeCategory

end LimitsKindergarten
