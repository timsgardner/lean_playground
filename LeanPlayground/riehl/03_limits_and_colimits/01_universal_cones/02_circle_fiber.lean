/-
# Riehl, *Category Theory in Context*, Example 3.1.18: the fiber of `ℝ → S¹`

A worked example, split out of `01_universal_cones.lean` because it is the only
part of §3.1 that needs topology, and the topology imports slow that file
down. It is the topological counterpart of Exercise 3 there (the fiber of a
function as a pullback in `Type`), and is otherwise independent of it.
-/
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Int
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

open CategoryTheory Limits

/-
Worked example (Example 3.1.18, solved). Riehl's example in the category of
spaces: the fiber of `ρ : ℝ → S¹`, `t ↦ e^{2πit}`, over the point `1` is the
discrete subspace `ℤ ⊂ ℝ`. This is Exercise 3 again, now in `TopCat`, where
the objects are topological spaces and the morphisms are continuous maps.

What the statement means, informally. Picture `ρ` as wrapping the real line
around a circle of circumference `1`, like thread around a spool: `t` and
`t + 1` land on the same point, and `t` is sent to the point a fraction `t` of
the way around (the "angle measured in turns"). The fiber over the starting
point consists of the reals that land there, which are exactly the integers.
As a set, this is just Exercise 3. The new content is that the fiber, as a
space, is `ℤ` with the discrete topology: each integer is isolated from the
others, with no other points of the fiber nearby, exactly as `ℤ` sits inside
`ℝ`.

The universal property makes this precise without any topology vocabulary. A
cone over the cospan amounts to a space `X` and a continuous map
`k : X → ℝ` whose values all land on the starting point, that is, a continuous
map into `ℝ` taking only integer values. The theorem says that such a map is
the same thing as a continuous map `X → ℤ`. The content is that the
continuity is not lost: a continuous real-valued function that only takes
integer values cannot jump from one integer to another, so it is locally
constant, and a locally constant function into `ℤ` is continuous for the
discrete topology. For instance, if `X` is an interval, `k` must be constant.
The discrete topology is also the only one the fiber could carry. For the
inclusion of the fiber into `ℝ` to be continuous, the preimage of the open
interval `(n - 1/2, n + 1/2)` must be open, and that preimage is the single
point `{n}`. So every point of the fiber is open, which is what discrete means.

Mathlib's `AddCircle (1 : ℝ)` is the quotient `ℝ/ℤ`, and the quotient map
`t ↦ (t : AddCircle 1)` is Riehl's `ρ` up to the homeomorphism `ℝ/ℤ ≅ S¹`,
`[t] ↦ e^{2πit}`, which sends the class `0` to the point `1`. With that
translation, the square to prove a pullback in `TopCat` is

  ℤ ──Int.cast──> ℝ
  │               │
  !               ρ
  ↓               ↓
  * ──── 0 ────> ℝ/ℤ

where `!` is the unique map to the one-point space `PUnit`.

The proof follows Exercise 3. Two facts carry the weight.

* `circleFiber_spec`: for a cone `s`, every point `x` of its summit is sent by
  `s.fst` to an integer. The commutativity of `s`, evaluated at `x`, says that
  `ρ (s.fst x) = 0` in `ℝ/ℤ`, and `AddCircle.coe_eq_zero_iff` translates this
  into `∃ n : ℤ, n • 1 = s.fst x`. The lift sends `x` to that integer, chosen
  with `Exists.choose` (so the definition is `noncomputable`; the integer is
  in fact unique, but nothing here needs that).
* Continuity of the lift. This is the only genuinely topological step, and it
  is what "`ℤ` is a subspace of `ℝ`" means: `Int.cast : ℤ → ℝ` is an embedding
  (`Int.isClosedEmbedding_coe_real`), and a map into the domain of an embedding
  is continuous if and only if its composite with the embedding is
  (`IsEmbedding.continuous_iff`). The composite here is `s.fst`, which is
  continuous because `s` is a cone in `TopCat`.

The two factorizations and uniqueness are then as in Exercise 3. The
factorization through `PUnit` holds by `ext` alone, since any two maps into a
one-point space agree. Uniqueness uses injectivity of `Int.cast` to reduce an
equation of integers to an equation of reals, which the factorization
hypothesis for `m` supplies.
-/
section CircleFiber

/-- Riehl's `ρ`, with the circle modeled as `ℝ/ℤ`. -/
def circleρ : TopCat.of ℝ ⟶ TopCat.of (AddCircle (1 : ℝ)) :=
  TopCat.ofHom ⟨fun t => (t : AddCircle (1 : ℝ)), continuous_quotient_mk'⟩

/-- The point `1 ∈ S¹`, which is the class `0` in `ℝ/ℤ`. -/
def circleBase : TopCat.of PUnit.{1} ⟶ TopCat.of (AddCircle (1 : ℝ)) :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

/-- The inclusion `ℤ ⊂ ℝ`. It is continuous because `ℤ` is discrete. -/
def intToReal : TopCat.of ℤ ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨Int.cast, continuous_of_discreteTopology⟩

def intToPoint : TopCat.of ℤ ⟶ TopCat.of PUnit.{1} :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The square commutes: every integer maps to `0` in `ℝ/ℤ`. -/
theorem circleFiber_w : intToReal ≫ circleρ = intToPoint ≫ circleBase := by
  ext n
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by rw [zsmul_one]; rfl⟩

/-- The leg of any cone over the cospan takes integer values. -/
theorem circleFiber_spec (s : PullbackCone circleρ circleBase) (x : s.pt) :
    ∃ n : ℤ, (n : ℝ) = s.fst x := by
  have h := ConcreteCategory.congr_hom s.condition x
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
  rw [zsmul_one] at hn
  exact ⟨n, hn⟩

noncomputable def circleFiberIsLimit :
    IsLimit (PullbackCone.mk intToReal intToPoint circleFiber_w) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => TopCat.ofHom ⟨fun x => (circleFiber_spec s x).choose, ?_⟩) ?_ ?_ ?_
  -- continuity of the lift: its composite with the embedding `ℤ ⊂ ℝ` is `s.fst`
  · exact (Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff).2
      (s.fst.hom.continuous.congr fun x => (circleFiber_spec s x).choose_spec.symm)
  -- fac_left: the chosen integer is the value of `s.fst`
  · intro s
    ext x
    exact (circleFiber_spec s x).choose_spec
  -- fac_right: maps into `PUnit` agree
  · intro s
    ext x
  -- uniq: compare in `ℝ`, where `m` and the lift both agree with `s.fst`
  · intro s m h₁ _
    ext x
    apply Int.cast_injective (α := ℝ)
    exact (ConcreteCategory.congr_hom h₁ x).trans (circleFiber_spec s x).choose_spec.symm

/-- The same fact in the form preferred by Mathlib. -/
theorem circleFiber_isPullback : IsPullback intToReal intToPoint circleρ circleBase :=
  IsPullback.of_isLimit circleFiberIsLimit

end CircleFiber
