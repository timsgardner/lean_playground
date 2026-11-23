# Controlled test: transport versus setup

The question: `comma_transport.lean` proves the hard round trip
`fromNatTrans (toNatTrans F) = F` without any `eqToHom` work, by transporting once along a
family of equations (`copy`) and coming back once (`copy_eq`). But it also changed the
setup: `Lift` became an `abbrev`, and `backward.defeqAttrib.useBackward` was turned on. Is
the improvement due to the transport approach, or to the setup?

## The grid

Four self-contained files, generated from one template, so that they share all their text
except the setup lines and the proof of the hard round trip. Each approach uses the same
proof text under both setups.

| | **plain** setup: `def Lift`, option off | **tuned** setup: `abbrev Lift`, option on |
|---|---|---|
| **direct**: `Functor.ext`, `eqToHom`s pushed through `Comma.eqToHom_left`/`_right` with `erw` | `direct_plain.lean` | `direct_tuned.lean` |
| **transport**: `copy` along `F c = ⟨c, c, component F c⟩`, compare on morphisms, `copy_eq` | `transport_plain.lean` | `transport_tuned.lean` |

**Result: all four compile, with no errors or warnings.** Each approach's proof works
unchanged in both setups, so the setup is not what made the transport proof possible. The
difference between the approaches is in the proof itself: the direct proof needs
`Functor.ext`, a special lemma for comma objects, and `erw` on `eqToHom`s; the transport
proof needs none of these, at the price of depending on `copy` and `copy_eq` from
`induced_eq.lean`.

## Probes of the setup

The files in `probes/` vary one thing against the grid, to find where the setup does
matter. Files that fail are part of the result. (They are not built by `lake build`, whose
default target imports only `LeanPlayground.Basic`.)

| Probe | What it changes | plain | tuned |
|---|---|---|---|
| A | naturality ends with `simp only [..., (F.val.map m).w]` instead of `simp only [...]; exact congrArg _ (F.val.map m).w` | fails | fails |
| B | the direct proof uses `rw` instead of `erw` for `Comma.eqToHom_left`/`_right` | fails | fails |
| C | the naive `InducedEq` proof of `bottom (obj_left_eq F) ((legsL F).map m) = m`: unfold, normalize endpoints with `dsimp`, then `simp [h]` | fails | works |
| D | the direct proof without Mathlib's `Comma.eqToHom_left`/`_right`: each leg is restated as the image under `Comma.fst`/`Comma.snd` (`← Comma.fst_map`), and the `eqToHom`s are pushed through with `Functor.map_comp` and the general `eqToHom_map` | works | not run |

Probe D answers a fairness question: does the direct approach depend on comma-specific
tools for `eqToHom`, which other categories might not have? It does not. With the general
`eqToHom_map` in place of `Comma.eqToHom_left`, the proof has the same length and still
needs `erw`. What both approaches need from the context is a projection functor for each
component of a morphism, its `@[simps]` `map` lemma, and an extensionality lemma for
morphisms (`Comma.hom_ext`), which any category whose morphisms are tuples of components
has.

For probe C the two setup factors were also separated:

| Probe C | `def Lift` | `abbrev Lift` |
|---|---|---|
| option off | fails (`probeC_plain`) | fails (`probeC_abbrevOnly`) |
| option on | works (`probeC_optionOnly`) | works (`probeC_tuned`) |

So the option is the factor that matters, and only for proofs that rely on `dsimp`
normalizing objects written through functors defined with `@[simps]` (here
`(legsL F).obj c`). Making `Lift` an `abbrev` made no difference anywhere in this test.

## Conclusions

* The improvement in the hard round trip comes from the transport approach, not from the
  setup.
* The option `backward.defeqAttrib.useBackward` matters when a proof normalizes objects
  with `dsimp` through `@[simps]` lemmas. That is the situation the induced-category API
  creates (objects like `(legsL F).obj c`), so files using it should turn the option on.
* `abbrev Lift` was not needed anywhere.

The generator script is not kept in the repository; the four grid files are its output and
can be edited directly.
