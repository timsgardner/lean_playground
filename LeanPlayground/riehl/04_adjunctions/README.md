# Chapter 4: Adjunctions

This directory follows Chapter 4 of Riehl's *Category Theory in Context*, which we are reading directly after §3.1 and so before the rest of Chapter 3. This README records what Chapter 4 actually draws from §§3.2–3.8, so that each piece of Chapter 3 can be read at the point where it is needed and not before.

The dependencies below come from the citations in the second edition (the PDF in `../assets/`). Section numbers in Chapter 3 differ from the first edition; see `../README.md` for the full table of contents. PDF page numbers are given so that a passage can be extracted with `pdftotext -layout -f <first> -l <last>`.

## Section by section

**§4.1 Adjoint functors (PDF 152).** The definition of an adjunction as a natural isomorphism of hom-sets uses the representability machinery of Chapter 2 and nothing from Chapter 3. Several examples mention products and coproducts, which §3.1 already covers.

**§4.2 The unit and counit as universal arrows (PDF 159).** The unit and counit are universal arrows in the sense of §2.3, so this section also depends only on Chapter 2.

**§4.3 The calculus of adjunctions (PDF 164).** The main text depends only on Chapter 2. Two exercises reach into Chapter 3: Exercise 4.3.iii suggests Exercise 3.2.v as a hint, and Exercise 4.3.vii builds on Exercise 3.6.v.

**§4.4 Contravariant and multivariable adjoint functors (PDF 170).** The main text again depends only on Chapter 2. Exercise 4.4.iv(ii) refers to the smash product from Exercise 3.6.iii.

**§4.5 Adjunctions, limits, and colimits (PDF 177).** This section is where Chapter 3 begins to matter, but less than one might expect.

- Proposition 4.5.1, which says that limits of shape J form a right adjoint to the constant diagram functor Δ, uses only the definition of a cone (Definition 3.1.2). It mentions the limit functor of Proposition 3.3.1 only for comparison.
- Theorem 4.5.2, which says that right adjoints preserve limits, is proved directly by transporting cones across the adjunction. It needs the notion of a functor preserving a limit (§3.4, PDF 122) but not the representable characterization of limits in §3.5.
- The discussion of exact functors (Proposition 4.5.8) uses the fact that finite limits can be built from finite products and equalizers (Theorems 3.5.5 and 3.5.11, PDF 129).
- Reflective subcategories (Proposition 4.5.14) use the notion of a functor creating limits (§3.4). Corollary 4.5.15, that Cat is complete and cocomplete, uses Proposition 3.4.9, which says that limits in a functor category are computed pointwise.
- Exercise 4.5.iii asks for the comparison map of Lemma 3.4.3.

**§4.6 Locally cartesian closed categories (PDF 185).** This section works with slice categories and pullbacks. It cites Theorem 3.5.17, that pullbacks and a terminal object suffice for all finite limits; Exercise 3.1.vi, the uniqueness of pullbacks up to a unique comparison isomorphism; and Exercise 3.6.iv, which presents quivers as presheaves.

**§4.7 Existence of adjoint functors (PDF 194).** This is the section that depends most heavily on the later parts of Chapter 3. Lemma 4.7.2 extends Proposition 3.4.8 (the forgetful functor from a slice category creates limits) and is a special case of Exercise 3.4.ii. The proofs of the adjoint functor theorems use Lemma 3.7.1, which identifies an initial object with a limit of the identity functor, together with the completeness results of §3.6. The closing material on locally presentable categories uses filtered categories (Definition 3.8.7).

## Suggested route

1. Read §§4.1–4.4 straight after §3.1. Nothing in their main text requires more of Chapter 3.
2. Before §4.5, read the definitions of preservation, reflection, and creation at the start of §3.4, together with Lemma 3.4.3 and Proposition 3.4.9. The material on exact functors additionally calls for Theorems 3.5.5 and 3.5.11, but it is a self-contained digression and can be skipped on a first pass.
3. Before §4.6, read Theorem 3.5.17 and Proposition 3.4.8.
4. Before §4.7, read §3.6 and Lemma 3.7.1. Definition 3.8.7 is needed only for the final part on locally presentable categories.

Nothing in Chapter 4 relies on §3.2 (limits in Set) or on the rest of §3.8 (interactions between limits and colimits) apart from the single exercise hint noted above. The rest of §3.5 is not needed either, although its representable description of limits, Hom(c, lim F) ≅ lim Hom(c, F), gives another way to see why Theorem 4.5.2 holds.

## Lean

Mathlib's `Adjunction` can be built either from a hom-set equivalence (`Adjunction.mkOfHomEquiv`) or from a unit and counit (`Adjunction.mkOfUnitCounit`), matching §4.1 and §4.2 respectively. Mathlib, like the second edition, proves that right adjoints preserve limits by transporting cones, so working with cones as in §3.1 is enough preparation for formalizing §4.5.
