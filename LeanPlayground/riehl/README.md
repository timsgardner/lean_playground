# Riehl's Category Theory in Context

This directory is for working through Riehl's Category Theory in Context somewhat systematically, and to relate it to Mathlib's implementations of the same ideas.

For reference, the pdf of Category Theory in Context can be found under `assets/riehl_category_theory_in_context.pdf`. This is personal use so it's fine to read and refer to it.

## Page numbers

The PDF has 299 pages. The book's printed (Arabic) page numbers are offset from PDF page numbers:

> **PDF page = book page + 20**

(Chapter 1 begins on book page 1 = PDF page 21. Checked against the running heads at book pages 3, 24, 54, 82, 93, 132, 184, 222, 253, 263, 267, 269, 271.)

The front matter uses roman numerals, and there the PDF page equals the roman numeral's value (vii = PDF 7, ix = PDF 9, xvii = PDF 17). The Contents itself is on PDF pages 7-8.

To read a passage without loading the whole PDF, use the PDF page numbers below, e.g. `pdftotext -layout -f 102 -l 104 assets/riehl_category_theory_in_context.pdf -`. Note that a section can begin partway down its first page.

## Table of contents

Transcribed from the book's Contents. "Book" is the printed page; "PDF" is the page to jump to.

| Section | Book | PDF |
|---|---|---|
| Preface | ix | 9 |
| Sample corollaries | x | 10 |
| A tour of basic categorical notions | xi | 11 |
| Note to the reader | xv | 15 |
| Notational conventions | xvi | 16 |
| Changes in this edition | xvi | 16 |
| Acknowledgments | xvii | 17 |
| **Chapter 1. Categories, Functors, Natural Transformations** | 1 | 21 |
| 1.1 Abstract and concrete categories | 3 | 23 |
| 1.2 Duality | 9 | 29 |
| 1.3 Functoriality | 14 | 34 |
| 1.4 Naturality | 24 | 44 |
| 1.5 Equivalence of categories | 31 | 51 |
| 1.6 The art of the diagram chase | 39 | 59 |
| 1.7 The 2-category of categories | 47 | 67 |
| **Chapter 2. Universal Properties, Representability, and the Yoneda Lemma** | 53 | 73 |
| 2.1 Representable functors | 54 | 74 |
| 2.2 The Yoneda lemma | 59 | 79 |
| 2.3 Universal properties and universal elements | 67 | 87 |
| 2.4 The category of elements | 72 | 92 |
| **Chapter 3. Limits and Colimits** | 81 | 101 |
| 3.1 Limits and colimits as universal cones | 82 | 102 |
| 3.2 Limits in the category of sets | 93 | 113 |
| 3.3 Functoriality of limits and colimits | 98 | 118 |
| 3.4 Preservation, reflection, and creation of limits and colimits | 102 | 122 |
| 3.5 The representable nature of limits and colimits | 109 | 129 |
| 3.6 Complete and cocomplete categories | 115 | 135 |
| 3.7 Matters of size | 123 | 143 |
| 3.8 Interactions between limits and colimits | 125 | 145 |
| **Chapter 4. Adjunctions** | 131 | 151 |
| 4.1 Adjoint functors | 132 | 152 |
| 4.2 The unit and counit as universal arrows | 139 | 159 |
| 4.3 The calculus of adjunctions | 144 | 164 |
| 4.4 Contravariant and multivariable adjoint functors | 150 | 170 |
| 4.5 Adjunctions, limits, and colimits | 157 | 177 |
| 4.6 Locally cartesian closed categories | 165 | 185 |
| 4.7 Existence of adjoint functors | 174 | 194 |
| **Chapter 5. Monads and their Algebras** | 183 | 203 |
| 5.1 Monads from adjunctions | 184 | 204 |
| 5.2 Adjunctions from monads | 189 | 209 |
| 5.3 Monadic functors | 197 | 217 |
| 5.4 Canonical presentations via free algebras | 200 | 220 |
| 5.5 Recognizing categories of algebras | 204 | 224 |
| 5.6 Limits and colimits in categories of algebras | 211 | 231 |
| **Chapter 6. All Concepts are Kan Extensions** | 221 | 241 |
| 6.1 Kan extensions | 222 | 242 |
| 6.2 A formula for Kan extensions | 226 | 246 |
| 6.3 Pointwise Kan extensions | 234 | 254 |
| 6.4 Derived functors as Kan extensions | 238 | 258 |
| 6.5 All concepts | 243 | 263 |
| **Epilogue: Theorems in Category Theory** | 253 | 273 |
| E.1 Theorems in basic category theory | 253 | 273 |
| E.2 Coherence for symmetric monoidal categories | 255 | 275 |
| E.3 The universal property of the unit interval | 257 | 277 |
| E.4 A characterization of Grothendieck toposes | 258 | 278 |
| E.5 Embeddings of abelian categories | 259 | 279 |
| **Bibliography** | 263 | 283 |
| **Catalog of Categories** | 267 | 287 |
| **Glossary of Notation** | 269 | 289 |
| **Index** | 271 | 291 |
