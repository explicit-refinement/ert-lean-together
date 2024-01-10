#import "@preview/polylux:0.3.1": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;
#let app = $med$;
#let llet = $sans("let")$;
#let case = $sans("case")$;

#title-slide[
  = Explicit Refinement Types
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami

  University of Cambridge
  
  January 11

  Lean Together 2024 -- Online
]

#focus-slide[
    = What is a type theory?
]

#slide[
    = Simply-Typed Lambda Calculus
    ...
]

#slide[
    = Weakening
    ...
]

#slide[
    = Substitution
    ...
]

#focus-slide[
    = What is a (denotational) semantics?
]

#slide[
    ...
]

#slide[
    = Semantic Weakening
    ...
]

#slide[
    = Semantic Substitution
    ...
]

#focus-slide[
    = How would we represent this in Lean?
]

#slide[
    = Intrinsic Style
    ...
]

#slide[
    = Extrinsic Style
    ...
]

#slide[
    = de-Bruijn Indices
    ...
]

#slide[
    = Coherence
    ...
]

#focus-slide[
    = What is a refinement type?
]

#slide[
    ...
]

#slide[
    = Weakening
    ...
]

#slide[
    = Substitution
    ...
]

#focus-slide[
    = Semantics of refinement types
]

#slide[
    = Erasure
    ...
]

#slide[
    = Semantic Regularity
    ...
]

#focus-slide[
    = Representing Refinement Types in Lean
]

#slide[
    = Coherence
    ...
]

#slide[
    = Doing Big Inductions
    ...
]

#focus-slide[
    = Experience Report
]

#slide[
    = _Explicit Refinement Types_
    ...
]

#slide[
    = _Adding Nothing to HOL_
    ...
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]

#bibliography("references.bib")