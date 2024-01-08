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
    = $ert$ in a nutshell
]

#slide[
    = Defining $stlc$

    #v(2em)

    #grid(
        columns: 4,
        gutter: 0.5em,
        $s, t ::=$, $x $, $| λ x: A. t$, $| s app t$,
        $$, $$, $| (s, t)$, $|  llet (x, y) = s; t$,
        $$, $$, $| ι_i med t$, 
                $| case t med (ι_0 x => l) med (ι_1 y => r)$,
        $$, $$, $| 0$, $| sans("succ") med t$,
        $$, $$, $$, $| sans("natrec") med n med z med (sans("succ") med x, y => s)$,
    )

    #v(1em)

    #grid(
        columns: 4,
        gutter: 0.5em,
        $A, B ::=$, $A -> B$, $| A × B$, $| A + B$,
        $$, $$, $| ℕ$,
    )
]

#slide[
    #align(center,
        grid(
            columns: 2,
            gutter: 8em,
            [= Intrinsic], [= de Bruijn],
            [...], [...]
        )
    )
]

#slide[
    = Weakening and Substitution of de-Bruijn Indices
    ...
]

#slide[
    = Lesson 1: Use Mathlib
    ...
]

#slide[
    = Lesson 2: Functional Style
    ...
]

#slide[
    = Semantics

    ... (so far following Lean 4 tutorial)
]

#slide[
    = Lesson 3: `Prop` and coherence
    
    ...
]

#slide[
    = Refinement Types   

    #v(2em)

    #grid(
        columns: 4,
        gutter: 0.5em,
        $A, B ::=$, $(x: A) -> B$, $| (x: A) × B$, $| A + B$,
        $$, $$, $| ℕ$, $$,
        $$, $$, $| {x: A | φ}$, $| (p: φ) => A$,
        $$, $$, $| ∀x: A, B$, $| ∃x: A, B$
    )

    #v(1em)

    #grid(
        columns: 4,
        gutter: 0.5em,
        $φ, ψ ::=$, $a = b: A$, $| ⊤$, $| ⊥$,
        $$, $$, $| (p: φ) => ψ$, $| (p: φ) ∧ ψ$,
        $$, $$, $| ∀x: A, φ$, $| ∃x: A, φ$
    )
]

#slide[
    = De Bruijn Indices
    ...
]

#slide[
    = Typing Rules
    ...
]

#slide[
    = Theorem: Weakening
    ...
]

#slide[
    = `apply_assumption`?

    ...
]

#slide[
    = Theorem: Substitution
    ...
]

#slide[
    = Erasure
    ...    
]

#slide[
    = Theorem: Semantic Substitution
    ...
]

#slide[
    = `dsimp` and the OOM killer
    ...
]

#slide[
    = Theorem: Semantic Regularity
    ...
]

#slide[
    = Doing Big Inductions
    ...
]

#slide[
    = Future: Verified Interpreter w/ `lean-sys`
    ...
]

#focus-slide[
    = Adding Nothing to HOL
]

#slide[
    ...
]

#focus-slide[
    = The Isotope Project
]

#slide[
    ...
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]

#bibliography("references.bib")