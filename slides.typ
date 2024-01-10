#import "@preview/polylux:0.3.1": *
#import "@preview/curryst:0.1.0": *

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

#let stlc-var(ctx, var, ty) = rule(name: "var", $ctx ⊢ var: ty$, $var: ty ∈ ctx$)
#let stlc-app(c, l, r) = rule(name: "app", c, l, r)
#let stlc-lam(c, p) = rule(name: $λ$, c, p)
#let stlc-zero(ctx) = rule(name: $0$, $Γ ⊢ 0: ℕ$, $$)
#let stlc-succ(c, p) = rule(name: $sans(s)$, c, p)
#let stlc-unit(ctx) = rule(name: $()$, $Γ ⊢ (): bold(1)$, $$)
#let stlc-abort(ctx) = rule(name: $⊥$, $Γ ⊢ ⊥: A$, $$)

#slide[
    = Simply-Typed Lambda Calculus
    #align(center + horizon, stack(dir: ttb, spacing: 2em,
        stack(dir: ltr, spacing: 2em,
            only("2-", proof-tree(stlc-var($Γ$, $x$, $A$))),
            only("3-", proof-tree(stlc-app($Γ ⊢ s med t: B$, $Γ ⊢ s: A -> B$, $Γ ⊢ t: A$))),
        ),
        stack(dir: ltr, spacing: 2em,
            only("4-", proof-tree(stlc-lam($Γ ⊢ λ x: A. t: A -> B$, $Γ, x: A ⊢ t: B$))),
            only("7-", proof-tree(stlc-abort($Γ$))),
        ),
        stack(dir: ltr, spacing: 2em,
            only("5-", proof-tree(stlc-zero($Γ$))),
            only("5-", proof-tree(stlc-succ($Γ ⊢ sans(s) med n: ℕ$, $Γ ⊢ n: ℕ$))),
            only("6-", proof-tree(stlc-unit($Γ$))),
        ),
    ))
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