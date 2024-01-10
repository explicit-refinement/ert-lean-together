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
#let stlc-pair(c, l, r) = rule(name: $×$, c, l, r)
#let stlc-let2(c, p) = rule(name: "let2", c, p)
#let stlc-unit(ctx) = rule(name: $()$, $Γ ⊢ (): bold(1)$, $$)
#let stlc-inl(c, p) = rule(name: $ι_0$, c, p)
#let stlc-inr(c, p) = rule(name: $ι_1$, c, p)
#let stlc-cases(c, e, l, r) = rule(name: $sans(c)$, c, e, l, r)
#let stlc-zero(ctx) = rule(name: $0$, $Γ ⊢ 0: ℕ$, $$)
#let stlc-succ(c, p) = rule(name: $sans(s)$, c, p)
#let stlc-natrec(c, z, s) = rule(name: $sans(i)$, c, z, s)
#let stlc-abort(ctx) = rule(name: $⊥$, $Γ ⊢ ⊥: A$, $$)

#slide[
    = Simply-Typed Lambda Calculus
    #align(center + horizon, stack(dir: ttb, spacing: 2em,
        stack(dir: ltr, spacing: 2em,
            only("1-", proof-tree(stlc-var($Γ$, $x$, $A$))),
            only("3-", proof-tree(stlc-app($Γ ⊢ s med t: B$, $Γ ⊢ s: A -> B$, $Γ ⊢ t: A$))),
        ),
        stack(dir: ltr, spacing: 2em,
            only("4-", proof-tree(stlc-lam($Γ ⊢ λ x: A. t: A -> B$, $Γ, x: A ⊢ t: B$))),
            only("5-", proof-tree(stlc-unit($Γ$))),
        ),
        only("2-", $Γ = x: A, y: B, z: C, ...", etc."$)
    ))
]

#slide[
    = Weakening
    #align(center + horizon)[
        $f: A -> B, #only("2", text(red, $y: C, $)) x: A ⊢ f med x: B$
    ]
]

#slide[
    #align(center + horizon)[
        *Lemma* (Weakening):
        #uncover("2-")[*If* $Δ ⊆ Γ$]
        #uncover("3-")[and $Δ ⊢ a: A$,]
        #uncover("4-")[*then* $Γ ⊢ a: A$]
    ]
]

#slide[
    = Substitution
    #align(center + horizon)[
        $
        f: A -> B, x: A ⊢ f med x: B
        $
        $
        #only("1", $y: B,$) 
        #only("2", text(red, $f: A -> B, x: A,$))
        g: B -> C ⊢ g
        #only("1", $y$)
        #only("2", text(red, $(f med x)$)): C
        $
    ]
]

#let stlc-subst-nil(ctx) = rule(name: "subst-nil", $dot: ctx -> dot$, $$)

#let stlc-subst-cons(c, σ, t) = rule(name: "subst-cons", c, σ, t)

#slide[
    = Substitution

    #align(center + horizon)[
        #stack(dir: ttb, spacing: 2em,
            align(left)[
                #uncover("2-")[*Lemma* (Substitution):]
                #uncover("3-")[*If* $σ: Γ -> Δ$, ]
                #uncover("4-")[$Δ ⊢ a: A$]
                #uncover("5-")[*then* $Γ ⊢ [σ]a: A$]
            ],
            stack(
                dir: ltr,
                spacing: 2em,
                proof-tree(stlc-subst-nil($Γ$)),
                proof-tree(stlc-subst-cons(
                    $[x ↦ t]σ: Γ -> Δ, x: A$, 
                    $σ: Γ -> Δ$, 
                    $Γ ⊢ t: A$))
            ),
        )
    ]
]

#focus-slide[
    = How would we represent this in Lean?
]

#slide[
    = Types
    #align(center + horizon,  grid(
        columns: 3,
        gutter: 3em,
        align(left, $A, B ::= bold(1) | A -> B$),
        uncover("2-", $ ⇝ $),
        uncover("2-", align(left, ```lean
        inductive Ty: Type
        | unit
        | fn (A B: Ty): Ty
        ```)),
        uncover("3-", align(left, $Γ, Δ ::= dot | Γ, x: A$)),
        uncover("3-", $ ⇝ $),
        uncover("3-", align(left, ```lean
        def Ctx := List Ty
        ```)),
    ))
]

#slide[
    = Intrinsic Style
    #align(left + horizon)[
        ```lean
        inductive Stlc: Ctx -> Ty -> Type
        ```
        #uncover("5-")[
        ```lean
        | var: Var Γ A -> Stlc Γ A
        ```
        ]
        #uncover("2-")[
        ```lean
        | lam: Stlc (A :: Γ) B -> Stlc Γ (fn A B)
        ```
        ]
        #uncover("3-")[
        ```lean
        | app: Stlc Γ (fn A B) -> Stlc Γ A -> Stlc Γ B
        ```
        ]
        #uncover("4-")[
        ```lean
        | unit: Stlc Γ unit
        ```
        ]
        #uncover("7-")[
        ```lean
        -- NOTE: *not* a `Prop`!
        ```
        ]
        #uncover("6-")[
        ```lean
        inductive Var: Ctx -> Ty -> Type
        | head: Var (A :: Γ) A
        | tail: Var Γ A -> Var (B :: Γ) A
        ```
        ]
    ]
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
    = Weakening Syntax
    - TODO: inductive style
    - TODO: functional style
    - TODO: definition
    - TODO: fun theorems
]

#slide[
    = Substituting Syntax
    - TODO: definition
    - TODO: fun theorems
]

#slide[
    = Typing Judgements
]

#slide[
    = Coherence
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
    = Set semantics

    - TODO: context semantics
    - TODO: type semantics
    - TODO: judgement semantics
]

#slide[
    = Data types

    - TODO: products
    - TODO: coproducts
    - TODO: natural numbers
]

#slide[
    = Effects

    - TODO: `abort` rule
    - TODO: `Option` monad
]

#slide[
    = Semantic Weakening

    - TODO: semantics of a weakening
    - TODO: statement
]

#slide[
    = Semantic Substitution

    - TODO: semantics of a substitution
    - TODO: statement
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