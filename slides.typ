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
        | fn (A B: Ty)
        ```)),
        uncover("3-", align(left, $Γ, Δ ::= dot | Γ, x: A$)),
        uncover("3-", $ ⇝ $),
        uncover("3-", align(left, ```lean
        def Ctx := List Ty
        ```)),
    ))
]

#focus-slide[
    = Intrinsic vs. Extrinsic Typing
]

#focus-slide[
    = Intrinsic Typing
]

#slide[
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
    = Weakening
    #align(center + horizon)[
        ```lean
        inductive Wk: Ctx -> Ctx
        | nil: Wk [] []
        | lift: Wk Γ Δ -> Wk (A::Γ) (A::Δ)
        | step: Wk Γ Δ -> Wk Γ (A::Δ)  
        ```
        #uncover("2-")[
            ```lean
            theorem Stlc.wk: Wk Γ Δ -> HasType Δ A -> HasType Γ A
            ```
        ]
    ]
]

#focus-slide[
    = Extrinsic Typing
]

#slide[
    = Untyped Syntax
    #align(center + horizon,  grid(
        columns: 3,
        gutter: 2em,
        align(left, $s, t ::= x | s med t | λ x: A. t | ()$),
        uncover("2-", $ ⇝ $),
        align(left,[ 
        #only("-2", uncover("2-", ```lean
        inductive Stlc: Type
        | var -- ???
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | app (s t: Stlc)
        | nil
        ```))
        #only("3-", ```lean
        inductive Stlc: Type
        | var (n: ℕ)
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | app (s t: Stlc)
        | nil
        ```)
        ]),
    )) 
]

#let mkred(x) = text(red, x)
#let mkblue(x) = text(blue, x)
#let mkgreen(x) = text(olive.darken(20%), x)

#slide[
    = de-Bruijn Indices
    #align(center + horizon, grid(columns: 3, gutter: 2em,
        $mkred(λ x). mkblue(λ y). bold(mkgreen(λ z)). bold(mkgreen(z))$,
        $==>$,
        $mkred(λ) mkblue(λ) bold(mkgreen(λ)) bold(mkgreen(0))$,
        $mkred(λ x). bold(mkblue(λ y)). mkgreen(λ z). mkblue(y)$,
        $==>$,
        $mkred(λ) bold(mkblue(λ)) mkgreen(λ) bold(mkblue(1))$,
        $bold(mkred(λ x)). mkblue(λ y). mkgreen(λ z). bold(mkred(x))$,
        $==>$,
        $bold(mkred(λ)) mkblue(λ) mkgreen(λ) bold(mkred(2))$,
        $bold(#[$w: A$]) ⊢  mkred(λ x). mkblue(λ y). mkgreen(λ z). bold(w)$,
        $==>$,
        $bold(A) ⊢ mkred(λ) mkblue(λ) mkgreen(λ) bold(3)$
    ))
]

#slide[
    = Typing Judgements
    ```lean
    inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
    ```
    ```lean
    | var : HasVar Γ n A -> HasTy Γ (var n) A
    ```
    ```lean
    | app : HasTy Γ s (fn A B) 
        -> HasTy Γ t A 
        -> HasTy Γ (app s t) B
    ```
    ```lean
    | lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
    ```
    ```lean
    | unit : HasTy Γ nil unit
    ```
    ```lean
    inductive Stlc.HasVar : Ctx -> Nat -> Ty -> Type
    | head : HasVar 0 (A :: Γ)
    | tail : HasVar n Γ -> HasVar (n + 1) (A :: Γ)
    ```
]

#slide[
    = Coherence
    - *Option 1:* _Explicit Refinement Types_
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Prop
        inductive Stlc.HasVar : Ctx -> Nat -> Ty -> Prop
        ```
        - Pros: coherence comes for free, computationally efficient
        - Cons: annoying to define things by induction on well-typed terms
    - *Option 2:* _Adding Nothing to HOL_
        ```lean
        theorem Stlc.HasTy.coherence (H H': HasTy Γ s A) : H = H'
        ```
        - Pros: very easy to define things by induction on well-typed terms
        - Cons: doesn't erase quite the same as `Prop`...
]

#slide[
    = Weakening: Intrinsic
    #align(center + horizon)[
        ```lean
        inductive Wk: Ctx -> Ctx
        | nil: Wk [] []
        | lift: Wk Γ Δ -> Wk (A::Γ) (A::Δ)
        | step: Wk Γ Δ -> Wk Γ (A::Δ)  
        ```
        #uncover("2-")[
            *Question*: how to weaken _terms_?
        ]
    ]
]

#slide[
    = Weakening: Extrinsic
    #align(left + horizon)[
        ```lean
        inductive Wk: (Nat -> Nat) -> Ctx -> Ctx
        | nil: Wk ρ [] []
        | lift: Wk ρ Γ Δ -> Wk (liftWk ρ) (A::Γ) (A::Δ)
        | step: Wk ρ Γ Δ -> Wk (stepWk ρ) Γ (A::Δ)  
        ```
        ```lean
        def liftWk (ρ: Nat -> Nat): Nat -> Nat
        | 0 => 0
        | n + 1 => (ρ n) + 1
        ```
        ```lean
        def stepWk (ρ: Nat -> Nat) (n: Nat): Nat := (ρ n) + 1
        ```
    ]
]

#slide[
    = Weakening Syntax
    #align(left + horizon)[
        ```lean
        def Stlc.wk (ρ: Nat -> Nat) : Stlc -> Stlc
        | var n => var (ρ n)
        | app s t => app (wk ρ s) (wk ρ t)
        | lam A t => lam A (wk (liftWk ρ) t)
        ```
        #uncover("2-")[
            ```lean

            theorem Stlc.wk_id: wk id s = s
            ```
        ]
        #uncover("3-")[
            ```lean
            theorem Stlc.wk_comp: (wk ρ (wk σ t)) = wk (ρ ∘ σ) t
            
            ```
        ]
        #uncover("4-")[
            etc...
        ]
    ]
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