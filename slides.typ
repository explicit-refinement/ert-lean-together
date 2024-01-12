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
  
  January 12

  Lean Together 2024 -- Online
]

#let newmark = text(red, "(new!)")

#slide[
    = The Plan
    #line-by-line(start: 2)[
        - Speedrun STLC w/ de-Bruijn indices tutorial
            - See #link("https://leanprover.github.io/lean4/doc/examples/deBruijn.lean.html")[Dependent de Bruijn indices in the Lean Manual]
        - Sketch syntactic weakening and substitution #newmark
        - Sketch semantic weakening and substitution #newmark
        - Sketch refinement types #newmark
        - *Hopefully*: sketch _semantic regularity_ #newmark
    ]
    #uncover("7-")[
        *Follow along at:* #link("https://github.com/explicit-refinement/ert-lean-together")
    ]
]

#focus-slide[
    = What is a type theory?
]

#focus-slide[
    = Simply-typed Lambda Calculus
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
#let stlc-abort(ctx, A) = rule(name: $⊥$, $Γ ⊢ attach(⊥, br: A): #A$, $$)
#let stlc-const(ctx, n) = rule(name: $n$, $ctx ⊢ #n: ℕ$, $$)

#slide[
    #align(center + horizon, stack(dir: ttb, spacing: 2em,
        stack(dir: ltr, spacing: 2em,
            only("1-", proof-tree(stlc-var($Γ$, $x$, $A$))),
            only("3-", proof-tree(stlc-app($Γ ⊢ s med t: B$, $Γ ⊢ s: A -> B$, $Γ ⊢ t: A$))),
        ),
        stack(dir: ltr, spacing: 2em,
            only("4-", proof-tree(stlc-lam($Γ ⊢ λ x: A. t: A -> B$, $Γ, x: A ⊢ t: B$))),
        ), 
        stack(dir: ltr, spacing: 2em,
            only("5-", proof-tree(stlc-unit($Γ$))),
            only("6-", proof-tree(stlc-const($Γ$, $n$))),
            only("7-", proof-tree(stlc-abort($Γ$, $A$))),
        ), 
        only("2-", $Γ = x: A, y: B, z: C, ...", etc."$)
    ))
]

#focus-slide[
    = Properties of Type Theories
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
        #uncover("2-")[*If* $Γ ⊇ Δ$]
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

    #align(horizon)[
        #stack(dir: ttb, spacing: 2em,
            [
                Given $σ: sans("Var") -> sans("Stlc")$,
                #uncover("2-", [we say $σ: Γ -> Δ$ if])
                #uncover("3-")[$∀x, x: A ∈ Δ ==> Γ ⊢ σ(x): A$]
            ],
            [
                #uncover("4-")[*Lemma* (Substitution):]
                #uncover("5-")[*If* $σ: Γ -> Δ$, ]
                #uncover("6-")[$Δ ⊢ a: A$]
                #uncover("7-")[*then* $Γ ⊢ [σ]a: A$]
            ],
            [
                #uncover("8-")[Here $[σ]$ denotes *capture-avoiding* substitution.]
            ]
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
        align(left, $A, B ::= bold(1) | ℕ | A -> B$),
        uncover("2-", $ ⇝ $),
        uncover("2-", align(left, ```lean
        inductive Ty: Type
        | unit
        | nat
        | fn (A B: Ty)
        ```)),
    ))
]

#slide[
    = Untyped Syntax
    #align(center + horizon,  grid(
        columns: 3,
        gutter: 2em,
        align(left, $s, t ::= x | s med t | λ x: A. t | () | n | attach(⊥, br: A)$),
        uncover("2-", $ ⇝ $),
        align(left,[ 
        #only("-4", uncover("2-", ```lean
        inductive Stlc: Type
        | var -- ???
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | nil
        | cnst (n: Nat)
        | abort (A: Ty)
        ```))
        #only("5-", ```lean
        inductive Stlc: Type
        | var (n: Nat)
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | nil
        | cnst (n: Nat)
        | abort (A: Ty)
        ```)
        ]),
        // only("7-", align(left, $Γ, Δ ::= dot | Γ, x: A$)),
        // only("8-", $ ⇝ $),
        // only("8-", align(left, ```lean
        // def Ctx := List Ty
        // ```)),
    ))
    #only("3-")[- Want $λ x: A. x = λ y: A. y$ ($α$-conversion)]
    #only("4-")[- Need to impelement capture-avoiding substitution]
    #only("5-")[*Solution: de Bruijn indices*]
]

#let mkred(x) = text(red, x)
#let mkblue(x) = text(blue, x)
#let mkgreen(x) = text(olive.darken(20%), x)

#slide[
    = de-Bruijn Indices
    #align(center + horizon, grid(columns: 3, gutter: 2em,
        $mkred(λ x). mkblue(λ y). bold(mkgreen(λ z)). bold(mkgreen(z))$,
        uncover("2-", $==>$),
        uncover("2-", $mkred(λ) mkblue(λ) bold(mkgreen(λ)) bold(mkgreen(0))$),
        uncover("3-", $mkred(λ x). bold(mkblue(λ y)). mkgreen(λ z). mkblue(y)$),
        uncover("4-", $==>$),
        uncover("4-", $mkred(λ) bold(mkblue(λ)) mkgreen(λ) bold(mkblue(1))$),
        uncover("5-", $bold(mkred(λ x)). mkblue(λ y). mkgreen(λ z). bold(mkred(x))$),
        uncover("6-", $==>$),
        uncover("6-", $bold(mkred(λ)) mkblue(λ) mkgreen(λ) bold(mkred(2))$),
        uncover("7-", $-: A, bold(#[$w: B,$]) -: C ⊢  mkred(λ x). mkblue(λ y). mkgreen(λ z). bold(w)$),
        uncover("8-", $==>$),
        uncover("8-", $A, bold(B), C ⊢ mkred(λ) mkblue(λ) mkgreen(λ) bold(4)$)
    ))
]

#slide[
    = Typing Contexts
    #align(center + horizon,  grid(
        columns: 3,
        gutter: 2em,
        align(left, $s, t ::= x | s med t | λ x: A. t | () | n | attach(⊥, br: A)$),
        $ ⇝ $,
        align(left,[ 
            ```lean
            inductive Stlc: Type
            | var (n: Nat)
            | app (s t: Stlc)
            | lam (A: Ty) (t: Stlc)
            | nil
            | cnst (n: Nat)
            | abort (A: Ty)
            ```
        ]),
        only("2-", align(left, $Γ, Δ ::= dot | Γ, x: A$)),
        only("3-", $ ⇝ $),
        only("3-", align(left, ```lean
        def Ctx := List Ty
        ```)),
    ))
]

#slide[
    = Typing Judgements
    #align(horizon)[
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
        ```
    ]
]

#slide[
    = Variables
    #align(horizon, stack(dir: ttb, spacing: 2em, 
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
        | var : Var Γ n A -> HasTy Γ (var n) A
        ```,
        align(center, proof-tree(stlc-var($Γ$, $x$, $A$))),
        only("2-")[
            ```lean
            inductive Var : Ctx -> Nat -> Ty -> Type
            | head : Var (A :: Γ) 0 A
            | tail : Var Γ n A -> Var (B :: Γ) (n + 1) A
            ```
        ]
    ))
]

#slide[
    = Applications
    #align(horizon, stack(dir: ttb, spacing: 2em, 
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
        | var : Var Γ n A -> HasTy Γ (var n) A
        | app : HasTy Γ s (fn A B) 
          -> HasTy Γ t A 
          -> HasTy Γ (app s t) B
        ```,
        align(center, proof-tree(
            stlc-app($Γ ⊢ s med t: B$, $Γ ⊢ s: A -> B$, $Γ ⊢ t: A$))),
    ))
]

#slide[
    = $λ$-Abstraction
    #align(horizon, stack(dir: ttb, spacing: 2em, 
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
        | var : Var Γ n A -> HasTy Γ (var n) A
        | app : HasTy Γ s (fn A B) 
          -> HasTy Γ t A 
          -> HasTy Γ (app s t) B
        | lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
        ```,
        align(center, proof-tree(
            stlc-lam($Γ ⊢ λ x: A. t: A -> B$, $Γ, x: A ⊢ t: B$))),
    ))
]

#slide[
    = Constants and Effects
    #align(horizon)[
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Type
        | var : Var Γ n A -> HasTy Γ (var n) A
        | app : HasTy Γ s (fn A B) 
            -> HasTy Γ t A 
            -> HasTy Γ (app s t) B
        | lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
        | nil: HasTy Γ nil unit
        | cnst : HasTy Γ (cnst n) nat
        | abort: HasTy Γ (abort A) A
        ```
    ]
]

#focus-slide[
    = Formalizing properties of the STLC
]

#slide[
    = Weakening
    #align(left + horizon)[
        ```lean
        inductive Wk: (Nat -> Nat) -> Ctx -> Ctx -> Type
        ```
        #uncover("3-")[
            ```lean
            | nil: Wk ρ [] []
            ```
        ]
        #uncover("4-")[
            ```lean
            | lift: Wk ρ Γ Δ -> Wk (liftWk ρ) (A::Γ) (A::Δ)
            ```
        ]
        #uncover("5-")[
            ```lean
            | step: Wk ρ Γ Δ -> Wk (stepWk ρ) (A::Γ) Δ  
            ```
        ]
        #only("4")[
            ```lean

            def liftWk (ρ: Nat -> Nat): Nat -> Nat
            | 0 => 0
            | n + 1 => (ρ n) + 1
            ```
        ]
        #only("5")[
            ```lean

            def stepWk (ρ: Nat -> Nat) (n: Nat): Nat := (ρ n) + 1
            ```
        ]
        #uncover("2-")[
            ```lean

            def Var.wk: Wk ρ Γ Δ -> Var Δ n A -> Var Γ (ρ n) A
            ```
        ]
    ]
]

#slide[
    = Weakening Variables
    ```lean
    inductive Wk: (Nat -> Nat) -> Ctx -> Ctx -> Type
    | nil: Wk ρ [] []
    | lift: Wk ρ Γ Δ -> Wk (liftWk ρ) (A::Γ) (A::Δ)
    | step: Wk ρ Γ Δ -> Wk (stepWk ρ) (A::Γ) Δ  

    def Var.wk: Wk ρ Γ Δ -> Var Δ n A -> Var Γ (ρ n) A
    | lift R, head => head
    | lift R, tail v
    | step R, v => tail (v.wk R)
    ```
]

#slide[
    = Weakening Syntax
    #align(left + horizon)[
        ```lean
        def Stlc.wk (ρ: Nat -> Nat) : Stlc -> Stlc
        | var n => var (ρ n)
        | app s t => app (wk ρ s) (wk ρ t)
        | lam t => lam (wk (liftWk ρ) t)
        | t => t
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
    = Weakening Derivations
    #align(horizon)[
        ```lean
        theorem HasTy.wk (R: Wk ρ Γ Δ): HasTy Δ s A 
            -> HasTy Γ (wk ρ s) A
        | var v => v.wk R
        | app s t => app (wk R s) (wk R t)
        | lam A t => lam A (wk R.lift t)
        | unit => unit
        | cnst => cnst
        | abort => abort
        ```
    ]
]

/*
#slide[
    = Weakening: aside
    #align(horizon)[
    ```lean
        inductive Wk
        | id
        | lift (ρ: Wk)
        | step (ρ: Wk)

        def Wk.var: Wk -> Nat -> Nat
        | id, n => n
        | lift ρ, 0 => 0
        | lift ρ, n + 1 => (ρ.var n) + 1
        | step ρ, n => (ρ.var n) + 1
        ```
    ]
]
*/

#slide[
    = Syntax Substitution
    #align(horizon)[
        #align(center)[
            #only("1")[
                $σ: sans("Var") -> sans("Stlc")$
            ]
            #only("2-")[
                ```lean
                σ: Nat -> Stlc
                ```
            ]
        ]

        #uncover("3-")[
            ```lean
            def Stlc.subst (σ: Nat -> Stlc) : Stlc -> Stlc
            | var n => σ n
            | app s t => app (subst σ s) (subst σ t)
            | lam A t => lam A (subst (liftSubst σ) t)
            | t => t
            ```
        ]
        #uncover("4-")[
            ```lean

            def liftSubst (σ: Nat -> Stlc) : Nat -> Stlc
            | 0 => var 0
            | n + 1 => (σ n).wk (stepWk id)
            ```
        ]
    ]
]

#slide[
    = Substitution
    #align(horizon)[
        #only("1", align(center)[
            $σ: Γ -> Δ <==> ∀x, x: A ∈ Δ ==> Γ ⊢ σ(x): A$
        ])
        #only("2-")[
            ```lean
            def Subst (σ: Nat -> Stlc) (Γ Δ: Ctx): Type := 
              ∀{n A}, Var Δ n A -> HasTy Γ (σ n) A
            ```
        ]
        #uncover("3-")[
            ```lean
            def HasTy.subst (S: Subst σ Γ Δ): HasTy Δ s A
              -> HasTy Γ (s.subst σ) A
            ```
        ]
        #uncover("4-")[
            ```lean
            | var v => S v
            ```
        ]
        #uncover("5-")[
            ```lean
            | app s t => app (subst S s) (subst S t)
            ```
        ]
        #uncover("5-")[
            ```lean
            | lam t => lam (subst S.lift t)
            ```
            #only("6-7")[
                ```lean
                lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
                ```
            ]
            #only("7")[
                ```lean
                Subst σ Γ Δ -> Subst (liftSubst σ) (A :: Γ) (A :: Δ)
                ```
            ]
        ]
    ]
]

#slide[
    = Substitution Lifting
    #align(horizon)[
        ```lean
        def Subst.lift (S: Subst σ Γ Δ): Subst (liftSubst σ) (A::Γ) (A::Δ)
        | _, _, head => var head
        | _, _, tail v => (S v).wk (Wk.step Wk.id)

        ```
        #uncover("2-")[
            ```lean

            def Wk.id: {Γ: Ctx} -> Wk id Γ Γ
            | [] => nil
            | _::_ => liftWk_id ▸ lift Wk.id
            ```
        ]
        #uncover("3-")[
            ```lean
            theorem liftWk_id: liftWk id = id 
                := by funext v; cases v <;> rfl
            ```
        ]
    ]
]

#slide[
    = Substitution (cont.)
    #align(horizon)[
        ```lean
        def HasTy.subst (S: Subst σ Γ Δ): HasTy Δ s A
            -> HasTy Γ (s.subst σ) A
        | var v => S v
        | app s t => app (subst S s) (subst S t)
        | lam t => lam (subst S.lift t)
        | unit => unit
        | cnst => cnst
        | abort => abort
        ```
    ]
]

#focus-slide[
    = What is a (denotational) semantics?
]

#let optm = $sans("Option")$

#slide[
    = Type semantics
    #align(horizon, 
    stack(dir: ttb, spacing: 3em,
        [
            #only("1-8", stack(dir: ltr, spacing: 3em,
                    uncover("2-", $[| bold(1) |] = bold(1)$),
                    uncover("3-", $[| ℕ |] = ℕ$),
                    uncover("4-", $[| A -> B |] = [| A |] -> #uncover("5-", optm) [| B |]$)
            ))
            #only("9-")[
                ```lean
                def Ty.den: Ty -> Type
                | nil => Unit
                | nat => Nat
                | fn A B => A.den -> Option (B.den)
                ```
            ]
        ]
        ,
        [
            #only("1-9", stack(dir: ltr, spacing: 3em,
                uncover("6-", $[| dot |] = bold(1)$),
                uncover("7-", 
                    $[| Γ, x: A |] = #uncover("8-", optm) [|A|] × [| Γ |]$)
            ))
            #only("10-")[
                ```lean
                inductive Ctx.den: Ctx -> Type
                | nil: Ctx.den []
                | cons: Option (Ty.den A) 
                    -> Ctx.den Γ 
                    -> Ctx.den (A::Γ)
                ```
            ]
        ]

    ))
]

#slide[
    = Term semantics
    #align(horizon)[
        ```lean
        def HasTy.den: HasTy Γ s A -> Ctx.den Γ -> Option A.den
        ```
    ]
]

#slide[
    = Variable semantics
    #align(horizon)[
        ```lean
        def HasTy.den: HasTy Γ s A -> Ctx.den Γ -> Option A.den
        | var v, G => v.den G
        ```
        #uncover("-2")[
            ```lean

            def Var.den: Var Γ n A -> Ctx.den Γ -> Option A.den
            | head, Ctx.den.cons a _ => a
            | tail v, Ctx.den.cons _ G => v.den G
            ```
        ]
    ]
]

#slide[
    = Application semantics
    #align(horizon)[
        ```lean
        def HasTy.den: HasTy Γ s A -> Ctx.den Γ -> Option A.den
        | var v, G => v.den G
        | app s t, G => do
          let s <- s.den G
          let t <- t.den G
          s t
        ```
    ]
]

#slide[
    = Lambda semantics
    #align(horizon)[
        ```lean
        def HasTy.den: HasTy Γ s A -> Ctx.den Γ -> Option A.den
        | var v, G => v.den G
        | app s t, G => do
          let s <- s.den G
          let t <- t.den G
          s t
        | lam t, G => pure (λx => t.den (Ctx.den.cons x G))
        ```
    ]
]

#slide[
    = Constant semantics
    #align(horizon)[
        ```lean
        def HasTy.den: HasTy Γ s A -> Ctx.den Γ -> Option A.den
        | var v, G => v.den G
        | app s t, G => do
          let s <- s.den G
          let t <- t.den G
          s t
        | lam t, G => pure (λx => t.den (Ctx.den.cons x G))
        | nil, G => pure ()
        | @cnst _ n, _ => pure n
        | abort, _ => none
        ```
    ]
]

#slide[
    = Semantic Weakening

    #align(horizon)[
        ```lean
        def Wk.den: Wk ρ Γ Δ -> Ctx.den Γ -> Ctx.den Δ
        | nil, x => x
        | lift ρ, Ctx.den.cons a G => Ctx.den.cons a (ρ.den G) 
        | step ρ, Ctx.den.cons a G => ρ.den G
        ```
        #uncover("2-")[
            ```lean

            theorem Var.wk_den: (v: Var Δ n A) -> (R: Wk ρ Γ Δ)
              -> ∀{G: Γ.den}, v.den (R.den G) = (v.wk R).den G
            | head, lift R, Ctx.den.cons _ _ => rfl
            | tail v, lift R, Ctx.den.cons _ _
            | v, step R, Ctx.den.cons _ _ 
                => by simp [Wk.den, den, v.wk_den R]
            ```
        ]
    ]
]

#slide[
    = Semantic Weakening

    #align(horizon)[
        ```lean
        theorem HasTy.wk_den (R: Wk ρ Γ Δ) (h: HasTy Δ a A)
        : ∀{G: Γ.den}, h.den (R.den G) = (h.wk R).den G := by
        induction h generalizing ρ Γ with
        | var v => exact Var.wk_den v R
        | lam t I => intros; simp [den, <-I]; rfl
        | _ => simp [den, *]
        ```
    ]
]

#slide[
    = Semantic Substitution

    #align(horizon)[
        ```lean
        def Subst.den: {Γ Δ: _} -> Subst σ Γ Δ -> Γ.den -> Δ.den
        | _, [], _, _ => Ctx.den.nil
        | _, _::_, S, G => Ctx.den.cons
          ((S head).den G)
          (den (Subst.uncons S) G)

        ```
        #uncover("2-")[
            ```lean
            def Var.subst_den: (S: Subst σ Γ Δ) -> (v: Var Δ n A)
              -> ∀{G: Γ.den}, v.den (S.den G) = (S v).den G
            | S, head, G => rfl
            | S, tail v, G => by simp [den, Var.subst_den]; rfl
            ```
        ]
    ]
]

#slide[
    = Semantic Substitution
    
    //TODO: fix sorry?
    #align(horizon)[
        ```lean
        def HasTy.subst_den (S: Subst σ Γ Δ) (h: HasTy Δ s A):
        ∀{G: Γ.den}, h.den (S.den G) = (h.subst S).den G := by
        induction h generalizing Γ σ with
        | var v => exact Var.subst_den S v
        | lam t I => sorry
        | _ => simp [den, *]
        ```
    ]
]

#let donemark = text(green, "✓")

#focus-slide[
    = Recap
]

#slide[
    = The Plan
    #line-by-line[
        - Speedrun STLC w/ de-Bruijn indices tutorial #donemark
        - Sketch syntactic weakening and substitution #donemark
        - Sketch semantic weakening and substitution #donemark
        - Sketch refinement types 
        - *Hopefully*: sketch _semantic regularity_ 
    ]
]

#focus-slide[
    = What is a refinement type?
]

#slide[
    = Refinement Types
    #align(horizon)[
        $
        #only("3-", $(a: $) ℕ#only("3-", $)$) 
            -> #only("2-", ${b :$)ℕ #only("2-", $| b ≤ 10 #only("3-", $∧ b ≤ a$) }$)
        $
        $
        #only("4-", $∀a: ℕ. { b : ℕ | a + b ≥ a }$)
        #only("5-", $≃ {b: ℕ | ∀a, a + b ≥ a}$)
        #only("6-", $≃ {b: ℕ | b ≠ 0}$)
        $
    ]
]

#slide[
    = Ghosts and proofs
    #align(horizon)[
        $
        ∀a, b: ℕ. a + b = b + a
        $
        #only("2-", 
        $
        ∀a: ℕ, { ℓ: [ℕ] | sans("len") med ℓ = a } -> { n: ℕ | n = a }
        $
        )
    ]
]

#slide[
    = Refined Terms
    $
    ∀a: ℕ, { ℓ: [ℕ] | sans("len") med ℓ = a } -> { n: ℕ | n = a }
    $
    #align(left + horizon)[
        #only("2-")[
            $#only("3-", $|$)hat(λ) a: ℕ. λ (ℓ, p):  { ℓ: [ℕ] | sans("len") med ℓ = a }.
                (sans("len") med ℓ, p)#only("3-", $|$)$
        ]
        #only("3-")[

            $= λ-: bold(1). |λ (ℓ, p):  { ℓ: [ℕ] | sans("len") med ℓ = a }.
                (sans("len") med ℓ, p)|$
        ]
        #only("4-")[

            $= λ-: bold(1). λ ℓ: [ℕ]. |(sans("len") med ℓ, p)|$
        ]
        #only("5-")[

            $= λ-: bold(1). λ ℓ: [ℕ]. sans("len") med ℓ$ 
        ]
        #only("5-")[

            $= λ-: bold(1). sans("len")$ 
            
            (by $η$) 
        ]
    ]
]

#let ert-ok-nil() = rule(name: "nil-ok", $dot med sans("ok")$, $$)
#let ert-ok-cons(c, pg, pa) = rule(name: "nil-cons", c, pg, pa)

#slide[
    = "Dependent" Types
    #align(center + horizon, stack(dir: ttb, spacing: 3em,
        $
        Γ ⊢ A med sans("ty")
        $,
        only("2-")[
            #stack(dir: ltr, spacing: 3em, 
                proof-tree(ert-ok-nil()),
                proof-tree(ert-ok-cons($Γ, x: A med sans("ok")$, $Γ med sans("ok")$, $Γ ⊢ A med sans("ty")$))
            )
        ],
        only("3-")[
            *Lemma* (Regularity): $Γ ⊢ a: A ==> Γ ⊢ A med sans("ty")$
        ]
    ))
]

#slide[
    = Semantics of Refinement Types
    #align(horizon)[
        #only("1")[
            $
            [|A|]: 𝒫([| |A| |])
            $
        ]
        #only("2")[
            $
            [|Γ ⊢ A med sans("ty")|]: [| |Γ| |] -> 𝒫([| |A| |])
            $
        ]
    ]
]

#slide[
    = Semantics of Refined Contexts
    #align(horizon)[
        $
        [|Γ ⊢ A med sans("ty")|]: [| |Γ| |] -> 𝒫([| |A| |])
        $
        $
        [|Γ med sans("ok")|]: 𝒫([| |Γ| |])
        $
        #uncover("2-")[
            $
            [|dot med sans("ok")|] &= bold(1) \
            [|Γ, x: A med sans("ok")|] &= [|Γ med sans("ok")|] × [|Γ ⊢ A med sans("ty")|]
            $
        ]
    ]
]

#slide[
    = Semantic Regularity
    #align(horizon)[
        *Theorem* (Semantic Regularity):
        $
        Γ ⊢ a: A ==> ∀ G ∈ [|Γ med sans("ok")|],
            [| |Γ| ⊢ |a|: |A| |] med G ∈ [|Γ ⊢ A med sans("ty")|] 
        $
    ]
]

#focus-slide[
    = So how do we represent this in Lean?
]

#slide[
    = Refined Terms
    ```lean
    inductive Term: Type
    -- Terms
    | var (n: Nat)
    | app (s t: Term)
    | lam (A: Term) (t: Term)
    | nil
    | cnst (n: Nat)
    ```
]

#slide[
    = Ghost Binders
    ```lean
    inductive Term: Type
    -- Terms
    | var (n: Nat)
    | app (s t: Term)
    -- `true` for comp
    -- `false` for ghosts
    | lam (k: Bool) (A: Term) (t: Term)
    | nil
    | cnst (n: Nat)
    ```
]

#slide[
    = "Proofs"
    ```lean
    inductive Term: Type
    -- Terms
    | var (n: Nat)
    | app (s t: Term)
    | lam (k: Bool) (A: Term) (t: Term)
    | nil
    | cnst (n: Nat)

    -- Proofs
    | refl (a: Term)
    ```
]

#slide[
    = "Dependent Types"
    ```lean
    inductive Term: Type
    -- Types (New!)
    | pi (k: Bool) (A: Term) (B: Term)
    | unit
    | nat
    | eq (A: Term) (s t: Term)

    -- Terms
    | var (n: Nat)
    | lam (k: Bool) (A: Term) (t: Term)
    -- ...
    ```
]

#slide[
    = Type Erasure
    #align(horizon)[
        ```lean
        def Term.ty: Term -> Ty
        | pi true A B => A.ty.fn B.ty
        | pi false _ B => Ty.unit.fn B.ty
        | nat => Ty.nat
        | _ => Ty.unit
        ```
    ]
]

#slide[
    = Term Erasure
    #align(horizon)[
        ```lean
        def Term.stlc: Term -> Stlc
        | var n => Stlc.var n
        | app s t => s.stlc.app t.stlc
        | lam true A t => t.stlc.lam A.ty
        | lam false _ t => t.stlc.lam Ty.unit
        | nil => Stlc.nil
        | cnst n => Stlc.cnst n
        | _ => Stlc.nil
        ```
    ]
]

#slide[
    = Syntactic Weakening
    #align(horizon)[
        ```lean
        def Term.wk (ρ: Nat -> Nat) : Term -> Term
        -- new: types weaken just like terms
        | pi k A B => pi k (wk ρ A) (wk ρ B)
        | eq A s t => eq (wk ρ A) (wk ρ s) (wk ρ t)
        --

        | var n => var (ρ n)
        | app s t => app (wk ρ s) (wk ρ t)
        | lam k A t => lam k A (wk (liftWk ρ) t)

        | t => t
        ```
    ]
]

#slide[
    = Syntactic Substitution
    #align(horizon)[
        ```lean
        def Term.subst (σ: Nat -> Term) : Term -> Term
        -- new: types substitute just like terms
        | pi k A B => pi k (subst σ A) (subst σ B)
        | eq A s t => eq (subst σ A) (subst σ s) (subst σ t)
        --

        | var n => σ n
        | app s t => app (subst σ s) (subst σ t)
        | lam k A t => lam k A (subst (liftDSubst σ) t)

        | t => t
        ```
    ]
]

#slide[
    = Dependent Contexts
    #align(horizon)[
        ```lean
        def DCtx := List (Bool × Term)
        ```
        #uncover("2-")[
            ```lean

            def DCtx.stlc: DCtx -> Ctx
            | [] => []
            | ⟨true, A⟩::Γ => A.ty :: stlc Γ            -- computational
            | ⟨false, _⟩::Γ => Ty.unit :: stlc Γ        -- ghost
            ```
        ]
        #uncover("3-")[
            ```lean

            def DCtx.gstlc: DCtx -> Ctx
            | [] => []
            | ⟨_, A⟩::Γ => A.ty :: gstlc Γ
            ```
        ]
    ]
]

#slide[
    = Downgrade
    #align(horizon)[
        ```lean
        def DCtx.downgrade: {Γ: DCtx} -> Γ.gstlc.den -> Γ.stlc.den
        | [], Ctx.den.nil 
          => Ctx.den.nil
        | ⟨true, _⟩::_, Ctx.den.cons a G 
          => Ctx.den.cons a (downgrade G)
        | ⟨false, _⟩::_, Ctx.den.cons _ G 
          => Ctx.den.cons none (downgrade G)
        ```
    ]
]

#slide[
    = Typing Judgements
    ```lean
    inductive DHasTy: DCtx -> Term -> ??? -> Type
    -- ...
    ```
    #line-by-line[
        - `Ty` doesn't work since `Term` can have a dependent type
        - `Term` works for terms, but we want to distinguish valid types...
        - We also want to distinguish "ghost" terms versus "computational" ones
        - *Solution*: introduce new `Annot` type
    ]
    #uncover("4-")[
        ```lean
        inductive Annot: Type
        | ty
        | tm (k: Bool) (A: Term)
        ```
    ]
]

#slide[
    = Valid Types
    ```lean
    inductive DHasTy: DCtx -> Term -> Annot -> Type
    ```
    #only("2-4")[
        ```lean
        | pi: DHasTy Γ A ty -> DHasTy (⟨k, A⟩::Γ) B ty
          -> DHasTy Γ (pi k A B) ty
        ```
    ]
    #only("3-4")[
        ```lean
        | eq: DHasTy Γ A ty 
          -> DHasTy Γ s (tm k A) 
          -> DHasTy Γ t (tm k A)
          -> DHasTy Γ (eq A s t) ty
        ```
    ]
    #only("4")[
        ```lean
        | unit: DHasTy Γ unit ty
        | nat: DHasTy Γ nat ty
        ```
    ]
    #only("5-")[
        ```lean
        -- ...

        inductive VCtx: DCtx -> Type
        | nil: VCtx []
        | cons: DHasTy Γ A ty -> VCtx Γ -> VCtx (⟨k, A⟩::Γ)
        ```
    ]
]

#slide[
    = Variables
    #align(horizon)[
        ```lean
        inductive DHasTy: DCtx -> Term -> Annot -> Type
        -- ...
        | var: DVar Γ n a -> DHasTy Γ (var n) a
        ```
        #only("2-4")[
        ```lean
        inductive DVar: DCtx -> Nat -> Annot -> Type
        ```
        ]
        #only("3-4")[
            ```lean
            | head: k ≥ k' 
              -> DVar (⟨k, A⟩::Γ) 0 (tm k' (A.wk (stepWk id)))
            ```
        ]
        #only("4-4")[
            ```lean
            | tail: DVar Γ n (tm k A) 
              -> DVar (X::Γ) (n + 1) (tm k (A.wk (stepWk id)))
            ```
        ]
        #only("5-")[
            ```lean

            def DVar.ghost: DVar Γ n (tm k A) -> DVar Γ n (tm false A)
            | head H => head (by simp)
            | tail v => tail (ghost v)
            ```
        ]
    ]
]

#slide[
    = Terms
    ```lean
    inductive DHasTy: DCtx -> Term -> Annot -> Type
    -- ...
    ```
    #only("1")[
        ```lean
        | lam:
        DHasTy (⟨k, A⟩::Γ) t (tm k' B)
          -> DHasTy Γ (lam k A t) (tm k' (pi k A B))
        ```
    ]
    #only("2-3")[
        ```lean
        | app:
        DHasTy Γ s (tm k (pi k' A B))
          -> DHasTy Γ t (tm k A)
          -> k' ≥ k
          -> DHasTy Γ (app s t) (tm k (B.subst t.subst0))
        ```
    ]
    #only("3")[
        ```lean

        def Term.subst0 (s: Term): Nat -> Term
        | 0 => s
        | n + 1 => var n
        ```
    ]
    #only("4-")[
        ```lean
        | nil: DHasTy Γ nil (tm k unit)
        | cnst: DHasTy Γ nat (tm k nat)
        ```
    ]
]

#slide[
    = Proofs
    ```lean
    inductive DHasTy: DCtx -> Term -> Annot -> Type
    -- ...
    | refl: DHasTy Γ a (tm k A)
      -> DHasTy Γ (refl a) (tm k' (eq A a a))
    ```
    #only("2-")[
        ```lean

        def DHasTy.ghost: DHasTy Γ s (tm k A) 
          -> DHasTy Γ s (tm false A)
        ```
    ]
]

#slide[
    = Erasure
    #align(horizon)[
        ```lean
        def DHasTy.gstlc: DHasTy Γ s (tm k A) 
          -> HasTy Γ.gstlc s.stlc A.ty
        ```
        #only("2-")[
            ```lean

            def DHasTy.stlc: DHasTy Γ s (tm true A) 
              -> HasTy Γ.stlc s.stlc A.ty
            ```
        ]
        #only("3-")[
            ```lean

            theorem DHasTy.ty_wk: DHasTy Γ s ty 
              -> (s.wk ρ).ty = s.ty
            theorem DHasTy.ty_subst: DHasTy Γ s ty 
              -> (s.subst σ).ty = s.ty
            ```
        ]
    ]
]

#slide[
    = Weakening
    #align(horizon)[
        ```lean
        inductive DWk: (Nat -> Nat) -> DCtx -> DCtx -> Type
        | nil: DWk ρ [] []
        | step: DWk ρ Γ Δ -> DWk (stepWk ρ) (X::Γ) Δ
        ```
        #only("2-")[
            ```lean
            | lift: DWk ρ Γ Δ -> k ≥ k'
              -> DWk (liftWk ρ) (⟨k, A⟩::Γ) (⟨k', A.wk ρ⟩::Δ)
            ```
        ]
        #only("3-")[
            ```lean

            def DVar.wk: DWk ρ Γ Δ -> DVar Δ n a -> DVar Γ (ρ n) a
            ```
        ]
        #only("4-")[
            ```lean

            def DHasTy.wk (R: DWk ρ Γ Δ): 
              DHasTy Δ s a -> DHasTy Γ (s.wk ρ) a
            ```
        ]
    ]
]

#slide[
    = Substitution
    #align(horizon)[
        ```lean
        def DSubst (σ: Nat -> Term) (Γ Δ: DCtx): Type :=
          ∀{n a}, DVar Δ n a -> DHasTy Γ (σ n) a
        ```
        #only("2-")[
            ```lean

            def DHasTy.subst (S: DSubst σ Γ Δ):
              DHasTy Δ s a -> DHasTy Γ (s.subst σ) a
            ```
        ]
    ]
]

#slide[
    = Regularity
    #align(horizon)[
        ```lean
        def DHasTy.reg: DHasTy Γ s (tm k A) -> DHasTy Γ A ty
        ```
    ]
]

#focus-slide[
    = Semantics of refinement types
]

#slide[
    = Semantic Regularity
    #align(horizon)[
        ```lean
        def DHasTy.den_ty: DHasTy Γ s ty 
          -> Γ.gstlc.den -> s.ty.den -> Prop
        ```
        #only("2-")[
            ```lean

            def VCtx.den: VCtx Γ -> Γ.gstlc.den -> Prop
            ```
        ]
        #only("3-")[
            ```lean

            theorem DHasTy.den_reg: (HΓ: VCtx Γ)
              -> (H: DHasTy Γ s (tm k A))
              -> HΓ.den G
              -> ∃a, some a = H.gstlc.den G ∧ H.reg.den_ty G a
            ```
        ]
    ]
]

#slide[
    = Irrelevance
    #align(horizon)[
        ```lean
        theorem DHasTy.irrel: (H: DHasTy Γ s (tm true A))
          -> H.gstlc.den G = H.stlc.den (DCtx.downgrade G)
        ```
    ]
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]

#slide[
    = Aside: Coherence
    #uncover("2-")[
    - *Option 1:* _Adding Nothing to HOL_
        ```lean
        theorem HasTy.ty_coh: HasTy Γ s A -> HasTy Γ s B -> A = B
        theorem HasTy.coh (H H': HasTy Γ s A) : H = H'
        ```
        - Pros: very easy to define things by induction on well-typed terms
        - Cons: doesn't erase quite the same as `Prop`...
    ]
    #uncover("3-")[
    - *Option 2:* _Explicit Refinement Types_
        ```lean
        inductive Stlc.HasTy : Ctx -> Stlc -> Ty -> Prop
        inductive Stlc.Var : Ctx -> Nat -> Ty -> Prop
        ```
        - Pros: coherence comes for free, can use tactics
        - Cons: annoying to define things by induction on well-typed terms
    ]
]

#slide[
    = Aside: why the spurious $bold(1)$ parameter?

    #align(horizon)[
        $
        |hat(λ) (n, p): { n: ℕ | ⊥ } . sans("abort") med p|
        = λ-: bold(1). ⊥
        $
    ]
]