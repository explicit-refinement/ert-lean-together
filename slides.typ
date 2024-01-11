#import "@preview/polylux:0.3.1": *
#import "@preview/curryst:0.1.0": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;
#let app = $med$;
#let llet = $sans("let")$;
#let case = $sans("case")$;

#show link: l => text(blue, l)

#title-slide[
  = Explicit Refinement Types
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami

  University of Cambridge
  
  January 11

  Lean Together 2024 -- Online
]

#let newmark = text(red, "(new!)")

#slide[
    = The Plan
    #line-by-line[
        - Speedrun simply-typed lambda calculus tutorial for de-Bruijn indices
            - See #link("https://leanprover.github.io/lean4/doc/examples/deBruijn.lean.html")[Dependent de Bruijn indices in the Lean Manual]
        - Sketch syntactic weakening and substitution #newmark
        - Sketch semantic weakening and substitution #newmark
        - Sketch refinement types #newmark
        - *Hopefully*: sketch _semantic regularity_ #newmark
    ]
    #uncover("6-")[
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
        align(left, $A, B ::= bold(1) | ℕ | A -> B$),
        uncover("2-", $ ⇝ $),
        uncover("2-", align(left, ```lean
        inductive Ty: Type
        | unit
        | nat
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
        | var: Var Γ A -> Stlc Γ A
        | lam: Stlc (A :: Γ) B -> Stlc Γ (fn A B)
        | app: Stlc Γ (fn A B) -> Stlc Γ A -> Stlc Γ B
        | nil: Stlc Γ unit
        | cnst: Nat -> Stlc Γ nat
        | abort: Stlc Γ A
        ```
        #uncover("3-")[
        ```lean

        -- NOTE: *not* a `Prop`!
        ```
        ]
        #uncover("2-")[
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
    #align(left + horizon)[
        ```lean
        inductive Wk: Ctx -> Ctx
        | nil: Wk [] []
        | lift: Wk Γ Δ -> Wk (A::Γ) (A::Δ)
        | step: Wk Γ Δ -> Wk (A::Γ) Δ  
        ```
        #uncover("2-")[
            ```lean

            def Var.wk: Wk Γ Δ -> Var Δ A -> Var Γ A
            | lift ρ, head => head
            | lift ρ, tail v
            | step ρ, v => tail (v.wk ρ)
            ```
        ]
    ]
]

#slide[
    = Weakening
    #align(horizon)[
    ```lean
        def Stlc.wk (ρ: Wk Γ Δ): Stlc Δ A -> Stlc Γ A
        | var v => var (v.wk ρ)
        | app s t => app (s.wk ρ) (t.wk ρ)
        | lam s => lam (s.wk ρ.lift)
        | nil => nil
        | cnst => cnst
        | abort => abort
        ```
    ]
]

#slide[
    = Substitution
    #align(center + horizon)[
        *Omitted for time*
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
        align(left, $s, t ::= x | s med t | λ x: A. t | () | n | attach(⊥, br: A)$),
        uncover("2-", $ ⇝ $),
        align(left,[ 
        #only("-2", uncover("2-", ```lean
        inductive Stlc: Type
        | var -- ???
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | nil
        | cnst (n: Nat)
        | abort (A: Ty)
        ```))
        #only("3-", ```lean
        inductive Stlc: Type
        | var (n: Nat)
        | app (s t: Stlc)
        | lam (A: Ty) (t: Stlc)
        | nil
        | cnst (n: Nat)
        | abort (A: Ty)
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

#slide[
    #align(horizon)[
        ```lean
        inductive Var : Ctx -> Nat -> Ty -> Type
        | head : Var (A :: Γ) 0 A
        | tail : Var Γ n A -> Var (B :: Γ) (n + 1) A
        ```
    ]
]

#slide[
    = Coherence
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
    = Weakening: Intrinsic
    #align(center + horizon)[
        ```lean
        inductive Wk: Ctx -> Ctx -> Type
        | id: Wk [] []
        | lift: Wk Γ Δ -> Wk (A :: Γ) (A :: Δ)
        | step: Wk Γ Δ -> Wk (A :: Γ) Δ
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
        inductive Wk: (Nat -> Nat) -> Ctx -> Ctx -> Type
        | nil: Wk ρ [] []
        | lift: Wk ρ Γ Δ -> Wk (liftWk ρ) (A::Γ) (A::Δ)
        | step: Wk ρ Γ Δ -> Wk (stepWk ρ) (A::Γ) Δ  
        ```
        #only("-3")[
            #uncover("2-")[
                ```lean

                def liftWk (ρ: Nat -> Nat): Nat -> Nat
                | 0 => 0
                | n + 1 => (ρ n) + 1
                ```
            ]
            #uncover("3-")[
                ```lean
                def stepWk (ρ: Nat -> Nat) (n: Nat): Nat := (ρ n) + 1
                ```
            ]
        ]
        #only("4-")[
            ```lean

            def Var.wk: Wk ρ Γ Δ -> Var Δ A -> Var Γ A
            | lift R, head => head
            | lift R, tail v
            | step R, v => tail (v.wk R)
            ```
        ]
    ]
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

#slide[
    = Syntax Substitution
    #align(horizon)[
        ```lean
        def Stlc.subst (σ: Nat -> Stlc) : Stlc -> Stlc
        | var n => σ n
        | app s t => app (subst σ s) (subst σ t)
        | lam A t => lam A (subst (liftSubst σ) t)
        | t => t
        ```
        #uncover("2-")[
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
        ```lean
        def Subst (σ: Nat -> Stlc) (Γ Δ: Ctx): Type := 
          ∀{n A}, Var Δ n A -> HasTy Γ (σ n) A
        ```
        #uncover("2-")[
            ```lean

            def Subst.lift (S: Subst σ Γ Δ): Subst (liftSubst σ) (A::Γ) (A::Δ)
            | _, _, head => var head
            | _, _, tail v => (S v).wk (Wk.step Wk.id)
            ```
        ]
    ]
]

#slide[
    = Substitution
    #align(horizon)[
        ```lean
        def Subst.lift (S: Subst σ Γ Δ): Subst (liftSubst σ) (A::Γ) (A::Δ)
        | _, _, head => var head
        | _, _, tail v => (S v).wk (Wk.step Wk.id)

        theorem liftWk_id: liftWk id = id 
            := by funext v; cases v <;> rfl
        def Wk.id: {Γ: Ctx} -> Wk id Γ Γ
        | [] => nil
        | _::_ => liftWk_id ▸ lift Wk.id
        ```
    ]
]

#slide[
    = Substitution
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
    #align(center + horizon, 
    grid(columns: 2, gutter: 3em,
        $[| ℕ |] = ℕ$,
        $[| A -> B |] = [| A |] -> #uncover("2-", optm) [| B |]$,
        uncover("3-", $[| dot |] = bold(1)$),
        uncover("3-", 
            $[| Γ, x: A |] = #uncover("4-", optm) [|A|] × [| Γ |]$)
    ))
]

#slide[
    = Type semantics
    #align(horizon)[
        ```lean
        def Ty.den: Ty -> Type
        | nil => Unit
        | nat => Nat
        | fn A B => A.den -> Option (B.den)

        inductive Ctx.den: Ctx -> Type
        | nil: Ctx.den []
        | cons: Option (Ty.den A) 
            -> Ctx.den Γ 
            -> Ctx.den (A::Γ)
        ```
    ]
]

#slide[
    = Term semantics
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
        ∀a: ℕ, { ℓ: [ℕ] | sans("len") med ℓ = a } -> { n: ℕ | n = a }
        $
        #only("2-", 
        $
        ∀a, b: ℕ. a + b = b + a
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

#slide[
    = Aside: why the spurious $bold(1)$ parameter?

    #align(horizon)[
        $
        |hat(λ) (n, p): { n: ℕ | ⊥ } . sans("abort") med p|
        = λ-: bold(1). ⊥
        $
    ]
]

#focus-slide[
    = So how do we represent this in Lean?
]

#slide[
    = Dependent Terms
    ```lean
    inductive Term: Type
    -- Types (New!)
    | pi (k: Bool) (A: Term) (B: Term)
    | unit
    | nat
    | eq (A: Term) (s t: Term)
    -- ...

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
        | _ => Stlc.abort Ty.unit
        ```
    ]
]

#slide[
    = Syntactic Weakening
    #align(horizon)[
        ```lean
        def Term.wk (ρ: Nat -> Nat) : Term -> Term
        | pi k A B => pi k (wk ρ A) (wk ρ B)
        | eq A s t => eq (wk ρ A) (wk ρ s) (wk ρ t)

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
        | pi k A B => pi k (subst σ A) (subst σ B)
        | eq A s t => eq (subst σ A) (subst σ s) (subst σ t)

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
            | ⟨true, A⟩::Γ => A.ty :: stlc Γ
            | ⟨false, _⟩::Γ => Ty.unit :: stlc Γ
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
    = Annotations
    #align(center + horizon)[
        ```lean
        inductive Annot: Type
        | ty
        | tm (k: Bool) (A: Term)
        ```
    ]
]

#slide[
    = Variables
    #align(horizon)[
        ```lean
        inductive DVar: DCtx -> Nat -> Annot -> Type
        ```
        #only("2-")[
            ```lean
            | head: k ≥ k' 
                -> DVar (⟨k, A⟩::Γ) 0 (tm k' (A.wk (stepWk id)))
            ```
        ]
        #only("3-")[
            ```lean
            | tail: DVar Γ n (tm k A) 
                -> DVar (X::Γ) (n + 1) (tm k (A.wk (stepWk id)))
            ```
        ]
        #only("4-")[
            ```lean

            def DVar.ghost: DVar Γ n (tm k A) -> DVar Γ n (tm false A)
            | head H => head (by simp)
            | tail v => tail (ghost v)
            ```
        ]
    ]
]

#slide[
    = Typing Judgements
    ...
]

#slide[
    = Erasure
    ...
]

#slide[
    = Weakening
    ...
    ... proof requirements ...
]

#slide[
    = Substitution
    ...
    ... proof requirements ...
]

#focus-slide[
    = Semantics of refinement types
    ...
    ... proof requirements ...
]

#slide[
    = Semantic Regularity
    ...
    ... proof requirements ...
]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]

#bibliography("references.bib")