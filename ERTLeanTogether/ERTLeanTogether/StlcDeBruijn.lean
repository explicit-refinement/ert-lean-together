namespace StlcDeBruijn

inductive Ty
| unit
| nat
| fn (A B: Ty)

open Ty

def Ty.den: Ty -> Type
| unit => Unit
| nat => Nat
| fn A B => A.den -> Option (B.den)

def Ctx := List Ty

inductive Ctx.den: Ctx -> Type
| nil: Ctx.den []
| cons: Option (Ty.den A) -> Ctx.den Γ -> Ctx.den (A::Γ)

inductive Stlc: Type
| var (n: Nat)
| app (s t: Stlc)
| lam (A: Ty) (t: Stlc)
| nil
| cnst (n: Nat)
| abort (A: Ty)

def liftWk (ρ: Nat -> Nat): Nat -> Nat
| 0 => 0
| n + 1 => (ρ n) + 1

def stepWk (ρ: Nat -> Nat) (n: Nat): Nat := (ρ n) + 1

def Stlc.wk (ρ: Nat -> Nat) : Stlc -> Stlc
| var n => var (ρ n)
| app s t => app (wk ρ s) (wk ρ t)
| lam A t => lam A (wk (liftWk ρ) t)
| t => t

open Stlc

inductive Var : Ctx -> Nat -> Ty -> Type
| head : Var (A :: Γ) 0 A
| tail : Var Γ n A -> Var (B :: Γ) (n + 1) A

theorem Var.ty_coh (v: Var Γ n A) (v': Var Γ n B): A = B :=
  by induction v with
  | head => cases v'; rfl
  | tail _ I => cases v'; rw [I]; assumption

theorem Var.coh (v v': Var Γ n A): v = v' := by
  induction v with
  | head => cases v'; rfl
  | tail v I => cases v'; rw [I]

open Var

inductive HasTy : Ctx -> Stlc -> Ty -> Type
| var : Var Γ n A -> HasTy Γ (var n) A
| app : HasTy Γ s (fn A B)
    -> HasTy Γ t A
    -> HasTy Γ (app s t) B
| lam : HasTy (A :: Γ) t B -> HasTy Γ (lam A t) (fn A B)
| nil: HasTy Γ nil unit
| cnst : HasTy Γ (cnst n) nat
| abort: HasTy Γ (abort A) A

theorem HasTy.ty_coh: HasTy Γ s A -> HasTy Γ s B -> A = B
| var v, var v' => Var.ty_coh v v'
| app s _, app s' _ => by cases (ty_coh s s'); rfl
| lam t, lam t' => by rw [ty_coh t t']
| nil, nil => rfl
| cnst, cnst => rfl
| abort, abort => rfl

theorem HasTy.coh: (h h': HasTy Γ s A) -> h = h'
| var v, var v' => by rw [Var.coh v v']
| app s t, app s' t' => by
  cases (ty_coh s s')
  rw [coh s s', coh t t']
| lam t, lam t' => by rw [coh t t']
| nil, nil => rfl
| cnst, cnst => rfl
| abort, abort => rfl

open HasTy

inductive Wk: (Nat -> Nat) -> Ctx -> Ctx -> Type
| nil: Wk ρ [] []
| lift: Wk ρ Γ Δ -> Wk (liftWk ρ) (A::Γ) (A::Δ)
| step: Wk ρ Γ Δ -> Wk (stepWk ρ) (A::Γ) Δ

open Wk

def Var.wk: Wk ρ Γ Δ -> Var Δ n A -> Var Γ (ρ n) A
| lift R, head => head
| lift R, tail v
| step R, v => tail (v.wk R)

def HasTy.wk (R: Wk ρ Γ Δ): HasTy Δ s A -> HasTy Γ (wk ρ s) A
| var v => var (v.wk R)
| app s t => app (wk R s) (wk R t)
| lam t => lam (wk R.lift t)
| nil => nil
| cnst => cnst
| abort => abort

def liftSubst (σ: Nat -> Stlc) : Nat -> Stlc
| 0 => var 0
| n + 1 => (σ n).wk (stepWk id)

def Stlc.subst (σ: Nat -> Stlc) : Stlc -> Stlc
| var n => σ n
| app s t => app (subst σ s) (subst σ t)
| lam A t => lam A (subst (liftSubst σ) t)
| t => t

def Subst (σ: Nat -> Stlc) (Γ Δ: Ctx): Type :=
  ∀{n A}, Var Δ n A -> HasTy Γ (σ n) A

theorem liftWk_id: liftWk id = id := by funext v; cases v <;> rfl

def Wk.id: {Γ: Ctx} -> Wk id Γ Γ
| [] => nil
| _::_ => liftWk_id ▸ lift Wk.id

def Subst.lift (S: Subst σ Γ Δ): Subst (liftSubst σ) (A::Γ) (A::Δ)
| _, _, head => var head
| _, _, tail v => (S v).wk (Wk.step Wk.id)

def HasTy.subst (S: Subst σ Γ Δ): HasTy Δ s A
    -> HasTy Γ (s.subst σ) A
| var v => S v
| app s t => app (subst S s) (subst S t)
| lam t => lam (subst S.lift t)
| nil => nil
| cnst => cnst
| abort => abort

def Var.den: Var Γ n A -> Ctx.den Γ -> Option A.den
| head, Ctx.den.cons a _ => a
| tail v, Ctx.den.cons _ G => v.den G

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

def Wk.den: Wk ρ Γ Δ -> Ctx.den Γ -> Ctx.den Δ
| nil, x => x
| lift ρ, Ctx.den.cons a G => Ctx.den.cons a (ρ.den G)
| step ρ, Ctx.den.cons a G => ρ.den G

theorem Var.wk_den: (v: Var Δ n A) -> (R: Wk ρ Γ Δ)
  -> ∀{G: Γ.den}, v.den (R.den G) = (v.wk R).den G
| head, lift R, Ctx.den.cons _ _ => rfl
| tail v, lift R, Ctx.den.cons _ _
| v, step R, Ctx.den.cons _ _ => by simp [Wk.den, den, v.wk_den R]

theorem HasTy.wk_den (R: Wk ρ Γ Δ) (h: HasTy Δ a A)
  : ∀{G: Γ.den}, h.den (R.den G) = (h.wk R).den G := by
  induction h generalizing ρ Γ with
  | var v => exact Var.wk_den v R
  | lam t I => intros; simp [den, <-I]; rfl
  | _ => simp [den, *]
