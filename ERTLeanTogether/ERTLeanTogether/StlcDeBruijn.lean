namespace StlcDeBruijn

inductive Ty
| unit
| fn (A B: Ty)

open Ty

def Ctx := List Ty

inductive Stlc: Type
| var (n: Nat)
| app (s t: Stlc)
| lam (A: Ty) (t: Stlc)
| nil

def liftWk (ρ: Nat -> Nat): Nat -> Nat
| 0 => 0
| n + 1 => (ρ n) + 1

def stepWk (ρ: Nat -> Nat) (n: Nat): Nat := (ρ n) + 1

def Stlc.wk (ρ: Nat -> Nat) : Stlc -> Stlc
| var n => var (ρ n)
| app s t => app (wk ρ s) (wk ρ t)
| lam A t => lam A (wk (liftWk ρ) t)
| nil => nil

open Stlc

inductive Var : Ctx -> Nat -> Ty -> Type
| head : Var (A :: Γ) 0 A
| tail : Var Γ n A -> Var (B :: Γ) (n + 1) A

theorem Var.ty_coherence (v: Var Γ n A) (v': Var Γ n B): A = B :=
  by induction v with
  | head => cases v'; rfl
  | tail _ I => cases v'; rw [I]; assumption

theorem Var.coherence (v v': Var Γ n A): v = v' := by
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
| nil : HasTy Γ nil unit

theorem HasTy.ty_coherence: HasTy Γ s A -> HasTy Γ s B -> A = B
| var v, var v' => Var.ty_coherence v v'
| app s _, app s' _ => by cases (ty_coherence s s'); rfl
| lam t, lam t' => by rw [ty_coherence t t']
| nil, nil => rfl

theorem HasTy.coherence: (h h': HasTy Γ s A) -> h = h'
| var v, var v' => by rw [Var.coherence v v']
| app s t, app s' t' => by
  cases (ty_coherence s s')
  rw [coherence s s', coherence t t']
| lam t, lam t' => by rw [coherence t t']
| nil, nil => rfl

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

def liftSubst (σ: Nat -> Stlc) : Nat -> Stlc
| 0 => var 0
| n + 1 => (σ n).wk (stepWk id)

def Stlc.subst (σ: Nat -> Stlc) : Stlc -> Stlc
| var n => σ n
| app s t => app (subst σ s) (subst σ t)
| lam A t => lam A (subst (liftSubst σ) t)
| nil => nil

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
