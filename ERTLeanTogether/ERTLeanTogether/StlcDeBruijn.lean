import Std.Data.Bool
import Mathlib.Init.Order.Defs

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

def Subst.uncons (S: Subst σ Γ (A::Δ)): Subst (σ ∘ Nat.succ) Γ Δ
| n, A, v => @S (n + 1) A (tail v)

def Subst.den: {Γ Δ: _} -> Subst σ Γ Δ -> Γ.den -> Δ.den
| _, [], _, _ => Ctx.den.nil
| _, _::_, S, G => Ctx.den.cons
  ((S head).den G)
  (den (Subst.uncons S) G)

def Var.subst_den: (S: Subst σ Γ Δ) -> (v: Var Δ n A)
  -> ∀{G: Γ.den}, v.den (S.den G) = (S v).den G
| S, head, G => rfl
| S, tail v, G => by simp [den, Var.subst_den]; rfl

def HasTy.subst_den (S: Subst σ Γ Δ) (h: HasTy Δ s A):
  ∀{G: Γ.den}, h.den (S.den G) = (h.subst S).den G := by
  induction h generalizing Γ σ with
  | var v => exact Var.subst_den S v
  | lam t I => sorry
  | _ => simp [den, *]

inductive Term: Type
-- Types
| pi (k: Bool) (A: Term) (B: Term)
| unit
| nat
| eq (A: Term) (s t: Term)

-- Terms
| var (n: Nat)
| app (s t: Term)
| lam (k: Bool) (A: Term) (t: Term)
| nil
| cnst (n: Nat)

-- Proofs
| refl (a: Term)

open Term

def Term.wk (ρ: Nat -> Nat) : Term -> Term
| pi k A B => pi k (wk ρ A) (wk ρ B)
| eq A s t => eq (wk ρ A) (wk ρ s) (wk ρ t)

| var n => var (ρ n)
| app s t => app (wk ρ s) (wk ρ t)
| lam k A t => lam k A (wk (liftWk ρ) t)

| t => t

def liftDSubst (σ: Nat -> Term) : Nat -> Term
| 0 => var 0
| n + 1 => (σ n).wk (stepWk id)

def Term.subst (σ: Nat -> Term) : Term -> Term
| pi k A B => pi k (subst σ A) (subst σ B)
| eq A s t => eq (subst σ A) (subst σ s) (subst σ t)

| var n => σ n
| app s t => app (subst σ s) (subst σ t)
| lam k A t => lam k A (subst (liftDSubst σ) t)

| t => t

def Term.subst0 (s: Term): Nat -> Term
| 0 => s
| n + 1 => var n

def Term.ty: Term -> Ty
| pi true A B => A.ty.fn B.ty
| pi false _ B => Ty.unit.fn B.ty
| nat => Ty.nat
| _ => Ty.unit

def Term.stlc: Term -> Stlc
| var n => Stlc.var n
| app s t => s.stlc.app t.stlc
| lam true A t => t.stlc.lam A.ty
| lam false _ t => t.stlc.lam Ty.unit
| nil => Stlc.nil
| cnst n => Stlc.cnst n
| _ => Stlc.abort Ty.unit

inductive Annot: Type
| ty
| tm (k: Bool) (A: Term)

open Annot

def DCtx := List (Bool × Term)

def DCtx.stlc: DCtx -> Ctx
| [] => []
| ⟨true, A⟩::Γ => A.ty :: stlc Γ
| ⟨false, _⟩::Γ => Ty.unit :: stlc Γ

def DCtx.gstlc: DCtx -> Ctx
| [] => []
| ⟨_, A⟩::Γ => A.ty :: gstlc Γ

def DCtx.downgrade: {Γ: DCtx} -> Γ.gstlc.den -> Γ.stlc.den
| [], Ctx.den.nil => Ctx.den.nil
| ⟨true, _⟩::_, Ctx.den.cons a G => Ctx.den.cons a (downgrade G)
| ⟨false, _⟩::_, Ctx.den.cons _ G => Ctx.den.cons (some ()) (downgrade G)

inductive DVar: DCtx -> Nat -> Annot -> Type
| head: k ≥ k' -> DVar (⟨k, A⟩::Γ) 0 (tm k' (A.wk (stepWk id)))
| tail: DVar Γ n (tm k A) -> DVar (X::Γ) (n + 1) (tm k (A.wk (stepWk id)))

def DVar.no_ty (v: DVar Γ n ty): False := match v with .

inductive DHasTy: DCtx -> Term -> Annot -> Type
| pi: DHasTy Γ A ty -> DHasTy (⟨k, A⟩::Γ) B ty
  -> DHasTy Γ (pi k A B) ty
| unit: DHasTy Γ unit ty
| nat: DHasTy Γ nat ty
| eq: DHasTy Γ A ty -> DHasTy Γ s (tm k A) -> DHasTy Γ t (tm k A)
  -> DHasTy Γ (eq A s t) ty

| var: DVar Γ n a -> DHasTy Γ (var n) a
| app:
  DHasTy Γ s (tm k (pi k' A B))
  -> DHasTy Γ t (tm k A)
  -> k' ≥ k
  -> DHasTy Γ (app s t) (tm k (B.subst t.subst0))
| lam:
  DHasTy (⟨k, A⟩::Γ) t (tm k' B)
  -> DHasTy Γ (lam k A t) (tm k' (pi k A B))
| nil: DHasTy Γ nil (tm k unit)
| cnst: DHasTy Γ nat (tm k nat)

| refl: DHasTy Γ a (tm k A)
  -> DHasTy Γ (refl a) (tm k' (eq A a a))

theorem DHasTy.ty_wk: DHasTy Γ s ty -> (s.wk ρ).ty = s.ty
| pi A B => by
  rename_i k _
  cases k <;>
  simp only [Term.wk, Term.ty, A.ty_wk, B.ty_wk]
| unit => rfl
| nat => rfl
| eq _ _ _ => rfl

theorem DHasTy.ty_subst: DHasTy Γ s ty -> (s.subst σ).ty = s.ty
| pi A B => by
  rename_i k _
  cases k <;>
  simp only [Term.subst, Term.ty, A.ty_subst, B.ty_subst]
| unit => rfl
| nat => rfl
| eq _ _ _ => rfl

def DVar.ghost: DVar Γ n (tm k A) -> DVar Γ n (tm false A)
| head H => head (by simp)
| tail v => tail (ghost v)

def DHasTy.ghost: DHasTy Γ s (tm k A) -> DHasTy Γ s (tm false A)
| var v => var v.ghost
| app s t H => app (ghost s) (ghost t) (by simp)
| lam t => lam (ghost t)
| nil => nil
| cnst => cnst
| refl a => refl a

def DHasTy.stlc: DHasTy Γ s (tm true A) -> HasTy Γ.stlc s.stlc A.ty
| var v => sorry
| app s t H => sorry
| lam t => sorry  -- HasTy.lam (sorry ▸ t.stlc)
| nil => HasTy.nil
| cnst => sorry -- HasTy.cnst?
| refl a => sorry -- HasTy.nil?

def DHasTy.gstlc: DHasTy Γ s (tm k A) -> HasTy Γ.gstlc s.stlc A.ty
| var v => sorry
| app s t H => sorry
| lam t => sorry  -- HasTy.lam (sorry ▸ t.stlc)
| nil => HasTy.nil
| cnst => sorry -- HasTy.cnst?
| refl a => sorry -- HasTy.nil?

def DHasTy.den_ty: DHasTy Γ s ty -> Γ.gstlc.den -> s.ty.den -> Prop
  := sorry

inductive DWk: (Nat -> Nat) -> DCtx -> DCtx -> Type
| nil: DWk ρ [] []
| lift: DWk ρ Γ Δ -> k ≥ k'
  -> DWk (liftWk ρ) (⟨k, A⟩::Γ) (⟨k', A.wk ρ⟩::Δ)
| step: DWk ρ Γ Δ -> DWk (stepWk ρ) (X::Γ) Δ

def DVar.wk: DWk ρ Γ Δ -> DVar Δ n a -> DVar Γ (ρ n) a :=
  sorry

def DHasTy.wk (R: DWk ρ Γ Δ): DHasTy Δ s a -> DHasTy Γ (s.wk ρ) a :=
  sorry

def DSubst (σ: Nat -> Term) (Γ Δ: DCtx): Type :=
  ∀{n a}, DVar Δ n a -> DHasTy Γ (σ n) a

def DHasTy.subst (S: DSubst σ Γ Δ):
  DHasTy Δ s a -> DHasTy Γ (s.subst σ) a :=
  sorry

inductive VCtx: DCtx -> Type
| nil: VCtx []
| cons: DHasTy Γ A ty -> VCtx Γ -> VCtx (⟨k, A⟩::Γ)

def VCtx.den: VCtx Γ -> Γ.gstlc.den -> Prop
| nil, _ => true
| cons H v, Ctx.den.cons a G =>
  ∃b, some b = a ∧ H.den_ty G b ∧ v.den G

def DHasTy.reg: DHasTy Γ s (tm k A) -> DHasTy Γ A ty
  := sorry

def DHasTy.den_reg: (HΓ: VCtx Γ)
  -> (H: DHasTy Γ s (tm k A))
  -> HΓ.den G
  -> ∃a, some a = H.gstlc.den G ∧ H.reg.den_ty G a
  := sorry


theorem DHasTy.irrel: (H: DHasTy Γ s (tm true A))
  -> H.gstlc.den G = H.stlc.den (DCtx.downgrade G)
  := sorry
