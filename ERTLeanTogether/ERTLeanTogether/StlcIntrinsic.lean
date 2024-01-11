namespace StlcIntrinsic

inductive Ty
| nat
| fn (A B: Ty)

def Ctx := List Ty

inductive Var: Ctx -> Ty -> Type
| head: Var (A :: Γ) A
| tail: Var Γ A -> Var (B :: Γ) A

def Ty.den: Ty -> Type
| nat => Nat
| fn A B => A.den -> Option (B.den)

open Var

inductive Stlc: Ctx -> Ty -> Type
| var: Var Γ A -> Stlc Γ A
| app: Stlc Γ (Ty.fn A B) -> Stlc Γ A -> Stlc Γ B
| lam: Stlc (A :: Γ) B -> Stlc Γ (Ty.fn A B)
| cnst: Nat -> Stlc Γ Ty.nat
| abort: Stlc Γ A

open Stlc

inductive Wk: Ctx -> Ctx -> Type
| id: Wk [] []
| lift: Wk Γ Δ -> Wk (A :: Γ) (A :: Δ)
| step: Wk Γ Δ -> Wk (A :: Γ) Δ

open Wk

def Var.wk: Wk Γ Δ -> Var Δ A -> Var Γ A
| lift ρ, head => head
| lift ρ, tail v
| step ρ, v => tail (v.wk ρ)

def Stlc.wk (ρ: Wk Γ Δ): Stlc Δ A -> Stlc Γ A
| var v => var (v.wk ρ)
| app s t => app (s.wk ρ) (t.wk ρ)
| lam s => lam (s.wk ρ.lift)
| cnst n => cnst n
| abort => abort
