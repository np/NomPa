{-# OPTIONS --no-positivity-check --no-termination-check #-}
module NaPa.Examples.NBE.Env where

open import  Level
open import  Function
open import  Data.Product
open import  Data.Maybe
open import  Data.Sum
open import  Data.Nat using (_+_)

open import  NaPa
open import  NaPa.Derived

{-
module M (Abs : (World → Set) → World → Set) where
  data T α : Set where
    V    : ∀ (x : Name α) → T α
    ƛ    : ∀ (abs : Abs T α) → T α
    _·_  : ∀ (t u : T α) → T α

open M FunAbs renaming (T to Sem)
open M SynAbs renaming (T to Term)
-}
-- Bug #279 force us to write this instead
data Term α : Set where
  V    : ∀ (x : Name α) → Term α
  ƛ    : ∀ (abs : SynAbs Term α) → Term α
  _·_  : ∀ (t u : Term α) → Term α
data Sem α : Set where
  V    : ∀ (x : Name α) → Sem α
  ƛ    : ∀ (abs : FunAbs Sem α) → Sem α
  _·_  : ∀ (t u : Sem α) → Sem α

shiftSem : Shift Sem Sem
shiftSem k pf (V a)    = V (a +ᴺ k ⟨-because pf -⟩)
shiftSem k pf (t · u)  = shiftSem k pf t · shiftSem k pf u
shiftSem k pf (ƛ f)    = ƛ (shiftFunAbs k pf f)

module NBE (envPack : ShiftableEnvPack zero) where
  open ShiftableEnvPack envPack

  impEnv : ∀ {α β γ} k → (α +ᵂ k) ⊆ β → Env (Sem α) α γ → Env (Sem β) β γ
  impEnv k pf = shiftEnv k pf ∘ mapEnv (shiftSem k pf)

  app : ∀ {α} → Sem α → Sem α → Sem α
  app (ƛ f)  v = f 0 ⊆-refl v
  app n      v = n · v

  eval : ∀ {α β} → Env (Sem α) α β → Term β → Sem α
  eval Γ (ƛ t)   = ƛ (λ k pf v → eval (impEnv k pf Γ ,, v) t)
  eval Γ (V x)   = [ V , id ]′ (lookupEnv Γ x)
  eval Γ (t · u) = eval Γ t ⟨ app ⟩ eval Γ u

  reify : ∀ {α} → Sem α → Term α
  reify (V a)    = V a
  reify (n · v)  = reify n · reify v
  reify (ƛ f)    = ƛ (reify (f 1 ⊆-+1↑1 (V (0 ᴺ))))

  nf : ∀ {α β} → Env (Sem α) α β → Term β → Term α
  nf Γ = reify ∘ eval Γ

  nfC : ∀ {α} → Term α → Term α
  nfC = nf emptyEnv

  nfø : Term ø → Term ø
  nfø = nfC

open NBE shiftableFunEnv

