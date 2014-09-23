{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NomPa.Record
module NomPa.Examples.NBE.Env (nomPa : NomPa) where

open         NomPa nomPa renaming (sucᴮ to sucᴮ; nameᴮ to nameᴮ)
import       NomPa.Derived
open         NomPa.Derived nomPa
open import  Level as L
open import  Function
open import  Data.Product
open import  Data.Sum

-- We reuse the data types...
import NomPa.Examples.NBE
open NomPa.Examples.NBE.TermType nomPa
open NomPa.Examples.NBE.SemType nomPa

coerceSem : ∀ {α β} → (α ⊆ β) → Sem α → Sem β
coerceSem pf (V a)    = V (coerceᴺ pf a)
coerceSem pf (t · u)  = coerceSem pf t · coerceSem pf u
coerceSem pf (ƛ f)    = ƛ (λ pf' v → f (⊆-trans pf pf') v)

module NBE (coeEnvPack : Envs.CoeEnvPack L.zero) where
  open Envs.CoeEnvPack coeEnvPack

  EvalEnv : (α Ω : World) → Set
  EvalEnv α Ω = Env (Sem Ω) α Ω

  coeEnv : ∀ {α β γ} → (α ⊆ β) → EvalEnv γ α → EvalEnv γ β
  coeEnv pf = mapEnv (coerceSem pf) ∘ coerceEnv pf

  app : ∀ {α} → Sem α → Sem α → Sem α
  app (ƛ f)  v = f ⊆-refl v
  app n      v = n · v

  eval : ∀ {α β} → EvalEnv β α → Term β → Sem α
  eval Γ (ƛ (a , t))  = ƛ (λ pf v → eval (coeEnv pf Γ , a ↦ v) t)
  eval Γ (V x)        = [ V , id ]′ (lookupEnv Γ x)
  eval Γ (t · u)      = eval Γ t ⟨ app ⟩ eval Γ u

  reify : ∀ {α} → Supply α → Sem α → Term α
  reify s         (V a)   = V a
  reify s         (n · v) = reify s n · reify s v
  reify (sᴮ , s#) (ƛ f)   =
      ƛ (sᴮ , reify (sucᴮ sᴮ , suc# s#) (f (⊆-# s#) (V (nameᴮ sᴮ))))

  nf : ∀ {α} → Supply α → Term α → Term α
  nf supply = reify supply ∘ eval emptyEnv

  nfø : Term ø → Term ø
  nfø = nf (0 ˢ)

module NBE-dataEnv = NBE Envs.dataEnv′
module NBE-funEnv = NBE Envs.funEnv
