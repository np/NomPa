{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NomPa.Record
module NomPa.Examples.NBE.Neu (nomPa : NomPa) where

open         NomPa nomPa renaming (sucᴮ to sucᴮ; nameᴮ to nameᴮ)
import       NomPa.Derived
open         NomPa.Derived nomPa
open import  Function
open import  Data.Product

-- We reuse the Term data type...
import NomPa.Examples.NBE
open NomPa.Examples.NBE.TermType nomPa public

mutual
 data Neu α : Set where
  V    : (x : Name α) → Neu α
  _·_  : (t : Neu α) (u : Sem α) → Neu α

 data Sem α : Set where
  N    : (t : Neu α) → Sem α
  ƛ    : (abs : FunAbs Sem α) → Sem α

mutual
  coerceNeu : ∀ {α β} → (α ⊆ β) → Neu α → Neu β
  coerceNeu pf (V a)    = V (coerceᴺ pf a)
  coerceNeu pf (t · u)  = coerceNeu pf t · coerceSem pf u

  coerceSem : ∀ {α β} → (α ⊆ β) → Sem α → Sem β
  coerceSem pf (N n)  = N (coerceNeu pf n)
  coerceSem pf (ƛ f)  = ƛ (λ pf' v → f (⊆-trans pf pf') v)

EvalEnv : (α β : World) → Set
EvalEnv α β = Name α → Sem β

_,_↦_ : ∀ {α β} (Γ : EvalEnv α β) b → Sem β → EvalEnv (b ◅ α) β
_,_↦_ Γ _ v = exportWith v Γ

app : ∀ {α} → Sem α → Sem α → Sem α
app (ƛ f)  v = f ⊆-refl v
app (N n)  v = N (n · v)

eval : ∀ {α β} → EvalEnv α β → Term α → Sem β
eval Γ (ƛ (a , t))  = ƛ (λ pf v → eval ((coerceSem pf ∘ Γ) , a ↦ v) t)
eval Γ (V x)        = Γ x
eval Γ (t · u)      = eval Γ t ⟨ app ⟩ eval Γ u

mutual
  reifyⁿ : ∀ {α} → Supply α → Neu α → Term α
  reifyⁿ s         (V a)   = V a
  reifyⁿ s         (n · v) = reifyⁿ s n · reify s v

  reify : ∀ {α} → Supply α → Sem α → Term α
  reify s         (N n)   = reifyⁿ s n
  reify (sᴮ , s#) (ƛ f)   =
    ƛ (sᴮ , reify (sucᴮ sᴮ , suc# s#) (f (⊆-# s#) (N (V (nameᴮ sᴮ)))))

nf : ∀ {α} → Supply α → Term α → Term α
nf supply = reify supply ∘ eval (N ∘ V)

nfø : Term ø → Term ø
nfø = nf (0 ˢ)
