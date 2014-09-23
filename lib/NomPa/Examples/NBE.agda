{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NomPa.Record
module NomPa.Examples.NBE (nomPa : NomPa) where

open         NomPa nomPa renaming (sucᴮ to sucᴮ; nameᴮ to nameᴮ)
import       NomPa.Derived
open         NomPa.Derived nomPa
open import  Function
open import  Data.Product

{-
module M (Abs : (World → Set) → World → Set) where
  data T α : Set where
    V    : ∀ (x : Name α) → T α
    ƛ    : ∀ (abs : Abs T α) → T α
    _·_  : ∀ (t u : T α) → T α

module TermType = M SynAbsᴺ renaming (T to Term)
module SemType  = M FunAbs renaming (T to Sem)
-}
-- Bug #279 force us to duplicate the type

module TermType where
  data Term α : Set where
    V    : ∀ (x : Name α) → Term α
    ƛ    : ∀ (abs : SynAbsᴺ Term α) → Term α
    _·_  : ∀ (t u : Term α) → Term α

module SemType where
  data Sem α : Set where
    V    : ∀ (x : Name α) → Sem α
    ƛ    : ∀ (abs : FunAbs Sem α) → Sem α
    _·_  : ∀ (t u : Sem α) → Sem α

open TermType public
open SemType public

coerceSem : ∀ {α β} → (α ⊆ β) → Sem α → Sem β
coerceSem pf (V a)    = V (coerceᴺ pf a)
coerceSem pf (t · u)  = coerceSem pf t · coerceSem pf u
coerceSem pf (ƛ f)    = ƛ (λ pf' v → f (⊆-trans pf pf') v)

EvalEnv : (α β : World) → Set
EvalEnv α β = Name α → Sem β

_,_↦_ : ∀ {α β} (Γ : EvalEnv α β) b → Sem β → EvalEnv (b ◅ α) β
_,_↦_ Γ _ v = exportWith v Γ

app : ∀ {α} → Sem α → Sem α → Sem α
app (ƛ f)  v = f ⊆-refl v
app n      v = n · v

eval : ∀ {α β} → EvalEnv α β → Term α → Sem β
eval Γ (ƛ (a , t))  = ƛ (λ pf v → eval ((coerceSem pf ∘ Γ) , a ↦ v) t)
eval Γ (V x)        = Γ x
eval Γ (t · u)      = eval Γ t ⟨ app ⟩ eval Γ u

reify : ∀ {α} → Supply α → Sem α → Term α
reify s         (V a)   = V a
reify s         (n · v) = reify s n · reify s v
reify (sᴮ , s#) (ƛ f)   =
    ƛ (sᴮ , reify (sucᴮ sᴮ , suc# s#) (f (⊆-# s#) (V (nameᴮ sᴮ))))

nf : ∀ {α} → Supply α → Term α → Term α
nf supply = reify supply ∘ eval V

nfø : Term ø → Term ø
nfø = nf (0 ˢ)
