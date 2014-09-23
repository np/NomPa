{-# OPTIONS --no-positivity-check --no-termination-check #-}
open import NomPa.Record
module NomPa.Examples.NBE.Can (nomPa : NomPa) where

open         NomPa nomPa renaming (sucᴮ to sucᴮ; nameᴮ to nameᴮ)
import       NomPa.Derived
open         NomPa.Derived nomPa
open import  Function
open import  Data.Product hiding (map)
open import  Data.List

-- We reuse the Term data type...
import NomPa.Examples.NBE
open NomPa.Examples.NBE.TermType nomPa public

data Sem α : Set where
  V    : (x : Name α) (ts : List (Sem α)) → Sem α
  ƛ    : (abs : FunAbs Sem α) → Sem α

coerceSem : ∀ {α β} → (α ⊆ β) → Sem α → Sem β
coerceSem pf (V x ts)  = V (coerceᴺ pf x) (map (coerceSem pf) ts)
coerceSem pf (ƛ f)     = ƛ (λ pf' v → f (⊆-trans pf pf') v)

EvalEnv : (α β : World) → Set
EvalEnv α β = Name α → Sem β

_,_↦_ : ∀ {α β} (Γ : EvalEnv α β) b → Sem β → EvalEnv (b ◅ α) β
_,_↦_ Γ _ v = exportWith v Γ

app : ∀ {α} → Sem α → Sem α → Sem α
app (ƛ f)     v = f ⊆-refl v
app (V x ts)  v = V x (ts ++ [ v ])

eval : ∀ {α β} → EvalEnv α β → Term α → Sem β
eval Γ (ƛ (a , t))  = ƛ (λ pf v → eval ((coerceSem pf ∘ Γ) , a ↦ v) t)
eval Γ (V x)        = Γ x
eval Γ (t · u)      = eval Γ t ⟨ app ⟩ eval Γ u

appn : ∀ {α} → Term α → List (Term α) → Term α
appn = foldl _·_

reify : ∀ {α} → Supply α → Sem α → Term α
reify s         (V x ts)  = appn (V x) (map (reify s) ts)
reify (sᴮ , s#) (ƛ f)     =
  ƛ (sᴮ , reify (sucᴮ sᴮ , suc# s#) (f (⊆-# s#) (V (nameᴮ sᴮ) [])))

nf : ∀ {α} → Supply α → Term α → Term α
nf supply = reify supply ∘ eval (λ x → V x [])

nfø : Term ø → Term ø
nfø = nf (0 ˢ)
