open import NomPa.Record

module NomPa.Examples.Records (nomPa : NomPa) where

open import  Coinduction
open import  Data.Nat using (ℕ ; suc ; zero) renaming (_≟_ to _≟ℕ_)
open import  Data.Empty using (⊥-elim)
open import  Data.Product hiding (map)
open import  Data.Maybe
open import  Function
import       Level as L
open import  Data.List as List
import       Category.Monad.Partiality as Pa
open         Pa using (_⊥; run_for_steps)
open import  Relation.Nullary
open import  Relation.Nullary.Decidable
open import  Relation.Binary hiding (_⇒_)
open         NomPa nomPa
import       NomPa.Derived
open         NomPa.Derived nomPa
open import  Data.Label

infixr 5 _⇒_
data Ty : Set where
  _⇒_  : ∀ (τ σ : Ty) → Ty
  ι ο  : Ty
  ⟨_⟩  : (ρ : LabelAssoc Ty) → Ty

open Envs.CEnvPack {L.zero} Envs.funCEnv

data Constant : ∀ τ → Set where
  Number  : (n : ℕ) → Constant ι
  suc     : Constant (ι ⇒ ι)
  NatFix  : ∀ τ → Constant (ι ⇒ (τ ⇒ τ) ⇒ (τ ⇒ τ))

data Trm α : Set where
  V    : ∀ (x : Name α) → Trm α
  _·_  : ∀ (t : Trm α) (u : Trm α) → Trm α
  ƛ    : ∀ b (t : Trm (b ◅ α)) → Trm α
  Let  : ∀ b (t : Trm α) (u : Trm (b ◅ α)) → Trm α
  Cst  : ∀ {τ} (κ : Constant τ) → Trm α
  ⟨_⟩  : ∀ (fs : LabelAssoc (Trm α)) → Trm α
  get  : ∀ (ℓ : Label) → Trm α
  -- set  : ∀ (ℓ : Label) → Trm α
  update⟨_⟩ : ∀ (fs : LabelAssoc (Trm α)) → Trm α

ƛ′ : (∀ {α} → Trm α → Trm α) → Trm ø -- generalize me with importTrm⊆
ƛ′ f = ƛ (x ᴮ) (f (V (x ᴺ)))
  where x = 0

set : ∀ (ℓ : Label) → Trm ø -- generalize me with importTrm⊆
set ℓ = ƛ′ (λ x → update⟨ [ ℓ , x ] ⟩)


module CBVBigStepEval where
  open Pa
  open Pa.Workaround

  sequencePa : ∀ {A : Set} → List (A ⊥P) → (List A) ⊥P
  sequencePa []        = now []
  sequencePa (x ∷ xs)  = x >>= λ y → sequencePa xs >>= λ ys → now (y ∷ ys)

  mapPa : ∀ {A : Set} {B} → (A → B ⊥P) → List A → (List B) ⊥P
  mapPa f = sequencePa ∘ List.map f

  data Val : Set where
    ƛ    : ∀ {α}
             (Γ   : CEnv Val α)
             b (t : Trm (b ◅ α)) → Val
    Cst  : ∀ {τ   : Ty} → Constant τ → Val
    ⟨_⟩  : ∀ (fs  : LabelAssoc Val) → Val
    get  : ∀ (ℓ   : Label) → Val
    -- set  : ∀ (ℓ : Label) → Val
    update⟨_⟩ : ∀ (fs : LabelAssoc Val) → Val

  diverge : ∀ {A : Set} → A ⊥P
  diverge = later (♯ diverge)

  ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
  ℕFix zero    _ = id
  ℕFix (suc n) f = f ∘ ℕFix n f

  -- λ f x → f (f (f ... (f x)))
  ℕFixø : ℕ → Val
  ℕFixø n = ƛ Γ (f ᴮ)
                  (ƛ (x ᴮ) (ℕFix n (_·_ (V f')) (V (x ᴺ))))
   where f = 0
         x = 1
         f' = name◅… 1 f
         Γ : CEnv Val ø
         Γ = Nameø-elim

  evalCst : ∀ {τ} → Constant τ → Val → Val ⊥P
  evalCst suc         (Cst (Number n))  = now (Cst (Number (suc n)))
  evalCst (NatFix τ)  (Cst (Number n))  = now (ℕFixø n)
  evalCst (Number _)  _                 = diverge
  evalCst suc         _                 = diverge
  evalCst (NatFix τ)  _                 = diverge

  mutual

   eval : ∀ {α}
           (t : Trm α) (Γ : CEnv Val α) → Val ⊥P
   eval (t · u) Γ = eval u Γ >>= λ v →
                    eval t Γ >>= λ w → app w v
    where
    app : Val → Val → Val ⊥P
    app (ƛ Γ x body)  v       = later (♯ eval body (Γ , x ↦ v))
    app (Cst κ)       v       = evalCst κ v
    app ⟨ _ ⟩         _       = diverge
    app (get ℓ)       ⟨ fs ⟩  = maybe′ now diverge (select ℓ fs)
    app (get _)       _       = diverge
 -- app (set ℓ)       ⟨ fs ⟩  = {!now (update ℓ )!}
 -- app (set _)       _       = diverge
    app update⟨ fs ⟩  ⟨ gs ⟩  = now ⟨ merge gs fs ⟩
    app update⟨ _ ⟩   _       = diverge

   eval (V x)         Γ  = now (Γ x)
   eval (ƛ x t)       Γ  = now (ƛ Γ x t)
   eval (Let x t u)   Γ  = eval t Γ >>= λ v → eval u (Γ , x ↦ v)
   eval (Cst n)       _  = now (Cst n)
   eval ⟨ fs ⟩        Γ  = evalFlds fs Γ >>= now ∘′ ⟨_⟩
   eval (get ℓ)       _  = now (get ℓ)
-- eval (set ℓ)       _  = now (set ℓ)
   eval update⟨ fs ⟩  Γ  = evalFlds fs Γ >>= now ∘′ update⟨_⟩

   evalFlds : ∀ {α} (fs : LabelAssoc (Trm α)) (Γ : CEnv Val α)
              → (LabelAssoc Val) ⊥P
   evalFlds []              _  =  now []
   evalFlds ((ℓ , t) ∷ fs)  Γ  = later (♯ (eval t Γ >>= λ v →
                                  evalFlds fs Γ >>= λ vs →
                                  now ((ℓ , v) ∷ vs)))

  eval′ : Trm ø → Val ⊥
  eval′ t = ⟦ eval t Nameø-elim ⟧P
