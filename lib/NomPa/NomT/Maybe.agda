{-# OPTIONS --universe-polymorphism #-}
open import NomPa.Record
module NomPa.NomT.Maybe (nomPa : NomPa) where

import      Level as L
open import Function
open import Data.Maybe.NP
open import Data.Bool
open import Data.Empty
open import Data.Sum
import      Relation.Binary.PropositionalEquality as ≡
open        ≡ using (_≡_)
open import Relation.Nullary
open NomPa nomPa
import Category.Monad as Cat
open Cat.RawMonad {L.zero} Data.Maybe.NP.monad

Name? : World → Set
Name? α = Maybe (Name α)

anon : ∀ {α} → Name? α
anon = nothing

nameᴮ? : ∀ {α} b → Name? (b ◅ α)
nameᴮ? b = just (nameᴮ b)

binderᴺ? : ∀ {α} → Name? α →? Binder
binderᴺ? = map? binderᴺ

_==ᴺ?_ : ∀ {α} (x y : Name? α) → Bool
nothing ==ᴺ? nothing = true
nothing ==ᴺ? _       = false
_       ==ᴺ? nothing = false
just x  ==ᴺ? just y  = x ==ᴺ y

-- no ¬Name?ø since anon : Name? ø
Name?ø≡anon : (x : Name? ø) → x ≡ anon
Name?ø≡anon nothing  = ≡.refl
Name?ø≡anon (just x) = ⊥-elim (¬Nameø x)

exportᴺ?? : ∀ {b α} → Name? (b ◅ α) → Name? α
exportᴺ?? x = exportᴺ? =<< x

data Cmpᴺ? α k : Set where
  nothing : Cmpᴺ? α k
  bound   : Name? (ø ↑ k) → Cmpᴺ? α k
  free    : Name? (α +ᵂ k) → Cmpᴺ? α k

cmpᴺ? : ∀ {α} k → Name? (α ↑ k) → Cmpᴺ? α k
cmpᴺ? k nothing  = nothing
cmpᴺ? k (just x) = [ bound ∘′ just , free ∘′ just ]′ (cmpᴺ k x)

addᴺ? : ∀ {α} k → Name? α → Name? (α +ᵂ k)
addᴺ? k x = addᴺ k <$> x

subtractᴺ?? : ∀ {α} k → Name? (α +ᵂ k) → Name? α
subtractᴺ?? k x = subtractᴺ k <$> x

coerceᴺ? : ∀ {α β} → α ⊆ β → Name? α → Name? β
coerceᴺ? pf x = coerceᴺ pf <$> x

_ᴺ? : ∀ {α} n → Name? (n ᴮ ◅ α)
n ᴺ? = nameᴮ? (n ᴮ)

infixl 6 addᴺ? subtractᴺ??
infix 4 cmpᴺ?
syntax subtractᴺ?? k x = x ∸ᴺ?? k
syntax addᴺ? k x = x +ᴺ? k
syntax cmpᴺ? k x = x <ᴺ? k

sucᴺ? : ∀ {α} → Name? α → Name? (α +1)
sucᴺ? = addᴺ? 1

sucᴺ↑? : ∀ {α} → Name? α → Name? (α ↑1)
sucᴺ↑? = coerceᴺ? ⊆-+1↑1 ∘ sucᴺ?

addᴺ↑? : ∀ {α} ℓ → Name? α → Name? (α ↑ ℓ)
addᴺ↑? ℓ = coerceᴺ? (⊆-+-↑ ℓ) ∘ addᴺ? ℓ

predᴺ?? : ∀ {α} → Name? (α +1) → Name? α
predᴺ?? = subtractᴺ?? 1

-- Handy name eliminator
--subtractWithᴺ : ∀ {a α} {A : Set a} ℓ → A → (Name? α → A) → Name? (α ↑ ℓ) → A
--subtractWithᴺ ℓ v f x = [ const v , f ∘′ subtractᴺ ℓ ]′ (x <ᴺ ℓ)

subtractᴺ↑? : ∀ {α} ℓ → Name? (α ↑ ℓ) → Name? α
-- subtractᴺ↑? ℓ = subtractWithᴺ ℓ nothing just
subtractᴺ↑? ℓ x with x <ᴺ? ℓ
... | nothing = nothing
... | bound _ = nothing
... | free x′ = subtractᴺ?? ℓ x′

predᴺ↑? : ∀ {α} → Name? (α ↑1) → Name? α
predᴺ↑? = subtractᴺ↑? 1

exportWith? : ∀ {b a α} {A : Set a} → A → (Name? α → A) → Name? (b ◅ α) → A
exportWith? v f = maybe (f ∘ just) v ∘′ exportᴺ??

protect↑1? : ∀ {α β} → (Name? α → Name? β) → (Name? (α ↑1) → Name? (β ↑1))
protect↑1? f = exportWith? (0 ᴺ?) (sucᴺ↑? ∘ f ∘ predᴺ??)

module TmExample where
  data Tm α : Set where
    V   : (a : Name? α) → Tm α
    ƛ   : (t : Tm (α ↑1)) → Tm α
    _·_ : (t u : Tm α) → Tm α

  -- For de Bruijn λ-terms we get the following renaming function:
  renTm : ∀ {α β} → (Name? α → Name? β) → Tm α → Tm β
  renTm f (V x)   = V (f x)
  renTm f (t · u) = renTm f t · renTm f u
  renTm f (ƛ t)   = ƛ (renTm (protect↑1? f) t)

  -- That applies nicely to exportᴺ??:
  exportTm : ∀ {b α} → Tm (b ◅ α) → Tm α
  exportTm = renTm exportᴺ??

  -- Since exportTm is total it can also be done lazily:
  lem : ∀ {b α} {t u : Tm (b ◅ α)} → exportTm (t · u) ≡ exportTm t · exportTm u
  lem = ≡.refl
