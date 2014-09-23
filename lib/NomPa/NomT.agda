{-# OPTIONS --universe-polymorphism #-}
open import NomPa.Record
module NomPa.NomT (nomPa : NomPa) where

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

abstract
 Name? : World → Set
 Name? α = Name (α ↑1)

 anonᴺ : ∀ {α} → Name? α
 anonᴺ = zeroᴺ

 known : ∀ {α} → Name α → Name? α
 known = sucᴺ↑

 known? : ∀ {a α} {A : Set a} → A → (Name α → A) → Name? α → A
 known? v f = exportWith v (f ∘ predᴺ)

 -- Those could be defined outside `abstract' but are nicer this way

 _==ᴺ?_ : ∀ {α} (x y : Name? α) → Bool
 _==ᴺ?_ = _==ᴺ_

 coerceᴺ? : ∀ {α β} → α ⊆ β → Name? α → Name? β
 coerceᴺ? = coerceᴺ ∘ ⊆-cong-↑1
 -- or the less erasable:
 -- coerceᴺ? = map-anon ∘ coerceᴺ

 map-anon : ∀ {α β} → (Name α → Name β) → (Name? α → Name? β)
 map-anon = protect↑1
 -- or equally:
 -- map-anon f = known? anonᴺ (known ∘ f)

nameᴮ? : ∀ {α} b → Name? (b ◅ α)
nameᴮ? b = known (nameᴮ b)

-- no ¬Name?ø since anonᴺ : Name? ø
-- Name?ø≡anon : (x : Name? ø) → x ≡ anonᴺ
-- Name?ø≡anon x = known? {!!} Nameø-elim x

exportWith? : ∀ {b a α} {A : Set a} → A → (Name? α → A) → Name? (b ◅ α) → A
exportWith? v f = known? v (exportWith v (f ∘ known))

exportᴺ?? : ∀ {b α} → Name? (b ◅ α) → Name? α
exportᴺ?? = exportWith? anonᴺ id

addᴺ? : ∀ {α} k → Name? α → Name? (α +ᵂ k)
addᴺ? = map-anon ∘ addᴺ

sucᴺ? : ∀ {α} → Name? α → Name? (α +1)
sucᴺ? = addᴺ? 1

sucᴺ↑? : ∀ {α} → Name? α → Name? (α ↑1)
sucᴺ↑? = coerceᴺ? ⊆-+1↑1 ∘ sucᴺ?
  -- Without the Name? abstraction
  -- we could defined it as simply sucᴺ↑
  -- this would be wrong since anon should
  -- stay anon.

addᴺ↑? : ∀ {α} ℓ → Name? α → Name? (α ↑ ℓ)
addᴺ↑? ℓ = coerceᴺ? (⊆-+-↑ ℓ) ∘ addᴺ? ℓ

subtractᴺ?? : ∀ {α} k → Name? (α +ᵂ k) → Name? α
subtractᴺ?? = map-anon ∘ subtractᴺ

predᴺ?? : ∀ {α} → Name? (α +1) → Name? α
predᴺ?? = subtractᴺ?? 1

data Cmpᴺ? α k : Set where
  anon  : Cmpᴺ? α k
  bound : Name? (ø ↑ k) → Cmpᴺ? α k
  free  : Name? (α +ᵂ k) → Cmpᴺ? α k

cmpᴺ? : ∀ {α} k → Name? (α ↑ k) → Cmpᴺ? α k
cmpᴺ? k = known? anon ([ bound ∘ known , free ∘ known ]′ ∘ cmpᴺ k)

_ᴺ? : ∀ {α} n → Name? (n ᴮ ◅ α)
n ᴺ? = nameᴮ? (n ᴮ)

infixl 6 addᴺ? subtractᴺ??
infix 4 cmpᴺ?
syntax subtractᴺ?? k x = x ∸ᴺ?? k
syntax addᴺ? k x = x +ᴺ? k
syntax cmpᴺ? k x = x <ᴺ? k

-- Handy name eliminator
--subtractWithᴺ : ∀ {a α} {A : Set a} ℓ → A → (Name? α → A) → Name? (α ↑ ℓ) → A
--subtractWithᴺ ℓ v f x = [ const v , f ∘′ subtractᴺ ℓ ]′ (x <ᴺ ℓ)

subtractᴺ↑? : ∀ {α} ℓ → Name? (α ↑ ℓ) → Name? α
-- subtractᴺ↑? ℓ = subtractWithᴺ ℓ nothing just
subtractᴺ↑? ℓ x with x <ᴺ? ℓ
... | anon    = anonᴺ
... | bound _ = anonᴺ
... | free x′ = subtractᴺ?? ℓ x′

predᴺ↑? : ∀ {α} → Name? (α ↑1) → Name? α
predᴺ↑? = subtractᴺ↑? 1

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
