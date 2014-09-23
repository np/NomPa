{-# OPTIONS --universe-polymorphism #-}
module NaPa.TransKit where

open import Level as L using (_⊔_)
import      Category.Functor as Cat
open import Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin
open import Data.Maybe.NP as Maybe
open import NaPa.Interface
open import NaPa using (Name; predᴺ?; sucᴺ↑; zeroᴺ; _↑1)

record TransKit ℓ₁ ℓ₂ : Set (L.suc (ℓ₁ ⊔ ℓ₂)) where
  constructor mkTransKit
  field
    k₁ : DataKit {ℓ₁}
    k₂ : DataKit {ℓ₂}
  open DataKit k₁ renaming (World to World₁; Name to Name₁; _↑1 to _↑1₁)
  open DataKit k₂ renaming (World to World₂; Name to Name₂; _↑1 to _↑1₂)
  field
    Env    : World₁ → World₂ → Set
    _↑↑    : ∀ {α₁ α₂} → Env α₁ α₂ → Env (α₁ ↑1₁) (α₂ ↑1₂)
    lookup : ∀ {α₁ α₂} → Env α₁ α₂ → Name₁ α₁ → Name₂ α₂

-- this should be moved elsewhere
naPaKit : DataKit
naPaKit = mkKit Name _↑1

naPa-to-fin : TransKit _ _
naPa-to-fin = mkTransKit naPaKit finKit (λ α n → Name α → Fin n) _↑↑ id where
  open import Data.Fin
  _↑↑ : ∀ {α n} → (Name α → Fin n) → (Name (α ↑1) → Fin (suc n))
  _↑↑ f = maybe (suc ∘′ f) zero ∘′ predᴺ?

naPa-to-may : TransKit _ _
naPa-to-may = mkTransKit naPaKit mayKit (λ α A → Name α → A) _↑↑ id where
  open Cat.RawFunctor Maybe.functor
  _↑↑ : ∀ {α A} → (Name α → A) → (Name (α ↑1) →? A)
  _↑↑ f x = f <$> predᴺ? x

naPa-to-raw : TransKit _ _
naPa-to-raw = mkTransKit naPaKit rawKit (λ α _ → Name α → ℕ) _↑↑ id where
  _↑↑ : ∀ {α} → (Name α → ℕ) → (Name (α ↑1) → ℕ)
  _↑↑ f = maybe (suc ∘′ f) zero ∘′ predᴺ?

raw-to-NaPa : TransKit _ _
raw-to-NaPa = mkTransKit rawKit naPaKit (λ _ α → ℕ → Name α) _↑↑ id where
  _↑↑ : ∀ {α} → (ℕ → Name α) → (ℕ → Name (α ↑1))
  _↑↑ _ zero    = zeroᴺ
  _↑↑ f (suc n) = sucᴺ↑ (f n)

fin-to-NaPa : TransKit _ _
fin-to-NaPa = mkTransKit finKit naPaKit (λ n α → Fin n → Name α) _↑↑ id where
  open import Data.Fin
  _↑↑ : ∀ {n α} → (Fin n → Name α) → (Fin (suc n) → Name (α ↑1))
  _↑↑ _ zero    = zeroᴺ
  _↑↑ f (suc n) = sucᴺ↑ (f n)

may-to-NaPa : TransKit _ _
may-to-NaPa = mkTransKit mayKit naPaKit (λ A α → A → Name α) _↑↑ id where
  _↑↑ : ∀ {A α} → (A → Name α) → (Maybe A → Name (α ↑1))
  _↑↑ _ nothing  = zeroᴺ
  _↑↑ f (just n) = sucᴺ↑ (f n)


