module NomPa.Laws where

open import NomPa.Record
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Data.Maybe.NP

record Laws (nomPa : NomPa) : Set where
  open NomPa nomPa
  field
   exportᴺ?∘coerceᴺ-success :
          ∀ {b α} {pf : α ⊆ b ◅ α} (x : Name α) → exportᴺ? (coerceᴺ pf x) ≡ just x
   coerceᴺ∘coerceᴺ :
          ∀ {α β γ} {pf₁ : α ⊆ β} {pf₂ : β ⊆ γ} (x : Name α) → coerceᴺ pf₂ (coerceᴺ pf₁ x) ≡ coerceᴺ (⊆-trans pf₁ pf₂) x

