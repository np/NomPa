open import NomPa.Record
open import NomPa.Record.LogicalRelation
import NomPa.Examples.LC.DataTypes
open import Level as L
open import Data.Empty using (⊥)
module NomPa.Examples.LC.DataTypes.Logical {ℓ} {dataKit : DataKit}
                                           (⟦dataKit⟧ : ⟦DataKit⟧ ℓ dataKit dataKit) where

open NomPa.Examples.LC.DataTypes dataKit ⊥
open DataKit dataKit
open ⟦DataKit⟧ ⟦dataKit⟧

data ⟦Tm⟧ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) : Tm α₁ → Tm α₂ → Set where
  ⟦V⟧    : ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ αᵣ x₁ x₂) → ⟦Tm⟧ αᵣ (V x₁) (V x₂)
  _⟦·⟧_  : ∀ {t₁ t₂ u₁ u₂} (tᵣ : ⟦Tm⟧ αᵣ t₁ t₂)
             (uᵣ : ⟦Tm⟧ αᵣ u₁ u₂) → ⟦Tm⟧ αᵣ (t₁ · u₁) (t₂ · u₂)
  ⟦ƛ⟧    : ∀ {b₁ b₂ t₁ t₂}
             (bᵣ : ⟦Binder⟧ b₁ b₂)
             (tᵣ : ⟦Tm⟧ (bᵣ ⟦◅⟧ αᵣ) t₁ t₂)
           → ⟦Tm⟧ αᵣ (ƛ b₁ t₁) (ƛ b₂ t₂)
  ⟦Let⟧  : ∀ {b₁ b₂ t₁ t₂ u₁ u₂}
             (bᵣ : ⟦Binder⟧ b₁ b₂)
             (tᵣ : ⟦Tm⟧ αᵣ t₁ t₂)
             (uᵣ : ⟦Tm⟧ (bᵣ ⟦◅⟧ αᵣ) u₁ u₂)
           → ⟦Tm⟧ αᵣ (Let b₁ t₁ u₁) (Let b₂ t₂ u₂)
