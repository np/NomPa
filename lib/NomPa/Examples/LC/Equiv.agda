open import Level as L
open import NomPa.Record
open import Data.Maybe as Maybe
open import Data.Bool
open import Data.Empty
open import Function
import NomPa.Examples.LC.DataTypes
import NomPa.Derived
import Data.Indexed

module NomPa.Examples.LC.Equiv (nomPa : NomPa) where
open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Examples.LC.DataTypes dataKit ⊥
open Data.Indexed {_} {World}

module TmEq (Env : (α β : World) → Set)
            (cmpName : ∀ {α₁ α₂} → Env α₁ α₂ → Name α₁ → Name α₂ → Bool)
            (extend : ∀ {α₁ α₂} {b₁ b₂} → Env α₁ α₂ → Env (b₁ ◅ α₁) (b₂ ◅ α₂)) where

  cmpTm : ∀ {α₁ α₂} (Δ : Env α₁ α₂) → Tm α₁ → Tm α₂ → Bool
  cmpTm Δ (V x₁)         (V x₂)         = cmpName Δ x₁ x₂
  cmpTm Δ (t₁ · u₁)      (t₂ · u₂)      = cmpTm Δ t₁ t₂ ∧ cmpTm Δ u₁ u₂
  cmpTm Δ (ƛ b₁ t₁)      (ƛ b₂ t₂)      = cmpTm (extend Δ) t₁ t₂
  cmpTm Δ (Let b₁ t₁ u₁) (Let b₂ t₂ u₂) = cmpTm Δ t₁ t₂ ∧ cmpTm (extend Δ) u₁ u₂
  cmpTm _ (` ())         _
  cmpTm _ _              (` ())
  cmpTm _ _              _              = false
{-
cmpTm _ (V _) (ƛ _ _) = false
cmpTm _ (V _) (Let _ _ _) = false
cmpTm _ (_ · _) (V _) = false
cmpTm _ (_ · _) (ƛ _ _) = false
cmpTm _ (_ · _) (Let _ _ _) = false
cmpTm _ (ƛ _ _) (V _) = false
cmpTm _ (ƛ _ _) (_ · _) = false
cmpTm _ (ƛ _ _) (Let _ _ _) = false
cmpTm _ (Let _ _ _) (V _) = false
cmpTm _ (Let _ _ _) (_ · _) = false
cmpTm _ (Let _ _ _) (ƛ _ _) = false
-}

open TmEq (|Cmp| Name) id extendNameCmp public

_==ᵀᵐ_ : ∀ {α} → Tm α → Tm α → Bool
_==ᵀᵐ_ = cmpTm _==ᴺ_
