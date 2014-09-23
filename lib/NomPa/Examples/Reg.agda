open import NomPa.Record

module NomPa.Examples.Reg (nomPa : NomPa) where

open NomPa nomPa

data Reg α : Set where
  V     : (x : Name α) → Reg α
  Let   : ∀ b (s : Reg α) (t : Reg (b ◅ α)) → Reg α
  `0 `1 : Reg α
  _`+_ _`×_ : (s t : Reg α) → Reg α
  `μ : ∀ b (f : Reg (b ◅ α)) → Reg α

data Tel : (α : World) → Set where
  ε      : ∀ {α} → Tel α -- or the empty world
  _,_↦_ : ∀ {α} → Tel α → ∀ b → Reg α → Tel (b ◅ α)

data ⟪_⊢_⟫ {α} : Tel α → Reg α → Set where
  
