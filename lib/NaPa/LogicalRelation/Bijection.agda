module NaPa.LogicalRelation.Bijection where

open import Data.Nat             using (zero; suc)
open import Data.Nat.Logical     using (⟦zero⟧; ⟦suc⟧)
open import Function.Equality    using (_⟶_; _⟨$⟩_)
open import Function.Injection   using (module Injection)
open import Function.Surjection  using (Surjective)
open import Function.LeftInverse using (_LeftInverseOf_)
open import Function.Bijection   using (Bijective)
open import NaPa                 using (Nm; Name→-to-Nm⟶; _↑1; _+1; protect↑1; predᴺ; sucᴺ; _,_)
open import NaPa.LogicalRelation using (⟦World⟧; _⟦↑1⟧; _⟦+1⟧)

_⟦↑1⟧-bij : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) → Bijective (Injection.to αᵣ) → Bijective (Injection.to (αᵣ ⟦↑1⟧))
_⟦↑1⟧-bij {α₁} {α₂} αᵣ αᵣ-bij = record { injective = injective; surjective = to-surj } where
  open Injection (αᵣ ⟦↑1⟧)
  from : Nm (α₂ ↑1) ⟶ Nm (α₁ ↑1)
  from = Name→-to-Nm⟶ (protect↑1 (_⟨$⟩_ (Bijective.from αᵣ-bij)))
  to-left-inv-from : to LeftInverseOf from
  to-left-inv-from (zero ,  _)   = ⟦zero⟧
  to-left-inv-from (suc n , pfx) = ⟦suc⟧ (Bijective.right-inverse-of αᵣ-bij (n , pfx))
  to-surj : Surjective to
  to-surj = record { from = from; right-inverse-of = to-left-inv-from }

_⟦+1⟧-bij : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) → Bijective (Injection.to αᵣ) → Bijective (Injection.to (αᵣ ⟦+1⟧))
_⟦+1⟧-bij {α₁} {α₂} αᵣ αᵣ-bij = record { injective = injective; surjective = sur } where
  open Injection (αᵣ ⟦+1⟧)
  from : Nm (α₂ +1) ⟶ Nm (α₁ +1)
  from = Name→-to-Nm⟶ (λ x → sucᴺ (Bijective.from αᵣ-bij ⟨$⟩ (predᴺ x)))
  to-left-inv-from : to LeftInverseOf from
  to-left-inv-from (zero  , ())
  to-left-inv-from (suc n , p) = ⟦suc⟧ (Bijective.right-inverse-of αᵣ-bij (n , p))
  sur : Surjective to
  sur = record { from = from; right-inverse-of = to-left-inv-from }
