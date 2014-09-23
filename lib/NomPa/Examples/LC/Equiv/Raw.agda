open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Relation.Binary.PropositionalEquality
-- open import Data.Atom
open import NomPa.Record
open import NomPa.Record.LogicalRelation

module NomPa.Examples.LC.Equiv.Raw {-(nomPa : NomPa)-} where

open import NomPa.Implem using (nomPa)
open import NomPa.Implem.LogicalRelation using (⟦nomPa⟧; ⟨_,_⟩⟦◅⟧_)
open NomPa nomPa
open ⟦NomPa⟧ ⟦nomPa⟧

import NomPa.Examples.Raw as Raw
import NomPa.Examples.LC as LC
import NomPa.Examples.LC.DataTypes.Logical as ⟦LC⟧

open LC nomPa ⊥ (λ())
open ⟦LC⟧ ⟦dataKit⟧

open Raw using (Rel₀)
open Raw.DataType ℕ
open Raw.RelTm ℕ _≡_

ext : ∀ {α} → ℕ → (Name α → ℕ) → (b : Binder) → Name (b ◅ α) → ℕ
ext s Γ b x = exportWith {b} s Γ x

raw : ∀ {α} → ℕ → (Name α → ℕ) → Tm α → Tmᴿ
raw s Γ (V x)   = V (Γ x)
raw s Γ (t · u) = raw s Γ t · raw s Γ u
raw s Γ (ƛ b t) = ƛ s (raw (suc s) (ext s Γ b) t)
raw s Γ (Let b t u) = V 9 -- {!!}
raw s Γ (` ())

rawø : Tm ø → Tmᴿ
rawø = raw 0 Nameø-elim

relenv→ : ∀ {α₁ α₂} → Rel₀ ℕ → ⟦World⟧ α₁ α₂
         → (Name α₁ → ℕ) → (Name α₂ → ℕ) → Set
relenv→ Δ αᵣ Γ₁ Γ₂ = ∀ x₁ x₂ → Δ (Γ₁ x₁) (Γ₂ x₂) → ⟦Name⟧ αᵣ x₁ x₂

extrelenv→ : ∀ {α₁ α₂} Δ (αᵣ : ⟦World⟧ α₁ α₂) Γ₁ Γ₂ s b b′
              → relenv→ Δ αᵣ Γ₁ Γ₂
              → relenv→ (Extend s s Δ) (⟨ b , b′ ⟩⟦◅⟧ αᵣ) (ext s Γ₁ b) (ext s Γ₂ b′) 
extrelenv→ Δ αᵣ Γ₁ Γ₂ s b b′ re x₁ x₂ Δr with exportᴺ? {b} x₁ | exportᴺ? {b′} x₂ | Δr
... | nothing | nothing | here refl refl = {!re ? ?!}
... | just x₁′ | just x₂′ | there s≢Γ₁x₁ s≢Γ₂x₂ Δr′ = {!re _ _ Δr′!} 
... | _ | _ | _ = {!!}

lem→ : ∀ (Δ : Rel₀ ℕ) {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂)
          Γ₁ Γ₂ s t t′ → relenv→ Δ αᵣ Γ₁ Γ₂
      → Rel™ Δ (raw s Γ₁ t) (raw s Γ₂ t′) → ⟦Tm⟧ αᵣ t t′
lem→ Δ αᵣ Γ₁ Γ₂ s (V x) (V x′) re (V xr) = ⟦V⟧ (re x x′ xr)
lem→ Δ αᵣ Γ₁ Γ₂ s (t · u) (t′ · u′) re (rt · ru) = ⟦LC⟧._⟦·⟧_ (lem→ Δ αᵣ Γ₁ Γ₂ s t t′ re rt) (lem→ Δ αᵣ Γ₁ Γ₂ s u u′ re ru)
lem→ Δ αᵣ Γ₁ Γ₂ s (ƛ b t) (ƛ b′ t′) re (ƛ rt) = ⟦ƛ⟧ _ (lem→ (Extend s s Δ) (⟨ b , b′ ⟩⟦◅⟧ αᵣ) (ext s Γ₁ b) (ext s Γ₂ b′) (suc s) t t′ (extrelenv→ Δ αᵣ Γ₁ Γ₂ s b b′ re) rt)
lem→ Δ αᵣ Γ₁ Γ₂ s (Let b t u) _ re _ = {!!}
lem→ Δ αᵣ Γ₁ Γ₂ s _ (Let b′ t′ u′) re _ = {!!}
lem→ _ _ _ _ _ (V _) (_ · _) _ ()
lem→ _ _ _ _ _ (V _) (ƛ _ _) _ ()
lem→ _ _ _ _ _ (_ · _) (V _) _ ()
lem→ _ _ _ _ _ (_ · _) (ƛ _ _) _ ()
lem→ _ _ _ _ _ (ƛ _ _) (_ · _) _ ()
lem→ _ _ _ _ _ (ƛ _ _) (V _) _ ()
lem→ _ _ _ _ _ _ (` ()) _ _
lem→ _ _ _ _ _ (` ()) _ _ _

relenv← : ∀ {α₁ α₂} → Rel₀ ℕ → ⟦World⟧ α₁ α₂
         → (Name α₁ → ℕ) → (Name α₂ → ℕ) → Set
relenv← = {!!}

relenv : ∀ {α₁ α₂} → Rel₀ ℕ → ⟦World⟧ α₁ α₂
         → (Name α₁ → ℕ) → (Name α₂ → ℕ) → Set
relenv = {!!}

{-
lem← : ∀ (Δ : Rel₀ ℕ) {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) s t t′ → relenv Δ αᵣ
      → ⟦Tm⟧ αᵣ t t′ → Rel™ Δ (raw s Γ₁ t) (raw s Γ₂ t′)
lem← Δ αᵣ s t t′ = ?

lem : ∀ (Δ : Rel₀ ℕ) {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) s t t′ → relenv Δ αᵣ
      → Rel™ Δ (raw s Γ₁ t) (raw s Γ₂ t′) ↔ ⟦Tm⟧ αᵣ t t′
lem Δ αᵣ s t t′ = ?

lemø : ∀ t u → raw t ≡™ raw u ↔ ⟦Tm⟧ ⟦ø⟧ t u
lemø = ?
-}
