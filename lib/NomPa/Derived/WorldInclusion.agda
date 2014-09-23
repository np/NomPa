open import NomPa.Record
open import Function
open import Relation.Binary  using (Reflexive; Transitive)
open import Relation.Nullary using (¬_)
import NomPa.Derived

module NomPa.Derived.WorldInclusion (nomPa : NomPa) where

open NomPa nomPa using (World; Binder; Name; ø; _↑1; _+1; _◅_;
                        Nameø-elim; sucᴺ; sucᴺ↑; predᴺ; sucᴮ; exportWith;
                        protect↑)
open NomPa.Derived nomPa using (_→ᴺ_)

infix 3 _⊆_

_⊆_ : (α β : World) → Set
α ⊆ β = α →ᴺ β -- such that the function behaves like the identity

infix 2 _#_
_#_  : Binder → World → Set
b # α = Name α → Name (b ◅ α)

_#ø  : ∀ b → b # ø
b #ø = Nameø-elim

⊆-# : ∀ {α b} → b # α → α ⊆ (b ◅ α)
⊆-# = id

{-
AFAIK these rules cannot be derived

-- nominal
suc# : ∀ {b α} → b # α → (sucᴮ b) # (b ◅ α)
⊆-◅ : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β)

-- de Bruijn
⊆-unctx-+1↑1 : ∀ {α β} → α +1 ⊆ β ↑1 → α ⊆ β
⊆-↑1-inj : ∀ {α β} → α ↑1 ⊆ β ↑1 → α ⊆ β

-- mixes
⊆-dist-+1-◅ : ∀ {α} b → (b ◅ α) +1 ⊆ (sucᴮ b) ◅ (α +1)
⊆-dist-◅-+1 : ∀ {α} b → (sucᴮ b) ◅ (α +1) ⊆ (b ◅ α) +1
-}

coerceᴺ  : ∀ {α β} → (α ⊆ β) → (Name α → Name β)
coerceᴺ  = id

⊆-refl  : Reflexive _⊆_
⊆-refl  = id

⊆-trans : Transitive _⊆_
⊆-trans = λ f g x → g (f x)

⊆-ø     : ∀ {α} → ø ⊆ α
⊆-ø     = Nameø-elim

⊆-cong-↑1 : ∀ {α β} (α⊆β : α ⊆ β) → α ↑1 ⊆ β ↑1
⊆-cong-↑1 f = protect↑ f 1

⊆-cong-+1 : ∀ {α β} (α⊆β : α ⊆ β) → α +1 ⊆ β +1
⊆-cong-+1 f = sucᴺ ∘ f ∘ predᴺ 

⊆-+1↑1 : ∀ {α} → α +1 ⊆ α ↑1
⊆-+1↑1 = sucᴺ↑ ∘ predᴺ

⊆-+1-inj : ∀ {α β} (α+1⊆β+1 : α +1 ⊆ β +1) → α ⊆ β
⊆-+1-inj f = predᴺ ∘ f ∘ sucᴺ

ø+1⊆ø : ø +1 ⊆ ø
ø+1⊆ø = ⊆-refl ∘ predᴺ
