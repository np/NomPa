{-# OPTIONS --universe-polymorphism #-}
module NaPa.Interface where

import Level as L
open import Function
open import Data.Nat hiding (_+_)
open import Data.Maybe.NP using (Maybe; nothing; just; _→?_)
open import Data.Unit using (⊤)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Bool
open import NomPa.Worlds
open import NomPa.Subtyping
open import Relation.Nullary

record DataKit {ℓ} : Set (L.suc ℓ) where
  constructor mkKit
  field
    {World} : Set ℓ
    Name    : World → Set
    _↑1     : World → World
  infix 10 _↑1

rawKit : DataKit
rawKit = mkKit {World = ⊤} (const ℕ) _

finKit : DataKit
finKit = mkKit Fin suc

mayKit : DataKit
mayKit = mkKit id Maybe

record Types (World : Set) : Set₁ where
  field
    Name : World → Set
    _⊆_ : World → World → Set
  infix 2 _⊆_

record Primitives {World}
                  (worldSym : WorldSymantics World)
                  (types : Types World)
                  (⊆-Sym : ⊆-Symantics worldSym (Types._⊆_ types)) : Set where
  open Types types
  open WorldSymantics worldSym
  open WorldOps worldSym
  open ⊆-Symantics ⊆-Sym
  field
    _==_      : ∀ {α} → Name α → Name α → Bool
    zeroᴺ     : ∀ {α} → Name (α ↑1)
    addᴺ      : ∀ {α} k → Name α → Name (α +ᵂ k)
    subtractᴺ : ∀ {α} k → Name (α +ᵂ k) → Name α
    coerceᴺ    : ∀ {α β} → α ⊆ β → Name α → Name β
    cmpᴺ       : ∀ {α} k → Name (α ↑ k) → Name (ø ↑ k) ⊎ Name (α +ᵂ k)
    ¬Nameø    : ¬(Name ø)

  infixl 6 addᴺ subtractᴺ
  infix 4 cmpᴺ
  syntax subtractᴺ k x = x ∸ᴺ k
  syntax addᴺ k x = x +ᴺ k
  syntax cmpᴺ k x = x <ᴺ k

module Derived {World}
               {worldSym : WorldSymantics World}
               (types : Types World)
               (⊆-Sym : ⊆-Symantics worldSym (Types._⊆_ types))
               (prims : Primitives worldSym types ⊆-Sym) where
  open Types types
  open WorldSymantics worldSym
  open WorldOps worldSym
  open ⊆-Symantics ⊆-Sym
  open Primitives prims

  naPaKit : DataKit
  naPaKit = mkKit Name _↑1

  -- zeroᴺ↑1+ : ∀ {α} k → Name (α ↑ (1 + k))
  -- zeroᴺ↑1+ _ = zeroᴺ

  sucᴺ : ∀ {α} → Name α → Name (α +1)
  sucᴺ = addᴺ 1

  sucᴺ↑ : ∀ {α} → Name α → Name (α ↑1)
  sucᴺ↑ = coerceᴺ ⊆-+1↑1 ∘ sucᴺ

  predᴺ : ∀ {α} → Name (α +1) → Name α
  predᴺ = subtractᴺ 1

  fromFin  : ∀ {α n} → Fin n → Name (α ↑ n)
  fromFin zero    = zeroᴺ
  fromFin (suc i) = sucᴺ↑ (fromFin i)

  subtractᴺ? : ∀ {α} k → Name (α ↑ k) →? Name α
  subtractᴺ? k x = [ const nothing , just ∘′ subtractᴺ k ]′ (x <ᴺ k)

  infix 0 _⟨-because_-⟩
  _⟨-because_-⟩ : ∀ {α β} → Name α → α ⊆ β → Name β
  _⟨-because_-⟩ n pf = coerceᴺ pf n

  shiftName : ∀ {α β} ℓ k → (α +ᵂ k) ⊆ β → Name (α ↑ ℓ) → Name (β ↑ ℓ)
  shiftName ℓ k pf n
    with n <ᴺ ℓ
  ...  | inj₁ n′ = n′       ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
  ...  | inj₂ n′ = n′ +ᴺ k  ⟨-because ⊆-trans (⊆-exch-+-+ ⊆-refl ℓ k) (⊆-ctx-+↑ pf ℓ) -⟩

  ¬Name : ∀ {α} → α ⊆ ø → ¬(Name α)
  ¬Name w = ¬Nameø ∘ coerceᴺ w
