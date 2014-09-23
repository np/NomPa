open import NomPa.Record
open import NomPa.Laws
open import Data.Maybe.NP
open import Data.Product
open import Data.Nat
import NomPa.Examples.PTS as PTS
import NomPa.Derived
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module NomPa.Examples.PTS.F (nomPa : NomPa) (laws : Laws nomPa) where

open Laws laws

data Sort : Set where
  ★ ∎ : Sort

data _∶κ_ : (s₁ s₂ : Sort) → Set where
  ★∶∎ : ★ ∶κ ∎

data ⟨_,_,_⟩∈R : (s₁ s₂ s₃ : Sort) → Set where
  `→` : ⟨ ★ , ★ , ★ ⟩∈R
  `∀` : ⟨ ∎ , ★ , ★ ⟩∈R

open NomPa nomPa
open NomPa.Derived nomPa
open PTS nomPa Sort
open Typing _∶κ_ ⟨_,_,_⟩∈R

∀⟨_⟩_ : ∀ {α} b → Ty (b ◅ α) → Ty α
∀⟨_⟩_ b τ = Π⟨ b ∶ ` ★ ⟩ τ

Λ⟨_⟩_ : ∀ {α} b → Tm (b ◅ α) → Tm α
Λ⟨_⟩_ b t = ƛ⟨ b ∶ ` ★ ⟩ t

there' : ∀ {b ω α} {b# : b # α} {x τ σ} {Γ : Cx ω α}
           (x∶τ∈Γ : ⟨ x ∶ τ ⟩∈ Γ                                              )
         →         ----------------------------------------------------------
                   ⟨ coerceᴺ (⊆-# b#) x ∶ impTmWith b# τ ⟩∈ (Γ ,, b# ∶ σ)
there' x = there (exportᴺ?∘coerceᴺ-success _) ≡.refl x

V′ : ∀ b {α} → Tm (b ◅ α)
V′ b = V (nameᴮ b)

V` : ∀ k x {α} → Tm ((k + x) ◅… α)
V` k x = V (name◅… k x)

V₀ = V` 0
V₁ = V` 1
V₂ = V` 2
V₃ = V` 3
V₄ = V` 4
V₅ = V` 5
V₆ = V` 6
V₇ = V` 7
V₈ = V` 8

module IdentityExample where

  A = 0 ᴮ
  A# = #-◅…′ø 0
  x = 1 ᴮ
  xˢ = 1 ˢ
  x# = #-◅…′ø 1

  idT : Tm ø
  idT = Λ⟨ A ⟩ ƛ⟨ x ∶ V′ A ⟩ V′ x

  idτ : Ty ø
  idτ = ∀⟨ A ⟩ ⟨ xˢ ∶ V′ A ⟩⇒ V′ A

  idτ∶★′ : ε ,, A# ∶ ` ★ ⊢ ⟨ xˢ ∶ V′ A ⟩⇒ V′ A ∶ ` ★
  idτ∶★′ = Π⟨ x# ∶ V here ⟩⟨ `→` ⟩ (V (there' here))

  idτ∶★ : ε ⊢ idτ ∶ ` ★
  idτ∶★ = Π⟨ A# ∶ ` ★∶∎ ⟩⟨ `∀` ⟩ idτ∶★′

  idT∶idτ : ε ⊢ idT ∶ idτ
  idT∶idτ = ƛ⟨ A# ∶ idτ∶★ ⟩ ƛ⟨ x# ∶ idτ∶★′ ⟩(V here)

module AppExample where

  _# : ∀ x → x ᴮ # x ◅…′ ø
  _# = #-◅…′ø

  A = 0
  B = 1
  f = 2
  x = 3

  -- « Λ A B → λ (f : A → B) (x : A) → f x »
  apT : Tm ø
  apT = Λ⟨ A ᴮ ⟩ Λ⟨ B ᴮ ⟩ ƛ⟨ f ᴮ ∶ ⟨ 2 ˢ ∶ V₁ A ⟩⇒ V₀ B ⟩ ƛ⟨ x ᴮ ∶ V₂ A ⟩ (V₁ f · V₀ x)

  -- « ∀ A B → (A → B) → A → B »
  apτ : Tm ø
  apτ = ∀⟨ A ᴮ ⟩ ∀⟨ B ᴮ ⟩ ⟨ 2 ˢ ∶ ⟨ 2 ˢ ∶ V₁ A ⟩⇒ V₀ B ⟩⇒ ⟨ 2 ˢ ∶ V₁ A ⟩⇒ V₀ B

{-
  apτ∶★ : ε ⊢ apτ ∶ ` ★
  apτ∶★ = Π⟨ A # ∶ ` ★∶∎ ⟩⟨ `∀` ⟩
           Π⟨ B # ∶ ` ★∶∎ ⟩⟨ `∀` ⟩
           Π⟨ f # ∶ Π⟨ 2 # ∶ V pf₁ ⟩⟨ `→` ⟩ V pf₂ ⟩⟨ `→` ⟩
           Π⟨ {!x #!} ∶ V (there {!!} {!!} {!!}) ⟩⟨ `→` ⟩ V {!!}
    where pf₁ = there (exportᴺ?∘coerceᴺ-success _) ≡.refl here
          pf₂ = there (≡.trans (≡.cong exportᴺ? (coerceᴺ∘coerceᴺ _)) (exportᴺ?∘coerceᴺ-success _)) ≡.refl here
-}
