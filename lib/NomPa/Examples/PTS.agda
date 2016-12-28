open import NomPa.Record
module NomPa.Examples.PTS (nomPa : NomPa) (Sort : Set) where

open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import  Data.List using (List; []; _∷_; map)
open import  Data.Bool
open import  Data.Maybe.NP using (Maybe; nothing; just; maybe; maybe′; applicative)
open import  Data.Product.NP using (_×_; _,_ ; fst ; snd)
open import  Data.Star using (Star; ε) renaming (_◅_ to _∷_)
open import  Function.NP hiding (Π)
open import  Relation.Nullary
open import  Relation.Nullary.Decidable hiding (map)
open import  Relation.Binary hiding (_⇒_)
import       Relation.Binary.PropositionalEquality as ≡
open         ≡ using (_≡_)
import  Level as L
import       NomPa.Derived
import       NomPa.Traverse

open         NomPa nomPa
open         NomPa.Derived nomPa
open         NomPa.Traverse nomPa

mutual
  data Tm α : Set where
    V               : ∀ (x : Name α) → Tm α
    ƛ⟨_∶_⟩_         : ∀ b (τ : Ty α) (t : Tm (b ◅ α)) → Tm α
    _·_             : ∀ (t u : Tm α) → Tm α
    Π⟨_∶_⟩_         : ∀ b (σ : Ty α) (τ : Ty (b ◅ α)) → Tm{-Ty-} α
    `_              : ∀ (s : Sort) → Tm{-Ty-} α

  Ty : World → Set
  Ty = Tm

infixl 5 _·_
-- infix 2 Π ƛ
-- this triggers an Agda bug in PTS.F
-- syntax Π b σ τ = Π⟨ b ∶ σ ⟩ τ
-- syntax ƛ b σ t = ƛ⟨ b ∶ σ ⟩ t

module TraverseTm {E}   (E-app : Applicative E)
                  {Env} (trKit : TrKit Env (E ∘ Tm)) where

  open Applicative E-app
  open TrKit trKit

  tr : ∀ {α β} → Env α β → Tm α → E (Tm β)
  tr Δ (V x)           = trName Δ x
  tr Δ (t · u)         = pure _·_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (ƛ⟨ b ∶ τ ⟩ t)  = pure (ƛ⟨_∶_⟩_ _) ⊛ tr Δ τ ⊛ tr (extEnv b Δ) t
  tr Δ (Π⟨ b ∶ σ ⟩ τ) = pure (Π⟨_∶_⟩_ _) ⊛ tr Δ σ ⊛ tr (extEnv b Δ) τ
  tr Δ (` κ)           = pure $ ` κ

open TraverseAGen V TraverseTm.tr
  public
  renaming (rename       to renameTm;
            rename?      to renameTm?;
            export?      to exportTm?;
            close?       to closeTm?;
            coerce       to coerceTm;
            coerceø      to coerceTmø;
            renameCoerce to renameCoerceTm;
            renameA      to renameTmA)

open SubstGen V coerceTm (TraverseTm.tr id-app)
  public
  renaming (subst to substTm;
            substøᴮ to substøᴮTm;
            substC to substCTm;
            substCø to substCøTm;
            substCᴮ to substCᴮTm;
            substCøᴮ to substCøᴮTm;
            openSynAbsᴺ to openSubstTm)

-- not used
data Tel α : World → Set where
  ε       : Tel α α
  ⟨_∶_⟩→_ : ∀ {β} b
              (τ : Ty α)
              (Γ : Tel (b ◅ α) β)
            → Tel α β

infixl 5 _,,_∶_

data Cx α : World → Set where
  ε      : Cx α α
  _,,_∶_ : ∀ {β b}
             (Γ : Cx α β)
             (b# : b # β)
             (τ : Ty β)
           → Cx α (b ◅ β)

module Lookup where
  open Applicative {L.zero} (applicative _)
  lookup : ∀ {ω α} (x : Name α) (Γ : Cx ω α) → Maybe (Ty α)
  lookup x ε = nothing
  lookup x (Γ ,, b# ∶ τ) = coerceTm (⊆-# b#) <$> (exportWith (just τ) (λ x' → lookup x' Γ)) x

open Lookup public

impTmWith : ∀ {b α} → b # α → Tm α → Tm (b ◅ α)
impTmWith = coerceTm ∘ ⊆-#

module Member where

 data ⟨_∶_⟩∈_ {ω} : ∀ {α} (x : Name α) (τ : Ty α) (Γ : Cx ω α) → Set where

  here' : ∀ {β b} {x : Name (b ◅ β)} {τ : Ty (b ◅ β)} {b# : b # β} {τ' Γ}
           (x≅b   : x ≡ nameᴮ b)
           (τ≅τ' : τ ≡ impTmWith b# τ')
         →         -----------------------
                   ⟨ x ∶ τ ⟩∈ (Γ ,, b# ∶ τ')

  there : ∀ {β b} {x : Name (b ◅ β)} {τ : Ty (b ◅ β)} {b# : b # β} {x' τ' σ Γ}
            (expOk : exportᴺ? x ≡ just x'       )
            (τ≅τ' :  τ ≡ impTmWith b# τ'      )
            (x∶τ∈Γ : ⟨ x' ∶ τ' ⟩∈ Γ            )
          →          --------------------------
                     ⟨ x ∶ τ ⟩∈ (Γ ,, b# ∶ σ)

 here : ∀ {ω β b τ} {b# : b # β} {Γ : Cx ω β}
        → ⟨ nameᴮ b ∶ impTmWith b# τ ⟩∈ (Γ ,, b# ∶ τ)
 here = here' ≡.refl ≡.refl

open Member public

{-
data Cx α : World → Set where
  ε     : Cx α α
  _,_∶_ : ∀ {β γ}
            (Γ : Cx α β)
            (τ : Ty β)
          → Cx α (β ^¹)

data Cx α : World → Set where
  ε     : Cx α (α ^ zero)
  _,_∶_ : ∀ {k}
            (Γ : Cx α (α ^ k))
            (τ : Ty (α ^ k))
          → Cx α (α ^ suc k)

data Cx α : ℕ → Set where
  ε     : Cx α zero
  _,_∶_ : ∀ {k}
            (Γ : Cx α k)
            (τ : Ty (α ^ k))
          → Cx α (suc k)

data Cx (F : ℕ → Set) : ℕ → Set where
  ε     : Cx F zero
  _,_∶_ : ∀ {k}
            (Γ : Cx F k)
            (τ : F k)
          → Cx F (suc k)

Cx α n = CX (λ k → Ty (α ^ k))
-}


_[_≔_] : ∀ {α b} → Tm (b ◅ α) → b # α → Tm α → Tm α
t [ b# ≔ u ] = substTm (_ , b#) (exportWith u V) t

infixr 40 ⟨_∶_⟩⇒_
⟨_∶_⟩⇒_ : ∀ {α} (s : Supply α) (τ σ : Ty α) → Ty α
⟨_∶_⟩⇒_ (b , b#) σ τ = Π⟨ b ∶ σ ⟩(coerceTm (⊆-# b#) τ)

module Typing
    (_∶κ_      : (s₁ s₂ : Sort) → Set)
    (⟨_,_,_⟩∈R : (s₁ s₂ s₃ : Sort) → Set)
  where

  infix 2 _⊢_∶_

  data _⊢_∶_ {α} (Γ : Cx ø α) : Tm α → Ty α → Set where

    V : ∀ {x τ}
          (x∈Γ : ⟨ x ∶ τ ⟩∈ Γ)
        →        -------------
                  Γ ⊢ V x ∶ τ

    ƛ⟨_∶_⟩_ : ∀ {b σ τ s t} (b# : b # α)
          (⊢Π : Γ ⊢ Π⟨ b ∶ σ ⟩ τ ∶ ` s          )
          (⊢t : (Γ ,, b# ∶ σ) ⊢ t ∶ τ            )
         →      ----------------------------------
                 Γ ⊢ ƛ⟨ b ∶ σ ⟩ t ∶ Π⟨ b ∶ σ ⟩ τ

    _·_  : ∀ {b σ τ s t u} {b# : b # α}
             (⊢Π : Γ ⊢ Π⟨ b ∶ σ ⟩ τ ∶ ` s   )
             (⊢t : Γ ⊢ t ∶ Π⟨ b ∶ σ ⟩ τ      )
             (⊢u : Γ ⊢ u ∶ σ                 )
           →       ---------------------------
                    Γ ⊢ t · u ∶ τ [ b# ≔ σ ]

    Π : ∀ {b σ τ s₁ s₂ s₃} (b# : b # α)
           (s∈ : ⟨ s₁ , s₂ , s₃ ⟩∈R         )
           (⊢σ : Γ ⊢ σ           ∶ ` s₁    )
           (⊢τ : (Γ ,, b# ∶ σ) ⊢ τ ∶ ` s₂  )
         →      -----------------------------
                  Γ ⊢ Π⟨ b ∶ σ ⟩ τ ∶ ` s₃

    `_ : ∀ {s₁ s₂}
           (s₁∶s₂ : s₁ ∶κ s₂        )
         →       ------------------
                   Γ ⊢ ` s₁ ∶ ` s₂

  syntax Π b# s∈ ⊢σ ⊢τ = Π⟨ b# ∶ ⊢σ ⟩⟨ s∈ ⟩ ⊢τ
  -- syntax ƛ b σ t = ƛ⟨ b ∶ σ ⟩ t
