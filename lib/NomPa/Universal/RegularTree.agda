open import NomPa.Record
import NomPa.Derived
import NomPa.Traverse
module NomPa.Universal.RegularTree (nomPa : NomPa) where

open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Function.NP
open import Data.List
open import Data.Bool
open import Data.Nat
open import Data.Indexed
open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa

data Any : World → Set where
  tt             : ∀ {α} → Any α
  _,_            : ∀ {α} (t u : Any α) → Any α
  inj₁ inj₂ roll : ∀ {α} (t : Any α) → Any α
  name           : ∀ {α} (x : Name α) → Any α
  ν              : ∀ {α} b (t : Any (b ◅ α)) → Any α

fv : ∀ {α} → Any α → List (Name α)
fv (name x) = [ x ]
fv (ν b t) = rm b (fv t)
fv tt = []
fv (t , u) = fv t ++ fv u
fv (inj₁ t) = fv t
fv (inj₂ t) = fv t
fv (roll t) = fv t

module CmpAny (Env : (α β : World) → Set)
              (cmpName : ∀ {α₁ α₂} → Env α₁ α₂ → Name α₁ → Name α₂ → Bool)
              (extend : ∀ {α₁ α₂} {b₁ b₂} → Env α₁ α₂ → Env (b₁ ◅ α₁) (b₂ ◅ α₂)) where

  cmpAny : ∀ {α₁ α₂} (Δ : Env α₁ α₂) → Any α₁ → Any α₂ → Bool
  cmpAny Δ (name x₁) (name x₂) = cmpName Δ x₁ x₂
  cmpAny Δ (ν b₁ t₁) (ν b₂ t₂) = cmpAny (extend Δ) t₁ t₂
  cmpAny Δ (t₁ , u₁) (t₂ , u₂) = cmpAny Δ t₁ t₂ ∧ cmpAny Δ u₁ u₂
  cmpAny Δ (inj₁ t₁) (inj₁ t₂) = cmpAny Δ t₁ t₂
  cmpAny Δ (inj₂ t₁) (inj₂ t₂) = cmpAny Δ t₁ t₂
  cmpAny Δ (roll t₁) (roll t₂) = cmpAny Δ t₁ t₂
  cmpAny _ tt        tt        = true
  cmpAny _ _         _         = false

open CmpAny (|Cmp| Name) id extendNameCmp public

_==Any_ : ∀ {α} → Any α → Any α → Bool
_==Any_ = cmpAny _==ᴺ_

module TraverseAny {E}   (E-app : Applicative E)
                   {Env} (trKit : TrKit Env (E ∘ Any)) where

  open Applicative E-app
  open TrKit trKit

  tr : ∀ {α β} → Env α β → Any α → E (Any β)
  tr Δ (name x)    = trName Δ x
  tr Δ (ν b t)     = pure (ν _) ⊛ tr (extEnv b Δ) t
  tr Δ (t , u)     = pure _,_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (inj₁ t)    = pure inj₁ ⊛ tr Δ t
  tr Δ (inj₂ t)    = pure inj₁ ⊛ tr Δ t
  tr Δ (roll t)    = pure inj₁ ⊛ tr Δ t
  tr _ tt          = pure tt

open TraverseAGen name TraverseAny.tr
  public
  renaming (rename       to renameAny;
            rename?      to renameAny?;
            export?      to exportAny?;
            close?       to closeAny?;
            coerce       to coerceAny;
            coerceø      to coerceøAny;
            renameCoerce to renameCoerceAny;
            renameA      to renameAnyA)

open SubstGen name coerceAny (TraverseAny.tr id-app)
  public
  renaming (subst to substAny;
            substøᴮ to substøᴮAny;
            substC to substCAny;
            substCø to substCøAny;
            substCᴮ to substCᴮAny;
            substCøᴮ to substCøᴮAny;
            openSynAbsᴺ to openSubstAny)

tag_,_ : ∀ {α} → ℕ → Any α → Any α
tag_,_ zero    = inj₁
tag_,_ (suc n) = tag_,_ n ∘ inj₂

module AnyTm where
  V′ : ∀ {α} → Name α → Any α
  V′ x = tag 0 , name x

  _·′_ : ∀ {α} (t u : Any α) → Any α
  t ·′ u = tag 1 , (roll t , roll u)

  ƛ′ : ∀ {α} b (t : Any (b ◅ α)) → Any α
  ƛ′ b t = tag 2 , ν b (roll t)

  Let′ : ∀ {α} b (t : Any α) (u : Any (b ◅ α)) → Any α
  Let′ b t u = tag 3 , (roll t , ν b (roll u))
