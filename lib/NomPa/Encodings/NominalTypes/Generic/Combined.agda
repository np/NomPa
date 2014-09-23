import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import NomPa.Encodings.NominalTypes
open import NomPa.Record
open import Function.NP
open import Data.List
open import Data.Product using (_,_)
open import Category.Applicative renaming (module RawApplicative to Applicative;
                                           RawApplicative to Applicative)

module NomPa.Encodings.NominalTypes.Generic.Combined (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa using (rm₀; _ᴺᴰ)
open NomPa.Traverse nomPa
open NomPa.Encodings.NominalTypes nomPa

infixr 1 _`⊎`_
infixr 2 _`×`_
data Universe : Set where
  `⊤` `⊥`    : Universe
  _`×`_ _`⊎`_ : (σ τ : Universe) → Universe
  `Rec`       : Universe
  `Name`      : Universe
  `Abs`       : (τ : Universe) → Universe

module Untyped where
 data T : 𝔼 where
  tt             : ∀ {α} → T α
  _,_            : ∀ {α} (t u : T α) → T α
  inj₁ inj₂ roll : ∀ {α} (t u : T α) → T α
  V              : Nameᵉ ↦ᵉ T
  bind           : Absᵉ T ↦ᵉ T

module |Untyped| where
 data T : 𝔼 where
  tt             : ∀ᵉ T
  _,_            : T ↦ᵉ T →ᵉ T
  inj₁ inj₂ roll : T ↦ᵉ T
  V              : Nameᵉ ↦ᵉ T
  bind           : Absᵉ T ↦ᵉ T

module Rec (r : Universe) where
 data ⟪_⟫ : Universe → 𝔼 where
  tt   : ∀ᵉ ⟪ `⊤` ⟫
  _,_  : ∀ {σ τ} → ⟪ σ ⟫ ↦ᵉ ⟪ τ ⟫ →ᵉ ⟪ σ `×` τ ⟫
  inj₁ : ∀ {σ τ} → ⟪ σ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
  inj₂ : ∀ {σ τ} → ⟪ τ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
  roll : ⟪ r ⟫ ↦ᵉ ⟪ `Rec` ⟫
  V    : Nameᵉ ↦ᵉ ⟪ `Name` ⟫
  bind : ∀ {τ} → Absᵉ ⟪ τ ⟫ ↦ᵉ ⟪ `Abs` τ ⟫

  bindᴰ : ∀ {τ} → Absᴰᵉ ⟪ τ ⟫ ↦ᵉ ⟪ `Abs` τ ⟫

open Rec using (tt; _,_; inj₁; inj₂; V; roll; bind; bindᴰ)
         renaming (⟪_⟫ to El)

⟪_⟫ : Universe → 𝔼
⟪ u ⟫ = Rec.⟪_⟫ u u

fv : ∀ {r s} → El r s ↦ᵉ (Listᵉ Nameᵉ)
fv tt        = []
fv (t , u)   = fv t ++ fv u
fv (inj₁ t)  = fv t
fv (inj₂ t)  = fv t
fv (roll t)  = fv t
fv (V x)     = [ x ]
fv (bind (b , t)) = rm b (fv t)
fv (bindᴰ t) = rm₀ (fv t)

module ToDeBruijn where
  Env : EnvType
  Env α β = Name α → Name β

  extEnvᴰ : ∀ {α β} → Env α β → Env (α ↑1) (β ↑1)
  extEnvᴰ = protect↑1

  extEnv : ∀ {α β} b → Env α β → Env (b ◅ α) (β ↑1)
  extEnv b Γ = exportWith (0 ᴺ) (sucᴺ↑ ∘′ Γ)

  tr : ∀ {r s α β} → Env α β → El r s α → El r s β
  tr Δ tt             = tt
  tr Δ (t , u)        = tr Δ t , tr Δ u
  tr Δ (inj₁ t)       = inj₁ $ tr Δ t
  tr Δ (inj₂ t)       = inj₂ $ tr Δ t
  tr Δ (roll t)       = roll $ tr Δ t
  tr Δ (bind (b , t)) = bindᴰ $ tr (extEnv b Δ) t
  tr Δ (bindᴰ t)      = bindᴰ $ tr (extEnvᴰ Δ) t
  tr Δ (V x)          = V $ Δ x

module Example where
  record TmA F : Set where
    constructor mk
    field
      var  : Nameᵉ ↦ᵉ F
      app  : (F ×ᵉ F) ↦ᵉ F
      lam  : Absᵉ F ↦ᵉ F
      lamᴰ : Absᴰᵉ F ↦ᵉ F

    _·_ : F ↦ᵉ F →ᵉ F
    _·_ t u = app (t , u)

    ƛ : ∀ {α} b → F (b ◅ α) → F α
    ƛ b t = lam (b , t)

    ƛᴰ : ∀ {α} → F (α ↑1) → F α
    ƛᴰ = lamᴰ

  TmU : Universe
  TmU = `Name` `⊎` (`Rec` `×` `Rec`) `⊎` (`Abs` `Rec`)

  Tm : 𝔼
  Tm = ⟪ TmU ⟫

  tmA : TmA Tm
  tmA = mk (inj₁ ∘′ V) app lam lamᴰ where
    app : (Tm ×ᵉ Tm) ↦ᵉ Tm
    app (t , u) = inj₂ (inj₁ (roll t , roll u))

    lam : Absᵉ Tm ↦ᵉ Tm
    lam (b , t) = inj₂ (inj₂ (bind (b , roll t)))

    lamᴰ : Absᴰᵉ Tm ↦ᵉ Tm
    lamᴰ t = inj₂ (inj₂ (bindᴰ (roll t)))

  open TmA tmA
  idTm : Tm ø
  idTm = ƛ (0 ᴮ) (var (0 ᴺ))

  apTm : Tm ø
  apTm = ƛ (0 ᴮ) (ƛ (1 ᴮ) (var (name◅… 1 0) · var (1 ᴺ)))

  idTmᴰ : Tm ø
  idTmᴰ = ƛᴰ (var (0 ᴺ))

  apTmᴰ : Tm ø
  apTmᴰ = ƛᴰ (ƛᴰ (var (1 ᴺᴰ) · var (0 ᴺᴰ)))

  fvTm : Tm ↦ᵉ Listᵉ Nameᵉ
  fvTm = fv

  dbTm : Tm ↦ᵉ Tm
  dbTm = ToDeBruijn.tr id

{-
  open import Relation.Binary.PropositionalEquality as ≡
  open import Data.Nat
  open import Data.Maybe

  coerce-sem : ∀ x {α β} (pf : α ↑(1 + x) ⊆ β ↑(1 + x))
               → coerceᴺ pf (x ᴺᴰ) ≡ x ᴺᴰ
  coerce-sem = {!!}

  exportᴺᴰ? : ℕ → ∀ {α} x → Maybe (Name ((α ↑ x)+1))
  exportᴺᴰ? = {!!}

  addᴺ0-sem : ∀ {α} x → addᴺ {α} 0 x ≡ x
  addᴺ0-sem = {!!}

  export-sem : ∀ {α} b x → exportᴺ? {α = (α ↑ x)+1} (x ᴺᴰ) ≡ exportᴺᴰ? b x
  export-sem = {!!}

  dbTm-ex : (pf₁ : _) (pf₂ : _) → dbTm apTm ≡ apTmᴰ 
  dbTm-ex pf₁ pf₂ = cong (ƛᴰ ∘ ƛᴰ)
                         (cong₂ _·_ (cong var pf₁) (cong var (trans {!trans ? (sym (coerce-sem 0 _))!} (cong (coerceᴺ _) (sym (addᴺ0-sem zeroᴺ))))))
-}
