import NomPa.Derived
import NomPa.Traverse
import NomPa.Encodings.NominalTypes
open import NomPa.Record
open import Function.NP
open import Data.List
open import Data.Product using (_,_)
open import Category.Applicative renaming (module RawApplicative to Applicative;
                                           RawApplicative to Applicative)

module NomPa.Encodings.NominalTypes.Generic.Subst (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa
open NomPa.Encodings.NominalTypes nomPa

infixr 1 _`⊎`_
infixr 2 _`×`_
data Universe : Set where
  `⊤` `⊥`    : Universe
  _`×`_ _`⊎`_ : (σ τ : Universe) → Universe
  `Rec`       : Universe
  `Abs`       : (τ : Universe) → Universe

module Rec (r : Universe) where
 data ⟪_⟫ : Universe → 𝔼 where
  tt   : ∀ᵉ ⟪ `⊤` ⟫
  _,_  : ∀ {σ τ} → ⟪ σ ⟫ ↦ᵉ ⟪ τ ⟫ →ᵉ ⟪ σ `×` τ ⟫
  inj₁ : ∀ {σ τ} → ⟪ σ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
  inj₂ : ∀ {σ τ} → ⟪ τ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
  roll : ⟪ r ⟫ ↦ᵉ ⟪ `Rec` ⟫
  V    : Nameᵉ ↦ᵉ ⟪ r ⟫
  bind : ∀ {τ} → Absᵉ ⟪ τ ⟫ ↦ᵉ ⟪ `Abs` τ ⟫

-- ^^^
-- like in NominalTypes but uses r instead of `Name` in the return type of V

open Rec using (tt; _,_; inj₁; inj₂; V; bind; roll) renaming (⟪_⟫ to El)

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

module TraverseEl r
                  {E}   (E-app : Applicative E)
                  {Env} (trKit : TrKit Env (E ∘ El r r)) where

  open Applicative E-app
  open TrKit trKit

  tr : ∀ {s α β} → Env α β → El r s α → E (El r s β)
  tr Δ tt            = pure tt
  tr Δ (t , u)       = pure _,_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (inj₁ t)      = pure inj₁ ⊛ tr Δ t
  tr Δ (inj₂ t)      = pure inj₂ ⊛ tr Δ t
  tr Δ (roll t)      = pure roll ⊛ tr Δ t
  tr Δ (bind(b , t)) = pure (bind ∘ _,_ _) ⊛ tr (extEnv b Δ) t
  tr Δ (V x)         = trName Δ x

  tr′ : ∀ {α β} → Env α β → ⟪ r ⟫ α → E (⟪ r ⟫ β)
  tr′ = tr

module Generic r where
  F = ⟪ r ⟫
  G = ⟪ r ⟫

  traverseAFGG : TraverseA F G G
  traverseAFGG = TraverseEl.tr′ r

  traverseFGG : Traverse F G G
  traverseFGG = traverseAFGG id-app

  traverseAFGName : TraverseA F G Name
  traverseAFGName E-app trKit = TraverseEl.tr′ r E-app (mapKit id (_<$>_ V) trKit)
     where open Applicative E-app

  open TraverseAFGNameGen traverseAFGName public

  open SubstGen {F} {G} V coerce traverseFGG public

module Example where
  record TmA F : Set where
    constructor mk
    field
      var : Nameᵉ ↦ᵉ F
      app : (F ×ᵉ F) ↦ᵉ F
      lam : Absᵉ F ↦ᵉ F

    _·_ : F ↦ᵉ F →ᵉ F
    _·_ t u = app (t , u)

    ƛ : ∀ {α} b → F (b ◅ α) → F α
    ƛ b t = lam (b , t)

{-
  -- base functor
  TmF : 𝔼 → 𝔼
  TmF F =  Nameᵉ
        ⊎ᵉ F ×ᵉ F
        ⊎ᵉ Absᵉ F
-}

  TmU : Universe
  TmU = (`Rec` `×` `Rec`) `⊎` (`Abs` `Rec`)

  Tm : 𝔼
  Tm = ⟪ TmU ⟫

  tmA : TmA Tm
  tmA = mk V app lam where
    app : (Tm ×ᵉ Tm) ↦ᵉ Tm
    app (t , u) = inj₁ (roll t , roll u)

    lam : Absᵉ Tm ↦ᵉ Tm
    lam (b , t) = inj₂ (bind (b , roll t))

  open TmA tmA
  idTm : Tm ø
  idTm = ƛ (0 ᴮ) (V (0 ᴺ))

  apTm : Tm ø
  apTm = ƛ (0 ᴮ) (ƛ (1 ᴮ) (V (name◅… 1 0) · V (1 ᴺ)))

  fvTm : Tm ↦ᵉ Listᵉ Nameᵉ
  fvTm = fv

  open Generic
    renaming (rename       to renameTm;
              rename?      to renameTm?;
              export?      to exportTm?;
              close?       to closeTm?;
              coerce       to coerceTm;
              coerceø      to coerceTmø;
              renameCoerce to renameCoerceTm;
              renameA      to renameTmA;
              subst        to substTm;
              substøᴮ      to substøᴮTm;
              substC       to substCTm;
              substCø      to substCøTm;
              substCᴮ      to substCᴮTm;
              substCøᴮ     to substCøᴮTm;
              openSynAbsᴺ  to openSubstTm)
