open import NomPa.Record
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import Data.Indexed
open import Function.NP
open import Data.Product.NP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
import NomPa.Encodings.NominalTypes.MultiSorts as NomSig

module NomPa.Encodings.NominalTypes.MultiSorts.Test where

module Client₁ (nomPa : NomPa) where

{- A Nominal Signature:
   Extended from example 2.2 in «Nominal Unification»

sort of atoms: vtm vty
sort of data:  Tm Ty

function symbols:

  var : vty → Ty
  arr : Ty × Ty → Ty
  all : <vty>Ty → Ty

  vr  : vtm → Tm
  app : Tm × Tm → Tm
  fn  : Ty × <vtm>Tm → Tm
  App : Tm × Ty → Tm
  Fn  : <vty>Tm → Tm
-}

  data Sort : Set where
    vtm vty : Sort

  _==_ : (x y : Sort) → Bool
  vtm == vtm = true
  vty == vty = true
  vtm == vty = false
  vty == vtm = false

  open NomSig nomPa Sort _==_
  |E = 𝔼

  data Ty : |E where
    var : Nameᵉ vty ↦ᵉ Ty
    arr : Ty ×ᵉ Ty ↦ᵉ Ty
    all : < vty >ᵉ Ty ↦ᵉ Ty

  data Tm : |E where
    vr  : Nameᵉ vtm ↦ᵉ Tm
    app : Tm ×ᵉ Tm ↦ᵉ Tm
    fn  : Ty ×ᵉ < vtm >ᵉ Tm ↦ᵉ Tm
    App : Tm ×ᵉ Ty ↦ᵉ Tm
    Fn  : < vty >ᵉ Tm ↦ᵉ Tm

  open NomPa.Derived nomPa

  fvtmTm : Tm ↦ᵉ Listᵉ (Nameᵉ vtm)
  fvtmTm (vr x) = [ x ]
  fvtmTm (app (t , u)) = fvtmTm t ++ fvtmTm u
  fvtmTm (fn (_ , b , t)) = rm b (fvtmTm t)
  fvtmTm (App (t , τ)) = fvtmTm t
  fvtmTm (Fn (b , t)) = fvtmTm t -- no b to remove

  fvtyTy : Ty ↦ᵉ Listᵉ (Nameᵉ vty)
  fvtyTy (var x) = [ x ]
  fvtyTy (arr (σ , τ)) = fvtyTy σ ++ fvtyTy τ
  fvtyTy (all (b , τ)) = rm b (fvtyTy τ)

  fvtyTm : Tm ↦ᵉ Listᵉ (Nameᵉ vty)
  fvtyTm (vr x) = []
    -- [ x ] would not type-check
  fvtyTm (app (t , u)) = fvtyTm t ++ fvtyTm u
  fvtyTm (fn (τ , b , t)) = fvtyTy τ ++ fvtyTm t
    -- «rm b …» would not type-check
  fvtyTm (App (t , τ)) = fvtyTm t ++ fvtyTy τ
  fvtyTm (Fn (b , t)) = rm b (fvtyTm t)
