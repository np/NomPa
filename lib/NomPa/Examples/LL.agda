open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Data.Maybe.NP as Maybe
open import Data.List
open import Data.Nat.NP as Nat using (ℕ; zero; suc; _+_)
open import Data.Bool
open import Data.Product.NP
open import Data.Atom
open import Function
open import NomPa.Record
import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps)
open import Coinduction
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import NomPa.Examples.LC.DbLevels
import NomPa.Examples.LC
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module NomPa.Examples.LL (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa
open NomPa.Traverse nomPa
open NomPa.Examples.LC.DbLevels nomPa Atom (const "<atom>") _==ᴬ_
  public
  using (ƛ; _·_; Let; _[0≔_])
  renaming (Tmᴸ to PreTm; V to Vᴺ; `_ to Vᴬ; shiftTmᴸ to shiftPreTm; shiftøTmᴸ to shiftøPreTm;
            coerceTmᴸ to coercePreTm)

AbsPreTm = SynAbsᴸ PreTm
{-
mutual
  AbsPreTm = SynAbsᴸ PreTm

  data PreTm b α : Set where
    Vᴺ   : (x : Name α) → PreTm b α
    Vᴬ   : (x : Atom) → PreTm b α
    _·_  : (t u : PreTm b α) → PreTm b α
    ƛ    : (t : AbsPreTm b α) → PreTm b α
    Let  : (t : PreTm b α) (u : AbsPreTm b α) → PreTm b α
-}

-- Locally closed terms
Tm : Set
Tm = PreTm (0 ᴮ) ø

-- Locally closed abstracted terms
AbsTm : Set
AbsTm = AbsPreTm (0 ᴮ) ø

module FreeVarsPreTm where
  fa : ∀ {b α} → PreTm b α → List Atom
  fa (Vᴺ _)      = []
  fa (Vᴬ x)      = [ x ]
  fa (fct · arg) = fa fct ++ fa arg
  fa (ƛ t)       = fa t
  fa (Let t u)   = fa t ++ fa u

openSubstTm : Tm → AbsTm → Tm
openSubstTm v t = t [0≔ v ]

closeTm : Atom → Tm → AbsTm
closeTm a t = closePreTm (0 ᴮ #ø) t where
  closePreTm : ∀ {b α} → b # α → PreTm b α → PreTm (b +ᴮ 1) (b ◅ α)
  closePreTm pf (Vᴺ x)    = Vᴺ (coerceᴺ (⊆-# pf) x)
  closePreTm _  (Vᴬ x)    = if a ==ᴬ x then Vᴺ (nameᴮ _) else Vᴬ x
  closePreTm pf (t · u)   = closePreTm pf t · closePreTm pf u
  closePreTm pf (ƛ t)     = ƛ (closePreTm (suc# pf) t)
  closePreTm pf (Let t u) = Let (closePreTm pf t) (closePreTm (suc# pf) u)

-- STARTING FROM HERE THIS IS THE EXACT SAME CODE AS WITH:
-- NomPa.Examples.LN

openTm : Atom → AbsTm → Tm
openTm = openSubstTm ∘ Vᴬ

mapAbsTm : Atom → (Tm → Tm) → AbsTm → AbsTm
mapAbsTm s f = closeTm s ∘ f ∘ openTm s

appⁿ : Tm → List Tm → Tm
appⁿ = foldl _·_

ƛ′ : Atom → Tm → Tm
ƛ′ x t = ƛ (closeTm x t)

let′ : Atom → Tm → Tm → Tm
let′ x t u = Let t (closeTm x u)

idᵀ : Tm
idᵀ = ƛ′ x (Vᴬ x)
  where x = 0 ᴬ

falseᵀ : Tm
falseᵀ = ƛ′ x (ƛ′ x (Vᴬ x))
  where x = 0 ᴬ

trueᵀ : Tm
trueᵀ = ƛ′ x (ƛ′ y (Vᴬ x))
  where x = 0 ᴬ
        y = 1 ᴬ

apᵀ : Tm
apᵀ = ƛ′ x (ƛ′ y (Vᴬ x · Vᴬ y))
  where x = 0 ᴬ
        y = 1 ᴬ

Ωᵀ : Tm
Ωᵀ = let′ δ (ƛ′ x (Vᴬ x · Vᴬ x))
            (Vᴬ δ · Vᴬ δ)
  where δ = 0 ᴬ
        x = 1 ᴬ

module Size where
  {-
  size : Tm → ℕ
  size (Vᴬ _)      = 1
  size (fct · arg) = 1 + size fct + size arg
  size (ƛ abs)     = 1 + size (openTm (0 ᴬ) abs)
  size (Let t abs) = 1 + size t + size (openTm (0 ᴬ) abs)
  size (Vᴺ x)      = Nameø-elim x
  -}

  -- ``fuel-extended'' to pass the termination checker
  size : (fuel : ℕ) → Tm → ℕ
  size (suc n) (Vᴬ _)      = 1
  size (suc n) (fct · arg) = 1 + size n fct + size n arg
  size (suc n) (ƛ abs)     = 1 + size n (openTm (0 ᴬ) abs)
  size (suc n) (Let t abs) = 1 + size n t + size n (openTm (0 ᴬ) abs)
  size (suc n) (Vᴺ x)      = Nameø-elim x
  size 0       _           = 0 -- dummy

module FreeVarsTm where
  -- ``fuel-extended'' to pass the termination checker
  fa : (fuel atomSupply : ℕ) → Tm → List Atom
  fa (suc n) _ (Vᴺ x)      = Nameø-elim x
  fa (suc n) _ (Vᴬ x)      = [ x ]
  fa (suc n) s (fct · arg) = fa n s fct ++ fa n s arg
  fa (suc n) s (ƛ abs)     = rmᴬ (s ᴬ) (fa n (1 + s) (openTm (s ᴬ) abs))
  fa (suc n) s (Let t abs) = fa n s t ++ rmᴬ (s ᴬ) (fa n (1 + s) (openTm (s ᴬ) abs))
  fa 0       _ _           = [] -- dummy

substTm : (fuel atomSupply : ℕ) → (Atom → Tm) → Tm → Tm
substTm fuel s Φ = ! fuel s where
  ! : (fuel atomSupply : ℕ) → Tm → Tm
  ! 0 s _ = Vᴬ (s ᴬ) -- dummy
  ! (suc n) s tm with tm
  ... | Vᴬ x      = Φ x
  ... | Vᴺ x      = Vᴺ x
  ... | t · u     = ! n s t · ! n s u
  ... | ƛ abs     = ƛ (mapAbsTm (s ᴬ) (! n (1 + s)) abs)
  ... | Let t abs = Let (! n s t) (mapAbsTm (s ᴬ) (! n (1 + s)) abs)

module KAM where -- Krivine Abstract Machine
  open Pa using (now; later; never)

  Stack = List Tm

  _★_ : Tm → Stack → Tm ⊥
  (t · u)     ★ π        = t ★ (u ∷ π)                       -- push
  (ƛ abs)     ★ (u ∷ π)  = later (♯ (openSubstTm u abs ★ π)) -- grab
  (Let t abs) ★ π        = later (♯ (openSubstTm t abs ★ π))
  v           ★ []       = now v
  (Vᴺ x)      ★ _        = Nameø-elim x
  (Vᴬ x)      ★ _        = never -- we have no static means to prevent this case
