open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Data.Maybe.NP as Maybe
open import Data.List
open import Data.Nat.NP as Nat using (ℕ; zero; suc; _+_)
open import Data.Bool
open import Data.Atom
open import Function.NP
open import NomPa.Record
import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps)
open import Coinduction
import NomPa.Derived
import NomPa.Derived.NaPa

module NomPa.Examples.LN (nomPa : NomPa) where

open NomPa nomPa hiding (_◅_; Binder)
open NomPa.Derived nomPa hiding (Supply)
open NomPa.Derived.NaPa nomPa

{-
data PreTm α : Set where
  Vᴺ   : (x : Name α) → PreTm α
  Vᴬ   : (x : Atom) → PreTm α
  _·_  : (t u : PreTm α) → PreTm α
  ƛ    : (t : PreTm (α ↑1)) → PreTm α
  Let  : (t : PreTm α) (u : PreTm (α ↑1)) → PreTm α
-}

mutual
  AbsPreTm = SynAbsᴰ PreTm

  -- Same as LocallyNamed
  data PreTm α : Set where
    Vᴺ   : (x : Name α) → PreTm α
    Vᴬ   : (x : Atom) → PreTm α
    _·_  : (t u : PreTm α) → PreTm α
    ƛ    : (t : AbsPreTm α) → PreTm α
    Let  : (t : PreTm α) (u : AbsPreTm α) → PreTm α

-- Locally closed terms
Tm : Set
Tm = PreTm ø

-- Locally closed abstracted terms
AbsTm : Set
AbsTm = AbsPreTm ø

module TraversePreTm {E} (E-app : Applicative E)
                     {α β} (trName : Su↑ Name (E ∘ PreTm) α β) where
  open Applicative E-app

  ! : Su↑ PreTm (E ∘ PreTm) α β
  ! _ (Vᴬ x)     = pure $ Vᴬ x
  ! ℓ (Vᴺ x)     = trName ℓ x
  ! ℓ (t · u)    = _·_ <$> ! ℓ t ⊛ ! ℓ u
  ! ℓ (ƛ t)      = ƛ   <$> ! (suc ℓ) t
  ! ℓ (Let t u)  = Let <$> ! ℓ t ⊛ ! (suc ℓ) u

open TraverseAFGGGen {PreTm} PreTm.Vᴺ TraversePreTm.! public
  renaming ( renameA   to renameAPreTm
           ; rename    to renamePreTm
           ; shift     to shiftPreTm
           ; coerceø   to coerceøPreTm
           ; coerce    to coercePreTm
           ; subtract? to subtractPreTm?
           ; close?    to closePreTm?
           )

open SubstGen {PreTm} Vᴺ shiftPreTm (TraversePreTm.! id-app) public
  renaming ( substVarG to substVarPreTm
           ; subst to substPreTm )


module FreeVarsPreTm where
  fa : ∀ {α} → PreTm α → List Atom
  fa (Vᴺ _)      = []
  fa (Vᴬ x)      = [ x ]
  fa (fct · arg) = fa fct ++ fa arg
  fa (ƛ t)       = fa t
  fa (Let t u)   = fa t ++ fa u

closeTm : Atom → Tm → AbsTm
closeTm a t = ! (0 ᴺ) (coerceøPreTm t) where
  ! : ∀ {α} → Name α → PreTm α → PreTm α
  ! y (Vᴬ x)    = if x ==ᴬ a then Vᴺ y else Vᴬ x
  ! y (Vᴺ x)    = Vᴺ x
  ! y (t · u)   = ! y t · ! y u
  ! y (ƛ t)     = ƛ (! (sucᴺ↑ y) t)
  ! y (Let t u) = Let (! y t) (! (sucᴺ↑ y) u)

openSubstTm : Tm → AbsTm → Tm
openSubstTm t = substPreTm (exportWith t (Name-elim ø+1⊆ø))

-- STARTING FROM HERE THIS IS THE EXACT SAME CODE AS WITH:
-- NomPa.Examples.LocallyNamed

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
