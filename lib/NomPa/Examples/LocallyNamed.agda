open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Data.Maybe.NP as Maybe
open import Data.List
open import Data.Nat.NP as Nat using (ℕ; zero; suc; _+_)
open import Data.Bool
open import Data.Product.NP
open import Data.Atom
open import Data.String using (String)
open import Function.NP
open import NomPa.Record
import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps)
open import Coinduction
import NomPa.Derived
import NomPa.Traverse
import NomPa.Examples.LC

module NomPa.Examples.LocallyNamed (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa
module LCᴺ = NomPa.Examples.LC nomPa Atom (const "<atom>")
open LCᴺ using (V; _·_; ƛ; Let; `_) renaming (Tm to Tmᴺ)

mutual
  AbsPreTm = SynAbsᴺ PreTm

  -- Same as LN
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

module TraversePreTm {E}   (E-app : Applicative E)
                     {Env} (trKit : TrKit Env (E ∘ PreTm))
                           (trAtm : ∀ {α β} → Env α β → Atom → E (PreTm β)) where

  open Applicative E-app
  open TrKit trKit

  tr : ∀ {α β} → Env α β → PreTm α → E (PreTm β)
  tr Δ (Vᴬ x)          = trAtm Δ x
  tr Δ (Vᴺ x)          = trName Δ x
  tr Δ (t · u)         = pure _·_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (ƛ (b , t))     = pure (λ t → ƛ (_ , t)) ⊛ tr (extEnv b Δ) t
  tr Δ (Let t (b , u)) = pure (λ t u → Let t (_ , u)) ⊛ tr Δ t ⊛ tr (extEnv b Δ) u

module TraversePreTm′ {E}   (E-app : Applicative E)
                     {Env} (trKit : TrKit Env (E ∘ PreTm)) where
  open Applicative E-app
  open TraversePreTm E-app trKit (const (pure ∘ Vᴬ)) public

open TraverseAGen Vᴺ TraversePreTm′.tr
  public
  renaming (rename       to renamePreTm;
            rename?      to renamePreTm?;
            export?      to export?PreTm;
            close?       to closePreTm?;
            coerce       to coercePreTm;
            coerceø      to coerceøPreTm;
            renameCoerce to renameCoercePreTm;
            renameA      to renamePreTmA)

open SubstGen Vᴺ coercePreTm (TraversePreTm′.tr id-app)
  public
  renaming (subst to substPreTm; openSynAbsᴺ to openSubstTm)

module PreTm⇒Tmᴺ where
  ⟪_⟫ : ∀ {α} → PreTm α → Tmᴺ α
  ⟪ Vᴺ x          ⟫ = V x
  ⟪ Vᴬ a          ⟫ = ` a
  ⟪ t · u         ⟫ = ⟪ t ⟫ · ⟪ u ⟫
  ⟪ ƛ (b , t)     ⟫ = ƛ b ⟪ t ⟫
  ⟪ Let t (b , u) ⟫ = Let b ⟪ t ⟫ ⟪ u ⟫

showTm : Tm → String
showTm = LCᴺ.showTmø ∘ PreTm⇒Tmᴺ.⟪_⟫

module Tmᴺ⇒PreTm where
  ⟪_⟫ : ∀ {α} → Tmᴺ α → PreTm α
  ⟪ V x       ⟫ = Vᴺ x
  ⟪ t · u     ⟫ = ⟪ t ⟫ · ⟪ u ⟫
  ⟪ ƛ b t     ⟫ = ƛ (b , ⟪ t ⟫)
  ⟪ Let b t u ⟫ = Let ⟪ t ⟫ (b , ⟪ u ⟫)
  ⟪ ` a       ⟫ = Vᴬ a

parseTm? : String →? Tm
parseTm? = map? Tmᴺ⇒PreTm.⟪_⟫ ∘ LCᴺ.parseTmø?

parseTm : ∀ s {s-ok : LCᴺ.TmøOk s} → Tm
parseTm s {s-ok} = Tmᴺ⇒PreTm.⟪_⟫ (LCᴺ.parseTmø s {s-ok})

module FreeVarsPreTm where
  fa : ∀ {α} → PreTm α → List Atom
  fa (Vᴺ _)          = []
  fa (Vᴬ x)          = [ x ]
  fa (fct · arg)     = fa fct ++ fa arg
  fa (ƛ (_ , t))     = fa t
  fa (Let t (_ , u)) = fa t ++ fa u

-- openSubstTm : Tm → AbsTm → Tm
-- openSubstTm t (_ , u) = substPreTm (0 ˢ) (exportWith t Nameø-elim) u

{-
Env α β
  trName : Name α → Name β

Env α β → Env (b ◅ α) (b ◅ β)

s & α

t : Tm α
s = H t

α >>> s & α

∀ {α β} → α >>> β → Name α → Name β

∀ {α} s → Name α → Name (s & α)

α >>> β → (b ◅ α) >>> (b ◅ β)
-}

closeTm : Atom → Tm → AbsTm
closeTm a t = 0 ᴮ , tr (renameEnvˢ 1 , ⊆-refl) t where
  β₀ = _

  trAtm : ∀ {α β} → SubstEnv+⊆ Name β₀ α β → Atom → PreTm β
  trAtm Δ a′ = if a ==ᴬ a′ then Vᴺ (coerceᴺ (SubstEnv+⊆.pf Δ) (0 ᴺ)) else Vᴬ a′

  kit = mapKit id Vᴺ (renameKit+⊆ β₀)
  tr = TraversePreTm.tr id-app kit trAtm

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

substAtom : Atom → Tm → (Atom → Tm)
substAtom x t y = if x ==ᴬ y then t else Vᴬ y

β-red : (fuel atomSupply : ℕ) → Tm → Tm
β-red fuel s (ƛ abs · arg) = substTm fuel (suc s) (substAtom (s ᴬ) arg) (openTm (s ᴬ) abs)
β-red _    _ t             = t

β-red-openSubst : Tm → Tm
β-red-openSubst (ƛ abs · arg) = openSubstTm arg abs
β-red-openSubst t             = t

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
