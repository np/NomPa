open import Data.String
open import Data.Nat
open import Data.Bool
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import NomPa.Examples.Raw
open NomPa.Examples.Raw.DataType String

module NomPa.Examples.Raw.Printer where

ShowS : Set
ShowS = String → String

Pr : Set → Set
Pr A = A → ShowS

`_ : String → ShowS
(` s) tail = Data.String._++_ s tail

parenBase : ShowS → ShowS
parenBase doc = ` "(" ∘ doc ∘ ` ")"

record PrEnv : Set where
  constructor mk
  field
    level : ℕ

  withLevel : ℕ → PrEnv
  withLevel x = record { level = x }

  top : PrEnv
  top = withLevel 2

  ap : PrEnv
  ap = withLevel 1

  atm : PrEnv
  atm = withLevel 0

open PrEnv

emptyPrEnv : PrEnv
emptyPrEnv = record { level = 2 }

paren : (PrEnv → PrEnv) → PrEnv → ShowS → ShowS
paren f Δ = if ⌊ level (f Δ) ≤? level Δ ⌋ then id else parenBase

prTmᴿ : PrEnv → Pr Tmᴿ
prTmᴿ Δ (ƛ b t)     = paren top Δ (` "λ" ∘ ` b ∘ ` ". " ∘ prTmᴿ (top Δ) t)
prTmᴿ Δ (t · u)     = paren ap Δ (prTmᴿ (ap Δ) t ∘ ` " " ∘ prTmᴿ (atm Δ) u)
{-
prTmᴿ Δ (Let b t u) = ` "let " ∘ ` b ∘ ` " = " ∘ prTmᴿ (top Δ) t ∘ ` " in "
                              ∘ prTmᴿ (top Δ) u ∘ ` " end"
-}
prTmᴿ Δ (V x)       = ` x

showTmᴿ : Tmᴿ → String
showTmᴿ t = prTmᴿ emptyPrEnv t ""
