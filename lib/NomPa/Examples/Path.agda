module NomPa.Examples.Path where

import Level as L
open import Function.NP
open import Data.List
open import Data.Char
open import Data.String as String
open import Data.Maybe.NP

data Segment : Set where
  ƛ ·₁ ·₂ Let₁ Let₂ : Segment

Path = List Segment

open M? L.zero

parsePath?′ : List Char →? Path
parsePath?′ [] = just []
parsePath?′ ('λ' ∷ cs) = pure (_∷_ ƛ) ⊛ parsePath?′ cs
parsePath?′ ('·' ∷ '₁' ∷ cs) = pure (_∷_ ·₁) ⊛ parsePath?′ cs
parsePath?′ ('·' ∷ '₂' ∷ cs) = pure (_∷_ ·₂) ⊛ parsePath?′ cs
parsePath?′ ('L' ∷ '₁' ∷ cs) = pure (_∷_ Let₁) ⊛ parsePath?′ cs
parsePath?′ ('L' ∷ '₂' ∷ cs) = pure (_∷_ Let₂) ⊛ parsePath?′ cs
parsePath?′ (_ ∷ _) = nothing

parsePath? : String →? Path
parsePath? = parsePath?′ ∘ String.toList

PathOk : String → Set
PathOk = just? ∘ parsePath?

parsePath : ∀ s {prf : PathOk s} → Path
parsePath s {prf} with parsePath? s
parsePath s {()}     | nothing
parsePath s {_}      | just t = t
