module NomPa.Encodings.AlphaCaml.Test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function
open import Data.List as List
open import Data.Sum
open import Data.Maybe.NP
open import Data.Product.NP
open import NomPa.Implem using (nomPa)
open import NomPa.Record
import NomPa.Encodings.AlphaCaml
open NomPa nomPa
open NomPa.Encodings.AlphaCaml nomPa
open ML-Example2
open Terms
open Ctors

test₁ : fvTm 4 apTm ≡ []
test₁ = refl

test₂ : map? (List.map binderᴺ ∘ fvTm 3 ∘ snd) (unLam apTm) ≡ just [ 0 ]
test₂ = refl
