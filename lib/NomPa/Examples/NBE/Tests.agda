module NomPa.Examples.NBE.Tests where

open import NomPa.Record
open import Data.Product hiding (map)
open import Data.List
import NomPa.Examples.NBE
import NomPa.Examples.NBE.Can
import NomPa.Examples.NBE.Neu
import NomPa.Examples.NBE.Env

module Tests (nomPa : NomPa) where
  open NomPa nomPa

  module NBE = NomPa.Examples.NBE nomPa
  module Can = NomPa.Examples.NBE.Can nomPa
  module Neu = NomPa.Examples.NBE.Neu nomPa
  module DataEnv = NomPa.Examples.NBE.Env.NBE-dataEnv nomPa
  module FunEnv = NomPa.Examples.NBE.Env.NBE-funEnv nomPa

  open NBE.TermType

  idᵀ : Term ø
  idᵀ = ƛ (0 ᴮ , V (0 ᴺ))

  falseᵀ : Term ø
  falseᵀ = ƛ (0 ᴮ , ƛ (1 ᴮ , V (1 ᴺ)))

  t₁ : Term ø
  t₁ = (idᵀ · (idᵀ · idᵀ)) · idᵀ

  t₂ : Term ø
  t₂ = (idᵀ · (falseᵀ · idᵀ)) · idᵀ

  t₃ : Term ø
  t₃ = idᵀ · (idᵀ · (idᵀ · falseᵀ))

  inputs : List (Term ø)
  inputs = t₁ ∷ t₂ ∷ t₃ ∷ []

  outputs : List (Term ø)
  outputs = idᵀ ∷ idᵀ ∷ falseᵀ ∷ []

module RunTests where
  open import NomPa.Implem
  open import Relation.Binary.PropositionalEquality
  open Tests nomPa
  -- since we applied the implementation the following
  -- equalities see through α-equivalance and thus we
  -- can distinguish α-equivalent terms.

  nbeTests : map NBE.nfø inputs ≡ outputs
  nbeTests = refl

  canTests : map Can.nfø inputs ≡ outputs
  canTests = refl

  neuTests : map Neu.nfø inputs ≡ outputs
  neuTests = refl

  dataEnvTests : map DataEnv.nfø inputs ≡ outputs
  dataEnvTests = refl

  funEnvTests : map FunEnv.nfø inputs ≡ outputs
  funEnvTests = refl
