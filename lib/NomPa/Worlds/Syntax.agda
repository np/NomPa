open import Data.Nat
open import Data.Empty
open import Data.Unit
open import NomPa.Worlds

module NomPa.Worlds.Syntax where

  data `World` : Set where
    _`↑1`  _`+1` : (`α` : `World`) → `World`
    `ø` : `World`

  _`↑`_ : (`α` : `World`) (k : ℕ) → `World`
  `α` `↑` zero = `α`
  `α` `↑` suc n = (`α` `↑` n) `↑1`

  _`+`_ : (`α` : `World`) (k : ℕ) → `World`
  `α` `+` zero = `α`
  `α` `+` suc n = (`α` `+` n) `+1`

  `worldSymantics` : WorldSymantics `World`
  `worldSymantics` = record { ø = `ø`; _↑1 = _`↑1`; _+1 = _`+1` }

  module El {World} (Wsym : WorldSymantics World) where
    open WorldSymantics Wsym

    El : `World` → World
    El (`α` `↑1`)  = El `α` ↑1
    El (`α` `+1`)  = El `α` +1
    El `ø`     = ø

  -- A second way to see bnd is to say that it loose the distinction
  -- between ↑1 and +1.
  bnd : `World` → ℕ
  bnd (`α` `↑1`)  = suc (bnd `α`)
  bnd (`α` `+1`)  = suc (bnd `α`)
  bnd `ø`         = 0

  empty? : `World` → Set
  empty? (`α` `↑1`) = ⊥
  empty? (`α` `+1`) = empty? `α`
  empty? `ø`        = ⊤

  _`∈`_ : ℕ → `World` → Set
  _      `∈` `ø`        = ⊥
  zero   `∈` (`α` `↑1`) = ⊤
  suc n  `∈` (`α` `↑1`) = n `∈` `α`
  zero   `∈` (`α` `+1`) = ⊥
  suc n  `∈` (`α` `+1`) = n `∈` `α`

  module Properties {W} (Wsym : WorldSymantics W) where
    import Relation.Binary.PropositionalEquality as ≡
    open ≡ using (_≡_)

    open WorldSymantics Wsym
    open WorldOps Wsym
    open El Wsym

    comm-El-↑ : ∀ `α` n → El `α` ↑ n ≡ El (`α` `↑` n)
    comm-El-↑ `α` zero                            = ≡.refl
    comm-El-↑ `α` (suc n) rewrite comm-El-↑ `α` n = ≡.refl

