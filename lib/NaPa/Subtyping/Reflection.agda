open import NaPa.Worlds
open import NaPa.Subtyping

module NaPa.Subtyping.Reflection {World} (Wsym : WorldSymantics World) where

open WorldSymantics Wsym

{- __ UNFINISHED __

open import Data.Product
open import Data.List
open import Data.Vec
open import Data.Nat
open import Reflection.NP
open import Reflection.Decoding

er : ArgSpec
er = explicit , relevant

module DecodeWorld {W′} (Wsym′ : WorldSymantics W′) where
  decodeWorld : D World
  decodeWorld =  (mk↑1 =<< deDef (quote _↑1) (er ∷ []))
             ⟨|⟩ (mk+1 =<< deDef (quote _+1) (er ∷ []))
             ⟨|⟩ mapD (λ _ → ø) (deDef (quote ø) [])
    where
      mk↑1 : Vec Term 1 → D World
      mk↑1 (t ∷ []) = mapD _↑1 (λ _ → decodeWorld t)
      mk+1 : Vec Term 1 → D World
      mk+1 (t ∷ []) = mapD _+1 (λ _ → decodeWorld t)

data Tagged (A : Set) {B : Set} (y : B) : Set where
  tagged : (x : A) → Tagged A y

decodeTagged : D (Term × Term)
decodeTagged = mapD vec2pair (deDef (quote Tagged) (er ∷ er ∷ []))
  where vec2pair : ∀ {A : Set} → Vec A 2 → A × A
        vec2pair (x ∷ y ∷ []) = x , y

withTagged : ∀ {A} → (x : A) → D A → Term → Tagged Term x
withTagged x decodeA t = tagged {!decodeA t!}

module Test where
  w = ø ↑1 ↑1 +1 ↑1

  ⊆-Pack.`⊆`-pack

  `w : Tagged Term w
  `w = quoteGoal g in withTagged w decodeWorld g
-}
