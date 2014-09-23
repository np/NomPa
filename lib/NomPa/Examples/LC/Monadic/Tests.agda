module NomPa.Examples.LC.Monadic.Tests where

open import Data.Bool
open import Data.Empty
open import NomPa.Record
import NomPa.Derived
import NomPa.Examples.LC
import NomPa.Examples.LC.Monadic
import NomPa.Examples.LC.Equiv
open import Relation.Binary.PropositionalEquality as ≡

module M (nomPa : NomPa) where
  open NomPa nomPa public
  open NomPa.Derived nomPa public
  open NomPa.Examples.LC nomPa ⊥ (λ()) public
  open NomPa.Examples.LC.Equiv nomPa public
  open NomPa.Examples.LC.Monadic nomPa public
  open ContTm public
  open CPS public

  x = 0
  xᴮ = x ᴮ
  xᵀ : ∀ {α} → Tm (x ᴮ ◅ α)
  xᵀ = V (x ᴺ)

  f = 0
  fᴮ = f ᴮ
  fᵀ : ∀ {α} → Tm (f ᴮ ◅ α)
  fᵀ = V (f ᴺ)

  cps-id : CTm
  cps-id = cps idTm

  cpsβ-id : CTm
  cpsβ-id = cps-β-ø idTm

  t₁ : CTm
  t₁ = Let fᴮ idTm (fᵀ · fᵀ)

  cps-t₁ : Tm ø
  cps-t₁ = cps t₁

  cpsβ-t₁ : Tm ø
  cpsβ-t₁ = cps-β-ø t₁

  cps-t₁-ref : Tm ø
  cps-t₁-ref = bind · (unit · ƛ xᴮ (unit · xᵀ)) · ƛ fᴮ (ap · (unit · fᵀ) · (unit · fᵀ))

  cpsβlet-t₁ : Tm ø
  cpsβlet-t₁ = cps-βlet-ø t₁

  open Cont renaming (bind to bind′; unit to unit′; ap to ap′)

  cpsβ-t₁-ref : Tm ø
  cpsβ-t₁-ref = bind′ 0ˢ (unit′ 0ˢ (ƛ xᴮ (unit′ 1ˢ xᵀ))) (ƛ fᴮ (ap′ 1ˢ (unit′ 1ˢ fᵀ) (unit′ 1ˢ fᵀ)))
    where 0ˢ = 0 ˢ
          1ˢ = 1 ˢ

  β-cpst₁ref : Tm ø
  β-cpst₁ref = β-reduce-bottom-upø cps-t₁-ref

  βlet-cps-t₁-ref : Tm ø
  βlet-cps-t₁-ref = βlet-reduce-bottom-upø cps-t₁-ref

open import NomPa.Implem using (nomPa)
open M nomPa

ex₁ : cps-t₁ ≡ cps-t₁-ref
ex₁ = ≡.refl

ex₂ : showTmø cpsβlet-t₁ ≡ showTmø βlet-cps-t₁-ref
ex₂ = ≡.refl

ex₄ : showTmø cpsβ-t₁ ≡ showTmø β-cpst₁ref
ex₄ = ≡.refl

-- ex₃ : showTmø cpsβ-t₁ ≡ showTmø cpsβ-t₁-ref
-- ex₃ = {!!} -- ≡.refl
