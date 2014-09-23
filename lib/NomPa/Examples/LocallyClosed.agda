open import Data.Sum
open import Function.NP
open import NomPa.Record

module NomPa.Examples.LocallyClosed (nomPa : NomPa) where
  open NomPa nomPa

  -- Hides the environment argument of a given function over terms.
  module M
    (Tm : Set → World → Set)
    (cst : ∀ {α Cst} → Cst → Tm Cst α)
    (var : ∀ {α Cst} → Name α → Tm Cst α)
    (substTm : ∀ {α Cst} → (Name α → Tm Cst ø) → Tm Cst α → Tm Cst ø)
    (bindTm : ∀ {α A B} → (A → Tm B α) → Tm A α → Tm B α)
    (coerceTmø : ∀ {α Cst} → Tm Cst ø → Tm Cst α)
    (f : ∀ {Cst} → Tm Cst ø → Tm Cst ø)
   where
   transform : ∀ {α Cst} → Tm Cst α → Tm Cst α
   transform = bindTm [ cst , var ]  -- untag constants and free variables
             ∘ coerceTmø             -- closed terms inhabit any world
             ∘ f                     -- operates on a locally closed term
             ∘ substTm (cst ∘ inj₂)  -- tag(₂) the free variables as constants
             ∘ bindTm (cst ∘ inj₁)   -- tag(₁) the original constants

  -- Less general
  module M-less-nice
    (Tm : Set → World → Set)
    (cst : ∀ {α Cst} → Cst → Tm Cst α)
    (var : ∀ {α Cst} → Name α → Tm Cst α)
    (substTm : ∀ {α β Cst} → (Name α → Tm Cst β) → Tm Cst α → Tm Cst β)
    (bindTm : ∀ {α A B} → (A → Tm B α) → Tm A α → Tm B α)
    (coerceTm : ∀ {α β Cst} → α ⊆ β → Tm Cst α → Tm Cst β)
    (Env : World → World → Set)
    (ε : Env ø ø)
    (f : ∀ {α β Cst} → Env α β → Tm Cst α → Tm Cst β)
   where
   transform : ∀ {α Cst} → Tm Cst α → Tm Cst α
   transform = bindTm [ cst , var ]  -- untag constants and free variables
             ∘ coerceTm ⊆-ø          -- closed terms inhabit any world
             ∘ f ε                   -- operates on a locally closed term
             ∘ substTm (cst ∘ inj₂)  -- tag(₂) the free variables as constants
             ∘ bindTm (cst ∘ inj₁)   -- tag(₁) the original constants
