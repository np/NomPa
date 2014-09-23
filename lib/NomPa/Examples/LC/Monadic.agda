open import NomPa.Record
import NomPa.Derived
import NomPa.Examples.LC
open import Function.NP
open import Data.Empty using (⊥)

module NomPa.Examples.LC.Monadic (nomPa : NomPa) where
open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Examples.LC nomPa ⊥ (λ())

module M (unit bind ap : CTm) where

  infix 0 !_

  !_ : ∀ {α} → Tm α → Tm α
  ! V x       = unit · V x
  ! ƛ b t     = unit · ƛ b (! t)
  ! t · u     = ap · (! t) · (! u)
  ! Let b t u = bind · (! t) · ƛ b (! u)
           -- = ap · (unit · ƛ b (! u)) · (! t)
           -- = ap · (! (ƛ b u)) · (! t)
  ! ` κ       = unit · ` κ

  monadic-β : ∀ {α} → Supply α → Tm α → Tm α
  monadic-β s t = β-reduce-bottom-up s (! t)

  -- The fact that we can go back with coerceTmø afterwards appeal to be able
  -- to do it directly.
  monadic-β-ø : Tm ø → CTm
  monadic-β-ø t = coerceTmø (monadic-β (0 ˢ) t)

  monadic-βlet : ∀ {α β} → α ⊆ β → Tm α → Tm β
  monadic-βlet ⊆w t = βlet-reduce-bottom-up ⊆w (! t)

  monadic-βlet-ø : Tm ø → CTm
  monadic-βlet-ø t = monadic-βlet ⊆-ø t

ap₁ : (f : ∀ {α} → Tm α) → ∀ {α} → Tm α → Tm α
ap₁ f t = f · t

ap₂ : (f : ∀ {α} → Tm α) → ∀ {α} → Tm α → Tm α → Tm α
ap₂ f t u = (f · t) · u

apGen : (unit bind : CTm) → CTm
apGen unit bind =
  ƛ` mf
    (ƛ` mx
       (bind · V₁ mf · (ƛ` f
          (bind · V₁ mx · (ƛ` x
             (unit · V₁ f · V₀ x))))))
  where mf = 0
        mx = 1
        f  = 2
        x  = 3

-- Cont R A = (A → R) → R

module ContTm where
  unit : CTm
  unit = ƛ` x (ƛ` k (V₀ k · V₁ x))
   where x = 0
         k = 1

  bind : CTm
  bind = ƛ` mx (ƛ` f (ƛ` k
               (V₂ mx · (ƛ` x ((V₂ f · V₀ x) · V₁ k)))))
   where mx = 0
         f  = 1
         k  = 2
         x  = 3

  ap : CTm
  ap = apGen unit bind

  run : CTm
  run = ƛ` mx (V₀ mx · idTm)
    where mx = 0

module CPS where
  open M ContTm.unit ContTm.bind ContTm.ap
    public renaming (monadic-β to cps-β; !_ to cps; monadic-β-ø to cps-β-ø;
                     monadic-βlet to cps-βlet; monadic-βlet-ø to cps-βlet-ø)

module Cont where
-- Without ``instance agruments'':
  unit : ∀ {α} → Supply α → Tm α → Tm α
  unit s x = ƛ k (V′ k · x₁)
   where x₁ = coerceTmˢ s x
         k  = Supply.seedᴮ s

  bind : ∀ {α} → Supply α → Tm α → Tm α → Tm α
  bind s mx f = ƛ k (mx₁ · (ƛ x ((f₂ · x₀) · k₂)))
   where mx₁ = coerceTmˢ s mx
         f₂  = coerceTmˢ (sucˢ s) (coerceTmˢ s f)
         k  = Supply.seedᴮ s
         k₂ = coerceTmˢ (sucˢ s) (V′ k)
         x  = Supply.seedᴮ (sucˢ s)
         x₀ = V′ x

  ap : ∀ {α} → Supply α → Tm α → Tm α → Tm α
  ap s mf mx = bind s mf (ƛ f
                  (bind (sucˢ s) (coerceTmˢ s mx) (ƛ x
                     (unit (sucˢ (sucˢ s)) (fT · xT)))))
    where f = Supply.seedᴮ s
          x = Supply.seedᴮ (sucˢ s)
          fT = coerceTmˢ (sucˢ s) (V′ f)
          xT = V′ x
{- with instance arguments
  unit : ∀ {α} ⦃ s : Supply α ⦄ → Tm α → Tm α
  unit ⦃ s ⦄ x = ƛ k (V′ k · x₁)
   where x₁ = coerceTmˢ … x
         k  = Supply.seedᴮ s

  bind : ∀ {α} ⦃ s : Supply α ⦄ → Tm α → Tm α → Tm α
  bind ⦃ s ⦄ mx f = ƛ k (mx₁ · (ƛ x ((f₂ · x₀) · k₂)))
   where mx₁ = coerceTmˢ s mx
         f₂  = coerceTmˢ (sucˢ s) (coerceTmˢ s f)
         k  = Supply.seedᴮ s
         k₂ = coerceTmˢ (sucˢ s) (V′ k)
         x  = Supply.seedᴮ (sucˢ s)
         x₀ = V′ x

  ap : ∀ {α} ⦃ s : Supply α ⦄ → Tm α → Tm α → Tm α
  ap ⦃ s ⦄ mf mx = bind mf (ƛ f
                       (bind (coerceTmˢ … mx) (ƛ x
                          (unit (fT · xT)))))
    where 1+s = sucˢ s
          2+s = sucˢ 1+s

          f = Supply.seedᴮ s
          x = Supply.seedᴮ (sucˢ s)
          fT = coerceTmˢ … (V′ f)
          xT = V′ x
-}
  run : ∀ {α} → Tm α → Tm α
  run mx = mx · idTm

-- module CPS = M-no-app contReturn contBind
