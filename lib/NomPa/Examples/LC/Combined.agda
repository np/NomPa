open import NomPa.Record
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Sum hiding (map)
open import Function
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

module NomPa.Examples.LC.Combined (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa
open NomPa.Traverse nomPa

module NomDbIx where
 data Tm α : Set where
  V    : (x : Name α) → Tm α
  ƛᴺ   : ∀ b (t : Tm (b ◅ α)) → Tm α
  ƛᴰ   : (t : Tm (α ↑1)) → Tm α
  _·_  : (t u : Tm α) → Tm α

 apTm₁ : ∀ {α} → Tm α
 apTm₁ = ƛᴺ x (ƛᴰ (V (sucᴺ↑ (nameᴮ x)) · V (0 ᴺ)))
   where x = 42 ᴮ

 {-
 apTm₂ : Tm ø
 apTm₂ = ƛᴰ (ƛᴺ x (V (coerceᴺ pf (zeroᴺ {α = ø})) · V (nameᴮ x)))
   where x  = 4 ᴮ
         pf = ⊆-trans (⊆-◅ _ (⊆-ø+ 1)) (⊆-swap-◅◅ (0 ᴮ) 3)
 -}

 -- rm₀ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
 -- rm₀ = map predᴺ ∘ rm (0 ᴮ)

 fv : ∀ {α} → Tm α → List (Name α)
 fv (V x)        = [ x ]
 fv (fct · arg)  = fv fct ++ fv arg
 fv (ƛᴺ b t)     = rm b (fv t)
 fv (ƛᴰ t)       = rm₀ (fv t)

 -- protect◅↑1 f b = 0
 -- protect◅↑1 f x = 1 + f x
 protect◅↑1 : ∀ {α β b} → (Name α → Name β)
                         → (Name (b ◅ α) → Name (β ↑1))
 protect◅↑1 f = exportWith (0 ᴺ) (sucᴺ↑ ∘ f)

 ren : ∀ {α β} → (Name α → Name β) → Tm α → Tm β
 ren f (ƛᴺ b t) = ƛᴰ (ren (protect◅↑1 f) t)
 ren f (V x)    = V (f x)
 ren f (ƛᴰ t)   = ƛᴰ (ren (protect↑1 f) t)
 ren f (t · u)  = ren f t · ren f u

 norm : ∀ {α} → Tm α → Tm α
 norm = ren id

 openTm : ∀ {α b} → b # α → Tm (α ↑1) → Tm (b ◅ α)
 openTm b# = ren (exportWith (nameᴮ _) (coerceᴺ (⊆-# b#) ∘ predᴺ))

 openTmS : ∀ {α} (s : Supply α) → Tm (α ↑1) → Tm (Supply.seedᴮ s ◅ α)
 openTmS (_ , b#) = openTm b#

 nomview : ∀ {α} → Supply α → Tm α → Tm α
 nomview s (ƛᴰ t) = ƛᴺ _ (openTmS s t)
 nomview _ t = t

{-

module NomDbIxOpenClose where
 data Tm α : Set where
  V    : Name α → Tm α
  ƛᴺ   : ∀ b → Tm (b ◅ α) → Tm α
  ƛᴰ   : Tm (α ↑1) → Tm α
  _·_  : (t u : Tm α) → Tm α
  Letᴺ : ∀ b → (t : Tm α) (u : Tm (b ◅ α)) → Tm α

  Close : ∀ {β} (eq : α ≡ β ↑1) b (t : Tm (b ◅ β)) → Tm α
  Open  : ∀ {β b} (eq : α ≡ b ◅ β) (b# : b # β) (t : Tm (β ↑1)) → Tm α

 rm₀ᴰ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
 rm₀ᴰ = map predᴺ ∘ rm (0 ᴮ)

 -- maps b to 0 and any other name x to x + 1
 toᴰ : ∀ {b α} → Name (b ◅ α) → Name (α ↑1)
 toᴰ = exportWith (0 ᴺ) sucᴺ↑

 -- maps 0 to b and any other name x + 1 to x
 toᴺ : ∀ {b α} → b # α → Name (α ↑1) → Name (b ◅ α)
 toᴺ b#α = exportWith (nameᴮ _) (coerceᴺ (⊆-# b#α) ∘ predᴺ)

 fv : ∀ {α} → Tm α → List (Name α)
 fv (V x)        = [ x ]
 fv (fct · arg)  = fv fct ++ fv arg
 fv (ƛᴺ b t)     = rm b (fv t)
 fv (ƛᴰ t)       = rm₀ᴰ (fv t)
 fv (Letᴺ b t u) = fv t ++ rm _ (fv u)
 fv (Close refl b t)  = map toᴰ (fv t)
 fv (Open refl b# t)  = map (toᴺ b#) (fv t)

 {-
 shiftTm : Shift Tm Tm
 shiftTm = {!!}

 open import Data.Product

 closeTm : ∀ {α} (b : Binder) → Tm (b ◅ α) → Tm (α ↑1)
 closeTm b t = ! (0 ᴺ , {!nameᴮ b!}) (shiftTm 1 (⊆-+-↑ 1) t) where
  ! : ∀ {α} → (Name α × Name α) → Tm α → Tm α
  -- ! y (Vᴬ x)    = if x ==ᴬ a then Vᴺ y else Vᴬ x
  ! y (V x)    = V x
  ! y (t · u)   = ! y t · ! y u
  ! (y , z) (ƛᴰ t)     = ƛᴰ (! (sucᴺ↑ y , sucᴺ↑ z) t)
  ! _ _ = {!!}
  --  ! y (Letᴺ t u) = Letᴺ (! y t) (! (sucᴺ↑ y) u)

-- closeTm : Atom → Tm ø → Tm (ø ↑1)
 close : ∀ {α} b → Tm (b ◅ α) → Tm (α ↑1)
 close b (V x) = V $ exportWith (0 ᴺ) sucᴺ↑ x
 close b (ƛᴺ b' t) = ƛᴺ b' {!!}
 close b (ƛᴰ y) = ƛᴰ (Close refl b {!y!})
 close b (t · u) = close b t · close b u
 close b (Letᴺ b' t u) = {!!}
 close b (Close eq b' t) = {!close b !}
 close b (Open eq b# t) = {!!}
  -}

module NomDbIxDbLvl where
 data Tm s α : Set where
  V    : Name α → Tm s α
  ƛᴺ   : ∀ b → Tm s (b ◅ α) → Tm s α
  ƛᴰ   : Tm s (α ↑1) → Tm s α
  ƛᴸ   : Tm (sucᴮ s) (s ◅ α) → Tm s α
  _·_  : (t u : Tm s α) → Tm s α
  Letᴺ : ∀ b → (t : Tm s α) (u : Tm s (b ◅ α)) → Tm s α

-- rm and map
{-
rm : ∀ {α β} b → (Name α → Name β) → List (Name (b ◅ α)) → List (Name β)
rm b f []         = []
rm b f (x ∷ xs) with exportᴺ x
...   {- bound -}  |  inj₁ _  = rm b f xs
...   {- free  -}  |  inj₂ x′  = f x′  ∷ rm b f xs

rm₀ᴰ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
rm₀ᴰ = rm (0 ᴮ) predᴺ
-}

 rm₀ᴰ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
 rm₀ᴰ = map predᴺ ∘ rm (0 ᴮ)

 fv : ∀ {α s} → Tm s α → List (Name α)
 fv (V x)        = [ x ]
 fv (fct · arg)  = fv fct ++ fv arg
 fv (ƛᴺ b t)     = rm b (fv t)
 fv (ƛᴰ t)       = rm₀ᴰ (fv t)
 fv (ƛᴸ t)       = rm _ (fv t)
 fv (Letᴺ b t u) = fv t ++ rm _ (fv u)
-}
