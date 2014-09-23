open import Function
open import NomPa.Record
import NomPa.Derived
import NomPa.Traverse
import NomPa.Examples.LC.DataTypes
import NomPa.Examples.LC
open import Data.Empty
open import Data.List.NP as L
open import Data.Maybe hiding (Eq)
open import Data.Bool
open import Data.String
open import Data.Nat
open import Data.Product.NP

module NomPa.Examples.LC.CC (nomPa : NomPa)
  (Cst : Set)
  (showCst : Cst → String) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa

open NomPa.Examples.LC nomPa Cst showCst
open FreeVars using (fv)

module CCs
  (Tmᵗ      : World → Set)
  (Vᵗ       : ∀ {α} → Name α → Tmᵗ α)
  (ƛᵗ       : ∀ {α} b → Tmᵗ (b ◅ α) → Tmᵗ α)
  (Letᵗ     : ∀ {α} b → Tmᵗ α → Tmᵗ (b ◅ α) → Tmᵗ α)
  (_$:_     : ∀ {α} → Tmᵗ α → Tmᵗ α → Tmᵗ α)
  (_:$_     : ∀ {α} → Tmᵗ ø → Tmᵗ α → Tmᵗ α)
  (proj     : ∀ {α} → ℕ → Tmᵗ α → Tmᵗ α)
  (tup      : ∀ {α} → List (Tmᵗ α) → Tmᵗ α)
  (`ᵗ_      : ∀ {α} → Cst → Tmᵗ α)
  (fvᵗ      : ∀ {α} → Tmᵗ α → List (Name α))
  (substTmᵗ : Subst Tmᵗ Tmᵗ)
    where

  cc-close : ∀ {α} → Tmᵗ α → Tmᵗ α
  cc-close {α} t = (ƛᵗ e (substTmᵗ (1 ˢ) Φ t)) :$ (tup (L.map Vᵗ xs))
    where xs = uniqBy _==ᴺ_ (fvᵗ t)
          e : Binder
          e = 0 ᴮ
          dummy : ℕ
          dummy = 0
          Φ : Name α → Tmᵗ (e ◅ ø)
          Φ x = proj (maybe′ id dummy (index _==ᴺ_ x xs)) (Vᵗ (nameᴮ e))

  module CC₁ where
    cc : ∀ {α} → Tm α → Tmᵗ α
    cc (V x)       = Vᵗ x
    cc (t · u)     = cc t $: cc u
    cc (ƛ b t)     = cc-close (ƛᵗ b (cc t))
    cc (Let b t u) = Letᵗ b (cc t) (cc u)
    cc (` n)       = `ᵗ n

  module CC₂ where
    cc  : ∀ {α} → Tm α → Tmᵗ α
    ccλ : ∀ {α} → Tm α → Tmᵗ α

    cc (V x)       = Vᵗ x
    cc (t · u)     = cc t $: cc u
    cc (ƛ b t)     = cc-close (ƛᵗ b (ccλ t))
    cc (Let b t u) = Letᵗ b (cc t) (cc u)
    cc (` n)       = `ᵗ n

    ccλ (ƛ b t) = ƛᵗ b (ccλ t)
    ccλ t       = cc t

module Target₁ where
  data Tmᵗ : World → Set where
    Vᵗ       : ∀ {α} → Name α → Tmᵗ α
    ƛᵗ       : ∀ {α} b → Tmᵗ (b ◅ α) → Tmᵗ α
    Letᵗ     : ∀ {α} b → Tmᵗ α → Tmᵗ (b ◅ α) → Tmᵗ α
    _$:_     : ∀ {α} → Tmᵗ α → Tmᵗ α → Tmᵗ α
    _:$_     : ∀ {α} → Tmᵗ ø → Tmᵗ α → Tmᵗ α
    proj     : ∀ {α} → ℕ → Tmᵗ α → Tmᵗ α
    tup      : ∀ {α} → List (Tmᵗ α) → Tmᵗ α
    `ᵗ_      : ∀ {α} → Cst → Tmᵗ α

  postulate
    fvᵗ      : ∀ {α} → Tmᵗ α → List (Name α)
    substTmᵗ : Subst Tmᵗ Tmᵗ

  open CCs Tmᵗ Vᵗ ƛᵗ Letᵗ _$:_ _:$_ proj tup `ᵗ_ fvᵗ substTmᵗ public


{-
{-
data a :-> b = forall e. !(e -> a -> b) :$ e
and define closure creation and application as

lam :: (a -> b) -> (a :-> b)
lam f = const f :$ ()

($:) :: (a :-> b) -> a -> b
(f :$ e) $: x = f e x
-}

postulate
  tup-ctor : ℕ → ℕ
  proj-ctor : ℕ → ℕ

proj : ∀ {α} → ℕ → Tm α
proj n = ` (proj-ctor n)

tup : ∀ {α} → List (Tm α) → Tm α
tup args = ` (tup-ctor (length args)) ·★ args

-- closure constructor
_:$_ : ∀ {α} → Tm ø → Tm α → Tm α
f :$ x = tup (coerceTm ⊆-ø f ∷ x ∷ [])

-- closure application
_$:_ : ∀ {α} → Tm α → Tm α → Tm α
clo $: x = (proj 1 · clo) · (proj 2 · clo) · x

{-
cc⟦\x -> e⟧            = (\(y1, .., yn) x_CC -> cc⟦e⟧) :$
                           (y1, .., yn)
  where
    y1 .. yn = FV e
-}
cc-close : ∀ {α} → Tm α → Tm α
cc-close {α} t = (ƛ e (substTm (1 ˢ) Φ t)) :$ (tup (L.map V xs))
  where xs = uniqBy _==ᴺ_ (fv t)
        e : Binder
        e = 0 ᴮ
        dummy = 0
        Φ : Name α → Tm (e ◅ ø)
        Φ x = proj (maybe id dummy (index _==ᴺ_ x xs)) · V (nameᴮ e)

cc : ∀ {α} → Tm α → Tm α
cc (V x)       = V x
cc (t · u)     = cc t $: cc u
cc (ƛ b t)     = cc-close (ƛ b (cc t))
cc (Let b t u) = Let b (cc t) (cc u)
cc (` n)       = ` n

ccλ : ∀ {α} → Tm α → Tm α
ccλ (ƛ b t) = ƛ b (ccλ t)
ccλ t       = cc t

data Tmᵗ α : Set where
  V : Name α → Tmᵗ α
  _·ₑ_·ₓ_ : Tmᵗ ø → Tmᵗ α → Tmᵗ α → Tmᵗ α
  ƛₑ_ƛₓ_↦_:$_ : ∀ bₑ bₓ → Tmᵗ (bₑ ◅ bₓ ◅ ø) → Tmᵗ α → Tmᵗ α
  Proj : ∀ n → Tmᵗ α → Tmᵗ α
  Tup : List (Tmᵗ α) → Tmᵗ α
  Let : ∀ b → Tmᵗ α → Tmᵗ (b ◅ α) → Tmᵗ α

data Value : Set where
  Tup : List Value → Value
  ƛₑ_ƛₓ_↦_:$_ : ∀ bₑ bₓ → Tmᵗ (bₑ ◅ bₓ ◅ ø) → Value → Value

postulate
  _!!_ : ∀ {A} → List A → ℕ → A

projVal : ℕ → Value → ?
projVal n (Tup xs) = xs !! n
projVal n _ = ?

dd : ∀ {α} → Tmᵗ α → Tm α
dd (V x) = V x
dd (f ·ₑ e ·ₓ x) = ?
dd (ƛₑ bₑ ƛₓ bₓ ↦ t :$ e) = ?
dd (Let b t u) = ?
dd (Proj n t) = ?
dd (Tup ts) = ?

open import Data.Vec

postulate
  app : ∀ {n α} → Supply α → Tmᵗ (n ◅… α) → Vec (Tmᵗ α) n → Tmᵗ α 
{-substTm ? Φ 
  where Φ : Name ( ◅ ◅ ø) → Name 
        Φ = e-}

evdd : Tmᵗ ø → Value
evdd (V x) = ?
evdd (f ·ₑ e ·ₓ x) = evdd (app {2} ? {!f!} (e ∷ x ∷ []))
evdd (ƛₑ bₑ ƛₓ bₓ ↦ t :$ e) = ƛₑ bₑ ƛₓ bₓ ↦ t :$ evdd e
evdd (Let b t u) = app ? u (evdd t ∷ [])
evdd (Proj n t) = projVal n (evdd t)
evdd (Tup ts) = Tup (L.map evdd ts)

{-
cc⟦C⟧
  | if C_CC exists       = $WC_CC
cc⟦x::t⟧
  | if x_CC exists       = x_CC
  | otherwise            = to iso<t> x
cc⟦lit⟧                = lit
cc⟦e@t⟧                = cc⟦e⟧t^
cc⟦/\a -> e⟧           = /\a -> cc⟦e⟧
cc⟦let x = e1 in e2]     = let x_CC = cc⟦e1⟧ in cc⟦e2⟧
cc⟦case e x::t of alts⟧= case cc⟦e⟧ x_CC::t^
                           of cc⟦alts⟧
cc⟦e `cast` t⟧         = cc⟦e⟧ `cast` t^

cc⟦alt1; ..; altn⟧    = cc⟦alt1⟧; ..; cc⟦altn⟧
cc⟦default -> e⟧      = default -> cc⟦e⟧
cc⟦C x1 .. xn -> e⟧
  | if C_CC exists      = C_CC x1_CC .. xn_CC -> cc⟦e⟧
  | otherwise           = C x1 .. xn -> cc⟦e⟧
-}
-}
