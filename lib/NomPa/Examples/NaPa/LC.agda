open import Category.Applicative renaming (RawApplicative to Applicative;
                                           module RawApplicative to Applicative)
open import Function.NP
open import Data.Product
open import Data.Nat.NP renaming (_==_ to _==ℕ_)
open import Data.Unit
open import Data.List using (List; foldl; []; _∷_; [_]; _++_)
open import Data.Bool hiding (T)
open import Data.Maybe.NP
open import NomPa.Record
open import NomPa.Examples.Path
open import NomPa.Examples.Raw
open import NomPa.Examples.Raw.Parser using (module ParseConv)
open import NomPa.Examples.Raw.Printer using (showTmᴿ)
open import Data.Char using (Char)
open import Data.String renaming (_++_ to _++ˢ_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
import NomPa.Derived
import NomPa.Derived.NaPa
import Level as L
import Data.Indexed
open NomPa.Examples.Raw.StringTerm

module NomPa.Examples.NaPa.LC (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa
open Data.Indexed {_} {World}

infixl 4 _·_
data Tmᴰ α : Set where
  V   : (a : Name α) → Tmᴰ α
  ƛ   : (t : Tmᴰ (α ↑1)) → Tmᴰ α
  _·_ : (t u : Tmᴰ α) → Tmᴰ α
  Let : (t : Tmᴰ α) (u : Tmᴰ (α ↑1)) → Tmᴰ α
  `_ : (n : ℕ) → Tmᴰ α

appⁿ : ∀ {α} → Tmᴰ α → List (Tmᴰ α) → Tmᴰ α
appⁿ = foldl _·_

un`? : Tmᴰ ø →? ℕ
un`? (` n) = just n
un`? _     = nothing

module RenameByHand where
  renameTmᴰ : ∀ {α β} → (α →ᴺ β)
                       → (Tmᴰ α → Tmᴰ β)
  renameTmᴰ f (V x)      = V (f x)
  renameTmᴰ f (t · u)    = renameTmᴰ f t · renameTmᴰ f u
  renameTmᴰ f (ƛ t)      = ƛ (renameTmᴰ (protect↑1 f) t)
  renameTmᴰ f (Let t u)  = Let (renameTmᴰ f t) (renameTmᴰ (protect↑1 f) u)
  renameTmᴰ _ (` n)      = ` n

  shiftTmᴰ↑ : ∀ {α} k → Tmᴰ α → Tmᴰ (α ↑ k)
  shiftTmᴰ↑ = renameTmᴰ ∘ addᴺ↑

  renameTmᴰ↑ : ∀ {α β} → (∀ ℓ → (α ↑ ℓ) →ᴺ (β ↑ ℓ))
                       → (Tmᴰ α → Tmᴰ β)
  renameTmᴰ↑ {α} {β} f = go 0 where
    go : ∀ ℓ → Tmᴰ (α ↑ ℓ) → Tmᴰ (β ↑ ℓ)
    go ℓ (V x)     = V (f ℓ x)
    go ℓ (t · u)   = go ℓ t · go ℓ u
    go ℓ (ƛ t)     = ƛ (go (suc ℓ) t)
    go ℓ (Let t u) = Let (go ℓ t) (go (suc ℓ) u)
    go ℓ (` κ)     = ` κ

  shiftᴺ↑ : ∀ {α} k ℓ → (α ↑ ℓ) →ᴺ (α ↑ k ↑ ℓ)
  shiftᴺ↑ = protect↑ ∘ addᴺ↑

  shiftTmᴰ↑′ : ∀ {α} k → Tmᴰ α → Tmᴰ (α ↑ k)
  shiftTmᴰ↑′ = renameTmᴰ↑ ∘ shiftᴺ↑

  unprotectedAdd : ∀ {α} k ℓ → Name (α ↑ ℓ)
                             → Name (α ↑ k ↑ ℓ)
  unprotectedAdd k ℓ
    = coerceᴺ (⊆-exch-↑-↑′ ℓ k) ∘ addᴺ↑ k
    -- this is ok since (α ↑  k) ↑ ℓ ≡ (α ↑ ℓ) ↑  k
    -- whereas          (α +ᵂ k) ↑ ℓ ≢ (α ↑ ℓ) +ᵂ k

  ⊆-mix : ∀ n k ℓ → (ø ↑ n) ↑ ℓ ⊆ ((ø ↑ n) ↑ k) ↑ ℓ
  ⊆-mix n k ℓ = ⊆-cong-↑ (⊆-trans (⊆-cong-↑ ⊆-ø n) (⊆-exch-↑-↑′ k n)) ℓ

  coerce-mix : ∀ n k ℓ → ((ø ↑ n) ↑ ℓ) →ᴺ (((ø ↑ n) ↑ k) ↑ ℓ)
  coerce-mix n k ℓ = coerceᴺ (⊆-mix n k ℓ)

module TraverseTmᴰ  {E} (E-app : Applicative E)
                    {α β} (trName : Su↑ Name (E ∘ Tmᴰ) α β) where
  open Applicative E-app

  ! : Su↑ Tmᴰ (E ∘ Tmᴰ) α β
  ! ℓ (V x)      = trName ℓ x
  ! ℓ (t · u)    = _·_ <$> ! ℓ t ⊛ ! ℓ u
  ! ℓ (ƛ t)      = ƛ   <$> ! (suc ℓ) t
  ! ℓ (Let t u)  = Let <$> ! ℓ t ⊛ ! (suc ℓ) u
  ! _ (` n)      = pure (` n)

open TraverseAFGGGen {Tmᴰ} Tmᴰ.V TraverseTmᴰ.! public
  renaming ( renameA   to renameATmᴰ
           ; rename    to renameTmᴰ
           ; shift     to shiftTmᴰ
           ; coerceø   to coerceTmøᴰ
           ; coerce    to coerceTmᴰ
           ; subtract? to subtractTmᴰ?
           ; close?    to closeTmᴰ?
           )

open SubstGen {Tmᴰ} V shiftTmᴰ (TraverseTmᴰ.! id-app) public
  renaming ( substVarG to substVarTmᴰ
           ; subst to substTmᴰ )

β-redᴰ : ∀ {α} → Tmᴰ α → Tmᴰ α
β-redᴰ (ƛ fct · arg) = substTmᴰ (subtractWithᴺ 1 arg V) fct
β-redᴰ t             = t

_[0≔_] : ∀ {α} → Tmᴰ (α ↑1) → Tmᴰ α → Tmᴰ α
t [0≔ u ] = substTmᴰ (subtractWithᴺ 1 u V) t

{- would require a coercion to exchange ↑ and ↑1
ƛs : Path → ℕ
ƛs [] = 0
ƛs (ƛ ∷ p) = suc (ƛs p)
ƛs (_ ∷ p) = ƛs p

focusᵂ : Path → World → World
focusᵂ p α = α ↑ (ƛs p)
-}

focusᵂ : Path → World → World
focusᵂ []         = id
focusᵂ (ƛ ∷ p)    = focusᵂ p ∘ _↑1
focusᵂ (Let₂ ∷ p) = focusᵂ p ∘ _↑1
focusᵂ (_ ∷ p)    = focusᵂ p

focus? : (p : Path) → ∀ {α} → Tmᴰ α →? Tmᴰ (focusᵂ p α)
focus? []         t         = just t
focus? (ƛ ∷ p)    (ƛ t)     = focus? p t
focus? (·₁ ∷ p)   (t · _)   = focus? p t
focus? (·₂ ∷ p)   (_ · t)   = focus? p t
focus? (Let₁ ∷ p) (Let t _) = focus? p t
focus? (Let₂ ∷ p) (Let _ t) = focus? p t
focus? _          _         = nothing

defocus : (p : Path) → ∀ {α} → Tmᴰ α → Tmᴰ (focusᵂ p α) → Tmᴰ α
defocus []         _         = id
defocus (ƛ ∷ p)    (ƛ t)    = ƛ ∘′ defocus p t
defocus (·₁ ∷ p)   (t · u)   = flip _·_ u ∘′ defocus p t
defocus (·₂ ∷ p)   (t · u)   = _·_ t ∘′ defocus p u
defocus (Let₁ ∷ p) (Let t u) = (flip Let u) ∘ defocus p t
defocus (Let₂ ∷ p) (Let t u) = Let t ∘ defocus p u
defocus _          t         = const t

module Parser where
  module Tmᴿ⇒Tmᴰ where
    Env : World → Set
    Env α = String → Name α
    extEnv : ∀ {α} → String → Env α → Env (α ↑1)
    extEnv b Δ s = if b == s then 0 ᴺ else sucᴺ↑ (Δ s)
    ! : ∀ {α} → Env α → Tmᴿˢ → Tmᴰ α
    ! Δ (V x) = V (Δ x)
    ! Δ (ƛ b t) = ƛ (! (extEnv b Δ) t)
    ! Δ (t · u) = ! Δ t · ! Δ u

  conv? : Tmᴿˢ →? (∀ {α} → Tmᴰ α)
  conv? = map? coerceTmøᴰ ∘ closeTmᴰ? ∘ Tmᴿ⇒Tmᴰ.! (const (zeroᴺ {ø}))

  open ParseConv conv? public renaming (parseConv? to parseTmᴰ?; parseConv to parseTmᴰ; TmOk to TmᴰOk)

open Parser public using (parseTmᴰ?; parseTmᴰ; TmᴰOk)

fvᴰ : ∀ {α} → Tmᴰ α → List (Name α)
fvᴰ (` _)        = []
fvᴰ (V x)        = [ x ]
fvᴰ (fct · arg)  = fvᴰ fct ++ fvᴰ arg
fvᴰ (ƛ t)        = rm₀ (fvᴰ t)
fvᴰ (Let t u)    = fvᴰ t ++ rm₀ (fvᴰ u)

module Tmᴰ⇒Tmᴿ where
  open import Data.Nat.Show renaming (show to showℕ)
  open import Data.Fin as Fin using (toℕ)
  binder! : ℕ → String
  binder! n = "x" ++ˢ showℕ n
  name! : ∀ ℓ → Name (ø ↑ ℓ) → String
  name! ℓ x = binder! (ℓ ∸ suc (Fin.toℕ (toFin {ℓ} x)))
  ! : ∀ ℓ → Tmᴰ (ø ↑ ℓ) → Tmᴿˢ
  ! ℓ (V x) = V (name! ℓ x)
  ! ℓ (ƛ t) = ƛ (binder! ℓ) (! (1 + ℓ) t)
  ! ℓ (t · u) = ! ℓ t · ! ℓ u
  ! ℓ (Let t u) = ƛ (binder! ℓ) (! (1 + ℓ) u) · ! ℓ t -- ! ℓ (ƛ u · t)
  ! _ (` n) = n ℕᴿˢ
open Tmᴰ⇒Tmᴿ public renaming (! to convTmᴰ⇒Tmᴿ)

showTmᴰ : Tmᴰ ø → String
showTmᴰ = showTmᴿ ∘ Tmᴰ⇒Tmᴿ.! 0

cmpTmᴰ : ∀ {α β} → Cmp° Name α β → Cmp° Tmᴰ α β
cmpTmᴰ {α} {β} Γ = go 0 where
  go : ∀ ℓ → Cmp° Tmᴰ (α ↑ ℓ) (β ↑ ℓ)
  go ℓ (V x)   (V y)        = cmp↑Name Γ ℓ x y
  go ℓ (t · u) (v · w)      = go ℓ t v ∧ go ℓ u w
  go ℓ (ƛ t) (ƛ u)          = go (suc ℓ) t u
  go ℓ (Let t u) (Let v w)  = go ℓ t v ∧ go (suc ℓ) u w
  go _ (` m) (` n)          = m ==ℕ n
  go _ _ _                  = false

eqTmᴰ : ∀ {α} → Cmp° Tmᴰ α α
eqTmᴰ (V x)     (V y)     = x ==ᴺ y
eqTmᴰ (t · u)   (v · w)   = eqTmᴰ t v ∧ eqTmᴰ u w
eqTmᴰ (ƛ t)     (ƛ u)     = eqTmᴰ t u
eqTmᴰ (Let t u) (Let v w) = eqTmᴰ t v ∧ eqTmᴰ u w
eqTmᴰ (` m)     (` n)     = m ==ℕ n
eqTmᴰ _         _         = false

data Frame : Set where
  arg fct : Tmᴰ ø → Frame

Stack = List Frame

import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps?)
open import Coinduction
module KAM where -- Krivine Abstract Machine
  -- slightly modified to have CBV primitives
  open Pa using (now; later; never)
  open Pa.M⊥ L.zero

  Tmø = Tmᴰ ø

  _★_ : Tmø → Stack → Tmø ⊥
  (t · u)   ★ π           = t ★ (arg u ∷ π)            -- push
  (ƛ t)     ★ (arg u ∷ π) = later (♯ (t [0≔ u ] ★ π)) -- grab
  (Let t u) ★ π           = later (♯ (u [0≔ t ] ★ π))
  v         ★ []          = now v
  v         ★ (fct t ∷ π) = later (♯ (t ★ (arg v ∷ π)))
  (V x)     ★ _           = Nameø-elim x

  -- 1 as function is `suc' and is CBV
  (` 1)     ★ (arg (` n) ∷ π) = later (♯ (`(suc n) ★ π))
  (` 1)     ★ (arg u ∷ π)     = later (♯ (u ★ (fct (` 1) ∷ π)))

-- debug versions
--(` _)     ★ (arg _ ∷ _)     = stuck where postulate stuck : Tmø ⊥
  _         ★ _ = never

-- CBV semantics
module AAM where -- Another Abstract Machine
  open Pa using (now; later; never)
  open Pa.M⊥ L.zero

  Tmø = Tmᴰ ø

  _★_ : Tmø → Stack → Tmø ⊥
  (t · u)   ★ π            = u ★ (fct t ∷ π)
  (ƛ t)     ★ (arg u ∷ π)  = later (♯ (t [0≔ u ] ★ π))
  (Let t u) ★ π            = t ★ (fct (ƛ u) ∷ π)
  v         ★ []           = now v
  v         ★ (fct u ∷ π)  = later (♯ (u ★ (arg v ∷ π)))
  (V x)     ★ _            = Nameø-elim x

  -- (` 1) as a function is `suc'
  (` 1)     ★ (arg (` n) ∷ π) = later (♯ (`(suc n) ★ π))
--(` n)     ★ (arg t ∷ π)     = stuck where postulate stuck : _ ⊥
  _         ★ _ = never
