open import NomPa.Record
open import Function.NP
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Maybe.NP as Maybe
open import Data.Bool
open import Data.Nat
import Data.Indexed
open import Data.String as String hiding (_++_)
open import Category.Applicative
            renaming (RawApplicative to Applicative; module RawApplicative to Applicative)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
open import NomPa.Examples.Raw
open import NomPa.Examples.Raw.Parser
import NomPa.Examples.LC

module NomPa.Examples.LC.DbLevels (nomPa : NomPa)
                                  (Cst : Set)
                                  (showCst : Cst → String)
                                  (_==ᶜ_ : Cmp Cst) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa hiding (module Env)
open NomPa.Traverse nomPa
open NomPa.Examples.LC nomPa Cst showCst
       using (V; ƛ; _·_; Let; `_)
       renaming (Tm to Tmᴺ; showTmø to showTmᴺ)
open Data.Indexed {_} {World}

data Tmᴸ s α : Set where
  V   : (x : Name α) → Tmᴸ s α
  ƛ   : (t : Tmᴸ (sucᴮ s) (s ◅ α)) → Tmᴸ s α
  _·_ : (t u : Tmᴸ s α) → Tmᴸ s α
  Let : (t : Tmᴸ s α) (u : Tmᴸ (sucᴮ s) (s ◅ α)) → Tmᴸ s α
  `_  : (κ : Cst) → Tmᴸ s α

fv : ∀ {s α} → Tmᴸ s α → List (Name α)
fv (V x)        = [ x ]
fv (fct · arg)  = fv fct ++ fv arg
fv (ƛ t)        = rm _ (fv t)
fv (Let t u)    = fv t ++ rm _ (fv u)
fv (` _)        = []

module CoerceTmByHand where
  coerceTmᴸ : ∀ {α β s} → (α ⊆ β) → Tmᴸ s α → Tmᴸ s β
  coerceTmᴸ α⊆β (V x) = V (x ⟨-because α⊆β -⟩)
  coerceTmᴸ α⊆β (t · u) = coerceTmᴸ α⊆β t · coerceTmᴸ α⊆β u
  coerceTmᴸ α⊆β (ƛ t) = ƛ (coerceTmᴸ (⊆-◅ _ α⊆β) t)
  coerceTmᴸ α⊆β (Let t u) = Let (coerceTmᴸ α⊆β t) (coerceTmᴸ (⊆-◅ _ α⊆β) u)
  coerceTmᴸ _    (` κ) = ` κ

-- generalized further by AddSubtractTmByHand
module AddTmByHand k where
  Env : EnvTypeᴸ
  Env s₁ s₂ α β = (α +ᵂ k) ⊆ β × (s₁ +ᴮ k) ≡ s₂

  extEnv : ExtEnvᴸ Env
  extEnv (pf , ≡.refl) = ⊆-trans (⊆-dist-+-◅ k) (⊆-◅ _ pf) , +ᴮ-dist1 k

  trName : TrNameᴸ Env (const Name)
  trName (pf , _) = coerceᴺ pf ∘ addᴺ k

  trTmᴸ : ∀ {α β s₁ s₂} → Env s₁ s₂ α β → Tmᴸ s₁ α → Tmᴸ s₂ β
  trTmᴸ Δ (V x)     = V (trName Δ x)
  trTmᴸ Δ (t · u)   = trTmᴸ Δ t · trTmᴸ Δ u
  trTmᴸ Δ (ƛ t)     = ƛ (trTmᴸ (extEnv Δ) t)
  trTmᴸ Δ (Let t u) = Let (trTmᴸ Δ t) (trTmᴸ (extEnv Δ) u)
  trTmᴸ Δ (` κ)     = ` κ

  addTmᴸ : ∀ {α s} → Tmᴸ s α → Tmᴸ (s +ᴮ k) (α +ᵂ k)
  addTmᴸ = trTmᴸ (⊆-refl , ≡.refl)

module TraverseTmᴸ {Envᴸ} (kitᴸ : TrKitᴸ Envᴸ Tmᴸ) where
  open TrKitᴸ kitᴸ

  trTmᴸ : ∀ {α β s₁ s₂} → Envᴸ s₁ s₂ α β → Tmᴸ s₁ α → Tmᴸ s₂ β
  trTmᴸ Δ (V x)     = trNameᴸ Δ x
  trTmᴸ Δ (t · u)   = trTmᴸ Δ t · trTmᴸ Δ u
  trTmᴸ Δ (ƛ t)     = ƛ (trTmᴸ (extEnvᴸ Δ) t)
  trTmᴸ Δ (Let t u) = Let (trTmᴸ Δ t) (trTmᴸ (extEnvᴸ Δ) u)
  trTmᴸ _ (` κ)     = ` κ

module TraverseNameTmᴸ {Envᴸ} (kitᴸ : TrKitᴸ Envᴸ (const Name)) where
  open TrKitᴸ kitᴸ

  trTmᴸ : ∀ {α β s₁ s₂} → Envᴸ s₁ s₂ α β → Tmᴸ s₁ α → Tmᴸ s₂ β
  trTmᴸ Δ (V x)     = V (trNameᴸ Δ x)
  trTmᴸ Δ (t · u)   = trTmᴸ Δ t · trTmᴸ Δ u
  trTmᴸ Δ (ƛ t)     = ƛ (trTmᴸ (extEnvᴸ Δ) t)
  trTmᴸ Δ (Let t u) = Let (trTmᴸ Δ t) (trTmᴸ (extEnvᴸ Δ) u)
  trTmᴸ _ (` κ)     = ` κ

module TraverseANameTmᴸ {E} (E-app : Applicative E)
                        {Envᴸ} (kitᴸ : TrKitᴸ Envᴸ (const (E ∘ Name))) where
  open Applicative E-app
  open TrKitᴸ kitᴸ

  trTmᴸ : ∀ {α β s₁ s₂} → Envᴸ s₁ s₂ α β → Tmᴸ s₁ α → E (Tmᴸ s₂ β)
  trTmᴸ Δ (V x)     = pure V ⊛ trNameᴸ Δ x
  trTmᴸ Δ (t · u)   = pure _·_ ⊛ trTmᴸ Δ t ⊛ trTmᴸ Δ u
  trTmᴸ Δ (ƛ t)     = pure ƛ ⊛ trTmᴸ (extEnvᴸ Δ) t
  trTmᴸ Δ (Let t u) = pure Let ⊛ trTmᴸ Δ t ⊛ trTmᴸ (extEnvᴸ Δ) u
  trTmᴸ _ (` κ)     = pure $ ` κ

module TraverseATmᴸ {E} (E-app : Applicative E)
                    {Envᴸ} (kitᴸ : TrKitᴸ Envᴸ (λ s α → E (Tmᴸ s α))) where
  open Applicative E-app
  open TrKitᴸ kitᴸ

  trTmᴸ : ∀ {α β s₁ s₂} → Envᴸ s₁ s₂ α β → Tmᴸ s₁ α → E (Tmᴸ s₂ β)
  trTmᴸ Δ (V x)     = trNameᴸ Δ x
  trTmᴸ Δ (t · u)   = pure _·_ ⊛ trTmᴸ Δ t ⊛ trTmᴸ Δ u
  trTmᴸ Δ (ƛ t)     = pure ƛ ⊛ trTmᴸ (extEnvᴸ Δ) t
  trTmᴸ Δ (Let t u) = pure Let ⊛ trTmᴸ Δ t ⊛ trTmᴸ (extEnvᴸ Δ) u
  trTmᴸ _ (` κ)     = pure $ ` κ

addSubtractTmᴸ : ∀ k₁ k₂
                   {α β s₁ s₂} → (s₁ +ᴮ k₁) ≡ (s₂ +ᴮ k₂)
                               → (α +ᵂ k₁) ⊆ (β +ᵂ k₂)
                               → Tmᴸ s₁ α → Tmᴸ s₂ β
addSubtractTmᴸ k₁ k₂ eq pf
  = TraverseNameTmᴸ.trTmᴸ (AddSubtractᴸ.kitᴸ k₁ k₂) (eq , pf)

shiftTmᴸ′ : ∀ {s₁ s₂ α β} k → s₁ +ᴮ k ≡ s₂ → (α +ᵂ k) ⊆ β → Tmᴸ s₁ α → Tmᴸ s₂ β
shiftTmᴸ′ k pf₁ pf₂ = addSubtractTmᴸ k 0 pf₁ pf₂

shiftTmᴸ : ∀ {α β s} k → (α +ᵂ k) ⊆ β → Tmᴸ s α → Tmᴸ (s +ᴮ k) β
shiftTmᴸ k = shiftTmᴸ′ k ≡.refl

addTmᴸ : ∀ {α s} k → Tmᴸ s α → Tmᴸ (s +ᴮ k) (α +ᵂ k)
addTmᴸ k = shiftTmᴸ k ⊆-refl

shiftøTmᴸ : ∀ {α} k → Tmᴸ (0 ᴮ) ø → Tmᴸ (k ᴮ) α
shiftøTmᴸ k = shiftTmᴸ′ k (0ᴮ-+ᴮ-id k) (⊆-ø+ k)

subtractTmᴸ : ∀ {α s} k → Tmᴸ (s +ᴮ k) (α +ᵂ k) → Tmᴸ s α
subtractTmᴸ k = addSubtractTmᴸ 0 k ≡.refl ⊆-refl

coerceTmᴸ : ∀ {s α β} → α ⊆ β → Tmᴸ s α → Tmᴸ s β
coerceTmᴸ = shiftTmᴸ 0

coerceTmøᴸ : ∀ {s α} → Tmᴸ s ø → Tmᴸ s α
coerceTmøᴸ = coerceTmᴸ ⊆-ø

rerootTmᴸ : ∀ {α} k₁ k₂ → Tmᴸ (k₁ ᴮ) ø → Tmᴸ (k₂ ᴮ) α
rerootTmᴸ k₁ k₂ = addSubtractTmᴸ k₂ k₁ (+ᴮ-comm k₁ k₂) (⊆-ø+ k₂)

renameTmᴸ : ∀ {α β s₁ s₂} → s₂ # β → (α →ᴺ β) → Tmᴸ s₁ α → Tmᴸ s₂ β
renameTmᴸ s₂#β trName = TraverseNameTmᴸ.trTmᴸ renameKitᴸ (trName , s₂#β)

protectedAddTmᴸ : ∀ {α s₁ s₂} k → s₂ # (α +ᵂ k) → Tmᴸ s₁ α → Tmᴸ s₂ (α +ᵂ k)
protectedAddTmᴸ k pf = renameTmᴸ pf (addᴺ k)

-- This function behave like addTmᴸ but protectedAddTmᴸ track separatedely
-- the bound and the free variables. This gives more flexibilty since one
-- can choose to move only the bound or only the free variables. However
-- addTmᴸ is faster and does not require a s#α
-- protectedAddTmᴸ′ : ∀ {α s} k → s # α → Tmᴸ s α → Tmᴸ (s +ᴮ k) (α +ᵂ k)
-- protectedAddTmᴸ′ k pf = protectedAddTmᴸ k (#-+ k)

protectedSubtractTmᴸ : ∀ {α s₁ s₂} k → s₂ # α → Tmᴸ s₁ (α +ᵂ k) → Tmᴸ s₂ α
protectedSubtractTmᴸ k pf = renameTmᴸ pf (subtractᴺ k)

renameTmᴸA : ∀ {E} (E-app : Applicative E)
               {α β s₁ s₂} → s₂ # β → (Name α → E (Name β)) → Tmᴸ s₁ α → E (Tmᴸ s₂ β)
renameTmᴸA E-app s₂#β trNameᴸ =
  TraverseANameTmᴸ.trTmᴸ E-app (renameAKitᴸ E-app) (trNameᴸ , s₂#β)

renameTmᴸ? : ∀ {α β s₁ s₂} → s₂ # β → (α →ᴺ? β) → Tmᴸ s₁ α →? (Tmᴸ s₂ β)
renameTmᴸ? = renameTmᴸA (Maybe.applicative _)

closeTmᴸ? : ∀ {s α} → Tmᴸ s α →? Tmᴸ s ø
closeTmᴸ? = renameTmᴸ? (_ #ø) (const nothing)

⊆-dist-+-◅… : ∀ n → (n ◅…′ ø) +1 ⊆ n ᴮ ◅ n ◅…′ ø
⊆-dist-+-◅… zero = ⊆-ø+ 1
⊆-dist-+-◅… (suc n) = ⊆-trans (⊆-dist-+-◅ 1) (⊆-◅ _ (⊆-dist-+-◅… n))

shiftTmᴸ1′◅… : ∀ {α s} n → s ≡ n ᴮ → α ≡ n ◅…′ ø → Tmᴸ s α → Tmᴸ (sucᴮ s) (s ◅ α)
shiftTmᴸ1′◅… n ≡.refl ≡.refl = shiftTmᴸ′ 1 ≡.refl (⊆-dist-+-◅… n)

importTm : ∀ {s α} → s # α → Tmᴸ s α → Tmᴸ (sucᴮ s) (s ◅ α)
importTm s#α = renameTmᴸ (suc# s#α) (coerceᴺ (⊆-# s#α))

substTmᴸ : ∀ {α β s s₂} → s₂ # β → (Name α → Tmᴸ s₂ β) → Tmᴸ s α → Tmᴸ s₂ β
substTmᴸ s₂#β f = TraverseTmᴸ.trTmᴸ (substKitᴸ V importTm) (f , s₂#β)

substTmᴸ0 : ∀ {α s} → (Name α → Tmᴸ (0 ᴮ) ø) → Tmᴸ s α → Tmᴸ (0 ᴮ) ø
substTmᴸ0 = substTmᴸ (0 ᴮ #ø)

substTm◅… : ∀ {α s} n → (Name α → Tmᴸ (n ᴮ) (n ◅…′ ø)) → Tmᴸ s α → Tmᴸ (n ᴮ) (n ◅…′ ø)
substTm◅… n = substTmᴸ (#-◅…′ø n)

_[0≔_] : Tmᴸ (1 ᴮ) (0 ᴮ ◅ ø) → Tmᴸ (0 ᴮ) ø → Tmᴸ (0 ᴮ) ø
t [0≔ u ] = substTmᴸ0 (exportWith u V) t

β-redᴸ : ∀ {s α} → s # α → Tmᴸ s α → Tmᴸ s α
β-redᴸ s# (ƛ fct · arg) = substTmᴸ s# (exportWith arg V) fct
β-redᴸ _  t             = t

-- While we can use the general technique we used for the nominal style
-- we can also take advantage of this canonical representation.
-- We do so in the EqTmᴸ module below.
-- Note however that while EqTmᴸ is more efficient and simpler the functions
-- in this module CmpTmᴸ are more general (does not require the same starting binder).
module CmpTmᴸ where
  cmpTmᴸ : ∀ {α β s₁ s₂} → Cmp° Name α β → Tmᴸ s₁ α → Tmᴸ s₂ β → Bool
  cmpTmᴸ Δ (V x₁)      (V x₂)      = Δ x₁ x₂
  cmpTmᴸ Δ (t₁ · u₁)   (t₂ · u₂)   = cmpTmᴸ Δ t₁ t₂ ∧ cmpTmᴸ Δ u₁ u₂
  cmpTmᴸ Δ (ƛ t₁)     (ƛ t₂)      = cmpTmᴸ (extendNameCmp Δ) t₁ t₂
  cmpTmᴸ Δ (Let t₁ u₁) (Let t₂ u₂) = cmpTmᴸ Δ t₁ t₂ ∧ cmpTmᴸ (extendNameCmp Δ) u₁ u₂
  cmpTmᴸ _ (` κ₁)      (` κ₂)      = κ₁ ==ᶜ κ₂
  cmpTmᴸ _ _ _ = false

  _==Tmᴸ_ : ∀ {α s₁ s₂} → Tmᴸ s₁ α → Tmᴸ s₂ α → Bool
  _==Tmᴸ_ = cmpTmᴸ _==ᴺ_

module EqTmᴸ where
  _==Tmᴸ_ : ∀ {α s} → Tmᴸ s α → Tmᴸ s α → Bool
  V x₁      ==Tmᴸ V x₂      = x₁ ==ᴺ x₂
  (t₁ · u₁) ==Tmᴸ (t₂ · u₂)  = t₁ ==Tmᴸ t₂ ∧ u₁ ==Tmᴸ u₂
  ƛ t₁      ==Tmᴸ ƛ t₂      = t₁ ==Tmᴸ t₂
  Let t₁ u₁ ==Tmᴸ Let t₂ u₂  = t₁ ==Tmᴸ t₂ ∧ u₁ ==Tmᴸ u₂
  (` κ₁)    ==Tmᴸ (` κ₂)    = κ₁ ==ᶜ κ₂
  _         ==Tmᴸ _         = false

import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps)
open import Coinduction
module KAM where -- Krivine Abstract Machine
  open Pa using (now; later; never)

  Tmø = Tmᴸ (0 ᴮ) ø

  Stack = List Tmø

  infix 10 _★_
  _★_ : Tmø → Stack → Tmø ⊥
  (t · u)   ★ π        = t ★ (u ∷ π)                -- push
  (ƛ t)     ★ (u ∷ π)  = later (♯ (t [0≔ u ] ★ π)) -- grab
  (Let t u) ★ π        = later (♯ (u [0≔ t ] ★ π))
  v         ★ []       = now v
  (V x)     ★ _        = Nameø-elim x
  (` _)     ★ _        = never

module Tmᴿ⇒Tmᴸ (Atm : Set) (_==ᴬ_ : (x y : Atm) → Bool) where
  open NomPa.Examples.Raw.DataType Atm
  record Env s α : Set where
    constructor _,_
    field
      trᴬ : Atm → Name α
      s#  : s # α
  extEnv : ∀ {s α} → Atm → Env s α → Env (sucᴮ s) (s ◅ α)
  extEnv bᴬ (trᴬ , s#) = (trᴬ′ , suc# s#)
    where trᴬ′ = λ a → if bᴬ ==ᴬ a then nameᴮ _ else coerceᴺ (⊆-# s#) (trᴬ a)

  open Env
  ! : ∀ {α s} → Env s α → Tmᴿ → Tmᴸ s α
  ! Δ (V x) = V (trᴬ Δ x)
  ! Δ (ƛ bᴬ t) = ƛ (! (extEnv bᴬ Δ) t)
  ! Δ (t · u) = ! Δ t · ! Δ u

  conv : ∀ {α} k → (Atm → Name α) → (k ᴮ) # α → Tmᴿ → Tmᴸ (k ᴮ) α
  conv _ trˢ k# = ! (trˢ , k#)

module Parser where
  open NomPa.Examples.Raw.DataType String
  open Tmᴿ⇒Tmᴸ String _==_ using (conv)

  convø? : Tmᴿ →? Tmᴸ (0 ᴮ) ø
  convø? = map? (rerootTmᴸ 1 0) ∘ closeTmᴸ? ∘ conv 1 (const (0 ᴺ)) (suc# (0 ᴮ #ø))

  conv? : Tmᴿ →? (∀ {α} n → Tmᴸ (n ᴮ) α)
  conv? = map? (λ t {η} n → shiftøTmᴸ n (rerootTmᴸ 1 0 t)) ∘ closeTmᴸ? ∘ conv 1 (const (0 ᴺ)) (suc# (0 ᴮ #ø))

  open ParseConv convø? public renaming (parseConv? to parseTmᴸø?; parseConv to parseTmᴸø; TmOk to TmᴸøOk)
  open ParseConv conv? public renaming (parseConv? to parseTmᴸ?; parseConv to parseTmᴸ; TmOk to TmᴸOk)

open Parser public using (parseTmᴸ?; parseTmᴸ; TmᴸOk; parseTmᴸø?; parseTmᴸø; TmᴸøOk)

module Tmᴸ⇒Tmᴺ where
  ⟪_⟫ : ∀ {α s} → Tmᴸ s α → Tmᴺ α
  ⟪ V x     ⟫ = V x
  ⟪ ƛ t     ⟫ = ƛ _ ⟪ t ⟫
  ⟪ t · u   ⟫ = ⟪ t ⟫ · ⟪ u ⟫
  ⟪ Let t u ⟫ = ƛ _ ⟪ u ⟫ · ⟪ t ⟫
  ⟪ ` κ     ⟫ = ` κ
open Tmᴸ⇒Tmᴺ public renaming (⟪_⟫ to convTmᴸ⇒Tmᴺ)

showTmᴸ : ∀ {s} → Tmᴸ s ø → String
showTmᴸ = showTmᴺ ∘ convTmᴸ⇒Tmᴺ

module TraverseTmᴺ⇒Tmᴸ {E}   (E-app : Applicative E)
                       {Env : World → Binder → World → Set}
                       (trName : ∀ {α s β} → Env α s β → Name α → E (Tmᴸ s β))
                       (extEnv : ∀ {α s₂ β} s₁ (Δ : Env α s₂ β) → Env (s₁ ◅ α) (sucᴮ s₂) (s₂ ◅ β)) where

  open Applicative E-app

  tr : ∀ {α s β} → Env α s β → Tmᴺ α → E (Tmᴸ s β)
  tr Δ (V x)       = trName Δ x
  tr Δ (t · u)     = pure _·_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (ƛ s t)     = pure ƛ ⊛ tr (extEnv s Δ) t
  tr Δ (Let s t u) = pure Let ⊛ tr Δ t ⊛ tr (extEnv s Δ) u
  tr _ (` κ)       = pure $ ` κ

module ConvTmᴺ⇒Tmᴸ where
  renameTmᴸ⇒Tmᴺ : ∀ {α β s} → s # β → (α →ᴺ β) → Tmᴺ α → Tmᴸ s β
  renameTmᴸ⇒Tmᴺ s#β trName = tr (trName , s#β)
    where
      Env : World → Binder → World → Set
      Env α s β = RenameEnvᴸ s s α β
      open SubstEnvᴸ
      extEnv : ∀ {α s₂ β} s₁ (Δ : Env α s₂ β) → Env (s₁ ◅ α) (sucᴮ s₂) (s₂ ◅ β)
      extEnv _ = Renameᴸ.extEnvᴸ
      open TraverseTmᴺ⇒Tmᴸ id-app (λ Δ → V ∘′ trNameᴸ Δ) extEnv

  convTmᴺø⇒Tmᴸ : ∀ {s β} → s # β → Tmᴺ ø → Tmᴸ s β
  convTmᴺø⇒Tmᴸ s#β = renameTmᴸ⇒Tmᴺ s#β Nameø-elim

  convTmᴺø⇒Tmᴸø : ∀ s → Tmᴺ ø → Tmᴸ s ø
  convTmᴺø⇒Tmᴸø s = convTmᴺø⇒Tmᴸ (s #ø)
