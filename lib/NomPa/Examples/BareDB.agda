open import Function
open import Data.List
open import Data.String renaming (_==_ to _==ˢ_)
open import Data.Nat.NP
open import Data.Maybe.NP
open import Data.Bool
import      Level as L
import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps; now; later; never)
open import Coinduction
open import NomPa.Examples.Raw
open import NomPa.Examples.Raw.Parser
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open NomPa.Examples.Raw.StringTerm

module NomPa.Examples.BareDB where

infixl 4 _·_
data Tmᴮ : Set where
  V : (x : ℕ) → Tmᴮ
  ƛ : (t : Tmᴮ) → Tmᴮ
  _·_ : (t u : Tmᴮ) → Tmᴮ
  `_ : (κ : ℕ) → Tmᴮ

appⁿ : Tmᴮ → List Tmᴮ → Tmᴮ
appⁿ = foldl _·_

_ℕᴮ : ℕ → Tmᴮ
n ℕᴮ = ƛ (ƛ (replicapp n (V 1) (V 0)))
  where replicapp : ℕ → Tmᴮ → Tmᴮ → Tmᴮ
        replicapp zero    t u = u
        replicapp (suc n) t u = t · replicapp n t u

-- closed term
CTmᴮ = Tmᴮ

-- either a variable or a closed term
VCTmᴮ = Tmᴮ

shiftVCTmᴮ : (k : ℕ) → VCTmᴮ → VCTmᴮ
shiftVCTmᴮ k (V x) = V (x + k)
shiftVCTmᴮ _ t     = t -- no need to shift a closed term

substCVarTmᴮ : (θ : (x : ℕ) → CTmᴮ) → (ℓ : ℕ) → (x : ℕ) → VCTmᴮ
substCVarTmᴮ θ ℓ x = if suc x <= ℓ then V x else shiftVCTmᴮ ℓ (θ (x ∸ ℓ))

substCTmᴮ : ((x : ℕ) → CTmᴮ) → Tmᴮ → CTmᴮ
substCTmᴮ θ = ! 0 where
  ! : ℕ → Tmᴮ → CTmᴮ
  ! ℓ (V x)     = substCVarTmᴮ θ ℓ x
  ! ℓ (t · u)   = ! ℓ t · ! ℓ u
  ! ℓ (ƛ t)     = ƛ (! (suc ℓ) t)
  -- ! ℓ (Let t u) = Let (! ℓ t) (! (suc ℓ) u)
  ! _ (` κ)     = ` κ

predWith : ∀ {A : Set} → A → (ℕ → A) → ℕ → A
predWith z _ 0       = z
predWith _ s (suc n) = s n

_[0≔_] : Tmᴮ → Tmᴮ → Tmᴮ
t [0≔ u ] = substCTmᴮ (predWith u V) t

module Parser where
  module Tmᴿ⇒Tmᴮ where
    Env : Set
    Env = String → ℕ
    extEnv : String → Env → Env
    extEnv b Δ s = if b ==ˢ s then 0 else suc (Δ s)
    ! : Env → Tmᴿˢ → Tmᴮ
    ! Δ (V x) = V (Δ x)
    ! Δ (ƛ b t) = ƛ (! (extEnv b Δ) t)
    ! Δ (t · u) = ! Δ t · ! Δ u

  conv? : Tmᴿˢ →? Tmᴮ
  conv? = just{-closeTmᴮ?-} ∘′ Tmᴿ⇒Tmᴮ.! (const 0)

  open ParseConv conv? public renaming (parseConv? to parseTmᴮ?; parseConv to parseTmᴮ; TmOk to TmᴮOk)

open Parser public using (parseTmᴮ?; parseTmᴮ; TmᴮOk)

data Frame : Set where
  arg fct : Tmᴮ → Frame

Stack = List Frame

module KAM where -- Krivine Abstract Machine
  -- slightly modified to have CBV primitives

  infix 10 _★_
  _★_ : Tmᴮ → Stack → Tmᴮ ⊥
  (t · u)   ★ π           = t ★ (arg u ∷ π)            -- push
  (ƛ t)     ★ (arg u ∷ π) = later (♯ (t [0≔ u ] ★ π)) -- grab
  -- (Let t u) ★ π           = later (♯ (u [0≔ t ] ★ π))
  v         ★ []          = now v
  v         ★ (fct t ∷ π) = later (♯ (t ★ (arg v ∷ π)))

  -- ` 1 as function is `suc' and is CBV
  (` 1)     ★ (arg (` n) ∷ π) = later (♯ (`(suc n) ★ π))
  (` 1)     ★ (arg u ∷ π)     = later (♯ (u ★ (fct (` 1) ∷ π)))

--debug mode
--(` _)     ★ (arg _ ∷ _) = stuck-` where postulate stuck-` : Tmᴮ ⊥
--(V _)     ★ _           = stuck-V where postulate stuck-V : Tmᴮ ⊥
  _         ★ _           = never

  runTmᴮℕ : Tmᴮ → Tmᴮ ⊥
  runTmᴮℕ t = (t · ` 1 · ` 0) ★ []

-- CBV semantics
module AAM where -- Another Abstract Machine

  infix 10 _★_
  _★_ : Tmᴮ → Stack → Tmᴮ ⊥
  (t · u)   ★ π            = u ★ (fct t ∷ π)
  (ƛ t)     ★ (arg u ∷ π)  = later (♯ (t [0≔ u ] ★ π))
--(Let t u) ★ π            = t ★ (fct (ƛ u) ∷ π)
  v         ★ []           = now v
  v         ★ (fct u ∷ π)  = later (♯ (u ★ (arg v ∷ π)))

  -- (` 1) as a function is `suc'
  (` 1)     ★ (arg (` n) ∷ π) = later (♯ (`(suc n) ★ π))

-- debug versions
--(` n)     ★ (arg t ∷ π)     = stuck-` where postulate stuck-` : Tmᴮ ⊥
--(V _)     ★ _               = stuck-V where postulate stuck-V : Tmᴮ ⊥
  _         ★ _               = never

  runTmᴮℕ : Tmᴮ → Tmᴮ ⊥
  runTmᴮℕ t = (t · ` 1 · ` 0) ★ []

idᴮ : Tmᴮ
idᴮ = parseTmᴮ "λx.x"
trueᴮ : Tmᴮ
trueᴮ = parseTmᴮ "λx.λ_.x"
falseᴮ : Tmᴮ
falseᴮ = parseTmᴮ "λ_.λx.x"
pairᴮ : Tmᴮ
pairᴮ = parseTmᴮ "λx.λy.λf.f x y"
fstᴮ : Tmᴮ
fstᴮ = parseTmᴮ "λtrue.λp.p true" · trueᴮ
  -- = parseTmᴮ "λp.p (λx.λ_.x)"
sndᴮ : Tmᴮ
sndᴮ = parseTmᴮ "λfalse.λp.p false" · falseᴮ
  -- = parseTmᴮ "λp.p (λ_.λx.x)"
uncurryᴮ : Tmᴮ
uncurryᴮ = parseTmᴮ "λtrue.λfalse.λf.λp.f (p true) (p false)" · trueᴮ · falseᴮ
      -- = parseTmᴮ "λf.λp.f (p (λx.λ_.x)) (p (λ_.λx.x))"
appᴮ : Tmᴮ
appᴮ = parseTmᴮ "λf.λx.f x"
compᴮ : Tmᴮ
compᴮ = parseTmᴮ "λf.λg.λx.f (g x)"

-- ℕ = ∀ {α} → (α → α) → (α → α)
zeroᴮ : Tmᴮ
zeroᴮ = falseᴮ -- "λf.λx.x"
sucᴮ  : Tmᴮ
sucᴮ  = parseTmᴮ "λn.λf.λx.n f (f x)" -- λn.λf.n f ∘ f
addᴮ  : Tmᴮ
addᴮ  = parseTmᴮ "λsuc.λm.m suc" · sucᴮ
multᴮ : Tmᴮ
multᴮ = parseTmᴮ "λzero.λadd.λm.λn.m (add n) zero" · zeroᴮ · addᴮ

2+1ᴮ : Tmᴮ
2+1ᴮ = addᴮ · 2 ℕᴮ · 1 ℕᴮ
  
2×2ᴮ : Tmᴮ
2×2ᴮ = multᴮ · 2 ℕᴮ · 2 ℕᴮ
  
3×4ᴮ : Tmᴮ
3×4ᴮ = multᴮ · 3 ℕᴮ · 4 ℕᴮ

module KAMᴮ-tests where
  open KAM using (_★_; runTmᴮℕ)

  test-3×4 : run runTmᴮℕ 3×4ᴮ for 90 steps ≡ now (` 12)
  test-3×4 = ≡.refl

module AAMᴮ-tests where
  open AAM using (_★_; runTmᴮℕ)

  test-3×4 : run runTmᴮℕ 3×4ᴮ for 124 steps ≡ now (` 12)
  test-3×4 = ≡.refl
