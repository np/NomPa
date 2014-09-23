open import NomPa.Record
import NomPa.Examples.LC.DataTypes
open import Data.Product.NP
open import Data.Indexed
open import Function
open import Data.Star.NP renaming (_◅_ to _∷_; ε to [])
open import Relation.Binary.PropositionalEquality

-- This is connected to:
--   «The Derivative of a Regular Type is its Type of One-Hole Contexts»
--    by Conor McBride.
-- In particular the type StackFrame seems be buried in there.

-- Part of the confusion comes from the fact that one can interpret
-- a list of stack frames in two ways:
--  1) In one-hole contexts, the hole is buried deep into the context.
--     The hole hence corresponds to the nil of the list of stack frames.
--     The first stack frame being at the root of the tree.
--  2) In zippers, the pointers are reversed, the hole is holding its
--     context which goes up to the root of the tree.
--     The hole hence corresponds to the root of the tree.
--     The first stack frame being the closest to the hole.
--
-- When we add the binding structures, though, we remark that the
-- stack frames can be combined in two different ways. The two
-- chainings yielding to one-hole contexts and zipper contexts.

module NomPa.Examples.LC.Contexts (nomPa : NomPa) (Cst : Set) where

open NomPa nomPa
open NomPa.Examples.LC.DataTypes dataKit Cst

infix 7 _·₂-
data StackFrame α : World → Set where
  ƛ    : ∀ b → StackFrame α (b ◅ α)
  -·₁  : (u : Tm α) → StackFrame α α
  _·₂- : (t : Tm α) → StackFrame α α
  Let₁ : ∀ b (u : Tm (b ◅ α)) → StackFrame α α
  Let₂ : ∀ b (t : Tm α) → StackFrame α (b ◅ α)

defocusᶠ : ∀ {α β} → StackFrame α β → Tm β → Tm α
defocusᶠ (ƛ b)      t = ƛ b t
defocusᶠ (-·₁ u)    t = t · u
defocusᶠ (t ·₂-)    u = t · u
defocusᶠ (Let₁ b u) t = Let b t u
defocusᶠ (Let₂ b t) u = Let b t u

-- Zipper contexts (one-hole contexts that one hold from the inner of the hole)
ZCx : World → World → Set
ZCx = Star⁻¹ StackFrame
{- Which is isomorphic to:
data ZCx α : World → Set where
  []  : ZCx α α
  _∷_ : ∀ {β γ} (s : StackFrame β γ) (p : ZCx α β) → ZCx α γ

and also isomorphic to ZCxᴰ (see below the module ZCx⇔ZCxᴰ)
-}

defocusᶻ : ∀ {α β} → ZCx α β → Tm β → Tm α
defocusᶻ []      t = t
defocusᶻ (s ∷ z) t = defocusᶻ z (defocusᶠ s t)

Zipper : World → Set
Zipper α = ∃[ β ](ZCx α β × Tm β)

up : ∀ {α} → Zipper α → Tm α
up (_ , z , t) = defocusᶻ z t

-- One-hole contexts (that one hold from the root)
Cx : World → World → Set
Cx = Star StackFrame
{- Which is isomorphic to:
data Cx α : World → Set where
  []  : Cx α α
  _∷_ : ∀ {β γ} (s : StackFrame α β) (p : Cx β γ) → Cx α γ

and also isomorphic to Cxᴰ (see the module StackFrame★⇔Cxᴰ below)
-}

CxTm : World → Set
CxTm α = ∃[ β ](Cx α β × Tm β)

plug : ∀ {α β} → Cx α β → Tm β → Tm α
plug []      t = t
plug (s ∷ c) t = defocusᶠ s (plug c t)

cmap : ∀ {α β} → (Cx α |↦| Cx β) → CxTm α → CxTm β
cmap f (_ , c , t) = (_ , f c , t)

hole : ∀ {α} → Tm α → CxTm α
hole t = (_ , [] , t)

module TermExamples where
  id™ : ∀ {α} → Tm α
  id™ = ƛ (0 ᴮ) (V (0 ᴺ))

  c₁ : ∀ {α} → Tm α
  c₁ = id™ · id™

  c₂ : ∀ {α} → Tm α
  c₂ = id™ · id™ · id™

  t₁ : ∀ {α} → Tm α
  t₁ = Let (0 ᴮ) (Let (3 ᴮ) c₁ (V (3 ᴺ))) c₂

  t₂ : ∀ {α} → Tm α
  t₂ = Let (0 ᴮ) c₁ (Let (1 ᴮ) c₂ (V (1 ᴺ)))

module ZipperExamples where
 open TermExamples

 ptrV₁ : ∀ {α} → ZCx α (3 ᴮ ◅ α)
 ptrV₁ = Let₂ (3 ᴮ) c₁ ∷ Let₁ (0 ᴮ) c₂ ∷ []

 ptrV₂ : ∀ {α} → ZCx α (1 ᴮ ◅ 0 ᴮ ◅ α)
 ptrV₂ = Let₂ (1 ᴮ) c₂ ∷ Let₂ (0 ᴮ) c₁ ∷ []

 test-defocusᶻ-ptrV₁ : ∀ {α} → defocusᶻ ptrV₁ (V (3 ᴺ)) ≡ (t₁ {α}) 
 test-defocusᶻ-ptrV₁ = refl

 test-defocusᶻ-ptrV₂ : ∀ {α} → defocusᶻ ptrV₂ (V (1 ᴺ)) ≡ (t₂ {α}) 
 test-defocusᶻ-ptrV₂ = refl

data Cxᴰ α : (β : World) → Set where
  Hole  : Cxᴰ α α
  _·₁_  : ∀ {β}   (c : Cxᴰ α β) (u : Tm α) → Cxᴰ α β
  _·₂_  : ∀ {β}   (t : Tm α) (c : Cxᴰ α β) → Cxᴰ α β
  ƛ     : ∀ {β} b (c : Cxᴰ (b ◅ α) β) → Cxᴰ α β
  Let₁  : ∀ {β} b (c : Cxᴰ α β) (u : Tm (b ◅ α)) → Cxᴰ α β
  Let₂  : ∀ {β} b (t : Tm α) (c : Cxᴰ (b ◅ α) β) → Cxᴰ α β

CxᴰTm : World → Set
CxᴰTm α = ∃[ β ](Cxᴰ α β × Tm β)

-- Smart constructors

_·₁′_ : ∀ {α β} (c : Cx α β) (u : Tm α) → Cx α β
c ·₁′ u = -·₁ u ∷ c

_·₂′_ : ∀ {α β} (t : Tm α) (c : Cx α β) → Cx α β
t ·₂′ c = t ·₂- ∷ c

ƛ′ : ∀ {α β} b (c : Cx (b ◅ α) β) → Cx α β
ƛ′ b c = ƛ b ∷ c

Let₁′ : ∀ {α β} b (c : Cx α β) (u : Tm (b ◅ α)) → Cx α β
Let₁′ b c u = Let₁ b u ∷ c

Let₂′ : ∀ {α β} b (t : Tm α) (c : Cx (b ◅ α) β) → Cx α β
Let₂′ b t c = Let₂ b t ∷ c

module Cx⇔Cxᴰ where
 ⇒ : ∀ {α β} → Cx α β → Cxᴰ α β
 ⇒ [] = Hole
 ⇒ (ƛ b ∷ p) = ƛ b (⇒ p)
 ⇒ (-·₁ u ∷ p) = ⇒ p ·₁ u
 ⇒ (t ·₂- ∷ p) = t ·₂ ⇒ p
 ⇒ (Let₁ b u ∷ p) = Let₁ b (⇒ p) u
 ⇒ (Let₂ b t ∷ p) = Let₂ b t (⇒ p)

 ⇐ : ∀ {α β} → Cxᴰ α β → Cx α β
 ⇐ Hole = []
 ⇐ (c ·₁ t) = -·₁ t ∷ ⇐ c
 ⇐ (t ·₂ c) = t ·₂- ∷ ⇐ c
 ⇐ (ƛ b c) = ƛ b ∷ ⇐ c
 ⇐ (Let₁ b c u) = Let₁ b u ∷ ⇐ c
 ⇐ (Let₂ b t c) = Let₂ b t ∷ ⇐ c

data ZCxᴰ α : World → Set where
  Root : ZCxᴰ α α
  _·₁_ : ∀ {β} (z : ZCxᴰ α β) (u : Tm β) → ZCxᴰ α β
  _·₂_ : ∀ {β} (t : Tm β) (z : ZCxᴰ α β) → ZCxᴰ α β
  ƛ    : ∀ {β} b (z : ZCxᴰ α β) → ZCxᴰ α (b ◅ β)
  Let₁ : ∀ {β} b (z : ZCxᴰ α β) (u : Tm (b ◅ β)) → ZCxᴰ α β
  Let₂ : ∀ {β} b (t : Tm β) (z : ZCxᴰ α β) → ZCxᴰ α (b ◅ β)

module ZCx⇔ZCxᴰ where
  ⇒ : ∀ {α β} → ZCx α β → ZCxᴰ α β
  ⇒ [] = Root
  ⇒ (ƛ b ∷ p) = ƛ b (⇒ p)
  ⇒ (-·₁ u ∷ p) = (⇒ p) ·₁ u
  ⇒ (t ·₂- ∷ p) = t ·₂ (⇒ p)
  ⇒ (Let₁ b u ∷ p) = Let₁ b (⇒ p) u
  ⇒ (Let₂ b t ∷ p) = Let₂ b t (⇒ p)

  ⇐ : ∀ {α β} → ZCxᴰ α β → ZCx α β
  ⇐ Root = []
  ⇐ (ƛ b z) = ƛ b ∷ ⇐ z
  ⇐ (z ·₁ u) = -·₁ u ∷ ⇐ z
  ⇐ (t ·₂ z) = t ·₂- ∷ ⇐ z
  ⇐ (Let₁ b z u) = Let₁ b u ∷ ⇐ z
  ⇐ (Let₂ b t z) = Let₂ b t ∷ ⇐ z

module Cx⇒ZCx where
  rev₁ : ∀ {α β} → Cx α β → ZCx α β
  rev₁ = reverse id

  rev₂ : ∀ {α β} → Cx α β → ZCx α β
  rev₂ [] = []
  rev₂ (x ∷ xs) = rev₂ xs ◅◅ (x ∷ [])

  rev₃ : ∀ {α β} → Cx α β → ZCx α β
  rev₃ c₀ = rev' c₀ []
    where rev' : ∀ {α β γ} → Cx α β → ZCx γ α → ZCx γ β
          rev' []       ys = ys
          rev' (x ∷ xs) ys = rev' xs (x ∷ ys)

  rev₄ : ∀ {α β} → Cxᴰ α β → ZCxᴰ α β
  rev₄ = ZCx⇔ZCxᴰ.⇒ ∘ rev₁ ∘ Cx⇔Cxᴰ.⇐

module ZCx⇒Cx where
  rev₁ : ∀ {α β} → ZCx α β → Cx α β
  rev₁ = reverse id

  rev₂ : ∀ {α β} → ZCx α β → Cx α β
  rev₂ [] = []
  rev₂ (x ∷ xs) = rev₂ xs ◅◅ (x ∷ [])

  rev₃ : ∀ {α β} → ZCxᴰ α β → Cxᴰ α β
  rev₃ = Cx⇔Cxᴰ.⇒ ∘ rev₁ ∘ ZCx⇔ZCxᴰ.⇐

module PathBasedNavigation where
  open import Data.Maybe.NP
  open import Data.List
  open import NomPa.Examples.Path

  focusᵂ : ∀ {α} → Path → Tm α → World
  focusᵂ (ƛ ∷ p)    (ƛ _ t) = focusᵂ p t
  focusᵂ (Let₁ ∷ p) (Let _ t _) = focusᵂ p t
  focusᵂ (Let₂ ∷ p) (Let _ _ t) = focusᵂ p t
  focusᵂ (·₁ ∷ p)   (t · _) = focusᵂ p t
  focusᵂ (·₂ ∷ p)   (_ · t) = focusᵂ p t
  focusᵂ {α} _ _ = α

  focus? : (p : Path) → ∀ {α} (t : Tm α) → Maybe (Tm (focusᵂ p t))
  focus? []         t           = just t
  focus? (ƛ ∷ p)    (ƛ _ t)     = focus? p t
  focus? (·₁ ∷ p)   (t · _)     = focus? p t
  focus? (·₂ ∷ p)   (_ · t)     = focus? p t
  focus? (Let₁ ∷ p) (Let _ t _) = focus? p t
  focus? (Let₂ ∷ p) (Let _ _ t) = focus? p t
  focus? _          _           = nothing

  defocus : (p : Path) → ∀ {α} (t : Tm α) → Tm (focusᵂ p t) → Tm α
  defocus []         _           = id
  defocus (ƛ ∷ p)    (ƛ b t)    = ƛ b ∘′ defocus p t
  defocus (·₁ ∷ p)   (t · u)     = flip _·_ u ∘′ defocus p t
  defocus (·₂ ∷ p)   (t · u)     = _·_ t ∘′ defocus p u
  defocus (Let₁ ∷ p) (Let b t u) = (flip (Let b) u) ∘′ defocus p t
  defocus (Let₂ ∷ p) (Let b t u) = Let b t ∘′ defocus p u
  defocus _          t           = const t
