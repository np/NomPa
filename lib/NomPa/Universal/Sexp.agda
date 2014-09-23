open import NomPa.Record
module NomPa.Universal.Sexp (nomPa : NomPa) where

open import Data.Vec using (Vec; []; _∷_; [_])
open import Data.Nat using (ℕ)
open NomPa nomPa

module Sexp (Form : ℕ → Set) (BindingForm : ℕ → ℕ → Set) (Atom : Set) where
  data T α : Set where
    V : (x : Name α) → T α
    A : (a : Atom) → T α
    S : ∀ {a} (f : Form a) (xs : Vec (T α) a) → T α
    B : ∀ {a₁ a₂}
          (bf : BindingForm a₁ a₂) b
          (xs : Vec (T α) a₁)
          (ys : Vec (T (b ◅ α)) a₂)
        → T α

module Sexp↔Tm (Cst : Set) where
  import NomPa.Examples.LC.DataTypes
  open NomPa.Examples.LC.DataTypes dataKit Cst

  data Form : ℕ → Set where
    -·- : Form 2

  data BindingForm : ℕ → ℕ → Set where
    ƛ : BindingForm 0 1
    Let : BindingForm 1 1

  data Atom : Set where
    `_ : (κ : Cst) → Atom

  open Sexp Form BindingForm Atom

  _·′_ : ∀ {α} (t u : T α) → T α
  t ·′ u = S -·- (t ∷ u ∷ [])

  ƛ′ : ∀ {α} b (t : T (b ◅ α)) → T α
  ƛ′ b t = B ƛ b [] [ t ]

  Let′ : ∀ {α} b (t : T α) (u : T (b ◅ α)) → T α
  Let′ b t u = B Let b [ t ] [ u ]

  ⇒ : ∀ {α} → Tm α → T α
  ⇒ (V x)       = V x
  ⇒ (t · u)     = ⇒ t ·′ ⇒ u
  ⇒ (ƛ b t)     = ƛ′ b (⇒ t)
  ⇒ (Let b t u) = Let′ b (⇒ t) (⇒ u)
  ⇒ (` κ)       = A (` κ)

  ⇐ : ∀ {α} → T α → Tm α
  ⇐ (V x)      = V x
  ⇐ (A (` κ))  = ` κ
  ⇐ (S -·- (t ∷ u ∷ [])) = ⇐ t · ⇐ u
  ⇐ (B ƛ b [] (t ∷ [])) = ƛ b (⇐ t)
  ⇐ (B Let b (t ∷ []) (u ∷ [])) = Let b (⇐ t) (⇐ u)

  open import Relation.Binary.PropositionalEquality

  ⇐⇒ : ∀ {α} (t : Tm α) → ⇐ (⇒ t) ≡ t
  ⇐⇒ (V x)       = refl
  ⇐⇒ (t · u)     = cong₂ _·_ (⇐⇒ t) (⇐⇒ u)
  ⇐⇒ (ƛ b t)     = cong (ƛ b) (⇐⇒ t)
  ⇐⇒ (Let b t u) = cong₂ (Let b) (⇐⇒ t) (⇐⇒ u)
  ⇐⇒ (` κ)       = refl

  ⇒⇐ : ∀ {α} (t : T α) → ⇒ (⇐ t) ≡ t
  ⇒⇐ (V x)                = refl
  ⇒⇐ (A (` κ))            = refl
  ⇒⇐ (S -·- (t ∷ u ∷ [])) = cong₂ _·′_ (⇒⇐ t) (⇒⇐ u)
  ⇒⇐ (B ƛ b [] (t ∷ []))  = cong (ƛ′ b) (⇒⇐ t)
  ⇒⇐ (B Let b (t ∷ []) (u ∷ [])) = cong₂ (Let′ b) (⇒⇐ t) (⇒⇐ u)

  open import Function.Inverse

  Tm↔T : ∀ {α} → Tm α ↔ T α
  Tm↔T = record { to = →-to-⟶ ⇒; from = →-to-⟶ ⇐
                 ; inverse-of = record { left-inverse-of = ⇐⇒; right-inverse-of = ⇒⇐ } }
