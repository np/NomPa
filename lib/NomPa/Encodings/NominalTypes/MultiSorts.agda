open import NomPa.Record
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import Data.Indexed
open import Function.NP
open import Data.Product.NP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; maybe)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Unit using (⊤)
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)

-- There is an example to test this module in
-- NomPa.Encodings.NominalTypes.MultiSorts.Test

module NomPa.Encodings.NominalTypes.MultiSorts
  (nomPa : NomPa)
  (Sort : Set)
  (_==_ : (x y : Sort) → Bool)
 where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa using (SynAbsᴰ)
open NomPa.Traverse nomPa

open Data.Indexed {_} {Sort → World}
  using (|Set|; |pure|; |liftA|; |liftA2|; _|→|_; _|↦|_;
         |List|; |Maybe|)

𝔼 : Set₁
𝔼 = |Set| _

Nameᵉ : Sort → 𝔼
Nameᵉ κ Γ = Name (Γ κ)

_[_≔_] : (Sort → World) → Sort → World → (Sort → World)
(Γ [ κ ≔ α ]) κ′ = if κ == κ′ then α else Γ κ′

<_>ᵉ_ : Sort → 𝔼 → 𝔼
(< κ >ᵉ F) Γ = ∃[ b ] F (Γ [ κ ≔ b ◅ Γ κ ])

Neutralᵉ : Set → 𝔼
Neutralᵉ = |pure|

Neutral1ᵉ : (Set → Set) → (𝔼 → 𝔼)
Neutral1ᵉ = |liftA|

Neutral2ᵉ : (Set → Set → Set) → (𝔼 → 𝔼 → 𝔼)
Neutral2ᵉ = |liftA2|

infixr 0 _→ᵉ_
infixr 0 _↦ᵉ_
infixr 1 _⊎ᵉ_
infixr 2 _×ᵉ_

_→ᵉ_ : 𝔼 → 𝔼 → 𝔼
_→ᵉ_ = _|→|_

_×ᵉ_ : 𝔼 → 𝔼 → 𝔼
_×ᵉ_ = Neutral2ᵉ _×_

_⊎ᵉ_ : 𝔼 → 𝔼 → 𝔼
_⊎ᵉ_ = Neutral2ᵉ _⊎_

Listᵉ : 𝔼 → 𝔼
Listᵉ = Neutral1ᵉ List

Maybeᵉ : 𝔼 → 𝔼
Maybeᵉ = Neutral1ᵉ Maybe

_↦ᵉ_ : 𝔼 → 𝔼 → Set
_↦ᵉ_ = _|↦|_

1ᵉ : 𝔼
1ᵉ = Neutralᵉ ⊤

{-
-- Some nominal algebras

Untyped λ-calculus
<{v}, {Λ}, {var^(v→Λ),λ^((v→Λ)→Λ),app^(Λ×Λ→Λ)}>

First order logic
<{v}, {ι,Φ}, {var^(v→ι), 0^ι, 1^ι, +^(ι×ι→ι),
              =^(ι×ι→Φ), ⊃^(Φ×Φ→Φ), ∀^((v→Φ)→Φ)} >

Second order logic
<{v,v′}, {ι,Φ}, {var^(v→ι), var′^(v′→ι) , 0^ι, S^(ι→ι),
                 =^(ι×ι→Φ), ⊃^(Φ×Φ→Φ),
                 ∀^((v→Φ)→Φ), Λ^((v′→Φ)→Φ)} >

π-calculus
<{v}, {ι}, {0^ι, |^(ι×ι→ι), τ^(ι→ι), =^(v×v×ι→ι),
            ν^((v→ι)→ι), in^(v×(v→ι)→ι), out^(v×v×ι→ι)}>
-}

module FreeVars κ where
  Fv : 𝔼 → Set
  Fv E = E ↦ᵉ Listᵉ (Nameᵉ κ)

  -- Combinators we do *not* have:
  --   * fvμᵉ
  --   * fv→ᵉ

  fv×ᵉ : ∀ {E₁ E₂} → Fv E₁ → Fv E₂ → Fv (E₁ ×ᵉ E₂)
  fv×ᵉ fv₁ fv₂ (x , y) = fv₁ x ++ fv₂ y

  fv⊎ᵉ : ∀ {E₁ E₂} → Fv E₁ → Fv E₂ → Fv (E₁ ⊎ᵉ E₂)
  fv⊎ᵉ fv₁ fv₂ = [ fv₁ , fv₂ ]′

  fvNeutralᵉ : ∀ {A} → Fv (Neutralᵉ A)
  fvNeutralᵉ _ = []

  fvNameᵉ : Fv (Nameᵉ κ)
  fvNameᵉ = [_]

  fvListᵉ : ∀ {E} → Fv E → Fv (Listᵉ E)
  fvListᵉ     _   []       = []
  fvListᵉ {E} fvE (x ∷ xs) = fvE x ++ fvListᵉ {E} fvE xs

  fvMaybeᵉ : ∀ {E} → Fv E → Fv (Maybeᵉ E)
  fvMaybeᵉ fvE = maybe fvE []

  abstract -- only here for debugging purposes
    fvDummy : ∀ {A B : Set} → A → List B
    fvDummy = const []

  fvMap : ∀ {E₁ E₂} → (E₂ ↦ᵉ E₁) → Fv E₁ → Fv E₂
  fvMap f fvE₁ = fvE₁ ∘ f
