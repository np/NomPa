open import NomPa.Record
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import Data.Indexed
open import Function.NP
open import Data.Product using (_×_;∃;_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; maybe)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Unit using (⊤)
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)

module NomPa.Encodings.NominalTypes (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa using (SynAbsᴰ)
open NomPa.Traverse nomPa
open Data.Indexed {_} {World}
  using (|Set|; |pure|; |liftA|; |liftA2|; _|→|_; _|↦|_;
         |List|; |Maybe|; |∀|)

𝔼 : Set₁
𝔼 = |Set| _

Nameᵉ : 𝔼
Nameᵉ = Name

νᵉ : 𝔼
νᵉ = Nameᵉ

Absᵉ : 𝔼 → 𝔼
Absᵉ = SynAbsᴺ

<ν>ᵉ_ : 𝔼 → 𝔼
<ν>ᵉ_ = Absᵉ

-- de Bruijn version!
Absᴰᵉ : 𝔼 → 𝔼
Absᴰᵉ = SynAbsᴰ

Neutralᵉ : Set → 𝔼
Neutralᵉ = |pure|

Neutral1ᵉ : (Set → Set) → (𝔼 → 𝔼)
Neutral1ᵉ = |liftA|

Neutral2ᵉ : (Set → Set → Set) → (𝔼 → 𝔼 → 𝔼)
Neutral2ᵉ = |liftA2|

infixr 0 _→ᵉ_ _↦ᵉ_ _⇒ᵉ_
infixr 1 _⊎ᵉ_
infixr 2 _×ᵉ_

_↦ᵉ_ : 𝔼 → 𝔼 → Set
_↦ᵉ_ = _|↦|_

_→ᵉ_ : 𝔼 → 𝔼 → 𝔼
_→ᵉ_ = _|→|_

_⇒ᵉ_ : 𝔼 → 𝔼 → 𝔼
(E₁ ⇒ᵉ E₂) α = ∀ {β} → α ⊆ β → (E₁ →ᵉ E₂) β

⇒-to-→ : ∀ {E₁ E₂} → (E₁ ⇒ᵉ E₂) ↦ᵉ (E₁ →ᵉ E₂)
⇒-to-→ f = f ⊆-refl

Coe : 𝔼 → Set
Coe E = ∀ {α β} → α ⊆ β → E α → E β

coerce-⇒ᵉ : ∀ {E₁ E₂} → Coe (E₁ ⇒ᵉ E₂)
coerce-⇒ᵉ pf f = f ∘ ⊆-trans pf

_×ᵉ_ : 𝔼 → 𝔼 → 𝔼
_×ᵉ_ = Neutral2ᵉ _×_

_⊎ᵉ_ : 𝔼 → 𝔼 → 𝔼
_⊎ᵉ_ = Neutral2ᵉ _⊎_

Listᵉ : 𝔼 → 𝔼
Listᵉ = Neutral1ᵉ List

Maybeᵉ : 𝔼 → 𝔼
Maybeᵉ = Neutral1ᵉ Maybe

1ᵉ : 𝔼
1ᵉ = Neutralᵉ ⊤

∀ᵉ : 𝔼 → Set
∀ᵉ = |∀|

Empty : 𝔼 → Set
Empty E = E ø

-- think about this:
--   F X ⊎ᵉ F Y ≡? F (X ⊎ᵉ Y)
-- this may explain why we can use data constructors
-- instead of _⊎ᵉ_.

module FreeVars where
  Fv : 𝔼 → Set
  Fv E = E ↦ᵉ Listᵉ Nameᵉ

  -- Combinators we do *not* have:
  --   * fvμᵉ
  --   * fv→ᵉ

  fv×ᵉ : ∀ {E₁ E₂} → Fv E₁ → Fv E₂ → Fv (E₁ ×ᵉ E₂)
  fv×ᵉ fv₁ fv₂ (x , y) = fv₁ x ++ fv₂ y

  fv⊎ᵉ : ∀ {E₁ E₂} → Fv E₁ → Fv E₂ → Fv (E₁ ⊎ᵉ E₂)
  fv⊎ᵉ fv₁ fv₂ = [ fv₁ , fv₂ ]′

  fvNeutralᵉ : ∀ {A} → Fv (Neutralᵉ A)
  fvNeutralᵉ _ = []

  fvNameᵉ : Fv Nameᵉ
  fvNameᵉ = [_]

  fvListᵉ : ∀ {E} → Fv E → Fv (Listᵉ E)
  fvListᵉ _   []       = []
  fvListᵉ fvE (x ∷ xs) = fvE x ++ fvListᵉ fvE xs

  fvMaybeᵉ : ∀ {E} → Fv E → Fv (Maybeᵉ E)
  fvMaybeᵉ fvE = maybe fvE []

  abstract -- only here for debugging purposes
    fvDummy : ∀ {A B : Set} → A → List B
    fvDummy = const []

  fvMap : ∀ {E₁ E₂} → (E₂ ↦ᵉ E₁) → Fv E₁ → Fv E₂
  fvMap f fvE₁ = fvE₁ ∘ f

{- A Nominal Signature:
   Example 2.2 from «Nominal Unification»

sort of atoms: vid
sort of data:  exp
function symbols:
  vr  : vid → exp
  app : exp × exp → exp
  fn  : <vid>exp → exp
  lv  : exp × <vid>exp → exp
  lf  : <vid>((<vid>exp) × exp) → exp
-}

module M₁ where
  data Exp : 𝔼 where
    vr  : νᵉ ↦ᵉ Exp
    app : Exp ×ᵉ Exp ↦ᵉ Exp
    fn  : <ν>ᵉ Exp ↦ᵉ Exp
    lv  : Exp ×ᵉ <ν>ᵉ Exp ↦ᵉ Exp
    lf  : <ν>ᵉ((<ν>ᵉ Exp) ×ᵉ Exp) ↦ᵉ Exp
  
  fv : Exp ↦ᵉ Listᵉ νᵉ
  fv (vr x)                  = [ x ]
  fv (app (t , u))           = fv t ++ fv u
  fv (fn (b , t))            = rm b (fv t)
  fv (lv (t , b , u))        = fv t ++ rm b (fv u)
  fv (lf (bf , (b , t) , u)) = rm bf (rm b (fv t) ++ fv u)
