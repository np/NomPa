import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Encodings.NominalTypes
open import NomPa.Record
open import Function.NP
open import Data.Product.NP using (_×_;∃;_,_;proj₁;proj₂)
open import Data.Sum
open import Data.Nat
open import Data.Empty
open import Data.Maybe.NP
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality

module NomPa.Encodings.AlphaCaml (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa
private
  module NomTypes = NomPa.Encodings.NominalTypes nomPa
open NomTypes public
  using (𝔼; _×ᵉ_; _⊎ᵉ_; _→ᵉ_; _↦ᵉ_; ∀ᵉ; Neutralᵉ;
         Neutral1ᵉ; Neutral2ᵉ; Nameᵉ; Listᵉ; Maybeᵉ; 1ᵉ)

ℙ : Set₁
ℙ = (α β : World) (Op : World → World) → Set

module M where
  Binderᵖ : ℙ
  Binderᵖ _ _ Op = ∃[ b ](Op ≡ _◅_ b)

  -- de Bruijn version!
  Binderᴰᵖ : ℙ
  Binderᴰᵖ _ _ Op = Op ≡ _↑1

  Outerᵖ : 𝔼 → ℙ
  Outerᵖ E α _ Op = E α × Op ≡ id

  Innerᵖ : 𝔼 → ℙ
  Innerᵖ E _ β Op = E β × Op ≡ id

  Neutralᵖ : Set → ℙ
  Neutralᵖ A _ _ Op = A × Op ≡ id
-- Neutralᵖ A ≡ Innerᵖ (Neutralᵉ A)
--            ≡ Outerᵖ (Neutralᵉ A)

  <_> : ℙ → 𝔼
  < P > α = ∃[ Op ](P α (Op α) Op)

data Binderᵖ : ℙ where
  binder : ∀ {α β} b → Binderᵖ α β (_◅_ b)

-- de Bruijn version!
data Binderᴰᵖ : ℙ where
  binder : ∀ {α β} → Binderᴰᵖ α β _↑1

data Outerᵖ (E : 𝔼) : ℙ where
  outer : ∀ {α β} (e : E α) → Outerᵖ E α β id

data Innerᵖ (E : 𝔼) : ℙ where
  inner : ∀ {α β} (e : E β) → Innerᵖ E α β id

data Neutralᵖ (A : Set) : ℙ where
  neutral : ∀ {α β} (x : A) → Neutralᵖ A α β id

data <_> (P : ℙ) : 𝔼 where
  mk<_> : ∀ {α Op} (p : P α (Op α) Op) → < P > α

∀ᵖ : ℙ → Set
∀ᵖ P = ∀ {α β Op} → P α β Op

infixr 0 _→ᵖ_ _↦ᵖ_
_→ᵖ_ : ℙ → ℙ → ℙ
_→ᵖ_ P₁ P₂ α β Op = P₁ α β Op → P₂ α β Op

_↦ᵖ_ : ℙ → ℙ → Set
_↦ᵖ_ P₁ P₂ = ∀ᵖ (P₁ →ᵖ P₂)

infixr 4 _,_
infixr 2 _×ᵖ_
data _×ᵖ_ (P₁ P₂ : ℙ) : ℙ where
  _,_ : ∀ {Op₁ Op₂ α β}
        → P₁ α β Op₁
        → P₂ α β Op₂
        → (P₁ ×ᵖ P₂) α β (Op₂ ∘ Op₁)

{-
record _×ᵖ_ (P₁ P₂ : ℙ) α β Op : Set where
  constructor _,_
  field
    {Op-def} : Op ≡ Op₂ ∘ Op₁
    proj₁ᵖ    : P₁ α β Op₁
    proj₂ᵖ    : P₂ α β Op₂
-}

infixr 1 _⊎ᵖ_
_⊎ᵖ_ : ℙ → ℙ → ℙ
(P₁ ⊎ᵖ P₂) α β Op = P₁ α β Op ⊎ P₂ α β Op
-- data _⊎ᵖ_ (P₁ : ℙ) (P₂ : ℙ) : ℙ where
--   inj₁ : P₁ ↦ᵖ (P₁ ⊎ᵖ P₂)
--   inj₂ : P₂ ↦ᵖ (P₁ ⊎ᵖ P₂)

1ᵖ : ℙ
1ᵖ = Neutralᵖ ⊤

data Listᵖ (P : ℙ) : ℙ where
  -- 1ᵖ provides the Op ≡ id
  [] : 1ᵖ ↦ᵖ Listᵖ P
  -- using →ᵉ instead of ×ᵖ would not put Op ≡ Op₁ ∘ Op₂
  ∷  : P ×ᵖ Listᵖ P ↦ᵖ Listᵖ P

open import Data.List
open import Data.Maybe

module FreeVars where
  open NomTypes.FreeVars public

  record Fv′ᵖ α β (Op : World → World) : Set where
    constructor mk
    field
      fvO : List (Name α)
      fvI : List (Name β)
      rmP : ∀ {γ} → List (Name (Op γ)) → List (Name γ)

  Fvᵖ : ℙ → Set
  Fvᵖ P = P ↦ᵖ Fv′ᵖ

  fv<> : ∀ {P} → Fvᵖ P → Fv < P >
  fv<> fvᵖ mk< p > with fvᵖ p
  ... | mk fvO fvI rmP = fvO ++ rmP fvI

  abstract -- only here for debugging purposes
    fvᵖdummy : ∀ {A : Set} {α β Op} → A → Fv′ᵖ α β Op
    fvᵖdummy _ = mk [] [] (const [])

  fvᵖMap : ∀ {P Q} → (Q ↦ᵖ P) → Fvᵖ P → Fvᵖ Q
  fvᵖMap f fvP = fvP ∘ f

  fvBinderᵖ : Fvᵖ Binderᵖ
  fvBinderᵖ (binder b) = mk [] [] (rm b)

  fvBinderᴰᵖ : Fvᵖ Binderᴰᵖ
  fvBinderᴰᵖ binder = mk [] [] rm₀

  _++ᵖ_ : ∀ {α β Op₁ Op₂} → Fv′ᵖ α β Op₁ → Fv′ᵖ α β Op₂ → Fv′ᵖ α β (Op₂ ∘ Op₁)
  mk fvO₁ fvI₁ rmP₁ ++ᵖ mk fvO₂ fvI₂ rmP₂ = mk (fvO₁ ++ fvO₂) (fvI₁ ++ fvI₂) (rmP₁ ∘ rmP₂)

  fv×ᵖ : ∀ {P₁ P₂} → Fvᵖ P₁ → Fvᵖ P₂ → Fvᵖ (P₁ ×ᵖ P₂)
  fv×ᵖ fv₁ fv₂ (p₁ , p₂) = fv₁ p₁ ++ᵖ fv₂ p₂

  fv⊎ᵖ : ∀ {P₁ P₂} → Fvᵖ P₁ → Fvᵖ P₂ → Fvᵖ (P₁ ⊎ᵖ P₂)
  fv⊎ᵖ fv₁ fv₂ = [ fv₁ , fv₂ ]′

  fvInnerᵖ : ∀ {E} → Fv E → Fvᵖ (Innerᵖ E)
  fvInnerᵖ fvE (inner x) = mk [] (fvE x) id

  fvOuterᵖ : ∀ {E} → Fv E → Fvᵖ (Outerᵖ E)
  fvOuterᵖ fvE (outer x) = mk (fvE x) [] id

  fvNeutralᵖ : ∀ {A} → Fvᵖ (Neutralᵖ A)
  fvNeutralᵖ (neutral _) = mk [] [] id

  fv1ᵖ : Fvᵖ 1ᵖ
  fv1ᵖ = fvNeutralᵖ

  fvListᵖ : ∀ {P : ℙ} → Fvᵖ P → Fvᵖ (Listᵖ P)
  fvListᵖ fvP ([] k) = fvNeutralᵖ k
  fvListᵖ fvP (∷ (x , xs)) = fvP x ++ᵖ fvListᵖ fvP xs

module LC-Example where
  data Tm : 𝔼 where
    var  : Nameᵉ ↦ᵉ Tm
    app  : (Tm ×ᵉ Tm) ↦ᵉ Tm
    lam  : < Binderᵖ ×ᵖ Innerᵖ Tm > ↦ᵉ Tm
    let′ : < Binderᵖ ×ᵖ Outerᵖ Tm ×ᵖ Innerᵖ Tm > ↦ᵉ Tm

  module Ctors where
    _·_ : Tm ↦ᵉ Tm →ᵉ Tm
    _·_ t u = app (t , u)

    ƛ : ∀ {α} b → Tm (b ◅ α) → Tm α
    ƛ b t = lam mk< binder b , inner t >

    Let : ∀ {α} b → Tm α → Tm (b ◅ α) → Tm α
    Let b t u = let′ mk< binder b , outer t , inner u >

  module Terms where
    open Ctors
    idTm : Tm ø
    idTm = ƛ (0 ᴮ) (var (0 ᴺ))
    apTm : Tm ø
    apTm = ƛ (0 ᴮ) (ƛ (1 ᴮ) (var (0 ᴺ¹) · var (1 ᴺ)))

module LC-Example2 where
  TmF : 𝔼 → 𝔼
  TmF Tm =  {-var-} Nameᵉ
         ⊎ᵉ {-app-} (Tm ×ᵉ Tm)
         ⊎ᵉ {-lam-} < Binderᵖ ×ᵖ Innerᵖ Tm >
         ⊎ᵉ {-let-} < Binderᵖ ×ᵖ Outerᵖ Tm ×ᵖ Innerᵖ Tm >

{-
  postulate
    μᵉ : (𝔼 → 𝔼) → 𝔼
    roll   : ∀ {F} → F (μᵉ F) ↦ᵉ μᵉ F
    unroll : ∀ {F} → μᵉ F ↦ᵉ F (μᵉ F)
  Tm = μᵉ TmF
-}

  data Tm : 𝔼 where
    roll : TmF Tm ↦ᵉ Tm
  unrollTm : Tm ↦ᵉ TmF Tm
  unrollTm (roll x) = x

  module Ctors where
    var : Nameᵉ ↦ᵉ Tm
    var = roll ∘′ inj₁

    app : Tm ↦ᵉ Tm →ᵉ Tm
    app t u = roll (inj₂ (inj₁ (t , u)))

    lam : ∀ {α} b → Tm (b ◅ α) → Tm α
    lam b t = roll (inj₂ (inj₂ (inj₁ mk< binder b , inner t >)))

  module Terms where
    open Ctors
    idTm : Tm ø
    idTm = lam (0 ᴮ) (var (0 ᴺ))
    apTm : Tm ø
    apTm = lam (0 ᴮ) (lam (1 ᴮ) (app (var (0 ᴺ¹)) (var (1 ᴺ))))

module ML-Example where
  Tag = ℕ

  mutual
    data Tm : 𝔼 where
      var   : Nameᵉ ↦ᵉ Tm
      app   : Tm ×ᵉ Tm ↦ᵉ Tm
      lam   : < Binderᵖ ×ᵖ Innerᵖ Tm > ↦ᵉ Tm
      ctor  : Neutralᵉ Tag ×ᵉ Listᵉ Tm ↦ᵉ Tm
      let′  : < Binderᵖ ×ᵖ Outerᵖ Tm ×ᵖ Innerᵖ Tm > ↦ᵉ Tm
      rec   : < Listᵖ (Binderᵖ ×ᵖ Innerᵖ Tm) ×ᵖ Innerᵖ Tm > ↦ᵉ Tm
      match : Tm ×ᵉ Listᵉ Branch ↦ᵉ Tm

    Branch : 𝔼
    Branch = < Pa ×ᵖ Innerᵖ (Maybeᵉ Tm) ×ᵖ Innerᵖ Tm >

    data Pa : ℙ where
      wildcard : 1ᵖ ↦ᵖ Pa
      binder   : Binderᵖ ↦ᵖ Pa
      pair     : Pa ×ᵖ Pa ↦ᵖ Pa
      ctor     : Neutralᵖ Tag ×ᵖ Listᵖ Pa ↦ᵖ Pa
      as       : Pa ×ᵖ Binderᵖ ↦ᵖ Pa

module ML-Example2 where
  Tag = ℕ

  module Types (Tm : 𝔼) (Pa : ℙ) where
    mutual
      TmF : 𝔼
      TmF = {-var-} Nameᵉ
          ⊎ᵉ {-app-}   Tm ×ᵉ Tm
          ⊎ᵉ {-lam-}   < Binderᵖ ×ᵖ Innerᵖ Tm >
          ⊎ᵉ {-ctor-}  Neutralᵉ Tag ×ᵉ Listᵉ Tm
          ⊎ᵉ {-let-}   < Binderᵖ ×ᵖ Outerᵖ Tm ×ᵖ Innerᵖ Tm >
          ⊎ᵉ {-rec-}   < Listᵖ (Binderᵖ ×ᵖ Innerᵖ Tm) ×ᵖ Innerᵖ Tm >
          ⊎ᵉ {-match-} Tm ×ᵉ Listᵉ Branch

      Branch : 𝔼
      Branch = < Pa ×ᵖ Innerᵖ (Maybeᵉ Tm) ×ᵖ Innerᵖ Tm >

      PaF : ℙ
      PaF =  {-wildcard-} 1ᵖ
          ⊎ᵖ {-binder-}   Binderᵖ
          ⊎ᵖ {-pair-}     Pa ×ᵖ Pa
          ⊎ᵖ {-ctor-}     Neutralᵖ Tag ×ᵖ Listᵖ Pa
          ⊎ᵖ {-as-}       Pa ×ᵖ Binderᵖ

  mutual
    data Tm : 𝔼 where
      roll : Types.TmF Tm Pa ↦ᵉ Tm
    data Pa : ℙ where
      roll : Types.PaF Tm Pa ↦ᵖ Pa

  open Types Tm Pa

  unrollTm : Tm ↦ᵉ TmF
  unrollTm (roll x) = x
  unrollPa : Pa ↦ᵖ PaF
  unrollPa (roll x) = x

  open FreeVars
  mutual
    fvTmF : ℕ → Fv TmF
    fvTmF n = fv⊎ᵉ fvNameᵉ
             (fv⊎ᵉ (fv×ᵉ (fvTm n) (fvTm n))
             (fv⊎ᵉ (fv<> (fv×ᵖ fvBinderᵖ (fvInnerᵖ (fvTm n))))
             (fv⊎ᵉ (fv×ᵉ fvNeutralᵉ (fvListᵉ (fvTm n)))
             (fv⊎ᵉ (fv<> (fv×ᵖ fvBinderᵖ (fv×ᵖ (fvOuterᵖ (fvTm n)) (fvInnerᵖ (fvTm n)))))
             (fv⊎ᵉ (fv<> (fv×ᵖ (fvListᵖ (fv×ᵖ fvBinderᵖ (fvInnerᵖ (fvTm n)))) (fvInnerᵖ (fvTm n))))
             (fv×ᵉ (fvTm n) (fvListᵉ (fvBranch n))))))))

    fvTm : ℕ → Fv Tm
    fvTm zero    = fvDummy
    fvTm (suc n) = fvTmF n ∘ unrollTm

    fvBranch : ℕ → Fv Branch
    fvBranch n = fv<> (fv×ᵖ (fvPa n) (fv×ᵖ (fvInnerᵖ (fvMaybeᵉ (fvTm n))) (fvInnerᵖ (fvTm n))))

    fvPa : ℕ → Fvᵖ Pa
    fvPa zero    = fvᵖdummy
    fvPa (suc n) = fvᵖMap unrollPa (fvPaF n)

    fvPaF : ℕ → Fvᵖ PaF
    fvPaF n = fv⊎ᵖ fvNeutralᵖ
             (fv⊎ᵖ fvBinderᵖ
             (fv⊎ᵖ (fv×ᵖ (fvPa n) (fvPa n))
             (fv⊎ᵖ (fv×ᵖ fvNeutralᵖ (fvListᵖ (fvPa n)))
                    (fv×ᵖ (fvPa n) fvBinderᵖ))))

  module Ctors where
    var : Nameᵉ ↦ᵉ Tm
    var = roll ∘′ inj₁

    app : Tm ↦ᵉ Tm →ᵉ Tm
    app t u = roll (inj₂ (inj₁ (t , u)))

    lam : ∀ {α} b → Tm (b ◅ α) → Tm α
    lam b t = roll (inj₂ (inj₂ (inj₁ mk< binder b , inner t >)))

    unLam : ∀ {α} → Tm α →? (∃[ b ](Tm (b ◅ α)))
    unLam (roll (inj₂ (inj₂ (inj₁ mk< binder b , inner t >)))) = just (b , t)
    unLam _ = nothing

  module Terms where
    open Ctors

    idTm : Tm ø
    idTm = lam (0 ᴮ) (var (0 ᴺ))

    apTm : Tm ø
    apTm = lam (0 ᴮ) (lam (1 ᴮ) (app (var (0 ᴺ¹)) (var (1 ᴺ))))
