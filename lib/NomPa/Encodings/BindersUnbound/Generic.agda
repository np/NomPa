open import NomPa.Record
import NomPa.Derived
import NomPa.Traverse
import NomPa.Encodings.BindersUnbound
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Function.NP
open import Data.Product.NP using (_×_;∃;_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

module NomPa.Encodings.BindersUnbound.Generic (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa
open NomPa.Encodings.BindersUnbound nomPa hiding (Listᵖ; module Example)

infixr 1 _`⊎`_
infixr 2 _`×`_
mutual
 data U : Set where
  `⊤` `⊥`    : U
  _`×`_ _`⊎`_ : (σ τ : U) → U
  `Rec`       : U
  `Name`      : U
  `Bind`      : (p : Uᵖ) (τ : U) → U
 data Uᵖ : Set where
  `⊤` `⊥`    : Uᵖ
  _`×`_ _`⊎`_ : (p q : Uᵖ) → Uᵖ
  `Rec`       : Uᵖ
  `Binder`    : Uᵖ
  `REC`       : (p : Uᵖ) → Uᵖ
  `Embed`     : (τ : U) → Uᵖ
  `Rebind`    : (p q : Uᵖ) → Uᵖ

module Rec (r : U) where
 mutual
  data ⟪_⟫ : U → 𝔼 where
   tt   : ∀ᵉ ⟪ `⊤` ⟫
   _,_  : ∀ {σ τ} → ∀ᵉ (⟪ σ ⟫ →ᵉ ⟪ τ ⟫ →ᵉ ⟪ σ `×` τ ⟫)
   inj₁ : ∀ {σ τ} → ⟪ σ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
   inj₂ : ∀ {σ τ} → ⟪ τ ⟫ ↦ᵉ ⟪ σ `⊎` τ ⟫
   roll : ⟪ r ⟫ ↦ᵉ ⟪ `Rec` ⟫
   V    : Name ↦ᵉ ⟪ `Name` ⟫
   bind : ∀ {P τ} → Bind ⟪ P ⟫ᵖ ⟪ τ ⟫ ↦ᵉ ⟪ `Bind` P τ ⟫
  data ⟪_⟫ᵖ : Uᵖ → ℙ where
   tt   : ∀ {α β} → ⟪ `⊤` ⟫ᵖ α β id
   _,_  : ∀ {σ τ α β Op₁ Op₂} → ⟪ σ ⟫ᵖ α β Op₁ → ⟪ τ ⟫ᵖ α β Op₂ → ⟪ σ `×` τ ⟫ᵖ α β (Op₂ ∘ Op₁)
   inj₁ : ∀ {σ τ} → ⟪ σ ⟫ᵖ ↦ᵖ ⟪ σ `⊎` τ ⟫ᵖ
   inj₂ : ∀ {σ τ} → ⟪ τ ⟫ᵖ ↦ᵖ ⟪ σ `⊎` τ ⟫ᵖ
   -- roll : ⟪ r ⟫ᵖ ↦ᵉ ⟪ `Rec` ⟫ᵖ
   V      : Binderᵖ ↦ᵖ ⟪ `Binder` ⟫ᵖ
   embed  : ∀ {E} → Embed ⟪ E ⟫ ↦ᵖ ⟪ `Embed` E ⟫ᵖ
   rebind : ∀ {P₁ P₂} → Rebind ⟪ P₁ ⟫ᵖ ⟪ P₂ ⟫ᵖ ↦ᵖ ⟪ `Rebind` P₁ P₂ ⟫ᵖ
   rec    : ∀ {P} → Rec ⟪ P ⟫ᵖ ↦ᵖ ⟪ `REC` P ⟫ᵖ

open Rec using (tt; _,_; inj₁; inj₂; roll; V; bind; embed; rebind; rec) renaming (⟪_⟫ to El; ⟪_⟫ᵖ to Elᵖ)

open import Data.List

module Common r where
  open Rec r using (⟪_⟫; ⟪_⟫ᵖ)

  bindersᵖ : ∀ {s α β Op} → ⟪ s ⟫ᵖ α β Op → List Binder
  bindersᵖ (V (binder b))     = [ b ]
  bindersᵖ (embed _)          = []
  bindersᵖ tt                 = []
  bindersᵖ (inj₁ p)           = bindersᵖ p
  bindersᵖ (inj₂ p)           = bindersᵖ p
  bindersᵖ (p₁ , p₂)          = bindersᵖ p₁ ++ bindersᵖ p₂
  bindersᵖ (rebind (p₁ , p₂)) = bindersᵖ p₁ ++ bindersᵖ p₂
  bindersᵖ (rec p)            = bindersᵖ p

  _◅ᵖ_ : ∀ {P α₀ β₀ Op₀} → Elᵖ r P α₀ β₀ Op₀ → World → World
  p ◅ᵖ α = bindersᵖ p ◅★ α

  open FreeVars
  mutual
    fv : ∀ {s} → Fv ⟪ s ⟫
    fv tt         = []
    fv (t , u)    = fv t ++ fv u
    fv (inj₁ t)   = fv t
    fv (inj₂ t)   = fv t
    fv (roll t)   = fv t
    fv (V x)      = [ x ]
    fv (bind (bind p e)) = fvO p ++ rmP p (fv e)

    fvO : ∀ {s α β Op} → ⟪ s ⟫ᵖ α β Op → List (Name α)
    fvO tt = []
    fvO (p , q) = fvO p ++ fvO q
    fvO (inj₁ p) = fvO p
    fvO (inj₂ p) = fvO p
    fvO (V _) = []
    fvO (embed (embed t)) = fv t
    fvO (rebind (p , q)) = fvO p ++ rmP p (fvO q)
    fvO (rec p) = rmP p (fvO p)

    rmP : ∀ {s α β γ Op} → ⟪ s ⟫ᵖ α β Op → List (Name (Op γ)) → List (Name γ)
    rmP tt = id
    rmP (p , q) = rmP p ∘ rmP q
    rmP (inj₁ p) = rmP p
    rmP (inj₂ p) = rmP p
    rmP (V (binder x)) = rm x
    rmP (embed (embed _)) = id
    rmP (rebind (p , q)) = rmP p ∘ rmP q
    rmP (rec p) = rmP p

  fvᵖ : ∀ {s} → Fvᵖ ⟪ s ⟫ᵖ
  fvᵖ p = mk (fvO p) [] (rmP p)

{-
module TraverseEl r
                  {E}   (E-app : Applicative E)
                  {Env} (trKit : TrKit Env (E ∘ Name)) where

 open Common
 open Applicative E-app
 open TrKit trKit

 ice : ∀ {A} → E A → A
 ice = {!!}

 mutual
  tr : ∀ {s α β} → Env α β → El r s α → E (El r s β)
  tr Δ tt             = pure tt
  tr Δ (t , u)        = pure _,_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (inj₁ t)       = pure inj₁ ⊛ tr Δ t
  tr Δ (inj₂ t)       = pure inj₂ ⊛ tr Δ t
  tr Δ (roll t)       = pure roll ⊛ tr Δ t
  tr Δ (bind (_ , p , t)) = pure (λ x y → bind (_ , x , y)) ⊛ {!trᵖ Δ p!} ⊛ tr (extEnvᵖ Δ p) t
  tr Δ (V x)          = pure V ⊛ trName Δ x

  trᵖ : ∀ {P α β γ Op} → Env α γ → Elᵖ r P α β Op → E (Elᵖ r P γ β Op)
  trᵖ Δ tt = {!!}
  trᵖ Δ (p , q) = {!!}
  trᵖ Δ (inj₁ p) = {!!}
  trᵖ Δ (inj₂ p) = {!!}
  trᵖ Δ (V (b , refl)) = pure (V (trBinder Δ b , {!!})) 
  trᵖ Δ (embed (e , refl)) = {!pure (λ x y → embed (x , y)) ⊛ tr Δ e ⊛ {!!}!}
  trᵖ Δ (rebind (δ , p₁ , p₂)) = pure (rebind ({!!} , ice (trᵖ {!!} p₁) , ice (trᵖ {!!} p₂)))
  trᵖ Δ (rec p) = {!!}

{-
  trᵖ : ∀ {P α β γ δ ε} → Env β ε → Elᵖ r P α β γ δ → E (Elᵖ r P α ε ? δ)
  trᵖ Δ tt = {!!}
  trᵖ Δ (p , q) = {!!}
  trᵖ Δ (inj₁ p) = {!!}
  trᵖ Δ (inj₂ p) = {!!}
  trᵖ Δ (V (b , refl)) = pure (V (trBinder Δ b , {!!})) 
  trᵖ Δ (embed (e , refl)) = {!pure (λ x y → embed (x , y)) ⊛ tr Δ e ⊛ {!!}!}
  trᵖ Δ (rebind (δ , p₁ , p₂)) = pure (rebind ({!!} , ice (trᵖ {!!} p₁) , ice (trᵖ {!!} p₂)))
  trᵖ Δ (rec p) = {!!}
-}

  extEnvᵖ : ∀ {P α β γ Op} (Δ : Env (Op α) γ) (p : Elᵖ r P α β Op) → Env ? {!{!ice (trᵖ Δ p)!} ◅ᵖ γ!}
  extEnvᵖ Δ tt = {!!}
  extEnvᵖ Δ (p , q) = {!!}
  extEnvᵖ Δ (inj₁ p) = {!!}
  extEnvᵖ Δ (inj₂ p) = {!!}
  extEnvᵖ Δ (V (b , refl)) = extEnv b Δ
  extEnvᵖ Δ (embed (_ , refl)) = Δ
  extEnvᵖ Δ (rebind (_ , p₁ , p₂)) = extEnvᵖ (extEnvᵖ Δ p₁) p₂
  extEnvᵖ Δ (rec p) = extEnvᵖ Δ p

-- module Generic r = TraverseAFGNameGen {⟪ r ⟫} {⟪ r ⟫} (λ η₁ η₂ → TraverseEl.tr r η₁ η₂)
-}

open import Data.Nat
open import Data.Vec as Vec

`Vecᵖ : ℕ → Uᵖ → Uᵖ
`Vecᵖ zero    _ = `⊤`
`Vecᵖ (suc n) P = P `×` `Vecᵖ n P

module Vecᵖ E where
  open Rec E using (⟪_⟫; ⟪_⟫ᵖ)

  Vecᵖ : ℕ → Uᵖ → ℙ
  Vecᵖ n P = ⟪ `Vecᵖ n P ⟫ᵖ

  `[] : ∀ {P α β} → Vecᵖ zero P α β id
  `[] = tt

  infixr 4 _`∷_
  _`∷_ : ∀ {n P α β Op₁ Op₂} → ⟪ P ⟫ᵖ α β Op₁ → Vecᵖ n P α β Op₂ → Vecᵖ (suc n) P α β (Op₂ ∘ Op₁)
  x `∷ xs = (x , xs)

`Listᵖ : ℕ → Uᵖ → Uᵖ
`Listᵖ zero    _ = `⊥`
`Listᵖ (suc n) P = `⊤` `⊎` (P `×` `Listᵖ n P)

module Listᵖ E where
  open Rec E using (⟪_⟫; ⟪_⟫ᵖ)
  open Common E

  Listᵖ : ℕ → Uᵖ → ℙ
  Listᵖ n P = ⟪ `Listᵖ n P ⟫ᵖ

  `[] : ∀ {n P α β} → Listᵖ (suc n) P α β id
  `[] = inj₁ tt

  infixr 4 _`∷_
  _`∷_ : ∀ {n P α β Op₁ Op₂} → ⟪ P ⟫ᵖ α β Op₁ → Listᵖ n P α β Op₂ → Listᵖ (suc n) P α β (Op₂ ∘ Op₁)
  x `∷ xs = inj₂ (x , xs)

  binders : ∀ {n k α β} (bs : Vec Binder n) → ⟪ `Listᵖ (n + 1 + k) `Binder` ⟫ᵖ α β (_◅★′_ (Vec.toList bs))
  binders [] = `[]
  binders (x ∷ xs) = V (binder x) `∷ binders xs

module Example (n : ℕ) where
  k = 4

  TmU : U
  TmU = `Name`
     `⊎` (`Rec` `×` `Rec`)
     `⊎` (`Bind` (`Listᵖ (k + 1 + n) `Binder`) `Rec`)

  Tm : 𝔼
  Tm = El TmU TmU

  open Listᵖ TmU
  open Rec TmU using (⟪_⟫; ⟪_⟫ᵖ)
  open Common TmU

  var : Name ↦ᵉ Tm
  var = inj₁ ∘′ V

  _·_ : ∀ᵉ (Tm →ᵉ Tm →ᵉ Tm)
  _·_ t u = inj₂ (inj₁ (roll t , roll u))

  ƛ : ∀ {α} b → Tm (b ◅ α) → Tm α
  ƛ b t = inj₂ (inj₂ (bind (bind (binders (b ∷ [])) (roll t))))

  ƛ² : ∀ {α} b₁ b₂ → Tm (b₂ ◅ b₁ ◅ α) → Tm α
  ƛ² b₁ b₂ t = inj₂ (inj₂ (bind (bind (binders (b₁ ∷ b₂ ∷ [])) (roll t))))

  ƛ★ : ∀ {α} (bs : Vec Binder k) → Tm (Vec.toList bs ◅★′ α) → Tm α
  ƛ★ bs t = inj₂ (inj₂ (bind (bind (binders bs) (roll t))))

  idTm : Tm ø
  idTm = ƛ (0 ᴮ) (var (0 ᴺ))

  apTm : Tm ø
  apTm = ƛ² (0 ᴮ) (1 ᴮ) (var (name◅… 1 0) · var (1 ᴺ))

  fvTm : Tm ↦ᵉ Listᵉ Nameᵉ
  fvTm = fv

{-
  open Generic
    renaming (rename       to renameTm;
              rename?      to renameTm?;
              export?      to exportTm?;
              close?       to closeTm?;
              coerce       to coerceTm;
              coerceø      to coerceøTm;
              renameCoerce to renameCoerceTm;
              renameA      to renameTmA)
-}
