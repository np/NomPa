open import NomPa.Record
import NomPa.Encodings.AlphaCaml
import NomPa.Derived
open import Data.List
open import Data.Nat
open import Function.NP hiding (Π)
open import Data.Product.NP using (_×_;∃;_,_)
import Data.Indexed

module NomPa.Encodings.BindersUnbound (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa

module Cαml = NomPa.Encodings.AlphaCaml nomPa

open Cαml using (Innerᵖ; Outerᵖ; <_>)

-- All these are re-exported
open Cαml public using (𝔼; Nameᵉ; _×ᵉ_; _⊎ᵉ_; Neutralᵉ; _→ᵉ_; _↦ᵉ_; ∀ᵉ;
                        ℙ; Binderᵖ; _×ᵖ_; _,_; _⊎ᵖ_; Neutralᵖ; _→ᵖ_; _↦ᵖ_; ∀ᵖ;
                        Listᵉ; Maybeᵉ; Listᵖ; 1ᵉ; 1ᵖ; neutral; binder)

data Bind (P : ℙ) (E : 𝔼) : 𝔼 where
  bind : ∀ {α Op} (p : P α (Op α) Op) (e : E (Op α)) → Bind P E α

--Bind : ℙ → 𝔼 → 𝔼
-- Bind P E α = ∃[ Op ](P α (Op α) Op × E (Op α))
        -- ≅ ∃[ Op ](∃[ Op₁ ](Op ≡ Op₁ × P α (Op α) Op₁ × E (Op α)))
        -- ≅ ∃[ Op ](∃[ Op₁ ](∃[ Op₂ ](Op ≡ Op₂ ∘ Op₁ × P α (Op α) Op₁ × E (Op α) × Op₂ ≡ id)))
        -- ≡ ∃[ Op ](∃[ Op₁ ](∃[ Op₂ ](Op ≡ Op₂ ∘ Op₁ × P α (Op α) Op₁ × Innerᵖ E α (Op α) Op₂)))
        -- ≅ ∃[ Op ]((P ×ᵖ Innerᵖ E) α (Op α) Op)
        -- ≡ < P ×ᵖ Innerᵖ E > α

-- Embed : 𝔼 → ℙ
-- Embed = Outerᵖ
data Embed (E : 𝔼) : ℙ where
  embed : ∀ {α β} → E α → Embed E α β id

{- from «Binders Unbound»
Rebind P₁ P₂ acts like the pattern type
(P₁ , P₂), except that P₁ also scopes over P₂, so the binders in P₁
may be referred to by terms embedded within P₂. (The fact that P₁
scopes over P₂ in this way has no effect on the pattern portion of
P₂.) -}
infixr 4 _,_
data Rebind (P₁ P₂ : ℙ) : ℙ where
  _,_ : ∀ {Op₁ Op₂ α β} → P₁ α β Op₁ → P₂ (Op₁ α) β Op₂ → Rebind P₁ P₂ α β (Op₂ ∘ Op₁)

{- from «Binders Unbound»
In Rec P, names in the pattern P scope recursively
over any terms embedded in P itself. However, Rec P itself is
also a pattern, so names in P also scope externally over any term
that binds Rec P . Intuitively, Rec is just a “recursive” version of
Rebind.
-}
Rec : ℙ → ℙ
Rec P α β Op = P (Op α) β Op

module FreeVars where
  -- hum there seems to be an Agda bug behind this...
  -- If I import Fv from here, the Fv is still parameterized by NomPa
  open Cαml.FreeVars public using ({-Fv;-} fv×ᵉ; fv⊎ᵉ; fvNeutralᵉ; fvNameᵉ; mk;
                                   Fv′ᵖ; {-Fvᵖ;-} _++ᵖ_; fv×ᵖ; fv⊎ᵖ; fvBinderᵖ; fvInnerᵖ; fvOuterᵖ; fvNeutralᵖ)

  Fv : 𝔼 → Set
  Fv E = E ↦ᵉ Listᵉ Nameᵉ

  Fvᵖ : ℙ → Set
  Fvᵖ P = P ↦ᵖ Fv′ᵖ

  fvBind : ∀ {P} {E : 𝔼} → Fvᵖ P → Fv E → Fv (Bind P E)
  fvBind fvP fvE (bind p e) with fvP p
  ... | mk fvO fvI rmP = fvO ++ rmP (fvI ++ fvE e)

  fvEmbed : ∀ {E} → Fv E → Fvᵖ (Embed E)
  -- fvEmbed = Cαml.FreeVars.fvOuterᵖ
  fvEmbed fvE (embed e) = mk (fvE e) [] id

  fvRec : ∀ {P} → Fvᵖ P → Fvᵖ (Rec P)
  fvRec fvP p with fvP p
  ... | mk fvO fvI rmP = mk (rmP fvO) fvI rmP

  fvRebind : ∀ {P₁ P₂} → Fvᵖ P₁ → Fvᵖ P₂ → Fvᵖ (Rebind P₁ P₂)
  fvRebind fvP₁ fvP₂ (p₁ , p₂) with fvP₁ p₁ | fvP₂ p₂
  ... | mk fvO₁ fvI₁ rmP₁ | mk fvO₂ fvI₂ rmP₂ = mk (fvO₁ ++ rmP₁ fvO₂) (fvI₁ ++ fvI₂) (rmP₁ ∘ rmP₂)

module Example where
 mutual -- no mutual
  data Exp : 𝔼 where
    V   : Nameᵉ ↦ᵉ Exp
    Π   : Bind Tele Exp ↦ᵉ Exp
    ƛ   : Bind Tele Exp ↦ᵉ Exp
    _·_ : Exp ×ᵉ Listᵉ Exp ↦ᵉ Exp
    set : 1ᵉ ↦ᵉ Exp

  data Tele : ℙ where
    [] : 1ᵖ ↦ᵖ Tele
    ∷  : Rebind (Binderᵖ ×ᵖ Embed Exp) Tele ↦ᵖ Tele

 ⟨⟩ : ∀ {α β} → Tele α β id
 ⟨⟩ = [] (neutral _)

 ⟨_∶_⟩_ : ∀ {α β Op} b → Exp α → Tele (b ◅ α) β Op → Tele α β (Op ∘ _◅_ b)
 ⟨ b ∶ τ ⟩ Γ = ∷ ((binder b , embed τ) , Γ)

 ⟨_∶_⟩· : ∀ {α β} b → Exp α → Tele α β (_◅_ b)
 ⟨ b ∶ τ ⟩· = ⟨ b ∶ τ ⟩ ⟨⟩

 infix 0 _→′_ ƛ′_→′_

 _→′_ : ∀ {α Op} → Tele α (Op α) Op → Exp (Op α) → Exp α
 _→′_ Γ τ = Π (bind Γ τ)

 ƛ′_→′_ : ∀ {α Op} → Tele α (Op α) Op → Exp (Op α) → Exp α
 ƛ′_→′_ Γ e = ƛ (bind Γ e)

 _ᵛ : ∀ {α} n → Exp (n ᴮ ◅ α)
 n ᵛ = V (n ᴺ)

 _ᵛ¹ : ∀ {α} n → Exp (1 + n ◅… α)
 n ᵛ¹ = V (n ᴺ¹)

 module Ex₁ where
  -- «(A : Set) (x : A) →»
  tele : ∀ {α β} → Tele α β _
  tele = ⟨ A ᴮ ∶ set _ ⟩ ⟨ x ᴮ ∶ A ᵛ ⟩·
    where A = 0
          x = 1

  -- «Π (A : Set) (x : A) → A»
  ID™ : Exp ø
  ID™ = tele →′ 0 ᵛ¹

  -- «λ (A : Set) (x : A) → x»
  id™ : Exp ø
  id™ = ƛ′ tele →′ 1 ᵛ

 module Ex₂ where
  -- «Π (A : Set) (x : A) → A»
  ID™ : Exp ø
  ID™ = ⟨ A ᴮ ∶ set _ ⟩ ⟨ x ᴮ ∶ A ᵛ ⟩· →′ A ᵛ¹
    where A = 0
          x = 1

  -- «λ (A : Set) (x : A) → x»
  id™ : Exp ø
  id™ = ƛ′ ⟨ A ᴮ ∶ set _ ⟩ ⟨ x ᴮ ∶ A ᵛ ⟩· →′ x ᵛ
    where A = 0
          x = 1

 mutual
  fv : Exp ↦ᵉ Listᵉ Nameᵉ
  fv (V x) = [ x ]
  fv (Π (bind Γ t)) = fvTele Γ ++ rmTele Γ (fv t)
  fv (ƛ (bind Γ t)) = fvTele Γ ++ rmTele Γ (fv t)
  fv (_·_ (t , us)) = fv t ++ fvL us
  fv (set _) = []

  fvL : Listᵉ Exp ↦ᵉ Listᵉ Nameᵉ
  fvL [] = []
  fvL (t ∷ ts) = fv t ++ fvL ts

  fvTele : ∀ {α β Op} → Tele α β Op → List (Name α)
  fvTele ([] _) = []
  fvTele (∷ ((binder b , embed τ) , Γ)) = fv τ ++ rm b (fvTele Γ)

  rmTele : ∀ {α β Op} → Tele α β Op → List (Name (Op α)) → List (Name α)
  rmTele ([] (neutral _)) = id
  rmTele (∷ ((binder b , embed _) , Γ)) = rm b ∘ rmTele Γ
