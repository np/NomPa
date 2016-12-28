open import Relation.Binary  using (Reflexive; Transitive)
open import Function
open import Function.InstanceArguments
open import Data.Nat
open import Data.Unit using (⊤)
-- open import Reflection.NP using (ηⁿ)
open import Data.Product.NP
open import Category.Functor
            renaming (RawFunctor to Functor; module RawFunctor to Functor)
open import Category.Applicative
            renaming (RawApplicative to Applicative; module RawApplicative to Applicative)

module NomPa.Examples.LC.SymanticsTy
  where

record Box {a} (A : Set a) : Set a where
  constructor mk
  field get : A

module DataFunctorReader {E} where
  Reader : Set → Set
  Reader A = E → A
  functor : Functor Reader
  functor = record { _<$>_ = λ f g → f ∘ g }
  applicative : Applicative Reader
  applicative = record { pure = const; _⊛_ = _ˢ_ }

module BasicSyms (Repr : Set → Set) where
  record BaseArithSym : Set where
    constructor mk
    field
      nat : ℕ → Repr ℕ
      add : Repr (ℕ → ℕ → ℕ)
      mul : Repr (ℕ → ℕ → ℕ)

  AppSym' : Set₁
  AppSym' = ∀ {A B : Set} → Repr (A → B) → Repr A → Repr B

  AppSym : Set₁
  AppSym = Box AppSym'

  record SimpleSym : Set₁ where
    constructor mk
    infixl 2 _$$_
    field
      baseArithSym : BaseArithSym
      appSym       : AppSym
    open BaseArithSym baseArithSym public
    _$$_ : AppSym'
    _$$_ = Box.get appSym
    _+:_ : Repr ℕ → Repr ℕ → Repr ℕ
    x +: y = add $$ x $$ y
    _*:_ : Repr ℕ → Repr ℕ → Repr ℕ
    x *: y = mul $$ x $$ y

  -- lamS in Staged Haskell
  LamPure : Set₁
  LamPure = Box (∀ {A B} → (Repr A → Repr B) → Repr (A → B))

  AssertPos : Set₁
  AssertPos = ∀ {A} → Repr ℕ → Repr A → Repr A

module IdSyms where
  open BasicSyms id
  baseArithSym : BaseArithSym
  baseArithSym = record { nat = id; add = _+_; mul = _*_ }
  _$$_ : AppSym
  _$$_ = mk id
  simpleSym : SimpleSym
  simpleSym = record { baseArithSym = baseArithSym; appSym = _$$_ }
  ƛᴾ : LamPure
  ƛᴾ = mk id

module ApplicativeSyms {M Repr : Set → Set} (M-app : Applicative M) where
  open BasicSyms
  open Applicative M-app

  instance
    baseArithSym : {{sym : BaseArithSym Repr}} → BaseArithSym (M ∘ Repr)
    baseArithSym = record { nat = pure ∘ nat; add = pure add; mul = pure mul } where
      open BaseArithSym it

  appSym : {{sym : AppSym Repr}} → AppSym (M ∘ Repr)
  appSym {{mk appSym'}} = mk λ x y → pure appSym' ⊛ x ⊛ y

  simpleSym : {{sym : SimpleSym Repr}} → SimpleSym (M ∘ Repr)
  simpleSym {{mk ba app}} = mk (baseArithSym {{ba}}) (appSym {{app}})

  assertPos : {{_ : AssertPos Repr}} → AssertPos (M ∘ Repr)
  assertPos {{assertPos′}} nᴹ aᴹ = pure assertPos′ ⊛ nᴹ ⊛ aᴹ

open BasicSyms

J : (M Repr : Set → Set) (A : Set) → Set
J M Repr A = M (Repr A)

HV : (H : Set) (Repr : Set → Set) (A : Set) → Set
-- HV H = J (λ B → H → B)
HV H Repr A = H → Repr A

module HVSyms {H Repr} = ApplicativeSyms {λ B → H → B} {Repr} DataFunctorReader.applicative

hmap : ∀ {A H₁ H₂ Repr} → (H₂ → H₁) → HV H₁ Repr A → HV H₂ Repr A
hmap f g = g ∘ f

-- called runH in Staged Haskell
runHV : ∀ {Repr A} → HV ⊤ Repr A → Repr A
runHV m = m _

record Lib : Set₁ where
  constructor mk
  field
    HA : (Repr : Set → Set) (S A : Set) → Set

  LamM : Set₁
  LamM = ∀ {M Repr : Set → Set}{A B H} {{funM : Functor M}} {{sSym : SimpleSym Repr}}
              {{ƛᴾ : LamPure Repr}} → (∀ {S} → HV (HA Repr S A × H) Repr A → M (HV (HA Repr S A × H) Repr B))
            → M (HV H Repr (A → B))

  field
    lam : LamM
    href : ∀ {Repr S A H} → HV (HA Repr S A × H) Repr A
    var : ∀ {H M Repr A} {{M-app : Applicative M}} → HV H Repr A → M (HV H Repr A)
    weaken : ∀ {H H′ A : Set} {M Repr : Set → Set} {{M-app : Functor M}} → M (HV H Repr A) → M (HV (H′ × H) Repr A)

module M2
  (Cst : Set)
  (Env : Set)
  -- (_↑1 : Env → Env)
  (Binder : Set)
  (Ty : Set)
  (⟨_,_∶_⟩ : Env → Binder → Ty → Env)
  (_#_ : Binder → Env → Set)
  (⟨_⟩↑1⟨_⟩ : Env → Ty → Env)
  (_⊆_ : Env → Env → Set)
  (_⇒_ : Ty → Ty → Ty)
  (ε : Env)
  (⊆-ε     : ∀ {Γ} → ε ⊆ Γ)
  (⊆-# : ∀ {Γ b τ} → b # Γ → Γ ⊆ ⟨ Γ , b ∶ τ ⟩)
  (⊆-cong-,ᴰ : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊆ Γ₂ → ⟨ Γ₁ ⟩↑1⟨ τ ⟩ ⊆ ⟨ Γ₂ ⟩↑1⟨ τ ⟩)
  (⊆-trans : Transitive _⊆_)
  (_+1 : Env → Env)
  (⊆-+1↑1 : ∀ {Γ τ} → (Γ +1) ⊆ ⟨ Γ ⟩↑1⟨ τ ⟩)
  (_⊢_ : Env → Ty → Set) where

 record Sym : Set where
  infixl 6 _·_

  field
   _·_  : ∀ {Γ σ τ} → (t : Γ ⊢ (σ ⇒ τ)) (u : Γ ⊢ σ) → Γ ⊢ τ
   ƛᴺ    : ∀ {Γ σ τ} → (f : ∀ {b} → b # Γ → ⟨ Γ , b ∶ σ ⟩ ⊢ σ → ⟨ Γ , b ∶ σ ⟩ ⊢ τ) → Γ ⊢ (σ ⇒ τ)
   ƛᴰ    : ∀ {Γ σ τ} → (f : ⟨ Γ ⟩↑1⟨ σ ⟩ ⊢ σ → ⟨ Γ ⟩↑1⟨ σ ⟩ ⊢ τ) → Γ ⊢ (σ ⇒ τ)
   -- Let  : ∀ {α} → (t : Tm α) (u : Tm (α ↑1) → Tm (α ↑1)) → Tm α
   -- ƛ    : ∀ {α} → (t : ∀ {b} → Tm (b ◅ α) → Tm (b ◅ α)) → Tm α
   -- Let  : ∀ {α} → (t : Tm α) (u : ∀ {b} → Tm (b ◅ α) → Tm (b ◅ α)) → Tm α
   -- `_   : ∀ {α} → (κ : Cst) → Tm α

   coerce™ : ∀ {Γ₁ Γ₂ τ} → Γ₁ ⊆ Γ₂ → Γ₁ ⊢ τ → Γ₂ ⊢ τ
   shift™ : ∀ {Γ₁ Γ₂ τ} → (Γ₁ +1) ⊆ Γ₂ → Γ₁ ⊢ τ → Γ₂ ⊢ τ

  weaken™ : ∀ {Γ σ τ} → Γ ⊢ τ → ⟨ Γ ⟩↑1⟨ σ ⟩ ⊢ τ
  weaken™ = shift™ ⊆-+1↑1


{-
   ⊆-cong-↑1 : ∀ {α β}
                  (α⊆β : α ⊆ β)
                → α ↑1 ⊆ β ↑1
-}

 module Examplesᴺ (sym : Sym) where
  open Sym sym

  id™ : ∀ {τ} → ε ⊢ (τ ⇒ τ)
  id™ = ƛᴺ (λ _ x → x)

  true™ : ∀ {σ τ} → ε ⊢ (τ ⇒ (σ ⇒ τ))
  true™ = ƛᴺ (λ _ x → ƛᴺ (λ y# y → coerce™ (⊆-# y#) x))

  false™ : ∀ {σ τ} → ε ⊢ (σ ⇒ (τ ⇒ τ))
  false™ = ƛᴺ (λ _ x → ƛᴺ (λ _ y → y))

 module Examplesᴰ (sym : Sym) where
  open Sym sym

  id™ : ∀ {τ} → ε ⊢ (τ ⇒ τ)
  id™ = ƛᴰ (λ x → x)

  true™ : ∀ {σ τ} → ε ⊢ (τ ⇒ (σ ⇒ τ))
  true™ = ƛᴰ (λ x → ƛᴰ (λ y → weaken™ x))

  false™ : ∀ {σ τ} → ε ⊢ (σ ⇒ (τ ⇒ τ))
  false™ = ƛᴰ (λ x → ƛᴰ (λ y → y))

module M3 where
  -- open module F {M : Set → Set} {{x}} = Functor {_} {M} x
  -- open module A {M : Set → Set} {{x}} = Applicative {_} {M} x

  record HA (Repr : Set → Set) (S A : Set) : Set where
    constructor mk
    field
      ha : Repr A

  href : ∀ {Repr S A H} → HV (HA Repr S A × H) Repr A
  href (mk x , h) = x

  -- dup
  LamM : Set₁
  LamM = ∀ {M Repr : Set → Set}{A B H} {{M-fun : Functor M}} {{sSym : SimpleSym Repr}}
              {{ƛᴾ : LamPure Repr}} → (∀ {S} → HV (HA Repr S A × H) Repr A → M (HV (HA Repr S A × H) Repr B))
            → M (HV H Repr (A → B))

  lam : LamM
  lam {{M-fun}} {{sym}} {{mk ƛᴾ}} f = _<$>_ (λ body h → ƛᴾ (λ x → body (mk x , h))) (f {⊤} href) where
    open SimpleSym sym
    open Functor M-fun

  var : ∀ {H M Repr A} {{M-app : Applicative M}} → HV H Repr A → M (HV H Repr A)
  var = Applicative.pure it

  weaken : ∀ {H H′ A : Set} {M Repr : Set → Set} {{M-app : Functor M}} → M (HV H Repr A) → M (HV (H′ × H) Repr A)
  weaken = Functor._<$>_ it (λ g → g ∘ snd) -- hmap goes yellow

  lib : Lib
  lib = mk HA lam href
           (λ {η₁} {η₂} {η₃} {η₄} → var {η₁} {η₂} {η₃} {η₄}) -- FIXME: unquote (ηⁿ (quote var))
           (λ {η₁} {η₂} {η₃} {η₄} {η₅} → weaken {η₁} {η₂} {η₃} {η₄} {η₅})
