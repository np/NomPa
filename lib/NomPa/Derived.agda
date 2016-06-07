{-# OPTIONS --universe-polymorphism #-}
import Level as L
open import Function.NP
open import Data.Bool
open import Data.Sum
open import Data.Nat.NP
open import Data.Maybe.NP
open import Data.List
open import Data.Product
open import Relation.Nullary
open import NomPa.Record
import Data.Indexed

module NomPa.Derived (nomPa : NomPa) where

open NomPa nomPa
open Data.Indexed {_} {World}

_→ᴺ_ : (α β : World) → Set
α →ᴺ β = Name α → Name β

_→ᴺ?_ : (α β : World) → Set
α →ᴺ? β = Name α →? Name β

SynAbsᴺ : (World → Set) → (World → Set)
SynAbsᴺ F α = Σ Binder λ b → F (b ◅ α)

FunAbs : (World → Set) → (World → Set)
FunAbs F α = ∀ {β} → (α ⊆ β) → F β → F β

SynAbsᴸ : (Binder → World → Set) → (Binder → World → Set)
SynAbsᴸ F b α = F (sucᴮ b) (b ◅ α)

Coercible : (World → Set) → World → Set
Coercible F α = ∀ {Ω} → α ⊆ Ω → F Ω

{-
this alternative definition seems to not be coercible
FunAbs′ : (World → Set) → (World → Set)
FunAbs′ F α = Coercible F α → Coercible F α
-}

coerceCoercible : ∀ {F α β} → α ⊆ β → Coercible F α → Coercible F β
coerceCoercible pf t′ pf′ = t′ (⊆-trans pf pf′)

_◅★_ : List Binder → World → World
[]       ◅★ α = α
(b ∷ bs) ◅★ α = b ◅ bs ◅★ α

-- Like _◅★_ but adds the binders in the reverse order.
_◅★′_ : List Binder → World → World
[]       ◅★′ α = α
(b ∷ bs) ◅★′ α = bs ◅★′ (b ◅ α)

module ⊆-Reasoning where
  infix  3 _∎
  infixr 2 _⊆⟨_⟩_

  _⊆⟨_⟩_ : ∀ α {β γ} → α ⊆ β → β ⊆ γ → α ⊆ γ
  _⊆⟨_⟩_ _ = ⊆-trans

  _∎ : ∀ α → α ⊆ α
  _∎ _ = ⊆-refl

module Envs where
  record EnvPack ℓ : Set (L.suc ℓ) where
    field
      Env        : Set ℓ → World → World → Set ℓ
      emptyEnv   : ∀ {A Ω} → Env A Ω Ω
      lookupEnv  : ∀ {A α Ω} (Γ : Env A α Ω) (x : Name α) → Name Ω ⊎ A
      _,_↦_      : ∀ {α Ω A} (Γ : Env A α Ω) b → A → Env A (b ◅ α) Ω
      mapEnv     : ∀ {α Ω A B} (f : A → B) (Γ : Env A α Ω) → Env B α Ω
    memEnv : ∀ {α Ω A} → Env A α Ω → Name α → Bool
    memEnv Γ x = [ const false , (λ _ → true) ]′ (lookupEnv Γ x)
    lookupEnv? : ∀ {A α Ω} → Env A α Ω → Name α →? A
    lookupEnv? Γ = [ const nothing , just ]′ ∘ lookupEnv Γ
    exportEnv? : ∀ {A α Ω} → Env A α Ω → α →ᴺ? Ω
    exportEnv? Γ = [ just , const nothing ]′ ∘ lookupEnv Γ

  record CoeEnvPack ℓ : Set (L.suc ℓ) where
    field
      envPack : EnvPack ℓ
    open EnvPack envPack
    field
      coerceEnv : ∀ {α β γ A} → α ⊆ β → Env A γ α → Env A γ β
    emptyEnv′ : ∀ {α β A} → α ⊆ β → Env A α β
    emptyEnv′ pf = coerceEnv pf emptyEnv
    open EnvPack envPack public

  -- CEnv is for closed Env
  record CEnvPack ℓ : Set (L.suc ℓ) where
    field
      CEnv        : Set ℓ → World → Set ℓ
      emptyCEnv   : ∀ {A} → CEnv A ø
      lookupCEnv  : ∀ {A α} (Γ : CEnv A α) (x : Name α) → A
      _,_↦_       : ∀ {α A} (Γ : CEnv A α) b → A → CEnv A (b ◅ α)
      mapCEnv     : ∀ {α A B} (f : A → B) (Γ : CEnv A α) → CEnv B α

  data DataEnv (A : Set) : (α Ω : World) → Set where
    ε : ∀ {Ω} → DataEnv A Ω Ω
    _,,_↦_ : ∀ {α Ω} (Γ : DataEnv A α Ω) b (x : A) → DataEnv A (b ◅ α) Ω

  dataEnv : EnvPack L.zero
  dataEnv = record { Env = DataEnv ; emptyEnv = ε ; lookupEnv = lookup
                   ; _,_↦_ = _,,_↦_ ; mapEnv = mapEnv } where

    lookup : ∀ {A α Ω} → DataEnv A α Ω → Name α → Name Ω ⊎ A
    lookup ε             = inj₁
    lookup (Γ ,, _ ↦ v) = exportWith (inj₂ v) (lookup Γ)

    mapEnv : ∀ {α Ω A B} → (A → B) → DataEnv A α Ω → DataEnv B α Ω
    mapEnv f ε             = ε
    mapEnv f (xs ,, x ↦ v)  = mapEnv f xs ,, x ↦ f v

  data DataEnv′ (A : Set) : (α Ω : World) → Set where
    ε : ∀ {α Ω} → α ⊆ Ω → DataEnv′ A α Ω
    _,,_↦_ : ∀ {α Ω} (Γ : DataEnv′ A α Ω) b (x : A) → DataEnv′ A (b ◅ α) Ω

  dataEnv′ : CoeEnvPack L.zero
  dataEnv′ = record {
               envPack = record { Env = DataEnv′ ; emptyEnv = ε ⊆-refl ; lookupEnv = lookup
                                ; _,_↦_ = _,,_↦_ ; mapEnv = mapEnv };
               coerceEnv = coerceEnv } where

    lookup : ∀ {A α Ω} → DataEnv′ A α Ω → Name α → Name Ω ⊎ A
    lookup (ε pf)       = inj₁ ∘ coerceᴺ pf
    lookup (Γ ,, _ ↦ v) = exportWith (inj₂ v) (lookup Γ)

    mapEnv : ∀ {α Ω A B} → (A → B) → DataEnv′ A α Ω → DataEnv′ B α Ω
    mapEnv f (ε pf)        = ε pf
    mapEnv f (xs ,, x ↦ v) = mapEnv f xs ,, x ↦ f v

    coerceEnv : ∀ {α β γ A} → α ⊆ β → DataEnv′ A γ α → DataEnv′ A γ β
    coerceEnv pf (ε pf')       = ε (⊆-trans pf' pf)
    coerceEnv pf (xs ,, x ↦ v) = coerceEnv pf xs ,, x ↦ v

  closeEnv : EnvPack L.zero → CEnvPack L.zero
  closeEnv env
    = record { CEnv = λ A α → Env A α ø
             ; emptyCEnv = emptyEnv
             ; lookupCEnv = λ Γ → [ Nameø-elim , id ]′ ∘ lookupEnv Γ
             ; mapCEnv = mapEnv
             ; _,_↦_ = _,_↦_ }
    where open EnvPack env

  FunEnv : ∀ {ℓ} → Set ℓ → World → World → Set ℓ
  FunEnv A α Ω = Name α → Name Ω ⊎ A

  funEnv : ∀ {ℓ} → CoeEnvPack ℓ
  funEnv {ℓ}
    = record { envPack =
                 record { Env = FunEnv
                        ; emptyEnv = inj₁
                        ; _,_↦_ = _,_↦_
                        ; lookupEnv = id
                        ; mapEnv = mapEnv };
               coerceEnv = coerceFunEnv }
   where
    _,_↦_ : ∀ {α Ω A} (Γ : FunEnv A α Ω) b → A → FunEnv A (b ◅ α) Ω
    _,_↦_ Γ _ v = exportWith (inj₂ v) Γ

    mapEnv : ∀ {α Ω} {A B : Set ℓ} → (A → B) → FunEnv A α Ω → FunEnv B α Ω
    mapEnv f g = [ inj₁ , inj₂ ∘ f ]′ ∘ g

    coerceFunEnv : ∀ {α β γ} {A : Set ℓ} → (α ⊆ β) → FunEnv A γ α → FunEnv A γ β
    coerceFunEnv pf Γ = [ inj₁ ∘ coerceᴺ pf , inj₂ ]′ ∘ Γ

  funCEnv : ∀ {ℓ} → CEnvPack ℓ
  funCEnv {ℓ}
    = record { CEnv        = λ A α → Name α → A
             ; emptyCEnv   = λ {η} → Nameø-elim
             ; _,_↦_       = λ Γ _ v → exportWith v Γ
             ; lookupCEnv  = id
             ; mapCEnv     = _∘′_ }

infixr 4 _,_

-- TODO sync with nompa
record Supply α : Set where
  constructor _,_
  field
    seedᴮ : Binder
    seed# : seedᴮ # α

  seedᵂ : World
  seedᵂ = seedᴮ ◅ α

  seedᴺ : Name seedᵂ
  seedᴺ = nameᴮ seedᴮ

  seed⊆ : α ⊆ seedᵂ
  seed⊆ = ⊆-# seed#

  coerceˢ : α →ᴺ seedᵂ
  coerceˢ = coerceᴺ seed⊆

  -- an Agda bug prevents this from typing
  -- sucˢ : Supply seedᵂ
  -- sucˢ = sucᴮ seedᴮ , suc# seed#

zeroˢ : Supply ø
zeroˢ = 0 ᴮ , 0 ᴮ #ø

sucˢ : ∀ {α} → (s : Supply α) → Supply (Supply.seedᵂ s)
sucˢ (seedᴮ , seed#) = sucᴮ seedᴮ , suc# seed#

mutual
  _ˢʷ : ℕ → World
  zero    ˢʷ = ø
  (suc n) ˢʷ = Supply.seedᴮ (n ˢ) ◅ n ˢʷ

  _ˢ : ∀ n → Supply (n ˢʷ)
  0     ˢ = zeroˢ
  suc n ˢ = sucˢ (n ˢ)

lift-◅ : ∀ {α β b₁ b₂} → (b₂ # β) → (α →ᴺ β) → ((b₁ ◅ α) →ᴺ (b₂ ◅ β))
lift-◅ {b₂ = b₂} b₂#β f x with exportᴺ x
... | inj₁ _  = nameᴮ b₂
... | inj₂ x′ = f x′ ⟨-because ⊆-# b₂#β -⟩

infixr 5 _◅…′_ _◅…_

_◅…′_ : ℕ → World → World
zero  ◅…′ α = α
suc n ◅…′ α = n ᴮ ◅ n ◅…′ α

_◅…_ : ℕ → World → World
n ◅… α = n ᴮ ◅ n ◅…′ α

import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_)

-- .suc#′ : ∀ {α n} → n ᴮ # α → (suc n)ᴮ # (n ᴮ ◅ α)
-- suc#′ = ≡.subst₂ _#_ (B-sem suc _) ≡.refl ∘ suc#

#-◅…′ø : ∀ x → x ᴮ # x ◅…′ ø
#-◅…′ø zero    = 0 ᴮ #ø
#-◅…′ø (suc n) = suc# (#-◅…′ø n)

#-◅…ø : ∀ x → (suc x ᴮ) # x ◅… ø
#-◅…ø = suc# ∘ #-◅…′ø

_ᴺ′ : ∀ n → Name (n ◅… ø)
n ᴺ′ = n ᴺ

⊆-◅…′ : ∀ {α β} x → α ⊆ β → x ◅…′ α ⊆ x ◅…′ β
⊆-◅…′ zero    = id
⊆-◅…′ (suc n) = ⊆-◅ (n ᴮ) ∘ ⊆-◅…′ n

⊆-◅… : ∀ {α β} x → α ⊆ β → x ◅… α ⊆ x ◅… β
⊆-◅… x = ⊆-◅ (x ᴮ) ∘ ⊆-◅…′ x

⊆-◅…′ø : ∀ {α} k x → x ◅…′ ø ⊆ (k + x) ◅…′ α
⊆-◅…′ø     zero    x = ⊆-◅…′ x ⊆-ø
⊆-◅…′ø {α} (suc k) x = x ◅…′ ø
                     ⊆⟨ ⊆-◅…′ø k x ⟩
                       (k + x) ◅…′ ø
                     ⊆⟨ ⊆-# (#-◅…′ø (k + x)) ⟩
                       (k + x) ᴮ ◅ k + x ◅…′ ø
                     ⊆⟨ ⊆-◅…′ (suc (k + x)) ⊆-ø ⟩
                       (suc k + x) ◅…′ α ∎
  where open ⊆-Reasoning

⊆-◅…ø : ∀ {α} k x → x ◅… ø ⊆ (k + x) ◅… α
⊆-◅…ø     zero    x = ⊆-◅… x ⊆-ø
⊆-◅…ø {α} (suc k) x = x ◅… ø
                     ⊆⟨ ⊆-◅…ø k x ⟩
                       (k + x) ◅… ø
                     ⊆⟨ ⊆-# (#-◅…ø (k + x)) ⟩
                       ((suc k + x) ᴮ) ◅ (k + x) ᴮ ◅ k + x ◅…′ ø
                     ⊆⟨ ⊆-◅… (suc (k + x)) ⊆-ø ⟩
                       (suc k + x) ◅… α ∎
  where open ⊆-Reasoning

name◅… : ∀ {α} k x → Name ((k + x) ◅… α)
name◅… {α} k x = x ᴺ ⟨-because ⊆-◅…ø k x -⟩

_ᴺ¹ : ∀ {α} x → Name ((1 + x) ◅… α)
_ᴺ¹ = name◅… 1

_ᴺ₂ : ∀ {α} x → Name ((2 + x) ◅… α)
_ᴺ₂ = name◅… 2

_ᴺ³ : ∀ {α} x → Name ((3 + x) ◅… α)
_ᴺ³ = name◅… 3

+ᴮ-dist : ∀ m n → (m ᴮ) +ᴮ n ≡ (n + m)ᴮ
+ᴮ-dist m zero = ≡.refl
+ᴮ-dist m (suc n) = ≡.cong sucᴮ (+ᴮ-dist m n)

+ᴮ-dist1 : ∀ {b} k → sucᴮ b +ᴮ k ≡ sucᴮ (b +ᴮ k)
+ᴮ-dist1 zero    = ≡.refl
+ᴮ-dist1 (suc k) = ≡.cong sucᴮ (+ᴮ-dist1 k)

+ᴮ-comm : ∀ m n → (m ᴮ) +ᴮ n ≡ (n ᴮ) +ᴮ m
+ᴮ-comm m n = (m ᴮ) +ᴮ n ≡⟨ +ᴮ-dist m n ⟩
              (n + m)ᴮ   ≡⟨ ≡.cong _ᴮ (ℕ°.+-comm n m) ⟩
              (m + n)ᴮ   ≡⟨ ≡.sym (+ᴮ-dist n m) ⟩
              (n ᴮ) +ᴮ m ∎
  where open ≡.≡-Reasoning

⊆-reflexive : ∀ {α β} → α ≡ β → α ⊆ β
⊆-reflexive ≡.refl = ⊆-refl

0ᴮ-+ᴮ-id : ∀ k → 0 ᴮ +ᴮ k ≡ k ᴮ
0ᴮ-+ᴮ-id zero    = ≡.refl
0ᴮ-+ᴮ-id (suc n) = ≡.cong sucᴮ (0ᴮ-+ᴮ-id n)

⊆-dist-+-◅ : ∀{α b} k → (b ◅ α) +ᵂ k ⊆ (b +ᴮ k) ◅ (α +ᵂ k)
⊆-dist-+-◅ zero    = ⊆-refl
⊆-dist-+-◅ (suc n) = ⊆-trans (⊆-cong-+1 (⊆-dist-+-◅ n)) (⊆-dist-+1-◅ _)

⊆-dist-◅-+ : ∀{α b} k → (b +ᴮ k) ◅ (α +ᵂ k) ⊆ (b ◅ α) +ᵂ k
⊆-dist-◅-+ zero    = ⊆-refl
⊆-dist-◅-+ (suc n) = ⊆-trans (⊆-dist-◅-+1 _) (⊆-cong-+1 (⊆-dist-◅-+ n))

rm : ∀ {α} b → List (Name (b ◅ α)) → List (Name α)
rm b []         = []
rm b (x ∷ xs) with  exportᴺ? x
...                 |  nothing = rm b xs
...                 |  just x′ = x′  ∷ rm b xs

extendNameCmp : ∀ {α₁ α₂ b₁ b₂} → Cmp° Name α₁ α₂ → Cmp° Name (b₁ ◅ α₁) (b₂ ◅ α₂)
extendNameCmp f x₁ x₂
 with exportᴺ? x₁ | exportᴺ? x₂
... | just x₁′     | just x₂′ = f x₁′ x₂′
... | nothing     | nothing = true
... | _           | _       = false

-- α-equivalence on pairs is just the conjunction
×-Cmp : ∀ {α β F G} → Cmp° F α β → Cmp° G α β → Cmp° (F ×° G) α β
×-Cmp rel-F rel-G  (x₁ , y₁) (x₂ , y₂) = rel-F x₁ x₂ ∧ rel-G y₁ y₂

data αEqDataEnv : (α₁ α₂ : World) → Set where
  ε : ∀ {α} → αEqDataEnv α α
  _,,_↔_ : ∀ {α₁ α₂} (Γ : αEqDataEnv α₁ α₂) b₁ b₂ → αEqDataEnv (b₁ ◅ α₁) (b₂ ◅ α₂)

extendαEqDataEnv : ∀ {α₁ α₂ b₁ b₂} → αEqDataEnv α₁ α₂ → αEqDataEnv (b₁ ◅ α₁) (b₂ ◅ α₂)
extendαEqDataEnv d = d ,, _ ↔ _

cmpNameαEqDataEnv : ∀ {α₁ α₂} → αEqDataEnv α₁ α₂ →  Cmp° Name α₁ α₂
cmpNameαEqDataEnv ε = _==ᴺ_
cmpNameαEqDataEnv (Γ ,, b₁ ↔ b₂) = extendNameCmp (cmpNameαEqDataEnv Γ)
