open import Data.Maybe.NP
open import Function
open import Category.Applicative
            renaming (RawApplicative to Applicative; module RawApplicative to Applicative)

module NomPa.Examples.LC.Maybe (Cst : Set) where

infixl 6 _·_

data Tmᴹ A : Set where
  V    : (x : A) → Tmᴹ A
  _·_  : (t u : Tmᴹ A) → Tmᴹ A
  ƛ    : (t : Tmᴹ (Maybe A)) → Tmᴹ A
  Let  : (t : Tmᴹ A) (u : Tmᴹ (Maybe A)) → Tmᴹ A
  `_   : (κ : Cst) → Tmᴹ A

mapTmᴹ : ∀ {A B} → (A → B) → (Tmᴹ A → Tmᴹ B)
mapTmᴹ f (V x) = V (f x)
mapTmᴹ f (t · u) = mapTmᴹ f t · mapTmᴹ f u
mapTmᴹ f (ƛ t) = ƛ (mapTmᴹ (map? f) t)
mapTmᴹ f (Let t u) = Let (mapTmᴹ f t) (mapTmᴹ (map? f) u)
mapTmᴹ f (` κ) = ` κ

mapA? : ∀ {M : Set → Set} {A : Set} {B} → Applicative M → (A → M B) → (Maybe A → M (Maybe B))
mapA? app-M f = maybe (_<$>_ just ∘ f) (pure nothing)
  where open Applicative app-M

{-
compA : ∀ {M N : Set → Set} → Applicative M → Applicative N → Applicative (M ∘ N)
compA = {!!}

app-Tmᴹ : Applicative Tmᴹ
app-Tmᴹ = {!!}

traverseATmᴺ : ∀ {M : Set → Set} {A B} → Applicative M → (A → M (Tmᴹ B)) → (Tmᴹ A → M (Tmᴹ B))
traverseATmᴺ {M} app-M = go
  where
   open Applicative app-M
   mapMTmᴹ : ∀ {A B} → (A → M (Tmᴹ B)) → (Maybe A → M (Tmᴹ (Maybe B)))
   mapMTmᴹ = mapA? (compA app-M app-Tmᴹ)
   mutual
    go? : ∀ {A B} → (A → M (Tmᴹ B)) → (Tmᴹ (Maybe A) → M (Tmᴹ (Maybe B)))
    go? f t = go (mapMTmᴹ f) t
    go : ∀ {A B} → (A → M (Tmᴹ B)) → (Tmᴹ A → M (Tmᴹ B))
    go f (V x) = f x
    go f (t · u) = pure _·_ ⊛ go f t ⊛ go f u
    go f (ƛ t) = pure ƛ ⊛ go? f t
    go f (Let t u) = pure Let ⊛ go f t ⊛ go? f u
    go f (` κ) = pure (` κ)

mapATmᴹ : ∀ {M : Set → Set} {A B} → Applicative M → (A → M B) → (Tmᴹ A → M (Tmᴹ B))
mapATmᴹ app-M f = traverseATmᴺ app-M (_<$>_ V ∘ f)
  where open Applicative app-M
-}

-- Tmᴹ ∘ Name ≅ Tmᴰ
-- mapTmᴹ id = id
-- mapTmᴹ (f ∘ g) = mapTmᴹ f ∘ mapTmᴹ g

-- isos:
-- in the iso section advocate for multiple representations
-- A ≅ B → Tmᴹ A ≅ Tmᴹ B

open import Data.Nat.NP

mapTmᴹ^ : ∀ {A B} → (∀ ℓ → Maybe^ ℓ A → Maybe^ ℓ B)
                  → (Tmᴹ A → Tmᴹ B)
mapTmᴹ^ {A} {B} f = go 0 where
  go : ∀ ℓ → Tmᴹ (Maybe^ ℓ A) → Tmᴹ (Maybe^ ℓ B)
  go ℓ (V x) = V (f ℓ x)
  go ℓ (t · u) = go ℓ t · go ℓ u
  go ℓ (ƛ t) = ƛ (go (suc ℓ) t)
  go ℓ (Let t u) = Let (go ℓ t) (go (suc ℓ) u)
  go ℓ (` κ) = ` κ

map?^ : ∀ {a b} {A : Set a} {B : Set b} ℓ → (A → B) → Maybe^ ℓ A → Maybe^ ℓ B
map?^ zero    = id
map?^ (suc n) = map? ∘ map?^ n 

-- analog to `subtractᴺ?'
{-
just^ : ∀ {A} ℓ → A → Maybe^ ℓ A
just^ zero    = id
just^ (suc n) = just ∘′ just^ n
-}

shift?^ : ∀ {a} {A : Set a} k ℓ → Maybe^ ℓ A → Maybe^ ℓ (Maybe^ k A)
shift?^ k ℓ = map?^ ℓ (just^ k) 

shiftTmᴹ^ : ∀ {A} k → Tmᴹ A → Tmᴹ (Maybe^ k A)
shiftTmᴹ^ = mapTmᴹ^ ∘ shift?^

-- analog to `subtractᴺ?'
-- Notice that this combines:
-- * join?^ 0 => just
-- * join?^ 1 => id
-- * join?^ 2 => join?
join?^ : ∀ {a} {A : Set a} n → Maybe^ n A → Maybe A
join?^ zero    = just
join?^ (suc n) = join? ∘′ map? (join?^ n)

open import Relation.Binary.PropositionalEquality

Maybe^-∘-+' : ∀ {a} m n → Maybe^ {a} m ∘ Maybe^ n ≡ Maybe^ (m + n)
Maybe^-∘-+' zero    _ = refl
Maybe^-∘-+' (suc m) n = cong (_∘_ Maybe) (Maybe^-∘-+' m n)

Maybe^-comm^ : ∀ {a} m n → Maybe^ {a} m ∘ Maybe^ n ≡ Maybe^ n ∘ Maybe^ m
Maybe^-comm^ m n = trans (Maybe^-∘-+' m n)
                  (trans (cong Maybe^ (ℕ°.+-comm m n))
                    (sym (Maybe^-∘-+' n m)))

coerce-comm^ : ∀ {a} {A : Set a} m n → Maybe^ m (Maybe^ n A) → Maybe^ n (Maybe^ m A)
coerce-comm^ {_} {A} m n = subst id (cong (λ x → x A) (Maybe^-comm^ m n))

-- analog to `unprotectedAdd'
unprotectedJust^ : ∀ {a} {A : Set a} k ℓ → Maybe^ ℓ A → Maybe^ ℓ (Maybe^ k A)
unprotectedJust^ k ℓ = coerce-comm^ k ℓ ∘ just^ k

open import Data.Empty

-- This coercion looks like shift?^ and unprotectedAdd?^ with an even more specialized type
-- coerce-shift-like : ∀ n k ℓ → Maybe^ ℓ (Maybe^ n ⊥) → Maybe^ ℓ (Maybe^ k (Maybe^ n ⊥))
-- coerce-shift-like n k ℓ =
  -- template: ⊆-cong-↑ (⊆-trans (⊆-cong-↑ ⊆-ø n) (⊆-exch-↑-↑′ k n)) ℓ
