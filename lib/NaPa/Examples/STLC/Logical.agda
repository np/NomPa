{-# OPTIONS --universe-polymorphism #-}
module NaPa.Examples.STLC.Logical where

open import Level hiding (suc)
open import Data.Product.NP
open import Data.Nat.NP as ℕ using (ℕ; zero; suc; _+_; _∸_) renaming (_≟_ to _≟ℕ_; module == to ==ℕ)
open import Data.Bool
open import Data.List
open import Function
open import Function.Injection.NP using (Injection; Injective; module
    Injection; _∈_)
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality as ≡
open        ≡ using (_≡_)
open import Function.Equivalence using (equivalence; _⇔_)
open import Relation.Nullary
open import Data.Unit using (⊤)
open import Data.Sum
open import Data.Maybe.NP as Maybe

open import NaPa hiding (_∈_)
open import NaPa.Derived hiding (protect↑) -- we have a simpler protect↑ here
open import NaPa.Examples.STLC

data ⟦Ty⟧ : Ty → Ty → Set where
  _⟦⟶⟧_  : ∀ {σ₁ σ₂ τ₁ τ₂} (σᵣ : ⟦Ty⟧ σ₁ σ₂) (τᵣ : ⟦Ty⟧ τ₁ τ₂)
           → ⟦Ty⟧ (σ₁ ⟶ τ₁) (σ₂ ⟶ τ₂)
  ⟦ι⟧    : ⟦Ty⟧ ι ι
  ⟦ο⟧    : ⟦Ty⟧ ο ο

⟦Ty⟧-refl : Reflexive ⟦Ty⟧
⟦Ty⟧-refl {σ ⟶ τ} = ⟦Ty⟧-refl {σ} ⟦⟶⟧ ⟦Ty⟧-refl {τ}
⟦Ty⟧-refl {ι} = ⟦ι⟧
⟦Ty⟧-refl {ο} = ⟦ο⟧

data ⟦Constant⟧ : (κ₁ κ₂ : Constant) → Set where
  --⟦num⟧     : ∀ {n₁ n₂} (nᵣ : ⟦ℕ⟧ n₁ n₂) → ⟦Constant⟧ (num n₁) (num n₂)
  ⟦num⟧     : ∀ n → ⟦Constant⟧ (num n) (num n)
  ⟦suc⟧     : ⟦Constant⟧ suc suc
  ⟦natFix⟧  : ∀ {τ₁ τ₂} (τᵣ : ⟦Ty⟧ τ₁ τ₂) → ⟦Constant⟧ (natFix τ₁) (natFix τ₂)

⟦Constant⟧-refl : Reflexive ⟦Constant⟧
⟦Constant⟧-refl {num y} = ⟦num⟧ y
⟦Constant⟧-refl {suc} = ⟦suc⟧
⟦Constant⟧-refl {natFix τ} = ⟦natFix⟧ (⟦Ty⟧-refl {τ})

open import Relation.Binary.Logical
open import Data.Nat.Logical

module ⟦Tm⟧ (⟦World⟧ : ⟦Set₀⟧ World World)
            (_⟦↑1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _↑1 _↑1)
            (⟦Name⟧ : (⟦World⟧ ⟦→⟧ ⟦Set₀⟧) Name Name)
     where
  data ⟦Tm⟧ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) : Tm α₁ → Tm α₂ → Set where
    ⟦V⟧    : ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ αᵣ x₁ x₂) → ⟦Tm⟧ αᵣ (V x₁) (V x₂)
    ⟦_·_⟧  : ∀ {t₁ t₂ u₁ u₂} (tᵣ : ⟦Tm⟧ αᵣ t₁ t₂)
               (uᵣ : ⟦Tm⟧ αᵣ u₁ u₂) → ⟦Tm⟧ αᵣ (t₁ · u₁) (t₂ · u₂)
    ⟦ƛ⟧    : ∀ {τ₁ τ₂ t₁ t₂}
               (τᵣ : ⟦Ty⟧ τ₁ τ₂)
               (tᵣ : ⟦Tm⟧ (αᵣ ⟦↑1⟧) t₁ t₂)
             → ⟦Tm⟧ αᵣ (ƛ τ₁ t₁) (ƛ τ₂ t₂)
    ⟦Let⟧  : ∀ {t₁ t₂ u₁ u₂}
               (tᵣ : ⟦Tm⟧ αᵣ t₁ t₂)
               (uᵣ : ⟦Tm⟧ (αᵣ ⟦↑1⟧) u₁ u₂)
             → ⟦Tm⟧ αᵣ (Let t₁ u₁) (Let t₂ u₂)
    ⟦`_⟧   : ∀ {κ₁ κ₂} (κᵣ : ⟦Constant⟧ κ₁ κ₂)
             → ⟦Tm⟧ αᵣ (` κ₁) (` κ₂)

{-
  module Refl (⟦World⟧-refl : Reflexive ⟦World⟧)
              (⟦Name⟧-refl : ∀ {α} → Reflexive (⟦Name⟧ {α} ⟦World⟧-refl)) where
    ⟦Tm⟧-refl : ∀ {α} → Reflexive (⟦Tm⟧ {α} (⟦World⟧-refl {α}))
    ⟦Tm⟧-refl {α} {V x} = ⟦V⟧ (⟦Name⟧-refl {α} {x})
    ⟦Tm⟧-refl {α} {t · u} = ⟦ (⟦Tm⟧-refl {α} {t}) · (⟦Tm⟧-refl {α} {u}) ⟧
    ⟦Tm⟧-refl {α} {ƛ τ t} = ⟦ƛ⟧ ⟦Ty⟧-refl {!⟦Tm⟧-refl {_} {t}!}
    ⟦Tm⟧-refl {α} {Let t u} = {!!}
    ⟦Tm⟧-refl {α} {` κ} = {!!}
-}

protect↑ : ∀ {α β} k → (Name α → Name β) → (Name (α ↑ k) → Name (β ↑ k))
protect↑ zero    = id
protect↑ (suc k) = protect↑1 ∘ protect↑ k

mapTm : ∀ {α β} k → (Name α → Name β) → Tm (α ↑ k) → Tm (β ↑ k)
mapTm k f (V x)      = V (protect↑ k f x)
mapTm _ _ (` x)      = ` x
mapTm k f (t · u)    = mapTm k f t · mapTm k f u
mapTm k f (ƛ τ t)    = ƛ τ (mapTm (suc k) f t)
mapTm k f (Let t u)  = Let (mapTm k f t) (mapTm (suc k) f u)

open import Function.Equality as ⟶≡ using (_⟶_; _⟨$⟩_)
open import NaPa.LogicalRelation renaming (_⟨$⟩ᵢ_ to _⟦$⟧_)
-- _⟦$⟧_ = _⟨$⟩ᵢ_

private
  module Inj = Injection
  module ℕs = Setoid ⟦ℕ⟧-setoid
  module ==ℕs = Setoid ==ℕ.setoid
  module ℕe = Equality ⟦ℕ⟧-equality

-- This is unfinished, see the postulate...
module Foo where
{-
module Foo  (⟦World⟧ : ⟦Set₀⟧ World World)
            (_⟦↑1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _↑1 _↑1)
            -- (⟦Name⟧ : (⟦World⟧ ⟦→⟧ ⟦Set₀⟧) Name Name)
            -- (⟦World⟧-refl : ∀ {α} → ⟦World⟧ α α)
            (_⟦$⟧_ : ∀ {α₁ α₂} → ⟦World⟧ α₁ α₂ → Name α₁ → Name α₂)
     where
  ⟦Name⟧ : (⟦World⟧ ⟦→⟧ ⟦Set₀⟧) Name Name
  ⟦Name⟧ αᵣ x₁ x₂ = αᵣ ⟦$⟧ x₁ ≡ᴺ x₂
-}

  module Tm≡ = ⟦Tm⟧ _≡_ (≡.cong (_∷_ true)) (λ eq x y → (≡.subst Name eq x) ≡ᴺ y)
  open ⟦Tm⟧ ⟦World⟧ _⟦↑1⟧ ⟦Name⟧ -- hiding (module Refl)
  open Tm≡ renaming (⟦Tm⟧ to Tm≡; ⟦V⟧ to V≡; ⟦_·_⟧ to _·≡_; ⟦ƛ⟧ to ƛ≡; ⟦Let⟧ to Let≡; ⟦`_⟧ to `≡_)

{-
  _⟦↑_⟧ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) _↑_ _↑_
  _⟦↑_⟧ αᵣ zero    = αᵣ
  _⟦↑_⟧ αᵣ (suc k) = αᵣ ⟦↑ k ⟧ ⟦↑1⟧
-}

  protect↑1∘protect↑k : ∀ {α β} (f : Name α → Name β) k (x : Name (α ↑ (suc k))) → protect↑1 (protect↑ k f) x ≡ protect↑ (suc k) f x
  protect↑1∘protect↑k f k x = ≡.refl
  -- protect↑1∘protect↑k f zero x = {!!}
  -- protect↑1∘protect↑k f (suc k) x = {!!}

  -- protect↑1∘protect↑k′ : ∀ {α β} (f : Name α → Name β) k (x : Name (α ↑ (suc k))) → protect↑1 (protect↑ k f) x ≡ᴺ protect↑ (suc k) f x
  -- protect↑1∘protect↑k′ f k x = {!!}

  bar1 : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) x
        → (αᵣ ⟦↑1⟧) ⟦$⟧ x ≡ᴺ protect↑ 1 (_⟦$⟧_ αᵣ) x
  bar1 αᵣ x = ℕe.refl

{-
   = ℕ.suc (name (αᵣ ⟦+ kᵣ ⟧ ⟨$⟩ᵢ (k₁ +ℕ name x₁ , _{-p-})))
   ≈⟨ ≡ᴺ-⟦ℕ⟧-cong (λ x → suc (name (αᵣ ⟦+ kᵣ ⟧ ⟨$⟩ᵢ x))) ℕe.refl ⟩
     suc (name (αᵣ ⟦+ kᵣ ⟧ ⟨$⟩ᵢ (k₁ +ℕ name x₁ , _{-q-})))
   ≈⟨ suc (⟦+ᴺ⟧ αᵣ {x₁} {x₂} x kᵣ) ⟩
     suc (k₂ +ℕ name x₂)
   ∎ where open ⟦ℕ⟧-Reasoning
-}
  postulate ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

  bar′ : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) x
        → (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) ⟦$⟧ x ≡ protect↑ k (_⟦$⟧_ αᵣ) x
  bar′ zero αᵣ _ = ≡.refl
  bar′ (suc n) αᵣ x = ≡.trans (≡.cong (λ f → protect↑1 f x) (ext (bar′ n αᵣ)) ) (protect↑1∘protect↑k (_⟦$⟧_ αᵣ) n x)

  bar : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {x₁ x₂}
          (xᵣ : (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) ⟦$⟧ x₁ ≡ᴺ x₂) → protect↑ k (_⟦$⟧_ αᵣ) x₁ ≡ᴺ x₂
  bar k {α₁} {α₂} αᵣ {x₁} {x₂} xᵣ = ℕe.trans (ℕe.sym (ℕe.reflexive (≡.cong name (bar′ k αᵣ x₁)))) xᵣ

  -- ⟦Name⟧-reflexive : ∀ {α} {x₁ x₂} → x₁ ≡ x₂ → ⟦Name⟧
  -- ⟦Name⟧-reflexive ≡.refl

  oofnx : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) x
        → (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) ⟦$⟧ x ≡ᴺ (protect↑ k (_⟦$⟧_ αᵣ) x)
  oofnx k αᵣ x = NmEq.reflexive (bar′ k αᵣ x)

  oofn : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {x₁ x₂}
        → x₁ ≡ x₂ → ⟦Name⟧ (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) x₁ (protect↑ k (_⟦$⟧_ αᵣ) x₂)
  oofn k αᵣ ≡.refl = oofnx k αᵣ _

  Tm≡-refl : ∀ {α} → Reflexive (Tm≡ {α} ≡.refl)
  Tm≡-refl {α} {V x} = V≡ ℕe.refl
  Tm≡-refl {α} {t · u} = (Tm≡-refl {α} {t}) ·≡ (Tm≡-refl {α} {u})
  Tm≡-refl {α} {ƛ τ t} = ƛ≡ ⟦Ty⟧-refl (Tm≡-refl {_} {t})
  Tm≡-refl {α} {Let t u} = Let≡ Tm≡-refl Tm≡-refl
  Tm≡-refl {α} {` κ} = `≡ ⟦Constant⟧-refl

  foo : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {t₁ t₂}
        → ⟦Tm⟧ (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) t₁ t₂ → Tm≡ ≡.refl (mapTm k (_⟦$⟧_ αᵣ) t₁) t₂
  foo k αᵣ (⟦V⟧ {x₁} {x₂} xᵣ) = V≡ (bar k αᵣ {x₁} {x₂} xᵣ)
  foo k αᵣ ⟦ tᵣ · uᵣ ⟧ = foo k αᵣ tᵣ ·≡ foo k αᵣ uᵣ
  foo k αᵣ (⟦ƛ⟧ τᵣ tᵣ) = ƛ≡ τᵣ (foo (suc k) αᵣ tᵣ)
  foo k αᵣ (⟦Let⟧ tᵣ uᵣ) = Let≡ (foo k αᵣ tᵣ) (foo (suc k) αᵣ uᵣ)
  foo k αᵣ ⟦` κᵣ ⟧ = `≡ κᵣ

  foo0 : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {t₁ t₂}
        → ⟦Tm⟧ αᵣ t₁ t₂ → Tm≡ ≡.refl (mapTm 0 (_⟦$⟧_ αᵣ) t₁) t₂
  foo0 = foo 0

  postulate Tm≡⇒≡ : ∀ {α} → Tm≡ {α} ≡.refl ⇒ _≡_

  ≡⇒Tm≡ : ∀ {α} → _≡_ ⇒ Tm≡ {α} ≡.refl
  -- ≡⇒Tm≡ ≡.refl = Refl.⟦Tm⟧-refl ≡.refl ℕe.refl
  ≡⇒Tm≡ ≡.refl = Tm≡-refl

  foo0≡ : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {t₁ t₂}
        → ⟦Tm⟧ αᵣ t₁ t₂ → mapTm 0 (_⟦$⟧_ αᵣ) t₁ ≡ t₂
  foo0≡ = λ αᵣ → Tm≡⇒≡ ∘ foo0 αᵣ

  oof : ∀ k {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {t₁ t₂}
        → Tm≡ ≡.refl t₁ t₂ → ⟦Tm⟧ (αᵣ ⟦↑ (ℕs.refl {k}) ⟧) t₁ (mapTm k (_⟦$⟧_ αᵣ) t₂)
  oof k αᵣ (V≡ xᵣ) = ⟦V⟧ (oofn k αᵣ (≡ᴺ⇒≡ xᵣ))
  oof k αᵣ (tᵣ ·≡ uᵣ) = ⟦ oof k αᵣ tᵣ · oof k αᵣ uᵣ ⟧
  oof k αᵣ (ƛ≡ τᵣ tᵣ) = ⟦ƛ⟧ τᵣ (oof (suc k) αᵣ tᵣ)
  oof k αᵣ (Let≡ tᵣ uᵣ) = ⟦Let⟧ (oof k αᵣ tᵣ) (oof (suc k) αᵣ uᵣ)
  oof k αᵣ (`≡ κᵣ) = ⟦` κᵣ ⟧

  oof0≡ : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {t}
         → ⟦Tm⟧ αᵣ t (mapTm 0 (_⟦$⟧_ αᵣ) t)
  oof0≡ = λ αᵣ → oof 0 αᵣ Tm≡-refl

  bazw : ∀ (f : ∀ {α} → Tm α → Tm α) (fᵣ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Tm⟧ αᵣ ⟦→⟧ ⟦Tm⟧ αᵣ) f f)
           → ∀  {α β} (Φ : ⟦World⟧ α β)
        → mapTm 0 (_⟦$⟧_ Φ) ∘ f ≗ f ∘ mapTm 0 (_⟦$⟧_ Φ)
  bazw f fᵣ Φ x = foo0≡ Φ (fᵣ Φ (oof0≡ Φ {x}))

  ban : ∀ (f : ∀ {α} → Name α → Name α) (fᵣ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ αᵣ) f f)
           → ∀  {α β} (Φ : Name α → Name β) (Φ-inj : Injective (Name→-to-Nm⟶ {B = Nm β} Φ))
        → Φ ∘ f ≗ f ∘ Φ
  ban f fᵣ {α} {β} Φ Φ-inj x = ≡ᴺ⇒≡ (fᵣ Φ′ ℕe.refl)
   where Φ′ : ⟦World⟧ α β
         Φ′ = record { to = Name→-to-Nm⟶ Φ; injective = Φ-inj }

  baz : ∀ (f : ∀ {α} → Tm α → Tm α) (fᵣ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Tm⟧ αᵣ ⟦→⟧ ⟦Tm⟧ αᵣ) f f)
           → ∀  {α β} (Φ : Name α → Name β) (Φ-inj : Injective (Name→-to-Nm⟶ {B = Nm β} Φ))
        → mapTm 0 Φ ∘ f ≡ f ∘ mapTm 0 Φ
  baz f fᵣ {α} {β} Φ Φ-inj = ext (bazw f fᵣ Φ′)
   where Φ′ : ⟦World⟧ α β
         Φ′ = record { to = Name→-to-Nm⟶ Φ; injective = Φ-inj }

-- (f : ∀ α → N α → N α) → f x ≡ x
-- (f : ∀ x → Nameˢ x → Nameˢ x) → f x ≡ x
-- (y : Nameˢ x) → x ≡ y
-- (f : ∀ α → [N α] → N α) → x `elem` f x


-- add k ∘ Φ ≗ lift+ k Φ ∘ add k
-- subtract k ∘ lift+ k ≗ Φ ∘ subtract k
