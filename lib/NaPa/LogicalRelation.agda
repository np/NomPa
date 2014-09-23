{-# OPTIONS --universe-polymorphism #-}
module NaPa.LogicalRelation where

import Level as L
open import Abstractor
open import Irrelevance
open import Data.Nat.NP hiding (_⊔_) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤?ℕ_; _<_ to _<ℕ_
                                              ;module == to ==ℕ; _==_ to _==ℕ_)
open import Data.Nat.Logical renaming (_≟_ to _≟ℕ_; _⟦+⟧_ to _⟦+ℕ⟧_)
open import Data.Nat.Properties as Nat
open import Data.Empty
open import Data.Unit
open import Data.Maybe.NP
open import Data.Bool.NP hiding (_==_)
open import Data.Sum.NP
open import Data.Product.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open ≡.≡-Reasoning
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.NP
open import Relation.Binary.Logical
open import Function
open import Function.Equality as ⟶≡ using (_⟶_; _⟨$⟩_)
open import Function.Injection.NP using (Injection; Injective; module
    Injection; _∈_)
open import NaPa hiding (_∈_)

private
  module Inj = Injection
  module ℕs = Setoid ⟦ℕ⟧-setoid
  module ==ℕs = Setoid ==ℕ.setoid
  module ℕe = Equality ⟦ℕ⟧-equality

_⟨$⟩ᵢ_ : ∀ {f₁ f₂ t₁ t₂}
           {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
         → Injection From To → Setoid.Carrier From → Setoid.Carrier To
_⟨$⟩ᵢ_ = ⟶≡._⟨$⟩_ ∘ Inj.to -- inj x = Inj.to inj ⟨$⟩ x

==ℕ-dec : ∀ x y → ⟦Bool⟧ ⌊ x ≟ℕ y ⌋ (x ==ℕ y)
==ℕ-dec x y with x ≟ℕ y
... | yes p = ⟦true⟧′  (==ℕs.reflexive (ℕe.to-propositional p))
... | no ¬p = ⟦false⟧′ (T'¬'not (¬p ∘ ℕs.reflexive ∘ ==ℕ.sound _ _))

⟦dec⟧ : ∀ {P Q : Set} (decP : Dec P) (decQ : Dec Q) → (P → Q) → (Q → P) → ⟦Bool⟧ ⌊ decP ⌋ ⌊ decQ ⌋
⟦dec⟧ (yes _) (yes _) _ _ = ⟦true⟧
⟦dec⟧ (no  _) (no  _) _ _ = ⟦false⟧
⟦dec⟧ (yes p) (no ¬q) f _ = ⊥-elim (¬q (f p))
⟦dec⟧ (no ¬p) (yes q) _ g = ⊥-elim (¬p (g q))

⟦World⟧ : (α₁ α₂ : World) → Set
⟦World⟧ = Injection on Nm

-- dup with NotSoFresh.LogicalRelation
⟦WorldPred⟧ : (P₁ P₂ : Pred L.zero World) → Set₁
⟦WorldPred⟧ = ⟦Pred⟧ _ ⟦World⟧

⟦WorldRel⟧ : (R₁ R₂ : Rel World L.zero) → Set₁
⟦WorldRel⟧ = ⟦Rel⟧ ⟦World⟧ L.zero

_⟦↑1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _↑1 _↑1
_⟦↑1⟧ {α₁} {α₂} αᵣ = record { to = to; injective = to-inj } where
  to : Nm (α₁ ↑1) ⟶ Nm (α₂ ↑1)
  to = Name→-to-Nm⟶ (protect↑1 (_⟨$⟩ᵢ_ αᵣ))
  to-inj : Injective to
  to-inj {zero  , _} {zero  , _} zero    = zero
  to-inj {suc _ , _} {suc _ , _} (suc e) = suc (Inj.injective αᵣ e)
  to-inj {suc _ , _} {zero  , _} ()
  to-inj {zero  , _} {suc _ , _} ()

_⟦+1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _+1 _+1
_⟦+1⟧ {α₁} {α₂} αᵣ = record { to = to; injective = inj } where
  to : Nm (α₁ +1) ⟶ Nm (α₂ +1)
  to = Name→-to-Nm⟶ (λ x → sucᴺ (αᵣ ⟨$⟩ᵢ (predᴺ x)))
  inj : Injective to
  inj {zero  , _} {zero  , _} _       = zero
  inj {suc _ , _} {suc _ , _} (suc e) = suc (Inj.injective αᵣ e)
  inj {suc _ , _} {zero  , ()} _
  inj {zero  , ()} {suc _ , _} _

_⟦↑_⟧ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) _↑_ _↑_
_⟦↑_⟧ αᵣ zero    = αᵣ
_⟦↑_⟧ αᵣ (suc k) = αᵣ ⟦↑ k ⟧ ⟦↑1⟧

_⟦+ᵂ⟧_ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) _+ᵂ_ _+ᵂ_
_⟦+ᵂ⟧_ αᵣ zero    = αᵣ
_⟦+ᵂ⟧_ αᵣ (suc k) = (αᵣ ⟦+ᵂ⟧ k) ⟦+1⟧

⟦Name⟧ : ⟦Pred⟧ L.zero ⟦World⟧ Name Name
⟦Name⟧ αᵣ x₁ x₂ = ( x₁ , x₂ ) ∈ αᵣ

⟦Name⟧≡ : ⟦WorldPred⟧ Name Name
⟦Name⟧≡ αᵣ x₁ x₂ = αᵣ ⟨$⟩ᵢ x₁ ≡ x₂

⟦ø⟧ : ⟦World⟧ ø ø
⟦ø⟧ = record { to = Name→-to-Nm⟶ Nameø-elim
             ; injective = λ{x} → Nameø-elim x }

_⟦==ᴺ⟧_ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Bool⟧) _==ᴺ_ _==ᴺ_
_⟦==ᴺ⟧_ αᵣ {_} {x₂} xᵣ {_} {y₂} yᵣ = helper (≡ᴺ⇒≡ {_} {_} {x₂} xᵣ) (≡ᴺ⇒≡ {_} {_} {y₂} yᵣ) where
  helper : (⟦Name⟧≡ αᵣ ⟦→⟧ ⟦Name⟧≡ αᵣ ⟦→⟧ ⟦Bool⟧) _==ᴺ_ _==ᴺ_
  helper {x} ≡.refl {y} ≡.refl =
       x ==ᴺ y       ≈⟨ sym (==ℕ-dec _ _) ⟩
       ⌊ x ≟ᴺ y ⌋   ≈⟨ ⟦dec⟧ (x ≟ᴺ y) (x′ ≟ᴺ y′) (⟶≡.cong (Inj.to αᵣ)) (Inj.injective αᵣ) ⟩
       ⌊ x′ ≟ᴺ y′ ⌋ ≈⟨ ==ℕ-dec _ _ ⟩
       x′ ==ᴺ y′ ∎
    where
      x′ = αᵣ ⟨$⟩ᵢ x
      y′ = αᵣ ⟨$⟩ᵢ y
      open ⟦Bool⟧-Props using (sym)
      open ⟦Bool⟧-Reasoning

⟦zeroᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧)) zeroᴺ zeroᴺ
⟦zeroᴺ⟧ _ = zero

⟦sucᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦+1⟧)) sucᴺ sucᴺ
⟦sucᴺ⟧ _ = suc

⟦sucᴺ↑⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧)) sucᴺ↑ sucᴺ↑
⟦sucᴺ↑⟧ _ = suc

⟦predᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦+1⟧) ⟦→⟧ ⟦Name⟧ αᵣ) predᴺ predᴺ
⟦predᴺ⟧ _ = ⟦ℕ⟧-cong (λ x → x ∸ 1)

⟦addᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ))) addᴺ addᴺ
⟦addᴺ⟧ _ zero x = x
⟦addᴺ⟧ {α₁} {α₂} αᵣ (suc {k₁} {k₂} kᵣ) {x₁} {x₂} x
   = ℕ.suc (name ((αᵣ ⟦+ᵂ⟧ kᵣ) ⟨$⟩ᵢ (k₁ +ℕ name x₁ , _{-p-})))
   ≈⟨ ≡ᴺ-⟦ℕ⟧-cong (λ x → suc (name ((αᵣ ⟦+ᵂ⟧ kᵣ) ⟨$⟩ᵢ x))) ℕe.refl ⟩
     suc (name ((αᵣ ⟦+ᵂ⟧ kᵣ) ⟨$⟩ᵢ (k₁ +ℕ name x₁ , _{-q-})))
   ≈⟨ suc (⟦addᴺ⟧ αᵣ kᵣ {x₁} {x₂} x) ⟩
     suc (k₂ +ℕ name x₂)
   ∎ where open ⟦ℕ⟧-Reasoning

⟦subtractᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ) ⟦→⟧ ⟦Name⟧ αᵣ) subtractᴺ subtractᴺ
⟦subtractᴺ⟧ _ zero x = x
⟦subtractᴺ⟧ {α₁} {α₂} αᵣ (suc {k₁} {k₂} kᵣ) {x₁} {x₂} xᵣ
   = name (αᵣ ⟨$⟩ᵢ (name x₁ ∸ suc k₁ , _{-p-}))
   ≈⟨ ≡-⟦ℕ⟧-cong (λ x → name (αᵣ ⟨$⟩ᵢ x)) (name-injective (≡.sym (∸-+-assoc (name x₁) 1 k₁))) ⟩
      name (αᵣ ⟨$⟩ᵢ (name x₁ ∸ 1 ∸ k₁ , _{-r-}))
   ≈⟨ ⟦subtractᴺ⟧ αᵣ kᵣ {predᴺ x₁} {predᴺ x₂} (⟦predᴺ⟧ (αᵣ ⟦+ᵂ⟧ kᵣ) {x₁} {x₂} xᵣ)  ⟩
      (name x₂ ∸ 1) ∸ k₂
   ≈⟨ ℕe.reflexive (∸-+-assoc (name x₂) 1 k₂) ⟩
      name x₂ ∸ suc k₂
   ∎ where open ⟦ℕ⟧-Reasoning

⟦cmpᴺ-bool⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑ kᵣ ⟧) ⟦→⟧ ⟦Bool⟧) cmpᴺ-bool cmpᴺ-bool
⟦cmpᴺ-bool⟧ αᵣ kᵣ {x₁} {x₂} xᵣ = helper kᵣ {x₁} {x₂} (≡ᴺ⇒≡ xᵣ) where
  helper : (⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧≡ (αᵣ ⟦↑ kᵣ ⟧) ⟦→⟧ ⟦Bool⟧) cmpᴺ-bool cmpᴺ-bool
  helper zero                   ≡.refl  = ⟦false⟧
  helper (suc kᵣ) {zero  , _ }  ≡.refl  = ⟦true⟧
  helper (suc kᵣ) {suc x , pf₁} ≡.refl  = helper kᵣ {x , pf₁} ≡.refl

⟦easy-cmpᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                  ⟦Name⟧ (αᵣ ⟦↑ kᵣ ⟧) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑ kᵣ ⟧) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)
             ) easy-cmpᴺ easy-cmpᴺ
⟦easy-cmpᴺ⟧ αᵣ kᵣ {x₁} {x₂} xᵣ = helper kᵣ {x₁} {x₂} (≡ᴺ⇒≡ xᵣ) where
  helper : (⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧≡ (αᵣ ⟦↑ kᵣ ⟧) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑ kᵣ ⟧) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) easy-cmpᴺ easy-cmpᴺ
  helper zero                             ≡.refl = inj₂ (≡ᴺ-⟦ℕ⟧-cong (λ x → name (αᵣ ⟨$⟩ᵢ x)) ℕe.refl)
  helper (suc kᵣ)           {zero  , _ }  ≡.refl = inj₁ zero
  helper (suc {k₁} {k₂} kᵣ) {suc x , pf₁} ≡.refl
    = ⟦map⟧ _ _ _ _ suc suc (helper kᵣ {x , pf₁} ≡.refl)

⟦cmpᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                  ⟦Name⟧ (αᵣ ⟦↑ kᵣ ⟧) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑ kᵣ ⟧) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)
         ) cmpᴺ cmpᴺ
⟦cmpᴺ⟧ {α₁} {α₂} αᵣ {k₁} {k₂} kᵣ {x₁} {x₂} xᵣ =
   ≡.subst (λ x → (⟦Name⟧ (⟦ø⟧ ⟦↑ kᵣ ⟧) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) (cmpᴺ {α₁} k₁ x₁) x)
           (easy-cmpᴺ≗cmpᴺ {α₂} k₂ x₂)
           (≡.subst (λ x → (⟦Name⟧ (⟦ø⟧ ⟦↑ kᵣ ⟧) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) x
                    (easy-cmpᴺ {α₂} k₂ x₂))
                    (easy-cmpᴺ≗cmpᴺ {α₁} k₁ x₁) (⟦easy-cmpᴺ⟧ αᵣ kᵣ {x₁} {x₂} xᵣ))

⟦protect↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧
           (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ) ⟦→⟧ (⟦Name⟧ (αᵣ ⟦↑1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦↑1⟧))) protect↑1 protect↑1
⟦protect↑1⟧ {α₁} {α₂} αᵣ {β₁} {β₂} βᵣ {f₁} {f₂} fᵣ {x₁} {x₂} xᵣ = helper {x₁} {x₂} (≡ᴺ⇒≡ xᵣ) where
   helper : (⟦Name⟧≡ (αᵣ ⟦↑1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦↑1⟧)) (protect↑1 f₁) (protect↑1 f₂)
   helper {zero ,  _}  ≡.refl = zero
   helper {suc x , pf} ≡.refl = suc (fᵣ ℕe.refl)

_⟦⊆⟧b_ : ⟦WorldRel⟧ _⊆_ _⊆_
_⟦⊆⟧b_ αᵣ βᵣ α⊆β₁ α⊆β₂
  = (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ) (coerceᴺ α⊆β₁) (coerceᴺ α⊆β₂)

data _⟦⊆⟧_ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {β₁ β₂} (βᵣ : ⟦World⟧ β₁ β₂) (x : α₁ ⊆ β₁) (y : α₂ ⊆ β₂) : Set where
  mk⟦⊆⟧ : _⟦⊆⟧b_ αᵣ βᵣ x y → _⟦⊆⟧_ αᵣ βᵣ x y

un⟦⊆⟧ : ∀ {α₁ α₂} {αᵣ : ⟦World⟧ α₁ α₂} {β₁ β₂} {βᵣ : ⟦World⟧ β₁ β₂} {x : α₁ ⊆ β₁} {y : α₂ ⊆ β₂} →
  _⟦⊆⟧_ αᵣ βᵣ x y → _⟦⊆⟧b_ αᵣ βᵣ x y
un⟦⊆⟧ (mk⟦⊆⟧ x) {a} {b} c = x {a} {b} c

-- this is the start of an experimentation to see if the issue with ⟦dropName⟧ is due
-- to implicit lambdas.
_⟦⊆⟧e_ : ⟦WorldRel⟧ _⊆_ _⊆_
_⟦⊆⟧e_ αᵣ βᵣ α⊆β₁ α⊆β₂
  = (⟦Name⟧ αᵣ ⟦→⟧e ⟦Name⟧ βᵣ) (coerceᴺ α⊆β₁) (coerceᴺ α⊆β₂)

⟦⊆-refl⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ αᵣ) ⊆-refl ⊆-refl
⟦⊆-refl⟧ _ = mk⟦⊆⟧ (λ xᵣ → xᵣ)

⟦⊆-trans⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ γᵣ ∶ ⟦World⟧ ⟩⟦→⟧
                  αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (βᵣ ⟦⊆⟧ γᵣ ⟦→⟧ (αᵣ ⟦⊆⟧ γᵣ))) ⊆-trans ⊆-trans
⟦⊆-trans⟧ _ _ _ {_} {f₂} f g = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → un⟦⊆⟧ g {_} {coerceᴺ f₂ x₂} (un⟦⊆⟧ f {x₁} {x₂} xᵣ))

⟦coerceᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ)) coerceᴺ coerceᴺ
⟦coerceᴺ⟧ _ _ α⊆βᵣ {x₁} {x₂} xᵣ = un⟦⊆⟧ α⊆βᵣ {x₁} {x₂} xᵣ

⟦¬Nameø⟧ : (⟦¬⟧(⟦Name⟧ ⟦ø⟧)) ¬Nameø ¬Nameø
⟦¬Nameø⟧ {_ , ()}

⟦⊆-cong-↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧)) ⊆-cong-↑1 ⊆-cong-↑1
⟦⊆-cong-↑1⟧ αᵣ βᵣ {α⊆β₁} {α⊆β₂} α⊆βᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → helper {x₁} {x₂} (≡ᴺ⇒≡ xᵣ)) where
  helper : (⟦Name⟧≡ (αᵣ ⟦↑1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦↑1⟧)) (coerceᴺ (⊆-cong-↑1 α⊆β₁)) (coerceᴺ (⊆-cong-↑1 α⊆β₂))
  helper {zero  , _} ≡.refl = zero
  helper {suc x , p} ≡.refl = suc (un⟦⊆⟧ α⊆βᵣ {x , p} {αᵣ ⟨$⟩ᵢ (x , p)} ℕe.refl)

⟦⊆-cong-+1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧)) ⊆-cong-+1 ⊆-cong-+1
⟦⊆-cong-+1⟧ αᵣ βᵣ {α⊆β₁} {α⊆β₂} α⊆βᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → helper {x₁} {x₂} (≡ᴺ⇒≡ xᵣ)) where
  helper : (⟦Name⟧≡ (αᵣ ⟦+1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦+1⟧)) (coerceᴺ (⊆-cong-+1 α⊆β₁)) (coerceᴺ (⊆-cong-+1 α⊆β₂))
  helper {zero  , ()} _
  helper {suc x , p} ≡.refl = suc (un⟦⊆⟧ α⊆βᵣ {x , p} {αᵣ ⟨$⟩ᵢ (x , p)} ℕe.refl)

⟦⊆-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (αᵣ ⟦↑1⟧)) ⊆-+1↑1 ⊆-+1↑1
⟦⊆-+1↑1⟧ αᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → helper {x₁} {x₂} (≡ᴺ⇒≡ xᵣ)) where
  helper : (⟦Name⟧≡ (αᵣ ⟦+1⟧) ⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧)) (coerceᴺ ⊆-+1↑1) (coerceᴺ ⊆-+1↑1)
  helper {zero  , ()} _
  helper {suc x , p} ≡.refl = suc ℕe.refl

⟦⊆-ø⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦ø⟧ ⟦⊆⟧ αᵣ) ⊆-ø ⊆-ø
⟦⊆-ø⟧ αᵣ = mk⟦⊆⟧ (λ {η₁} {η₂} η → helper {η₁} {η₂} η) where
   helper : (⟦ø⟧ ⟦⊆⟧b αᵣ) ⊆-ø ⊆-ø
   helper {_ , ()}

⟦⊆-+1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-+1-inj ⊆-+1-inj
⟦⊆-+1-inj⟧ _ _ α+⊆β+ᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → ⟦ℕ⟧-cong (λ x → x ∸ 1) (un⟦⊆⟧ α+⊆β+ᵣ {sucᴺ x₁} {sucᴺ x₂} (suc xᵣ)))

⟦⊆-↑1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-↑1-inj ⊆-↑1-inj
⟦⊆-↑1-inj⟧ _ _ α↑⊆β↑ᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → ⟦ℕ⟧-cong (λ x → x ∸ 1) (un⟦⊆⟧ α↑⊆β↑ᵣ {sucᴺ↑ x₁} {sucᴺ↑ x₂} (suc xᵣ)))

⟦⊆-unctx-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-unctx-+1↑1 ⊆-unctx-+1↑1
⟦⊆-unctx-+1↑1⟧ _ _ α+⊆β↑ᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → ⟦ℕ⟧-cong (λ x → x ∸ 1) (un⟦⊆⟧ α+⊆β↑ᵣ {sucᴺ x₁} {sucᴺ x₂} (suc xᵣ)))

⟦α⊆ø→α+1⊆ø⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ ⟦ø⟧ ⟦→⟧ αᵣ ⟦+1⟧ ⟦⊆⟧ ⟦ø⟧) α⊆ø→α+1⊆ø α⊆ø→α+1⊆ø
⟦α⊆ø→α+1⊆ø⟧ _ {α⊆ø} _ = mk⟦⊆⟧ (λ {x} _ → Name-elim α⊆ø (predᴺ x))

⟦α+1⊆ø→α⊆ø⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦+1⟧ ⟦⊆⟧ ⟦ø⟧ ⟦→⟧ αᵣ ⟦⊆⟧ ⟦ø⟧) α+1⊆ø→α⊆ø α+1⊆ø→α⊆ø
⟦α+1⊆ø→α⊆ø⟧ _ {α+1⊆ø} _ = mk⟦⊆⟧ (λ {x} _ → Name-elim α+1⊆ø (sucᴺ x))

-- not primitive

⟦predᴺ?⟧-core : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) x
                    → ⟦Maybe⟧ (⟦Name⟧ αᵣ) (predᴺ? x) (predᴺ? (protect↑1 (_⟨$⟩ᵢ_ αᵣ) x))
⟦predᴺ?⟧-core _  (zero  , _) = ⟦nothing⟧
⟦predᴺ?⟧-core αᵣ (suc _ , _) = ⟦just⟧ (⟶≡.cong (Inj.to αᵣ) ℕe.refl)

⟦predᴺ?⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧) ⟦→⟧ ⟦Maybe⟧ (⟦Name⟧ αᵣ)) predᴺ? predᴺ?
⟦predᴺ?⟧ {_} {α₂} αᵣ {x₁} {x₂} xᵣ = helper {x₂} (≡ᴺ⇒≡ xᵣ)
    -- BUG: the 'with' notation failed here
  where helper : ∀ {x₂} (eq : protect↑1 (_⟨$⟩ᵢ_ αᵣ) x₁ ≡ x₂) → ⟦Maybe⟧ (⟦Name⟧ αᵣ) (predᴺ? x₁) (predᴺ? x₂)
        helper ≡.refl = ⟦predᴺ?⟧-core αᵣ x₁

⟦⊆-ctx-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧)) ⊆-ctx-+1↑1 ⊆-ctx-+1↑1
⟦⊆-ctx-+1↑1⟧ αᵣ βᵣ {α⊆β₁} {α⊆β₂} α⊆βᵣ = mk⟦⊆⟧ (λ {x₁} {x₂} xᵣ → helper {x₁} {x₂} (≡ᴺ⇒≡ xᵣ)) where
  helper : (⟦Name⟧≡ (αᵣ ⟦+1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦↑1⟧)) (coerceᴺ (⊆-ctx-+1↑1 α⊆β₁)) (coerceᴺ (⊆-ctx-+1↑1 α⊆β₂))
  helper {zero  , ()} _
  helper {suc x , p} ≡.refl = suc (un⟦⊆⟧ α⊆βᵣ {x , p} {αᵣ ⟨$⟩ᵢ (x , p)} ℕe.refl)

⟦¬Name⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ ⟦ø⟧ ⟦→⟧ (⟦¬⟧(⟦Name⟧ αᵣ))) ¬Name ¬Name
⟦¬Name⟧ _ {α⊆ø₁} _ {x₁} _ = Name-elim α⊆ø₁ x₁

⟦⊆-cong-+⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ((αᵣ ⟦+ᵂ⟧ kᵣ) ⟦⊆⟧ (βᵣ ⟦+ᵂ⟧ kᵣ)))) ⊆-cong-+ ⊆-cong-+
⟦⊆-cong-+⟧ _ _ α⊆βᵣ zero    = α⊆βᵣ
⟦⊆-cong-+⟧ _ _ α⊆βᵣ (suc kᵣ) = ⟦⊆-cong-+1⟧ _ _ (⟦⊆-cong-+⟧ _ _ α⊆βᵣ kᵣ)

⟦⊆-+-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ((αᵣ ⟦+ᵂ⟧ kᵣ) ⟦⊆⟧ (βᵣ ⟦+ᵂ⟧ kᵣ)) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-+-inj ⊆-+-inj
⟦⊆-+-inj⟧ _ _ zero    α⊆βᵣ = α⊆βᵣ
⟦⊆-+-inj⟧ _ _ (suc kᵣ) α⊆βᵣ = ⟦⊆-+-inj⟧ _ _ kᵣ (⟦⊆-+1-inj⟧ _ _ α⊆βᵣ)

⟦⊆-assoc-+′⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (⟨ k₁ᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ (⟨ k₂ᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                 (αᵣ ⟦+ᵂ⟧ (k₂ᵣ ⟦+ℕ⟧ k₁ᵣ)) ⟦⊆⟧ ((βᵣ ⟦+ᵂ⟧ k₁ᵣ) ⟦+ᵂ⟧ k₂ᵣ)))) ⊆-assoc-+′ ⊆-assoc-+′
⟦⊆-assoc-+′⟧ _ _ base k₁ zero      = ⟦⊆-cong-+⟧ _ _ base k₁
⟦⊆-assoc-+′⟧ _ _ base k₁ (suc k₂)  = ⟦⊆-cong-+1⟧ _ _ (⟦⊆-assoc-+′⟧ _ _ base k₁ k₂)
