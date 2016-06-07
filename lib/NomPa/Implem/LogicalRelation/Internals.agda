{-# OPTIONS --universe-polymorphism #-}
import Level as L
open import Data.Bool.NP
open import Data.Nat.Logical
open import Data.Two hiding (_==_)
open import Data.Two.Logical
open import Data.Unit
open import Data.Empty
open import Data.Sum.NP
open import Data.Sum.Logical
open import Data.Maybe.NP
open import Data.List
open import Data.Product.NP
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Binary.NP as Bin
open import Relation.Binary.Logical
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as ⇔ using (_⇔_; equivalence; module Equivalence)
import Relation.Binary.PropositionalEquality.NP as ≡
open import Relation.Binary.PropositionalEquality.Param.Binary
import Data.Nat.NP as ℕ
open ℕ renaming (_==_ to _==ℕ_)
import Data.Nat.Properties as ℕ
open import NomPa.Record using (module NomPa)
open import NomPa.Implem
import NaPa
open NaPa using (∈-uniq)
open import NomPa.Worlds
import NomPa.Derived

module NomPa.Implem.LogicalRelation.Internals where

open ≡ using (_≡_; _≢_)
open ≡.≡-Reasoning
open NomPa.Implem.Internals
open NomPa NomPa.Implem.nomPa using (worldSym; Nameø-elim; sucᴺ; sucᴺ↑)

-- move to record
predᴺ : ∀ {α} → Name (α +1) → Name α
predᴺ = subtractᴺ 1

≢→✓-not-==ℕ : ∀ {x y} → x ≢ y → ✓ (not (x ==ℕ y))
≢→✓-not-==ℕ ¬p = ✓-¬-not (¬p ∘ ℕ.==.sound _ _)

#⇒∉ : ∀ {α b} → b # α → b ∉ α
#⇒∉ (_ #ø)      = id
#⇒∉ (suc#∷ b#α) = #⇒∉ b#α
#⇒∉ (0# _)      = id

#⇒≢ : ∀ {α b} → b # α → (x : Name α) → binderᴺ x ≢ b
#⇒≢ b# (b , b∈) ≡.refl = #⇒∉ b# b∈

binderᴺ-injective : ∀ {α} {x y : Name α} → binderᴺ x ≡ binderᴺ y → x ≡ y
binderᴺ-injective {α} {_ , p₁} {a , p₂} eq rewrite eq = ≡.cong (_,_ a) (∈-uniq α p₁ p₂)

pf-irr′ : ∀ {α β} (ℛ : Name α → Name β → Set) {x x′ : Name α} {y y′ : Name β}
         → binderᴺ x ≡ binderᴺ x′ → binderᴺ y ≡ binderᴺ y′ → ℛ x y → ℛ x′ y′
pf-irr′ {α} {β} ℛ {x , x∈} {x′ , x′∈} {y , y∈} {y′ , y′∈} eq₁ eq₂ xᵣy
  rewrite eq₁ | eq₂ | ∈-uniq α x∈ x′∈ | ∈-uniq β y∈ y′∈ = xᵣy

pf-irr : ∀ {α β} (ℛ : Name α → Name β → Set) {x y x∈ x∈′ y∈ y∈′}
         → ℛ (x , x∈) (y , y∈) → ℛ (x , x∈′) (y , y∈′)
pf-irr ℛ = pf-irr′ ℛ ≡.refl ≡.refl

Preserve-≈ : ∀ {a b ℓ ℓa ℓb} {A : Set a} {B : Set b} → Rel A ℓa → Rel (B) ℓb → REL A (B) ℓ → Set _
Preserve-≈ _≈a_ _≈b_ _∼_ = ∀ {x₁ x₂ y₁ y₂} → x₁ ∼ x₂ → y₁ ∼ y₂ → (x₁ ≈a y₁) ⇔ (x₂ ≈b y₂)

==ℕ⇔≡ : ∀ {x y} → ✓ (x ==ℕ y) ⇔ x ≡ y
==ℕ⇔≡ {x} {y} = equivalence (ℕ.==.sound _ _) ℕ.==.reflexive

≡-on-name⇔≡ : ∀ {α} {x y : Name α} → binderᴺ x ≡ binderᴺ y ⇔ x ≡ y
≡-on-name⇔≡ {α} {x} {y} = equivalence binderᴺ-injective (≡.cong binderᴺ)

T⇔T→≡ : ∀ {b₁ b₂} → ✓ b₁ ⇔ ✓ b₂ → b₁ ≡ b₂
T⇔T→≡ {1₂} {1₂} b₁⇔b₂ = ≡.refl
T⇔T→≡ {1₂} {0₂} b₁⇔b₂ = ⊥-elim (Equivalence.to b₁⇔b₂ ⟨$⟩ _)
T⇔T→≡ {0₂} {1₂} b₁⇔b₂ = ⊥-elim (Equivalence.from b₁⇔b₂ ⟨$⟩ _)
T⇔T→≡ {0₂} {0₂} b₁⇔b₂ = ≡.refl

==ᴺ⇔≡ : ∀ {α} {x y : Name α} → ✓ (x ==ᴺ y) ⇔ x ≡ y
==ᴺ⇔≡ = ≡-on-name⇔≡ ⟨∘⟩ ==ℕ⇔≡ where open ⇔ renaming (_∘_ to _⟨∘⟩_)

-- Preserving the equalities also mean that the relation is functional and injective
Preserve-≡ : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A (B) ℓ → Set _
Preserve-≡ _∼_ = Preserve-≈ _≡_ _≡_ _∼_

exportᴺ?-nothing : ∀ {b α} (x : Name (b ◅ α)) → ✓ (binderᴺ x ==ℕ b) → exportᴺ? {b} x ≡ nothing
exportᴺ?-nothing {b} {α} (x , x∈) p with x ==ℕ b | export∈ α x b
... | 1₂ | _ = ≡.refl
... | 0₂ | _ = ⊥-elim p

exportᴺ?-just : ∀ {α b} (x : Name (b ◅ α)) {x∈} → ✓ (not (binderᴺ x ==ℕ b)) → exportᴺ? {b} x ≡ just (binderᴺ x , x∈)
exportᴺ?-just {α} {b} (x , x∈) p with x ==ℕ b | export∈ α x b
... | 1₂ | _ = ⊥-elim p
... | 0₂ | _ = ≡.cong just (binderᴺ-injective ≡.refl)

record ⟦World⟧ (α₁ α₂ : World) : Set₁ where
  constructor _,_
  field
    _∼_ : Name α₁ → Name α₂ → Set
    ∼-pres-≡ : Preserve-≡ _∼_

  ∼-inj : ∀ {x y z} → x ∼ z → y ∼ z → x ≡ y
  ∼-inj p q = Equivalence.from (∼-pres-≡ p q) ⟨$⟩ ≡.refl
  ∼-fun : ∀ {x y z} → x ∼ y → x ∼ z → y ≡ z
  ∼-fun p q = Equivalence.to (∼-pres-≡ p q) ⟨$⟩ ≡.refl

  ∼-∈-uniq : ∀ {x₁ x₂} {x₁∈′ x₂∈′} →
        x₁ ∼ x₂ ≡ (binderᴺ x₁ , x₁∈′) ∼ (binderᴺ x₂ , x₂∈′)
  ∼-∈-uniq {_ , x₁∈} {_ , x₂∈} {x₁∈′} {x₂∈′} = ≡.ap₂ (λ x₁∈ x₂∈ → (_ , x₁∈) ∼ (_ , x₂∈)) (∈-uniq α₁ x₁∈ x₁∈′) (∈-uniq α₂ x₂∈ x₂∈′)

⟦sym⟧ : ∀ {α₁ α₂} → ⟦World⟧ α₁ α₂ → ⟦World⟧ α₂ α₁
⟦sym⟧ (ℛ , ℛ-pres-≡) = ℛ-sym , ℛ-sym-pres-≡
  where ℛ-sym = flip ℛ
        ℛ-sym-pres-≡ : Preserve-≡ ℛ-sym
        ℛ-sym-pres-≡ p q = ⇔.sym (ℛ-pres-≡ p q)

record ⟦Binder⟧ (b₁ b₂ : Binder) : Set where

module ⟦◅⟧ (b₁ b₂ : Binder) {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) where
  open ⟦World⟧ αᵣ
  data _ℛ_ (x : Name (b₁ ◅ α₁)) (y : Name (b₂ ◅ α₂)) : Set where
    here  : (x≡b₁ : binderᴺ x ≡ b₁) (y≡b₂ : binderᴺ y ≡ b₂) → x ℛ y
    there : ∀ (x≢b₁ : binderᴺ x ≢ b₁) (y≢b₂ : binderᴺ y ≢ b₂) {x∈ y∈} (x∼y : (binderᴺ x , x∈) ∼ (binderᴺ y , y∈)) → x ℛ y

  ℛ-inj : ∀ {x y z} → x ℛ z → y ℛ z → x ≡ y
  ℛ-inj (here x≡b₁ _)    (here y≡b₁ _)     = binderᴺ-injective (≡.trans x≡b₁ (≡.sym y≡b₁))
  ℛ-inj (here _ z≡b₂)    (there _ z≢b₂ _)  = ⊥-elim (z≢b₂ z≡b₂)
  ℛ-inj (there _ z≢b₂ _) (here _ z≡b₂)     = ⊥-elim (z≢b₂ z≡b₂)
  ℛ-inj {x} {y} {z} (there x≢b₁ z≢b₂ {x∈} {z∈} x∼z) (there y≢b₁ _ {y∈} {z∈′} y∼z) =
    binderᴺ-injective (≡.cong binderᴺ (∼-inj x∼z (≡.tr (λ z∈ → (binderᴺ y , y∈) ∼ (binderᴺ z , z∈)) (∈-uniq α₂ z∈′ z∈) y∼z )))

  ℛ-fun : ∀ {x y z} → x ℛ y → x ℛ z → y ≡ z
  ℛ-fun (here _ y≡b₂)  (here _ z≡b₂)    = binderᴺ-injective (≡.trans y≡b₂ (≡.sym z≡b₂))
  ℛ-fun (here p _)     (there ¬p _ _)    = ⊥-elim (¬p p)
  ℛ-fun (there ¬p _ _) (here p _)        = ⊥-elim (¬p p)
  ℛ-fun {x} {y} {z} (there x≢b₁ y≢b₂ {x∈} {y∈} x∼y) (there p q {x∈′} {z∈} x∼z) =
    binderᴺ-injective (≡.cong binderᴺ (∼-fun x∼y (≡.tr (λ x∈ → (binderᴺ x , x∈) ∼ (binderᴺ z , z∈)) (∈-uniq α₁ x∈′ x∈) x∼z )))

  ℛ-pres-≡ : Preserve-≡ _ℛ_
  ℛ-pres-≡ {x₁} {x₂} {y₁} {y₂} x₁∼x₂ y₁∼y₂ =
     equivalence (λ x₁=y₁ → ℛ-fun {y₁} (≡.tr (λ x₁ → x₁ ℛ x₂) x₁=y₁ x₁∼x₂) y₁∼y₂)
                 (λ x₂=y₂ → ℛ-inj x₁∼x₂ (≡.tr (λ y₂ → y₁ ℛ y₂) (≡.sym x₂=y₂) y₁∼y₂))

  ⟦world⟧ : ⟦World⟧ (b₁ ◅ α₁) (b₂ ◅ α₂)
  ⟦world⟧ = _ℛ_ , ℛ-pres-≡

here′ : ∀ {α₁ α₂ b₁ b₂ pf₁ pf₂} {αᵣ : ⟦World⟧ α₁ α₂} → ⟦◅⟧._ℛ_ b₁ b₂ αᵣ (b₁ , pf₁) (b₂ , pf₂)
here′ = ⟦◅⟧.here ≡.refl ≡.refl

_⟦◅⟧_ : (⟦Binder⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦World⟧) _◅_ _◅_
_⟦◅⟧_ {b₁} {b₂} _ αᵣ = ⟦◅⟧.⟦world⟧ b₁ b₂ αᵣ

⟦Name⟧ : ⟦Pred⟧ L.zero ⟦World⟧ Name Name
⟦Name⟧ (ℛ , _) x₁ x₂ = ℛ x₁ x₂

⟦zeroᴮ⟧ : ⟦Binder⟧ zeroᴮ zeroᴮ
⟦zeroᴮ⟧ = _

⟦sucᴮ⟧ : (⟦Binder⟧ ⟦→⟧ ⟦Binder⟧) sucᴮ sucᴮ
⟦sucᴮ⟧ = _

⟦ø⟧ : ⟦World⟧ ø ø
⟦ø⟧ = (λ _ _ → ⊥) , (λ())

_⟦==ᴺ⟧_ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦𝟚⟧) _==ᴺ_ _==ᴺ_
_⟦==ᴺ⟧_ αᵣ xᵣ yᵣ =
   ⟦𝟚⟧-Props.reflexive (T⇔T→≡ (sym ==ᴺ⇔≡ ⟨∘⟩ ∼-pres-≡ xᵣ yᵣ ⟨∘⟩ ==ᴺ⇔≡)) where
  open ⟦World⟧ αᵣ
  open ⇔ using (sym) renaming (_∘_ to _⟨∘⟩_)

⟦nameᴮ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ)) nameᴮ nameᴮ
⟦nameᴮ⟧ _ _ = here′

⟦binderᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Binder⟧) binderᴺ binderᴺ
⟦binderᴺ⟧ _ _ = _

⟦nothing⟧′ : ∀ {a} {A₁ A₂ : Set a} {Aᵣ : A₁ → A₂ → Set} {x : Maybe A₁} {y : Maybe A₂}
            → x ≡ nothing → y ≡ nothing → ⟦Maybe⟧ Aᵣ x y
⟦nothing⟧′ ≡.refl ≡.refl = ⟦nothing⟧

⟦just⟧′ : ∀ {a} {A₁ A₂ : Set a} {Aᵣ : A₁ → A₂ → Set} {x : Maybe A₁} {y : Maybe A₂} {x′ y′}
            → x ≡ just x′ → y ≡ just y′ → Aᵣ x′ y′ → ⟦Maybe⟧ Aᵣ x y
⟦just⟧′ ≡.refl ≡.refl = ⟦just⟧

⟦exportᴺ?⟧ : (∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ ∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦→⟧ ⟦Maybe⟧ (⟦Name⟧ αᵣ)) (λ {b} → exportᴺ? {b}) (λ {b} → exportᴺ? {b})
⟦exportᴺ?⟧ _ αᵣ {x₁} {x₂} (⟦◅⟧.here e₁ e₂)
  = ⟦nothing⟧′ (exportᴺ?-nothing x₁ (ℕ.==.reflexive e₁)) (exportᴺ?-nothing x₂ (ℕ.==.reflexive e₂))
⟦exportᴺ?⟧ _ αᵣ {x₁} {x₂} (⟦◅⟧.there x₁≢b₁ x₂≢b₂ x₁∼x₂)
  = ⟦just⟧′ (exportᴺ?-just x₁ (≢→✓-not-==ℕ x₁≢b₁))
           (exportᴺ?-just x₂ (≢→✓-not-==ℕ x₂≢b₂)) x₁∼x₂

_⟦⊆⟧b_ : ⟦Rel⟧ ⟦World⟧ L.zero _⊆_ _⊆_
_⟦⊆⟧b_ αᵣ βᵣ x y = (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ) (coerceᴺ x) (coerceᴺ y)

data _⟦⊆⟧_ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {β₁ β₂} (βᵣ : ⟦World⟧ β₁ β₂) (x : α₁ ⊆ β₁) (y : α₂ ⊆ β₂) : Set where
  mk : _⟦⊆⟧b_ αᵣ βᵣ x y → _⟦⊆⟧_ αᵣ βᵣ x y

un⟦⊆⟧ : ∀ {α₁ α₂} {αᵣ : ⟦World⟧ α₁ α₂} {β₁ β₂} {βᵣ : ⟦World⟧ β₁ β₂} {x y} → (αᵣ ⟦⊆⟧ βᵣ) x y → (αᵣ ⟦⊆⟧b βᵣ) x y
un⟦⊆⟧ (mk x) {a} {b} c = x {a} {b} c

⟦⊆-refl⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ αᵣ) ⊆-refl ⊆-refl
⟦⊆-refl⟧ _ = mk (λ xᵣ → xᵣ)

⟦⊆-trans⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ γᵣ ∶ ⟦World⟧ ⟩⟦→⟧
                  αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (βᵣ ⟦⊆⟧ γᵣ ⟦→⟧ (αᵣ ⟦⊆⟧ γᵣ))) ⊆-trans ⊆-trans
⟦⊆-trans⟧ _ _ _ {mk f₁} {mk f₂} f {mk g₁} {mk g₂} g
  = mk (λ {x₁} {x₂} xᵣ → un⟦⊆⟧ g {coerceᴺ (mk f₁) x₁} {coerceᴺ (mk f₂) x₂} (un⟦⊆⟧ f {x₁} {x₂} xᵣ))

⟦coerceᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ)) coerceᴺ coerceᴺ
⟦coerceᴺ⟧ _ _ α⊆βᵣ {x₁} {x₂} xᵣ = un⟦⊆⟧ α⊆βᵣ {x₁} {x₂} xᵣ

⟦¬Nameø⟧ : (⟦¬⟧(⟦Name⟧ ⟦ø⟧)) ¬Nameø ¬Nameø
⟦¬Nameø⟧ ()

⟦⊆-ø⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦ø⟧ ⟦⊆⟧ αᵣ) ⊆-ø ⊆-ø
⟦⊆-ø⟧ αᵣ = mk λ { {_ , ()} }

_⟦#⟧_ : (⟦Binder⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦Set₀⟧) _#_ _#_
_⟦#⟧_ _ _ _ _ = ⊤

_⟦#ø⟧ : (⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ bᵣ ⟦#⟧ ⟦ø⟧) _#ø _#ø
_⟦#ø⟧ _ = _

⟦suc#⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ bᵣ ⟦#⟧ αᵣ ⟦→⟧ (⟦sucᴮ⟧ bᵣ) ⟦#⟧ (bᵣ ⟦◅⟧ αᵣ)) suc# suc#
⟦suc#⟧ _ _ _ = _

⟦⊆-#⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                  (bᵣ ⟦#⟧ αᵣ) ⟦→⟧ αᵣ ⟦⊆⟧ (bᵣ ⟦◅⟧ αᵣ)) ⊆-# ⊆-#
⟦⊆-#⟧ _ {b₁} {b₂} _ {b₁#α₁} {b₂#α₂} _ = mk (λ {x₁} {x₂} → ⟦◅⟧.there (#⇒≢ b₁#α₁ x₁) (#⇒≢ b₂#α₂ x₂))

⟦⊆-◅⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦⊆⟧ (bᵣ ⟦◅⟧ βᵣ)) ⊆-◅ ⊆-◅
⟦⊆-◅⟧ {α₁} {α₂} αᵣ {β₁} {β₂} βᵣ {b₁} {b₂} _ {α⊆β₁} {α⊆β₂} (mk f) = mk g where
  open ⟦◅⟧ b₁ b₂
  g : ∀ {x₁ x₂} → _ℛ_ αᵣ x₁ x₂ → _ℛ_ βᵣ (coerceᴺ (⊆-◅ b₁ α⊆β₁) x₁) (coerceᴺ (⊆-◅ b₂ α⊆β₂) x₂)
  g (here x≡b₁ y≡b₂)       = here x≡b₁ y≡b₂
  g (there x≢b₁ y≢b₂ x∼y) = there x≢b₁ y≢b₂ (f x∼y)

congℕ : ∀ {α β : World} {x y : Name α} (f : ℕ → ℕ) {fx∈ fy∈} → x ≡ y → _≡_ {A = Name β} (f (binderᴺ x) , fx∈) (f (binderᴺ y) , fy∈)
congℕ f = binderᴺ-injective ∘ ≡.cong (f ∘ binderᴺ)

module ⟦+1⟧ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) where
  open ⟦World⟧ αᵣ renaming (_∼_ to ℛ; ∼-inj to ℛ-inj; ∼-fun to ℛ-fun)
  ℛ+1 : Name (α₁ +1) → Name (α₂ +1) → Set
  ℛ+1 x y = ⟦Name⟧ αᵣ (predᴺ x) (predᴺ y)
{-
  data ℛ+1 : Name (α₁ +1) → Name (α₂ +1) → Set where
    suc : ∀ {x x∈ y y∈} → ⟦Name⟧ αᵣ x y → ℛ+1 (suc x , ) (sucN y)
  data ℛ+1 : Name (α₁ +1) → Name (α₂ +1) → Set where
    suc : ∀ {x y} → ⟦Name⟧ αᵣ x y → ℛ+1 (sucN x) (sucN y)
-}

  ℛ+1-inj : ∀ {x y z} → ℛ+1 x z →  ℛ+1 y z → x ≡ y
  -- ℛ+1-inj {suc x , _} {suc y , _} {suc z , _} (suc a) (suc b) = {!!}
  ℛ+1-inj {suc x , _} {suc y , _} {suc z , _} a b = congℕ suc (ℛ-inj a b)
  ℛ+1-inj {zero , ()} _ _
  ℛ+1-inj {_} {zero , ()} _ _
  ℛ+1-inj {_} {_} {zero , ()} _ _
  ℛ+1-fun : ∀ {x y z} → ℛ+1 x y →  ℛ+1 x z → y ≡ z
  ℛ+1-fun {suc x , _} {suc y , _} {suc z , _} a b = congℕ suc (ℛ-fun a b)
  ℛ+1-fun {zero , ()} _ _
  ℛ+1-fun {_} {zero , ()} _ _
  ℛ+1-fun {_} {_} {zero , ()} _ _

  ℛ+1-pres-≡ : Preserve-≡ ℛ+1
  -- ℛ+1-pres-≡ x y = equivalence {!ℛ+1-inj!} {!!}
  ℛ+1-pres-≡ {x₁} {x₂} {y₁} {y₂} x₁∼x₂ y₁∼y₂ =
     -- factor this move
     equivalence (λ x₁=y₁ → ℛ+1-fun {y₁} (≡.tr (λ x₁ → ℛ+1 x₁ x₂) x₁=y₁ x₁∼x₂) y₁∼y₂)
                 (λ x₂=y₂ → ℛ+1-inj {x₁} {y₁} {x₂} x₁∼x₂ (≡.tr (λ y₂ → ℛ+1 y₁ y₂) (≡.sym x₂=y₂) y₁∼y₂))


infix 21 _⟦+1⟧
_⟦+1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _+1 _+1
_⟦+1⟧ αᵣ = ℛ+1 , ℛ+1-pres-≡ where open ⟦+1⟧ αᵣ

open WorldOps worldSym

_⟦↑1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) _↑1 _↑1
_⟦↑1⟧ αᵣ = ⟦zeroᴮ⟧ ⟦◅⟧ (αᵣ ⟦+1⟧)

_⟦↑⟧_ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) _↑_ _↑_
_⟦↑⟧_ αᵣ ⟦zero⟧    = αᵣ
_⟦↑⟧_ αᵣ (⟦suc⟧ k) = (αᵣ ⟦↑⟧ k) ⟦↑1⟧

_⟦+ᵂ⟧_ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) _+ᵂ_ _+ᵂ_
_⟦+ᵂ⟧_ αᵣ ⟦zero⟧    = αᵣ
_⟦+ᵂ⟧_ αᵣ (⟦suc⟧ k) = (αᵣ ⟦+ᵂ⟧ k) ⟦+1⟧

⟦predᴺ⟧-sucᴺ↑ : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂)
                 {x₁ x₂} (xᵣ : ⟦Name⟧ (αᵣ ⟦↑1⟧) (sucᴺ↑ x₁) (sucᴺ↑ x₂)) → ⟦Name⟧ αᵣ x₁ x₂
⟦predᴺ⟧-sucᴺ↑ _  (⟦◅⟧.here () _)
⟦predᴺ⟧-sucᴺ↑ αᵣ (⟦◅⟧.there _ _ x∼y) = pf-irr (⟦Name⟧ αᵣ) x∼y

⟦ø+1⊆ø⟧ : (⟦ø⟧ ⟦+1⟧ ⟦⊆⟧ ⟦ø⟧) ø+1⊆ø ø+1⊆ø
⟦ø+1⊆ø⟧ = mk (λ {x} _ → Nameø-elim (predᴺ x))

⟦⊆-cong-+1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧)) ⊆-cong-+1 ⊆-cong-+1
⟦⊆-cong-+1⟧ _ βᵣ α⊆βᵣ = mk (pf-irr (⟦Name⟧ βᵣ) ∘ un⟦⊆⟧ α⊆βᵣ)

⟦⊆-cong-↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧)) ⊆-cong-↑1 ⊆-cong-↑1
⟦⊆-cong-↑1⟧ αᵣ βᵣ {α⊆β₁} {α⊆β₂} α⊆βᵣ = mk helper where
  open ⟦◅⟧ 0 0
  helper : (⟦Name⟧ (αᵣ ⟦↑1⟧) ⟦→⟧ ⟦Name⟧ (βᵣ ⟦↑1⟧)) (coerceᴺ (⊆-cong-↑1 α⊆β₁)) (coerceᴺ (⊆-cong-↑1 α⊆β₂))
  helper (here x≡b₁ y≡b₂) = here x≡b₁ y≡b₂
  helper {x₁ , _} {x₂ , _} (there x≢b₁ y≢b₂ {p₁} {p₂} x∼y)
     = there x≢b₁ y≢b₂ {coe (⊆-cong-+1 α⊆β₁) x₁ p₁}
                        {coe (⊆-cong-+1 α⊆β₂) x₂ p₂}
                        (pf-irr (⟦Name⟧ βᵣ) (un⟦⊆⟧ α⊆βᵣ x∼y))

⟦⊆-+1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-+1-inj ⊆-+1-inj
⟦⊆-+1-inj⟧ _ _ α+⊆β+ᵣ = mk (λ {x₁} {x₂} → un⟦⊆⟧ α+⊆β+ᵣ {addᴺ 1 x₁} {addᴺ 1 x₂}) 

≢0 : ∀ {α} (x : Name (α +1)) → binderᴺ x ≢ 0
≢0 (0 , ()) ≡.refl
≢0 (suc _ , _) ()

⟦⊆-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (αᵣ ⟦↑1⟧)) ⊆-+1↑1 ⊆-+1↑1
⟦⊆-+1↑1⟧ αᵣ = mk (λ {x₁} {x₂} → there (≢0 x₁) (≢0 x₂)) where open ⟦◅⟧ 0 0

⟦⊆-↑1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-↑1-inj ⊆-↑1-inj
⟦⊆-↑1-inj⟧ _ βᵣ α↑⊆β↑ᵣ = mk (λ {x₁} {x₂} xᵣ → ⟦predᴺ⟧-sucᴺ↑ βᵣ (un⟦⊆⟧ α↑⊆β↑ᵣ {sucᴺ↑ x₁} {sucᴺ↑ x₂} (there (λ()) (λ()) xᵣ))) where
  open ⟦◅⟧ 0 0

⟦⊆-unctx-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) ⊆-unctx-+1↑1 ⊆-unctx-+1↑1
⟦⊆-unctx-+1↑1⟧ _ βᵣ α+⊆β↑ᵣ = mk (λ {x₁} {x₂} xᵣ → helper (un⟦⊆⟧ α+⊆β↑ᵣ {sucᴺ x₁} {sucᴺ x₂} xᵣ)) where
  open ⟦◅⟧ 0 0
  helper : ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ (βᵣ ⟦↑1⟧) (sucᴺ↑ x₁) (sucᴺ↑ x₂)) → ⟦Name⟧ βᵣ x₁ x₂
  helper (here () _)
  helper (there _ _ x∼y) = pf-irr (⟦Name⟧ βᵣ) x∼y

⟦sucᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦+1⟧)) sucᴺ sucᴺ
⟦sucᴺ⟧ αᵣ = pf-irr (⟦Name⟧ αᵣ)

⟦predᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦+1⟧) ⟦→⟧ ⟦Name⟧ αᵣ) predᴺ predᴺ
⟦predᴺ⟧ αᵣ = pf-irr (⟦Name⟧ αᵣ)

⟦sucᴺ↑⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧)) sucᴺ↑ sucᴺ↑
⟦sucᴺ↑⟧ αᵣ xᵣ = ⟦coerceᴺ⟧ _ _ (⟦⊆-+1↑1⟧ αᵣ) (⟦sucᴺ⟧ αᵣ xᵣ)

⟦addᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ))) addᴺ addᴺ
⟦addᴺ⟧ _  ⟦zero⟧ xᵣ = xᵣ
⟦addᴺ⟧ αᵣ (⟦suc⟧ kᵣ) xᵣ = pf-irr (⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) (⟦addᴺ⟧ αᵣ kᵣ xᵣ)

⟦subtractᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ) ⟦→⟧ ⟦Name⟧ αᵣ) subtractᴺ subtractᴺ
⟦subtractᴺ⟧ _ ⟦zero⟧ x = x
⟦subtractᴺ⟧ αᵣ (⟦suc⟧ {k₁} {k₂} kᵣ) {x₁} {x₂} xᵣ
   = pf-irr′ (⟦Name⟧ αᵣ) (ℕ.∸-+-assoc (binderᴺ x₁) 1 k₁) (ℕ.∸-+-assoc (binderᴺ x₂) 1 k₂) (⟦subtractᴺ⟧ αᵣ kᵣ xᵣ)

¬⟦Name⟧-αᵣ-⟦↑1⟧-0-suc : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {pf₁ : 0 ∈ α₁ ↑1} {n} {pf₂ : suc n ∈ α₂ ↑1} → ¬(⟦Name⟧ (αᵣ ⟦↑1⟧) (0 , pf₁) (suc n , pf₂))
¬⟦Name⟧-αᵣ-⟦↑1⟧-0-suc _ (⟦◅⟧.there p _ _) = p ≡.refl
¬⟦Name⟧-αᵣ-⟦↑1⟧-0-suc _ (⟦◅⟧.here _ ())

¬⟦Name⟧-αᵣ-⟦↑1⟧-suc-0 : ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) {n} {pf₁ : suc n ∈ α₁ ↑1} {pf₂ : 0 ∈ α₂ ↑1} → ¬(⟦Name⟧ (αᵣ ⟦↑1⟧) (suc n , pf₁) (0 , pf₂))
¬⟦Name⟧-αᵣ-⟦↑1⟧-suc-0 _ (⟦◅⟧.there _ p _) = p ≡.refl
¬⟦Name⟧-αᵣ-⟦↑1⟧-suc-0 _ (⟦◅⟧.here () _)

-- cmpᴺ-bool : ∀ {α} ℓ → Name (α ↑ ℓ) → 𝟚
-- cmpᴺ-bool ℓ x = suc (binderᴺ x) <= ℓ

⟦cmpᴺ-bool⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑⟧ kᵣ) ⟦→⟧ ⟦𝟚⟧) NaPa.cmpᴺ-bool NaPa.cmpᴺ-bool
⟦cmpᴺ-bool⟧ _ ⟦zero⟧ _ = ⟦0₂⟧
⟦cmpᴺ-bool⟧ _ (⟦suc⟧ _) {zero , _} {zero , _} _ = ⟦1₂⟧
⟦cmpᴺ-bool⟧ αᵣ (⟦suc⟧ kᵣ) {suc _ , _} {suc _ , _} xᵣ = ⟦cmpᴺ-bool⟧ αᵣ kᵣ (⟦predᴺ⟧-sucᴺ↑ (αᵣ ⟦↑⟧ kᵣ) xᵣ)
⟦cmpᴺ-bool⟧ αᵣ (⟦suc⟧ kᵣ) {zero , _} {suc _ , _} xᵣ = ⊥-elim (¬⟦Name⟧-αᵣ-⟦↑1⟧-0-suc (αᵣ ⟦↑⟧ kᵣ) xᵣ)
⟦cmpᴺ-bool⟧ αᵣ (⟦suc⟧ kᵣ) {suc _ , _} {zero , _} xᵣ = ⊥-elim (¬⟦Name⟧-αᵣ-⟦↑1⟧-suc-0 (αᵣ ⟦↑⟧ kᵣ) xᵣ)

⟦easy-cmpᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                  ⟦Name⟧ (αᵣ ⟦↑⟧ kᵣ) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑⟧ kᵣ) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)
             ) NaPa.easy-cmpᴺ NaPa.easy-cmpᴺ
⟦easy-cmpᴺ⟧ _ ⟦zero⟧ xᵣ = ⟦inr⟧ xᵣ
⟦easy-cmpᴺ⟧ _ (⟦suc⟧ _) {zero , _} {zero , _} xᵣ = ⟦inl⟧ here′
⟦easy-cmpᴺ⟧ αᵣ (⟦suc⟧ kᵣ) {suc _ , _} {suc _ , _} xᵣ = ⟦map⟧ _ _ _ _ (⟦sucᴺ↑⟧ (⟦ø⟧ ⟦↑⟧ kᵣ)) (pf-irr (⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ))) (⟦easy-cmpᴺ⟧ αᵣ kᵣ (⟦predᴺ⟧-sucᴺ↑ (αᵣ ⟦↑⟧ kᵣ) xᵣ))
⟦easy-cmpᴺ⟧ αᵣ (⟦suc⟧ kᵣ) {zero , _} {suc _ , _} xᵣ = ⊥-elim (¬⟦Name⟧-αᵣ-⟦↑1⟧-0-suc (αᵣ ⟦↑⟧ kᵣ) xᵣ)
⟦easy-cmpᴺ⟧ αᵣ (⟦suc⟧ kᵣ) {suc _ , _} {zero , _} xᵣ = ⊥-elim (¬⟦Name⟧-αᵣ-⟦↑1⟧-suc-0 (αᵣ ⟦↑⟧ kᵣ) xᵣ)

⟦cmpᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                  ⟦Name⟧ (αᵣ ⟦↑⟧ kᵣ) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑⟧ kᵣ) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)
         ) cmpᴺ cmpᴺ
⟦cmpᴺ⟧ {α₁} {α₂} αᵣ {k₁} {k₂} kᵣ {x₁} {x₂} xᵣ =
   ≡.tr (λ x → (⟦Name⟧ (⟦ø⟧ ⟦↑⟧ kᵣ) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) (cmpᴺ {α₁} k₁ x₁) x)
           (NaPa.easy-cmpᴺ≗cmpᴺ {α₂} k₂ x₂)
           (≡.tr (λ x → (⟦Name⟧ (⟦ø⟧ ⟦↑⟧ kᵣ) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)) x
                    (NaPa.easy-cmpᴺ {α₂} k₂ x₂))
                    (NaPa.easy-cmpᴺ≗cmpᴺ {α₁} k₁ x₁) (⟦easy-cmpᴺ⟧ αᵣ kᵣ {x₁} {x₂} xᵣ))

⟦⊆-dist-+1-◅⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                 (((bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧) ⟦⊆⟧ ((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧))))
                 ⊆-dist-+1-◅ ⊆-dist-+1-◅
⟦⊆-dist-+1-◅⟧ αᵣ {b₁} {b₂} bᵣ = mk (λ {η₁} {η₂} η₃ → helper {η₁} {η₂} η₃) where
  -- open ⟦◅⟧ b₁ b₂

  hper :   ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ) x₁ x₂)
           → ⟦Name⟧ ((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧))
                     (sucᴺ x₁) (sucᴺ x₂)
  hper (⟦◅⟧.here x≡b₁ y≡b₂) = ⟦◅⟧.here (≡.cong suc x≡b₁) (≡.cong suc y≡b₂)
  hper (⟦◅⟧.there x≢b₁ y≢b₂ x∼y) = ⟦◅⟧.there (x≢b₁ ∘ ≡.cong pred) (y≢b₂ ∘ ≡.cong pred) x∼y

  helper : ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ ((bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧) x₁ x₂)
           → ⟦Name⟧ ((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧))
                     (coerceᴺ (⊆-dist-+1-◅ b₁) x₁)
                     (coerceᴺ (⊆-dist-+1-◅ b₂) x₂)
  helper {suc x₁ , pf₁} {suc x₂ , pf₂} xᵣ = hper xᵣ
  helper {zero , ()} {_ , _} _
  helper {_ , _} {zero , ()} _

⟦⊆-dist-◅-+1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                 (((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧)) ⟦⊆⟧ ((bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧)))
                 ⊆-dist-◅-+1 ⊆-dist-◅-+1
⟦⊆-dist-◅-+1⟧ αᵣ {b₁} {b₂} bᵣ = mk helper where
  helper : ∀ {x₁ x₂} (xᵣ : ⟦Name⟧ ((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧)) x₁ x₂)
           → ⟦Name⟧ ((bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧)
                     (coerceᴺ (⊆-dist-◅-+1 b₁) x₁)
                     (coerceᴺ (⊆-dist-◅-+1 b₂) x₂)
  helper {suc x₁ , pf₁} {suc x₂ , pf₂} xᵣ with xᵣ
  ... | ⟦◅⟧.here x≡b₁ y≡b₂ = ⟦◅⟧.here (≡.cong (λ x → x ∸ 1) x≡b₁) (≡.cong (λ x → x ∸ 1) y≡b₂)
  ... | ⟦◅⟧.there x≢b₁ y≢b₂ x∼y = ⟦◅⟧.there (x≢b₁ ∘ ≡.cong suc) (y≢b₂ ∘ ≡.cong suc) x∼y
  helper {zero , ()} {_ , _} _
  helper {_ , _} {zero , ()} _

{-
Binder≡ℕ : Binder ≡ ℕ
Binder≡ℕ = ≡.refl

postulate
  ⟦Binder⟧≢⟦ℕ⟧ : ⟦Binder⟧ ≢ ⟦ℕ⟧

⟦≡⟧-lem : ∀ {a₁ a₂ aᵣ A₁ A₂} {Aᵣ : ⟦Set⟧ {a₁} {a₂} aᵣ A₁ A₂} {x₁ x₂} {xᵣ : Aᵣ x₁ x₂} {y₁ y₂} {yᵣ : Aᵣ y₁ y₂} {pf₁ pf₂} → ⟦≡⟧ Aᵣ xᵣ yᵣ pf₁ pf₂ → ∀ (P : ∀ {z₁ z₂} → Aᵣ z₁ z₂ → Set) → P xᵣ → P yᵣ
⟦≡⟧-lem = {!!}

¬⟦Binder≡ℕ⟧ : ¬((⟦≡⟧ ⟦Set₀⟧ ⟦Binder⟧ ⟦ℕ⟧) Binder≡ℕ Binder≡ℕ)
¬⟦Binder≡ℕ⟧ = λ pf → ⟦≡⟧-lem pf (λ x → ⊥) {!!}
-}

⟦binderᴺ∘nameᴮ⟧ : (⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧
                   ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                    ⟦≡⟧ ⟦Binder⟧ (⟦binderᴺ⟧ (bᵣ ⟦◅⟧ αᵣ) (⟦nameᴮ⟧ αᵣ bᵣ)) bᵣ) binderᴺ∘nameᴮ binderᴺ∘nameᴮ
⟦binderᴺ∘nameᴮ⟧ αᵣ bᵣ = ⟦refl⟧

⟨_,_⟩⟦◅⟧_ : (b₁ b₂ : Binder) → ∀ {α₁ α₂} (αᵣ : ⟦World⟧ α₁ α₂) → ⟦World⟧ (b₁ ◅ α₁) (b₂ ◅ α₂)
⟨ b₁ , b₂ ⟩⟦◅⟧ αᵣ = _⟦◅⟧_ {b₁} {b₂} _ αᵣ

module Perm (m n : ℕ) (m≢n : m ≢ n) where
  mnᵂ : World
  mnᵂ = m ◅ n ◅ ø
  nmᵂ : World
  nmᵂ = n ◅ m ◅ ø
  perm-m-n : ⟦World⟧ mnᵂ nmᵂ
  perm-m-n = ⟨ m , n ⟩⟦◅⟧ (⟨ n , m ⟩⟦◅⟧ ⟦ø⟧)
  m-n : ∀ {m∈ n∈} → ⟦Name⟧ perm-m-n (m , m∈) (n , n∈)
  m-n = here′
  n-m : ∀ {m∈ n∈} → ⟦Name⟧ perm-m-n (n , n∈) (m , m∈)
  n-m = ⟦◅⟧.there (m≢n ∘ ≡.sym) m≢n {b∈b◅ n ø} {b∈b◅ m ø} here′

¬⟦𝟚⟧-1₂-0₂ : ¬(⟦𝟚⟧ 1₂ 0₂)
¬⟦𝟚⟧-1₂-0₂ ()

binder-irrelevance : ∀ (f : Binder → 𝟚)
                     → (⟦Binder⟧ ⟦→⟧ ⟦𝟚⟧) f f
                     → ∀ {b₁ b₂} → f b₁ ≡ f b₂
binder-irrelevance _ fᵣ = ⟦𝟚⟧-Props.to-propositional (fᵣ _)

contrab : ∀ (f : Binder → 𝟚) {b₁ b₂}
          → f b₁ ≢ f b₂
          → ¬((⟦Binder⟧ ⟦→⟧ ⟦𝟚⟧) f f)
contrab f = contraposition (λ fᵣ → binder-irrelevance f (λ xᵣ → fᵣ xᵣ))

module Single α₁ α₂ x₁ x₂ where
  data ℛ : Name α₁ → Name α₂ → Set where
    refl : ℛ x₁ x₂
  ℛ-pres-≡ : ∀ {x₁ x₂ y₁ y₂} → ℛ x₁ x₂ → ℛ y₁ y₂ → (x₁ ≡ y₁) ⇔ (x₂ ≡ y₂)
  ℛ-pres-≡ refl refl = equivalence (const ≡.refl) (const ≡.refl)
  αᵣ : ⟦World⟧ α₁ α₂
  αᵣ = ℛ , ℛ-pres-≡

poly-name-uniq : ∀ (f : ∀ {α} → Name α → 𝟚)
                          (fᵣ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦𝟚⟧) f f)
                          {α} (x : Name α) → f x ≡ f {ø ↑1} (0 , _)
poly-name-uniq f fᵣ {α} x =
  ⟦𝟚⟧-Props.to-propositional (fᵣ {α} {ø ↑1} αᵣ {x} {0 , _} refl)
  where open Single α (ø ↑1) x (0 , _)

poly-name-irrelevance : ∀ (f : ∀ {α} → Name α → 𝟚)
                          (fᵣ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦𝟚⟧) f f)
                          {α₁ α₂} (x₁ : Name α₁) (x₂ : Name α₂)
                        → f x₁ ≡ f x₂
poly-name-irrelevance f fᵣ x₁ x₂ =
  ≡.trans (poly-name-uniq f fᵣ x₁) (≡.sym (poly-name-uniq f fᵣ x₂))

module Broken where
  _<=ᴺ_ : ∀ {α} → Name α → Name α → 𝟚
  (m , _) <=ᴺ (n , _) = ℕ._<=_ m n

  ¬⟦<=ᴺ⟧ : ¬((∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦𝟚⟧) _<=ᴺ_ _<=ᴺ_)
  ¬⟦<=ᴺ⟧ ⟦<=⟧ = ¬⟦𝟚⟧-1₂-0₂ (⟦<=⟧ perm-0-1 {0 , _} {1 , _} 0-1 {1 , _} {0 , _} 1-0)
     where open Perm 0 1 (λ()) renaming (perm-m-n to perm-0-1; m-n to 0-1; n-m to 1-0)

  ⊆-broken : ∀ α b → α ⊆ (b ◅ α)
  ⊆-broken α b = mk (λ b′ b′∈α → ≡.tr id (≡.sym (◅-sem α b′ b)) (If′ ℕ._==_ b′ b then _ else b′∈α))

  ¬⟦⊆-broken⟧ : ¬((⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ (bᵣ ⟦◅⟧ αᵣ))
                  ⊆-broken ⊆-broken)
  ¬⟦⊆-broken⟧ ⟦⊆-broken⟧ = bot
     where 0↔0 : ⟦Name⟧ (⟨ 0 , 1 ⟩⟦◅⟧ ⟨ 0 , 0 ⟩⟦◅⟧ ⟦ø⟧) (0 , _) (0 , _)
           0↔0 = un⟦⊆⟧ (⟦⊆-broken⟧ (⟨ 0 , 0 ⟩⟦◅⟧ ⟦ø⟧) _) {0 , _} {0 , _} here′

           bot : ⊥
           bot with 0↔0
           bot | ⟦◅⟧.here _ ()
           bot | ⟦◅⟧.there 0≢0 _ _ = 0≢0 ≡.refl
