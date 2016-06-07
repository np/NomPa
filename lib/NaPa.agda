{-# OPTIONS --universe-polymorphism #-}
-- vim: iskeyword=a-z,A-Z,48-57,-,+,',#,/,~,],[,=,_,`,⊆
module NaPa where

import Level as L
-- open import Irrelevance
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≢_; _≗_; module ≗-Reasoning; module ≡-Reasoning)
open import Data.Nat.NP as Nat using (ℕ; zero; suc; s≤s; z≤n; ≤-pred; pred; _<=_; module <=)
                            renaming (_+_ to _+ℕ_ ; _∸_ to _∸ℕ_ ; _==_ to _==ℕ_; ¬≤ to ¬≤ℕ;
                                      _<_ to _<ℕ_ ; _≤_ to _≤ℕ_; _≥_ to _≥ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Logical using (⟦ℕ⟧; ⟦zero⟧; ⟦suc⟧; ⟦ℕ⟧-setoid; ⟦ℕ⟧-equality; ⟦ℕ⟧-cong)
                          renaming (_≟_ to _≟⟦ℕ⟧_)
import Data.Nat.Properties as Nat
open import Function
open import Function.Equality as ⟶≡ using (_⟶_; _⟨$⟩_)
open import Data.Sum.NP as Sum using (_⊎_; inl; inr; [_,_]′) renaming (map to ⊎-map)
open import Data.Bool using (Bool; true; false; if_then_else_; T; not)
open import Data.Two renaming (✓-not-¬ to T'not'¬)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.NP using (_,_)
open import Data.Maybe.NP using (Maybe; nothing; just; maybe; _→?_)
open import Relation.Binary.NP as Bin
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Relation.Binary.On as On
open import NomPa.Worlds
open import NomPa.Worlds.Syntax as WorldSyntax
open import NomPa.Subtyping
open ListBoolWorlds public hiding (_⊆_) renaming (_⊆′_ to _⊆_)
import Category.Monad as Cat
open Cat.RawMonad (Data.Maybe.NP.monad {L.zero})
open Data.Maybe.NP.FunctorLemmas

private
  module ℕs = Setoid ⟦ℕ⟧-setoid
  module ℕe = Equality ⟦ℕ⟧-equality

infixr 4 _,_
record Name α : Set where
  constructor _,_
  field
    name    : ℕ
    -- .poofname∈α : name ∈ α
    name∈α : name ∈ α

open Name public
{-
data Name α : Set where
  _,_ : (x : ℕ) → .(x ∈ α) → Name α
name : ∀ {α} (x : Name α) → ℕ
name (x , _) = x

.name∈α : ∀ {α} (x : Name α) → name x ∈ α
name∈α (_ , pf) = pf
-}

--mkName : ∀ {α} (x : ℕ) → Irr (x ∈ α) → Name α
--mkName x (irr pf) = x , pf
mkName : ∀ {α} (x : ℕ) → x ∈ α → Name α
mkName x pf = x , pf

--name∈α : ∀ {α} (x : Name α) → Irr (name x ∈ α)
--name∈α (_ , pf) = irr pf

infix 4 _≡ᴺ_ _≟ᴺ_ _==ᴺ_

-- prim
_≡ᴺ_ : ∀ {α} (x y : Name α) → Set
_≡ᴺ_ = ⟦ℕ⟧ on name

-- prim
_≟ᴺ_ : ∀ {α} → Decidable (_≡ᴺ_ {α})
x ≟ᴺ y = name x ≟⟦ℕ⟧ name y

-- prim
_==ᴺ_ : ∀ {α} (x y : Name α) → Bool
_==ᴺ_ x y = name x ==ℕ name y

name-injective : ∀ {α} {x y : Name α} → name x ≡ name y → x ≡ y
name-injective {α} {_ , p₁} {a , p₂} eq rewrite eq
--= ≡.refl {_} {_} {a , p₂}
  = ≡.cong (_,_ a) (∈-uniq α p₁ p₂)

Nm : World → Setoid L.zero L.zero
Nm α = On.setoid ⟦ℕ⟧-setoid (name {α})

≡ᴺ-equality : ∀ {α} → Equality (_≡ᴺ_ {α})
≡ᴺ-equality {α}
   = record { isEquivalence = Setoid.isEquivalence (Nm α)
              -- I would prefered not going to PropEq.≡
            ; subst = λ P → ≡.tr P ∘ name-injective ∘ Equality.to-propositional ⟦ℕ⟧-equality }

module NmEq {α} = Equality (≡ᴺ-equality {α})

≡ᴺ⇒≡ : ∀ {α} → _≡ᴺ_ {α} ⇒ _≡_
≡ᴺ⇒≡ = NmEq.to-propositional

≡ᴺ-cong : ∀ {α β} (f : Name α → Name β) → _≡ᴺ_ =[ f ]⇒ _≡ᴺ_
≡ᴺ-cong f = NmEq.reflexive ∘ ≡.cong f ∘ ≡ᴺ⇒≡

≡ᴺ-⟦ℕ⟧-cong : ∀ {α} (f : Name α → ℕ) → _≡ᴺ_ =[ f ]⇒ ⟦ℕ⟧
≡ᴺ-⟦ℕ⟧-cong f = ℕe.reflexive ∘ ≡.cong f ∘ ≡ᴺ⇒≡

≡-⟦ℕ⟧-cong : ∀ {a} {A : Set a} (f : A → ℕ) → _≡_ =[ f ]⇒ ⟦ℕ⟧
≡-⟦ℕ⟧-cong f = ℕe.reflexive ∘ ≡.cong f

≡ᴺ-≡-cong : ∀ {a α} {A : Set a} (f : Name α → A) → _≡ᴺ_ =[ f ]⇒ _≡_
≡ᴺ-≡-cong f = ≡.cong f ∘ ≡ᴺ⇒≡

⟦ℕ⟧-≡ᴺ-cong : ∀ {α} (f : ℕ → Name α) → ⟦ℕ⟧ =[ f ]⇒ _≡ᴺ_
⟦ℕ⟧-≡ᴺ-cong f = NmEq.reflexive ∘ ≡.cong f ∘ ℕe.to-propositional

⟦ℕ⟧-≡-cong : ∀ {a} {A : Set a} (f : ℕ → A) → ⟦ℕ⟧ =[ f ]⇒ _≡_
⟦ℕ⟧-≡-cong f = ≡.cong f ∘ ℕe.to-propositional

module ≡ᴺ-Reasoning {α} = Bin.Setoid-Reasoning (Nm α)

open WorldSymantics listBoolWorlds public
open WorldOps listBoolWorlds public
open WorldOps listBoolWorlds using ()
open NomPa.Subtyping.⊆-Pack ⊆′ᵇ-pack public hiding (_⊆_; _⊈_)
open NomPa.Subtyping.SyntacticOnBools ⊆′ᵇ-pack public hiding (minimalSymantics)

-- Here is a first set of core primitives easy to define

-- prim
zeroᴺ : ∀ {α} → Name (α ↑1)
zeroᴺ = 0 , _

-- prim
¬Nameø : ¬(Name ø)
¬Nameø (_ , ())

-- prim
addᴺ : ∀ {α} k (x : Name α) → Name (α +ᵂ k)
addᴺ {α} k x = k +ℕ name x , proof k where
  proof : ∀ k → k +ℕ name x ∈ α +ᵂ k
  proof zero    = name∈α x
  proof (suc k) = proof k

infixl 6 addᴺ
syntax addᴺ k x = x +ᴺ k

-- prim
subtractᴺ : ∀ {α} k (x : Name (α +ᵂ k)) → Name α
subtractᴺ k x = name x ∸ℕ k , proof (name x) k (name∈α x) where
  proof : ∀ {α} x k → (x ∈ α +ᵂ k) → (x ∸ℕ k ∈ α)
  proof x       zero = id
  proof zero    (suc k) = λ()
  proof (suc x) (suc k) = proof x k

infixl 4 subtractᴺ
syntax subtractᴺ k x = x ∸ᴺ k

-- prim
coerceᴺ : ∀ {α β} → α ⊆ β → Name α → Name β
coerceᴺ α⊆β x = name x , coe α⊆β (name x) (name∈α x)

-- Then we define some convenience functions on top of them.

infix 0 _⟨-because_-⟩
_⟨-because_-⟩ : ∀ {α β} → Name α → α ⊆ β → Name β
_⟨-because_-⟩ n pf = coerceᴺ pf n

addᴺ↑ : ∀ {α} ℓ → Name α → Name (α ↑ ℓ)
addᴺ↑ ℓ x = addᴺ ℓ x  ⟨-because ⊆-+-↑ ℓ -⟩

sucᴺ : ∀ {α} → Name α → Name (α +1)
sucᴺ = addᴺ 1

sucᴺ↑ : ∀ {α} → Name α → Name (α ↑1)
sucᴺ↑ = addᴺ↑ 1

-- Then comes <ᴺ and the necessary intermediate definitions

private
  lem-<ℓ : ∀ {α β x ℓ} → x ≤ℕ ℓ → x ∈ (α ↑ suc ℓ) → x ∈ (β ↑ suc ℓ)
  lem-<ℓ z≤n       = _
  lem-<ℓ (s≤s m≤n) = lem-<ℓ m≤n

  lem-≥ℓ : ∀ {α x ℓ} → x ≥ℕ ℓ → x ∈ α ↑ ℓ → x ∈ α +ᵂ ℓ
  lem-≥ℓ z≤n        = id
  lem-≥ℓ (s≤s m≤n)  = lem-≥ℓ m≤n

  lem-<ℓ? : ∀ {α β n} ℓ → n ∈ β ↑ ℓ → n ∈ (if suc n <= ℓ then α ↑ ℓ else β +ᵂ ℓ)
  lem-<ℓ? {n = n} ℓ with suc n <= ℓ | <=.sound (suc n) ℓ | <=.complete {suc n} {ℓ}
  ... | true  | n<ℓ | _    = lem-<ℓ (n<ℓ _)
  ... | false | _   | ¬n<ℓ = lem-≥ℓ (¬≤ℕ ¬n<ℓ)

-- prim
cmpᴺ-bool : ∀ {α} ℓ → Name (α ↑ ℓ) → Bool
cmpᴺ-bool ℓ x = suc (name x) <= ℓ

syntax cmpᴺ-bool k x = x <ᴺ-bool k

-- prim
cmpᴺ-name : ∀ {α} ℓ (x : Name (α ↑ ℓ)) → Name (if cmpᴺ-bool ℓ x then ø ↑ ℓ else α +ᵂ ℓ)
cmpᴺ-name ℓ x = name x , lem-<ℓ? ℓ (name∈α x)

syntax cmpᴺ-name ℓ x = x <ᴺ-name ℓ

-- prim
cmpᴺ-name∈α : ∀ {α} ℓ (x : Name (α ↑ ℓ)) → name x ∈ (if cmpᴺ-bool ℓ x then ø ↑ ℓ else α +ᵂ ℓ)
cmpᴺ-name∈α ℓ x = lem-<ℓ? ℓ (name∈α x)

syntax cmpᴺ-name∈α ℓ x = x <ᴺ-name∈α ℓ

-- prim
cmpᴺ : ∀ {α} ℓ → Name (α ↑ ℓ) → Name (ø ↑ ℓ) ⊎ Name (α +ᵂ ℓ)
cmpᴺ ℓ x with cmpᴺ-bool ℓ x | cmpᴺ-name∈α ℓ x
... | true  | pf = inl (name x , pf)
... | false | pf = inr (name x , pf)

infix 4 cmpᴺ
syntax cmpᴺ k x = x <ᴺ k

cmpᴺ-ind : ∀ {a α} ℓ (x : Name (α ↑ ℓ))
            (P : (Name (ø ↑ ℓ) ⊎ Name (α +ᵂ ℓ)) → Set a)
            (Pinl : T (cmpᴺ-bool ℓ x) → ∀ pf → P (inl (name x , pf)))
            (Pinr : T (not (cmpᴺ-bool ℓ x)) → ∀ pf → P (inr (name x , pf)))
          → P (cmpᴺ ℓ x)
cmpᴺ-ind ℓ x P p₁ p₂
 with cmpᴺ-bool ℓ x | cmpᴺ-name∈α ℓ x
... | true         | pf = p₁ _ pf
... | false        | pf = p₂ _ pf

easy-cmpᴺ : ∀ {α} ℓ → Name (α ↑ ℓ) → Name (ø ↑ ℓ) ⊎ Name (α +ᵂ ℓ)
easy-cmpᴺ zero x               = inr x
easy-cmpᴺ (suc _) (zero , _)   = inl (zero , _)
easy-cmpᴺ (suc ℓ) (suc x , pf) = ⊎-map sucᴺ↑ sucᴺ (easy-cmpᴺ ℓ (x , pf))

syntax easy-cmpᴺ ℓ x = x <ᴺ-easy ℓ

easy-cmpᴺ≗cmpᴺ : ∀ {α} ℓ → easy-cmpᴺ {α} ℓ ≗ cmpᴺ ℓ
easy-cmpᴺ≗cmpᴺ zero x = ≡.cong inr (name-injective ≡.refl)
easy-cmpᴺ≗cmpᴺ (suc n) (zero , _) = ≡.refl
easy-cmpᴺ≗cmpᴺ {α} (suc n) (suc x , pf) rewrite easy-cmpᴺ≗cmpᴺ n (x , pf) = helper n x pf
  where
    helper : ∀ ℓ x pf → ⊎-map sucᴺ↑ sucᴺ (cmpᴺ {α} ℓ (x , pf)) ≡ cmpᴺ (suc ℓ) (suc x , pf)
    helper ℓ x pf = cmpᴺ-ind ℓ (x , pf) (λ r → ⊎-map sucᴺ↑ sucᴺ r ≡ cmpᴺ (suc ℓ) (suc x , pf))
                      (λ h pf' → cmpᴺ-ind (suc ℓ) (suc x , pf) (λ r → inl (suc x , pf') ≡ r)
                                         (λ _ _ → ≡.cong inl (name-injective ≡.refl))
                                         (λ h' → ⊥-elim (T'not'¬ h' h)))
                      (λ h pf' → cmpᴺ-ind (suc ℓ) (suc x , pf) (λ r → inr (suc x , pf') ≡ r)
                                         (λ h' → ⊥-elim (T'not'¬ h h'))
                                         (λ _ _ → ≡.cong inr (name-injective ≡.refl)))

-- prim (could be defined with (cmpᴺ 1)
protect↑1 : ∀ {α β} → (Name α → Name β) → Name (α ↑1) → Name (β ↑1)
protect↑1 f x with name x | {-irr-} (name∈α x)
... | zero  | _  = zero , _
... | suc m | pf = sucᴺ↑ (f (m , {-cert-} pf))

-- mkName; _,_; name; name∈α are forbidden from now on (except in proofs).

zeroᴺ↑1+ : ∀ {α} ℓ → Name (α ↑ (1 +ℕ ℓ))
zeroᴺ↑1+ _ = zeroᴺ

infix 10 _ᴺ
_ᴺ : ∀ {α} ℓ → Name (α ↑ suc ℓ)
_ᴺ {α} ℓ = zeroᴺ +ᴺ ℓ ⟨-because (α ↑1 +ᵂ ℓ) ⊆⟨ ⊆-+-↑ ℓ ⟩
                                α ↑1 ↑  ℓ   ⊆⟨ ⊆-exch-↑-↑ ⊆-refl 1 ℓ ⟩
                                α ↑ suc ℓ ∎ -⟩
   where open ⊆-Reasoning

-- Handy name eliminator
subtractWithᴺ : ∀ {a α} {A : Set a} ℓ → A → (Name α → A) → Name (α ↑ ℓ) → A
subtractWithᴺ ℓ v f x = [ const v , f ∘′ subtractᴺ ℓ ]′ (x <ᴺ ℓ)

subtractᴺ? : ∀ {α} ℓ → Name (α ↑ ℓ) →? Name α
subtractᴺ? ℓ = subtractWithᴺ ℓ nothing just

infixl 4 subtractᴺ?
syntax subtractᴺ? k x = x ∸ᴺ? k

private
 module CoeExamples where
  Nameα+→Nameα↑ : ∀ {α} k → Name (α +ᵂ k) → Name (α ↑ k)
  Nameα+→Nameα↑ k = coerceᴺ (⊆-ctx-+↑ ⊆-refl k)
 module Unused where
  open import Data.List using ([]; _∷_; replicate; _++_)
  n∈trueⁿ⁺¹ : ∀ {α} n → n ∈ replicate (suc n) true ++ α
  n∈trueⁿ⁺¹ zero    = _
  n∈trueⁿ⁺¹ (suc n) = n∈trueⁿ⁺¹ n

predᴺ : ∀ {α} → Name (α +1) → Name α
predᴺ = subtractᴺ 1

predᴺ? : ∀ {α} → Name (α ↑1) →? Name α
predᴺ? = subtractᴺ? 1

Name→-to-Nm⟶ : ∀ {b₁ b₂ α} {B : Setoid b₁ b₂} →
                 (Name α → Setoid.Carrier B) → Nm α ⟶ B
Name→-to-Nm⟶ {α = α} {B} f = record { _⟨$⟩_ = f; cong = cong′ }
  where
  open Setoid B renaming (_≈_ to _≈B_)

  cong≡ : ∀ {x y} → x ≡ y → f x ≈B f y
  cong≡ ≡.refl = Setoid.refl B

  cong′ : ∀ {x y} → x ≡ᴺ y → f x ≈B f y
  cong′ = cong≡ ∘ Equality.to-propositional ≡ᴺ-equality
  -- cong′ = Setoid.reflexive ∘ Equality.to-propositional ≡ᴺ-equality

¬Name : ∀ {α} → α ⊆ ø → ¬(Name α)
¬Name α⊆ø = ¬Nameø ∘ coerceᴺ α⊆ø

Name-elim : ∀ {a} {A : Set a} {α} (α⊆ø : α ⊆ ø) (x : Name α) → A
Name-elim x y with ¬Name x y
... | ()

Nameø-elim : ∀ {a} {A : Set a} → Name ø → A
Nameø-elim = Name-elim ⊆-refl

¬Nameø+ : ∀ k → ¬(Name (ø +ᵂ k))
¬Nameø+ = ¬Name ∘ ⊆-ø+

Nameø+-elim : ∀ {a} {A : Set a} k → Name (ø +ᵂ k) → A
Nameø+-elim = Name-elim ∘ ⊆-ø+

Nameø↑→Nameα↑ : ∀ {ℓ} → Name (ø ↑ ℓ) → ∀ {α} → Name (α ↑ ℓ)
Nameø↑→Nameα↑ {ℓ} x = x ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩

is0? : ∀ {α} → Name (α ↑1) → Bool
is0? = cmpᴺ-bool 1
-- is0? = [ const true , const false ]′ (x <ᴺ 1)

shiftℕ : ∀ (ℓ k n : ℕ) → ℕ
shiftℕ ℓ k n = if suc n <= ℓ then n else n +ℕ k

shiftᴺ : ∀ {α β} ℓ k → α +ᵂ k ⊆ β → Name (α ↑ ℓ) → Name (β ↑ ℓ)
shiftᴺ ℓ k pf n
  with n <ᴺ ℓ
...  | inl n′ = n′       ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
...  | inr n′ = n′ +ᴺ k  ⟨-because ⊆-trans (⊆-exch-+-+ ⊆-refl ℓ k) (⊆-ctx-+↑ pf ℓ) -⟩

module Singletons where

  SWorld : ℕ → World
  SWorld n = ø ↑1 +ᵂ n

  Nameˢ : ℕ → Set
  Nameˢ = Name ∘ SWorld

  _ˢ : ∀ n → Nameˢ n
  _ˢ n = zeroᴺ +ᴺ n

  addˢ : ∀ {n} k → Nameˢ n → Nameˢ (k +ℕ n)
  addˢ {n} k x = addᴺ k x  ⟨-because ⊆-assoc-+ ⊆-refl n k -⟩

  subtractˢ : ∀ {n} k → Nameˢ (k +ℕ n) → Nameˢ n
  subtractˢ {n} k x = subtractᴺ k (x ⟨-because ⊆-assoc-+′ ⊆-refl n k -⟩)

{-
shiftᴺ-1-1+-
  shiftᴺ 1 (suc k) pf n ≡ shiftᴺ 1 k ? (shiftᴺ 1 1 ? n)
-}

-- Properties

coerceᴺ-names : ∀ {α β} (α⊆β : α ⊆ β) → name ∘ coerceᴺ α⊆β ≗ name
coerceᴺ-names _ _ = ≡.refl

{-
<ᴺ-coerce : ∀ {α} ℓ (x : Name (α ↑ ℓ)) → [ coerceᴺ (⊆-cong-↑ ⊆-ø ℓ) , coerceᴺ (⊆-ctx-+↑ ⊆-refl ℓ) ]′ (x <ᴺ ℓ) ≡ x
<ᴺ-coerce ℓ x with x <ᴺ-bool ℓ | x <ᴺ-name∈α ℓ
... | true  | _ = name-injective ≡.refl
... | false | _ = name-injective ≡.refl
-}

<ᴺ-names : ∀ {α ℓ} {x : Name (α ↑ ℓ)} → [ name , name ]′ (x <ᴺ ℓ) ≡ name x
<ᴺ-names {α} {ℓ} {x} with x <ᴺ-bool ℓ | x <ᴺ-name∈α ℓ
... | true  | _ = ≡.refl
... | false | _ = ≡.refl

Dec-≡ᴺ→≡ : ∀ {α} → Decidable (_≡ᴺ_ {α}) → Decidable _≡_
Dec-≡ᴺ→≡ _≟_ x y with x ≟ y
... | yes x≡y = yes (≡ᴺ⇒≡ x≡y)
... | no  x≢y = no  (x≢y ∘′ ℕs.reflexive ∘′ ≡.cong name)

shiftᴺ-ℓ-0≡coerceᴺ : ∀ {α β} ℓ (pf : α ⊆ β) n → name (shiftᴺ ℓ 0 pf n) ≡ name n
shiftᴺ-ℓ-0≡coerceᴺ ℓ pf x with x <ᴺ-bool ℓ | x <ᴺ-name∈α ℓ
... | true  | _ = ≡.refl
... | false | _ = ≡.refl

pred-shiftℕ-comm : ∀ k x → pred (shiftℕ 1 k (suc x)) ≡ x +ℕ k
pred-shiftℕ-comm k x = ≡.refl

.shift11-predᴺ?-comm :
  ∀ {α β} (pf : α +1 ⊆ β) (x : Name (α ↑1)) →
  predᴺ? (shiftᴺ 1 1 pf x) ≡ (coerceᴺ pf ∘ sucᴺ <$> predᴺ? x)
shift11-predᴺ?-comm {α} pf x
   = <$>-injective₁ name-injective (≡.trans (helper (name x) {name∈α x} (suc (name x) ≤?ℕ 1)) (<$>-assoc (predᴺ? x)))
  where
    -- getting the name unpacked (and the Dec), works around an Agda bug in 2.2.8.
    .helper : ∀ n {pn : n ∈ α ↑1} → Dec (n <ℕ 1) → let x = n , pn in
             (name <$> (predᴺ? (shiftᴺ 1 1 pf x))) ≡ (name ∘ (coerceᴺ pf ∘ sucᴺ) <$> predᴺ? x)
    helper zero    (no ¬p)         = ⊥-elim (¬p (s≤s z≤n))
    helper .0      (yes (s≤s z≤n)) = ≡.refl
    helper (suc _) (no _)          = ≡.refl

1+ : ∀ {α} → Name α → Name (α +1)
1+ x = x +ᴺ 1

module Name↑⇔Fin where
  open import Data.Fin as Fin

  ⇒ : ∀ n → Name (ø ↑ n) → Fin n
  ⇒ zero    = Nameø-elim
  ⇒ (suc n) = maybe (suc ∘′ ⇒ n) zero ∘′ predᴺ?

  ⇐ : ∀ {α n} → Fin n → Name (α ↑ n)
  ⇐ (zero {n})  = zeroᴺ↑1+ n
  ⇐ (suc i)     = sucᴺ↑ (⇐ i)

{-
  open Singletons
  open ⊆-Reasoning
  f : ∀ {α n} → Fin n → Name (α ↑ n)
  f {α} {zero} ()
  f {α} {suc n} x = coerceᴺ c (sName x′) where
    x′ = Fin.toℕ x
    c′ = ø ↑1 +[ n ∸ℕ x′ ]   ⊆⟨ {!!} ⟩
         (ø +[ n ∸ℕ x′ ]) ↑1 ⊆⟨ ⊆-cong-↑1 (α+⊆ø→α⊆ø _ ⊆-refl) ⟩
         ø ↑1                 ⊆⟨ ⊆-cong-↑1 ⊆-ø ⟩
         α ↑1 ∎
    c : SWorld x′ ⊆ α ↑ (suc n)
    c = SWorld x′                ⊆⟨ refl ⟩
        ø ↑1 +[ x′ ]             ⊆⟨ {!!} ⟩
        ø ↑1 +[ n ∸ℕ x′ ] +[ n ] ⊆⟨ ⊆-ctx-+↑ c′ n ⟩
        α ↑1 ↑ n                 ⊆⟨ ⊆-exch-↑-↑ ⊆-refl 1 n ⟩
        α ↑ suc n ∎
-}

  -- ⇔ : ∀ n → Name (ø ↑ n) ⇔ Fin n
  -- ⇔ n = ?

{-
module Bug where
  record Fin′ (n : ℕ) : Set where
    constructor mkFin
    field
      x    : ℕ
      .x<n : x <ℕ n
  raise : ∀ {n m} → Fin′ n → n ≤ℕ m → Fin′ m
  raise (mkFin x x<n) n≤m = mkFin x (ℕ≤.trans x<n n≤m)
  raise-assoc : ∀ {n m o} p (q : m ≤ℕ o) (x : Fin′ n) → (raise (raise x p) q) ≡ (raise x (ℕ≤.trans p q))
  raise-assoc p q (mkFin x x<n) with raise-assoc p q (mkFin x x<n)
  ... | refl = ?
-}

{-
module Fin′ where
  record Fin′ (n : ℕ) : Set where
    constructor mkFin
    field
      x    : ℕ
      .x<n : x <ℕ n
  zeroF : ∀ {n} → Fin′ (suc n)
  zeroF = mkFin 0 (s≤s z≤n)
  sucF : ∀ {n} → Fin′ n → Fin′ (suc n)
  sucF (mkFin x x<n) = mkFin (suc x) (s≤s x<n)

  raise : ∀ {n} (x : Fin′ n) k → Fin′ (n +ℕ k)
  raise (mkFin x x<n) k = mkFin x (m≤n→m≤n+k x<n)
    where m≤n→m≤n+k : ∀ {m n k} → m ≤ℕ n → m ≤ℕ n +ℕ k
          m≤n→m≤n+k z≤n        = z≤n
          m≤n→m≤n+k (s≤s m≤n)  = s≤s (m≤n→m≤n+k m≤n)
-}

{-
(x : α +ᵂ n) → x ≥ n

(x : α +ᵂ suc n) → x ≢ zeroᴺ
-}

module ℕ⇒Name`α` where
  open WorldSyntax
  open WorldSyntax.El listBoolWorlds
  ⇒ : ∀ `α` x → x ∈ El `α` → Name (El `α`)
  ⇒ (`α` `↑1`) zero    _     = zero , _
  ⇒ (`α` `↑1`) (suc i) pf    = sucᴺ↑ (⇒ `α` i pf)
  ⇒ (`α` `+1`) zero    ()
  ⇒ (`α` `+1`) (suc i) pf    = sucᴺ (⇒ `α` i pf)
  ⇒ `ø`        _       ()

module Name`α`⇔Fin where
  open import Data.Fin as F renaming (_+_ to _+F_)
  open WorldSyntax
  open WorldSyntax.El listBoolWorlds
  open WorldSyntax.Properties listBoolWorlds
  mutual

    ⇒+1 : ∀ `α` → Name (El `α` +1) → Fin (suc (bnd `α`))
    ⇒+1 `α` = F.raise 1 ∘ ⇒ `α` ∘ predᴺ

    ⇒ : ∀ `α` → Name (El `α`) → Fin (bnd `α`)
    ⇒ (`α` `↑1`)  = [ inject+ _ ∘ Name↑⇔Fin.⇒ 1 , ⇒+1 `α` ]′ ∘ cmpᴺ 1
    ⇒ (`α` `+1`)  = ⇒+1 `α`
    ⇒ `ø`         = Nameø-elim

  ⇐₁ : ∀ {n} `α` → (x : Fin n) → toℕ x ∈ El `α` → Name (El `α`)
  ⇐₁ `α` = ℕ⇒Name`α`.⇒ `α` ∘ toℕ

  x∈ø↑x : ∀ {n} (x : Fin n) → toℕ x ∈ (ø ↑ n)
  x∈ø↑x zero    = _
  x∈ø↑x (suc n) = x∈ø↑x n

  ⇐₂ : ∀ {n} → (x : Fin n) → Name (ø ↑ n)
  ⇐₂ {n} x with x∈ø↑x x
  ...         | y       rewrite comm-El-↑ `ø` n = ⇐₁ (`ø` `↑` n) x y

  {- I would have prefered a local `where` here
  ⇐₂ : ∀ {n} → (x : Fin n) → Name (ø ↑ n)
  ⇐₂ {n} x where y = x∈ø↑x x rewrite comm-El-↑ `ø` n = ⇐₁ (`ø` `↑` n) x y
  -}

module WellFormedWorld where
  data WF : World → Set where
    `ø : WF ø
    _`+_ : ∀ {α} (`α : WF α) k → WF (α +ᵂ k)
    _`↑_ : ∀ {α} (`α : WF α) k → WF (α ↑ k)

_+↑ᴺ_ : ∀ {α} → Name α → ∀ ℓ → Name (α ↑ ℓ)
_+↑ᴺ_ x ℓ = coerceᴺ (⊆-ctx-+↑ ⊆-refl ℓ) (x +ᴺ ℓ)

subtractᴺ↑ : ∀ {α} ℓ → Name (α ↑ ℓ) → Name (ø ↑ ℓ) ⊎ Name α
subtractᴺ↑ ℓ x with x <ᴺ ℓ
... | inl x′ = inl x′
... | inr x′ = inr (x′ ∸ᴺ ℓ)

infixl 4 subtractᴺ↑
syntax subtractᴺ↑ ℓ x = x -↑ᴺ ℓ

data WithLim (R : (α β : World) → Set) : (α β : World) → Set where
  mkWithLim : ∀ {α₀ β₀} ℓ (Rα₀β₀ : R α₀ β₀) → WithLim R (α₀ ↑ ℓ) (β₀ ↑ ℓ)

withLim : ∀ {R α β} → R α β → WithLim R α β
withLim = mkWithLim 0

-- functions known to be ``bad'' and that we don't want to export
private
 module Bad where
  Name2ℕ : ∀ {α} → Name α → ℕ
  Name2ℕ = name
  isZero? : ∀ {α} → Name α → Bool
  isZero? (zero  , _) = true
  isZero? (suc _ , _) = false
