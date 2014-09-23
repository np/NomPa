open import Data.List

module NomPa.Examples.Raw where

module DataType (Atom : Set) where
  infixl 4 _·_
  data Tmᴿ : Set where
    V : (x : Atom) → Tmᴿ
    ƛ : (b : Atom) (t : Tmᴿ) → Tmᴿ
    _·_ : (t u : Tmᴿ) → Tmᴿ
    -- Let : (b : Atom) (t u : Tmᴿ) → Tmᴿ

  appⁿ : Tmᴿ → List Tmᴿ → Tmᴿ
  appⁿ = foldl _·_

open import Function.NP
open import Data.Bool.NP hiding (_≟_)
open import Relation.Nullary

Rel₀ : Set → Set₁
Rel₀ A = A → A → Set

{-
module RelTm (Atom : Set) (_≡ᴬ_ : Rel₀ Atom) where
  open DataType Atom

  _≢ᴬ_ : Rel₀ Atom
  x ≢ᴬ y = ¬(x ≡ᴬ y)

  data Extend (b₁ b₂ : Atom) (Δ : Rel₀ Atom) (x₁ x₂ : Atom) : Set where
    here : b₁ ≡ᴬ x₁ → b₂ ≡ᴬ x₂ → Extend b₁ b₂ Δ x₁ x₂
    there : b₁ ≢ᴬ x₁ → b₂ ≢ᴬ x₂ → Δ x₁ x₂ → Extend b₁ b₂ Δ x₁ x₂

  data _⊢_≈_ (Δ : Rel₀ Atom) : Rel₀ Tmᴿ where
    V : ∀ {x x′} → Δ x x′ → _⊢_≈_ Δ (V x) (V x′)
    ƛ : ∀ {b t b′ t′} → _⊢_≈_ (Extend b b′ Δ) t t′ → _⊢_≈_ Δ (ƛ b t) (ƛ b′ t′)
    _·_ : ∀ {t u t′ u′} → _⊢_≈_ Δ t t′ → _⊢_≈_ Δ u u′ → _⊢_≈_ Δ (t · u) (t′ · u′)
  -- Let

  _≡™_ : Rel₀ Tmᴿ
  _≡™_ = _⊢_≈_ _≡ᴬ_
-}

module ΔTm (Atom : Set) (_≡ᴬ_ : Rel₀ Atom) where
  open DataType Atom

  _≢ᴬ_ : Rel₀ Atom
  x ≢ᴬ y = ¬(x ≡ᴬ y)

  data E : Set where
    ε : E
    _,⟨_,_⟩ : E → Atom → Atom → E

  data RelΔ x₁ x₂ : (Δ : E) → Set where
    ε : (≡ₓ : x₁ ≡ᴬ x₂) → RelΔ x₁ x₂ ε
    here : ∀ {b₁ b₂ Δ} (≡₁ : b₁ ≡ᴬ x₁) (≡₂ : b₂ ≡ᴬ x₂) → RelΔ x₁ x₂ (Δ ,⟨ b₁ , b₂ ⟩)
    there : ∀ {b₁ b₂ Δ} (≢₁ : b₁ ≢ᴬ x₁) (≢₂ : b₂ ≢ᴬ x₂) (Δᵣ : RelΔ x₁ x₂ Δ) → RelΔ x₁ x₂ (Δ ,⟨ b₁ , b₂ ⟩)

  infix 0 _⊢_≈ᴬ_ _⊢_≈_

  _⊢_≈ᴬ_ : E → Rel₀ Atom
  Δ ⊢ x₁ ≈ᴬ x₂ = RelΔ x₁ x₂ Δ

  data _⊢_≈_ Δ : Rel₀ Tmᴿ where
    V : ∀ {x₁ x₂} (xᵣ : Δ ⊢ x₁ ≈ᴬ x₂) → _⊢_≈_ Δ (V x₁) (V x₂)
    ƛ : ∀ {b₁ b₂ t₁ t₂} (tᵣ : _⊢_≈_ (Δ ,⟨ b₁ , b₂ ⟩) t₁ t₂) → _⊢_≈_ Δ (ƛ b₁ t₁) (ƛ b₂ t₂)
    _·_ : ∀ {t₁ u₁ t₂ u₂} (tᵣ : _⊢_≈_ Δ t₁ t₂) (uᵣ : _⊢_≈_ Δ u₁ u₂) → _⊢_≈_ Δ (t₁ · u₁) (t₂ · u₂)
  -- Let

  _≡™_ : Rel₀ Tmᴿ
  _≡™_ = _⊢_≈_ ε

module CmpEqnTm (Atom : Set) (_==ᴬ_ : Cmp Atom) where
  open DataType Atom
  extend : (b₁ b₂ : Atom) → Cmp Atom → Cmp Atom
  extend b₁ b₂ Δ x₁ x₂ with b₁ ==ᴬ x₁ | b₂ ==ᴬ x₂
  ...                     | true     | true      = true
  ...                     | false    | false     = Δ x₁ x₂
  ...                     | _        | _         = false
  cmp™ : Cmp Atom → Cmp Tmᴿ
  cmp™ Δ (V x)       (V x′)         = Δ x x′
  cmp™ Δ (ƛ b t)     (ƛ b′ t′)      = cmp™ (extend b b′ Δ) t t′
  cmp™ Δ (t · u)     (t′ · u′)      = cmp™ Δ t t′ ∧ cmp™ Δ u u′
  -- cmp™ Δ (Let b t u) (Let b′ t′ u′) = {!!}
  cmp™ Δ _ _ = false

  _==™_ : Cmp Tmᴿ
  _==™_ = cmp™ _==ᴬ_

open import Relation.Binary.PropositionalEquality

module MapTm {A B : Set} (f : A → B) where
  open DataType
  map™ : Tmᴿ A → Tmᴿ B
  map™ (V x) = V (f x)
  map™ (ƛ b t) = ƛ (f b) (map™ t)
  map™ (t · u) = map™ t · map™ u

module MapProps where
  open DataType
  open MapTm

  map∘ : ∀ {A B C} (f : B → C) (g : A → B) → map™ f ∘ map™ g ≗ map™ (f ∘ g)
  map∘ f g (V x) = refl
  map∘ f g (ƛ b t) rewrite map∘ f g t = refl
  map∘ f g (t · u) rewrite map∘ f g t | map∘ f g u = refl

module Swap (Atom : Set) (_==ᴬ_ : Cmp Atom) where
  open DataType Atom

  sw : Atom → Atom → Atom → Atom
  sw x y z with x ==ᴬ z
  ... | true = y
  ... | false with y ==ᴬ z
  ...            | true = x
  ...            | false = z

  swap_and_inᴬ_ : Atom → Atom → Atom → Atom
  swap_and_inᴬ_ = sw

  swap_and_in™_ : Atom → Atom → Tmᴿ → Tmᴿ
  swap x and y in™ t = MapTm.map™ (λ z → swap x and y inᴬ z) t

-- perm™ : Tmᴿ A → Tmᴿ A
-- perm™ t = map™ (perm

{-
module CmpConvTm (Atom : Set) (_==ᴬ_ : Cmp Atom) where
  open DataType Atom
  open Swap Atom _==ᴬ_

  cmp™ : Tmᴿ → Tmᴿ → Bool
  cmp™ (V x₁)    (V x₂) = x₁ ==ᴬ x₂
  cmp™ (ƛ b₁ t₁) (ƛ b₂ t₂) = cmp™ t₁ (swap b₁ and b₂ in™ t₂)
  cmp™ (t₁ · u₁) (t₂ · u₂) = cmp™ t₁ t₂ ∧ cmp™ u₁ u₂
  cmp™ _ _ = false
-}

{-
Recall that α-conversion, =α , is usually defined as the least congruence on the set of
λ-terms that identifies λa.M with λa .[a /a]M .
-}


module ∼Tm (Atom : Set) (_==ᴬ_ : Cmp Atom) where
  open DataType Atom
  open Swap Atom _==ᴬ_

  record _# (b : Atom) : Set where

  infix 0 _∼™_
  data _∼™_ : Rel₀ Tmᴿ where
    V : ∀ {x₁ x₂} (xᵣ : x₁ ≡ x₂) → V x₁ ∼™ V x₂
    ƛ : ∀ {b₁ b₂ b₃ t₁ t₂} (b₃# : b₃ #) (tᵣ : swap b₃ and b₁ in™ t₁ ∼™ swap b₃ and b₂ in™ t₂) → ƛ b₁ t₁ ∼™ ƛ b₂ t₂
    _·_ : ∀ {t u t′ u′} (tᵣ : t ∼™ t′) (uᵣ : u ∼™ u′) → t · u ∼™ t′ · u′

{-

THIS PART IS UNFINISHED BUT VERY IMPORTANT

open import Data.Unit using (⊤)
open import Data.Empty
open import Data.Nat.NP renaming (_==_ to _==ℕ_)

module CmpEqn⇔CmpConv where
  Atom : Set
  Atom = ℕ
  _==ᴬ_ : Cmp Atom
  _==ᴬ_ = _==ℕ_
  open DataType  Atom
  -- open CmpEqnTm  Atom _==ᴬ_ renaming (cmp™ to ce; _==™_ to ee)
  -- open CmpConvTm Atom _==ᴬ_ renaming (cmp™ to cc)
  -- open RelTm     Atom _≡_ -- using (V; ƛ; _·_; _⊢_≈_)
  open ΔTm     Atom _≡_ -- using (V; ƛ; _·_; _⊢_≈_)
  open ∼Tm      Atom _==ᴬ_ renaming (_∼™_ to _∼_) -- using (V; ƛ; _·_; _∼™_)
  open Swap      Atom _==ᴬ_
  open MapTm

  Π : Set
  Π = Atom → Atom

  open MapProps

{-
  postulate
    z : Atom
    z# : ∀ x → z ≢ x -- ah ah ah

  π₁ : (Δ : E) → Π
  π₁ ε = id
  π₁ (Δ ,⟨ x , y ⟩) = π₁ Δ ∘ sw x z

  π₂ : (Δ : E) → Π
  π₂ ε = id
  π₂ (Δ ,⟨ x , y ⟩) = π₂ Δ ∘ sw y z
-}

{-
  R : E → Rel₀ Atom
  R ε               = _≡_
  R (Δ ,⟨ y₁ , y₂ ⟩) = Extend y₁ y₂ (R Δ)
-}

{-
  _⊢_≈_ : E → Rel₀ Tmᴿ
  Δ ⊢ t₁ ≈ t₂ = _⊢_≈_ (R Δ) t₁ t₂

  _⊢_≈ᴬ_ : E → Rel₀ Atom
  Δ ⊢ x₁ ≈ᴬ x₂ = R Δ x₁ x₂
-}

  infixr 2 _●_
  _●_ : Π → Tmᴿ → Tmᴿ
  π ● t = map™ π t

{-
  postulate
    swz : ∀ x → sw x z x ≡ z
    π₁z : ∀ Δ → π₁ Δ z ≡ z
    π₂z : ∀ Δ → π₂ Δ z ≡ z
    swz≢ : ∀ {b x} → b ≢ x → sw b z x ≡ x

  ⇒ᴬ : ∀ {x₁ x₂ Δ} → Δ ⊢ x₁ ≈ᴬ x₂ → π₁ Δ x₁ ≡ π₂ Δ x₂
  ⇒ᴬ (ε ≡ₓ) = ≡ₓ
  ⇒ᴬ (here {x₁} {x₂} {Δ} refl refl) rewrite swz x₁ | swz x₂ | π₁z Δ | π₂z Δ = refl
  ⇒ᴬ (there ≢₁ ≢₂ Δᵣ) rewrite swz≢ ≢₁ | swz≢ ≢₂ = ⇒ᴬ Δᵣ
-}

{-
  foo : ∀ {b₁ b₂ Δ t₁ t₂} → π₁ Δ ∘ sw b₁ z ● t₁ ∼ π₂ Δ ∘ sw b₂ z ● t₂
                          → π₁ Δ ● sw b₁ z ● t₁ ∼ π₂ Δ ● sw b₂ z ● t₂
                         
  foo = {!!}

  comm : ∀ {a b c d} → sw a b ∘ sw c d ≗ sw (sw a b c) (sw a b d) ∘ sw a b
  comm = {!!}

  lift™ : ∀ {π₁ π₂} → π₁ ≗ π₂ → ∀ t → (π₁ ● t) ≡ (π₂ ● t)
  lift™ = {!!}

  lift∼ : ∀ {π₁ π₂ π₁′ π₂′ t₁ t₂} → π₁ ≗ π₁′ → π₂ ≗ π₂′ → π₁ ● t₁ ∼ π₂ ● t₂ → π₁′ ● t₁ ∼ π₂′ ● t₂
  lift∼ = {!!}

  comm∼ : ∀ {π₁ π₂ a₁ b₁ a₂ b₂ t₁ t₂} → π₁ ● sw a₁ b₁ ● t₁ ∼ π₂ ● sw a₂ b₂ ● t₂
           → sw (π₁ a₁) (π₁ b₁) ● π₁ ● t₁ ∼ sw (π₂ a₂) (π₂ b₂) ● π₂ ● t₂
  comm∼ = {!!}

  ⇒ : ∀ {Δ t₁ t₂} → Δ ⊢ t₁ ≈ t₂ → π₁ Δ ● t₁ ∼ π₂ Δ ● t₂
  ⇒ (V xᵣ) = V (⇒ᴬ xᵣ)
  ⇒ {Δ} (ƛ {b₁} {b₂} {t₁} {t₂} tᵣ) {-rewrite map∘ (π₁ Δ)-} = tz where
           tx : π₁ Δ ∘ sw b₁ z ● t₁ ∼ π₂ Δ ∘ sw b₂ z ● t₂
           tx = ⇒ tᵣ -- foo {b₁} {b₂} {{!!}} (⇒ {Δ ,⟨ b₁ , b₂ ⟩} tᵣ)
           ty : π₁ Δ ● sw b₁ z ● t₁ ∼ π₂ Δ ● sw b₂ z ● t₂
           ty = foo {b₁} {b₂} {Δ} tx
           ty' : sw b₁ z ● π₁ Δ ● t₁ ∼ sw b₂ z ● π₂ Δ ● t₂
           ty' = {!!}
           z3 : Atom
           z3 = {!!}
           ty'' : sw z3 (π₁ Δ b₁) ● π₁ Δ ● t₁ ∼ sw z3 (π₂ Δ b₂) ● π₂ Δ ● t₂
           ty'' = {!comm∼ ty!}
           tz : π₁ Δ ● ƛ b₁ t₁ ∼ π₂ Δ ● ƛ b₂ t₂
           tz = ƛ {b₃ = z3} _ ty''
  ⇒ (tᵣ · uᵣ) = {!!}
-}

{-
  ⟨_,_⟩●_ : Π → Π → E → E
  ⟨ π₁ , π₂ ⟩● ε = ε
  ⟨ π₁ , π₂ ⟩● Δ ,⟨ b₁ , b₂ ⟩ = (⟨ π₁ , π₂ ⟩● Δ) ,⟨ π₁ b₁ , π₂ b₂ ⟩

  πᵈ : E → Π
  πᵈ ε = id
  πᵈ (Δ ,⟨ b₁ , b₂ ⟩) = πᵈ Δ ∘ sw b₁ b₂

  bara : ∀ Δ x → Δ ⊢ x ≈ᴬ πᵈ Δ x
  bara ε x = ε refl
  bara (Δ ,⟨ b₁ , b₂ ⟩) x = {!!}

  bar : ∀ Δ t → Δ ⊢ t ≈ πᵈ Δ ● t
  bar Δ (V x) = V (bara Δ x)
  bar Δ (ƛ b t) = ƛ {!bar (Δ ,⟨ b , πᵈ Δ b ⟩) t!}
  bar Δ (t · u) = bar Δ t · bar Δ u
-}

{-
  postulate
    -- _-1 : Π → Π
    -- sw-1 : ∀ a b → (sw a b) -1 ≡ sw b a
    -- ∘-1 : ∀ π₁ π₂ → (π₁ ∘ π₂) -1 ≡ π₂ -1 ∘ π₁ -1
    -- +1 : ∀ a b π → ((π -1) a ≡ b) ≡ (a ≡ π b)
    π-inj : ∀ (π : Π) {x₁ x₂} → π x₁ ≡ π x₂ → x₁ ≡ x₂

  sw₁ : ∀ a b → sw a b a ≡ b
  sw₁ a b with a ==ℕ a | ==.reflexive {a} refl
  ... | true  | _ = refl
  ... | false | ()

  sw₂ : ∀ a b → sw a b b ≡ a
  sw₂ a b with a ==ℕ b | ==.sound a b
  ... | true | p rewrite p _ = refl
  ... | false | _ with b ==ℕ b | ==.reflexive {b} refl
  ... | true | _ = refl
  ... | false | ()

  commsw : ∀ a b → sw a b ≗ sw b a
  commsw a b c with a ==ℕ c | ==.sound a c
  ... | true | p rewrite p _ = sym (sw₂ b c)
  ... | false | _ with b ==ℕ c
  ... | true = refl
  ... | false with a ==ℕ c | ==.sound a c
  ... | true | p = {!!}
  ... | false | _ = refl

  nosw : ∀ {a b c} → c ≢ a → c ≢ b → sw a b c ≡ c
  nosw {a} {b} {c} c≢a c≢b with a ==ℕ c | ==.sound a c
  ... | true | p = ⊥-elim (c≢a (sym (p _)))
  ... | false | _ with b ==ℕ c | ==.sound b c
  ... | true | p = ⊥-elim (c≢b (sym (p _)))
  ... | false | _ = refl

  nono : ∀ {A B : Set} {a b c : B} → a ≡ b → a ≡ c → b ≢ c → A
  nono refl refl neq with neq refl
  ... | ()

  nonosw : ∀ {a b c} → b ≢ a → b ≢ c → sw a c b ≢ c
  nonosw b≢a b≢c swacb≡c = nono (nosw b≢a b≢c) swacb≡c b≢c

  nonosw₂ : ∀ a b c → b ≢ a → b ≢ c → sw c a b ≢ c
  nonosw₂ a b c b≢a b≢c swacb≡c = {!!}

  coinj : ∀ {a b} (π : Π) → a ≢ b → π a ≢ π b
  coinj π neq eq = neq (π-inj π eq)

  ct : (π₁ π₂ : Π) (Δ : E) {-(A₁ A₂ : )-} → Set
  ct π₁ π₂ Δ {-A₁ A₂-} = ∀ {b₁ b₂} → {-x₁ ∈ A₁ → b₂ ∈ A₂ →-} π₁ b₁ ≡ π₂ b₂ → Δ ⊢ b₁ ≈ᴬ b₂

  lem : ∀ {π₁ π₂ Δ} c a₁ a₂ →
      ct π₁ π₂ Δ {-(A₁ / {a₁}) (A₂ / {a₂})-} → c # {- (π₁ (A₁ / {a₁}) , π₂ (A₂ / {a₂})) -} →
      ct (sw (π₁ a₁) c ∘ π₁) (sw (π₂ a₂) c ∘ π₂) (Δ ,⟨ a₁ , a₂ ⟩) {-A₁ A₂-}
  lem {π₁} {π₂} {Δ} c a₁ a₂ r c# {b₁} {b₂} eq
    with b₁ ≟ a₁ | b₂ ≟ a₂
  ...  | yes ≡₁  | yes ≡₂ rewrite ≡₁ | ≡₂ = here refl refl
  ...  | yes ≡₁  | no  ≢₂ rewrite ≡₁ | sw₁ (π₁ a₁) c = nono (nosw (coinj π₂ ≢₂) π₂b₂≢c) (sym eq) π₂b₂≢c
          where
           π₂b₂≢c : π₂ b₂ ≢ c
           π₂b₂≢c = {!!}
  ...  | no  ≢₁  | yes ≡₂ rewrite ≡₂ | sw₁ (π₂ a₂) c = nono (nosw (coinj π₁ ≢₁) π₁b₁≢c) eq π₁b₁≢c
          where
           π₁b₁≢c : π₁ b₁ ≢ c
           π₁b₁≢c = {!!}
  ...  | no  ≢₁  | no  ≢₂ = there (≢₁ ∘ sym) (≢₂ ∘ sym) (r pf)
     where π₁b₁≢π₁a₁ = coinj π₁ ≢₁
           π₂b₂≢π₂a₂ = coinj π₂ ≢₂
           π₁b₁≢c : π₁ b₁ ≢ c
           π₁b₁≢c = {!!}
           π₂b₂≢c : π₂ b₂ ≢ c
           π₂b₂≢c = {!!}
           pf : π₁ b₁ ≡ π₂ b₂
           pf = trans (sym (nosw π₁b₁≢π₁a₁ π₁b₁≢c))
                (trans eq (nosw π₂b₂≢π₂a₂ π₂b₂≢c))

  commct : ∀ {π₁ π₂ π₃ π₄ π₁′ π₂′ : Π} {Δ} → π₁ ≗ π₁′ → π₂ ≗ π₂′ → ct (π₁ ∘ π₃) (π₂ ∘ π₄) Δ → ct (π₁′ ∘ π₃) (π₂′ ∘ π₄) Δ
  commct e1 e2 q r = q (trans (e1 _) (trans r (sym (e2 _))))

  lem' : ∀ {π₁ π₂ Δ} c a₁ a₂ →
      ct π₁ π₂ Δ {-(A₁ / {a₁}) (A₂ / {a₂})-} → c # {- (π₁ (A₁ / {a₁}) , π₂ (A₂ / {a₂})) -} →
      ct (sw c (π₁ a₁) ∘ π₁) (sw c (π₂ a₂) ∘ π₂) (Δ ,⟨ a₁ , a₂ ⟩) {-A₁ A₂-}
  lem' {π₁} {π₂} {Δ} c a₁ a₂ r c# {b₁} {b₂} eq
    with b₁ ≟ a₁ | b₂ ≟ a₂
  ...  | yes ≡₁  | yes ≡₂ rewrite ≡₁ | ≡₂ = {!here refl refl!}
  ...  | yes ≡₁  | no  ≢₂ rewrite ≡₁ | sw₁ (π₁ a₁) c = {!⊥-elim (nonosw (coinj π₂ ≢₂) π₂b₂≢c (sym eq))!}
          where
           π₂b₂≢c : π₂ b₂ ≢ c
           π₂b₂≢c = {!!}
  ...  | no  ≢₁  | yes ≡₂ rewrite ≡₂ | sw₁ (π₂ a₂) c = {!⊥-elim (nonosw (coinj π₁ ≢₁) π₁b₁≢c eq)!}
          where
           π₁b₁≢c : π₁ b₁ ≢ c
           π₁b₁≢c = {!!}
  ...  | no  ≢₁  | no  ≢₂ = {!there (≢₁ ∘ sym) (≢₂ ∘ sym) (r pf)!}
     where π₁b₁≢π₁a₁ = coinj π₁ ≢₁
           π₂b₂≢π₂a₂ = coinj π₂ ≢₂
           π₁b₁≢c : π₁ b₁ ≢ c
           π₁b₁≢c = {!!}
           π₂b₂≢c : π₂ b₂ ≢ c
           π₂b₂≢c = {!!}
           pf : π₁ b₁ ≡ π₂ b₂
           pf = {!trans (sym (nosw π₁b₁≢π₁a₁ π₁b₁≢c))
                (trans eq (nosw π₂b₂≢π₂a₂ π₂b₂≢c))!}

  thm : ∀ π₁ π₂ Δ (R : ct π₁ π₂ Δ) {t₁ t₂} → π₁ ● t₁ ∼ π₂ ● t₂ → Δ ⊢ t₁ ≈ t₂
  thm π₁ π₂ Δ R {V x₁} {V x₂} (V xᵣ) = V (R xᵣ)
  thm π₁ π₂ Δ R {ƛ b₁ t₁} {ƛ b₂ t₂} (ƛ {b₃ = b₃} b₃# tᵣ) rewrite map∘ (sw b₃ (π₁ b₁)) π₁ t₁ | map∘ (sw b₃ (π₂ b₂)) π₂ t₂
    = ƛ (thm (sw b₃ (π₁ b₁) ∘ π₁) (sw b₃ (π₂ b₂) ∘ π₂) (Δ ,⟨ b₁ , b₂ ⟩) (λ {b₁'} {b₂'} → lem' b₃ b₁ b₂ (λ x → R x) {!c#!}) tᵣ)
  thm π₁ π₂ Δ R {_ · _} {_ · _} (tᵣ · uᵣ) = thm π₁ π₂ Δ R tᵣ · thm π₁ π₂ Δ R uᵣ
  thm π₁ π₂ Δ R {V _} {ƛ _ _} ()
  thm π₁ π₂ Δ R {V _} {_ · _} ()
  thm π₁ π₂ Δ R {ƛ _ _} {V _} ()
  thm π₁ π₂ Δ R {ƛ _ _} {_ · _} ()
  thm π₁ π₂ Δ R {_ · _} {V _} ()
  thm π₁ π₂ Δ R {_ · _} {ƛ _ _} ()

  unthere₁ : ∀ {a₁ b₁ a₂ b₂ Δ} → a₁ ≢ b₁ → (Δ ,⟨ a₁ , a₂ ⟩) ⊢ b₁ ≈ᴬ b₂ → Δ ⊢ b₁ ≈ᴬ b₂
  unthere₁ ≢₁ (here ≡₁ ≡₂) = ⊥-elim (≢₁ ≡₁)
  unthere₁ _  (there _ _ Δᵣ) = Δᵣ

  contra₁ : ∀ {a₁ b₁ a₂ b₂ Δ} → a₁ ≢ b₁ → a₂ ≡ b₂ → ¬((Δ ,⟨ a₁ , a₂ ⟩) ⊢ b₁ ≈ᴬ b₂)
  contra₁ ≢₁ _ (here ≡₁ _) = ≢₁ ≡₁
  contra₁ _ ≡₂ (there _ ≢₂ _) = ≢₂ ≡₂

  contra₂ : ∀ {a₁ b₁ a₂ b₂ Δ} → a₁ ≡ b₁ → a₂ ≢ b₂ → ¬((Δ ,⟨ a₁ , a₂ ⟩) ⊢ b₁ ≈ᴬ b₂)
  contra₂ _ ≢₂ (here _ ≡₂) = ≢₂ ≡₂
  contra₂ ≡₁ _ (there ≢₁ _ _) = ≢₁ ≡₁

  unthere₂ : ∀ {a₁ b₁ a₂ b₂ Δ} → a₂ ≢ b₂ → (Δ ,⟨ a₁ , a₂ ⟩) ⊢ b₁ ≈ᴬ b₂ → Δ ⊢ b₁ ≈ᴬ b₂
  unthere₂ ≢₂ (here ≡₁ ≡₂) = ⊥-elim (≢₂ ≡₂)
  unthere₂ ≢₂ (there _ _ Δᵣ) = Δᵣ

  ct' : (π₁ π₂ : Π) (Δ : E) {-(A₁ A₂ : )-} → Set
  ct' π₁ π₂ Δ {-A₁ A₂-} = ∀ {b₁ b₂} → {-x₁ ∈ A₁ → b₂ ∈ A₂ →-} Δ ⊢ b₁ ≈ᴬ b₂ → π₁ b₁ ≡ π₂ b₂

  ext' : ∀ {π₁ π₂ Δ} c a₁ a₂ →
      ct' π₁ π₂ Δ {-(A₁ / {a₁}) (A₂ / {a₂})-} → c # {- (π₁ (A₁ / {a₁}) , π₂ (A₂ / {a₂})) -} →
      ct' (sw c (π₁ a₁) ∘ π₁) (sw c (π₂ a₂) ∘ π₂) (Δ ,⟨ a₁ , a₂ ⟩) {-A₁ A₂-}
  ext' c a₁ a₂ r c# (here refl refl) = trans (sw₂ c _) (sym (sw₂ c _))
  ext' {π₁} {π₂} {Δ} c a₁ a₂ r c# {b₁} {b₂} (there ≢₁ ≢₂ Δᵣ) =
                            trans (nosw π₁b₁≢c (π₁b₁≢π₁a₁ ∘ sym)) (trans pf (sym (nosw π₂b₂≢c (π₂b₂≢π₂a₂ ∘ sym))))
     where π₁b₁≢π₁a₁ = coinj π₁ ≢₁
           π₂b₂≢π₂a₂ = coinj π₂ ≢₂
           π₁b₁≢c : π₁ b₁ ≢ c
           π₁b₁≢c = {!!}
           π₂b₂≢c : π₂ b₂ ≢ c
           π₂b₂≢c = {!!}
           pf : π₁ b₁ ≡ π₂ b₂
           pf = r Δᵣ

  thm' : ∀ {π₁ π₂ Δ t₁ t₂} → ct' π₁ π₂ Δ
                           → Δ ⊢ t₁ ≈ t₂
                           → π₁ ● t₁ ∼ π₂ ● t₂
  thm' R (V xᵣ) = V (R xᵣ)
  thm' {π₁} {π₂} {Δ} R (ƛ {b₁} {b₂} {t₁} {t₂} tᵣ) = pf''
    where c : Atom
          c = {!!}
          pf : sw c (π₁ b₁) ∘ π₁ ● t₁ ∼ sw c (π₂ b₂) ∘ π₂ ● t₂
          pf = thm' (ext' c b₁ b₂ R {!!}) tᵣ
          pf' : sw c (π₁ b₁) ● π₁ ● t₁ ∼ sw c (π₂ b₂) ● π₂ ● t₂
          pf' rewrite map∘ (sw c (π₁ b₁)) π₁ t₁ | map∘ (sw c (π₂ b₂)) π₂ t₂ = pf
          pf'' : π₁ ● ƛ _ t₁ ∼ π₂ ● ƛ _ t₂
          pf'' = ƛ {b₃ = c} {!!} pf'
  thm' R (tᵣ · uᵣ) = thm' R tᵣ · thm' R uᵣ

{-
  postulate
    -- π-inj : ∀ {π₁ π₂ : Π} {x₁ x₂} → π₁ x₁ ≡ π₂ x₂ → x₁ ≡ x₂ -- ?
    -- π-cong₂ : ∀ (π₁ π₂ : Π) {x₁ x₂} → x₁ ≡ x₂ → π₁ x₁ ≡ π₂ x₂

  ●≈ᴬ : ∀ π₁ π₂ {Δ x₁ x₂} → Δ ⊢ x₁ ≈ᴬ x₂
                           → ⟨ π₁ , π₂ ⟩● Δ ⊢ π₁ x₁ ≈ᴬ π₂ x₂
  ●≈ᴬ π₁ π₂ (ε ≡ₓ) = {!!} -- = ε (π-cong₂ π₁ π₂ ≡ₓ)
  ●≈ᴬ π₁ π₂ (here refl refl) = here refl refl
  ●≈ᴬ π₁ π₂ (there ≢₁ ≢₂ Δᵣ) = there (≢₁ ∘ π-inj π₁) (≢₂ ∘ π-inj π₂) (●≈ᴬ π₁ π₂ Δᵣ)

  ●≈' : ∀ π₁ π₂ {Δ t₁ t₂} → Δ ⊢ t₁ ≈ t₂
                           → ⟨ π₁ , π₂ ⟩● Δ ⊢ π₁ ● t₁ ≈ π₂ ● t₂
  ●≈' π₁ π₂ (V xᵣ) = V (●≈ᴬ _ _ xᵣ)
  ●≈' π₁ π₂ {Δ} (ƛ {b₁} {b₂} {t₁} {t₂} tᵣ) = ƛ {⟨ π₁ , π₂ ⟩● Δ} {π₁ b₁} {π₂ b₂} {π₁ ● t₁} {π₂ ● t₂} (●≈' π₁ π₂ {Δ ,⟨ b₁ , b₂ ⟩} tᵣ)
  ●≈' π₁ π₂ (tᵣ · uᵣ) = ●≈' π₁ π₂ tᵣ · ●≈' π₁ π₂ uᵣ

  ●≈ : ∀ π₁ π₂ {Δ t₁ t₂} → ⟨ π₁ , π₂ ⟩● Δ ⊢ π₁ ● t₁ ≈ π₂ ● t₂
                          → Δ ⊢ t₁ ≈ t₂
  ●≈ π₁ π₂ r = {!!}

  ≈● : ∀ {b₁ b₂ b₃ t₁ t₂} Δ →
         Δ ,⟨ b₃ , b₃ ⟩ ⊢ sw b₃ b₁ ● t₁ ≈ sw b₃ b₂ ● t₂ → 
         Δ ,⟨ b₁ , b₂ ⟩ ⊢ t₁ ≈ t₂
  ≈● {b₁} {b₂} {b₃} Δ₀ = pf Δ₀ _ _
   where
    pf : ∀ Δ t₁ t₂ →
         Δ ,⟨ b₃ , b₃ ⟩ ⊢ sw b₃ b₁ ● t₁ ≈ sw b₃ b₂ ● t₂ → 
         Δ ,⟨ b₁ , b₂ ⟩ ⊢ t₁ ≈ t₂
    pf Δ (V x₁) (V x₂) (V xᵣ) = V {!!}
    pf Δ (ƛ b₁ t₁) (ƛ b₂ t₂) (ƛ tᵣ) = ƛ {!pf ? t₁ t₂ ?!}
    pf Δ (t₁ · u₁) (t₂ · u₂) (tᵣ · uᵣ) = pf Δ t₁ t₂ tᵣ · pf Δ u₁ u₂ uᵣ
    pf _ _ _ _ = {!!}

  ≈●' : ∀ {b₁ b₂ b₃ t₁ t₂} Δ →
         Δ ,⟨ b₁ , b₂ ⟩ ⊢ t₁ ≈ t₂ →
         Δ ,⟨ b₃ , b₃ ⟩ ⊢ sw b₃ b₁ ● t₁ ≈ sw b₃ b₂ ● t₂
  ≈●' Δ (V xᵣ) = V {!!}
  ≈●' Δ (ƛ tᵣ) rewrite map∘ (sw b₃ b₁)  = ƛ {!≈●' ? tᵣ!}
  ≈●' Δ (tᵣ · uᵣ) = ≈●' Δ tᵣ · ≈●' Δ uᵣ

  ⇐ : ∀ {t₁ t₂} → t₁ ∼ t₂ → ε ⊢ t₁ ≈ t₂
  ⇐ (V xᵣ) = {!V (ε xᵣ)!}
  ⇐ (ƛ {b₃ = b₃} b₃# tᵣ) = {!ƛ (≈● {b₃ = b₃} ε (⇐ tᵣ))!}
  ⇐ (tᵣ · uᵣ) = ⇐ tᵣ · ⇐ uᵣ
-}
{-
  record E : Set₁ where
    constructor mk
    field
      ra : Rel₀ Atom
      π₁ π₂ : Π
      ok : ∀ x₁ x₂ → π₁ x₁ ≡ π₂ x₂ → ra x₁ x₂ 
  open E

  foo : ∀ b₁ b₂ b₃ x₁ x₂ (π₁ π₂ : Π) ra →
        sw b₃ (π₁ b₁) (π₁ x₁) ≡ sw b₃ (π₂ b₂) (π₂ x₂) → Extend b₁ b₂ ra x₁ x₂
  foo b₁ b₂ b₃ x₁ x₂ π₁ π₂ ra eq with b₃ ==ᴬ π₁ x₁ | b₃ ==ᴬ π₂ x₂
  ... | true  | true = {!here!}
  ... | true  | false = {!!}
  ... | false | _ = {!!}

  sw∼ : ∀ b₁ b₂ {t₁ t₂} → t₁ ∼™ t₂ → swap b₁ and b₂ in™ t₁ ∼™ swap b₁ and b₂ in™ t₂
  sw∼ b₁ b₂ (V refl) = V refl
  sw∼ b₁ b₂ (ƛ {b₃ = b₃} b₃# tᵣ) = ƛ {b₃ = {!!}} _ {!!}
  sw∼ b₁ b₂ (tᵣ · uᵣ) = sw∼ b₁ b₂ tᵣ · sw∼ b₁ b₂ uᵣ

  ∼sw : ∀ b₁ b₂ {t₁ t₂} → swap b₁ and b₂ in™ t₁ ∼™ swap b₁ and b₂ in™ t₂ → t₁ ∼™ t₂
  ∼sw = {!!}

  ⇐ : ∀ Δ {t₁ t₂} → map™ (π₁ Δ) t₁ ∼™ map™ (π₂ Δ) t₂ → _⊢_≈_ (ra Δ) t₁ t₂
  ⇐ Δ {V x₁} {V x₂} (V eq) = V (ok Δ _ _ eq)
  ⇐ (mk ra π₁ π₂ ok) {ƛ b₁ t₁} {ƛ b₂ t₂} (ƛ {b₃ = b₃} b₃# tᵣ)
    rewrite map∘ (sw b₃ (π₁ b₁)) π₁ t₁
          | map∘ (sw b₃ (π₂ b₂)) π₂ t₂ = ƛ (⇐ (mk _ _ _ (λ x₁ x₂ → foo b₁ b₂ b₃ x₁ x₂ π₁ π₂ ra)) tᵣ)
  ⇐ Δ {_ · _} {_ · _} (tᵣ · uᵣ) = ⇐ Δ tᵣ · ⇐ Δ uᵣ
  ⇐ Δ {V _} {ƛ _ _} ()
  ⇐ Δ {V _} {_ · _} ()
  ⇐ Δ {ƛ _ _} {V _} ()
  ⇐ Δ {ƛ _ _} {_ · _} ()
  ⇐ Δ {_ · _} {V _} ()
  ⇐ Δ {_ · _} {ƛ _ _} ()

  ⇒ : ∀ Δ {t₁ t₂} → _⊢_≈_ Δ t₁ t₂ → t₁ ∼™ t₂
  ⇒ Δ (V x) = {!V ?!}
  ⇒ Δ (ƛ tᵣ) = ƛ {b₃ = _} {!!} {!⇒ Δ!}
  ⇒ Δ (tᵣ · uᵣ) = ⇒ Δ tᵣ · ⇒ Δ uᵣ
-}
{-
  lemm : ∀ Δ x₁ x₂ t₁ t₂
     → ce Δ t₁ t₂ ≡ cc t₁ (swap x₁ and x₂ in™ t₂)
  lemm Δ x₁ x₂ t₁ t₂ = {!!}

  lemmm : ∀ x₁ x₂ t₁ t₂
     → ee t₁ t₂ ≡ cc t₁ (swap x₁ and x₂ in™ t₂)
  lemmm x₁ x₂ t₁ t₂ = {!!}
-}
{-
  lem : ∀ Δ t u → ce Δ t u ≡ cc t u
  lem Δ (V x₁) (V x₂) = {!!}
  lem Δ (ƛ b₁ t₁) (ƛ b₂ t₂) rewrite lem (extend b₁ b₂ Δ) t₁ t₂ = {!!}
  lem Δ (t₁ · u₁) (t₂ · u₂) rewrite lem Δ t₁ t₂ | lem Δ u₁ u₂ = refl
  lem _ (V _) (ƛ _ _) = refl
  lem _ (V _) (_ · _) = refl
  lem _ (ƛ _ _) (V _) = refl
  lem _ (ƛ _ _) (_ · _) = refl
  lem _ (_ · _) (V _) = refl
  lem _ (_ · _) (ƛ _ _) = refl
-}

{-
  lem : ∀ Δ t u → T (ce Δ t u) → T (cc t u)
  lem Δ (V x₁) (V x₂) p = {!!}
  lem Δ (ƛ b₁ t₁) (ƛ b₂ t₂) p = {!!}
  lem Δ (t₁ · u₁) (t₂ · u₂) p = T∧ (lem Δ t₁ t₂ (T∧₁ p)) (lem Δ u₁ u₂ (T∧₂ {_} p))
  lem _ (V _) (ƛ _ _) ()
  lem _ (V _) (_ · _) ()
  lem _ (ƛ _ _) (V _) ()
  lem _ (ƛ _ _) (_ · _) ()
  lem _ (_ · _) (V _) ()
  lem _ (_ · _) (ƛ _ _) ()



  π= : (π₁ π₂ : Atom → Atom) → Atom → Atom → Bool
  π= π₁ π₂ x₁ x₂ = π₁ x₁ ==ᴬ π₂ x₂


  _≗₂_ : (Δ₁ Δ₂ : Cmp Atom) → Set
  Δ₁ ≗₂ Δ₂ = ∀ x₁ x₂ → Δ₁ x₁ x₂ ≡ Δ₂ x₁ x₂

  foo : ∀ {Δ π₁ π₂} {re : Δ ≗₂ π= π₁ π₂} b₁ b₂ x₁ x₂ → extend b₁ b₂ Δ x₁ x₂ ≡ π₁ x₁ ==ᴬ sw (π₁ b₁) (π₂ b₂) (π₂ x₂)
  foo b₁ b₂ x₁ x₂ with b₁ ==ᴬ x₁ | b₂ ==ᴬ x₂
  ... | true | true = {!!}
  ... | false | false = {!!}
  ... | false | true = {!!}
  ... | true | false = {!!}
-}

{-with b₁ ==ℕ x₁ | b₂ ==ℕ x₂ | b₁ ==ℕ π x₂
  ... | true | true | true = {!re x₁ b₂!}
  ... | true | true | false = {!!}
  ... | true | false | true = {!!}
  ... | true | false | false = {!!}
  ... | false | true | true = {!!}
  ... | false | true | false = {!!}
  ... | false | false | true = {!!}
  ... | false | false | false = {!re ? ?!}
-}

{-
  ⇐ : ∀ Δ π₁ π₂ (re : Δ ≗₂ π= π₁ π₂) t u → T (cc (map™ π₁ t) (map™ π₂ u)) → T (ce Δ t u)
  ⇐ Δ π₁ π₂ re (V x₁) (V x₂) p rewrite re x₁ x₂ = p
  ⇐ Δ π₁ π₂ re (ƛ b₁ t₁) (ƛ b₂ t₂) p rewrite map∘ (sw (π₁ b₁) (π₂ b₂)) π₂ t₂ = ⇐ (extend b₁ b₂ Δ) π₁ (sw (π₁ b₁) (π₂ b₂) ∘ π₂) (foo {Δ} {π₁} {π₂} {re} b₁ b₂) t₁ t₂ p
  ⇐ Δ π₁ π₂ re (t₁ · u₁) (t₂ · u₂) p = T∧ (⇐ Δ π₁ π₂ re t₁ t₂ (T∧₁ p)) (⇐ Δ π₁ π₂ re u₁ u₂ (T∧₂ {cc (map™ π₁ t₁) _} {cc (map™ π₁ u₁) _} p))
  ⇐ _ _ _ _ (V _) (ƛ _ _) ()
  ⇐ _ _ _ _ (V _) (_ · _) ()
  ⇐ _ _ _ _ (ƛ _ _) (V _) ()
  ⇐ _ _ _ _ (ƛ _ _) (_ · _) ()
  ⇐ _ _ _ _ (_ · _) (V _) ()
  ⇐ _ _ _ _ (_ · _) (ƛ _ _) ()
-}

-}
open import Data.String

module StringTerm where
  open DataType String public hiding (appⁿ) renaming (Tmᴿ to Tmᴿˢ)

  _ℕᴿˢ : ℕ → Tmᴿˢ
  n ℕᴿˢ = ƛ "f" (ƛ "x" (replicapp n (V "f") (V "x")))
    where replicapp : ℕ → Tmᴿˢ → Tmᴿˢ → Tmᴿˢ
          replicapp zero    t u = u
          replicapp (suc n) t u = t · replicapp n t u
