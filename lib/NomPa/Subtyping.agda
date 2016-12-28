module NomPa.Subtyping where

open import Data.Nat as Nat renaming (_+_ to _+ℕ_ ; _∸_ to _-ℕ_ ;
                                      _≤?_ to _≤?ℕ_ ; _<_ to _<ℕ_ ;
                                      _≤_ to _≤ℕ_ ; _<′_ to _<′ℕ_ ;
                                      _≥_ to _≥ℕ_ )
open import NomPa.Worlds
open import Relation.Nullary
open import Relation.Binary using (Transitive)
open import Relation.Nullary.Decidable
open import Function
open import Data.Empty
open import Data.Bool
open import Data.List
open ListBoolWorlds using (listBoolWorlds)

record MinimalSymantics {World} (worldSym : WorldSymantics World)
                        (Rel : (α β : World) → Set) : Set where
  private
    infix 4 _⊆_
    _⊆_ : (α β : World) → Set
    _⊆_ = Rel
  open WorldSymantics worldSym
  field
    ⊆-ø : ∀ {α} → ø ⊆ α

    ⊆-cong-↑1 : ∀ {α β}
                  (α⊆β : α ⊆ β)
                → α ↑1 ⊆ β ↑1

    ⊆-cong-+1 : ∀ {α β}
                  (α⊆β : α ⊆ β)
                → α +1 ⊆ β +1

    ⊆-ctx-+1↑1 : ∀ {α β}
                   (α⊆β : α ⊆ β)
                 → α +1 ⊆ β ↑1

    α⊆ø→α+1⊆β : ∀ {α β} → α ⊆ ø → α +1 ⊆ β

  open WorldOps worldSym

  α⊆ø→α+⊆ø : ∀ {α} (base : α ⊆ ø) k → (α +ᵂ k) ⊆ ø
  α⊆ø→α+⊆ø base zero    = base
  α⊆ø→α+⊆ø base (suc n) = α⊆ø→α+1⊆β (α⊆ø→α+⊆ø base n)

  ⊆-ctx-+↑ : ∀ {α β} (base : α ⊆ β) k → (α +ᵂ k) ⊆ (β ↑ k)
  ⊆-ctx-+↑ base zero    = base
  ⊆-ctx-+↑ base (suc n) = ⊆-ctx-+1↑1 (⊆-ctx-+↑ base n)

  ⊆-cong-+ : ∀ {α β} (base : α ⊆ β) k → (α +ᵂ k) ⊆ (β +ᵂ k)
  ⊆-cong-+ base zero    = base
  ⊆-cong-+ base (suc n) = ⊆-cong-+1 (⊆-cong-+ base n)

  ⊆-cong-↑ : ∀ {α β} (base : α ⊆ β) k → (α ↑ k) ⊆ (β ↑ k)
  ⊆-cong-↑ base zero    = base
  ⊆-cong-↑ base (suc n) = ⊆-cong-↑1 (⊆-cong-↑ base n)

  -- later generalized into ⊆-exch-+-+
  ⊆-exch-+-+1 : ∀ {α β} (base : α ⊆ β) k → (α +ᵂ k) +1 ⊆ (β +1 +ᵂ k)
  ⊆-exch-+-+1 base zero     = ⊆-cong-+1 base
  ⊆-exch-+-+1 base (suc k)  = ⊆-cong-+1 (⊆-exch-+-+1 base k)

  -- later generalized into ⊆-exch-↑-↑
  ⊆-exch-↑-↑1 : ∀ {α β} (base : α ⊆ β) k → (α ↑ k) ↑1 ⊆ (β ↑1 ↑ k)
  ⊆-exch-↑-↑1 base zero     = ⊆-cong-↑1 base
  ⊆-exch-↑-↑1 base (suc k)  = ⊆-cong-↑1 (⊆-exch-↑-↑1 base k)

  ⊆-assoc-↑ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → (α ↑ k₁ ↑ k₂) ⊆ (β ↑ (k₂ +ℕ k₁))
  ⊆-assoc-↑ base k₁ zero     = ⊆-cong-↑ base k₁
  ⊆-assoc-↑ base k₁ (suc k₂) = ⊆-cong-↑1 (⊆-assoc-↑ base k₁ k₂)

  ⊆-assoc-↑′ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → (α ↑ (k₂ +ℕ k₁)) ⊆ (β ↑ k₁ ↑ k₂)
  ⊆-assoc-↑′ base k₁ zero     = ⊆-cong-↑ base k₁
  ⊆-assoc-↑′ base k₁ (suc k₂) = ⊆-cong-↑1 (⊆-assoc-↑′ base k₁ k₂)

  ⊆-assoc-+ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → ((α +ᵂ k₁) +ᵂ k₂) ⊆ (β +ᵂ (k₂ +ℕ k₁))
  ⊆-assoc-+ base k₁ zero      = ⊆-cong-+ base k₁
  ⊆-assoc-+ base k₁ (suc k₂)  = ⊆-cong-+1 (⊆-assoc-+ base k₁ k₂)

  ⊆-assoc-+′ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → (α +ᵂ (k₂ +ℕ k₁)) ⊆ ((β +ᵂ k₁) +ᵂ k₂)
  ⊆-assoc-+′ base k₁ zero      = ⊆-cong-+ base k₁
  ⊆-assoc-+′ base k₁ (suc k₂)  = ⊆-cong-+1 (⊆-assoc-+′ base k₁ k₂)


record ⊆-Symantics {World} (worldSym : WorldSymantics World)
                 (_⊆_ : (α β : World) → Set) : Set where
  open WorldSymantics worldSym
  field
    ⊆-ø : ∀ {α} → ø ⊆ α

    ⊆-refl  : ∀ {α} → α ⊆ α

    ⊆-trans : ∀ {α β γ}
                (α⊆β : α ⊆ β)
                (β⊆γ : β ⊆ γ)
              → α ⊆ γ

    ⊆-cong-↑1 : ∀ {α β}
                  (α⊆β : α ⊆ β)
                → α ↑1 ⊆ β ↑1

    ⊆-cong-+1 : ∀ {α β}
                  (α⊆β : α ⊆ β)
                → α +1 ⊆ β +1

    ⊆-+1↑1 : ∀ {α} → α +1 ⊆ α ↑1

    ⊆-↑1-inj : ∀ {α β}
                 (α↑1⊆β↑1 : α ↑1 ⊆ β ↑1)
               → α ⊆ β

    ⊆-+1-inj : ∀ {α β}
                 (α+1⊆β+1 : α +1 ⊆ β +1)
               → α ⊆ β

    ⊆-unctx-+1↑1 : ∀ {α β}
                     (α+1⊆β↑1 : α +1 ⊆ β ↑1)
                   → α ⊆ β

    ø+1⊆ø : ø +1 ⊆ ø

  α⊆ø→α+1⊆ø : ∀ {α} → α ⊆ ø → α +1 ⊆ ø
  α⊆ø→α+1⊆ø α⊆ø = ⊆-trans (⊆-cong-+1 α⊆ø) ø+1⊆ø

  α+1⊆ø→α⊆ø : ∀ {α} → α +1 ⊆ ø → α ⊆ ø
  α+1⊆ø→α⊆ø α+1⊆ø = ⊆-+1-inj (⊆-trans α+1⊆ø ⊆-ø)

  --private
  mutual
    α⊆ø→α+1⊆β : ∀ {α β} → α ⊆ ø → α +1 ⊆ β
    α⊆ø→α+1⊆β α⊆ø = ⊆-trans (α⊆ø→α+1⊆ø α⊆ø) ⊆-ø

  ⊆-ctx-+1↑1 : ∀ {α β} (α⊆β : α ⊆ β) → α +1 ⊆ β ↑1
  ⊆-ctx-+1↑1 α⊆β = ⊆-trans (⊆-cong-+1 α⊆β) ⊆-+1↑1

  minimalSymantics : MinimalSymantics worldSym _⊆_
  minimalSymantics = record {
              ⊆-ø = ⊆-ø;
              ⊆-cong-↑1 = ⊆-cong-↑1;
              ⊆-cong-+1 = ⊆-cong-+1;
              ⊆-ctx-+1↑1 = ⊆-ctx-+1↑1;
              α⊆ø→α+1⊆β = α⊆ø→α+1⊆β }

  open MinimalSymantics minimalSymantics public using
    (⊆-ctx-+↑; ⊆-cong-+; ⊆-cong-↑; α⊆ø→α+⊆ø;
     ⊆-exch-+-+1; ⊆-exch-↑-↑1;
     ⊆-assoc-+; ⊆-assoc-+′; ⊆-assoc-↑; ⊆-assoc-↑′)

  open WorldOps worldSym

  ⊆-+-↑ : ∀ {α} k → (α +ᵂ k) ⊆ (α ↑ k)
  ⊆-+-↑ = ⊆-ctx-+↑ ⊆-refl

  module ⊆-Reasoning where
    infix  3 _∎
    infixr 2 _⊆⟨_⟩_

    _⊆⟨_⟩_ : ∀ α {β γ} → α ⊆ β → β ⊆ γ → α ⊆ γ
    _⊆⟨_⟩_ _ = ⊆-trans

    _∎ : ∀ α → α ⊆ α
    _∎ _ = ⊆-refl

  ⊆-exch-+-+ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → ((α +ᵂ k₁) +ᵂ k₂) ⊆ ((β +ᵂ k₂) +ᵂ k₁)
  ⊆-exch-+-+ base k₁ zero     = ⊆-cong-+ base k₁
  ⊆-exch-+-+ {α} {β} base k₁ (suc k₂)
     = α +ᵂ k₁ +ᵂ k₂ +ᵂ 1  ⊆⟨ ⊆-cong-+1 (⊆-exch-+-+ base k₁ k₂) ⟩
       β +ᵂ k₂ +ᵂ k₁ +ᵂ 1  ⊆⟨ ⊆-exch-+-+1 ⊆-refl k₁ ⟩
       β +ᵂ k₂ +ᵂ 1  +ᵂ k₁ ∎
     where open ⊆-Reasoning

  ⊆-exch-↑-↑ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → (α ↑ k₁ ↑ k₂) ⊆ (β ↑ k₂ ↑ k₁)
  ⊆-exch-↑-↑ base k₁ zero = ⊆-cong-↑ base k₁
  ⊆-exch-↑-↑ {α} {β} base k₁ (suc k₂)
     = α ↑ k₁ ↑ k₂ ↑ 1  ⊆⟨ ⊆-cong-↑1 (⊆-exch-↑-↑ base k₁ k₂) ⟩
       β ↑ k₂ ↑ k₁ ↑ 1  ⊆⟨ ⊆-exch-↑-↑1 ⊆-refl k₁ ⟩
       β ↑ k₂ ↑ 1  ↑ k₁ ∎
     where open ⊆-Reasoning

  ⊆-exch-↑-↑′ : ∀ {α} k₁ k₂ → (α ↑ k₁ ↑ k₂) ⊆ (α ↑ k₂ ↑ k₁)
  ⊆-exch-↑-↑′ _      zero = ⊆-refl
  ⊆-exch-↑-↑′ {α} k₁ (suc k₂)
     = α ↑ k₁ ↑ k₂ ↑ 1  ⊆⟨ ⊆-cong-↑1 (⊆-exch-↑-↑′ k₁ k₂) ⟩
       α ↑ k₂ ↑ k₁ ↑ 1  ⊆⟨ ⊆-exch-↑-↑1 ⊆-refl k₁ ⟩
       α ↑ k₂ ↑ 1  ↑ k₁ ∎
     where open ⊆-Reasoning

  ⊆-exch-↑-↑′′ : ∀ {α β} (base : α ⊆ β) k₁ k₂ → (α ↑ k₁ ↑ k₂) ⊆ (β ↑ k₂ ↑ k₁)
  ⊆-exch-↑-↑′′ base k₁ k₂ = ⊆-trans (⊆-exch-↑-↑′ k₁ k₂) (⊆-cong-↑ (⊆-cong-↑ base k₂) k₁)

  α+⊆ø→α⊆ø : ∀ {α} k (base : (α +ᵂ k) ⊆ ø) → α ⊆ ø
  α+⊆ø→α⊆ø zero    base = base
  α+⊆ø→α⊆ø (suc n) base = α+⊆ø→α⊆ø n (α+1⊆ø→α⊆ø base)

  ⊆-ø+ : ∀ {α} k → (ø +ᵂ k) ⊆ α
  ⊆-ø+ k = ⊆-trans (α⊆ø→α+⊆ø ⊆-refl k) ⊆-ø

  ⊆-+-inj : ∀ {α β} k
              (α+k⊆β+k : (α +ᵂ k) ⊆ (β +ᵂ k))
            → α ⊆ β
  ⊆-+-inj zero    x = x
  ⊆-+-inj (suc k) x = ⊆-+-inj k (⊆-+1-inj x)

  module Useless where
    ø↑⊆α↑ : ∀ {α} k → (ø ↑ k) ⊆ (α ↑ k)
    ø↑⊆α↑ = ⊆-cong-↑ ⊆-ø

record ⊈-Symantics {World} (worldSym : WorldSymantics World)
                   (_⊆_ _⊈_ : (α β : World) → Set) : Set where
  open WorldSymantics worldSym
  field
    ↑1⊈ø  : ∀ {α} → α ↑1 ⊈ ø
    ↑1⊈+1 : ∀ {α β} → α ↑1 ⊈ β +1

    ⊈-cong-+1 : ∀ {α β} (α⊈β : α ⊈ β) → α +1 ⊈ β +1
    ⊈-cong-↑1 : ∀ {α β} (α⊈β : α ⊈ β) → α ↑1 ⊈ β ↑1
    ⊈-ctx-+1↑1 : ∀ {α β} (α⊈β : α ⊈ β) → α +1 ⊈ β ↑1
    ⊈-inj-+1 : ∀ {α β} (α+1⊈β+1 : α +1 ⊈ β +1) → α ⊈ β
    ⊈-inj-↑1 : ∀ {α β} (α↑1⊈β↑1 : α ↑1 ⊈ β ↑1) → α ⊈ β
    ⊈-unctx-+1↑1 : ∀ {α β} (α+1⊈β↑1 : α +1 ⊈ β ↑1) → α ⊈ β
    α⊈ø→α+1⊈ø : ∀ {α} (α⊈ø : α ⊈ ø) → α +1 ⊈ ø
    α+1⊈ø→α⊈ø : ∀ {α} (α+1⊈ø : α +1 ⊈ ø) → α ⊈ ø

record ⊆-Pack {World} (worldSym : WorldSymantics World) : Set₁ where
  infix 2 _⊆_
  infix 2 _⊈_
  field
    _⊆_ _⊈_ : ∀ (α β : World) → Set
    ⊈-elim : ∀ {α β} → α ⊈ β → ¬(α ⊆ β)
    ⊆-symantics : ⊆-Symantics worldSym _⊆_
    ⊈-symantics : ⊈-Symantics worldSym _⊆_ _⊈_
  open ⊆-Symantics ⊆-symantics public
  open ⊈-Symantics ⊈-symantics public

⊆ᵇ-pack : ⊆-Pack listBoolWorlds
⊆ᵇ-pack = record { _⊆_ = _⊆_
                 ; _⊈_ = _⊈_
                 ; ⊈-elim = id
                 ; ⊆-symantics = ⊆-symantics
                 ; ⊈-symantics = ⊈-symantics }
  where
  open ListBoolWorlds using (World; _∈_; _⊆_; _⊈_)
  open WorldSymantics listBoolWorlds
  open WorldOps listBoolWorlds

  ⊆-symantics : ⊆-Symantics listBoolWorlds _⊆_
  ⊆-symantics = record {
                ⊆-ø = λ _ ();
                ⊆-refl = λ _ x → x;
                ⊆-trans = λ f g _ → g _ ∘ f _;
                ⊆-cong-↑1 = λ x → ⊆-cong-↑1 x;
                ⊆-cong-+1 = λ x → ⊆-cong-+1 x;
                ⊆-+1↑1 = λ x → ⊆-+1↑1 x;
                ⊆-↑1-inj = λ f → f ∘ suc;
                ⊆-+1-inj = λ f → f ∘ suc;
                ⊆-unctx-+1↑1 = λ f → f ∘ suc;
                ø+1⊆ø = ø+1⊆ø }
    where
    ⊆-cong-↑1 : ∀ {α β} (α⊆β : α ⊆ β) → α ↑1 ⊆ β ↑1
    ⊆-cong-↑1 _   zero    _   = _
    ⊆-cong-↑1 α⊆β (suc x) x∈α = α⊆β x x∈α

    ⊆-cong-+1 : ∀ {α β} (α⊆β : α ⊆ β) → α +1 ⊆ β +1
    ⊆-cong-+1 _   zero    ()
    ⊆-cong-+1 α⊆β (suc n) x∈α+1 = α⊆β n x∈α+1

    ⊆-+1↑1 : ∀ {α} → α +1 ⊆ α ↑1
    ⊆-+1↑1 zero    = _
    ⊆-+1↑1 (suc _) = id

    ø+1⊆ø : ø +1 ⊆ ø
    ø+1⊆ø zero    ()
    ø+1⊆ø (suc _) ()

  open ⊆-Symantics ⊆-symantics public hiding (module Useless)

  ⊈-symantics : ⊈-Symantics listBoolWorlds _⊆_ _⊈_
  ⊈-symantics = record {
                  ↑1⊈ø = λ p → p 0 _;
                  ↑1⊈+1 = λ p → p 0 _;
                  ⊈-cong-+1 = λ g f → g (f ∘ suc);
                  ⊈-cong-↑1 = λ g f → g (f ∘ suc);
                  ⊈-ctx-+1↑1 = λ g f → g (f ∘ suc);
                  ⊈-inj-+1 = λ f → f ∘ ⊆-cong-+1;
                  ⊈-inj-↑1 = λ f → f ∘ ⊆-cong-↑1;
                  ⊈-unctx-+1↑1 = λ f → f ∘ ⊆-ctx-+1↑1;
                  α⊈ø→α+1⊈ø = λ g f → g (f ∘ suc);
                  α+1⊈ø→α⊈ø = λ f → f ∘ α⊆ø→α+1⊆ø }

-- Same as ⊆ᵇ-pack but _⊆_ is wrapped in a record.
⊆′ᵇ-pack : ⊆-Pack listBoolWorlds
⊆′ᵇ-pack = record { _⊆_ = _⊆_
                 ; _⊈_ = _⊈_
                 ; ⊈-elim = id
                 ; ⊆-symantics = ⊆-symantics
                 ; ⊈-symantics = ⊈-symantics }
  where
  open ListBoolWorlds using (World; _∈_; mk; coe) renaming (_⊆′_ to _⊆_; _⊈′_ to _⊈_)
  open WorldSymantics listBoolWorlds
  open WorldOps listBoolWorlds

  module B = ⊆-Pack ⊆ᵇ-pack

  ⊆-symantics : ⊆-Symantics listBoolWorlds _⊆_
  ⊆-symantics = record {
                ⊆-ø = mk λ _ ();
                ⊆-refl = mk λ _ x → x;
                ⊆-trans = λ f g → mk (λ _ → coe g _ ∘ coe f _);
                ⊆-cong-↑1 = mk ∘ B.⊆-cong-↑1 ∘ coe;
                ⊆-cong-+1 = mk ∘ B.⊆-cong-+1 ∘ coe;
                ⊆-+1↑1 = mk B.⊆-+1↑1;
                ⊆-↑1-inj = mk ∘ B.⊆-↑1-inj ∘ coe;
                ⊆-+1-inj = λ f → mk (coe f ∘ suc);
                ⊆-unctx-+1↑1 = λ f → mk (coe f ∘ suc);
                ø+1⊆ø = mk B.ø+1⊆ø }

  open ⊆-Symantics ⊆-symantics public hiding (module Useless)

  ⊈-symantics : ⊈-Symantics listBoolWorlds _⊆_ _⊈_
  ⊈-symantics = record {
                  ↑1⊈ø = λ p → coe p 0 _;
                  ↑1⊈+1 = λ p → coe p 0 _;
                  ⊈-cong-+1 = λ g f → g (mk $ coe f ∘ suc);
                  ⊈-cong-↑1 = λ g f → g (mk $ coe f ∘ suc);
                  ⊈-ctx-+1↑1 = λ g f → g (mk $ coe f ∘ suc);
                  ⊈-inj-+1 = λ f → f ∘ ⊆-cong-+1;
                  ⊈-inj-↑1 = λ f → f ∘ ⊆-cong-↑1;
                  ⊈-unctx-+1↑1 = λ f → f ∘ ⊆-ctx-+1↑1;
                  α⊈ø→α+1⊈ø = λ g f → g (mk $ coe f ∘ suc);
                  α+1⊈ø→α⊈ø = λ f → f ∘ α⊆ø→α+1⊆ø }

module Complete {_⊆_} (⊆-minimalSymantics : MinimalSymantics listBoolWorlds _⊆_)
                (⊆ᵇ-pack : ⊆-Pack listBoolWorlds) where
  open WorldSymantics listBoolWorlds
  open MinimalSymantics ⊆-minimalSymantics
  module B = ⊆-Pack ⊆ᵇ-pack
  open B using () renaming (_⊆_ to _⊆ᵇ_)

  ⊆-complete : ∀ {α β} → α ⊆ᵇ β → α ⊆ β
  ⊆-complete {α} {β} α⊆β = f α β α⊆β where

    ⊆ø : ∀ xs → xs ⊆ᵇ ø → xs ⊆ ø
    ⊆ø []             = λ _ → ⊆-ø
    ⊆ø (true   ∷ xs)  = ⊥-elim ∘ B.⊈-elim B.↑1⊈ø
    ⊆ø (false  ∷ xs)  = α⊆ø→α+1⊆β ∘ ⊆ø xs ∘ B.α+1⊆ø→α⊆ø

    f : ∀ xs ys → xs ⊆ᵇ ys → xs ⊆ ys
    f []             _             = λ _ → ⊆-ø
    f xs             []            = ⊆ø xs
    f (true   ∷ _)   (false ∷ _)   = ⊥-elim      ∘ B.⊈-elim B.↑1⊈+1
    f (true   ∷ xs)  (true ∷ ys)   = ⊆-cong-↑1   ∘ f xs ys ∘ B.⊆-↑1-inj
    f (false  ∷ xs)  (true ∷ ys)   = ⊆-ctx-+1↑1  ∘ f xs ys ∘ B.⊆-unctx-+1↑1
    f (false  ∷ xs)  (false ∷ ys)  = ⊆-cong-+1   ∘ f xs ys ∘ B.⊆-+1-inj

module CompleteListBoolWorlds {_⊆_} (⊆-minimalSymantics : MinimalSymantics listBoolWorlds _⊆_) where
  open Complete ⊆-minimalSymantics ⊆ᵇ-pack

module SemSyn {World} (worldSym : WorldSymantics World) where
  open WorldSymantics worldSym
  open WorldOps worldSym
  infix 2 _`⊆`_

  data _`⊆`_ : (α β : World) → Set where
    ø-bottom : ∀ {α} → ø `⊆` α

    refl  : ∀ {α} → α `⊆` α

    cong-↑1 : ∀ {α β}
                (α⊆β : α `⊆` β)
              → α ↑1 `⊆` β ↑1

    cong-+1 : ∀ {α β}
                (α⊆β : α `⊆` β)
              → α +1 `⊆` β +1

    ctx-+1↑1 : ∀ {α β}
                (α⊆β : α `⊆` β)
              → α +1 `⊆` β ↑1

    α`⊆`ø→α+1`⊆`β : ∀ {α β} → α `⊆` ø → α +1 `⊆` β

module Sem where
  open WorldSymantics listBoolWorlds
  open SemSyn listBoolWorlds public

  α`⊆`ø→α`⊆`β : ∀ {α} → α `⊆` ø → ∀ {β} → α `⊆` β
  α`⊆`ø→α`⊆`β ø-bottom           = ø-bottom
  α`⊆`ø→α`⊆`β refl               = ø-bottom
  α`⊆`ø→α`⊆`β (α`⊆`ø→α+1`⊆`β x)  = α`⊆`ø→α+1`⊆`β x

  `⊆`-symantics : ⊆-Symantics listBoolWorlds _`⊆`_
  `⊆`-symantics = record {
                  ⊆-ø    = ø-bottom;
                  ⊆-refl        = refl;
                  ⊆-trans       = trans;
                  ⊆-cong-↑1     = cong-↑1;
                  ⊆-cong-+1     = cong-+1;
                  ⊆-+1↑1        = ctx-+1↑1 refl;
                  ⊆-↑1-inj      = ↑1-inj;
                  ⊆-+1-inj      = +1-inj;
                  ⊆-unctx-+1↑1  = unctx-+1↑1;
                  ø+1⊆ø         = α`⊆`ø→α+1`⊆`β refl  } where

    trans : ∀ {α β γ} (α⊆β : α `⊆` β) (β⊆γ : β `⊆` γ) → α `⊆` γ
    trans ø-bottom        _                    = ø-bottom
    trans refl            α⊆γ                  = α⊆γ
    trans α⊆γ             refl                 = α⊆γ
    trans (cong-↑1 α⊆β)   (cong-↑1 β⊆γ)        = cong-↑1 (trans α⊆β β⊆γ)
    trans (cong-+1 α⊆β)   (cong-+1 β⊆γ)        = cong-+1 (trans α⊆β β⊆γ)
    trans (cong-+1 α⊆β)   (ctx-+1↑1 β⊆γ)       = ctx-+1↑1 (trans α⊆β β⊆γ)
    trans (ctx-+1↑1 α⊆β)  (cong-↑1 β⊆γ)        = ctx-+1↑1 (trans α⊆β β⊆γ)
    trans (cong-+1 α⊆β)   (α`⊆`ø→α+1`⊆`β β⊆ø)  = α`⊆`ø→α+1`⊆`β (trans α⊆β β⊆ø)
    trans (α`⊆`ø→α+1`⊆`β α⊆ø) _                = α`⊆`ø→α+1`⊆`β α⊆ø

    ↑1-inj : ∀ {α β} → α ↑1 `⊆` β ↑1 → α `⊆` β
    ↑1-inj refl           = refl
    ↑1-inj (cong-↑1 α⊆β)  = α⊆β

    +1-inj : ∀ {α β} → α +1 `⊆` β +1 → α `⊆` β
    +1-inj refl               = refl
    +1-inj (cong-+1 α⊆β)      = α⊆β
    +1-inj (α`⊆`ø→α+1`⊆`β x)  = α`⊆`ø→α`⊆`β x

    unctx-+1↑1 : ∀ {α β} (α+1⊆β↑1 : α +1 `⊆` β ↑1) → α `⊆` β
    unctx-+1↑1 (ctx-+1↑1 α⊆β)       = α⊆β
    unctx-+1↑1 (α`⊆`ø→α+1`⊆`β α⊆ø)  = trans α⊆ø ø-bottom

    α+1`⊆`ø→α`⊆`ø : ∀ {α} → α +1 `⊆` ø → α `⊆` ø
    α+1`⊆`ø→α`⊆`ø (α`⊆`ø→α+1`⊆`β α⊆ø) = α⊆ø

  open WorldOps listBoolWorlds


  minimalSymantics : MinimalSymantics listBoolWorlds _`⊆`_
  minimalSymantics = record {
              ⊆-ø = ø-bottom;
              ⊆-cong-↑1 = cong-↑1;
              ⊆-cong-+1 = cong-+1;
              ⊆-ctx-+1↑1 = ctx-+1↑1;
              α⊆ø→α+1⊆β = α`⊆`ø→α+1`⊆`β }

  module `⊆`-Sound {_⊆_} (⊆-symantics : ⊆-Symantics listBoolWorlds _⊆_) where
    open ⊆-Symantics ⊆-symantics hiding (minimalSymantics)

    `⊆`-sound : ∀ {α β} → α `⊆` β → α ⊆ β
    `⊆`-sound ø-bottom                     = ⊆-ø
    `⊆`-sound refl                         = ⊆-refl
    `⊆`-sound (cong-↑1 α⊆β)                = ⊆-cong-↑1 (`⊆`-sound α⊆β)
    `⊆`-sound (cong-+1 α⊆β)                = ⊆-cong-+1 (`⊆`-sound α⊆β)
    `⊆`-sound (ctx-+1↑1 x)                 = ⊆-ctx-+1↑1 (`⊆`-sound x)
    `⊆`-sound {β = β} (α`⊆`ø→α+1`⊆`β α⊆ø)  = α⊆ø→α+1⊆β {β = β} (`⊆`-sound α⊆ø)

  open Complete minimalSymantics public renaming (⊆-complete to `⊆`-complete)

module Syntactic {World} (worldSym : WorldSymantics World) where
  open WorldSymantics worldSym

  infix 2 _`⊆`_

  data _`⊆`_ : (α β : World) → Set where
    ø-bottom : ∀ {α} → ø `⊆` α

    refl  : ∀ {α} → α `⊆` α

    trans : ∀ {α β γ}
              (α⊆β : α `⊆` β)
              (β⊆γ : β `⊆` γ)
            → α `⊆` γ

    cong-↑1 : ∀ {α β}
                (α⊆β : α `⊆` β)
              → α ↑1 `⊆` β ↑1


    cong-+1 : ∀ {α β}
                (α⊆β : α `⊆` β)
              → α +1 `⊆` β +1

    +1↑1 : ∀ {α} → α +1 `⊆` α ↑1

    ↑1-inj : ∀ {α β}
              (α↑1⊆β↑1 : α ↑1 `⊆` β ↑1)
            → α `⊆` β

    +1-inj : ∀ {α β}
              (α+1⊆β+1 : α +1 `⊆` β +1)
            → α `⊆` β

    unctx-+1↑1 : ∀ {α β}
                   (α+1⊆β↑1 : α +1 `⊆` β ↑1)
                 → α `⊆` β

    ø+1`⊆`ø : ø +1 `⊆` ø

  `⊆`-symantics : ⊆-Symantics worldSym _`⊆`_
  `⊆`-symantics = record {
                ⊆-ø = ø-bottom;
                ⊆-refl = refl;
                ⊆-trans = trans;
                ⊆-cong-↑1 = cong-↑1;
                ⊆-cong-+1 = cong-+1;
                ⊆-+1↑1 = +1↑1;
                ⊆-↑1-inj = ↑1-inj;
                ⊆-+1-inj = +1-inj;
                ⊆-unctx-+1↑1 = unctx-+1↑1;
                ø+1⊆ø = ø+1`⊆`ø }

  minimalSymantics : MinimalSymantics worldSym _`⊆`_
  minimalSymantics = ⊆-Symantics.minimalSymantics `⊆`-symantics

  infix 2 _`⊈`_

  data _`⊈`_ : (α β : World) → Set where
    ↑1`⊈`ø  : ∀ {α} → α ↑1 `⊈` ø
    ↑1`⊈`+1 : ∀ {α β} → α ↑1 `⊈` β +1
    cong-+1 : ∀ {α β} (α⊈β : α `⊈` β) → α +1 `⊈` β +1
    cong-↑1 : ∀ {α β} (α⊈β : α `⊈` β) → α ↑1 `⊈` β ↑1
    ctx-+1↑1 : ∀ {α β} (α⊈β : α `⊈` β) → α +1 `⊈` β ↑1
    inj-+1 : ∀ {α β} (α+1⊈β+1 : α +1 `⊈` β +1) → α `⊈` β
    inj-↑1 : ∀ {α β} (α↑1⊈β↑1 : α ↑1 `⊈` β ↑1) → α `⊈` β
    unctx-+1↑1 : ∀ {α β} (α+1⊈β↑1 : α +1 `⊈` β ↑1) → α `⊈` β
    α`⊈`ø→α+1`⊈`ø : ∀ {α} (α⊈ø : α `⊈` ø) → α +1 `⊈` ø
    α+1`⊈`ø→α`⊈`ø : ∀ {α} (α+1⊈ø : α +1 `⊈` ø) → α `⊈` ø

  `⊈`-symantics : ⊈-Symantics worldSym _`⊆`_ _`⊈`_
  `⊈`-symantics = record
                  { ↑1⊈ø         = ↑1`⊈`ø
                  ; ↑1⊈+1        = ↑1`⊈`+1
                  ; ⊈-cong-+1    = cong-+1
                  ; ⊈-cong-↑1    = cong-↑1
                  ; ⊈-ctx-+1↑1   = ctx-+1↑1
                  ; ⊈-inj-+1     = inj-+1
                  ; ⊈-inj-↑1     = inj-↑1
                  ; ⊈-unctx-+1↑1 = unctx-+1↑1
                  ; α⊈ø→α+1⊈ø   = α`⊈`ø→α+1`⊈`ø
                  ; α+1⊈ø→α⊈ø   = α+1`⊈`ø→α`⊈`ø }

module SyntacticOnBools (⊆-pack : ⊆-Pack listBoolWorlds) where
  open WorldSymantics listBoolWorlds
  open Syntactic listBoolWorlds public
  open ⊆-Pack ⊆-pack hiding (minimalSymantics)

  `⊆`-sound : ∀ {α β} → α `⊆` β → α ⊆ β
  `⊆`-sound ø-bottom       = ⊆-ø
  `⊆`-sound refl           = ⊆-refl
  `⊆`-sound (trans x y)    = ⊆-trans (`⊆`-sound x) (`⊆`-sound y)
  `⊆`-sound (cong-↑1 x)    = ⊆-cong-↑1 (`⊆`-sound x)
  `⊆`-sound (↑1-inj x)     = ⊆-↑1-inj (`⊆`-sound x)
  `⊆`-sound (cong-+1 x)    = ⊆-cong-+1 (`⊆`-sound x)
  `⊆`-sound (+1-inj x)     = ⊆-+1-inj (`⊆`-sound x)
  `⊆`-sound +1↑1           = ⊆-+1↑1
  `⊆`-sound (unctx-+1↑1 x) = ⊆-unctx-+1↑1 (`⊆`-sound x)
  `⊆`-sound ø+1`⊆`ø       = ø+1⊆ø

  `⊈`-sound : ∀ {α β} → α `⊈` β → α ⊈ β
  `⊈`-sound ↑1`⊈`ø                 = ↑1⊈ø
  `⊈`-sound ↑1`⊈`+1                = ↑1⊈+1
  `⊈`-sound (cong-+1 α⊈β)          = ⊈-cong-+1 (`⊈`-sound α⊈β)
  `⊈`-sound (cong-↑1 α⊈β)          = ⊈-cong-↑1 (`⊈`-sound α⊈β)
  `⊈`-sound (ctx-+1↑1 α⊈β)         = ⊈-ctx-+1↑1 (`⊈`-sound α⊈β)
  `⊈`-sound (inj-+1 α+1⊈β+1)       = ⊈-inj-+1 (`⊈`-sound α+1⊈β+1)
  `⊈`-sound (inj-↑1 α↑1⊈β↑1)       = ⊈-inj-↑1 (`⊈`-sound α↑1⊈β↑1)
  `⊈`-sound (unctx-+1↑1 α+1⊈β↑1)   = ⊈-unctx-+1↑1 (`⊈`-sound α+1⊈β↑1)
  `⊈`-sound (α`⊈`ø→α+1`⊈`ø α⊈ø)    = α⊈ø→α+1⊈ø (`⊈`-sound α⊈ø)
  `⊈`-sound (α+1`⊈`ø→α`⊈`ø α+1⊈ø)  = α+1⊈ø→α⊈ø (`⊈`-sound α+1⊈ø)

  `⊈`-elim : ∀ {α β} → α `⊈` β → ¬(α `⊆` β)
  `⊈`-elim x y = ⊈-elim (`⊈`-sound x) (`⊆`-sound y)

  module Consquences where
    `⊈`-irrefl : ∀ {α} → ¬(α `⊈` α)
    `⊈`-irrefl x = `⊈`-elim x refl
    ¬+1`⊈`↑1 : ∀ {α} → ¬(α +1 `⊈` α ↑1)
    ¬+1`⊈`↑1 x = `⊈`-elim x +1↑1
    `⊈`-elim-bottom : ∀ {α} → ¬(ø `⊈` α)
    `⊈`-elim-bottom x = `⊈`-elim x ø-bottom

  open Complete minimalSymantics public renaming (⊆-complete to `⊆`-complete)

`⊆`-pack : ⊆-Pack listBoolWorlds
`⊆`-pack = record { _⊆_ = _`⊆`_
                  ; _⊈_ = _`⊈`_
                  ; ⊈-elim = `⊈`-elim
                  ; ⊆-symantics = `⊆`-symantics
                  ; ⊈-symantics = `⊈`-symantics }
  where
    open SyntacticOnBools ⊆ᵇ-pack

module Decidable (⊆-pack : ⊆-Pack listBoolWorlds) where
  open ⊆-Pack ⊆-pack

  dec⊆ : ∀ xs ys → Dec (xs ⊆ ys)
  dec⊆ []           ys           = yes ⊆-ø
  dec⊆ (true ∷ _)   []           = no (⊈-elim ↑1⊈ø)
  dec⊆ (false ∷ xs) []           = map′ α⊆ø→α+1⊆ø α+1⊆ø→α⊆ø (dec⊆ xs [])
  dec⊆ (true ∷ xs)  (true ∷ ys)  = map′ ⊆-cong-↑1 ⊆-↑1-inj (dec⊆ xs ys)
  dec⊆ (true ∷ xs)  (false ∷ ys) = no (⊈-elim ↑1⊈+1)
  dec⊆ (false ∷ xs) (true ∷ ys)  = map′ ⊆-ctx-+1↑1 ⊆-unctx-+1↑1 (dec⊆ xs ys)
  dec⊆ (false ∷ xs) (false ∷ ys) = map′ ⊆-cong-+1 ⊆-+1-inj (dec⊆ xs ys)

module Decidable⊆ where
  open Decidable ⊆ᵇ-pack public
  open ListBoolWorlds using (_∉_)
  decEmpty? : ∀ xs → Dec (∀ x → x ∉ xs)
  decEmpty? xs = dec⊆ xs []

module ⊆? where
  open ListBoolWorlds using (World; _∈_) renaming (listBoolWorlds to worldSym)
  open WorldSymantics worldSym

  empty? : (α : World) → Bool
  empty? []        = true
  empty? (x ∷ xs)  = not x ∧ empty? xs

  _⊆?_ : (α β : World) → Bool
  []        ⊆? _         = true
  (x ∷ xs)  ⊆? []        = not x ∧ xs ⊆? []
  (x ∷ xs)  ⊆? (y ∷ ys)  = (not x ∨ y) ∧ xs ⊆? ys

  T⊆? : (α β : World) → Set
  T⊆? α β = T (α ⊆? β)

  T⊈? : (α β : World) → Set
  T⊈? α β = T (not (α ⊆? β))

  empty?-⊆ø : ∀ {α} → T (empty? α) → T (α ⊆? ø)
  empty?-⊆ø {[]}           = _
  empty?-⊆ø {true   ∷ _}   = λ()
  empty?-⊆ø {false  ∷ xs}  = empty?-⊆ø {xs}

  ⊆ø⇒empty? : ∀ {α} → T (α ⊆? ø) → T (empty? α)
  ⊆ø⇒empty? {[]}           = _
  ⊆ø⇒empty? {true   ∷ _}   = λ()
  ⊆ø⇒empty? {false  ∷ xs}  = ⊆ø⇒empty? {xs}

  empty?-empty?+1 : ∀ {α} → T (empty? α) → T (empty? (α +1))
  empty?-empty?+1 {[]}     = id
  empty?-empty?+1 {_ ∷ _}  = id

  empty?α-α⊆β : ∀ {α β} → T (empty? α) → T (α ⊆? β)
  empty?α-α⊆β {[]}                   = _
  empty?α-α⊆β {true   ∷ _}           = λ()
  empty?α-α⊆β {false  ∷ xs} {[]}     = empty?α-α⊆β {xs}
  empty?α-α⊆β {false  ∷ xs} {_ ∷ _}  = empty?α-α⊆β {xs}

  α⊆?ø→α+1⊆?β : ∀ {α β} → T (α ⊆? ø) → T (α +1 ⊆? β)
  α⊆?ø→α+1⊆?β {xs} {ys} = empty?α-α⊆β {false ∷ xs} {ys}
                         ∘ empty?-empty?+1 {xs}
                         ∘ ⊆ø⇒empty? {xs}

{-
  ⊆?-pack : ⊆-Pack listBoolWorlds
  ⊆?-pack = record { _⊆_ = T⊆?
                  ; _⊈_ = {!_`⊈`_!}
                  ; ⊈-elim = {!`⊈`-elim!}
                  ; ⊆-symantics = ⊆?-symantics
                  ; ⊈-symantics = {!`⊈`-symantics!} }
--  where
--    open SyntacticOnBools ⊆ᵇ-pack
-}

  ⊆?-minimalSymantics : MinimalSymantics worldSym T⊆?
  ⊆?-minimalSymantics = record {
                          ⊆-ø = λ {_} → _;
                          ⊆-cong-↑1 = id;
                          ⊆-cong-+1 = id;
                          ⊆-ctx-+1↑1 = id;
                          α⊆ø→α+1⊆β = λ {α} {β} η → α⊆?ø→α+1⊆?β {α} {β} η }

  module ⊆?-Sound {_⊆_} (⊆-symantics : ⊆-Symantics listBoolWorlds _⊆_) where
    open ⊆-Symantics ⊆-symantics hiding (minimalSymantics)

    ⊆?-sound : ∀ {α β} → T (α ⊆? β) → α ⊆ β
    ⊆?-sound {[]}                          = λ _ → ⊆-ø
    ⊆?-sound {false  ∷ xs}  {[]}           = α⊆ø→α+1⊆ø  ∘ ⊆?-sound {xs} {[]}
    ⊆?-sound {false  ∷ xs}  {true   ∷ ys}  = ⊆-ctx-+1↑1  ∘ ⊆?-sound {xs} {ys}
    ⊆?-sound {false  ∷ xs}  {false  ∷ ys}  = ⊆-cong-+1   ∘ ⊆?-sound {xs} {ys}
    ⊆?-sound {true   ∷ xs}  {true   ∷ ys}  = ⊆-cong-↑1   ∘ ⊆?-sound {xs} {ys}
    ⊆?-sound {true   ∷ xs}  {false  ∷ ys}  = λ()
    ⊆?-sound {true   ∷ xs}  {[]}           = λ()

  module ⊆?-Complete (⊆ᵇ-pack : ⊆-Pack listBoolWorlds) where
    open Complete ⊆?-minimalSymantics ⊆ᵇ-pack public renaming (⊆-complete to ⊆?-complete)

  open ⊆?-Sound     (⊆-Pack.⊆-symantics ⊆ᵇ-pack) public
  open ⊆?-Complete  ⊆ᵇ-pack public

  ⊆?-symantics : ⊆-Symantics worldSym T⊆?
  ⊆?-symantics = record {
                   ⊆-ø = _;
                   ⊆-refl = λ {η} → refl {η};
                   ⊆-trans = λ {η₁} → trans {η₁};
                   ⊆-cong-↑1 = id;
                   ⊆-cong-+1 = id;
                   ⊆-+1↑1 = λ {x} → refl {x};
                   ⊆-↑1-inj = id;
                   ⊆-+1-inj = id;
                   ⊆-unctx-+1↑1 = id;
                   ø+1⊆ø = _ } where
    refl : ∀ {α} → T (α ⊆? α)
    refl {α} = ⊆?-complete {α} {α} (λ _ x → x)

    trans : Transitive T⊆?
    trans {xs} {ys} {zs} p q =  ⊆?-complete {xs} {zs} (λ _ r → ⊆?-sound {ys} {zs} q _ (⊆?-sound {xs} {ys} p _ r))
{-
    trans {[]}                                         = _
    trans {true   ∷  _}  {[]}                          = λ()
    trans {true   ∷  _}  {false  ∷  _}                 = λ()
    trans {_      ∷  _}  {true   ∷  _}  {[]}           = λ _ ()
    trans {_      ∷  _}  {true   ∷  _}  {false  ∷ _}  = λ _ ()
    trans {false  ∷ xs}  {[]}           {zs}           = λ x _ → α⊆?ø→α+1⊆?β {xs} {zs} x
    trans {false  ∷ xs}  {false  ∷ ys}  {[]}           = trans {xs} {ys} {[]}
    trans {true   ∷ xs}  {true   ∷ ys}  {true   ∷ zs}  = trans {xs} {ys} {zs}
    trans {false  ∷ xs}  {true   ∷ ys}  {true   ∷ zs}  = trans {xs} {ys} {zs}
    trans {false  ∷ xs}  {false  ∷ ys}  {_      ∷ zs}  = trans {xs} {ys} {zs}
-}

  -- module ⊆?-Decidable = Decidable ⊆?-pack
