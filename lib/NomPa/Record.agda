{-# OPTIONS --universe-polymorphism #-}
module NomPa.Record where

open import Function         using (_∘′_; _∘_; id; const)
open import Data.Nat         using (ℕ; zero; suc)
open import Data.Sum         using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Bool        using (Bool)
open import Data.List        using (List; foldr)
open import Data.Product     using (_×_; uncurry)
open import Data.Maybe.NP    using (maybe; _→?_; just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary  using (Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import NomPa.Worlds
open import NomPa.Subtyping using (⊆-Symantics)

_^ⁿ_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
f ^ⁿ 0     = id
f ^ⁿ suc n = f ∘ (f ^ⁿ n)

-- minimal kit to define types
record DataKit : Set₁ where
 constructor mk

 infixr 5 _◅_

 field
  World  : Set
  Name   : World → Set
  Binder : Set
  _◅_   : Binder → World → World

record NomPa : Set₁ where
 constructor mk

 infix 3 _⊆_
 infix 2 _#_
 infixr 5 _◅_

 field
  -- minimal kit to define types
  World  : Set
  Name   : World → Set
  Binder : Set
  _◅_   : Binder → World → World

  -- An infinite set of binders
  zeroᴮ : Binder
  sucᴮ  : Binder → Binder
  -- laws: we may want to say that zeroᴮ and sucᴮ are not phony

  nameᴮ : ∀ {α} b → Name (b ◅ α)
  binderᴺ : ∀ {α} → Name α → Binder
  -- nameᴮ-binderᴺ : ∀ {α} b → binderᴺ (nameᴮ {α} b) ≡ b
  -- NOTE: we already have a binderᴺ∘nameᴮ later on

  -- There is no name in the empty world
  ø      : World
  ¬Nameø : ¬(Name ø)

  -- Names are comparable and exportable
  _==ᴺ_      : ∀ {α} (x y : Name α) → Bool
  -- ==ᴺ-binderᴺ : ∀ {α} (x₁ x₂ : Name α) →
  --                 binderᴺ x₁ ≡ binderᴺ x₂ ⇔ (x₁ ==ᴺ x₂) ≡ true
  exportᴺ?   : ∀ {b α} → Name (b ◅ α) →? Name α
  -- exportᴺ?-binderᴺ : ∀ {b α} (x : Name α) →
  --                      map? binderᴺ (exportᴺ? x)
  --                    ≡ if nameᴮ b ==ᴺ x then nothing else just b

  -- The fresh-for relation
  _#_  : Binder → World → Set
  _#ø  : ∀ b → b # ø
  suc# : ∀ {b α} → b # α → (sucᴮ b) # (b ◅ α)
  -- TODO
  -- suc#◅  : ∀ {b α} → b # α → (sucᴮ b) # (b ◅ α)
  -- suc#+1 : ∀ {b α} → b # α → (sucᴮ b) # (α +1)
  --
  -- more ideas:
  -- suc#  : ∀ {b α} → b # α → (sucᴮ b) # (b ◅ (α +1))
  -- + => b₁ # b₂ ◅ α → b₁ # α
  -- and ...
  --
  -- #-◅ : ∀ b₁ b₂ α → b₁ #ᴮ b₂ → b₁ # α → b₁ # b₂ ◅ α
  -- with:
  -- _#ᴮ_ : Binder → Binder → Set
  -- and:
  -- z#s : ∀ b → zeroᴮ #ᴮ sucᴮ b
  -- s#z : ∀ b → sucᴮ b #ᴮ zeroᴮ
  -- s#s : ∀ b₁ b₂ → b₁ #ᴮ b₂ → sucᴮ b₁ #ᴮ sucᴮ b₂
  -- #ᴮ-# : ∀ b₁ b₂ → b₁ #ᴮ b₂ ↔ b₁ # (b₂ ◅ ø)

  -- inclusion between worlds
  _⊆_     : World → World → Set
  coerceᴺ  : ∀ {α β} → (α ⊆ β) → (Name α → Name β)
  -- coerceᴺ-binderᴺ : ∀ {α β} (pf : α ⊆ β) x → binderᴺ (coerceᴺ pf x) ≡ binderᴺ x
  ⊆-refl  : Reflexive _⊆_
  ⊆-trans : Transitive _⊆_
  ⊆-ø     : ∀ {α} → ø ⊆ α
  ⊆-◅     : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β)
  ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◅ α)

 field
   _+1 : World → World

 _↑1 : World → World
 _↑1 α = zeroᴮ ◅ (α +1)

 worldSym : WorldSymantics World
 worldSym = record { ø = ø; _↑1 = _↑1; _+1 = _+1 }

 field
    -- TODO derivable
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

 -- Combination of +1 and ◅
 field
    ⊆-dist-+1-◅ : ∀ {α} b → (b ◅ α) +1 ⊆ (sucᴮ b) ◅ (α +1)

    ⊆-dist-◅-+1 : ∀ {α} b → (sucᴮ b) ◅ (α +1) ⊆ (b ◅ α) +1

 field
    binderᴺ∘nameᴮ : ∀ α b → binderᴺ (nameᴮ {α} b) ≡ b

 open WorldOps worldSym
{-
 infixl 6 _↑_ _+ᵂ_

 _+ᵂ_ : World → ℕ → World
 _+ᵂ_ α n = (_+1 ^ⁿ n) α
{-
 α +ᵂ 0     = α
 α +ᵂ suc n = (α +ᵂ n)+1
-}

 _↑_ : World → ℕ → World
 _↑_ α n = (_↑1 ^ⁿ n) α
{-
 α ↑ 0     = α
 α ↑ suc n = (α ↑ n)↑1
-}
-}

 ⊆-symantics : ⊆-Symantics worldSym _⊆_
 ⊆-symantics = record {
                ⊆-ø = ⊆-ø;
                ⊆-refl = ⊆-refl;
                ⊆-trans = ⊆-trans;
                ⊆-cong-↑1 = ⊆-cong-↑1;
                ⊆-cong-+1 = ⊆-cong-+1;
                ⊆-+1↑1 = ⊆-+1↑1;
                ⊆-↑1-inj = ⊆-↑1-inj;
                ⊆-+1-inj = ⊆-+1-inj;
                ⊆-unctx-+1↑1 = ⊆-unctx-+1↑1;
                ø+1⊆ø = ø+1⊆ø }

 field
    addᴺ      : ∀ {α} k → Name α → Name (α +ᵂ k)
    -- addᴺ-binderᴺ : ∀ {α} k (x : Name α) → binderᴺ (addᴺ k x) ≡ binderᴺ x +ᴮ k
    subtractᴺ : ∀ {α} k → Name (α +ᵂ k) → Name α
    -- subtractᴺ-binderᴺ : ∀ {α} k (x : Name (α +ᵂ k)) → binderᴺ (subtractᴺ k x) +ᴮ k ≡ binderᴺ x
    -- OR addᴺ-subtractᴺ : subtractᴺ (addᴺ x k) k
    cmpᴺ      : ∀ {α} k → Name (α ↑ k) → Name (ø ↑ k) ⊎ Name (α +ᵂ k)
    -- cmpᴺ-binderᴺ : ∀ {α} k (x : Name (α ↑ k)) →
    --                  [ binderᴺ , binderᴺ ] (cmpᴺ k x) ≡ binderᴺ x
    -- The bit of information is not reflected in the spec.

{-
 field
    ifᴮ_==_then_else_ : (x y if-x≡y if-x≢y : Binder) → Binder

 Perm : Set
 Perm = List (Binder × Binder)

 ⟨_,_⟩●ᴮ_ : (x y : Binder) → Binder → Binder
 ⟨_,_⟩●ᴮ_ = λ x y z →
   ifᴮ z == x then y
   else ifᴮ z == y then x
   else z

 _●ᴮ_ : Perm → Binder → Binder
 _●ᴮ_ = λ π z → foldr (uncurry ⟨_,_⟩●ᴮ_) z π

 field
    _●ᵂ_ : Perm → World → World
    ●ø   : ∀ π → π ●ᵂ ø ≡ ø
    ●◅  : ∀ {π α b} → π ●ᵂ (b ◅ α) ≡ (π ●ᴮ b) ◅ (π ●ᵂ α)
    -- ●+1
    -- ●↑1
    _●ᴺ_ : ∀ {α} π → Name α → Name (π ●ᵂ α)
-}

 infixl 6 addᴺ subtractᴺ
 infix 4 cmpᴺ
 syntax subtractᴺ k x = x ∸ᴺ k
 syntax addᴺ k x = x +ᴺ k
 syntax cmpᴺ k x = x <ᴺ k

 -- A few common derived definitions

 infix 100 _ᴺ _ᴮ

 -- From numbers to binders
 _ᴮ : ℕ → Binder
 zero  ᴮ = zeroᴮ
 suc n ᴮ = sucᴮ (n ᴮ)

 -- From numbers to names
 _ᴺ : ∀ {α} n → Name (n ᴮ ◅ α)
 n ᴺ = nameᴮ (n ᴮ)

 open ⊆-Symantics ⊆-symantics public using
  (⊆-cong-+; ⊆-cong-↑; ⊆-assoc-+′; ⊆-assoc-+; ⊆-assoc-↑; ⊆-assoc-↑′;
   ⊆-+-↑; ⊆-exch-+-+; ⊆-ctx-+↑;
   ⊆-ø+; ⊆-+-inj; ⊆-exch-↑-↑; ⊆-exch-↑-↑′)

 -- doc
 zeroᴺ : ∀ {α} → Name (α ↑1)
 zeroᴺ = nameᴮ (0 ᴮ)

 -- Proper refining of the world of a name
 exportᴺ : ∀ {b α} → Name (b ◅ α) → Name (b ◅ ø) ⊎ Name α
 exportᴺ = maybe inj₂ (inj₁ (nameᴮ _)) ∘′ exportᴺ?

 -- Handy name eliminator
 exportWith : ∀ {b a α} {A : Set a} → A → (Name α → A) → Name (b ◅ α) → A
 exportWith v f = maybe f v ∘′ exportᴺ?

 -- Convenient notation to put the proof details on the side
 infix 0 _⟨-because_-⟩
 _⟨-because_-⟩ : ∀ {α β} → Name α → (α ⊆ β) → Name β
 x ⟨-because α⊆β -⟩ = coerceᴺ α⊆β x

 -- Turns the emptyness problem into a world inclusion one
 ¬Name : ∀ {α} → (α ⊆ ø) → ¬(Name α)
 ¬Name α⊆ø = ¬Nameø ∘′ coerceᴺ α⊆ø

 -- Elimination form of ¬Name
 Name-elim : ∀ {a} {A : Set a} {α} (α⊆ø : α ⊆ ø) (x : Name α) → A
 Name-elim x y with ¬Name x y
 ... | ()

 -- Elimination form of ¬Nameø
 Nameø-elim : ∀ {a} {A : Set a} → Name ø → A
 Nameø-elim = Name-elim ⊆-refl

 sucᴺ : ∀ {α} → Name α → Name (α +1)
 sucᴺ = addᴺ 1

 sucᴺ↑ : ∀ {α} → Name α → Name (α ↑1)
 sucᴺ↑ = coerceᴺ ⊆-+1↑1 ∘ sucᴺ

 addᴺ↑ : ∀ {α} ℓ → Name α → Name (α ↑ ℓ)
 addᴺ↑ ℓ x = addᴺ ℓ x  ⟨-because ⊆-+-↑ ℓ -⟩

 predᴺ : ∀ {α} → Name (α +1) → Name α
 predᴺ = subtractᴺ 1

 -- Handy name eliminator
 subtractWithᴺ : ∀ {a α} {A : Set a} ℓ → A → (Name α → A) → Name (α ↑ ℓ) → A
 subtractWithᴺ ℓ v f x = [ const v , f ∘′ subtractᴺ ℓ ]′ (x <ᴺ ℓ)

 subtractᴺ? : ∀ {α} ℓ → Name (α ↑ ℓ) →? Name α
 subtractᴺ? ℓ = subtractWithᴺ ℓ nothing just

 predᴺ? : ∀ {α} → Name (α ↑1) →? Name α
 predᴺ? = subtractᴺ? 1

 protect↑1 : ∀ {α β} → (Name α → Name β) → (Name (α ↑1) → Name (β ↑1))
 protect↑1 f = subtractWithᴺ 1 zeroᴺ (sucᴺ↑ ∘ f)
   -- OR: exportWith (0 ᴺ) (sucᴺ↑ ∘ f ∘ predᴺ)

 -- Generalizes protect↑1 to any ℓ
 protect↑ : ∀ {α β} → (Name α → Name β) → ∀ ℓ → (Name (α ↑ ℓ) → Name (β ↑ ℓ))
 protect↑ f ℓ x  with x <ᴺ ℓ
 ... {- bound -} | inj₁ x′ = x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
 ... {- free  -} | inj₂ x′ = (addᴺ↑ ℓ ∘ f ∘ subtractᴺ ℓ) x′

 _+ᴮ_ : Binder → ℕ → Binder
 b +ᴮ zero  = b
 b +ᴮ suc n = sucᴮ (b +ᴮ n)

 dataKit : DataKit
 dataKit = mk World Name Binder _◅_

 open WorldOps worldSym public
