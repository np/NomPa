module NomPa.Worlds where

open import Data.Nat.NP       using (ℕ; zero; suc; pred)
                              renaming (_+_ to _+ℕ_; _==_ to _==ℕ_)
open import Data.List         using (List; []; _∷_; replicate; _++_; foldr; map)
open import Data.Bool         using (Bool; true; false; if_then_else_)
open import Data.Empty        using (⊥)
open import Data.Unit         using (⊤)
open import Function          using (id)
open import Relation.Nullary  using (¬_)
open import Relation.Binary.PropositionalEquality as ≡

record WorldSymantics (W : Set) : Set where
  infix 21 _↑1 _+1
  field
    ø : W
    _↑1 _+1 : (α : W) → W

  _^1 : (α : W) → W
  _^1 = _↑1

  Abs : (α : W) → W
  Abs = _↑1

module WorldOps {World} (Wsym : WorldSymantics World) where
  open WorldSymantics Wsym

  infixl 6 _↑_ _+ᵂ_

  _+ᵂ_ : World → ℕ → World
  α +ᵂ 0     = α
  α +ᵂ suc n = (α +ᵂ n)+1

  _↑_ : World → ℕ → World
  α ↑ 0     = α
  α ↑ suc n = (α ↑ n)↑1

{-
  fromBool : Bool → World → World
  fromBool true  x = x ↑1
  fromBool false x = x +1
-}

  fromBool : Bool → World → World
  fromBool true  = _↑1
  fromBool false = _+1

  fromBools : List Bool → World
  fromBools = foldr fromBool ø

{-
  fromBools : List Bool → World
  fromBools [] = ø
  fromBools (x ∷ xs) = fromBool x (fromBools xs)

  fromBools : List Bool → World
  fromBools [] = ø
  fromBools (true  ∷ xs) = fromBools xs ↑1
  fromBools (false ∷ xs) = fromBools xs +1

  test : fromBool _ ø ≡ ø ↑1
  test = ≡.refl

  tests : fromBools _ ≡ ø ↑1
  tests = ≡.refl
-}

module ListBoolSpecialized where
  infixl 6 _↑_

  World : Set
  World = List Bool

  _+ᵂ_ : World → ℕ → World
  α +ᵂ k = replicate k false ++ α
     -- {(i+k,j+k) | (i,j) ∈ α}

  _↑_ : World → ℕ → World
  α ↑ k = replicate k true ++ α
  -- {(i,i) | i ∈ 0 .. k-1 } ∪ α :+ k

module ℕ★ where
  World : Set
  World = List ℕ

  ℕ★ : WorldSymantics World
  ℕ★ = record { ø = []; _↑1 = λ α → 0 ∷ map suc α; _+1 = map suc }

  open WorldSymantics ℕ★ public

module ListBoolWorlds where
  World : Set
  World = List Bool

  listBoolWorlds : WorldSymantics (List Bool)
  listBoolWorlds = record { ø = ø; _↑1 = _↑1; _+1 = _+1 }
   where
    ø : World
    ø = []

    _+1 : World → World
    α +1 = false ∷ α

    _↑1 : World → World
    α ↑1 = true ∷ α

  _∈_ : ℕ → World → Set
  _      ∈ []            = ⊥
  zero   ∈ (false ∷ _)   = ⊥
  zero   ∈ (true  ∷ _)   = ⊤
  suc n  ∈ (_     ∷ xs)  = n ∈ xs

  _∉_ : ℕ → World → Set
  x ∉ α = ¬(x ∈ α)
  infix 2 _∈_ _∉_

  ∈-uniq : ∀ {x} α (p q : x ∈ α) → p ≡ q
  ∈-uniq         []            ()  _
  ∈-uniq {zero}  (false ∷ xs)  ()  _
  ∈-uniq {zero}  (true ∷ xs)   _   _ = ≡.refl
  ∈-uniq {suc n} (_ ∷ xs)      p   q = ∈-uniq {n} xs p q

  infix 2 _⊆_
  _⊆_ : (α β : World) → Set
  α ⊆ β = ∀ x → x ∈ α → x ∈ β

  infix 2 _⊈_
  _⊈_ : ∀ (α β : World) → Set
  α ⊈ β = ¬(α ⊆ β)

  infix 2 _⊆′_
  record _⊆′_ (α β : List Bool) : Set where
    constructor mk
    field
      coe : ∀ x → x ∈ α → x ∈ β
  open _⊆′_ public

  infix 2 _⊈′_
  _⊈′_ : ∀ (α β : World) → Set
  α ⊈′ β = ¬(α ⊆′ β)

  toℕ★ : List Bool → List ℕ
  toℕ★ []           = []
  toℕ★ (true  ∷ bs) = 0 ∷ map suc (toℕ★ bs)
  toℕ★ (false ∷ bs) = map suc (toℕ★ bs)

  private
   module Unused where
    open WorldSymantics listBoolWorlds
    open WorldOps listBoolWorlds
    x∉ø+ : ∀ x k → x ∉ (ø +ᵂ k)
    x∉ø+ zero    zero ()
    x∉ø+ (suc _) zero ()
    x∉ø+ zero (suc k) ()
    x∉ø+ (suc n) (suc k) pf = x∉ø+ n k pf

    ∈false∷ : ∀ x {xs} → x ∈ false ∷ xs → pred x ∈ xs
    ∈false∷ zero     = λ()
    ∈false∷ (suc n)  = id

  module Nominal where
    _◅_ : ℕ → World → World
    zero  ◅ []      = true  ∷ []
    suc n ◅ []      = false ∷ n ◅ []
    zero  ◅ (_ ∷ α) = true  ∷ α
    suc n ◅ (b ∷ α) = b     ∷ n ◅ α

    infixr 5 _◅_

    ◅-sem : ∀ α x y → (x ∈ y ◅ α) ≡ (if x ==ℕ y then ⊤ else x ∈ α)
    ◅-sem [] zero zero = ≡.refl
    ◅-sem [] zero (suc _) = ≡.refl
    ◅-sem [] (suc _) zero = ≡.refl
    ◅-sem (true ∷ _) zero (suc _) = ≡.refl
    ◅-sem (false ∷ _) zero (suc _) = ≡.refl
    ◅-sem (_ ∷ _) (suc _) zero = ≡.refl
    ◅-sem (_ ∷ _) zero zero = ≡.refl
    ◅-sem [] (suc x) (suc y) = ◅-sem [] x y
    ◅-sem (_ ∷ α) (suc x) (suc y) = ◅-sem α x y

    -- a consequence of ◅-sem
    b∈b◅ : ∀ b α → b ∈ (b ◅ α)
    b∈b◅ zero    []       = _
    b∈b◅ zero    (x ∷ xs) = _
    b∈b◅ (suc n) []       = b∈b◅ n []
    b∈b◅ (suc n) (x ∷ xs) = b∈b◅ n xs
