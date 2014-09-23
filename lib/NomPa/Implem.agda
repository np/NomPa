module NomPa.Implem where

open import Data.Bool
open import Data.Maybe.NP
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ hiding (subst)
open import Data.List
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Bool.NP using (If′_then_else_; If-map; If-false)
open import Function.NP hiding (_→⟨_⟩_) renaming (_→⟨_⟩₀_ to _→⟨_⟩_)
import Data.Nat.NP as ℕ
open ℕ renaming (_==_ to _==ℕ_)
import Data.Nat.Properties as ℕ
open import Algebra
open import NomPa.Record
open import Function.Equivalence using (Equivalence;_⇔_;equivalence)

import NaPa
import NomPa.Worlds

open NaPa public using (World; _∈_; _∉_; Name; ø; coerceᴺ; ⊆-refl; ⊆-trans; ⊆-ø; _⊆_; _==ᴺ_;
                        ⊆-cong-↑1; ⊆-cong-+1; ⊆-+1↑1; ⊆-↑1-inj; ⊆-+1-inj;
                        ⊆-unctx-+1↑1; ø+1⊆ø; addᴺ; subtractᴺ; cmpᴺ)
open NomPa.Worlds.ListBoolWorlds.Nominal public using (_◅_; b∈b◅; ◅-sem)

module Internals where
  open NaPa public using (_,_; mk; coe; _↑1; _+1) renaming (name to binderᴺ; name∈α to binderᴺ∈α)
  open NomPa.Worlds.ListBoolWorlds public using (toℕ★)

  Binder : Set
  Binder = ℕ

  infix 2 _#_

  nameᴮ : ∀ {α} (b : Binder) → Name (b ◅ α)
  nameᴮ {α} b = b , b∈b◅ b α

  export∈ : ∀ α x y → T (not (x ==ℕ y)) → x ∈ y ◅ α → x ∈ α
  export∈ α x y prf = ≡.subst id (≡.trans (◅-sem _ x y) (If-false prf))

  -- unexported
  safeExport : ∀ {α} (b : Binder) (x : Name (b ◅ α)) {prf : T (not (x ==ᴺ nameᴮ b))} → Name α
  safeExport {α} b (x , x∈b◅α) {prf} = x , export∈ α _ _ prf x∈b◅α

  exportᴺ? : ∀ {b α} → Name (b ◅ α) →? Name α
  exportᴺ? {b} {α} (x , x∈) with x ==ℕ b | export∈ α x b
  ... | true  | _ = nothing
  ... | false | f = just (x , f _ x∈)

  ¬Nameø : ¬ (Name ø)
  ¬Nameø (_ , ())

  zeroᴮ : Binder
  zeroᴮ = zero

  sucᴮ : Binder → Binder
  sucᴮ = suc

  data _#_ : Binder → World → Set where
    _#ø   : ∀ b → b # ø
    suc#∷ : ∀ {bool α b} → (b#α : b # α) → suc b # (bool ∷ α)
    0#_   : ∀ {α} → (0#α : 0 # α) → 0 # (α +1)

  _#-Sem_ : Binder → World → Set
  x #-Sem α = ∀ y → y ∈ α → x > y

  -- This syntactic definition is sound and complete for closed worlds
  #⇔#-Sem : ∀ {x α} → (x # α) ⇔ (x #-Sem α)
  #⇔#-Sem = equivalence (⇒) (⇐ _ _)
    where 0#ø : ∀ {α} → 0 # α → (∀ y → y ∉ α)
          0#ø (.0 #ø) y pf = pf
          0#ø (0# 0#α) zero ()
          0#ø (0# 0#α) (suc y) pf = 0#ø 0#α y pf

          1≰0 : ¬(1 ≤ 0)
          1≰0 ()

          ⇒ : ∀ {x α} → x # α → (x #-Sem α)
          ⇒ (_ #ø) _ ()
          ⇒ (suc#∷ {true}  b#α) zero _ = s≤s z≤n
          ⇒ (suc#∷ {false} b#α) zero ()
          ⇒ (suc#∷ b#α) (suc y) pf = s≤s (⇒ b#α y pf)
          ⇒ (0# 0#α) zero ()
          ⇒ (0# 0#α) (suc y) pf = ⊥-elim (0#ø 0#α y pf)

          ⇐ : ∀ x α → (x #-Sem α) → x # α
          ⇐ x       []           _  = x #ø
          ⇐ zero    (true  ∷ _)  pf = ⊥-elim (1≰0 (pf 0 _))
          ⇐ zero    (false ∷ α)  pf = 0# (⇐ zero α (λ y → ≤-pred ∘ ℕ.≤-step ∘ pf (suc y)))
          ⇐ (suc n) (_     ∷ α)  pf = suc#∷ (⇐ n α (λ y → ≤-pred ∘ pf (suc y)))

  suc# : ∀ {α b} → b # α → suc b # (b ◅ α)
  suc# (zero  #ø) = suc#∷ (zero #ø)
  suc# (suc b #ø) = suc#∷ (suc# (b #ø))
  suc# (suc#∷ pf) = suc#∷ (suc# pf)
  suc# (0# pf)    = suc#∷ pf

  _∈_◅′_ : Binder → Binder → World → Set
  x ∈ b ◅′ α = if x ==ℕ b then ⊤ else x ∈ α

  ⊆-◅ : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β)
  ⊆-◅ {α} {β} b (mk α⊆β) = mk pf
   where
    pf′ : ∀ x → x ∈ b ◅′ α → x ∈ b ◅′ β
    pf′ x with x ==ℕ b
    ... | true = id
    ... | false = α⊆β _
    pf : ∀ x → x ∈ b ◅ α → x ∈ b ◅ β
    pf x = ≡.subst id (≡.sym (◅-sem _ x b)) ∘ pf′ x ∘ ≡.subst id (◅-sem _ x b)

  -- The b # β is not used here. It is necessary for the logical relation proof, though.
  ⊆-# : ∀ {α b} → b # α → α ⊆ (b ◅ α)
  ⊆-# {α} {b} _ = mk (λ b′ b′∈α → ≡.subst id (≡.sym (◅-sem α b′ b)) (If′ ℕ._==_ b′ b then _ else b′∈α))

  ⊆-dist-+1-◅ : ∀ {α} b → (b ◅ α) +1 ⊆ (sucᴮ b) ◅ (α +1)
  ⊆-dist-+1-◅ _ = ⊆-refl

  ⊆-dist-◅-+1 : ∀ {α} b → (sucᴮ b) ◅ (α +1) ⊆ (b ◅ α) +1
  ⊆-dist-◅-+1 _ = ⊆-refl

  binderᴺ∘nameᴮ : ∀ α b → binderᴺ (nameᴮ {α} b) ≡ b
  binderᴺ∘nameᴮ _ _ = ≡.refl

{-
  ifᴮ_==_then_else_ : (x y if-x≡y if-x≢y : Binder) → Binder
  ifᴮ x == y then z else t = if x ==ℕ y then z else t

  Perm : Set
  Perm = List (Binder × Binder)

  ⟨_,_⟩●ᴮ_ : (x y : Binder) → Binder → Binder
  ⟨_,_⟩●ᴮ_ = λ x y z →
    ifᴮ z == x then y
    else ifᴮ z == y then x
    else z

  _●ᴮ_ : Perm → Binder → Binder
  _●ᴮ_ = λ π z → foldr (uncurry ⟨_,_⟩●ᴮ_) z π

{-
  ⟨_,_⟩●ᵂ_ : Binder → Binder → World → World
  ⟨ _ , _ ⟩●ᵂ [] = []
  ⟨ zero , y ⟩●ᵂ (true  ∷ bs) = y ◅ bs
  ⟨ zero , y ⟩●ᵂ (false ∷ bs) = bs
  ⟨ x , zero ⟩●ᵂ (true  ∷ bs) = x ◅ bs
  ⟨ x , zero ⟩●ᵂ (false ∷ bs) = bs
  ⟨ suc x , suc y ⟩●ᵂ (b ∷ bs) = b ∷ ⟨ x , y ⟩●ᵂ bs
-}

  _●ᵂ_ : Perm → World → World
  -- π ●ᵂ α = foldr (uncurry ⟨_,_⟩●ᵂ_) α π
  π ●ᵂ α = foldr _◅_ ø (map (_●ᴮ_ π) (toℕ★ α))

  ●ø : ∀ π → π ●ᵂ ø ≡ ø
  ●ø _ = refl

  _+1π : Perm → Perm
  _+1π = map suc² where
    suc² : ℕ × ℕ → ℕ × ℕ
    suc² (x , y) = (suc x , suc y)

  ●+1 : ∀ {π α} → (π +1π) ●ᵂ (α +1) ≡ (π ●ᵂ α) +1
  ●+1 {π} {α} = go α where
    go : ∀ α → (π +1π) ●ᵂ (α +1) ≡ (π ●ᵂ α) +1
    go [] = {!!}
    go (x ∷ xs) = {!!}

  ●◅ : ∀ {π α b} → π ●ᵂ (b ◅ α) ≡ (π ●ᴮ b) ◅ (π ●ᵂ α)
  ●◅ = {!!}

    -- ●+1
    -- ●↑1
  ●∈ : ∀ π b α → b ∈ α → (π ●ᴮ b) ∈ (π ●ᵂ α)
  ●∈ π = go where
    go : ∀ b α → b ∈ α → (π ●ᴮ b) ∈ (π ●ᵂ α)
    go _ [] ()
    go zero (true ∷ xs) pf' = {!!}
    go zero (false ∷ xs) ()
    go (suc n) (b ∷ α) pf' = {!go n α ?!}

  _●ᴺ_ : ∀ {α} π → Name α → Name (π ●ᵂ α)
  _●ᴺ_ {α} π (b , pf) = (π ●ᴮ b , ●∈ π b α pf)
-}

nomPa : NomPa
nomPa = mk World Name Binder _◅_
           zeroᴮ sucᴮ nameᴮ binderᴺ ø ¬Nameø _==ᴺ_ (λ {b} → exportᴺ? {b})
           _#_ _#ø suc# _⊆_ coerceᴺ
           ⊆-refl ⊆-trans ⊆-ø ⊆-◅ ⊆-#
           _+1
           ⊆-cong-↑1 ⊆-cong-+1 ⊆-+1↑1 ⊆-↑1-inj ⊆-+1-inj ⊆-unctx-+1↑1 ø+1⊆ø
           ⊆-dist-+1-◅ ⊆-dist-◅-+1 binderᴺ∘nameᴮ
           addᴺ subtractᴺ cmpᴺ {-ifᴮ_==_then_else_ _●ᵂ_ ●ø (λ {η} → ●◅ {η}) _●ᴺ_-}
  where open Internals

{- wrong things

x ◅ α ⊆ y ◅ β ≢ sucᴮ x ◅ α ⊆ sucᴮ y ◅ β

-}
