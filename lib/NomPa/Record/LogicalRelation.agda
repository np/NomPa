{-# OPTIONS --universe-polymorphism #-}
module NomPa.Record.LogicalRelation where

open import NomPa.Record
open import Relation.Binary.Logical
open import Relation.Binary.PropositionalEquality.NP
open import Data.Bool.NP
open import Data.Sum.NP
open import Data.Maybe.NP
open import Data.Nat.Logical
open import NomPa.Worlds
import Level as L

record ⟦DataKit⟧ ℓ (dataKit₁ dataKit₂ : DataKit) : Set (L.suc ℓ) where
 constructor mk

 module D₁ = DataKit dataKit₁
 module D₂ = DataKit dataKit₂
 infixr 5 _⟦◅⟧_

 field
  -- minimal kit to define types
  ⟦World⟧  : ⟦Set⟧ ℓ {-suc zero should we make it a parameter -} D₁.World D₂.World
  ⟦Name⟧   : ⟦Pred⟧ L.zero ⟦World⟧ D₁.Name D₂.Name
  ⟦Binder⟧ : ⟦Set₀⟧ D₁.Binder D₂.Binder
  _⟦◅⟧_   : (⟦Binder⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦World⟧) D₁._◅_ D₂._◅_

-- ⟦NomPa⟧ : ⟦Set₁⟧ NomPa NomPa where
record ⟦NomPa⟧ ℓ (nomPa₁ nomPa₂ : NomPa) : Set (L.suc ℓ) where
 constructor mk

 module N₁ = NomPa nomPa₁
 module N₂ = NomPa nomPa₂
 infix 3 _⟦⊆⟧_
 infix 2 _⟦#⟧_

 field
  -- minimal kit to define types
  ⟦World⟧  : ⟦Set⟧ ℓ {-suc zero should we make it a parameter -} N₁.World N₂.World
  ⟦Name⟧   : ⟦Pred⟧ L.zero ⟦World⟧ N₁.Name N₂.Name
  ⟦Binder⟧ : ⟦Set₀⟧ N₁.Binder N₂.Binder
  _⟦◅⟧_   : (⟦Binder⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦World⟧) N₁._◅_ N₂._◅_

  -- An infinite set of binders
  ⟦zeroᴮ⟧ : ⟦Binder⟧ N₁.zeroᴮ N₂.zeroᴮ
  ⟦sucᴮ⟧ : (⟦Binder⟧ ⟦→⟧ ⟦Binder⟧) N₁.sucᴮ N₂.sucᴮ

  ⟦nameᴮ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ)) N₁.nameᴮ N₂.nameᴮ
  ⟦binderᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Binder⟧) N₁.binderᴺ N₂.binderᴺ

  -- There is no name in the empty world
  ⟦ø⟧ : ⟦World⟧ N₁.ø N₂.ø
  ⟦¬Nameø⟧ : (⟦¬⟧(⟦Name⟧ ⟦ø⟧)) N₁.¬Nameø N₂.¬Nameø

  -- Names are comparable and exportable
  _⟦==ᴺ⟧_ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ αᵣ ⟦→⟧ ⟦Bool⟧) N₁._==ᴺ_ N₂._==ᴺ_
  ⟦exportᴺ?⟧ : (∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ ∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦→?⟧ ⟦Name⟧ αᵣ) N₁.exportᴺ? N₂.exportᴺ?

  -- The fresh-for relation
  _⟦#⟧_ : (⟦Binder⟧ ⟦→⟧ ⟦World⟧ ⟦→⟧ ⟦Set₀⟧) N₁._#_ N₂._#_
  _⟦#ø⟧ : (⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ bᵣ ⟦#⟧ ⟦ø⟧) N₁._#ø N₂._#ø
  ⟦suc#⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ bᵣ ⟦#⟧ αᵣ ⟦→⟧ (⟦sucᴮ⟧ bᵣ) ⟦#⟧ (bᵣ ⟦◅⟧ αᵣ)) N₁.suc# N₂.suc#

  -- inclusion between worlds
  _⟦⊆⟧_        : ⟦Rel⟧ ⟦World⟧ L.zero N₁._⊆_ N₂._⊆_

  ⟦coerceᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ βᵣ)) N₁.coerceᴺ N₂.coerceᴺ
  ⟦⊆-refl⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ αᵣ) N₁.⊆-refl N₂.⊆-refl
  ⟦⊆-trans⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ γᵣ ∶ ⟦World⟧ ⟩⟦→⟧
                  αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (βᵣ ⟦⊆⟧ γᵣ ⟦→⟧ (αᵣ ⟦⊆⟧ γᵣ))) N₁.⊆-trans N₂.⊆-trans
  ⟦⊆-ø⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦ø⟧ ⟦⊆⟧ αᵣ) N₁.⊆-ø N₂.⊆-ø
  ⟦⊆-◅⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦⊆⟧ (bᵣ ⟦◅⟧ βᵣ)) N₁.⊆-◅ N₂.⊆-◅
  ⟦⊆-#⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
           (bᵣ ⟦#⟧ αᵣ) ⟦→⟧ αᵣ ⟦⊆⟧ (bᵣ ⟦◅⟧ αᵣ)) N₁.⊆-# N₂.⊆-#

 field
   _⟦+1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) N₁._+1 N₂._+1

 _⟦↑1⟧ : (⟦World⟧ ⟦→⟧ ⟦World⟧) N₁._↑1 N₂._↑1
 _⟦↑1⟧ αᵣ = ⟦zeroᴮ⟧ ⟦◅⟧ (αᵣ ⟦+1⟧)

 -- ⟦worldSym⟧ : ⟦WorldSymantics⟧ ⟦World⟧ N₁.worldSym N₂.worldSym
 -- ⟦worldSym⟧ = record { ⟦ø⟧ = ⟦ø⟧; _⟦↑1⟧ = _⟦↑1⟧; _⟦+1⟧ = _⟦+1⟧ }

 field
    -- TODO derivable
    ⟦⊆-cong-↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧)) N₁.⊆-cong-↑1 N₂.⊆-cong-↑1

    ⟦⊆-cong-+1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ αᵣ ⟦⊆⟧ βᵣ ⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧)) N₁.⊆-cong-+1 N₂.⊆-cong-+1

    ⟦⊆-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (αᵣ ⟦↑1⟧)) N₁.⊆-+1↑1 N₂.⊆-+1↑1

    ⟦⊆-↑1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦↑1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) N₁.⊆-↑1-inj N₂.⊆-↑1-inj

    ⟦⊆-+1-inj⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦+1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) N₁.⊆-+1-inj N₂.⊆-+1-inj

    ⟦⊆-unctx-+1↑1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ∀⟨ βᵣ ∶ ⟦World⟧ ⟩⟦→⟧ (αᵣ ⟦+1⟧) ⟦⊆⟧ (βᵣ ⟦↑1⟧) ⟦→⟧ αᵣ ⟦⊆⟧ βᵣ) N₁.⊆-unctx-+1↑1 N₂.⊆-unctx-+1↑1

    ⟦ø+1⊆ø⟧ : (⟦ø⟧ ⟦+1⟧ ⟦⊆⟧ ⟦ø⟧) N₁.ø+1⊆ø N₂.ø+1⊆ø

 module W₁ = WorldOps N₁.worldSym
 module W₂ = WorldOps N₂.worldSym

 field
  _⟦↑⟧_ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) W₁._↑_ W₂._↑_
 -- _⟦↑⟧_ αᵣ zero    = αᵣ
 -- _⟦↑⟧_ αᵣ (suc k) = (αᵣ ⟦↑⟧ k) ⟦↑1⟧

 field
  _⟦+ᵂ⟧_ : (⟦World⟧ ⟦→⟧ ⟦ℕ⟧ ⟦→⟧ ⟦World⟧) W₁._+ᵂ_ W₂._+ᵂ_
 -- _⟦+ᵂ⟧_ αᵣ zero    = αᵣ
 -- _⟦+ᵂ⟧_ αᵣ (suc k) = (αᵣ ⟦+ᵂ⟧ k) ⟦+1⟧

 field
   ⟦addᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ (⟦Name⟧ αᵣ ⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ))) N₁.addᴺ N₂.addᴺ
   ⟦subtractᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ) ⟦→⟧ ⟦Name⟧ αᵣ) N₁.subtractᴺ N₂.subtractᴺ
   ⟦cmpᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ kᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧
                     ⟦Name⟧ (αᵣ ⟦↑⟧ kᵣ) ⟦→⟧ ⟦Name⟧ (⟦ø⟧ ⟦↑⟧ kᵣ) ⟦⊎⟧ ⟦Name⟧ (αᵣ ⟦+ᵂ⟧ kᵣ)
            ) N₁.cmpᴺ N₂.cmpᴺ

 infixl 6 ⟦addᴺ⟧ ⟦subtractᴺ⟧
 infix 4 ⟦cmpᴺ⟧
 syntax ⟦subtractᴺ⟧ k x = x ⟦∸ᴺ⟧ k
 syntax ⟦addᴺ⟧ k x = x ⟦+ᴺ⟧ k
 syntax ⟦cmpᴺ⟧ k x = x ⟦<ᴺ⟧ k

 field
   ⟦⊆-dist-+1-◅⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                      (((bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧) ⟦⊆⟧ ((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧))))
                    N₁.⊆-dist-+1-◅ N₂.⊆-dist-+1-◅
   ⟦⊆-dist-◅-+1⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                      (((⟦sucᴮ⟧ bᵣ) ⟦◅⟧ (αᵣ ⟦+1⟧)) ⟦⊆⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦+1⟧))
                    N₁.⊆-dist-◅-+1 N₂.⊆-dist-◅-+1

 field
   ⟦binderᴺ∘nameᴮ⟧ : (⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧
                      ⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧
                      ⟦≡⟧ ⟦Binder⟧ (⟦binderᴺ⟧ (bᵣ ⟦◅⟧ αᵣ) (⟦nameᴮ⟧ αᵣ bᵣ)) bᵣ)
                      N₁.binderᴺ∘nameᴮ N₂.binderᴺ∘nameᴮ

 infix 100 _⟦ᴺ⟧ _⟦ᴮ⟧

 -- From numbers to binders
 _⟦ᴮ⟧ : (⟦ℕ⟧ ⟦→⟧ ⟦Binder⟧) N₁._ᴮ N₂._ᴮ
 zero   ⟦ᴮ⟧ = ⟦zeroᴮ⟧
 suc nᵣ ⟦ᴮ⟧ = ⟦sucᴮ⟧ (nᵣ ⟦ᴮ⟧)

 -- From numbers to names
 _⟦ᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟨ nᵣ ∶ ⟦ℕ⟧ ⟩⟦→⟧ ⟦Name⟧ ((nᵣ ⟦ᴮ⟧) ⟦◅⟧ αᵣ)) N₁._ᴺ N₂._ᴺ
 _⟦ᴺ⟧ αᵣ nᵣ = ⟦nameᴮ⟧ αᵣ (nᵣ ⟦ᴮ⟧)

 ⟦zeroᴺ⟧ : (∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (αᵣ ⟦↑1⟧)) N₁.zeroᴺ N₂.zeroᴺ
 ⟦zeroᴺ⟧ αᵣ = _⟦ᴺ⟧ (αᵣ ⟦+1⟧) zero

 ⟦exportᴺ⟧ : (∀⟨ bᵣ ∶ ⟦Binder⟧ ⟩⟦→⟧ ∀⟨ αᵣ ∶ ⟦World⟧ ⟩⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ αᵣ) ⟦→⟧ ⟦Name⟧ (bᵣ ⟦◅⟧ ⟦ø⟧) ⟦⊎⟧ ⟦Name⟧ αᵣ) N₁.exportᴺ N₂.exportᴺ
 ⟦exportᴺ⟧ {b₁} {b₂} bᵣ αᵣ {x₁} {x₂} xᵣ = ⟦maybe⟧ (⟦Name⟧ αᵣ) (⟦Name⟧ (bᵣ ⟦◅⟧ ⟦ø⟧) ⟦⊎⟧ ⟦Name⟧ αᵣ)
                                                {inj₂} {inj₂} inj₂
                                                {inj₁ (N₁.nameᴮ b₁)} {inj₁ (N₂.nameᴮ b₂)} (inj₁ (⟦nameᴮ⟧ _ bᵣ))
                                                (⟦exportᴺ?⟧ bᵣ αᵣ {x₁} {x₂} xᵣ)

 -- more derived stuff could be added here for completeness

 ⟦dataKit⟧ : ⟦DataKit⟧ ℓ N₁.dataKit N₂.dataKit
 ⟦dataKit⟧ = mk ⟦World⟧ ⟦Name⟧ ⟦Binder⟧ _⟦◅⟧_
