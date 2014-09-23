module NomPa.Implem.LogicalRelation where

open import NomPa.Record.LogicalRelation
open import NomPa.Implem
open import NomPa.Implem.LogicalRelation.Internals hiding (⟨_,_⟩⟦◅⟧_)
open NomPa.Implem.LogicalRelation.Internals public using (⟨_,_⟩⟦◅⟧_)

⟦nomPa⟧ : ⟦NomPa⟧ _ nomPa nomPa
⟦nomPa⟧ = mk ⟦World⟧ ⟦Name⟧ ⟦Binder⟧ _⟦◅⟧_ ⟦zeroᴮ⟧ ⟦sucᴮ⟧ ⟦nameᴮ⟧ ⟦binderᴺ⟧ ⟦ø⟧ ⟦¬Nameø⟧ _⟦==ᴺ⟧_
             ⟦exportᴺ?⟧ _⟦#⟧_ _⟦#ø⟧ ⟦suc#⟧ _⟦⊆⟧_ ⟦coerceᴺ⟧ ⟦⊆-refl⟧ ⟦⊆-trans⟧
             ⟦⊆-ø⟧ ⟦⊆-◅⟧ ⟦⊆-#⟧ _⟦+1⟧ ⟦⊆-cong-↑1⟧
             -- derivable
             ⟦⊆-cong-+1⟧
             ⟦⊆-+1↑1⟧ ⟦⊆-↑1-inj⟧ ⟦⊆-+1-inj⟧ ⟦⊆-unctx-+1↑1⟧ ⟦ø+1⊆ø⟧
             -- derived
             _⟦↑⟧_ _⟦+ᵂ⟧_
             ⟦addᴺ⟧ ⟦subtractᴺ⟧ ⟦cmpᴺ⟧ ⟦⊆-dist-+1-◅⟧ ⟦⊆-dist-◅-+1⟧ ⟦binderᴺ∘nameᴮ⟧
