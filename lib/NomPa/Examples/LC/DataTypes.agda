open import NomPa.Record
module NomPa.Examples.LC.DataTypes (dataKit : DataKit) (Cst : Set) where

open DataKit dataKit

infixl 6 _·_

data Tm α : Set where
  V    : (x : Name α) → Tm α
  _·_  : (t u : Tm α) → Tm α
  ƛ    : (b : Binder) (t : Tm (b ◅ α)) → Tm α
  Let  : (b : Binder) (t : Tm α) (u : Tm (b ◅ α)) → Tm α
  `_   : (κ : Cst) → Tm α
