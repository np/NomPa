module NomPa.Examples.LC.Tests where

open import Function
open import Data.Empty
open import NomPa.Record
open import NomPa.Implem using (nomPa)
import NomPa.Examples.LC
open NomPa.Examples.LC nomPa ⊥ (λ())
open NomPa nomPa

-- ap : Tm ø
ap = showTmø $ parseTm "λx.λy.x y"
uncurry = showTmø $ parseTm "λf.λp.f (p (λx.λ_.x)) (p (λ_.λx.x))"
