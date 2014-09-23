open import Data.Maybe.NP as Maybe
open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Data.Char using (Char) renaming (_==_ to _==ᶜ_)
open import Data.String as String
open import Data.List using (List; length; foldl)
open import Function
open import Text.Parser
import Level as L
import NomPa.Examples.Raw
open NomPa.Examples.Raw.DataType String

open M? L.zero using () renaming (_>>=_ to _>>=?_; _=<<_ to _=<<?_)

module NomPa.Examples.Raw.Parser where

{-
simple grammar:
var ∷= char ∉ "λ(.) "
t ∷= 'λ' var '.' t
   | '(' t ' ' t ')'
   | var

good grammar:
var ∷= (char ∉ "λ(.) ")+
t ∷= t′ (' '+ t′)★
t′ ∷= 'λ' var '.' t
   | '(' t ')'
   | var
-}

kwdChars : List Char
kwdChars = String.toList "λ(.) "

isSpace : Char → Bool
isSpace = (_==ᶜ_ ' ')

spaces : Parser ⊤
spaces = manySat isSpace *> pure _

someSpaces : Parser ⊤
someSpaces = someSat isSpace *> pure _

var : Parser String
var = map String.fromList $ spaces *> someNoneOf kwdChars
                                   -- some (noneOf kwdChars)

tok : Char → Parser ⊤
tok c = spaces *> char c *> pure _

mutual
  tm : ℕ → Parser Tmᴿ
  tm n = pure appⁿ ⊛ tm′ n ⊛ many (someSpaces *> tm′ n) n

  tm′ : ℕ → Parser Tmᴿ
  tm′ 0 = empty
  tm′ (suc n)
    =  pure ƛ <* tok 'λ' ⊛ var <* tok '.' ⊛ tm n
    ⟨|⟩ tok '(' *> tm n <* tok ')'
    ⟨|⟩ pure V ⊛ var

{-
tm : ℕ → Parser Tmᴿ
tm 0 = empty
tm (suc n)
  =  pure ƛ   <* tok 'λ' ⊛ var  <* tok '.' ⊛ tm n
  ⟨|⟩ pure _·_ <* tok '(' ⊛ tm n <* tok ' ' ⊛ tm n <* tok ')'
  ⟨|⟩ pure V ⊛ var
-}

parseTmᴿ? : String →? Tmᴿ
parseTmᴿ? s = runParser (tm n <* eof) l
  where l = String.toList s
        n = length l

module ParseConv {A} (conv? : Tmᴿ →? A) where
  parseConv? : String →? A
  parseConv? s = conv? =<<? parseTmᴿ? s

  TmOk : String → Set
  TmOk = just? ∘ parseConv?

  parseConv : ∀ s {s-ok : TmOk s} → A
  parseConv s {s-ok} with parseConv? s
  parseConv s {()}     | nothing
  parseConv s {_}      | just t = t

open ParseConv just public using () renaming (parseConv to parseTmᴿ)

module Tests where
  open import Relation.Binary.PropositionalEquality
  open import Data.Product.NP hiding (map)

  idˢ : String
  idˢ = "λx.x"

  idᵀ : Tmᴿ
  idᵀ = ƛ "x" (V "x")

  Δˢ : String
  Δˢ = "λx.(x x)"

  Δᵀ : Tmᴿ
  Δᵀ = ƛ "x" (V "x" · V "x")

  appˢ : String
  appˢ = "λf.λx.(f x)"

  appᵀ : Tmᴿ
  appᵀ = ƛ "f" (ƛ "x" (V "f" · V "x"))

  compˢ : String
  compˢ = "λf.λg.λx.(f (g x))"

  compᵀ : Tmᴿ
  compᵀ = ƛ "f" (ƛ "g" (ƛ "x" (V "f" · (V "g" · V "x"))))

  longVarsˢ = "λfoo.λbar.(bar foo)"
  longVarsᵀ = ƛ "foo" $ ƛ "bar" $ V "bar" · V "foo"

  multispacesˢ = "foo   bar baz"
  multispacesᵀ = V "foo" · V "bar" · V "baz"

  applightˢ = "λf.λx.f x"
  notappˢ = "(λf.λx.f) x"
  notappᵀ = (ƛ "f" (ƛ "x" (V "f"))) · V "x"

  tests : ( parseTmᴿ idˢ ≡ idᵀ
          × parseTmᴿ? Δˢ ≡ just Δᵀ
          × parseTmᴿ appˢ ≡ appᵀ
          × parseTmᴿ compˢ ≡ compᵀ
          × parseTmᴿ longVarsˢ ≡ longVarsᵀ
          × parseTmᴿ multispacesˢ ≡ multispacesᵀ
          × parseTmᴿ applightˢ  ≡ appᵀ
          × parseTmᴿ notappˢ  ≡ notappᵀ
          )
  tests = refl , refl , refl , refl , refl , refl , refl , refl
