module NomPa.Examples.LC.WellScopedJudgment where

open import Function
open import Data.Nat
open import Data.List
open import Data.Bool
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≢_)

-- open import Data.Atom
import Data.Atom
open Data.Atom.Internals

module BareNominal where
  x : Atom
  x = 0 ᴬ
  y : Atom
  y = 1 ᴬ
  z : Atom
  z = 2 ᴬ
  f : Atom
  f = 3 ᴬ
  g : Atom
  g = 4 ᴬ

  []-inj : ∀ {A : Set} {x y : A} → [ x ] ≡ [ y ] → x ≡ y
  []-inj ≡.refl = ≡.refl

  [x]≢[y] : [ x ] ≢ [ y ]
  [x]≢[y] eq with injᴬ ([]-inj eq)
  ... | ()

  -- we may want to move this to a ``bare nominal module''
  data Tm : Set where
    V   : (x : Atom) → Tm
    _·_ : (t u : Tm) → Tm
    ƛ   : (b : Atom) (t : Tm) → Tm

  -- λx. x
  idTm : Tm
  idTm = ƛ x (V x)

  -- λf. λx. f x
  apTm : Tm
  apTm = ƛ f (ƛ x (V f · V x))

  rm : Atom → List Atom → List Atom
  rm _ []       = []
  rm x (y ∷ ys) =
    if x ==ᴬ y then rm x ys
               else y ∷ rm x ys

  -- Since rm behaves well, this holds:
  test-rm : rm x [ x ] ≡ rm y [ y ]
  test-rm = ≡.refl -- both reduces to []

  fv : Tm → List Atom
  fv (V x)   = [ x ]
  fv (t · u) = fv t ++ fv u
  fv (ƛ x t) = rm x (fv t)

  tˣ : Tm
  tˣ = ƛ x (V f · V x)

  tʸ : Tm
  tʸ = ƛ y (V f · V y)

  ba : Tm → List Atom
  ba (ƛ x t) = x ∷ ba t
  ba (t · u) = ba t ++ ba u
  ba (V _)   = []

  -- Since ba does not behave well:
  test-ba : ba tˣ ≢ ba tʸ
  test-ba = [x]≢[y]

infixl 5 _,_

data Env : Set where
  ε   : Env
  _,_ : (Γ : Env) (x : Atom) → Env

data _∈_ x : (Γ : Env) → Set where

  here  : ∀ {Γ}     → -------------
                       x ∈ (Γ , x)

  there : ∀ {Γ y}
            {-{pf : False ⌊ x ≟ y ⌋}-}
                    →  x ∈ Γ
                    → -------------
                       x ∈ (Γ , y)

open BareNominal hiding (fv; ba; tˣ; tʸ; test-ba)

infix 0 _⊢_
data _⊢_ Γ : Tm → Set where
  V : ∀ {x}         →  x ∈ Γ
                    → ---------
                       Γ ⊢ V x

  _·_ : ∀ {t u}     →  Γ ⊢ t
                    →  Γ ⊢ u
                    → -----------
                       Γ ⊢ t · u

  ƛ : ∀ {t b}       →  Γ , b ⊢ t
                    → -----------
                       Γ ⊢ ƛ b t

⊢id : ε ⊢ idTm
⊢id = ƛ (V here)

⊢ap : ε ⊢ apTm
⊢ap = ƛ (ƛ (V (there here) · V here))

⊢ap′ : ε ⊢ apTm
⊢ap′ = ƛ {ε} {ƛ x (V f · V x)} {f}
         (ƛ {ε , f} {V f · V x} {x}
            (V {ε , f , x} {f}
               (there {f} {ε , f} {x}
                  (here {f} {ε})) ·
             V {ε , f , x} {x}
               (here {x} {ε , f})))

fail₁ : (ε , x , x) ⊢ V x
fail₁ = V here

fail₂ : (ε , x , x) ⊢ V x
fail₂ = V (there here)

-- Internally well-scoped terms

module Internally where
  data Tmʷˢ Γ : Set where
    V   : ∀ {x} → x ∈ Γ → Tmʷˢ Γ
    _·_ : Tmʷˢ Γ → Tmʷˢ Γ → Tmʷˢ Γ
    ƛ   : ∀ b → Tmʷˢ (Γ , b) → Tmʷˢ Γ

  idTmʷˢ : Tmʷˢ ε
  idTmʷˢ = ƛ x (V here)

  apTmʷˢ : Tmʷˢ ε
  apTmʷˢ = ƛ f (ƛ x (V (there here) · V here))

  fv : ∀ {Γ} → Tmʷˢ Γ → List Atom
  fv (V {x} _) = [ x ]
  fv (t · u)   = fv t ++ fv u
  fv (ƛ x t)   = rm x (fv t)

  ba : ∀ {Γ} → Tmʷˢ Γ → List Atom
  ba (ƛ x t) = x ∷ ba t
  ba (t · u) = ba t ++ ba u
  ba (V _)   = []

  tˣ : Tmʷˢ (ε , f)
  tˣ = ƛ x (V (there here) · V here)

  tʸ : Tmʷˢ (ε , f)
  tʸ = ƛ y (V (there here) · V here)

  -- Since ba does not behave well:
  test-ba : ba tˣ ≢ ba tʸ
  test-ba = [x]≢[y]

  cmp-ba : ∀ {Γ₁ Γ₂} → Tmʷˢ Γ₁ → Tmʷˢ Γ₂ → Bool
  cmp-ba (ƛ x _) (ƛ y _) = x ==ᴬ y
  cmp-ba _       _       = false

  fast-fv : ∀ {Γ} → Tmʷˢ Γ → List Atom
  fast-fv {ε} _ = []  -- for sure the term is closed
  fast-fv     t = fv t

  env-length : Env → ℕ
  env-length ε       = 0
  env-length (Γ , _) = 1 + env-length Γ

  env-length-Tm : ∀ {Γ} → Tmʷˢ Γ → ℕ
  env-length-Tm {Γ} _ = env-length Γ
