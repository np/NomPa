import Level as L
open import Data.List as List
open import Data.Nat.NP
open import Data.Bool
open import Data.Unit using (⊤)
open import Data.Maybe.NP
open import Data.String renaming (_==_ to _==ˢ_)
open import Data.Atom
open import Function.NP
import      Data.Empty
import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps; now; later; never)
open import Coinduction
import NomPa.Examples.LN
import NomPa.Examples.LocallyNamed
import NomPa.Examples.LL
import NomPa.Examples.NaPa.LC
import NomPa.Examples.LC
import NomPa.Examples.LC.DbLevels
import Relation.Binary.PropositionalEquality as ≡
import NomPa.Derived
import NomPa.Derived.NaPa

module NomPa.Examples.Tests where
open import NomPa.Implem using (nomPa)
open import NomPa.Record
open import NomPa.Examples.Path
open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Derived.NaPa nomPa
module LN   = NomPa.Examples.LN nomPa
module LNom = NomPa.Examples.LocallyNamed nomPa
module LL   = NomPa.Examples.LL nomPa
module LCᴰ  = NomPa.Examples.NaPa.LC nomPa
module LCᴺ  = NomPa.Examples.LC nomPa Data.Empty.⊥ (λ())
open LCᴺ using (ƛ; V; Let; V₁)
         renaming (Tm to Tmᴺ; showTmø to showTmøᴺ; parseTmø to parseTmᴺø;
                   parseTm to parseTmᴺ;
                   β-red to β-redᴺ;
                   TmOk to TmᴺOk; TmøOk to TmøᴺOk;
                   _·_ to _·ᴺ_)
-- NomPa.Examples.LC.Contexts ... renaming (focus? to focusᴺ?; defocus to defocusᴺ;
open LL using (Vᴬ; Vᴺ; ƛ; Let) renaming (openSubstTm to openSubstTmᴸ; _·_ to _·ᴸ_)
module LCᴸ  = NomPa.Examples.LC.DbLevels nomPa Data.Empty.⊥ (λ()) (λ())
open ≡ using (_≡_)

  -- test₁ : openSubstTmᴸ (Vᴬ (42 ᴬ)) (3 ᴮ , Vᴺ (3 ᴺ)) ≡ Vᴬ (42 ᴬ)
  -- test₂ : openSubstTmᴸ (Vᴬ (42 ᴬ)) (3 ᴮ , ƛ (4 ᴮ , Vᴺ (4 ᴺ) · Vᴺ (coerceᴺ (⊆-# (suc# (0 ᴮ #ø))) (3 ᴺ)))) ≡ ƛ (Vᴺ (0 ᴺ) · Vᴬ (42 ᴬ))
test₁ : openSubstTmᴸ (Vᴬ (42 ᴬ)) (Vᴺ (0 ᴺ′)) ≡ Vᴬ (42 ᴬ)
test₁ = ≡.refl
test₂ : openSubstTmᴸ (Vᴬ (42 ᴬ)) (ƛ (Vᴺ (1 ᴺ′) ·ᴸ Vᴺ (coerceᴺ (⊆-# (suc# (0 ᴮ #ø))) (0 ᴺ′)))) ≡ ƛ (Vᴺ (0 ᴺ′) ·ᴸ Vᴬ (42 ᴬ))
test₂ = ≡.refl

{-
-- ℕ = ∀ {α} → α → (α → α) → α

zeroˢ = trueˢ
sucˢ  = "λn.λz.λs.s (n z s)"
addˢ  = "λm.λn.λz.λs.m (n z s) (s)"

-- ℕ = ∀ {α} → (α → α) → (α → α)

zeroˢ = falseˢ -- "λf.λx.x"
sucˢ  = "λn.λf.λx.n f (f x)" -- λn.λf.n f ∘ f
addˢ  = "λsuc.λm.m suc" · sucˢ
multˢ = "λzero.λadd.λm.λn.m (add n) zero" · zeroˢ · addˢ
_ℕˢ :
-}

open LCᴰ renaming (focus? to focusᴰ?; defocus to defocusᴰ)
idᴰ : ∀ {α} → Tmᴰ α
idᴰ = parseTmᴰ "λx.x"
trueᴰ : ∀ {α} → Tmᴰ α
trueᴰ = parseTmᴰ "λx.λ_.x"
falseᴰ : ∀ {α} → Tmᴰ α
falseᴰ = parseTmᴰ "λ_.λx.x"
pairᴰ : ∀ {α} → Tmᴰ α
pairᴰ = parseTmᴰ "λx.λy.λf.f x y"
fstᴰ : ∀ {α} → Tmᴰ α
fstᴰ = parseTmᴰ "λtrue.λp.p true" · trueᴰ
  -- = parseTmᴰ "λp.p (λx.λ_.x)"
sndᴰ : ∀ {α} → Tmᴰ α
sndᴰ = parseTmᴰ "λfalse.λp.p false" · falseᴰ
  -- = parseTmᴰ "λp.p (λ_.λx.x)"
uncurryᴰ : ∀ {α} → Tmᴰ α
uncurryᴰ = parseTmᴰ "λtrue.λfalse.λf.λp.f (p true) (p false)" · trueᴰ · falseᴰ
      -- = parseTmᴰ "λf.λp.f (p (λx.λ_.x)) (p (λ_.λx.x))"
appᴰ : ∀ {α} → Tmᴰ α
appᴰ = parseTmᴰ "λf.λx.f x"
compᴰ : ∀ {α} → Tmᴰ α
compᴰ = parseTmᴰ "λf.λg.λx.f (g x)"

-- ℕ = ∀ {α} → (α → α) → (α → α)
zeroᴰ : ∀ {α} → Tmᴰ α
zeroᴰ = falseᴰ -- "λf.λx.x"
sucᴰ  : ∀ {α} → Tmᴰ α
sucᴰ  = parseTmᴰ "λn.λf.λx.n f (f x)" -- λn.λf.n f ∘ f
addᴰ  : ∀ {α} → Tmᴰ α
addᴰ  = parseTmᴰ "λsuc.λm.m suc" · sucᴰ
multᴰ : ∀ {α} → Tmᴰ α
multᴰ = parseTmᴰ "λzero.λadd.λm.λn.m (add n) zero" · zeroᴰ · addᴰ

_ℕᴰ : ℕ → ∀ {α} → Tmᴰ α
{-
zero  ℕᴰ = zeroᴰ
suc n ℕᴰ = sucᴰ · n ℕᴰ
-}
n ℕᴰ = ƛ (ƛ (replicapp n (V (1 ᴺᴰ)) (V (0 ᴺᴰ))))
  where replicapp : ∀ {α} → ℕ → Tmᴰ α → Tmᴰ α → Tmᴰ α
        replicapp zero    t u = u
        replicapp (suc n) t u = t · replicapp n t u

2+1ᴰ : ∀ {α} → Tmᴰ α
2+1ᴰ = addᴰ · 2 ℕᴰ · 1 ℕᴰ

2×2ᴰ : ∀ {α} → Tmᴰ α
2×2ᴰ = multᴰ · 2 ℕᴰ · 2 ℕᴰ

3×4ᴰ : ∀ {α} → Tmᴰ α
3×4ᴰ = multᴰ · 3 ℕᴰ · 4 ℕᴰ

module KAMᴰ-tests where
  open LCᴰ.KAM using (_★_; Tmø)
  runTmℕ_for_steps : Tmø → ℕ → Tmø ⊥
  runTmℕ_for_steps t n = run (t ★ (arg (` 1) ∷ arg (` 0) ∷ [])) for n steps

  2+1≡3 : runTmℕ 2+1ᴰ for 19 steps ≡ now (` 3)
  2+1≡3 = ≡.refl

  -- test : ⊤
  -- test = ?

module AAMᴰ-tests where
  open LCᴰ.AAM using (_★_; Tmø)
  runTmℕ_for_steps : Tmø → ℕ → Tmø ⊥
  runTmℕ_for_steps t n = run (t ★ (arg (` 1) ∷ arg (` 0) ∷ [])) for n steps

  2+1≡3 : runTmℕ 2+1ᴰ for 29 steps ≡ now (` 3)
  2+1≡3 = ≡.refl

  -- test : ⊤
  -- test

showTmᴰ-tests : List.map showTmᴰ (idᴰ ∷ appᴰ ∷ uncurryᴰ ∷ [])
                      ≡ ("λx0. x0" ∷ "λx0. λx1. x0 x1" ∷
                          "(λx0. λx1. λx2. λx3. x2 (x3 x0) (x3 x1)) (λx0. λx1. x0) (λx0. λx1. x1)" ∷ [])
showTmᴰ-tests = ≡.refl

test-β-redᴰ : ∀ p {p-ok : PathOk p}
                s {s-ok : TmᴰOk s}
                (s′ : String) → Set
test-β-redᴰ p {p-ok} s {s-ok} s′ =
  let p = parsePath p {p-ok} in
  let t = parseTmᴰ s {s-ok} {ø} in
  T(showTmᴰ (maybe′ (defocusᴰ p t ∘ β-redᴰ) t $ focusᴰ? p t) ==ˢ s′)

-- TODO focus/defocus support:
--   * the issue is with the Supply that β-red expects
--   * to ``focus a supply'' we would need the ``max'' function on binders and ``_#_'' rules.
test-β-redᴺ : ∀ s {s-ok : TmøᴺOk s} (s′ : String) → Set
test-β-redᴺ s {s-ok} s′ =
  let t = parseTmᴺø s {s-ok} in
  T(showTmøᴺ (β-redᴺ (0 ˢ) t) ==ˢ s′)

module β-redᴰ-tests where
  t1 : test-β-redᴰ "" "(λx.x x) (λx.x)" "(λx0. x0) (λx0. x0)"
  t1 = _
  t2 : test-β-redᴰ "λλ" "λy.λz.(λx.y x x z) (λx.x y z)" "λx0. λx1. x0 (λx2. x2 x0 x1) (λx2. x2 x0 x1) x1"
  t2 = _
  t3 : test-β-redᴰ "λλλ" "λx.λy.λz.(λx.x (λy.λz. x)) y" "λx0. λx1. λx2. x1 (λx3. λx4. x1)"
  t3 = _

idᴺ : ∀ {α} → Tmᴺ α
idᴺ = parseTmᴺ "λx.x"

module β-redᴺ-tests where
  t1 : test-β-redᴺ "(λx.x x) (λx.x)" "(λx0. x0) (λx0. x0)"
  t1 = _
  t2 : test-β-redᴺ "(λx.x (λy. x) (λx. x)) (λx.x)" "(λx0. x0) (λx0. λx1. x1) (λx0. x0)"
  t2 = _
  t3 : T(showTmøᴺ (β-redᴺ (0 ˢ) (ƛ (0 ᴮ) (V (0 ᴺ′) ·ᴺ (ƛ (1 ᴮ) (V₁ 0 {ø})) ·ᴺ idᴺ) ·ᴺ idᴺ))
         ==ˢ "(λx0. x0) (λx0. λx1. x1) (λx0. x0)")
  t3 = _

open LCᴸ -- renaming (focus? to focusᴰ?; defocus to defocusᴰ)

idᴸ : ∀ {α} → Tmᴸ (0 ᴮ) α
idᴸ = parseTmᴸ "λx.x" 0

-- try to support focus/defocus
test-β-redᴸ : ∀ s {s-ok : TmᴸøOk s}
                (s′ : String) → Set
test-β-redᴸ s {s-ok} s′ = T(showTmᴸ (β-redᴸ (0 ᴮ #ø) (parseTmᴸø s {s-ok})) ==ˢ s′)

module β-redᴸ-tests where
  t1 : test-β-redᴸ "(λx.x (λy. x) (λx. x)) (λx.x)" "(λx0. x0) (λx0. λx1. x1) (λx0. x0)"
  t1 = _
{-
  t2 : test-β-redᴸ "λλ" "λy.λz.(λx.y x x z) (λx.x y z)" "λx0. λx1. x0 (λx2. x2 x0 x1) (λx2. x2 x0 x1) x1"
  t2 = ≡.refl
  t3 : test-β-redᴸ "λλλ" "λx.λy.λz.(λx.x (λy.λz. x)) y" "λx0. λx1. λx2. x1 (λx3. λx4. x1)"
  t3 = ≡.refl
-}
