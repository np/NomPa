{-# OPTIONS --universe-polymorphism #-}
module NaPa.Examples.STLC where

import      Level as L
open import Data.Product.NP
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_) renaming (_≟_ to _≟ℕ_)
open import Data.Bool
import      Category.Monad.Partiality as Pa
open import Category.Applicative renaming (RawApplicative to Applicative;
                                           module RawApplicative to Applicative)
open import Category.Monad renaming (RawMonad to Monad; module RawMonad to Monad)
open import Coinduction
open import Function.NP
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
open        ≡ using (_≡_)
open import Function.Equivalence using (equivalence; _⇔_)
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to mapDec)
open import Data.Unit using (⊤)
open import Data.Sum
import      Data.List as List
open        List
open import Data.Maybe.NP as Maybe
open        Pa using (_⊥; run_for_steps; later; now)
open import NaPa.Interface
open import NaPa.TransKit

infixr 5 _⟶_
data Ty : Set where
  _⟶_  : ∀ (σ τ : Ty) → Ty
  ι ο   : Ty

data Constant : Set where
  num     : ℕ → Constant
  suc     : Constant
  natFix  : (τ : Ty) → Constant

module DataTm {ℓ} (kit : DataKit {ℓ}) where
  open DataKit kit
  infixl 4 _·_
  data Tm α : Set ℓ where
    V    : (x : Name α) → Tm α
    _·_  : (t u : Tm α) → Tm α
    ƛ    : (τ : Ty) (t : Tm (α ↑1)) → Tm α
    Let  : (t : Tm α) (u : Tm (α ↑1)) → Tm α
    `_   : (κ : Constant) → Tm α

open import NaPa
open import NaPa.Derived

module RawTm  = DataTm rawKit
module FinTm  = DataTm finKit
module MayTm  = DataTm mayKit
module NaPaTm = DataTm naPaKit

module TransTm {ℓ₁ ℓ₂} (transKit : TransKit ℓ₁ ℓ₂) where
  open DataTm
  open TransKit transKit

  ! : ∀ {α₁ α₂} (Γ : Env α₁ α₂) → Tm k₁ α₁ → Tm k₂ α₂
  ! Γ (V x)     = V (lookup Γ x)
  ! Γ (t · u)   = ! Γ t · ! Γ u
  ! Γ (ƛ τ t)   = ƛ τ (! (Γ ↑↑) t)
  ! Γ (Let t u) = Let (! Γ t) (! (Γ ↑↑) u)
  ! Γ (` κ)     = ` κ

cookTm : ∀ {α} → (ℕ → Name α) → RawTm.Tm _ → NaPaTm.Tm α
cookTm = TransTm.! raw-to-NaPa

cookTm′ : ∀ {α} (default : Name α) → RawTm.Tm _ → NaPaTm.Tm α
cookTm′ = cookTm ∘ const

-- Free variables in the input term are translated to occurences to the `0' variable.
cookTm₀ : RawTm.Tm _ → NaPaTm.Tm (ø ↑1)
cookTm₀ = cookTm′ (0 ᴺ)

open NaPaTm public

module TermExamples where

  idTm : ∀ {α} → Ty → Tm α
  idTm τ = ƛ τ (V (0 ᴺ))

  appTm : ∀ {α} (τ σ : Ty) → Tm α
  appTm τ σ
    = ƛ (τ ⟶ σ)
        (ƛ τ (V (1 ᴺ) · V (0 ᴺ)))

  compTm : ∀ {α} (σ τ θ : Ty) → Tm α
  compTm σ τ θ
    = ƛ (τ ⟶ θ) (ƛ (σ ⟶ τ) (ƛ σ (V (2 ᴺ) · (V (1 ᴺ) · V (0 ᴺ)))))

data C α : (β : World) → Set where
  Hole  : C α α
  _·₁_  : ∀ {β} (c : C α β) (t : Tm α) → C α β
  _·₂_  : ∀ {β} (t : Tm α) (c : C α β) → C α β
  ƛ     : ∀ {β} (τ : Ty) (c : C (α ↑1) β) → C α β
  Let₁  : ∀ {β} (c : C α β) (t : Tm (α ↑1)) → C α β
  Let₂  : ∀ {β} (t : Tm α) (c : C (α ↑1) β) → C α β

mutual
  neu? : ∀ {α} → Tm α → Bool
  neu? (ƛ _ _)    = false
  neu? (Let _ _)  = false
  neu? (` _)      = true
  neu? (V _)      = true
  neu? (t · u)    = neu? t ∧ nf? u

  nf? : ∀ {α} → Tm α → Bool
  nf? (ƛ _ t)  = nf? t
  nf? t        = neu? t

module Contexts where
  plug : ∀ {α β} → C α β → Tm β → Tm α
  plug Hole        t  = t
  plug (c ·₁ t)    u  = plug c u · t
  plug (t ·₂ c)    u  = t · plug c u
  plug (ƛ τ c)     t  = ƛ τ (plug c t)
  plug (Let₁ c t)  u  = Let (plug c u) t
  plug (Let₂ t c)  u  = Let t (plug c u)

  CTm : World → Set
  CTm α = ∃ λ β → C α β × Tm β

  cmap : ∀ {α β} → (∀ {γ} → C α γ → C β γ) → CTm α → CTm β
  cmap f (_ , c , t) = (_ , f c , t)

  hole : ∀ {α} → Tm α → CTm α
  hole t = (_ , Hole , t)

module CBVBigStepEval where
  open CEnvPack (funCEnv {L.zero})
  open Pa.Workaround

  data Val : Set where
    ƛ   : ∀ {α} → (Name α → Val) → Tm (α ↑1) → Val
    `_  : Constant → Val

  neverP : {A : Set} → A ⊥P
  neverP = later (♯ neverP)

  ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
  ℕFix zero    _  = id
  ℕFix (suc n) f  = f ∘ ℕFix n f

  -- λ f x → f (f (f ... (f x)))
  ℕFixø : ℕ → (τ : Ty) → Val
  ℕFixø n τ = ƛ Γ (ƛ τ (ℕFix n (_·_ (V (1 ᴺ))) (V (0 ᴺ))))
    where Γ : CEnv Val ø
          Γ = Nameø-elim

  evalCst : Constant → Val → Val ⊥P
  evalCst suc         (` num n)  = now (` num (suc n))
  evalCst (natFix τ)  (` num n)  = now (ℕFixø n τ)
  evalCst suc         _          = neverP -- ill typed program
  evalCst (natFix _)  _          = neverP -- ill typed program
  evalCst (num _)     _          = neverP -- ill typed program

  eval : ∀ {α} → Tm α → CEnv Val α → Val ⊥P
  eval (t · u) Δ = eval u Δ >>= λ v →
                   eval t Δ >>= λ w → app w v
   where
    app : Val → Val → Val ⊥P
    app (ƛ Δ body)  v = later (♯ eval body (Δ ,, v))
    app (` κ)       v = evalCst κ v

  eval (V x)      Δ  = now (Δ x)
  eval (ƛ τ t)    Δ  = now (ƛ Δ t)
  eval (Let t u)  Δ  = eval t Δ >>= λ v →
                       eval u (Δ ,, v)
  eval (` n)      _  = now (` n)

  eval′ : Tm ø → Val ⊥
  eval′ t = ⟦ eval t Nameø-elim ⟧P

_==Ty_ : (σ τ : Ty) → Bool
ι          ==Ty ι           = true
ι          ==Ty ο           = false
ι          ==Ty (_ ⟶ _)     = false
ο          ==Ty ο           = true
ο          ==Ty ι           = false
ο          ==Ty (_  ⟶ _  )  = false
(_ ⟶ _)    ==Ty ι           = false
(_ ⟶ _)    ==Ty ο           = false
(σ₁ ⟶ τ₁)  ==Ty (σ₂ ⟶ τ₂)  = σ₁ ==Ty σ₂ ∧ τ₁ ==Ty τ₂

⟶-inj₁  : ∀ {σ τ σ′ τ′} → σ ⟶ τ ≡ σ′ ⟶ τ′ → σ ≡ σ′
⟶-inj₁  refl = refl

⟶-inj₂  : ∀ {σ τ σ′ τ′} → σ ⟶ τ ≡ σ′ ⟶ τ′ → τ ≡ τ′
⟶-inj₂  refl = refl

Number-inj : ∀ {m n} → num m ≡ num n → m ≡ n
Number-inj refl = refl

NatFix-inj : ∀ {σ τ} → natFix σ ≡ natFix τ → σ ≡ τ
NatFix-inj refl = refl

Number-con : ∀ {m n} → m ≡ n ⇔ num m ≡ num n
Number-con = equivalence (cong num) Number-inj

NatFix-con : ∀ {m n} → m ≡ n ⇔ natFix m ≡ natFix n
NatFix-con = equivalence (cong natFix) NatFix-inj

_≟Ty_ : Decidable {A = Ty} _≡_
ι           ≟Ty ι           = yes refl
ι           ≟Ty ο           = no λ()
ι           ≟Ty (_ ⟶ _)     = no λ()
ο           ≟Ty ο           = yes refl
ο           ≟Ty ι           = no λ()
ο           ≟Ty (_  ⟶ _  )  = no λ()
(_ ⟶ _)     ≟Ty ι           = no λ()
(_ ⟶ _)     ≟Ty ο           = no λ()
(τ₁ ⟶ τ₁')  ≟Ty (τ₂ ⟶ τ₂') with τ₁ ≟Ty τ₂ | τ₁' ≟Ty τ₂'
... | yes p | yes q = yes (cong₂ _⟶_ p q)
... | yes p | no ¬q = no (¬q ∘ ⟶-inj₂)
... | no ¬p | yes q = no (¬p ∘ ⟶-inj₁)
... | no ¬p | no ¬q = no (¬p ∘ ⟶-inj₁)

_≟κ_ : Decidable {A = Constant} _≡_
num m     ≟κ num n     = mapDec Number-con (m ≟ℕ n)
natFix σ  ≟κ natFix τ  = mapDec NatFix-con (σ ≟Ty τ)
suc       ≟κ suc       = yes refl
num _     ≟κ natFix _  = no λ()
num _     ≟κ suc       = no λ()
natFix _  ≟κ num _     = no λ()
natFix _  ≟κ suc       = no λ()
suc       ≟κ natFix _  = no λ()
suc       ≟κ num _     = no λ()

rm₀ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
rm₀ [] = []
rm₀ (x ∷ xs) with predᴺ? x
...               |  just x'  = x'  ∷ rm₀ xs
...               |  nothing  = rm₀ xs

fv : ∀ {α} → Tm α → List (Name α)
fv (` _)        = []
fv (V x)        = [ x ]
fv (fct · arg)  = fv fct ++ fv arg
fv (ƛ _ t)      = rm₀ (fv t)
fv (Let t u)    = fv t ++ rm₀ (fv u)

αeqTm : ∀ {α β} → αEq Name α β → αEq Tm α β
αeqTm {α} {β} Γ = go 0 where
  open αEquivalence
  go : ∀ ℓ → αEq Tm (α ↑ ℓ) (β ↑ ℓ)
  go _ (` κ)   (` κ')       = ⌊ κ ≟κ κ' ⌋
  go ℓ (V x)   (V y)        = αeqName Γ ℓ x y
  go ℓ (t · u) (v · w)      = go ℓ t v ∧ go ℓ u w
  go ℓ (ƛ τ t) (ƛ σ u)     = ⌊ τ ≟Ty σ ⌋ ∧ go (suc ℓ) t u
  go ℓ (Let t u) (Let v w)  = go ℓ t v ∧ go (suc ℓ) u w
  go _ _ _                  = false

size : ∀ {α} → Tm α → ℕ
size (V _)      = 1
size (t · u)    = 1 + size t + size u
size (ƛ _ t)    = 1 + size t
size (Let t u)  = 1 + size t + size u
size (` _)      = 1

count : ∀ {α} → Name α → Tm α → ℕ
count {α} x₀ = cnt 0
  where
    cnt : ∀ ℓ → Tm (α ↑ ℓ) → ℕ
    cnt ℓ (V x)
     with subtractᴺ? ℓ x
    ... | just x'  = if x' ==ᴺ x₀ then 1 else 0
    ... | nothing  = 0
    cnt ℓ (t · u)    = cnt ℓ t + cnt ℓ u
    cnt ℓ (ƛ _ t)    = cnt (suc ℓ) t
    cnt ℓ (Let t u)  = cnt ℓ t + cnt (suc ℓ) u
    cnt _ (` _)      = 0

fv' : ∀ {α} ℓ → Tm (α ↑ ℓ) → List (Name α)
fv' ℓ (V x)      = List.fromMaybe (subtractᴺ? ℓ x)
fv' ℓ (t · u)    = fv' ℓ t ++ fv' ℓ u
fv' ℓ (ƛ _ t)    = fv' (suc ℓ) t
fv' ℓ (Let t u)  = fv' ℓ t ++ fv' (suc ℓ) u
fv' _ (` _)      = []

fv₂Env : (α β : World) → Set
fv₂Env α β = Name α → List (Name β)

extfv₂ : ∀ {α β} → fv₂Env α β → fv₂Env (α ↑1) β
extfv₂ f = concatMap f ∘ List.fromMaybe ∘ predᴺ?

fv₂ : ∀ {α β} → fv₂Env α β → Tm α → List (Name β)
fv₂ Γ (V x)      = Γ x
fv₂ Γ (t · u)    = fv₂ Γ t ++ fv₂ Γ u
fv₂ Γ (ƛ _ t)    = fv₂ (extfv₂ Γ) t
fv₂ Γ (Let t u)  = fv₂ Γ t ++ fv₂ (extfv₂ Γ) u
fv₂ _ (` _)      = []

member : ∀ {α} → Name α → Tm α → Bool
member {α} x = mem 0
  where
    mem : ∀ ℓ → Tm (α ↑ ℓ) → Bool
    mem ℓ (V y)      = maybe′ (_==ᴺ_ x) false (subtractᴺ? ℓ y)
    mem ℓ (t · u)    = mem ℓ t ∨ mem ℓ u
    mem ℓ (ƛ _ t)    = mem (suc ℓ) t
    mem ℓ (Let t u)  = mem ℓ t ∨ mem (suc ℓ) u
    mem _ (` _)      = false

module TraverseTm  {E} (E-app : Applicative E)
                   {α β} (trName : Su↑ Name (E ∘ Tm) α β) where
  open Applicative E-app

  traverseTm : Su↑ Tm (E ∘ Tm) α β
  traverseTm ℓ (V x)      = trName ℓ x
  traverseTm _ (` x)      = pure (` x)
  traverseTm ℓ (t · u)    = _·_ <$> traverseTm ℓ t ⊛ traverseTm ℓ u
  traverseTm ℓ (ƛ τ t)    = ƛ τ <$> traverseTm (suc ℓ) t
  traverseTm ℓ (Let t u)  = Let <$> traverseTm ℓ t ⊛ traverseTm (suc ℓ) u

module DerivedOperationsByHand where
  open TraverseTm

  tr : ∀ {E} (E-app : Applicative E)
         {α β} (trName : ∀ ℓ → Name (α ↑ ℓ) → E (Name (β ↑ ℓ)))
       → Tm α → E (Tm β)
  tr E-app trName = traverseTm E-app (λ ℓ x → V <$> trName ℓ x) 0
     where open Applicative E-app

  renameTmA : ∀ {E} (E-app : Applicative E)
                {α β} (θ : Name α → E (Name β))
              → Tm α → E (Tm β)
  renameTmA E-app θ = tr E-app (protect↑A E-app θ)

  renameTm : ∀ {α β} → (Name α → Name β) → Tm α → Tm β
  renameTm θ = tr id-app (protect↑ θ)
  -- renameTm = renameTmA id-app

  addTm : ∀ {α} k → Tm α → Tm (α +ᵂ k)
  addTm = renameTm ∘ addᴺ

  subtractTm : ∀ {α} k → Tm (α +ᵂ k) → Tm α
  subtractTm = renameTm ∘ subtractᴺ

  shiftTm : ∀ {α β} k → (α +ᵂ k) ⊆ β → Tm α → Tm β
  shiftTm k pf = tr id-app (λ ℓ → shiftName ℓ k pf)

  -- This version is less efficient it will subtract ℓ and add it back after adding k.
  -- shiftTm k pf = renameTm (coerceᴺ pf ∘ addᴺ k)

  coerceTm : ∀ {α β} → α ⊆ β → Tm α → Tm β
  coerceTm pf = tr id-app (coerceᴺ ∘ ⊆-cong-↑ pf)
  -- or less efficiently:
  -- coerceTm = renameTm ∘ coerceᴺ

  coerceTmø : Tm ø → ∀ {α} → Tm α
  coerceTmø t = renameTm Nameø-elim t

  renameTm? : ∀ {α β} → (Name α →? Name β) → Tm α →? Tm β
  renameTm? = renameTmA Maybe.applicative

  subtractTm? : ∀ {α} ℓ → Tm (α ↑ ℓ) →? Tm α
  subtractTm? = renameTm? ∘ subtractᴺ?

  closeTm? : ∀ {α} → Tm α →? Tm ø
  closeTm? = renameTm? (const nothing)

  substTm : ∀ {α β} → (Name α → Tm β) → Tm α → Tm β
  substTm f = traverseTm id-app (substVar V shiftTm f) 0

open TraverseAFGGGen {Tm} V TraverseTm.traverseTm public
  renaming ( renameA   to renameATm
           ; rename    to renameTm
           ; shift     to shiftTm
           ; coerceø   to coerceTmø
           ; coerce    to coerceTm
           ; subtract? to subtractTm?
           ; close?    to closeTm?
           )

module SubstTmByHand where
 substVarTm : SubstVar Tm
 substVarTm = substVar V shiftTm

 substTm : Subst Tm Tm Tm
 substTm {α} {β} θ = go 0 where
  go : Su↑ Tm Tm α β
  go ℓ (V x)     = substVarTm θ ℓ x
  go ℓ (t · u)   = go ℓ t · go ℓ u
  go ℓ (ƛ τ t)   = ƛ τ (go (suc ℓ) t)
  go ℓ (Let t u) = Let (go ℓ t) (go (suc ℓ) u)
  go _ (` κ)     = ` κ

open SubstGen {Tm} V shiftTm (TraverseTm.traverseTm id-app) public
  renaming ( substVarG to substVarTm
           -- ; substName to subst0Tm
           ; subst to substTm )

substNmTm : ∀ {α} → (Name α × Tm α) → (Name α → Tm α)
substNmTm (x , v) y = if x ==ᴺ y then v else V y

β-red : ∀ {α} (fct : Tm (α ↑1)) (arg : Tm α) → Tm α
β-red {α} fct arg = substTm (φ ∘ predᴺ?) fct where
    φ : Maybe (Name α) → Tm α
    φ (just x) = V x
    φ nothing  = arg

β-red-rule : ∀ {α τ} {fct : Tm (α ↑1)} {arg : Tm α} {t : Tm α}
             → t ≡ ƛ τ fct · arg
             → Tm α
β-red-rule {fct = fct} {arg} refl = β-red fct arg

{-
NOTICE
  By instanciating a
    rename : ∀ {α β} ℓ → (Name α → Name β) → F (α ↑ ℓ) → G (β ↑ ℓ)
  into a
    rename 0 : ∀ {α β} → (Name α → Name β) → F α → G β
  we actually lose no generality since
    λ ℓ f → rename 0 (protect↑ f ℓ) : ∀ {α β} ℓ → (Name α → Name β) → F (α ↑ ℓ) → G (β ↑ ℓ)

  This is because:
     protect↑ f (ℓ₁ + ℓ₂) ≈ protect↑ (protect↑ f ℓ₁) ℓ₂
-}
renameTm↑ : ∀ {α β} → (Name α → Name β) → ∀ ℓ → Tm (α ↑ ℓ) → Tm (β ↑ ℓ)
renameTm↑ f ℓ = renameTm (protect↑ f ℓ)

wrongShiftNameSimple : ∀ {α} ℓ k → Name (α ↑ ℓ) → Name (α ↑ k ↑ ℓ)
wrongShiftNameSimple ℓ k = coerceᴺ (⊆-exch-↑-↑′ ℓ k) ∘ addᴺ↑ k

wrongShiftName : ∀ {α β} ℓ k → (α ↑ k) ⊆ β → Name (α ↑ ℓ) → Name (β ↑ ℓ)
wrongShiftName {α} {β} ℓ k pf = coerceᴺ pf′ ∘ addᴺ↑ k
  where open ⊆-Reasoning
        pf′ = α ↑ ℓ ↑ k
           ⊆⟨ ⊆-exch-↑-↑′ ℓ k ⟩
             α ↑ k ↑ ℓ
           ⊆⟨ ⊆-cong-↑ pf ℓ ⟩
             β ↑ ℓ ∎

open Contexts
module Reducer (split  : ∀ {α} → Tm α → CTm α)
               (val?   : ∀ {α} → Tm α → Bool)
               (reduce : ∀ {α} → Tm α → Tm α) where

  open Monad (Pa.monad {L.zero})

  reduce★ : ∀ {α} → Tm α → (Tm α) ⊥
  reduce★ t with val? t
  ... | true = return t
  ... | false = later (♯ r)
      where st = proj₂ (split t)
            c  = proj₁ st
            u  = proj₂ st
            r  = reduce★ (plug c (reduce u))

  module Check (n : ℕ) where
    infix 0 _↝★_
    _↝★_ : Tm ø → Tm ø → Set
    t ↝★ u = run (reduce★ t) for n steps ≡ now u

module SmallStep where
  module Strong where
    -- one strategy among others
    split : ∀ {α} → Tm α → CTm α
    split (V x)      = hole (V x)
    split (t · u)    = if nf? t  then cmap (_·₂_ t) (split u)
                                 else cmap (flip _·₁_ u) (split t)
    split (ƛ τ t)   = cmap (ƛ τ) (split t)
    split (Let t u)  = if nf? t  then cmap (Let₂ t) (split u)
                                 else cmap (λ y → Let₁ y u) (split t)
    split (` κ)      = hole (` κ)

  module WeakCBV where
    val? : ∀ {α} → Tm α → Bool
    val? (ƛ _ _)  = true
    val? (` _)    = true
    val? _        = false

    split : ∀ {α} → Tm α → CTm α
    split t0 with t0
    ... | t · u    =  if val? u then
                        if val? t then hole t0
                        else cmap (flip _·₁_ u) (split t)
                      else cmap (_·₂_ t) (split u)
    ... | Let t u  =  if val? t then hole t0
                      else cmap (λ y → Let₁ y u) (split t)
    ... | _        =  hole t0

    ℕFix : ∀ {A : Set} → ℕ → (A → A) → (A → A)
    ℕFix zero     _  = id
    ℕFix (suc n)  f  = f ∘ ℕFix n f

    ℕFixTm : ∀ {α} → ℕ → Ty → Tm α
    ℕFixTm n τ = ƛ (τ ⟶ τ) (
                   ƛ τ (
                     ℕFix n (_·_ (V (1 ᴺ))) (V (0 ᴺ))))

    red : ∀ {α} → Tm α → Tm α
    red (ƛ τ fct · arg)            = β-red fct arg
    red (Let t u)                   = β-red u t
    red (` (natFix τ) · ` (num n))  = ℕFixTm n τ
    red (` suc · ` (num n))         = ` (num (suc n))
    red t                           = t

    open Reducer split val? red public

    module Examples where
      open TermExamples
      open Check 10
      ex₁ : appTm ι ι · idTm (ι ⟶ ι) · idTm ι ↝★ idTm ι
      ex₁ = ≡.refl

module Typing (cenv : CEnvPack L.zero) where
  open Monad (Maybe.monad {L.zero})
  open CEnvPack cenv

  typing-constants : Constant → Ty
  typing-constants (num _)     = ι
  typing-constants suc         = ι ⟶ ι
  typing-constants (natFix τ)  = ι ⟶ (τ ⟶ τ) ⟶ (τ ⟶ τ)

  typing : ∀ {α} → CEnv Ty α → Tm α →? Ty
  typing Γ (V v) = just (lookupCEnv Γ v)
  typing Γ (ƛ τ t) = _⟶_ τ <$> typing (Γ ,, τ) t
  typing Γ (Let t u) = typing Γ t >>= λ τ → typing (Γ ,, τ) u
  typing _ (` κ) = just (typing-constants κ)
  typing Γ (t · u) with typing Γ t | typing Γ u
  ... | just (from ⟶ to) | just σ
            = if ⌊ from ≟Ty σ ⌋ then just to else nothing
  ... | _ | _ = nothing

  module Check where
    infix 0 ⊢_∶_
    ⊢_∶_ : Tm ø → Ty → Set
    ⊢ t ∶ τ = typing emptyCEnv t ≡ just τ

module Examples where
  open Typing funCEnv
  open Check
  open TermExamples

  ex₁ : ⊢ idTm ι ∶ ι ⟶ ι
  ex₁ = ≡.refl

  ex₂ : ⊢ appTm ο ι ∶ (ο ⟶ ι) ⟶ (ο ⟶ ι)
  ex₂ = ≡.refl

  ex₃ : ⊢ compTm ο ι ι ∶ (ι ⟶ ι) ⟶ (ο ⟶ ι) ⟶ ο ⟶ ι
  ex₃ = ≡.refl

  ex₄ : ⊢ compTm ο ι ο ∶ (ι ⟶ ο) ⟶ (ο ⟶ ι) ⟶ ο ⟶ ο
  ex₄ = ≡.refl

strenghten? : ∀ {α} → Tm (α ↑1) →? Tm α
strenghten? = subtractTm? 1

η-contract : ∀ {α} → Tm α → Tm α
η-contract t with t
... | ƛ τ (f · V x) with is0? x | strenghten? f
...                     | true   | just f′        = f′
...                     | _      | _             = t
η-contract t | _ = t

module η-contract-examples where
  ex₁ : η-contract {ø ↑ 2} (ƛ ι (V(2 ᴺ) · V(0 ᴺ))) ≡ V(1 ᴺ)
  ex₁ = ≡.refl
