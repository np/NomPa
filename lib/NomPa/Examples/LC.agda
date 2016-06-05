{-# OPTIONS --universe-polymorphism #-}
import Level as L
open import NomPa.Record
import NomPa.Derived
import NomPa.Traverse
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Category.Monad renaming (RawMonad to Monad; module RawMonad to Monad)
open import Data.Maybe.NP as Maybe
open import Data.Unit using (⊤)
open import Data.List
open import Data.Product.NP
open import Data.Nat
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Indexed using (_↦°_)
open import Data.Sum
open import Data.String renaming (_++_ to _++ˢ_)
open import Data.Bool
open import Function.NP
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
import NomPa.Examples.Raw
open import NomPa.Examples.Raw.Parser
open import NomPa.Examples.Path
import NomPa.Examples.LC.DataTypes
import NomPa.Examples.LC.Equiv
import NomPa.Examples.LC.Contexts

module NomPa.Examples.LC
  (nomPa : NomPa)
  (Cst : Set)
  (showCst : Cst → String) where

open NomPa nomPa
open NomPa.Derived nomPa
open NomPa.Traverse nomPa hiding (Subst)
open NomPa.Examples.LC.Equiv nomPa using (cmpTm; _==ᵀᵐ_)
open NomPa.Examples.LC.DataTypes dataKit Cst public
open NomPa.Examples.LC.Contexts nomPa Cst

appⁿ : ∀ {α} → Tm α → List (Tm α) → Tm α
appⁿ = foldl _·_
-- an alternative name to appⁿ is _·★_

CTm : Set
CTm = ∀ {α} → Tm α

module FreeVars where
  fv : ∀ {α} → Tm α → List (Name α)
  fv (V x)        = [ x ]
  fv (fct · arg)  = fv fct ++ fv arg
  fv (ƛ b t)      = rm b (fv t)
  fv (Let b t u)  = fv t ++ rm b (fv u)
  fv (` _)        = []

module CoerceTmByHand where
  coerceTm : ∀ {α β} → (α ⊆ β) → Tm α → Tm β
  coerceTm α⊆β (V x) = V (x ⟨-because α⊆β -⟩)
  coerceTm α⊆β (t · u) = coerceTm α⊆β t · coerceTm α⊆β u
  coerceTm α⊆β (ƛ b t) = ƛ b (coerceTm (⊆-◅ b α⊆β) t)
  coerceTm α⊆β (Let b t u) = Let b (coerceTm α⊆β t) (coerceTm (⊆-◅ b α⊆β) u)
  coerceTm _    (` κ) = ` κ

module TraverseTm {E}   (E-app : Applicative E)
                  {Env} (trKit : TrKit Env (E ∘ Tm)) where

  open Applicative E-app
  open TrKit trKit

  tr : ∀ {α β} → Env α β → Tm α → E (Tm β)
  tr Δ (V x)       = trName Δ x
  tr Δ (t · u)     = pure _·_ ⊛ tr Δ t ⊛ tr Δ u
  tr Δ (ƛ b t)     = pure (ƛ _) ⊛ tr (extEnv b Δ) t
  tr Δ (Let b t u) = pure (Let _) ⊛ tr Δ t ⊛ tr (extEnv b Δ) u
  tr Δ (` κ)       = pure $ ` κ

module DerivedByHand where
  open TraverseTm

  tr′ : ∀ {E}   (E-app : Applicative E)
          {Env} (trKit : TrKit Env (E ∘ Name))
          {α β} → Env α β → Tm α → E (Tm β)
  tr′ E-app trKit = tr E-app (mapKit id (Applicative._<$>_ E-app V) trKit)

  renameTmA : ∀ {E} (E-app : Applicative E) →
              ∀ {α β} → Supply β → (Name α → E (Name β)) → (Tm α → E (Tm β))
  renameTmA E-app s f = tr′ E-app (renameAKit E-app) (f , s)

  coerceTm : ∀ {α β} → α ⊆ β → Tm α → Tm β
  coerceTm = tr′ id-app coerceKit

  coerceTmø : Tm ø → ∀ {α} → Tm α
  coerceTmø t = coerceTm ⊆-ø t

  renameTm : ∀ {α β} → Supply β → (α →ᴺ β) → (Tm α → Tm β)
  renameTm s f = tr′ id-app renameKit (f , s)

  renameCoerceTm : ∀ {α β γ} → Supply β → (α →ᴺ β) → β ⊆ γ → (Tm α → Tm γ)
  renameCoerceTm s f β⊆γ = tr′ id-app (coerceKit ∘-Kit renameKit) ((f , s) , β⊆γ)

  renameTm? : ∀ {α β} → Supply β → (α →ᴺ? β) → Tm α →? Tm β
  renameTm? = renameTmA (Maybe.applicative _)

  exportTm? : ∀ {b α} → Supply α → Tm (b ◅ α) →? Tm α
  exportTm? s = renameTm? s exportᴺ?

  closeTm? : ∀ {α} → Tm α →? Tm ø
  closeTm? = renameTm? (0 ˢ) (const nothing)

  substTm : ∀ {α β} → Supply β → (Name α → Tm β) → Tm α → Tm β
  substTm s f = tr id-app (substKit V coerceTm) (f , s)

  substTmø : ∀ {α} → (Name α → Tm ø) → Tm α → Tm ø
  substTmø = substTm (0 ˢ)

module CoerceTmWithCoerceKit where
  open TrKit coerceKit

  tr : ∀ {α β} → α ⊆ β → Tm α → Tm β
  tr Δ (V x)       = V (trName Δ x)
  tr Δ (t · u)     = tr Δ t · tr Δ u
  tr Δ (ƛ b t)     = ƛ (trBinder Δ b) (tr (extEnv b Δ) t)
  tr Δ (Let b t u) = Let (trBinder Δ b) (tr Δ t) (tr (extEnv b Δ) u)
  tr _ (` κ)       = ` κ

  coerceTmø : Coerceø Tm Tm
  coerceTmø t = tr ⊆-ø t

module SubstCByHand (envPack : Envs.EnvPack L.zero)
              {Ω} (Φ : Name Ω →? Tm ø) where
  open Envs.EnvPack envPack
  open CoerceTmWithCoerceKit using (coerceTmø)

  open M? L.zero

  substCNm : ∀ {α} (Δ : Env ⊤ α Ω) → Name α → Tm α
  substCNm Δ x = maybe′ (λ t → coerceTmø t) (V x) (Φ =<< exportEnv? Δ x)

  substCTm : ∀ {α} (Δ : Env ⊤ α Ω) → Tm α → Tm α
  substCTm Δ (V x)        = substCNm Δ x
  substCTm Δ (t · u)      = substCTm Δ t · substCTm Δ u
  substCTm Δ (ƛ b' t)     = ƛ b' (substCTm (Δ , b' ↦ _) t)
  substCTm Δ (Let b' t u) = Let b' (substCTm Δ t) (substCTm (Δ , b' ↦ _) u)
  substCTm _ (` κ)        = ` κ

  substC : Tm Ω → Tm Ω
  substC = substCTm emptyEnv

-- open SubstCByHand Envs.dataEnv

open TraverseAGen V TraverseTm.tr
  public
  renaming (rename       to renameTm;
            rename?      to renameTm?;
            export?      to exportTm?;
            close?       to closeTm?;
            coerce       to coerceTm;
            coerceˢ      to coerceTmˢ;
            coerceø      to coerceTmø;
            renameCoerce to renameCoerceTm;
            renameA      to renameTmA)

open SubstGen V coerceTm (TraverseTm.tr id-app)
  public
  renaming (subst to substTm;
            substøᴮ to substøᴮTm;
            substC to substCTm;
            substCø to substCøTm;
            substCᴮ to substCᴮTm;
            substCøᴮ to substCøᴮTm;
            openSynAbsᴺ to openSubstTm)

-- coerceˢTm : ∀ {α} (s : Supply α) → Tm α → Tm (Supply.seedᵂ s)
-- coerceˢTm = coerceTm ∘ Supply.seed⊆

V′ : ∀ b {α} → Tm (b ◅ α)
V′ b = V (nameᴮ b)

V` : ∀ k x {α} → Tm ((k + x) ◅… α)
V` k x = V (name◅… k x)

V₀ = V` 0
V₁ = V` 1
V₂ = V` 2
V₃ = V` 3
V₄ = V` 4
V₅ = V` 5
V₆ = V` 6
V₇ = V` 7
V₈ = V` 8

ƛ` : ∀ {α} (n : ℕ) → Tm (n ᴮ ◅ α) → Tm α
ƛ` n = ƛ (n ᴮ)

idTm : ∀ {α} → Tm α
idTm = ƛ x Vx
  where x  = 0 ᴮ
        Vx = V (nameᴮ x)

falseTm : ∀ {α} → Tm α
falseTm = ƛ x (ƛ x Vx)
  where x  = 0 ᴮ
        Vx = V (nameᴮ x)

{-
trueTm : ∀ {α} → Tm α
trueTm {α} = ƛ x (ƛ y (V (nameᴮ x ⟨-because pf -⟩)))
   where x = 0 ᴮ
         y = 1 ᴮ
         open ⊆-Reasoning
         pf = x ◅ ø
            ⊆⟨ ⊆-# (suc# (x #ø)) ⟩
              y ◅ x ◅ ø
            ⊆⟨ ⊆-◅ y (⊆-◅ x ⊆-ø) ⟩
              y ◅ x ◅ α
            ∎
-}

trueTm : ∀ {α} → Tm α
trueTm {α} = ƛ` x (ƛ` y (V₁ x))
   where x = 0
         y = 1

apTm : ∀ {α} → Tm α
apTm = ƛ` f (ƛ` x (V₁ f · V₀ x))
  where f = 0
        x = 1

β-red : ∀ {α} → Supply α → Tm α → Tm α
β-red s (ƛ b fct · arg) = substTm s (exportWith arg V) fct
β-red _ t               = t

β-red′ : ∀ {α b} → Supply α → Tm (b ◅ α) → Tm α → Tm α
β-red′ s fct arg = substTm s (exportWith arg V) fct

import      Category.Monad.Partiality.NP as Pa
open        Pa using (_⊥; run_for_steps; later; now)
open import Coinduction
module CBVBigStepEval where
  open Envs.CEnvPack (Envs.funCEnv {L.zero})
  open Pa.Workaround

  data Val : Set where
    ƛ : ∀
      {α}
      (Δ : Name α → Val)
      (b : Binder)
      (t : Tm (b ◅ α)) → Val
    `_ : Cst → Val

  eval : ∀ {α} → Tm α → CEnv Val α → Val ⊥P
  eval (t · u) Δ = eval u Δ >>= λ v →
                   eval t Δ >>= λ w → app w v
   where
    app : Val → Val → Val ⊥P
    app (ƛ Δ b body)  v = later (♯ eval body (Δ , b ↦ v))
    app (` κ)         v = stuck where postulate stuck : _ ⊥P
  --app (` κ)         v = never

  eval (V x)        Δ  = now (Δ x)
  eval (ƛ b t)      Δ  = now (ƛ Δ b t)
  eval (Let b t u)  Δ  = eval t Δ >>= λ v →
                         eval u (Δ , b ↦ v)
  eval (` κ)        _  = now (` κ)

  eval′ : Tm ø → Val ⊥
  eval′ t = ⟦ eval t Nameø-elim ⟧P

data Val : Set where
  ƛ : ∀ b (t : Tm (b ◅ ø)) → Val
  `_ : Cst → Val

tmVal : Val → Tm ø
tmVal (ƛ b t) = ƛ b t
tmVal (` κ)   = ` κ

module CBNBigStepRed where
  open Pa.Workaround

  redP : Tm ø → Val ⊥P
  redP (t · u) = redP t >>= app where
    app : Val → Val ⊥P
    app (ƛ b body) = later (♯ redP (Let b u body))
    app (` κ)      = stuck where postulate stuck : _ ⊥P
  --app (` κ)      = never

  redP (ƛ b t)      = now (ƛ b t)
  redP (Let b t u)  = later (♯ redP (substøᴮTm b t u))
  redP (` κ)        = now (` κ)
  redP (V x)        = Nameø-elim x

  reduce : Tm ø → Val ⊥
  reduce t = ⟦ redP t ⟧P

module CBVBigStepRed where
  open Pa.Workaround

  redP : Tm ø → Val ⊥P
  redP (t · u) = redP t >>= app where
    app : Val → Val ⊥P
    app (ƛ b body) = later (♯ redP (Let b u body))
    app (` κ)      = stuck where postulate stuck : _ ⊥P

  redP (ƛ b t)      = now (ƛ b t)
  redP (Let b t u)  = redP t >>= λ v → later (♯ redP (substøᴮTm b (tmVal v) u))
  redP (` κ)        = now (` κ)
  redP (V x)        = Nameø-elim x

  reduce : Tm ø → Val ⊥
  reduce t = ⟦ redP t ⟧P

module KAM where -- Krivine Abstract Machine
  open Pa using (now; later)

  Stack = List (Tm ø)

  _★_ : Tm ø → Stack → (Tm ø)⊥
  (t · u)     ★ π        = t ★ (u ∷ π)                   -- push
  (ƛ b t)     ★ (u ∷ π)  = later (♯ (substøᴮTm b u t ★ π)) -- grab
  (Let b t u) ★ π        = later (♯ (substøᴮTm b t u ★ π))
  v           ★ []       = now v
  (` κ)       ★ _        = stuck where postulate stuck : _ ⊥
  (V x)       ★ _        = Nameø-elim x

module FoldTm {R : World → Set}
              (var : ∀ {α} → Name α → R α)
              (app : ∀ {α} → R α → R α → R α)
              (lam : ∀ {α} b → R (b ◅ α) → R α)
              (leT : ∀ {α} b → R α → R (b ◅ α) → R α)
              (cst : ∀ {α} → Cst → R α)
              {Env} (trKit : TrKit Env Name) where
  open TrKit trKit
  ! : ∀ {α β} → Env α β → Tm α → R β
  ! Δ (V x)       = var (trName Δ x)
  ! Δ (t · u)     = app (! Δ t) (! Δ u)
  ! Δ (ƛ b t)     = lam (trBinder Δ b) (! (extEnv b Δ) t)
  ! Δ (Let b t u) = leT (trBinder Δ b) (! Δ t) (! (extEnv b Δ) u)
  ! _ (` κ)       = cst κ

-- Reduce all visible β-redexes, bottom up.
-- This reduce only those already present in the term, hence
-- new redexes may appear as a result of reducing one.
-- As the typecheking tells, this process terminates.
β-reduce-bottom-up : ∀ {α} → Supply α → Tm α → Tm α
β-reduce-bottom-up s₀ = ! (id , s₀)
 where
  open TrKit renameKit
  open SubstEnv using (supply)

  app : ∀ {α} → Supply α → Tm α → Tm α → Tm α
  app s (ƛ b t) u = substTm s (substName u) t
  app _ t       u = t · u

  ! : ∀ {α β} → RenameEnv α β → Tm α → Tm β
  ! Δ (V x)       = V (trName Δ x)
  ! Δ (t · u)     = app (supply Δ) (! Δ t) (! Δ u)
  ! Δ (ƛ b t)     = ƛ _ (! (extEnv b Δ) t)
  ! Δ (Let b t u) = Let _ (! Δ t) (! (extEnv b Δ) u)
  ! _ (` κ)       = ` κ

β-reduce-bottom-upø : Tm ø → ∀ {α} → Tm α
β-reduce-bottom-upø t = coerceTmø (β-reduce-bottom-up (0 ˢ) t)

-- Reduce all β-redexes into "Let"s, bottom up.
-- Since this reduction rule does not introduce new β-redexes, this
-- single-pass bottom-up function indeed reduce them all.
-- As the typecheking tells, this process terminates, and does not
-- refresh the input term.
-- While the built-in term coercion is not necessary (see ƛ⇒Let)
-- it enables to strengthen (at no-cost) the type of
-- βlet-reduce-bottom-up on closed terms as its done in
-- βlet-reduce-bottom-upø.
βlet-reduce-bottom-up : ∀ {α β} → α ⊆ β → Tm α → Tm β
βlet-reduce-bottom-up ⊆w = ! ⊆w
  where app : ∀ {α} → Tm α → Tm α → Tm α
        app (ƛ b t) u = Let b u t
        app t       u = t · u
        open FoldTm {Tm} V app ƛ Let `_
                    {_⊆_} coerceKit

βlet-reduce-bottom-upø : Tm ø → ∀ {α} → Tm α
βlet-reduce-bottom-upø t = βlet-reduce-bottom-up ⊆-ø t

module ƛ⇒Let where
  ⟪_⟫ : ∀ {α} → Tm α → Tm α
  ⟪ ƛ b t · u ⟫ = Let b ⟪ u ⟫ ⟪ t ⟫
  ⟪ V x       ⟫ = V x
  ⟪ t · u     ⟫ = ⟪ t ⟫ · ⟪ u ⟫
  ⟪ ƛ b t     ⟫ = ƛ b ⟪ t ⟫
  ⟪ Let b t u ⟫ = Let b ⟪ t ⟫ ⟪ u ⟫
  ⟪ ` κ       ⟫ = ` κ

module Let⇒ƛ where
  ⟪_⟫ : ∀ {α} → Tm α → Tm α
  ⟪ Let b t u ⟫ = ƛ b ⟪ u ⟫ · ⟪ t ⟫
  ⟪ V x       ⟫ = V x
  ⟪ t · u     ⟫ = ⟪ t ⟫ · ⟪ u ⟫
  ⟪ ƛ b t     ⟫ = ƛ b ⟪ t ⟫
  ⟪ ` κ       ⟫ = ` κ

occurs : ∀ {α} → Name α → Tm α → Bool
occurs x₀ = occ (λ y → x₀ ==ᴺ y)
   where
     OccEnv  : World → Set
     OccEnv  α = Name α → Bool
     extend  : ∀ {α b} → OccEnv α → OccEnv (b ◅ α)
     extend  = exportWith false

     occ : ∀ {α} → OccEnv α → Tm α → Bool
     occ Γ  (V y)        = Γ y
     occ Γ  (t · u)      = occ Γ t ∨ occ Γ u
     occ Γ  (ƛ _ t)      = occ (extend Γ) t
     occ Γ  (Let _ t u)  = occ Γ t ∨ occ (extend Γ) u
     occ _  (` _)        = false

module FreeVarsWithEnv (env : Envs.EnvPack L.zero) where
  open Envs.EnvPack env

  fv' : ∀ {α β} → Env ⊤ α β → Tm α → List (Name β)
  fv' Γ (V x)        = [ [_] , const [] ]′ (lookupEnv Γ x)
  fv' Γ (t · u)      = fv' Γ t ++ fv' Γ u
  fv' Γ (ƛ b t)      = fv' (Γ , b ↦ _) t
  fv' Γ (Let b t u)  = fv' Γ t ++ fv' (Γ , b ↦ _) u
  fv' _ (` _)        = []

  fv : ∀ {α} → Tm α → List (Name α)
  fv = fv' emptyEnv

open FreeVarsWithEnv Envs.dataEnv

module TopDown where
  morphRen : ∀ {α₀ β₀} (ren : RenameEnv α₀ β₀)
               (trans : ∀ {α β} → RenameEnv α β → β₀ ⊆ β → Tm α → Tm β → Tm β)
             → Tm α₀ → Tm β₀
  morphRen {_} {β₀} ren₀ trans = ! (ren₀ , ⊆-refl) where
    open TrKit (renameKit+⊆ β₀)
    Env = SubstEnv+⊆ Name β₀
    mutual
      ! : ∀ {α β} → Env α β → Tm α → Tm β
      ! Δ t = trans ren pf t (!! Δ t) -- lazy semantics is expected
        where open SubstEnv+⊆ Δ

      !! : ∀ {α β} → Env α β → Tm α → Tm β
      !! Δ (V x) = V (trName Δ x)
      !! Δ (ƛ b t) = ƛ _ (! (extEnv b Δ) t)
      !! Δ (t · u) = ! Δ t · ! Δ u
      !! Δ (Let b t u) = Let _ (! Δ t) (! (extEnv b Δ) u)
      !! _ (` κ) = ` κ

  morph : ∀ {α₀ β₀} (s : Supply β₀) (pf : α₀ ⊆ β₀)
                    (trans : ∀ {α β} → Supply β → β₀ ⊆ β → Tm α →? Tm β)
               → Tm α₀ → Tm β₀
  morph s pf trans = morphRen (coerceᴺ pf , s) (λ s pf t dflt → maybe′ id dflt (trans (SubstEnv.supply s) pf t))

  factor : ∀ {α} (s : Supply α) → (∀ {α} → Tm α → Bool) → Tm α → Tm (Supply.seedᴮ s ◅ α)
  factor s pred = morph (sucˢ s) (Supply.seed⊆ s)
                        (λ _ pf t → if pred t then just (V (coerceᴺ pf (Supply.seedᴺ s))) else nothing)

module BottomUp where
  morphRen : ∀ {α₀ β₀} (ren : RenameEnv α₀ β₀)
               (trans : ∀ {β} → Supply β → β₀ ⊆ β → Tm β → Tm β)
             → Tm α₀ → Tm β₀
  morphRen ren trans = TopDown.morphRen ren (λ ren pf _ → trans (SubstEnv.supply ren) pf)

  morph : ∀ {α₀ β₀} (s : Supply β₀) (pf : α₀ ⊆ β₀)
                    (trans : ∀ {β} → Supply β → β₀ ⊆ β → Tm β → Tm β)
                  → Tm α₀ → Tm β₀
  morph s pf = morphRen (coerceᴺ pf , s)

  factor : ∀ {α} (s : Supply α) → (∀ {α} → Tm α → Bool) → Tm α → Tm (Supply.seedᴮ s ◅ α)
  factor s pred = morph (sucˢ s) (Supply.seed⊆ s) (λ _ pf t → if pred t then V (coerceᴺ pf (Supply.seedᴺ s)) else t)

focusᵂ : ∀ {α} → Path → Tm α → World
focusᵂ (ƛ ∷ p)    (ƛ _ t) = focusᵂ p t
focusᵂ (Let₁ ∷ p) (Let _ t _) = focusᵂ p t
focusᵂ (Let₂ ∷ p) (Let _ _ t) = focusᵂ p t
focusᵂ (·₁ ∷ p)   (t · _) = focusᵂ p t
focusᵂ (·₂ ∷ p)   (_ · t) = focusᵂ p t
focusᵂ {α} _ _ = α

focus? : (p : Path) → ∀ {α} (t : Tm α) → Maybe (Tm (focusᵂ p t))
focus? []         t           = just t
focus? (ƛ ∷ p)    (ƛ _ t)     = focus? p t
focus? (·₁ ∷ p)   (t · _)     = focus? p t
focus? (·₂ ∷ p)   (_ · t)     = focus? p t
focus? (Let₁ ∷ p) (Let _ t _) = focus? p t
focus? (Let₂ ∷ p) (Let _ _ t) = focus? p t
focus? _          _           = nothing

defocus : (p : Path) → ∀ {α} (t : Tm α) → Tm (focusᵂ p t) → Tm α
defocus []         _           = id
defocus (ƛ ∷ p)    (ƛ b t)    = ƛ b ∘′ defocus p t
defocus (·₁ ∷ p)   (t · u)     = flip _·_ u ∘′ defocus p t
defocus (·₂ ∷ p)   (t · u)     = _·_ t ∘′ defocus p u
defocus (Let₁ ∷ p) (Let b t u) = (flip (Let b) u) ∘′ defocus p t
defocus (Let₂ ∷ p) (Let b t u) = Let b t ∘′ defocus p u
defocus _          t           = const t

module Conv-Tmᴿ⇒Tm where
  open NomPa.Examples.Raw.DataType String
  record Env α : Set where
    constructor _,_
    field
      trName : String → Name α
      supply : Supply α
    open Supply supply public
  open Env

  extEnv : ∀ {α} → String → (Δ : Env α) → Env (seedᴮ Δ ◅ α)
  extEnv bˢ Δ = trᴺ , sucˢ (supply Δ)
     where trᴺ = λ xˢ → if bˢ == xˢ then seedᴺ Δ else coerceˢ Δ (trName Δ xˢ)

  emptyEnv : Env (0 ᴮ ◅ ø)
  emptyEnv = const (0 ᴺ) , 1 ˢ

  ! : ∀ {α} → Env α → Tmᴿ → Tm α
  ! Δ (V x) = V (trName Δ x)
  ! Δ (ƛ b t) = ƛ _ (! (extEnv b Δ) t)
  ! Δ (t · u) = ! Δ t · ! Δ u

  convø? : Tmᴿ →? Tm ø
  convø? = closeTm? ∘ ! emptyEnv

  conv? : Tmᴿ →? (∀ {α} → Tm α)
  conv? = map? coerceTmø ∘ convø?

open ParseConv Conv-Tmᴿ⇒Tm.conv? public
  renaming (parseConv? to parseTm?; parseConv to parseTm)

open ParseConv Conv-Tmᴿ⇒Tm.convø? public
  renaming (parseConv? to parseTmø?; parseConv to parseTmø; TmOk to TmøOk)

ShowS : Set
ShowS = String → String

module Printer where
  Pr : Set → Set
  Pr A = A → ShowS

  ``_ : String → ShowS
  (`` s) tail = Data.String._++_ s tail

  parenBase : ShowS → ShowS
  parenBase doc = `` "(" ∘ doc ∘ `` ")"

  record PrEnv (α : World) : Set where
    constructor mk
    field
      prName : Pr (Name α)
      fresh  : ℕ
      level  : ℕ

    prBinder : Pr Binder
    prBinder _ = `` "x" ∘ ``(showℕ fresh)

    extend : ∀ {b} → PrEnv (b ◅ α)
    extend {b} = record { prName = exportWith (prBinder b) prName; fresh = suc fresh; level = level }

    withLevel : ℕ → PrEnv α
    withLevel x = record { prName = prName; fresh = fresh; level = x }

    top : PrEnv α
    top = withLevel 2

    ap : PrEnv α
    ap = withLevel 1

    atm : PrEnv α
    atm = withLevel 0

  open PrEnv

  emptyPrEnv : PrEnv ø
  emptyPrEnv = record { prName = Nameø-elim; fresh = zero; level = 2 }

  paren : ∀ {α} → (PrEnv α → PrEnv α) → PrEnv α → ShowS → ShowS
  paren f Δ = if ⌊ level (f Δ) ≤? level Δ ⌋ then id else parenBase

  prTm : ∀ {α} (Δ : PrEnv α) → Pr (Tm α)
  prTm Δ (ƛ b t)     = paren top Δ (`` "λ" ∘ prBinder Δ b ∘ `` ". " ∘ prTm (extend (top Δ)) t)
  prTm Δ (t · u)     = paren ap Δ (prTm (ap Δ) t ∘ `` " " ∘ prTm (atm Δ) u)
  prTm Δ (Let b t u) = `` "let " ∘ prBinder Δ b ∘ `` " = " ∘ prTm (top Δ) t ∘ `` " in "
                                ∘ prTm (extend (top Δ)) u ∘ `` " end"
  prTm Δ (V x)       = prName Δ x
  prTm Δ (` κ)       = ``(showCst κ)

showTmø : Tm ø → String
showTmø t = Printer.prTm Printer.emptyPrEnv t ""
