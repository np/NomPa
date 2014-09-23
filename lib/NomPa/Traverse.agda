{-# OPTIONS --universe-polymorphism #-}
open import NomPa.Record
import      NomPa.Derived
open import Data.Maybe.NP as Maybe
open import Data.Sum
open import Data.Product
open import Function.NP
open import Category.Monad
            renaming (RawMonad to Monad; module RawMonad to Monad)
open import Category.Applicative
            renaming (RawApplicative to Applicative; module RawApplicative to Applicative)
import      Category.Monad.Identity as Id
import      Relation.Binary.PropositionalEquality as ≡
open import Data.Indexed
open ≡ using (_≡_)

module NomPa.Traverse (nompa : NomPa) where

open NomPa nompa
open NomPa.Derived nompa

Rename : (F G : World → Set) → Set
Rename F G = ∀ {α β} → Supply β → (α →ᴺ β) → (F α → G β)

RenameA : (F G : World → Set) → Set₁
RenameA F G = ∀ {E} (E-app : Applicative E) →
              ∀ {α β} → Supply β → (Name α → E (Name β)) → (F α → E (G β))

Rename? : (F G : World → Set) → Set
Rename? F G = ∀ {α β} → Supply β → (α →ᴺ? β) → F α →? G β

Coerce : (F G : World → Set) → Set
Coerce F G = ∀ {α β} → α ⊆ β → F α → G β

Coerceˢ : (F G : World → Set) → Set
Coerceˢ F G = ∀ {α} (s : Supply α) → F α → G (Supply.seedᵂ s)

Coerceø : (F G : World → Set) → Set
Coerceø F G = F ø → ∀ {α} → G α

Export? : (F G : World → Set) → Set
Export? F G = ∀ {b α} → Supply α → F (b ◅ α) →? G α

Close? : (F G : World → Set) → Set
Close? F G = ∀ {α} → F α →? G ø

Subst : (F G : World → Set) → Set
Subst F G = ∀ {α β} → Supply β → (Name α → G β) → F α → G β

Substø : (F G : World → Set) → Set
Substø F G = ∀ {α} → (Name α → G ø) → F α → G ø

SubstCø : (F G : World → Set) → Set
SubstCø F G = ∀ {α} → (Name α → |∀| G) → F α → G ø

SubstCᴮ : (F G : World → Set) → Set
SubstCᴮ F G = ∀ {α} b → Supply α → |∀| G → F (b ◅ α) → G α

SubstCøᴮ : (F G : World → Set) → Set
SubstCøᴮ F G = ∀ b → |∀| G → F (b ◅ ø) → G ø

-- Substø/C F G = ∀ {α} → (Name α → G ø) → F α → |∀| G

SubstC? : (F G : World → Set) → Set
SubstC? F G = ∀ {α} → (Name α →? |∀| G) → F α → G α

SubstC : (F G : World → Set) → Set
SubstC F G = ∀ {α β} → Supply β → (Name α → Name β ⊎ |∀| G) → F α → G β

Shift : (F G : World → Set) → Set
Shift F G = ∀ {α β} k → (α +ᵂ k) ⊆ β → F α → G β

Shifted : (World → Set) → (World → Set)
Shifted F α = ∀ {β} k → (α +ᵂ k) ⊆ β → F β

Add : (F G : World → Set) → Set
Add F G = ∀ {α} k → F α → G (α +ᵂ k)

EnvType : Set₁
EnvType = (α β : World) → Set

TrName : (Env : EnvType) (Res : World → Set) → Set
TrName Env Res = ∀ {α β} → Env α β → Name α → Res β

TrBinder : (Env : EnvType) → Set
TrBinder Env = ∀ {α β} → Env α β → Binder → Binder

ExtEnv : (Env : EnvType) (trBinder : TrBinder Env) → Set
ExtEnv Env trBinder = ∀ {α β} b (Δ : Env α β) → Env (b ◅ α) (trBinder Δ b ◅ β)

record TrKit (Env : EnvType) (Res : World → Set) : Set where
  constructor mk
  field
    trName   : TrName Env Res
    trBinder : TrBinder Env
    extEnv   : ExtEnv Env trBinder

coerceKit : TrKit _⊆_ Name
coerceKit = mk coerceᴺ (const id) ⊆-◅

≡-kit : TrKit _≡_ Name
≡-kit = mk (≡.subst Name) (const id) (λ b → ≡.cong (_◅_ b))

mapKit : ∀ {Env F G} (f : Name |↦| Name) (g : F |↦| G)
         → TrKit Env F → TrKit Env G
mapKit f g kit = mk (λ Δ → g ∘ trName Δ ∘ f) trBinder extEnv
  where open TrKit kit

record CompEnv (Env₁ Env₂ : EnvType) α γ : Set where
  constructor _,_
  field
    {β}  : World
    env₁ : Env₁ α β
    env₂ : Env₂ β γ

composeKits : ∀ {⇒₁ ⇒₂ Res} → TrKit ⇒₁ Name → TrKit ⇒₂ Res → TrKit (CompEnv ⇒₁ ⇒₂) Res
composeKits {⇒₁} {⇒₂} {Res} kit₁ kit₂ = mk trName trBinder extEnv
  where
   module K₁ = TrKit kit₁
   module K₂ = TrKit kit₂
   Env = CompEnv ⇒₁ ⇒₂
   trName : ∀ {α β} → Env α β → Name α → Res β
   trName (Δ₁ , Δ₂) x = K₂.trName Δ₂ (K₁.trName Δ₁ x)
   trBinder : ∀ {α β} → Env α β → Binder → Binder
   trBinder (Δ₁ , Δ₂) b = K₂.trBinder Δ₂ (K₁.trBinder Δ₁ b)
   extEnv : ∀ {α β} b (Δ : Env α β) → Env (b ◅ α) (trBinder Δ b ◅ β)
   extEnv b (Δ₁ , Δ₂) = K₁.extEnv b Δ₁ , K₂.extEnv (K₁.trBinder Δ₁ b) Δ₂

syntax composeKits x y = y ∘-Kit x

record SubstEnv (Res : World → Set) α β : Set where
  constructor _,_
  field
    trName  : Name α → Res β
    supply : Supply β
  open Supply supply public
  trBinder : Binder → Binder
  trBinder _ = seedᴮ

RenameEnv = SubstEnv Name

substEnvˢ : ∀ {Res} n → SubstEnv Res ø (n ˢʷ)
substEnvˢ n = Nameø-elim , n ˢ

substEnvø : ∀ {Res} → SubstEnv Res ø ø
substEnvø = substEnvˢ 0

renameEnvˢ : ∀ n → RenameEnv ø (n ˢʷ)
renameEnvˢ = substEnvˢ

renameEnvø : RenameEnv ø ø
renameEnvø = renameEnvˢ 0

RenameAEnv : (E : Set → Set) → EnvType
RenameAEnv E = SubstEnv (E ∘ Name)

renameAKit : ∀ {E} (E-app : Applicative E) → TrKit (RenameAEnv E) (E ∘ Name)
renameAKit {E} E-app = mk trName trBinder extEnv
  where
    open SubstEnv
    Env = RenameAEnv E
    extEnv : ExtEnv Env trBinder
    extEnv _ (trName , (s , s#)) = trName′ , sucˢ (Supply._,_ s s#) where
      open Applicative E-app
      trName′ = exportWith (pure (nameᴮ s)) -- bound
                          (_<$>_ (coerceᴺ (⊆-# s#)) ∘ trName) -- free

module RenameKitByHand where
 renameKit : TrKit RenameEnv Name
 renameKit = mk trName trBinder extEnv
  where
    open SubstEnv
    extEnv : ExtEnv RenameEnv trBinder
    extEnv _ (trName , (s , s#)) = trName′ , sucˢ (Supply._,_ s s#)
     where
      trName′ = exportWith (nameᴮ s) -- bound
                           (coerceᴺ (⊆-# s#) ∘ trName) -- free

renameKit : TrKit RenameEnv Name
renameKit = renameAKit id-app

record SubstEnv+⊆ Res β₀ α β : Set where
  constructor _,_
  field
    ren : SubstEnv Res α β
    pf  : β₀ ⊆ β
  open SubstEnv ren public

renameAKit+⊆ : ∀ {E} (E-app : Applicative E) β₀ → TrKit (SubstEnv+⊆ (E ∘ Name) β₀) (E ∘ Name)
renameAKit+⊆ {E} E-app β₀ = mk trName trBinder extEnv
  where
    Env = SubstEnv+⊆ (E ∘ Name) β₀
    open SubstEnv+⊆
    extEnv : ExtEnv Env trBinder
    extEnv b (ren , pf) =
       (TrKit.extEnv (renameAKit E-app) b ren , ⊆-trans pf (SubstEnv.seed⊆ ren))

-- we could simply give id-app to renameAKit+⊆ but this version has
-- some pedagogical value.
renameKit+⊆ : ∀ β₀ → TrKit (SubstEnv+⊆ Name β₀) Name
renameKit+⊆ β₀ = mk trName trBinder extEnv
  where
    Env = SubstEnv+⊆ Name β₀
    open SubstEnv+⊆
    extEnv : ExtEnv Env trBinder
    extEnv b (ren , pf) =
       (TrKit.extEnv renameKit b ren , ⊆-trans pf (SubstEnv.seed⊆ ren))

substKit : ∀ {F}
             (V      : Name |↦| F)
             (coerce : Coerce F F)
           → TrKit (SubstEnv F) F
substKit {F} V coerce = mk SubstEnv.trName SubstEnv.trBinder extEnv
  where
    open Supply
    Env = SubstEnv F
    extEnv : ExtEnv Env SubstEnv.trBinder
    extEnv b (trName , s) = trName′ , sucˢ s where
      trName′ = exportWith
                 (V (nameᴮ (seedᴮ s))) -- bound
                 (coerce (⊆-# (seed# s)) ∘ trName) -- free

record SubstC?Env (F : World → Set) (α β : World) : Set where
  constructor _,_
  field
    α≡β    : α ≡ β
    trName? : Name α →? (∀ {α} → F α)
  trBinder : Binder → Binder
  trBinder = id

substC?Kit : ∀ {F} (V : Name |↦| F)
             → TrKit (SubstC?Env F) F
substC?Kit {F} V = mk trName SubstC?Env.trBinder extEnv
  where
    Env = SubstC?Env F
    trName : TrName Env F
    trName (≡.refl , trName?) x = maybe′ (λ x → x {_}) (V x) (trName? x)
    extEnv : ExtEnv Env SubstC?Env.trBinder
    extEnv b (≡.refl , trName?) = ≡.refl , exportWith nothing trName?

SubstCEnv : (F : World → Set) → EnvType
SubstCEnv F = SubstEnv (λ β → Name β ⊎ |∀| F)

substCKit : ∀ {F} (V : Name |↦| F)
             → TrKit (SubstCEnv F) F
substCKit {F} V = mk trName SubstEnv.trBinder extEnv
  where
    Env = SubstCEnv F
    trName : TrName Env F
    trName (f , _) x = [ V , (λ x → x {_}) ]′ (f x)
    extEnv : ExtEnv Env SubstEnv.trBinder
    extEnv b (f , s) = (exportWith (inj₁ (nameᴮ _)) ([ inj₁ ∘ coerceᴺ (Supply.seed⊆ s) , inj₂ ]′ ∘ f) , sucˢ s)

-- AddKit cannot directly extended to support subtractions
-- (like with dB levels) since binders hidden in abstractions
-- are arbitrary and thus may not be large enough to support
-- the subtraction. With dB levels the root binder reveals
-- the lowest binder and thus can support subtractions.
-- Addition is always possible since the operation is total
-- and no assumption is made on the input of addition.
module AddKit k where
  Env : EnvType
  Env α β = (α +ᵂ k) ⊆ β

  trName : TrName Env Name
  trName pf = coerceᴺ pf ∘ addᴺ k

  trBinder : TrBinder Env
  trBinder _ b = b +ᴮ k

  extEnv : ExtEnv Env trBinder
  extEnv b pf = ⊆-trans (⊆-dist-+-◅ k) (⊆-◅ (b +ᴮ k) pf)

  kit : TrKit Env Name
  kit = mk trName trBinder extEnv

open AddKit public using () renaming (kit to addKit)

import Data.Star as S
starKit : ∀ {Env} → TrKit Env Name → TrKit (S.Star Env) Name
starKit {Env} kit = mk trName★ trBinder★ extEnv★
  where open S renaming (_◅_ to _∷_)
        open TrKit kit
        Env★ = Star Env

        trName★ : TrName Env★ Name
        trName★ ε = id
        trName★ (Δ ∷ Δ★) = trName★ Δ★ ∘ trName Δ

        trBinder★ : TrBinder Env★
        trBinder★ ε = id
        trBinder★ (Δ ∷ Δ★) = trBinder★ Δ★ ∘ trBinder Δ

        extEnv★ : ExtEnv Env★ trBinder★
        extEnv★ _ ε = ε
        extEnv★ _ (Δ ∷ Δ★) = extEnv _ Δ ∷ extEnv★ _ Δ★

-- De Bruijn Levels Kits

EnvTypeᴸ : Set₁
EnvTypeᴸ = (b₁ b₂ : Binder) (α β : World) → Set

TrNameᴸ : (Env : EnvTypeᴸ) (Res : Binder → World → Set) → Set
TrNameᴸ Env Res = ∀ {b₁ b₂ α β} → Env b₁ b₂ α β → Name α → Res b₂ β

ExtEnvᴸ : (Env : EnvTypeᴸ) → Set
ExtEnvᴸ Env = ∀ {b₁ b₂ α β} → Env b₁ b₂ α β → Env (sucᴮ b₁) (sucᴮ b₂) (b₁ ◅ α) (b₂ ◅ β)

record TrKitᴸ (Env : EnvTypeᴸ)
              (Res : Binder → World → Set) : Set where
  constructor mk
  field
    trNameᴸ : TrNameᴸ Env Res
    extEnvᴸ : ExtEnvᴸ Env

-- Further generalized by Addᴸ and AddSubtractᴸ
CoerceEnvᴸ : EnvTypeᴸ
CoerceEnvᴸ b₁ b₂ α β = b₁ ≡ b₂ × α ⊆ β

coerceKitᴸ : TrKitᴸ CoerceEnvᴸ (const Name)
coerceKitᴸ = mk (coerceᴺ ∘ proj₂) extEnv where
  extEnv : ExtEnvᴸ CoerceEnvᴸ
  extEnv (≡.refl , pf) = ≡.refl , ⊆-◅ _ pf

-- ≡-Kitᴸ, composeKitsᴸ

record SubstEnvᴸ (Res : Binder → World → Set) (b₁ b₂ : Binder) (α β : World) : Set where
  constructor _,_
  field
    trNameᴸ : Name α → Res b₂ β
    b₂#β    : b₂ # β

RenameEnvᴸ : EnvTypeᴸ
RenameEnvᴸ = SubstEnvᴸ (const Name)

module Renameᴸ where
  Envᴸ = RenameEnvᴸ

  -- open SubstEnvᴸ public using (trNameᴸ)
  trNameᴸ : TrNameᴸ Envᴸ (const Name)
  trNameᴸ = SubstEnvᴸ.trNameᴸ

  -- The type is more general than ExtEnvᴸ Envᴸ on purpose
  extEnvᴸ : ∀ {b₁ b₁′ b₁′′ b₂ α β}
            → RenameEnvᴸ b₁ b₂ α β
            → RenameEnvᴸ b₁′ (sucᴮ b₂) (b₁′′ ◅ α) (b₂ ◅ β)
  extEnvᴸ (trNameᴸ , b₂#β)
    = (exportWith (nameᴮ _) (coerceᴺ (⊆-# b₂#β) ∘ trNameᴸ)) , suc# b₂#β

renameKitᴸ : TrKitᴸ RenameEnvᴸ (const Name)
renameKitᴸ = mk trNameᴸ extEnvᴸ where open Renameᴸ

module RenameAᴸ {E : Set → Set} (E-app : Applicative E) where
  open Applicative E-app

  Envᴸ = SubstEnvᴸ (const (E ∘ Name))

  -- open SubstEnvᴸ public using (trNameᴸ)
  trNameᴸ : TrNameᴸ Envᴸ (const (E ∘ Name))
  trNameᴸ = SubstEnvᴸ.trNameᴸ

  extEnvᴸ : ExtEnvᴸ Envᴸ
  extEnvᴸ (trName , b₂#β)
    = exportWith (pure (nameᴮ _)) (_<$>_ (coerceᴺ (⊆-# b₂#β)) ∘ trName) , suc# b₂#β

  kitᴸ : TrKitᴸ Envᴸ (const (E ∘ Name))
  kitᴸ = mk trNameᴸ extEnvᴸ

open RenameAᴸ public using () renaming (kitᴸ to renameAKitᴸ)

module Substᴸ {F : Binder → World → Set}
              (V : ∀ {b} → Name |↦| F b)
              (importF : ∀ {b α} → b # α → F b α → F (sucᴮ b) (b ◅ α)) where
  Envᴸ = SubstEnvᴸ F

  -- open SubstEnvᴸ public using (trNameᴸ)
  trNameᴸ : TrNameᴸ Envᴸ F
  trNameᴸ = SubstEnvᴸ.trNameᴸ

  extEnvᴸ : ExtEnvᴸ Envᴸ
  extEnvᴸ (trNameᴸ , b₂#β)
    = exportWith (V (nameᴮ _)) (importF b₂#β ∘′ trNameᴸ) , suc# b₂#β

  kitᴸ : TrKitᴸ Envᴸ F
  kitᴸ = mk trNameᴸ extEnvᴸ

open Substᴸ public using () renaming (kitᴸ to substKitᴸ)

-- Further generalized by AddSubtractᴸ
module Addᴸ k where
  Envᴸ : EnvTypeᴸ
  Envᴸ b₁ b₂ α β = (α +ᵂ k) ⊆ β × (b₁ +ᴮ k) ≡ b₂

  trNameᴸ : TrNameᴸ Envᴸ (const Name)
  trNameᴸ (pf , _) = coerceᴺ pf ∘ addᴺ k

  extEnvᴸ : ExtEnvᴸ Envᴸ
  extEnvᴸ (pf , ≡.refl) = ⊆-trans (⊆-dist-+-◅ k) (⊆-◅ _ pf) , +ᴮ-dist1 k

  kitᴸ : TrKitᴸ Envᴸ (const Name)
  kitᴸ = mk trNameᴸ extEnvᴸ

open Addᴸ public using () renaming (kitᴸ to addKitᴸ)

module AddSubtractᴸ k₁ k₂ where
  Envᴸ : EnvTypeᴸ
  Envᴸ b₁ b₂ α β = (b₁ +ᴮ k₁) ≡ (b₂ +ᴮ k₂) × (α +ᵂ k₁) ⊆ (β +ᵂ k₂)

  ⊆-◅′ : ∀ {α β b₁ b₂} → b₁ ≡ b₂ → α ⊆ β → b₁ ◅ α ⊆ b₂ ◅ β
  ⊆-◅′ ≡.refl = ⊆-◅ _

  trNameᴸ : TrNameᴸ Envᴸ (const Name)
  trNameᴸ (_ , pf) = subtractᴺ k₂ ∘ coerceᴺ pf ∘ addᴺ k₁

  extEnvᴸ : ExtEnvᴸ Envᴸ
  extEnvᴸ (eq , pf) = ≡.trans (+ᴮ-dist1 k₁) (≡.trans (≡.cong sucᴮ eq) (≡.sym (+ᴮ-dist1 k₂)))
                    , ⊆-trans (⊆-trans (⊆-dist-+-◅ k₁) (⊆-◅′ eq ⊆-refl))
                      (⊆-trans (⊆-◅ _ pf) (⊆-dist-◅-+ k₂))

  kitᴸ : TrKitᴸ Envᴸ (const Name)
  kitᴸ = mk trNameᴸ extEnvᴸ

open AddSubtractᴸ public using () renaming (kitᴸ to addSubtractKitᴸ)

Traverse : (F G H : World → Set) → Set₁
Traverse F G H = ∀ {Env} → TrKit Env H →
                 ∀ {α β} → Env α β → F α → G β

TraverseA : (F G H : World → Set) → Set₁
TraverseA F G H = ∀ {E} (E-app : Applicative E) → Traverse F (E ∘ G) (E ∘ H)

module Rename?Gen {F G} (rename? : Rename? F G) where
  export? : Export? F G
  export? supply = rename? supply exportᴺ?

  close? : Close? F G
  close? = rename? (0 ˢ) (const nothing)

module RenameAGen {F G} (renameA : RenameA F G) where
  rename : Rename F G
  rename = renameA id-app

  rename? : Rename? F G
  rename? = renameA Maybe.applicative

  open Rename?Gen rename? public

module TraverseGen {F G} (traverse : Traverse F G Name) where
  coerce : Coerce F G
  coerce = traverse coerceKit

  coerceˢ : Coerceˢ F G
  coerceˢ = coerce ∘ Supply.seed⊆

  coerceø : Coerceø F G
  coerceø t = coerce ⊆-ø t

  rename : Rename F G
  rename supply f = traverse renameKit (f , supply)

  renameCoerce : ∀ {α β γ} → Supply β → (α →ᴺ β) → β ⊆ γ → (F α → G γ)
  renameCoerce supply f β⊆γ = traverse (coerceKit ∘-Kit renameKit) ((f , supply) , β⊆γ)

  -- shift maybe a confusing name
  shift : Shift F G
  shift k pf = traverse (addKit k) pf

  add : Add F G
  add k = shift k ⊆-refl

module TraverseAFGNameGen {F G} (traverseAFGName : TraverseA F G Name) where
  traverse : Traverse F G Name
  traverse = traverseAFGName id-app

  renameA : RenameA F G
  renameA E-app supply f = traverseAFGName E-app (renameAKit E-app) (f , supply)

  open TraverseGen  traverse  public
  open RenameAGen renameA public hiding (rename)

-- These functions have no access to a coerce function.
-- They have a lower complexity: O(n * log n) where
--    * n is the size of the input term
--    * the initial mapping is supposed constant
--    * log n is took as an approximation of the height of the term
--    * the height is an approximation of the number of binders between
--      the root and a variable.
--    * assuming world erasing is performed
module SubstCGen {F G} (V : Name |↦| G) (traverseFGG : Traverse F G G) where
  substC : SubstC F G
  substC supply f = traverseFGG (substCKit V) (f , supply)

  substC? : SubstC? F G
  substC? f = traverseFGG (substC?Kit V) (≡.refl , f)

  substCø : SubstCø F G
  substCø f = substC (0 ˢ) (inj₂ ∘ f)

  substCᴮ : SubstCᴮ F G
  substCᴮ _ supply v t = substC supply (exportWith (inj₂ (λ {_} → v)) inj₁) t

  substCøᴮ : SubstCøᴮ F G
  substCøᴮ _ v = substCø (λ x → exportWith v Nameø-elim x)

  -- helper function
  substName : ∀ {b α} → G α → (Name (b ◅ α) → G α)
  substName t = exportWith t V

module TraverseAGen {F G} (V : Name |↦| G) (traverseAFGG : TraverseA F G G) where
  traverseAFGName : TraverseA F G Name
  traverseAFGName E-app trKit = traverseAFGG E-app (mapKit id (_<$>_ V) trKit)
     where open Applicative E-app
  open TraverseAFGNameGen traverseAFGName public

module SubstøGen {F G}
                 (V           : Name |↦| G)
                 (coerceø     : Coerceø G G)
                 (traverseFGG : Traverse F G G) where

  open SubstCGen V traverseFGG public

  substø : Substø F G
  substø f = substCø (coerceø ∘ f)

  -- Here the cost of coerce is amortized (assuming world erasing)
  -- since it is performed once and for all.
  substøᴮ : ∀ b → G ø → F (b ◅ ø) → G ø
  substøᴮ _ = substCøᴮ _ ∘ coerceø

  -- Not more than substøᴮ with its arguments reordered.
  -- This function opens an abstraction as in Locally Nameless
  openSynAbsᴺ : G ø → SynAbsᴺ F ø → G ø
  openSynAbsᴺ v (b , t) = substøᴮ b v t

-- These substitution functions have a higher complexity
-- than those from SubstCGen (except substøᴮ) since calls
-- to the coerce function for each matching variable.
-- However if we assume that calls to coerce are erased
-- by an optimizing compiler then they are as good as SubstCGen.
module SubstGen {F G}
                (V           : Name |↦| G)
                (coerce      : Coerce G G)
                (traverseFGG : Traverse F G G) where
  subst : Subst F G
  subst supply f = traverseFGG (substKit V coerce) (f , supply)

  open SubstøGen V (λ η → coerce ⊆-ø η) traverseFGG public
