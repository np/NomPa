open import NomPa.Record
import NomPa.Derived
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Maybe.NP
open import Data.Product.NP
open import Relation.Binary
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Function
open import Data.Indexed

module NomPa.Link (nomPa : NomPa) where

open NomPa nomPa
open NomPa.Derived nomPa

record Link (_↪_ : (α β : World) → Set) : Set where
  constructor mk
  field
    weaken      : ∀ {α β} → α ↪ β → Name α → Name β
    strengthen? : ∀ {α β} → α ↪ β → Name β →? Name α

    -- From binding-links to names
    nameOf : ∀ {α β} → α ↪ β → Name β

  syntax weaken ℓ x      = ℓ $ x
  syntax strengthen? ℓ x = ℓ $⁻¹ x

  strengthenWith : ∀ {A : Set} {α β} → A → (Name α → A) → α ↪ β → Name β → A
  strengthenWith x f ℓ = maybe′ f x ∘ strengthen? ℓ

record FreshLink {_↪_} (link : Link _↪_) : Set where
  constructor mk
  open Link link

  Fresh : World → Set
  Fresh α = ∃[ β ](α ↪ β)

  field
    -- An infinite set of binding-links
    init   : Fresh ø
    next   : ∀ {α} (x : Fresh α) → Fresh (proj₁ x)

  open Link link public

_≡?_ : ∀ {A : Set} → Maybe A → A → Set
just x  ≡? y = x ≡ y
nothing ≡? _ = ⊤

record LinkLaws {_↪_} (link : Link _↪_) : Set where
  constructor mk
  open Link link

  field
    strengthen?-fails   : ∀ {α β} (ℓ : α ↪ β) x → x ≡ nameOf ℓ ⇔ strengthen? ℓ x ≡ nothing
    strengthen?-weaken : ∀ {α β} (ℓ : α ↪ β) x → strengthen? ℓ (weaken ℓ x) ≡ just x
    weaken-strengthen? : ∀ {α β} (ℓ : α ↪ β) x → map? (weaken ℓ) (strengthen? ℓ x) ≡? x
    link-irrelevance    : ∀ {α β} (ℓ₁ ℓ₂ : α ↪ β) → ℓ₁ ≡ ℓ₂

module Nom where
  record _↪_ α β : Set where
    constructor _,_
    field supply : Supply α
    open  Supply supply
    field β-def  : β ≡ seedᴮ ◅ α

  weaken : ∀ {α β} → α ↪ β → Name α → Name β
  weaken (supply , ≡.refl) = coerceᴺ (Supply.seed⊆ supply)

  strengthen? : ∀ {α β} → α ↪ β → Name β →? Name α
  strengthen? (_ , ≡.refl) = exportᴺ?

  nameOf : ∀ {α β} → α ↪ β → Name β
  nameOf ((seedᴮ , _) , ≡.refl) = nameᴮ seedᴮ

  nomLinks : Link _↪_
  nomLinks = mk weaken strengthen? nameOf

  Fresh : World → Set
  Fresh α = ∃[ β ](α ↪ β)

  init : Fresh ø
  init = _ , 0 ˢ , ≡.refl

  next : ∀ {α} (x : Fresh α) → Fresh (proj₁ x)
  next (._ , s , ≡.refl) = _ , sucˢ s , ≡.refl

  -- ⊆-does-not-commute : ¬ (∀ {α β γ} → α ↪ γ → α ⊆ β → ∃[ δ ](γ ⊆ δ × β ↪ δ))

  nomFreshLinks : FreshLink nomLinks
  nomFreshLinks = mk init next

module DeBruijn where
  _↪_ : (α β : World) → Set
  α ↪ β = β ≡ (α ↑1)

  weaken : ∀ {α β} → α ↪ β → Name α → Name β
  weaken ≡.refl = sucᴺ↑

  strengthen? : ∀ {α β} → α ↪ β → Name β →? Name α
  strengthen? ≡.refl = predᴺ?

  nameOf : ∀ {α β} → α ↪ β → Name β
  nameOf ≡.refl = zeroᴺ

  deBruijnLinks : Link _↪_
  deBruijnLinks = mk weaken strengthen? nameOf

  Fresh : World → Set
  Fresh α = ∃[ β ](α ↪ β)

  init : Fresh ø
  init = _ , ≡.refl

  next : ∀ {α} (x : Fresh α) → Fresh (proj₁ x)
  next _ = _ , ≡.refl

  deBruijnFreshLinks : FreshLink deBruijnLinks
  deBruijnFreshLinks = mk init next

  -- unused
  ⊆-commute : ∀ {α β γ} → α ↪ γ → α ⊆ β → ∃[ δ ](γ ⊆ δ × β ↪ δ)
  ⊆-commute ≡.refl pf = _ , ⊆-cong-↑1 pf , ≡.refl

module Traverse {_↪_} {link : Link _↪_} (flink : FreshLink link) where
  open FreshLink flink

  Comm : (_↝_ : Rel World _) → Set
  Comm _↝_ = ∀ {α β γ} → (α ↪ β × α ↝ γ)
                  → ∃[ δ ](γ ↪ δ × β ↝ δ)

  record TrKit (Env : (α β : World) → Set) (Res : World → Set) : Set where
    constructor mk
    field
      trName  : ∀ {α β} → Env α β → Name α → Res β
      commEnv : Comm Env

  -- α →ᴺ β
  -- n     n
  -- |     |
  -- v     v
  -- γ →ᴺ δ
  importFun : ∀ {α β γ δ} → α ↪ γ → β ↪ δ
                           → (Name α → Name β) → (Name γ → Name δ)
  importFun ℓ₁ ℓ₂ f = strengthenWith (nameOf ℓ₂) (weaken ℓ₂ ∘′ f) ℓ₁

  RenameEnv : (α β : World) → Set
  RenameEnv α β = Fresh β × (Name α → Name β)

  renameKit : TrKit RenameEnv Name
  renameKit = mk proj₂ comm
    where
      comm : Comm RenameEnv
      comm (x , (_ , y) , f)
        = _ , y , next (_ , y) , importFun x y f

module LC _↪_ {link : Link _↪_} (flink : FreshLink link) where

 data Tm α : Set where
  V    : (x : Name α) → Tm α
  _·_  : (t u : Tm α) → Tm α
  ƛ    : ∀ {β} (ℓ : α ↪ β) (t : Tm β) → Tm α
  Let  : ∀ {β} (ℓ : α ↪ β) (t : Tm α) (u : Tm β) → Tm α

 open FreshLink flink
 open Traverse flink

 rmℓ : ∀ {α β} → α ↪ β → List (Name β) → List (Name α)
 rmℓ _ []       = []
 rmℓ ℓ (x ∷ xs) with strengthen? ℓ x
 ...               | nothing = rmℓ ℓ xs
 ...               | just x′  = x′ ∷ rmℓ ℓ xs

 fv : ∀ {α} → Tm α → List (Name α)
 fv (V x)       = [ x ]
 fv (t · u)     = fv t ++ fv u
 fv (ƛ ℓ t)     = rmℓ ℓ (fv t)
 fv (Let ℓ t u) = fv t ++ rmℓ ℓ (fv u)

 extendCmpName : ∀ {α β α′ β′} → |Cmp| Name α β → α ↪ α′ → β ↪ β′ → |Cmp| Name α′ β′
 extendCmpName f ℓ₁ ℓ₂ x₁ x₂
  with strengthen? ℓ₁ x₁ | strengthen? ℓ₂ x₂
 ... | just x₁′          | just x₂′ = f x₁′ x₂′
 ... | nothing           | nothing = true
 ... | _                 | _       = false

 cmpTm : ∀ {α β} → |Cmp| Name α β → |Cmp| Tm α β
 cmpTm f (V x)       (V x′)       = f x x′
 cmpTm f (t · u)     (t′ · u′)     = cmpTm f t t′ ∧ cmpTm f u u′
 cmpTm f (ƛ ℓ t)     (ƛ ℓ′ t′)     = cmpTm (extendCmpName f ℓ ℓ′) t t′
 cmpTm f (Let ℓ t u) (Let ℓ′ t′ u′) = cmpTm f t t′
                                  ∧ cmpTm (extendCmpName f ℓ ℓ′) u u′
 cmpTm _ _           _            = false

 _==Tm_ : ∀ {α} → |Cmp| Tm α α
 _==Tm_ = cmpTm _==ᴺ_

 idTm : Tm ø
 idTm = ƛ x (V xᴺ)
   where x = proj₂ init
         xᴺ = nameOf x

 apTm : Tm ø
 apTm = ƛ x (ƛ y (V xᴺ · V yᴺ))
   where x = proj₂ init
         y = proj₂ (next init)
         xᴺ = weaken y (nameOf x)
         yᴺ = nameOf y

 module Tr {Env    : (α β : World) → Set}
           (trKit  : TrKit Env Tm)
  where
  open TrKit trKit
  {-
  Res : World → Set
  Res α = ∀ {β} → Env α β → Tm β

  V′ : Name |↦| Res
  V′ x Γ = trName Γ x

  _·′_ : ∀ {α} (t u : Res α) → Res α
  t ·′ u = λ Γ → t Γ · u Γ

  ƛ′ : ∀ {α β} (ℓ : α ↪ β) (t : Res β) → Res α
  ƛ′ ℓ t Γ with commEnv (ℓ , Γ)
  ... | _ , ℓ′ , Γ′ = ƛ ℓ′ (t Γ′)

  Let′ : ∀ {α β} (ℓ : α ↪ β) (t : Res α) (u : Res β) → Res α
  Let′ ℓ t u Γ with commEnv (ℓ , Γ)
  ... | _ , ℓ′ , Γ′ = Let ℓ′ (t Γ) (u Γ′)

  tr : Tm |↦| Res
  tr (V x)       = V′ x
  tr (t · u)     = tr t ·′ tr u
  tr (ƛ ℓ t)     = ƛ′ ℓ (tr t)
  tr (Let ℓ t u) = Let′ ℓ (tr t) (tr u)
  -}

  tr : ∀ {α β} → Env α β → Tm α → Tm β
  tr Γ (V x)       = trName Γ x
  tr Γ (t · u)     = tr Γ t · tr Γ u
  tr Γ (ƛ ℓ t)     with commEnv (ℓ , Γ)
  ...                 | _ , ℓ′ , Γ′ = ƛ ℓ′ (tr Γ′ t)
  tr Γ (Let ℓ t u) with commEnv (ℓ , Γ)
  ...                 | _ , ℓ′ , Γ′ = Let ℓ′ (tr Γ t) (tr Γ′ u)

 kitVar : ∀ {Env} → TrKit Env Name → TrKit Env Tm
 kitVar (mk trName commEnv) = mk (λ Γ → V ∘ trName Γ) commEnv

 renameTm : ∀ {α β} → Fresh β → (Name α → Name β) → Tm α → Tm β
 renameTm fr f = Tr.tr (kitVar renameKit) (fr , f)

 coerceTm : ∀ {α β} → Fresh β → α ⊆ β → Tm α → Tm β
 coerceTm fr = renameTm fr ∘ coerceᴺ

 weakenTm : ∀ {α β} → α ↪ β → Tm α → Tm β
 weakenTm ℓ t = renameTm (next (_ , ℓ)) (weaken ℓ) t

 SubstEnv : (α β : World) → Set
 SubstEnv α β = Fresh β × (Name α → Tm β)

 substKit : TrKit SubstEnv Tm
 substKit = mk proj₂ comm
   where
     importFunTm : ∀ {α β γ δ} → α ↪ γ → β ↪ δ → (Name α → Tm β)
                                                      → (Name γ → Tm δ)
     importFunTm ℓ₁ ℓ₂ f x
         with strengthen? ℓ₁ x
     ... | nothing = V (nameOf ℓ₂)
     ... | just x′  = weakenTm ℓ₂ (f x′)

     comm : Comm SubstEnv
     comm (x , (_ , y) , f)
       = (_ , y , (next (_ , y) , importFunTm x y f))

 substTm : ∀ {α β} → Fresh β → (Name α → Tm β) → Tm α → Tm β
 substTm fr f = Tr.tr substKit (fr , f)

 substTmø : ∀ {α} → (Name α → Tm ø) → Tm α → Tm ø
 substTmø = substTm init

 _[_≔_] : ∀ {α} → Tm α → ø ↪ α → Tm ø → Tm ø
 t [ x ≔ u ] = substTmø (strengthenWith u V x) t

 β-red : Tm ø → Tm ø
 β-red (ƛ ℓ t · u) = t [ ℓ ≔ u ]
 β-red t = t

{-
  strengthen?-fails : ∀ {α β} (ℓ : α ↪ β) x → x ≡ nameOf ℓ ⇔ strengthen? ℓ x ≡ nothing
  strengthen?-fails ≡.refl x = equivalence {!!} {!!}

  strengthen?-weaken : ∀ {α β} (ℓ : α ↪ β) x → strengthen? ℓ (weaken ℓ x) ≡ just x
  strengthen?-weaken ≡.refl x = {!!}

  link-irrelevance : ∀ {α β} (ℓ₁ ℓ₂ : α ↪ β) → ℓ₁ ≡ ℓ₂
  link-irrelevance ≡.refl ≡.refl = ≡.refl

  weaken-strengthen? : ∀ {α β} (ℓ : α ↪ β) x → map? (weaken ℓ) (strengthen? ℓ x) ≡? x
  weaken-strengthen? ≡.refl x = {!!}

  deBruijnLinksLaws : LinkLaws deBruijnLinks
  deBruijnLinksLaws = mk strengthen?-fails strengthen?-weaken weaken-strengthen? link-irrelevance
-}

module FreshStream _↪_ {link : Link _↪_} (flink : FreshLink link) where
  open import Coinduction
  open FreshLink flink

  data FreshStream (α : World) : Set where
    _∷_ : ∀ {β} (ℓ : α ↪ β) (tl : ∞ (FreshStream β)) → FreshStream α

  enumFrom : ∀ {α} → Fresh α → FreshStream α
  enumFrom ℓ = proj₂ ℓ ∷ ♯ (enumFrom (next ℓ))

  freshStream : FreshStream ø
  freshStream = enumFrom init

-- The ``coincidence'' I'm trying to understand here starts from the fact that
-- the three operations of Link are all projecting something out of a link.
-- Hence we could capture these three operations as three projections of a record
-- called L here.
-- The definiton for link says that the record type L perfectly fits the interface Link.
-- Each operation is a projection.
-- The function linkL combine the three operations as a single operation returning a record L.
-- Then define freshL which states that we can build an L link for any world.
-- Indeed the definition reveals the trick, our choose L link the de Bruijn link which is
-- canonical.
-- We seems to not have enough information to build nominal links, though.
-- Then we make a defintion for FreshLink link, which states that we can produce
-- as many links we want. However using freshL is simpler.

record L α β : Set where
  constructor mk
  field
    weaken      : Name α → Name β
    strengthen? : Name β →? Name α
    nameOf      : Name β

link : Link L
link = mk L.weaken L.strengthen? L.nameOf

linkL : ∀ {_↪_} (link : Link _↪_) {α β} → α ↪ β → L α β
linkL link ℓ = mk (weaken ℓ) (strengthen? ℓ) (nameOf ℓ)
  where open Link link

FreshL : World → Set
FreshL α = ∃[ β ](L α β)

freshL : ∀ {α} → FreshL α
freshL = _ , mk sucᴺ↑ predᴺ? zeroᴺ

freshLink : FreshLink link
freshLink = mk freshL (λ _ → freshL)
  where open Link link

dbL : ∀ {α} → L α (α ↑1)
dbL = mk sucᴺ↑ predᴺ? zeroᴺ
-- or dbL = linkL DeBruijn.deBruijnLinks ≡.refl
-- or dbL = proj₂ freshL

nomL : ∀ {α b} → b # α → L α (b ◅ α)
nomL b# = linkL nomLinks ((_ , b#) , ≡.refl)
  where open Nom

{-
-- Self-contained
record ComPa : Set₁ where
  constructor mk

  infix 3 _↪_

  field
    -- minimal kit to define types
    World  : Set
    Name   : World → Set
    _↪_  : World → World → Set

    -- There is no name in the empty world
    ø      : World
    ¬Nameø : ¬ (Name ø)

    -- Names are comparable
    _==ᴺ_   : ∀ {α} (x y : Name α) → Bool
    -- law: ==ᴺ decides equality

    link : Link _↪_
    flink : FreshLink link
  open FreshLink flink public
-}
