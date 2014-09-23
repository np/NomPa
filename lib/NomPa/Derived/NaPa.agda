{-# OPTIONS --universe-polymorphism #-}

import Level as L
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Relation.Binary
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality as PropEq hiding (subst)
open import Coinduction
open import Function.NP
open import Data.Bool
open import Data.Indexed
open import Data.List
open import Data.Nat using ( ℕ ; suc ; zero ) renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_)
open import Data.Fin using ( Fin ; suc ; zero )
open import Data.Maybe.NP as Maybe
open import Data.Product
open import Data.Empty
open import Data.Sum using (_⊎_;inj₁;inj₂;[_,_]′) renaming (map to ⊎-map)
open import Data.Star.NP as Star hiding (_>>=_)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary
open import NomPa.Record
import NomPa.Derived
import NomPa.Traverse

module NomPa.Derived.NaPa (nomPa : NomPa) where

open NomPa nomPa hiding (_◅_)
open NomPa.Derived nomPa
open NomPa.Traverse nomPa public using (Add; Shift; Shifted)

SynAbsᴰ : (World → Set) → World → Set
SynAbsᴰ F α = F (α ↑1)

FunAbsᴰ : (World → Set) → World → Set
-- FunAbsᴰ F α = ∀ {β} k → (α +ᵂ k) ⊆ β → (F β → F β)
FunAbsᴰ F = Shifted (F |→| F)

shiftFunAbsᴰ : ∀ {F} → Shift (FunAbsᴰ F) (FunAbsᴰ F)
shiftFunAbsᴰ {_} {α} {β} k ⊆w f {γ} k' ⊆w'
   = f (k' +ℕ k)
       (α +ᵂ (k' +ℕ k)   ⊆⟨ ⊆-assoc-+′ ⊆-refl k k' ⟩
        (α +ᵂ k) +ᵂ k'   ⊆⟨ ⊆-cong-+ ⊆w k' ⟩
        β +ᵂ k'          ⊆⟨ ⊆w' ⟩
        γ ∎)
  where open ⊆-Reasoning

fromFin  : ∀ {α n} → Fin n → Name (α ↑ n)
fromFin zero    = zeroᴺ
fromFin (suc i) = sucᴺ↑ (fromFin i)

toFin : ∀ {n} → Name (ø ↑ n) → Fin n
toFin {zero}  = Nameø-elim
toFin {suc n} = subtractWithᴺ 1 zero (suc ∘′ toFin {n})

infix 10 _ᴺᴰ
_ᴺᴰ : ∀ {α} ℓ → Name (α ↑ suc ℓ)
_ᴺᴰ {α} ℓ = zeroᴺ +ᴺ ℓ ⟨-because (α ↑1 +ᵂ ℓ) ⊆⟨ ⊆-+-↑ ℓ ⟩
                                 α ↑1 ↑  ℓ   ⊆⟨ ⊆-exch-↑-↑ ⊆-refl 1 ℓ ⟩
                                 α ↑ suc ℓ ∎ -⟩
   where open ⊆-Reasoning

rm₀ : ∀ {α} → List (Name (α ↑1)) → List (Name α)
rm₀ [] = []
rm₀ (x ∷ xs) with predᴺ? x
...               |  just x'  = x'  ∷ rm₀ xs
...               |  nothing  = rm₀ xs

data Carry {I : Set} (F : I → I) {a} (A : Set a) : Rel I a where
  carry : ∀ {i} → A → Carry F A i (F i)

record EnvPack ℓ : Set (L.suc ℓ) where
  field
    Env        : Set ℓ → World → World → Set ℓ
    emptyEnv   : ∀ {A α} → Env A α α
    lookupEnv  : ∀ {A α β} → Env A α β → Name β → Name α ⊎ A
    _,,_       : ∀ {α β A} → Env A α β → A → Env A α (β ↑1)
    mapEnv     : ∀ {α β A B} → (A → B) → Env A α β → Env B α β

record ShiftableEnvPack ℓ : Set (L.suc ℓ) where
  field
    envPack : EnvPack ℓ
  open EnvPack envPack
  field
    shiftEnv : ∀ {α β γ A} k → (α +ᵂ k) ⊆ β → Env A α γ → Env A β γ
  open EnvPack envPack public

-- CEnv is for closed Env
record CEnvPack ℓ : Set (L.suc ℓ) where
  field
    CEnv        : Set ℓ → World → Set ℓ
    emptyCEnv   : ∀ {A} → CEnv A ø
    lookupCEnv  : ∀ {A α} → CEnv A α → Name α → A
    _,,_        : ∀ {α A} → CEnv A α → A → CEnv A (α ↑1)
    mapCEnv     : ∀ {α A B} → (A → B) → CEnv A α → CEnv B α

lookupStar : ∀ {α β ℓ} {_↝_ : Rel World ℓ} → (∀ {γ δ} → γ ↝ δ → γ →ᴺ? δ)
             → Star _↝_ α β → Name α → Name β ⊎ ∃₂ _↝_
lookupStar _ ε y = inj₁ y
lookupStar f (x ◅ Γ) y
 with f x y
... | just y' = lookupStar f Γ y'
... | nothing = inj₂ (_ , _ , x)

-- Star does not support univ poly yet
starEnv : EnvPack L.zero
starEnv = record { Env = Env ; emptyEnv = ε ; lookupEnv = lookupEnv
                 ; _,,_ = λ Γ x → carry x ◅ Γ ; mapEnv = mapEnv }
   where
     Env : (A : Set) → Rel World _
     Env = Star⁻¹ ∘ Carry _↑1
{-
     Env A α β = Star⁻¹ (Carry _↑ A) α β
     Env A α β = Star (flip (Carry _↑ A)) β α

     data Env A : Rel World _ where
        ε   : Reflexive (Env A)
        _◅_ : ∀ {β α} (x : A) (xs : Env A α β) → Env A α (β ↑1)

     Env A β α = Σ[ xs ∶ List A ] (β ≡ α ↑ (length xs))
     Env A β α = ∃[ ℓ ] (β ≡ α ↑ ℓ × Vec A ℓ)
-}

     lookupEnv : ∀ {α γ A} → Env A α γ → Name γ → Name α ⊎ A
     lookupEnv ε              = inj₁
     lookupEnv (carry z ◅ Γ) = subtractWithᴺ 1 (inj₂ z) (lookupEnv Γ)

     mapEnv : ∀ {α β A B} → (A → B) → Env A α β → Env B α β
     mapEnv f ε               = ε
     mapEnv f (carry x ◅ xs)  = carry (f x) ◅ mapEnv f xs

{-
shiftableStarEnv : ShiftableEnvPack L.zero
shiftableStarEnv = record { envPack = starEnv ; shiftEnv = {!shiftEnv!} }
  where
    open EnvPack starEnv
{-
    shiftEnv : ∀ {α β γ A} k → α +ᵂ k ⊆ β → Env A α γ → Env A β γ
    shiftEnv k imp ε = {!ε!}
    shiftEnv k imp (carry x ◅ xs) = carry x ◅ shiftEnv {_} {_} {_} {_} k imp xs
-}
    shiftEnv : ∀ {α β A} k → Env A α β → Env A (α +ᵂ k) (β +ᵂ k)
    shiftEnv k ε = {!ε!}
    shiftEnv k (carry x ◅ xs) = {!carry x ◅ {!shiftEnv {_} {_} {_} k xs!}!}
-}

module Env = EnvPack starEnv

closeEnv : EnvPack L.zero → CEnvPack L.zero
closeEnv env
  = record { CEnv = CEnv
           ; emptyCEnv = emptyEnv
           ; lookupCEnv = lookupCEnv
           ; mapCEnv = mapEnv
           ; _,,_ = _,,_ }
  where
    open EnvPack env

    CEnv : Set → World → Set
    CEnv A = Env A ø

    lookupCEnv : ∀ {α τ} → CEnv τ α → Name α → τ
    lookupCEnv Γ = [ Nameø-elim , id ]′ ∘ lookupEnv Γ

module CEnv = CEnvPack (closeEnv starEnv)

funEnv : ∀ {ℓ} → EnvPack ℓ
funEnv {ℓ}
  = record { Env = Env
           ; emptyEnv = inj₁
           ; _,,_ = _,,_
           ; lookupEnv = id
           ; mapEnv = mapEnv }
  where
    Env : Set ℓ → World → World → Set ℓ
    Env A α β = Name β → Name α ⊎ A

    _,,_ : ∀ {α β A} → Env A α β → A → Env A α (β ↑1)
    _,,_ Γ v = subtractWithᴺ 1 (inj₂ v) Γ

    mapEnv : ∀ {α β A B} → (A → B) → Env A α β → Env B α β
    mapEnv f g x = [ inj₁ , inj₂ ∘ f ]′ (g x)

funCEnv : ∀ {ℓ} → CEnvPack ℓ
funCEnv {ℓ}
  = record { CEnv        = CEnv
           ; emptyCEnv   = λ {η} → Nameø-elim
           ; _,,_        = _,,_
           ; lookupCEnv  = id
           ; mapCEnv     = _∘′_ }
  where
    CEnv : Set ℓ → World → Set ℓ
    CEnv A α = Name α → A

    _,,_ : ∀ {α A} → CEnv A α → A → CEnv A (α ↑1)
    _,,_ Γ v = subtractWithᴺ 1 v Γ

shiftableFunEnv : ∀ {ℓ} → ShiftableEnvPack ℓ
shiftableFunEnv = record { envPack = funEnv ; shiftEnv = shiftEnv }
  where
    open EnvPack funEnv
    shiftEnv : ∀ {α β γ A} k → (α +ᵂ k) ⊆ β → Env A α γ → Env A β γ
    shiftEnv k α+k⊆β Γ = ⊎-map (coerceᴺ α+k⊆β ∘ addᴺ k) id ∘ Γ

Su↑ : (F G : World → Set) (α β : World) → Set
Su↑ F G α β = ∀ ℓ → F (α ↑ ℓ) → G (β ↑ ℓ)

Subst : (F G H : World → Set) → Set
Subst F G H = ∀ {α β} → (Name α → H β) → F α → G β

SubstVar : (F : World → Set) → Set
SubstVar F = ∀ {α β} → (Name α → F β) → Su↑ Name F α β

{-
-- This module is more an example of how to write traverse for your data type.
module Traversable {E} (E-app : Applicative E)
                   {F α β} (trName : Su↑ Name (E ∘ F) α β) where
  open Applicative E-app

  Tr : (World → Set) → Set
  Tr G = Su↑ G (E ∘ F) α β

  traverseName : Tr Name
  traverseName = trName

  traverse-× : ∀ {G H} → Tr G → Tr H → Tr (G |×| H)
  traverse-× trG trH ℓ (x , y) = trG ℓ x ⊗ trH ℓ y

  traverseAbs : ∀ {G} → Tr G → Tr (SynAbsᴰ G)
  traverseAbs trG ℓ = trG (suc ℓ)
-}

Traverse : (F G H : World → Set) → Set
Traverse F G H = ∀ {α β} (trName : Su↑ Name H α β) → Su↑ F G α β

TraverseA : (F G H : World → Set) → Set₁
TraverseA F G H = ∀ {E} (E-app : Applicative E) → Traverse F (E ∘ G) (E ∘ H)

Var : (World → Set) → Set
Var F = Name |↦| F

Rename : (F G : World → Set) → Set
Rename F G = ∀ {α β} → (α →ᴺ β) → (F α → G β)

Rename? : (F G : World → Set) → Set
Rename? F G = ∀ {α β} → (α →ᴺ? β) → F α →? G β

RenameA : (F G : World → Set) → Set₁
RenameA F G = ∀ {E} (E-app : Applicative E)
                  {α β} (θ : Name α → E (Name β))
                → F α → E (G β)

Coerce : (F G : World → Set) → Set
Coerce F G = ∀ {α β} → α ⊆ β → F α → G β

Coerceø : (F G : World → Set) → Set
Coerceø F G = F ø → ∀ {α} → G α

Subtract? : (F G : World → Set) → Set
Subtract? F G = ∀ {α} ℓ → F (α ↑ ℓ) →? G α

Close? : (F G : World → Set) → Set
Close? F G = ∀ {α} → F α →? G ø

-- generalizes protect↑ to any Applicative
protect↑A : ∀ {E} (E-app : Applicative E)
              {α β} → (Name α → E (Name β)) → ∀ ℓ → (Name (α ↑ ℓ) → E (Name (β ↑ ℓ)))
protect↑A E-app f ℓ x  with x <ᴺ ℓ
... {- bound -} | inj₁ x′ = pure (x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩)  where open Applicative E-app
... {- free  -} | inj₂ x′ = (_<$>_ (addᴺ↑ ℓ) ∘ f ∘ subtractᴺ ℓ) x′ where open Applicative E-app

shiftName : ∀ {α β} ℓ k → (α +ᵂ k) ⊆ β → (α ↑ ℓ) →ᴺ (β ↑ ℓ)
shiftName ℓ k pf n
             with n <ᴺ ℓ
... {- ℓ-bound -} | inj₁ n′ = n′
                              ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
... {- ℓ-free  -} | inj₂ n′ = (n′ +ᴺ k)
                              ⟨-because ⊆-trans (⊆-exch-+-+ ⊆-refl ℓ k) (⊆-ctx-+↑ pf ℓ) -⟩

shiftName′ : ∀ {α β} ℓ k → (α +ᵂ k) ⊆ β → (α ↑ ℓ) →ᴺ (β ↑ ℓ)
shiftName′ ℓ k pf = protect↑ (coerceᴺ pf ∘ addᴺ k) ℓ

-- generalizes protect↑
substVar : ∀ {F} → Var F → Shift F F → SubstVar F
substVar varF shiftF θ ℓ x
    with x <ᴺ ℓ
...    | inj₁ x′ = varF     (x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩)
...    | inj₂ x′ = shiftF ℓ (⊆-+-↑ ℓ) (θ (x′ ∸ᴺ ℓ))

protect?↑ : ∀ {a α} {A : Set a} → (A → Name α) → (Maybe A → Name (α ↑1))
protect?↑ f = maybe (sucᴺ↑ ∘ f) zeroᴺ

protect↑? : ∀ {a α} {A : Set a} → (Name α → A) → (Name (α ↑1) → Maybe A)
protect↑? f = subtractWithᴺ 1 nothing (just ∘′ f)

{-
rewrite rules
* protect↑ n (coerceᴺ pf) ≗ coerceᴺ (⊆-cong-↑ n pf)
* protect↑ n id ≗ id
* protect↑ ℓ (addᴺ k) ≗ shiftᴺ ℓ k ⊆-refl
* protect↑ n (f ∘ g) ≗ protect↑ n f ∘ protect↑ n g
* protect↑ ℓ (coerceᴺ pf ∘ addᴺ k) ≗ shiftᴺ ℓ k pf
* coerceᴺ ⊆-refl ≗ id

full isos:
* Maybeⁿ ⊥ ≅ Fin n

step isos:
* Maybe ∘ Fin ≅ Fin ∘ suc
* Maybe ∘ Name ≅ Name ∘ _↑1 ≅ SynAbs Name
* ⊥ ≅ Fin 0
* ⊤ ≅ Fin 1
* Bool ≅ Fin 2
* Tmᴹ ∘ Name ≅ Tmᴰ ≅ Tmᴺ
* Name ≅ Name ∘ _+1
* Tmᴺ α ≅ ∃[ b ](Tmᴸ b α)
* Fin ≅ Name ∘ (_↑_ ø)


postulate
  -- 0<1 : ∀ {α} → cmpᴺ {α} 1 zeroᴺ ≡ inj₁ zeroᴺ
  0<1    : ∀ {α} → cmpᴺ {α} 1 zeroᴺ ≡ inj₁ zeroᴺ
  suc≰1 : ∀ {α} → cmpᴺ {α} 1 ∘ sucᴺ↑ ≗ inj₂ ∘ sucᴺ
  predᴺ∘sucᴺ : ∀ {α} → predᴺ {α} ∘ sucᴺ ≗ id

protect↑?∘protect?↑ : ∀ {α a} {A : Set a} (f : Name α → A) (g : A → Name α) →
                      protect↑? f ∘ protect?↑ g ≗ map? (f ∘ g)
protect↑?∘protect?↑ f g (just x) rewrite suc≰1 (g x) = cong (just ∘ f) (predᴺ∘sucᴺ (g x))
protect↑?∘protect?↑ {α} f g nothing rewrite 0<1 {α} = refl

protect?↑∘protect↑? : ∀ {a α} {A : Set a} (f : A → Name α) (g : Name α → A) →
                      protect?↑ f ∘ protect↑? g ≗ protect↑ (f ∘ g) 1
protect?↑∘protect↑? f g x = subtractWithᴺ 1 {!helper₁!} {!helper₁!} x
  where
    helper₁ : maybe (sucᴺ↑ ∘ f) zeroᴺ ∘ subtractWithᴺ 1 nothing (just ∘ g) ≗ protect↑ (f ∘ g) 1
    helper₁ = {!!}
    helper₂ : subtractWithᴺ 1 zeroᴺ (sucᴺ↑ ∘ g) ≗ protect↑ (f ∘ g) 1
    helper₂ = {!!}
-}

module RenameGen {F G} (rename : Rename F G) where
  shift : Shift F G
  shift k ⊆w = rename (coerceᴺ ⊆w ∘ addᴺ k)

  add : Add F G
  add k = shift k ⊆-refl

  coerceø : Coerceø F G
  coerceø t = rename Nameø-elim t

  coerce : Coerce F G
  coerce = rename ∘ coerceᴺ

module RenameAGen {F G} (renameA : RenameA F G) where
  rename : Rename F G
  rename = renameA id-app

  rename? : Rename? F G
  rename? = renameA Maybe.applicative

  subtract? : Subtract? F G
  subtract? = rename? ∘ subtractᴺ?

  close? : Close? F G
  close? = rename? (const nothing)

  open RenameGen rename public

module TraverseFGNameGen {F G} (traverseFGName : Traverse F G Name) where
  shift : Shift F G
  shift k ⊆w = traverseFGName (λ ℓ → shiftName ℓ k ⊆w) 0

  add : Add F G
  add k = shift k ⊆-refl

  coerce : Coerce F G
  coerce pf = traverseFGName (coerceᴺ ∘ ⊆-cong-↑ pf) 0

  coerceø : Coerceø F G
  coerceø t = coerce ⊆-ø t

  rename : Rename F G
  rename θ = traverseFGName (protect↑ θ) 0

  -- open RenameGen rename public

module TraverseAFGNameGen {F G} (traverseAFGName : TraverseA F G Name) where
  renameA : RenameA F G
  renameA E-app θ = traverseAFGName E-app (protect↑A E-app θ) 0

  traverseFGName : Traverse F G Name
  traverseFGName = traverseAFGName id-app

  open TraverseFGNameGen {F} {G} traverseFGName public
  open RenameAGen renameA public hiding (add; shift; rename; coerce; coerceø)

module TraverseAFGGGen {F G} (V : Var G) (traverseAFGG : TraverseA F G G) where
  traverseAFGName : TraverseA F G Name
  traverseAFGName E-app trName = traverseAFGG E-app (λ ℓ x → V <$> trName ℓ x)
     where open Applicative E-app

  open TraverseAFGNameGen {F} {G} traverseAFGName public

module SubstGen {F G} (V : Var G)
                      (shiftGG : Shift G G)
                      (traverseFGG : Traverse F G G) where

  substVarG : SubstVar G
  substVarG = substVar V shiftGG

  subst : Subst F G G
  subst f = traverseFGG (substVarG f) 0

  substName : ∀ {α} → G α → (Name (α ↑1) → G α)
  substName t = subtractWithᴺ 1 t V

  syn2fun : SynAbsᴰ F |↦| FunAbsᴰ G
  syn2fun t k pf u = subst (subtractWithᴺ 1 u (V ∘ shiftName 0 k pf)) t

fun2syn : ∀ {F} (V : Var F) → FunAbsᴰ F |↦| SynAbsᴰ F
fun2syn {F} V {α} f = f 1 ⊆-+1↑1 (V (0 ᴺ))

{-
-- This has more pedagogical value than code-reuse value.
module Substitution {α β} where

  SuF : ∀ F → Set
  SuF F = Su↑ F F α β

  subst-× : ∀ {F₁ F₂ G₁ G₂} → Su↑ F₁ G₁ α β → Su↑ F₂ G₂ α β → Su↑ (F₁ |×| F₂) (G₁ |×| G₂) α β
  subst-× subst₁ subst₂ ℓ (x , y) = (subst₁ ℓ x , subst₂ ℓ y)

  substAbs : ∀ {F G} → Su↑ F G α β → Su↑ (SynAbsᴰ F) (SynAbsᴰ G) α β
  substAbs subst = subst ∘ suc
-}

-- alternative definition of protect↑A using substVar
protect↑A′ : ∀ {E} (E-app : Applicative E)
               {α β} → (Name α → E (Name β)) → ∀ ℓ → (Name (α ↑ ℓ) → E (Name (β ↑ ℓ)))
protect↑A′ E-app θ = substVar pure shift θ
  where open Applicative E-app using (pure; _<$>_)
        open RenameGen _<$>_ using (shift)

|Cmp↑| : (F : World → Set) (α β : World) → Set
|Cmp↑| F α β = ∀ k → |Cmp| F (α ↑ k) (β ↑ k)

cmp↑Name : ∀ {α β} → |Cmp| Name α β → |Cmp↑| Name α β
cmp↑Name Γ k x y with x <ᴺ k | y <ᴺ k
... | inj₁ x′ | inj₁ y′ = x′ ==ᴺ y′
... | inj₂ x′ | inj₂ y′ = Γ (subtractᴺ k x′) (subtractᴺ k y′)
... | _       | _       = false

-- This specialisation of cmp↑Name to k = 1, is the de Bruijn version
-- of the function extendNameCmp used for nominal
cmp↑1Name : ∀ {α β} → |Cmp| Name α β → |Cmp| Name (α ↑1) (β ↑1)
cmp↑1Name Γ = cmp↑Name Γ 1

cmp↑-× : ∀ {α β F G} → |Cmp↑| F α β → |Cmp↑| G α β → |Cmp↑| (F |×| G) α β
cmp↑-× cmpF cmpG k (x₁ , y₁) (x₂ , y₂) = cmpF k x₁ x₂ ∧ cmpG k y₁ y₂

cmp↑Absᴰ : ∀ {α β F} → |Cmp↑| F α β → |Cmp↑| (SynAbsᴰ F) α β
cmp↑Absᴰ cmpF = cmpF ∘ suc
