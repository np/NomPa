{-# OPTIONS --universe-polymorphism #-}
module NaPa.Derived where

import Level as L
open import Category.Applicative renaming (module RawApplicative to Applicative; RawApplicative to Applicative)
open import Relation.Binary
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality as PropEq hiding (subst)
open import Coinduction
open import Function.NP
open import Data.Bool
open import Data.Indexed
open import Data.Nat using ( ℕ ; suc ; zero ) renaming (_≟_ to _≟ℕ_; _+_ to _+ℕ_)
open import Data.Maybe.NP as Maybe
open import Data.Product
open import Data.Empty
open import Data.Sum using (_⊎_;inj₁;inj₂;[_,_]′) renaming (map to ⊎-map)
open import Data.Star.NP as Star hiding (_>>=_)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary
open import NaPa

Shift : (F G : World → Set) → Set
Shift F G = ∀ {α β} k → (α +ᵂ k) ⊆ β → F α → G β

Shifted : (World → Set) → (World → Set)
Shifted F α = ∀ {β} k → (α +ᵂ k) ⊆ β → F β

SynAbs : (World → Set) → World → Set
SynAbs F α = F (α ↑1)

FunAbs : (World → Set) → World → Set
-- FunAbs F α = ∀ {β} k → (α +ᵂ k) ⊆ β → (F β → F β)
FunAbs F = Shifted (F |→| F)

shiftFunAbs : ∀ {F} → Shift (FunAbs F) (FunAbs F)
shiftFunAbs {_} {α} {β} k ⊆w f {γ} k' ⊆w'
   = f (k' +ℕ k)
       (α +ᵂ (k' +ℕ k)   ⊆⟨ ⊆-assoc-+′ ⊆-refl k k' ⟩
        (α +ᵂ k) +ᵂ k'   ⊆⟨ ⊆-cong-+ ⊆w k' ⟩
        β +ᵂ k'          ⊆⟨ ⊆w' ⟩
        γ ∎)
  where open ⊆-Reasoning

module NamePack {β} (x : Name β) where
  nameOf      : Name β
  nameOf      = x

  -- Nameø-elim : ∀ {a} {A : Set a} → Name ø → A
  Nameø-elim'  : ∀ {A : Set} → β ≡ ø → A
  Nameø-elim' eq = go eq x
    where go : ∀ {α} {A : Set} → (α ≡ ø) → Name α → A
          go refl = Nameø-elim

  _==ᴺ-nameOf_ : (y : Name β) → Bool
  _==ᴺ-nameOf_ = _==ᴺ_ x

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

lookupStar : ∀ {α β ℓ} {_↝_ : Rel World ℓ} → (∀ {γ δ} → γ ↝ δ → Name γ →? Name δ)
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
     lookupEnv ε x = inj₁ x
     lookupEnv (carry z ◅ Γ) x
       with predᴺ? x
     ...  | just x' = lookupEnv Γ x'
     ...  | nothing = inj₂ z
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
      where open NamePack

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
    _,,_ Γ v = maybe′ Γ (inj₂ v) ∘ predᴺ?

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
    open NamePack

    CEnv : Set ℓ → World → Set ℓ
    CEnv A α = Name α → A

    _,,_ : ∀ {α A} → CEnv A α → A → CEnv A (α ↑1)
    _,,_ Γ v = maybe′ Γ v ∘ predᴺ?

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

  traverseAbs : ∀ {G} → Tr G → Tr (SynAbs G)
  traverseAbs trG ℓ = trG (suc ℓ)
-}

Traverse : (F G H : World → Set) → Set
Traverse F G H = ∀ {α β} (trName : Su↑ Name H α β) → Su↑ F G α β

TraverseA : (F G H : World → Set) → Set₁
TraverseA F G H = ∀ {E} (E-app : Applicative E) → Traverse F (E ∘ G) (E ∘ H)

Var : (World → Set) → Set
Var F = Name |↦| F

Rename : (F G : World → Set) → Set
Rename F G = ∀ {α β} → (Name α → Name β) → (F α → G β)

Rename? : (F G : World → Set) → Set
Rename? F G = ∀ {α β} → (Name α →? Name β) → F α →? G β

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

-- generalizes NaPa.protect↑ to any ℓ
protect↑ : ∀ {α β} → (Name α → Name β) → ∀ ℓ → (Name (α ↑ ℓ) → Name (β ↑ ℓ))
protect↑ f ℓ x  with x <ᴺ ℓ
... {- bound -} | inj₁ x′ = x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
... {- free  -} | inj₂ x′ = (addᴺ↑ ℓ ∘ f ∘ subtractᴺ ℓ) x′

-- generalizes protect↑ to any Applicative
protect↑A : ∀ {E} (E-app : Applicative E)
              {α β} → (Name α → E (Name β)) → ∀ ℓ → (Name (α ↑ ℓ) → E (Name (β ↑ ℓ)))
protect↑A E-app f ℓ x  with x <ᴺ ℓ
... {- bound -} | inj₁ x′ = pure (x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩)  where open Applicative E-app
... {- free  -} | inj₂ x′ = (_<$>_ (addᴺ↑ ℓ) ∘ f ∘ subtractᴺ ℓ) x′ where open Applicative E-app

-- dup of NaPa.Interface.shiftName
shiftName : ∀ {α β} ℓ k → (α +ᵂ k) ⊆ β → Name (α ↑ ℓ) → Name (β ↑ ℓ)
shiftName ℓ k pf n
             with n <ᴺ ℓ
... {- ℓ-bound -} | inj₁ n′ = n′
                              ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩
... {- ℓ-free  -} | inj₂ n′ = n′ +ᴺ k
                              ⟨-because ⊆-trans (⊆-exch-+-+ ⊆-refl ℓ k) (⊆-ctx-+↑ pf ℓ) -⟩

shiftName′ : ∀ {α β} ℓ k → (α +ᵂ k) ⊆ β → Name (α ↑ ℓ) → Name (β ↑ ℓ)
shiftName′ ℓ k pf = protect↑ (coerceᴺ pf ∘ addᴺ k) ℓ

-- generalizes protect↑
substVar : ∀ {F} → Var F → Shift F F → SubstVar F
substVar varF shiftF θ ℓ x
    with x <ᴺ ℓ
...    | inj₁ x′ = varF     (x′ ⟨-because ⊆-cong-↑ ⊆-ø ℓ -⟩)
...    | inj₂ x′ = shiftF ℓ (⊆-+-↑ ℓ) (θ (x′ ∸ᴺ ℓ))

module RenameGen {F G} (rename : Rename F G) where
  shift : Shift F G
  shift k ⊆w = rename (coerceᴺ ⊆w ∘ addᴺ k)

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
  open RenameAGen renameA public hiding (shift; rename; coerce; coerceø)

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

  syn2fun : SynAbs F |↦| FunAbs G
  syn2fun t k pf u = subst (subtractWithᴺ 1 u (V ∘ shiftName 0 k pf)) t

fun2syn : ∀ {F} (V : Var F) → FunAbs F |↦| SynAbs F
fun2syn {F} V {α} f = f 1 ⊆-+1↑1 (V (0 ᴺ))

{-
-- This has more pedagogical value than code-reuse value.
module Substitution {α β} where

  SuF : ∀ F → Set
  SuF F = Su↑ F F α β

  subst-× : ∀ {F₁ F₂ G₁ G₂} → Su↑ F₁ G₁ α β → Su↑ F₂ G₂ α β → Su↑ (F₁ |×| F₂) (G₁ |×| G₂) α β
  subst-× subst₁ subst₂ ℓ (x , y) = (subst₁ ℓ x , subst₂ ℓ y)

  substAbs : ∀ {F G} → Su↑ F G α β → Su↑ (SynAbs F) (SynAbs G) α β
  substAbs subst = subst ∘ suc
-}

-- alternative definition of protect↑A using substVar
protect↑A′ : ∀ {E} (E-app : Applicative E)
               {α β} → (Name α → E (Name β)) → ∀ ℓ → (Name (α ↑ ℓ) → E (Name (β ↑ ℓ)))
protect↑A′ E-app θ = substVar pure shift θ
  where open Applicative E-app using (pure; _<$>_)
        open RenameGen _<$>_ using (shift)

αEq : (F : World → Set) (α β : World) → Set
αEq F α β = F α → F β → Bool

--αEq : (F : World → Set) (α β : World) → Set
--αEq F α β = ∀ {α β} → αEq Name α β → αEq F α β

module αEquivalence {α β} where

  αEq↑ : (F : World → Set) → Set
  αEq↑ F = ∀ k → αEq F (α ↑ k) (β ↑ k)

  αeqName : αEq Name α β → αEq↑ Name
  αeqName Γ k x y with x <ᴺ k | y <ᴺ k
  ... | inj₁ x′ | inj₁ y′ = x′ ==ᴺ y′
  ... | inj₂ x′ | inj₂ y′ = Γ (subtractᴺ k x′) (subtractᴺ k y′)
  ... | _       | _       = false

  -- α-equivalence on pairs is just the conjunction
  ×-αeq : ∀ {F G} → αEq↑ F → αEq↑ G → αEq↑ (F |×| G)
  ×-αeq αeqF αeqG k (x₁ , y₁) (x₂ , y₂) = αeqF k x₁ x₂ ∧ αeqG k y₁ y₂

  -- α-equivalence on abstraction is just incrementing `k`
  αeqAbs : ∀ {F} → αEq↑ F → αEq↑ (SynAbs F)
  αeqAbs αeqF = αeqF ∘ suc
