module Semantics where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.String using (String)
open import Data.Unit

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl)
open Eq.≡-Reasoning
open import Level renaming (zero to lzero; suc to lsuc)

{- TODO:
* subtyping of refinement types
* union types
* intersection types
-}

Id = String

variable
  x y : Id
  ℓ : Level

data Expr : Set where
  Nat : ℕ → Expr
  Var : Id → Expr
  Lam : Id → Expr → Expr
  App : Expr → Expr → Expr
  Pair : Expr → Expr → Expr
  Fst Snd : Expr → Expr
  Inl Inr : Expr → Expr
  Case : Expr → Id → Expr → Id → Expr → Expr

data Type : Set₁ where
  S-Nat : ℕ → Type              -- singleton type
  Base : (P : ℕ → Set) → (∃P : Σ ℕ P) → Type -- non-empty refinement
  _⇒_ : Type → Type → Type
  _⋆_ : Type → Type → Type
  _⊹_ : Type → Type → Type

T-Nat = Base (λ n → ⊤) (zero , tt) -- all natural numbers

data Env (A : Set ℓ) : Set ℓ where
  · : Env A
  _,_⦂_ : Env A → (x : Id) → (a : A) → Env A

{-
_++_ : {A : Set ℓ} → Env A → Env A → Env A
γ ++ · = γ
γ ++ (δ , x ⦂ v) = (γ ++ δ) , x ⦂ v
-}

variable
  S T U : Type
  Γ Γ₁ Γ₂ : Env Type
  L M N : Expr
  n : ℕ
  P : ℕ → Set

data Split {A : Set ℓ} : Env A → Env A → Env A → Set ℓ where
  nil : Split · · ·
  lft : ∀ {a : A}{Γ Γ₁ Γ₂ : Env A} → Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ a) (Γ₁ , x ⦂ a) Γ₂
  rgt : ∀ {a : A}{Γ Γ₁ Γ₂ : Env A} → Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ a) Γ₁ (Γ₂ , x ⦂ a)

data _⦂_∈_ {A : Set ℓ} : Id → A → Env A → Set ℓ where

  found : ∀ {a : A}{E : Env A} →
    x ⦂ a ∈ (E , x ⦂ a)

  there : ∀ {a a' : A}{E : Env A} →
    x ⦂ a ∈ E →
      -- x ≢ y →
    x ⦂ a ∈ (E , y ⦂ a')

data _<:_ : Type → Type → Set where

  <:-refl :
    T <: T

  <:-single :
    (p : P n) →
    S-Nat n <: Base P (n , p)

  <:-base :
    (P Q : ℕ → Set) →
    (p→q : ∀ n → P n → Q n) →
    (∃p : ∃ P) →
    Base P ∃p <: Base Q (proj₁ ∃p , p→q (proj₁ ∃p) (proj₂ ∃p))

  <:-base-nat :
    {∃p : ∃ P} →
    Base P ∃p <: Nat
    
  <:-⇒ :
    S′ <: S →
    T <: T′ →
    (S ⇒ T) <: (S′ ⇒ T′)
    
  <:-⋆ :
    S <: S′ →
    T <: T′ →
    (S ⋆ T) <: (S′ ⋆ T′)

  <:-⊹ :
    S <: S′ →
    T <: T′ →
    (S ⊹ T) <: (S′ ⊹ T′)

data _⊢_⦂_ : Env Type → Expr → Type → Set₁ where

  nat : 
    --------------------
    Γ ⊢ Nat n ⦂ S-Nat n

  var :
    (x∈ : x ⦂ T ∈ Γ) →
    --------------------
    Γ ⊢ Var x ⦂ T

  lam :
    (Γ , x ⦂ S) ⊢ M ⦂ T →
    --------------------
    Γ ⊢ Lam x M ⦂ (S ⇒ T)

  app :
    Γ ⊢ M ⦂ (S ⇒ T) →
    Γ ⊢ N ⦂ S →
    --------------------
    Γ ⊢ App M N ⦂ T

  pair :
    Γ ⊢ M ⦂ S →
    Γ ⊢ N ⦂ T →
    --------------------
    Γ ⊢ Pair M N ⦂ (S ⋆ T)

  pair-E1 :
    Γ ⊢ M ⦂ (S ⋆ T) →
    --------------------
    Γ ⊢ Fst M ⦂ S

  pair-E2 :
    Γ ⊢ M ⦂ (S ⋆ T) →
    --------------------
    Γ ⊢ Snd M ⦂ T

  sum-I1 :
    Γ ⊢ M ⦂ S →
    --------------------
    Γ ⊢ Inl M ⦂ (S ⊹ T)

  sum-I2 :
    Γ ⊢ N ⦂ T →
    --------------------
    Γ ⊢ Inl N ⦂ (S ⊹ T)
  
  sum-E :
    Γ ⊢ L ⦂ (S ⊹ T) →
    (Γ , x ⦂ S) ⊢ M ⦂ U →
    (Γ , y ⦂ T) ⊢ N ⦂ U →
    --------------------
    Γ ⊢ Case L x M y N ⦂ U

split-sym : Split Γ Γ₁ Γ₂ → Split Γ Γ₂ Γ₁
split-sym nil = nil
split-sym (lft sp) = rgt (split-sym sp)
split-sym (rgt sp) = lft (split-sym sp)

weaken-∈ : Split Γ Γ₁ Γ₂ → x ⦂ T ∈ Γ₁ → x ⦂ T ∈ Γ
weaken-∈ (lft sp) found = found
weaken-∈ (rgt sp) found = there (weaken-∈ sp found)
weaken-∈ (lft sp) (there x∈) = there (weaken-∈ sp x∈)
weaken-∈ (rgt sp) (there x∈) = there (weaken-∈ sp (there x∈))

weaken : Split Γ Γ₁ Γ₂ → Γ₁ ⊢ M ⦂ T → Γ ⊢ M ⦂ T
weaken sp (nat) = nat
weaken sp (var x∈) = var (weaken-∈ sp x∈)
weaken sp (lam ⊢M) = lam (weaken (lft sp) ⊢M)
weaken sp (app ⊢M ⊢N) = app (weaken sp ⊢M) (weaken sp ⊢N)
weaken sp (pair ⊢M ⊢N) = pair (weaken sp ⊢M) (weaken sp ⊢N)
weaken sp (pair-E1 ⊢M) = pair-E1 (weaken sp ⊢M)
weaken sp (pair-E2 ⊢M) = pair-E2 (weaken sp ⊢M)
weaken sp (sum-I1 ⊢M) = sum-I1 (weaken sp ⊢M)
weaken sp (sum-I2 ⊢N) = sum-I2 (weaken sp ⊢N)
weaken sp (sum-E ⊢L ⊢M ⊢N) = sum-E (weaken sp ⊢L) (weaken (lft sp) ⊢M) (weaken (lft sp) ⊢N)

-- incorrectness typing

P=n : ℕ → ℕ → Set
P=n = λ n x → n ≡ x

data _⊢_÷_ : Env Type → Expr → Type → Set₁ where

  nat :
    --------------------
    · ⊢ Nat n ÷ S-Nat n

  var1 :
    ( · , x ⦂ T) ⊢ Var x ÷ T

  var :
    x ⦂ T ∈ Γ →
    --------------------
    Γ ⊢ Var x ÷ T

  lam :
    (· , x ⦂ S) ⊢ M ÷ T →
    --------------------
    · ⊢ Lam x M ÷ (S ⇒ T)

  pair :
    Split Γ Γ₁ Γ₂ →
    Γ₁ ⊢ M ÷ S →
    Γ₂ ⊢ N ÷ T →
    --------------------
    Γ ⊢ Pair M N ÷ (S ⋆ T)

  pair-E1 :
    Γ ⊢ M ÷ (S ⋆ T) →
    --------------------
    Γ ⊢ Fst M ÷ S

  pair-E2 :
    Γ ⊢ M ÷ (S ⋆ T) →
    --------------------
    Γ ⊢ Snd M ÷ T

  sum-E :
    Split Γ Γ₁ Γ₂ →
    Γ₁ ⊢ L ÷ (S ⊹ T) →
    (Γ₂ , x ⦂ S) ⊢ M ÷ U →
    (Γ₂ , y ⦂ T) ⊢ N ÷ U →
    --------------------
    Γ ⊢ Case L x M y N ÷ U
{-
  `sub` :
    Γ ⊢ M ÷ S →
    T <: S → 
    --------------------
    Γ ⊢ M ÷ T
-}

record _←_ (A B : Set) : Set where
  field
    func : A → B
    back : ∀ (b : B) → ∃ λ (a : A) → func a ≡ b

open _←_

T⟦_⟧ : Type → Set
T⟦ S-Nat n ⟧ = Σ ℕ (λ x → x ≡ n)
T⟦ Base P ∃P ⟧ = Σ ℕ P
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧
T⟦ S ⋆ T ⟧ = T⟦ S ⟧ × T⟦ T ⟧
T⟦ S ⊹ T ⟧ = T⟦ S ⟧ ⊎ T⟦ T ⟧

T'⟦_⟧ : Type → Set
T'⟦ S-Nat n ⟧ = Σ ℕ (λ x → x ≡ n)
T'⟦ Base P ∃P ⟧ = Σ ℕ P
T'⟦ S ⇒ T ⟧ = T'⟦ S ⟧ ← T'⟦ T ⟧
T'⟦ S ⋆ T ⟧ = T'⟦ S ⟧ × T'⟦ T ⟧
T'⟦ S ⊹ T ⟧ = T'⟦ S ⟧ ⊎ T'⟦ T ⟧

  
E⟦_⟧ : Env Type → Env Set
E⟦ · ⟧ = ·
E⟦ Γ , x ⦂ T ⟧ = E⟦ Γ ⟧ , x ⦂ T⟦ T ⟧

data iEnv : Env Set → Set where
  · : iEnv ·
  _,_⦂_ : ∀ {E}{A} → iEnv E → (x : Id) → (a : A) → iEnv (E , x ⦂ A)

lookup : (x ⦂ T ∈ Γ) → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
lookup found (γ , _ ⦂ a) = a
lookup (there x∈) (γ , _ ⦂ a) = lookup x∈ γ

eval : Γ ⊢ M ⦂ T → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
eval (nat{n = n}) γ = n , refl
eval (var x∈) γ = lookup x∈ γ
eval (lam ⊢M) γ = λ s → eval ⊢M (γ , _ ⦂ s)
eval (app ⊢M ⊢N) γ = eval ⊢M γ (eval ⊢N γ)
eval (pair ⊢M ⊢N) γ = (eval ⊢M γ) , (eval ⊢N γ)
eval (pair-E1 ⊢M) γ = proj₁ (eval ⊢M γ)
eval (pair-E2 ⊢M) γ = proj₂ (eval ⊢M γ)
eval (sum-I1 ⊢M) γ = inj₁ (eval ⊢M γ)
eval (sum-I2 ⊢N) γ = inj₂ (eval ⊢N γ)
eval (sum-E{S = S}{T = T}{U = U} ⊢L ⊢M ⊢N) γ =
  [ (λ s → eval ⊢M (γ , _ ⦂ s)) , (λ t → eval ⊢N (γ , _ ⦂ t)) ] (eval ⊢L γ)


corr : Γ ⊢ M ÷ T → Γ ⊢ M ⦂ T
corr (nat) = nat
corr var1 = var found
corr (var x) = var x
corr (lam ⊢M) = lam (corr ⊢M)
corr (pair-E1 ÷M) = pair-E1 (corr ÷M)
corr (pair-E2 ÷M) = pair-E2 (corr ÷M)
corr (pair sp ÷M ÷N) = pair (weaken sp (corr ÷M)) (weaken (split-sym sp) (corr ÷N))
corr (sum-E sp ÷L ÷M ÷N) = sum-E (weaken sp (corr  ÷L)) (weaken (lft (split-sym sp)) (corr ÷M)) (weaken (lft (split-sym sp)) (corr ÷N))

-- pick one element of a type to demonstrate non-emptiness
one : T⟦ T ⟧
one {S-Nat n} = n , refl
one {Base P ∃P} = ∃P
one {S ⇒ T} = λ x → one
one {S ⋆ T} = one , one
one {S ⊹ T} = inj₁ one

many : iEnv E⟦ Γ ⟧
many {·} = ·
many {Γ , x ⦂ T} = many , x ⦂ one

gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → iEnv E⟦ Γ ⟧
gen found t = many , _ ⦂ t
gen (there x∈) t = (gen x∈ t) , _ ⦂ one

lookup-gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → lookup x∈ (gen x∈ t) ≡ t
lookup-gen found t = refl
lookup-gen (there x∈) t = lookup-gen x∈ t

open Eq.≡-Reasoning

postulate
  ext : ∀ {A B : Set}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

unsplit-env : Split Γ Γ₁ Γ₂ → iEnv E⟦ Γ₁ ⟧ → iEnv E⟦ Γ₂ ⟧ → iEnv E⟦ Γ ⟧
unsplit-env nil γ₁ γ₂ = ·
unsplit-env (lft sp) (γ₁ , _ ⦂ a) γ₂ = (unsplit-env sp γ₁ γ₂) , _ ⦂ a
unsplit-env (rgt sp) γ₁ (γ₂ , _ ⦂ a) = (unsplit-env sp γ₁ γ₂) , _ ⦂ a

unsplit-split : (sp : Split Γ Γ₁ Γ₂) (γ₁ : iEnv E⟦ Γ₁ ⟧) (γ₂ : iEnv E⟦ Γ₂ ⟧) →
  unsplit-env sp γ₁ γ₂ ≡ unsplit-env (split-sym sp) γ₂ γ₁
unsplit-split nil γ₁ γ₂ = refl
unsplit-split (lft sp) (γ₁ , _ ⦂ a) γ₂ rewrite unsplit-split sp γ₁ γ₂ = refl
unsplit-split (rgt sp) γ₁ (γ₂ , _ ⦂ a) rewrite unsplit-split sp γ₁ γ₂ = refl

lookup-unsplit : (sp : Split Γ Γ₁ Γ₂) (γ₁ : iEnv E⟦ Γ₁ ⟧) (γ₂ : iEnv E⟦ Γ₂ ⟧) →
  (x∈ : x ⦂ T ∈ Γ₁) →
  lookup (weaken-∈ sp x∈) (unsplit-env sp γ₁ γ₂) ≡ lookup x∈ γ₁
lookup-unsplit (lft sp) (γ₁ , _ ⦂ a) γ₂ found = refl
lookup-unsplit (rgt sp) γ₁ (γ₂ , _ ⦂ a) found = lookup-unsplit sp γ₁ γ₂ found
lookup-unsplit (lft sp) (γ₁ , _ ⦂ a) γ₂ (there x∈) = lookup-unsplit sp γ₁ γ₂ x∈
lookup-unsplit (rgt sp) γ₁ (γ₂ , _ ⦂ a) (there x∈) = lookup-unsplit sp γ₁ γ₂ (there x∈)

eval-unsplit : (sp : Split Γ Γ₁ Γ₂) (γ₁ : iEnv E⟦ Γ₁ ⟧) (γ₂ : iEnv E⟦ Γ₂ ⟧) →
  (⊢M : Γ₁ ⊢ M ⦂ T) →
  eval (weaken sp ⊢M) (unsplit-env sp γ₁ γ₂) ≡ eval ⊢M γ₁
eval-unsplit sp γ₁ γ₂ (nat)= refl
eval-unsplit sp γ₁ γ₂ (var x∈) = lookup-unsplit sp γ₁ γ₂ x∈
eval-unsplit sp γ₁ γ₂ (lam ⊢M) = ext (λ s → eval-unsplit (lft sp) (γ₁ , _ ⦂ s) γ₂ ⊢M)
eval-unsplit sp γ₁ γ₂ (app ⊢M ⊢M₁) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M | eval-unsplit sp γ₁ γ₂ ⊢M₁ = refl
eval-unsplit sp γ₁ γ₂ (pair ⊢M ⊢M₁)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M | eval-unsplit sp γ₁ γ₂ ⊢M₁ = refl
eval-unsplit sp γ₁ γ₂ (pair-E1 ⊢M)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (pair-E2 ⊢M)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (sum-I1 ⊢M) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (sum-I2 ⊢N)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢N = refl
eval-unsplit sp γ₁ γ₂ (sum-E ⊢L ⊢M ⊢N) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢L
        | ext (λ s → eval-unsplit (lft sp) (γ₁ , _ ⦂ s) γ₂ ⊢M)
        | ext (λ t → eval-unsplit (lft sp) (γ₁ , _ ⦂ t) γ₂ ⊢N)
  = refl

-- soundness of the incorrectness rules
lave :
  (÷M : Γ ⊢ M ÷ T) →
  ∀ (t : T⟦ T ⟧) →
  ∃ λ (γ : iEnv E⟦ Γ ⟧) →
  eval (corr ÷M) γ ≡ t

lave nat (n , refl) = · , refl

lave var1 t = (· , _ ⦂ t) , refl
lave (var x∈) t =  (gen x∈ t) , lookup-gen x∈ t
lave (lam{x = x}{S = S} ÷M) t = · , ext aux
  where
    aux : (s : T⟦ S ⟧) → eval (corr ÷M) (· , x ⦂ s) ≡ t s
    aux s with lave ÷M (t s)
    ... | (· , .x ⦂ a) , snd = {!!} -- impossible to complete!

lave (pair-E1 ÷M) t with lave ÷M (t , one)
... | γ , ih = γ , Eq.cong proj₁ ih
lave (pair-E2 ÷M) t with lave ÷M (one , t)
... | γ , ih = γ , Eq.cong proj₂ ih

lave (pair sp ÷M ÷N) (s , t) with lave ÷M s | lave ÷N t
... | γ₁ , ih-M | γ₂ , ih-N =
  unsplit-env sp γ₁ γ₂ ,
  Eq.cong₂ _,_ (Eq.trans (eval-unsplit sp γ₁ γ₂ (corr ÷M)) ih-M)
               (begin eval (weaken (split-sym sp) (corr ÷N)) (unsplit-env sp γ₁ γ₂) 
               ≡⟨ Eq.cong (eval (weaken (split-sym sp) (corr ÷N))) (unsplit-split sp γ₁ γ₂) ⟩
               eval (weaken (split-sym sp) (corr ÷N)) (unsplit-env (split-sym sp) γ₂ γ₁)
               ≡⟨ eval-unsplit (split-sym sp) γ₂ γ₁ (corr ÷N) ⟩
               ih-N)

-- works, but unsatisfactory!
-- this proof uses only one branch of the case
-- this choice is possible because both branches ÷M and ÷N have the same type
-- in general, U could be the union of the types of ÷M and ÷N
lave (sum-E{S = S}{T = T}{U = U} sp ÷L ÷M ÷N) u
  with lave ÷M u | lave ÷N u
... | (γ₁ , x ⦂ s) , ih-M | (γ₂ , y ⦂ t) , ih-N
  with lave ÷L (inj₁ s)
... | γ₀ , ih-L
  =
  unsplit-env sp γ₀ γ₁ ,
  (begin [
      (λ s₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷M))
         (unsplit-env sp γ₀ γ₁ , x ⦂ s₁))
      ,
      (λ t₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷N))
         (unsplit-env sp γ₀ γ₁ , y ⦂ t₁))
      ]
      (eval (weaken sp (corr ÷L)) (unsplit-env sp γ₀ γ₁))
  ≡⟨ Eq.cong [
      (λ s₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷M))
         (unsplit-env sp γ₀ γ₁ , x ⦂ s₁))
      ,
      (λ t₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷N))
         (unsplit-env sp γ₀ γ₁ , y ⦂ t₁))
      ] (eval-unsplit sp γ₀ γ₁ (corr ÷L)) ⟩ 
    [
      (λ s₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷M))
         (unsplit-env sp γ₀ γ₁ , x ⦂ s₁))
      ,
      (λ t₁ →
         eval (weaken (lft (split-sym sp)) (corr ÷N))
         (unsplit-env sp γ₀ γ₁ , y ⦂ t₁))
      ]
      (eval (corr ÷L) γ₀) 
  ≡⟨ Eq.cong
       [
       (λ s₁ →
          eval (weaken (lft (split-sym sp)) (corr ÷M))
          (unsplit-env sp γ₀ γ₁ , x ⦂ s₁))
       ,
       (λ t₁ →
          eval (weaken (lft (split-sym sp)) (corr ÷N))
          (unsplit-env sp γ₀ γ₁ , y ⦂ t₁))
       ]
       ih-L ⟩
    eval (weaken (lft (split-sym sp)) (corr ÷M)) (unsplit-env sp γ₀ γ₁ , x ⦂ s) 
  ≡⟨  Eq.cong (λ γ → eval (weaken (lft (split-sym sp)) (corr ÷M)) (γ , x ⦂ s)) (unsplit-split sp γ₀ γ₁) ⟩
    eval (weaken (lft (split-sym sp)) (corr ÷M)) (unsplit-env (split-sym sp) γ₁ γ₀ , x ⦂ s)
  ≡⟨⟩
    eval (weaken (lft (split-sym sp)) (corr ÷M)) (unsplit-env (lft (split-sym sp)) (γ₁ , x ⦂ s) γ₀)
  ≡⟨ eval-unsplit (lft (split-sym sp)) (γ₁ , x ⦂ s) γ₀ (corr ÷M) ⟩
    ih-M)

