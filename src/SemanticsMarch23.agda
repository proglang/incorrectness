module SemanticsMarch23 where

open import Data.Nat hiding (_⊔_; _⊓_)
open import Data.Product
open import Data.Sum
open import Data.String using (String)
open import Data.Unit hiding (_≟_)
open import Data.Empty

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl)
open Eq.≡-Reasoning
open import Level hiding (_⊔_) renaming (zero to lzero; suc to lsuc)

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

-- simple types

data RawType : Set where
  Nat : RawType
  _⇒_ _⋆_ _⊹_ : RawType → RawType → RawType

ss⇒tt : ∀ {S S₁ T T₁ : RawType} → (S ⇒ S₁) ≡ (T ⇒ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⇒tt refl = refl , refl

ss⋆tt : ∀ {S S₁ T T₁ : RawType} → (S ⋆ S₁) ≡ (T ⋆ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⋆tt refl = refl , refl

ss⊹tt : ∀ {S S₁ T T₁ : RawType} → (S ⊹ S₁) ≡ (T ⊹ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⊹tt refl = refl , refl

-- refinement types
-- given by a semantic, non-empty predicate on ℕ

data Type : Set₁ where
  Base : (P : ℕ → Set) → (∃P : Σ ℕ P) → Type -- refinement
  Nat : Type
  _⇒_ : Type → Type → Type
  _⋆_ : Type → Type → Type
  _⊹_ : Type → Type → Type

T-Nat = Base (λ n → ⊤) (zero , tt) -- all natural numbers

-- -- non-empty type

-- data ne : Type → Set where
--   ne-base : ∀ {P} → (∃P : Σ ℕ P) → ne (Base P)
--   ne-nat : ne Nat
--   ne-⇒ : ∀ {S T} → ne S → ne T → ne (S ⇒ T)
--   ne-⋆ : ∀ {S T} → ne S → ne T → ne (S ⋆ T)
--   ne-⊹L : ∀ {S T} → ne S → ne (S ⊹ T)
--   ne-⊹R : ∀ {S T} → ne T → ne (S ⊹ T)

-- type environments

data Env (A : Set ℓ) : Set ℓ where
  · : Env A
  _,_⦂_ : Env A → (x : Id) → (a : A) → Env A

-- underlying raw type, erases refinements

∥_∥ : Type → RawType
∥ Base P ∃P ∥ = Nat
∥ Nat ∥ = Nat
∥ S ⇒ S₁ ∥ = ∥ S ∥ ⇒ ∥ S₁ ∥
∥ S ⋆ S₁ ∥ = ∥ S ∥ ⋆ ∥ S₁ ∥
∥ S ⊹ S₁ ∥ = ∥ S ∥ ⊹ ∥ S₁ ∥

-- operations on semantic predicates

_∨_ : (P Q : ℕ → Set) → ℕ → Set
P ∨ Q = λ n → P n ⊎ Q n

_∧_ : (P Q : ℕ → Set) → ℕ → Set
P ∧ Q = λ n → P n × Q n

implies : ∀ {P Q : ℕ → Set} → (n : ℕ) → P n → (P n ⊎ Q n)
implies n Pn = inj₁ Pn

p*q->p : ∀ {P Q : ℕ → Set} → (n : ℕ) → (P n × Q n) → P n
p*q->p n (Pn , Qn) = Pn

_⊔_ _⊓_  : (S T : Type) {r : ∥ S ∥ ≡ ∥ T ∥} → Type

(Base P ∃P ⊔ Base Q ∃Q) {refl} = Base (P ∨ Q) (proj₁ ∃P , inj₁ (proj₂ ∃P))
(Base P ∃P ⊔ Nat) = Nat
(Nat ⊔ Base Q ∃Q) = Nat
(Nat ⊔ Nat) = Nat
((S ⇒ S₁) ⊔ (T ⇒ T₁)) {r} with ss⇒tt r
... | sss , ttt = (S ⊓ T){sss} ⇒ (S₁ ⊔ T₁){ttt}
((S ⋆ S₁) ⊔ (T ⋆ T₁)) {r} with ss⋆tt r
... | sss , ttt = (S ⊔ T){sss} ⋆ (S₁ ⊔ T₁){ttt}
((S ⊹ S₁) ⊔ (T ⊹ T₁)) {r} with ss⊹tt r
... | sss , ttt = (S ⊔ T){sss} ⊹ (S₁ ⊔ T₁){ttt}

-- cannot prove non-emptyness here
Base P ∃P ⊓ Base Q ∃Q = Base (P ∧ Q) {!!}
Base P ∃P ⊓ Nat = Base P ∃P
Nat ⊓ Base P ∃P = Base P ∃P
Nat ⊓ Nat = Nat
((S ⇒ S₁) ⊓ (T ⇒ T₁)){r} with ss⇒tt r
... | sss , ttt = (S ⊔ T){sss} ⇒ (S₁ ⊓ T₁){ttt}
((S ⋆ S₁) ⊓ (T ⋆ T₁)){r} with ss⋆tt r
... | sss , ttt = (S ⊓ T){sss} ⋆ (S₁ ⊓ T₁){ttt}
((S ⊹ S₁) ⊓ (T ⊹ T₁)){r} with ss⊹tt r
... | sss , ttt = (S ⊓ T){sss} ⊹ (S₁ ⊓ T₁){ttt}


variable
  S T U S′ T′ U′ U″ : Type
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

  <:-base : 
    (P Q : ℕ → Set) →
    ∀ ∃P ∃Q →
    (p→q : ∀ n → P n → Q n) →
    Base P ∃P <: Base Q ∃Q

  <:-base-nat :
    ∀ {∃P} →
    Base P ∃P <: Nat
    
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

-- subtyping is compatible with raw types

<:-raw : S <: T → ∥ S ∥ ≡ ∥ T ∥
<:-raw <:-refl = refl
<:-raw (<:-base P Q ∃P ∃Q p→q) = refl
<:-raw <:-base-nat = refl
<:-raw (<:-⇒ s<:t s<:t₁) = Eq.cong₂ _⇒_ (Eq.sym (<:-raw s<:t)) (<:-raw s<:t₁)
<:-raw (<:-⋆ s<:t s<:t₁) = Eq.cong₂ _⋆_ (<:-raw s<:t) (<:-raw s<:t₁)
<:-raw (<:-⊹ s<:t s<:t₁) = Eq.cong₂ _⊹_ (<:-raw s<:t) (<:-raw s<:t₁)

<:-⊔ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → S <: (S ⊔ T){c}
<:-⊓ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → (S ⊓ T){c} <: S

<:-⊔ (Base P ∃P) (Base Q ∃Q) {refl} = {!!} -- <:-base P (P ∨ P₁) implies
<:-⊔ (Base P ∃P) Nat = <:-base-nat
<:-⊔ Nat (Base Q ∃Q) = <:-refl
<:-⊔ Nat Nat = <:-refl
<:-⊔ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊓ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊔ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊔ S T) (<:-⊔ S₁ T₁)

<:-⊓ (Base P ∃P) (Base Q ∃Q) {refl} = {!!} -- <:-base (P ∧ P₁) P p*q->p
<:-⊓ (Base P ∃P) Nat = <:-refl
<:-⊓ Nat (Base Q ∃Q) = <:-base-nat
<:-⊓ Nat Nat = <:-refl
<:-⊓ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊔ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊓ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊓ S T) (<:-⊓ S₁ T₁)

-- should be in terms of RawType for evaluation

-- standard typing

data _⊢_⦂_ : Env Type → Expr → Type → Set₁ where

  nat' :
    Γ ⊢ Nat n ⦂ Base (_≡_ n) (n , refl)

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
    Γ ⊢ Inr N ⦂ (S ⊹ T)
  
  sum-E :
    Γ ⊢ L ⦂ (S ⊹ T) →
    (Γ , x ⦂ S) ⊢ M ⦂ U →
    (Γ , y ⦂ T) ⊢ N ⦂ U →
    --------------------
    Γ ⊢ Case L x M y N ⦂ U

-- auxiliary definitions

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
weaken sp (nat') = nat'
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

  nat' :
    --------------------
    · ⊢ Nat n ÷ Base (_≡_ n) (n , refl)

  var1 :
    ( · , x ⦂ T) ⊢ Var x ÷ T

{-
  var :
    x ⦂ T ∈ Γ →
    --------------------
    Γ ⊢ Var x ÷ T
-}

  lam :
    (Γ , x ⦂ S) ⊢ M ÷ T →
    --------------------
    Γ ⊢ Lam x M ÷ (S ⇒ T)

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

  sum-E′ : ∀ {ru′=ru″} →
    Split Γ Γ₁ Γ₂ →
    Γ₁ ⊢ L ÷ (S ⊹ T) →
    (Γ₂ , x ⦂ S) ⊢ M ÷ U′ →
    (Γ₂ , y ⦂ T) ⊢ N ÷ U″ →
    U ≡ (U′ ⊔ U″){ru′=ru″} →
    --------------------
    Γ ⊢ Case L x M y N ÷ U

{-
  `sub` :
    Γ ⊢ M ÷ S →
    T <: S → 
    --------------------
    Γ ⊢ M ÷ T
-}

-- semantics of types for correctness and incorrectness

record _←_ (A B : Set) : Set where
  field
    func : A → B
    back : ∀ (b : B) → ∃ λ (a : A) → func a ≡ b

open _←_

T⟦_⟧ : Type → Set
T⟦ Base P ∃P ⟧ = Σ ℕ P
T⟦ Nat ⟧ = ℕ
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧
T⟦ S ⋆ T ⟧ = T⟦ S ⟧ × T⟦ T ⟧
T⟦ S ⊹ T ⟧ = T⟦ S ⟧ ⊎ T⟦ T ⟧

T'⟦_⟧ : Type → Set
↓_ : ∀ {T} → T'⟦ T ⟧ → T⟦ T ⟧

T'⟦ Base P ∃P ⟧ = Σ ℕ P
T'⟦ Nat ⟧ = ℕ
T'⟦ S ⇒ T ⟧ = Σ (T⟦ S ⟧ → T⟦ T ⟧) (λ f → ∃ λ (t : T'⟦ T ⟧) → ∃ λ (s : T'⟦ S ⟧) → f (↓ s) ≡ (↓ t))
T'⟦ S ⋆ T ⟧ = T'⟦ S ⟧ × T'⟦ T ⟧
T'⟦ S ⊹ T ⟧ = T'⟦ S ⟧ ⊎ T'⟦ T ⟧
{- alternative?
T'⟦ S ⇒ T ⟧ = Σ (T⟦ S ⟧ → T⟦ T ⟧) (λ f → ∀ (t : T'⟦ T ⟧) → ∃ λ (s : T'⟦ S ⟧) → f (↓ s) ≡ (↓ t))
-}
↓_ {Base P ∃P} t = t
↓_ {Nat} t = t
↓_ {S ⇒ T} t = proj₁ t
↓_ {S ⋆ T} (s , t) = ↓ s , ↓ t
↓_ {S ⊹ T} (inj₁ s) = inj₁ (↓ s)
↓_ {S ⊹ T} (inj₂ t) = inj₂ (↓ t)

-- semantics of type environments

E⟦_⟧ : Env Type → Env Set
E⟦ · ⟧ = ·
E⟦ Γ , x ⦂ T ⟧ = E⟦ Γ ⟧ , x ⦂ T⟦ T ⟧

data iEnv : Env Set → Set where
  · : iEnv ·
  _,_⦂_ : ∀ {E}{A} → iEnv E → (x : Id) → (a : A) → iEnv (E , x ⦂ A)

lookup : (x ⦂ T ∈ Γ) → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
lookup found (γ , _ ⦂ a) = a
lookup (there x∈) (γ , _ ⦂ a) = lookup x∈ γ

-- denotational semantics of expressions

eval : Γ ⊢ M ⦂ T → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
eval (nat'{n = n}) γ = n , refl
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

-- seems like we need a lemma like this one to complete the correspondence theorem below

-- Γ ⊢ M ÷ S → S <: T → ∃[ Γ′ ] (Γ <: Γ′ × Γ′ ⊢ M ÷ T)

corr : Γ ⊢ M ÷ T → Γ ⊢ M ⦂ T
corr (nat') = nat'
corr var1 = var found
-- corr (var x) = var x
corr (lam ⊢M) = lam (corr ⊢M)
corr (pair-E1 ÷M) = pair-E1 (corr ÷M)
corr (pair-E2 ÷M) = pair-E2 (corr ÷M)
corr (pair sp ÷M ÷N) = pair (weaken sp (corr ÷M)) (weaken (split-sym sp) (corr ÷N))
corr (sum-E sp ÷L ÷M ÷N) = sum-E (weaken sp (corr  ÷L)) (weaken (lft (split-sym sp)) (corr ÷M)) (weaken (lft (split-sym sp)) (corr ÷N))
corr (sum-E′ sp ÷L ÷M ÷N U≡U′⊔U″) =
  sum-E (weaken sp (corr  ÷L)) (weaken (lft (split-sym sp)) (corr {!÷M!})) (weaken (lft (split-sym sp)) (corr {!÷N!}))
{-
corr (`sub` ÷M T<S) = {!÷M!}
-}

-- pick one element of a type to demonstrate non-emptiness
one : ∀ (T : Type) → T⟦ T ⟧
one (Base P ∃P) = ∃P
one Nat = zero
one (T ⇒ T₁) = λ x → one T₁
one (T ⋆ T₁) = one T , one T₁
one (T ⊹ T₁) = inj₁ (one T)
-- one (T ⊹ T₁) = inj₂ (one T₁)

{- not needed
many : iEnv E⟦ Γ ⟧
many {·} = ·
many {Γ , x ⦂ T} = many , x ⦂ one T

gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → iEnv E⟦ Γ ⟧
gen found t = many , _ ⦂ t
gen (there x∈) t = (gen x∈ t) , _ ⦂ one {!!}

lookup-gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → lookup x∈ (gen x∈ t) ≡ t
lookup-gen found t = refl
lookup-gen (there x∈) t = lookup-gen x∈ t
-}

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
eval-unsplit sp γ₁ γ₂ (nat')= refl
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

E'⟦_⟧ : Env Type → Env Set
E'⟦ · ⟧ = ·
E'⟦ Γ , x ⦂ T ⟧ = E'⟦ Γ ⟧ , x ⦂ T'⟦ T ⟧


unsplit-env' : Split Γ Γ₁ Γ₂ → iEnv E'⟦ Γ₁ ⟧ → iEnv E'⟦ Γ₂ ⟧ → iEnv E'⟦ Γ ⟧
unsplit-env' nil γ₁ γ₂ = ·
unsplit-env' (lft sp) (γ₁ , _ ⦂ a) γ₂ = (unsplit-env' sp γ₁ γ₂) , _ ⦂ a
unsplit-env' (rgt sp) γ₁ (γ₂ , _ ⦂ a) = (unsplit-env' sp γ₁ γ₂) , _ ⦂ a

-- pick one element of a type to demonstrate non-emptiness
one' : ∀ (T : Type) → T'⟦ T ⟧
one≡↓one' : ∀ T → one T ≡ ↓ one' T

one' (Base P ∃P) = ∃P
one' Nat = zero
one' (S ⇒ T) = one (S ⇒ T) , (one' T) , ((one' S) , one≡↓one' T)
one' (S ⋆ T) = one' S , one' T
one' (S ⊹ T) = inj₁ (one' S)

one≡↓one' (Base P ∃P) = refl
one≡↓one' Nat = refl
one≡↓one' (S ⇒ T) = refl
one≡↓one' (S ⋆ T) = Eq.cong₂ _,_ (one≡↓one' S) (one≡↓one' T)
one≡↓one' (S ⊹ T) = Eq.cong inj₁ (one≡↓one' S)

eval' :
  (÷M : Γ ⊢ M ÷ T) →
  T'⟦ T ⟧ →
  iEnv E'⟦ Γ ⟧
eval' nat' t' = ·
eval' var1 t' = · , _ ⦂ t'
eval' {Γ = Γ} {T = .(_ ⇒ _)} (lam ÷M) (f , t' , s' , fs'≡t')
  with eval' ÷M t'
... | ih , _ ⦂ a = ih
eval' (pair x ÷M ÷N) (s' , t') = unsplit-env' x (eval' ÷M s') (eval' ÷N t')
eval' (pair-E1{S = T₁}{T = T₂} ÷M) t' = eval' ÷M (t' , one' T₂)
eval' (pair-E2{S = T₁}{T = T₂} ÷M) t' = eval' ÷M (one' T₁ , t')
eval' (sum-E x ÷M ÷M₁ ÷M₂) t'
  with eval' ÷M₁ t'
... | ih₁ , _ ⦂ t₁'
  with eval' ÷M₂ t'
... | ih₁ , _ ⦂ t₂'
  with eval' ÷M (inj₁ t₁')
... | ih = unsplit-env' x ih ih₁
eval' (sum-E′{S = S}{T = T}{U = U} x ÷M ÷M₁ ÷M₂ x₁) t' = {!!}



lave :
  (÷M : Γ ⊢ M ÷ T) →
  ∀ (t' : T'⟦ T ⟧) →
  ∃ λ (γ : iEnv E⟦ Γ ⟧) →
  eval (corr ÷M) γ ≡ ↓ t'

lave nat' (n , refl) = · , refl
lave var1 t' = {!!}
lave (lam ÷M) (f , rest)
  with lave ÷M {!!}
... | ih = {!!}
lave (pair x ÷M ÷M₁) t' = {!!}
lave (pair-E1 ÷M) t' = {!!}
lave (pair-E2 ÷M) t' = {!!}
lave (sum-E x ÷M ÷M₁ ÷M₂) t' = {!!}
lave (sum-E′ x ÷M ÷M₁ ÷M₂ x₁) t' = {!!}

