module RawSemantics where

open import Data.Maybe
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
  ℓ ℓ′ : Level
  n : ℕ

data Expr : Set where
  Nat : ℕ → Expr
  Var : Id → Expr
  Lam : Id → Expr → Expr
  App : Expr → Expr → Expr
  Pair : Expr → Expr → Expr
  Fst Snd : Expr → Expr
  Inl Inr : Expr → Expr
  Case : Expr → Id → Expr → Id → Expr → Expr

-- raw types are the types which support standard execution
-- currently just simple types

data RawType : Set where
  Nat : RawType
  _⇒_ _⋆_ _⊹_ : RawType → RawType → RawType


ss⇒tt : ∀ {S S₁ T T₁ : RawType} → (S ⇒ S₁) ≡ (T ⇒ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⇒tt refl = refl , refl

ss⋆tt : ∀ {S S₁ T T₁ : RawType} → (S ⋆ S₁) ≡ (T ⋆ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⋆tt refl = refl , refl

ss⊹tt : ∀ {S S₁ T T₁ : RawType} → (S ⊹ S₁) ≡ (T ⊹ T₁) → (S ≡ T × S₁ ≡ T₁)
ss⊹tt refl = refl , refl

-- semantics of raw types
R⟦_⟧ : RawType → Set
R⟦ Nat ⟧ = ℕ
R⟦ S ⇒ T ⟧ = R⟦ S ⟧ → R⟦ T ⟧
R⟦ S ⋆ T ⟧ = R⟦ S ⟧ × R⟦ T ⟧
R⟦ S ⊹ T ⟧ = R⟦ S ⟧ ⊎ R⟦ T ⟧


data Env (A : Set ℓ) : Set ℓ where
  · : Env A
  _,_⦂_ : Env A → (x : Id) → (a : A) → Env A

variable
  L M N : Expr

  RS RT RU RV RW : RawType
  Δ Δ₁ Δ₂ : Env RawType

-- mapping a function over an environment

_⁺ : ∀ {A : Set ℓ′}{B : Set ℓ} → (A → B) → (Env A → Env B)
(f ⁺) · = ·
(f ⁺) (Φ , x ⦂ a) = (f ⁺) Φ , x ⦂ f a

RE⟦_⟧ : Env RawType → Env Set
RE⟦_⟧ = R⟦_⟧ ⁺

data _⦂_∈_ {A : Set ℓ} : Id → A → Env A → Set ℓ where

  found : ∀ {a : A}{E : Env A} →
    x ⦂ a ∈ (E , x ⦂ a)

  there : ∀ {a a' : A}{E : Env A} →
    x ⦂ a ∈ E →
      -- x ≢ y →
    x ⦂ a ∈ (E , y ⦂ a')

data iEnv : Env Set → Set where
  · : iEnv ·
  _,_⦂_ : ∀ {E}{A} → iEnv E → (x : Id) → (a : A) → iEnv (E , x ⦂ A)

-- should be in terms of RawType for evaluation

data _⊢_⦂_ : Env RawType → Expr → RawType → Set₁ where

  nat :
    Δ ⊢ Nat n ⦂ Nat

  var :
    (x∈ : x ⦂ RT ∈ Δ) →
    --------------------
    Δ ⊢ Var x ⦂ RT

  lam :
    (Δ , x ⦂ RS) ⊢ M ⦂ RT →
    --------------------
    Δ ⊢ Lam x M ⦂ (RS ⇒ RT)

  app :
    Δ ⊢ M ⦂ (RS ⇒ RT) →
    Δ ⊢ N ⦂ RS →
    --------------------
    Δ ⊢ App M N ⦂ RT

  pair :
    Δ ⊢ M ⦂ RS →
    Δ ⊢ N ⦂ RT →
    --------------------
    Δ ⊢ Pair M N ⦂ (RS ⋆ RT)

  pair-E1 :
    Δ ⊢ M ⦂ (RS ⋆ RT) →
    --------------------
    Δ ⊢ Fst M ⦂ RS

  pair-E2 :
    Δ ⊢ M ⦂ (RS ⋆ RT) →
    --------------------
    Δ ⊢ Snd M ⦂ RT

  sum-I1 :
    Δ ⊢ M ⦂ RS →
    --------------------
    Δ ⊢ Inl M ⦂ (RS ⊹ RT)

  sum-I2 :
    Δ ⊢ N ⦂ RT →
    --------------------
    Δ ⊢ Inl N ⦂ (RS ⊹ RT)
  
  sum-E :
    Δ ⊢ L ⦂ (RS ⊹ RT) →
    (Δ , x ⦂ RS) ⊢ M ⦂ RU →
    (Δ , y ⦂ RT) ⊢ N ⦂ RV →
    RW ≡ RU × RW ≡ RV →
    --------------------
    Δ ⊢ Case L x M y N ⦂ RW

lookup : (x ⦂ RT ∈ Δ) → iEnv RE⟦ Δ ⟧ → R⟦ RT ⟧
lookup found (γ , _ ⦂ a) = a
lookup (there x∈) (γ , _ ⦂ a) = lookup x∈ γ

eval : Δ ⊢ M ⦂ RT → iEnv RE⟦ Δ ⟧ → R⟦ RT ⟧
eval (nat{n = n}) γ = n
eval (var x∈) γ = lookup x∈ γ
eval (lam ⊢M) γ = λ s → eval ⊢M (γ , _ ⦂ s)
eval (app ⊢M ⊢N) γ = eval ⊢M γ (eval ⊢N γ)
eval (pair ⊢M ⊢N) γ = (eval ⊢M γ) , (eval ⊢N γ)
eval (pair-E1 ⊢M) γ = proj₁ (eval ⊢M γ)
eval (pair-E2 ⊢M) γ = proj₂ (eval ⊢M γ)
eval (sum-I1 ⊢M) γ = inj₁ (eval ⊢M γ)
eval (sum-I2 ⊢N) γ = inj₂ (eval ⊢N γ)
eval (sum-E ⊢L ⊢M ⊢N (refl , refl)) γ =
  [ (λ s → eval ⊢M (γ , _ ⦂ s)) , (λ t → eval ⊢N (γ , _ ⦂ t)) ] (eval ⊢L γ)

----------------------------------------------------------------------
-- refinement types that drive the incorrectness typing

data Type : Set₁ where
  Base : (P : ℕ → Set) → Type -- refinement
  Nat : Type
  _⇒_ _⋆_ _⊹_ : (S : Type) (T : Type) → Type

T-Nat = Base (λ n → ⊤) -- all natural numbers

-- characterize non-empty types

data ne : Type → Set where
  ne-base : ∀ {P} → (∃P : Σ ℕ P) → ne (Base P)
  ne-nat : ne Nat
  ne-⇒ : ∀ {S T} → ne S → ne T → ne (S ⇒ T)
  ne-⋆ : ∀ {S T} → ne S → ne T → ne (S ⋆ T)
  ne-⊹L : ∀ {S T} → ne S → ne (S ⊹ T)
  ne-⊹R : ∀ {S T} → ne T → ne (S ⊹ T)

∥_∥ : Type → RawType
∥ Base P ∥ = Nat
∥ Nat ∥ = Nat
∥ S ⇒ S₁ ∥ = ∥ S ∥ ⇒ ∥ S₁ ∥
∥ S ⋆ S₁ ∥ = ∥ S ∥ ⋆ ∥ S₁ ∥
∥ S ⊹ S₁ ∥ = ∥ S ∥ ⊹ ∥ S₁ ∥

T⟦_⟧ : Type → Set
T⟦ Base P ⟧ = Σ ℕ P
T⟦ Nat ⟧ = ℕ
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧
T⟦ S ⋆ T ⟧ = T⟦ S ⟧ × T⟦ T ⟧
T⟦ S ⊹ T ⟧ = T⟦ S ⟧ ⊎ T⟦ T ⟧

E⟦_⟧ : Env Type → Env Set
E⟦_⟧ = T⟦_⟧ ⁺

∥_∥⁺ : Env Type → Env RawType
∥_∥⁺ = ∥_∥ ⁺

-- a value is a member of refinement type T

_∋_ : (T : Type) → R⟦ ∥ T ∥ ⟧ → Set
Base P ∋ x = P x
Nat ∋ x = ⊤
(T ⇒ T₁) ∋ f = ∀ x → T ∋ x → T₁ ∋ f x
(T ⋆ T₁) ∋ (fst , snd) = T ∋ fst × T₁ ∋ snd
(T ⊹ T₁) ∋ inj₁ x = T ∋ x
(T ⊹ T₁) ∋ inj₂ y = T₁ ∋ y

-- operations on predicates 
_∨_ : (P Q : ℕ → Set) → ℕ → Set
P ∨ Q = λ n → P n ⊎ Q n

_∧_ : (P Q : ℕ → Set) → ℕ → Set
P ∧ Q = λ n → P n × Q n

implies : ∀ {P Q : ℕ → Set} → (n : ℕ) → P n → (P n ⊎ Q n)
implies n Pn = inj₁ Pn

p*q->p : ∀ {P Q : ℕ → Set} → (n : ℕ) → (P n × Q n) → P n
p*q->p n (Pn , Qn) = Pn

_⊔_ _⊓_  : (S T : Type) {r : ∥ S ∥ ≡ ∥ T ∥} → Type

(Base P ⊔ Base P₁) {refl} = Base (P ∨ P₁)
(Base P ⊔ Nat) = Nat
(Nat ⊔ Base P) = Nat
(Nat ⊔ Nat) = Nat
((S ⇒ S₁) ⊔ (T ⇒ T₁)) {r} with ss⇒tt r
... | sss , ttt = (S ⊓ T){sss} ⇒ (S₁ ⊔ T₁){ttt}
((S ⋆ S₁) ⊔ (T ⋆ T₁)) {r} with ss⋆tt r
... | sss , ttt = (S ⊔ T){sss} ⋆ (S₁ ⊔ T₁){ttt}
((S ⊹ S₁) ⊔ (T ⊹ T₁)) {r} with ss⊹tt r
... | sss , ttt = (S ⊔ T){sss} ⊹ (S₁ ⊔ T₁){ttt}

Base P ⊓ Base P₁ = Base (P ∧ P₁)
Base P ⊓ Nat = Base P
Nat ⊓ Base P = Base P
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
  P : ℕ → Set
  A : Set ℓ
  a : A
  Φ Φ₁ Φ₂ : Env A

⊔-preserves : ∀ S T {st : ∥ S ∥ ≡ ∥ T ∥} → ∥ (S ⊔ T){st} ∥ ≡ ∥ S ∥ × ∥ (S ⊔ T){st} ∥ ≡ ∥ T ∥
⊓-preserves : ∀ S T {st : ∥ S ∥ ≡ ∥ T ∥} → ∥ (S ⊓ T){st} ∥ ≡ ∥ S ∥ × ∥ (S ⊓ T){st} ∥ ≡ ∥ T ∥

⊔-preserves (Base P) (Base P₁) {refl} = refl , refl
⊔-preserves (Base P) Nat {st} = refl , refl
⊔-preserves Nat (Base P) {st} = refl , refl
⊔-preserves Nat Nat {st} = refl , refl
⊔-preserves (S ⇒ S₁) (T ⇒ T₁) {st} with ss⇒tt st
... | sss , ttt with ⊓-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st
⊔-preserves (S ⋆ S₁) (T ⋆ T₁) {st} with ss⋆tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st
⊔-preserves (S ⊹ S₁) (T ⊹ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st

⊓-preserves (Base P) (Base P₁) {st} = refl , refl
⊓-preserves (Base P) Nat {st} = refl , refl
⊓-preserves Nat (Base P) {st} = refl , refl
⊓-preserves Nat Nat {st} = refl , refl
⊓-preserves (S ⇒ S₁) (T ⇒ T₁) {st} with ss⇒tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊓-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s1 , sut=t1 rewrite sut=s | sut=s1 = refl , st
⊓-preserves (S ⋆ S₁) (T ⋆ T₁) {st} with ss⋆tt st
... | sss , ttt with ⊓-preserves S T {sss} | ⊓-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s1 , sut=t1 rewrite sut=s | sut=s1 = refl , st
⊓-preserves (S ⊹ S₁) (T ⊹ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊓-preserves S T {sss} | ⊓-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s1 , sut=t1 rewrite sut=s | sut=s1 = refl , st


data Split {A : Set ℓ} : Env A → Env A → Env A → Set ℓ where
  nil : Split · · ·
  lft : ∀ {a : A}{Γ Γ₁ Γ₂ : Env A} → Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ a) (Γ₁ , x ⦂ a) Γ₂
  rgt : ∀ {a : A}{Γ Γ₁ Γ₂ : Env A} → Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ a) Γ₁ (Γ₂ , x ⦂ a)

-- subtyping

data _<:_ : Type → Type → Set where

  <:-refl :
    T <: T

  <:-base : 
    (P Q : ℕ → Set) →
    (p→q : ∀ n → P n → Q n) →
    Base P <: Base Q

  <:-base-nat :
    Base P <: Nat
    
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
<:-raw (<:-base P Q p→q) = refl
<:-raw <:-base-nat = refl
<:-raw (<:-⇒ s<:t s<:t₁) = Eq.cong₂ _⇒_ (Eq.sym (<:-raw s<:t)) (<:-raw s<:t₁)
<:-raw (<:-⋆ s<:t s<:t₁) = Eq.cong₂ _⋆_ (<:-raw s<:t) (<:-raw s<:t₁)
<:-raw (<:-⊹ s<:t s<:t₁) = Eq.cong₂ _⊹_ (<:-raw s<:t) (<:-raw s<:t₁)

<:-⊔ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → S <: (S ⊔ T){c}
<:-⊓ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → (S ⊓ T){c} <: S

<:-⊔ (Base P) (Base P₁) {refl} = <:-base P (P ∨ P₁) implies
<:-⊔ (Base P) Nat = <:-base-nat
<:-⊔ Nat (Base P) = <:-refl
<:-⊔ Nat Nat = <:-refl
<:-⊔ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊓ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊔ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊔ S T) (<:-⊔ S₁ T₁)

<:-⊓ (Base P) (Base P₁) {refl} = <:-base (P ∧ P₁) P p*q->p
<:-⊓ (Base P) Nat = <:-refl
<:-⊓ Nat (Base P) = <:-base-nat
<:-⊓ Nat Nat = <:-refl
<:-⊓ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊔ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊓ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊓ S T) (<:-⊓ S₁ T₁)


split-sym : Split Φ Φ₁ Φ₂ → Split Φ Φ₂ Φ₁
split-sym nil = nil
split-sym (lft sp) = rgt (split-sym sp)
split-sym (rgt sp) = lft (split-sym sp)

weaken-∈ : Split Φ Φ₁ Φ₂ → x ⦂ a ∈ Φ₁ → x ⦂ a ∈ Φ
weaken-∈ (lft sp) found = found
weaken-∈ (rgt sp) found = there (weaken-∈ sp found)
weaken-∈ (lft sp) (there x∈) = there (weaken-∈ sp x∈)
weaken-∈ (rgt sp) (there x∈) = there (weaken-∈ sp (there x∈))

weaken : Split Δ Δ₁ Δ₂ → Δ₁ ⊢ M ⦂ RT → Δ ⊢ M ⦂ RT
weaken sp (nat) = nat
weaken sp (var x∈) = var (weaken-∈ sp x∈)
weaken sp (lam ⊢M) = lam (weaken (lft sp) ⊢M)
weaken sp (app ⊢M ⊢N) = app (weaken sp ⊢M) (weaken sp ⊢N)
weaken sp (pair ⊢M ⊢N) = pair (weaken sp ⊢M) (weaken sp ⊢N)
weaken sp (pair-E1 ⊢M) = pair-E1 (weaken sp ⊢M)
weaken sp (pair-E2 ⊢M) = pair-E2 (weaken sp ⊢M)
weaken sp (sum-I1 ⊢M) = sum-I1 (weaken sp ⊢M)
weaken sp (sum-I2 ⊢N) = sum-I2 (weaken sp ⊢N)
weaken sp (sum-E ⊢L ⊢M ⊢N (RT=RU , RT=RV)) =
  sum-E (weaken sp ⊢L) (weaken (lft sp) ⊢M) (weaken (lft sp) ⊢N) (RT=RU , RT=RV)

-- incorrectness typing

-- attempt to map type (interpretation) to corresponding raw type (interpretation)
-- * must be monadic because of refinement
-- * fails at function types
toRaw : ∀ T → T⟦ T ⟧ → Maybe R⟦ ∥ T ∥ ⟧
fromRaw : ∀ T → R⟦ ∥ T ∥ ⟧ → Maybe T⟦ T ⟧

toRaw (Base P) (n , Pn) = just n
toRaw Nat n = just n
toRaw (T ⇒ T₁) t = {!!}
toRaw (T ⋆ T₁) (t , t₁) = toRaw T t >>= (λ r → toRaw T₁ t₁ >>= (λ r₁ → just (r , r₁)))
toRaw (T ⊹ T₁) (inj₁ x) = Data.Maybe.map inj₁ (toRaw T x)
toRaw (T ⊹ T₁) (inj₂ y) = Data.Maybe.map inj₂ (toRaw T₁ y)

fromRaw (Base P) r = {!!}       -- need a Decidable P here
fromRaw Nat r = just r
fromRaw (T ⇒ T₁) r = {!!}
fromRaw (T ⋆ T₁) r = {!!}
fromRaw (T ⊹ T₁) r = {!!}

module rule-by-rule where

  data
    _⊢_÷_ : Env Type → Expr → Type → Set₁ 
   where
    nat' :
      --------------------
      · ⊢ Nat n ÷ Base (_≡_ n)

  corr : Γ ⊢ M ÷ T → ∥ Γ ∥⁺ ⊢ M ⦂ ∥ T ∥
  corr nat' = nat

  lave :
    (÷M : Γ ⊢ M ÷ T) →
    ∀ (t : T⟦ T ⟧) →
    ∃ λ (γ : iEnv E⟦ Γ ⟧) →
    eval (corr ÷M) {!!} ≡ {!!}
  lave = {!!}


data _⊢_÷_ : Env Type → Expr → Type → Set₁ where

  nat' :
    --------------------
    · ⊢ Nat n ÷ Base (_≡_ n)

  var1 :
    ( · , x ⦂ T) ⊢ Var x ÷ T

{-
  var :
    x ⦂ T ∈ Γ →
    --------------------
    Γ ⊢ Var x ÷ T
-}

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




corr-sp : Split Γ Γ₁ Γ₂ → Split ∥ Γ ∥⁺ ∥ Γ₁ ∥⁺ ∥ Γ₂ ∥⁺
corr-sp nil = nil
corr-sp (lft sp) = lft (corr-sp sp)
corr-sp (rgt sp) = rgt (corr-sp sp)

corr : Γ ⊢ M ÷ T → ∥ Γ ∥⁺ ⊢ M ⦂ ∥ T ∥
corr (nat') = nat
corr var1 = var found
-- corr (var x) = var x
corr (lam ⊢M) = lam (corr ⊢M)
corr (pair-E1 ÷M) = pair-E1 (corr ÷M)
corr (pair-E2 ÷M) = pair-E2 (corr ÷M)
corr (pair sp ÷M ÷N) =
  pair (weaken (corr-sp sp) (corr ÷M)) (weaken (split-sym (corr-sp sp)) (corr ÷N))
corr (sum-E sp ÷L ÷M ÷N) =
  sum-E (weaken (corr-sp sp) (corr  ÷L))
        (weaken (lft (split-sym (corr-sp sp))) (corr ÷M))
        (weaken (lft (split-sym (corr-sp sp))) (corr ÷N))
        (refl , refl)
corr (sum-E′ {S = S}{T = T}{U′ = U′}{U″ = U″}{U = U}{ru′=ru″ = ru′=ru″} sp ÷L ÷M ÷N refl) =
  sum-E (weaken (corr-sp sp) (corr ÷L))
        (weaken (lft (split-sym (corr-sp sp))) (corr ÷M))
        (weaken (lft (split-sym (corr-sp sp))) (corr ÷N))
        (⊔-preserves U′ U″)

-- pick one element of a type to demonstrate non-emptiness
one : ∀ (T : Type) {ne-T : ne T} → T⟦ T ⟧
one (Base P) {ne-base ∃P} = ∃P
one Nat = zero
one (T ⇒ T₁) {ne-⇒ ne-T ne-T₁} = λ x → one T₁ {ne-T₁}
one (T ⋆ T₁) {ne-⋆ ne-T ne-T₁} = (one T {ne-T}) , (one T₁ {ne-T₁})
one (T ⊹ T₁) {ne-⊹L ne-T} = inj₁ (one T {ne-T})
one (T ⊹ T₁) {ne-⊹R ne-T₁} = inj₂ (one T₁ {ne-T₁})

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
{-
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
lave :
  (÷M : Γ ⊢ M ÷ T) →
  ∀ (t : T⟦ T ⟧) →
  ∃ λ (γ : iEnv E⟦ Γ ⟧) →
  eval (corr ÷M) γ ≡ t

lave nat' (n , refl) = · , refl

lave var1 t = (· , _ ⦂ t) , refl
-- lave (var x∈) t =  (gen x∈ t) , lookup-gen x∈ t
lave (lam{x = x}{S = S} ÷M) t = · , ext aux
  where
    aux : (s : T⟦ S ⟧) → eval (corr ÷M) (· , x ⦂ s) ≡ t s
    aux s with lave ÷M (t s)
    ... | (· , .x ⦂ a) , snd = {!!} -- impossible to complete!

lave (pair-E1 ÷M) t with lave ÷M (t , one {!!})
... | γ , ih = γ , Eq.cong proj₁ ih
lave (pair-E2 ÷M) t with lave ÷M (one {!!} , t)
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

lave (sum-E′{S = S}{T = T}{U = U} sp ÷L ÷M ÷N uuu) u = {!!}
-}

-- unused stuff

{- unused - needed?
record _←_ (A B : Set) : Set where
  field
    func : A → B
    back : ∀ (b : B) → ∃ λ (a : A) → func a ≡ b

open _←_
-}
