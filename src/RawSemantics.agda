module RawSemantics where

open import Data.Maybe
open import Data.Nat hiding (_⊔_; _⊓_)
open import Data.Product
open import Data.Sum
open import Data.String using (String)
open import Data.Unit hiding (_≟_)
open import Data.Empty

open import Function using (_∘_)

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl)
open Eq.≡-Reasoning
open import Level hiding (_⊔_) renaming (zero to lzero; suc to lsuc)

{- TODO:
* might be useful to distinguish positive and negative (refinement) types from the start
* subtyping of refinement types
* union types: want a rule to convert from a (union) type to a sum type using a decidable predicate
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
  LetPair : Id → Id → Expr → Expr → Expr
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

data AllEnv (A : Set ℓ) (P : A → Set) : Env A → Set ℓ where
  · : AllEnv A P ·
  _,_ : ∀ {γ}{x : Id}{a : A} → AllEnv A P γ → P a → AllEnv A P (γ , x ⦂ a)

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

data jEnv {A : Set ℓ} (⟦_⟧ : A → Set) : Env A → Set where
  · : jEnv ⟦_⟧ ·
  _,_⦂_ : ∀ {E}{A} → jEnv ⟦_⟧ E → (x : Id) → (a : ⟦ A ⟧) → jEnv ⟦_⟧ (E , x ⦂ A)

-- F here is a natural transformation
jEnvMap : {A : Set ℓ} {⟦_⟧ ⟦_⟧′ : A → Set}{E : Env A} →
  (F : {a : A} → ⟦ a ⟧ → ⟦ a ⟧′) →
  jEnv ⟦_⟧ E → jEnv ⟦_⟧′ E
jEnvMap F · = ·
jEnvMap F (env , x ⦂ ⟦a⟧) = (jEnvMap F env) , x ⦂ F ⟦a⟧

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

  pair-E :
    Δ ⊢ M ⦂ (RS ⋆ RT) →
    ((Δ , x ⦂ RS) , y ⦂ RT) ⊢ N ⦂ RU →
    ------------------------------
    Δ ⊢ LetPair x y M N ⦂ RU

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
    Δ ⊢ Inr N ⦂ (RS ⊹ RT)
  
  sum-E :
    Δ ⊢ L ⦂ (RS ⊹ RT) →
    (Δ , x ⦂ RS) ⊢ M ⦂ RU →
    (Δ , y ⦂ RT) ⊢ N ⦂ RV →
    RW ≡ RU × RW ≡ RV →
    --------------------
    Δ ⊢ Case L x M y N ⦂ RW

glookup : ∀ {A : Set ℓ} {⟦_⟧ : A → Set}{Φ : Env A}{a : A} →
  (x ⦂ a ∈ Φ) → jEnv ⟦_⟧ Φ → ⟦ a ⟧
glookup found (γ , _ ⦂ a) = a
glookup (there x∈) (γ , _ ⦂ a) = glookup x∈ γ
{-
lookup : (x ⦂ RT ∈ Δ) → jEnv R⟦_⟧ Δ → R⟦ RT ⟧
lookup found (γ , _ ⦂ a) = a
lookup (there x∈) (γ , _ ⦂ a) = lookup x∈ γ
-}
eval : Δ ⊢ M ⦂ RT → jEnv R⟦_⟧ Δ → R⟦ RT ⟧
eval (nat{n = n}) γ = n
eval (var x∈) γ = glookup x∈ γ
eval (lam ⊢M) γ = λ s → eval ⊢M (γ , _ ⦂ s)
eval (app ⊢M ⊢N) γ = eval ⊢M γ (eval ⊢N γ)
eval (pair ⊢M ⊢N) γ = (eval ⊢M γ) , (eval ⊢N γ)
eval (pair-E ⊢M ⊢N) γ with eval ⊢M γ
... | vx , vy = eval ⊢N ((γ , _ ⦂ vx) , _ ⦂ vy)
eval (pair-E1 ⊢M) γ = proj₁ (eval ⊢M γ)
eval (pair-E2 ⊢M) γ = proj₂ (eval ⊢M γ)
eval (sum-I1 ⊢M) γ = inj₁ (eval ⊢M γ)
eval (sum-I2 ⊢N) γ = inj₂ (eval ⊢N γ)
eval (sum-E ⊢L ⊢M ⊢N (refl , refl)) γ =
  [ (λ s → eval ⊢M (γ , _ ⦂ s)) , (λ t → eval ⊢N (γ , _ ⦂ t)) ] (eval ⊢L γ)

----------------------------------------------------------------------
-- refinement types that drive the incorrectness typing

data Type : Set₁ where
  Base : (P : ℕ → Set) (p : ∀ n → Dec (P n)) → Type -- refinement
  Nat : Type
  _⇒_ _⋆_ : (S : Type) (T : Type) → Type
  _⊹_ _⊹ˡ_ _⊹ʳ_ : (S : Type) (T : Type) → Type

T-Nat : Type
T-Nat = Base (λ n → ⊤) (λ n → yes tt) -- all natural numbers

-- characterize non-empty types

data ne : Type → Set where
  ne-base : ∀ {P p} → (∃P : Σ ℕ P) → ne (Base P p)
  ne-nat : ne Nat
  ne-⇒ : ∀ {S T} → ne S → ne T → ne (S ⇒ T)
  ne-⋆ : ∀ {S T} → ne S → ne T → ne (S ⋆ T)
  ne-⊹L : ∀ {S T} → ne S → ne (S ⊹ T)
  ne-⊹R : ∀ {S T} → ne T → ne (S ⊹ T)

∥_∥ : Type → RawType
∥ Base P p ∥ = Nat
∥ Nat ∥ = Nat
∥ S ⇒ S₁ ∥ = ∥ S ∥ ⇒ ∥ S₁ ∥
∥ S ⋆ S₁ ∥ = ∥ S ∥ ⋆ ∥ S₁ ∥
∥ S ⊹ S₁ ∥ = ∥ S ∥ ⊹ ∥ S₁ ∥
∥ S ⊹ˡ S₁ ∥ = ∥ S ∥ ⊹ ∥ S₁ ∥
∥ S ⊹ʳ S₁ ∥ = ∥ S ∥ ⊹ ∥ S₁ ∥

T⟦_⟧ : Type → Set
T⟦ Base P p ⟧ = Σ ℕ P
T⟦ Nat ⟧ = ℕ
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧
T⟦ S ⋆ T ⟧ = T⟦ S ⟧ × T⟦ T ⟧
T⟦ S ⊹ T ⟧ = T⟦ S ⟧ ⊎ T⟦ T ⟧
T⟦ S ⊹ˡ T ⟧ = T⟦ S ⟧
T⟦ S ⊹ʳ T ⟧ = T⟦ T ⟧

M⟦_⟧ V⟦_⟧ : Type → (Set → Set) → Set

V⟦ Base P p ⟧ m = Σ ℕ P
V⟦ Nat ⟧ m = ℕ
V⟦ T ⇒ T₁ ⟧ m = V⟦ T ⟧ m → M⟦ T₁ ⟧ m
V⟦ T ⋆ T₁ ⟧ m = V⟦ T ⟧ m × V⟦ T₁ ⟧ m
V⟦ T ⊹ T₁ ⟧ m = V⟦ T ⟧ m ⊎ V⟦ T₁ ⟧ m
V⟦ T ⊹ˡ T₁ ⟧ m = V⟦ T ⟧ m
V⟦ T ⊹ʳ T₁ ⟧ m = V⟦ T₁ ⟧ m

M⟦ T ⟧ m = m (V⟦ T ⟧ m)

E⟦_⟧ : Env Type → Env Set
E⟦_⟧ = T⟦_⟧ ⁺

∥_∥⁺ : Env Type → Env RawType
∥_∥⁺ = ∥_∥ ⁺

-- a value is a member of refinement type T

_∋_ : (T : Type) → R⟦ ∥ T ∥ ⟧ → Set
Base P p ∋ x = P x
Nat ∋ x = ⊤
(T ⇒ T₁) ∋ f = ∀ x → T ∋ x → T₁ ∋ f x
(T ⋆ T₁) ∋ (fst , snd) = T ∋ fst × T₁ ∋ snd
(T ⊹ T₁) ∋ inj₁ x = T ∋ x
(T ⊹ T₁) ∋ inj₂ y = T₁ ∋ y
(S ⊹ˡ T) ∋ inj₁ x = S ∋ x
(S ⊹ˡ T) ∋ inj₂ y = ⊥
(S ⊹ʳ T) ∋ inj₁ x = ⊥
(S ⊹ʳ T) ∋ inj₂ y = T ∋ y

-- operations on predicates 
_∨_ : (P Q : ℕ → Set) → ℕ → Set
P ∨ Q = λ n → P n ⊎ Q n

_∧_ : (P Q : ℕ → Set) → ℕ → Set
P ∧ Q = λ n → P n × Q n

implies : ∀ {P Q : ℕ → Set} → (n : ℕ) → P n → (P n ⊎ Q n)
implies n Pn = inj₁ Pn

p*q->p : ∀ {P Q : ℕ → Set} → (n : ℕ) → (P n × Q n) → P n
p*q->p n (Pn , Qn) = Pn

dec-P∨Q : ∀ {P Q : ℕ → Set} → (p : ∀ n → Dec (P n)) (q : ∀ n → Dec (Q n)) → (∀ n → Dec ((P ∨ Q) n))
dec-P∨Q p q n with p n | q n
... | no ¬p | no ¬q = no [ ¬p , ¬q ]
... | no ¬p | yes !q = yes (inj₂ !q)
... | yes !p | no ¬q = yes (inj₁ !p)
... | yes !p | yes !q = yes (inj₁ !p)

dec-P∧Q : ∀ {P Q : ℕ → Set} → (p : ∀ n → Dec (P n)) (q : ∀ n → Dec (Q n)) → (∀ n → Dec ((P ∧ Q) n))
dec-P∧Q p q n with p n | q n
... | no ¬p | no ¬q = no (¬p ∘ proj₁)
... | no ¬p | yes !q = no (¬p ∘ proj₁)
... | yes !p | no ¬q = no (¬q ∘ proj₂)
... | yes !p | yes !q = yes (!p , !q)

_⊔_ _⊓_  : (S T : Type) {r : ∥ S ∥ ≡ ∥ T ∥} → Type

(Base P p ⊔ Base P₁ p₁) {refl} = Base (P ∨ P₁) (dec-P∨Q p p₁)
(Base P p ⊔ Nat) = Nat
(Nat ⊔ Base P p) = Nat
(Nat ⊔ Nat) = Nat
((S ⇒ S₁) ⊔ (T ⇒ T₁)) {r} with ss⇒tt r
... | sss , ttt = (S ⊓ T){sss} ⇒ (S₁ ⊔ T₁){ttt}
((S ⋆ S₁) ⊔ (T ⋆ T₁)) {r} with ss⋆tt r
... | sss , ttt = (S ⊔ T){sss} ⋆ (S₁ ⊔ T₁){ttt}
((S ⊹ S₁) ⊔ (T ⊹ T₁)) {r} with ss⊹tt r
... | sss , ttt = (S ⊔ T){sss} ⊹ (S₁ ⊔ T₁){ttt}
((S ⊹ S₁) ⊔ (T ⊹ˡ T₁)) {r} with ss⊹tt r
... | sss , ttt = (S ⊔ T){sss} ⊹ S₁
((S ⊹ S₁) ⊔ (T ⊹ʳ T₁)) {r} with ss⊹tt r
... | sss , ttt = S ⊹ (S₁ ⊔ T₁){ttt}
((S ⊹ˡ S₁) ⊔ (T ⊹ T₁)) {r} with ss⊹tt r
... | sss , ttt = ((S ⊔ T){sss}) ⊹ (S₁ ⊔ T₁){ttt}
((S ⊹ˡ S₁) ⊔ (T ⊹ˡ T₁)) {r} with ss⊹tt r
... | sss , ttt = ((S ⊔ T){sss}) ⊹ˡ ((S₁ ⊔ T₁){ttt})
((S ⊹ˡ S₁) ⊔ (T ⊹ʳ T₁)) {r} = S ⊹ T₁
((S ⊹ʳ S₁) ⊔ (T ⊹ T₁)) {r} with ss⊹tt r
... | sss , ttt = T ⊹ ((S₁ ⊔ T₁) {ttt})
((S ⊹ʳ S₁) ⊔ (T ⊹ˡ T₁)) {r} = T ⊹ S₁
((S ⊹ʳ S₁) ⊔ (T ⊹ʳ T₁)) {r} with ss⊹tt r
... | sss , ttt = (S ⊔ T) {sss} ⊹ (S₁ ⊔ T₁) {ttt}

Base P p ⊓ Base P₁ p₁ = Base (P ∧ P₁) (dec-P∧Q p p₁)
Base P p ⊓ Nat = Base P p
Nat ⊓ Base P p = Base P p
Nat ⊓ Nat = Nat
((S ⇒ S₁) ⊓ (T ⇒ T₁)){r} with ss⇒tt r
... | sss , ttt = (S ⊔ T){sss} ⇒ (S₁ ⊓ T₁){ttt}
((S ⋆ S₁) ⊓ (T ⋆ T₁)){r} with ss⋆tt r
... | sss , ttt = (S ⊓ T){sss} ⋆ (S₁ ⊓ T₁){ttt}
((S ⊹ S₁) ⊓ (T ⊹ T₁)){r} with ss⊹tt r
... | sss , ttt = (S ⊓ T){sss} ⊹ (S₁ ⊓ T₁){ttt}
((S ⊹ˡ S₁) ⊓ (T ⊹ T₁)) {r} = {!!}
((S ⊹ʳ S₁) ⊓ (T ⊹ T₁)) {r} = {!!}
((S ⊹ S₁) ⊓ (T ⊹ˡ T₁)) {r} = {!!}
((S ⊹ˡ S₁) ⊓ (T ⊹ˡ T₁)) {r} = {!!}
((S ⊹ʳ S₁) ⊓ (T ⊹ˡ T₁)) {r} = {!!}
((S ⊹ S₁) ⊓ (T ⊹ʳ T₁)) {r} = {!!}
((S ⊹ˡ S₁) ⊓ (T ⊹ʳ T₁)) {r} = {!!}
((S ⊹ʳ S₁) ⊓ (T ⊹ʳ T₁)) {r} = {!!}

variable
  S T U S′ T′ U′ U″ : Type
  Γ Γ₁ Γ₂ : Env Type
  P : ℕ → Set
  p : ∀ n → Dec (P n)
  A : Set ℓ
  a : A
  Φ Φ₁ Φ₂ : Env A

⊔-preserves : ∀ S T {st : ∥ S ∥ ≡ ∥ T ∥} →
  ∥ (S ⊔ T){st} ∥ ≡ ∥ S ∥ × ∥ (S ⊔ T){st} ∥ ≡ ∥ T ∥
⊓-preserves : ∀ S T {st : ∥ S ∥ ≡ ∥ T ∥} →
  ∥ (S ⊓ T){st} ∥ ≡ ∥ S ∥ × ∥ (S ⊓ T){st} ∥ ≡ ∥ T ∥

⊔-preserves (Base P p) (Base P₁ p₁) {refl} = refl , refl
⊔-preserves (Base P p) Nat {st} = refl , refl
⊔-preserves Nat (Base P p) {st} = refl , refl
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
⊔-preserves (S ⊹ S₁) (T ⊹ˡ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s = refl , st
⊔-preserves (S ⊹ S₁) (T ⊹ʳ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st
⊔-preserves (S ⊹ˡ S₁) (T ⊹ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st
⊔-preserves (S ⊹ˡ S₁) (T ⊹ˡ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st
⊔-preserves (S ⊹ˡ S₁) (T ⊹ʳ T₁) {st} with ss⊹tt st
... | sss , ttt rewrite sss | ttt = refl , refl
⊔-preserves (S ⊹ʳ S₁) (T ⊹ T₁) {st} with ss⊹tt st
... | sss , ttt rewrite sss with ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t rewrite sut=t = (Eq.sym st) , refl
⊔-preserves (S ⊹ʳ S₁) (T ⊹ˡ T₁) {st} with ss⊹tt st
... | sss , ttt rewrite sss = refl , st
⊔-preserves (S ⊹ʳ S₁) (T ⊹ʳ T₁) {st} with ss⊹tt st
... | sss , ttt with ⊔-preserves S T {sss} | ⊔-preserves S₁ T₁ {ttt}
... | sut=s , sut=t | sut=s₁ , sut=t₁ rewrite sut=s | sut=s₁ = refl , st

⊓-preserves (Base P p) (Base P₁ p₂) {st} = refl , refl
⊓-preserves (Base P p) Nat {st} = refl , refl
⊓-preserves Nat (Base P p) {st} = refl , refl
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
⊓-preserves (S ⊹ˡ S₁) (T ⊹ T₁) {st} = {!!}
⊓-preserves (S ⊹ʳ S₁) (T ⊹ T₁) {st} = {!!}
⊓-preserves S (T ⊹ˡ T₁) {st} = {!!}
⊓-preserves S (T ⊹ʳ T₁) {st} = {!!}


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
    {p : ∀ n → Dec (P n)} 
    {q : ∀ n → Dec (Q n)}
    (p→q : ∀ n → P n → Q n) →
    Base P p <: Base Q q

  <:-base-nat : ∀ {p : ∀ n → Dec (P n)} →
    Base P p <: Nat
    
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

  <:-⊹ˡ-⊹ :
    S <: S′ →
    (S ⊹ˡ T) <: (S′ ⊹ T)

  <:-⊹ʳ-⊹ :
    T <: T′ →
    (S ⊹ʳ T) <: (S ⊹ T′)

-- subtyping is compatible with raw types

<:-raw : S <: T → ∥ S ∥ ≡ ∥ T ∥
<:-raw <:-refl = refl
<:-raw (<:-base P Q p→q) = refl
<:-raw <:-base-nat = refl
<:-raw (<:-⇒ s<:t s<:t₁) = Eq.cong₂ _⇒_ (Eq.sym (<:-raw s<:t)) (<:-raw s<:t₁)
<:-raw (<:-⋆ s<:t s<:t₁) = Eq.cong₂ _⋆_ (<:-raw s<:t) (<:-raw s<:t₁)
<:-raw (<:-⊹ s<:t s<:t₁) = Eq.cong₂ _⊹_ (<:-raw s<:t) (<:-raw s<:t₁)
<:-raw (<:-⊹ˡ-⊹ s<:t) = Eq.cong₂ _⊹_ (<:-raw s<:t) refl
<:-raw (<:-⊹ʳ-⊹ s<:t) = Eq.cong₂ _⊹_ refl (<:-raw s<:t)

<:-⊔ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → S <: (S ⊔ T){c}
<:-⊓ : ∀ S T → {c : ∥ S ∥ ≡ ∥ T ∥} → (S ⊓ T){c} <: S

<:-⊔ (Base P p) (Base P₁ p₁) {refl} = <:-base P (P ∨ P₁) implies
<:-⊔ (Base P p) Nat = <:-base-nat
<:-⊔ Nat (Base P p) = <:-refl
<:-⊔ Nat Nat = <:-refl
<:-⊔ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊓ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊔ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊔ S T) (<:-⊔ S₁ T₁)
<:-⊔ (S ⊹ S₁) (T ⊹ˡ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊔ S T) <:-refl
<:-⊔ (S ⊹ S₁) (T ⊹ʳ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ <:-refl (<:-⊔ S₁ T₁)
<:-⊔ (S ⊹ˡ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c12 = {!<:-⊹!}
<:-⊔ (S ⊹ˡ S₁) (T ⊹ˡ T₁) = {!!}
<:-⊔ (S ⊹ˡ S₁) (T ⊹ʳ T₁) = {!!}
<:-⊔ (S ⊹ʳ S₁) T = {!!}


<:-⊓ (Base P p) (Base P₁ p₁) {refl} = <:-base (P ∧ P₁) P p*q->p
<:-⊓ (Base P p) Nat = <:-refl
<:-⊓ Nat (Base P p) = <:-base-nat
<:-⊓ Nat Nat = <:-refl
<:-⊓ (S ⇒ S₁) (T ⇒ T₁) {c} with ss⇒tt c
... | c1 , c2 = <:-⇒ (<:-⊔ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⋆ S₁) (T ⋆ T₁) {c} with ss⋆tt c
... | c1 , c2 = <:-⋆ (<:-⊓ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⊹ S₁) (T ⊹ T₁) {c} with ss⊹tt c
... | c1 , c2 = <:-⊹ (<:-⊓ S T) (<:-⊓ S₁ T₁)
<:-⊓ (S ⊹ S₁) (T ⊹ˡ T₁) = {!!}
<:-⊓ (S ⊹ S₁) (T ⊹ʳ T₁) = {!!}
<:-⊓ (S ⊹ˡ S₁) T = {!!}
<:-⊓ (S ⊹ʳ S₁) T = {!!}

-- subtyping generates an embedding and a projection
embed : (S <: T) → T⟦ S ⟧ → T⟦ T ⟧
embed <:-refl s = s
embed (<:-base P Q p→q) (s , p) = s , p→q s p
embed <:-base-nat (s , p) = s
embed (<:-⇒ s<:t s<:t₁) s = λ x → embed s<:t₁ (s (embed s<:t x))
embed (<:-⋆ s<:t s<:t₁) (s , t) = (embed s<:t s) , (embed s<:t₁ t)
embed (<:-⊹ s<:t s<:t₁) (inj₁ x) = inj₁ (embed s<:t x)
embed (<:-⊹ s<:t s<:t₁) (inj₂ y) = inj₂ (embed s<:t₁ y)
embed (<:-⊹ˡ-⊹ s<:t) s = inj₁ (embed s<:t s)
embed (<:-⊹ʳ-⊹ s<:t) s = inj₂ (embed s<:t s)

{- no definable
inject : T⟦ S ⟧ → V⟦ S ⟧ Maybe
eject  : V⟦ S ⟧ Maybe → Maybe T⟦ S ⟧

inject {Base P p} s = s
inject {Nat} s = s
inject {S ⇒ S₁} s = λ x → eject{S} x >>= λ x₁ → let s₁ = s x₁ in just (inject {S₁} s₁)
inject {S ⋆ S₁} (s , s₁) = (inject{S} s) , (inject{S₁} s₁)
inject {S ⊹ S₁} (inj₁ x) = inj₁ (inject{S} x)
inject {S ⊹ S₁} (inj₂ y) = inj₂ (inject{S₁} y)
inject {S ⊹ˡ S₁} s = inject{S} s
inject {S ⊹ʳ S₁} s = inject{S₁} s

eject {Base P p} s = {!!}
eject {Nat} s = {!!}
eject {S ⇒ S₁} s = just (λ x → {!!})
eject {S ⋆ S₁} s = {!!}
eject {S ⊹ S₁} s = {!!}
eject {S ⊹ˡ S₁} s = {!!}
eject {S ⊹ʳ S₁} s = {!!}
-}

project : (S <: T) → V⟦ T ⟧ Maybe → M⟦ S ⟧ Maybe
project <:-refl t = just t
project (<:-base P Q {p = p} p→q) (t , qt)
  with p t
... | no ¬p = nothing
... | yes p₁ = just (t , p₁)
project (<:-base-nat{p = p}) t
  with p t
... | no ¬p = nothing
... | yes p₁ = just (t , p₁)
project (<:-⇒ s<:t s<:t₁) t = just λ s → project s<:t s >>= t >>= project s<:t₁
project (<:-⋆ s<:t s<:t₁) (s , t) = project s<:t s >>= λ x → project s<:t₁ t >>= λ x₁ → just (x , x₁)
project (<:-⊹ s<:t s<:t₁) (inj₁ x) = Data.Maybe.map inj₁ (project s<:t x)
project (<:-⊹ s<:t s<:t₁) (inj₂ y) = Data.Maybe.map inj₂ (project s<:t₁ y)
project (<:-⊹ˡ-⊹ s<:t) (inj₁ x) = project s<:t x
project (<:-⊹ˡ-⊹ s<:t) (inj₂ y) = nothing
project (<:-⊹ʳ-⊹ s<:t) (inj₁ x) = nothing
project (<:-⊹ʳ-⊹ s<:t) (inj₂ y) = project s<:t y

split-sym : Split Φ Φ₁ Φ₂ → Split Φ Φ₂ Φ₁
split-sym nil = nil
split-sym (lft sp) = rgt (split-sym sp)
split-sym (rgt sp) = lft (split-sym sp)

split-map : ∀ {A : Set ℓ}{B : Set ℓ′}{Φ Φ₁ Φ₂ : Env A} →
  {f : A → B} → Split Φ Φ₁ Φ₂ → Split ((f ⁺) Φ) ((f ⁺) Φ₁) ((f ⁺) Φ₂)
split-map nil = nil
split-map (lft sp) = lft (split-map sp)
split-map (rgt sp) = rgt (split-map sp)

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
weaken sp (pair-E ⊢M ⊢N) = pair-E (weaken sp ⊢M) (weaken (lft (lft sp)) ⊢N)
weaken sp (pair-E1 ⊢M) = pair-E1 (weaken sp ⊢M)
weaken sp (pair-E2 ⊢M) = pair-E2 (weaken sp ⊢M)
weaken sp (sum-I1 ⊢M) = sum-I1 (weaken sp ⊢M)
weaken sp (sum-I2 ⊢N) = sum-I2 (weaken sp ⊢N)
weaken sp (sum-E ⊢L ⊢M ⊢N (RT=RU , RT=RV)) =
  sum-E (weaken sp ⊢L) (weaken (lft sp) ⊢M) (weaken (lft sp) ⊢N) (RT=RU , RT=RV)

-- incorrectness typing

-- a positive type contains refinements only in positive positions

mutual
  data Pos : Type → Set where
    Pos-Base : Pos (Base P p)
    Pos-Nat : Pos Nat
    Pos-⇒ : Neg S → Pos T → Pos (S ⇒ T)
    Pos-⋆ : Pos S → Pos T → Pos (S ⋆ T)
    Pos-⊹ : Pos S → Pos T → Pos (S ⊹ T)
    Pos-⊹ˡ : Pos S → Pos (S ⊹ˡ T)
    Pos-⊹ʳ : Pos T → Pos (S ⊹ʳ T)

  data Neg : Type → Set where
    Neg-Nat : Neg Nat
    Neg-⇒ : Pos S → Neg T → Neg (S ⇒ T)
    Neg-⋆ : Neg S → Neg T → Neg (S ⋆ T)
    Neg-⊹ : Neg S → Neg T → Neg (S ⊹ T)

pos-unique : ∀ T → (pos pos' : Pos T) → pos ≡ pos'
neg-unique : ∀ T → (neg neg' : Neg T) → neg ≡ neg'

pos-unique (Base P p) Pos-Base Pos-Base = refl
pos-unique Nat Pos-Nat Pos-Nat = refl
pos-unique (T ⇒ T₁) (Pos-⇒ x pos) (Pos-⇒ x₁ pos') rewrite neg-unique T x x₁ | pos-unique T₁ pos pos' = refl
pos-unique (T ⋆ T₁) (Pos-⋆ pos pos₁) (Pos-⋆ pos' pos'') rewrite pos-unique T pos pos' | pos-unique T₁ pos₁ pos'' = refl
pos-unique (T ⊹ T₁) (Pos-⊹ pos pos₁) (Pos-⊹ pos' pos'') rewrite pos-unique T pos pos' | pos-unique T₁ pos₁ pos'' = refl
pos-unique (T ⊹ˡ T₁) (Pos-⊹ˡ pos) (Pos-⊹ˡ pos') rewrite pos-unique T pos pos' = refl
pos-unique (T ⊹ʳ T₁) (Pos-⊹ʳ pos) (Pos-⊹ʳ pos') rewrite pos-unique T₁ pos pos' = refl
--etc
neg-unique T neg neg' = {!!}

module positive-restricted where
  toRaw : ∀ T → Pos T → T⟦ T ⟧ → R⟦ ∥ T ∥ ⟧
  fromRaw : ∀ T → Neg T → R⟦ ∥ T ∥ ⟧ → T⟦ T ⟧

  toRaw (Base P p) Pos-Base (n , pn) = n
  toRaw Nat Pos-Nat t = t
  toRaw (T ⇒ T₁) (Pos-⇒ neg pos₁) t = toRaw T₁ pos₁ ∘ t ∘ fromRaw T neg
  toRaw (T ⋆ T₁) (Pos-⋆ pos pos₁) (t , t₁) = toRaw T pos t , (toRaw T₁ pos₁ t₁)
  toRaw (T ⊹ T₁) (Pos-⊹ pos pos₁) (inj₁ x) = inj₁ (toRaw T pos x)
  toRaw (T ⊹ T₁) (Pos-⊹ pos pos₁) (inj₂ y) = inj₂ (toRaw T₁ pos₁ y)
  toRaw (S ⊹ˡ T) (Pos-⊹ˡ pos) x = inj₁ (toRaw S pos x)
  toRaw (S ⊹ʳ T) (Pos-⊹ʳ pos) y = inj₂ (toRaw T pos y)

  fromRaw (Base P p) () r
  fromRaw Nat Neg-Nat r = r
  fromRaw (T ⇒ T₁) (Neg-⇒ pos neg) r = fromRaw T₁ neg ∘ r ∘ toRaw T pos
  fromRaw (T ⋆ T₁) (Neg-⋆ neg neg₁) (r , r₁) = fromRaw T neg r , fromRaw T₁ neg₁ r₁
  fromRaw (T ⊹ T₁) (Neg-⊹ neg neg₁) (inj₁ x) = inj₁ (fromRaw T neg x)
  fromRaw (T ⊹ T₁) (Neg-⊹ neg neg₁) (inj₂ y) = inj₂ (fromRaw T₁ neg₁ y)
  
  toRawEnv : AllEnv Type Pos Γ → jEnv T⟦_⟧ Γ → jEnv R⟦_⟧ ∥ Γ ∥⁺
  toRawEnv{·} posΓ · = ·
  toRawEnv{Γ , _ ⦂ T} (posΓ , x₁) (γ , x ⦂ a) = toRawEnv{Γ} posΓ γ , x ⦂ toRaw T x₁ a

{-
-- attempt to map type (interpretation) to corresponding raw type (interpretation)
-- * must be monadic because of refinement
-- * fails at function types
module monadic where
  toRaw : ∀ T → T⟦ T ⟧ → Maybe R⟦ ∥ T ∥ ⟧
  fromRaw : ∀ T → R⟦ ∥ T ∥ ⟧ → Maybe T⟦ T ⟧

  toRaw (Base P p) (n , Pn) = just n
  toRaw Nat n = just n
  toRaw (T ⇒ T₁) t = {!!}
  toRaw (T ⋆ T₁) (t , t₁) = toRaw T t >>= (λ r → toRaw T₁ t₁ >>= (λ r₁ → just (r , r₁)))
  toRaw (T ⊹ T₁) (inj₁ x) = Data.Maybe.map inj₁ (toRaw T x)
  toRaw (T ⊹ T₁) (inj₂ y) = Data.Maybe.map inj₂ (toRaw T₁ y)

  fromRaw (Base P p) r with p r
  ... | no ¬p = nothing
  ... | yes pr = just (r , pr)
  fromRaw Nat r = just r
  fromRaw (T ⇒ T₁) r = {!!}
  fromRaw (T ⋆ T₁) (r , r₁) = fromRaw T r >>= (λ t → fromRaw T₁ r₁ >>= (λ t₁ → just (t , t₁)))
  fromRaw (T ⊹ T₁) (inj₁ x) = Data.Maybe.map inj₁ (fromRaw T x)
  fromRaw (T ⊹ T₁) (inj₂ y) = Data.Maybe.map inj₂ (fromRaw T₁ y)
-}

corr-sp : Split Γ Γ₁ Γ₂ → Split ∥ Γ ∥⁺ ∥ Γ₁ ∥⁺ ∥ Γ₂ ∥⁺
corr-sp nil = nil
corr-sp (lft sp) = lft (corr-sp sp)
corr-sp (rgt sp) = rgt (corr-sp sp)

postulate
  ext : ∀ {A B : Set}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

unsplit-env :  ∀ {A : Set ℓ} {⟦_⟧ : A → Set}{Φ Φ₁ Φ₂ : Env A}→
  Split Φ Φ₁ Φ₂ → jEnv ⟦_⟧ Φ₁ → jEnv ⟦_⟧ Φ₂ → jEnv ⟦_⟧ Φ
unsplit-env nil γ₁ γ₂ = ·
unsplit-env (lft sp) (γ₁ , _ ⦂ a) γ₂ = (unsplit-env sp γ₁ γ₂) , _ ⦂ a
unsplit-env (rgt sp) γ₁ (γ₂ , _ ⦂ a) = (unsplit-env sp γ₁ γ₂) , _ ⦂ a

unsplit-split :  ∀ {A : Set ℓ} {⟦_⟧ : A → Set}{Φ Φ₁ Φ₂ : Env A} →
  (sp : Split Φ Φ₁ Φ₂) (γ₁ : jEnv ⟦_⟧ Φ₁) (γ₂ : jEnv ⟦_⟧ Φ₂) →
  unsplit-env sp γ₁ γ₂ ≡ unsplit-env (split-sym sp) γ₂ γ₁
unsplit-split nil γ₁ γ₂ = refl
unsplit-split (lft sp) (γ₁ , _ ⦂ a) γ₂ rewrite unsplit-split sp γ₁ γ₂ = refl
unsplit-split (rgt sp) γ₁ (γ₂ , _ ⦂ a) rewrite unsplit-split sp γ₁ γ₂ = refl

lookup-unsplit :  ∀ {A : Set ℓ} {⟦_⟧ : A → Set}{Φ Φ₁ Φ₂ : Env A}{a : A} →
  (sp : Split Φ Φ₁ Φ₂) (γ₁ : jEnv ⟦_⟧ Φ₁) (γ₂ : jEnv ⟦_⟧ Φ₂) →
  (x∈ : x ⦂ a ∈ Φ₁) →
  glookup (weaken-∈ sp x∈) (unsplit-env sp γ₁ γ₂) ≡ glookup x∈ γ₁
lookup-unsplit (lft sp) (γ₁ , _ ⦂ a) γ₂ found = refl
lookup-unsplit (rgt sp) γ₁ (γ₂ , _ ⦂ a) found = lookup-unsplit sp γ₁ γ₂ found
lookup-unsplit (lft sp) (γ₁ , _ ⦂ a) γ₂ (there x∈) = lookup-unsplit sp γ₁ γ₂ x∈
lookup-unsplit (rgt sp) γ₁ (γ₂ , _ ⦂ a) (there x∈) = lookup-unsplit sp γ₁ γ₂ (there x∈)

open positive-restricted
eval-unsplit' : (sp : Split Γ Γ₁ Γ₂) (γ₁ : jEnv T⟦_⟧ Γ₁) (γ₂ : jEnv T⟦_⟧ Γ₂) →
  (posΓ₁ : AllEnv Type Pos Γ₁) (posΓ₂ : AllEnv Type Pos Γ₂) →
  (⊢M : ∥ Γ₁ ∥⁺ ⊢ M ⦂ RT) →
  eval (weaken (corr-sp sp) ⊢M) (unsplit-env (corr-sp sp) (toRawEnv posΓ₁ γ₁) (toRawEnv posΓ₂ γ₂)) ≡ eval ⊢M (toRawEnv posΓ₁ γ₁)
eval-unsplit' sp γ₁ γ₂ posΓ₁ posΓ₂ ⊢M = {!!}
{-
      (eval (weaken (corr-sp sp) (corr ÷M))
       (toRawEnv posΓ (unsplit-env sp γ₁ γ₂)))
-}

eval-unsplit : (sp : Split Δ Δ₁ Δ₂) (γ₁ : jEnv R⟦_⟧ Δ₁) (γ₂ : jEnv R⟦_⟧ Δ₂) →
  (⊢M : Δ₁ ⊢ M ⦂ RT) →
  eval (weaken sp ⊢M) (unsplit-env sp γ₁ γ₂) ≡ eval ⊢M γ₁
eval-unsplit sp γ₁ γ₂ (nat)= refl
eval-unsplit sp γ₁ γ₂ (var x∈) = lookup-unsplit sp γ₁ γ₂ x∈
eval-unsplit sp γ₁ γ₂ (lam ⊢M) = ext (λ s → eval-unsplit (lft sp) (γ₁ , _ ⦂ s) γ₂ ⊢M)
eval-unsplit sp γ₁ γ₂ (app ⊢M ⊢M₁) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M | eval-unsplit sp γ₁ γ₂ ⊢M₁ = refl
eval-unsplit sp γ₁ γ₂ (pair ⊢M ⊢M₁)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M | eval-unsplit sp γ₁ γ₂ ⊢M₁ = refl
eval-unsplit sp γ₁ γ₂ (pair-E ⊢M ⊢N)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = eval-unsplit (lft (lft sp)) ((γ₁ , _ ⦂ _) , _ ⦂ _) γ₂ ⊢N
eval-unsplit sp γ₁ γ₂ (pair-E1 ⊢M)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (pair-E2 ⊢M)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (sum-I1 ⊢M) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢M = refl
eval-unsplit sp γ₁ γ₂ (sum-I2 ⊢N)
  rewrite eval-unsplit sp γ₁ γ₂ ⊢N = refl
eval-unsplit sp γ₁ γ₂ (sum-E ⊢L ⊢M ⊢N (refl , refl)) 
  rewrite eval-unsplit sp γ₁ γ₂ ⊢L
        | ext (λ s → eval-unsplit (lft sp) (γ₁ , _ ⦂ s) γ₂ ⊢M)
        | ext (λ t → eval-unsplit (lft sp) (γ₁ , _ ⦂ t) γ₂ ⊢N)
  = refl

module rule-by-rule where

  open positive-restricted
  open Eq.≡-Reasoning

  data _⊢_÷_ : Env Type → Expr → Type → Set₁ where

    nat' :
      --------------------
      · ⊢ Nat n ÷ Base (_≡_ n) (_≟_ n)

    var' :
      ( · , x ⦂ T) ⊢ Var x ÷ T

    pair-I :
      Split Γ Γ₁ Γ₂ →
      Γ₁ ⊢ M ÷ S →
      Γ₂ ⊢ N ÷ T →
      --------------------
      Γ ⊢ Pair M N ÷ (S ⋆ T)

    sum-I1 :
      Γ ⊢ M ÷ S →
      --------------------
      Γ ⊢ Inl M ÷ (S ⊹ˡ T)

    sum-I2 :
      Γ ⊢ M ÷ T →
      --------------------
      Γ ⊢ Inr M ÷ (S ⊹ʳ T)

    {- perhaps this rule should involve splitting between L and M,N -}
    sum-Case :
      Split Γ Γ₁ Γ₂ →
      Γ₁ ⊢ L ÷ (S ⊹ T) →
      (Γ₂ , x ⦂ S) ⊢ M ÷ (U ⊹ˡ U′) →
      (Γ₂ , y ⦂ T) ⊢ N ÷ (U ⊹ʳ U′) →
      ------------------------------
      Γ ⊢ Case L x M y N ÷ (U ⊹ U′)

  corr : Γ ⊢ M ÷ T → ∥ Γ ∥⁺ ⊢ M ⦂ ∥ T ∥
  corr nat' =
    nat
  corr var' =
    var found
  corr (pair-I sp ÷M ÷N) =
    pair (weaken (corr-sp sp) (corr ÷M)) (weaken (split-sym (corr-sp sp)) (corr ÷N))
  corr (sum-I1 ÷M) = 
    sum-I1 (corr ÷M)
  corr (sum-I2 ÷M) =
    sum-I2 (corr ÷M)
  corr (sum-Case sp ÷L ÷M ÷N) =
    sum-E (weaken (corr-sp sp) (corr ÷L))
          (weaken (split-sym (corr-sp (rgt sp))) (corr ÷M))
          (weaken (split-sym (corr-sp (rgt sp))) (corr ÷N)) 
          (refl , refl) 

  applySplit : {A : Set ℓ}{P : A → Set}{Θ Θ₁ Θ₂ : Env A} →
    Split Θ Θ₁ Θ₂ → AllEnv A P Θ → AllEnv A P Θ₁ × AllEnv A P Θ₂
  applySplit nil · = · , ·
  applySplit (lft sp) (ae , x)
    with applySplit sp ae
  ... | ae1 , ae2 = (ae1 , x) , ae2
  applySplit (rgt sp) (ae , x)
    with applySplit sp ae
  ... | ae1 , ae2 = ae1 , (ae2 , x)

  lave' :
    (÷M : Γ ⊢ M ÷ T) →
    (posT : Pos T) →
    (posΓ : AllEnv Type Pos Γ) →
    ∀ (t : T⟦ T ⟧) →
    ∃ λ (γ : jEnv T⟦_⟧ Γ) →
    eval (corr ÷M) (toRawEnv posΓ γ) ≡ toRaw T posT t
  lave' nat' Pos-Base posΓ (n , refl) = · , refl
  lave' var' posT (· , posT') t rewrite pos-unique _ posT posT' = (· , _ ⦂ t) , refl
  lave' (pair-I x ÷M ÷M₁) posT posΓ t = {!!}
  lave' (sum-I1 ÷M) (Pos-⊹ˡ posT) posΓ t
    with lave' ÷M posT posΓ t
  ... | γ , ih = γ , Eq.cong inj₁ ih
  lave' (sum-I2 ÷M) (Pos-⊹ʳ posT) posΓ t
    with lave' ÷M posT posΓ t
  ... | γ , ih = γ , Eq.cong inj₂ ih
  lave' (sum-Case sp ÷M ÷M₁ ÷M₂) (Pos-⊹ posT posT₁) posΓ (inj₁ x)
    with applySplit sp posΓ
  ... | posΓ₁ , posΓ₂
    with lave' ÷M₁ (Pos-⊹ˡ posT) (posΓ₂ , {!!}) x
  ... | (γ₂ , _ ⦂ s) , ih₂
    with lave' ÷M (Pos-⊹ {!!} {!!}) posΓ₁ (inj₁ s)
  ... | γ₁ , ih₁ =
    let ih₂′ = {!eval-unsplit' sp γ₁ γ₂ posΓ₁ posΓ₂ (corr ÷M) !} in 
    (unsplit-env sp γ₁ γ₂) , {!!}
  lave' (sum-Case sp ÷M ÷M₁ ÷M₂) (Pos-⊹ posT posT₁) posΓ (inj₂ y) = {!!}

  lave :
    (÷M : Γ ⊢ M ÷ T) →
    (pos : Pos T) → 
    ∀ (t : T⟦ T ⟧) →
    ∃ λ (γ : jEnv R⟦_⟧ ∥ Γ ∥⁺) →
    eval (corr ÷M) γ ≡ toRaw T pos t
  lave nat' Pos-Base (n , pn) = · , pn
  lave var' pos t = (· , _ ⦂ toRaw _ pos t) , refl
  lave (pair-I sp ÷M ÷N) (Pos-⋆ pos₁ pos₂) (t₁ , t₂) 
    with lave ÷M pos₁ t₁ | lave ÷N pos₂ t₂
  ... | γ₁ , ih₁ | γ₂ , ih₂ =
    (unsplit-env (corr-sp sp) γ₁ γ₂) , 
    Eq.cong₂ _,_ 
      (begin (eval (weaken (corr-sp sp) (corr ÷M)) (unsplit-env (corr-sp sp) γ₁ γ₂) 
           ≡⟨ eval-unsplit (corr-sp sp) γ₁ γ₂ (corr ÷M) ⟩
             ih₁))
      (begin (eval (weaken (split-sym (corr-sp sp)) (corr ÷N)) (unsplit-env (corr-sp sp) γ₁ γ₂)
           ≡⟨ Eq.cong (eval (weaken (split-sym (corr-sp sp)) (corr ÷N))) (unsplit-split (corr-sp sp) γ₁ γ₂) ⟩
             eval (weaken (split-sym (corr-sp sp)) (corr ÷N)) (unsplit-env (split-sym (corr-sp sp)) γ₂ γ₁)
           ≡⟨ eval-unsplit (split-sym (corr-sp sp)) γ₂ γ₁ (corr ÷N) ⟩
             ih₂))
  lave (sum-I1 ÷M) (Pos-⊹ˡ pos) t
    with lave ÷M pos t
  ... | γ , ih = γ , Eq.cong inj₁ ih
  lave (sum-I2 ÷M) (Pos-⊹ʳ pos) t
    with lave ÷M pos t
  ... | γ , ih = γ , Eq.cong inj₂ ih
  lave (sum-Case sp ÷L ÷M ÷N) (Pos-⊹ p p₁) (inj₁ x)
    with lave ÷M (Pos-⊹ˡ p) x
  ... | (γ₂ , _ ⦂ a) , ih₂
    with lave ÷L {!!} (inj₁ {!!})
  ... | γ₁ , ih₁ = {!!}
  lave (sum-Case sp ÷L ÷M ÷N) (Pos-⊹ p p₁) (inj₂ y) = {!!}

data _⊢_÷_ : Env Type → Expr → Type → Set₁ where

  nat' :
    --------------------
    · ⊢ Nat n ÷ Base (_≡_ n) λ n₁ → n ≟ n₁

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
one (Base P p) {ne-base ∃P} = ∃P
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


{-
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
