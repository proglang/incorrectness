module Semantics where

open import Data.Nat
open import Data.Product
open import Data.String
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_; refl)
open Eq.≡-Reasoning
open import Level renaming (zero to lzero; suc to lsuc)

Id = String

variable
  x y : Id
  ℓ : Level

data Expr : Set where
  Var : Id → Expr
  Lam : Id → Expr → Expr
  App : Expr → Expr → Expr
  Pair : Expr → Expr → Expr
  Fst Snd : Expr → Expr

data Type : Set where
  Base : ℕ → Type
  _⇒_ : Type → Type → Type
  _⋆_ : Type → Type → Type

data Type' : Set where
  Base : ℕ → Type'
  _⇐_ : Type' → Type' → Type'

data Env (A : Set ℓ) : Set ℓ where
  · : Env A
  _,_⦂_ : Env A → Id → A → Env A

data _⦂_∈_ {A : Set ℓ} : Id → A → Env A → Set ℓ where

  found : ∀ {a : A}{E : Env A} →
    x ⦂ a ∈ (E , x ⦂ a)

  there : ∀ {a a' : A}{E : Env A} →
    x ⦂ a ∈ E →
    x ≢ y →
    x ⦂ a ∈ (E , y ⦂ a')

variable
  S T : Type
  Γ : Env Type
  M N : Expr

data _⊢_⦂_ : Env Type → Expr → Type → Set where

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

data _⊢_÷_ : Env Type → Expr → Type → Set where

  var :
    x ⦂ T ∈ Γ →
    --------------------
    Γ ⊢ Var x ÷ T

  lam :
    (· , x ⦂ S) ⊢ M ÷ T →
    --------------------
    · ⊢ Lam x M ÷ (S ⇒ T)

  pair-E1 :
    Γ ⊢ M ÷ (S ⋆ T) →
    --------------------
    Γ ⊢ Fst M ÷ S

  pair-E2 :
    Γ ⊢ M ÷ (S ⋆ T) →
    --------------------
    Γ ⊢ Snd M ÷ T

record _←_ (A B : Set) : Set where
  field
    func : A → B
    back : ∀ (b : B) → ∃ λ (a : A) → func a ≡ b

open _←_

T⟦_⟧ : Type → Set
T⟦ Base x ⟧ = ℕ
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧
T⟦ S ⋆ T ⟧ = T⟦ S ⟧ × T⟦ T ⟧

T'⟦_⟧ : Type → Set
T'⟦ Base x ⟧ = ℕ
T'⟦ S ⇒ T ⟧ = T'⟦ S ⟧ ← T'⟦ T ⟧
T'⟦ S ⋆ T ⟧ = T'⟦ S ⟧ × T'⟦ T ⟧
  
E⟦_⟧ : Env Type → Env Set
E⟦ · ⟧ = ·
E⟦ Γ , x ⦂ T ⟧ = E⟦ Γ ⟧ , x ⦂ T⟦ T ⟧

data iEnv : Env Set → Set where
  · : iEnv ·
  _,_⦂_ : ∀ {E}{A} → iEnv E → (x : Id) → (a : A) → iEnv (E , x ⦂ A)

lookup : (x ⦂ T ∈ Γ) → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
lookup found (γ , _ ⦂ a) = a
lookup (there x∈ x) (γ , _ ⦂ a) = lookup x∈ γ

eval : Γ ⊢ M ⦂ T → iEnv E⟦ Γ ⟧ → T⟦ T ⟧
eval (var x∈) γ = lookup x∈ γ
eval (lam ⊢M) γ = λ s → eval ⊢M (γ , _ ⦂ s)
eval (app ⊢M ⊢N) γ = eval ⊢M γ (eval ⊢N γ)
eval (pair ⊢M ⊢N) γ = (eval ⊢M γ) , (eval ⊢N γ)
eval (pair-E1 ⊢M) γ = proj₁ (eval ⊢M γ)
eval (pair-E2 ⊢M) γ = proj₂ (eval ⊢M γ)

corr : Γ ⊢ M ÷ T → Γ ⊢ M ⦂ T
corr (var x) = var x
corr (lam ⊢M) = lam (corr ⊢M)
corr (pair-E1 ÷M) = pair-E1 (corr ÷M)
corr (pair-E2 ÷M) = pair-E2 (corr ÷M)

-- pick one element of a type to demonstrate non-emptiness
one : T⟦ T ⟧
one {Base x} = 0
one {S ⇒ T} = λ x → one
one {S ⋆ T} = one , one

many : iEnv E⟦ Γ ⟧
many {·} = ·
many {Γ , x ⦂ T} = many , x ⦂ one

gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → iEnv E⟦ Γ ⟧
gen found t = many , _ ⦂ t
gen (there x∈ x) t = (gen x∈ t) , _ ⦂ one

lookup-gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → lookup x∈ (gen x∈ t) ≡ t
lookup-gen found t = refl
lookup-gen (there x∈ x) t = lookup-gen x∈ t

open Eq.≡-Reasoning

postulate
  ext : ∀ {A B : Set}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

-- soundness of the incorrectness rules
lave :
  (÷M : Γ ⊢ M ÷ T) →
  ∀ (t : T⟦ T ⟧) →
  ∃ λ (γ : iEnv E⟦ Γ ⟧) →
  eval (corr ÷M) γ ≡ t
lave (var x∈) t =  (gen x∈ t) , lookup-gen x∈ t
lave (lam{x = x}{S = S} ÷M) t = · , ext aux
  where
    aux : (s : T⟦ S ⟧) → eval (corr ÷M) (· , x ⦂ s) ≡ t s
    aux s with lave ÷M (t s)
    ... | (· , .x ⦂ a) , snd = {!!} -- cannot complete!
lave (pair-E1 ÷M) t with lave ÷M (t , one)
... | γ , ih rewrite Eq.sym ih = γ , {!ih!}
lave (pair-E2 ÷M) t = {!!}
