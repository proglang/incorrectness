module Semantics where

open import Data.Nat
open import Data.Product
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero; suc to lsuc)

Id = String

variable
  x y : Id
  ℓ : Level

data Expr : Set where
  Var : Id → Expr
  Lam : Id → Expr → Expr
  App : Expr → Expr → Expr

data Type : Set where
  Base : ℕ → Type
  _⇒_ : Type → Type → Type

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
  S' T' : Type'
  Γ' : Env Type'

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

data _⊢_÷_ : Env Type' → Expr → Type' → Set where

  var :
    x ⦂ T' ∈ Γ' →
    --------------------
    Γ' ⊢ Var x ÷ T'

record _←_ (A B : Set) : Set where
  field
    func : A → B
    back : ∀ (b : B) → ∃ λ (a : A) → func a ≡ b

T⟦_⟧ : Type → Set
T⟦ Base x ⟧ = ℕ
T⟦ S ⇒ T ⟧ = T⟦ S ⟧ → T⟦ T ⟧

T'⟦_⟧ : Type' → Set
T'⟦ Base x ⟧ = ℕ
T'⟦ S' ⇐ T' ⟧ = T'⟦ S' ⟧ ← T'⟦ T' ⟧
  
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

T-corr : Type' → Type
T-corr (Base x) = Base x
T-corr (S' ⇐ T') = T-corr S' ⇒ T-corr T'

TE-corr : Env Type' → Env Type
TE-corr · = ·
TE-corr (Γ' , x ⦂ T') = (TE-corr Γ') , x ⦂ T-corr T'

∈-corr : (x∈  : x ⦂ T' ∈ Γ') → x ⦂ T-corr T' ∈ TE-corr Γ'
∈-corr found = found
∈-corr (there x∈ x) = there (∈-corr x∈) x

corr : Γ' ⊢ M ÷ T' → TE-corr Γ' ⊢ M ⦂ T-corr T'
corr (var x) = var (∈-corr x)


-- pick one element of a type to demonstrate non-emptiness
one : T⟦ T ⟧
one {Base x} = 0
one {S ⇒ T} = λ x → one

many : iEnv E⟦ Γ ⟧
many {·} = ·
many {Γ , x ⦂ T} = many , x ⦂ one

gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → iEnv E⟦ Γ ⟧
gen found t = many , _ ⦂ t
gen (there x∈ x) t = (gen x∈ t) , _ ⦂ one

lookup-gen : (x∈ : x ⦂ T ∈ Γ) (t  : T⟦ T ⟧) → lookup x∈ (gen x∈ t) ≡ t
lookup-gen found t = refl
lookup-gen (there x∈ x) t = lookup-gen x∈ t

-- soundness of the incorrectness rules
lave :
  (÷M : Γ' ⊢ M ÷ T') →
  ∀ (t : T⟦ T-corr T' ⟧) → ∃ λ (γ : iEnv E⟦ TE-corr Γ' ⟧) → eval (corr ÷M) γ ≡ t
lave (var x∈) = λ t → (gen (∈-corr x∈) t) , (lookup-gen (∈-corr x∈) t)
