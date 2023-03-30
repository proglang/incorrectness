### notes on first order incorrectness typing
### IST - March 2023

ℓ ranges over a finite set of labels (let's say {l, r})

Σ ::= ...  f : T → T
Γ ::= ...  x : T
S, T, U ::= { v | P v } | S × T | in ℓ S | S ⊔ T

d ::= f x = e

e ::= x | f e
  | n | e + e | if0 e e e
  | (e, e) | let (x, y) = e in e
  | ℓ e | case e of ℓᵢ xᵢ → eᵢ

### subtyping (standard for refinement typing) and least upper bound

P → Q
-------------------------
{ v | P v } <: { v | Q v}

S <: S ⊔ T

T <: S ⊔ T

etc

least upper bound only defined for types with same underlying raw (simple) type

{ z | P z } ⊔ { z | Q z } = { z | P z ∨ Q z }

pointwise for pairs

in ℓ S ⊔ in ℓ T = in ℓ (S ⊔ T)


### typing rules

Γ, x : T ⊢ x ÷ T

Γ ⊢ n ÷ { v | v = n }

Γ₁ ⊢ e₁ ÷ T₁
Γ₂ ⊢ e₂ ÷ T₂
---------------------------
Γ₁, Γ₂ ⊢ (e₁, e₂) ÷ T₁ × T₂


Γ₁ ⊢ e₁ ÷ S × T
Γ₂, x : S, y : T ⊢ e₂ ÷ U
-----------------------------------
Γ₁, Γ₂ ⊢ let (x, y) = e₁ in e₂ ÷ U


Γ ⊢ e ÷ S
--------------------
Γ ⊢ ℓ e ÷ in ℓ S


Γ₀ ⊢ e₀ ÷ ⊔{ in ℓᵢ Sᵢ }
Γᵢ, xᵢ : Sᵢ ⊢ eᵢ ÷ Uᵢ
Γ₂ = ⊔{ Γᵢ }
----------------------------------------
Γ₀, Γ₂ ⊢ case e₀ of { ℓᵢ xᵢ → eᵢ } ÷ ⊔{ Uᵢ }

## a single-point function type is not sufficient for multiple (recursive) calls

Σ(f) = ∩{ Sᵢ → Tᵢ | i ∈ I }
j ∈ I
Γ ⊢ e ÷ Sⱼ
------------
Γ ⊢ f e ÷ Tⱼ

## it's enough if there exists a single pair x, y such that P (x + y)

P (x + y)
Γ₁ ⊢ e₁ ÷ { z | z = x }
Γ₂ ⊢ e₂ ÷ { z | z = y }
------------------------------
Γ₁, Γ₂ ⊢ e₁ + e₂ ÷ { z | P z }

Γ₀ ⊢ e₀ ÷ { z | True }
Γ₁ ⊢ e₁ ÷ U₁
Γ₂ ⊢ e₂ ÷ U₂ 
------------------------------
Γ₀, Γ₁ ⊔ Γ₂ ⊢ if0 e₀ e₁ e₂ ÷ U₁ ⊔ U₂

