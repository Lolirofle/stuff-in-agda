module Structure.Operator.Properties lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)

Commutativity : {T₁ T₂ : Set} → (T₁ → T₁ → T₂) → Stmt
Commutativity {T₁} (_▫_) = {x y : T₁} → (x ▫ y) ≡ (y ▫ x)

Associativity : {T : Set} → (T → T → T) → Stmt
Associativity {T} (_▫_) = {x y z : T} → ((x ▫ y) ▫ z) ≡ (x ▫ (y ▫ z))

Distributivityₗ : {T₁ T₂ : Set} → (T₁ → T₂ → T₂) → (T₂ → T₂ → T₂) → Stmt
Distributivityₗ {T₁} {T₂} (_▫₁_) (_▫₂_) = ∀ {x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ (x ▫₁ y) ▫₂ (x ▫₁ z)

Distributivityᵣ : {T₁ T₂ : Set} → (T₂ → T₁ → T₂) → (T₂ → T₂ → T₂) → Stmt
Distributivityᵣ {T₁} {T₂} (_▫₁_) (_▫₂_) = ∀ {x y : T₂} {z : T₁} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₂ (y ▫₁ z)

DistributivityIntoᵣ : {T₁ T₂ T₃ : Set} → (T₁ → T₂ → T₃) → (T₁ → T₁ → T₁) → (T₃ → T₃ → T₃) → Stmt
DistributivityIntoᵣ {T₁} {T₂} {T₃} (_▫₁_) (_▫₂_) (_▫₃_) = ∀ {x y : T₁} {z : T₂} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₃ (y ▫₁ z)

Identityₗ : {T₁ T₂ : Set} → (T₁ → T₂ → T₂) → T₁ → Stmt
Identityₗ {_} {T₂} (_▫_) id = {x : T₂} → (id ▫ x) ≡ x

Identityᵣ : {T₁ T₂ : Set} → (T₁ → T₂ → T₁) → T₂ → Stmt
Identityᵣ {T₁} {_} (_▫_) id = {x : T₁} → (x ▫ id) ≡ x

Inverseₗ : {T₊ T₋ Tᵣ : Set} → (T₋ → T₊ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseₗ {T₊} (_▫_) id inv = {x : T₊} → ((inv x) ▫ x) ≡ id

Inverseᵣ : {T₊ T₋ Tᵣ : Set} → (T₊ → T₋ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseᵣ {T₊} (_▫_) id inv = {x : T₊} → (x ▫ (inv x)) ≡ id

Compatibility : {T₁ T₂ : Set} → (T₁ → T₁ → T₁) → (T₁ → T₂ → T₂) → Stmt
Compatibility {T₁} {T₂} (_▫₁_) (_▫₂_) = {x₁ x₂ : T₁} → {y : T₂} → (x₁ ▫₂ (x₂ ▫₂ y)) ≡ ((x₁ ▫₁ x₂) ▫₂ y)

commute : ∀{T _▫_ x y z} → (Commutativity {T} {T} (_▫_)) → (z ≡ x ▫ y) → (z ≡ y ▫ x)
commute comm stmt =
  [≡]-transitivity([∧]-intro
    stmt
    comm
  )
