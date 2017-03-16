module Structure.Operator.Properties lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)

Commutativity : {T₁ T₂ : Stmt} → (T₁ → T₁ → T₂) → Stmt
Commutativity {T₁} (_▫_) = {x y : T₁} → (x ▫ y) ≡ (y ▫ x)

Associativity : {T : Stmt} → (T → T → T) → Stmt
Associativity {T} (_▫_) = {x y z : T} → ((x ▫ y) ▫ z) ≡ (x ▫ (y ▫ z))

Identityₗ : {T₁ T₂ : Stmt} → (T₁ → T₂ → T₂) → T₁ → Stmt
Identityₗ {_} {T₂} (_▫_) id = {x : T₂} → (id ▫ x) ≡ x

Identityᵣ : {T₁ T₂ : Stmt} → (T₁ → T₂ → T₁) → T₂ → Stmt
Identityᵣ {T₁} {_} (_▫_) id = {x : T₁} → (x ▫ id) ≡ x

Inverseₗ : {T₊ T₋ Tᵣ : Stmt} → (T₋ → T₊ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseₗ {T₊} (_▫_) id inv = {x : T₊} → ((inv x) ▫ x) ≡ id

Inverseᵣ : {T₊ T₋ Tᵣ : Stmt} → (T₊ → T₋ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
Inverseᵣ {T₊} (_▫_) id inv = {x : T₊} → (x ▫ (inv x)) ≡ id
