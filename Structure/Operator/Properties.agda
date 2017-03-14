module Structure.Operator.Properties where

open import Relator.Equals

Commutativity : {T : Set} → (T → T → T) → Set
Commutativity {T} (_▫_) = {x y : T} → (x ▫ y) ≡ (y ▫ x)

Associativity : {T : Set} → (T → T → T) → Set
Associativity {T} (_▫_) = {x y z : T} → ((x ▫ y) ▫ z) ≡ ((x ▫ y) ▫ z)

Identityₗ : {T : Set} → (T → T → T) → T → Set
Identityₗ {T} (_▫_) id = {x : T} → (id ▫ x) ≡ x

Identityᵣ : {T : Set} → (T → T → T) → T → Set
Identityᵣ {T} (_▫_) id = {x : T} → (x ▫ id) ≡ x

Inverseₗ : {T : Set} → (T → T → T) → T → (T → T) → Set
Inverseₗ {T} (_▫_) id inv = {x : T} → ((inv x) ▫ x) ≡ id

Inverseᵣ : {T : Set} → (T → T → T) → T → (T → T) → Set
Inverseᵣ {T} (_▫_) id inv = {x : T} → (x ▫ (inv x)) ≡ id
