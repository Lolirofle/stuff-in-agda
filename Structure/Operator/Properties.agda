module Structure.Operator.Properties lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)

Commutativity : {T : Stmt} → (T → T → T) → Stmt
Commutativity {T} (_▫_) = {x y : T} → (x ▫ y) ≡ (y ▫ x)

Associativity : {T : Stmt} → (T → T → T) → Stmt
Associativity {T} (_▫_) = {x y z : T} → ((x ▫ y) ▫ z) ≡ ((x ▫ y) ▫ z)

Identityₗ : {T : Stmt} → (T → T → T) → T → Stmt
Identityₗ {T} (_▫_) id = {x : T} → (id ▫ x) ≡ x

Identityᵣ : {T : Stmt} → (T → T → T) → T → Stmt
Identityᵣ {T} (_▫_) id = {x : T} → (x ▫ id) ≡ x

Inverseₗ : {T : Stmt} → (T → T → T) → T → (T → T) → Stmt
Inverseₗ {T} (_▫_) id inv = {x : T} → ((inv x) ▫ x) ≡ id

Inverseᵣ : {T : Stmt} → (T → T → T) → T → (T → T) → Stmt
Inverseᵣ {T} (_▫_) id inv = {x : T} → (x ▫ (inv x)) ≡ id
