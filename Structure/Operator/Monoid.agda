module Structure.Operator.Monoid where

import      Lvl
open import Logic
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Operator.Properties hiding (associativity ; identityₗ ; identityᵣ)
open import Type

-- A type and a binary operator using this type is a monoid when:
-- • The operator is associative.
-- • The operator have an identity in both directions.
record Monoid {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ} where
  field
    instance ⦃ closed ⦄         : BinaryOperator(_▫_)
    instance ⦃ associativity ⦄  : Associativity(_▫_)
    instance ⦃ identity ⦄       : ∃(Identity(_▫_))

  id = [∃]-witness identity

  identityₗ : Identityₗ (_▫_) id
  identityₗ = Identity.left([∃]-proof identity)

  identityᵣ : Identityᵣ (_▫_) id
  identityᵣ = Identity.right([∃]-proof identity)

record Homomorphism {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  field
    instance ⦃ structureₗ ⦄ : Monoid(_▫X_)
    instance ⦃ structureᵣ ⦄ : Monoid(_▫Y_)

  idₗ = Monoid.id(structureₗ)
  idᵣ = Monoid.id(structureᵣ)

  field
    preserve-op : ∀{x y : X} → (f(x ▫X y) ≡ f(x) ▫Y f(y))
    preserve-id : (f(idₗ) ≡ idᵣ)

  -- TODO: When f is a function and a homomorphism and only _▫X_ is a monoid, is it enough to prove that RHS is a monoid?
  -- structureᵣ : ⦃ _ : Function(f) ⦄ → Monoid(_▫Y_)
  -- Identityₗ.proof(Monoid.identityₗ(structureᵣ)) = function(f) (Identityₗ.proof(Monoid.identityₗ(structureₗ)))
