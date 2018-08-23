module Structure.Operator.Proofs{ℓ₁}{ℓ₂} where

import Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Relator.Equals.Uniqueness{ℓ₁}{ℓ₂}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}

-- When an identity element exists and is the same for both sides, it is unique.
unique-identity : ∀{T}{_▫_ : T → T → T} → Unique(Identity(_▫_))
unique-identity{T}{_▫_} {x₁}{x₂} ([∧]-intro identityₗ₁ identityᵣ₁) ([∧]-intro identityₗ₂ identityᵣ₂) =
  symmetry(identityₗ₂{x₁})
  🝖 identityᵣ₁{x₂}

unique-identityₗ-by-commutativity : ∀{T}{_▫_ : T → T → T} → Commutativity(_▫_) → Unique(Identityₗ(_▫_))
unique-identityₗ-by-commutativity{T}{_▫_} (commutativity) {x₁}{x₂} (identity₁) (identity₂) =
  symmetry(identity₂{x₁})
  🝖 commutativity{x₂}{x₁}
  🝖 identity₁{x₂}

unique-identityₗ-by-cancellation : ∀{T}{_▫_ : T → T → T} → Cancellationᵣ(_▫_) → Unique(Identityₗ(_▫_))
unique-identityₗ-by-cancellation{T}{_▫_} (cancellation) {x₁}{x₂} (identity₁) (identity₂) =
  cancellation {x₁}{x₁}{x₂} (identity₁{x₁} 🝖 symmetry(identity₂{x₁}))

cancellation-by-associativity-inverse : ∀{T}{_▫_ : T → T → T} → Associativity(_▫_) → ∀{id} → Identityₗ(_▫_)(id) → ∀{inv} → InverseFunctionₗ(_▫_)(id)(inv) → Cancellationₗ(_▫_)
cancellation-by-associativity-inverse{T}{_▫_} (associativity) {id} (identity) {inv} (inverse) {x}{a}{b} (xa≡xb) =
    symmetry(identity{a})
    🝖 [≡]-with(_▫ a) (symmetry(inverse{x}))
    🝖 associativity{inv(x)}{x}{a}
    🝖 [≡]-with(inv(x) ▫_) (xa≡xb)
    🝖 symmetry(associativity{inv(x)}{x}{b})
    🝖 [≡]-with(_▫ b) (inverse{x})
    🝖 identity{b}
    -- TODO: This pattern of applying symmetric transitivity rules, make it a function

-- unique-inverse : ∀{T}{_▫_ : T → T → T} → Associativity(_▫_) → ∀{id} → Identity(_▫_)(id) → Unique(InverseFunctionₗ(_▫_)(id))
