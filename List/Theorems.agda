module List.Theorems {ℓ₁} {ℓ₂} where

import Lvl
open import Functional
open import List
open import List.Properties
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁} renaming (_≡_ to _[≡]_ ; _≢_ to _[≢]_) hiding ([≡]-substitution ; [≡]-substitutionₗ ; [≡]-substitutionᵣ)
open import Type{ℓ₂}

-- Statement of whether a list is contained in the beginning of another list (TODO: Move to a separate file)
module OrderedContainment {T} where
  data _contains-in-order_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt where
    instance
      empty : (∅ contains-in-order ∅)
      use   : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order (x ⊰ L₂))
      skip  : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order L₂)

  instance
    self : ∀{L} → (L contains-in-order L)
    self {∅}     = empty
    self {a ⊰ L} = use(self{L})

  instance
    emptyᵣ : ∀{L} → (L contains-in-order ∅)
    emptyᵣ {∅}     = empty
    emptyᵣ {a ⊰ L} = skip(emptyᵣ{L})

  instance
    [∈]-of-[++]ₗ : ∀{L₁ L₂} → ((L₁ ++ L₂) contains-in-order L₂)
    [∈]-of-[++]ₗ {∅}{∅} = empty
    [∈]-of-[++]ₗ {∅}{L₂} = self
    -- [∈]-of-[++]ₗ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
    [∈]-of-[++]ₗ {a₁ ⊰ L₁}{L₂} = skip{a₁}([∈]-of-[++]ₗ{L₁}{L₂})

  constructₗ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{ℓ₂}(T)
  constructₗ {L₁}{_} (_) = L₁

  constructᵣ : ∀{L₁ L₂} → (L₁ contains-in-order L₂) → List{ℓ₂}(T)
  constructᵣ {_}{L₂} (_) = L₂
open OrderedContainment using (_contains-in-order_) public
