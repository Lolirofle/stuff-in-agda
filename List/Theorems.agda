module List.Theorems {ℓ₁} {ℓ₂} where

import Lvl
open import Functional
open import List
open import List.Properties
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}
open import Type

-- Statement of whether a list is contained in the beginning of another list (TODO: Move to List.Relation)
module Sublist {T} where
  data _⊑_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt where
    instance
      empty : (∅ ⊑ ∅)
      use   : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → ((x ⊰ L₁) ⊑ (x ⊰ L₂))
      skip  : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → ((x ⊰ L₁) ⊑ L₂)

  instance
    self : ∀{L} → (L ⊑ L)
    self {∅}     = empty
    self {a ⊰ L} = use(self{L})

  instance
    emptyᵣ : ∀{L} → (L ⊑ ∅)
    emptyᵣ {∅}     = empty
    emptyᵣ {a ⊰ L} = skip(emptyᵣ{L})

  instance
    [∈]-of-[++]ₗ : ∀{L₁ L₂} → ((L₁ ++ L₂) ⊑ L₂)
    [∈]-of-[++]ₗ {∅}{∅} = empty
    [∈]-of-[++]ₗ {∅}{L₂} = self
    -- [∈]-of-[++]ₗ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
    [∈]-of-[++]ₗ {a₁ ⊰ L₁}{L₂} = skip{a₁}([∈]-of-[++]ₗ{L₁}{L₂})

  constructₗ : ∀{L₁ L₂} → (L₁ ⊑ L₂) → List{ℓ₂}(T)
  constructₗ {L₁}{_} (_) = L₁

  constructᵣ : ∀{L₁ L₂} → (L₁ ⊑ L₂) → List{ℓ₂}(T)
  constructᵣ {_}{L₂} (_) = L₂

  postulate [++] : ∀{L₁ L₂} → (L₁ ⊑ L₂) ↔ (∃(pre ↦ ∃(post ↦ (pre ++ L₁ ++ post ≡ L₂))))
open Sublist using (_⊑_) public
