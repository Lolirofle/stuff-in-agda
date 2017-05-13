module List.Theorems {l₁} {l₂} where

import Level as Lvl
open import Functional
open import List
open import List.Properties
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Relator.Equals{l₁}{l₂}
open import Type{l₁}

-- Statement of whether a list is contained in the beginning of another list
module OrderedContainment {T} where
  data _contains-in-order_ : List{l₁}(T) → List{l₁}(T) → Stmt where
    empty : (∅ contains-in-order ∅)
    use   : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order (x ⊰ L₂))
    skip  : ∀{x}{L₁ L₂} → (L₁ contains-in-order L₂) → ((x ⊰ L₁) contains-in-order L₂)

  self : ∀{L : List{l₁}(T)} → (L contains-in-order L)
  self {∅}     = empty
  self {a ⊰ L} = use(self{L})

  emptyᵣ : ∀{L : List{l₁}(T)} → (L contains-in-order ∅)
  emptyᵣ {∅}     = empty
  emptyᵣ {a ⊰ L} = skip(emptyᵣ{L})

  concatᵣ : ∀{L₁ L₂ : List{l₁}(T)} → ((L₁ ++ L₂) contains-in-order L₂)
  concatᵣ {∅}{∅} = empty
  concatᵣ {∅}{L₂} = self
  -- concatᵣ {L₁}{∅} = emptyᵣ -- Either this line or the first seems to be redundant
  concatᵣ {a₁ ⊰ L₁}{L₂} = skip{a₁}(concatᵣ{L₁}{L₂})
open OrderedContainment using (_contains-in-order_) public
