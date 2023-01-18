import      Lvl
open import Type

module Formalization.RegularExpression.Relations {ℓ} (Σ : Type{ℓ}) where

open import Data.List as List using (List)
import      Data.List.Functions as List
open import Formalization.RegularExpression(Σ)
open import Logic.Propositional
open import Relator.Equals

-- Relation for whether a pattern/expression matches a word (whether the word is in the language that the pattern/expression describes).
-- Note: One interpretation of this relation is that this is similar to set membership with RegExp being sets and List(Σ) elements.
data _matches_ : RegExp → List(Σ) → Type{ℓ} where
  empty-word : ε matches List.∅
  literal : ∀{a} → ((• a) matches List.singleton(a))
  concatenation : ∀{r₁ r₂}{l₁ l₂} → (r₁ matches l₁) → (r₂ matches l₂) → ((r₁ · r₂) matches (l₁ List.++ l₂))
  disjunctionₗ : ∀{rₗ rᵣ}{l} → (rₗ matches l) → ((rₗ + rᵣ) matches l)
  disjunctionᵣ : ∀{rₗ rᵣ}{l} → (rᵣ matches l) → ((rₗ + rᵣ) matches l)
  iteration₀ : ∀{r} → ((r *) matches List.∅)
  iteration₊ : ∀{r}{l₁ l₂} → (r matches l₁) → ((r *) matches l₂) → ((r *) matches (l₁ List.++ l₂))

-- optional-empty : ∀{e} → ((e ??) matches List.∅)
pattern optional-empty = disjunctionₗ empty-word

∅-match : ∀{l} → ¬(∅ matches l)
∅-match ()

[??]-match : ∀{e}{l} → ((l ≡ List.∅) ∨ (e matches l)) ↔ ((e ??) matches l)
[??]-match = [↔]-intro
  (\{(disjunctionₗ empty-word) → [∨]-introₗ [≡]-intro ; (disjunctionᵣ m) → [∨]-introᵣ m})
  ([∨]-elim (\{[≡]-intro → disjunctionₗ empty-word}) disjunctionᵣ)

_≡ᵣ_ : RegExp → RegExp → Type
x ≡ᵣ y = ∀{l} → (x matches l) ↔ (y matches l)

-- TODO: Structure.Set for _matches_
