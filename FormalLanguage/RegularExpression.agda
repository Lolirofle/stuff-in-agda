import      Lvl
open import Type

module FormalLanguage.RegularExpression {ℓ} (Σ : Type{ℓ}) where

open import Data.Boolean
open import Data.List as List using (List)
open import Logic
open import Numeral.Natural

data RegExp : Type{ℓ} where
  ∅ : RegExp
  ε : RegExp
  • : Σ → RegExp
  _++_ : RegExp → RegExp → RegExp
  _‖_ : RegExp → RegExp → RegExp
  _* : RegExp → RegExp

_+ : RegExp → RegExp
e + = e ++ (e *)

_?? : RegExp → RegExp
e ?? = ε ‖ e

exactly : ℕ → RegExp → RegExp
exactly 𝟎      e = ε
exactly (𝐒(n)) e = e ++ (exactly n e)

at-least : ℕ → RegExp → RegExp
at-least 𝟎      e = e *
at-least (𝐒(n)) e = e ++ (at-least n e)

at-most : ℕ → RegExp → RegExp
at-most 𝟎      e = ε
at-most (𝐒(n)) e = ε ‖ (e ++ (at-most n e))

data _matches_ : RegExp → List(Σ) → Stmt{ℓ} where
  empty-word : ∅ matches List.∅
  concatenation : ∀{r₁ r₂}{l₁ l₂} → (r₁ matches l₁) → (r₂ matches l₂) → ((r₁ ++ r₂) matches (l₁ List.++ l₂))
  disjunctionₗ : ∀{rₗ rᵣ}{l} → (rₗ matches l) → ((rₗ ‖ rᵣ) matches l)
  disjunctionᵣ : ∀{rₗ rᵣ}{l} → (rᵣ matches l) → ((rₗ ‖ rᵣ) matches l)
  iteration : ∀{r}{l₁ l₂} → (r matches l₁) → ((r *) matches l₂) → ((r *) matches (l₁ List.++ l₂))
  literal : ∀{a} → ((• a) matches List.singleton(a))
