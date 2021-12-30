import      Lvl
open import Type

module FormalLanguage.RegularExpression {ℓ} (Σ : Type{ℓ}) where

open import Data.Boolean
open import Data.Boolean.Stmt.Logic
open import Data.List as List using (List)
open import FormalLanguage
open import FormalLanguage.Proofs
open import Functional
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Relator.Equals

data RegExp : Type{ℓ} where
  ∅ : RegExp     -- Empty language (Consisting of no words).
  ε : RegExp     -- Empty word language (Consisting of a single empty word).
  • : Σ → RegExp -- Singleton language (Consisting of a single one letter word).
  _++_ : RegExp → RegExp → RegExp -- Concatenation language (Consisting of the words concatenated pairwise).
  _‖_  : RegExp → RegExp → RegExp -- Union language (Consisting of the words in both languages).
  _*   : RegExp → RegExp          -- Infinite concatenations language (Consisting of the words concatenated with themselves any number of times).

-- Non-empty infinite concatenations language.
_+ : RegExp → RegExp
e + = e ++ (e *)

-- Optional expression language
_?? : RegExp → RegExp
e ?? = ε ‖ e

-- Finitely repeated expression language
exactly : ℕ → RegExp → RegExp
exactly 𝟎      e = ε
exactly (𝐒(n)) e = e ++ (exactly n e)

-- Minimum repetitions of an expression language
at-least : ℕ → RegExp → RegExp
at-least 𝟎      e = e *
at-least (𝐒(n)) e = e ++ (at-least n e)

-- Maximum repetitions of an expression language
at-most : ℕ → RegExp → RegExp
at-most 𝟎      e = ε
at-most (𝐒(n)) e = ε ‖ (e ++ (at-most n e))

-- Relation for whether a pattern/expression matches a word (whether the word is in the language that the pattern/expression describes).
data _matches_ : RegExp → List(Σ) → Stmt{ℓ} where
  empty-word : ε matches List.∅
  concatenation : ∀{r₁ r₂}{l₁ l₂} → (r₁ matches l₁) → (r₂ matches l₂) → ((r₁ ++ r₂) matches (l₁ List.++ l₂))
  disjunctionₗ : ∀{rₗ rᵣ}{l} → (rₗ matches l) → ((rₗ ‖ rᵣ) matches l)
  disjunctionᵣ : ∀{rₗ rᵣ}{l} → (rᵣ matches l) → ((rₗ ‖ rᵣ) matches l)
  iteration : ∀{r}{l₁ l₂} → (r matches l₁) → ((r *) matches l₂) → ((r *) matches (l₁ List.++ l₂))
  literal : ∀{a} → ((• a) matches List.singleton(a))

-- optional-empty : ∀{e} → ((e ??) matches List.∅)
pattern optional-empty = disjunctionₗ empty-word

optional-self : ∀{e}{l} → (e matches l) → ((e ??) matches l)
optional-self = disjunctionᵣ

empty-none : ∀{l} → ¬(∅ matches l)
empty-none ()

module _ ⦃ _ : ComputablyDecidable(_≡_) ⦄ where
  language : RegExp → Language(Σ)
  language ∅        = Oper.∅
  language ε        = Oper.ε
  language (• x)    = Oper.single x
  language (x ++ y) = language(x) Oper.𝁼 language(y)
  language (x ‖ y)  = language(x) Oper.∪ language(y)
  language (x *)    = language(x) Oper.*

  postulate matches-language : ∀{e}{l} → (e matches l) → (l Oper.∈ language(e))
  {-matches-language {ε} {List.∅} empty-word = [⊤]-intro
  matches-language {• a} {.a List.⊰ .List.∅} literal = {!!}
  matches-language {e₁ ++ e₂} {List.∅}     p = {!!}
  matches-language {e₁ ++ e₂} {x List.⊰ l} p = {!!}
  matches-language {e₁ ‖ e₂} {List.∅} (disjunctionₗ p) = IsTrue.[∨]-introₗ(matches-language {e₁} p)
  matches-language {e₁ ‖ e₂} {List.∅} (disjunctionᵣ p) = IsTrue.[∨]-introᵣ(matches-language {e₂} p)
    matches-language {e₁ ‖ e₂} {x List.⊰ l} (disjunctionₗ p) = [↔]-to-[←] ([∪]-containment {x = x List.⊰ l}{A = language(e₁)}{B = language(e₂)}) ([∨]-introₗ (matches-language {e₁} p))
    matches-language {e₁ ‖ e₂} {x List.⊰ l} (disjunctionᵣ p) = [↔]-to-[←] ([∪]-containment {x = x List.⊰ l}{A = language(e₁)}{B = language(e₂)}) ([∨]-introᵣ (matches-language {e₂} p))
  matches-language {e *} {List.∅}     p = {!!}
  matches-language {e *} {x List.⊰ l} p = {!!}
  -}

  postulate language-matches : ∀{e}{l} → (l Oper.∈ language(e)) → (e matches l)
  {-language-matches {∅}        {x List.⊰ l} p with () ← language-matches {∅} {l} p
  language-matches {ε}        {List.∅}     [⊤]-intro = empty-word
  language-matches {ε}        {x List.⊰ l} p with () ← [↔]-to-[→] ([ε]-containment {x = x List.⊰ l}) p
  language-matches {• a}      {x List.⊰ l} p with [≡]-intro ← [↔]-to-[→] (single-containment {x = x List.⊰ l}) p = literal
  language-matches {e₁ ++ e₂} {List.∅}     p = {!!}
  language-matches {e₁ ++ e₂} {x List.⊰ l} p = {!!}
  language-matches {e₁ ‖ e₂}  {l} p = [∨]-elim (disjunctionₗ ∘ language-matches) (disjunctionᵣ ∘ language-matches) ([↔]-to-[→] ([∪]-containment {x = l} {A = language(e₁)} {B = language(e₂)}) p)
  language-matches {e *}      {List.∅} [⊤]-intro = {![*]-containment!}
  language-matches {e *}      {x List.⊰ l} p = {!!}
  -}
