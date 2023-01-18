{-# OPTIONS --guardedness #-}

import      Lvl
open import Operator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type

module Formalization.RegularExpression.Language {ℓ} (Σ : Type{ℓ}) ⦃ equiv-dec : EquivDecidable(Σ) ⦄ where

open import Data.List as List using (List)
import      Data.List.Functions as List
import      Data.List.Relation.Quantification as List
open import Data.Tuple using (_,_)
open import FormalLanguage2
import      FormalLanguage2.Oper as Lang
open import FormalLanguage2.Proofs
open import Formalization.RegularExpression(Σ)
open import Formalization.RegularExpression.Relations(Σ)
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.IntroInstances
open import Relator.Equals
open import Structure.Relator
open import Structure.Set.Operators hiding (_∪_ ; _∩_ ; ∁ ; ∅ ; 𝐔)

language : RegExp → Language(Σ)
language ∅       = Lang.∅
language ε       = Lang.ε
language (• x)   = Lang.symbol ⦃ equiv-dec = equiv-dec ⦄ x
language (x · y) = language(x) Lang.𝁼 language(y)
language (x + y) = language(x) Lang.∪ language(y)
language (x *)   = language(x) Lang.*

matches-language : ∀{e}{l} → (e matches l) → (l Lang.∈ language(e))
matches-language empty-word                             = [↔]-to-[←] ([ε]-set {Σ = Σ}) [≡]-intro
matches-language (literal{a = a})                       = [↔]-to-[←] (symbol-set ⦃ equiv-dec ⦄ {c = a}) [≡]-intro
matches-language (concatenation {l₁ = l₁}{l₂ = l₂} p q) = [↔]-to-[←] [𝁼]-membership ([∃]-intro (l₁ , l₂) ⦃ [∧]-intro [≡]-intro ([∧]-intro (matches-language p) (matches-language q)) ⦄)
matches-language (disjunctionₗ{l = l} p)                = [↔]-to-[←] ([∪]-membership {x = l}) ([∨]-introₗ (matches-language p))
matches-language (disjunctionᵣ{l = l} p)                = [↔]-to-[←] ([∪]-membership {x = l}) ([∨]-introᵣ (matches-language p))
matches-language (iteration₀{r})                        = [*]-setₗ {L = language r} {ws = List.∅} List.∅
matches-language (iteration₊{r}{l₁}{l₂} p q)
  with [∃]-intro rest ⦃ [∧]-intro [≡]-intro pp ⦄ ← [↔]-to-[→] ([*]-set {w = l₂}) (matches-language q)
  = [*]-setₗ {ws = l₁ List.⊰ rest} (matches-language p List.⊰ pp)

language-matches : ∀{e}{l} → (l Lang.∈ language(e)) → (e matches l)
language-matches-all : ∀{e}{ls} → List.AllElements(Lang._∈ language(e)) ls → ((e *) matches List.concat(ls))

language-matches-all {e} {List.∅} List.∅ = iteration₀
language-matches-all {e} {l List.⊰ ls} (elem List.⊰ all) = iteration₊ (language-matches {e}{l} elem) (language-matches-all {e}{ls} all)

language-matches {∅} {l} p
  with () ← [∅]-membership {x = l} p
language-matches {ε} {l} p
  with [≡]-intro ← [↔]-to-[→] ([ε]-set {Σ = Σ}{x = l}) p
  = empty-word
language-matches {• c} {l} p
  with [≡]-intro ← [↔]-to-[→] (symbol-set {Σ = Σ} ⦃ equiv-dec ⦄ {c = c} {w = l}) p
  = literal
language-matches {e₁ · e₂} {l} p
  with [∃]-intro (w₁ , w₂) ⦃ [∧]-intro [≡]-intro ([∧]-intro p₁ p₂) ⦄ ← [↔]-to-[→] ([𝁼]-membership {A = language e₁}{B = language e₂}{x = l}) p
  = concatenation (language-matches {e₁}{w₁} p₁) (language-matches {e₂}{w₂} p₂)
language-matches {e₁ + e₂} {l} p = [∨]-elim
  (\p₁ → disjunctionₗ(language-matches {e₁}{l} p₁))
  (\p₂ → disjunctionᵣ(language-matches {e₂}{l} p₂))
  ([↔]-to-[→] ([∪]-membership {x = l}) p)
language-matches {e *} {List.∅}     p = iteration₀
language-matches {e *} l@{_ List.⊰ _} p
  with [∃]-intro (w List.⊰ ws) ⦃ [∧]-intro eq (mem List.⊰ all) ⦄ ← [↔]-to-[→] ([*]-set {w = l}) p
  = substitute₂-₂ᵣ(_matches_)(e *) eq (iteration₊ (language-matches{e}{w} mem) (language-matches-all all))
