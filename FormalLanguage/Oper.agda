{-# OPTIONS --sized-types #-}

module FormalLanguage.Oper where

import      Lvl
open import Sized.Data.List renaming (∅ to [])
open import Lang.Size
open import Data.Boolean
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming hiding (_==_)
open import Data.Boolean.Stmt
open import FormalLanguage
open import Functional
open import Operator.Equals
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type

private variable ℓ : Lvl.Level
private variable Σ Σ₁ Σ₂ : Type{ℓ}
private variable s s₁ s₂ sₗ : Size

infixl 1003 _∪_
infixl 1002 _∩_
infixl 1001 _𝁼_
infixl 1000 _*

-- The empty language.
-- The language that does not include any word at all.
∅ : Language(Σ){s}
Language.accepts-ε ∅   = 𝐹
Language.suffix    ∅ _ = ∅

-- The empty word language.
-- The language with only the empty word.
ε : Language(Σ){s}
Language.accepts-ε ε   = 𝑇
Language.suffix    ε _ = ∅

-- The language of length 1 words that only accepts some symbols of its alphabet
alphabet-filter : (Σ → Bool) → Language(Σ){s}
Language.accepts-ε (alphabet-filter f)   = 𝐹
Language.suffix    (alphabet-filter f) c = if f(c) then ε else ∅

-- The single symbol language.
-- The language consisting of a single word with a single letter
-- Note: This is only possible when Alphabet has a computably decidable equality relation
single : ⦃ _ : EquivDecidable(Σ) ⦃ [≡]-equiv ⦄ ⦄ → Σ → Language(Σ){s}
single(a) = alphabet-filter(_==_ a)

-- The sublanguage filtered by a decidable predicate.
filter : ∀{sₛ : <ˢⁱᶻᵉ s} → (Word Σ sₗ → Bool) → Language(Σ){s} → Language(Σ){sₛ}
Language.accepts-ε (filter P(𝔏))   = P(List.∅)
Language.suffix    (filter P(𝔏)) c = filter (P ∘ tail) (Language.suffix(𝔏)(c))

-- The language where every letter in the alphabet is applied to a function.
unmap : ∀{sₛ : <ˢⁱᶻᵉ s} → (Σ₁ → Σ₂) → Language(Σ₂){s} → Language(Σ₁){sₛ}
Language.accepts-ε (unmap f(𝔏))   = Language.accepts-ε (𝔏)
Language.suffix    (unmap f(𝔏)) c = unmap f(Language.suffix(𝔏)(f(c)))

-- Union.
-- The language that includes any words that the two languages have.
_∪_ : Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (L₁ ∪ L₂)   = Language.accepts-ε(L₁) || Language.accepts-ε(L₂)
Language.suffix    (L₁ ∪ L₂) c = Language.suffix(L₁)(c) ∪ Language.suffix(L₂)(c)

-- Intersection.
-- The language that only includes the words that both languages have in common.
_∩_ : Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (L₁ ∩ L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
Language.suffix    (L₁ ∩ L₂) c = Language.suffix(L₁)(c) ∩ Language.suffix(L₂)(c)

-- Concatenation.
-- The language that includes words that start with a word the first language and end in a word from the second language.
_𝁼_ : Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (L₁ 𝁼 L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
Language.suffix    (L₁ 𝁼 L₂) c =
  if   Language.accepts-ε(L₁)
  then (Language.suffix(L₁)(c) 𝁼 L₂) ∪ Language.suffix(L₂)(c)
  else (Language.suffix(L₁)(c) 𝁼 L₂)

-- Star/Closure
-- The language that includes words in any number of concatenations with itself.
_* : Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (L *)   = 𝑇
Language.suffix    (L *) c = Language.suffix(L)(c) 𝁼 (L *)

-- Non-empty closure
-- The language that includes words in at least one concatenation with itself.
_+ : Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (L +)   = 𝐹
Language.suffix    (L +) c = Language.suffix(L)(c) 𝁼 (L +)

-- Complement
-- The language that includes all words that a language does not have.
∁_ : Language(Σ){s} → Language(Σ){s}
Language.accepts-ε (∁ L)   = !(Language.accepts-ε(L))
Language.suffix    (∁ L) c = ∁(Language.suffix(L)(c))

-- The universal language.
-- The language that includes all words in any combination of the alphabet.
-- The largest language (with most words) with a certain alphabet.
𝐔 : Language(Σ){s}
𝐔 = ∁(∅)

-- Containment check
-- Checks whether a word is in the language.
_∈?_ : Word Σ s → Language(Σ) → Bool
_∈?_ []             L = Language.accepts-ε(L)
_∈?_ (_⊰_ {sₗ} c w) L = _∈?_ {s = sₗ} w (Language.suffix L c)

-- Containment
-- The relation of whether a word is in the language or not.
_∈_ : Word Σ s → Language(Σ) → Type
_∈_ {s} a b = IsTrue(_∈?_ {s} a b)

[_]_∈_ : ∀(s) → Word Σ s → Language(Σ) → Type
[ s ] a ∈ b = a ∈ b

-- Uncontainment
-- The relation of whether a word is not in the language or not.
_∉_ : Word Σ s → Language(Σ) → Type
_∉_ {s} a b = IsFalse(_∈?_ {s} a b)

[_]_∉_ : ∀(s) → Word Σ s → Language(Σ) → Type
[ s ] a ∉ b = a ∉ b
