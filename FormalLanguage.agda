{-# OPTIONS --sized-types #-}

module FormalLanguage {ℓ} where

import      Lvl
open import Sized.Data.List renaming (∅ to [])
open import Lang.Size
open import Logic.Computability.Binary
open import Data.Boolean
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Functional
open import Relator.Equals
open import Type

-- Definitions:
--   A language is a set of words.
--   A word in a language is a list of valid symbols in the language.
--   A valid symbol in the language is an element in the alphabet of the language.
--   An alphabet of a language is a set.
--   A string is a word.
-- Standard conventions for variable naming in languages:
--   L is a language
--   Σ is an alphabet

Alphabet = Type{ℓ}
Word     = List

-- Language is defined as a trie: (LHS is using the definition of Language, RHS is using the usual "semantics" of languages as sets):
--   For a language L
--   accepts-ε:
--     (accepts-ε(L) = 𝑇) ↔ (ε ∈ L)
--     accepts-ε(L) returns a boolean determining whether the empty word is accepted in the language.
--   suffix-lang:
--     ∀word∀c. (word ∈ suffix-lang(L)(c)) ↔ ((c 𝁼 word) ∈ L)
--     suffix-lang(L)(c) is the language that consists of the rest of the words when a word is starting with c in L.
-- Copied (with modifications) from: http://agda.readthedocs.io/en/v2.5.2/language/sized-types.html (2017-05-13)
-- which links the following paper: "Formal Languages, Formally and Coinductively, Dmitriy Traytel, FSCD (2016)" [https://www21.in.tum.de/~traytel/papers/fscd16-coind_lang/paper.pdf]
-- Example:
--   A language 𝔏 consists of 6 words:
--   𝔏 = {"" , "aa" , "aaa" , "aab" , "aba" , "aaab"}
--   accepts-ε  (𝔏)    = 𝑇
--   suffix-lang(𝔏)(a) = {"a" , "aa" , "ab" , "ba" , "aab"}
--   accepts-ε  (suffix-lang(𝔏)(a))    = 𝐹
--   suffix-lang(suffix-lang(𝔏)(a))(a) = {"" , "a" , "b" , "ab"}
--   suffix-lang(suffix-lang(𝔏)(a))(b) = {"a"}
record Language (Σ : Alphabet) {s : Size} : Type{ℓ} where
  constructor intro
  coinductive
  field
    accepts-ε : Bool
    suffix-lang : ∀{sₛ : <ˢⁱᶻᵉ s} → Σ → Language(Σ){sₛ}

module Oper {Σ} where
  infixl 1003 _∪_
  infixl 1002 _∩_
  infixl 1001 _𝁼_
  infixl 1000 _*

  -- The empty language.
  -- The language that does not include any word at all.
  ∅ : ∀{s} → Language(Σ){s}
  Language.accepts-ε   ∅   = 𝐹
  Language.suffix-lang ∅ _ = ∅

  -- The empty word language.
  -- The language with only the empty word.
  ε : ∀{s} → Language(Σ){s}
  Language.accepts-ε   ε   = 𝑇
  Language.suffix-lang ε _ = ∅

  -- The language of length 1 words that only accepts some symbols of its alphabet
  alphabet-filter : ∀{s} → (Σ → Bool) → Language(Σ){s}
  Language.accepts-ε   (alphabet-filter f)   = 𝐹
  Language.suffix-lang (alphabet-filter f) c = if f(c) then ε else ∅

  -- The single symbol language.
  -- The language consisting of a single word with a single letter
  -- Note: This is only possible when Alphabet has a computably decidable equality relation
  single : ⦃ _ : ComputablyDecidable(_≡_) ⦄ → ∀{s} → Σ → Language(Σ){s}
  single(a) = alphabet-filter(ComputablyDecidable.decide(_≡_) a)

  -- The sublanguage filtered by a decidable predicate.
  filter : ∀{s} → (Word(Σ) → Bool) → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (filter P(𝔏))   = P(List.∅)
  Language.suffix-lang (filter P(𝔏)) c = filter (P ∘ tail) (Language.suffix-lang(𝔏)(c))

  -- The language where every letter in the alphabet is applied to a function.
  unmap : ∀{Σ₂}{s} → (Σ → Σ₂) → Language(Σ₂){s} → Language(Σ){s}
  Language.accepts-ε   (unmap f(𝔏))   = Language.accepts-ε (𝔏)
  Language.suffix-lang (unmap f(𝔏)) c = unmap f(Language.suffix-lang(𝔏)(f(c)))

  -- Union.
  -- The language that includes any words that the two languages have.
  _∪_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ ∪ L₂)   = Language.accepts-ε(L₁) || Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∪ L₂) c = Language.suffix-lang(L₁)(c) ∪ Language.suffix-lang(L₂)(c)

  -- Intersection.
  -- The language that only includes the words that both languages have in common.
  _∩_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ ∩ L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∩ L₂) c = Language.suffix-lang(L₁)(c) ∩ Language.suffix-lang(L₂)(c)

  -- Concatenation.
  -- The language that includes words that start with a word the first language and end in a word from the second language.
  _𝁼_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ 𝁼 L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ 𝁼 L₂) c =
    if   Language.accepts-ε(L₁)
    then (Language.suffix-lang(L₁)(c) 𝁼 L₂) ∪ Language.suffix-lang(L₂)(c)
    else (Language.suffix-lang(L₁)(c) 𝁼 L₂)

  -- Star/Closure
  -- The language that includes words in any number of concatenations with itself.
  _* : ∀{s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L *)   = 𝑇
  Language.suffix-lang (L *) c = Language.suffix-lang(L)(c) 𝁼 (L *)

  -- Complement
  -- The language that includes all words that a language does not have.
  ∁_ : ∀{s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (∁ L)   = !(Language.accepts-ε(L))
  Language.suffix-lang (∁ L) c = ∁(Language.suffix-lang(L)(c))

  -- The universal language.
  -- The language that includes all words in any combination of the alphabet.
  -- The largest language (with most words) with a certain alphabet.
  𝐔 : ∀{s} → Language(Σ){s}
  𝐔 = ∁(∅)

  -- Containment check
  -- Checks whether a word is in the language.
  _∈?_ : ∀{s} → Word{s = s}(Σ) → Language(Σ) → Bool
  _∈?_ []             L = Language.accepts-ε(L)
  _∈?_ (_⊰_ {sₗ} c w) L = _∈?_ {s = sₗ} w (Language.suffix-lang L c)

  -- Containment
  -- The relation of whether a word is in the language or not.
  _∈_ : ∀{s} → Word{s = s}(Σ) → Language(Σ) → Type
  _∈_ {s} a b = IsTrue(_∈?_ {s} a b)

  [_]_∈_ : ∀(s) → Word{s = s}(Σ) → Language(Σ) → Type
  [ s ] a ∈ b = _∈_ {s} a b

  -- Uncontainment
  -- The relation of whether a word is not in the language or not.
  _∉_ : ∀{s} → Word{s = s}(Σ) → Language(Σ) → Type
  _∉_ {s} a b = IsFalse(_∈?_ {s} a b)

  [_]_∉_ : ∀(s) → Word{s = s}(Σ) → Language(Σ) → Type
  [ s ] a ∉ b = _∉_ {s} a b
