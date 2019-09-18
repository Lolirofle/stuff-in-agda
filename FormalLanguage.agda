module FormalLanguage where

import      Lvl
open import Data.List renaming (∅ to []) hiding (filter)
open import Lang.Size
open import Data.Boolean
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Functional
open import Relator.Equals

-- Definitions:
--   A language is a set of words.
--   A word in a language is a list of valid symbols in the language.
--   A valid symbol in the language is an element in the alphabet of the language.
--   An alphabet of a language is a set.
--   A string is a word.
-- Standard conventions for variable naming in languages:
--   L is a language
--   Σ is an alphabet

Alphabet = Set
Word     = List

-- Language is defined as follows (LHS is using the definition of Language, RHS is using the usual "semantics" of languages as sets):
--   For a language L
--   accepts-ε:
--     (accepts-ε(L) = 𝑇) ↔ (ε∈L)
--     accepts-ε(L) returns a boolean determining whether the empty word is accepted the language.
--   suffix-lang:
--     ∀word∀c. (word ∈ suffix-lang(L)(c)) ↔ (c𝁼word ∈ L)
--     suffix-lang(L)(c) returns the language of the rest of the words when a word is starting with c in L.
-- Copied (with modifications) from: http://agda.readthedocs.io/en/v2.5.2/language/sized-types.html (2017-05-13)
-- which links the following paper: "Formal Languages, Formally and Coinductively, Dmitriy Traytel, FSCD (2016)" [https://www21.in.tum.de/~traytel/papers/fscd16-coind_lang/paper.pdf]
record Language (Σ : Alphabet) {s₁ : Size} : Set where
  constructor intro
  coinductive
  field
    accepts-ε : Bool
    suffix-lang : ∀{s₂ : Size< s₁} → Σ → Language(Σ){s₂}

module Oper {Σ} where
  infixl 1003 _∪_
  infixl 1002 _∩_
  infixl 1001 _𝁼_
  infixl 1000 _*

  -- The empty language
  -- The language that does not include any word at all.
  ∅ : ∀{s} → Language(Σ){s}
  Language.accepts-ε   ∅ = 𝐹
  Language.suffix-lang ∅ = const(∅)

  -- The empty word language
  -- The language with only the empty word.
  ε : ∀{s} → Language(Σ){s}
  Language.accepts-ε   ε = 𝑇
  Language.suffix-lang ε = const(∅)

  -- The single symbol language
  -- The language consisting of a single word with a single letter
  -- TODO: This is only possible when Alphabet has a computably decidable equality relation
  -- single : ∀{s} → Alphabet → Language(Σ){s}
  -- Language.accepts-ε   (single _)   = 𝐹
  -- Language.suffix-lang (single a) c = if (a ≡? c) then ε else ∅

  -- The filtered language
  filter : ∀{s} → (Σ → Bool) → Language(Σ){s}
  Language.accepts-ε   (filter f) = 𝐹
  Language.suffix-lang (filter f) c = if f(c) then (filter f) else ∅

  -- Union
  -- The language that includes any words that the two languages have.
  _∪_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ ∪ L₂)   = Language.accepts-ε(L₁) || Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∪ L₂) c = Language.suffix-lang(L₁)(c) ∪ Language.suffix-lang(L₂)(c)

  -- Intersection
  -- The language that only includes the words that both languages have in common.
  _∩_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ ∩ L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∩ L₂) c = Language.suffix-lang(L₁)(c) ∩ Language.suffix-lang(L₂)(c)

  -- Concatenation
  -- The language that includes words that start with a word the first language and end in a word from the second language.
  _𝁼_ : ∀{s} → Language(Σ){s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L₁ 𝁼 L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ 𝁼 L₂) c =
    if  Language.accepts-ε(L₁)
    then((Language.suffix-lang(L₁)(c) 𝁼 L₂) ∪ Language.suffix-lang(L₂)(c))
    else(Language.suffix-lang(L₁)(c) 𝁼 L₂)

  -- Star/Closure
  -- The language that includes words in any number of concatenations with itself.
  _* : ∀{s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (L *)   = 𝑇
  Language.suffix-lang (L *) c = Language.suffix-lang(L)(c) 𝁼 (L *)

  -- Complement
  -- The language that includes all words that a language does not have.
  -- TODO: Is this correct?
  ∁_ : ∀{s} → Language(Σ){s} → Language(Σ){s}
  Language.accepts-ε   (∁ L)   = !(Language.accepts-ε(L))
  Language.suffix-lang (∁ L) c = ∁(Language.suffix-lang(L)(c))

  -- All
  -- The language that includes all words in any combination of the alphabet.
  -- The largest language (with most words) with a certain alphabet.
  Σ* : ∀{s} → Language(Σ){s}
  Language.accepts-ε   (Σ*) = 𝑇
  Language.suffix-lang (Σ*) = const(Σ*)

  -- Containment check
  -- Checks whether a word is in the language.
  _∈?_ : Word(Σ) → Language(Σ) → Bool
  _∈?_ []      (L) = Language.accepts-ε(L)
  _∈?_ (c ⊰ w) (L) = w ∈? (Language.suffix-lang(L)(c))

  -- Containment
  -- The relation of whether a word is in the language or not.
  _∈_ : Word(Σ) → Language(Σ) → Set
  _∈_ a b = IsTrue(a ∈? b)

  -- Uncontainment
  -- The relation of whether a word is not in the language or not.
  _∉_ : Word(Σ) → Language(Σ) → Set
  _∉_ a b = IsFalse(a ∈? b)

  -- The language of length 1 words that only accepts some symbols of its alphabet
  alphabet-filter : ∀{s} → (Σ → Bool) → Language(Σ){s}
  Language.accepts-ε   (alphabet-filter f) = 𝐹
  Language.suffix-lang (alphabet-filter f) = (c ↦ if f(c) then ε else ∅)
