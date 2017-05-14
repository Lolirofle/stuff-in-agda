module FormalLanguage.Language where

import      Level as Lvl
open import List renaming (∅ to [])
open import Agda.Builtin.Size
open import Boolean
open import Boolean.Operators
open        Boolean.Operators.Programming
open import Functional
open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

-- Definitions:
--   A language is a set of words.
--   A word in a language is a list of valid symbols in the language.
--   A valid symbol in the language is an element in the alphabet of the language.
--   An alphabet of a language is a set.
--   A string is a word.
-- Standard conventions for variable naming in languages:
--   L is a language
--   ∑ is an alphabet

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
record Language (∑ : Alphabet) {s₁ : Size} : Set where
  coinductive
  field
    accepts-ε : Bool
    suffix-lang : ∀{s₂ : Size< s₁} → ∑ → Language(∑){s₂}

module Oper {∑} where
  infixl 1003 _∪_
  infixl 1002 _∩_
  infixl 1001 _𝁼_
  infixl 1000 _*

  -- The empty language
  -- The language that does not include any word at all.
  ∅ : ∀{s} → Language(∑){s}
  Language.accepts-ε   ∅ = 𝐹
  Language.suffix-lang ∅ = const(∅)

  -- The empty word language
  -- The language with only the empty word.
  ε : ∀{s} → Language(∑){s}
  Language.accepts-ε   ε = 𝑇
  Language.suffix-lang ε = const(∅)

  -- Union
  -- The language that includes any words that the two languages have.
  _∪_ : ∀{s} → Language(∑){s} → Language(∑){s} → Language(∑){s}
  Language.accepts-ε   (L₁ ∪ L₂) = Language.accepts-ε(L₁) || Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∪ L₂) = (c ↦ Language.suffix-lang(L₁)(c) ∪ Language.suffix-lang(L₂)(c))

  -- Intersection
  -- The language that only includes the words that both languages have in common.
  _∩_ : ∀{s} → Language(∑){s} → Language(∑){s} → Language(∑){s}
  Language.accepts-ε   (L₁ ∩ L₂) = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ ∩ L₂) = (c ↦ Language.suffix-lang(L₁)(c) ∩ Language.suffix-lang(L₂)(c))

  -- Concatenation
  -- The language that includes words that start with the first language and end in the second language.
  _𝁼_ : ∀{s} → Language(∑){s} → Language(∑){s} → Language(∑){s}
  Language.accepts-ε   (L₁ 𝁼 L₂) = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
  Language.suffix-lang (L₁ 𝁼 L₂) =
    (c ↦
      if  Language.accepts-ε(L₁)
      then((Language.suffix-lang(L₁)(c) 𝁼 L₂) ∪ Language.suffix-lang(L₂)(c))
      else(Language.suffix-lang(L₁)(c) 𝁼 L₂)
    )

  -- Star/Closure
  -- The language that includes words in any number of concatenations with itself.
  _* : ∀{s} → Language(∑){s} → Language(∑){s}
  Language.accepts-ε   (L *) = 𝑇
  Language.suffix-lang (L *) =
    (c ↦
      Language.suffix-lang(L)(c) 𝁼 (L *)
    )

  -- TODO: How to define the complement?

  -- All
  -- The language that includes all words in any combination of the alphabet.
  -- The largest language (with most words) with a certain alphabet.
  ∑* : ∀{s} → Language(∑){s}
  Language.accepts-ε   (∑*) = 𝑇
  Language.suffix-lang (∑*) = const(∑*)

  -- Containment check
  -- Checks whether a word is in the language.
  _is-in_ : Word(∑) → Language(∑){ω} → Bool
  _is-in_ ([])    (L) = Language.accepts-ε(L)
  _is-in_ (c ⊰ w) (L) = w is-in (Language.suffix-lang(L)(c))

  -- Containment
  -- The relation of whether a word is in the language or not.
  _∈_ : Word(∑) → Language(∑){ω} → Set
  _∈_ a b = (a is-in b) ≡ 𝑇

  -- The language of length 1 words that only accepts some symbols of its alphabet
  alphabet-filter : ∀{s} → (∑ → Bool) → Language(∑){s}
  Language.accepts-ε   (alphabet-filter f) = 𝐹
  Language.suffix-lang (alphabet-filter f) = (c ↦ if f(c) then (ε) else (∅))

module TestOnOffSwitch where
  data ∑ : Alphabet where
    Push : ∑

module TestVendingMachine where
  data ∑ : Alphabet where
    OutputTea    : ∑
    OutputCoffee : ∑
    Input5kr     : ∑
    Input10kr    : ∑
