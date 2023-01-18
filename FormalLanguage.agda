{-# OPTIONS --sized-types #-}

module FormalLanguage where

open import Data.Boolean
open import Lang.Size
import      Lvl
open import Sized.Data.List renaming (∅ to [])
open import Type

private variable ℓ : Lvl.Level

-- Definitions:
-- Standard conventions for variable naming in languages:
--   L is a language
--   Σ is an alphabet

-- An alphabet is a set where the inhabitants (letters) are interpreted as the valid symbols for a language.
Alphabet = Type

-- A word using a certain alphabet is a list of symbols using this alphabet (also called a string).
Word = List

-- Language represents a formal language in a certain alphabet.
-- A formal language is semantically a set of words with a certain alphabet.
-- The representation used here is an infinite trie:
--   (Conventions below: LHS is the definition of Language, RHS is the usual semantics of formal languages as sets):
--   For a language L
--   accepts-ε:
--     (accepts-ε(L) = 𝑇) ↔ (ε ∈ L)
--     accepts-ε(L) decides whether the empty word is accepted in the language L.
--   suffix:
--     ∀word∀c. (word ∈ suffix(L)(c)) ↔ ((c 𝁼 word) ∈ L)
--     suffix(L)(c) is the language that consists of the words that is starting with c in the language L.
-- Source: Copied with modifications from: http://agda.readthedocs.io/en/v2.5.2/language/sized-types.html (2017-05-13) which references the following paper: "Formal Languages, Formally and Coinductively, Dmitriy Traytel, FSCD (2016)" [https://www21.in.tum.de/~traytel/papers/fscd16-coind_lang/paper.pdf]
-- Example:
--   A language 𝔏 consists of 6 words:
--   𝔏 = {"" , "aa" , "aaa" , "aab" , "aba" , "aaab"}
--   suffix(𝔏)(a) = {"a" , "aa" , "ab" , "ba" , "aab"}
--   suffix(suffix(𝔏)(a))(a) = {"" , "a" , "b" , "ab"}
--   suffix(suffix(suffix(𝔏)(a))(a))(a) = {"" , "b"}
--   suffix(suffix(suffix(suffix(𝔏)(a))(a))(a))(a) = {}
--   suffix(suffix(𝔏)(a))(b) = {"a"}
--   suffix(suffix(suffix(𝔏)(a))(b))(a) = {}
--   accepts-ε(𝔏) = 𝑇
--   accepts-ε(suffix(𝔏)(a)) = 𝐹
record Language {ℓ} (Σ : Alphabet{ℓ}) {s : Size} : Type{ℓ} where
  constructor intro
  coinductive
  field
    accepts-ε : Bool
    suffix    : ∀{sₛ : <ˢⁱᶻᵉ s} → Σ → Language(Σ){sₛ}

private variable s : Size
private variable Σ : Type{ℓ}

suffixOf : ∀{sₛ : <ˢⁱᶻᵉ s} → Σ → Language(Σ){s} → Language(Σ){sₛ}
suffixOf c 𝔏 = Language.suffix 𝔏 c

-- TODO: Not sure of the sizes
-- suffixOfWord : ∀{s}{sₛ : <ˢⁱᶻᵉ s}{sₗ}{Σ} → Word(sₗ)(Σ) → Language(Σ){s} → Language(Σ){sₛ}
-- suffixOfWord        []      𝔏 = 𝔏
-- suffixOfWord{s}{sₛ}{sₗ} (_⊰_ {sₗₛ} c w) 𝔏 = suffixOfWord{sₛ}{sₗₛ}{sₗ} ? {!suffixOf{s}{sₛ} c 𝔏!}

{-
Language-intro : Bool → (∀{s}{sₛ : <ˢⁱᶻᵉ s} → Language(Σ){sₛ} → Σ → Language(Σ){sₛ}) → (∀{s} → Language(Σ){s})
Language.accepts-ε (Language-intro b rec) = b
Language.suffix    (Language-intro b rec) = rec(Language-intro b rec)
-}
