module FormalLanguage2 where

open import Data.Boolean
open import Data.List
import      Lvl
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
-- The representation used here is an infinite prefix trie:
--   (Conventions below: LHS is the definition of Language, RHS is the usual semantics of formal languages as sets):
--   For a language L
--   accepts-ε:
--     (accepts-ε(L) = 𝑇) ↔ (ε ∈ L)
--     accepts-ε(L) decides whether the empty word is accepted in the language L.
--   suffix:
--     ∀word∀c. (word ∈ suffix(L)(c)) ↔ ((c 𝁼 word) ∈ L)
--     suffix(L)(c) is the language that consists of the words that is starting with c in the language L.
-- Sources:
--   • Agda 2.5.2 documentation (Copied with modifications) [http://agda.readthedocs.io/en/v2.5.2/language/sized-types.html] (2017-05-13).
--   • The Agda 2.5.2 documentation references the following paper: "Formal Languages, Formally and Coinductively, Dmitriy Traytel, FSCD (2016)" [https://www21.in.tum.de/~traytel/papers/fscd16-coind_lang/paper.pdf].
--   • The initial design using `Size` was also based on the following paper: "Equational Reasoning about Formal Languages in Coalgebraic Style, Andreas Abel (2016)" [http://www.cse.chalmers.se/~abela/jlamp17.pdf].
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
record Language (Σ : Alphabet{ℓ}) : Type{ℓ} where
  constructor intro
  coinductive
  field
    accepts-ε : Bool
    suffix    : Σ → Language(Σ)

private variable Σ : Alphabet{ℓ}

suffix : Σ → Language(Σ) → Language(Σ)
suffix c 𝔏 = Language.suffix 𝔏 c

wordSuffix : Word(Σ) → Language(Σ) → Language(Σ)
wordSuffix ∅       𝔏 = 𝔏
wordSuffix (c ⊰ w) 𝔏 = wordSuffix w (suffix c 𝔏)
