{-# OPTIONS --guardedness #-}

module FormalLanguage2.Oper where

import      Lvl
open import Data.List using (List ; _⊰_) renaming (∅ to [])
open import Data.Boolean
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming hiding (_==_)
open import Data.Boolean.Stmt
open import FormalLanguage2
open import Functional
open import Numeral.Natural
open import Operator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid
open import Type

private variable ℓ : Lvl.Level
private variable Σ Σ₁ Σ₂ : Type{ℓ}

infixl 1003 _∪_
infixl 1002 _∩_
infixl 1001 _𝁼_
infixl 1000 _*

-- The empty language.
-- The language that does not include any word at all.
-- Definition (Language set): ∅ = {}
∅ : Language(Σ)
Language.accepts-ε ∅   = 𝐹
Language.suffix    ∅ _ = ∅

-- The empty word language.
-- The language with only the empty word.
-- Definition (Language set): ε = {ε} = {""}
-- Note: Not to be confused by the empty word "", also denoted as ε.
ε : Language(Σ)
Language.accepts-ε ε   = 𝑇
Language.suffix    ε _ = ∅

-- The language of length 1 words that only accepts some symbols of its alphabet
-- Example (Language set): symbolFilter(c ↦ (c == 'a') || (c == 'b')) = {"a","b"}
symbolFilter : (Σ → Bool) → Language(Σ)
Language.accepts-ε (symbolFilter f)   = 𝐹
Language.suffix    (symbolFilter f) c = if f(c) then ε else ∅

-- The single symbol language.
-- The language consisting of a single word with a single letter
-- Note: This is only possible when Alphabet has a computably decidable equality relation
-- Example (Language set): symbol 'a' = {"a"}
symbol : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(Σ) ⦄ ⦃ equiv-dec : EquivDecidable(Σ) ⦃ equiv ⦄ ⦄ → Σ → Language(Σ)
symbol(a) = symbolFilter(_==_ a)

-- The single word language.
-- The language consisting of a single wordr
-- Note: This is only possible when Alphabet has a computably decidable equality relation
-- Definition (Language set): word w = {w}
word : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(Σ) ⦄ ⦃ equiv-dec : EquivDecidable(Σ) ⦃ equiv ⦄ ⦄ → Word Σ → Language(Σ)
word [] = ε
Language.accepts-ε (word (_ ⊰ w)) = 𝐹
Language.suffix    (word (c₁ ⊰ w)) c₂ with c₁ == c₂
... | 𝑇 = word w
... | 𝐹 = ∅

-- The sublanguage filtered by a decidable predicate.
-- Definition (Language set): filter f(L) = {w. (w ∈ L) ∧ (f(w) ≡ 𝑇)}
-- Example (Language set): filter(w ↦ length w == 2) {"a","ab","abc","b","bc","c"} = {"ab","bc"}
filter : (Word Σ → Bool) → Language(Σ) → Language(Σ)
Language.accepts-ε (filter P(𝔏))   = P(List.∅)
Language.suffix    (filter P(𝔏)) c = filter (P ∘ (c ⊰_)) (Language.suffix(𝔏)(c))

-- The language where every letter in the alphabet is applied to a function.
unmap : (Σ₁ ← Σ₂) → Language(Σ₁) → Language(Σ₂)
Language.accepts-ε (unmap f(𝔏))   = Language.accepts-ε (𝔏)
Language.suffix    (unmap f(𝔏)) c = unmap f(Language.suffix(𝔏)(f(c)))

-- Union.
-- The language that includes any words that the two languages have.
-- Definition (Language set): L₁ ∪ L₂ = {w. (w ∈ L₁) ∨ (w ∈ L₂)}
-- Example (Language set): {"a","aa","aaa"} ∪ {"b","bb"} = {"a","aa","aaa","b","bb"}
_∪_ : Language(Σ) → Language(Σ) → Language(Σ)
Language.accepts-ε (L₁ ∪ L₂)   = Language.accepts-ε(L₁) || Language.accepts-ε(L₂)
Language.suffix    (L₁ ∪ L₂) c = Language.suffix(L₁)(c) ∪ Language.suffix(L₂)(c)

-- Intersection.
-- The language that includes only the words that both languages have in common.
-- Definition (Language set): L₁ ∩ L₂ = {w. (w ∈ L₁) ∧ (w ∈ L₂)}
-- Example (Language set): {"a","ab","abc"} ∩ {"ab","abc","abcd"} = {"ab","abc"}
_∩_ : Language(Σ) → Language(Σ) → Language(Σ)
Language.accepts-ε (L₁ ∩ L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
Language.suffix    (L₁ ∩ L₂) c = Language.suffix(L₁)(c) ∩ Language.suffix(L₂)(c)

-- Concatenation.
-- The language that includes words that start with a word from the first language and end in a word from the second language.
-- Definition (Language set): L₁ 𝁼 L₂ = {w₁ 𝁼 w₂. (w₁ ∈ L₁) ∧ (w₂ ∈ L₂)}
-- Example (Language set):
--   {}   𝁼 {}   = {}
--   {""} 𝁼 {}   = {}
--   {}   𝁼 {""} = {}
--   {""} 𝁼 {""} = {""}
--   {} 𝁼 {"a"} = {}
--   {"a"} 𝁼 {} = {}
--   {""} 𝁼 {"a"} = {"a"}
--   {"a"} 𝁼 {""} = {"a"}
--   {"test"} 𝁼 {"","1","2","10"} = {"test","test1","test2","test10"}
--   {"a","ab","abc"} 𝁼 {"1","01","2"} = {"a1","ab1","abc1" , "a01","ab01","abc01" , "a2","ab2","abc2"}
{-# TERMINATING #-}
_𝁼_ : Language(Σ) → Language(Σ) → Language(Σ)
Language.accepts-ε (L₁ 𝁼 L₂)   = Language.accepts-ε(L₁) && Language.accepts-ε(L₂)
Language.suffix    (L₁ 𝁼 L₂) c with Language.accepts-ε(L₁)
... | 𝑇 = (Language.suffix(L₁)(c) 𝁼 L₂) ∪ Language.suffix(L₂)(c)
... | 𝐹 = (Language.suffix(L₁)(c) 𝁼 L₂)

-- Power.
-- The language that includes words in the specified number of concatenations with itself.
-- Note: (L ^ n = (L ^ n) ∪ (L ^ (n − 1)) ∪ … (L ^ 0)) when (ε ∈ L).
_^_ : Language(Σ) → ℕ → Language(Σ)
L ^ 𝟎    = ε
L ^ 𝐒(n) = L 𝁼 (L ^ n)

-- Conditional power.
-- The language that includes words in some specific numbers of concatenations with itself.
-- Note: (L ^? f = L *) when (ε ∈ L).
{-# TERMINATING #-}
_^?_ : Language(Σ) → (ℕ → Bool) → Language(Σ)
Language.accepts-ε (L ^? f)   = f(𝟎) || Language.accepts-ε(L)
Language.suffix    (L ^? f) c = (Language.suffix L c) 𝁼 (L ^? (f ∘ 𝐒))

-- Star/Closure
-- The language that includes words in any number of concatenations with itself.
-- Definition (Language set): : L * = ⋃{(L ^ n). n ∈ ℕ}
-- Example (Language set):
--   {} * = {""}
--   {""} * = {""}
--   {"yes"} * = {"","yes","yesyes","yesyesyes",…}
--   {"0","1"} * = {"","0","1","00","01","10","11","000","001",‥‥}
{-# TERMINATING #-}
_* : Language(Σ) → Language(Σ)
Language.accepts-ε (L *)   = 𝑇
Language.suffix    (L *) c = Language.suffix(L)(c) 𝁼 (L *)

-- Non-empty closure
-- The language that includes words in at least one concatenation with itself.
-- Definition (Language set): : L * = ⋃{(L ^ n). n ∈ ℕ₊}
-- Example (Language set):
--   {} + = {}
--   {""} + = {""}
--   {"yes"} + = {"yes","yesyes","yesyesyes",…}
--   {"0","1"} + = {"0","1","00","01","10","11","000","001",‥‥}
_+ : Language(Σ) → Language(Σ)
Language.accepts-ε (L +) = Language.accepts-ε(L)
Language.suffix    (L +) = Language.suffix(L *)

-- Complement
-- The language that includes all words that a language does not have.
-- Definition (Language set): : ∁ L = {w. w ∉ L}
∁_ : Language(Σ) → Language(Σ)
Language.accepts-ε (∁ L)   = !(Language.accepts-ε(L))
Language.suffix    (∁ L) c = ∁(Language.suffix(L)(c))

-- Optional
-- Definition (Language set): : L ?? = L ∪ ε
_?? : Language(Σ) → Language(Σ)
Language.accepts-ε (L ??) = 𝑇
Language.suffix    (L ??) = Language.suffix(L)

-- The universal language.
-- The language that includes all words in any combination of the alphabet.
-- The largest language (in the sense of the most words) using a certain alphabet.
-- Definition (Language set): : ⋃ = {w. ⊤}
𝐔 : Language(Σ)
𝐔 = ∁(∅)

-- Containment check
-- Checks whether a word is in the language.
_∈?_ : Word Σ → Language(Σ) → Bool
[]      ∈? L = Language.accepts-ε(L)
(c ⊰ w) ∈? L = w ∈? (Language.suffix L c)

-- Containment
-- States that a word is in the language.
_∈_ : Word Σ → Language(Σ) → Type
a ∈ b = IsTrue(a ∈? b)

-- Uncontainment
-- States that a word is not in the language.
_∉_ : Word Σ → Language(Σ) → Type
a ∉ b = IsFalse(a ∈? b)
