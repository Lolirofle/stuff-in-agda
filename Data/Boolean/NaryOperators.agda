module Data.Boolean.NaryOperators where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Logic
open import Function.DomainRaise
open import Numeral.Natural

private variable n : ℕ

-- N-ary conjunction (AND).
-- Every term is true.
∧₊ : (n : ℕ) → (Bool →̂ Bool)(n)
∧₊(0) = 𝑇
∧₊(1) x = x
∧₊(𝐒(𝐒(n))) x = (x ∧_) ∘ (∧₊(𝐒(n)))

-- N-ary disjunction (OR).
-- There is a term which is true.
∨₊ : (n : ℕ) → (Bool →̂ Bool)(n)
∨₊(0) = 𝐹
∨₊(1) x = x
∨₊(𝐒(𝐒(n))) x = (x ∨_) ∘ (∨₊(𝐒(n)))

-- N-ary implication.
-- All left terms together imply the right-most term.
⟶₊ : (n : ℕ) → (Bool →̂ Bool)(n)
⟶₊(0) = 𝑇
⟶₊(1) x = x
⟶₊(𝐒(𝐒(n))) x = (x ⟶_) ∘ (⟶₊(𝐒(n)))

-- N-ary NAND.
-- Not every term is true.
-- There is a term which is false.
⊼₊ : (n : ℕ) → (Bool →̂ Bool)(n)
⊼₊(0) = 𝐹
⊼₊(1) x = ¬ x
⊼₊(𝐒(𝐒(n))) x = (x ⊼_) ∘ ((¬) ∘ (⊼₊(𝐒(n))))

-- N-ary NOR.
-- There are no terms that are true.
-- Every term is false.
⊽₊ : (n : ℕ) → (Bool →̂ Bool)(n)
⊽₊(0) = 𝐹
⊽₊(1) x = ¬ x
⊽₊(𝐒(𝐒(n))) x = (x ⊽_) ∘ ((¬) ∘ (⊽₊(𝐒(n))))
