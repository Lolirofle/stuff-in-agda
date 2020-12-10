module Miscellaneous.TFlipFlop where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Logic
open import Data.Boolean.Numeral
open import Numeral.Natural
open import Syntax.Number

tFlipFlop : Bool → (ℕ → Bool) → (ℕ → Bool)
tFlipFlop init T(𝟎)    = init
tFlipFlop init T(𝐒(n)) = T(n) ⊕ tFlipFlop init T(n)

open import Data
open import Relator.Equals

module _ where
  postulate Q₀ : ℕ → Bool
  postulate Q₁ : ℕ → Bool

  postulate f : Bool → Bool
  postulate g : Bool → Bool

  postulate q₀0 : Q₀(0) ≡ 1
  postulate q₁0 : Q₁(0) ≡ 1

  postulate q₀1 : Q₀(1) ≡ 0
  postulate q₁1 : Q₁(1) ≡ 1

  postulate q₀2 : Q₀(2) ≡ 1
  postulate q₁2 : Q₁(2) ≡ 0

  postulate q₀3 : Q₀(3) ≡ 0
  postulate q₁3 : Q₁(3) ≡ 0

  postulate q₀4 : Q₀(4) ≡ Q₀(0)
  postulate q₁4 : Q₁(4) ≡ Q₁(0)

  {-# REWRITE q₀0 q₁0 q₀1 q₁1 q₀2 q₁2 q₀3 q₁3 q₀4 q₁4 #-}

  private variable n : ℕ

  postulate q₀step : Q₀(𝐒 n) ≡ f(Q₁(n)) ⊕ Q₀(n)
  postulate q₁step : Q₁(𝐒 n) ≡ g(Q₀(n)) ⊕ Q₁(n)

  open import Numeral.Natural.Oper
  open import Relator.Equals.Proofs
  open import Structure.Function
  open import Structure.Operator
  open import Syntax.Transitivity

  q₀cyclic : Q₀(n + 4) ≡ Q₀(n)
  q₁cyclic : Q₁(n + 4) ≡ Q₁(n)

  q₀cyclic {𝟎} = [≡]-intro
  q₀cyclic {𝐒 n} =
    Q₀ (𝐒 n + 4)                🝖[ _≡_ ]-[]
    Q₀ (𝐒(n + 4))               🝖[ _≡_ ]-[ q₀step{n + 4} ]
    f(Q₁(n + 4)) ⊕ Q₀(n + 4)    🝖[ _≡_ ]-[ congruence₂(_⊕_) (congruence₁(f) (q₁cyclic{n})) (q₀cyclic{n}) ]
    f(Q₁(n)) ⊕ Q₀(n)            🝖[ _≡_ ]-[ q₀step{n} ]-sym
    Q₀ (𝐒 n)                    🝖-end

  q₁cyclic {𝟎} = [≡]-intro
  q₁cyclic {𝐒 n} =
    Q₁ (𝐒 n + 4)                🝖[ _≡_ ]-[]
    Q₁ (𝐒(n + 4))               🝖[ _≡_ ]-[ q₁step{n + 4} ]
    g(Q₀(n + 4)) ⊕ Q₁(n + 4)    🝖[ _≡_ ]-[ congruence₂(_⊕_) (congruence₁(g) (q₀cyclic{n})) (q₁cyclic{n}) ]
    g(Q₀(n)) ⊕ Q₁(n)            🝖[ _≡_ ]-[ q₁step{n} ]-sym
    Q₁ (𝐒 n)                    🝖-end

  f0 : f(0) ≡ 1
  f0 with f(0) | q₀step{2}
  ... | 𝑇 | q = [≡]-intro

  f1 : f(1) ≡ 1
  f1 with f(1) | q₀step{0}
  ... | 𝑇 | q = [≡]-intro

  f1' : f(1) ≡ 1
  f1' with f(1) | q₀step{1}
  ... | 𝑇 | q = [≡]-intro

  f1'' : f(1) ≡ 1
  f1'' with f(1) | q₀step{0}
  ... | 𝑇 | q = [≡]-intro



  g1 : g(1) ≡ 0
  g1 with g(1) | q₁step{0}
  ... | 𝐹 | q = [≡]-intro

  g0 : g(0) ≡ 1
  g0 with g(0) | q₁step{1}
  ... | 𝑇 | q = [≡]-intro

  g1' : g(1) ≡ 0
  g1' with g(1) | q₁step{2}
  ... | 𝐹 | q = [≡]-intro

  g1'' : g(0) ≡ 1
  g1'' with g(0) | q₁step{3}
  ... | 𝑇 | q = [≡]-intro
