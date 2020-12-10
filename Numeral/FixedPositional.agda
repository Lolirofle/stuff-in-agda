module Numeral.FixedPositional where

open import Data.List
open import Numeral.Finite
open import Numeral.Natural
open import Type

FixedPositional : ℕ → Type
FixedPositional(b) = List(𝕟(b))

open import Numeral.Natural.Oper

private variable b : ℕ

to-ℕ : FixedPositional(b) → ℕ
to-ℕ {_} ∅       = 𝟎
to-ℕ {b} (n ⊰ l) = 𝕟-to-ℕ (n) + (b ⋅ to-ℕ (l))

module _ where
  open import Functional
  open import Function.Iteration using (repeatᵣ)
  open import Numeral.Natural.Induction
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Syntax.Function
  open import Syntax.Transitivity

  {- TODO: Attempt to prove `∀a∀b. aᵇ = 1 + ((a−1) ⋅ ∑(0‥b) (i ↦ aⁱ))` inductively. An intuitive example of this is: `10³ = 1000 = 1+999 = 1+(9⋅111) = 1+(9⋅(1+10+100)) = 1+((10−1)⋅(10⁰+10¹+10²))`. This can also be proved by using the binomial theorem?
  powerSum : ℕ → ℕ → ℕ
  powerSum a 0         = 0
  powerSum a 1         = 1
  powerSum a (𝐒(𝐒(b))) = (powerSum a (𝐒(b))) + (a ⋅ (powerSum a (𝐒(b))))

  exponentiation-is-sum-of-parts : ∀{a b} → (𝐒(a) ^ b ≡ 𝐒(a ⋅ (powerSum (𝐒(a)) b)))
  exponentiation-is-sum-of-parts {a} {0}       = [≡]-intro
  exponentiation-is-sum-of-parts {a} {1}       = [≡]-intro
  exponentiation-is-sum-of-parts {a} {𝐒(b@(𝐒(_)))} =
    𝐒(a) ^ 𝐒(b)                     🝖[ _≡_ ]-[]
    𝐒(a) ⋅ (𝐒(a) ^ b)               🝖[ _≡_ ]-[ {!!} ]
    (𝐒(a) ^ b) + (𝐒(a) ⋅ (a ⋅ (powerSum (𝐒(a)) b)))                   🝖[ _≡_ ]-[ {!!} ]
    (𝐒(a) ^ b) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))                   🝖[ _≡_ ]-[ {!!} ]
    𝐒(a ⋅ (powerSum (𝐒(a)) b)) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))   🝖[ _≡_ ]-[ {!!} ]
    𝐒((a ⋅ (powerSum (𝐒(a)) b)) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))) 🝖[ _≡_ ]-[ {!!} ]
    𝐒(a ⋅ ((powerSum (𝐒(a)) b) + (𝐒(a) ⋅ (powerSum (𝐒(a)) b))))       🝖[ _≡_ ]-[]
    𝐒(a ⋅ (powerSum (𝐒(a)) (𝐒(b))))                                   🝖-end
  -}

module _ where
  open import Data.List.Functions
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  {-
  FixedPositional-maximum : ∀{n : FixedPositional(b)} → (to-ℕ (n) < b ^ length(n))
  FixedPositional-maximum {_}   {∅}     = reflexivity(_≤_)
  FixedPositional-maximum {𝐒 b} {n ⊰ l} =
    𝐒(𝕟-to-ℕ (n) + (𝐒(b) ⋅ to-ℕ (l)))                               🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + (𝐒(b) ⋅ (b ^ length(l))))                        🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + ((b ⋅ (b ^ length(l))) + (1 ⋅ (b ^ length(l))))) 🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + ((b ^ 𝐒(length(l))) + (b ^ length(l))))          🝖[ _≤_ ]-[ {!!} ]
    ?                                                               🝖[ _≤_ ]-[ {!!} 
    (b ⋅ (𝐒(b) ^ length(l))) + (𝐒(b) ^ length(l))                   🝖[ _≤_ ]-[ {!!} ]
    𝐒(b) ⋅ (𝐒(b) ^ length(l))                                       🝖-end
  -}
