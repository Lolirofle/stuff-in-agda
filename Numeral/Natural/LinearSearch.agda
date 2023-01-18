module Numeral.Natural.LinearSearch where

open import Data.Boolean
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper

findUpperboundedMin : ℕ → (ℕ → Bool) → Option(ℕ)
findUpperboundedMin 𝟎       f = None
findUpperboundedMin (𝐒 max) f with f(𝟎)
... | 𝑇 = Some(𝟎)
... | 𝐹 = Option.map 𝐒(findUpperboundedMin max (f ∘ 𝐒))

findUpperboundedMax : ℕ → (ℕ → Bool) → Option(ℕ)
findUpperboundedMax 𝟎       f = None
findUpperboundedMax (𝐒 max) f with f(max)
... | 𝑇 = Some(max)
... | 𝐹 = findUpperboundedMax max f

findBoundedMin : ℕ → ℕ → (ℕ → Bool) → Option(ℕ)
findBoundedMin min max f = Option.map(_+ min) (findUpperboundedMin (max −₀ min) (f ∘ (_+ min)))

findBoundedMax : ℕ → ℕ → (ℕ → Bool) → Option(ℕ)
findBoundedMax min max f = Option.map(_+ min) (findUpperboundedMax (max −₀ min) (f ∘ (_+ min)))

open import Data.List
import      Data.List.Functions as List
open import Numeral.Finite
import      Numeral.Finite.LinearSearch as 𝕟

findBoundedAll : ℕ → ℕ → (ℕ → Bool) → List(ℕ)
findBoundedAll a b f = List.map ((_+ a) ∘ toℕ) (𝕟.findAll{b −₀ a} (f ∘ (_+ a) ∘ toℕ))
