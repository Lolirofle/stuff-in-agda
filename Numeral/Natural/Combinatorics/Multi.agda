module Numeral.Natural.Combinatorics.Multi where

open import Function.DomainRaise
open import Numeral.Natural
open import Numeral.Natural.Oper

-- TODO: How to define? Should probably be 𝑐𝐶₊(3) n k₁ k₂ k₃ = (n !) / ((k₁ !) ⋅ (k₂ !) ⋅ (k₂ !)) = (𝑐𝐶 k₁ k₁) ⋅ (𝑐𝐶(k₁ + k₂) k₂) ⋅ (𝑐𝐶(k₁ + k₂ + k₃) k₃) or 𝑐𝐶₊(3) (𝐒 n) (𝐒 k₁) (𝐒 k₂) (𝐒 k₃) = (𝑐𝐶₊(3) (𝐒 n) k₁ (𝐒 k₂) (𝐒 k₃)) + (𝑐𝐶₊(3) (𝐒 n) (𝐒 k₁) k₂ (𝐒 k₃)) + (𝑐𝐶₊(3) (𝐒 n) (𝐒 k₁) (𝐒 k₂) k₃) in the inductive case and for example 𝑐𝐶₊(3) (𝐒 n) (𝐒 k₁) 0 (𝐒 k₃) = 𝑐𝐶₊(2) (𝐒 n) (𝐒 k₁) (𝐒 k₃) and 𝑐𝐶₊(3) (𝐒 n) (𝐒 k₁) 0 0 = 𝑐𝐶₊(1) (𝐒 n) (𝐒 k₁) in the base cases.

-- Also called: Multinomial coefficients
{-𝑐𝐶₊ : (m : ℕ) → ℕ → (ℕ →̂ ℕ)(m)
𝑐𝐶₊ 0        n   = 1
𝑐𝐶₊ 1        n k = {!!}
𝑐𝐶₊(𝐒(𝐒 m)) 𝟎 𝟎 = {!!}
𝑐𝐶₊(𝐒(𝐒 m)) 𝟎 (𝐒 k) = {!!}
𝑐𝐶₊(𝐒(𝐒 m)) (𝐒 n) 𝟎 = {!!}
𝑐𝐶₊(𝐒(𝐒 m)) (𝐒 n) (𝐒 k) = {!𝑐𝐶₊(𝐒(𝐒 m)) n (k , ks) + 𝑐𝐶₊(𝐒(𝐒 m))!}-}
