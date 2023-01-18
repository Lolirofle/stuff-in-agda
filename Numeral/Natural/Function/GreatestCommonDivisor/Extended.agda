module Numeral.Natural.Function.GreatestCommonDivisor.Extended where

import Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Numeral.Integer as ℤ
open import Numeral.Integer.Oper using (_+_ ; _−_ ; _⋅_)
open import Numeral.Natural as ℕ
open import Numeral.Natural.Function.GreatestCommonDivisor.Algorithm
open import Numeral.Natural.Oper.FlooredDivision
open import Syntax.Number

gcdExt : ℕ → ℕ → (ℤ ⨯ ℤ)
gcdExt = gcdAlgorithm(\a b _ (x , y) → (y , x − ((+ₙ(a ⌊/⌋ b)) ⋅ y))) Tuple.swap (\_ → (1 , 0))

{- TODO: Remove later. Just for testing whether it is possible to use ℕ._𝄩_
open import Data.List

-- TODO: Does the same algorithm work in the naturals? https://math.stackexchange.com/questions/237372/finding-positive-b%C3%A9zout-coefficients https://math.stackexchange.com/questions/1230224/positive-solutions-of-893x-2432y-19?rq=1 Probably not
gcdExt' : ℕ → ℕ → List(ℕ ⨯ ℕ ⨯ ℕ ⨯ ℕ)
gcdExt' = gcdAlgorithm(\{ a b _ ((a' , b' , x , y) ⊰ l) → (a , b , y , (x ℕ.𝄩 ((a ⌊/⌋ b) ℕ.⋅ y))) ⊰ (a' , b' , x , y) ⊰ l}) (\_ → (0 , 0 , 1 , 0) ⊰ ∅)


gcdExt'' : ℕ → ℕ → List(ℕ ⨯ ℕ ⨯ ℤ ⨯ ℤ)
gcdExt'' = gcdAlgorithm(\{ a b _ ((a' , b' , x , y) ⊰ l) → (a , b , y , (x − ((+ₙ(a ⌊/⌋ b)) ⋅ y))) ⊰ (a' , b' , x , y) ⊰ l}) (\_ → (0 , 0 , 1 , 0) ⊰ ∅)

test2 = {!gcdExt'' 240 46!}
test = {!let (a , b) = (240 , 46) ; (x , y) = gcdExt a b in (x ⋅ (+ₙ a) + y ⋅ (+ₙ b) , gcd a b)!}
-}
