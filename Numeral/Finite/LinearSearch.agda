-- Note: This module could also belong to Numeral.CoordinateVector.LinearSearch.
module Numeral.Finite.LinearSearch where

open import Data
open import Data.Boolean
open import Data.List
import      Data.List.Functions as List
open import Data.Option
import      Data.Option.Functions as Option
open import Functional
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural

private variable n : ℕ

-- Finds the maximal argument satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findMax{5}   (10 ∣?_) = None
--   findMax{10}  (10 ∣?_) = None
--   findMax{20}  (10 ∣?_) = Some 10
--   findMax{21}  (10 ∣?_) = Some 20
--   findMax{22}  (10 ∣?_) = Some 20
--   findMax{100} (10 ∣?_) = Some 90
--   findMax{102} (10 ∣?_) = Some 100
-- Alternative implementation: findMax f = Option.map Wrapping.[−]_ (findMin(f ∘ Wrapping.[−]_))
findMax : (𝕟(n) → Bool) → Option(𝕟(n))
findMax {𝟎}    f = None
findMax {𝐒(n)} f with f(maximum)
findMax {𝐒(n)} f | 𝑇 = Some maximum
findMax {𝐒(n)} f | 𝐹 = Option.map bound-𝐒 (findMax{n} (f ∘ bound-𝐒))

-- Finds the minimal argument satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findMin{5}   (10 ∣?_) = None
--   findMin{10}  (10 ∣?_) = None
--   findMin{20}  (10 ∣?_) = Some 10
--   findMin{21}  (10 ∣?_) = Some 10
--   findMin{22}  (10 ∣?_) = Some 10
--   findMin{100} (10 ∣?_) = Some 10
--   findMax{102} (10 ∣?_) = Some 10
findMin : (𝕟(n) → Bool) → Option(𝕟(n))
findMin{𝟎}    f = None
findMin{𝐒(n)} f with f(𝟎)
findMin{𝐒(n)} f | 𝑇 = Some 𝟎
findMin{𝐒(n)} f | 𝐹 = Option.map 𝐒 (findMin{n} (f ∘ 𝐒))

-- Finds all arguments satisfying the given decidable predicate by searching linearly.
-- Examples:
--   findAll{10} (2 ∣?_) = [0,2,4,6,8]
findAll : (𝕟(n) → Bool) → List(𝕟(n))
findAll{𝟎}    f = ∅
findAll{𝐒(n)} f = (if f(𝟎) then (𝟎 ⊰_) else id) (List.map 𝐒 (findAll{n} (f ∘ 𝐒)))

-- Examples:
--   f : 𝕟(5) → Bool
--   f(𝟎)            = 𝐹
--   f(𝐒 𝟎)          = 𝑇
--   f(𝐒(𝐒 𝟎))       = 𝑇
--   f(𝐒(𝐒(𝐒 𝟎)))    = 𝑇
--   f(𝐒(𝐒(𝐒(𝐒 𝟎)))) = 𝐹
--
--   findMin f = Some(𝐒 𝟎)
--   findMax f = Some(𝐒(𝐒(𝐒 𝟎)))
--   findAll f = 1 ⊰ 2 ⊰ 3 ⊰ ∅
