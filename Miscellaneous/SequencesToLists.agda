module Miscellaneous.SequencesToLists where

open import Data
open import Data.List
open import Data.List.Functions
open import Data.Tuple as Tuple
open import Functional
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Natural
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

sequenceList : ∀{n} → (𝕟(n) → T) → List(T)
sequenceList {n = 𝟎}   f = ∅
sequenceList {n = 𝐒 n} f = f(𝟎) ⊰ sequenceList{n = n} (f ∘ 𝐒)

-- TODO: These are essentially some different bijective mappings from a 2d table to a 1d list.

-- 1 2 3
-- 4 6 7
-- 5 8 9
R0D : ∀{n} → ((𝕟(n) ⨯ 𝕟(n)) → T) → List(T)
R0D{n = 𝟎}   f = ∅
R0D{n = 𝐒 n} f = f(𝟎 , 𝟎) ⊰ (sequenceList{n = n} (i ↦ f(𝐒(i) , 𝟎)) ++ sequenceList{n = n} (i ↦ f(𝟎 , 𝐒(i))) ++ R0D{n = n} (f ∘ Tuple.map 𝐒 𝐒))

-- 1 2 3
-- 6 7 4
-- 9 8 5
RD : ∀{n} → ((𝕟(n) ⨯ 𝕟(n)) → T) → List(T)
RD{n = 𝟎}   f = ∅
RD{n = 𝐒 n} f = f(𝟎 , 𝟎) ⊰ (sequenceList{n = n} (i ↦ f(𝐒(i) , 𝟎)) ++ sequenceList{n = n} (i ↦ f(maximum , 𝐒(i))) ++ RD{n = n} (f ∘ Tuple.map bound-𝐒 𝐒))

-- 1 2 3
-- 8 9 4
-- 7 6 5
RDspiral : ∀{n} → ((𝕟(n) ⨯ 𝕟(n)) → T) → List(T)
RDspiral{n = 𝟎}   f = ∅
RDspiral{n = 𝐒 n} f = f(𝟎 , 𝟎) ⊰ (sequenceList{n = n} (i ↦ f(𝐒(i) , 𝟎)) ++ sequenceList{n = n} (i ↦ f(maximum , 𝐒(i))) ++ RDspiral{n = n} (f ∘ Tuple.map (bound-𝐒 ∘ Wrapping.flip) (𝐒 ∘ Wrapping.flip)))

{-
test : (𝕟(3) ⨯ 𝕟(3)) → ℕ
test (𝟎      , 𝟎)      = 1
test (𝐒 𝟎    , 𝟎)      = 2
test (𝐒(𝐒 𝟎) , 𝟎)      = 3
test (𝟎      , 𝐒 𝟎)    = 4
test (𝐒 𝟎    , 𝐒 𝟎)    = 5
test (𝐒(𝐒 𝟎) , 𝐒 𝟎)    = 6
test (𝟎      , 𝐒(𝐒 𝟎)) = 7
test (𝐒 𝟎    , 𝐒(𝐒 𝟎)) = 8
test (𝐒(𝐒 𝟎) , 𝐒(𝐒 𝟎)) = 9

test4 = {!RDspiral test!}
-}
