{-# OPTIONS --guardedness #-}

module Iterator where

import      Lvl
open import Data.Option as Option using (Option ; Some ; None)
open import Data.Tuple  as Tuple  using (_⨯_ ; _,_)
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable a x init : T
private variable f : A → B

-- A finite/infinite sequence.
record Iterator (T : Type{ℓ}) : Type{ℓ} where
  coinductive
  field
    next : Option(T ⨯ Iterator(T))

open Iterator

empty : Iterator(T)
next empty = None

singleton : T → Iterator(T)
next(singleton x) = Some(x , empty)

prepend : T → Iterator(T) -> Iterator(T)
next(prepend x i) = Some(x , i)

import Data.Option.Functions as Option

head : Iterator(T) → Option(T)
head i = Option.map Tuple.left (next(i))

tail : Iterator(T) → Option(Iterator(T))
tail i = Option.map Tuple.right (next(i))

open import Functional

tail₀ : Iterator(T) → Iterator(T)
tail₀ = (Option._or empty) ∘ tail

open import Numeral.Natural
open import Numeral.Natural.Induction

index : ℕ → Iterator(T) → Option(T)
index n      i with next(i)
index _      _ | None        = None
index 𝟎      _ | Some(x , r) = Some x
index (𝐒(k)) _ | Some(x , r) = index k r



repeat : T → Iterator(T)
next(repeat(x)) = Some(x , repeat(x))

map : (A → B) → (Iterator(A) → Iterator(B))
next(map f(i)) with next(i)
... | None        = None
... | Some(x , r) = Some(f(x) , map f(r))
-- Option.map (Tuple.map f (map f)) (next i)
