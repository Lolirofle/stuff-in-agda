import      Lvl
open import Type

module Data.ListSized {ℓ} (T : Type{ℓ}) where

import      Data.IndexedList
open import Functional
open import Numeral.Natural

open Data.IndexedList(T){ℕ} using (IndexedList ; intro)

-- A list is a container/collection with elements in order and which allows multiples
List : ℕ → Type{ℓ}
List(n) = IndexedList(intro 𝟎 (const 𝐒))(n)

open Data.IndexedList(T){ℕ} using (∅ ; _⊰_ ; singleton) public
