module Data.List.FunctionsProven where

import      Lvl
open import Data.Boolean
open import Data.List as List using (List ; ∅ ; _⊰_)
open import Data.List.Relation.Membership
open import Lang.Instance
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable A B T : Type{ℓ}

map : (l : List(A)) → ((x : A) → ⦃ _ : (x ∈ l) ⦄ → B) → List(B)
map ∅          _ = ∅
map (elem ⊰ l) f = (f elem ⦃ use ⦄) ⊰ (map l (\x → f(x) ⦃ skip ⦄))

filter : (l : List(T)) → ((x : T) → ⦃ _ : (x ∈ l) ⦄ → Bool) → List(T)
filter ∅       f = ∅
filter (x ⊰ l) f =
  if f(x) ⦃ use ⦄
  then (x ⊰ (filter l (\x → f(x) ⦃ skip ⦄)))
  else (filter l (\x → f(x) ⦃ skip ⦄))
