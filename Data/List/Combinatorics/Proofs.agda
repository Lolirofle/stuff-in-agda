module Data.List.Combinatorics.Proofs where

import      Lvl
open import Data
open import Data.List
open import Data.List.Combinatorics
open import Data.List.Functions
open import Data.List.Relation.Quantification
open import Data.List.Relation.Sublist
open import Data.List.Relation.Sublist.Proofs
open import Data.List.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Data.Tuple.Raiseᵣ as Tuple₊
import      Data.Tuple.Raiseᵣ.Functions as Tuple₊
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l : List(T)
private variable x : T
private variable n : ℕ

{- TODO: Not sure how to prove this. Maybe by proving that the inductive case of sublists₊ is a permutation of something that easier to prove
sublists₊-contains-sublists : AllElements (_⊑ l) (sublists₊(l))
sublists₊-contains-sublists {l = ∅} = ∅
sublists₊-contains-sublists {l = x ⊰ l} = use [⊑]-minimum ⊰ {!!}
-}

-- TODO: Similar to binomial theorem in a simple case
-- tuples-prepended-length : length(tuples n (x ⊰ l)) ≡ length(l) + 𝐒(length(l)) + length(tuples n l)

{-
tuples-length : length(tuples n l) ≡ length(l) ^ n
tuples-length {𝟎}       {l = _}     = [≡]-intro
tuples-length {𝐒(𝟎)}    {l = _}     = [≡]-intro
tuples-length {𝐒(𝐒(n))} {l = ∅}     = [≡]-intro
tuples-length {𝐒(𝐒(n))} {l = x ⊰ l} =
  length(tuples(𝐒(𝐒(n))) (x ⊰ l))                                             🝖[ _≡_ ]-[]
  length(concat(map (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) (x ⊰ l))) 🝖[ _≡_ ]-[]
  length(concat(map (x Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l)) ⊰ map (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) l)) 🝖[ _≡_ ]-[]
  length(map (x Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l)) ++ concat(map (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) l)) 🝖[ _≡_ ]-[ length-[++] {l₁ = map (x Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))} {l₂ = concat(map (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) l)} ]
  length(map (x Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) + length(concat(map (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) l)) 🝖[ _≡_ ]-[ {!!} ]
  -- TODO: Maybe not like this
  length(x ⊰ l) ⋅ length(tuples(𝐒(n)) (x ⊰ l))                                🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_) (length(x ⊰ l)) (tuples-length {𝐒(n)} {l = x ⊰ l}) ]
  length(x ⊰ l) ⋅ (length(x ⊰ l) ^ 𝐒(n))                                      🝖[ _≡_ ]-[]
  length(x ⊰ l) ^ 𝐒(𝐒(n))                                                     🝖-end
-}
