module Operator.Summation.Range.Proofs where

import      Lvl
open import Data.List
open import Data.List.Functions
open        Data.List.Functions.LongOper
open import Data.List.Proofs
open import Data.List.Equiv.Id
open import Data.List.Proofs.Length
open import Functional as Fn using (_$_ ; _∘_ ; const)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Operator.Summation.Range
open import Relator.Equals hiding (_≡_)
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

Range-empty : ∀{a} → (a ‥ a ≡ ∅)
Range-empty {𝟎} = [≡]-intro
Range-empty {𝐒 a} rewrite Range-empty {a} = [≡]-intro
{-# REWRITE Range-empty #-}

Range-reversed : ∀{a b} → ⦃ _ : (a ≥ b) ⦄ → (a ‥ b ≡ ∅)
Range-reversed {a}   {𝟎}   ⦃ min ⦄ = [≡]-intro
Range-reversed {𝐒 a} {𝐒 b} ⦃ succ p ⦄
  rewrite Range-reversed {a} {b} ⦃ p ⦄
  = [≡]-intro

Range-succ : ∀{a b} → (map 𝐒(a ‥ b) ≡ 𝐒(a) ‥ 𝐒(b))
Range-succ = [≡]-intro

Range-prepend : ∀{a b} → ⦃ _ : (a < b) ⦄ → (a ‥ b ≡ prepend a (𝐒(a) ‥ b))
Range-prepend {𝟎}   {𝐒 b} = [≡]-intro
Range-prepend {𝐒 a} {𝐒 b} ⦃ succ ab ⦄ rewrite Range-prepend {a} {b} ⦃ ab ⦄ = [≡]-intro

Range-postpend : ∀{a b} → ⦃ _ : (a < 𝐒(b)) ⦄ → (a ‥ 𝐒(b) ≡ postpend b (a ‥ b))
Range-postpend {𝟎}   {𝟎}   ⦃ [≤]-with-[𝐒] ⦄ = [≡]-intro
Range-postpend {𝟎}   {𝐒 b} ⦃ [≤]-with-[𝐒] ⦄  = congruence₁(prepend 𝟎) $
  map 𝐒(𝟎 ‥ 𝐒(b))                 🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-postpend {𝟎}{b}) ]
  map 𝐒(postpend b (𝟎 ‥ b))       🝖[ _≡_ ]-[ map-postpend ]
  postpend (𝐒(b)) (map 𝐒(𝟎 ‥ b))  🝖-end
Range-postpend {𝐒 a} {𝐒 b} ⦃ succ 𝐒ab ⦄
  rewrite Range-postpend {a} {b} ⦃ 𝐒ab ⦄
  = map-postpend

Range-length : ∀{a b} → (length(a ‥ b) ≡ b −₀ a)
Range-length {𝟎} {𝟎} = [≡]-intro
Range-length {𝟎} {𝐒 b}
  rewrite length-map{f = 𝐒}{x = 𝟎 ‥ b}
  rewrite Range-length {𝟎} {b}
  = congruence₁(𝐒) [≡]-intro
Range-length {𝐒 a} {𝟎} = [≡]-intro
Range-length {𝐒 a} {𝐒 b}
  rewrite length-map{f = 𝐒}{x = a ‥ b}
  rewrite Range-length {a} {b}
  = [≡]-intro

Range-length-zero : ∀{b} → (length(𝟎 ‥ b) ≡ b)
Range-length-zero {b} = Range-length {𝟎}{b}

Range-singleton : ∀{a} → (a ‥ 𝐒(a) ≡ singleton(a))
Range-singleton {𝟎} = [≡]-intro
Range-singleton {𝐒 a}
  rewrite Range-singleton {a}
  = [≡]-intro
{-# REWRITE Range-singleton #-}

Range-concat : ∀{a b c} → ⦃ ab : (a ≤ b) ⦄ ⦃ bc : (b < c) ⦄ → ((a ‥ b) ++ (b ‥ c) ≡ a ‥ c)
Range-concat {𝟎} {𝟎}   {𝐒 c} ⦃ min ⦄ ⦃ succ bc ⦄ = [≡]-intro
Range-concat {𝟎} {𝐒 b} {𝐒 c} ⦃ min ⦄ ⦃ succ bc ⦄ = congruence₁ (prepend 0) $
  map 𝐒(𝟎 ‥ b) ++ map 𝐒 (b ‥ c) 🝖[ _≡_ ]-[ preserving₂(map 𝐒)(_++_)(_++_) {𝟎 ‥ b}{b ‥ c} ]-sym
  map 𝐒((𝟎 ‥ b) ++ (b ‥ c))     🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-concat {𝟎} {b} {c}) ]
  map 𝐒(𝟎 ‥ c)                  🝖-end
  where instance _ = bc
Range-concat {𝐒 a} {𝐒 b} {𝐒 c} ⦃ succ ab ⦄ ⦃ succ bc ⦄ =
  map 𝐒(a ‥ b) ++ map 𝐒 (b ‥ c) 🝖[ _≡_ ]-[ preserving₂(map 𝐒)(_++_)(_++_) {a ‥ b}{b ‥ c} ]-sym
  map 𝐒((a ‥ b) ++ (b ‥ c))     🝖[ _≡_ ]-[ congruence₁(map 𝐒) (Range-concat {a} {b} {c}) ]
  map 𝐒(a ‥ c)                  🝖-end
  where
    instance _ = ab
    instance _ = bc
