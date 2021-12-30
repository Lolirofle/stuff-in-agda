module Numeral.Natural.Relation.Order.Category where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.IntroInstances
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Function
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Relator.Properties
open import Type

instance
  [≤]-identityₗ : Morphism.Identityₗ{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x})) (reflexivity(_≤_))
  [≤]-identityₗ = Morphism.intro proof where
    proof : Names.Morphism.Identityₗ{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x})) (reflexivity(_≤_))
    proof {𝟎}   {y}   {min}    = [≡]-intro
    proof {𝐒 x} {𝐒 y} {succ p} = congruence₁(succ) (proof {x}{y} {p})

instance
  [≤]-identityᵣ : Morphism.Identityᵣ{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x})) (reflexivity(_≤_))
  [≤]-identityᵣ = Morphism.intro proof where
    proof : Names.Morphism.Identityᵣ{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x})) (reflexivity(_≤_))
    proof {𝟎}   {y}   {min} = [≡]-intro
    proof {𝐒 x} {𝐒 y} {succ p} = congruence₁(p ↦ [≤]-with-[𝐒] ⦃ p ⦄) (proof {x}{y} {p})

instance
  [≤]-associativity : Morphism.Associativity{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x}))
  [≤]-associativity = Morphism.intro proof where
    proof : Names.Morphism.Associativity{Obj = ℕ}(\{x} → swap(transitivity(_≤_) {x}))
    proof {.𝟎}     {.𝟎}     {.𝟎}     {w}      {min}    {min}    {min}    = [≡]-intro
    proof {.𝟎}     {.𝟎}     {.(𝐒 _)} {.(𝐒 _)} {succ _} {min}    {min}    = [≡]-intro
    proof {.𝟎}     {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {succ _} {succ _} {min}    = [≡]-intro
    proof {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {.(𝐒 _)} {succ _} {succ _} {succ _} = congruence₁(succ) proof

instance
  [≤]-category : Category(_≤_)
  Category._∘_ [≤]-category = swap(transitivity(_≤_))
  Category.id  [≤]-category = reflexivity(_≤_)
  Category.binaryOperator [≤]-category = intro(\{[≡]-intro [≡]-intro → [≡]-intro})
