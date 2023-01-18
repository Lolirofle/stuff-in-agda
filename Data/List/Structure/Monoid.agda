module Data.List.Structure.Monoid where

import      Lvl
open import Data.List hiding (prepend)
open import Data.List.Equiv
open import Data.List.Proofs
open import Data.List.Functions
open import Function
open import Logic.Predicate
open import Structure.Operator.Monoid
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑₗ : Lvl.Level
private variable T : Type{ℓ}

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄
  ⦃ extensionality : Extensionality(equiv-List) ⦄
  where

  -- The monoid of lists and list concatenation.
  -- Also called: Free monoid.
  instance
    listMonoid : Monoid{T = List(T)}(_++_)
    Monoid.identity-existence listMonoid = [∃]-intro ∅ ⦃ intro ⦄

open import Numeral.Natural
open import Function.Proofs
open import Structure.Function
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄
  ⦃ ext : Extensionality(equiv-List) ⦄
  {_▫_ : T → T → T}
  where

  open Extensionality(ext)

  instance
    map₂-identityₗ : ∀{f} → Identityₗ(map₂(_▫_) f id) ∅
    map₂-identityₗ{f} = intro(\{x} → p{x}) where
      p : Names.Identityₗ(map₂(_▫_) f id) ∅
      p{∅}      = reflexivity(_≡_)
      p{x ⊰ xl} = reflexivity(_≡_)

  instance
    map₂-identityᵣ : ∀{g} → Identityᵣ(map₂(_▫_) id g) ∅
    map₂-identityᵣ{g} = intro(\{x} → p{x}) where
      p : Names.Identityᵣ(map₂(_▫_) id g) ∅
      p{∅}      = reflexivity(_≡_)
      p{x ⊰ xl} = reflexivity(_≡_)

  instance
    map₂-∅-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(map₂(_▫_) (const ∅) (const ∅))
    map₂-∅-associativity = intro(\{x}{y}{z} → p{x}{y}{z}) where
      p : Names.Associativity(map₂(_▫_) (const ∅) (const ∅))
      p{∅}     {∅}     {∅}      = reflexivity(_≡_)
      p{∅}     {∅}     {z ⊰ zl} = reflexivity(_≡_)
      p{∅}     {y ⊰ yl}{∅}      = reflexivity(_≡_)
      p{∅}     {y ⊰ yl}{z ⊰ zl} = reflexivity(_≡_)
      p{x ⊰ xl}{∅}     {∅}      = reflexivity(_≡_)
      p{x ⊰ xl}{∅}     {z ⊰ zl} = reflexivity(_≡_)
      p{x ⊰ xl}{y ⊰ yl}{∅}      = reflexivity(_≡_)
      p{x ⊰ xl}{y ⊰ yl}{z ⊰ zl} = congruence₂(_⊰_) (associativity(_▫_)) (p{xl}{yl}{zl})

  instance
    map₂-id-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(map₂(_▫_) id id)
    map₂-id-associativity = intro(\{x}{y}{z} → p{x}{y}{z}) where
      p : Names.Associativity(map₂(_▫_) id id)
      p{∅}     {∅}     {∅}      = reflexivity(_≡_)
      p{∅}     {∅}     {z ⊰ zl} = reflexivity(_≡_)
      p{∅}     {y ⊰ yl}{∅}      = reflexivity(_≡_)
      p{∅}     {y ⊰ yl}{z ⊰ zl} = reflexivity(_≡_)
      p{x ⊰ xl}{∅}     {∅}      = reflexivity(_≡_)
      p{x ⊰ xl}{∅}     {z ⊰ zl} = reflexivity(_≡_)
      p{x ⊰ xl}{y ⊰ yl}{∅}      = reflexivity(_≡_)
      p{x ⊰ xl}{y ⊰ yl}{z ⊰ zl} = congruence₂(_⊰_) (associativity(_▫_)) (p{xl}{yl}{zl})

  instance
    listMapMonoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid{T = List(T)}(map₂(_▫_) id id)
    Monoid.binaryOperator     listMapMonoid = map₂-function
    Monoid.associativity      listMapMonoid = map₂-id-associativity
    Monoid.identity-existence listMapMonoid = [∃]-intro ∅ ⦃ intro ⦄
