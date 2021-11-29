module Data.Boolean.Decidable where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Operator.Equals using (EquivDecider)
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type
open import Type.Properties.Decidable

instance
  [≡]-decider : EquivDecider(_==_)
  [≡]-decider {𝑇} {𝑇} = true [≡]-intro
  [≡]-decider {𝑇} {𝐹} = false \()
  [≡]-decider {𝐹} {𝑇} = false \()
  [≡]-decider {𝐹} {𝐹} = true [≡]-intro
