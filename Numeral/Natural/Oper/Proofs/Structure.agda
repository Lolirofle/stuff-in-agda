module Numeral.Natural.Oper.Proofs.Structure where

open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Monoid

instance
  [+]-monoid : Monoid(_+_)
  Monoid.identity-existence [+]-monoid = [∃]-intro(𝟎)

instance
  [⋅]-monoid : Monoid(_⋅_)
  Monoid.identity-existence [⋅]-monoid = [∃]-intro(𝐒(𝟎))
