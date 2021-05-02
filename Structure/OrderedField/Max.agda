open import Logic
open import Structure.Setoid
open import Structure.Relator.Ordering
open import Type

module Structure.OrderedField.Max
  {ℓ ℓₗ ℓₑ}
  {F : Type{ℓ}}
  ⦃ equiv : Equiv{ℓₑ}(F) ⦄
  (_≤_ : F → F → Stmt{ℓₗ})
  ⦃ ordered : Weak.TotalOrder(_≤_) ⦄
  where

open import Functional
open import Structure.Relator.Ordering.Proofs

open import Structure.OrderedField.Min(swap(_≤_)) ⦃ swap-weakTotalOrder ⦄
  using()
  renaming(
    min                                          to max ;
    min-intro                                    to max-intro ;
    min-values                                   to max-values ;
    min-correctness                              to max-correctness ;
    min-when-left                                to max-when-left ;
    min-when-right                               to max-when-right ;
    min-self                                     to max-self ;
    min-function                                 to max-function ;
    min-commutativity                            to max-commutativity ;
    min-associativity                            to max-associativity ;
    min-preserve-function                        to max-preserve-function ;
    min-preserve-function-by-converse-preserving to max-preserve-function-by-converse-preserving
  ) public
