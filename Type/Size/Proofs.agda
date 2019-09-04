module Type.Size.Proofs where

import      Lvl
open import Functional
open import Functional.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type
open import Type.Size.Setoid

module _ {ℓ} where
  instance
    [≍]-reflexivity : Reflexivity(_≍_ {ℓ})
    Reflexivity.proof([≍]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-bijective ⦄

module _ {ℓ} where
  instance
    [≍]-symmetry : Symmetry(_≍_ {ℓ})
    Symmetry.proof([≍]-symmetry) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄)
      = [∃]-intro(inv-fn f ⦃ f-bijective ⦄) ⦃ [∧]-intro
          (inv-function{f = f} ⦃ f-function ⦄ ⦃ f-bijective ⦄)
          (inv-bijective{f = f} ⦃ f-function ⦄ ⦃ f-bijective ⦄)
        ⦄

-- module _ {ℓ} where
--   instance
--     [≍]-transitivity : Transitivity(_≍_ {ℓ})
--     Transitivity.proof([≍]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-bijective ⦄)
--       = [∃]-intro(g ∘ f) ⦃ [∧]-intro
--           ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
--           ([∘]-bijective {f = g}{g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄)
--         ⦄
