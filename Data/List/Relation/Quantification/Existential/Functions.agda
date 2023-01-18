module Data.List.Relation.Quantification.Existential.Functions where

open import Data.List
open import Data.List.Functions as List using (length)
open import Data.List.Relation.Quantification
open import Logic
import      Lvl
open import Numeral.Finite
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable P : T → Stmt{ℓ}

module _ {T : Type{ℓ}} where
  private variable l l₁ l₂ : List(T)

  -- The index/position in the list where the existing element is.
  index : ExistsElement P(l) → 𝕟(length l)
  index(• _) = 𝟎
  index(⊰ e) = 𝐒(index e)

  -- The existing element, the witness of the existential proof.
  witness : ExistsElement P(l) → T
  witness(•_ {x} _) = x
  witness(⊰ e)      = witness e

  module _ where
    open import Data.List.Relation.Membership using (_∈_)
    open import Logic.Propositional.Equiv
    open import Relator.Equals
    open import Relator.Equals.Proofs.Equiv
    open import Structure.Relator

    witness-index : ∀{e : ExistsElement P(l)} → (witness e ≡ List.index l (index e))
    witness-index{e = • _} = [≡]-intro
    witness-index{e = ⊰ e} = witness-index{e = e}

    witness-correctness : ∀{e : ExistsElement P(l)} → P(witness e)
    witness-correctness{e = • px} = px
    witness-correctness{e = ⊰ e}  = witness-correctness{e = e}

    witness-membership : ∀{e : ExistsElement P(l)} → (witness e ∈ l)
    witness-membership{e = • x} = • [≡]-intro
    witness-membership{e = ⊰ e} = ⊰ witness-membership{e = e}

    index-correctness : ∀{e : ExistsElement P(l)} → P(List.index l (index e))
    index-correctness{P = P}{e = e} = substitute₁ᵣ(P) (witness-index{e = e}) (witness-correctness{e = e})
