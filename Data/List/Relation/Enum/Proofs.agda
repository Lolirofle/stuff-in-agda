module Data.List.Relation.Enum.Proofs where

open import BidirectionalFunction
open import Data.List
open import Data.List.Functions
open import Data.List.Relation.Enum
open import Data.List.Relation.Membership.Proofs
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
import      Numeral.CoordinateVector.List as Vector
import      Numeral.Finite.Bound.Substitution as 𝕟
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Size.Finite using (FinitelyEnumerable)

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  enum-surjective-index : ∀{l} → Enumeration(l) → Surjective(index l)
  enum-surjective-index p = intro \{y} → [∃]-map-proof (symmetry(_≡_)) ([↔]-to-[→] [∈]-index-existence (p{y}))

  enum-is-finEnum : Enumerable(T) ↔ FinitelyEnumerable(T)
  enum-is-finEnum = [↔]-intro l r where
    l : Enumerable(T) ← FinitelyEnumerable(T)
    l ([∃]-intro d ⦃ [∃]-intro f ⦃ surj-f ⦄ ⦄) = [∃]-intro (Vector.list f) ⦃ coordVecList-proof{d} ⦄ where
      coordVecList-proof : ∀{d}{f} ⦃ surj : Surjective(f) ⦄ → Enumeration(Vector.list{d = d} f)
      coordVecList-proof{d = d}{f = f}{x} =
        let [∃]-intro i ⦃ p ⦄ = surjective(f) {x}
            i' = 𝕟.subst Vector.list-length-is-dim $ₗ i
        in [↔]-to-[←] [∈]-index-existence ([∃]-intro i' ⦃
          x                       🝖[ _≡_ ]-[ p ]-sym
          f(i)                    🝖[ _≡_ ]-[ Vector.list-index-is-proj {v = f}{n₁ = i'}{n₂ = i} (𝕟.subst-identity{n = i}) ]-sym
          index(Vector.list f) i' 🝖-end
        ⦄)

    r : Enumerable(T) → FinitelyEnumerable(T)
    r ([∃]-intro l ⦃ p ⦄) = [∃]-intro(length(l)) ⦃ [∃]-intro (index l) ⦃ enum-surjective-index p ⦄ ⦄
