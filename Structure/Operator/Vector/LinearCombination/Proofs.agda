import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid
open import Type

module Structure.Operator.Vector.LinearCombination.Proofs
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

import      Lvl
open import Function.Equals
open import Logic.Predicate
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Structure.Function.Multi
import      Structure.Function.Names as Names
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Operator.Vector.LinearCombination ⦃ vectorSpace = vectorSpace ⦄
open import Structure.Operator.Vector.Proofs
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Number
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₗ : Lvl.Level
private variable n n₁ n₂ : ℕ
private variable i j k : 𝕟(n)
private variable vf vf₁ vf₂ : Vec(n)(V)
private variable sf sf₁ sf₂ : Vec(n)(S)

instance
  linearCombination-binaryOperator : BinaryOperator(linearCombination{n})
  linearCombination-binaryOperator = intro p where
    p : Names.Congruence₂(linearCombination{n})
    p {𝟎}       {vf₁} {vf₂} {sf₁} {sf₂} (intro vfeq) (intro sfeq) = reflexivity(_≡_)
    p {𝐒(𝟎)}    {vf₁} {vf₂} {sf₁} {sf₂} (intro vfeq) (intro sfeq) = congruence₂(_⋅ₛᵥ_) sfeq vfeq
    p {𝐒(𝐒(n))} {vf₁} {vf₂} {sf₁} {sf₂} (intro vfeq) (intro sfeq) =
      (sf₁(𝟎) ⋅ₛᵥ vf₁(𝟎)) +ᵥ linearCombination(Vec.tail vf₁) (Vec.tail sf₁) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (congruence₂(_⋅ₛᵥ_) sfeq vfeq) (p {𝐒(n)} (intro vfeq) (intro sfeq)) ]
      (sf₂(𝟎) ⋅ₛᵥ vf₂(𝟎)) +ᵥ linearCombination(Vec.tail vf₂) (Vec.tail sf₂) 🝖-end

instance
  linearCombination-scalar-preserves-[+] : Preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_)
  linearCombination-scalar-preserves-[+] {vf = vf} = intro(p{vf = vf}) where
    p : ∀{n}{vf : Vec(n)(V)} → Names.Preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_)
    p {𝟎}{vf} {sf₁} {sf₂} =
      𝟎ᵥ       🝖[ _≡_ ]-[ identityₗ(_+ᵥ_)(𝟎ᵥ) ]-sym
      𝟎ᵥ +ᵥ 𝟎ᵥ 🝖-end
    p {𝐒(𝟎)}{vf} {sf₁} {sf₂} =
      (Vec.map₂(_+ₛ_) sf₁ sf₂ 𝟎) ⋅ₛᵥ vf(𝟎)     🝖[ _≡_ ]-[]
      (sf₁(𝟎) +ₛ sf₂(𝟎)) ⋅ₛᵥ vf(𝟎)             🝖[ _≡_ ]-[ preserving₂(_⋅ₛᵥ _)(_+ₛ_)(_+ᵥ_) ]
      (sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (sf₂(𝟎) ⋅ₛᵥ vf(𝟎)) 🝖-end
    p {𝐒(𝐒(n))}{vf} {sf₁} {sf₂} =
      ((Vec.map₂(_+ₛ_) sf₁ sf₂ 𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail(Vec.map₂(_+ₛ_) sf₁ sf₂)))                                                🝖[ _≡_ ]-[]
      ((sf₁(𝟎) +ₛ sf₂(𝟎)) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail(Vec.map₂(_+ₛ_) sf₁ sf₂)))                                                        🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (preserving₂(_⋅ₛᵥ _)(_+ₛ_)(_+ᵥ_)) (p {𝐒(n)}{Vec.tail vf} {Vec.tail sf₁} {Vec.tail sf₂}) ]
      ((sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (sf₂(𝟎) ⋅ₛᵥ vf(𝟎))) +ᵥ ((linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₁)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₂)))   🝖[ _≡_ ]-[ One.associate-commute4 (commutativity(_+ᵥ_)) ]
      (((sf₁(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₁))) +ᵥ ((sf₂(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination {𝐒(n)} (Vec.tail vf) (Vec.tail sf₂)))) 🝖-end

instance
  linearCombination-scalar-preserves-[⋅] : ∀{s} → Preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_)
  linearCombination-scalar-preserves-[⋅] {vf = vf} {s = s} = intro(p{vf = vf}) where
    p : ∀{n}{vf : Vec(n)(V)} → Names.Preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_)
    p {𝟎} {vf} {sf} =
      𝟎ᵥ       🝖[ _≡_ ]-[ [⋅ₛᵥ]-absorberᵣ ]-sym
      s ⋅ₛᵥ 𝟎ᵥ 🝖-end
    p {𝐒(𝟎)} {vf} {sf} =
      (s ⋅ₛ sf(𝟎)) ⋅ₛᵥ vf(𝟎)  🝖[ _≡_ ]-[ preserving₁(_⋅ₛᵥ _)(_ ⋅ₛ_)(_ ⋅ₛᵥ_) ]
      s ⋅ₛᵥ (sf(𝟎) ⋅ₛᵥ vf(𝟎)) 🝖-end
    p {𝐒(𝐒(n))} {vf} {sf} =
      linearCombination vf (Vec.map (s ⋅ₛ_) sf)                                                     🝖[ _≡_ ]-[]
      ((s ⋅ₛ sf(𝟎)) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination (Vec.tail vf) (Vec.map (s ⋅ₛ_) (Vec.tail sf))) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binary-operator ⦄ (preserving₁(_⋅ₛᵥ _)(_ ⋅ₛ_)(_ ⋅ₛᵥ_)) (p {𝐒(n)} {Vec.tail vf} {Vec.tail sf}) ]
      (s ⋅ₛᵥ (sf(𝟎) ⋅ₛᵥ vf(𝟎))) +ᵥ (s ⋅ₛᵥ (linearCombination (Vec.tail vf) (Vec.tail sf)))          🝖[ _≡_ ]-[ distributivityₗ(_⋅ₛᵥ_)(_+ᵥ_) ]-sym
      s ⋅ₛᵥ ((sf(𝟎) ⋅ₛᵥ vf(𝟎)) +ᵥ (linearCombination (Vec.tail vf) (Vec.tail sf)))                  🝖[ _≡_ ]-[]
      s ⋅ₛᵥ (linearCombination vf sf)                                                               🝖-end

-- linearCombination-of-unit : linearCombination vf (Vec.fill 𝟏ₛ) ≡ (foldᵣ(_+_) 𝟎ᵥ vf)
postulate linearCombination-of-indexProject : (linearCombination vf (Vec.indexProject i 𝟏ₛ 𝟎ₛ) ≡ vf(i))
