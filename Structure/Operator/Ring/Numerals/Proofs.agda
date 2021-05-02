open import Structure.Operator.Ring
open import Structure.Setoid
open import Type

module Structure.Operator.Ring.Numerals.Proofs
  {ℓF ℓₑF}
  {F : Type{ℓF}}
  ⦃ equiv-F : Equiv{ℓₑF}(F) ⦄
  {_+_}{_⋅_}
  ⦃ ring : Ring(_+_)(_⋅_) ⦄
  where

open import Functional
open import Numeral.Integer as ℤ using (ℤ)
open import Numeral.Natural as ℕ using (ℕ)
open import Structure.Operator.Ring.Numerals
open import Syntax.Number
open import Syntax.Transitivity

open Ring(ring)

module _ where
  open import Function.Iteration
  open import Logic
  open import Logic.Classical
  open import Numeral.Natural.Induction
  open import Relator.Equals renaming (_≡_ to _≡ᵢ_ ; [≡]-intro to intro) using()
  open import Structure.Function
  open import Structure.Operator
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Structure.Operator.Ring.Proofs

  instance
    𝐒-function : Function(𝐒)
    𝐒-function = BinaryOperator.left [+]-binary-operator

  instance
    𝐏-function : Function(𝐏)
    𝐏-function = BinaryOperator.left [+]-binary-operator

  from-ℕ-is-𝐒-iteration : ∀{n} → (from-ℕ n ≡ (𝐒 ^ n)(𝟎))
  from-ℕ-is-𝐒-iteration {ℕ.𝟎}        = reflexivity(_≡_)
  from-ℕ-is-𝐒-iteration {ℕ.𝟏}        = symmetry(_≡_) (identityₗ(_+_)(𝟎))
  from-ℕ-is-𝐒-iteration {ℕ.𝐒(ℕ.𝐒 n)} = congruence₁(𝐒) (from-ℕ-is-𝐒-iteration {ℕ.𝐒(n)})

  [⋅]-distributeᵣ-over-𝐒-iteration : ∀{n}{x} → ((𝐒 ^ n)(𝟎) ⋅ x ≡ ((_+ x) ^ n)(𝟎))
  [⋅]-distributeᵣ-over-𝐒-iteration {ℕ.𝟎}{x} =
    ((𝐒 ^ ℕ.𝟎)(𝟎) ⋅ x) 🝖[ _≡_ ]-[]
    (id(𝟎) ⋅ x)        🝖[ _≡_ ]-[]
    (𝟎 ⋅ x)            🝖[ _≡_ ]-[ absorberₗ(_⋅_)(𝟎) ]
    𝟎                  🝖[ _≡_ ]-[]
    id(𝟎)              🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝟎)(𝟎)  🝖-end
  [⋅]-distributeᵣ-over-𝐒-iteration {ℕ.𝐒(n)}{x} =
    ((𝐒 ^ ℕ.𝐒(n))(𝟎) ⋅ x)        🝖[ _≡_ ]-[]
    (𝐒((𝐒 ^ n)(𝟎)) ⋅ x)          🝖[ _≡_ ]-[]
    (((𝐒 ^ n)(𝟎) + 𝟏) ⋅ x)       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) ]
    (((𝐒 ^ n)(𝟎) ⋅ x) + (𝟏 ⋅ x)) 🝖[ _≡_ ]-[ congruence₂(_+_) ([⋅]-distributeᵣ-over-𝐒-iteration {n}{x}) (identityₗ(_⋅_)(𝟏)) ]
    ((_+ x) ^ n)(𝟎) + x          🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝐒(n))(𝟎)         🝖-end

  [⋅]-distributeₗ-over-𝐒-iteration : ∀{n}{x} → (x ⋅ (𝐒 ^ n)(𝟎) ≡ ((_+ x) ^ n)(𝟎))
  [⋅]-distributeₗ-over-𝐒-iteration {ℕ.𝟎}{x} =
    (x ⋅ (𝐒 ^ ℕ.𝟎)(𝟎)) 🝖[ _≡_ ]-[]
    (x ⋅ id(𝟎))        🝖[ _≡_ ]-[]
    (x ⋅ 𝟎)            🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
    𝟎                  🝖[ _≡_ ]-[]
    id(𝟎)              🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝟎)(𝟎)  🝖-end
  [⋅]-distributeₗ-over-𝐒-iteration {ℕ.𝐒(n)}{x} =
    (x ⋅ (𝐒 ^ ℕ.𝐒(n))(𝟎))        🝖[ _≡_ ]-[]
    (x ⋅ 𝐒((𝐒 ^ n)(𝟎)))          🝖[ _≡_ ]-[]
    (x ⋅ ((𝐒 ^ n)(𝟎) + 𝟏))       🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]
    ((x ⋅ (𝐒 ^ n)(𝟎)) + (x ⋅ 𝟏)) 🝖[ _≡_ ]-[ congruence₂(_+_) ([⋅]-distributeₗ-over-𝐒-iteration {n}{x}) (identityᵣ(_⋅_)(𝟏)) ]
    ((_+ x) ^ n)(𝟎) + x          🝖[ _≡_ ]-[]
    ((_+ x) ^ ℕ.𝐒(n))(𝟎)         🝖-end
