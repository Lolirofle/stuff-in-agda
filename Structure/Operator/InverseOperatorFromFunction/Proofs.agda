module Structure.Operator.InverseOperatorFromFunction.Proofs where

open import Data.Tuple
import      Lang.Vars.Structure.Operator
open        Lang.Vars.Structure.Operator.Select
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.InverseOperatorFromFunction
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f : A → B
private variable _▫_ _▫⁻¹_ _△_ : A → B → C

module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} {inv : T → T} where
  open Lang.Vars.Structure.Operator.One ⦃ equiv = equiv ⦄ {_▫_ = _▫_} hiding (inv)
  private _▫⁻¹ₗ_ = invOpₗ(_▫_)(inv)
  private _▫⁻¹ᵣ_ = invOpᵣ(_▫_)(inv)

  invOpₗ-binaryOperator : let _ = op , select-func ⦃ equiv ⦄ ⦃ equiv ⦄ (inv)(func) in BinaryOperator(_▫⁻¹ₗ_)
  BinaryOperator.congruence invOpₗ-binaryOperator {x₁}{y₁}{x₂}{y₂} xy1 xy2 =
    (x₁ ▫⁻¹ₗ x₂)   🝖[ _≡_ ]-[]
    (inv(x₁) ▫ x₂) 🝖[ _≡_ ]-[ congruence₂(_▫_) (congruence₁(inv) xy1) xy2 ]
    (inv(y₁) ▫ y₂) 🝖[ _≡_ ]-[]
    (y₁ ▫⁻¹ₗ y₂)   🝖-end

  invOpᵣ-binaryOperator : let _ = op , select-func ⦃ equiv ⦄ ⦃ equiv ⦄ (inv)(func) in BinaryOperator(_▫⁻¹ᵣ_)
  BinaryOperator.congruence invOpᵣ-binaryOperator {x₁}{y₁}{x₂}{y₂} xy1 xy2 =
    (x₁ ▫⁻¹ᵣ x₂)   🝖[ _≡_ ]-[]
    (x₁ ▫ inv(x₂)) 🝖[ _≡_ ]-[ congruence₂(_▫_) xy1 (congruence₁(inv) xy2) ]
    (y₁ ▫ inv(y₂)) 🝖[ _≡_ ]-[]
    (y₁ ▫⁻¹ᵣ y₂)   🝖-end

  inverse-operatorₗ-by-involuting-inverse-propₗ : let _ = op , select-invol ⦃ equiv ⦄(inv)(invol) , select-invPropₗ(inv)(inverPropₗ) in InverseOperatorₗ(_▫⁻¹ₗ_)(_▫_)
  InverseOperatorₗ.proof (inverse-operatorₗ-by-involuting-inverse-propₗ) {x} {y} =
    x ▫ (inv x ▫ y)            🝖-[ congruence₂-₁(_▫_)((inv x ▫ y)) (involution(inv)) ]-sym
    inv(inv(x)) ▫ (inv x ▫ y)  🝖-[ inversePropₗ(_▫_)(inv) ]
    y                          🝖-end

  inverse-inverse-operatorₗ-by-inverse-propₗ : let _ = select-invPropₗ(inv)(inverPropₗ) in InverseOperatorₗ(_▫_)(_▫⁻¹ₗ_)
  InverseOperatorₗ.proof (inverse-inverse-operatorₗ-by-inverse-propₗ) {x} {y} = inversePropₗ(_▫_)(inv)

  inverse-operatorᵣ-by-involuting-inverse-propᵣ : let _ = op , select-invol ⦃ equiv ⦄(inv)(invol) , select-invPropᵣ(inv)(inverPropᵣ) in InverseOperatorᵣ(invOpᵣ(_▫_)(inv))(_▫_)
  InverseOperatorᵣ.proof (inverse-operatorᵣ-by-involuting-inverse-propᵣ) {x} {y} =
    (x ▫ inv y) ▫ y           🝖-[ congruence₂-₂(_▫_)((x ▫ inv y)) (involution(inv)) ]-sym
    (x ▫ inv y) ▫ inv(inv(y)) 🝖-[ inversePropᵣ(_▫_)(inv) ]
    x                         🝖-end

  inverse-inverse-operatorᵣ-by-inverse-propᵣ : let _ = select-invPropᵣ(inv)(inverPropᵣ) in InverseOperatorᵣ(_▫_)(_▫⁻¹ᵣ_)
  InverseOperatorᵣ.proof (inverse-inverse-operatorᵣ-by-inverse-propᵣ) {x} {y} = inversePropᵣ(_▫_)(inv)

  inverse-operator-eq-by-comm : let _ = comm in (∀{x y} → (x ▫⁻¹ₗ y ≡ y ▫⁻¹ᵣ x))
  inverse-operator-eq-by-comm = commutativity(_)

  inverse-operatorₗ-identityₗ-by-identity-inverseFunc : let _ = op , select-id(id)(ident) , select-inv(id)(ident)(inv)(inver) in Identityₗ(_▫⁻¹ₗ_)(id)
  Identityₗ.proof (inverse-operatorₗ-identityₗ-by-identity-inverseFunc {id = id}) {x} =
    id ▫⁻¹ₗ x   🝖[ _≡_ ]-[]
    inv(id) ▫ x 🝖[ _≡_ ]-[ congruence₂-₁(_▫_)(x) One.inv-of-id ]
    id ▫ x      🝖[ _≡_ ]-[ identityₗ(_▫_)(id) ]
    x           🝖-end

  inverse-operatorᵣ-identityᵣ-by-identity-inverseFunc : let _ = op , select-id(id)(ident) , select-inv(id)(ident)(inv)(inver) in Identityᵣ(_▫⁻¹ᵣ_)(id)
  Identityᵣ.proof (inverse-operatorᵣ-identityᵣ-by-identity-inverseFunc {id = id}) {x} =
    x ▫⁻¹ᵣ id   🝖[ _≡_ ]-[]
    x ▫ inv(id) 🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x) One.inv-of-id ]
    x ▫ id      🝖[ _≡_ ]-[ identityᵣ(_▫_)(id) ]
    x           🝖-end

  module _ {id : T} {_△_ : T → T → T} where
    open Lang.Vars.Structure.Operator.OneTypeTwoOp ⦃ equiv = equiv ⦄ {_▫₁_ = _△_} {_▫₂_ = _▫_} using (op₁ ; op₂ ; assoc₂ ; distriₗ ; distriᵣ ; absorbₗ₁ ; absorbᵣ₁ ; ident₂ ; inver₂)

    invᵣ-distributivityₗ : let _ = op₁ , op₂ , assoc₂ , distriₗ , select-inv(id)(ident₂)(inv)(inver₂) , select-absᵣ(id)(absorbᵣ₁) in Distributivityₗ(_△_)(_▫⁻¹ᵣ_)
    Distributivityₗ.proof invᵣ-distributivityₗ {x}{y}{z} =
      (x △ (y ▫⁻¹ᵣ z))         🝖[ _≡_ ]-[]
      (x △ (y ▫ inv(z)))       🝖[ _≡_ ]-[ distributivityₗ(_△_)(_▫_) ]
      ((x △ y) ▫ (x △ inv(z))) 🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x △ y) OneTypeTwoOp.distributeᵣ-inv ]
      ((x △ y) ▫ inv(x △ z))   🝖[ _≡_ ]-[]
      ((x △ y) ▫⁻¹ᵣ (x △ z))   🝖-end

    invᵣ-distributivityᵣ : let _ = op₁ , op₂ , assoc₂ , distriᵣ , select-inv(id)(ident₂)(inv)(inver₂) , select-absₗ(id)(absorbₗ₁) in Distributivityᵣ(_△_)(_▫⁻¹ᵣ_)
    Distributivityᵣ.proof invᵣ-distributivityᵣ {x}{y}{z} =
      ((x ▫⁻¹ᵣ y) △ z)         🝖[ _≡_ ]-[]
      ((x ▫ inv(y)) △ z)       🝖[ _≡_ ]-[ distributivityᵣ(_△_)(_▫_) ]
      ((x △ z) ▫ (inv(y) △ z)) 🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x △ z) OneTypeTwoOp.distributeₗ-inv ]
      ((x △ z) ▫ inv(y △ z))   🝖[ _≡_ ]-[]
      ((x △ z) ▫⁻¹ᵣ (y △ z))   🝖-end
