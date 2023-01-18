module Sets.ImageSet where

open import Data
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)
open import Type
open import Type.Dependent.Sigma

private variable ℓ ℓₑ ℓᵢ ℓᵢ₁ ℓᵢ₂ ℓᵢ₃ ℓᵢₑ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T X Y Z : Type{ℓ}

record ImageSet {ℓᵢ ℓ} (T : Type{ℓ}) : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ ℓ} where
  constructor intro
  field
    {Index} : Type{ℓᵢ}
    elem : Index → T
open ImageSet using (Index ; elem) public

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  _∈_ : T → ImageSet{ℓᵢ}(T) → Stmt
  a ∈ A = ∃(i ↦ a ≡ₛ elem A(i))

  open import Data.Proofs
  open import Function.Proofs
  open import Logic.Propositional.Theorems
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  {-
  instance
    ImageSet-equiv : Equiv(ImageSet{ℓᵢ}(T))
    ImageSet-equiv = intro(_≡_) ⦃ [≡]-equivalence ⦄
  -}

  instance
    [∈]-unaryOperatorₗ : ∀{A : ImageSet{ℓᵢ}(T)} → UnaryRelator(_∈ A)
    [∈]-unaryOperatorₗ = UnaryRelator-introᵣ \xy ([∃]-intro i ⦃ p ⦄) → [∃]-intro i ⦃ symmetry(_≡ₛ_) xy 🝖 p ⦄
