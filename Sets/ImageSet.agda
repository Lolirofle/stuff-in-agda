module Sets.ImageSet where

open import Data
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_)
open import Type
open import Type.Dependent

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
  open import Structure.Container.SetLike
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  instance
    ImageSet-setLike : SetLike(_∈_ {ℓᵢ})
    SetLike._⊆_ ImageSet-setLike A B = ∀{x} → (x ∈ A) → (x ∈ B)
    SetLike._≡_ ImageSet-setLike A B = ∀{x} → (x ∈ A) ↔ (x ∈ B)
    SetLike.[⊆]-membership ImageSet-setLike = [↔]-reflexivity
    SetLike.[≡]-membership ImageSet-setLike = [↔]-reflexivity
  private open module ImageSet-SetLike {ℓᵢ} = SetLike(ImageSet-setLike{ℓᵢ}) public
  open import Structure.Container.SetLike.Proofs using ([⊇]-membership) public
  module _ {ℓᵢ} where
    instance [⊆]-binaryRelator  = Structure.Container.SetLike.Proofs.[⊆]-binaryRelator  ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [⊇]-binaryRelator  = Structure.Container.SetLike.Proofs.[⊇]-binaryRelator  ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-to-[⊆]         = Structure.Container.SetLike.Proofs.[≡]-to-[⊆]         ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-to-[⊇]         = Structure.Container.SetLike.Proofs.[≡]-to-[⊇]         ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [⊆]-reflexivity    = Structure.Container.SetLike.Proofs.[⊆]-reflexivity    ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [⊆]-antisymmetry   = Structure.Container.SetLike.Proofs.[⊆]-antisymmetry   ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [⊆]-transitivity   = Structure.Container.SetLike.Proofs.[⊆]-transitivity   ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [⊆]-partialOrder   = Structure.Container.SetLike.Proofs.[⊆]-partialOrder   ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-reflexivity    = Structure.Container.SetLike.Proofs.[≡]-reflexivity    ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-symmetry       = Structure.Container.SetLike.Proofs.[≡]-symmetry       ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-transitivity   = Structure.Container.SetLike.Proofs.[≡]-transitivity   ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [≡]-equivalence    = Structure.Container.SetLike.Proofs.[≡]-equivalence    ⦃ ImageSet-setLike{ℓᵢ} ⦄
    instance [∈]-unaryOperatorᵣ = Structure.Container.SetLike.Proofs.[∈]-unaryOperatorᵣ ⦃ ImageSet-setLike{ℓᵢ} ⦄

  instance
    ImageSet-equiv : Equiv(ImageSet{ℓᵢ}(T))
    ImageSet-equiv = intro(_≡_) ⦃ [≡]-equivalence ⦄

  instance
    [∈]-unaryOperatorₗ : ∀{A : ImageSet{ℓᵢ}(T)} → UnaryRelator(_∈ A)
    UnaryRelator.substitution [∈]-unaryOperatorₗ xy ([∃]-intro i ⦃ p ⦄) = [∃]-intro i ⦃ symmetry(_≡ₛ_) xy 🝖 p ⦄
