
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
