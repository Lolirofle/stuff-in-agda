module Structure.Type.Dependent.Function.Properties where

open import Functional.Instance
open import Logic.Predicate
import      Lvl
open import Type
open import Structure.Setoid
open import Structure.Type.Dependent.Function

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}

module _
  (_⟶_ : (A : Type{ℓ₁}) → (A → Type{ℓ₂}) → Type{ℓ₃})
  ⦃ equiv-func : ∀{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} → Equiv{ℓₑ}(A ⟶ B) ⦄
  ⦃ func : FunctionType(_⟶_) ⦄
  where

  module Names where
    module _ {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ (f g : A ⟶ B) where
      FunctionExtensionalityOn = (∀{x : A} → (f $ x) ≡ (g $ x)) → (f ≡ g)
    module _ (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ where
      FunctionExtensionality = ∀²(FunctionExtensionalityOn{A = A}{B = B})

  module _ {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ (f g : A ⟶ B) where
    record FunctionExtensionalityOn : Type{ℓ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ} where
      constructor intro
      field proof : Names.FunctionExtensionalityOn f g
    functionExtensionalityOn = inferArg FunctionExtensionalityOn.proof

  module _ (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ where
    FunctionExtensionality = ∀²(FunctionExtensionalityOn{A = A}{B = B})
    functionExtensionality : ⦃ funcExt : FunctionExtensionality ⦄ → Names.FunctionExtensionality(A)(B)
    functionExtensionality {f}{g} = functionExtensionalityOn f g
