module Sets.Setoid.Proofs{ℓₗ} where

import Lvl
open import Functional
import      Logic.Propositional
open import Sets.Setoid{ℓₗ}
import      Structure.Relator.Equivalence
import      Structure.Relator.Properties

module _ {ℓₒ₁}{ℓₒ₂} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  open Structure.Relator.Properties{ℓₗ}{ℓₒ₂}

  const-is-function : ∀{T₁ : Set(ℓₒ₁)} → ⦃ _ : Equiv(T₁) ⦄
                    → ∀{T₂ : Set(ℓₒ₂)} → ⦃ _ : Equiv(T₂) ⦄
                    → ∀{x : T₂}
                    → Function {_}{_} {T₁}{T₂} (const x)
  Function.congruence(const-is-function {T₁}{T₂} ⦃ equiv₂ ⦄ {x}) = const(reflexivity)

  {-
  inverse-is-function : ∀{T₁ : Set(ℓₒ₁)} → ⦃ _ : Equiv(T₁) ⦄
                      → ∀{T₂ : Set(ℓₒ₂)} → ⦃ _ : Equiv(T₂) ⦄
                      → ∀{f : T₁ → T₂}
                      → Function(f) → Function(inv f)

  -}

module _ {ℓₒ} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ}
  open Structure.Relator.Properties{ℓₗ}{ℓₒ}

  instance
    id-is-function : ∀{T : Set(ℓₒ)} → ⦃ _ : Equiv(T) ⦄ → Function(id{_}{T})
    Function.congruence(id-is-function) = id

module _ {ℓₒ₁}{ℓₒ₂}{ℓₒ₃} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃}
  open Structure.Relator.Properties{ℓₗ}

  instance
    composition-is-function : ∀{T₁ : Set(ℓₒ₁)} → ⦃ _ : Equiv(T₁) ⦄
                            → ∀{T₂ : Set(ℓₒ₂)} → ⦃ _ : Equiv(T₂) ⦄
                            → ∀{T₃ : Set(ℓₒ₃)} → ⦃ _ : Equiv(T₃) ⦄
                            → ∀{f : T₂ → T₃}{g : T₁ → T₂}
                            → ⦃ _ : Function(f) ⦄ → ⦃ _ : Function(g) ⦄ → Function(f ∘ g)
    Function.congruence(composition-is-function {_}{_}{_} {f}{g} ⦃ f-proof ⦄ ⦃ g-proof ⦄) {x}{y} =
      (Function.congruence(f-proof) {g(x)}{g(y)}) ∘ (Function.congruence(g-proof) {x}{y})
