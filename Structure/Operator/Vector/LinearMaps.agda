module Structure.Operator.Vector.LinearMaps where

open import Functional
open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓᵥ₁ ℓᵥ₂ ℓᵥ₃ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable f g : Vₗ → Vᵣ

open VectorSpace ⦃ … ⦄

module _
  ⦃ equiv-Vₗ : Equiv{ℓᵥₑₗ}(Vₗ) ⦄
  ⦃ equiv-Vᵣ : Equiv{ℓᵥₑᵣ}(Vᵣ) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpaceₗ : VectorSpace{V = Vₗ}{S = S}(_+ᵥₗ_)(_⋅ₛᵥₗ_)(_+ₛ_)(_⋅ₛ_))
  (vectorSpaceᵣ : VectorSpace{V = Vᵣ}{S = S}(_+ᵥᵣ_)(_⋅ₛᵥᵣ_)(_+ₛ_)(_⋅ₛ_))
  where

  instance _ = vectorSpaceₗ
  instance _ = vectorSpaceᵣ

  zero : LinearMap(vectorSpaceₗ)(vectorSpaceᵣ)(const 𝟎ᵥ)
  Preserving.proof (LinearMap.preserves-[+ᵥ] zero) {x} {y} =
    const 𝟎ᵥ (x +ᵥₗ y)            🝖[ _≡_ ]-[]
    𝟎ᵥ                            🝖[ _≡_ ]-[ identityₗ(_+ᵥᵣ_)(𝟎ᵥ) ]-sym
    𝟎ᵥ +ᵥᵣ 𝟎ᵥ                     🝖[ _≡_ ]-[]
    (const 𝟎ᵥ x) +ᵥᵣ (const 𝟎ᵥ y) 🝖-end
  Preserving.proof (LinearMap.preserves-[⋅ₛᵥ] zero {s}) {x} =
    const 𝟎ᵥ (s ⋅ₛᵥₗ x) 🝖[ _≡_ ]-[]
    𝟎ᵥ                  🝖[ _≡_ ]-[ [⋅ₛᵥ]-absorberᵣ ]-sym
    s ⋅ₛᵥᵣ 𝟎ᵥ           🝖[ _≡_ ]-[]
    s ⋅ₛᵥᵣ (const 𝟎ᵥ x) 🝖-end

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_))
  where

  instance _ = vectorSpace

  identity : LinearOperator(vectorSpace)(id)
  Preserving.proof (LinearMap.preserves-[+ᵥ]  identity) = reflexivity(_≡_)
  Preserving.proof (LinearMap.preserves-[⋅ₛᵥ] identity) = reflexivity(_≡_)

module _
  ⦃ equiv-V₁ : Equiv{ℓᵥₑ₁}(V₁) ⦄
  ⦃ equiv-V₂ : Equiv{ℓᵥₑ₂}(V₂) ⦄
  ⦃ equiv-V₂ : Equiv{ℓᵥₑ₃}(V₃) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace₁ : VectorSpace{V = V₁}{S = S}(_+ᵥ₁_)(_⋅ₛᵥ₁_)(_+ₛ_)(_⋅ₛ_))
  (vectorSpace₂ : VectorSpace{V = V₂}{S = S}(_+ᵥ₂_)(_⋅ₛᵥ₂_)(_+ₛ_)(_⋅ₛ_))
  (vectorSpace₃ : VectorSpace{V = V₃}{S = S}(_+ᵥ₃_)(_⋅ₛᵥ₃_)(_+ₛ_)(_⋅ₛ_))
  where

  instance _ = vectorSpace₁
  instance _ = vectorSpace₂
  instance _ = vectorSpace₃

  compose : LinearMap(vectorSpace₂)(vectorSpace₃)(f) → LinearMap(vectorSpace₁)(vectorSpace₂)(g) → LinearMap(vectorSpace₁)(vectorSpace₃)(f ∘ g)
  LinearMap.function-f (compose {f} {g} F G) = [∘]-function {f = f}{g = g}
  Preserving.proof (LinearMap.preserves-[+ᵥ] (compose {f} {g} F G)) {x}{y} =
    (f ∘ g)(x +ᵥ₁ y)          🝖[ _≡_ ]-[]
    f(g(x +ᵥ₁ y))             🝖[ _≡_ ]-[ congruence₁(f) (preserving₂(g) (_+ᵥ₁_)(_+ᵥ₂_)) ]
    f(g(x) +ᵥ₂ g(y))          🝖[ _≡_ ]-[ preserving₂(f) (_+ᵥ₂_)(_+ᵥ₃_) ]
    f(g(x)) +ᵥ₃ f(g(y))       🝖[ _≡_ ]-[]
    (f ∘ g)(x) +ᵥ₃ (f ∘ g)(y) 🝖-end
  Preserving.proof (LinearMap.preserves-[⋅ₛᵥ] (compose {f} {g} F G) {s}) {v} =
    (f ∘ g) (s ⋅ₛᵥ₁ v) 🝖[ _≡_ ]-[]
    f(g(s ⋅ₛᵥ₁ v))     🝖[ _≡_ ]-[ congruence₁(f) (preserving₁(g) (s ⋅ₛᵥ₁_)(s ⋅ₛᵥ₂_)) ]
    f(s ⋅ₛᵥ₂ g(v))     🝖[ _≡_ ]-[ preserving₁(f) (s ⋅ₛᵥ₂_)(s ⋅ₛᵥ₃_) ]
    s ⋅ₛᵥ₃ f(g(v))     🝖[ _≡_ ]-[]
    s ⋅ₛᵥ₃ (f ∘ g)(v)  🝖-end

module _ ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ {_+ₛ_ _⋅ₛ_ : S → S → S} where
  private variable A B C : VectorSpaceVObject {ℓᵥ}{_}{ℓᵥₑ}{ℓₛₑ} ⦃ equiv-S ⦄ (_+ₛ_)(_⋅ₛ_)
  open VectorSpaceVObject hiding (𝟎ᵥ)

  𝟎ˡⁱⁿᵉᵃʳᵐᵃᵖ : A →ˡⁱⁿᵉᵃʳᵐᵃᵖ B
  𝟎ˡⁱⁿᵉᵃʳᵐᵃᵖ {A = A}{B = B} = [∃]-intro (const 𝟎ᵥ) ⦃ zero (vectorSpace A) (vectorSpace B) ⦄

  idˡⁱⁿᵉᵃʳᵐᵃᵖ : A →ˡⁱⁿᵉᵃʳᵐᵃᵖ A
  idˡⁱⁿᵉᵃʳᵐᵃᵖ {A = A} = [∃]-intro id ⦃ identity(vectorSpace A) ⦄

  _∘ˡⁱⁿᵉᵃʳᵐᵃᵖ_ : let _ = A in (B →ˡⁱⁿᵉᵃʳᵐᵃᵖ C) → (A →ˡⁱⁿᵉᵃʳᵐᵃᵖ B) → (A →ˡⁱⁿᵉᵃʳᵐᵃᵖ C)
  _∘ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {A = A}{B = B}{C = C} ([∃]-intro f ⦃ linmap-f ⦄) ([∃]-intro g ⦃ linmap-g ⦄) = [∃]-intro (f ∘ g) ⦃ compose (vectorSpace A) (vectorSpace B) (vectorSpace C) linmap-f linmap-g ⦄
