module Structure.Operator.StarAlgebra where

open import Logic.Predicate
import      Lvl
open import Structure.Operator
open import Structure.Operator.Algebra
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator.Vector
open import Structure.Operator.Vector.BilinearOperator
open import Structure.Operator.Vector.LinearMap
open import Structure.Setoid
open import Type

open import Structure.Function.Domain
open import Structure.Operator.Ring.Homomorphism

module _
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ᵥ_ : V → V → V)
  (_⋆ᵥ : V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  (_⋆ₛ : S → S)
  {ℓᵥₙ₀ ℓₛₙ₀}
  where

  record ⋆-algebra : Type{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ Lvl.⊔ Lvl.𝐒(ℓᵥₙ₀ Lvl.⊔ ℓₛₙ₀)} where
    constructor intro
    field
      ⦃ algebra ⦄ : Algebra(_+ᵥ_)(_⋅ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓᵥₙ₀}{ℓₛₙ₀}
    open Algebra(algebra) public

    field
      ⦃ [⋅ᵥ]-binaryOperator ⦄   : BinaryOperator(_⋅ᵥ_)
      -- TODO: Do not require assoc and ident
      ⦃ [⋅ᵥ]-associativity ⦄    : Associativity(_⋅ᵥ_)
      ⦃ [⋅ᵥ]-identity ⦄         : ∃(Identity(_⋅ᵥ_))

      ⦃ [⋆ₛ]-involution ⦄       : Involution(_⋆ₛ)
      ⦃ [⋆ₛ]-antihomomorphism ⦄ : Antihomomorphism scalarRing scalarRing (_⋆ₛ)

      ⦃ [⋆ᵥ]-involution ⦄       : Involution(_⋆ᵥ)
      ⦃ [⋆ᵥ]-antihomomorphism ⦄ : Antihomomorphism vectorRing vectorRing (_⋆ᵥ)

      [⋆]-preserves-[⋅ₛᵥ] : ∀{s}{v} → ((s ⋅ₛᵥ v)⋆ᵥ ≡ (s ⋆ₛ) ⋅ₛᵥ (v ⋆ᵥ))

    instance
      [⋅ᵥ]-monoid : Monoid(_⋅ᵥ_)
      [⋅ᵥ]-monoid = record{}
    open Monoid([⋅ᵥ]-monoid)
      using()
      renaming(
        id to 𝟏ᵥ ;
        identityₗ to [⋅ᵥ]-identityₗ ;
        identityᵣ to [⋅ᵥ]-identityᵣ
      ) public

open import Data.Tuple
open import Data.Tuple.Equivalence
open import Structure.Function
-- open import Structure.Operator.Ring.Proofs
open import Syntax.Transitivity

private variable ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ ℓᵥₙ₀ ℓₛₙ₀ : Lvl.Level
private variable V : Type{ℓᵥ}
private variable S : Type{ℓₛ}
private variable _+ᵥ_ _⋅ᵥ_ : V → V → V
private variable _⋆ᵥ : V → V
private variable _⋅ₛᵥ_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable _⋆ₛ : S → S

-- Also called: General Cayley–Dickson construction.
-- Source: https://en.wikipedia.org/wiki/Cayley%E2%80%93Dickson_construction#General_Cayley%E2%80%93Dickson_construction (20210610)
module ComplexConstruction
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  ⦃ starAlgebra : ⋆-algebra ⦃ equiv-V ⦄ ⦃ equiv-S ⦄ (_+ᵥ_)(_⋅ᵥ_)(_⋆ᵥ)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)(_⋆ₛ) {ℓᵥₙ₀}{ℓₛₙ₀} ⦄
  where

  open ⋆-algebra(starAlgebra)

  Vector = V ⨯ V

  _+_ : Vector → Vector → Vector
  (x₁ , x₂) + (y₁ , y₂) = ((x₁ +ᵥ y₁) , (x₂ +ᵥ y₂))
  
  _⋅_ : Vector → Vector → Vector
  (x₁ , x₂) ⋅ (y₁ , y₂) = (((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂)) , ((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))
  
  _⋆ : Vector → Vector
  (x₁ , x₂)⋆ = ((x₁ ⋆ᵥ) , (−ᵥ x₂))

  𝟏 : Vector
  𝟏 = (𝟏ᵥ , 𝟎ᵥ)

  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  left (Identityₗ.proof [⋅]-identityₗ {x₁ , x₂}) =
    (𝟏ᵥ ⋅ᵥ x₁) −ᵥ ((x₂ ⋆ᵥ) ⋅ᵥ 𝟎ᵥ) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ {!!} ⦄ (identityₗ(_⋅ᵥ_)(𝟏ᵥ)) (absorberᵣ(_⋅ᵥ_)(𝟎ᵥ) ⦃ {!!} ⦄) ]
    x₁ −ᵥ 𝟎ᵥ                      🝖[ _≡_ ]-[ identityᵣ(_−ᵥ_)(𝟎ᵥ) ⦃ {!!} ⦄ ]
    x₁                            🝖-end
  right (Identityₗ.proof [⋅]-identityₗ {x₁ , x₂}) =
    (x₂ ⋅ᵥ 𝟏ᵥ) +ᵥ (𝟎ᵥ ⋅ᵥ (x₁ ⋆ᵥ)) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (identityᵣ(_⋅ᵥ_)(𝟏ᵥ)) (absorberₗ(_⋅ᵥ_)(𝟎ᵥ) ⦃ {!!} ⦄) ]
    x₂ +ᵥ 𝟎ᵥ                      🝖[ _≡_ ]-[ identityᵣ(_+ᵥ_)(𝟎ᵥ) ]
    x₂                            🝖-end

  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  left (Identityᵣ.proof [⋅]-identityᵣ {x₁ , x₂}) = {!!}
  right (Identityᵣ.proof [⋅]-identityᵣ {x₁ , x₂}) = {!!}

  [⋆ᵥ][⋅ᵥ]ₗ-move : ∀{x y} → ((x ⋆ᵥ) ⋅ᵥ y ≡ ((y ⋆ᵥ) ⋅ᵥ x)⋆ᵥ)
  [⋆ᵥ][⋅ᵥ]ₗ-move {x}{y} =
    (x ⋆ᵥ) ⋅ᵥ y          🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅ᵥ_)(x ⋆ᵥ) (involution(_⋆ᵥ)) ]-sym
    (x ⋆ᵥ) ⋅ᵥ ((y ⋆ᵥ)⋆ᵥ) 🝖[ _≡_ ]-[ Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism ]-sym
    ((y ⋆ᵥ) ⋅ᵥ x)⋆ᵥ      🝖-end

  [⋆ᵥ][⋅ᵥ]ᵣ-move : ∀{x y} → (x ⋅ᵥ (y ⋆ᵥ) ≡ (y ⋅ᵥ (x ⋆ᵥ))⋆ᵥ)
  [⋆ᵥ][⋅ᵥ]ᵣ-move {x}{y} =
    x ⋅ᵥ (y ⋆ᵥ)          🝖[ _≡_ ]-[ congruence₂ₗ(_⋅ᵥ_)(y ⋆ᵥ) (involution(_⋆ᵥ)) ]-sym
    ((x ⋆ᵥ)⋆ᵥ) ⋅ᵥ (y ⋆ᵥ) 🝖[ _≡_ ]-[ Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism ]-sym
    (y ⋅ᵥ (x ⋆ᵥ))⋆ᵥ      🝖-end

  [⋅]-commutativity : (∀{x} → ((x ⋆ᵥ) ≡ x)) → ⦃ commᵥ : Commutativity(_⋅ᵥ_) ⦄ → Commutativity(_⋅_)
  left (Commutativity.proof ([⋅]-commutativity [⋆ᵥ]-is-id) {x₁ , x₂} {y₁ , y₂}) =
    (x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂) 🝖[ _≡_ ]-[ congruence₂ᵣ(_−ᵥ_) ⦃ {!!} ⦄ (x₁ ⋅ᵥ y₁) (congruence₂ₗ(_⋅ᵥ_)(x₂) [⋆ᵥ]-is-id) ]
    (x₁ ⋅ᵥ y₁) −ᵥ (y₂ ⋅ᵥ x₂)      🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ {!!} ⦄ (commutativity(_⋅ᵥ_)) (commutativity(_⋅ᵥ_)) ]
    (y₁ ⋅ᵥ x₁) −ᵥ (x₂ ⋅ᵥ y₂)      🝖[ _≡_ ]-[ congruence₂ᵣ(_−ᵥ_) ⦃ {!!} ⦄ (y₁ ⋅ᵥ x₁) (congruence₂ₗ(_⋅ᵥ_)(y₂) [⋆ᵥ]-is-id) ]-sym
    (y₁ ⋅ᵥ x₁) −ᵥ ((x₂ ⋆ᵥ) ⋅ᵥ y₂) 🝖-end
  right (Commutativity.proof ([⋅]-commutativity [⋆ᵥ]-is-id) {x₁ , x₂} {y₁ , y₂}) =
    (y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+ᵥ_)(y₂ ⋅ᵥ x₁) (congruence₂ᵣ(_⋅ᵥ_)(x₂) [⋆ᵥ]-is-id) ]
    (y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ y₁)      🝖[ _≡_ ]-[ commutativity(_+ᵥ_) ]
    (x₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ x₁)      🝖[ _≡_ ]-[ congruence₂ᵣ(_+ᵥ_)(x₂ ⋅ᵥ y₁) (congruence₂ᵣ(_⋅ᵥ_)(y₂) [⋆ᵥ]-is-id) ]-sym
    (x₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (x₁ ⋆ᵥ)) 🝖-end

  [⋅]-associativity : ⦃ commᵥ : Commutativity(_⋅ᵥ_) ⦄ {- ⦃ assocᵥ : Associativity(_⋅ᵥ_) ⦄ -} → Associativity(_⋅_)
  left (Associativity.proof [⋅]-associativity {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}) =
    (((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂)) ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ ((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ)))) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ {!!} ⦄ (distributivityᵣ(_⋅ᵥ_)(_−ᵥ_) ⦃ {!!} ⦄) (distributivityₗ(_⋅ᵥ_)(_+ᵥ_)) ]
    (((x₁ ⋅ᵥ y₁) ⋅ᵥ z₁) −ᵥ (((y₂ ⋆ᵥ) ⋅ᵥ x₂) ⋅ᵥ z₁)) −ᵥ (((z₂ ⋆ᵥ) ⋅ᵥ (y₂ ⋅ᵥ x₁)) +ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))  🝖[ _≡_ ]-[ {!!} ]

    (x₁ ⋅ᵥ ((y₁ ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((z₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (z₁ ⋆ᵥ)))⋆ᵥ) ⋅ᵥ x₂) 🝖-end
  right (Associativity.proof [⋅]-associativity) = {!!}


{-
(((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂)) ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ ((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))
(((x₁ ⋅ᵥ y₁) ⋅ᵥ z₁) −ᵥ (((y₂ ⋆ᵥ) ⋅ᵥ x₂) ⋅ᵥ z₁)) −ᵥ (((z₂ ⋆ᵥ) ⋅ᵥ (y₂ ⋅ᵥ x₁)) +ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))

((x₁ ⋅ᵥ (y₁ ⋅ᵥ z₁)) −ᵥ (x₁ ⋅ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) ⋅ᵥ x₂) +ᵥ ((z₁ ⋅ᵥ (y₂ ⋆ᵥ)) ⋅ᵥ x₂))
((x₁ ⋅ᵥ (y₁ ⋅ᵥ z₁)) −ᵥ (x₁ ⋅ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) +ᵥ (z₁ ⋅ᵥ (y₂ ⋆ᵥ))) ⋅ᵥ x₂)
((x₁ ⋅ᵥ (y₁ ⋅ᵥ z₁)) −ᵥ (x₁ ⋅ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((z₂ ⋅ᵥ y₁)⋆ᵥ) +ᵥ ((y₂ ⋅ᵥ (z₁ ⋆ᵥ))⋆ᵥ)) ⋅ᵥ x₂)
(x₁ ⋅ᵥ ((y₁ ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((z₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (z₁ ⋆ᵥ)))⋆ᵥ) ⋅ᵥ x₂)
-}
