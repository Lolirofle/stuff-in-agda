module Structure.Operator.StarAlgebra where

import      Functional as Fn
open import Logic.Predicate
import      Lvl
open import Structure.Operator
open import Structure.Operator.Algebra
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Ring as Ring
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
    open Algebra(algebra) hiding (vectorRing) public

    field
      ⦃ [⋅ᵥ]-binaryOperator ⦄   : BinaryOperator(_⋅ᵥ_)
      -- TODO: Do not require assoc and ident. The problem is that the type of antihomomorphism depends on whether identity exists, so maybe have structures as parameters to Algebra and Ring, or maybe define some kind of "substructure"-relation using homomorphisms, and also try to define a "function" (by instances) returning a signature from a structure and try to define homomorphisms from this
      -- TODO: Also, create UnitalAssociativeAlgebra and move
      ⦃ [⋅ᵥ]-associativity ⦄    : Associativity(_⋅ᵥ_)
      ⦃ [⋅ᵥ]-identity ⦄         : ∃(Identity(_⋅ᵥ_))

    instance
      vectorRing : Ring(_+ᵥ_)(_⋅ᵥ_) {ℓᵥₙ₀}
      vectorRing = Algebra.vectorRing(algebra)
    open Ring.Ring(vectorRing)
      using ()
      renaming(
        rg to vectorRg ;
        rng to vectorRng ;
        unity to vectorUnity ;
        [+]-group to [+ᵥ]-group
      ) public

    field
      ⦃ [⋆ₛ]-involution ⦄       : Involution(_⋆ₛ)
      ⦃ [⋆ₛ]-antihomomorphism ⦄ : Ring.Antihomomorphism scalarRing scalarRing (_⋆ₛ)

      ⦃ [⋆ᵥ]-involution ⦄       : Involution(_⋆ᵥ)
      ⦃ [⋆ᵥ]-antihomomorphism ⦄ : Ring.Antihomomorphism vectorRing vectorRing (_⋆ᵥ)

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
open import Structure.Function.Multi
open import Structure.Operator.InverseOperatorFromFunction.Proofs
open import Structure.Operator.Ring.Proofs
open import Structure.Operator.Proofs
open import Syntax.Implication
open import Syntax.Transitivity

private variable ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ ℓᵥₙ₀ ℓₛₙ₀ : Lvl.Level
private variable V : Type{ℓᵥ}
private variable S : Type{ℓₛ}
private variable _+ᵥ_ _⋅ᵥ_ : V → V → V
private variable _⋆ᵥ : V → V
private variable _⋅ₛᵥ_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable _⋆ₛ : S → S

module Proofs
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  ⦃ starAlgebra : ⋆-algebra ⦃ equiv-V ⦄ ⦃ equiv-S ⦄ (_+ᵥ_)(_⋅ᵥ_)(_⋆ᵥ)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)(_⋆ₛ) {ℓᵥₙ₀}{ℓₛₙ₀} ⦄
  where

  open ⋆-algebra(starAlgebra)

  -- TODO: Move
  open import Structure.Relator.Properties
  double-is-single-is-identity : ∀{x : V} → (x +ᵥ x ≡ x) → Identity(_+ᵥ_)(x)
  Identityₗ.proof (Identity.left (double-is-single-is-identity {x} xxx)) {y} = congruence₂-₁(_+ᵥ_)(y) (cancellationᵣ(_+ᵥ_) (xxx 🝖 symmetry(_≡_) (identityₗ(_+ᵥ_)(𝟎ᵥ)))) 🝖 identityₗ(_+ᵥ_)(𝟎ᵥ)
  Identityᵣ.proof (Identity.right (double-is-single-is-identity {x} xxx)) {y} = congruence₂-₂(_+ᵥ_)(y) (cancellationₗ(_+ᵥ_) (xxx 🝖 symmetry(_≡_) (identityᵣ(_+ᵥ_)(𝟎ᵥ)))) 🝖 identityᵣ(_+ᵥ_)(𝟎ᵥ)

  -- TODO: Maybe these are general results about functions preserving an operator with inverse function and preserving element
  instance
    [⋆ᵥ]-preserving-[𝟎ᵥ] : Preserving₀(_⋆ᵥ)(𝟎ᵥ)(𝟎ᵥ)
    Preserving.proof [⋆ᵥ]-preserving-[𝟎ᵥ] = One.unique-identity (double-is-single-is-identity p) [+ᵥ]-identity where
      p =
        (𝟎ᵥ ⋆ᵥ) +ᵥ (𝟎ᵥ ⋆ᵥ) 🝖[ _≡_ ]-[ preserving₂(_⋆ᵥ)(_+ᵥ_)(_+ᵥ_) ]-sym
        (𝟎ᵥ +ᵥ 𝟎ᵥ) ⋆ᵥ      🝖[ _≡_ ]-[ congruence₁(_⋆ᵥ) (identityₗ(_+ᵥ_)(𝟎ᵥ)) ]
        𝟎ᵥ ⋆ᵥ              🝖-end

  instance
    [⋆ᵥ]-preserving-[−ᵥ]₁ : Preserving₁(_⋆ᵥ)(−ᵥ_)(−ᵥ_)
    Preserving.proof [⋆ᵥ]-preserving-[−ᵥ]₁ {x} =
      (
        (x ⋆ᵥ) +ᵥ ((−ᵥ x) ⋆ᵥ) 🝖[ _≡_ ]-[ preserving₂(_⋆ᵥ)(_+ᵥ_)(_+ᵥ_) ]-sym
        (x +ᵥ (−ᵥ x)) ⋆ᵥ      🝖[ _≡_ ]-[ congruence₁(_⋆ᵥ) (inverseFunctionᵣ(_+ᵥ_) ⦃ [∃]-intro _ ⦃ [+ᵥ]-identityᵣ ⦄ ⦄ (−ᵥ_)) ]
        𝟎ᵥ ⋆ᵥ                 🝖[ _≡_ ]-[ preserving₀(_⋆ᵥ)(𝟎ᵥ)(𝟎ᵥ) ]
        𝟎ᵥ                    🝖-end
      ) ⇒
      (x ⋆ᵥ) +ᵥ ((−ᵥ x) ⋆ᵥ) ≡ 𝟎ᵥ ⇒-[ One.unique-inverseᵣ-by-id ]
      (−ᵥ x) ⋆ᵥ ≡ −ᵥ(x ⋆ᵥ)       ⇒-end

  instance
    [⋆ᵥ]-preserving-[−ᵥ]₂ : Preserving₂(_⋆ᵥ)(_−ᵥ_)(_−ᵥ_)
    Preserving.proof [⋆ᵥ]-preserving-[−ᵥ]₂ {x} {y} =
      (x −ᵥ y) ⋆ᵥ          🝖[ _≡_ ]-[]
      (x +ᵥ (−ᵥ y)) ⋆ᵥ     🝖[ _≡_ ]-[ preserving₂(_⋆ᵥ)(_+ᵥ_)(_+ᵥ_) ]
      (x ⋆ᵥ) +ᵥ ((−ᵥ y)⋆ᵥ) 🝖[ _≡_ ]-[ congruence₂-₂(_+ᵥ_)(x ⋆ᵥ) (preserving₁(_⋆ᵥ)(−ᵥ_)(−ᵥ_)) ]
      (x ⋆ᵥ) +ᵥ (−ᵥ(y ⋆ᵥ)) 🝖[ _≡_ ]-[]
      (x ⋆ᵥ) −ᵥ (y ⋆ᵥ)     🝖-end

  [⋆ᵥ][⋅ᵥ]ₗ-move : ∀{x y} → ((x ⋆ᵥ) ⋅ᵥ y ≡ ((y ⋆ᵥ) ⋅ᵥ x)⋆ᵥ)
  [⋆ᵥ][⋅ᵥ]ₗ-move {x}{y} =
    (x ⋆ᵥ) ⋅ᵥ y          🝖[ _≡_ ]-[ congruence₂-₂(_⋅ᵥ_)(x ⋆ᵥ) (involution(_⋆ᵥ) ⦃ [⋆ᵥ]-involution ⦄) ]-sym
    (x ⋆ᵥ) ⋅ᵥ ((y ⋆ᵥ)⋆ᵥ) 🝖[ _≡_ ]-[ Ring.Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism ]-sym -- preserving₂(_⋆ᵥ)(_⋅ᵥ_)(Fn.swap(_⋅ᵥ_)) ⦃  ⦄
    ((y ⋆ᵥ) ⋅ᵥ x)⋆ᵥ      🝖-end

  [⋆ᵥ][⋅ᵥ]ᵣ-move : ∀{x y} → (x ⋅ᵥ (y ⋆ᵥ) ≡ (y ⋅ᵥ (x ⋆ᵥ))⋆ᵥ)
  [⋆ᵥ][⋅ᵥ]ᵣ-move {x}{y} =
    x ⋅ᵥ (y ⋆ᵥ)          🝖[ _≡_ ]-[ congruence₂-₁(_⋅ᵥ_)(y ⋆ᵥ) (involution(_⋆ᵥ) ⦃ [⋆ᵥ]-involution ⦄) ]-sym
    ((x ⋆ᵥ)⋆ᵥ) ⋅ᵥ (y ⋆ᵥ) 🝖[ _≡_ ]-[ Ring.Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism ]-sym
    (y ⋅ᵥ (x ⋆ᵥ))⋆ᵥ      🝖-end

  [⋆ᵥ][⋅ᵥ]-antipreserving-neutralizingᵣ : ∀{x y} → ((x ⋅ᵥ (y ⋆ᵥ))⋆ᵥ ≡ y ⋅ᵥ (x ⋆ᵥ))
  [⋆ᵥ][⋅ᵥ]-antipreserving-neutralizingᵣ {x}{y} =
    (x ⋅ᵥ (y ⋆ᵥ)) ⋆ᵥ      🝖[ _≡_ ]-[ Ring.Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism ]
    ((y ⋆ᵥ) ⋆ᵥ) ⋅ᵥ (x ⋆ᵥ) 🝖[ _≡_ ]-[ congruence₂-₁(_⋅ᵥ_)(x ⋆ᵥ) (involution(_⋆ᵥ) ⦃ [⋆ᵥ]-involution ⦄) ]
    y ⋅ᵥ (x ⋆ᵥ)           🝖-end

import      Structure.Operator.Ring.Numerals
open import Syntax.Number

-- Also called: General Cayley–Dickson construction.
-- Source: https://en.wikipedia.org/wiki/Cayley%E2%80%93Dickson_construction#General_Cayley%E2%80%93Dickson_construction (20210610)
-- TODO: But it is incorrect because of too many assumptions from the star algebra. See the todo above
module ComplexConstruction
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  ⦃ starAlgebra : ⋆-algebra ⦃ equiv-V ⦄ ⦃ equiv-S ⦄ (_+ᵥ_)(_⋅ᵥ_)(_⋆ᵥ)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_)(_⋆ₛ) {ℓᵥₙ₀}{ℓₛₙ₀} ⦄
  where

  open ⋆-algebra(starAlgebra)
  open Proofs ⦃ starAlgebra = starAlgebra ⦄

  Vector = V ⨯ V

  _+_ : Vector → Vector → Vector
  (x₁ , x₂) + (y₁ , y₂) = ((x₁ +ᵥ y₁) , (x₂ +ᵥ y₂))
  
  _⋅_ : Vector → Vector → Vector
  (x₁ , x₂) ⋅ (y₁ , y₂) = (((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂)) , ((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))
  
  _⋆ : Vector → Vector
  (x₁ , x₂)⋆ = ((x₁ ⋆ᵥ) , (−ᵥ x₂))

  𝟎 : Vector
  𝟎 = (𝟎ᵥ , 𝟎ᵥ)

  𝟏 : Vector
  𝟏 = (𝟏ᵥ , 𝟎ᵥ)

  instance
    Vector-from-ℕ : InfiniteNumeral(Vector)
    Numeral.num Vector-from-ℕ n = (num n , 𝟎ᵥ)

  [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
  left (Identityₗ.proof [⋅]-identityₗ {x₁ , x₂}) =
    (𝟏ᵥ ⋅ᵥ x₁) −ᵥ ((x₂ ⋆ᵥ) ⋅ᵥ 𝟎ᵥ) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (identityₗ(_⋅ᵥ_)(𝟏ᵥ)) (absorberᵣ(_⋅ᵥ_)(𝟎ᵥ)) ]
    x₁ −ᵥ 𝟎ᵥ                      🝖[ _≡_ ]-[ identityᵣ(_−ᵥ_)(𝟎ᵥ) ⦃ inverse-operatorᵣ-identityᵣ-by-identity-inverseFunc ⦄ ]
    x₁                            🝖-end
  right (Identityₗ.proof [⋅]-identityₗ {x₁ , x₂}) =
    (x₂ ⋅ᵥ 𝟏ᵥ) +ᵥ (𝟎ᵥ ⋅ᵥ (x₁ ⋆ᵥ)) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (identityᵣ(_⋅ᵥ_)(𝟏ᵥ)) (absorberₗ(_⋅ᵥ_)(𝟎ᵥ)) ]
    x₂ +ᵥ 𝟎ᵥ                      🝖[ _≡_ ]-[ identityᵣ(_+ᵥ_)(𝟎ᵥ) ]
    x₂                            🝖-end

  [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
  left (Identityᵣ.proof [⋅]-identityᵣ {x₁ , x₂}) =
    (x₁ ⋅ᵥ 𝟏ᵥ) −ᵥ ((𝟎ᵥ ⋆ᵥ) ⋅ᵥ x₂) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (identityᵣ(_⋅ᵥ_)(𝟏ᵥ)) (congruence₂-₁(_⋅ᵥ_)(x₂) (preserving₀(_⋆ᵥ)(𝟎ᵥ)(𝟎ᵥ) ⦃ [⋆ᵥ]-preserving-[𝟎ᵥ] ⦄)) ]
    x₁ −ᵥ (𝟎ᵥ ⋅ᵥ x₂)              🝖[ _≡_ ]-[ congruence₂-₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (x₁) (absorberₗ(_⋅ᵥ_)(𝟎ᵥ)) ]
    x₁ −ᵥ 𝟎ᵥ                      🝖[ _≡_ ]-[ identityᵣ(_−ᵥ_)(𝟎ᵥ) ⦃ inverse-operatorᵣ-identityᵣ-by-identity-inverseFunc ⦄ ]
    x₁ 🝖-end
  right (Identityᵣ.proof [⋅]-identityᵣ {x₁ , x₂}) =
    (𝟎ᵥ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (𝟏ᵥ ⋆ᵥ)) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) (absorberₗ(_⋅ᵥ_)(𝟎ᵥ)) (congruence₂-₂(_⋅ᵥ_)(x₂) (preserving₀(_⋆ᵥ)(𝟏ᵥ)(𝟏ᵥ) ⦃ Ring.Antihomomorphism.preserve-𝟏 [⋆ᵥ]-antihomomorphism ⦄)) ]
    𝟎ᵥ +ᵥ (x₂ ⋅ᵥ 𝟏ᵥ)              🝖[ _≡_ ]-[ congruence₂-₂(_+ᵥ_)(𝟎ᵥ) (identityᵣ(_⋅ᵥ_)(𝟏ᵥ)) ]
    𝟎ᵥ +ᵥ x₂                      🝖[ _≡_ ]-[ identityₗ(_+ᵥ_)(𝟎ᵥ) ]
    x₂                            🝖-end

  [⋅]-commutativity : (∀{x} → ((x ⋆ᵥ) ≡ x)) → ⦃ commᵥ : Commutativity(_⋅ᵥ_) ⦄ → Commutativity(_⋅_)
  left (Commutativity.proof ([⋅]-commutativity [⋆ᵥ]-is-id) {x₁ , x₂} {y₁ , y₂}) =
    (x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂) 🝖[ _≡_ ]-[ congruence₂-₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (x₁ ⋅ᵥ y₁) (congruence₂-₁(_⋅ᵥ_)(x₂) [⋆ᵥ]-is-id) ]
    (x₁ ⋅ᵥ y₁) −ᵥ (y₂ ⋅ᵥ x₂)      🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (commutativity(_⋅ᵥ_)) (commutativity(_⋅ᵥ_)) ]
    (y₁ ⋅ᵥ x₁) −ᵥ (x₂ ⋅ᵥ y₂)      🝖[ _≡_ ]-[ congruence₂-₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (y₁ ⋅ᵥ x₁) (congruence₂-₁(_⋅ᵥ_)(y₂) [⋆ᵥ]-is-id) ]-sym
    (y₁ ⋅ᵥ x₁) −ᵥ ((x₂ ⋆ᵥ) ⋅ᵥ y₂) 🝖-end
  right (Commutativity.proof ([⋅]-commutativity [⋆ᵥ]-is-id) {x₁ , x₂} {y₁ , y₂}) =
    (y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ)) 🝖[ _≡_ ]-[ congruence₂-₂(_+ᵥ_)(y₂ ⋅ᵥ x₁) (congruence₂-₂(_⋅ᵥ_)(x₂) [⋆ᵥ]-is-id) ]
    (y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ y₁)      🝖[ _≡_ ]-[ commutativity(_+ᵥ_) ]
    (x₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ x₁)      🝖[ _≡_ ]-[ congruence₂-₂(_+ᵥ_)(x₂ ⋅ᵥ y₁) (congruence₂-₂(_⋅ᵥ_)(y₂) [⋆ᵥ]-is-id) ]-sym
    (x₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (x₁ ⋆ᵥ)) 🝖-end

  postulate [⋅]-associativity : ⦃ commᵥ : Commutativity(_⋅ᵥ_) ⦄ {- ⦃ assocᵥ : Associativity(_⋅ᵥ_) ⦄ -} → Associativity(_⋅_)
  {-left (Associativity.proof [⋅]-associativity {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}) =
    (((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂)) ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ ((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))))                      🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (distributivityᵣ(_⋅ᵥ_)(_−ᵥ_) ⦃ {!!} ⦄) (distributivityₗ(_⋅ᵥ_)(_+ᵥ_)) ]
    (((x₁ ⋅ᵥ y₁) ⋅ᵥ z₁) −ᵥ (((y₂ ⋆ᵥ) ⋅ᵥ x₂) ⋅ᵥ z₁)) −ᵥ (((z₂ ⋆ᵥ) ⋅ᵥ (y₂ ⋅ᵥ x₁)) +ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ)))) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ (associativity(_⋅ᵥ_)) {!!}) (congruence₂(_+ᵥ_) {!!} {!!}) ]
    ((x₁ ⋅ᵥ (y₁ ⋅ᵥ z₁)) −ᵥ ((z₁ ⋅ᵥ (y₂ ⋆ᵥ)) ⋅ᵥ x₂)) −ᵥ ((x₁ ⋅ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂)) +ᵥ (((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) ⋅ᵥ x₂)) 🝖[ _≡_ ]-[ {!!} ]
    ((x₁ ⋅ᵥ (y₁ ⋅ᵥ z₁)) −ᵥ (x₁ ⋅ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) ⋅ᵥ x₂) +ᵥ ((z₁ ⋅ᵥ (y₂ ⋆ᵥ)) ⋅ᵥ x₂)) 🝖[ _≡_ ]-[ congruence₂(_−ᵥ_) ⦃ [−]-binaryOperator ⦄ ((distributivityₗ(_⋅ᵥ_)(_−ᵥ_) ⦃ {![⋅ᵥ][−ᵥ]-distributivityₗ!} ⦄)) p ]-sym
    (x₁ ⋅ᵥ ((y₁ ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂))) −ᵥ ((((z₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (z₁ ⋆ᵥ)))⋆ᵥ) ⋅ᵥ x₂)                       🝖-end
    where
      p =
        (((z₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (z₁ ⋆ᵥ)))⋆ᵥ) ⋅ᵥ x₂               🝖[ _≡_ ]-[ congruence₂-₁(_⋅ᵥ_)(x₂) (preserving₂(_⋆ᵥ)(_+ᵥ_)(_+ᵥ_)) ]
        (((z₂ ⋅ᵥ y₁)⋆ᵥ) +ᵥ ((y₂ ⋅ᵥ (z₁ ⋆ᵥ))⋆ᵥ)) ⋅ᵥ x₂           🝖[ _≡_ ]-[ congruence₂-₁(_⋅ᵥ_)(x₂) (congruence₂(_+ᵥ_) (Ring.Antihomomorphism.antipreserve-[⋅] [⋆ᵥ]-antihomomorphism) [⋆ᵥ][⋅ᵥ]-antipreserving-neutralizingᵣ) ]
        (((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) +ᵥ (z₁ ⋅ᵥ (y₂ ⋆ᵥ))) ⋅ᵥ x₂         🝖[ _≡_ ]-[ distributivityᵣ(_⋅ᵥ_)(_+ᵥ_) ]
        (((y₁ ⋆ᵥ) ⋅ᵥ (z₂ ⋆ᵥ)) ⋅ᵥ x₂) +ᵥ ((z₁ ⋅ᵥ (y₂ ⋆ᵥ)) ⋅ᵥ x₂) 🝖-end
  right (Associativity.proof [⋅]-associativity {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}) =
    (z₂ ⋅ᵥ ((x₁ ⋅ᵥ y₁) −ᵥ ((y₂ ⋆ᵥ) ⋅ᵥ x₂))) +ᵥ (((y₂ ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (y₁ ⋆ᵥ))) ⋅ᵥ (z₁ ⋆ᵥ)) 🝖[ _≡_ ]-[ {!!} ]
    (((z₂ ⋅ᵥ y₁) +ᵥ (y₂ ⋅ᵥ (z₁ ⋆ᵥ))) ⋅ᵥ x₁) +ᵥ (x₂ ⋅ᵥ (((y₁ ⋅ᵥ z₁) −ᵥ ((z₂ ⋆ᵥ) ⋅ᵥ y₂)) ⋆ᵥ)) 🝖-end
  -}
