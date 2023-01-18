module Structure.IndexedOperator.Properties.Preserving where

open import Data.Boolean
open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ using (_^_)
open import Functional using (_→ᶠ_ ; _∘_)
open import Functional.Instance using (inferArg)
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Structure.IndexedOperator
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ₁ ℓₘ₂ ℓₑ₂ : Lvl.Level
private variable I₁ I₂ : Type{ℓₒ}

module _
  (A : I₁ → Type{ℓₘ₁})
  (B : I₂ → Type{ℓₘ₂})
  ⦃ equiv₂ : ∀{i} → Equiv{ℓₑ₂}(B(i)) ⦄
  where

  module Names where
    PreservingSignature = \n S F → (∀{i} → A(i) → B(F(i))) → IndexedOperator(A)(𝐒(n)) S → IndexedOperator(B ∘ F)(𝐒(n)) S → Type{if(positive?(n)) then (ℓₘ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂}

    -- A relation between a functor and two n-ary operations between morphisms that states:
    -- The functor preserves the operations.
    -- Often used when defining homomorphisms.
    -- Examples:
    --   Preserving(0) {x , y} (map)(G₁)(G₂)
    --   = (map ∘₀ G₁ ≡ G₂ on₀ map)
    --   = (map(G₁) ≡ G₂(f))
    --   Preserving(1) {(x , y) , (x , y)} (map)(G₁)(G₂)
    --   = ∀{f : x ⟶ y} → ((map ∘₁ G₁)(f) ≡ (G₂ on₁ map)(f))
    --   = ∀{f : x ⟶ y} → (map(G₁(f)) ≡ G₂(map(f)))
    --   Preserving(2) {(y , z) , (x , y) , (x , z)} (map)(G₁)(G₂)
    --   = ∀{f₁ : y ⟶ z}{f₂ : x ⟶ y} → ((map ∘₂ G₁)(f₁)(f₂) ≡ (G₂ on₂ map)(f₁)(f₂))
    --   = ∀{f₁ : y ⟶ z}{f₂ : x ⟶ y} → (map(G₁ f₁ f₂) ≡ G₂ (map(f₁)) (map(f₂)))
    --   Preserving(3) {(z , w) , (y , z) , (x , y) , (x , w)} (map)(G₁)(G₂)
    --   = ∀{f₁ f₂ f₃} → ((map ∘₃ G₁)(f₁)(f₂)(f₃) ≡ (G₂ on₃ map)(f₁)(f₂)(f₃))
    --   = ∀{f₁ f₂ f₃} → (map(G₁ f₁ f₂ f₃) ≡ G₂ (map(f₁)) (map(f₂)) (map(f₃)))
    Preserving : (n : ℕ) → {S : I₁ ^ 𝐒(n)} → ∀{F : I₁ → I₂} → PreservingSignature n S F
    Preserving 0        {i}     map G₁ G₂ = map(G₁) ≡ G₂
    Preserving 1        {i , o} map G₁ G₂ = ∀{f : A(i)} → (map(G₁ f) ≡ G₂(map f))
    Preserving(𝐒(𝐒(n))) {i , o} map G₁ G₂ = ∀{f : A(i)} → Preserving(𝐒(n)) {o} map (G₁ f) (G₂(map f))

    Preserving₀ = Preserving 0
    Preserving₁ = Preserving 1
    Preserving₂ = Preserving 2
    Preserving₃ = Preserving 3
    Preserving₄ = Preserving 4
    Preserving₅ = Preserving 5
    Preserving₆ = Preserving 6
    Preserving₇ = Preserving 7
    Preserving₈ = Preserving 8
    Preserving₉ = Preserving 9

  module _ (n : ℕ) {S : I₁ ^ 𝐒(n)} {F : I₁ → I₂} (map : ∀{i} → A(i) → B(F(i))) (G₁ : IndexedOperator(A)(𝐒(n)) S) (G₂ : IndexedOperator(B ∘ F)(𝐒(n)) S) where
    record Preserving : Type{if(positive?(n)) then (ℓₘ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂} where
      constructor intro
      field proof : Names.Preserving(n) map G₁ G₂
    preserving = inferArg Preserving.proof

  Preserving₀ = Preserving 0
  Preserving₁ = Preserving 1
  Preserving₂ = Preserving 2
  Preserving₃ = Preserving 3
  Preserving₄ = Preserving 4
  Preserving₅ = Preserving 5
  Preserving₆ = Preserving 6
  Preserving₇ = Preserving 7
  Preserving₈ = Preserving 8
  Preserving₉ = Preserving 9
