module Functional.Repeat.Proofs {ℓₗ}{ℓₒ} where

import Lvl
open import Functional
open import Functional.Repeat -- {ℓₒ}
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Numeral.Natural
open import Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}{ℓₒ}
open import Relator.Equals.Proofs{ℓₗ}{ℓₒ}
open import Structure.Relator.Properties{ℓₗ}{ℓₒ}
open import Type{ℓₒ}

repeatᵣₗ-flip-equality : ∀{n : ℕ}{X Y : Type}{_▫_ : Y → X → Y}{init : Y}{x : X} → (repeatᵣ n (swap _▫_) x init ≡ repeatₗ n (_▫_) init x)
repeatᵣₗ-flip-equality {𝟎}                     = [≡]-intro
repeatᵣₗ-flip-equality {𝐒(n)}{_}{_}{_▫_}{_}{x} = [≡]-with(_▫ x) (repeatᵣₗ-flip-equality {n})

repeatₗᵣ-flip-equality : ∀{n : ℕ}{X Y : Type}{_▫_ : X → Y → Y}{x : X}{init : Y} → (repeatₗ n (swap _▫_) init x ≡ repeatᵣ n (_▫_) x init)
repeatₗᵣ-flip-equality {n}{X}{Y}{_▫_}{x}{init} = symmetry (repeatᵣₗ-flip-equality {n}{X}{Y}{swap _▫_}{init}{x})

-- repeat-equality : ∀{n : ℕ}{X : Type}{_▫_ : X → X → X}{x : X} → ⦃ _ : Commutativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
-- repeat-equality : ∀{n : ℕ}{X : Type}{_▫_ : X → X → X}{x init : X} → ⦃ _ : Commutativity(_▫_) ⦄ ⦃ _ : Identity(_▫_)(init) ⦄ → (repeatₗ n (_▫_) init x ≡ repeatᵣ n (_▫_) x init)

repeat-raise-equality : ∀{n : ℕ}{X : Type}{_▫_ : X → X → X}{elem x : X} → (repeatᵣ n (_▫_) elem (x) ≡ ((elem ▫_) ^ n)(x))
repeat-raise-equality{𝟎}                     = [≡]-intro
repeat-raise-equality{𝐒(n)}{X}{_▫_}{elem}{x} = [≡]-with(elem ▫_) (repeat-raise-equality{n}{X}{_▫_}{elem}{x})

raise-repeat-equality : ∀{n : ℕ}{X : Type}{f : X → X} → (f ^ n ≡ repeatᵣ n (_∘_) f id)
raise-repeat-equality{𝟎}          = [≡]-intro
raise-repeat-equality{𝐒(n)}{X}{f} = [≡]-with(f ∘_) (raise-repeat-equality{n}{X}{f})

{- TODO
x ▫₂ n = repeatₗ n (_▫_) init x
(a ▫₂ n₁) ▫₂ n₂ = (a ▫₂ n₂) ▫₂ n₁
a ▫₂ (n₁ + n₂) = (a ▫₂ n₁) ▫₂ n₂
Commutativity(_▫_) → Associativity(_▫_) → Identity(_▫_)(id) → ((a ▫ b) ▫₂ n = (a ▫₂ n) ▫ (b ▫₂ n))
Identity(_▫_)(id) → (id ▫₂ n = id)
-}
