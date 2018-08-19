module Logic.Computability.Binary {ℓₗ}{ℓₒ} where

import      Lvl
open import Data.Boolean
open import Data.Tuple
open import Functional
import      Logic.Computability{ℓₗ}{ℓₒ} as C
open import Logic.Classical{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Propositional.Theorems{ℓₗ Lvl.⊔ ℓₒ}
open import Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}
open import Type{ℓₒ}

ComputablyDecidable : ∀{X Y : Type} → (X → Y → Stmt) → Stmt
ComputablyDecidable = C.ComputablyDecidable ∘ uncurry

ComputablyDecidable-intro : ∀{X Y : Type}{_▫_ : X → Y → Stmt} → (decide : X → Y → Bool) → ⦃ _ : ∀{x}{y} → (x ▫ y) ↔ (decide(x)(y) ≡ 𝑇) ⦄ → ComputablyDecidable(_▫_)
ComputablyDecidable-intro {X}{Y}{_▫_} (decide) ⦃ proof ⦄ = C.ComputablyDecidable-intro(uncurry decide) ⦃ lr ⦄ where
   l : ∀{arg} → ((uncurry _▫_)(arg)) ← ((uncurry decide)(arg) ≡ 𝑇)
   l{x , y} = [↔]-elimₗ (proof{x}{y})

   r : ∀{arg} → ((uncurry _▫_)(arg)) → ((uncurry decide)(arg) ≡ 𝑇)
   r{x , y} = [↔]-elimᵣ (proof{x}{y})

   lr : ∀{arg} → ((uncurry _▫_)(arg)) ↔ ((uncurry decide)(arg) ≡ 𝑇)
   lr{x , y} = [↔]-intro (l{x , y}) (r{x , y})

-- TODO: The other functions in Logic.Computability.ComputablyDecidable

module ComputablyDecidable {X Y : Type} (_▫_ : X → Y → Stmt) ⦃ decidable : ComputablyDecidable{X}{Y}(_▫_) ⦄ where
  decide : X → Y → Bool
  decide(x)(y) = C.ComputablyDecidable.decide (decidable) (x , y)

  proof : ∀{x y} → (x ▫ y) ↔ (decide(x)(y) ≡ 𝑇)
  proof{x}{y} = C.ComputablyDecidable.proof (decidable) {x , y}
