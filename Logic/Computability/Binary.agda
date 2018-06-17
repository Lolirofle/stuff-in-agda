module Logic.Computability.Binary {ℓ} where

open import Data.Boolean
open import Data.Tuple
open import Functional
import      Logic.Computability{ℓ} as C
open import Logic.Properties{ℓ}
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Relator.Equals{ℓ}
open import Type{ℓ}

ComputablyDecidable : ∀{X Y : Type} → (X → Y → Stmt) → Stmt
ComputablyDecidable = C.ComputablyDecidable ∘ uncurry

module ComputablyDecidable {X Y : Type} (_▫_ : X → Y → Stmt) where
  decide : ⦃ _ : ComputablyDecidable{X}{Y}(_▫_) ⦄ → X → Y → Bool
  decide ⦃ proof ⦄ (x)(y) = C.ComputablyDecidable.decide (proof) (x , y)

  ComputablyDecidable-intro : (∀{x}{y} → (x ▫ y) ↔ (decide(x)(y) ≡ 𝑇)) → ComputablyDecidable(_▫_)
  ComputablyDecidable-intro (proof) = C.ComputablyDecidable-intro(uncurry _▫_) (lr) where
    lr{x , y} = [↔]-intro (l{x , y}) (r{x , y})
    l{x , y} = [↔]-elimₗ (proof{x}{y})
    r{x , y} = [↔]-elimᵣ (proof{x}{y})

  -- TODO: The other functions in Logic.Computability.ComputablyDecidable

