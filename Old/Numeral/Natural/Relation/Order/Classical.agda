module Numeral.Natural.Relation.Order.Classical{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Classical{ℓ}
open import Logic.Computability.Binary{ℓ}{Lvl.𝟎}
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Numeral.Natural.Relation.Order.Computability{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

[≰]-to-[>] : ∀{a b : ℕ} → (a ≰ b) → (a > b)
[≰]-to-[>] {a}{b} (a≰b) with excluded-middle ⦃ ComputablyDecidable.classical(_>_) ⦄
... | [∨]-introₗ a>b = a>b
... | [∨]-introᵣ a≯b = [⊥]-elim ([≰][≯]-not (a≰b) (a≯b))

[≯]-to-[≤] : ∀{a b : ℕ} → (a ≯ b) → (a ≤ b)
[≯]-to-[≤] {a}{b} = contrapositive-variantₗ ⦃ ComputablyDecidable.classical(_≤_) ⦄ ([≰]-to-[>] {a}{b})

[≱]-to-[<] : ∀{a b : ℕ} → (a ≱ b) → (a < b)
[≱]-to-[<] {a}{b} (a≱b) with excluded-middle ⦃ ComputablyDecidable.classical(_<_) ⦄
... | [∨]-introₗ a<b = a<b
... | [∨]-introᵣ a≮b = [⊥]-elim ([≮][≱]-not (a≮b) (a≱b))

[≮]-to-[≥] : ∀{a b : ℕ} → (a ≮ b) → (a ≥ b)
[≮]-to-[≥] {a}{b} = contrapositive-variantₗ ⦃ ComputablyDecidable.classical(_≥_) ⦄ ([≱]-to-[<] {a}{b})

[≤]-or-[>] : ∀{a b : ℕ} → (a ≤ b)∨(a > b)
[≤]-or-[>] with excluded-middle ⦃ ComputablyDecidable.classical(_≤_) ⦄
... | [∨]-introₗ a≤b = [∨]-introₗ a≤b
... | [∨]-introᵣ a≰b = [∨]-introᵣ ([≰]-to-[>] a≰b)

[≥]-or-[<] : ∀{a b : ℕ} → (a < b)∨(a ≥ b)
[≥]-or-[<] with excluded-middle ⦃ ComputablyDecidable.classical(_≤_) ⦄
... | [∨]-introₗ a≥b = [∨]-introᵣ a≥b
... | [∨]-introᵣ a≱b = [∨]-introₗ ([≱]-to-[<] a≱b)
