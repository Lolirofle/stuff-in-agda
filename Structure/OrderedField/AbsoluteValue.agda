open import Logic
open import Structure.Setoid
open import Structure.OrderedField
open import Type

module Structure.OrderedField.AbsoluteValue
  {ℓ₁ ℓ₂}
  {F : Type{ℓ₁}}
  ⦃ _ : Equiv(F) ⦄
  {_+_ _⋅_ : F → F → F}
  {_≤_ : F → F → Stmt{ℓ₂}}
  (orderedField : OrderedField(_+_)(_⋅_)(_≤_))
  where

open OrderedField(orderedField)

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Functional
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Function.Ordering
open import Structure.Function
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

-- TODO: Stuff related to absolute value can be proven in ordered rings
‖_‖ : F → F
‖ x ‖ = if Either.isRight(converseTotal(_≤_){𝟎}{x}) then (− x) else x

instance
  postulate abs-function : Function(‖_‖)

abs-positive : ∀{x} → (‖ x ‖ ≥ 𝟎)
abs-positive{x} = if-either-bool-intro {P = _≥ 𝟎} {x = x} {y = − x} id ([↔]-to-[→] [≤]-flip-negative) (converseTotal(_≤_){𝟎}{x})

abs-values : ∀{x} → (‖ x ‖ ≡ x) ∨ (‖ x ‖ ≡ − x)
abs-values{x} with converseTotal(_≤_){𝟎}{x}
... | [∨]-introₗ _ = [∨]-introₗ (reflexivity(_≡_))
... | [∨]-introᵣ _ = [∨]-introᵣ (reflexivity(_≡_))

postulate abs-of-zero : (‖ 𝟎 ‖ ≡ 𝟎)

abs-of-negation : ∀{x} → (‖ − x ‖ ≡ ‖ x ‖)
abs-of-negation{x} with converseTotal(_≤_){𝟎}{x} | converseTotal(_≤_){𝟎}{− x}
... | [∨]-introₗ _   | [∨]-introᵣ _   = involution(−_)
... | [∨]-introᵣ _   | [∨]-introₗ _   = reflexivity(_≡_)
... | [∨]-introₗ zx  | [∨]-introₗ znx = antisymmetry(_≤_)(_≡_) (nxz 🝖 zx) (xz 🝖 znx) where
  nxz : (− x) ≤ 𝟎
  nxz = [↔]-to-[←] [≤]-flip-negative (zx 🝖 (sub₂(_≡_)(_≤_) $ symmetry(_≡_) $ involution(−_)))

  xz : x ≤ 𝟎
  xz = [↔]-to-[←] [≤]-flip-negative znx
... | [∨]-introᵣ xz | [∨]-introᵣ nxz  = antisymmetry(_≤_)(_≡_) (involution(−_) 🝖-subₗ (xz 🝖 znx)) (nxz 🝖 zx 🝖-subᵣ symmetry(_≡_) (involution(−_))) where
  znx : 𝟎 ≤ (− x)
  znx = [↔]-to-[→] [≤]-flip-negative xz

  zx : 𝟎 ≤ x
  zx = [↔]-to-[→] [≤]-flip-negative nxz 🝖 (sub₂(_≡_)(_≤_) $ involution(−_))

-- TODO: These can probably be proven using abs-values and abs-positive
postulate abs-of-positive : ∀{x} → (𝟎 ≤ x) → (‖ x ‖ ≡ x)
postulate abs-of-negative : ∀{x} → (x ≤ 𝟎) → (‖ x ‖ ≡ − x)

-- Distance
_𝄩_ : F → F → F
x 𝄩 y = ‖ x − y ‖

instance
  [𝄩]-commutativity : Commutativity(_𝄩_)
  Commutativity.proof [𝄩]-commutativity {x}{y} =
    ‖ x − y ‖    🝖-[ abs-of-negation ]-sym
    ‖ −(x − y) ‖ 🝖-[ congruence₁(‖_‖) [−]-negation-distribution ]
    ‖ y − x ‖    🝖-end

postulate [𝄩]-triangle-inequality : ∀{x y z} → ((x 𝄩 z) ≤ ((x 𝄩 y) + (y 𝄩 z)))

postulate [𝄩]-self : ∀{x y} → (x 𝄩 y ≡ 𝟎) ↔ (x ≡ y)
