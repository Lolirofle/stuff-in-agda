open import Logic
open import Structure.Setoid
open import Structure.Operator.Ring
open import Structure.OrderedField
open import Type

module Structure.OrderedField.AbsoluteValue
  {ℓ ℓₗ}
  {F : Type{ℓ}}
  ⦃ equiv : Equiv(F) ⦄
  (_+_ _⋅_ : F → F → F)
  (_≤_ : F → F → Stmt{ℓₗ})
  ⦃ ring : Ring(_+_)(_⋅_) ⦄
  ⦃ ordered : Ordered(_+_)(_⋅_)(_≤_) ⦄
  where

open Ring(ring)
open Ordered(ordered)

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Functional
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Function.Ordering
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity

‖_‖ : F → F
‖ x ‖ = if Either.isRight(converseTotal(_≤_){𝟎}{x}) then (− x) else x

instance
  abs-function : Function(‖_‖)
  Function.congruence abs-function {x}{y} xy with converseTotal(_≤_){𝟎}{x} | converseTotal(_≤_){𝟎}{y}
  ... | Either.Left  p | Either.Left  q = xy
  ... | Either.Left  p | Either.Right q = antisymmetry(_≤_)(_≡_) (sub₂(_≡_)(_≤_) xy 🝖 q) p 🝖 antisymmetry(_≤_)(_≡_) ([↔]-to-[→] [≤]-flip-negative q) ([≤]-flip-positive(p 🝖 sub₂(_≡_)(_≤_) xy))
  ... | Either.Right p | Either.Left  q = antisymmetry(_≤_)(_≡_) ([≤]-flip-positive(q 🝖 sub₂(_≡_)(_≤_) (symmetry(_≡_) xy))) ([↔]-to-[→] [≤]-flip-negative p) 🝖 antisymmetry(_≤_)(_≡_) q (sub₂(_≡_)(_≤_) (symmetry(_≡_) xy) 🝖 p)
  ... | Either.Right p | Either.Right q = congruence₁(−_) xy

abs-positive : ∀{x} → (‖ x ‖ ≥ 𝟎)
abs-positive{x} = if-either-bool-intro {P = _≥ 𝟎} {x = x} {y = − x} id ([↔]-to-[→] [≤]-flip-negative) (converseTotal(_≤_){𝟎}{x})

abs-values : ∀{x} → (‖ x ‖ ≡ x) ∨ (‖ x ‖ ≡ − x)
abs-values{x} with converseTotal(_≤_){𝟎}{x}
... | [∨]-introₗ _ = [∨]-introₗ (reflexivity(_≡_))
... | [∨]-introᵣ _ = [∨]-introᵣ (reflexivity(_≡_))

abs-of-zero : (‖ 𝟎 ‖ ≡ 𝟎)
abs-of-zero with abs-values{𝟎}
... | Either.Left  p = p
... | Either.Right p = p 🝖 [−]-of-𝟎

abs-when-zero : ∀{x} → (‖ x ‖ ≡ 𝟎) ↔ (x ≡ 𝟎)
abs-when-zero{x} = [↔]-intro (p ↦ congruence₁(‖_‖) p 🝖 abs-of-zero) (p ↦ symmetry(_≡_) ([∨]-elim id (q ↦ p 🝖 symmetry(_≡_) ([↔]-to-[→] [−]-is-𝟎 (symmetry(_≡_) q 🝖 p))) abs-values) 🝖 p)

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

abs-idempotent : Idempotent(‖_‖)
Idempotent.proof abs-idempotent {x} with abs-values{x}
... | Either.Left  p = congruence₁(‖_‖) p
... | Either.Right p = congruence₁(‖_‖) p 🝖 abs-of-negation

abs-order : ∀{x} → ((− ‖ x ‖) ≤ ‖ x ‖)
abs-order{x} = [≤]-flip-positive(abs-positive{x}) 🝖 abs-positive{x}

abs-order-pos : ∀{x} → (x ≤ ‖ x ‖)
abs-order-pos {x} with converseTotal(_≤_){𝟎}{x}
... | Either.Left  p = reflexivity(_≤_)
... | Either.Right p = p 🝖 [↔]-to-[→] [≤]-flip-negative p

abs-order-neg : ∀{x} → ((− x) ≤ ‖ x ‖)
abs-order-neg {x} with converseTotal(_≤_){𝟎}{x}
... | Either.Left  p = [≤]-flip-positive p 🝖 p
... | Either.Right p = reflexivity(_≤_)

abs-of-positive : ∀{x} → (𝟎 ≤ x) → (‖ x ‖ ≡ x)
abs-of-positive {x} ox = antisymmetry(_≤_)(_≡_) p abs-order-pos where
  p : ‖ x ‖ ≤ x
  p with converseTotal(_≤_){𝟎}{x}
  ... | Either.Left  _ = reflexivity(_≤_)
  ... | Either.Right _ = [≤]-flip-positive ox 🝖 ox
  -- Alternative 1:
  -- with abs-values{x}
  -- ... | Either.Left  p = p
  -- ... | Either.Right p = [↔]-to-[←] abs-when-zero xzero 🝖 symmetry(_≡_) xzero where
  --   xzero : (x ≡ 𝟎)
  --   xzero = antisymmetry(_≤_)(_≡_) ([↔]-to-[←] [≤]-flip-negative (abs-positive{x} 🝖 sub₂(_≡_)(_≤_) p)) ox
  -- Alternative 2: antisymmetry(_≤_)(_≡_) (sub₂(_≡_)(_≤_) p 🝖 [≤]-flip-positive ox 🝖 ox) (sub₂(_≡_)(_≤_) (symmetry(_≡_) (congruence₁(−_) p 🝖 [−−]-elim)) 🝖 abs-order{x})

abs-of-negative : ∀{x} → (x ≤ 𝟎) → (‖ x ‖ ≡ − x)
abs-of-negative {x} xo = antisymmetry(_≤_)(_≡_) p abs-order-neg where
  p : ‖ x ‖ ≤ (− x)
  p with converseTotal(_≤_){𝟎}{x}
  ... | Either.Left  _ = xo 🝖 [↔]-to-[→] [≤]-flip-negative xo
  ... | Either.Right _ = reflexivity(_≤_)
  -- Alternative 1:
  -- with abs-values{x}
  -- ... | Either.Right p = p
  -- ... | Either.Left  p = symmetry(_≡_) abs-of-negation 🝖 [↔]-to-[←] abs-when-zero xzero 🝖 symmetry(_≡_) xzero where
  --   xzero : (− x ≡ 𝟎)
  --   xzero = antisymmetry(_≤_)(_≡_) ([↔]-to-[←] [≤]-flip-negative (abs-positive{x} 🝖 sub₂(_≡_)(_≤_) p 🝖 sub₂(_≡_)(_≤_) (symmetry(_≡_) [−−]-elim))) ([↔]-to-[→] [≤]-flip-negative xo)

abs-triangle-inequality : ∀{x y} → (‖ x + y ‖ ≤ (‖ x ‖ + ‖ y ‖))
abs-triangle-inequality {x}{y} with converseTotal(_≤_){𝟎}{x + y}
... | Either.Left  p =
  (x + y)         🝖[ _≤_ ]-[ [≤][+]-preserve abs-order-pos abs-order-pos ]
  (‖ x ‖ + ‖ y ‖) 🝖-end
... | Either.Right p =
  −(x + y)        🝖[ _≡_ ]-[ [+]-negation-distribution ]-sub
  (− x) + (− y)   🝖[ _≤_ ]-[ [≤][+]-preserve abs-order-neg abs-order-neg ]
  (‖ x ‖ + ‖ y ‖) 🝖-end

-- TODO: True in rings? Only division rings? Maybe ≤ instead of ≡ is better because of zero divisors
-- abs-scaling : ∀{a x} → (‖ a ⋅ x ‖ ≡ (‖ a ‖ ⋅ ‖ x ‖))
-- abs-scaling{a}{x} with converseTotal(_≤_){𝟎}{a ⋅ x} | converseTotal(_≤_){𝟎}{a} | converseTotal(_≤_){𝟎}{x}
{-... | Either.Left  p =
  (a ⋅ x)         🝖[ _≡_ ]-[ {!!} ]
  (‖ a ‖ ⋅ ‖ x ‖) 🝖-end
... | Either.Right p = {!!}
-}

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
