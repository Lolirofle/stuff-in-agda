module Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Logic.Computability.Binary
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Finite
import      Numeral.Finite.Proofs as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.DivisibilityWithRemainder hiding (base₀ ; base₊ ; step)
open import Numeral.Natural.Relation.Order.Computability
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Syntax.Transitivity

-- [∣ᵣₑₘ]-remainder-dividend : ∀{x y}{r : 𝕟(y)} → (x < y) → (y ∣ᵣₑₘ x)(r) → (x ≡ 𝕟-to-ℕ r)

[∣ᵣₑₘ]-is-division-with-remainder : ∀{x y}{r}{p : (𝐒(y) ∣ᵣₑₘ x)(r)} → ((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p)) ≡ x)
[∣ᵣₑₘ]-is-division-with-remainder {𝟎}             {_}   {𝟎}   {DivRem𝟎} = [≡]-intro
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(𝕟-to-ℕ r)} {𝐒 y} {𝐒 r} {DivRem𝟎} = [≡]-intro
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(x + y)} {y} {𝟎}   {DivRem𝐒 {x = x} p} =
  𝐒([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)         🝖[ _≡_ ]-[ [⋅]-with-[𝐒]ₗ {[∣ᵣₑₘ]-quotient p}{𝐒(y)} ]
  (([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + 𝐒(y) 🝖[ _≡_ ]-[]
  𝐒((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + y) 🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₂ₗ(_+_)(y) ([∣ᵣₑₘ]-is-division-with-remainder {p = p})) ]
  𝐒(x + y)                            🝖-end
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(x + y)} {y} {r} {DivRem𝐒 {x = x} p} =
  (([∣ᵣₑₘ]-quotient (DivRem𝐒 p)) ⋅ 𝐒(y)) + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[]
  (𝐒([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y))          + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(𝕟-to-ℕ r) ([⋅]-with-[𝐒]ₗ {[∣ᵣₑₘ]-quotient p}{𝐒(y)}) ]
  ((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + 𝐒(y))  + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {a = ([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)}{b = 𝐒(y)}{c = 𝕟-to-ℕ r} ]
  ((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ r)) + 𝐒(y)  🝖[ _≡_ ]-[]
  𝐒(((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ r)) + y)  🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₂ₗ(_+_)(y) ([∣ᵣₑₘ]-is-division-with-remainder {p = p})) ]
  𝐒(x + y)                                                 🝖-end 

[∣ᵣₑₘ]-quotient-of-1 : ∀{x}{r}{p : (1 ∣ᵣₑₘ x)(r)} → ([∣ᵣₑₘ]-quotient p ≡ x)
[∣ᵣₑₘ]-quotient-of-1 {𝟎}  {𝟎} {DivRem𝟎}   = [≡]-intro
[∣ᵣₑₘ]-quotient-of-1 {𝐒 x}{𝟎} {DivRem𝐒 p} = [≡]-with(𝐒) ([∣ᵣₑₘ]-quotient-of-1 {x}{𝟎} {p})

[⌊/⌋][∣ᵣₑₘ]-quotient-equality : ∀{x y r}{p : (𝐒(y) ∣ᵣₑₘ x)(r)} → ((x ⌊/⌋ 𝐒(y)) ≡ [∣ᵣₑₘ]-quotient p)
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝟎}             {_}   {𝟎}   {DivRem𝟎} = [≡]-intro
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(𝕟-to-ℕ r)} {𝐒 y} {𝐒 r} {DivRem𝟎} =
  ([ 0 , 𝐒(y) ] (𝕟-to-ℕ r) div y) 🝖[ _≡_ ]-[ inddiv-smaller(𝕟.bounded{y}{r}) ]
  𝟎                               🝖-end
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 x} {𝟎} {𝟎} {DivRem𝐒 p} = [≡]-with(𝐒) $
  ([ 0 , 0 ] x div 0) 🝖[ _≡_ ]-[ [⌊/⌋]-of-1ᵣ ]
  x                   🝖[ _≡_ ]-[ [∣ᵣₑₘ]-quotient-of-1 ]-sym
  [∣ᵣₑₘ]-quotient p   🝖-end
[⌊/⌋][∣ᵣₑₘ]-quotient-equality {𝐒 .(x + y)} {y} {r} {DivRem𝐒 {x = x} p} =
  ([ 0 , (y) ] (𝐒(x) + y) div y) 🝖[ _≡_ ]-[ inddiv-step-denominator{0}{(y)}{𝐒(x)}{y} ]
  ([ 0 , (y) ] 𝐒(x) div 𝟎)       🝖[ _≡_ ]-[]
  𝐒([ 0 , y ] x div y)           🝖[ _≡_ ]-[ [≡]-with(𝐒) ([⌊/⌋][∣ᵣₑₘ]-quotient-equality {p = p}) ]
  𝐒([∣ᵣₑₘ]-quotient p)           🝖-end

[mod][∣ᵣₑₘ]-remainder-equality : ∀{x y r}{p : (𝐒(y) ∣ᵣₑₘ x)(r)} → ((x mod 𝐒(y)) ≡ 𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p))
[mod][∣ᵣₑₘ]-remainder-equality {𝟎}             {_}   {𝟎}   {DivRem𝟎} = [≡]-intro
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 .(𝕟-to-ℕ r)} {𝐒 y} {𝐒 r} {DivRem𝟎} = mod'-result-lesser {1}{𝐒(y)}{𝕟-to-ℕ r}{y} ⦃ [≤]-without-[𝐒] 𝕟.bounded ⦄
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 x}        {𝟎} {𝟎} {DivRem𝐒 p}         = mod-of-1 {x}
[mod][∣ᵣₑₘ]-remainder-equality {𝐒 .(x + y)} {y} {r} {DivRem𝐒 {x = x} p} =
  ([ 𝟎 , y ] 𝐒(x + y) mod' y)           🝖[ _≡_ ]-[]
  ([ 𝟎 , y ] (𝐒(x) + y) mod' y)         🝖[ _≡_ ]-[ [mod₀]-2-2ₗ {0}{y}{x}{y} ]
  ([ 𝟎 , y ] x mod' y)                  🝖[ _≡_ ]-[ [mod][∣ᵣₑₘ]-remainder-equality {p = p} ]
  𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p)           🝖[ _≡_ ]-[]
  𝕟-to-ℕ ([∣ᵣₑₘ]-remainder (DivRem𝐒 p)) 🝖-end

-- ⌊/⌋-when-zero : ∀{x y} → (x ⌊/⌋ 𝐒(y) ≡ 𝟎) → (x ≡ 0)
-- ⌊/⌋-when-positive : ∀{x y q} → (x ⌊/⌋ 𝐒(y) ≡ 𝐒(q)) → ∃(x₀ ↦ (x ≡ x₀ + 𝐒(y)))

{-∃.witness ([∣ᵣₑₘ]-existence {x} {y}) = ℕ-to-𝕟 (x mod 𝐒(y)) ⦃ {![↔]-to-[→] decide-is-true mod-maxᵣ!} ⦄
∃.proof ([∣ᵣₑₘ]-existence {x} {y}) with x ⌊/⌋ 𝐒(y)
... | 𝟎    with [≡]-intro ← ⌊/⌋-when-zero {x}{y} {!!} = DivRem𝟎
-- ... | 𝐒(q) with [∃]-intro x₀ ⦃ [≡]-intro ⦄ ← ⌊/⌋-when-positive {x}{y} {!!} with _ ← ∃.proof ([∣ᵣₑₘ]-existence {x₀} {y}) = DivRem𝐒 {!!} -- TODO: (x₀ < x) intuitively, but the termination checker will probably not catch this.
... | 𝐒(q) with [∃]-intro x₀ ⦃ [≡]-intro ⦄ ← ⌊/⌋-when-positive {x}{y} {!!} with <>
∃.proof ([∣ᵣₑₘ]-existence {𝐒 .(x₀ + y)} {y}) | 𝐒(q) | _ with _ ← ∃.proof ([∣ᵣₑₘ]-existence {x₀} {y}) = DivRem𝐒 {!!}
-}

{-
[∣ᵣₑₘ]-existence2 : ∀{x y} → (𝐒(y) ∣ᵣₑₘ x)(ℕ-to-𝕟 (x mod 𝐒(y)) ⦃ {![↔]-to-[→] decide-is-true mod-maxᵣ!} ⦄)
[∣ᵣₑₘ]-existence2 {x} {y} with x ⌊/⌋ 𝐒(y)
... | 𝟎    with [≡]-intro ← ⌊/⌋-when-zero {x}{y} {!!} = DivRem𝟎
... | 𝐒(q) with [∃]-intro x₀ ⦃ [≡]-intro ⦄ ← ⌊/⌋-when-positive {x}{y} {!!} with <>
[∣ᵣₑₘ]-existence2 {𝐒 .(x₀ + y)} {y} | 𝐒(q) | _ with _ ← [∣ᵣₑₘ]-existence2 {x₀} {y} = DivRem𝐒 {!!}
-}

DivRem𝟎Alt : ∀{x y} → (xy : (x < y)) → (y ∣ᵣₑₘ x)(ℕ-to-𝕟 x ⦃ [↔]-to-[→] (ComputablyDecidable.proof-istrue(_<_)) xy ⦄)
DivRem𝟎Alt {x} {𝐒 y} ([≤]-with-[𝐒] ⦃ p ⦄) = [≡]-substitutionᵣ (𝕟.𝕟-ℕ-inverse) {expr ↦ (𝐒 y ∣ᵣₑₘ expr)(ℕ-to-𝕟 x)} ((DivRem𝟎{𝐒(y)}{ℕ-to-𝕟 x})) where
  instance
    x<𝐒y : IsTrue (x <? 𝐒(y))
    x<𝐒y = [↔]-to-[→] (ComputablyDecidable.proof-istrue(_<_)) ([≤]-with-[𝐒] ⦃ p ⦄)

DivRem𝐒Alt : ∀{x y}{r : 𝕟(y)} → (x ≥ y) → (y ∣ᵣₑₘ x −₀ y)(r) → (y ∣ᵣₑₘ x)(r)
DivRem𝐒Alt{x}{𝟎}{}
DivRem𝐒Alt{x}{𝐒(y)}{r} xy = [≡]-substitutionᵣ ([↔]-to-[→] ([−₀][+]-nullify2ᵣ{𝐒(y)}{x}) xy) {\expr → (𝐒(y) ∣ᵣₑₘ expr) r} ∘ DivRem𝐒{𝐒(y)}{x −₀ 𝐒(y)}{r}

[∣ᵣₑₘ]-existence : ∀{x y} → ∃(𝐒(y) ∣ᵣₑₘ x)
[∣ᵣₑₘ]-existence {x} {y} = [ℕ]-strong-induction {φ = x ↦ ∃(𝐒(y) ∣ᵣₑₘ x)} base step {x} where
  base : ∃(𝐒(y) ∣ᵣₑₘ 𝟎)
  base = [∃]-intro 𝟎 ⦃ DivRem𝟎 ⦄

  step : ∀{i} → (∀{j} → (j ≤ i) → ∃(𝐒(y) ∣ᵣₑₘ j)) → ∃(𝐒(y) ∣ᵣₑₘ 𝐒(i))
  step{i} p with [≤][>]-dichotomy {y}{i}
  ... | [∨]-introₗ yi = [∃]-map-proof (DivRem𝐒Alt([≤]-with-[𝐒] ⦃ yi ⦄)) (p{𝐒(i) −₀ 𝐒(y)} ([−₀]-lesser {i}{y}))
  ... | [∨]-introᵣ 𝐒iy = [∃]-intro (ℕ-to-𝕟 (𝐒(i)) ⦃ [↔]-to-[→] (ComputablyDecidable.proof-istrue(_<_)) 𝐒iy ⦄) ⦃ DivRem𝟎Alt ([≤]-with-[𝐒] ⦃ 𝐒iy ⦄) ⦄

{-
open import Structure.Setoid.Uniqueness
{-[∣ᵣₑₘ]-uniqueness : ∀{x y}{p : ∃(𝐒(y) ∣ᵣₑₘ x)} → (p ≡ [∣ᵣₑₘ]-existence)
[∣ᵣₑₘ]-uniqueness {.(𝕟-to-ℕ r)} {y} {[∃]-intro r ⦃ DivRem𝟎 ⦄} = {![≡]-intro!}
[∣ᵣₑₘ]-uniqueness {.(x + 𝐒 y)} {y} {[∃]-intro r ⦃ DivRem𝐒 {x = x} p ⦄} = {!!}-}
{-[∣ᵣₑₘ]-unique-remainder : ∀{x y} → Unique(𝐒(y) ∣ᵣₑₘ x)
[∣ᵣₑₘ]-unique-remainder {.(𝕟-to-ℕ a)} {y} {a} {b} DivRem𝟎 q = {!!}
[∣ᵣₑₘ]-unique-remainder {.(x + 𝐒 y)} {y} {a} {b} (DivRem𝐒 {x = x} p) q = {!!}-}
open import Type.Properties.MereProposition
[∣ᵣₑₘ]-mereProposition : ∀{x y}{r : 𝕟(𝐒(y))} → MereProposition((𝐒(y) ∣ᵣₑₘ x)(r))
[∣ᵣₑₘ]-mereProposition = intro proof where
  proof : ∀{x y}{r : 𝕟(𝐒(y))}{p q : (𝐒(y) ∣ᵣₑₘ x)(r)} → (p ≡ q)
  proof {.(𝕟-to-ℕ r)} {y} {r} {DivRem𝟎} {q} = {!!}
  proof {.(x + 𝐒 y)} {y} {r} {DivRem𝐒 {x = x} p} {q} = {!p!}

  -- testor : ∀{y x}{r : 𝕟(𝐒 y)}{p : (𝐒(y) ∣ᵣₑₘ x)(r)} → (p ≡ DivRem𝟎) ∨ ∃(q ↦ (p ≡ DivRem𝐒 q))

  -- TODO: Maybe by injectivity of 𝕟-to-ℕ?
  test : ∀{y}{r : 𝕟(𝐒 y)}{p : (𝐒(y) ∣ᵣₑₘ (𝕟-to-ℕ r))(r)} → (p ≡ DivRem𝟎)
{-  test {y} {r} {p} with 𝕟-to-ℕ r
  test {_} {_} {_} | 𝟎 = {!!}-}
-}
