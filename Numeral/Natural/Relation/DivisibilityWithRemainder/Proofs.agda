module Numeral.Natural.Relation.DivisibilityWithRemainder.Proofs where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Finite
import      Numeral.Finite.Proofs as 𝕟
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.DivisibilityWithRemainder hiding (base₀ ; base₊ ; step)
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Relator
open import Syntax.Transitivity
open import Type.Properties.Decidable.Proofs

-- 0 does not divide anything with any remainder.
[∣ᵣₑₘ]-0-divides : ∀{x}{r} → ¬(0 ∣ᵣₑₘ x)(r)
[∣ᵣₑₘ]-0-divides {r = ()}

-- 1 divides everything with the only possible remainder 0.
[∣ᵣₑₘ]-1-divides : ∀{x}{r} → (1 ∣ᵣₑₘ x)(r)
[∣ᵣₑₘ]-1-divides {𝟎}   {r = 𝟎} = DivRem𝟎
[∣ᵣₑₘ]-1-divides {𝐒 x} {r = 𝟎} = DivRem𝐒 [∣ᵣₑₘ]-1-divides

-- The quotient is the dividend when divided by 1.
[∣ᵣₑₘ]-quotient-of-1 : ∀{x}{r} → (p : (1 ∣ᵣₑₘ x)(r)) → ([∣ᵣₑₘ]-quotient p ≡ x)
[∣ᵣₑₘ]-quotient-of-1 {𝟎}  {𝟎} DivRem𝟎     = [≡]-intro
[∣ᵣₑₘ]-quotient-of-1 {𝐒 x}{𝟎} (DivRem𝐒 p) = congruence₁(𝐒) ([∣ᵣₑₘ]-quotient-of-1 {x}{𝟎} p)

-- [∣ᵣₑₘ]-remainder-dividend : ∀{x y}{r : 𝕟(y)} → (x < y) → (y ∣ᵣₑₘ x)(r) → (x ≡ 𝕟-to-ℕ r)

-- How the arguments in the divisibility relation is related to each other by elementary functions.
-- Note: The division theorem is proven using this. By proving that [∣ᵣₑₘ]-quotient and [∣ᵣₑₘ]-remainder is equal to the algorithmic functions of floored division and modulo, the theorem follows directly from this.
[∣ᵣₑₘ]-is-division-with-remainder : ∀{x y}{r} → (p : (y ∣ᵣₑₘ x)(r)) → ((([∣ᵣₑₘ]-quotient p) ⋅ y) + (𝕟-to-ℕ ([∣ᵣₑₘ]-remainder p)) ≡ x)
[∣ᵣₑₘ]-is-division-with-remainder {𝟎}             {_}   {𝟎}   DivRem𝟎 = [≡]-intro
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(x + y)}    {𝐒 y} {𝟎}   (DivRem𝐒 {x = x} p) =
  𝐒([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)         🝖[ _≡_ ]-[ [⋅]-with-[𝐒]ₗ {[∣ᵣₑₘ]-quotient p}{𝐒(y)} ]
  (([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + 𝐒(y) 🝖[ _≡_ ]-[]
  𝐒((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + y) 🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₂-₁(_+_)(y) ([∣ᵣₑₘ]-is-division-with-remainder p)) ]
  𝐒(x + y)                            🝖-end
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(𝕟-to-ℕ r)} {𝐒 y} {𝐒 r} DivRem𝟎 = [≡]-intro
[∣ᵣₑₘ]-is-division-with-remainder {𝐒 .(x + y)} {𝐒(y@(𝐒 _))} {r@(𝐒 _)} (DivRem𝐒 {x = x} p) =
  (([∣ᵣₑₘ]-quotient (DivRem𝐒 p)) ⋅ 𝐒(y)) + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[]
  (𝐒([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y))          + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(𝕟-to-ℕ r) ([⋅]-with-[𝐒]ₗ {[∣ᵣₑₘ]-quotient p}{𝐒(y)}) ]
  ((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + 𝐒(y))  + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {a = ([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)}{b = 𝐒(y)}{c = 𝕟-to-ℕ r} ]
  ((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ r)) + 𝐒(y)  🝖[ _≡_ ]-[]
  𝐒(((([∣ᵣₑₘ]-quotient p) ⋅ 𝐒(y)) + (𝕟-to-ℕ r)) + y)  🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₂-₁(_+_)(y) ([∣ᵣₑₘ]-is-division-with-remainder p)) ]
  𝐒(x + y)                                                 🝖-end 

-- When the arguments in the divisibility relation are related to each other.
-- This also indicates that the divisibility relation actually states something about divisibility in the sense of the inverse of multiplication.
[∣ᵣₑₘ]-equivalence : ∀{x y}{r} → (y ∣ᵣₑₘ x)(r) ↔ ∃(q ↦ (q ⋅ y) + (𝕟-to-ℕ r) ≡ x)
[∣ᵣₑₘ]-equivalence = [↔]-intro (p ↦ l {q = [∃]-witness p} ([∃]-proof p)) (p ↦ [∃]-intro ([∣ᵣₑₘ]-quotient p) ⦃ [∣ᵣₑₘ]-is-division-with-remainder p ⦄) where
  l :  ∀{x y q}{r} → ((q ⋅ y) + (𝕟-to-ℕ r) ≡ x) → (y ∣ᵣₑₘ x)(r)
  l {_}{_}{𝟎}  {_} [≡]-intro = DivRem𝟎
  l {x}{y}{𝐒 q}{r} p = substitute₁ᵣ(x ↦ (y ∣ᵣₑₘ x)(r)) eq (DivRem𝐒 (l{(q ⋅ y) + (𝕟-to-ℕ r)}{y}{q}{r} [≡]-intro)) where
    eq =
      ((q ⋅ y) + (𝕟-to-ℕ r)) + y 🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {a = q ⋅ y}{b = 𝕟-to-ℕ r}{c = y} ]
      ((q ⋅ y) + y) + (𝕟-to-ℕ r) 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(𝕟-to-ℕ r) ([⋅]-with-[𝐒]ₗ {q}{y}) ]-sym
      (𝐒(q) ⋅ y) + (𝕟-to-ℕ r)    🝖[ _≡_ ]-[ p ]
      x                          🝖-end

-- ⌊/⌋-when-zero : ∀{x y} → (x ⌊/⌋ 𝐒(y) ≡ 𝟎) → (x ≡ 0)
-- ⌊/⌋-when-positive : ∀{x y q} → (x ⌊/⌋ 𝐒(y) ≡ 𝐒(q)) → ∃(x₀ ↦ (x ≡ x₀ + 𝐒(y)))


{-
[∣ᵣₑₘ]-existence : ∀{x y} → ∃(𝐒(y) ∣ᵣₑₘ x)
∃.witness ([∣ᵣₑₘ]-existence {x} {y}) = ℕ-to-𝕟 (x mod 𝐒(y)) ⦃ {![↔]-to-[→] decide-is-true mod-maxᵣ!} ⦄
∃.proof   ([∣ᵣₑₘ]-existence {x} {y}) = [↔]-to-[←] [∣ᵣₑₘ]-equivalence ([∃]-intro (x ⌊/⌋ 𝐒(y)) ⦃ {!TODO: Insert division theorem here!} ⦄)
-}

DivRem𝟎Alt : ∀{x y} → (xy : (x < y)) → (y ∣ᵣₑₘ x)(ℕ-to-𝕟 x ⦃ [↔]-to-[→] decider-true xy ⦄)
DivRem𝟎Alt {x} {𝐒 y} (succ p) = substitute₁ᵣ(expr ↦ (𝐒 y ∣ᵣₑₘ expr)(ℕ-to-𝕟 x)) (𝕟.𝕟-ℕ-inverse) ((DivRem𝟎{𝐒(y)}{ℕ-to-𝕟 x})) where
  instance
    x<𝐒y : IsTrue (x <? 𝐒(y))
    x<𝐒y = [↔]-to-[→] decider-true ([≤]-with-[𝐒] ⦃ p ⦄)

DivRem𝐒Alt : ∀{x y}{r : 𝕟(y)} → (x ≥ y) → (y ∣ᵣₑₘ x −₀ y)(r) → (y ∣ᵣₑₘ x)(r)
DivRem𝐒Alt{x}{𝟎}{}
DivRem𝐒Alt{x}{𝐒(y)}{r} xy = substitute₁ᵣ(\expr → (𝐒(y) ∣ᵣₑₘ expr) r) ([↔]-to-[→] ([−₀][+]-nullify2ᵣ{𝐒(y)}{x}) xy) ∘ DivRem𝐒{𝐒(y)}{x −₀ 𝐒(y)}{r}

-- Every pair of numbers (positive divisor) when divided will yield a remainder and there is always a proof of it being the case.
-- This is an alternative way of constructing the modulo operator.
[∣ᵣₑₘ]-existence-alt : ∀{x y} → ∃(𝐒(y) ∣ᵣₑₘ x)
[∣ᵣₑₘ]-existence-alt {x} {y} = ℕ-strong-induction {φ = x ↦ ∃(𝐒(y) ∣ᵣₑₘ x)} base step {x} where
  base : ∃(𝐒(y) ∣ᵣₑₘ 𝟎)
  base = [∃]-intro 𝟎 ⦃ DivRem𝟎 ⦄

  step : ∀{i} → (∀{j} → (j ≤ i) → ∃(𝐒(y) ∣ᵣₑₘ j)) → ∃(𝐒(y) ∣ᵣₑₘ 𝐒(i))
  step{i} p with [≤][>]-dichotomy {y}{i}
  ... | [∨]-introₗ yi = [∃]-map-proof (DivRem𝐒Alt([≤]-with-[𝐒] ⦃ yi ⦄)) (p{𝐒(i) −₀ 𝐒(y)} ([−₀]-lesser {i}{y}))
  ... | [∨]-introᵣ 𝐒iy = [∃]-intro (ℕ-to-𝕟 (𝐒(i)) ⦃ [↔]-to-[→] decider-true 𝐒iy ⦄) ⦃ DivRem𝟎Alt ([≤]-with-[𝐒] ⦃ 𝐒iy ⦄) ⦄

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

{-
open import Data.Tuple using (_⨯_ ; _,_)
open import Type.Dependent
open import Type.Properties.MereProposition
[∣ᵣₑₘ]-mereProposition : ∀{x y}{r : 𝕟(y)} → MereProposition((y ∣ᵣₑₘ x)(r))
[∣ᵣₑₘ]-mereProposition = intro {!!} where
  proof : ∀{y}{r : 𝕟(y)} → (p q : Σ(ℕ) (x ↦ (y ∣ᵣₑₘ x)(r))) → (p ≡ q)
  proof {y} {r} (intro .(𝕟-to-ℕ r) DivRem𝟎) (intro .(𝕟-to-ℕ r) DivRem𝟎) = [≡]-intro
  proof {y} {r} (intro .(𝕟-to-ℕ r) DivRem𝟎) (intro .(x₂ + y) (DivRem𝐒{x = x₂} p₂)) = {!!}
  proof {y} {r} (intro .(x₁ + y) (DivRem𝐒{x = x₁} p₁)) (intro .(𝕟-to-ℕ r) DivRem𝟎) = {!!}
  proof {y} {r} (intro .(x₁ + y) (DivRem𝐒{x = x₁} p₁)) (intro .(x₂ + y) (DivRem𝐒{x = x₂} p₂)) = {!congruence₂-₁(_+_)(y) (congruence₁(Σ.left) eq)!} where
    eq = proof (intro x₁ p₁) (intro x₂ p₂)
    test : ∀{a₁ a₂ : A}{b₁ : B(a₁)}{b₂ : B(a₂)} → (a₁ ≡ a₂) → (intro a₁ b₁ ≡ intro a₂ b₂)
-}
