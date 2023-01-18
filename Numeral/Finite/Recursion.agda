module Numeral.Finite.Recursion where

open import Data
open import Logic.Propositional
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
open import Type

private variable ℓ : Lvl.Level
private variable b₁ b₂ N : ℕ
private variable n x y x₁ x₂ y₁ y₂ : 𝕟(N)

module _
  (T : ∀{n} → 𝕟(n) → Type{ℓ})
  (zero : ∀{N} → ⦃ pos : ℕ.Positive(N) ⦄ → T{N}(minimum))
  (succ : ∀{N} → (i : 𝕟(N)) → T(𝐒(i)))
  where

  𝕟-case : ∀{N} → (n : 𝕟(N)) → T(n)
  𝕟-case 𝟎      = zero
  𝕟-case (𝐒(i)) = succ i

module _
  (T : ∀{n} → 𝕟(n) → Type{ℓ})
  (base : ∀{N} → ⦃ pos : ℕ.Positive(N) ⦄ → T{N}(minimum))
  (step : ∀{N} → (i : 𝕟(N)) → T(i) → T(𝐒(i)))
  where

  𝕟-elim : ∀{N} → (n : 𝕟(N)) → T(n)
  𝕟-elim{𝐒 N} 𝟎     = base
  𝕟-elim{𝐒 N} (𝐒 n) = step n (𝕟-elim{N} n)

module _
  (P : ∀{N} → 𝕟(N) → Type{ℓ})
  (rec : ∀{N} → (n : 𝕟(N)) → (∀{I} → (i : 𝕟(I)) → (i < n) → P(i)) → P(n))
  where

  𝕟-strong-recursion : ∀{N} → (n : 𝕟(N)) → P(n)
  𝕟-strong-recursion n = 𝕟-elim(\n → ∀{I} → (i : 𝕟(I)) → (i < n) → P(i))
    (\i imin → empty([<]-minimumᵣ {a = i} imin))
    (\n prev i i𝐒n → rec i (\j ji → prev j ([<][≤]-subtransitivityᵣ-raw {a = j}{b = i}{c = n} ji ([↔]-to-[←] ([≤][<]-convert {a = i}{b = n}) i𝐒n))))
    (𝐒(n)) n ([<]-of-successor {a = n})

open import Functional

-- TODO: Is this necessary?
𝕟-strong-recursion₂ : (P : ∀{N₁ N₂} → 𝕟(N₁) → 𝕟(N₂) → Type{ℓ}) → (∀{X Y} → (x : 𝕟(X)) → (y : 𝕟(Y)) → (∀{I J} → (i : 𝕟(I)) → (j : 𝕟(J)) → (i < x) ∨ ((i ≤ x) ∧ (j < y)) → P i j) → P x y) → (∀{N₁ N₂} → (x : 𝕟(N₁)) → (y : 𝕟(N₂)) → P x y)
𝕟-strong-recursion₂ P rec x y =
  𝕟-strong-recursion(\x → ∀{Y} → (y : 𝕟(Y)) → P x y) (\x prevX y →
  𝕟-strong-recursion(\y → ∀{X} → (x₂ : 𝕟(X)) → (x₂ ≤ x) → P x₂ y) (\y prevY x x₂x → rec x y \i j → [∨]-elim
    (\ix → prevX i ([<][≤]-subtransitivityᵣ-raw {a = i}{b = x} ix x₂x) j)
    (\([∧]-intro ix jy) → prevY j jy i ([≤]-transitivity-raw {a = i}{b = x} ix x₂x))
  ) y x ([≤]-reflexivity-raw {a = x}))
  x y
