module Numeral.Natural.Finite where

import Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Structure.Function.Domain
open import Type

-- A structure corresponding to a finite set of natural numbers (0,..,n).
-- Positive integers including zero less than a specified integer (0≤_≤n).
-- This structure works in the following way:
--   • Finite-𝟎 can always be constructed, for any upper bound (n).
--   • Finite-𝐒 can only be constructed from a smaller upper bounded Finite-ℕ.
--       Example: A Finite-ℕ constructed through Finite-𝐒{3} can only be the following:
--         0 ≡ Finite-𝟎{3}
--         1 ≡ Finite-𝐒{3} (Finite-𝟎{2})
--         2 ≡ Finite-𝐒{3} (Finite-𝐒{2} (Finite-𝟎{1}))
--         3 ≡ Finite-𝐒{3} (Finite-𝐒{2} (Finite-𝐒{1} (Finite-𝟎{0})))
--         because there is nothing that could fill the blank in (Finite-𝐒{3} (Finite-𝐒{2} (Finite-𝐒{1} (Finite-𝐒{0} (_))))).
--       The smallest upper bound that can be is 0 (from using ℕ and its definition).
--       This limits how many successors (Finite-𝐒) that can "fit".
data Finite-ℕ : ℕ → Set where
  Finite-𝟎 : ∀{n} → Finite-ℕ(n)                   -- Zero
  Finite-𝐒 : ∀{n} → Finite-ℕ(n) → Finite-ℕ(𝐒(n)) -- Successor function
{-# INJECTIVE Finite-ℕ #-}

-- Definition of a finite set/type
Finite : ∀{ℓ₁ ℓ₂} → Type{ℓ₂} → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Finite {ℓ₁}{ℓ₂} (T) = ∃{ℓ₁ Lvl.⊔ ℓ₂}{Lvl.𝟎}{ℕ}(n ↦ (∃{ℓ₁}{ℓ₂}{T → Finite-ℕ(n)}(f ↦ Injective{ℓ₁}(f))))
-- TODO: Create a module Relator.Injection like Relator.Bijection

[Finite-ℕ]-to-[ℕ] : ∀{n} → Finite-ℕ(n) → ℕ
[Finite-ℕ]-to-[ℕ] (Finite-𝟎)    = 𝟎
[Finite-ℕ]-to-[ℕ] (Finite-𝐒(n)) = 𝐒([Finite-ℕ]-to-[ℕ] (n))

module Theorems{ℓ} where
  open import Numeral.Natural.Function
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Properties{ℓ}
  open import Relator.Equals{ℓ}{Lvl.𝟎}

  upscale-𝐒 : ∀{n} → Finite-ℕ(n) → Finite-ℕ(𝐒(n))
  upscale-𝐒 (Finite-𝟎)    = Finite-𝟎
  upscale-𝐒 (Finite-𝐒(n)) = Finite-𝐒(upscale-𝐒 (n))

  upscale-[+] : ∀{n₁ n₂} → Finite-ℕ(n₁) → Finite-ℕ(n₁ + n₂)
  upscale-[+] (Finite-𝟎) = Finite-𝟎
  upscale-[+] {𝐒(n₁)}{n₂}(Finite-𝐒(n)) =
    [≡]-substitutionₗ ([+1]-commutativity{n₁}{n₂}) {Finite-ℕ} (Finite-𝐒{n₁ + n₂}(upscale-[+] {n₁}{n₂} (n)))

  upscale-maxₗ : ∀{n₁ n₂} → Finite-ℕ(n₁) → Finite-ℕ(max n₁ n₂)
  upscale-maxₗ {n₁}{n₂} = upscale-[+] {n₁}{n₂ −₀ n₁}

  upscale-maxᵣ : ∀{n₁ n₂} → Finite-ℕ(n₂) → Finite-ℕ(max n₁ n₂)
  upscale-maxᵣ {n₁}{n₂} (n) = [≡]-substitutionᵣ (Theorems.max-commutativity{ℓ}{n₂}{n₁}) {Finite-ℕ} (upscale-maxₗ {n₂}{n₁} (n))
