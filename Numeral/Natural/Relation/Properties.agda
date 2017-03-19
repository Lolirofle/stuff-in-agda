module Numeral.Natural.Relation.Properties where

import Level as Lvl
open import Data
open import Logic(Lvl.𝟎)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
open import Relator.Equals(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)
open import Structure.Relator.Properties(Lvl.𝟎)
open import Type

[≤][0]-minimum : ∀{x : ℕ} → (0 ≤ x)
[≤][0]-minimum {0}    = [≤]-from-[≡]([≡]-intro :of: (0 ≡ 0))
[≤][0]-minimum {𝐒(n)} = [≤]-next(([≤][0]-minimum {n}) , [≡]-intro)

-- [≤]-successorᵣ : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
-- [≤]-successorᵣ([≤]-from-[≡] a≡b) = [≤]-next(([≤]-successorᵣ a≡b) , a≡b)
-- [≤]-successorᵣ([≤]-next(a≤x , 𝐒x≡b)) = [≤]-next(([≤]-successorᵣ a≤b) , [≡]-intro)

-- [≤]-with-[𝐒] : {a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
-- [≤]-with-[𝐒] ([≤]-from-[≡] a≡b) = [≤]-from-[≡]([≡]-with-[ 𝐒 ](a≡b))
-- [≤]-with-[𝐒] ([≤]-next(a≤x , Sx≡b)) =
--   ([≤]-with-[𝐒] a≤x)
--   ()
-- 𝐒(a) ≤ 𝐒(b)
--   a ≤ x
--   𝐒(a) ≤ 𝐒(x)

--   𝐒(x) = b
--   𝐒(x) ≤ b
--   ?

-- [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
-- [≤]-antisymmetry([≤]-from-[≡] a≡b , _) = a≡b
-- [≤]-antisymmetry(_ , [≤]-from-[≡] b≡a) = [≡]-symmetry b≡a
-- [≤]-antisymmetry([≤]-next(a≤x₁ , sx₁≡b) , [≤]-next(b≤x₂ , sx₂≡a)) =
--   ([≡]-transitivity([∧]-intro
--     ([≡]-symmetry sx₂≡a)
--     (sx₁≡b)
--   ))
-- ∀{x₁} → ((a ≤ x₁) ∧ (𝐒(x₁) ≡ b)) → (a ≤ b)
-- ∀{x₂} → ((b ≤ x₂) ∧ (𝐒(x₂) ≡ a)) → (b ≤ a)
-- a ≤ x₁
-- 𝐒(a) ≤ 𝐒(x₁)
-- 𝐒(a) ≤ b
