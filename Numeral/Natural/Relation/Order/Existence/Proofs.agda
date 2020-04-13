module Numeral.Natural.Relation.Order.Existence.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order.Existence
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
import      Structure.Relator.Names as Names
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] x≡y = [∃]-intro 0 ⦃ x≡y ⦄

[≤]-minimum : ∀{x : ℕ} → (0 ≤ x)
[≤]-minimum {x} = [∃]-intro x ⦃ [+]-identityₗ-raw ⦄
-- [∃]-intro {ℕ} {\n → 0 + n ≡ x} (x) ⦃ [+]-identityₗ ⦄

[≤][0]ᵣ : ∀{x : ℕ} → (x ≤ 0) ↔ (x ≡ 0)
[≤][0]ᵣ {𝟎} = [↔]-intro l r where
  l : (𝟎 ≤ 0) ← (𝟎 ≡ 0)
  l refl = [≡]-to-[≤] refl

  r : (𝟎 ≤ 0) → (𝟎 ≡ 0)
  r _ = [≡]-intro
[≤][0]ᵣ {𝐒(n)} = [↔]-intro l r where
  l : (𝐒(n) ≤ 0) ← (𝐒(n) ≡ 0)
  l ()

  r : (𝐒(n) ≤ 0) → (𝐒(n) ≡ 0)
  r ([∃]-intro _ ⦃ ⦄ )

[≤][0]ᵣ-negation : ∀{x : ℕ} → ¬(𝐒(x) ≤ 0)
[≤][0]ᵣ-negation {x} (Sx≤0) = [𝐒]-not-0([↔]-to-[→] ([≤][0]ᵣ {𝐒(x)}) (Sx≤0))

[≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
[≤]-successor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(𝐒) (proof) ⦄
-- a + n ≡ b //f
-- a + ? ≡ 𝐒(b) //What value works if f?
-- a + 𝐒(n) ≡ 𝐒(b)
-- 𝐒(a + n) ≡ 𝐒(b) //congruence₁(𝐒) f

[≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
[≤]-predecessor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ proof ⦄

[≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))
[≤]-without-[𝐒] {𝟎}   {b}    (_)                    = [≤]-minimum
[≤]-without-[𝐒] {𝐒(a)}{𝟎}    ()
[≤]-without-[𝐒] {𝐒(a)}{𝐒(b)} ([∃]-intro(n) ⦃ proof ⦄) = [≤]-with-[𝐒] {a}{b} ([≤]-without-[𝐒] {a}{b} ([∃]-intro(n) ⦃ [𝐒]-injectivity-raw proof ⦄))

[≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
[≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
[≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

instance
  [≤]-transitivity : Transitivity (_≤_)
  Transitivity.proof [≤]-transitivity {a}{b}{c} ([∃]-intro n₁ ⦃ a+n₁≡b ⦄) ([∃]-intro n₂ ⦃ b+n₂≡c ⦄) =
    [∃]-intro
      (n₁ + n₂)
     ⦃
        (symmetry(_≡_) ([+]-associativity-raw {a} {n₁} {n₂})) -- a+(n₁+n₂) = (a+n₁)+n₂
        🝖 ([≡]-with(expr ↦ expr + n₂) (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
        🝖 (b+n₂≡c) -- b+n₂ = c
      ⦄ -- a+(n₁+n₂) = c

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  Reflexivity.proof [≤]-reflexivity = [≡]-to-[≤] [≡]-intro

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  Antisymmetry.proof [≤]-antisymmetry {a} {b} ([∃]-intro(n₁) ⦃ a+n₁≡b ⦄) ([∃]-intro(n₂) ⦃ b+n₂≡a ⦄) = [≡]-elimᵣ (n₁≡0) {n ↦ (a + n ≡ b)} (a+n₁≡b) where
    n₁+n₂≡0 : ((n₁ + n₂) ≡ 0)
    n₁+n₂≡0 =
      [+]ᵣ-injectivity-raw(
        (symmetry(_≡_) ([+]-associativity-raw {a} {n₁} {n₂}))
        🝖 ([≡]-with(expr ↦ expr + n₂) a+n₁≡b)
        🝖 b+n₂≡a
      )
    n₁≡0 : (n₁ ≡ 0)
    n₁≡0 = [+]-sum-is-0ₗ {n₁} {n₂} n₁+n₂≡0
  -- a+n₁ = b
  -- (a+n₁)+n₂ = b+n₂
  -- (a+n₁)+n₂ = a
  -- a+(n₁+n₂) = a
  -- a+(n₁+n₂) = a+0
  -- n₁+n₂ = 0
  -- a = b

instance
  [≤]-weakPartialOrder : Weak.PartialOrder (_≤_) (_≡_)
  [≤]-weakPartialOrder = record{
      antisymmetry = [≤]-antisymmetry;
      transitivity = [≤]-transitivity;
      reflexivity  = [≤]-reflexivity
    }

[<]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
[<]-minimum {x} = [≤]-with-[𝐒] {0} ([≤]-minimum)

[≥]-is-[≮] : ∀{a b : ℕ} → ¬(a < b) ← (a ≥ b)
[≥]-is-[≮] {a}{b} (b≤a) (Sa≤b) = [≤][𝐒]ₗ (transitivity(_≤_) {x = 𝐒(a)}{y = b}{z = a} (Sa≤b) (b≤a))

-- [≤]-is-[≯] : ∀{a b : ℕ} → ¬(a > b) ← (a ≤ b)
-- [≤]-is-[≯] {a}{b} = [≥]-is-[≮] {b}{a}

-- [>]-is-[≰] : ∀{a b : ℕ} → ¬(a ≤ b) ← (a > b)
-- [>]-is-[≰] {a}{b} (Sb≤a) (a≤b) = [≤]-is-[≯] {a}{b} (a≤b) (Sb≤a)

-- [<]-is-[≱] : ∀{a b : ℕ} → ¬(a ≥ b) ← (a < b)
-- [<]-is-[≱] {a}{b} = [>]-is-[≰] {b}{a}

[≤]-totality-raw : Names.ConverseTotal(_≤_)
[≤]-totality-raw {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
[≤]-totality-raw {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
[≤]-totality-raw {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
[≤]-totality-raw {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ ([≤]-with-[𝐒] {a}{b})) ([∨]-introᵣ ∘ ([≤]-with-[𝐒] {b}{a})) ([≤]-totality-raw {a}{b})


instance
  [≤]-totality : ConverseTotal(_≤_)
  ConverseTotal.proof [≤]-totality = [≤]-totality-raw

