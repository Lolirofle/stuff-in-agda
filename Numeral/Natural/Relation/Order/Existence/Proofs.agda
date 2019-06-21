module Numeral.Natural.Relation.Order.Existence.Proofs{ℓ} where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Propositional.Theorems{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Induction{ℓ}
import      Numeral.Natural.Relation.Order{ℓ} as [≤def]
open import Numeral.Natural.Relation.Order.Existence{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] x≡y = [∃]-intro 0 ⦃ x≡y ⦄

[≤]-minimum : ∀{x : ℕ} → (0 ≤ x)
[≤]-minimum {x} = [∃]-intro x ⦃ [+]-identityₗ ⦄
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
[≤][0]ᵣ-negation {x} (Sx≤0) = [𝐒]-not-0([↔]-elimᵣ([≤][0]ᵣ {𝐒(x)}) (Sx≤0))

[≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
[≤]-successor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ [≡]-with(𝐒) (proof) ⦄
-- a + n ≡ b //f
-- a + ? ≡ 𝐒(b) //What value works if f?
-- a + 𝐒(n) ≡ 𝐒(b)
-- 𝐒(a + n) ≡ 𝐒(b) //[≡]-with(𝐒) f

[≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
[≤]-predecessor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ proof ⦄

[≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
[≤]-with-[𝐒] {a} {b} ([∃]-intro n ⦃ f ⦄) =
  [∃]-intro
    (n)
   ⦃
      ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
      🝖 ([≡]-with(𝐒) f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
    ⦄

[≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))
[≤]-without-[𝐒] {𝟎}   {b}    (_)                    = [≤]-minimum
[≤]-without-[𝐒] {𝐒(a)}{𝟎}    ()
[≤]-without-[𝐒] {𝐒(a)}{𝐒(b)} ([∃]-intro(n) ⦃ proof ⦄) = [≤]-with-[𝐒] {a}{b} ([≤]-without-[𝐒] {a}{b} ([∃]-intro(n) ⦃ [𝐒]-injectivity proof ⦄))

[≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
[≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
[≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

instance
  [≤]-transitivity : Transitivity (_≤_)
  transitivity ⦃ [≤]-transitivity ⦄ {a}{b}{c} ([∃]-intro n₁ ⦃ a+n₁≡b ⦄) ([∃]-intro n₂ ⦃ b+n₂≡c ⦄) =
    [∃]-intro
      (n₁ + n₂)
     ⦃
        (symmetry ([+]-associativity {a} {n₁} {n₂})) -- a+(n₁+n₂) = (a+n₁)+n₂
        🝖 ([≡]-with(expr ↦ expr + n₂) (a+n₁≡b)) -- (a+n₁)+n₂ = b+n₂
        🝖 (b+n₂≡c) -- b+n₂ = c
      ⦄ -- a+(n₁+n₂) = c

instance
  [≤]-reflexivity : Reflexivity (_≤_)
  reflexivity ⦃ [≤]-reflexivity ⦄ = [≡]-to-[≤] [≡]-intro

instance
  [≤]-antisymmetry : Antisymmetry (_≤_) (_≡_)
  antisymmetry ⦃ [≤]-antisymmetry ⦄ {a} {b} ([∃]-intro(n₁) ⦃ a+n₁≡b ⦄) ([∃]-intro(n₂) ⦃ b+n₂≡a ⦄) = [≡]-elimᵣ (n₁≡0) {n ↦ (a + n ≡ b)} (a+n₁≡b) where
    n₁+n₂≡0 : ((n₁ + n₂) ≡ 0)
    n₁+n₂≡0 =
      [+]-injectivityᵣ(
        (symmetry([+]-associativity {a} {n₁} {n₂}))
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
[≥]-is-[≮] {a}{b} (b≤a) (Sa≤b) = [≤][𝐒]ₗ (transitivity {_}{_}{𝐒(a)}{b}{a} (Sa≤b) (b≤a))

-- [≤]-is-[≯] : ∀{a b : ℕ} → ¬(a > b) ← (a ≤ b)
-- [≤]-is-[≯] {a}{b} = [≥]-is-[≮] {b}{a}

-- [>]-is-[≰] : ∀{a b : ℕ} → ¬(a ≤ b) ← (a > b)
-- [>]-is-[≰] {a}{b} (Sb≤a) (a≤b) = [≤]-is-[≯] {a}{b} (a≤b) (Sb≤a)

-- [<]-is-[≱] : ∀{a b : ℕ} → ¬(a ≥ b) ← (a < b)
-- [<]-is-[≱] {a}{b} = [>]-is-[≰] {b}{a}

instance
  [≤]-totality : SymmetricallyTotal(_≤_)
  converseTotal ⦃ [≤]-totality ⦄ {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
  converseTotal ⦃ [≤]-totality ⦄ {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
  converseTotal ⦃ [≤]-totality ⦄ {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
  converseTotal ⦃ [≤]-totality ⦄ {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ ([≤]-with-[𝐒] {a}{b})) ([∨]-introᵣ ∘ ([≤]-with-[𝐒] {b}{a})) (converseTotal ⦃ [≤]-totality ⦄ {a}{b})

[≤]-equivalence : ∀{x y} → (x ≤ y) ↔ (x [≤def].≤ y)
[≤]-equivalence{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x [≤def].≤ y)
  l{𝟎}   {y}    ([≤def].[≤]-minimum)      = [∃]-intro(y) ⦃ [≡]-intro ⦄
  l{𝐒(x)}{𝟎}    ()
  l{𝐒(x)}{𝐒(y)} ([≤def].[≤]-with-[𝐒] ⦃ proof ⦄) = [≤]-with-[𝐒] {x}{y} (l{x}{y} (proof))

  r : ∀{x y} → (x ≤ y) → (x [≤def].≤ y)
  r{𝟎}   {y}    ([∃]-intro(z) ⦃ 𝟎+z≡y   ⦄) = [≤def].[≤]-minimum
  r{𝐒(x)}{𝟎}    ([∃]-intro(z) ⦃ ⦄)
  r{𝐒(x)}{𝐒(y)} ([∃]-intro(z) ⦃ 𝐒x+z≡𝐒y ⦄) = [≤def].[≤]-with-[𝐒] ⦃ r{x}{y} ([∃]-intro(z) ⦃ [𝐒]-injectivity(𝐒x+z≡𝐒y) ⦄ ) ⦄
