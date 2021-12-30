module Numeral.Natural.Relation.Order.Existence.Proofs where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Induction
open import Numeral.Natural.Relation.Order.Existence
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Properties
import      Structure.Relator.Names as Names
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

[≡]-to-[≤] : ∀{x y : ℕ} → (x ≡ y) → (x ≤ y)
[≡]-to-[≤] x≡y = [∃]-intro 0 ⦃ x≡y ⦄

[≤]-minimum : ∀{x : ℕ} → (0 ≤ x)
[≤]-minimum {x} = [∃]-intro x ⦃ identityₗ(_+_)(𝟎) ⦄

[≤][0]ᵣ : ∀{x : ℕ} → (x ≤ 0) ↔ (x ≡ 0)
[≤][0]ᵣ {𝟎}    = [↔]-intro [≡]-to-[≤] (const [≡]-intro)
[≤][0]ᵣ {𝐒(n)} = [↔]-intro (\()) (\{([∃]-intro _ ⦃ ⦄ )})

[≤][0]ᵣ-negation : ∀{x : ℕ} → ¬(𝐒(x) ≤ 0)
[≤][0]ᵣ-negation {x} (Sx≤0) = [𝐒]-not-0([↔]-to-[→] ([≤][0]ᵣ {𝐒(x)}) (Sx≤0))

[≤]-successor : ∀{a b : ℕ} → (a ≤ b) → (a ≤ 𝐒(b))
[≤]-successor ([∃]-intro(n) ⦃ proof ⦄) = [∃]-intro (𝐒(n)) ⦃ congruence₁(𝐒) (proof) ⦄

[≤]-predecessor : ∀{a b : ℕ} → (𝐒(a) ≤ b) → (a ≤ b)
[≤]-predecessor ([∃]-intro n) = [∃]-intro(𝐒(n))

[≤]-without-[𝐒] : ∀{a b : ℕ} → (a ≤ b) ← (𝐒(a) ≤ 𝐒(b))
[≤]-without-[𝐒] {𝟎}   {b}    (_)                      = [≤]-minimum
[≤]-without-[𝐒] {𝐒(a)}{𝟎}    ()
[≤]-without-[𝐒] {𝐒(a)}{𝐒(b)} ([∃]-intro(n) ⦃ proof ⦄) = [≤]-with-[𝐒] {a}{b} ([≤]-without-[𝐒] {a}{b} ([∃]-intro(n) ⦃ injective(𝐒) proof ⦄))

[≤][𝐒]ₗ : ∀{x : ℕ} → ¬(𝐒(x) ≤ x)
[≤][𝐒]ₗ {𝟎}    (1≤0)    = [≤][0]ᵣ-negation{0}(1≤0)
[≤][𝐒]ₗ {𝐒(n)} (SSn≤Sn) = [≤][𝐒]ₗ {n} ([≤]-without-[𝐒] {𝐒(n)}{n} (SSn≤Sn))

instance
  [≤]-transitivity : Transitivity (_≤_)
  Transitivity.proof [≤]-transitivity {a}{b}{c} ([∃]-intro n₁ ⦃ an₁b ⦄) ([∃]-intro n₂ ⦃ bn₂c ⦄) = [∃]-intro (n₁ + n₂) ⦃ p ⦄ where
    p =
      a + (n₁ + n₂) 🝖[ _≡_ ]-[ associativity(_+_) {a}{n₁}{n₂} ]-sym
      (a + n₁) + n₂ 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(n₂) an₁b ]
      b + n₂        🝖[ _≡_ ]-[ bn₂c ]
      c             🝖-end

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  Reflexivity.proof [≤]-reflexivity = [≡]-to-[≤] [≡]-intro

instance
  [≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
  Antisymmetry.proof [≤]-antisymmetry {a} {b} ([∃]-intro(n₁) ⦃ an₁b ⦄) ([∃]-intro(n₂) ⦃ bn₂a ⦄) =
    a      🝖[ _≡_ ]-[]
    a + 𝟎  🝖[ _≡_ ]-[ congruence₂-₂(_+_)(a) n₁0 ]-sym
    a + n₁ 🝖[ _≡_ ]-[ an₁b ]
    b      🝖-end
    where
      n₁n₂0 : (n₁ + n₂ ≡ 0)
      n₁n₂0 = cancellationₗ(_+_) $
        a + (n₁ + n₂) 🝖[ _≡_ ]-[ associativity(_+_) {a}{n₁}{n₂} ]-sym
        (a + n₁) + n₂ 🝖[ _≡_ ]-[ congruence₂-₁(_+_)(n₂) an₁b ]
        b + n₂        🝖[ _≡_ ]-[ bn₂a ]
        a             🝖[ _≡_ ]-[]
        a + 0         🝖-end

      n₁0 : (n₁ ≡ 0)
      n₁0 = [∧]-elimₗ ([+]-sum-is-0 {n₁} {n₂} n₁n₂0)

instance
  [≤]-weakPartialOrder : Weak.PartialOrder(_≤_)
  [≤]-weakPartialOrder = record{}

[<]-minimum : ∀{x : ℕ} → (0 < 𝐒(x))
[<]-minimum = [≤]-with-[𝐒] {0} [≤]-minimum

[≥]-is-[≮] : ∀{a b : ℕ} → ¬(a < b) ← (a ≥ b)
[≥]-is-[≮] {a}{b} b≤a Sa≤b = [≤][𝐒]ₗ (transitivity(_≤_) {x = 𝐒(a)}{y = b}{z = a} Sa≤b b≤a)

-- [≤]-is-[≯] : ∀{a b : ℕ} → ¬(a > b) ← (a ≤ b)
-- [≤]-is-[≯] {a}{b} = [≥]-is-[≮] {b}{a}

-- [>]-is-[≰] : ∀{a b : ℕ} → ¬(a ≤ b) ← (a > b)
-- [>]-is-[≰] {a}{b} (Sb≤a) (a≤b) = [≤]-is-[≯] {a}{b} (a≤b) (Sb≤a)

-- [<]-is-[≱] : ∀{a b : ℕ} → ¬(a ≥ b) ← (a < b)
-- [<]-is-[≱] {a}{b} = [>]-is-[≰] {b}{a}

instance
  [≤]-totality : ConverseTotal(_≤_)
  [≤]-totality = intro p where
    p : Names.ConverseTotal(_≤_)
    p {𝟎}   {𝟎}    = [∨]-introₗ ([≡]-to-[≤] [≡]-intro)
    p {𝐒(a)}{𝟎}    = [∨]-introᵣ ([≤]-minimum)
    p {𝟎}   {𝐒(b)} = [∨]-introₗ ([≤]-minimum)
    p {𝐒(a)}{𝐒(b)} = [∨]-elim ([∨]-introₗ ∘ ([≤]-with-[𝐒] {a}{b})) ([∨]-introᵣ ∘ ([≤]-with-[𝐒] {b}{a})) (p {a}{b})


