module Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility where

open import Data
open import Functional
open import Functional.Instance
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv

{-
⌊/⌋[⋅]-compatibility : ∀{x y z} ⦃ pos-y : Positive(y) ⦄ ⦃ pos-z : Positive(z) ⦄ → (y ⋅ z ∣ x) → ((x ⌊/⌋ y) ⌊/⌋ z ≡ (x ⌊/⌋ (y ⋅ z)) ⦃ [⋅]-positiveᵣ pos-y pos-z ⦄)
⌊/⌋[⋅]-compatibility {x}{y}{z} ⦃ pos-y ⦄ ⦃ pos-z ⦄ div = [⋅]-cancellationᵣ {x = y ⋅ z} $
  ((x ⌊/⌋ y) ⌊/⌋ z) ⋅ (y ⋅ z) 🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)((x ⌊/⌋ y) ⌊/⌋ z) (commutativity(_⋅_) {y}{z}) ]
  ((x ⌊/⌋ y) ⌊/⌋ z) ⋅ (z ⋅ y) 🝖[ _≡_ ]-[ associativity(_⋅_) {(x ⌊/⌋ y) ⌊/⌋ z}{z}{y} ]-sym
  (((x ⌊/⌋ y) ⌊/⌋ z) ⋅ z) ⋅ y 🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(y) ([⋅][⌊/⌋]-inverseOperatorᵣ {x ⌊/⌋ y}{z} ([↔]-to-[←] (divides-div {x}{y}{z} div-yx) div)) ]
  (x ⌊/⌋ y) ⋅ y               🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorᵣ {x}{y} div-yx ]
  x                           🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorᵣ {x}{y ⋅ z} div ]-sym
  (x ⌊/⌋ (y ⋅ z)) ⋅ (y ⋅ z)   🝖-end
  where
    instance
      pos-yz : Positive(y ⋅ z)
      pos-yz = [⋅]-positiveᵣ pos-y pos-z

    div-yx : (y ∣ x)
    div-yx = [∧]-elimₗ (divides-of-[⋅]ₗ ([∧]-to-[↔] ([∧]-intro pos-y pos-z)) div)
-}

-- TODO: Use ((a mod c) + (b mod c) < c) as the hypothesis for a generalized form of this. Not sure how useful it would be though
[⌊/⌋][+]-distributivityᵣ : ∀{a b c} ⦃ pos-c : Positive(c) ⦄ → ((c ∣ a) ∨ (c ∣ b)) → ((a + b) ⌊/⌋ c ≡ (a ⌊/⌋ c) + (b ⌊/⌋ c))
[⌊/⌋][+]-distributivityᵣ {a}{b}{c@(𝐒 C)} ([∨]-introₗ ca) = [⋅]-cancellationᵣ{c} $
  ((a + b) ⌊/⌋ c) ⋅ c               🝖[ _≡_ ]-[ [⌊/⌋][⋅]-semiInverseOperatorᵣ {a + b}{C} ]
  (a + b) −₀ ((a + b) mod c)        🝖[ _≡_ ]-[ congruence₂-₂(_−₀_)(a + b) (mod-of-modulus-sum-divisibleₗ {a}{b} ca) ]
  (a + b) −₀ (b mod c)              🝖[ _≡_ ]-[ [+][−₀]-almost-associativity {a}{b}{b mod c} (mod-maxₗ {b}{c}) ]
  a + (b −₀ (b mod c))              🝖[ _≡_ ]-[ congruence₂(_+_) ([⋅][⌊/⌋]-inverseOperatorᵣ ca) ([⌊/⌋][⋅]-semiInverseOperatorᵣ {b}{C}) ]-sym
  ((a ⌊/⌋ c) ⋅ c) + ((b ⌊/⌋ c) ⋅ c) 🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {a ⌊/⌋ c}{b ⌊/⌋ c}{c} ]-sym
  ((a ⌊/⌋ c) + (b ⌊/⌋ c)) ⋅ c       🝖-end

[⌊/⌋][+]-distributivityᵣ {a}{b}{c@(𝐒 C)} ([∨]-introᵣ cb) =
  (a + b) ⌊/⌋ c     🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ c) (commutativity(_+_) {a}{b}) ]
  (b + a) ⌊/⌋ c     🝖[ _≡_ ]-[ [⌊/⌋][+]-distributivityᵣ {b}{a}{c} ([∨]-introₗ cb) ]
  b ⌊/⌋ c + a ⌊/⌋ c 🝖[ _≡_ ]-[ commutativity(_+_) {b ⌊/⌋ c}{a ⌊/⌋ c} ]
  a ⌊/⌋ c + b ⌊/⌋ c 🝖-end

[⌊/⌋][⋅]ₗ-compatibility : ∀{a b c} ⦃ pos : Positive(c) ⦄ → (c ∣ a) → (((a ⋅ b) ⌊/⌋ c) ≡ (a ⌊/⌋ c) ⋅ b)
[⌊/⌋][⋅]ₗ-compatibility {a} {𝟎} {𝐒 c} ca = [≡]-intro
[⌊/⌋][⋅]ₗ-compatibility {a} {𝐒 b} {c} ca =
  (a ⋅ 𝐒(b)) ⌊/⌋ c            🝖[ _≡_ ]-[]
  (a + (a ⋅ b)) ⌊/⌋ c         🝖[ _≡_ ]-[ [⌊/⌋][+]-distributivityᵣ {a}{a ⋅ b}{c} ([∨]-introₗ ca) ]
  (a ⌊/⌋ c) + ((a ⋅ b) ⌊/⌋ c) 🝖[ _≡_ ]-[ congruence₂-₂(_+_)(a ⌊/⌋ c) ([⌊/⌋][⋅]ₗ-compatibility {a}{b}{c} ca) ]
  (a ⌊/⌋ c) + ((a ⌊/⌋ c) ⋅ b) 🝖[ _≡_ ]-[]
  (a ⌊/⌋ c) ⋅ 𝐒(b)            🝖-end

[⌊/⌋][⋅]ᵣ-compatibility : ∀{a b c} ⦃ pos : Positive(c) ⦄ → (c ∣ b) → (((a ⋅ b) ⌊/⌋ c) ≡ a ⋅ (b ⌊/⌋ c))
[⌊/⌋][⋅]ᵣ-compatibility {a}{b}{c} cb =
  (a ⋅ b) ⌊/⌋ c 🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ c) (commutativity(_⋅_) {a}{b}) ]
  (b ⋅ a) ⌊/⌋ c 🝖[ _≡_ ]-[ [⌊/⌋][⋅]ₗ-compatibility {b}{a}{c} cb ]
  (b ⌊/⌋ c) ⋅ a 🝖[ _≡_ ]-[ commutativity(_⋅_) {b ⌊/⌋ c}{a} ]
  a ⋅ (b ⌊/⌋ c) 🝖-end

[⌊/⌋₀][⋅]ₗ-compatibility : ∀{a b c} → (c ∣ a) → (((a ⋅ b) ⌊/⌋₀ c) ≡ (a ⌊/⌋₀ c) ⋅ b)
[⌊/⌋₀][⋅]ₗ-compatibility {a}{b}{𝟎}   = const [≡]-intro
[⌊/⌋₀][⋅]ₗ-compatibility {a}{b}{𝐒 c} = [⌊/⌋][⋅]ₗ-compatibility {a}{b}{𝐒 c}

[⌊/⌋₀][⋅]ᵣ-compatibility : ∀{a b c} → (c ∣ b) → (((a ⋅ b) ⌊/⌋₀ c) ≡ a ⋅ (b ⌊/⌋₀ c))
[⌊/⌋₀][⋅]ᵣ-compatibility {a}{b}{𝟎}   = const [≡]-intro
[⌊/⌋₀][⋅]ᵣ-compatibility {a}{b}{𝐒 c} = [⌊/⌋][⋅]ᵣ-compatibility {a}{b}{𝐒 c}

divides-[⌊/⌋] : ∀{a b c} ⦃ pos : Positive(c) ⦄ → (c ∣ a) → (a ∣ b) → ((a ⌊/⌋ c) ∣ (b ⌊/⌋ c))
divides-[⌊/⌋] {a}{b}{c} ca ab =
  let [∃]-intro n ⦃ eq ⦄ = [↔]-to-[←] divides-[⋅]-existence ab
  in [↔]-to-[→] divides-[⋅]-existence ([∃]-intro n ⦃ symmetry(_≡_) ([⌊/⌋][⋅]ₗ-compatibility {a}{n}{c} ca) 🝖 congruence₁(_⌊/⌋ c) eq ⦄)

open import Functional
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs

⌊/⌋[⋅]-compatibility : ∀{x y z} ⦃ pos-y : Positive(y) ⦄ ⦃ pos-z : Positive(z) ⦄ → ((x ⌊/⌋₀ y) ⌊/⌋₀ z ≡ x ⌊/⌋₀ (y ⋅ z))
⌊/⌋[⋅]-compatibility {x}{y@(𝐒 Y)}{z@(𝐒 Z)} = [⌊/⌋]-elim{P = \{x} div → ((x ⌊/⌋₀ y) ⌊/⌋₀ z ≡ div)} {y ⋅ z}
  (\{x} lt → [⌊/⌋]-zero {x ⌊/⌋ y}{z} $
    x ⌊/⌋ y       🝖[ _<_ ]-[ [<][⌊/⌋]ₗ-preserving (divides-with-[⋅] {y}{y}{z} ([∨]-introₗ (reflexivity(_∣_)))) lt ]-super
    (y ⋅ z) ⌊/⌋ y 🝖[ _≡_ ]-[ [⌊/⌋][swap⋅]-inverseOperatorᵣ {y}{z} ]
    z             🝖-end
  )
  (\{x} prev →
    ((x + (y ⋅ z)) ⌊/⌋ y) ⌊/⌋ z         🝖[ _≡_ ]-[ congruence₁(_⌊/⌋₀ z) ([⌊/⌋][+]-distributivityᵣ {x} ([∨]-introᵣ (divides-with-[⋅] {y}{y}{z} ([∨]-introₗ (reflexivity(_∣_) {y}))))) ]
    ((x ⌊/⌋ y) + ((y ⋅ z) ⌊/⌋ y)) ⌊/⌋ z 🝖[ _≡_ ]-[ congruence₁(_⌊/⌋₀ z) (congruence₂-₂(_+_)(x ⌊/⌋ y) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {y}{z})) ]
    ((x ⌊/⌋ y) + z) ⌊/⌋ z               🝖[ _≡_ ]-[ [⌊/⌋][+]-distributivityᵣ {x ⌊/⌋ y}{z} ([∨]-introᵣ (reflexivity(_∣_) {z})) ]
    ((x ⌊/⌋ y) ⌊/⌋ z) + (z ⌊/⌋ z)       🝖[ _≡_ ]-[ congruence₂-₂(_+_)((x ⌊/⌋ y) ⌊/⌋ z) ([⌊/⌋]-of-same {z}) ]
    ((x ⌊/⌋ y) ⌊/⌋ z) + 1               🝖[ _≡_ ]-[]
    𝐒((x ⌊/⌋ y) ⌊/⌋ z)                  🝖[ _≡_ ]-[ congruence₁(𝐒) prev ]
    𝐒(x ⌊/⌋ (y ⋅ z))                    🝖-end
  )
  {x}

⌊/⌋₀[⋅]-compatibility : ∀{x y z} → ((x ⌊/⌋₀ y) ⌊/⌋₀ z ≡ x ⌊/⌋₀ (y ⋅ z))
⌊/⌋₀[⋅]-compatibility {x}{𝟎}  {𝟎}   = [≡]-intro
⌊/⌋₀[⋅]-compatibility {x}{𝟎}  {𝐒 z} = [≡]-intro
⌊/⌋₀[⋅]-compatibility {x}{𝐒 y}{𝟎}   = [≡]-intro
⌊/⌋₀[⋅]-compatibility {x}{𝐒 y}{𝐒 z} = ⌊/⌋[⋅]-compatibility {x}{𝐒 y}{𝐒 z}

⌊/⌋₀-swapᵣ : ∀{x y z} → ((x ⌊/⌋₀ y) ⌊/⌋₀ z ≡ (x ⌊/⌋₀ z) ⌊/⌋₀ y)
⌊/⌋₀-swapᵣ {x}{y}{z} =
  (x ⌊/⌋₀ y) ⌊/⌋₀ z 🝖[ _≡_ ]-[ ⌊/⌋₀[⋅]-compatibility {x}{y}{z} ]
  x ⌊/⌋₀ (y ⋅ z)    🝖[ _≡_ ]-[ congruence₂-₂(_⌊/⌋₀_)(x) (commutativity(_⋅_) {y}{z}) ]
  x ⌊/⌋₀ (z ⋅ y)    🝖[ _≡_ ]-[ ⌊/⌋₀[⋅]-compatibility {x}{z}{y} ]-sym
  (x ⌊/⌋₀ z) ⌊/⌋₀ y 🝖-end

⌊/⌋-swapᵣ : ∀{x y z} ⦃ pos-y : Positive(y) ⦄ ⦃ pos-z : Positive(z) ⦄ → ((x ⌊/⌋ y) ⌊/⌋ z ≡ (x ⌊/⌋ z) ⌊/⌋ y)
⌊/⌋-swapᵣ {x}{y@(𝐒 _)}{z@(𝐒 _)} = ⌊/⌋₀-swapᵣ {x}{y}{z}

[⌊/⌋]-equalityᵣ : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : Positive(x₂) ⦄ ⦃ pos-y₂ : Positive(y₂) ⦄ → (x₁ ⋅ y₂ ≡ y₁ ⋅ x₂) → (x₁ ⌊/⌋ x₂ ≡ y₁ ⌊/⌋ y₂)
[⌊/⌋]-equalityᵣ {x₁} {x₂} {y₁} {y₂} eq =
  x₁ ⌊/⌋ x₂                 🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ x₂) ([⌊/⌋][⋅]-inverseOperatorᵣ {x₁}{y₂}) ]-sym
  ((x₁ ⋅ y₂) ⌊/⌋ y₂) ⌊/⌋ x₂ 🝖[ _≡_ ]-[ ⌊/⌋-swapᵣ {x₁ ⋅ y₂}{y₂}{x₂} ]
  ((x₁ ⋅ y₂) ⌊/⌋ x₂) ⌊/⌋ y₂ 🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ y₂) (congruence₁(_⌊/⌋ x₂) eq) ]
  ((y₁ ⋅ x₂) ⌊/⌋ x₂) ⌊/⌋ y₂ 🝖[ _≡_ ]-[ congruence₁(_⌊/⌋ y₂) ([⌊/⌋][⋅]-inverseOperatorᵣ {y₁}{x₂}) ]
  y₁ ⌊/⌋ y₂                 🝖-end

[⌊/⌋]-equalityₗ : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : Positive(x₂) ⦄ ⦃ pos-y₂ : Positive(y₂) ⦄ → (x₂ ∣ x₁) → (y₂ ∣ y₁) → (x₁ ⌊/⌋ x₂ ≡ y₁ ⌊/⌋ y₂) → (x₁ ⋅ y₂ ≡ y₁ ⋅ x₂)
[⌊/⌋]-equalityₗ {x₁} {x₂} {y₁} {y₂} div-x div-y eq =
  x₁ ⋅ y₂                 🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(y₂) ([⋅][⌊/⌋]-inverseOperatorᵣ div-x) ]-sym
  ((x₁ ⌊/⌋ x₂) ⋅ x₂) ⋅ y₂ 🝖[ _≡_ ]-[ associativity(_⋅_) {x₁ ⌊/⌋ x₂}{x₂}{y₂} ]
  (x₁ ⌊/⌋ x₂) ⋅ (x₂ ⋅ y₂) 🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(x₂ ⋅ y₂) eq ]
  (y₁ ⌊/⌋ y₂) ⋅ (x₂ ⋅ y₂) 🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)(y₁ ⌊/⌋ y₂) (commutativity(_⋅_) {x₂}{y₂}) ]
  (y₁ ⌊/⌋ y₂) ⋅ (y₂ ⋅ x₂) 🝖[ _≡_ ]-[ associativity(_⋅_) {y₁ ⌊/⌋ y₂}{y₂}{x₂} ]-sym
  ((y₁ ⌊/⌋ y₂) ⋅ y₂) ⋅ x₂ 🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(x₂) ([⋅][⌊/⌋]-inverseOperatorᵣ div-y) ]
  y₁ ⋅ x₂                 🝖-end

[⌊/⌋₀]-equalityᵣ : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : Positive(x₂) ⦄ ⦃ pos-y₂ : Positive(y₂) ⦄ → (x₁ ⋅ y₂ ≡ y₁ ⋅ x₂) → (x₁ ⌊/⌋₀ x₂ ≡ y₁ ⌊/⌋₀ y₂)
[⌊/⌋₀]-equalityᵣ {x₁} {x₂@(𝐒 _)} {y₁} {y₂@(𝐒 _)} eq = [⌊/⌋]-equalityᵣ {x₁}{x₂}{y₁}{y₂} eq

[⌊/⌋₀]-equalityₗ : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : Positive(x₂) ⦄ ⦃ pos-y₂ : Positive(y₂) ⦄ → (x₂ ∣ x₁) → (y₂ ∣ y₁) → (x₁ ⌊/⌋₀ x₂ ≡ y₁ ⌊/⌋₀ y₂) → (x₁ ⋅ y₂ ≡ y₁ ⋅ x₂)
[⌊/⌋₀]-equalityₗ {x₁} {x₂@(𝐒 _)} {y₁} {y₂@(𝐒 _)} div-x div-y eq = [⌊/⌋]-equalityₗ {x₁}{x₂}{y₁}{y₂} div-x div-y eq
