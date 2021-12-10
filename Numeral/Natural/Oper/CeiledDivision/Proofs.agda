module Numeral.Natural.Oper.CeiledDivision.Proofs where

import Lvl
open import Data
import      Data.Tuple as Tuple
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.CeiledDivision
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable P : T → Type{ℓ}
private variable a b m : ℕ

[⌊/⌋]-zero : ∀{a b} ⦃ pos-b : Positive(b)⦄ → (a ≡ 𝟎) ↔ (a ⌈/⌉ b ≡ 𝟎)
Tuple.left  ([⌊/⌋]-zero {𝟎}   {𝐒 b}) [≡]-intro = [≡]-intro
Tuple.right ([⌊/⌋]-zero {.𝟎}  {𝐒 b}) [≡]-intro = [≡]-intro

[⌊/⌋]-one : ∀{a} ⦃ pos-a : Positive(a)⦄ {b} ⦃ pos-b : Positive(b)⦄ → (a ≤ b) ↔ (a ⌈/⌉ b ≡ 𝟏)
[⌊/⌋]-one {a@(𝐒 _)} {b@(𝐒 _)} =
  a ≤ b                 ⇔-[ [−₀]-when-0 ]
  a −₀ b ≡ 𝟎            ⇔-[ [⌊/⌋]-zero ]
  (a −₀ b) ⌈/⌉ b ≡ 𝟎    ⇔-[ [↔]-intro (injective(𝐒)) (congruence₁(𝐒)) ]
  𝐒((a −₀ b) ⌈/⌉ b) ≡ 𝟏 ⇔-[]
  a ⌈/⌉ b ≡ 𝟏           ⇔-end

[⌊/⌋]-step : ∀{a b} ⦃ pos-b : Positive(b)⦄ → ((a + b) ⌈/⌉ b ≡ 𝐒(a ⌈/⌉ b))
[⌊/⌋]-step {a} {b@(𝐒 _)} = congruence₁(𝐒) $
  ((a + b) −₀ b) ⌈/⌉ b 🝖[ _≡_ ]-[ congruence₁(_⌈/⌉ b) ([−₀]ₗ[+]ᵣ-nullify {a}{b}) ]
  a ⌈/⌉ b              🝖-end

[⌊/⌋]-positive : ∀{a b} ⦃ pos-b : Positive(b) ⦄ → Positive(a) ↔ Positive(a ⌈/⌉ b)
Tuple.left  ([⌊/⌋]-positive {𝟎}       {b@(𝐒 _)}) ()
Tuple.left  ([⌊/⌋]-positive {a@(𝐒 _)} {b@(𝐒 _)}) <> = <>
Tuple.right ([⌊/⌋]-positive {a@(𝐒 _)} {b@(𝐒 _)}) <> = <>

[⌈/⌉]-elim : (P : {ℕ} → ℕ → Type{ℓ}) → ∀{b} ⦃ pos-b : Positive(b) ⦄ → P{𝟎}(𝟎) → (∀{a} ⦃ pos-a : Positive(a) ⦄ → (a < b) → P{a}(𝟏)) → (∀{a} → P{a}(a ⌈/⌉ b) → P{a + b}(𝐒(a ⌈/⌉ b))) → ∀{a} → P{a}(a ⌈/⌉ b)
[⌈/⌉]-elim P{b = b@(𝐒 B)} p0 p1 p+ {a = a} = ℕ-strong-recursion(a ↦ P{a}(a ⌈/⌉ b)) p a where
  p : (n : ℕ) → ((i : ℕ) → i < n → P{i}(i ⌈/⌉ b)) → P{n}(n ⌈/⌉ b)
  p 𝟎         _    = p0
  p (a@(𝐒 A)) prev = [∨]-elim
    (ab ↦ substitute₁ᵣ(x ↦ P{x} (𝐒((a −₀ b) ⌈/⌉ b))) ([↔]-to-[→] [−₀][+]-nullify2ᵣ ab) (p+{a −₀ b} (prev(a −₀ b) (succ ([−₀]-lesser {A}{B})))))
    (ba ↦ substitute₁ₗ(P) ([↔]-to-[→] [⌊/⌋]-one (sub₂(_<_)(_≤_) ba)) (p1 ba))
    ([≤]-or-[>] {b}{a})

[⌈/⌉]-elim-alt : (P : {ℕ} → ℕ → Type{ℓ}) → ∀{b} ⦃ pos-b : Positive(b) ⦄ → P{𝟎}(𝟎) → (∀{a} ⦃ pos-a : Positive(a) ⦄ → (a ≤ b) → P{a}(𝟏)) → (∀{a} ⦃ pos-a : Positive(a) ⦄ → P{a}(a ⌈/⌉ b) → P{a + b}(𝐒(a ⌈/⌉ b))) → ∀{a} → P{a}(a ⌈/⌉ b)
[⌈/⌉]-elim-alt P{b = b@(𝐒 B)} p0 p1 p+ {a = a} = ℕ-strong-recursion(a ↦ P{a}(a ⌈/⌉ b)) p a where
  p : (n : ℕ) → ((i : ℕ) → i < n → P{i}(i ⌈/⌉ b)) → P{n}(n ⌈/⌉ b)
  p 𝟎         _    = p0
  p (a@(𝐒 A)) prev = [∨]-elim
    ([∨]-elim
      (ba ↦ substitute₁ₗ(P) ([↔]-to-[→] [⌊/⌋]-one (sub₂(_<_)(_≤_) ba)) (p1(sub₂(_<_)(_≤_) ba)))
      (eq ↦ substitute₁ₗ(P) (congruence₁(𝐒) ([↔]-to-[→] [⌊/⌋]-zero ([↔]-to-[→] [−₀]-when-0 (sub₂(_≡_)(_≤_) eq)))) (p1(sub₂(_≡_)(_≤_) eq))))
    (ab ↦ substitute₁ᵣ(x ↦ P{x} (𝐒((a −₀ b) ⌈/⌉ b))) ([↔]-to-[→] [−₀][+]-nullify2ᵣ (sub₂(_<_)(_≤_) ab)) (p+{a −₀ b} ⦃ [↔]-to-[→] [−₀]-positive ab ⦄ (prev(a −₀ b) (succ ([−₀]-lesser {A}{B})))))
    (trichotomy(_<_)(_≡_) {a}{b})

-- TODO: Move somewhere else and prove the following: (b ∣ a) ↔ (a ⌊/⌋ b ≡ a ⌈/⌉ b) and (b ∤ a) ↔ (𝐒(a ⌊/⌋ b) ≡ a ⌈/⌉ b)

open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Proofs
open import Structure.Operator

{-
⌈/⌉-and-⌊/⌋ : ∀{x y} → (x ⌈/⌉ y ≡ (x + 𝐏(y)) ⌊/⌋ y)
⌈/⌉-and-⌊/⌋ = ?
-}

{-
[⌈/⌉][mod]-is-division-with-remainder : ∀{x y} ⦃ pos : Positive(y) ⦄ → (((x ⌈/⌉ y) ⋅ y) −₀ (y −₀ (x mod y)) ≡ x) -- TODO: Also false when x = y. The problem is the modulo operation. If (y mod y = y), then this would work, or just change it to (((x ⌈/⌉ y) ⋅ y) −₀ ((y −₀ (x mod y)) mod y) ≡ x), but would such a complicated formula really be useful?
[⌈/⌉][mod]-is-division-with-remainder {x} {y@(𝐒 Y)} = [⌈/⌉]-elim(\{x} div → ((div ⋅ y) −₀ (y −₀ (x mod y)) ≡ x)) {y} [≡]-intro base1 step {x} where
  base1 : ∀{x} ⦃ pos-x : Positive x ⦄ → (x < y) → (y −₀ (y −₀ (x mod y)) ≡ x)
  base1 {x} (succ lt) =
    y −₀ (y −₀ (x mod y)) 🝖[ _≡_ ]-[ [↔]-to-[→] [−₀]-nested-sameₗ (sub₂(_<_)(_≤_) (mod-maxᵣ {x}{y})) ]
    x mod y               🝖[ _≡_ ]-[ mod-lesser-than-modulus ⦃ lt ⦄ ]
    x                     🝖-end

  step : ∀{x} → (((x ⌈/⌉ y) ⋅ y) −₀ (y −₀ (x mod y)) ≡ x) → ((𝐒(x ⌈/⌉ y) ⋅ y) −₀ (y −₀ ((x + y) mod y)) ≡ x + y)
  step {𝟎}       prev =
    (𝐒(𝟎 ⌈/⌉ y) ⋅ y) −₀ (y −₀ ((𝟎 + y) mod y)) 🝖[ _≡_ ]-[]
    y −₀ (y −₀ (y mod y))                      🝖[ _≡_ ]-[ {!!} ]
    y −₀ (y −₀ 𝟎)                              🝖[ _≡_ ]-[ {!!} ]
    y −₀ y                                     🝖[ _≡_ ]-[ {!!} ]
    y                                          🝖[ _≡_ ]-[]
    𝟎 + 𝐒 Y                                    🝖-end
  step {x@(𝐒 _)} prev =
    (𝐒(x ⌈/⌉ y) ⋅ y) −₀ (y −₀ ((x + y) mod y)) 🝖[ _≡_ ]-[ congruence₂(_−₀_) ([⋅]-with-[𝐒]ₗ {x ⌈/⌉ y}{y}) (congruence₂-₂(_−₀_)(y) (mod-of-modulus-addᵣ {x}{Y})) ]
    (((x ⌈/⌉ y) ⋅ y) + y) −₀ (y −₀ (x mod y))  🝖[ _≡_ ]-[ [+][−₀]-almost-associativityₗ {(x ⌈/⌉ y) ⋅ y}{y}{y −₀ (x mod y)} {!!} ]
    (((x ⌈/⌉ y) ⋅ y) −₀ (y −₀ (x mod y))) + y  🝖[ _≡_ ]-[ {!!} ]
    x + y                                      🝖-end
-}

{-
[⌈/⌉][mod]-is-division-with-remainder : ∀{x y} ⦃ pos : Positive(y) ⦄ → ((𝐏(x ⌈/⌉ y) ⋅ y) + (x mod y) ≡ x) -- TODO: False when x = y
[⌈/⌉][mod]-is-division-with-remainder {x} {y@(𝐒 Y)} = [⌈/⌉]-elim(\{x} div → ((𝐏(div) ⋅ y) + (x mod y) ≡ x)) {y} [≡]-intro base1 step {x} where
  base1 : ∀{x} ⦃ pos-x : Positive x ⦄ → (x < y) → (x mod y ≡ x)
  base1(succ lt) = mod-lesser-than-modulus ⦃ lt ⦄

  step : ∀{x} → ((𝐏(x ⌈/⌉ y) ⋅ y) + (x mod y) ≡ x) → (((x ⌈/⌉ y) ⋅ y) + ((x + y) mod y) ≡ x + y)
  step {𝟎}       prev = {!!}
  step {x@(𝐒 _)} prev =
    ((x ⌈/⌉ y) ⋅ y) + ((x + y) mod y)        🝖[ _≡_ ]-[ congruence₂(_+_) (symmetry(_≡_) ([↔]-to-[→] ([−₀][+]-nullify2ᵣ {y}) ([⋅]ᵣ-growing {_}{x ⌈/⌉ y} ([↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] ([⌊/⌋]-positive {x}{y}) <>))))) (mod-of-modulus-addᵣ {x}{Y}) ]
    ((((x ⌈/⌉ y) ⋅ y) −₀ y) + y) + (x mod y) 🝖[ _≡_ ]-[ {!!} ]
    ((((x ⌈/⌉ y) ⋅ y) −₀ y) + (x mod y)) + y 🝖[ _≡_ ]-[ {!!} ]
    ((𝐏(x ⌈/⌉ y) ⋅ y) + (x mod y)) + y       🝖[ _≡_ ]-[ congruence₂-₁(_+_)(y) prev ]
    x + y                                    🝖-end
-}

{-
13/3 = 5
13/3*3 = 15
13/3*3 - 3 + 1 = 15
-}
