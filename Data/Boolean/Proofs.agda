module Data.Boolean.Proofs where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

-- A boolean operation is either true or false
bivalence : ∀{a} → ((a ≡ 𝑇) ∨ (a ≡ 𝐹))
bivalence {𝑇} = [∨]-introₗ [≡]-intro
bivalence {𝐹} = [∨]-introᵣ [≡]-intro

-- A boolean operation is not both true and false at the same time
disjointness : ∀{a} → ¬((a ≡ 𝑇) ∧ (a ≡ 𝐹))
disjointness {𝑇} ([∧]-intro [≡]-intro ())
disjointness {𝐹} ([∧]-intro () [≡]-intro)



[∧]-intro-[𝑇] : ∀{a b} → (a ≡ 𝑇) → (b ≡ 𝑇) → ((a && b) ≡ 𝑇)
[∧]-intro-[𝑇] [≡]-intro [≡]-intro = [≡]-intro

[∨]-introₗ-[𝑇] : ∀{a b} → (a ≡ 𝑇) → ((a || b) ≡ 𝑇)
[∨]-introₗ-[𝑇] {_}{𝑇} [≡]-intro = [≡]-intro
[∨]-introₗ-[𝑇] {_}{𝐹} [≡]-intro = [≡]-intro

[∨]-introᵣ-[𝑇] : ∀{a b} → (b ≡ 𝑇) → ((a || b) ≡ 𝑇)
[∨]-introᵣ-[𝑇] {𝑇}{_} [≡]-intro = [≡]-intro
[∨]-introᵣ-[𝑇] {𝐹}{_} [≡]-intro = [≡]-intro

[∧]-elimₗ-[𝑇] : ∀{a b} → ((a && b) ≡ 𝑇) → (a ≡ 𝑇)
[∧]-elimₗ-[𝑇] {𝑇}{𝑇} [≡]-intro = [≡]-intro
[∧]-elimₗ-[𝑇] {𝑇}{𝐹} ()
[∧]-elimₗ-[𝑇] {𝐹}{𝑇} ()
[∧]-elimₗ-[𝑇] {𝐹}{𝐹} ()

[∧]-elimᵣ-[𝑇] : ∀{a b} → ((a && b) ≡ 𝑇) → (b ≡ 𝑇)
[∧]-elimᵣ-[𝑇] {𝑇}{𝑇} [≡]-intro = [≡]-intro
[∧]-elimᵣ-[𝑇] {𝑇}{𝐹} ()
[∧]-elimᵣ-[𝑇] {𝐹}{𝑇} ()
[∧]-elimᵣ-[𝑇] {𝐹}{𝐹} ()

[∨]-elim-[𝑇] : ∀{a b c} → ((a ≡ 𝑇) → (c ≡ 𝑇)) → ((b ≡ 𝑇) → (c ≡ 𝑇)) → ((a || b) ≡ 𝑇) → (c ≡ 𝑇)
[∨]-elim-[𝑇] {𝑇}{𝑇}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝑇}{𝐹}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝐹}{𝑇}{_} _ f [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝐹}{𝐹}{_} _ f ()

[∨]-elim-proof-[𝑇] : ∀{a b}{ℓ₂}{φ : Set(ℓ₂)} → ((a ≡ 𝑇) → φ) → ((b ≡ 𝑇) → φ) → ((a || b) ≡ 𝑇) → φ
[∨]-elim-proof-[𝑇] {𝑇}{𝑇}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-proof-[𝑇] {𝑇}{𝐹}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-proof-[𝑇] {𝐹}{𝑇}{_} _ f [≡]-intro = f [≡]-intro
[∨]-elim-proof-[𝑇] {𝐹}{𝐹}{_} _ f ()

[¬]-intro-[𝑇] : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
[¬]-intro-[𝑇] [≡]-intro = [≡]-intro

[¬]-elim-[𝑇] : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
[¬]-elim-[𝑇] {𝑇} ()
[¬]-elim-[𝑇] {𝐹} [≡]-intro = [≡]-intro



[∧]-introₗ-[𝐹] : ∀{a b} → (a ≡ 𝐹) → ((a && b) ≡ 𝐹)
[∧]-introₗ-[𝐹] {_}{𝑇} [≡]-intro = [≡]-intro
[∧]-introₗ-[𝐹] {_}{𝐹} [≡]-intro = [≡]-intro

[∧]-introᵣ-[𝐹] : ∀{a b} → (b ≡ 𝐹) → ((a && b) ≡ 𝐹)
[∧]-introᵣ-[𝐹] {𝑇}{_} [≡]-intro = [≡]-intro
[∧]-introᵣ-[𝐹] {𝐹}{_} [≡]-intro = [≡]-intro

[∨]-intro-[𝐹] : ∀{a b} → (a ≡ 𝐹) → (b ≡ 𝐹) → ((a || b) ≡ 𝐹)
[∨]-intro-[𝐹] [≡]-intro [≡]-intro = [≡]-intro

[¬]-intro-[𝐹] : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
[¬]-intro-[𝐹] = [¬]-elim-[𝑇]

[¬]-elim-[𝐹] : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
[¬]-elim-[𝐹] = [¬]-intro-[𝑇]



[≢][𝑇]-is-[𝐹] : ∀{a} → (a ≢ 𝑇) ↔ (a ≡ 𝐹)
[≢][𝑇]-is-[𝐹] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝑇) → (a ≡ 𝐹)
  r {𝑇} (a≢𝑇) = [⊥]-elim ((a≢𝑇) ([≡]-intro))
  r {𝐹} (a≢𝑇) = [≡]-intro

  l : ∀{a} → (a ≢ 𝑇) ← (a ≡ 𝐹)
  l {𝑇} ()
  l {𝐹} (a≡𝐹) ()

[≢][𝐹]-is-[𝑇] : ∀{a} → (a ≢ 𝐹) ↔ (a ≡ 𝑇)
[≢][𝐹]-is-[𝑇] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝐹) → (a ≡ 𝑇)
  r {𝑇} (a≢𝐹) = [≡]-intro
  r {𝐹} (a≢𝐹) = [⊥]-elim ((a≢𝐹) ([≡]-intro))

  l : ∀{a} → (a ≢ 𝐹) ← (a ≡ 𝑇)
  l {𝑇} (a≡𝑇) ()
  l {𝐹} ()

[¬]-double : ∀{a} → (! ! a ≡ a)
[¬]-double {𝑇} = [≡]-intro
[¬]-double {𝐹} = [≡]-intro


module _ {ℓ} {T : Type{ℓ}} {x y : T} where
  if-and : ∀{B₁ B₂} → (if (B₁ && B₂) then x else y ≡ if B₁ then (if B₂ then x else y) else y)
  if-and {𝐹}{𝐹} = [≡]-intro
  if-and {𝐹}{𝑇} = [≡]-intro
  if-and {𝑇}{𝐹} = [≡]-intro
  if-and {𝑇}{𝑇} = [≡]-intro

  if-or : ∀{B₁ B₂} → (if (B₁ || B₂) then x else y ≡ if B₁ then x else if B₂ then x else y)
  if-or {𝐹}{𝐹} = [≡]-intro
  if-or {𝐹}{𝑇} = [≡]-intro
  if-or {𝑇}{𝐹} = [≡]-intro
  if-or {𝑇}{𝑇} = [≡]-intro

  if-not : ∀{B} → (if (! B) then x else y ≡ if B then y else x)
  if-not {𝐹} = [≡]-intro
  if-not {𝑇} = [≡]-intro

  if-elim-true : ∀{B} → ⦃ _ : B ≡ 𝑇 ⦄ → (if B then x else y ≡ x)
  if-elim-true {𝐹} ⦃ ⦄
  if-elim-true {𝑇} = [≡]-intro

  if-elim-false : ∀{B} → ⦃ _ : B ≡ 𝐹 ⦄ → (if B then x else y ≡ y)
  if-elim-false {𝐹} = [≡]-intro
  if-elim-false {𝑇} ⦃ ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} {T : Type{ℓ₁}} {x y : T} {P : T → Type{ℓ₂}} {Q : Type{ℓ₃}} where
  if-elim : ∀{B} → P(if B then x else y) → (P(x) → Q) → (P(y) → Q) → Q
  if-elim{𝑇} p pxq pyq = pxq p
  if-elim{𝐹} p pxq pyq = pyq p
