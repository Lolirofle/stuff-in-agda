module Boolean.Theorems {ℓ₁} where -- TODO: Move

import      Lvl
open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Functional
open import Logic.Propositional{ℓ₁}
open import Relator.Equals{ℓ₁}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ₁}{Lvl.𝟎}

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

[∧]-elim-[𝑇] : ∀{a b} → ((a && b) ≡ 𝑇) → (a ≡ 𝑇)
[∧]-elim-[𝑇] {𝑇}{𝑇} [≡]-intro = [≡]-intro
[∧]-elim-[𝑇] {𝑇}{𝐹} ()
[∧]-elim-[𝑇] {𝐹}{𝑇} ()
[∧]-elim-[𝑇] {𝐹}{𝐹} ()

[∨]-elim-[𝑇] : ∀{a b c} → ((a ≡ 𝑇) → (c ≡ 𝑇)) → ((b ≡ 𝑇) → (c ≡ 𝑇)) → ((a || b) ≡ 𝑇) → (c ≡ 𝑇)
[∨]-elim-[𝑇] {𝑇}{𝑇}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝑇}{𝐹}{_} f _ [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝐹}{𝑇}{_} _ f [≡]-intro = f [≡]-intro
[∨]-elim-[𝑇] {𝐹}{𝐹}{_} _ f ()

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



if-and : ∀{B₁ B₂}{T}{x y : T} → (if (B₁ && B₂) then x else y ≡ if B₁ then (if B₂ then x else y) else y)
if-and {𝐹}{𝐹} = [≡]-intro
if-and {𝐹}{𝑇} = [≡]-intro
if-and {𝑇}{𝐹} = [≡]-intro
if-and {𝑇}{𝑇} = [≡]-intro

if-or : ∀{B₁ B₂}{T}{x y : T} → (if (B₁ || B₂) then x else y ≡ if B₁ then x else if B₂ then x else y)
if-or {𝐹}{𝐹} = [≡]-intro
if-or {𝐹}{𝑇} = [≡]-intro
if-or {𝑇}{𝐹} = [≡]-intro
if-or {𝑇}{𝑇} = [≡]-intro

if-not : ∀{B}{T}{x y : T} → (if (! B) then x else y ≡ if B then y else x)
if-not {𝐹} = [≡]-intro
if-not {𝑇} = [≡]-intro

if-elim-true : ∀{B}{T}{x y : T} → ⦃ _ : B ≡ 𝑇 ⦄ → (if B then x else y ≡ x)
if-elim-true {𝐹} ⦃ ⦄
if-elim-true {𝑇} = [≡]-intro

if-elim-false : ∀{B}{T}{x y : T} → ⦃ _ : B ≡ 𝐹 ⦄ → (if B then x else y ≡ y)
if-elim-false {𝐹} = [≡]-intro
if-elim-false {𝑇} ⦃ ⦄
