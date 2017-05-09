module Boolean.Theorems {l₁} {l₂} where -- TODO: Move

import      Level as Lvl
open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Relator.Equals{l₁}{l₂}

-- A boolean operation is either true or false
bivalence : ∀{a} → ((a ≡ 𝑇) ∨ (a ≡ 𝐹))
bivalence {𝑇} = [∨]-introₗ [≡]-intro
bivalence {𝐹} = [∨]-introᵣ [≡]-intro

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