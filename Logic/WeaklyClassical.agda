module Logic.WeaklyClassical where

import      Lvl
open import Functional
open import Logic.Names
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Type

private variable ℓ : Lvl.Level
private variable T X Y : Type{ℓ}
private variable P : T → Type{ℓ}

-- TODO: What should (¬¬ P → P) for a P be called? DoubleNegation? Stable proposition?

[⊤]-doubleNegation : DoubleNegationOn(⊤)
[⊤]-doubleNegation = const [⊤]-intro

[⊥]-doubleNegation : DoubleNegationOn(⊥)
[⊥]-doubleNegation = apply id

[¬]-doubleNegation : DoubleNegationOn(¬ X)
[¬]-doubleNegation = _∘ apply

[∧]-doubleNegation : DoubleNegationOn(X) → DoubleNegationOn(Y) → DoubleNegationOn(X ∧ Y)
[∧]-doubleNegation nnxx nnyy nnxy = [∧]-intro (nnxx(nx ↦ nnxy(nx ∘ [∧]-elimₗ))) (nnyy(ny ↦ nnxy(ny ∘ [∧]-elimᵣ)))

[→]-doubleNegation : DoubleNegationOn(Y) → DoubleNegationOn(X → Y)
[→]-doubleNegation nnyy nnxy x = nnyy(ny ↦ nnxy(xy ↦ (ny ∘ xy) x))

[∀]-doubleNegation-distribute : (∀{x} → DoubleNegationOn(P(x))) → DoubleNegationOn(∀{x} → P(x))
[∀]-doubleNegation-distribute annp nnap = annp(npx ↦ nnap(npx $_))

doubleNegation-to-callCC : DoubleNegationOn(X) → DoubleNegationOn(Y) → (((X → Y) → X) → X)
doubleNegation-to-callCC dx dy xyx = dx(nx ↦ nx(xyx(dy ∘ const ∘ nx)))
