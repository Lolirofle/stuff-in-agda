module Lang.Instance where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T X Y Z : Type{ℓ}

-- Infers/resolves/(searches for) an instance/proof of the specified type/statement
resolve : (T : Type{ℓ}) →  ⦃ _ : T ⦄ → T
resolve (_) ⦃ x ⦄ = x

-- Infers/resolves/(searches for) an instance/proof of an inferred type/statement
infer : ⦃ _ : T ⦄ → T
infer ⦃ x ⦄ = x

inst-fn : (X → Y) → (⦃ inst : X ⦄ → Y)
inst-fn P ⦃ x ⦄ = P(x)

inst-fn₂ : (X → Y → Z) → (⦃ inst₁ : X ⦄ → ⦃ inst₂ : Y ⦄ → Z)
inst-fn₂ P ⦃ x ⦄ ⦃ y ⦄ = P(x)(y)

inst-fnᵢ : ({_ : X} → Y → Z) → ({_ : X} → ⦃ _ : Y ⦄ → Z)
inst-fnᵢ P {x} ⦃ y ⦄ = P{x}(y)

impl-to-expl : ({ _ : X} → Y) → (X → Y)
impl-to-expl f(x) = f{x}

expl-to-impl : (X → Y) → ({ _ : X} → Y)
expl-to-impl f{x} = f(x)
