module Lang.Instance where

-- Infers/resolves/(searches for) an instance/proof of the specified type/statement
resolve : ∀{ℓ}(T : Set(ℓ)) ⦃ _ : T ⦄ → T
resolve (_) ⦃ x ⦄ = x

-- Infers/resolves/(searches for) an instance/proof of an inferred type/statement
infer : ∀{ℓ}{T : Set(ℓ)} ⦃ _ : T ⦄ → T
infer ⦃ x ⦄ = x

inst-fn : ∀{ℓ₁ ℓ₂}{X : Set(ℓ₁)}{Y : Set(ℓ₂)} → (X → Y) → (⦃ _ : X ⦄ → Y)
inst-fn P ⦃ x ⦄ = P(x)

inst-fn₂ : ∀{ℓ₁ ℓ₂ ℓ₃}{X : Set(ℓ₁)}{Y : Set(ℓ₂)}{Z : Set(ℓ₃)} → (X → Y → Z) → (⦃ _ : X ⦄ → ⦃ _ : Y ⦄ → Z)
inst-fn₂ P ⦃ x ⦄ ⦃ y ⦄ = P(x)(y)

inst-fnᵢ : ∀{ℓ₁ ℓ₂ ℓ₃}{X : Set(ℓ₁)}{Y : Set(ℓ₂)}{Z : Set(ℓ₃)} → ({_ : X} → Y → Z) → ({_ : X} → ⦃ _ : Y ⦄ → Z)
inst-fnᵢ P {x} ⦃ y ⦄ = P{x}(y)

impl-to-expl : ∀{ℓ₁ ℓ₂}{X : Set(ℓ₁)}{Y : Set(ℓ₂)} → ({ _ : X} → Y) → (X → Y)
impl-to-expl f(x) = f{x}

expl-to-impl : ∀{ℓ₁ ℓ₂}{X : Set(ℓ₁)}{Y : Set(ℓ₂)} → (X → Y) → ({ _ : X} → Y)
expl-to-impl f{x} = f(x)
