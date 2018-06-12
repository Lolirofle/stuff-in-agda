module Lang.Instance where

-- Infers/resolves/(searches for) an instance/proof of the specified type/statement
resolve : ∀{ℓ}(T : Set(ℓ)) ⦃ _ : T ⦄ → T
resolve (_) ⦃ x ⦄ = x

-- Infers/resolves/(searches for) an instance/proof of an inferred type/statement
infer : ∀{ℓ}{T : Set(ℓ)} ⦃ _ : T ⦄ → T
infer ⦃ x ⦄ = x
