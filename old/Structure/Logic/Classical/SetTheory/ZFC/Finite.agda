
Finite : Domain → Formula
Finite(s) = ∃ₛ(ℕ)(n ↦ s ≼ 𝕟(n)) -- TODO: Now this means that there is an injection (s → 𝕟(n)), which is equivalent to the existance of an surjection (𝕟(n) → s) because stuff that follows from excluded middle (more specifically ((s ≼ 𝕟(n)) ↔ (𝕟(n) ≽ s))). Define ∑ (summation over finite sets) by using the existance of a finite sequence

-- reduce : (_▫_ : Domain → Domain → Domain) → ⦃ _ : Commutativity(_▫_) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → ⦃ _ : Identity(_▫_) ⦄ → (s : Domain) → ⦃ _ : Finite(s) ⦄ → Domain
-- reduce₀ : (_▫_ : Domain → Domain → Domain) → ⦃ _ : Commutativity(_▫_) ⦄ → ⦃ _ : Associativity(_▫_) ⦄ → (s : Domain) → ⦃ _ : Finite(s) ⦄ → Domain → Domain
