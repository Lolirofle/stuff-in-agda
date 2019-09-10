module Limit where
  -- Statement that the limit of the function f at point l exists (and its value is L)
  -- This is expressed by converting the standard (ε,δ)-limit definition to Skolem normal form (TODO: ...I think? Is this correct? I am just having a hunch)
  record Lim (f : ℝ → ℝ) (p : ℝ) : Stmt where
    field
      L : ℝ -- The limit point
      δ : ℝ₊ → ℝ₊ -- The delta function that is able to depend on epsilon
      satisfaction : ∀{ε : ℝ₊}{x : ℝ} → (0 < abs(x − p) < #(δ(ε))) → (abs(f(x) − L) < #(ε))

  -- Limit value function f (if the limit exists)
  lim : (f : ℝ → ℝ) → (p : ℝ) → ⦃ _ : Lim f(p) ⦄ → ℝ
  lim _ _ ⦃ l ⦄ = Lim.L(l)

module Proofs where
  instance postulate [+]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) + g(x))(p)
  instance postulate [−]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) − g(x))(p)
  instance postulate [⋅]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) ⋅ g(x))(p)
  instance postulate [/]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) / g(x))(p)

  instance postulate [+]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) + g(x))(p) ≡ lim f(p) + lim g(p))
  instance postulate [−]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) − g(x))(p) ≡ lim f(p) − lim g(p))
  instance postulate [⋅]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) ⋅ g(x))(p) ≡ lim f(p) ⋅ lim g(p))
  instance postulate [/]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) / g(x))(p) ≡ lim f(p) / lim g(p))
