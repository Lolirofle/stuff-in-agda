-- TODO: Move these to stuff related to metric spaces

module Derivative where
  open Limit using (Lim ; lim)

  -- Statement that the point x of function f is a differentiable point
  DifferentiablePoint : (ℝ → ℝ) → ℝ → Stmt
  DifferentiablePoint f(p) = Lim(x ↦ ((f(x) − f(p))/(x − p)))(p)

  -- Statement that function f is differentiable
  Differentiable : (ℝ → ℝ) → Stmt
  Differentiable f = ∀{x} → DifferentiablePoint f(x)

  -- Derivative value of function f at point x (if the point is differentiable)
  𝐷 : (f : ℝ → ℝ) → (x : ℝ) → ⦃ _ : DifferentiablePoint f(x) ⦄ → ℝ
  𝐷 _ _ ⦃ l ⦄ = Lim.L(l)

module Proofs where
  instance postulate Differentiable-constant     : ∀{a} → Differentiable(const(a))
  instance postulate Differentiable-id           : Differentiable(id)
  instance postulate Differentiable-monomial     : ∀{a} → Differentiable(x ↦ x ^ a)
  instance postulate Differentiable-[eˣ]         : Differentiable(x ↦ e ^ x)
  instance postulate Differentiable-[⋅]-scalar   : ∀{a} → Differentiable(x ↦ a ⋅ x)
  instance postulate Differentiable-[+]-function : ∀{f g} → ⦃ _ : Differentiable(f) ⦄ → ⦃ _ : Differentiable(g) ⦄ → Differentiable(x ↦ f(x) + g(x))
  instance postulate Differentiable-[−]-function : ∀{f g} → ⦃ _ : Differentiable(f) ⦄ → ⦃ _ : Differentiable(g) ⦄ → Differentiable(x ↦ f(x) − g(x))
  instance postulate Differentiable-[⋅]-function : ∀{f g} → ⦃ _ : Differentiable(f) ⦄ → ⦃ _ : Differentiable(g) ⦄ → Differentiable(x ↦ f(x) ⋅ g(x))
  instance postulate Differentiable-[/]-function : ∀{f g} → ⦃ _ : Differentiable(f) ⦄ → ⦃ _ : Differentiable(g) ⦄ → Differentiable(x ↦ f(x) / g(x))
  instance postulate Differentiable-[∘]-function : ∀{f g} → ⦃ _ : Differentiable(f) ⦄ → ⦃ _ : Differentiable(g) ⦄ → Differentiable(f ∘ g)

  instance postulate [𝐷]-constant     : ∀{a} → ⦃ diff : Differentiable(const(a)) ⦄ → ∀{x} → 𝐷(const(a))(x)⦃ diff ⦄ ≡ a
  instance postulate [𝐷]-id           : ⦃ diff : Differentiable(id) ⦄ → ∀{x} → 𝐷(id)(x)⦃ diff ⦄ ≡ #(1)
  instance postulate [𝐷]-monomial     : ∀{a} → ⦃ diff : Differentiable(x ↦ x ^ a) ⦄ → ∀{x} → 𝐷(x ↦ x ^ a)(x)⦃ diff ⦄ ≡ a ⋅ x ^ (a − #(1))
  instance postulate [𝐷]-[eˣ]         : ⦃ diff : Differentiable(x ↦ e ^ x) ⦄ → ∀{x} → 𝐷(x ↦ e ^ x)(x)⦃ diff ⦄ ≡ e ^ x
  instance postulate [𝐷]-[+]-function : ∀{f g} → ⦃ diff-f : Differentiable(f) ⦄ → ⦃ diff-g : Differentiable(g) ⦄ → ∀{x} → 𝐷(x ↦ f(x) + g(x))(x)⦃ Differentiable-[+]-function ⦃ diff-f ⦄ ⦃ diff-g ⦄ ⦄ ≡ 𝐷(f)(x)⦃ diff-f ⦄ + 𝐷(g)(x)⦃ diff-g ⦄
  instance postulate [𝐷]-[−]-function : ∀{f g} → ⦃ diff-f : Differentiable(f) ⦄ → ⦃ diff-g : Differentiable(g) ⦄ → ∀{x} → 𝐷(x ↦ f(x) − g(x))(x)⦃ Differentiable-[−]-function ⦃ diff-f ⦄ ⦃ diff-g ⦄ ⦄ ≡ 𝐷(f)(x)⦃ diff-f ⦄ − 𝐷(g)(x)⦃ diff-g ⦄
  instance postulate [𝐷]-[⋅]-function : ∀{f g} → ⦃ diff-f : Differentiable(f) ⦄ → ⦃ diff-g : Differentiable(g) ⦄ → ∀{x} → 𝐷(x ↦ f(x) ⋅ g(x))(x)⦃ Differentiable-[⋅]-function ⦃ diff-f ⦄ ⦃ diff-g ⦄ ⦄ ≡ 𝐷(f)(x)⦃ diff-f ⦄ ⋅ g(x) + f(x) ⋅ 𝐷(g)(x)⦃ diff-g ⦄
  instance postulate [𝐷]-[/]-function : ∀{f g} → ⦃ diff-f : Differentiable(f) ⦄ → ⦃ diff-g : Differentiable(g) ⦄ → ∀{x} → 𝐷(x ↦ f(x) / g(x))(x)⦃ Differentiable-[/]-function ⦃ diff-f ⦄ ⦃ diff-g ⦄ ⦄ ≡ (𝐷(f)(x)⦃ diff-f ⦄ ⋅ g(x) − f(x) ⋅ 𝐷(g)(x)⦃ diff-g ⦄)/(g(x) ^ #(2))
  instance postulate [𝐷]-[∘]-function : ∀{f g} → ⦃ diff-f : Differentiable(f) ⦄ → ⦃ diff-g : Differentiable(g) ⦄ → ∀{x} → 𝐷(x ↦ f(g(x)))(x)⦃ Differentiable-[∘]-function ⦃ diff-f ⦄ ⦃ diff-g ⦄ ⦄ ≡ 𝐷(f)(g(x))⦃ diff-f ⦄ ⋅ 𝐷(g)(x)⦃ diff-g ⦄
