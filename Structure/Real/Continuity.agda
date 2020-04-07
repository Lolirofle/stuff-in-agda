-- TODO: Move these to stuff related to metric spaces

module Continuity where
  open Limit

  -- Statement that the point x of function f is a continous point
  ContinuousPoint : (ℝ → ℝ) → ℝ → Stmt
  ContinuousPoint f(x) = (⦃ limit : Lim f(x) ⦄ → (lim f(x)⦃ limit ⦄ ≡ f(x)))

  -- Statement that the function f is continous
  Continuous : (ℝ → ℝ) → Stmt
  Continuous f = ∀{x} → ContinuousPoint f(x)

module Proofs where
  -- instance postulate DifferentiablePoint-to-ContinuousPoint : ∀{f}{x}{diff} → ⦃ _ : DifferentiablePoint f(x)⦃ diff ⦄ ⦄ → ContinuousPoint f(x)
  -- instance postulate Differentiable-to-Continuous : ∀{f}{diff} → ⦃ _ : Differentiable(f)⦃ diff ⦄ ⦄ → Continuous(f)
