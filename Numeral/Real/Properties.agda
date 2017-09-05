module Numeral.Real.Properties where

import Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Numeral.Real
open        Numeral.Real.Continuity
open        Numeral.Real.Derivative
open        Numeral.Real.Limit

module Limits where
  instance postulate [+]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) + g(x))(p)
  instance postulate [−]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) − g(x))(p)
  instance postulate [⋅]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) ⋅ g(x))(p)
  instance postulate [/]-limit : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → Lim(x ↦ f(x) / g(x))(p)

  instance postulate [+]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) + g(x))(p) ≡ lim f(p) + lim g(p))
  instance postulate [−]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) − g(x))(p) ≡ lim f(p) − lim g(p))
  instance postulate [⋅]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) ⋅ g(x))(p) ≡ lim f(p) ⋅ lim g(p))
  instance postulate [/]-lim : ∀{f g p} → ⦃ _ : Lim f(p) ⦄ → ⦃ _ : Lim g(p) ⦄ → (lim(x ↦ f(x) / g(x))(p) ≡ lim f(p) / lim g(p))

module Continuities where
  -- instance postulate DifferentiablePoint-to-ContinuousPoint : ∀{f}{x}{diff} → ⦃ _ : DifferentiablePoint f(x)⦃ diff ⦄ ⦄ → ContinuousPoint f(x)
  -- instance postulate Differentiable-to-Continuous : ∀{f}{diff} → ⦃ _ : Differentiable(f)⦃ diff ⦄ ⦄ → Continuous(f)

module Derivatives where
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
