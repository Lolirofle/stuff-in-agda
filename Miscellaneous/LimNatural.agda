{-# OPTIONS --cubical #-}

module Miscellaneous.LimNatural where

import      Lvl
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Sign as Sign using (−|+ ; −|0|+ ; ➖ ; ➕)
open import Type.Cubical
open import Type.Cubical.Path.Equality
open import Type

data ℕ∞ : Type{Lvl.𝟎} where
  𝟎 : ℕ∞
  𝐒 : ℕ∞ → ℕ∞
  ∞ : ℕ∞
  𝐒-fixpoint : (𝐒(∞) ≡ ∞)

𝐏₀ : ℕ∞ → ℕ∞
𝐏₀(𝟎)    = 𝟎
𝐏₀(𝐒(n)) = n
𝐏₀(∞)    = ∞
𝐏₀(𝐒-fixpoint i) = ∞

_+_ : ℕ∞ → ℕ∞ → ℕ∞
x + 𝟎    = x
x + 𝐒(y) = 𝐒(x + y)
_ + ∞    = ∞
x + 𝐒-fixpoint i = 𝐒-fixpoint i

_⋅_ : ℕ∞ → ℕ∞ → ℕ∞
x ⋅ 𝟎    = 𝟎
x ⋅ 𝐒(y) = x + (x ⋅ y)
x ⋅ ∞    = ∞
x ⋅ 𝐒-fixpoint i = ∞

infixl 10010 _+_
infixl 10020 _⋅_

open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type.Cubical.Path.Proofs

private variable x y z : ℕ∞

𝐒-∞-involutive : (𝐒(𝐒(∞)) ≡ ∞)
𝐒-∞-involutive = congruence₁(𝐒) 𝐒-fixpoint 🝖 𝐒-fixpoint

instance
  𝐒-injectivity : Injective(𝐒)
  Injective.proof 𝐒-injectivity = congruence₁(𝐏₀)

[+]-baseₗ : (𝟎 + x ≡ x)
[+]-baseₗ {𝟎}   = reflexivity(_≡_)
[+]-baseₗ {𝐒 x} = congruence₁(𝐒) ([+]-baseₗ {x})
[+]-baseₗ {∞}   = reflexivity(_≡_)
[+]-baseₗ {𝐒-fixpoint i} = reflexivity(_≡_) {𝐒-fixpoint i}

[+]-stepₗ : (𝐒(x) + y ≡ 𝐒(x + y))
[+]-stepₗ {x} {𝟎}   = reflexivity(_≡_)
[+]-stepₗ {x} {𝐒 y} = congruence₁(𝐒) ([+]-stepₗ {x}{y})
[+]-stepₗ {x} {∞}   = symmetry(_≡_) 𝐒-fixpoint
[+]-stepₗ {x} {𝐒-fixpoint i} = symmetry(_≡_) (Interval.hComp diagram {!!}) where
  diagram : Interval → Interval.Partial(Interval.farBound i) _
  diagram _ (i = Interval.𝟎) = congruence₁(𝐒) 𝐒-fixpoint
  diagram _ (i = Interval.𝟏) = 𝐒-fixpoint
  {-
  i0 j0 𝐒∞
  i0 j1 𝐒𝐒∞
  i1 j0 ∞
  i1 j1 𝐒∞
  -}
  -- test : ∀{i} → (𝐒(𝐒-fixpoint i) ≡ 𝐒-fixpoint i)
  -- test {i} j = {!!}
  {-
  i0 j0 𝐒𝐒∞
  i0 j1 𝐒∞
  i1 j0 𝐒∞
  i1 j1 ∞
  -}
