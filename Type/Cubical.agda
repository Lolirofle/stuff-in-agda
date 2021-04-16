{-# OPTIONS --cubical #-}

module Type.Cubical where

import      Lvl
open import Type

open import Agda.Primitive public
  using (SSet)

open import Agda.Primitive.Cubical public
  using ()
  renaming (I to Interval) -- _ : SSet(Lvl.𝟎). Inhabitants can be seen as points on a closed unit interval.

module Interval where
  open Agda.Primitive.Cubical public
    using (
      Partial ; -- _ : ∀{ℓ} → Interval → Type{ℓ} → SSet(ℓ)
      PartialP -- _ : ∀{ℓ} → (i : Interval) → (.(Is-𝟏 i) → Type{ℓ}) → SSet(ℓ)
    )
    renaming (
      i0 to 𝟎 ; -- _ : Interval. 0 (the initial point) in the interval.
      i1 to 𝟏 ; -- _ : Interval. 1 (the terminal point) in the interval.
      primIMin to min ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟎. Also called: _∧_ (from lattice structure).
      primIMax to max ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟏. Also called: _∨_ (from lattice structure).
      primINeg to flip ; -- _ : Interval → Interval. Flips a point in the interval around the point of symmetry (the middle). Essentially (p ↦ 𝟏 − p).
      IsOne to Is-𝟏 ; -- _ : Interval → SSet(Lvl.𝟎). The predicate stating that a point is 𝟏.
      itIsOne to 𝟏-is-𝟏 ; -- _ : Is-𝟏(𝟏). Proof of 𝟏 being 𝟏.
      primComp to comp ; -- _ : ∀{ℓ : Interval → Lvl.Level} → (P : (i : Interval) → Type{ℓ(i)}) → ∀{i : Interval} → ((j : Interval) → .(Is-𝟏 i) → P(j)) → (P(𝟎) → P(𝟏))
      primHComp to hComp ; -- _ : ∀{ℓ}{A : Type{ℓ}}{i : Interval} → (Interval → .(Is-𝟏 i) → A) → (A → A)
      primTransp to transp -- _ : ∀{ℓ : Interval → Lvl.Level}(A : (i : Interval) → Type{ℓ(i)}) → Interval → A(𝟎)→ A(𝟏).
    )

  -- The distance to the nearest boundary.
  nearBound : Interval → Interval
  nearBound x = min x (flip x)

  -- The distance to the furthest boundary.
  farBound : Interval → Interval
  farBound x = max x (flip x)

  -- Proof of maximum of 𝟏 being 𝟏.
  maxₗ-is-𝟏 : ∀{x y} → Is-𝟏(x) → Is-𝟏(max x y)
  maxₗ-is-𝟏 {x}{y} = Agda.Primitive.Cubical.IsOne1 x y

  -- Proof of maximum of 𝟏 being 𝟏.
  maxᵣ-is-𝟏 : ∀{x y} → Is-𝟏(y) → Is-𝟏(max x y)
  maxᵣ-is-𝟏 {x}{y} = Agda.Primitive.Cubical.IsOne2 x y

  -- The predicate stating that a point is 𝟎.
  Is-𝟎 : Interval → SSet(Lvl.𝟎)
  Is-𝟎 i = Is-𝟏(flip i)

  -- Proof of 𝟎 being 𝟎.
  𝟎-is-𝟎 : Is-𝟎(𝟎)
  𝟎-is-𝟎 = 𝟏-is-𝟏

  -- Proof of minimum of 𝟎 being 𝟎.
  minₗ-is-𝟎 : ∀{x y} → Is-𝟎(x) → Is-𝟎(min x y)
  minₗ-is-𝟎 {x}{y} = maxₗ-is-𝟏 {flip x} {flip y}

  -- Proof of minimum of 𝟎 being 𝟎.
  minᵣ-is-𝟎 : ∀{x y} → Is-𝟎(y) → Is-𝟎(min x y)
  minᵣ-is-𝟎 {x}{y} = maxᵣ-is-𝟏 {flip x} {flip y}
