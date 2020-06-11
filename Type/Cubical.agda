module Type.Cubical where

import      Agda.Primitive.Cubical
open import Type

open Agda.Primitive.Cubical public
  using ()
  renaming (I to Interval) -- _ : Typeω. Inhabitants can be seen as points on a closed unit interval.

module Interval where
  open Agda.Primitive.Cubical public
    using (
      Partial ; -- _ : ∀{ℓ} → Interval → Type{ℓ} → Typeω
      PartialP -- _ : ∀{ℓ} → (i : Interval) → Partial(i)(Type{ℓ}) → Typeω
    )
    renaming (
      i0 to 𝟎 ; -- _ : Interval. 0 (the initial point) in the interval.
      i1 to 𝟏 ; -- _ : Interval. 1 (the terminal point) in the interval.
      primIMin to min ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟎.
      primIMax to max ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟏.
      primINeg to flip ; -- _ : Interval → Interval. Flips a point in the interval around the point of symmetry (the middle). Essentially (p ↦ 𝟏 − p).
      IsOne to Is-𝟏 ; -- _ : Interval → Stmtω. The predicate stating that a point is 𝟏.
      itIsOne to 𝟏-is-𝟏 ; -- _ : Is-𝟏(𝟏). Proof of 𝟏 being 𝟏.
      primComp to comp ;
      primHComp to hComp ; -- _ : ∀{ℓ}{A : Type{ℓ}}{i : Interval} → (Interval → Partial(i)(A)) → A → A
      primTransp to transp -- _ : ∀{ℓ}(A : Interval → Type{ℓ}) → Interval → A(𝟎)→ A(𝟏). 
    )

  -- Proof of maximum of 𝟏 being 𝟏.
  maxₗ-is-𝟏 : ∀{x y} → Is-𝟏(x) → Is-𝟏(max x y)
  maxₗ-is-𝟏 {x}{y} = Agda.Primitive.Cubical.IsOne1 x y

  -- Proof of maximum of 𝟏 being 𝟏.
  maxᵣ-is-𝟏 : ∀{x y} → Is-𝟏(y) → Is-𝟏(max x y)
  maxᵣ-is-𝟏 {x}{y} = Agda.Primitive.Cubical.IsOne2 x y

  -- The predicate stating that a point is 𝟎.
  Is-𝟎 : Interval → Typeω
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
