module Type.Cubical where

import      Agda.Primitive.Cubical
open import Logic
open import Type

open Agda.Primitive.Cubical public
  using ()
  renaming (I to Interval) -- _ : Typeω. The closed unit interval.

module Interval where
  open Agda.Primitive.Cubical public
    using ()
    renaming (
      i0 to 𝟎 ; -- _ : Interval. 0 (the initial point) in the interval.
      i1 to 𝟏 ; -- _ : Interval. 1 (the terminal point) in the interval.
      primIMin to min ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟎.
      primIMax to max ; -- _ : Interval → Interval → Interval. Chooses the point nearest 𝟏.
      primINeg to inv ; -- _ : Interval → Interval. Flips a point in the interval around the point of symmetry (the middle). Essentially (p ↦ 𝟏 − p).
      IsOne to Is-𝟏 ; -- _ : Interval → Stmtω. The predicate stating that a point is 𝟏.
      itIsOne to 𝟏-is-𝟏 ; -- _ : Is-𝟏(𝟏). Proof of 𝟏 being 𝟏.
      IsOne1 to maxₗ-is-𝟏 ; -- _ : ∀{x y} → Is-𝟏(x) → Is-𝟏(max x y). Proof of maximum of 𝟏 being 𝟏.
      IsOne2 to maxᵣ-is-𝟏 -- _ : ∀{x y} → Is-𝟏(y) → Is-𝟏(max x y) Proof of maximum of 𝟏 being 𝟏.
    )

  Is-𝟎 : Interval → Stmtω
  Is-𝟎 i = Is-𝟏(inv i)

  𝟎-is-𝟎 : Is-𝟎(𝟎)
  𝟎-is-𝟎 = 𝟏-is-𝟏

  -- TODO: Are these not possible to prove?
  -- minₗ-is-𝟎 : ∀{x y} → Is-𝟎(x) → Is-𝟎(min x y)
  -- minᵣ-is-𝟎 : ∀{x y} → Is-𝟎(y) → Is-𝟎(min x y)
