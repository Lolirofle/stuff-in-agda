module Sets.FnSet where

open import Functional hiding (restrict)

-- TODO: This idea does not seem to work?
record FnSet(T : Set) : Set where
  field
    fn : T → T

  set : FnSet(T)
  fn(set) = id

  restrict : (T → T) → FnSet(T)
  fn(restrict(f)) = fn ∘ f
