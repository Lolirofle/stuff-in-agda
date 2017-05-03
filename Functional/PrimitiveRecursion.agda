module Functional.PrimitiveRecursion{lvl} where

open import Data
open        Data.Tuple.Raise
open import Functional
open import Numeral.Natural
open import Type{lvl}

data Function (n : ℕ) : Type where
  -- Base cases
  Constant    : Function(n)
  Successor   : ℕ → Function(n)
  Projection  : ℕ → Function(n)

  -- Inductive cases
  Composition : ∀{k : ℕ} → Function(k) → (Function(n) ^ k) → Function(n)
  Recursion   : ∀{k : ℕ} → Function(k) → Function(𝐒(𝐒(k))) → Function(n)

record Defs (T : Type) : Type where
  field
    constant  : T
    successor : T → T

-- evaluate : ∀{n}{T} → Defs(T) → Function(n) → (T ^ n) → T
-- evaluate defs Constant _ = Defs.constant(defs)
-- evaluate defs (Successor(i)) x = Defs.successor(defs)(x)
-- evaluate defs (Projection(i)) x = nth(i)(x)
-- evaluate defs (Composition{k}(f)(gs)) x = evaluate{k} defs f (map(g ↦ evaluate defs g x)(gs))
