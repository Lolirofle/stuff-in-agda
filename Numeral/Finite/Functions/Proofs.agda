module Numeral.Finite.Functions.Proofs where

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.Functions
open import Numeral.Finite.Relation
open import Numeral.Finite.Relation.Order
open import Numeral.Natural

private variable N X Y : ℕ
private variable x : 𝕟(X)
private variable y : 𝕟(Y)

min₌-positive : ∀{n}{x y : 𝕟(n)} → Positive(min₌ x y) → Positive(x) ∧ Positive(y)
min₌-positive {x = 𝟎}   {y = 𝟎}   ()
min₌-positive {x = 𝟎}   {y = 𝐒 _} ()
min₌-positive {x = 𝐒 _} {y = 𝟎}   ()
min₌-positive {x = 𝐒 _} {y = 𝐒 _} _ = [∧]-intro [⊤]-intro [⊤]-intro

min-left-value : (x ≤ y) ↔ (min x y ≡ x)
min-left-value {x = 𝟎}  {y = 𝟎}   = [↔]-intro (const <>) (const <>)
min-left-value {x = 𝐒 x}{y = 𝟎}   = [↔]-intro (\()) (\())
min-left-value {x = 𝟎}  {y = 𝐒 y} = [↔]-intro (const <>) (const <>)
min-left-value {x = 𝐒 x}{y = 𝐒 y} = min-left-value {x = x}{y = y}

min-right-value : (x ≥ y) ↔ (min x y ≡ y)
min-right-value {x = 𝟎}  {y = 𝟎}   = [↔]-intro (const <>) (const <>)
min-right-value {x = 𝟎}  {y = 𝐒 y} = [↔]-intro (\()) (\())
min-right-value {x = 𝐒 x}{y = 𝟎}   = [↔]-intro (const <>) (const <>)
min-right-value {x = 𝐒 x}{y = 𝐒 y} = min-right-value {x = x}{y = y}

{-
open import Numeral.Finite.Bound.Proofs
max-left-value : (x ≥ y) ↔ (max x y ≡ x)
max-left-value {x = 𝟎}  {y = 𝟎}   = [↔]-intro (const <>) (const <>)
max-left-value {x = 𝐒 x}{y = 𝟎}   = [↔]-intro (const <>) {!\()!}
max-left-value {x = 𝟎}  {y = 𝐒 y} = [↔]-intro (\()) (\())
max-left-value {x = 𝐒 x}{y = 𝐒 y} = max-left-value {x = x}{y = y}

max-right-value : (x ≤ y) ↔ (max x y ≡ y)
max-right-value {x = 𝟎}    {y = 𝟎}   = [↔]-intro (const <>) (const <>)
max-right-value {x = 𝟎 {X}}{y = 𝐒 y} = [↔]-intro (const <>) {!\_ → bound-[≤?]-identity {A = X}{n = 𝐒 y}!}
max-right-value {x = 𝐒 x}  {y = 𝟎}   = [↔]-intro (\()) (\())
max-right-value {x = 𝐒 x}  {y = 𝐒 y} = max-right-value {x = x}{y = y}
-}
