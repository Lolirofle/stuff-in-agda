module Boolean where

import Level as Lvl
open import Type

-- Boolean type
data Bool : Type{Lvl.𝟎} where
  𝑇 : Bool -- Represents truth
  𝐹 : Bool -- Represents falsity

-- Control-flow if-else expression
if_then_else_ : ∀{ℓ}{T : Type{ℓ}} → Bool → T → T → T
if_then_else_ 𝑇 expr _ = expr
if_then_else_ 𝐹 _ expr = expr
