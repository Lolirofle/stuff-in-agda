module Boolean {lvl} where

open import Type{lvl}

-- Boolean type
data Bool : Type where
  𝑇 : Bool -- Represents truth
  𝐹 : Bool -- Represents falsity

-- Control-flow if-else expression
if_then_else_ : ∀{T : Type} → Bool → T → T → T
if_then_else_ 𝑇 expr _ = expr
if_then_else_ 𝐹 _ expr = expr
