module Boolean {lvl} where

open import Type{lvl}

data Bool : Type where
  𝑇 : Bool
  𝐹 : Bool

if_then_else_ : ∀{T : Type} → Bool → T → T → T
if_then_else_ 𝑇 expr _ = expr
if_then_else_ 𝐹 _ expr = expr
