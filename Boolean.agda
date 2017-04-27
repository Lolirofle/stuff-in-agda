module Boolean where

open import Type

data Bool : Set where
  𝑇 : Bool
  𝐹 : Bool

module Operators where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_ _⊕_

  _∧_ : Bool → Bool → Bool
  _∧_ 𝑇 𝑇 = 𝑇
  _∧_ 𝐹 𝑇 = 𝐹
  _∧_ 𝑇 𝐹 = 𝐹
  _∧_ 𝐹 𝐹 = 𝐹

  _∨_ : Bool → Bool → Bool
  _∨_ 𝑇 𝑇 = 𝑇
  _∨_ 𝐹 𝑇 = 𝑇
  _∨_ 𝑇 𝐹 = 𝑇
  _∨_ 𝐹 𝐹 = 𝐹

  _⊕_ : Bool → Bool → Bool
  _⊕_ 𝑇 𝑇 = 𝐹
  _⊕_ 𝐹 𝑇 = 𝑇
  _⊕_ 𝑇 𝐹 = 𝑇
  _⊕_ 𝐹 𝐹 = 𝐹

  ¬_ : Bool → Bool
  ¬_ 𝑇 = 𝐹
  ¬_ 𝐹 = 𝑇

if_then_else_ : ∀{n}{T : TypeN n} → Bool → T → T → T
if_then_else_ 𝑇 expr _ = expr
if_then_else_ 𝐹 _ expr = expr
