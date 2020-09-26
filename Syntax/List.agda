-- Opening this module allows lists to be written using "list notation".
-- Examples:
--   []            = ∅
--   [ a ]         = a ⊰ ∅
--   [ a , b ]     = a ⊰ b ⊰ ∅
--   [ a , b , c ] = a ⊰ b ⊰ c ⊰ ∅
module Syntax.List where

open import Data.List

{-
infixl 1      [_
infixr 1000   _,_
infixl 100000 _]

pattern []      = ∅
pattern [_ l    = l
pattern _,_ x l = x ⊰ l
pattern _] x    = x ⊰ ∅
-}

pattern []                                             = ∅
pattern [_]                 x₁                         = x₁ ⊰ ∅
pattern [_,_]               x₁ x₂                      = x₁ ⊰ x₂ ⊰ ∅
pattern [_,_,_]             x₁ x₂ x₃                   = x₁ ⊰ x₂ ⊰ x₃ ⊰ ∅
pattern [_,_,_,_]           x₁ x₂ x₃ x₄                = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ ∅
pattern [_,_,_,_,_]         x₁ x₂ x₃ x₄ x₅             = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ x₅ ⊰ ∅
pattern [_,_,_,_,_,_]       x₁ x₂ x₃ x₄ x₅ x₆          = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ x₅ ⊰ x₆ ⊰ ∅
pattern [_,_,_,_,_,_,_]     x₁ x₂ x₃ x₄ x₅ x₆ x₇       = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ x₅ ⊰ x₆ ⊰ x₇ ⊰ ∅
pattern [_,_,_,_,_,_,_,_]   x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈    = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ x₅ ⊰ x₆ ⊰ x₇ ⊰ x₈ ⊰ ∅
pattern [_,_,_,_,_,_,_,_,_] x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ = x₁ ⊰ x₂ ⊰ x₃ ⊰ x₄ ⊰ x₅ ⊰ x₆ ⊰ x₇ ⊰ x₈ ⊰ x₉ ⊰ ∅
