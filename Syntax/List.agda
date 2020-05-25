-- Opening this module allows lists to be written using "list notation".
-- Examples:
--   []            = ∅
--   [ a ]         = a ⊰ ∅
--   [ a , b ]     = a ⊰ b ⊰ ∅
--   [ a , b , c ] = a ⊰ b ⊰ c ⊰ ∅
module Syntax.List where

open import Data.List

infixl 1      [_
infixr 1000   _,_
infixl 100000 _]

pattern []      = ∅
pattern [_ l    = l
pattern _,_ x l = x ⊰ l
pattern _] x    = x ⊰ ∅
