module Formalization.LambdaCalculus.ByVarCount.Syntax.ImplicitLambda where

open import Formalization.LambdaCalculus.ByVarCount

open import Formalization.LambdaCalculus.ByVarCount.Syntax.VarNumeral public
{-# DISPLAY Term.Var v = v #-}

pattern 𝜆_ {d} expr = Term.Abstract{d} expr
infixl 100 𝜆_
{-# DISPLAY Term.Abstract expr = 𝜆 expr #-}

pattern _←_ a b  = Term.Apply a b
infixl 101 _←_
{-# DISPLAY Term.Apply a b = a ← b #-}
