module Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda where

open import Formalization.LambdaCalculus.ByVarCount

open import Formalization.LambdaCalculus.ByVarCount.Syntax.VarNumeral public
{-# DISPLAY Term.Var v = v #-}

pattern 𝜆 d expr = Term.Abstract{d} expr
{-# DISPLAY Term.Abstract{d} expr = 𝜆 d expr #-}

pattern _←_ a b  = Term.Apply a b
infixl 101 _←_
{-# DISPLAY Term.Apply a b = a ← b #-}

