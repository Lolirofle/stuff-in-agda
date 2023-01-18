module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Operators where

import      Lvl
open import Data.Boolean
open import Formalization.LambdaCalculus.ByVarCount
open import Numeral.Finite
open import Numeral.Natural
open import Type

private variable d : ℕ

isAbstract : Term(d) → Bool
isAbstract (Abstract _) = 𝑇
{-# CATCHALL #-}
isAbstract _ = 𝐹

isApply : Term(d) → Bool
isApply (Apply _ _) = 𝑇
{-# CATCHALL #-}
isApply _ = 𝐹

isVar : Term(d) → Bool
isVar (Var _) = 𝑇
{-# CATCHALL #-}
isVar _ = 𝐹
