-- Sources:
-- • (2022-12-01) [https://en.wikipedia.org/wiki/Beta_normal_form]
-- • (2022-12-01) [https://en.wikipedia.org/wiki/Lambda_calculus_definition#Normal_form] (βη-normal forms)
-- • "Demonstrating Lambda Calculus Reduction, Peter Sestoft" (2022-12-01) [https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf]
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Operators.Normal where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Formalization.LambdaCalculus.ByVarCount
import      Numeral.Finite.Oper.Comparisons as 𝕟
open import Type

record Options : Type{Lvl.𝟎} where
  field
    apply-arg     : Bool
    abstract-body : Bool
    β : Bool
    η : Bool

-- β normal form.
βNF : Options
βNF = record { apply-arg = 𝑇 ; abstract-body = 𝑇 ; β = 𝑇 ; η = 𝐹 }

-- β head normal form.
βHNF : Options
βHNF = record { apply-arg = 𝐹 ; abstract-body = 𝑇 ; β = 𝑇 ; η = 𝐹 }

-- β weak normal form.
βWNF : Options
βWNF = record { apply-arg = 𝑇 ; abstract-body = 𝐹 ; β = 𝑇 ; η = 𝐹 }

-- β weak head normal form.
βWHNF : Options
βWHNF = record { apply-arg = 𝐹 ; abstract-body = 𝐹 ; β = 𝑇 ; η = 𝐹 }

{-# TERMINATING #-}
isNormalForm : Options → ∀{d} → Term(d) → Bool
isNormalForm opt@record{η = 𝑇}                     (Abstract(Apply _ (Var v))) with 𝕟.isMax v
isNormalForm opt@record{η = 𝑇}                     (Abstract _) | 𝑇 = 𝐹
isNormalForm opt@record{η = 𝑇 ; abstract-body = 𝑇} (Abstract x) | 𝐹 = isNormalForm opt x -- Note: This clause is the problem for the termination checker. It should not be a problem because it is the same as the clauses below.
{-# CATCHALL #-}
isNormalForm opt@record{η = 𝑇}                     _            | 𝐹 = 𝑇
{-# CATCHALL #-}
isNormalForm opt@record{abstract-body = 𝑇} (Abstract x)                    = isNormalForm opt x
{-# CATCHALL #-}
isNormalForm record{β = 𝑇}                 (Apply(Abstract _) _)           = 𝐹
{-# CATCHALL #-}
isNormalForm opt@record{apply-arg = 𝑇}     (Apply f x)                     = isNormalForm opt f && isNormalForm opt x
{-# CATCHALL #-}
isNormalForm opt@record{apply-arg = 𝐹}     (Apply f _)                     = isNormalForm opt f
{-# CATCHALL #-}
isNormalForm opt                           _                               = 𝑇
