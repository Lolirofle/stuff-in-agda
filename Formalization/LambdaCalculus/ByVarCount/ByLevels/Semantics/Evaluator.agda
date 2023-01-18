-- Normalization of terms, defined using a non-terminating function.
-- Denotational semantics expressed using an Agda function.
-- Expressing this as a function is possible because the reduction semantics are deterministic
-- Sources:
-- • "Demonstrating Lambda Calculus Reduction, Peter Sestoft" (2022-12-01) [https://www.itu.dk/~sestoft/papers/sestoft-lamreduce.pdf]
-- • (2022-12-01) [https://en.wikipedia.org/wiki/Evaluation_strategy]
-- TODO: Not sure if these are the usual definitions of for example call-by-name vs normal order and call-by-value vs applicative order. Look up how influential and how often cited the paper is, and the author. Though, the definitions below are convenient for distinguishing between strategies that reduces under lambdas or not.
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Evaluator where

open import Data
open import Data.Boolean
open import Data.Option
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Functions
import      Lvl
import      Numeral.Finite as 𝕟
open import Type

record βOptions : Type{Lvl.𝟎}
record Options : Type{Lvl.𝟎}

-- Options for β-reductions for the function `normalize`.
record βOptions where
  field
    -- If the argument should be normalized in `Apply`-terms before β-reducing.
    -- Reflects `_⇴_.cong-applyₗ`.
    -- This is usually defined as strict or non-strict evaluation order, whether to evaluate the argument before or after the β-reduction.
    -- Note: Lazy evaluation or call-by-need, defined as non-strict and arguments evaluated only once (when needed), is not possible in this implementation because the terms are directly substituted in β-reductions. The implementation have no sharing of environments.
    apply-arg : Bool

-- Options for the function `normalize`.
record Options where
  inductive
  field
    -- If the function body should be normalized in `Abstract`-terms.
    -- Reflects `_⇴_.cong-abstract`.
    abstract-body : Bool

    -- If the function should be normalized in `Apply`-terms, and if it should use different options when doing so.
    -- Reflects `_⇴_.cong-applyₗ`.
    apply-func : Option(Option Options)

    -- If the argument should be normalized in `Apply`-terms.
    -- Reflects `_⇴_.cong-applyᵣ`.
    apply-arg : Bool

    -- If β-reductions should be performed.
    -- Reflects `_⇴_.β`.
    β : Option βOptions

    -- If η-reductions should be performed.
    -- Reflects `_⇴_.η`.
    -- TODO: Not implemented yet
    η : Option Unit

-- Normalization options for the call-by-name reduction strategy.
-- This normalizes to weak head normal form (WHNF).
callByName : Options
callByName = record
  { abstract-body = 𝐹
  ; apply-func = Some None
  ; apply-arg = 𝐹
  ; β = Some record{apply-arg = 𝐹}
  ; η = None
  }

-- Normalization options for the normal order reduction strategy.
-- This normalizes to normal form (NF).
normalOrder : Options
normalOrder = record
  { abstract-body = 𝑇
  ; apply-func = Some(Some callByName)
  ; apply-arg = 𝑇
  ; β = Some record{apply-arg = 𝐹}
  ; η = None
  }

-- Normalization options for the call-by-value reduction strategy.
-- This normalizes to weak normal form (WNF).
callByValue : Options
callByValue = record
  { abstract-body = 𝐹
  ; apply-func = Some None
  ; apply-arg = 𝑇
  ; β = Some record{apply-arg = 𝑇}
  ; η = None
  }

-- Normalization options for the applicative order reduction strategy.
-- This normalizes to normal form (NF).
applicativeOrder : Options
applicativeOrder = record
  { abstract-body = 𝑇
  ; apply-func = Some None
  ; apply-arg = 𝑇
  ; β = Some record{apply-arg = 𝑇}
  ; η = None
  }

-- Normalization options for the head spine reduction strategy.
-- This normalizes to head normal form (HNF).
headSpine : Options
headSpine = record
  { abstract-body = 𝑇
  ; apply-func = Some None
  ; apply-arg = 𝐹
  ; β = Some record{apply-arg = 𝐹}
  ; η = None
  }

-- Also called: evaluate, eval, ⟦_⟧.
{-# NON_TERMINATING #-}
normalize : Options → ∀{d} → Term(d) → Term(d)

private
  -- `normalize` if true.
  -- `const id` if false.
  maybeNormalize : Bool → Options → ∀{d} → Term(d) → Term(d)
  maybeNormalize 𝑇 opt t = normalize opt t
  maybeNormalize 𝐹 opt t = t
  {-# INLINE maybeNormalize #-}

  -- Normalize using `opt` if `Some(Some opt)`.
  -- `normalize` if `Some None`.
  -- `const id` if `None`.
  maybeOptNormalize : Option(Option Options) → Options → ∀{d} → Term(d) → Term(d)
  maybeOptNormalize (Some(Some opt)) _   t = normalize opt t
  maybeOptNormalize (Some None)      opt t = normalize opt t
  maybeOptNormalize None             opt t = t
  {-# INLINE maybeOptNormalize #-}

normalize opt                       (Var v)      = Var v
normalize opt                       (Abstract x) = Abstract(maybeNormalize (Options.abstract-body opt) opt x)
normalize opt                       (Apply f x) with maybeOptNormalize (Options.apply-func opt) opt f
normalize opt@record{β = Some βopt} (Apply f x) | Abstract fₑ = normalize opt(substituteVar 𝕟.maximum (maybeNormalize (βOptions.apply-arg βopt) opt x) fₑ)
{-# CATCHALL #-}
normalize opt                       (Apply f x) | fₑ          = Apply fₑ (maybeNormalize (Options.apply-arg opt) opt x)
