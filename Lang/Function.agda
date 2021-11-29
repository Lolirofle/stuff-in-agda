module Lang.Function where

import      Lvl
open import Data.Boolean
open import Data.List as List using (List)
open import Data.List.Functions.Positional as List
open import Data.Option
open import Data
open import Lang.Reflection
open import Lang.Reflection.DoNotation
open import Syntax.Do
open import Type

-- A default value tactic for implicit arguments.
-- This implements a "default arguments" language feature.
-- It works by always unifying the hole with the specified value.
-- Essentially a constant function for holes.
-- Example:
--   test : ∀{@(tactic default 𝑇) x : Bool} → Bool
--   test{x} = x
--   Now, `test = 𝑇`, `test{𝑇} = 𝑇`, `test{𝐹} = 𝐹`.
default : ∀{ℓ}{T : Type{ℓ}} → T → Term → TC(Unit{Lvl.𝟎})
default x hole = quoteTC x >>= unify hole

-- A no inferrance tactic for implicit arguments.
-- This makes implicit arguments work like explicit arguments by throwing an error when the hole does not match perfectly while still maintaining its implicit visibility status.
-- It works by always selecting the last argument in the hole, and the last argument is the one closest to the value, which is the argument one expects it to choose.
-- Examples:
--   idᵢwith : ∀{T : TYPE} → {@(tactic no-infer) x : T} → T
--   idᵢwith {x = x} = x
--
--   idᵢwithout : ∀{T : TYPE} → {x :  T} → T
--   idᵢwithout {x = x} = x
--
--   postulate test : ({_ : Bool} → Bool) → Bool
--
--   test1 : Bool
--   test1 = test idᵢwith
--
--   test2 : (Bool → Bool) → Bool
--   test2 _ = test idᵢwith
--
--   test3 : ∀{T : TYPE} → {_ : T} → T
--   test3 = idᵢwith
--
--   It is useful in these kinds of scenarios because idᵢwithout would require writing the implicit argument explicitly, while idᵢwith always uses the given argument in order like how explicit arguments work.
no-infer : Term → TC(Unit{Lvl.𝟎})
no-infer hole@(meta _ args) with List.last(args)
... | None                                   = typeError (List.singleton (strErr "Expected a parameter with \"hidden\" visibility when using \"no-infer\", found none."))
... | Some (arg (arg-info hidden    _) term) = unify hole term
{-# CATCHALL #-}
... | Some (arg (arg-info _         _) term) = typeError (List.singleton (strErr "Wrong visibility of argument. Expected \"hidden\" when using \"no-infer\"."))
{-# CATCHALL #-}
no-infer _ = typeError (List.singleton (strErr "TODO: In what situations are this error occurring?"))

-- TODO: Implement idᵢwith, rename it to idᵢ, and put it in Functional. Also, try to refactor Data.Boolean, Data.List and Data.Option so that they only contain the type definition and its constructors. This minimizes the amount of dependencies this module requires (which should help in case of circular dependencies when importing this module).
