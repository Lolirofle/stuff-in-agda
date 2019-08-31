module Main where

import Data
import Data.Any
import Data.Boolean
import Data.Boolean.Stmt
import Data.Boolean.Operators
-- import Data.Boolean.Proofs
import Data.Either
import Data.List
-- import Data.List
-- import Data.List.Computability
-- import Data.List.Proofs
-- import Data.List.Proofs.Membership
-- import Data.List.Proofs.Sublist
-- import Data.List.Relation
-- import Data.List.Relation.Membership
-- import Data.List.Relation.Sublist
-- import Data.ListNonEmpty
import Data.ListSized
import Data.Option
-- import Data.Proofs
import Data.Tuple
import Data.Tuple.Function
-- import Data.Tuple.List
import Data.Tuple.Proofs
import Data.Tuple.Raise
import Data.Tuple.Raiseᵣ
import Data.Tuple.Raiseₗ
-- import FFI.IO
import Functional
-- import Functional.DomainRaise
import Functional.Domains
import Functional.Domains.Proofs
import Functional.Equals
import Functional.Equals.Proofs
import Functional.Names
import Functional.PrimitiveRecursion
import Functional.Proofs
import Functional.Repeat
import Functional.Repeat.Proofs
import Lang.Instance
import Lang.Irrelevance
import Logic.Names
import Logic.Predicate
import Logic.Predicate.Theorems
import Logic.Propositional
import Logic.Propositional.Theorems
import Lvl
-- import Numeral.CoordinateVector
import Numeral.FiniteStrict
-- import Numeral.FiniteStrict.Oper
-- import Numeral.Finite
-- import Numeral.Matrix
import Numeral.Natural
import Numeral.Natural.Relation.Computability
import Numeral.Integer
-- import Relator.Bijection
-- import Relator.Congruence
-- import Relator.Congruence.Proofs
-- import Relator.Countable
import Relator.Equals
import Relator.Equals.Proofs
import Relator.Equals.Uniqueness
-- import Relator.Equals.Uniqueness.Proofs
-- import Relator.Finite
import Relator.Ordering
-- import String
-- import Structure.Function.Domain
import Structure.Function.Linear
import Structure.Function.Ordering
import Structure.Relator.Equivalence
import Structure.Relator.Function
import Structure.Relator.Ordering
import Structure.Relator.Properties
import Syntax.Function
import Syntax.Method
import Syntax.Number
import Type
import Type.Dependent
import Type.Empty
import Type.Empty.Proofs
import Type.Singleton
import Type.Singleton.Proofs
-- import Type.Size
-- import Type.Size.Finite.Count
-- import Type.Size.Proofs
import Type.Unit
import Type.Unit.Proofs

-- main : FFI.IO Data.Unit
-- main = FFI.printStrLn("Okay")

module _ where
  open Syntax.Function
  open Type

  test : Set → Set → Set
  test = (x ↦ y ↦ x :of: Set :of: Set)
