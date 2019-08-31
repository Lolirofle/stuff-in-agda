module Main where

import Data
import Data.Any
import Data.Boolean
import Data.Boolean.Operators
import Data.Boolean.Proofs
import Data.Boolean.Stmt
import Data.Either
import Data.List
import Data.List.Computability
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
import FFI.IO as FFI
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
import Logic
import Logic.Classical
import Logic.Computability
import Logic.Computability.Binary
import Logic.Names
import Logic.Predicate
import Logic.Predicate.Theorems
import Logic.Propositional
import Logic.Propositional.Theorems
import Lvl
-- import Numeral.CoordinateVector
import Numeral.Finite
-- import Numeral.Finite.Oper
-- import Numeral.FiniteInclusive
-- import Numeral.Matrix
import Numeral.Integer
import Numeral.Natural
import Numeral.Natural.Oper
import Numeral.Natural.Oper.Comparisons
import Numeral.Natural.Relation.Computability
import Numeral.Natural.Relation.Order
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
import Sets.Setoid
-- import String
import Structure.Function.Domain
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

module _ where
  main : FFI.IO Data.Unit
  main = FFI.printStrLn("Okay")

module _ where
  open Syntax.Function
  open Type

  test : Set → Set → Set
  test = (x ↦ y ↦ x :of: Set :of: Set)
