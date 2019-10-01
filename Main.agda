module Main where

import Data
import Data.Any
import Data.Boolean
import Data.Boolean.Operators
import Data.Boolean.Proofs
import Data.Boolean.Stmt
import Data.Boolean.Stmt.Proofs
import Data.Either
import Data.Either.Proofs
import Data.List
import Data.List.Computability
import Data.List.Proofs
import Data.List.Relation.Membership.Proofs
import Data.List.Relation.Sublist.Proofs
import Data.List.Relation
import Data.List.Relation.Membership
import Data.List.Relation.Sublist
-- import Data.ListNonEmpty
import Data.ListSized
import Data.Option
import Data.Option.Proofs
import Data.Proofs
import Data.Tuple
import Data.Tuple.Function
-- import Data.Tuple.List
import Data.Tuple.Proofs
import Data.Tuple.Raise
import Data.Tuple.Raiseᵣ
import Data.Tuple.Raiseₗ
import FFI.IO as FFI
import Functional
import FormalLanguage
import FormalLanguage.Equals
import FormalLanguage.Proofs
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
import Metalogic.Classical.Propositional.ProofSystem
import Metalogic.Classical.Propositional.Syntax
import Metalogic.Classical.Propositional.TruthSemanticsModel
import Numeral.CoordinateVector
-- import Numeral.CoordinateVector.Proofs
import Numeral.Finite
import Numeral.Finite.Bound
import Numeral.Finite.Functions
import Numeral.Finite.Oper
import Numeral.Finite.Oper.Comparisons
import Numeral.Finite.Proofs
-- import Numeral.FiniteInclusive
import Numeral.Integer
-- import Numeral.Integer.Function
-- import Numeral.Integer.Oper
-- import Numeral.Integer.Proofs
-- import Numeral.Integer.Relation
-- import Numeral.Integer.Sign
import Numeral.Matrix
import Numeral.Natural
-- import Numeral.Natural.Coprime
import Numeral.Natural.Function
import Numeral.Natural.Function.Proofs
-- import Numeral.Natural.GreatestCommonDivisor
import Numeral.Natural.Induction
import Numeral.Natural.Inductions
import Numeral.Natural.Oper
import Numeral.Natural.Oper.Comparisons
import Numeral.Natural.Oper.Comparisons.Proofs
import Numeral.Natural.Oper.Divisibility
import Numeral.Natural.Oper.Modulo
-- import Numeral.Natural.Oper.Modulo.Proofs
import Numeral.Natural.Oper.Proofs
-- import Numeral.Natural.Prime
import Numeral.Natural.Relation
import Numeral.Natural.Relation.Computability
-- import Numeral.Natural.Relation.Divisibility
-- import Numeral.Natural.Relation.Divisibility.Proofs
import Numeral.Natural.Relation.Order
-- import Numeral.Natural.Relation.Order.Classical
-- import Numeral.Natural.Relation.Order.Computability
-- import Numeral.Natural.Relation.Order.Existence
-- import Numeral.Natural.Relation.Order.Existence.Proofs
import Numeral.Natural.Relation.Order.Proofs
-- import Numeral.Natural.Relation.Properties
-- import Numeral.Natural.TotalOper
import Numeral.Natural.UnclosedOper
-- import Numeral.Rational.AlterAdd
-- import Numeral.Rational.SternBrocot
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Sign.Oper0
import Operator.Equals
import Relator.Congruence
import Relator.Congruence.Proofs
import Relator.Equals
import Relator.Equals.Equivalence
import Relator.Equals.Heterogenous
import Relator.Equals.Names
import Relator.Equals.Proofs
import Relator.Names
import Relator.Ordering
import Sets.BoolSet
import Sets.Setoid
import Sets.Setoid.Proofs
import Sets.Setoid.Size
import Sets.Setoid.Size.Proofs
import Sets.Setoid.Uniqueness
import Sets.Setoid.Uniqueness.Proofs
import Stream
import String
-- import Structure.Arithmetic
import Structure.Category
import Structure.Function.Domain
import Structure.Function.Domain.Proofs
import Structure.Function.Linear
import Structure.Function.Ordering
-- import Structure.LinearAlgebra
-- import Structure.Logic.Classical.NaturalDeduction
-- import Structure.Logic.Classical.NaturalDeduction.Proofs
-- import Structure.Logic.Classical.PredicateBoundedQuantification
-- import Structure.Logic.Classical.SetTheory
-- import Structure.Logic.Classical.SetTheory.Function
-- import Structure.Logic.Classical.SetTheory.Relation
-- import Structure.Logic.Classical.SetTheory.SetBoundedQuantification
-- import Structure.Logic.Classical.SetTheory.Structure.Function
-- import Structure.Logic.Classical.SetTheory.Structure.Numeral
-- import Structure.Logic.Classical.SetTheory.Structure.Relator
-- import Structure.Logic.Classical.SetTheory.ZFC
-- import Structure.Logic.Classical.SetTheory.ZFC.BinaryRelatorSet
-- import Structure.Logic.Classical.SetTheory.ZFC.Finite
-- import Structure.Logic.Classical.SetTheory.ZFC.FunctionSet
-- import Structure.Logic.Classical.SetTheory.ZFC.FunctionSet.Proofs
-- import Structure.Logic.Classical.SetTheory.ZFC.Numeral
-- import Structure.Logic.Classical.SetTheory.ZFC.Numeral.Integer
-- import Structure.Logic.Classical.SetTheory.ZFC.Numeral.Natural
-- import Structure.Logic.Classical.SetTheory.ZFC.Numeral.Rational
-- import Structure.Logic.Classical.SetTheory.ZFC.Numeral.Real
-- import Structure.Logic.Classical.SetTheory.ZFC.Proofs
-- import Structure.Logic.Constructive.Functions
-- import Structure.Logic.Constructive.Functions.Properties
-- import Structure.Logic.Constructive.NaturalDeduction
-- import Structure.Logic.Constructive.Relations.Properties
-- import Structure.Logic.Constructive.Syntax.Algebra
import Structure.Operator.Field
import Structure.Operator.Functions
import Structure.Operator.Group
-- import Structure.Operator.Group.Proofs
import Structure.Operator.Monoid
-- import Structure.Operator.Monoid.Proofs
import Structure.Operator.Names
-- import Structure.Operator.Proofs
import Structure.Operator.Properties
-- import Structure.Operator.SetAlgebra
-- import Structure.Operator.Vector
import Structure.Real
import Structure.Real.Abs
import Structure.Relator.Equivalence
import Structure.Relator.Function
import Structure.Relator.Ordering
import Structure.Relator.Properties
import Structure.Relator.Properties.Proofs
import Syntax.Function
import Syntax.Method
import Syntax.Number
import Type
import Type.Dependent
import Type.Empty
import Type.Empty.Proofs
import Type.Singleton
import Type.Singleton.Proofs
import Type.Size
import Type.Size.Countable
import Type.Size.Finite
import Type.Size.Proofs

import Type.Unit
import Type.Unit.Proofs

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")

module _ where
  open Syntax.Function
  open Type

  test : Set → Set → Set
  test = (x ↦ y ↦ x :of: Set :of: Set)
