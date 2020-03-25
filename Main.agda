module Main where

import Data
import Data.Any
import Data.Boolean
import Data.Boolean.Operators
import Data.Boolean.Proofs
import Data.Boolean.Stmt
import Data.Boolean.Stmt.Proofs
import Data.Either
import Data.Either.Equiv
import Data.Either.Equiv.Proofs
import Data.Either.Proofs
import Data.List
import Data.List.Computability
-- import Data.List.Functor
import Data.List.Proofs
import Data.List.Relation
import Data.List.Relation.Membership
import Data.List.Relation.Membership.Proofs
import Data.List.Relation.Sublist
import Data.List.Relation.Sublist.Proofs
-- import Data.ListNonEmpty
import Data.ListSized
import Data.Option
-- import Data.Option.Functor
import Data.Option.Proofs
import Data.Proofs
import Data.Tuple
-- import Data.Tuple.Category
import Data.Tuple.Equiv
import Data.Tuple.Function
-- import Data.Tuple.List
import Data.Tuple.Proofs
import Data.Tuple.Raise
import Data.Tuple.Raiseᵣ
import Data.Tuple.Raiseₗ
import FFI.IO as FFI
import FormalLanguage
import FormalLanguage.ContextFreeGrammar
import FormalLanguage.Equals
import FormalLanguage.Proofs
import FormalLanguage.RegularExpression
-- import Formalization.ClassicalPropositionalLogic
-- import Formalization.FunctionalML
-- import Formalization.LambdaCalculus
import Formalization.PrimitiveRecursion
-- import Formalization.SKICombinatorCalculus
import Formalization.SimplyTypedLambdaCalculus
import Function
import Function.DomainRaise
import Function.Domains
import Function.Domains.Proofs
import Function.Equals
import Function.Equals.Proofs
import Function.Multi
import Function.Inverse
import Function.Inverseᵣ
-- import Function.Inverseₗ
import Function.Iteration
import Function.Iteration.Order
import Function.Iteration.Proofs
import Function.Multi
import Function.Names
import Function.Proofs
import Functional
import Graph
import Graph.Oper
import Graph.Properties
import Graph.Properties.Proofs
import Graph.Walk
import Graph.Walk.Functions
import Graph.Walk.Functions.Proofs
import Graph.Walk.Proofs
import Graph.Walk.Properties
import Lang.Inspect
import Lang.Instance
import Lang.Irrelevance
import Lang.Size
import Logic
import Logic.Classical
import Logic.Classical.DoubleNegated
import Logic.Computability
import Logic.Computability.Binary
import Logic.Names
import Logic.Predicate
import Logic.Predicate.Theorems
import Logic.Propositional
import Logic.Propositional.Theorems
import Lvl
import Numeral.CoordinateVector
import Numeral.CoordinateVector.Proofs
import Numeral.Finite
import Numeral.Finite.Bound
import Numeral.Finite.Functions
import Numeral.Finite.Oper
import Numeral.Finite.Oper.Comparisons
import Numeral.Finite.Oper.Comparisons.Proofs
import Numeral.Finite.Proofs
import Numeral.Finite.Sequence
import Numeral.Integer
-- import Numeral.Integer.Function
-- import Numeral.Integer.Oper
-- import Numeral.Integer.Proofs
-- import Numeral.Integer.Relation
-- import Numeral.Integer.Sign
import Numeral.Matrix
import Numeral.Natural
-- import Numeral.Natural.Coprime
import Numeral.Natural.Combinatorics
import Numeral.Natural.Combinatorics.Proofs
import Numeral.Natural.Function
import Numeral.Natural.Function.Proofs
import Numeral.Natural.GreatestCommonDivisor
import Numeral.Natural.Induction
import Numeral.Natural.Inductions
-- import Numeral.Natural.LinearSearchDecidable
import Numeral.Natural.Oper
import Numeral.Natural.Oper.Comparisons
import Numeral.Natural.Oper.Comparisons.Proofs
import Numeral.Natural.Oper.DivMod.Proofs
import Numeral.Natural.Oper.Divisibility
import Numeral.Natural.Oper.FlooredDivision
import Numeral.Natural.Oper.Modulo
import Numeral.Natural.Oper.Modulo.Proofs
import Numeral.Natural.Oper.Proofs
-- import Numeral.Natural.Prime
import Numeral.Natural.Relation
import Numeral.Natural.Relation.Computability
import Numeral.Natural.Relation.Divisibility
import Numeral.Natural.Relation.Divisibility.Proofs
import Numeral.Natural.Relation.Order
import Numeral.Natural.Relation.Order.Classical
import Numeral.Natural.Relation.Order.Computability
import Numeral.Natural.Relation.Order.Existence
import Numeral.Natural.Relation.Order.Existence.Proofs
import Numeral.Natural.Relation.Order.Proofs
import Numeral.Natural.Relation.Properties
-- import Numeral.Natural.Sequence
import Numeral.Natural.TotalOper
import Numeral.Natural.UnclosedOper
-- import Numeral.Rational.AlterAdd
-- import Numeral.Rational.SternBrocot
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Sign.Oper0
import Operator.Equals
import ReductionSystem
import Relator.Congruence
import Relator.Congruence.Proofs
import Relator.Converse
import Relator.Equals
import Relator.Equals.Heterogenous
import Relator.Equals.Names
import Relator.Equals.Proofs
import Relator.Equals.Proofs.Equivalence
import Relator.Ordering
import Relator.Ordering.Proofs
import Relator.ReflexiveTransitiveClosure
import Sets.BoolSet
import Sets.IterativeSet
import Sets.PredicateSet
import Sets.Setoid
import Sets.Setoid.Names
import Sets.Setoid.Proofs
import Sets.Setoid.Size
import Sets.Setoid.Size.Proofs
import Sets.Setoid.Uniqueness
import Sets.Setoid.Uniqueness.Proofs
import Stream
import String
import Structure.Arithmetic
import Structure.Category
import Structure.Category.Categories
-- import Structure.Category.Category
import Structure.Category.Dual
-- import Structure.Category.Equiv
import Structure.Category.Functor
-- import Structure.Category.Functor.Category
import Structure.Category.Functor.Equiv
import Structure.Category.Functor.Functors
import Structure.Category.Functor.Proofs
import Structure.Category.Monad
-- import Structure.Category.Monad.Category
import Structure.Category.Monad.ExtensionSystem
import Structure.Category.Names
import Structure.Category.NaturalTransformation
import Structure.Category.NaturalTransformation.NaturalTransformations
import Structure.Category.Proofs
import Structure.Category.Properties
import Structure.Category.Semicategory
import Structure.Function.Domain
import Structure.Function.Domain.Proofs
import Structure.Function.Linear
-- import Structure.Function.Metric
import Structure.Function.Ordering
-- import Structure.LinearAlgebra
import Structure.Operator.Field
import Structure.Operator.Functions
import Structure.Operator.Group
import Structure.Operator.Group.Proofs
import Structure.Operator.Lattice
import Structure.Operator.Monoid
import Structure.Operator.Monoid.Category
import Structure.Operator.Monoid.Proofs
import Structure.Operator.Names
import Structure.Operator.Proofs
import Structure.Operator.Properties
import Structure.Operator.SetAlgebra
import Structure.Operator.Vector
import Structure.Operator.Vector.Proofs
import Structure.OrderedField
import Structure.Real
import Structure.Real.Abs
-- import Structure.Real.Continuity
-- import Structure.Real.Derivative
-- import Structure.Real.Limit
import Structure.Relator.Equivalence
import Structure.Relator.Function
import Structure.Relator.Names
import Structure.Relator.Ordering
import Structure.Relator.Ordering.Lattice
import Structure.Relator.Ordering.Proofs
import Structure.Relator.Properties
import Structure.Relator.Properties.Proofs
import Structure.Type.Quotient
import Syntax.Function
import Syntax.Number
import Syntax.Transitivity
import Type
-- import Type.Category
-- import Type.Cubical
-- import Type.Cubical.Equality
-- import Type.Cubical.Path
-- import Type.Cubical.Path.Proofs
import Type.Dependent
import Type.Dependent.Functions
import Type.Empty
import Type.Empty.Proofs
import Type.Homotopy
import Type.Singleton
import Type.Singleton.Proofs
import Type.Size
import Type.Size.Countable
import Type.Size.Finite
import Type.Size.Proofs
import Type.Unit
import Type.Unit.Proofs
import Type.WellOrdering

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")

module _ where
  open Syntax.Function
  open Type

  test : Set → Set → Set
  test = (x ↦ y ↦ x :of: Set :of: Set)
