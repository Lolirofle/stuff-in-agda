module Main where

import Automaton.DeterministicFinite
import Automaton.NonDeterministicFinite
import Automaton.Pushdown
import Automaton.TuringMachine
import Cardinal
import Cardinal.Finite.Count
import Cardinal.Proofs
import Data
import Data.Any
import Data.Boolean
import Data.Boolean.Stmt
import Data.Boolean.Operators
import Data.Boolean.Proofs
import Data.Either
import Data.List
import Data.List.Computability
import Data.List.Proofs
import Data.List.Relation.Membership.Proofs
import Data.List.Relation.Sublist.Proofs
import Data.List.Relation
import Data.List.Relation.Membership
import Data.List.Relation.Sublist
import Data.ListNonEmpty
import Data.Option
import Data.Proofs
import Data.Tuple
import Data.Tuple.Function
import Data.Tuple.List
import Data.Tuple.Proofs
import Data.Tuple.Raise
import Data.Tuple.Raiseᵣ
import Data.Tuple.Raiseₗ
import FFI.IO   as FFI
import FormalLanguage
import FormalLanguage.ContextFreeGrammar
import FormalLanguage.Proofs
import FormalLanguage.RegularExpression
import Functional
import Function.DomainRaise
import Function.Domains
import Function.Domains.Proofs
import Function.Equals
import Function.Names
import Function.PrimitiveRecursion
import Function.Proofs
import Function.Iteration
import Function.Iteration.Proofs
-- import Geometry.Test
-- import Geometry.Test2
import Geometry.Test3
import Graph
import Functional.Instance
import Lang.Irrelevance
import Logic.Classical
import Logic.Classical.DoubleNegated
import Logic.Classical.Mere
import Logic.Computability
import Logic.Computability.Binary
import Logic.Convenience
import Logic.DiagonalProof
import Logic.LambdaCalculus
import Logic.Predicate
import Logic.Predicate.Theorems
import Logic.Propositional
import Logic.Propositional.Names
import Logic.Propositional.Theorems
import Lvl
import Metalogic.Classical.Propositional.ProofSystem
import Metalogic.Classical.Propositional.Syntax
import Metalogic.Classical.Propositional.TruthSemanticsModel
import Metalogic.Constructive.NaturalDeduction.TreeModel
-- import Metalogic.Constructive.Provability
import Metalogic.Linear.SequentCalculus
import Metalogic.Linear.Syntax
import Numeral.CoordinateVector
import Numeral.FiniteInclusive
import Numeral.Finite
import Numeral.Finite.Bound
import Numeral.Finite.Functions
import Numeral.Finite.Oper
import Numeral.Finite.Oper.Comparisons
import Numeral.Finite.Proofs
import Numeral.Integer
import Numeral.Integer.Function
import Numeral.Integer.Oper
import Numeral.Integer.Proofs
import Numeral.Integer.Relation
import Numeral.Integer.Sign
import Numeral.Matrix
import Numeral.Natural
import Numeral.Natural.Coprime
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
import Numeral.Natural.Oper.Modulo.Proofs
import Numeral.Natural.Oper.Proofs
import Numeral.Natural.Order
import Numeral.Natural.Prime
import Numeral.Natural.Relation
import Numeral.Natural.Relation.Computability
import Numeral.Natural.Relation.Countable
import Numeral.Natural.Relation.Divisibility
import Numeral.Natural.Relation.Order
import Numeral.Natural.Relation.Order.Computability
import Numeral.Natural.Relation.Order.Existence
import Numeral.Natural.Relation.Order.Existence.Proofs
import Numeral.Natural.Relation.Order.Proofs
import Numeral.Natural.Relation.Properties
import Numeral.Natural.TotalOper
import Numeral.Natural.UnclosedOper
import Numeral.PositiveInteger
import Numeral.PositiveInteger.Oper
import Numeral.Rational.AlterAdd
-- import Numeral.Rational.SternBrocot
import Numeral.Real
import Numeral.Real.Properties
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Charge.Oper
import Operator.Equals
import Relator.Bijection
import Relator.Congruence
import Relator.Congruence.Proofs
import Relator.Countable
import Relator.Equals
import Relator.Equals.Proofs
import Relator.Equals.Proofs.Uniqueness
import Structure.Setoid.Uniqueness
import Relator.Finite
import Sets.BoolSet
import Sets.BoolSet.Proofs
import Sets.ETCS
import Sets.IZF
import Sets.PredicateSet
import Sets.PredicateSet.Filter
import Sets.PredicateSet.Finite
import Sets.PredicateSet.Proofs
import Sets.PredicateSet.Relations
import Structure.Setoid
import Structure.Setoid.Proofs
import Stream
import String
import Structure.Arithmetic
-- import Structure.Category
import Structure.Function.Domain
import Structure.Function.Linear
import Structure.Function.Ordering
import Structure.LinearAlgebra
import Structure.Logic.Classical.PredicateBoundedQuantification
import Structure.Logic.Classical.NaturalDeduction
import Structure.Logic.Classical.NaturalDeduction.Proofs
import Structure.Logic.Classical.SetTheory
import Structure.Logic.Classical.SetTheory.SetBoundedQuantification
import Structure.Logic.Classical.SetTheory.Function
import Structure.Logic.Classical.SetTheory.Relation
import Structure.Logic.Classical.SetTheory.ZFC
import Structure.Logic.Classical.SetTheory.ZFC.BinaryRelatorSet
-- import Structure.Logic.Classical.SetTheory.ZFC.Finite
import Structure.Logic.Classical.SetTheory.ZFC.FunctionSet
import Structure.Logic.Classical.SetTheory.ZFC.Proofs
import Structure.Logic.Constructive.Functions.Properties
import Structure.Logic.Constructive.NaturalDeduction
import Structure.Operator.Field
import Structure.Operator.Functions
import Structure.Operator.Group
import Structure.Operator.Group.Proofs
import Structure.Operator.Monoid
import Structure.Operator.Proofs
import Structure.Operator.Properties
import Structure.Operator.SetAlgebra
import Structure.Operator.Vector
import Structure.Real
import Structure.Relator.Equivalence as Eq
import Structure.Relator.Function
import Structure.Relator.Ordering
import Structure.Relator.Ordering.Subsets
import Structure.Relator.Properties
import Structure.Relator.Properties.Proofs
import Syntax.Function
import Syntax.Method
import Syntax.Number
import Type
import Type.Cardinality
import Type.Cardinality.Proofs
import Type.Dependent.Sigma
import Type.Properties.Empty
import Type.Properties.Empty.Proofs
import Type.Functions
import Type.Functions.Inverse
import Type.Functions.Inverse.Proofs
import Type.Functions.Proofs
import Type.Singleton
import Type.Singleton.Proofs
import Type.Properties.Singleton
import Type.Properties.Singleton.Proofs
import Type.Univalence

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")
