module Main where

import Automaton.DeterministicFinite
import Automaton.NonDeterministicFinite
import Automaton.Pushdown
import Automaton.TuringMachine
import Data.Boolean
import Data.Boolean.AsSet
import Data.Boolean.Theorems
import Data.Boolean.Operators
import Cardinal
import Data
import Data.Either
import Data.Option
import Data.Tuple
import Data.Tuple.List
import Data.Tuple.Raise
import Data.Tuple.Raiseₗ
import Data.Tuple.Raiseᵣ
import FFI.IO   as FFI
import FormalLanguage
import FormalLanguage.ContextFreeGrammar
import FormalLanguage.Properties
import FormalLanguage.RegularExpression
import Functional
import Functional.Domains
import Functional.Equals
import Functional.ComposeRaise
import Functional.PrimitiveRecursion
import Functional.Properties
import Functional.DomainRaise
import Lvl
import Data.List
import Data.List.Properties
import Data.List.Relation
import Data.List.Theorems
import Data.ListNonEmpty
import Logic.Classical.Mere
import Logic.Classical.NaturalDeduction
import Logic.Classical.DoubleNegated
import Logic.Classical.SetTheory.ZFC
import Logic.Constructive.NaturalDeduction
import Logic.Computability
import Logic.Convenience
import Logic.DiagonalProof
import Logic.LambdaCalculus
import Logic.Propositional
import Logic.Propositional.Theorems
import Logic.Predicate
import Logic.Predicate.Theorems
import Logic.Properties
-- import Geometry.Test
import Graph
import Metalogic.Classical.Propositional.ProofSystem
import Metalogic.Classical.Propositional.Semantics
import Metalogic.Classical.Propositional.Syntax
import Numeral.Integer
import Numeral.Integer.Function
import Numeral.Integer.Oper
import Numeral.Integer.Relation
import Numeral.Integer.Sign
import Numeral.Integer.Theorems
import Numeral.Natural
import Numeral.Natural.Coprime
import Numeral.Natural.Divisibility
import Numeral.Finite
import Numeral.FiniteStrict
import Numeral.FiniteStrict.BooleanOper
import Numeral.Natural.Function
import Numeral.Natural.BooleanOper
import Numeral.Natural.Oper
import Numeral.Natural.Oper.Properties
import Numeral.Natural.Prime
import Numeral.Natural.Proof
import Numeral.Natural.Relation
import Numeral.Natural.Relation.Countable
import Numeral.Natural.Relation.Properties
import Numeral.Natural.TotalOper
import Numeral.Natural.UnclosedOper
import Numeral.Matrix
import Numeral.Rational.AlterAdd
import Numeral.Real
import Numeral.Real.Properties
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Sign.Oper0
import Numeral.Vector
import Operator.Equals
import Relator.Bijection
import Relator.Congruence
import Relator.Countable
import Relator.Equals
import Relator.Equals.Theorems
import Relator.Equals.Uniqueness
import Relator.Finite
import Relator.FunctionEquals
import Sets.BoolSet
import Sets.ETCS
import Sets.IZF
import Sets.ListSet
import Sets.TypeSet
import Sets.PredicateSet
-- import Sets.PredicateSet.Finite
-- import Sets.PredicateSet.Properties
import Structure.Arithmetic
import Structure.Category
import Structure.Function
import Structure.Function.Domain
import Structure.Function.Linear
import Structure.Function.Ordering
import Structure.LinearAlgebra
import Structure.Operator.Field
import Structure.Operator.Group
import Structure.Operator.Monoid
import Structure.Operator.Properties
import Structure.Operator.SetAlgebra
import Structure.Operator.Vector
import Structure.Real
import Structure.Relator.Equivalence as Eq
import Structure.Relator.Ordering
import Structure.Relator.Ordering.Subsets
import Structure.Relator.Properties
import Stream
import String
import Syntax.Method
import Syntax.Number
import Type

main : FFI.IO Data.Unit
main = FFI.printStrLn("Okay")
