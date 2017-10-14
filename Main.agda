module Main where

import Automaton.DeterministicFinite
import Automaton.NonDeterministicFinite
import Automaton.Pushdown
import Automaton.TuringMachine
import Boolean
import Boolean.Theorems
import Boolean.Operators
import Data
import Data.Tuple.List
import FFI.IO   as FFI
import FFI.Type as FFI
import FormalLanguage
import FormalLanguage.ContextFreeGrammar
import FormalLanguage.Properties
import FormalLanguage.RegularExpression
import Functional
import Functional.Equals
import Functional.Raise
import Functional.PrimitiveRecursion
import Functional.Properties
import Lvl
import List
import List.Properties
import List.Relation
import List.Theorems
import Logic.Classic.Propositional.ProofSystem
import Logic.Classic.Propositional.Semantics
import Logic.Classic.Propositional.Syntax
import Logic.Convenience
import Logic.DiagonalProof
import Logic.LambdaCalculus
import Logic.Propositional
import Logic.Predicate
import Logic.Theorems
import Graph
import Numeral.Integer
import Numeral.Integer.Oper
import Numeral.Integer.Relation
import Numeral.Integer.Sign
import Numeral.Integer.Theorems
import Numeral.Natural
import Numeral.Natural.Finite
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
import Numeral.Real
import Numeral.Real.Properties
import Numeral.Real.Theory
import Numeral.Sign
import Numeral.Sign.Oper
import Numeral.Sign.Oper0
import Operator.Equals
import Relator.Bijection
import Relator.Congruence
import Relator.Equals
import Sets.AdditiveSet
import Sets.BoolSet
import Sets.FnSet
import Sets.IZF
import Sets.ListSet
import Sets.TypeSet
import Structure.Function.Domain
import Structure.Function.Linear
import Structure.Function.Ordering
import Structure.Operator.Field
import Structure.Operator.Group
import Structure.Operator.Properties
import Structure.Operator.SetAlgebra
import Structure.Operator.Vector
import Structure.Relator.Equivalence as Eq
import Structure.Relator.Ordering
import Structure.Relator.Properties
import String
import Type

main : FFI.IO FFI.Unit
main = FFI.printStrLn "Okay"
