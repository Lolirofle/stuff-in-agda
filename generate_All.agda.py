#!/usr/bin/python3

import os
import os.path

skip_dirs = {
	'./gen',
	'./old',
	'./Miscellaneous',
}
skip_modules = {
	'All',
	'Automaton.Deterministic.FormalLanguage',
	'Automaton.NonDeterministic',
	'Automaton.Pushdown',
	'Automaton.TuringMachine',
	'FormalLanguage',
	'FormalLanguage.ContextFreeGrammar',
	'FormalLanguage.Equals',
	'FormalLanguage.Proofs',
	'FormalLanguage.RegularExpression',
	'Formalization.ClassicalPropositionalLogic',
	'Formalization.FunctionalML',
	'Formalization.PureTypeSystem',
	'Geometry.Axioms',
	'Geometry.HilbertAxioms',
	'Logic.Decidable',
	'Numeral.Integer.Relation',
	'Numeral.Matrix.OverField',
	'Numeral.Matrix.Relations',
	'Numeral.Natural.LinearSearchDecidable',
	'Numeral.Natural.Oper.Proofs.Elemantary',
	'Numeral.Natural.Oper.Proofs.Iteration',
	'Numeral.Natural.Oper.Proofs.Structure',
	'Numeral.Rational.AlterAdd',
	'Numeral.Rational.SternBrocot',
	'Sets.ExtensionalPredicateSet.SetLike',
	'Sets.ImageSet.SetLike',
	'Structure.Categorical.Multi',
	'Structure.Category.Equiv',
	'Structure.Category.Monoidal',
	'Structure.Container.List',
	'Structure.Container.ListLike',
	'Structure.Container.SetLike',
	'Structure.Container.SetLike.Proofs',
	'Structure.Function.Metric',
	'Structure.Numeral.Integer.Proofs',
	'Structure.Operator.Iteration',
	'Structure.Operator.Vector.Equiv',
	'Structure.Operator.Vector.FiniteDimensional.Proofs',
	'Structure.Operator.Vector.LinearCombination.Proofs',
	'Structure.Operator.Vector.LinearMap.Category',
	'Structure.Operator.Vector.LinearMap.Equiv',
	'Structure.Operator.Vector.Subspace',
	'Structure.Operator.Vector.Subspace.Proofs',
	'Structure.Operator.Vector.Subspaces.DirectSum',
	'Structure.Operator.Vector.Subspaces.Image',
	'Structure.Operator.Vector.Subspaces.Kernel',
	'Structure.Operator.Vector.Subspaces.Span',
	'Structure.Real.Continuity',
	'Structure.Real.Derivative',
	'Structure.Real.Limit',
	'Structure.Topology.Proofs',
	'Structure.Topology.Properties',
	'Structure.Type.Identity.Proofs.Multi',
	'Type.Category.IntensionalFunctionsCategory.HomFunctor',
	'Type.Properties.Homotopy.Proofs',
}

print('{-# OPTIONS --sized-types --guardedness --cubical #-}')
print('')
print('-- Note: This module is not meant to be imported.')
print('module All where')
print('')

"""
for (root_path,subdirs,files) in os.walk('.'):
	root_path = root_path[2:]
	subdirs.sort()
	files.sort()
	path = root_path.split(os.path.sep)

	if root_path in skip_dirs:
		subdirs.clear()
		continue

	for file in files:
		(name,ext) = os.path.splitext(file)
		if (ext == '.agda'):
			module = '.'.join(path + [name])
			if module in skip_modules:
				print('-- ',end='')
			print('import',module)
"""

def without_singleton_false(l: list) -> list:
	try:
		[a] = l
		if not a:
			return []
	except ValueError:
		pass
	return l

def print_modules(root_path: str = '.') -> None:
	names = os.listdir(root_path)
	names.sort()
	for name in names:
		path = os.path.join(root_path,name)
		if os.path.isdir(path):
			if path not in skip_dirs:
				print_modules(path)
		elif os.path.isfile(path):
			(basename,ext) = os.path.splitext(name)
			if (ext == '.agda'):
				rootpath_list = without_singleton_false(root_path[2:].split(os.path.sep))
				module = '.'.join(rootpath_list + [basename])
				if module in skip_modules:
					print('-- ',end='')
				print('import',module)

print_modules()
