
  open import Structure.Setoid.Signature.IndexedCategory

  instance
    setoidFunctionSignature : FunctionSignature setoidFunction
    setoidFunctionSignature = HomFunctorEquivalence.functionSignature
      (intro(functor Tuple.right [∃]-witness) [∃]-witness)
      ⦃ \{_}{e} → [∃]-proof e ⦄

  instance
    setoidFunctionApplication : FunctionApplication setoidFunction
    setoidFunctionApplication = HomFunctorEquivalence.functionApplication _
