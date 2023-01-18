module Function.Structure where

open import Functional as Explicit using (_→ᶠ_ ; _←_)
open import Functional.Implicit as Implicit using (_﹛$﹜_)
open import Functional.Instance as Instance using (_⦃$⦄_)
open import Function.Signature.IndexedCategory
open import Relator.Equals.Proofs.Equiv
open import Signature.IndexedCategory.Functor
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Structure.Type.Function
open import Typeω.Dependent.Sigma

instance
  explicitFunctionSignature : FunctionSignature explicitFunction
  explicitFunctionSignature = HomFunctorEquivalence.functionSignature
    idᶠᵘⁿᶜᵗᵒʳ
    ⦃ [≡]-equiv ⦄

instance
  implicitFunctionSignature : FunctionSignature implicitFunction
  implicitFunctionSignature = HomFunctorEquivalence.functionSignature
    (intro(functor Explicit.id Explicit.id) (_﹛$﹜_))
    ⦃ [≡]-equiv ⦄

instance
  instanceFunctionSignature : FunctionSignature instanceFunction
  instanceFunctionSignature = HomFunctorEquivalence.functionSignature
    (intro(functor Explicit.id Explicit.id) (_⦃$⦄_))
    ⦃ [≡]-equiv ⦄

instance
  explicitFunctionApplication : FunctionApplication explicitFunction
  explicitFunctionApplication = HomFunctorEquivalence.functionApplication _

instance
  implicitFunctionApplication : FunctionApplication implicitFunction
  implicitFunctionApplication = HomFunctorEquivalence.functionApplication _

instance
  instanceFunctionApplication : FunctionApplication instanceFunction
  instanceFunctionApplication = HomFunctorEquivalence.functionApplication _

instance
  explicitFunctionAbstraction : FunctionAbstraction explicitFunction
  explicitFunctionAbstraction = intro
    Explicit.id
    ⦃ intro Explicit.id ⦄
    ⦃ intro ⦃ _ ⦄ ⦃ _ ⦄ ⦃ left = intro(\{f}{x} → reflexivity(_) {f(x)}) ⦄ ⦃ right = intro \{f}{x} → reflexivity(_) {f(x)} ⦄ ⦄

instance
  implicitFunctionAbstraction : FunctionAbstraction implicitFunction
  implicitFunctionAbstraction = intro
    Implicit.inferArg
    ⦃ intro Explicit.id ⦄
    ⦃ intro ⦃ _ ⦄ ⦃ _ ⦄ ⦃ left = intro(\{f}{x} → reflexivity(_) {f(x)}) ⦄ ⦃ right = intro \{f}{x} → reflexivity(_) {f{x}} ⦄ ⦄

instance
  instanceFunctionAbstraction : FunctionAbstraction instanceFunction
  instanceFunctionAbstraction = intro
    Instance.inferArg
    ⦃ intro Explicit.id ⦄
    ⦃ intro ⦃ _ ⦄ ⦃ _ ⦄ ⦃ left = intro(\{f}{x} → reflexivity(_) {f(x)}) ⦄ ⦃ right = intro \{f}{x} → reflexivity(_) {f ⦃ x ⦄} ⦄ ⦄
