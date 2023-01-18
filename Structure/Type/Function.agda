module Structure.Type.Function where

open import BidirectionalFunction using (_↔_ ; intro)
open import Functional as Explicit using (_→ᶠ_ ; _←_)
open import Function.Signature.IndexedCategory
import      Lvl
open import Signature.IndexedCategory
open import Signature.IndexedCategory.Functor
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Setoid
open import Typeω.Dependent.Sigma
open import Type

private variable ℓ : Lvl.Level

-- Categorically, this is just a correct hom-functor.
record FunctionSignature(C : IndexedCategory) : Typeω where
  constructor intro
  open IndexedCategory(C)
  field signature : HomFunctor(C)
  open Functor(signature) using () public renaming (
    index to ℓₜ ;
    obj   to type)
  field
    {ℓₘ} : Index → Index → Lvl.Level
    ⦃ morphism-equiv ⦄ : IndexedCategory.MorphismEquiv C ℓₘ
    {ℓₑₜ} : Index → Lvl.Level
    ⦃ type-equiv ⦄ : ∀{i}{T : Obj(i)} → Equiv{ℓₑₜ(i)}(type(T))

-- FunctionApplication(C) means that the the morphisms in the indexed category C have a hom-functor that behaves like function application.
-- Categorically, this is just a functional hom-functor.
record FunctionApplication(C : IndexedCategory) ⦃ funcSig : FunctionSignature(C) ⦄ : Typeω where
  constructor intro
  open IndexedCategory(C)
  open FunctionSignature(funcSig)
  field _$_ : Functor.Map(signature)

  signatureFunctor : C →ᶠᵘⁿᶜᵗᵒʳ explicitFunction
  signatureFunctor = intro signature (_$_)

  field ⦃ apply-function ⦄ : ∀{i₁ i₂}{A : Obj(i₁)}{B : Obj(i₂)} → Function ⦃ morphism-equiv ⦄ ⦃ HomFunctor.Morphism-equiv idᶠᵘⁿᶜᵗᵒʳ ⦄ (_$_ {i₁}{i₂}{A}{B})

-- FunctionExtensionality(C) ⦃ funcApp ⦄ means that funcApp have the correct extensionality principle for functions.
-- Categorically, this is just an injective hom-functor.
record FunctionExtensionality(C : IndexedCategory) ⦃ funcSig : FunctionSignature(C) ⦄ ⦃ funcApp : FunctionApplication(C) ⦄ : Typeω where
  constructor intro
  open IndexedCategory(C)
  open FunctionSignature(funcSig)
  open FunctionApplication(funcApp)
  field ⦃ proof ⦄ : ∀{i₁ i₂}{A : Obj(i₁)}{B : Obj(i₂)} → Injective ⦃ morphism-equiv ⦄ ⦃ HomFunctor.Morphism-equiv idᶠᵘⁿᶜᵗᵒʳ ⦄ (_$_ {i₁}{i₂}{A}{B})

-- FunctionAbstraction(C) ⦃ funcApp ⦄ means that it is possible to contruct morphisms directly by function abstraction.
-- Categorically, this is just an invertible hom-functor.
record FunctionAbstraction(C : IndexedCategory) ⦃ funcSig : FunctionSignature(C) ⦄ ⦃ funcApp : FunctionApplication(C) ⦄ : Typeω where
  constructor intro
  open IndexedCategory(C)
  open FunctionSignature(funcSig)
  open FunctionApplication(funcApp)
  open Functor(signature)
  field
    abstr : ∀{i₁ i₂}{A : Obj₁(i₁)}{B : Obj₁(i₂)} → (A ⟶₁ B) ← (obj(A) ⟶₂ obj(B))
    ⦃ abstr-function ⦄ : ∀{i₁ i₂}{A : Obj(i₁)}{B : Obj(i₂)} → Function ⦃ HomFunctor.Morphism-equiv idᶠᵘⁿᶜᵗᵒʳ ⦄ ⦃ morphism-equiv ⦄ (abstr{i₁}{i₂}{A}{B})

  convert : ∀{i₁ i₂}{A : Obj₁(i₁)}{B : Obj₁(i₂)} → (A ⟶₁ B) ↔ (obj(A) ⟶₂ obj(B))
  convert = intro abstr (_$_)

  field ⦃ correctness ⦄ : ∀{i₁ i₂}{A : Obj₁(i₁)}{B : Obj₁(i₂)} → InversePair ⦃ morphism-equiv ⦄ ⦃ HomFunctor.Morphism-equiv idᶠᵘⁿᶜᵗᵒʳ ⦄(convert{i₁}{i₂}{A}{B})

open import Function.Signature.IndexedCategory

module HomFunctorEquivalence
  {C : IndexedCategory}
  (F@(intro obj map) : C →ᶠᵘⁿᶜᵗᵒʳ explicitFunction)
  {ℓ : IndexedCategory.Index C → Lvl.Level}
  ⦃ type-equiv : ∀{i}{T : IndexedCategory.Obj C(i)} → Equiv{ℓ(i)}(Functor.obj(obj) T) ⦄
  where

  functionSignature : FunctionSignature(C)
  functionSignature = intro obj ⦃ HomFunctor.Morphism-equiv F ⦄ ⦃ type-equiv ⦄

  functionApplication : FunctionApplication(C) ⦃ functionSignature ⦄
  functionApplication = intro map ⦃ intro Explicit.id ⦄
