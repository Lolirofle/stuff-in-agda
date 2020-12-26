module Function.PointwiseStructure where

open import Functional using (_∘_) renaming (const to const₁)
open import Function.Equals
open import Function.Multi.Functions
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Operator
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₑ ℓₗ ℓₗₑ : Lvl.Level
private variable I S T : Type{ℓ}
private variable _+_ _⋅_ : S → S → S

-- TODO: Possible to generalize to functions with multiple arguments
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ _▫₁_ _▫₂_ : T → T → T
  private variable f inv : T → T
  private variable id : T

  -- A component-wise function is a function when its underlying function is a function.
  pointwiseFunction-function : ⦃ oper : Function(f) ⦄ → Function(pointwise(1)(1) {As = I} (f))
  Function.congruence (pointwiseFunction-function {f = f}) (intro p) = intro(congruence₁(f) p)

  -- A component-wise binary operator is a binary operator when its underlying binary operator is a binary operator.
  pointwiseFunction-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(pointwise(1)(2) {As = I} (_▫_))
  BinaryOperator.congruence (pointwiseFunction-binaryOperator {_▫_ = _▫_}) (intro p) (intro q) = intro(congruence₂(_▫_) p q)

  -- A component-wise operator is associative when its underlying operator is associative.
  pointwiseFunction-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(pointwise(1)(2) {As = I} (_▫_))
  pointwiseFunction-associativity {_▫_ = _▫_} = intro(intro(associativity(_▫_)))

  -- A component-wise operator is commutative when its underlying operator is commutative.
  pointwiseFunction-commutativity : ⦃ comm : Commutativity(_▫_) ⦄ → Commutativity(pointwise(1)(2) {As = I} (_▫_))
  pointwiseFunction-commutativity {_▫_ = _▫_} = intro(intro(commutativity(_▫_)))

  -- A component-wise operator have a left identity of repeated elements when its underlying operator have a left identity.
  pointwiseFunction-identityₗ : ⦃ identₗ : Identityₗ(_▫_)(id) ⦄ → Identityₗ(pointwise(1)(2) {As = I} (_▫_))(const₁ id)
  pointwiseFunction-identityₗ {_▫_ = _▫_} {id = id} = intro(intro(identityₗ(_▫_)(id)))

  -- A component-wise operator have a right identity of repeated elements when its underlying operator have a right identity.
  pointwiseFunction-identityᵣ : ⦃ identᵣ : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(pointwise(1)(2) {As = I} (_▫_))(const₁ id)
  pointwiseFunction-identityᵣ {_▫_ = _▫_} {id = id} = intro(intro(identityᵣ(_▫_)(id)))

  -- A component-wise operator have an identity of repeated elements when its underlying operator have an identity.
  pointwiseFunction-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(pointwise(1)(2) {As = I} (_▫_))(const₁ id)
  Identity.left  pointwiseFunction-identity = pointwiseFunction-identityₗ
  Identity.right pointwiseFunction-identity = pointwiseFunction-identityᵣ

  pointwiseFunction-inverseFunctionₗ : ⦃ identₗ : Identityₗ(_▫_)(id) ⦄  ⦃ inverₗ : InverseFunctionₗ(_▫_) ⦃ [∃]-intro(id) ⦄ (inv) ⦄ → InverseFunctionₗ(pointwise(1)(2) {As = I} (_▫_)) ⦃ [∃]-intro _ ⦃ pointwiseFunction-identityₗ ⦄ ⦄ (pointwise(1)(1) {As = I} inv)
  pointwiseFunction-inverseFunctionₗ {_▫_ = _▫_} {id = id} {inv = inv} = intro(intro(inverseFunctionₗ(_▫_) ⦃ [∃]-intro id ⦄ (inv)))

  pointwiseFunction-inverseFunctionᵣ : ⦃ identᵣ : Identityᵣ(_▫_)(id) ⦄  ⦃ inverᵣ : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro(id) ⦄ (inv) ⦄ → InverseFunctionᵣ(pointwise(1)(2) {As = I} (_▫_)) ⦃ [∃]-intro _ ⦃ pointwiseFunction-identityᵣ ⦄ ⦄ (pointwise(1)(1) {As = I} inv)
  pointwiseFunction-inverseFunctionᵣ {_▫_ = _▫_} {id = id} {inv = inv} = intro(intro(inverseFunctionᵣ(_▫_) ⦃ [∃]-intro id ⦄ (inv)))

  pointwiseFunction-inverseFunction : ⦃ ident : Identity(_▫_)(id) ⦄  ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro(id) ⦄ (inv) ⦄ → InverseFunction(pointwise(1)(2) {As = I} (_▫_)) ⦃ [∃]-intro _ ⦃ pointwiseFunction-identity ⦄ ⦄ (pointwise(1)(1) {As = I} inv)
  InverseFunction.left  pointwiseFunction-inverseFunction = pointwiseFunction-inverseFunctionₗ
  InverseFunction.right pointwiseFunction-inverseFunction = pointwiseFunction-inverseFunctionᵣ

  -- A component-wise operator is left distributive over another component-wise operator when their underlying operators distribute.
  pointwiseFunction-distributivityₗ : ⦃ distₗ : Distributivityₗ(_▫₁_)(_▫₂_) ⦄ → Distributivityₗ(pointwise(1)(2) {As = I} (_▫₁_))(pointwise(1)(2) {As = I} (_▫₂_))
  pointwiseFunction-distributivityₗ = intro(intro(distributivityₗ _ _))

  -- A component-wise operator is right distributive over another component-wise operator when their underlying operators distribute.
  pointwiseFunction-distributivityᵣ : ⦃ distᵣ : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ → Distributivityᵣ(pointwise(1)(2) {As = I} (_▫₁_))(pointwise(1)(2) {As = I} (_▫₂_))
  pointwiseFunction-distributivityᵣ = intro(intro(distributivityᵣ _ _))

  pointwiseFunction-const-preserves : Preserving₂(const₁) (_▫_) (pointwise(1)(2) {As = I} (_▫_))
  pointwiseFunction-const-preserves = intro(intro(reflexivity(_≡_)))

  -- A component-wise operator is a monoid when its underlying operator is a monoid.
  pointwiseFunction-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(pointwise(1)(2) {As = I} (_▫_))
  Monoid.binary-operator    pointwiseFunction-monoid = pointwiseFunction-binaryOperator
  Monoid.associativity      pointwiseFunction-monoid = pointwiseFunction-associativity
  Monoid.identity-existence pointwiseFunction-monoid = [∃]-intro _ ⦃ pointwiseFunction-identity ⦄

  -- A component-wise operator is a group when its underlying operator is a group.
  pointwiseFunction-group : ⦃ group : Group(_▫_) ⦄ → Group(pointwise(1)(2) {As = I} (_▫_))
  Group.monoid            pointwiseFunction-group = pointwiseFunction-monoid
  Group.inverse-existence pointwiseFunction-group = [∃]-intro _ ⦃ pointwiseFunction-inverseFunction ⦄
  Group.inv-function      pointwiseFunction-group = pointwiseFunction-function

  -- A component-wise operator is a commutative group when its underlying operator is a commutative group.
  pointwiseFunction-commutativeGroup : ⦃ commutativeGroup : CommutativeGroup(_▫_) ⦄ → CommutativeGroup(pointwise(1)(2) {As = I} (_▫_))
  CommutativeGroup.group         pointwiseFunction-commutativeGroup = pointwiseFunction-group
  CommutativeGroup.commutativity pointwiseFunction-commutativeGroup = pointwiseFunction-commutativity

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  (field-structure : Field{T = S}(_+_)(_⋅_))
  where
  open Field(field-structure)

  -- Component-wise operators constructs a vector space from a field when using the fields as scalars and coordinate vectors as vectors.
  pointwiseFunction-vectorSpace : VectorSpace(pointwise(1)(2) {As = I} (_+_))(pointwise(1)(1) ∘ (_⋅_))(_+_)(_⋅_)
  VectorSpace.scalarField pointwiseFunction-vectorSpace = field-structure
  VectorSpace.vectorCommutativeGroup pointwiseFunction-vectorSpace = pointwiseFunction-commutativeGroup
  _⊜_.proof (BinaryOperator.congruence (VectorSpace.[⋅ₛᵥ]-binaryOperator pointwiseFunction-vectorSpace) p (intro q)) = congruence₂(_⋅_) p q
  _⊜_.proof (VectorSpace.[⋅ₛ][⋅ₛᵥ]-compatibility pointwiseFunction-vectorSpace) = associativity(_⋅_)
  _⊜_.proof (Identityₗ.proof (VectorSpace.[⋅ₛᵥ]-identity pointwiseFunction-vectorSpace)) = identityₗ(_⋅_)(𝟏)
  _⊜_.proof (Distributivityₗ.proof (VectorSpace.[⋅ₛᵥ][+ᵥ]-distributivityₗ pointwiseFunction-vectorSpace)) = distributivityₗ(_⋅_)(_+_)
  _⊜_.proof (VectorSpace.[⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ pointwiseFunction-vectorSpace) = distributivityᵣ(_⋅_)(_+_)
