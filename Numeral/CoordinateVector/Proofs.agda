module Numeral.CoordinateVector.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
import      Data.Either as Either
import      Functional as Fn
open import Function.Equals
open import Function.Names
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.CoordinateVector
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Proofs
open import Numeral.Natural
import      Relator.Equals as Eq
open import Relator.Equals.Proofs.Equivalence
open import Structure.Setoid.WithLvl
open import Structure.Function.Multi
open import Structure.Function
open import Structure.Operator.Field
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Operator
open import Structure.Relator.Properties
open import Type
open import Syntax.Function

module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ _▫₁_ _▫₂_ _+_ _⋅_ : T → T → T
  private variable f inv : T → T
  private variable id : T
  private variable n : ℕ
  private variable i j k : 𝕟(n)

  instance
    -- A component-wise operator have a left identity of repeated elements when its underlying operator have a left identity.
    map₂-fill-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityₗ = intro(intro(identityₗ _ _))

  instance
    -- A component-wise operator have a right identity of repeated elements when its underlying operator have a right identity.
    map₂-fill-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityᵣ = intro(intro(identityᵣ _ _))

  instance
    -- A component-wise operator have an identity of repeated elements when its underlying operator have an identity.
    map₂-fill-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identity = intro ⦃ _ ⦄ ⦃ map₂-fill-identityₗ ⦄ ⦃ map₂-fill-identityᵣ ⦄

  instance
    map₂-map-inverseₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionₗ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseₗ = intro(intro(inverseFunctionₗ _ ⦃ [∃]-intro _ ⦄ _))

  instance
    map₂-map-inverseᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionᵣ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseᵣ = intro(intro(inverseFunctionᵣ _ ⦃ [∃]-intro _ ⦄ _))

  instance
    map₂-map-inverse : ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunction(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverse = intro ⦃ _ ⦄ ⦃ _ ⦄ ⦃ map₂-map-inverseₗ ⦄ ⦃ map₂-map-inverseᵣ ⦄

  instance
    -- A component-wise operator is commutative when its underlying operator is commutative.
    map₂-commutativity : ⦃ comm : Commutativity(_▫_) ⦄ → Commutativity(map₂{d = n}(_▫_))
    map₂-commutativity = intro(intro(commutativity _))

  instance
    -- A component-wise operator is associative when its underlying operator is associative.
    map₂-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(map₂{d = n}(_▫_))
    map₂-associativity = intro(intro(associativity _))

  instance
    -- A component-wise operator is left distributive over another component-wise operator when their underlying operators distribute.
    map₂-distributivityₗ : ⦃ distₗ : Distributivityₗ(_▫₁_)(_▫₂_) ⦄ → Distributivityₗ(map₂{d = n}(_▫₁_))(map₂{d = n}(_▫₂_))
    map₂-distributivityₗ ⦃ distₗ = distₗ ⦄ = intro(intro(distributivityₗ _ _))

  instance
    -- A component-wise operator is right distributive over another component-wise operator when their underlying operators distribute.
    map₂-distributivityᵣ : ⦃ distᵣ : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ → Distributivityᵣ(map₂{d = n}(_▫₁_))(map₂{d = n}(_▫₂_))
    map₂-distributivityᵣ ⦃ distᵣ = distᵣ ⦄ = intro(intro(distributivityᵣ _ _))

  instance
    map₂-preserves : Preserving₂(fill) (_▫_) (map₂{d = n}(_▫_))
    map₂-preserves = intro(intro(reflexivity(_≡_)))

  instance
    -- A component-wise function is a function when its underlying function is a function.
    map-function : ⦃ func : Function(f) ⦄ → Function(map{d = n}(f))
    Function.congruence map-function (intro p) = intro (congruence₁ _ p)

  instance
    -- A component-wise binary operator is a binary operator when its underlying binary operator is a binary operator.
    map₂-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(map₂{d = n}(_▫_))
    BinaryOperator.congruence map₂-binaryOperator (intro p) (intro q) = intro (congruence₂ _ p q)

  instance
    -- A component-wise operator is a monoid when its underlying operator is a monoid.
    map₂-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(map₂{d = n}(_▫_))
    Monoid.identity-existence map₂-monoid = [∃]-intro _

  instance
    -- A component-wise operator is a group when its underlying operator is a group.
    map₂-group : ⦃ group : Group(_▫_) ⦄ → Group(map₂{d = n}(_▫_))
    Group.monoid            map₂-group = map₂-monoid
    Group.inverse-existence map₂-group = [∃]-intro _

  instance
    -- A component-wise operator is a commutative group when its underlying operator is a commutative group.
    map₂-commutativeGroup : ⦃ commutativeGroup : CommutativeGroup(_▫_) ⦄ → CommutativeGroup(map₂{d = n}(_▫_))
    map₂-commutativeGroup = intro

  {-instance
    -- Note: The reason for `d = 𝐒(n)` is so that one cannot shrink a field to the "trivial field" in this way (which is not a field).
    map₂-field : ⦃ field-structure : Field(_+_)(_⋅_) ⦄ → Field(map₂{d = 𝐒(n)}(_+_))(map₂{d = 𝐒(n)}(_⋅_))
    Field.[+]-commutative-group map₂-field = map₂-commutativeGroup
    Field.[⋅]-monoid map₂-field = map₂-monoid
    Field.⅟ (map₂-field ⦃ f ⦄) v ⦃ Field.intro nonzero ⦄ = {!!} -- map (x ↦ Field.⅟ f x ⦃ Field.intro (p ↦ nonzero (intro {!!})) ⦄) v
    Field.[⋅]-inverseₗ map₂-field = {!!}
    Field.[⋅]-inverseᵣ map₂-field = {!!}
    Field.distinct-identities (map₂-field ⦃ f ⦄) p = Field.distinct-identities f (_⊜_.proof p {𝟎})
  -}

  instance
    -- Component-wise operators constructs a vector space from a field when using the fields as scalars and coordinate vectors as vectors.
    CoordinateVector-vectorSpace : ⦃ field-structure : Field(_+_)(_⋅_) ⦄ → VectorSpace(map₂{d = n}(_+_)) (s ↦ map{d = n}(s ⋅_)) (_+_) (_⋅_)
    VectorSpace.scalarField           (CoordinateVector-vectorSpace ⦃ f ⦄) = f
    VectorSpace.vectorCommutativeGroup CoordinateVector-vectorSpace = map₂-commutativeGroup
    BinaryOperator.congruence (VectorSpace.[⋅ₛᵥ]-binaryOperator  CoordinateVector-vectorSpace) p (intro q) = intro (congruence₂ _ p q)
    VectorSpace.[⋅ₛ][⋅ₛᵥ]-compatibility       CoordinateVector-vectorSpace = intro (associativity _)
    VectorSpace.[⋅ₛᵥ]-identity                CoordinateVector-vectorSpace = intro(intro (identityₗ _ _))
    VectorSpace.[⋅ₛᵥ][+ᵥ]-distributivityₗ     CoordinateVector-vectorSpace = intro(intro (distributivityₗ _ _))
    VectorSpace.[⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ CoordinateVector-vectorSpace = intro (distributivityᵣ _ _)

  indexProject-values : ∀{true false : T} → (proj(indexProject i true false) j ≡ true) ∨ (proj(indexProject i true false) j ≡ false)
  indexProject-values {𝐒 n}{i = i}{j = j} with (i ≡? j)
  ... | 𝑇 = [∨]-introₗ (reflexivity(_≡_))
  ... | 𝐹 = [∨]-introᵣ (reflexivity(_≡_))

  indexProject-true  : ∀{true false : T} → (i Eq.≡ j) ∨ (false ≡ true) ↔ (proj(indexProject i true false) j ≡ true)
  indexProject-true {n}{i = i}{j = j} {true = true}{false = false} =
    [∨]-mapₗ-[↔] [≡][≡?]-equivalence ⦗ [↔]-transitivity ⦘ᵣ
    [↔]-intro
      (l{n}{i}{j})
      ([↔]-to-[←] [→ₗ][∨][∧]-preserving ([∧]-intro (r₁{n}{i}{j}) (r₂{n}{i}{j})))
    where
      l : ∀{n}{i j : 𝕟(n)} → IsTrue(i ≡? j) ∨ (false ≡ true) ← (proj(indexProject i true false) j ≡ true)
      l {𝐒 n} {i = i} {j = j} p with (i ≡? j)
      ... | 𝑇 = [∨]-introₗ [⊤]-intro
      ... | 𝐹 = [∨]-introᵣ p

      r₁ : ∀{n}{i j : 𝕟(n)} → IsTrue(i ≡? j) → (proj(indexProject i true false) j ≡ true)
      r₁ {𝐒 n} {i = i}{j = j} p with 𝑇 ← (i ≡? j) = reflexivity(_≡_)

      r₂ : ∀{n}{i j : 𝕟(n)} → (false ≡ true) → (proj(indexProject i true false) j ≡ true)
      r₂ {𝐒 n} {i = i}{j = j} p with (i ≡? j)
      ... | 𝑇 = reflexivity(_≡_)
      ... | 𝐹 = p

  indexProject-false : ∀{true false : T} → ((i Eq.≢ j) ∨ (false ≡ true)) ↔ (proj(indexProject i true false) j ≡ false)
  indexProject-false {n}{i = i}{j = j} {true = true}{false = false} =
    [∨]-mapₗ-[↔] ([↔]-transitivity ([¬]-unaryOperator [≡][≡?]-equivalence) ([↔]-symmetry false-true-opposites)) ⦗ [↔]-transitivity ⦘ᵣ
    [↔]-intro
      (l{n}{i}{j})
      ([↔]-to-[←] [→ₗ][∨][∧]-preserving ([∧]-intro (r₁{n}{i}{j}) (r₂{n}{i}{j})))
    where
      l : ∀{n}{i j : 𝕟(n)} → (IsFalse(i ≡? j) ∨ (false ≡ true)) ← (proj(indexProject i true false) j ≡ false)
      l {n} {i} {j} p with (i ≡? j)
      ... | 𝑇 = [∨]-introᵣ (symmetry(_≡_) p)
      ... | 𝐹 = [∨]-introₗ [⊤]-intro

      r₁ : ∀{n}{i j : 𝕟(n)} → IsFalse(i ≡? j) → (proj(indexProject i true false) j ≡ false)
      r₁ {𝐒 n} {i = i}{j = j} p with (i ≡? j)
      ... | 𝑇 = [⊥]-elim p
      ... | 𝐹 = reflexivity(_≡_)

      r₂ : ∀{n}{i j : 𝕟(n)} → (false ≡ true) → (proj(indexProject i true false) j ≡ false)
      r₂ {𝐒 n} {i = i}{j = j} p with (i ≡? j)
      ... | 𝑇 = symmetry(_≡_) p
      ... | 𝐹 = reflexivity(_≡_)
