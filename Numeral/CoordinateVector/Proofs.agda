module Numeral.CoordinateVector.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
import      Data.Either as Either
import      Functional as Fn
open import Function.Equals
open import Function.Names
open import Function.PointwiseStructure
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
open import Structure.Setoid
open import Structure.Function.Multi
import      Structure.Function.Names as Names
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
open import Syntax.Transitivity

-- Note: The structure stuff here is actually a specialization of Function.PointwiseStructure
module _ {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  private variable _▫_ _▫₁_ _▫₂_ _+_ _⋅_ : T → T → T
  private variable f inv : T → T
  private variable id 𝟎ₛ 𝟏ₛ x init : T
  private variable d n : ℕ
  private variable i j k : 𝕟(n)
  private variable v : Vector(n)(T)

  instance
    -- A component-wise operator have a left identity of repeated elements when its underlying operator have a left identity.
    map₂-fill-identityₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ → Identityₗ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityₗ = pointwiseFunction-identityₗ

  instance
    -- A component-wise operator have a right identity of repeated elements when its underlying operator have a right identity.
    map₂-fill-identityᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ → Identityᵣ(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identityᵣ = pointwiseFunction-identityᵣ

  instance
    -- A component-wise operator have an identity of repeated elements when its underlying operator have an identity.
    map₂-fill-identity : ⦃ ident : Identity(_▫_)(id) ⦄ → Identity(map₂{d = n}(_▫_))(fill{d = n}(id))
    map₂-fill-identity = pointwiseFunction-identity

  instance
    map₂-map-inverseₗ : ⦃ ident : Identityₗ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionₗ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionₗ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseₗ = pointwiseFunction-inverseFunctionₗ

  instance
    map₂-map-inverseᵣ : ⦃ ident : Identityᵣ(_▫_)(id) ⦄ ⦃ inver : InverseFunctionᵣ(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunctionᵣ(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverseᵣ = pointwiseFunction-inverseFunctionᵣ

  instance
    map₂-map-inverse : ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ inver : InverseFunction(_▫_) ⦃ [∃]-intro _ ⦄ (inv) ⦄ → InverseFunction(map₂{d = n}(_▫_)) ⦃ [∃]-intro _ ⦄ (map(inv))
    map₂-map-inverse = pointwiseFunction-inverseFunction

  instance
    -- A component-wise operator is commutative when its underlying operator is commutative.
    map₂-commutativity : ⦃ comm : Commutativity(_▫_) ⦄ → Commutativity(map₂{d = n}(_▫_))
    map₂-commutativity = pointwiseFunction-commutativity

  instance
    -- A component-wise operator is associative when its underlying operator is associative.
    map₂-associativity : ⦃ assoc : Associativity(_▫_) ⦄ → Associativity(map₂{d = n}(_▫_))
    map₂-associativity = pointwiseFunction-associativity

  instance
    -- A component-wise operator is left distributive over another component-wise operator when their underlying operators distribute.
    map₂-distributivityₗ : ⦃ distₗ : Distributivityₗ(_▫₁_)(_▫₂_) ⦄ → Distributivityₗ(map₂{d = n}(_▫₁_))(map₂{d = n}(_▫₂_))
    map₂-distributivityₗ = pointwiseFunction-distributivityₗ

  instance
    -- A component-wise operator is right distributive over another component-wise operator when their underlying operators distribute.
    map₂-distributivityᵣ : ⦃ distᵣ : Distributivityᵣ(_▫₁_)(_▫₂_) ⦄ → Distributivityᵣ(map₂{d = n}(_▫₁_))(map₂{d = n}(_▫₂_))
    map₂-distributivityᵣ = pointwiseFunction-distributivityᵣ

  instance
    map₂-preserves : Preserving₂(fill) (_▫_) (map₂{d = n}(_▫_))
    map₂-preserves = pointwiseFunction-const-preserves

  instance
    -- A component-wise function is a function when its underlying function is a function.
    map-function : ⦃ func : Function(f) ⦄ → Function(map{d = n}(f))
    map-function = pointwiseFunction-function

  instance
    -- A component-wise binary operator is a binary operator when its underlying binary operator is a binary operator.
    map₂-binaryOperator : ⦃ oper : BinaryOperator(_▫_) ⦄ → BinaryOperator(map₂{d = n}(_▫_))
    map₂-binaryOperator = pointwiseFunction-binaryOperator

  instance
    -- A component-wise operator is a monoid when its underlying operator is a monoid.
    map₂-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(map₂{d = n}(_▫_))
    map₂-monoid = pointwiseFunction-monoid

  instance
    -- A component-wise operator is a group when its underlying operator is a group.
    map₂-group : ⦃ group : Group(_▫_) ⦄ → Group(map₂{d = n}(_▫_))
    map₂-group = pointwiseFunction-group

  instance
    -- A component-wise operator is a commutative group when its underlying operator is a commutative group.
    map₂-commutativeGroup : ⦃ commutativeGroup : CommutativeGroup(_▫_) ⦄ → CommutativeGroup(map₂{d = n}(_▫_))
    map₂-commutativeGroup = pointwiseFunction-commutativeGroup

  {- TODO: Is this even possible?
  instance
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
    CoordinateVector-vectorSpace ⦃ field-structure ⦄ = pointwiseFunction-vectorSpace field-structure

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

  module _
    ⦃ ident : Identityₗ(_⋅_)(𝟏ₛ) ⦄
    ⦃ absor : Absorberₗ(_⋅_)(𝟎ₛ) ⦄
    where
    map₂-indexProject-identityₗ : map₂(_⋅_) (indexProject i 𝟏ₛ 𝟎ₛ) v ≡ indexProject i (v(i)) 𝟎ₛ
    _⊜_.proof (map₂-indexProject-identityₗ {i = i}{v = v}) {x} with (i ≡? x) | [↔]-to-[←] ([≡][≡?]-equivalence {i = i}{j = x})
    ... | 𝑇 | p = identityₗ(_⋅_)(𝟏ₛ) 🝖 congruence₁ ⦃ [≡]-equiv ⦄ (v) ⦃ [≡]-to-function ⦄ (symmetry(Eq._≡_) (p([⊤]-intro)))
    ... | 𝐹 | _ = absorberₗ(_⋅_)(𝟎ₛ)

  module _
    ⦃ ident : Identityᵣ(_⋅_)(𝟏ₛ) ⦄
    ⦃ absor : Absorberᵣ(_⋅_)(𝟎ₛ) ⦄
    where
    map₂-indexProject-identityᵣ : map₂(_⋅_) v (indexProject i 𝟏ₛ 𝟎ₛ) ≡ indexProject i (v(i)) 𝟎ₛ
    _⊜_.proof (map₂-indexProject-identityᵣ {v = v}{i = i}) {x} with (i ≡? x) | [↔]-to-[←] ([≡][≡?]-equivalence {i = i}{j = x})
    ... | 𝑇 | p = identityᵣ(_⋅_)(𝟏ₛ) 🝖 congruence₁ ⦃ [≡]-equiv ⦄ (v) ⦃ [≡]-to-function ⦄ (symmetry(Eq._≡_) (p([⊤]-intro)))
    ... | 𝐹 | _ = absorberᵣ(_⋅_)(𝟎ₛ)

  tail-function : Function(tail{d = 𝐒(d)}{T = T})
  Function.congruence(tail-function{d = d}) (intro xy) = intro xy

  instance
    foldᵣ-function : ∀{ℓᵣ ℓₑᵣ}{R : Type{ℓᵣ}} ⦃ equiv-R : Equiv{ℓₑᵣ}(R)⦄ {f : T → R → R}{init} → ⦃ oper : BinaryOperator(f) ⦄ → Function(foldᵣ{d = d} f init)
    foldᵣ-function {d} {f = f}{init = init} = intro(p{d = d}) where
      p : ∀{d} → Names.Congruence₁(foldᵣ{d = d} f init)
      p {𝟎}       _  = reflexivity(_≡_)
      p {𝐒(𝟎)}    xy = congruence₂ₗ(f)(_) (_⊜_.proof xy)
      p {𝐒(𝐒(d))} xy = congruence₂(f) (_⊜_.proof xy) (p {𝐒(d)} (congruence₁(tail) ⦃ tail-function ⦄ xy))

  -- TODO: Generalize Numeral.Natural.Oper.Summation for these kinds of proofs
  {-
  module _
    ⦃ oper : BinaryOperator(_▫_) ⦄
    ⦃ ident : Identityᵣ(_▫_)(id) ⦄
    ( neq : (id ≢ x) )
    where
    foldᵣ-indexProject-identityᵣ : foldᵣ(_▫_) init (indexProject i x id) ≡ x ▫ init
    foldᵣ-indexProject-identityᵣ {init}{𝐒(𝟎)}    {i = 𝟎}   = reflexivity(_≡_)
    foldᵣ-indexProject-identityᵣ {init}{𝐒(𝐒(n))} {i = 𝟎}   =
      foldᵣ{d = 𝐒(𝐒(n))}(_▫_) init (indexProject 𝟎 x id)                                                🝖[ _≡_ ]-[]
      proj(indexProject{d = 𝐒(𝐒(n))} 𝟎 x id)(𝟎) ▫ foldᵣ{d = 𝐒(n)}(_▫_) init (tail(indexProject 𝟎 x id)) 🝖[ _≡_ ]-[]
      x ▫ foldᵣ{d = 𝐒(n)}(_▫_) init (tail(indexProject 𝟎 x id))                                         🝖[ _≡_ ]-[ {!!} ]
      x ▫ init                                                                                          🝖-end
      {-foldᵣ(_▫_) id (indexProject 𝟎 x id)                                        🝖[ _≡_ ]-[ {!!} ]
      proj(indexProject 𝟎 x id)(𝟎) ▫ (foldᵣ(_▫_) id (tail(indexProject 𝟎 x id))) 🝖[ _≡_ ]-[ {!!} ]
      id ▫ (foldᵣ(_▫_) id (tail(indexProject 𝟎 x id)))                           🝖[ _≡_ ]-[ {!!} ]
      foldᵣ(_▫_) id (tail(indexProject 𝟎 x id))                                  🝖[ _≡_ ]-[ {!!} ]
      x                                                                          🝖-end-}
    foldᵣ-indexProject-identityᵣ {init}{𝐒(𝐒(n))} {i = 𝐒 i} = {!!}
  -}
