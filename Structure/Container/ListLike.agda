module Structure.Container.ListLike where

{-open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Lang.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator hiding (module Names)
open import Type.Properties.Inhabited
-}

open import Data.Boolean.Stmt
open import Data.Option           as Option using (Option)
open import Data.Option.Equiv
open import Data.Option.Functions as Option
import      Lvl
open import Logic.Propositional
open import Logic
open import Numeral.Finite
import      Numeral.Finite.Bound as 𝕟-bound
import      Numeral.Finite.Oper as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Relation.Order
open import Relator.Equals renaming (_≡_ to _≡ₑ_ ; _≢_ to _≢ₑ_)
open import Relator.Equals.Proofs.Equivalence
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₑ ℓₑₑ ℓₑₐ : Lvl.Level
private variable A B : Type{ℓ}
private variable I : Type{ℓᵢ}
private variable C C₁ C₂ Cₒ Cᵢ : I → Type{ℓₗ}
-- private variable E E₁ E₂ : Type{ℓₑ}
private variable n : ℕ

module _ {I : Type{ℓᵢ}} (C : I → Type{ℓₗ}) where
  private variable i i₁ i₂ : I
  private variable l l₁ l₂ : C(i)
  -- private variable x : E

  record ListLike : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ Lvl.𝐒(ℓₑ)} where
    field
      E : Type{ℓₑ}
      length : C(i) → ℕ
      index : C(i) → ℕ → Option(E)
      --_∈_ : C(i₁) → C(i₂) → Stmt{ℓ₄}
      --_≡_ : C(i₁) → C(i₂) → Stmt{ℓ₅}
      --All : (E → Stmt) → C → Stmt{}
      --Any : (E → Stmt) → C → Stmt{}

    field
      index-correct : (n < length(l)) → IsTrue(Option.isSome(index l n))
      index-finite  : (n ≥ length(l)) → IsTrue(Option.isNone(index l n))

module _ {I : Type{ℓᵢ}} {C : I → Type{ℓₗ}} where
  private variable i i₁ i₂ : I

  module _ ⦃ listLike : ListLike(C){ℓₑ} ⦄ where
    open ListLike(listLike)

    module _ ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄ where
      record PrependFunction : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ ℓₑₑ} where
        field
          indexing : I → I
          prepend  : E → C(i) → C(indexing i)
        Size = ∀{i}{x}{l} → (length(prepend{i} x l) ≡ₑ 𝐒(length l))
        field size : Size
        Ordering =
          ∀{i}{x}{l}
          → (index(prepend{i} x l)(𝟎) ≡ₛ Option.Some(x))
          ∧ (∀{n} → (index(prepend{i} x l)(𝐒(n)) ≡ₛ index l n))
        field ordering : Ordering
      open PrependFunction ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Prepend ⦃ inst ⦄ = PrependFunction(inst)

      record PostpendFunction : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ ℓₑₑ} where
        field
          indexing : I → I
          postpend  : E → C(i) → C(indexing i)
        Size = ∀{i}{x}{l : C(i)} → (length(postpend x l) ≡ₑ 𝐒(length l))
        field size : Size
        OrderingBase = ∀{i}{x}{l} → (index(postpend{i} x l)(length l) ≡ₛ Option.Some(x))
        OrderingStep = ∀{i}{x}{l}{n} → (n < length(l)) → (index(postpend{i} x l)(n) ≡ₛ index l n)
        Ordering = OrderingBase ∧ OrderingStep
        field ordering : Ordering
      open PostpendFunction ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Postpend ⦃ inst ⦄ = PostpendFunction(inst)
{-
      record ConcatenationOperator : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ ℓₑₑ} where
        field
          indexing : I → I → I
          _++_  : C(i₁) → C(i₂) → C(indexing i₁ i₂)
        Size = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)} → (length(l₁ ++ l₂) ≡ₑ length(l₁) ℕ.+ length(l₂))
        field size : Size
        OrderingLeft  = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)}{n} → (index(l₁ ++ l₂)([≡]-substitutionₗ size {𝕟} (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ index l₁(n))
        OrderingRight = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)}{n} → (index(l₁ ++ l₂)([≡]-substitutionₗ size {𝕟} (𝕟.Optional.maximum{length l₁} 𝕟.+₀ₗ n)) ≡ₛ index l₂(n))
        Ordering = OrderingLeft ∧ OrderingRight
        field ordering : Ordering
      open ConcatenationOperator ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Concatenation ⦃ inst ⦄ = ConcatenationOperator(inst)
-}


open import Data
import      Data.Tuple as Tuple
open import Data.List as List
import      Data.List.Functions as List
open import Data.List.Proofs
open import Functional
open import Structure.Function.Multi
open import Structure.Relator.Properties
open import Syntax.Transitivity

instance
  List-listLike : ListLike{I = Unit{Lvl.𝟎}}(const(List(A)))
  ListLike.E      (List-listLike {A = A}) = A
  ListLike.length List-listLike = List.length
  ListLike.index List-listLike = swap List.index₀
  ListLike.index-correct List-listLike {n} {l = l} x with n | List.length l | l
  ... | 𝟎 | 𝟎 | x₁ ⊰ p = {!!}
  ... | 𝟎 | 𝐒 nn | x₁ ⊰ p = {!!}
  ... | 𝐒 ll | 𝟎 | x₁ ⊰ p = {!!}
  ... | 𝐒 ll | 𝐒 nn | x₁ ⊰ p = {!!}
  ListLike.index-finite List-listLike = {!!}
{-
instance
  List-prependFunction : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → PrependFunction ⦃ List-listLike{A = A} ⦄
  PrependFunction.indexing List-prependFunction _ = <>
  PrependFunction.prepend  List-prependFunction = _⊰_
  PrependFunction.size     List-prependFunction {x = x} {l = l} = preserving₁ ⦃ [≡]-equiv ⦄ (List.length)(x ⊰_)(𝐒) {l}
  Tuple.left  (PrependFunction.ordering List-prependFunction) = reflexivity(_≡ₛ_)
  Tuple.right (PrependFunction.ordering List-prependFunction) = reflexivity(_≡ₛ_)
-
length-[++]' : ∀{l₁ l₂} → (List.length{T = A}(l₁ List.++ l₂) ≡ₑ List.length(l₁) ℕ.+ List.length(l₂))
length-[++]' {l₁ = ∅}      {l₂} = [≡]-intro
length-[++]' {l₁ = x ⊰ l₁} {l₂} = [≡]-with(𝐒) (length-[++]' {l₁ = l₁}{l₂})

test0 : ∀{a b : ℕ}{ab : a ≡ₑ b}{P : ℕ → Stmt{Lvl.𝟎}}{pa : P(𝐒 a)} → ([≡]-substitutionᵣ ([≡]-with(𝐒) ab) {P} pa ≡ₑ {!!})

test : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ∀{l₁ l₂}{n} → List.index(l₁ List.++ l₂)([≡]-substitutionₗ (length-[++]' {l₁ = l₁}{l₂ = l₂}) {𝕟} (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ List.index l₁(n)
test {l₁ = x ⊰ l₁} {∅} {𝟎} = {!reflexivity(_≡ₛ_)!}
{-  List.index ((x ⊰ l₁) List.++ ∅) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ (l₁ List.++ ∅)) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ l₁) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[ {!!} ]
  x 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ l₁) 𝟎 🝖-end-}
test {l₁ = x ⊰ l₁} {∅} {𝐒 n} = {!!}
test {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝟎} = {!!}
test {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝐒 n} = {!!}

{-
instance
  List-concatenationOperator : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ConcatenationOperator ⦃ List-listLike{A = A} ⦄
  ConcatenationOperator.indexing List-concatenationOperator _ _ = <>
  ConcatenationOperator._++_     List-concatenationOperator = List._++_
  ConcatenationOperator.size     List-concatenationOperator {l₁ = l₁} {l₂ = l₂} = length-[++] {l₁ = l₁}{l₂ = l₂}
  Tuple.left (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {n = 𝟎} = {!!}
  Tuple.left (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {n = 𝐒 n} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = ∅} {x ⊰ l₂} {n = 𝟎} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = ∅} {x ⊰ l₂} {n = 𝐒 n} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝟎} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝐒 n} = {!!}
-}

module _ where
  open import Numeral.CoordinateVector as Vec

  
  instance
    Vector-listLike : ListLike{I = ℕ}(n ↦ Vector n A)
    ListLike.E (Vector-listLike {A = A}) = A
    ListLike.length Vector-listLike {n} = const n
    ListLike.index Vector-listLike l(i) = l(i)

  instance
    Vector-prependFunction : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → PrependFunction ⦃ Vector-listLike{A = A} ⦄
    PrependFunction.indexing Vector-prependFunction = 𝐒
    PrependFunction.prepend  Vector-prependFunction = Vec.prepend
    PrependFunction.size     Vector-prependFunction = [≡]-intro
    PrependFunction.ordering Vector-prependFunction = [∧]-intro (reflexivity(_≡ₛ_)) (reflexivity(_≡ₛ_))

  instance
    Vector-concatenationOperator : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ConcatenationOperator ⦃ Vector-listLike{A = A} ⦄
    ConcatenationOperator.indexing Vector-concatenationOperator = ℕ._+_
    ConcatenationOperator._++_     Vector-concatenationOperator = Vec._++_
    ConcatenationOperator.size     Vector-concatenationOperator = [≡]-intro
    ConcatenationOperator.ordering Vector-concatenationOperator = [∧]-intro {!!} {!!}
-}
