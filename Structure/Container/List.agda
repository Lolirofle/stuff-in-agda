module Structure.Container.List where

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

import      Data.Option as Option
import      Lvl
open import Logic.Propositional
open import Logic
open import Numeral.Finite
import      Numeral.Finite.Bound as 𝕟-bound
-- open import Numeral.Finite.Category
import      Numeral.Finite.Oper as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
open import Relator.Equals renaming (_≡_ to _≡ₑ_ ; _≢_ to _≢ₑ_)
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₑ ℓₑₑ ℓₑₐ : Lvl.Level
private variable A B : Type{ℓ}
private variable I : Type{ℓᵢ}
private variable C C₁ C₂ Cₒ Cᵢ : I → Type{ℓₗ}
-- private variable E E₁ E₂ : Type{ℓₑ}

module _ {I : Type{ℓᵢ}} (C : I → Type{ℓₗ}) where
  private variable i i₁ i₂ : I
  private variable l l₁ l₂ : C(i)
  -- private variable x : E

  record ListLike : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ Lvl.𝐒(ℓₑ)} where
    field
      E : Type{ℓₑ}
      length : C(i) → ℕ
      index : (l : C(i)) → 𝕟(length l) → E

  record FoldingListLike {ℓₑ} : Typeω where
    field
      E : Type{ℓₑ}

      empty-indexing : I
      empty : C(empty-indexing)

      prepend-indexing : I → I
      prepend : E → C(i) → C(prepend-indexing i)

      foldᵣ : (E → A → A) → A → C(i) → A
      foldᵣ-of-empty   : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ∀{_▫_}{id : A} → (foldᵣ(_▫_) id empty ≡ₛ id)
      foldᵣ-of-prepend : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ∀{_▫_}{id : A}{x}{l : C(i)} → (foldᵣ(_▫_) id (prepend x l) ≡ₛ x ▫ (foldᵣ(_▫_) id l))

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
          → (index(prepend{i} x l)([≡]-substitutionₗ size {𝕟} 𝟎) ≡ₛ x)
          ∧ (∀{n} → (index(prepend{i} x l)([≡]-substitutionₗ size {𝕟}(𝐒(n))) ≡ₛ index l n))
        field ordering : Ordering
      open PrependFunction ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Prepend ⦃ inst ⦄ = PrependFunction(inst)

      record PostpendFunction : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ ℓₑₑ} where
        field
          indexing : I → I
          postpend  : E → C(i) → C(indexing i)
        Size = ∀{i}{x}{l : C(i)} → (length(postpend x l) ≡ₑ 𝐒(length l))
        field size : Size
        OrderingBase = ∀{i}{x}{l}    → (index(postpend{i} x l)([≡]-substitutionₗ size {𝕟} maximum) ≡ₛ x)
        OrderingStep = ∀{i}{x}{l}{n} → (index(postpend{i} x l)([≡]-substitutionₗ size {𝕟}(𝐒(n))) ≡ₛ index l n)
        Ordering = OrderingBase ∧ OrderingStep
        field ordering : Ordering
      open PostpendFunction ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Postpend ⦃ inst ⦄ = PostpendFunction(inst)

      record ConcatenationOperator : Type{ℓᵢ Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ ℓₑₑ} where
        field
          indexing : I → I → I
          _++_  : C(i₁) → C(i₂) → C(indexing i₁ i₂)
        Size = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)} → (length(l₁ ++ l₂) ≡ₑ length(l₁) ℕ.+ length(l₂))
        field size : Size
        OrderingLeft  = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)}{n} → (index(l₁ ++ l₂)([≡]-substitutionₗ size {𝕟} (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ index l₁(n))
        OrderingRight = ∀{i₁ i₂}{l₁ : C(i₁)}{l₂ : C(i₂)}{n} → (index(l₁ ++ l₂)([≡]-substitutionₗ size {𝕟} (length(l₁) 𝕟.Unclosed.+ₙₗ n)) ≡ₛ index l₂(n))
        Ordering = OrderingLeft ∧ OrderingRight
        field ordering : Ordering
      open ConcatenationOperator ⦃ ... ⦄ hiding (Size ; size ; Ordering ; ordering) public
      module Concatenation ⦃ inst ⦄ = ConcatenationOperator(inst)



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
  ListLike.length (List-listLike {A = A}) = List.length
  ListLike.index  (List-listLike {A = A}) = List.index

instance
  List-prependFunction : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → PrependFunction ⦃ List-listLike{A = A} ⦄
  PrependFunction.indexing List-prependFunction _ = <>
  PrependFunction.prepend  List-prependFunction = _⊰_
  PrependFunction.size     List-prependFunction {x = x} {l = l} = preserving₁ ⦃ [≡]-equiv ⦄ (List.length)(x ⊰_)(𝐒) {l}
  Tuple.left  (PrependFunction.ordering List-prependFunction) = reflexivity(_≡ₛ_)
  Tuple.right (PrependFunction.ordering List-prependFunction) = reflexivity(_≡ₛ_)

length-[++]' : ∀{l₁ l₂} → (List.length{T = A}(l₁ List.++ l₂) ≡ₑ List.length(l₁) ℕ.+ List.length(l₂))
length-[++]' {l₁ = ∅}      {l₂} = [≡]-intro
length-[++]' {l₁ = x ⊰ l₁} {l₂} = [≡]-with(𝐒) (length-[++]' {l₁ = l₁}{l₂})
{-
test0 : ∀{a b : ℕ}{ab : a ≡ₑ b}{P : ℕ → Stmt{Lvl.𝟎}}{pa : P(𝐒 a)} → ([≡]-substitutionᵣ ([≡]-with(𝐒) ab) {P} pa ≡ₑ {![≡]-intro!})

test : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ∀{l₁ l₂}{n} → List.index(l₁ List.++ l₂)([≡]-substitutionₗ (length-[++]' {l₁ = l₁}{l₂ = l₂}) {𝕟} (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ List.index l₁(n)
test {l₁ = x ⊰ l₁} {∅} {𝟎} = {!reflexivity(_≡ₛ_)!}
test {l₁ = x ⊰ l₁} {∅} {𝐒 n} = {!!}
test {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝟎} = {!!}
test {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝐒 n} = {!!}
{-
  List.index ((x ⊰ l₁) List.++ ∅) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ (l₁ List.++ ∅)) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ l₁) ([≡]-substitutionₗ length-[++]' (𝕟-bound.bound-[+]ᵣ 𝟎)) 🝖[ _≡ₛ_ ]-[ {!!} ]
  x 🝖[ _≡ₛ_ ]-[]
  List.index (x ⊰ l₁) 𝟎 🝖-end-}
-}

-- 𝕟-function-𝟎 : ∀{n₁ n₂ : ℕ}{i₁ : 𝕟(n₁)} → (n₁ ≡ₑ n₂) → (𝟎 ≡ₑ 𝟎)

instance -- TODO: It would be nice to have UIP/axiom K for this so that substitution always are equal, but maybe (decidable → UIP)? Lists should have many decidable stuff when the underlying type is decidable?
  List-concatenationOperator : ⦃ equiv-A : Equiv{ℓₑₐ}(A) ⦄ → ConcatenationOperator ⦃ List-listLike{A = A} ⦄
  ConcatenationOperator.indexing List-concatenationOperator _ _ = <>
  ConcatenationOperator._++_     List-concatenationOperator = List._++_
  ConcatenationOperator.size     List-concatenationOperator {l₁ = l₁} {l₂ = l₂} = length-[++] {l₁ = l₁}{l₂ = l₂}
  ConcatenationOperator.ordering (List-concatenationOperator {ℓₑₐ = ℓₑₐ}{A = A}) = [∧]-intro {!!} {!p!} where
    -- l-type : (l₁ l₂ : List(A)) → (n : 𝕟(List.length l₁)) → Type{ℓₑₐ}
    -- l-type l₁ l₂ n rewrite (length-[++] {l₁ = l₁}{l₂ = l₂}) = List.index (l₁ List.++ l₂) {!𝕟-bound.bound-[+]ᵣ {n₂ = List.length l₂} n!} ≡ₛ List.index l₁ n
    -- l-type l₁@(_ ⊰ _)      l₂ 𝟎    = (List.index (l₁ List.++ l₂) 𝟎 ≡ₛ List.index l₁ 𝟎)
    -- l-type l₁@(x ⊰ y ⊰ l₁ₛ) l₂ (𝐒 n) rewrite symmetry _ (length-[++] {l₁ = l₁ₛ}{l₂ = l₂}) = (List.index (l₁ List.++ l₂) (𝐒 {!𝕟-bound.bound-[+]ᵣ n!}) ≡ₛ List.index l₁ (𝐒 n))
    -- l-type l₁ l₂ n with l₁ | List.length l₁ | n
    -- ... | p | q | r = ?
    -- l-type l₁ l₂ n = (List.index (l₁ List.++ l₂) ([≡]-substitutionₗ length-[++] (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ List.index l₁ n)
    -- l : ∀{l₁ l₂ : List(A)}{n : 𝕟(List.length l₁)} → l-type l₁ l₂ n

    -- test : ∀{ℓ}{T : Type{ℓ}}{a b : T}{eq : a ≡ₑ b}{P}{x} → [≡]-substitutionₗ eq {P} x ≡ₛ x

    l : ∀{l₁ l₂ : List(A)}{n : 𝕟(List.length l₁)} → (List.index (l₁ List.++ l₂) ([≡]-substitutionₗ (length-[++] {l₁ = l₁}{l₂ = l₂}) {𝕟} (𝕟-bound.bound-[+]ᵣ n)) ≡ₛ List.index l₁ n)
    l {x ⊰ l₁} {l₂} {𝟎} =
      List.index ((x ⊰ l₁) List.++ l₂) ([≡]-substitutionₗ (length-[++] {l₁ = x ⊰ l₁}{l₂ = l₂}) {𝕟} (𝕟-bound.bound-[+]ᵣ {n₁ = List.length(x ⊰ l₁)}{n₂ = List.length l₂} 𝟎)) 🝖[ _≡ₛ_ ]-[]
      List.index (x ⊰ (l₁ List.++ l₂)) ([≡]-substitutionₗ (length-[++] {l₁ = x ⊰ l₁}{l₂ = l₂}) {𝕟} (𝕟-bound.bound-[+]ᵣ {n₁ = 𝐒(List.length l₁)}{n₂ = List.length l₂} 𝟎)) 🝖[ _≡ₛ_ ]-[ {!!} ]
      -- TODO: I think the substitution should preserve composition and disappear inside here because it is a groupoid
      x                     🝖[ _≡ₛ_ ]-[]
      List.index (x ⊰ l₁) 𝟎 🝖-end
    l {x ⊰ l₁} {l₂} {𝐒 n} = {!!}
    -- p : ∀{l₁ l₂ : List{ℓ}(A)}{n : ℕ}{i : 𝕟(n)} → [≡]-substitutionₗ(length-[++] {l₁ = l₁}{l₂ = l₂}) {𝕟} {!!} ≡ₑ {![≡]-intro!}
  
  {-Tuple.left (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {n = 𝟎} = {!!}
  Tuple.left (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {n = 𝐒 n} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = ∅} {x ⊰ l₂} {n = 𝟎} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = ∅} {x ⊰ l₂} {n = 𝐒 n} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝟎} = {!!}
  Tuple.right (ConcatenationOperator.ordering List-concatenationOperator) {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} {𝐒 n} = {!!}-}


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
    ConcatenationOperator.ordering (Vector-concatenationOperator {A = A}) = [∧]-intro (\{i₁}{i₂}{l₁}{l₂}{n} → l{i₁}{i₂}{l₁}{l₂}{n}) (\{i₁}{i₂}{l₁}{l₂}{n} → r{i₁}{i₂}{l₁}{l₂}{n}) where
      l : ∀{i₁ i₂ : ℕ}{l₁ : Vector i₁ A}{l₂ : Vector i₂ A}{n : 𝕟(i₁)} → ((l₁ Vec.++ l₂) (𝕟-bound.bound-[+]ᵣ n) ≡ₛ l₁(n))
      l {i₁ = 𝐒 i₁} {n = 𝟎}   = reflexivity(_≡ₛ_)
      l {i₁ = 𝐒 i₁} {n = 𝐒 n} = l {i₁ = i₁} {n = n}

      r : ∀{i₁ i₂ : ℕ}{l₁ : Vector i₁ A}{l₂ : Vector i₂ A}{n : 𝕟 i₂} → ((l₁ Vec.++ l₂) (i₁ 𝕟.Unclosed.+ₙₗ n) ≡ₛ l₂(n))
      r {𝟎}    = reflexivity(_≡ₛ_)
      r {𝐒 i₁} = r {i₁}
