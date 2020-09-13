open import Type

module Structure.Container.IndexedIterable {ℓᵢ} {Index : Type{ℓᵢ}} where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Option
import      Data.Option.Functions as Option
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Relator.Equals

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}
private variable Elem : Type{ℓₑ}
private variable i : Index

module _ (Iter : Index → Type{ℓ}) where
  IsEmptyTypeFn = ∀{i} → Iter(i) → Bool

  IndexStepFn : IsEmptyTypeFn → Type
  IndexStepFn isEmpty = ∀{i} → (iter : Iter(i)) → (if isEmpty(iter) then Unit else Index)

  CurrentFn : Type{ℓₑ} → IsEmptyTypeFn → Type
  CurrentFn Element isEmpty = ∀{i} → (iter : Iter(i)) → (if isEmpty(iter) then Unit else Element)

  StepFn : Type{ℓₑ} → (isEmpty : IsEmptyTypeFn) → IndexStepFn isEmpty → Type
  StepFn Element isEmpty indexStep =  ∀{i} → (iter : Iter(i)) → Out iter where
    Out : Iter(i) → Type
    Out iter with isEmpty iter | indexStep iter
    ... | 𝑇 | <> = Unit
    ... | 𝐹 | is = Iter(is)

-- An iterator type `Iter` is iterable when there may be elements that the iterator can yield in sequence.
-- It should be possible to decide whether the iterator is empty, and when it is not, get the element it points to and advancing to its next state containing the next element in order.
record Iterable (Iter : Index → Type{ℓ}) {ℓₑ} : Type{ℓ Lvl.⊔ ℓᵢ Lvl.⊔ Lvl.𝐒(ℓₑ)} where
  field
    -- The type of the elements in the iterator.
    {Element} : Type{ℓₑ}

    -- Whether there are no elements left in the iterator.
    isEmpty : IsEmptyTypeFn(Iter)

    -- The current/frontmost element in the iterator if it is non-empty.
    current : CurrentFn(Iter) Element isEmpty

    -- The next iterator index. Advances the index if the iterator is non-empty.
    {indexStep} : IndexStepFn(Iter) isEmpty

    -- The next iterator state. Advancing the iterator if it is non-empty.
    step : StepFn(Iter) Element isEmpty indexStep

  -- Whether there are at most the given number of elements in the iterator.
  atMost : ℕ → Iter(i) → Bool
  atMost(𝟎)    iter = isEmpty(iter)
  atMost(𝐒(n)) iter with isEmpty(iter) | indexStep iter | step iter
  ... | 𝑇 | <>  | <> = 𝑇
  ... | 𝐹 | _   | is = atMost(n) is

  -- Skipping the given number of iterator indices. Advances as many steps as possible.
  indexWalk : (n : ℕ) → (iter : Iter(i)) → (if(atMost n iter) then Unit else Index)
  indexWalk {i} 𝟎 iter with isEmpty(iter)
  ... | 𝑇 = <>
  ... | 𝐹 = i
  indexWalk {i} (𝐒(n)) iter with isEmpty(iter) | indexStep iter | step iter
  ... | 𝑇 | <> | <>    = <>
  ... | 𝐹 | _  | iters = indexWalk n iters

  WalkFn : Type
  WalkFn = ∀{i} → (n : ℕ) → (iter : Iter(i)) → Out n iter where
    Out : ℕ → Iter(i) → Type
    Out n iter with atMost n iter | indexWalk n iter
    ... | 𝑇 | <> = Unit
    ... | 𝐹 | is = Iter(is)

    {-
    walk : WalkFn
    walk(𝟎) iter with isEmpty(iter)
    ... | 𝑇 = <>
    ... | 𝐹 = iter
    walk(𝐒(n)) iter with isEmpty(iter) | indexStep iter | step iter | walk n iter
    ... | 𝑇 | <> | <>    | _    = <>
    ... | 𝐹 | _  | iters | iters2 = ? -- walk n iters
    -}

  Foldᵣ : ∀{ℓ} → Type{ℓ} → Type
  Foldᵣ(T) = ∀{i} → (Element → T → T) → T → Iter(i) → T

  FoldᵣCriteria : Foldᵣ(T) → (∀{i} → (Element → T → T) → T → Iter(i) → Type)
  FoldᵣCriteria foldᵣ(_▫_) id iter with isEmpty iter | indexStep iter | current iter | step iter
  ... | 𝑇 | <> | <> | <>    = (foldᵣ(_▫_) id iter ≡ id)
  ... | 𝐹 | _  | x  | iters = (foldᵣ(_▫_) id iter ≡ x ▫ foldᵣ(_▫_) id iters)

  -- An iterator is finite when it is possible to fold it (when a fold function exists).
  -- This works because a fold for an infinite iterator cannot terminate, and only terminating functions exist.
  -- TODO: But it seems to be impossible to define a "foldUntil" function (though it is up to function extensionality).
  Finite = ∀{ℓ}{T : Type{ℓ}} → ∃{Obj = Foldᵣ(T)}(foldᵣ ↦ ∀{i}{_▫_}{id : T}{iter : Iter(i)} → FoldᵣCriteria (\{i}(_▫_) id → foldᵣ{i}(_▫_) id) (_▫_) id iter)
  module _ ⦃ fin : Finite ⦄ where
    foldᵣ : ∀{i} → (Element → T → T) → T → Iter(i) → T
    foldᵣ = [∃]-witness fin

    length : ∀{i} → Iter(i) → ℕ
    length = foldᵣ(const 𝐒) 𝟎

    count : ∀{i} → (Element → Bool) → Iter(i) → ℕ
    count(P) = foldᵣ(x ↦ if P(x) then 𝐒 else id) 𝟎

    foldₗ : (T → Element → T) → T → Iter(i) → T
    foldₗ(_▫_) = swap(foldᵣ(y ↦ f ↦ x ↦ f(x ▫ y)) id)

    last : ∀{i} → Iter(i) → Option(Element)
    last = foldₗ(const Some) None

    -- Note: Below are possibly inefficient implementations of functions because if they were guaranteed to exit early, the number of computations would be reduced.
    first : ∀{i} → Iter(i) → Option(Element)
    first = foldᵣ(const ∘ Some) None

  -- TODO: Complete = Surjective(step)

  record Initialed (i : Index) : Type{ℓᵢ Lvl.⊔ ℓ} where
    constructor initialed
    eta-equality
    field
      iter : Iter(i)
      left : ℕ

  Initialed-iterable : Iterable(Initialed)
  Element   Initialed-iterable = Element
  isEmpty   Initialed-iterable (initialed iter 𝟎)      = 𝑇
  current   Initialed-iterable (initialed iter 𝟎)      = <>
  indexStep Initialed-iterable (initialed iter 𝟎)      = <>
  step      Initialed-iterable (initialed iter 𝟎)      = <>
  isEmpty   Initialed-iterable (initialed iter (𝐒(_))) = isEmpty iter
  current   Initialed-iterable (initialed iter (𝐒(_))) = current iter
  indexStep Initialed-iterable (initialed iter (𝐒(_))) = indexStep iter
  step      Initialed-iterable (initialed iter (𝐒(n))) with isEmpty iter | indexStep iter | step iter
  ... | 𝑇 | _ | _     = <>
  ... | 𝐹 | _ | sIter = initialed sIter n

  {-
  record Skipped (i : Index) : Type{ℓᵢ Lvl.⊔ ℓ} where
    constructor skipped
    eta-equality
    field
      iter  : Iter(i)
      still : ℕ

  Skipped-iterable : Iterable(Skipped)
  Element   Skipped-iterable = Element
  isEmpty   Skipped-iterable (skipped iter 𝟎)      = 𝑇
  current   Skipped-iterable (skipped iter 𝟎)      = <>
  indexStep Skipped-iterable (skipped iter 𝟎)      = <>
  step      Skipped-iterable (skipped iter 𝟎)      = <>
  isEmpty   Skipped-iterable (skipped iter (𝐒(_))) = isEmpty (walk (𝐒(n)) iter)
  current   Skipped-iterable (skipped iter (𝐒(_))) = current (walk (𝐒(n)) iter)
  indexStep Skipped-iterable (skipped iter (𝐒(_))) = indexStep (walk (𝐒(n)) iter)
  step      Skipped-iterable (skipped iter (𝐒(n))) with isEmpty iter | indexStep iter | step iter
  -}

  mapped : (Element → Elem) → Iterable(Iter)
  Element (mapped {Elem = Elem} f) = Elem
  isEmpty (mapped f) = isEmpty
  current (mapped f) iter with isEmpty iter | current iter
  ... | 𝑇 | <> = <>
  ... | 𝐹 | x  = f(x)
  indexStep (mapped f) iter = indexStep iter
  step      (mapped f) iter = step iter

{-record Stored (n : ℕ) {Iter : Index → Type{ℓ₁}} (iterable : Iterable(Iter)) : Type where
  field
    Queue(Iterator.Element(iterable))
-}

  {- TODO: Also needs to store data, so it cannot be the same Iter
  skipped : ℕ → Iterator{ℓₑ} → Iterator
  Iterator.Element (skipped _ iterator) = Iterator.Element iterator
  Iterator.isEmpty (skipped n iterator) = Iterator.atMost n iterator
  Iterator.current (skipped _ iterator) =
  Iterator.indexStep (skipped iterator) =
  Iterator.step      (skipped iterator) =
-}

{-
skipped : ℕ → ∀{iter} → Iterable{ℓₑ}(iter) → Iterable(iter)
skipped 𝟎 iterable = iterable
skipped (𝐒 n) iterable = {!!}
-}

  -- An empty iterator of the iterable.
  EmptyConstruction : ∀{i} → Iter(i) → Type
  EmptyConstruction(empty) = IsTrue(isEmpty empty)

  -- A function prepending an element to an iterator of the iterable.
  PrependConstruction : ∀{indexPrepend : ∀{i} → Element → Iter(i) → Index} → (∀{i} → (x : Element) → (iter : Iter(i)) → Iter(indexPrepend x iter)) → Type
  PrependConstruction{indexPrepend} (prepend) = ∀{i}{x}{iter : Iter(i)} → ∃{Obj = IndexStep x iter}(Out x iter) where
    IndexStep : Element → Iter(i) → Type
    IndexStep{i} x iter with isEmpty(prepend x iter) | indexStep(prepend x iter)
    ... | 𝑇 | _ = Empty
    ... | 𝐹 | p = (p ≡ i)

    Out : (x : Element) → (iter : Iter(i)) → IndexStep x iter → Type
    Out x iter stepProof with isEmpty(prepend x iter) | indexStep(prepend x iter) | current(prepend x iter) | step(prepend x iter)
    ... | 𝐹 | _ | cur | st with [≡]-intro ← stepProof = (x ≡ cur) ∧ (st ≡ iter)

  module _
    {indexEmpty}{empty}
    ⦃ empty-construciton : EmptyConstruction{indexEmpty}(empty) ⦄
    {indexPrepend : ∀{i} → Element → Iter(i) → Index}
    {prepend : ∀{i} → (x : Element) → (iter : Iter(i)) → Iter(indexPrepend x iter)}
    ⦃ prepend-construction : PrependConstruction{indexPrepend}(prepend) ⦄
    where

    singleton : (x : Element) → Iter(indexPrepend x empty)
    singleton x = prepend x empty
