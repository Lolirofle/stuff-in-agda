module Sets.IterativeSet.Oper where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Numeral.Natural
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to intro)
open import Sets.IterativeSet
open import Syntax.Function
open import Type.Dependent.Sigma

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level
  open Iset

  -- The empty set, consisting of no elements.
  -- Index is the empty type, which means that there are no objects pointing to elements in the set.
  ∅ : Iset{ℓ}
  ∅ = set{Index = Empty} empty

  -- The singleton set, consisting of one element.
  -- Index is the unit type, which means that there are a single object pointing to a single element in the set.
  singleton : Iset{ℓ} → Iset{ℓ}
  singleton = set{Index = Unit} ∘ const

  -- The pair set, consisting of two elements.
  -- Index is the boolean type, which means that there are two objects pointing to two elements in the set.
  pair : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  pair A B = set{Index = Lvl.Up(Bool)} ((if_then B else A) ∘ Lvl.Up.obj)

  -- The union operator.
  -- Index(A ∪ B) is the either type of two indices, which means that both objects from the A and the B index point to elements in the set.
  _∪_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ∪ B = set{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))

  _,_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A , B = pair (singleton A) (pair A B)

  _⨯_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ⨯ B = set{Index = Index(A) Tuple.⨯ Index(B)} \{(ia Tuple., ib) → (elem(A)(ia) , elem(B)(ib))}

  -- The big union operator.
  -- Index(⋃ A) is the dependent sum type of an Index(A) and the index of the element this index points to.
  ⋃ : Iset{ℓ} → Iset{ℓ}
  ⋃ A = set{Index = Σ(Index(A)) (ia ↦ Index(elem(A)(ia)))} (\{(intro ia i) → elem(elem(A)(ia))(i)})

  indexFilter : (A : Iset{ℓ}) → (Index(A) → Stmt{ℓ}) → Iset{ℓ}
  indexFilter A P = set{Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  filter : (A : Iset{ℓ}) → (Iset{ℓ} → Stmt{ℓ}) → Iset{ℓ}
  filter{ℓ} A P = indexFilter A (P ∘ elem(A))

  indexFilterBool : (A : Iset{ℓ}) → (Index(A) → Bool) → Iset{ℓ}
  indexFilterBool A f = indexFilter A (Lvl.Up ∘ IsTrue ∘ f)

  filterBool : (A : Iset{ℓ}) → (Iset{ℓ} → Bool) → Iset{ℓ}
  filterBool A f = indexFilterBool A (f ∘ elem(A))

  mapSet : (Iset{ℓ} → Iset{ℓ}) → (Iset{ℓ} → Iset{ℓ})
  mapSet f(A) = set{Index = Index(A)} (f ∘ elem(A))

  -- The power set operator.
  -- Index(℘(A)) is a function type. An instance of such a function represents a subset, and essentially maps every element in A to a boolean which is interpreted as "in the subset of not".
  -- Note: This only works properly in a classical setting. Trying to use indexFilter instead result in universe level problems.
  ℘ : Iset{ℓ} → Iset{ℓ}
  ℘(A) = set{Index = Index(A) → Bool} (indexFilterBool A)

  -- The set of ordinal numbers of the first order.
  ω : Iset{ℓ}
  ω = set{Index = Lvl.Up ℕ} (N ∘ Lvl.Up.obj) where
    N : ℕ → Iset{ℓ}
    N(𝟎)    = ∅
    N(𝐒(n)) = N(n) ∪ singleton(N(n))
