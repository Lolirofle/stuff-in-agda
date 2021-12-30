open import Data.Boolean
open import Type

module Data.BinaryTree.Heap {ℓ} {T : Type{ℓ}} (_≤?_ : T → T → Bool) where

import      Lvl
open import Data hiding (empty)
open import Data.BinaryTree

BinaryHeap = BinaryTree (Unit{Lvl.𝟎}) (T)

private variable ℓᵣ : Lvl.Level
private variable R : Type{ℓᵣ}

open import Data.BinaryTree.Functions
open import Data.Option
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn using (_∘_ ; _∘₂_ ; _$_)

merge : BinaryHeap → BinaryHeap → BinaryHeap
merge (Leaf <>)         (Leaf <>)      = Leaf <>
merge x@(Node _ _ _)    (Leaf <>)      = x
merge (Leaf <>)         y@(Node _ _ _) = y
merge x@(Node xa xl xr) y@(Node ya yl yr) with (xa ≤? ya) | (\_ → merge y xr) | (\_ → merge x yr)
... | 𝑇 | 𝑇-branch | _ = Node xa (𝑇-branch(<>{Lvl.𝟎})) xl
... | 𝐹 | _ | 𝐹-branch = Node ya (𝐹-branch(<>{Lvl.𝟎})) yl

insert : T → BinaryHeap → BinaryHeap
insert a = merge(singletonTree a)

pop : BinaryHeap → Option(T ⨯ BinaryHeap)
pop (Leaf <>)    = None
pop (Node a l r) = Some(a , merge l r)

{-# TERMINATING #-}
foldOrdered : (T → R → R) → R → BinaryHeap → R
foldOrdered(_▫_) id (Leaf <>)    = id
foldOrdered(_▫_) id (Node a l r) = a ▫ foldOrdered(_▫_) id (merge l r)

filterFold : (T → R → Option(R)) → R → BinaryHeap → (R ⨯ BinaryHeap)
filterFold (_▫_) r₀ (Leaf <>)    = (r₀ , Leaf <>)
filterFold (_▫_) r₀ (Node a l r)
  with (r₁ , il) ← filterFold (_▫_) r₀ l
  with (r₂ , ir) ← filterFold (_▫_) r₁ r
  with (a ▫ r₂)
... | Some r₃ = (r₃ , merge il ir)
... | None    = (r₂ , Node a il ir)

filter : (T → Bool) → BinaryHeap → BinaryHeap
filter f = Tuple.right ∘ filterFold (\{a <> → (\{𝐹 → None ; 𝑇 → Some <>}) $ f(a)}) (<>{Lvl.𝟎})

open import Data.List
import      Data.List.Functions as List

separate : (T → Bool) → BinaryHeap → (List(T) ⨯ BinaryHeap)
separate f = filterFold (\a l → (\{𝐹 → None ; 𝑇 → Some(a ⊰ l)}) $ f(a)) ∅

update : (T → Bool) → (T → T) → BinaryHeap → BinaryHeap
update p f a with (as , b) ← separate p a = List.foldᵣ insert b (List.map f as)
